import FK.NestedMetricRightExtension

/-!
# Source-faithful ordinary nested gluing

A right-disjoint presentation has duplicated small-box and outside vertices.
The no-cross sum law cannot be transported after those copies are identified.
This module uses the different, source-faithful boundary law obtained by
pulling an ordinary target setoid back along the gluing map.  Under this law,
each fibre is wired, and the resulting FK law is proved to be the ordinary
target FK law, without requiring a vertex equivalence.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.Finite.LabelledMultigraph.VertexGluing

open FK.Finite FK.Finite.LabelledMultigraph

universe u v

variable {G H : LabelledMultigraph}

/-- Reindex a configuration along an edge equivalence. -/
noncomputable def gluedConfig (e : G.Edge ≃ H.Edge) :
    G.Configuration ≃ H.Configuration :=
  Equiv.arrowCongr e (Equiv.refl Bool)

@[simp] lemma gluedConfig_apply (e : G.Edge ≃ H.Edge)
    (ω : G.Configuration) (i : G.Edge) : gluedConfig e ω (e i) = ω i := by
  simp [gluedConfig]

section Reachability

variable (g : G.Vertex → H.Vertex) (e : G.Edge ≃ H.Edge)
variable (hs : ∀ i, g (G.source i) = H.source (e i))
variable (ht : ∀ i, g (G.target i) = H.target (e i))
variable (α : H.BoundaryPartition) (ω : G.Configuration)

/-- Boundary-related vertices in a glued fibre are reachable, including when
the two representatives are definitionally distinct. -/
lemma reachable_of_boundary {u v : G.Vertex}
    (huv : α.r (g u) (g v)) :
    (G.connectionGraph (Setoid.comap g α) ω).Reachable u v := by
  by_cases h : u = v
  · subst v
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨h, Or.inl huv⟩

/-- An open labelled edge joins its two endpoints in the source graph. -/
lemma reachable_of_open_joins {i : G.Edge} {u v : G.Vertex}
    (hi : ω i = true) (hjoin : G.Joins i u v) :
    (G.connectionGraph (Setoid.comap g α) ω).Reachable u v := by
  by_cases h : u = v
  · subst v
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨h, Or.inr ⟨i, hi, hjoin⟩⟩

include hs ht

/-- Every source adjacency becomes a target reachability after gluing. -/
lemma reachable_target_of_adj {u v : G.Vertex}
    (huv : (G.connectionGraph (Setoid.comap g α) ω).Adj u v) :
    (H.connectionGraph α (gluedConfig e ω)).Reachable (g u) (g v) := by
  by_cases h : g u = g v
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    refine ⟨h, ?_⟩
    rcases huv.2 with hwire | ⟨i, hi, hjoin⟩
    · exact Or.inl hwire
    · refine Or.inr ⟨e i, ?_, ?_⟩
      · simpa only [gluedConfig_apply] using hi
      · rcases hjoin with hjoin | hjoin
        · exact Or.inl ⟨(hs i).symm.trans (congrArg g hjoin.1),
            (ht i).symm.trans (congrArg g hjoin.2)⟩
        · exact Or.inr ⟨(hs i).symm.trans (congrArg g hjoin.1),
            (ht i).symm.trans (congrArg g hjoin.2)⟩

/-- Forward reachability for a surjective or non-surjective vertex gluing. -/
theorem reachable_target_of_reachable {u v : G.Vertex}
    (huv : (G.connectionGraph (Setoid.comap g α) ω).Reachable u v) :
    (H.connectionGraph α (gluedConfig e ω)).Reachable (g u) (g v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact ih.trans ((SimpleGraph.reachable_iff_reflTransGen _ _).mp
        (reachable_target_of_adj g e hs ht α ω hbc))

/-- One target adjacency lifts between arbitrary representatives of its
endpoints. -/
lemma reachable_source_of_adj_aux {x y : H.Vertex}
    (hxy : (H.connectionGraph α (gluedConfig e ω)).Adj x y)
    {u v : G.Vertex} (hu : g u = x) (hv : g v = y) :
    (G.connectionGraph (Setoid.comap g α) ω).Reachable u v := by
  rcases hxy.2 with hwire | ⟨i, hi, hjoin⟩
  · apply reachable_of_boundary g α ω
    rw [hu, hv]
    exact hwire
  · let j := e.symm i
    have hopen : ω j = true := by
      have he : gluedConfig e ω i = true := hi
      rw [← e.apply_symm_apply i] at he
      simpa only [gluedConfig_apply] using he
    rcases hjoin with hjoin | hjoin
    · have hsource : g (G.source j) = x := by
        rw [hs]
        change H.source (e (e.symm i)) = x
        rw [e.apply_symm_apply, hjoin.1]
      have htarget : g (G.target j) = y := by
        rw [ht]
        change H.target (e (e.symm i)) = y
        rw [e.apply_symm_apply, hjoin.2]
      exact (reachable_of_boundary g α ω (u := u) (v := G.source j) (by
          rw [hu, hsource])).trans
        ((reachable_of_open_joins g α ω hopen
          (Or.inl ⟨rfl, rfl⟩ : G.Joins j (G.source j) (G.target j))).trans
          (reachable_of_boundary g α ω (u := G.target j) (v := v) (by
            rw [htarget, hv])))
    · have hsource : g (G.target j) = x := by
        rw [ht]
        change H.target (e (e.symm i)) = x
        rw [e.apply_symm_apply, hjoin.2]
      have htarget : g (G.source j) = y := by
        rw [hs]
        change H.source (e (e.symm i)) = y
        rw [e.apply_symm_apply, hjoin.1]
      exact (reachable_of_boundary g α ω (u := u) (v := G.target j) (by
          rw [hu, hsource])).trans
        ((reachable_of_open_joins g α ω hopen
          (Or.inr ⟨rfl, rfl⟩ : G.Joins j (G.target j) (G.source j))).trans
          (reachable_of_boundary g α ω (u := G.source j) (v := v) (by
            rw [htarget, hv])))

/-- A surjective endpoint-compatible gluing preserves reachability exactly:
all identifications are already wired by the pullback boundary setoid. -/
theorem reachable_source_iff_target (hg : Function.Surjective g) (u v : G.Vertex) :
    (G.connectionGraph (Setoid.comap g α) ω).Reachable u v ↔
      (H.connectionGraph α (gluedConfig e ω)).Reachable (g u) (g v) := by
  constructor
  · exact reachable_target_of_reachable g e hs ht α ω
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    have aux : ∀ {x y : H.Vertex},
        Relation.ReflTransGen
          (H.connectionGraph α (gluedConfig e ω)).Adj x y →
        ∀ {a b : G.Vertex}, g a = x → g b = y →
          (G.connectionGraph (Setoid.comap g α) ω).Reachable a b := by
      intro x y hxy
      induction hxy with
      | refl =>
          intro a b ha hb
          apply reachable_of_boundary g α ω
          rw [ha, hb]
      | @tail y z hxy hyz ih =>
          intro a c ha hc
          obtain ⟨b, hb⟩ := hg y
          exact (ih ha hb).trans
            (reachable_source_of_adj_aux g e hs ht α ω hyz hb hc)
    exact aux h rfl rfl

/-- Connected components of the source and target wired-open graphs are
 canonically equivalent. -/
noncomputable def connectedComponentEquiv (hg : Function.Surjective g) :
    (G.connectionGraph (Setoid.comap g α) ω).ConnectedComponent ≃
      (H.connectionGraph α (gluedConfig e ω)).ConnectedComponent := by
  let F : (G.connectionGraph (Setoid.comap g α) ω).ConnectedComponent →
      (H.connectionGraph α (gluedConfig e ω)).ConnectedComponent :=
    fun C => Quot.lift
      (fun u : G.Vertex =>
        (H.connectionGraph α (gluedConfig e ω)).connectedComponentMk (g u))
      (fun _ _ h => SimpleGraph.ConnectedComponent.sound
        (reachable_target_of_reachable g e hs ht α ω h)) C
  apply Equiv.ofBijective F
  constructor
  · intro C D hCD
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h u =>
      induction D using SimpleGraph.ConnectedComponent.ind with
      | h v =>
        apply SimpleGraph.ConnectedComponent.sound
        exact (reachable_source_iff_target g e hs ht α ω hg u v).2
          (SimpleGraph.ConnectedComponent.exact hCD)
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x =>
      obtain ⟨u, rfl⟩ := hg x
      exact ⟨(G.connectionGraph (Setoid.comap g α) ω).connectedComponentMk u, rfl⟩

end Reachability

end FK.Finite.LabelledMultigraph.VertexGluing

namespace FK.Finite.LabelledMultigraph.VertexGluing

open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

universe u v

variable {G H : LabelledMultigraph}

/-- Fibre wiring makes the glued component count equal to the target count. -/
theorem componentCount_gluing (g : G.Vertex → H.Vertex) (e : G.Edge ≃ H.Edge)
    (hs : ∀ i, g (G.source i) = H.source (e i))
    (ht : ∀ i, g (G.target i) = H.target (e i))
    (α : H.BoundaryPartition) (ω : G.Configuration)
    (hg : Function.Surjective g) :
    G.componentCount (Setoid.comap g α) ω =
      H.componentCount α (gluedConfig e ω) := by
  unfold LabelledMultigraph.componentCount
  exact Nat.card_congr (connectedComponentEquiv g e hs ht α ω hg)

/-- Edge weights are invariant under the configuration reindexing. -/
lemma edgeWeight_gluedConfig (e : G.Edge ≃ H.Edge) (p : NNReal)
    (ω : G.Configuration) :
    H.edgeWeight p (gluedConfig e ω) = G.edgeWeight p ω := by
  unfold LabelledMultigraph.edgeWeight gluedConfig
  change (∏ i : H.Edge, if ω (e.symm i) then p else 1 - p) = _
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp

/-- The unnormalized FK weight is invariant under source-faithful vertex
 gluing. -/
theorem fkWeight_gluing (g : G.Vertex → H.Vertex) (e : G.Edge ≃ H.Edge)
    (hs : ∀ i, g (G.source i) = H.source (e i))
    (ht : ∀ i, g (G.target i) = H.target (e i))
    (α : H.BoundaryPartition) (q p : NNReal) (ω : G.Configuration)
    (hg : Function.Surjective g) :
    H.fkWeight q p α (gluedConfig e ω) =
      G.fkWeight q p (Setoid.comap g α) ω := by
  unfold LabelledMultigraph.fkWeight
  rw [← componentCount_gluing g e hs ht α ω hg, edgeWeight_gluedConfig]

/-- **Exact FK-law transport by noninjective vertex gluing.** No vertex
 equivalence is assumed.  The source boundary is the ordinary target setoid
 pulled back along the surjection, not a no-cross sum boundary. -/
theorem map_gluedConfig_fkPMF (g : G.Vertex → H.Vertex) (e : G.Edge ≃ H.Edge)
    (hs : ∀ i, g (G.source i) = H.source (e i))
    (ht : ∀ i, g (G.target i) = H.target (e i))
    (α : H.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hg : Function.Surjective g) :
    PMF.map (gluedConfig e)
        (G.fkPMF hq hp₁.le (Setoid.comap g α)) = H.fkPMF hq hp₁.le α := by
  rw [← normalizedPMF_eq_actual_fkPMF G (Setoid.comap g α) hq hp₀ hp₁,
    ← normalizedPMF_eq_actual_fkPMF H α hq hp₀ hp₁]
  exact normalizedPMF_map_eq_of_proportional (gluedConfig e) _ _ 1 zero_lt_one
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (by
      intro ω
      rw [one_mul]
      exact fkWeight_gluing g e hs ht α q p ω hg)

/-- The pullback setoid wires any two source copies of one target vertex. -/
lemma comap_gluing_relation_of_eq (g : G.Vertex → H.Vertex)
    (α : H.BoundaryPartition) {u v : G.Vertex} (huv : g u = g v) :
    (Setoid.comap g α).r u v := by
  change α.r (g u) (g v)
  rw [huv]

end FK.Finite.LabelledMultigraph.VertexGluing


namespace FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing

open FK.Finite FK.Finite.LabelledMultigraph
open FK.InfiniteVolume.FiniteBox
open FK.Finite.LabelledMultigraph.VertexGluing

universe u v

variable {E : Type u} {U : Type v}

/-- The unquotiented disjoint-union presentation of two nested boxes. -/
noncomputable def nestedSplitGraph (BS BD : FiniteBox E) {nS nD : ℕ}
    (_jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) : LabelledMultigraph :=
  FK.Finite.MarkovFactorization.disjointSum (BD.indexedGraph jD)
    (outsideGraph BS BD)

/-- A geometric small-vertex map and the identity on the outside graph glue
all duplicated vertices to the ordinary large box. -/
noncomputable def nestedGluingMap (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (d : BD.Vertex → BS.Vertex) :
    (nestedSplitGraph BS BD jS jD).Vertex → (BS.indexedGraph jS).Vertex :=
  Sum.elim d id

/-- The nested edge equivalence uses exactly these disjoint-union summands. -/
noncomputable def nestedSplitEdgeEquiv (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) :
    (nestedSplitGraph BS BD jS jD).Edge ≃ (BS.indexedGraph jS).Edge :=
  nestedEdgeEquiv BS BD jS jD hBD

/-- The outside copy alone makes the gluing surjective. -/
theorem nestedGluingMap_surjective (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (d : BD.Vertex → BS.Vertex) :
    Function.Surjective (nestedGluingMap BS BD jS jD d) := by
  intro x
  exact ⟨Sum.inr x, rfl⟩

/-- Global large-box label of a small edge under the canonical nesting. -/
lemma nestedSplitEdgeEquiv_inl_label (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (a : Fin nD) :
    ((jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inl a)) : BS.edges) : E) =
      (jD a : E) := by
  change ((jS (jS.symm
    ((Equiv.Set.sumDiffSubset
      (show (BD.edges : Set E) ⊆ (BS.edges : Set E) from hBD))
        (Sum.inl (jD a)))) : BS.edges) : E) = (jD a : E)
  rw [Equiv.apply_symm_apply, Equiv.Set.sumDiffSubset_apply_inl]

/-- Global large-box label of an added edge under the canonical nesting. -/
lemma nestedSplitEdgeEquiv_inr_label (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (a : (outsideGraph BS BD).Edge) :
    ((jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inr a)) : BS.edges) : E) =
      a.1 := by
  change ((jS (jS.symm
    ((Equiv.Set.sumDiffSubset
      (show (BD.edges : Set E) ⊆ (BS.edges : Set E) from hBD))
        (Sum.inr a))) : BS.edges) : E) = a.1
  rw [Equiv.apply_symm_apply]
  rfl

/-- Small-edge endpoint compatibility is precisely the geometric data needed
for the nested gluing; outside endpoints require no additional assumption. -/
theorem nestedGluing_source (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (d : BD.Vertex → BS.Vertex)
    (hd : ∀ a, d (BD.source (jD a)) = BS.source ⟨(jD a).1, hBD (jD a).2⟩)
    (a : (nestedSplitGraph BS BD jS jD).Edge) :
    nestedGluingMap BS BD jS jD d
        ((nestedSplitGraph BS BD jS jD).source a) =
      (BS.indexedGraph jS).source (nestedSplitEdgeEquiv BS BD jS jD hBD a) := by
  cases a with
  | inl a =>
      change d (BD.source (jD a)) =
        BS.source (jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inl a)))
      have hi : jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inl a)) =
          ⟨(jD a).1, hBD (jD a).2⟩ :=
        Subtype.ext (nestedSplitEdgeEquiv_inl_label BS BD jS jD hBD a)
      rw [hi, hd a]
  | inr a =>
      change BS.source ⟨a.1, a.2.1⟩ =
        BS.source (jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inr a)))
      have hi : jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inr a)) =
          ⟨a.1, a.2.1⟩ :=
        Subtype.ext (nestedSplitEdgeEquiv_inr_label BS BD jS jD hBD a)
      rw [hi]

/-- Target analogue of `nestedGluing_source`. -/
theorem nestedGluing_target (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (d : BD.Vertex → BS.Vertex)
    (hd : ∀ a, d (BD.target (jD a)) = BS.target ⟨(jD a).1, hBD (jD a).2⟩)
    (a : (nestedSplitGraph BS BD jS jD).Edge) :
    nestedGluingMap BS BD jS jD d
        ((nestedSplitGraph BS BD jS jD).target a) =
      (BS.indexedGraph jS).target (nestedSplitEdgeEquiv BS BD jS jD hBD a) := by
  cases a with
  | inl a =>
      change d (BD.target (jD a)) =
        BS.target (jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inl a)))
      have hi : jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inl a)) =
          ⟨(jD a).1, hBD (jD a).2⟩ :=
        Subtype.ext (nestedSplitEdgeEquiv_inl_label BS BD jS jD hBD a)
      rw [hi, hd a]
  | inr a =>
      change BS.target ⟨a.1, a.2.1⟩ =
        BS.target (jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inr a)))
      have hi : jS (nestedSplitEdgeEquiv BS BD jS jD hBD (Sum.inr a)) =
          ⟨a.1, a.2.1⟩ :=
        Subtype.ext (nestedSplitEdgeEquiv_inr_label BS BD jS jD hBD a)
      rw [hi]

/-- Exact FK compatibility of the ordinary nested box with its duplicated
split, using the pullback of any ordinary large-box boundary setoid. -/
theorem map_nestedSplit_fkPMF (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (d : BD.Vertex → BS.Vertex)
    (hds : ∀ a, d (BD.source (jD a)) = BS.source ⟨(jD a).1, hBD (jD a).2⟩)
    (hdt : ∀ a, d (BD.target (jD a)) = BS.target ⟨(jD a).1, hBD (jD a).2⟩)
    (α : BS.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (gluedConfig (nestedSplitEdgeEquiv BS BD jS jD hBD))
        ((nestedSplitGraph BS BD jS jD).fkPMF hq hp₁.le
          (Setoid.comap (nestedGluingMap BS BD jS jD d)
            (BS.indexedBoundary jS α))) =
      (BS.indexedGraph jS).fkPMF hq hp₁.le (BS.indexedBoundary jS α) := by
  exact map_gluedConfig_fkPMF _ _ (nestedGluing_source BS BD jS jD hBD d hds)
    (nestedGluing_target BS BD jS jD hBD d hdt) _ hq hp₀ hp₁
    (nestedGluingMap_surjective BS BD jS jD d)

section Metric

open CurvatureVariance.Infra.Percolation
open FK.Finite.Exploration FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.Sequential FK.Exploration.StoppedInterior
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial
open FK.InfiniteVolume.NestedMetricGeometry.RightExtension
open FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Radial

universe uV

variable {V : Type uV} {Gph : SimpleGraph V}

/-- Inclusion of the vertices of one centered metric box into every larger
centered metric box. -/
noncomputable def metricVertexInclusion [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n) :
    (metricBox hG o r).Vertex → (metricBox hG o n).Vertex :=
  fun x => ⟨x.1, (mem_innerBall hG).2 <|
    ((mem_innerBall hG).1 x.2).trans_le (Nat.add_le_add_right hrn 1)⟩

/-- Inclusion sends a small metric source to the large metric source with the
same global label. -/
lemma metricVertexInclusion_source [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (e : (metricBox hG o r).edges)
    (he : (e.1 : Gph.edgeSet) ∈ (metricBox hG o n).edges) :
    metricVertexInclusion hG o hrn ((metricBox hG o r).source e) =
      (metricBox hG o n).source ⟨e.1, he⟩ := by
  apply Subtype.ext
  rfl

/-- Target version of `metricVertexInclusion_source`. -/
lemma metricVertexInclusion_target [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (e : (metricBox hG o r).edges)
    (he : (e.1 : Gph.edgeSet) ∈ (metricBox hG o n).edges) :
    metricVertexInclusion hG o hrn ((metricBox hG o r).target e) =
      (metricBox hG o n).target ⟨e.1, he⟩ := by
  apply Subtype.ext
  rfl

/-- The split radial small box and the ordinary small metric box have the
same source at the same reindexed global edge. -/
lemma vertexEquiv_smallMetricBox_source [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r : ℕ)
    (a : Fin (Fintype.card (ExternalEdge (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) + Fintype.card (InternalEdge (boxSource hG o r)
          (boxTarget hG o r) (inBall hG o R r)))) :
    vertexEquiv (inBall hG o R r)
        ((smallMetricBox hG o R r).source (smallIndex hG o R r a)) =
      (metricBox hG o r).source (smallIndex hG o R r a) := by
  rw [smallBox_source]
  let a₀ := exteriorFirst a
  change vertexEquiv (inBall hG o R r)
      ((ambientOfSum (splitSource (si hG o R r) (so hG o R r))
        (splitTarget (ti hG o R r) (xo hG o R r))).source a₀) = _
  change vertexEquiv (inBall hG o R r)
      (splitSource (internalSource (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) (externalSource (boxSource hG o r) (boxTarget hG o r)
          (inBall hG o R r)) a₀) = boxSource hG o r (d hG o R r a₀)
  exact vertexEquiv_splitSource (boxSource hG o r) (boxTarget hG o r)
    (inBall hG o R r) a₀

/-- The split radial small box and the ordinary small metric box have the
same target at the same reindexed global edge. -/
lemma vertexEquiv_smallMetricBox_target [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r : ℕ)
    (a : Fin (Fintype.card (ExternalEdge (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) + Fintype.card (InternalEdge (boxSource hG o r)
          (boxTarget hG o r) (inBall hG o R r)))) :
    vertexEquiv (inBall hG o R r)
        ((smallMetricBox hG o R r).target (smallIndex hG o R r a)) =
      (metricBox hG o r).target (smallIndex hG o R r a) := by
  rw [smallBox_target]
  let a₀ := exteriorFirst a
  change vertexEquiv (inBall hG o R r)
      ((ambientOfSum (splitSource (si hG o R r) (so hG o R r))
        (splitTarget (ti hG o R r) (xo hG o R r))).target a₀) = _
  change vertexEquiv (inBall hG o R r)
      (splitTarget (internalTarget (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) (externalTarget (boxSource hG o r) (boxTarget hG o r)
          (inBall hG o R r)) a₀) = boxTarget hG o r (d hG o R r a₀)
  exact vertexEquiv_splitTarget (boxSource hG o r) (boxTarget hG o r)
    (inBall hG o R r) a₀

/-- Canonical small-vertex map for the actual radial nested presentation. -/
noncomputable def radialGluingVertexMap [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n) :
    (smallMetricBox hG o R r).Vertex → (metricBox hG o n).Vertex :=
  fun x => metricVertexInclusion hG o hrn (vertexEquiv (inBall hG o R r) x)

/-- The canonical radial small-vertex map respects every source. -/
lemma radialGluingVertexMap_source [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (a : Fin (Fintype.card (ExternalEdge (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) + Fintype.card (InternalEdge (boxSource hG o r)
          (boxTarget hG o r) (inBall hG o R r)))) :
    radialGluingVertexMap hG o R r n hrn
        ((smallMetricBox hG o R r).source (smallIndex hG o R r a)) =
      (metricBox hG o n).source ⟨(smallIndex hG o R r a).1,
        nested_metricBox_edges hG o hrn (smallIndex hG o R r a).2⟩ := by
  unfold radialGluingVertexMap
  rw [vertexEquiv_smallMetricBox_source]
  exact metricVertexInclusion_source hG o hrn _ _

/-- The canonical radial small-vertex map respects every target. -/
lemma radialGluingVertexMap_target [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (a : Fin (Fintype.card (ExternalEdge (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) + Fintype.card (InternalEdge (boxSource hG o r)
          (boxTarget hG o r) (inBall hG o R r)))) :
    radialGluingVertexMap hG o R r n hrn
        ((smallMetricBox hG o R r).target (smallIndex hG o R r a)) =
      (metricBox hG o n).target ⟨(smallIndex hG o R r a).1,
        nested_metricBox_edges hG o hrn (smallIndex hG o R r a).2⟩ := by
  unfold radialGluingVertexMap
  rw [vertexEquiv_smallMetricBox_target]
  exact metricVertexInclusion_target hG o hrn _ _

/-- Actual radial split of two ordinary centered metric boxes. -/
noncomputable def radialSplitGraph [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (_hrn : r ≤ n) : LabelledMultigraph :=
  nestedSplitGraph (metricBox hG o n) (smallMetricBox hG o R r)
    (edgeIndex _) (smallIndex hG o R r)

/-- Canonical ordinary nested edge labels on the radial split. -/
noncomputable def radialSplitEdgeEquiv [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n) :
    (radialSplitGraph hG o R r n hrn).Edge ≃
      ((metricBox hG o n).indexedGraph (edgeIndex _)).Edge :=
  nestedSplitEdgeEquiv (metricBox hG o n) (smallMetricBox hG o R r)
    (edgeIndex _) (smallIndex hG o R r) (nested_metricBox_edges hG o hrn)

/-- Canonical generally noninjective radial vertex gluing. -/
noncomputable def radialSplitGluingMap [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n) :
    (radialSplitGraph hG o R r n hrn).Vertex → (metricBox hG o n).Vertex :=
  nestedGluingMap (metricBox hG o n) (smallMetricBox hG o R r)
    (edgeIndex _) (smallIndex hG o R r) (radialGluingVertexMap hG o R r n hrn)

/-- The source-faithful law: pull an arbitrary ordinary large-box boundary
setoid back along the actual vertex gluing. -/
@[instance_reducible]
noncomputable def radialSplitSourceLaw [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition) :
    (radialSplitGraph hG o R r n hrn).BoundaryPartition :=
  Setoid.comap (radialSplitGluingMap hG o R r n hrn)
    ((metricBox hG o n).indexedBoundary (edgeIndex _) α)

/-- Every two copies of one ordinary vertex are related by the radial source
law.  In particular, its cross-summand relations need not be false. -/
lemma radialSplitSourceLaw_cross [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (u : (smallMetricBox hG o R r).Vertex) (v : (metricBox hG o n).Vertex)
    (huv : radialGluingVertexMap hG o R r n hrn u = v) :
    (radialSplitSourceLaw hG o R r n hrn α).r (Sum.inl u) (Sum.inr v) := by
  apply comap_gluing_relation_of_eq
  exact huv

/-- **Ordinary radial FK compatibility.** The canonical nested edge labels,
vertex gluing, and pullback source law all use actual metric boxes.  There is
no assumed vertex equivalence and no no-cross boundary restriction. -/
theorem map_radialSplit_fkPMF [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (gluedConfig (radialSplitEdgeEquiv hG o R r n hrn))
        ((radialSplitGraph hG o R r n hrn).fkPMF hq hp₁.le
          (radialSplitSourceLaw hG o R r n hrn α)) =
      ((metricBox hG o n).indexedGraph (edgeIndex _)).fkPMF hq hp₁.le
        ((metricBox hG o n).indexedBoundary (edgeIndex _) α) := by
  exact map_nestedSplit_fkPMF (metricBox hG o n) (smallMetricBox hG o R r)
    (edgeIndex _) (smallIndex hG o R r) (nested_metricBox_edges hG o hrn)
    (radialGluingVertexMap hG o R r n hrn)
    (radialGluingVertexMap_source hG o R r n hrn)
    (radialGluingVertexMap_target hG o R r n hrn) α hq hp₀ hp₁

/-- Read a glued radial configuration in the actual large metric-box edge
coordinates. -/
noncomputable def radialSplitConfigToBox [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n) :
    (radialSplitGraph hG o R r n hrn).Configuration →
      (metricBox hG o n).Interior :=
  (metricBox hG o n).reindex (edgeIndex _) ∘
    gluedConfig (radialSplitEdgeEquiv hG o R r n hrn)

/-- Exact ordinary unindexed FK law of the source-faithful radial split. -/
theorem map_radialSplitConfigToBox_fkPMF [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (radialSplitConfigToBox hG o R r n hrn)
        ((radialSplitGraph hG o R r n hrn).fkPMF hq hp₁.le
          (radialSplitSourceLaw hG o R r n hrn α)) =
      (metricBox hG o n).graph.fkPMF hq hp₁.le α := by
  unfold radialSplitConfigToBox
  rw [← PMF.map_comp, map_radialSplit_fkPMF hG o R r n hrn α hq hp₀ hp₁]
  exact (metricBox hG o n).map_reindex_fkPMF (edgeIndex _) α hq hp₀ hp₁

/-- Exact finite-cylinder compatibility with the ordinary global finite-volume
law.  This is a probability identity, not a claim of `hgood` or an arm bound. -/
theorem radialSplit_real_boxCylinder [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset Gph.edgeSet) (S : Set (J → Bool))
    (hJ : J ⊆ (metricBox hG o n).edges) :
    ((radialSplitGraph hG o R r n hrn).fkPMF hq hp₁.le
        (radialSplitSourceLaw hG o R r n hrn α)).toMeasure.real
        (radialSplitConfigToBox hG o R r n hrn ⁻¹'
          (metricBox hG o n).boxCylinder J S hJ) =
      ((metricBox hG o n).finiteVolumeLaw hq hp₁.le α :
        Measure (Configuration Gph.edgeSet)).real (cylinder J S) := by
  rw [(metricBox hG o n).finiteVolumeLaw_real_boxCylinder hq hp₁.le α J S hJ]
  apply congrArg ENNReal.toReal
  have hmap := congrArg PMF.toMeasure
    (map_radialSplitConfigToBox_fkPMF hG o R r n hrn α hq hp₀ hp₁)
  rw [← PMF.toMeasure_map _ _ (by fun_prop)] at hmap
  rw [← hmap]
  exact (Measure.map_apply (by fun_prop) MeasurableSet.of_discrete).symm

end Metric

end FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing

#print axioms FK.Finite.LabelledMultigraph.VertexGluing.reachable_source_iff_target
#print axioms FK.Finite.LabelledMultigraph.VertexGluing.connectedComponentEquiv
#print axioms FK.Finite.LabelledMultigraph.VertexGluing.componentCount_gluing
#print axioms FK.Finite.LabelledMultigraph.VertexGluing.fkWeight_gluing
#print axioms FK.Finite.LabelledMultigraph.VertexGluing.map_gluedConfig_fkPMF
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.nestedGluing_source
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.nestedGluing_target
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.map_nestedSplit_fkPMF

#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion_source
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion_target
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.vertexEquiv_smallMetricBox_source
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.vertexEquiv_smallMetricBox_target
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialGluingVertexMap_source
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialGluingVertexMap_target
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplitSourceLaw_cross
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.map_radialSplit_fkPMF
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.map_radialSplitConfigToBox_fkPMF
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplit_real_boxCylinder

#print axioms FK.Finite.LabelledMultigraph.VertexGluing.gluedConfig
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.nestedSplitGraph
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.nestedGluingMap
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.nestedSplitEdgeEquiv
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialGluingVertexMap
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplitGraph
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplitEdgeEquiv
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplitGluingMap
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplitSourceLaw
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing.radialSplitConfigToBox
