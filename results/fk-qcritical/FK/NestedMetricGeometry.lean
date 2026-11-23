import FK.NestedFiniteAssembly
import FK.ConventionTransport
import FK.MaximalStrata

/-!
# Canonical metric geometry for the nested finite assembly

This module constructs finite labelled boxes from metric balls of a connected
locally finite simple graph.  It also supplies the canonical edge split of two
nested boxes and proves the exact finite-support realization of the
`farConnection` error event.  No maximal-stratum or good-intersection identity
is asserted here.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The graph edges used by the radius-`n` arm event, as a finite set. -/
noncomputable def metricEdges [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    Finset G.edgeSet :=
  (finite_innerEdges hG o n).toFinset

@[simp] lemma mem_metricEdges [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ)
    (e : G.edgeSet) :
    e ∈ metricEdges hG o n ↔ e.1 ∈ innerEdges G o n := by
  exact Set.Finite.mem_toFinset _

/-- Both endpoints of an edge with one endpoint in the open radius-`n` ball
lie in the open radius-`n+1` ball. -/
lemma dist_lt_succ_of_mem_of_mem_innerEdges [G.LocallyFinite] (hG : G.Connected)
    {o : V} {n : ℕ} {e : G.edgeSet} (he : e.1 ∈ innerEdges G o n)
    {v : V} (hv : v ∈ e.1) : G.dist o v < n + 1 := by
  have hpair : s(e.1.out.1, e.1.out.2) = e.1 := by
    rw [Sym2.mk, e.1.out_eq]
  rw [← hpair] at he hv
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet, hpair]
    exact e.2
  simp only [innerEdges, Set.mem_ofPred_eq, Sym2.mem_iff] at he hv
  obtain ⟨x, hx, hxn⟩ := he
  rcases hx with rfl | rfl <;> rcases hv with rfl | rfl
  · omega
  · exact (dist_le_of_adj_of_dist_lt hG hadj hxn).trans_lt (Nat.lt_succ_self n)
  · exact (dist_le_of_adj_of_dist_lt hG hadj.symm hxn).trans_lt (Nat.lt_succ_self n)
  · omega

/-- A genuine finite labelled box on all edges having an endpoint at graph
distance `< n`.  Its vertices are the open ball of radius `n+1`. -/
noncomputable def metricBox [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    FiniteBox G.edgeSet where
  Vertex := innerBall hG o (n + 1)
  edges := metricEdges hG o n
  source e := ⟨e.1.1.out.1, (mem_innerBall hG).2 <|
    dist_lt_succ_of_mem_of_mem_innerEdges hG
      ((mem_metricEdges hG o n e.1).1 e.2) (Sym2.out_fst_mem _)⟩
  target e := ⟨e.1.1.out.2, (mem_innerBall hG).2 <|
    dist_lt_succ_of_mem_of_mem_innerEdges hG
      ((mem_metricEdges hG o n e.1).1 e.2) (Sym2.out_snd_mem _)⟩

@[simp] lemma metricBox_edges [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    (metricBox hG o n).edges = metricEdges hG o n := rfl

/-- Metric boxes use the original global vertices and have exactly the global
edge endpoints. -/
noncomputable def metricBoxData [G.LocallyFinite] (hG : G.Connected) (o : V) :
    FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData G
      (fun n => metricBox hG o n) where
  vertex _ x := x.1
  endpoint _ e := e.1.1.out_eq

lemma metricBoxData_vertex_injective [G.LocallyFinite] (hG : G.Connected) (o : V) (n : ℕ) :
    Function.Injective ((metricBoxData hG o).vertex n) := by
  intro x y hxy
  exact Subtype.ext hxy

lemma monotone_metricEdges [G.LocallyFinite] (hG : G.Connected) (o : V) :
    Monotone (metricEdges hG o) := by
  intro m n hmn
  apply Set.Finite.toFinset_mono
  rintro e ⟨x, hx, hxn⟩
  exact ⟨x, hx, hxn.trans_le hmn⟩

/-- The metric boxes form an actual finite-box exhaustion of a connected
locally finite graph. -/
noncomputable def metricBoxExhaustion [G.LocallyFinite] (hG : G.Connected) (o : V) :
    BoxExhaustion G.edgeSet where
  box n := metricBox hG o n
  monotone := monotone_metricEdges hG o
  covers e := by
    refine ⟨G.dist o e.1.out.1 + 1, (Set.Finite.mem_toFinset _).2 ?_⟩
    exact ⟨e.1.out.1, Sym2.out_fst_mem _, Nat.lt_succ_self _⟩

/-- The outside graph on the literal labelled-edge difference of two boxes. -/
noncomputable def outsideGraph {E : Type*} (BS BD : FiniteBox E) : LabelledMultigraph where
  Vertex := BS.Vertex
  Edge := ↥((BS.edges : Set E) \ (BD.edges : Set E))
  source e := BS.source ⟨e.1, e.2.1⟩
  target e := BS.target ⟨e.1, e.2.1⟩

/-- The canonical `EΔ ⊕ EO ≃ EΣ` equivalence for nested finite boxes. -/
noncomputable def nestedEdgeEquiv {E : Type*} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) :
    (BD.indexedGraph jD).Edge ⊕ (outsideGraph BS BD).Edge ≃ (BS.indexedGraph jS).Edge :=
  (Equiv.sumCongr jD (Equiv.refl _)).trans <|
    (Equiv.Set.sumDiffSubset (show (BD.edges : Set E) ⊆ (BS.edges : Set E) from hBD)).trans
      jS.symm

/-- The canonical split agrees on every common global edge label. -/
lemma nestedEdgeEquiv_inl {E : Type*} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (J : Finset E)
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges) (i : J) :
    nestedEdgeEquiv BS BD jS jD hBD
        (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) = jS.symm ⟨i.1, hJS i.2⟩ := by
  change jS.symm ((Equiv.Set.sumDiffSubset _) (Sum.inl
    (jD (jD.symm ⟨i.1, hJD i.2⟩)))) = _
  simp only [Equiv.apply_symm_apply]
  rw [Equiv.Set.sumDiffSubset_apply_inl]

/-- An event read in a box after closing every exterior coordinate. -/
def closedLocalEvent {E : Type*} (B : FiniteBox E) (U : Set (Configuration E)) :
    Set B.Interior :=
  (fun η => B.glue (B.closedExterior, η)) ⁻¹' U

/-- Finite-coordinate dependence gives the exact global/local realization
required by the nested assembly's `hU`. -/
lemma preimage_interiorRestriction_closedLocalEvent {E : Type*} (B : FiniteBox E)
    (U : Set (Configuration E)) (hU : FKLimit.DependsOnCoordinates U B.edges) :
    B.interiorRestriction ⁻¹' closedLocalEvent B U = U := by
  ext ω
  change (B.glue (B.closedExterior, B.interiorRestriction ω) ∈ U) ↔ ω ∈ U
  apply hU
  intro e he
  simp [FiniteBox.glue, FiniteBox.interiorRestriction, FiniteBox.splitEquiv,
    FiniteBox.split, he]

/-- `farConnection` up to radius `r` depends only on the metric-box edges when
all its roots start strictly inside that radius.  The proof truncates a walk
at its first radius-`r` vertex. -/
theorem farConnection_dependsOnCoordinates_metricBox [G.LocallyFinite]
    (hG : G.Connected) (roots : Finset V) (o : V) (r : ℕ)
    (hroots : ∀ a ∈ roots, G.dist o a < r) :
    FKLimit.DependsOnCoordinates (NestedAssembly.farConnection G roots o r)
      (metricBox hG o r).edges := by
  intro ω η hωη
  constructor
  · rintro ⟨a, ha, w, hw, p, hp⟩
    obtain ⟨w', hw', hc⟩ := exists_dist_eq_openConnected hG ω o r p hp
      (hroots a ha) hw
    refine ⟨a, ha, w', hw'.ge, (hc.congr ?_).mono_edges (Set.subset_univ _)⟩
    intro e he
    exact hωη e ((mem_metricEdges hG o r e).2 he)
  · rintro ⟨a, ha, w, hw, p, hp⟩
    obtain ⟨w', hw', hc⟩ := exists_dist_eq_openConnected hG η o r p hp
      (hroots a ha) hw
    refine ⟨a, ha, w', hw'.ge, (hc.congr ?_).mono_edges (Set.subset_univ _)⟩
    intro e he
    exact (hωη e ((mem_metricEdges hG o r e).2 he)).symm

/-- Exact local/global arm realization on a metric box. -/
theorem preimage_interiorRestriction_closedLocalEvent_farConnection [G.LocallyFinite]
    (hG : G.Connected) (roots : Finset V) (o : V) (r : ℕ)
    (hroots : ∀ a ∈ roots, G.dist o a < r) :
    (metricBox hG o r).interiorRestriction ⁻¹'
      closedLocalEvent (metricBox hG o r) (NestedAssembly.farConnection G roots o r) =
        NestedAssembly.farConnection G roots o r := by
  exact preimage_interiorRestriction_closedLocalEvent _ _ <|
    farConnection_dependsOnCoordinates_metricBox hG roots o r hroots

/-- Radius of one labelled edge from a center, using its canonical unordered-
pair representative. -/
noncomputable def edgeRadius (G : SimpleGraph V) (o : V) (e : G.edgeSet) : ℕ :=
  max (G.dist o e.1.out.1) (G.dist o e.1.out.2)

/-- A width covering a finite observation base and a finite root set. -/
noncomputable def dataWidth (G : SimpleGraph V) (o : V) (J : Finset G.edgeSet)
    (roots : Finset V) : ℕ :=
  max (J.sup (edgeRadius G o)) (roots.sup (G.dist o)) + 1

lemma dist_lt_dataWidth (G : SimpleGraph V) (o : V) (J : Finset G.edgeSet)
    {roots : Finset V} {a : V} (ha : a ∈ roots) :
    G.dist o a < dataWidth G o J roots := by
  have h := (Finset.le_sup (f := G.dist o) ha).trans
    (le_max_right (J.sup (edgeRadius G o)) (roots.sup (G.dist o)))
  unfold dataWidth
  omega

lemma dist_le_dataWidth (G : SimpleGraph V) (o : V) (J : Finset G.edgeSet)
    {roots : Finset V} {a : V} (ha : a ∈ roots) :
    G.dist o a ≤ dataWidth G o J roots := by
  exact (dist_lt_dataWidth G o J ha).le

lemma dist_lt_add_dataWidth (G : SimpleGraph V) (o : V) (J : Finset G.edgeSet)
    {roots : Finset V} {a : V} (ha : a ∈ roots) (m : ℕ) :
    G.dist o a < m + dataWidth G o J roots := by
  have h := dist_lt_dataWidth G o J ha
  omega

lemma subset_metricBox_add_dataWidth [G.LocallyFinite] (hG : G.Connected)
    (o : V) (J : Finset G.edgeSet) (roots : Finset V) (m : ℕ) :
    J ⊆ (metricBox hG o (m + dataWidth G o J roots)).edges := by
  intro e he
  apply (mem_metricEdges hG o (m + dataWidth G o J roots) e).2
  refine ⟨e.1.out.1, Sym2.out_fst_mem _, ?_⟩
  have h := (Finset.le_sup (f := edgeRadius G o) he).trans
    (le_max_left (J.sup (edgeRadius G o)) (roots.sup (G.dist o)))
  have hfst : G.dist o e.1.out.1 ≤ edgeRadius G o e := le_max_left _ _
  unfold dataWidth
  omega

/-- Once `n` reaches the smaller scale, both the fixed observation base and
all smaller metric-box edges lie in the larger box. -/
lemma nested_metricBox_edges [G.LocallyFinite] (hG : G.Connected) (o : V)
    {r n : ℕ} (hrn : r ≤ n) :
    (metricBox hG o r).edges ⊆ (metricBox hG o n).edges := by
  exact monotone_metricEdges hG o hrn

end FK.InfiniteVolume.NestedMetricGeometry


namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly

universe u

/-- The canonical finite indexing of a box's labelled edges. -/
noncomputable def edgeIndex {E : Type*} (B : FiniteBox E) :
    Fin (Fintype.card B.edges) ≃ B.edges :=
  (Fintype.equivFin B.edges).symm

/-- Canonical nested-split form of the integrated finite-box estimate.  The
edge equivalence, its common-label identity, and the global/local arm identity
are constructed here.  `hgood` and the exceptional-event inclusion are exactly
the remaining non-geometric inputs. -/
theorem finiteBox_cylinder_abs_sub_le_farConnection_canonical_of_good
    {V : Type u} {G : SimpleGraph V} (BS BD : FiniteBox G.edgeSet)
    (hBD : BD.edges ⊆ BS.edges)
    (α : BS.BoundaryPartition) (β : BD.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool))
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges)
    (roots : Finset V) (center : V) (r : ℕ)
    (hdep : FKLimit.DependsOnCoordinates
      (NestedAssembly.farConnection G roots center r) BS.edges)
    (C : Set (BD.indexedGraph (edgeIndex BD)).Configuration)
    (hgood :
      let e := nestedEdgeEquiv BS BD (edgeIndex BS) (edgeIndex BD) hBD
      let t := fkNestedOrderedTriple
        (fun i => BS.source (edgeIndex BS i)) (fun i => BS.target (edgeIndex BS i))
        (fun i => BD.source (edgeIndex BD i)) (fun i => BD.target (edgeIndex BD i))
        (outsideGraph BS BD) e (BS.indexedBoundary (edgeIndex BS) α)
        (BD.indexedBoundary (edgeIndex BD) β) hq hp₀ hp₁
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹'
            (BS.reindex (edgeIndex BS) ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹'
            (BS.reindex (edgeIndex BS) ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (hD :
      let e := nestedEdgeEquiv BS BD (edgeIndex BS) (edgeIndex BD) hBD
      (restrictΔ e ⁻¹' C)ᶜ ⊆ BS.reindex (edgeIndex BS) ⁻¹'
        closedLocalEvent BS (NestedAssembly.farConnection G roots center r)) :
    |(BS.finiteVolumeLaw hq hp₁.le α : Measure (Configuration G.edgeSet)).real
          (cylinder J S) -
        (BD.finiteVolumeLaw hq hp₁.le β : Measure (Configuration G.edgeSet)).real
          (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G roots center r) := by
  let e := nestedEdgeEquiv BS BD (edgeIndex BS) (edgeIndex BD) hBD
  have he : ∀ i : J,
      e (Sum.inl ((edgeIndex BD).symm ⟨i.1, hJD i.2⟩)) =
        (edgeIndex BS).symm ⟨i.1, hJS i.2⟩ := by
    intro i
    exact nestedEdgeEquiv_inl BS BD (edgeIndex BS) (edgeIndex BD) hBD J hJS hJD i
  have hU : BS.interiorRestriction ⁻¹'
      closedLocalEvent BS (NestedAssembly.farConnection G roots center r) =
        NestedAssembly.farConnection G roots center r :=
    preimage_interiorRestriction_closedLocalEvent BS _ hdep
  exact finiteBox_cylinder_abs_sub_le_farConnection_of_good
    BS BD (edgeIndex BS) (edgeIndex BD) (outsideGraph BS BD) e α β hq hp₀ hp₁
    J S hJS hJD he C
    (closedLocalEvent BS (NestedAssembly.farConnection G roots center r))
    roots center r hU hgood hD

end FK.InfiniteVolume.NestedMetricGeometry


namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The edge equivalence between two metric scales, the smaller one first. -/
noncomputable def metricNestedEquiv [G.LocallyFinite] (hG : G.Connected) (o : V)
    {r n : ℕ} (hrn : r ≤ n) :=
  nestedEdgeEquiv (metricBox hG o n) (metricBox hG o r)
    (edgeIndex _) (edgeIndex _) (nested_metricBox_edges hG o hrn)

/-- A finite base covered by the canonical width is contained in the smaller
metric scale `m + width`. -/
lemma base_subset_smaller_metricBox [G.LocallyFinite] (hG : G.Connected)
    (o : V) (J : Finset G.edgeSet) (roots : Finset V) (m : ℕ) :
    J ⊆ (metricBox hG o (m + dataWidth G o J roots)).edges :=
  subset_metricBox_add_dataWidth hG o J roots m

/-- The same finite base is contained in every larger metric scale. -/
lemma base_subset_larger_metricBox [G.LocallyFinite] (hG : G.Connected)
    (o : V) (J : Finset G.edgeSet) (roots : Finset V) (m : ℕ) {n : ℕ}
    (hrn : m + dataWidth G o J roots ≤ n) :
    J ⊆ (metricBox hG o n).edges := by
  exact (base_subset_smaller_metricBox hG o J roots m).trans
    (nested_metricBox_edges hG o hrn)

/-- Root localization needed by the larger metric box. -/
lemma roots_lt_larger_metricBox [G.LocallyFinite] (_hG : G.Connected)
    (o : V) (J : Finset G.edgeSet) (roots : Finset V) (m : ℕ) {n : ℕ}
    (hrn : m + dataWidth G o J roots ≤ n) :
    ∀ a ∈ roots, G.dist o a < n := by
  intro a ha
  exact (dist_lt_add_dataWidth G o J ha m).trans_le hrn

/-- The actual nested FK/FK/Bernoulli triple at two ordered metric scales. -/
noncomputable def metricNestedTriple [G.LocallyFinite] (hG : G.Connected) (o : V)
    {r n : ℕ} (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (β : (metricBox hG o r).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :=
  fkNestedOrderedTriple
    (fun i => (metricBox hG o n).source (edgeIndex _ i))
    (fun i => (metricBox hG o n).target (edgeIndex _ i))
    (fun i => (metricBox hG o r).source (edgeIndex _ i))
    (fun i => (metricBox hG o r).target (edgeIndex _ i))
    (outsideGraph (metricBox hG o n) (metricBox hG o r))
    (metricNestedEquiv hG o hrn)
    ((metricBox hG o n).indexedBoundary (edgeIndex _) α)
    ((metricBox hG o r).indexedBoundary (edgeIndex _) β) hq hp₀ hp₁

end FK.InfiniteVolume.NestedMetricGeometry


namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Finite estimate at the canonical two metric scales.  The smaller scale is
`m + dataWidth`, so every finite base is covered and every root is strictly
inside.  Every larger scale `n` supplies the outer box. -/
theorem metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool)) (roots : Finset V) (m n : ℕ)
    (hrn : m + dataWidth G o J roots ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (β : (metricBox hG o (m + dataWidth G o J roots)).BoundaryPartition)
    (C : Set ((metricBox hG o
      (m + dataWidth G o J roots)).indexedGraph (edgeIndex _)).Configuration)
    (hgood :
      let t := metricNestedTriple hG o hrn α β hq hp₀ hp₁
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J roots m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J roots m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (hD :
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      (restrictΔ e ⁻¹' C)ᶜ ⊆ BS.reindex (edgeIndex BS) ⁻¹'
        closedLocalEvent BS
          (NestedAssembly.farConnection G roots o (m + dataWidth G o J roots))) :
    |((metricBox hG o n).finiteVolumeLaw hq hp₁.le α :
          Measure (Configuration G.edgeSet)).real (cylinder J S) -
        ((metricBox hG o (m + dataWidth G o J roots)).finiteVolumeLaw hq hp₁.le β :
          Measure (Configuration G.edgeSet)).real (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G roots o (m + dataWidth G o J roots)) := by
  have hdep : FKLimit.DependsOnCoordinates
      (NestedAssembly.farConnection G roots o (m + dataWidth G o J roots))
        (metricBox hG o n).edges :=
    (farConnection_dependsOnCoordinates_metricBox hG roots o
      (m + dataWidth G o J roots) (fun a ha => dist_lt_add_dataWidth G o J ha m)).mono
        (nested_metricBox_edges hG o hrn)
  exact finiteBox_cylinder_abs_sub_le_farConnection_canonical_of_good
    (metricBox hG o n) (metricBox hG o (m + dataWidth G o J roots))
    (nested_metricBox_edges hG o hrn) α β hq hp₀ hp₁ J S
    (base_subset_larger_metricBox hG o J roots m hrn)
    (base_subset_smaller_metricBox hG o J roots m)
    roots o (m + dataWidth G o J roots) hdep C hgood hD

end FK.InfiniteVolume.NestedMetricGeometry


namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly
open Topology

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Nested arm assembly with a base-dependent reindexing of the second weakly
convergent sequence.  For each fixed cylinder base `K`, only convergence of
`d K` to infinity is needed. -/
theorem probabilityMeasure_eq_of_nested_finiteRootArm_bounds_reindexed
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μs νs : ℕ → ProbabilityMeasure (G.edgeSet → Bool))
    (μ ν ρ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V) (d : Finset G.edgeSet → ℕ → ℕ)
    (hd : ∀ (K : Finset G.edgeSet), Tendsto (d K) atTop atTop)
    (hbound : ∀ (K : Finset G.edgeSet) (S : Set (K → Bool)) (m : ℕ),
      ∀ᶠ n in atTop,
        |(μs n : Measure (G.edgeSet → Bool)).real (cylinder K S) -
          (νs (d K m) : Measure (G.edgeSet → Bool)).real (cylinder K S)| ≤
        (ρ : Measure (G.edgeSet → Bool)).real (finiteRootArms G (roots K) m)) :
    μ = ν := by
  apply Subtype.ext
  apply FKModel.measure_ext_of_eq_on_boolCylinders
    (μ : Measure (G.edgeSet → Bool)) (ν : Measure (G.edgeSet → Bool))
  intro K S
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  apply FKModel.eq_of_tendsto_of_eventually_abs_sub_le
    ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto μs μ).mp hμ K S)
    (((tendsto_probabilityMeasure_iff_cylinder_real_tendsto νs ν).mp hν K S).comp
      (hd K))
    (tendsto_measureReal_finiteRootArms_of_ae_nonPercolating hG
      (ρ : Measure (G.edgeSet → Bool)) (roots K) hρ)
  exact hbound K S

/-- Two FK weak limits on the same centered metric exhaustion, with arbitrary
boundary sequences, agree if the actual finite coupling's two remaining
inputs are supplied at every nested pair of scales.  All box construction,
base containment, edge compatibility, root widths, arm realization and
eventual index selection are proved here.  The displayed `hgood` and `hD` are
explicitly the remaining stochastic/maximal-stratum obligations; this is not
an unconditional strong-uniqueness theorem. -/
theorem eq_of_isFKLimit_metricBox_of_nested_good
    [Countable V] [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α β : ∀ n, (metricBox hG o n).BoundaryPartition)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le α μ)
    (hν : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le β ν)
    (hzero : ∀ x, percolationProb G x
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)) = 0)
    (roots : Finset G.edgeSet → Finset V)
    (C : ∀ (J : Finset G.edgeSet) (m : ℕ),
      Set ((metricBox hG o (m + dataWidth G o J (roots J))).indexedGraph
        (edgeIndex _)).Configuration)
    (hgood : ∀ (J : Finset G.edgeSet) (S : Set (J → Bool)) (m n : ℕ)
      (hrn : m + dataWidth G o J (roots J) ≤ n),
      let t := metricNestedTriple hG o hrn (α n)
        (β (m + dataWidth G o J (roots J))) hq hp₀ hp₁
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J (roots J) m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C J m)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J (roots J) m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C J m)))
    (hD : ∀ (J : Finset G.edgeSet) (m n : ℕ)
      (hrn : m + dataWidth G o J (roots J) ≤ n),
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      (restrictΔ e ⁻¹' C J m)ᶜ ⊆ BS.reindex (edgeIndex BS) ⁻¹'
        closedLocalEvent BS
          (NestedAssembly.farConnection G (roots J) o
            (m + dataWidth G o J (roots J)))) :
    μ = ν := by
  let ρ : ProbabilityMeasure (G.edgeSet → Bool) :=
    ⟨percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)),
      inferInstance⟩
  refine probabilityMeasure_eq_of_nested_finiteRootArm_bounds_reindexed hG
    (fun n => (metricBox hG o n).finiteVolumeLaw hq hp₁.le (α n))
    (fun n => (metricBox hG o n).finiteVolumeLaw hq hp₁.le (β n)) μ ν ρ
    hμ hν ?_ roots (fun J m => m + dataWidth G o J (roots J)) ?_ ?_
  · change ∀ᵐ ω ∂(percolation G
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))),
      ω ∈ FK.NonPercolating G
    exact NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero _ hzero
  · intro J
    exact tendsto_add_atTop_nat (dataWidth G o J (roots J))
  · intro J S m
    filter_upwards [eventually_ge_atTop (m + dataWidth G o J (roots J))] with n hn
    exact (metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le
      hG o hq hp₀ hp₁ J S (roots J) m n hn (α n)
      (β (m + dataWidth G o J (roots J))) (C J m)
      (hgood J S m n hn) (hD J m n hn)).trans <|
        measureReal_mono
          (NestedAssembly.farConnection_add_subset_finiteRootArms hG (roots J) o
            (dataWidth G o J (roots J)) m (fun a ha => dist_le_dataWidth G o J ha))
          (measure_ne_top _ _)

end FK.InfiniteVolume.NestedMetricGeometry

namespace FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata FK.Exploration.NestedFiniteCoupling

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-- An exact labelled map from a finite graph's open paths to a global simple
graph.  It records endpoint equality and openness of the corresponding global
label, not a reachability conclusion. -/
structure LabelledOpenPathMap (H : LabelledMultigraph) (G : SimpleGraph V)
    (ρ : H.Configuration) (ω : G.edgeSet → Bool) where
  vertex : H.Vertex → V
  edge : H.Edge → G.edgeSet
  endpoint : ∀ e, s(vertex (H.source e), vertex (H.target e)) = (edge e).1
  isOpen : ∀ e, ρ e = true → ω (edge e) = true

namespace LabelledOpenPathMap

variable {H : LabelledMultigraph} {ρ : H.Configuration} {ω : G.edgeSet → Bool}

/-- One free-boundary adjacency transports to one actual global open edge. -/
lemma openConnected_of_free_adj (M : LabelledOpenPathMap H G ρ ω) {x y : H.Vertex}
    (hxy : (H.connectionGraph H.freeBoundary ρ).Adj x y) :
    OpenConnected G ω Set.univ (M.vertex x) (M.vertex y) := by
  rcases hxy.2 with hfree | ⟨e, he, hjoin⟩
  · exact (hxy.1 hfree).elim
  · rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hend := M.endpoint e
      rw [hs, ht] at hend
      have hadj : G.Adj (M.vertex x) (M.vertex y) := by
        rw [← SimpleGraph.mem_edgeSet, hend]
        exact (M.edge e).2
      apply OpenConnected.of_adj hadj (Set.mem_univ _)
      rw [show (⟨s(M.vertex x, M.vertex y), hadj⟩ : G.edgeSet) = M.edge e from
        Subtype.ext hend]
      exact M.isOpen e he
    · have hend := M.endpoint e
      rw [hs, ht] at hend
      have hend' : s(M.vertex x, M.vertex y) = (M.edge e).1 := Sym2.eq_swap.trans hend
      have hadj : G.Adj (M.vertex x) (M.vertex y) := by
        rw [← SimpleGraph.mem_edgeSet, hend']
        exact (M.edge e).2
      apply OpenConnected.of_adj hadj (Set.mem_univ _)
      rw [show (⟨s(M.vertex x, M.vertex y), hadj⟩ : G.edgeSet) = M.edge e from
        Subtype.ext hend']
      exact M.isOpen e he

/-- Free-boundary reachability transports to an actual global open path. -/
theorem openConnected_of_reachable (M : LabelledOpenPathMap H G ρ ω) {x y : H.Vertex}
    (hxy : (H.connectionGraph H.freeBoundary ρ).Reachable x y) :
    OpenConnected G ω Set.univ (M.vertex x) (M.vertex y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact OpenConnected.refl _ _ _
  | tail _ ha ih => exact ih.trans (M.openConnected_of_free_adj ha)

end LabelledOpenPathMap

/-- Failure of the actual maximal split stratum produces a left vertex openly
reachable from the right summand. -/
lemma exists_left_right_reachable_of_not_mem_maximalSplitStratum
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool) (hρ : ρ ∉ maximalSplitStratum si ti so xo) :
    ∃ u k, ((ambientOfSum (splitSource si so) (splitTarget ti xo)).openGraph
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary ρ).Reachable
        (Sum.inr k) (Sum.inl u) := by
  let H := ambientOfSum (splitSource si so) (splitTarget ti xo)
  have hex : ∃ u, Sum.inl u ∈ H.outerRegion H.freeBoundary (Set.range Sum.inr) ρ := by
    by_contra hn
    push Not at hn
    apply hρ
    change H.outerRegion H.freeBoundary (Set.range Sum.inr) ρ = Set.range Sum.inr
    apply Set.Subset.antisymm
    · intro x hx
      cases x with
      | inl u => exact (hn u hx).elim
      | inr k => exact ⟨k, rfl⟩
    · exact subset_closedRegion
  obtain ⟨u, hu⟩ := hex
  obtain ⟨b, hb, hbu⟩ := mem_outerRegion_iff.mp hu
  obtain ⟨k, rfl⟩ := hb
  exact ⟨u, k, hbu⟩

/-- **Exceptional maximal-stratum configurations yield a metric arm.**  The
finite graph map is explicit data.  Every left vertex maps into the prescribed
finite roots, and every right vertex maps outside the radius `r`. -/
theorem mem_farConnection_of_not_mem_maximalSplitStratum
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool) (ω : G.edgeSet → Bool)
    (M : LabelledOpenPathMap
      (ambientOfSum (splitSource si so) (splitTarget ti xo)) G ρ ω)
    (roots : Finset V) (o : V) (r : ℕ)
    (hleft : ∀ u, M.vertex (Sum.inl u) ∈ roots)
    (hfar : ∀ k, r ≤ G.dist o (M.vertex (Sum.inr k)))
    (hρ : ρ ∉ maximalSplitStratum si ti so xo) :
    ω ∈ NestedAssembly.farConnection G roots o r := by
  obtain ⟨u, k, hk⟩ := exists_left_right_reachable_of_not_mem_maximalSplitStratum
    si ti so xo ρ hρ
  refine ⟨M.vertex (Sum.inl u), hleft u, M.vertex (Sum.inr k), hfar k, ?_⟩
  exact ConventionGeometry.openConnected_symm (M.openConnected_of_reachable hk)

/-- The canonical path map induced by a split presentation of the smaller
indexed graph.  Its vertex map and endpoint identity are geometric data.  Its
open-edge property is proved from the nested common-label identity. -/
noncomputable def nestedOpenPathMap
    {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (z : (BS.indexedGraph jS).Configuration)
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1) :
    LabelledOpenPathMap
      (ambientOfSum (splitSource si so) (splitTarget ti xo)) G
      ((restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z) ∘ d)
      (BS.glue (BS.closedExterior, BS.reindex jS z)) where
  vertex := f
  edge a := (jD (d a)).1
  endpoint := hend
  isOpen := by
    intro (a : Fin m ⊕ Fin k) ha
    change restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z (d a) = true at ha
    have he := nestedEdgeEquiv_inl BS BD jS jD hBD BD.edges hBD (Subset.rfl)
      (jD (d a))
    simp only [FiniteBox.glue]
    split_ifs with hbox
    · change z (jS.symm ⟨(jD (d a)).1, hbox⟩) = true
      rw [← he]
      simpa only [restrictΔ, Subtype.coe_eta, Equiv.symm_apply_apply] using ha
    · exact (hbox (hBD (jD (d a)).2)).elim

/-- The actual exceptional set pulled back from `maximalSplitStratum` is
contained in the closed-exterior realization of `farConnection`.  This proves
the nested assembly's `hD`; `hend`, `hleft` and `hfar` are finite geometric
certificate data rather than the desired inclusion. -/
theorem bad_maximalSplit_subset_closedLocalEvent
    {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1)
    (roots : Finset V) (o : V) (r : ℕ)
    (hleft : ∀ u, f (Sum.inl u) ∈ roots)
    (hfar : ∀ k, r ≤ G.dist o (f (Sum.inr k))) :
    (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) ⁻¹'
      ((fun ρ : (BD.indexedGraph jD).Configuration => ρ ∘ d) ⁻¹'
        maximalSplitStratum si ti so xo))ᶜ ⊆
      BS.reindex jS ⁻¹' closedLocalEvent BS (NestedAssembly.farConnection G roots o r) := by
  intro z hz
  change (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z ∘ d) ∉
    maximalSplitStratum si ti so xo at hz
  change BS.glue (BS.closedExterior, BS.reindex jS z) ∈
    NestedAssembly.farConnection G roots o r
  exact mem_farConnection_of_not_mem_maximalSplitStratum si ti so xo _ _
    (nestedOpenPathMap BS BD jS jD hBD si ti so xo d z f hend)
    roots o r hleft hfar hz

end FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry

namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Metric-scale finite estimate on an actual pulled-back maximal split
stratum.  Unlike `metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le`,
this version proves `hD` from the explicit endpoint/root/radius certificate.
Only the good-intersection identity remains stochastic input. -/
theorem metricBox_cylinder_abs_sub_le_farConnection_of_maximalSplit_good_of_le
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool)) (roots : Finset V) (m n : ℕ)
    (hrn : m + dataWidth G o J roots ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (β : (metricBox hG o (m + dataWidth G o J roots)).BoundaryPartition)
    {mI kO : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (si : Fin mI → U) (ti : Fin mI → U) (so xo : Fin kO → U ⊕ K)
    (d : (Fin mI ⊕ Fin kO) ≃
      Fin (Fintype.card (metricBox hG o (m + dataWidth G o J roots)).edges))
    (C : Set ((metricBox hG o
      (m + dataWidth G o J roots)).indexedGraph (edgeIndex _)).Configuration)
    (hC : let BD := metricBox hG o (m + dataWidth G o J roots)
      C = (fun ρ : (BD.indexedGraph (edgeIndex BD)).Configuration => ρ ∘ d) ⁻¹'
        maximalSplitStratum si ti so xo)
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        (((edgeIndex (metricBox hG o (m + dataWidth G o J roots))) (d a)).1).1)
    (hleft : ∀ u, f (Sum.inl u) ∈ roots)
    (hfar : ∀ k, m + dataWidth G o J roots ≤ G.dist o (f (Sum.inr k)))
    (hgood :
      let t := metricNestedTriple hG o hrn α β hq hp₀ hp₁
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J roots m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_larger_metricBox hG o J roots m hrn)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C))) :
    |((metricBox hG o n).finiteVolumeLaw hq hp₁.le α :
          Measure (Configuration G.edgeSet)).real (cylinder J S) -
        ((metricBox hG o (m + dataWidth G o J roots)).finiteVolumeLaw hq hp₁.le β :
          Measure (Configuration G.edgeSet)).real (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G roots o (m + dataWidth G o J roots)) := by
  subst C
  exact metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le
    hG o hq hp₀ hp₁ J S roots m n hrn α β _ hgood
    (OpenPathGeometry.bad_maximalSplit_subset_closedLocalEvent
      (metricBox hG o n) (metricBox hG o (m + dataWidth G o J roots))
      (edgeIndex _) (edgeIndex _) (nested_metricBox_edges hG o hrn)
      si ti so xo d f hend roots o (m + dataWidth G o J roots) hleft hfar)

end FK.InfiniteVolume.NestedMetricGeometry

#print axioms FK.InfiniteVolume.NestedMetricGeometry.metricBox
#print axioms FK.InfiniteVolume.NestedMetricGeometry.metricBoxExhaustion
#print axioms FK.InfiniteVolume.NestedMetricGeometry.nestedEdgeEquiv_inl
#print axioms FK.InfiniteVolume.NestedMetricGeometry.preimage_interiorRestriction_closedLocalEvent_farConnection
#print axioms FK.InfiniteVolume.NestedMetricGeometry.finiteBox_cylinder_abs_sub_le_farConnection_canonical_of_good
#print axioms FK.InfiniteVolume.NestedMetricGeometry.metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le
#print axioms FK.InfiniteVolume.NestedMetricGeometry.probabilityMeasure_eq_of_nested_finiteRootArm_bounds_reindexed
#print axioms FK.InfiniteVolume.NestedMetricGeometry.eq_of_isFKLimit_metricBox_of_nested_good
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry.LabelledOpenPathMap.openConnected_of_reachable
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry.exists_left_right_reachable_of_not_mem_maximalSplitStratum
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry.mem_farConnection_of_not_mem_maximalSplitStratum

#print axioms FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry.nestedOpenPathMap
#print axioms FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry.bad_maximalSplit_subset_closedLocalEvent

#print axioms FK.InfiniteVolume.NestedMetricGeometry.metricBox_cylinder_abs_sub_le_farConnection_of_maximalSplit_good_of_le
