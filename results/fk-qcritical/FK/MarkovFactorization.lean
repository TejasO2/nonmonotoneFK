import FK.FreeInterior

/-!
# Product factorization of finite FK measures on disconnected labelled multigraphs

The graph operations in this file keep every vertex and labelled edge. Thus
loops, parallel edges, isolated vertices and arbitrary setoid wiring on each
connected piece are retained. The factorization is proved for all `q > 0`
and `0 ≤ p ≤ 1`; no pointwise weight positivity is used.
-/

namespace FK.Finite.MarkovFactorization

noncomputable section

open scoped BigOperators ENNReal Classical
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane

/-- The independent law of a finite family of PMFs on their finite product. -/
def independentPi {C : Type*} [Fintype C] {α : C → Type*}
    [∀ c, Fintype (α c)] (P : ∀ c, PMF (α c)) : PMF (∀ c, α c) :=
  PMF.ofFintype (fun ω => ∏ c, P c (ω c)) (by
    classical
    calc
      (∑ ω : (∀ c, α c), ∏ c, P c (ω c)) = ∏ c, ∑ a, P c a :=
        (Fintype.prod_sum _).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro c hc
        have h : (∑' a, P c a) = ∑ a, P c a := tsum_fintype (fun a => P c a)
        exact h.symm.trans (P c).tsum_coe)

@[simp] lemma independentPi_apply {C : Type*} [Fintype C] {α : C → Type*}
    [∀ c, Fintype (α c)] (P : ∀ c, PMF (α c)) (ω : ∀ c, α c) :
    independentPi P ω = ∏ c, P c (ω c) := rfl


open MeasureTheory

/-- The finite independent PMF product induces the usual product measure. -/
lemma independentPi_toMeasure {C : Type*} [Fintype C] {α : C → Type*}
    [∀ c, Fintype (α c)] [∀ c, MeasurableSpace (α c)]
    [∀ c, MeasurableSingletonClass (α c)] (P : ∀ c, PMF (α c)) :
    (independentPi P).toMeasure = Measure.pi (fun c => (P c).toMeasure) := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro ω
  rw [PMF.toMeasure_apply_singleton _ _ (by simp), Measure.pi_singleton]
  simp only [independentPi_apply]
  apply Finset.prod_congr rfl
  intro c hc
  rw [PMF.toMeasure_apply_singleton _ _ (by simp)]

/-- Independent law on an ordinary binary product. -/
def independentProd {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) : PMF (α × β) :=
  PMF.ofFintype (fun z => P z.1 * Q z.2) (by
    classical
    calc
      (∑ z : α × β, P z.1 * Q z.2) = (∑ a, P a) * ∑ b, Q b := by
        rw [Fintype.sum_prod_type]
        exact (Fintype.sum_mul_sum _ _).symm
      _ = 1 := by
        have hP : (∑' a, P a) = ∑ a, P a := tsum_fintype (fun a => P a)
        have hQ : (∑' b, Q b) = ∑ b, Q b := tsum_fintype (fun b => Q b)
        rw [← hP, P.tsum_coe, ← hQ, Q.tsum_coe, mul_one])

@[simp] lemma independentProd_apply {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (z : α × β) :
    independentProd P Q z = P z.1 * Q z.2 := rfl

/-- Disjoint sum of finite labelled multigraphs, retaining all labels. -/
def disjointSum (G H : LabelledMultigraph) : LabelledMultigraph where
  Vertex := G.Vertex ⊕ H.Vertex
  Edge := G.Edge ⊕ H.Edge
  source
    | Sum.inl e => Sum.inl (G.source e)
    | Sum.inr e => Sum.inr (H.source e)
  target
    | Sum.inl e => Sum.inl (G.target e)
    | Sum.inr e => Sum.inr (H.target e)

/-- Join configurations on the two labelled-edge summands. -/
def joinConfig {G H : LabelledMultigraph}
    (ω : G.Configuration) (η : H.Configuration) : (disjointSum G H).Configuration :=
  glue ω η

/-- Split a configuration on the disjoint sum into its two restrictions. -/
def splitConfig (G H : LabelledMultigraph) :
    (disjointSum G H).Configuration ≃ G.Configuration × H.Configuration :=
  Equiv.sumArrowEquivProdArrow G.Edge H.Edge Bool

@[simp] lemma splitConfig_symm (G H : LabelledMultigraph) (z : G.Configuration × H.Configuration) :
    (splitConfig G H).symm z = joinConfig z.1 z.2 := by
  funext e
  cases e <;> rfl

/-- Boundary setoids on the two pieces, with no cross-piece wiring. -/
@[instance_reducible] def sumBoundary {G H : LabelledMultigraph}
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) :
    (disjointSum G H).BoundaryPartition where
  r
    | Sum.inl u, Sum.inl v => ξ.r u v
    | Sum.inr u, Sum.inr v => ζ.r u v
    | _, _ => False
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · rintro (u | u)
      · exact ξ.refl u
      · exact ζ.refl u
    · rintro (u | u) (v | v) h
      · exact ξ.symm h
      · exact h.elim
      · exact h.elim
      · exact ζ.symm h
    · rintro (u | u) (v | v) (w | w) huv hvw
      · exact ξ.trans huv hvw
      · exact hvw.elim
      · exact hvw.elim
      · exact huv.elim
      · exact huv.elim
      · exact huv.elim
      · exact hvw.elim
      · exact ζ.trans huv hvw

@[simp] lemma sumBoundary_inl_inl {G H : LabelledMultigraph}
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) (u v : G.Vertex) :
    sumBoundary ξ ζ (Sum.inl u) (Sum.inl v) = ξ u v := rfl

@[simp] lemma sumBoundary_inr_inr {G H : LabelledMultigraph}
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) (u v : H.Vertex) :
    sumBoundary ξ ζ (Sum.inr u) (Sum.inr v) = ζ u v := rfl

@[simp] lemma sumBoundary_inl_inr {G H : LabelledMultigraph}
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) (u : G.Vertex) (v : H.Vertex) :
    (sumBoundary ξ ζ).r (Sum.inl u) (Sum.inr v) = False := rfl

@[simp] lemma sumBoundary_inr_inl {G H : LabelledMultigraph}
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) (u : H.Vertex) (v : G.Vertex) :
    (sumBoundary ξ ζ).r (Sum.inr u) (Sum.inl v) = False := rfl

@[simp] lemma freeBoundary_disjointSum (G H : LabelledMultigraph) :
    (disjointSum G H).freeBoundary =
      sumBoundary G.freeBoundary H.freeBoundary := by
  apply Setoid.ext
  rintro (u | u) (v | v)
  · exact ⟨fun h => Sum.inl.inj h, fun h => congrArg Sum.inl h⟩
  · simp
  · simp
  · exact ⟨fun h => Sum.inr.inj h, fun h => congrArg Sum.inr h⟩

/-- The wired open graph of a disjoint sum is the disjoint sum of its two
wired open graphs. -/
theorem connectionGraph_disjointSum (G H : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition)
    (ω : G.Configuration) (η : H.Configuration) :
    (disjointSum G H).connectionGraph (sumBoundary ξ ζ) (joinConfig ω η) =
      G.connectionGraph ξ ω ⊕g H.connectionGraph ζ η := by
  ext x y
  rcases x with u | u <;> rcases y with v | v <;>
    simp [disjointSum, joinConfig,
      LabelledMultigraph.connectionGraph, LabelledMultigraph.Joins, glue]
  case inl.inl => intro _; rfl
  case inr.inr => intro _; rfl
  all_goals exact not_false

lemma componentCount_disjointSum (G H : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition)
    (ω : G.Configuration) (η : H.Configuration) :
    (disjointSum G H).componentCount (sumBoundary ξ ζ) (joinConfig ω η) =
      G.componentCount ξ ω + H.componentCount ζ η := by
  unfold LabelledMultigraph.componentCount
  rw [connectionGraph_disjointSum]
  exact SimpleGraph.natCard_connectedComponent_sum _ _

lemma edgeWeight_join (G H : LabelledMultigraph) (p : NNReal)
    (ω : G.Configuration) (η : H.Configuration) :
    (disjointSum G H).edgeWeight p (joinConfig ω η) =
      G.edgeWeight p ω * H.edgeWeight p η := by
  unfold LabelledMultigraph.edgeWeight
  change (∏ e : G.Edge ⊕ H.Edge, if joinConfig ω η e then p else 1 - p) = _
  rw [Fintype.prod_sum_type]
  rfl

lemma fkWeight_join (G H : LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition)
    (ω : G.Configuration) (η : H.Configuration) :
    (disjointSum G H).fkWeight q p (sumBoundary ξ ζ) (joinConfig ω η) =
      G.fkWeight q p ξ ω * H.fkWeight q p ζ η := by
  unfold LabelledMultigraph.fkWeight
  rw [componentCount_disjointSum, edgeWeight_join, pow_add]
  ac_rfl

lemma partitionFunction_disjointSum (G H : LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) :
    (disjointSum G H).partitionFunction q p (sumBoundary ξ ζ) =
      G.partitionFunction q p ξ * H.partitionFunction q p ζ := by
  unfold LabelledMultigraph.partitionFunction
  calc
    (∑ ρ, (disjointSum G H).fkWeight q p (sumBoundary ξ ζ) ρ) =
        ∑ z : G.Configuration × H.Configuration,
          G.fkWeight q p ξ z.1 * H.fkWeight q p ζ z.2 := by
      apply Fintype.sum_equiv (splitConfig G H)
      intro ρ
      rw [← fkWeight_join]
      have hρ : joinConfig ((splitConfig G H ρ).1) ((splitConfig G H ρ).2) = ρ :=
        (splitConfig_symm G H ((splitConfig G H) ρ)).symm.trans
          ((splitConfig G H).symm_apply_apply ρ)
      rw [hρ]
    _ = G.partitionFunction q p ξ * H.partitionFunction q p ζ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum _ _).symm

/-- Point masses of the FK law on a disjoint sum factor exactly. -/
theorem fkPMF_disjointSum_join (G H : LabelledMultigraph)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition)
    (ω : G.Configuration) (η : H.Configuration) :
    (disjointSum G H).fkPMF hq hp (sumBoundary ξ ζ) (joinConfig ω η) =
      G.fkPMF hq hp ξ ω * H.fkPMF hq hp ζ η := by
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.fkPMF_apply,
    LabelledMultigraph.fkPMF_apply, fkWeight_join, partitionFunction_disjointSum]
  exact_mod_cast (div_mul_div_comm
    (G.fkWeight q p ξ ω) (G.partitionFunction q p ξ)
    (H.fkWeight q p ζ η) (H.partitionFunction q p ζ)).symm

/-- Splitting an FK configuration on a disconnected labelled multigraph gives
exactly the independent product of the two wired FK laws. -/
theorem map_splitConfig_fkPMF_disjointSum (G H : LabelledMultigraph)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) :
    PMF.map (splitConfig G H) ((disjointSum G H).fkPMF hq hp (sumBoundary ξ ζ)) =
      independentProd (G.fkPMF hq hp ξ) (H.fkPMF hq hp ζ) := by
  apply PMF.ext
  rintro ⟨ω, η⟩
  rw [pmf_map_equiv_apply]
  simpa only [splitConfig_symm, independentProd_apply] using
    fkPMF_disjointSum_join G H hq hp ξ ζ ω η

/-- Conversely, gluing the two independent component laws gives the FK law on
their disjoint sum. -/
theorem map_join_independentProd_eq_fkPMF_disjointSum (G H : LabelledMultigraph)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (ζ : H.BoundaryPartition) :
    PMF.map (fun z : G.Configuration × H.Configuration => joinConfig z.1 z.2)
        (independentProd (G.fkPMF hq hp ξ) (H.fkPMF hq hp ζ)) =
      (disjointSum G H).fkPMF hq hp (sumBoundary ξ ζ) := by
  rw [← map_splitConfig_fkPMF_disjointSum G H hq hp ξ ζ, PMF.map_comp]
  have h : (fun z : G.Configuration × H.Configuration => joinConfig z.1 z.2) ∘
      splitConfig G H = id := by
    funext ρ
    exact (splitConfig_symm G H ((splitConfig G H) ρ)).symm.trans
      ((splitConfig G H).symm_apply_apply ρ)
  rw [h, PMF.map_id]

end
end FK.Finite.MarkovFactorization

namespace FK.Finite.MarkovFactorization

noncomputable section

open scoped BigOperators ENNReal Classical
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane

/-- Add an arbitrary family of labelled edges to a fixed graph.  Conditioning
below will force precisely these added labels to be closed. -/
def addExterior (G : LabelledMultigraph) {O : Type*} [Fintype O]
    (s t : O → G.Vertex) : LabelledMultigraph where
  Vertex := G.Vertex
  Edge := G.Edge ⊕ O
  source
    | Sum.inl e => G.source e
    | Sum.inr o => s o
  target
    | Sum.inl e => G.target e
    | Sum.inr o => t o

/-- The source map of `addExterior`, in the form used by `ambientOfSum`. -/
def addExteriorSource (G : LabelledMultigraph) {O : Type*} [Fintype O]
    (s : O → G.Vertex) : G.Edge ⊕ O → G.Vertex
  | Sum.inl e => G.source e
  | Sum.inr o => s o

/-- The target map of `addExterior`, in the form used by `ambientOfSum`. -/
def addExteriorTarget (G : LabelledMultigraph) {O : Type*} [Fintype O]
    (t : O → G.Vertex) : G.Edge ⊕ O → G.Vertex
  | Sum.inl e => G.target e
  | Sum.inr o => t o

/-- The exterior configuration in which every distinguished edge is closed. -/
def closedExterior (O : Type*) : O → Bool := fun _ => false

lemma ambientOfSum_addExterior (G : LabelledMultigraph) {O : Type*} [Fintype O]
    (s t : O → G.Vertex) :
    ambientOfSum (addExteriorSource G s) (addExteriorTarget G t) = addExterior G s t := rfl

lemma interiorOfSum_addExterior (G : LabelledMultigraph) {O : Type*} [Fintype O]
    (s t : O → G.Vertex) :
    interiorOfSum (addExteriorSource G s) (addExteriorTarget G t) = G := rfl

/-- When all exterior edges are closed, their induced boundary setoid is free. -/
theorem exteriorBoundary_closedExterior (G : LabelledMultigraph) {O : Type*}
    [Fintype O] (s t : O → G.Vertex) :
    exteriorBoundary (addExteriorSource G s) (addExteriorTarget G t) (closedExterior O) =
      G.freeBoundary := by
  apply Setoid.ext
  intro u v
  exact exteriorBoundary_related_iff_of_no_open_incident _ _ _ Set.univ
    (by intro o ho; simp [closedExterior] at ho) (Set.mem_univ u)

/-- Actual finite free-boundary Markov property.  Conditioning the ambient FK
law on the exact cylinder where every added edge is closed returns the original
free-boundary FK law, glued with that closed cylinder. -/
theorem filter_addExterior_closedExterior (G : LabelledMultigraph) {O : Type*}
    [Fintype O] (s t : O → G.Vertex) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (fun ω : G.Configuration => glue ω (closedExterior O))
        (G.fkPMF hq hp₁.le G.freeBoundary) =
      ((addExterior G s t).fkPMF hq hp₁.le (addExterior G s t).freeBoundary).filter
        (exteriorFiber (closedExterior O))
        (exteriorFiber_support_actual _ _ hq hp₀ hp₁ (closedExterior O)) := by
  have h := filter_ambient_fkPMF_eq_map_glue
    (addExteriorSource G s) (addExteriorTarget G t) hq hp₀ hp₁ (closedExterior O)
  rw [← exteriorBoundary_closedExterior G s t]
  exact h

/-- Closed-cutset FK Markov factorization into two independent free-boundary
FK laws.  The distinguished edge labels `O` are arbitrary labelled edges,
including loops and parallel edges. -/
theorem filter_addExterior_disjointSum_closedExterior
    (G H : LabelledMultigraph) {O : Type*} [Fintype O]
    (s t : O → (disjointSum G H).Vertex) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (fun z : G.Configuration × H.Configuration =>
          glue (joinConfig z.1 z.2) (closedExterior O))
        (independentProd (G.fkPMF hq hp₁.le G.freeBoundary)
          (H.fkPMF hq hp₁.le H.freeBoundary)) =
      ((addExterior (disjointSum G H) s t).fkPMF hq hp₁.le
        (addExterior (disjointSum G H) s t).freeBoundary).filter
        (exteriorFiber (closedExterior O))
        (exteriorFiber_support_actual _ _ hq hp₀ hp₁ (closedExterior O)) := by
  rw [← filter_addExterior_closedExterior (disjointSum G H) s t hq hp₀ hp₁]
  rw [freeBoundary_disjointSum]
  rw [← map_join_independentProd_eq_fkPMF_disjointSum G H hq hp₁.le]
  rw [PMF.map_comp]
  rfl

end
end FK.Finite.MarkovFactorization

namespace SimpleGraph

open scoped Classical

/-- Disjoint union of a family of simple graphs on a sigma type. -/
def sigmaFamily {C : Type*} {V : C → Type*} (K : ∀ c, SimpleGraph (V c)) :
    SimpleGraph (Sigma V) where
  Adj x y := ∃ h : x.1 = y.1,
    (K y.1).Adj (cast (congrArg V h) x.2) y.2
  symm := ⟨by
    rintro ⟨c, u⟩ ⟨d, v⟩ ⟨hidx, h⟩
    change c = d at hidx
    subst d
    refine ⟨rfl, ?_⟩
    simpa using (K c).adj_symm h⟩
  loopless := ⟨by
    rintro ⟨c, u⟩ ⟨hidx, h⟩
    apply (K c).loopless.irrefl u
    exact h⟩

/-- Inclusion of one fibre in a disjoint family of graphs. -/
def sigmaFamilyHom {C : Type*} {V : C → Type*} (K : ∀ c, SimpleGraph (V c))
    (c : C) : K c →g sigmaFamily K where
  toFun u := ⟨c, u⟩
  map_rel' h := ⟨rfl, h⟩

/-- Every path in a disjoint family lies in a single fibre and projects to a
path in that fibre. -/
lemma exists_fibre_of_sigmaFamily_reachable {C : Type*} {V : C → Type*}
    {K : ∀ c, SimpleGraph (V c)} {x y : Sigma V}
    (h : (sigmaFamily K).Reachable x y) :
    ∃ c, ∃ (u v : V c), x = ⟨c, u⟩ ∧ y = ⟨c, v⟩ ∧ (K c).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨x.1, x.2, x.2, rfl, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail y z hxy hyz ih =>
      rcases ih with ⟨c, u, v, rfl, rfl, huv⟩
      rcases z with ⟨d, w⟩
      rcases hyz with ⟨hidx, hvw⟩
      change c = d at hidx
      subst d
      have hvw' : (K c).Adj v w := by simpa using hvw
      exact ⟨c, u, w, rfl, rfl, huv.trans hvw'.reachable⟩

lemma reachable_sigmaFamily_of_fibre {C : Type*} {V : C → Type*}
    (K : ∀ c, SimpleGraph (V c)) {c : C} {u v : V c}
    (h : (K c).Reachable u v) :
    (sigmaFamily K).Reachable (⟨c, u⟩ : Sigma V) ⟨c, v⟩ :=
  h.map (sigmaFamilyHom K c)

/-- Connected components of a disjoint family are the sigma type of the
component types of its fibres. -/
noncomputable def connectedComponentSigmaFamilyEquiv {C : Type*} {V : C → Type*}
    (K : ∀ c, SimpleGraph (V c)) :
    (sigmaFamily K).ConnectedComponent ≃ Σ c, (K c).ConnectedComponent where
  toFun C := Quot.lift
    (fun x : Sigma V => ⟨x.1, (K x.1).connectedComponentMk x.2⟩)
    (by
      intro x y hxy
      obtain ⟨c, u, v, rfl, rfl, huv⟩ := exists_fibre_of_sigmaFamily_reachable hxy
      exact Sigma.ext rfl (heq_of_eq (SimpleGraph.ConnectedComponent.sound huv))) C
  invFun z := z.2.map (sigmaFamilyHom K z.1)
  left_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x => rcases x with ⟨c, u⟩; rfl
  right_inv z := by
    rcases z with ⟨c, C⟩
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h u => rfl

lemma natCard_connectedComponent_sigmaFamily {C : Type*} [Fintype C]
    {V : C → Type*} [∀ c, Finite (V c)] (K : ∀ c, SimpleGraph (V c)) :
    Nat.card (sigmaFamily K).ConnectedComponent = ∑ c, Nat.card (K c).ConnectedComponent := by
  rw [Nat.card_congr (connectedComponentSigmaFamilyEquiv K), Nat.card_sigma]

end SimpleGraph

namespace FK.Finite.MarkovFactorization

noncomputable section

open scoped BigOperators ENNReal Classical
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane

/-- Disjoint sum of an arbitrary finite family of labelled multigraphs. -/
def sigmaDisjointSum {C : Type*} [Fintype C] (G : C → LabelledMultigraph) :
    LabelledMultigraph where
  Vertex := Σ c, (G c).Vertex
  Edge := Σ c, (G c).Edge
  source e := ⟨e.1, (G e.1).source e.2⟩
  target e := ⟨e.1, (G e.1).target e.2⟩

/-- Uncurried configuration on all edges of a finite disjoint family. -/
def joinPiConfig {C : Type*} [Fintype C] {G : C → LabelledMultigraph}
    (ω : ∀ c, (G c).Configuration) : (sigmaDisjointSum G).Configuration :=
  Sigma.uncurry ω

/-- Currying identifies ambient configurations with the product of the
component configurations. -/
def splitPiConfig {C : Type*} [Fintype C] (G : C → LabelledMultigraph) :
    (sigmaDisjointSum G).Configuration ≃ ∀ c, (G c).Configuration :=
  Equiv.piCurry (fun c (_ : (G c).Edge) => Bool)

@[simp] lemma splitPiConfig_symm {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) (ω : ∀ c, (G c).Configuration) :
    (splitPiConfig G).symm ω = joinPiConfig ω := rfl

/-- The free open graph on a finite disjoint sum is the disjoint family of the
free open graphs. -/
theorem connectionGraph_sigmaDisjointSum_free {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) (ω : ∀ c, (G c).Configuration) :
    (sigmaDisjointSum G).connectionGraph (sigmaDisjointSum G).freeBoundary
        (joinPiConfig ω) =
      SimpleGraph.sigmaFamily
        (fun c => (G c).connectionGraph (G c).freeBoundary (ω c)) := by
  ext x y
  constructor
  · rintro ⟨hne, hfree | ⟨e, he, hjoin⟩⟩
    · exact (hne hfree).elim
    · rcases e with ⟨c, e⟩
      rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · cases hs
        cases ht
        refine ⟨rfl, ?_, Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩
        intro hst
        exact hne (congrArg (Sigma.mk c) hst)
      · cases hs
        cases ht
        refine ⟨rfl, ?_, Or.inr ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩⟩
        intro hst
        exact hne (congrArg (Sigma.mk c) hst)
  · rintro ⟨hidx, hlocal⟩
    rcases x with ⟨c, u⟩
    rcases y with ⟨d, v⟩
    dsimp at hidx
    subst d
    change (G c).connectionGraph (G c).freeBoundary (ω c) |>.Adj u v at hlocal
    refine ⟨?_, Or.inr ?_⟩
    · intro huv
      exact hlocal.1 (eq_of_heq (Sigma.mk.inj_iff.mp huv).2)
    · rcases hlocal.2 with hfree | ⟨e, he, hjoin⟩
      · exact (hlocal.1 hfree).elim
      · refine ⟨⟨c, e⟩, he, ?_⟩
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact Or.inl ⟨congrArg (Sigma.mk c) hs, congrArg (Sigma.mk c) ht⟩
        · exact Or.inr ⟨congrArg (Sigma.mk c) hs, congrArg (Sigma.mk c) ht⟩

lemma componentCount_sigmaDisjointSum_free {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) (ω : ∀ c, (G c).Configuration) :
    (sigmaDisjointSum G).componentCount (sigmaDisjointSum G).freeBoundary
        (joinPiConfig ω) =
      ∑ c, (G c).componentCount (G c).freeBoundary (ω c) := by
  unfold LabelledMultigraph.componentCount
  rw [connectionGraph_sigmaDisjointSum_free]
  exact SimpleGraph.natCard_connectedComponent_sigmaFamily _

lemma edgeWeight_joinPiConfig {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) (p : NNReal) (ω : ∀ c, (G c).Configuration) :
    (sigmaDisjointSum G).edgeWeight p (joinPiConfig ω) =
      ∏ c, (G c).edgeWeight p (ω c) := by
  unfold LabelledMultigraph.edgeWeight
  change (∏ e : Σ c, (G c).Edge, if joinPiConfig ω e then p else 1 - p) = _
  rw [Fintype.prod_sigma]
  rfl

lemma fkWeight_joinPiConfig {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) (q p : NNReal) (ω : ∀ c, (G c).Configuration) :
    (sigmaDisjointSum G).fkWeight q p (sigmaDisjointSum G).freeBoundary
        (joinPiConfig ω) =
      ∏ c, (G c).fkWeight q p (G c).freeBoundary (ω c) := by
  unfold LabelledMultigraph.fkWeight
  rw [componentCount_sigmaDisjointSum_free, edgeWeight_joinPiConfig]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]

lemma partitionFunction_sigmaDisjointSum_free {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) (q p : NNReal) :
    (sigmaDisjointSum G).partitionFunction q p (sigmaDisjointSum G).freeBoundary =
      ∏ c, (G c).partitionFunction q p (G c).freeBoundary := by
  unfold LabelledMultigraph.partitionFunction
  calc
    (∑ ρ, (sigmaDisjointSum G).fkWeight q p (sigmaDisjointSum G).freeBoundary ρ) =
        ∑ ω : ∀ c, (G c).Configuration,
          ∏ c, (G c).fkWeight q p (G c).freeBoundary (ω c) := by
      apply Fintype.sum_equiv (splitPiConfig G)
      intro ρ
      rw [← fkWeight_joinPiConfig]
      have hρ : joinPiConfig ((splitPiConfig G) ρ) = ρ :=
        (splitPiConfig G).symm_apply_apply ρ
      rw [hρ]
    _ = ∏ c, ∑ η, (G c).fkWeight q p (G c).freeBoundary η :=
      (Fintype.prod_sum _).symm

/-- Point masses factor over an arbitrary finite family of connected pieces. -/
theorem fkPMF_sigmaDisjointSum_joinPiConfig {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ω : ∀ c, (G c).Configuration) :
    (sigmaDisjointSum G).fkPMF hq hp (sigmaDisjointSum G).freeBoundary
        (joinPiConfig ω) =
      independentPi (fun c => (G c).fkPMF hq hp (G c).freeBoundary) ω := by
  rw [LabelledMultigraph.fkPMF_apply, fkWeight_joinPiConfig,
    partitionFunction_sigmaDisjointSum_free]
  simp only [independentPi_apply, LabelledMultigraph.fkPMF_apply]
  exact_mod_cast (Finset.prod_div_distrib
    (fun c => (G c).fkWeight q p (G c).freeBoundary (ω c))
    (fun c => (G c).partitionFunction q p (G c).freeBoundary)).symm

/-- Currying an FK configuration on a finite disjoint family gives the
independent product of all free component FK laws. -/
theorem map_splitPiConfig_fkPMF_sigmaDisjointSum {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    PMF.map (splitPiConfig G)
        ((sigmaDisjointSum G).fkPMF hq hp (sigmaDisjointSum G).freeBoundary) =
      independentPi (fun c => (G c).fkPMF hq hp (G c).freeBoundary) := by
  apply PMF.ext
  intro ω
  rw [pmf_map_equiv_apply]
  exact fkPMF_sigmaDisjointSum_joinPiConfig G hq hp ω

/-- Measure-theoretic form of family factorization: the actual FK measure on
the disjoint sum pushes forward to the product of the component FK measures. -/
theorem map_splitPiConfig_fkMeasure_sigmaDisjointSum {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    MeasureTheory.Measure.map (splitPiConfig G)
        ((sigmaDisjointSum G).fkMeasure hq hp (sigmaDisjointSum G).freeBoundary) =
      MeasureTheory.Measure.pi (fun c => (G c).fkMeasure hq hp (G c).freeBoundary) := by
  rw [LabelledMultigraph.fkMeasure, PMF.toMeasure_map _ _ (by fun_prop),
    map_splitPiConfig_fkPMF_sigmaDisjointSum, independentPi_toMeasure]
  rfl

/-- Gluing the independent finite-family product gives the FK law on the
actual disjoint sum. -/
theorem map_joinPiConfig_independentPi {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    PMF.map joinPiConfig
        (independentPi (fun c => (G c).fkPMF hq hp (G c).freeBoundary)) =
      (sigmaDisjointSum G).fkPMF hq hp (sigmaDisjointSum G).freeBoundary := by
  rw [← map_splitPiConfig_fkPMF_sigmaDisjointSum G hq hp, PMF.map_comp]
  have h : joinPiConfig ∘ splitPiConfig G = id := by
    funext ρ
    exact (splitPiConfig G).symm_apply_apply ρ
  rw [h, PMF.map_id]

/-- Closed-cutset Markov factorization into the independent free FK laws of an
arbitrary finite family of components. -/
theorem filter_addExterior_sigmaDisjointSum_closedExterior {C : Type*} [Fintype C]
    (G : C → LabelledMultigraph) {O : Type*} [Fintype O]
    (s t : O → (sigmaDisjointSum G).Vertex) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (fun ω : ∀ c, (G c).Configuration =>
          glue (joinPiConfig ω) (closedExterior O))
        (independentPi (fun c => (G c).fkPMF hq hp₁.le (G c).freeBoundary)) =
      ((addExterior (sigmaDisjointSum G) s t).fkPMF hq hp₁.le
        (addExterior (sigmaDisjointSum G) s t).freeBoundary).filter
        (exteriorFiber (closedExterior O))
        (exteriorFiber_support_actual _ _ hq hp₀ hp₁ (closedExterior O)) := by
  rw [← filter_addExterior_closedExterior (sigmaDisjointSum G) s t hq hp₀ hp₁]
  rw [← map_joinPiConfig_independentPi G hq hp₁.le]
  rw [PMF.map_comp]
  rfl

end
end FK.Finite.MarkovFactorization
