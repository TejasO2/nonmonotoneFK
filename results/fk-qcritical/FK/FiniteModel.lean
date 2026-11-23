import FK.FinitePlanarDuality

/-!
# The finite random-cluster model on a labelled multigraph

Vertices and edges are arbitrary finite types.  `source` and `target` are not
required to be distinct, and no injectivity condition is imposed on the map
from an edge to its endpoints.  Loops and parallel labelled edges are
therefore part of the model.  A boundary partition is represented by its
setoid; it can have arbitrary blocks and is not restricted to free or wired
boundary conditions.

To count components with boundary wiring, we put an auxiliary connection
between every pair of distinct vertices in the same boundary block and an
open-edge connection between the endpoints of every open edge.  The resulting
`SimpleGraph` is used only to define connectivity.  The FK product weight still
has one factor for every labelled edge, including loops and parallel edges.
-/

namespace FK.Finite

open scoped BigOperators ENNReal
open MeasureTheory

/-- A finite labelled multigraph, with loops and parallel edges allowed. -/
structure LabelledMultigraph where
  Vertex : Type*
  Edge : Type*
  [fintypeVertex : Fintype Vertex]
  [fintypeEdge : Fintype Edge]
  source : Edge → Vertex
  target : Edge → Vertex

attribute [instance] LabelledMultigraph.fintypeVertex LabelledMultigraph.fintypeEdge

namespace LabelledMultigraph

variable (G : LabelledMultigraph)

/-- Open/closed configurations on the labelled edges. -/
abbrev Configuration := G.Edge → Bool

/-- The finite configuration space, without requiring a decidable equality
assumption on the externally supplied edge labels. -/
noncomputable instance : Fintype (Configuration G) := by
  classical
  infer_instance

/-- An arbitrary boundary partition, encoded by its equivalence relation. -/
abbrev BoundaryPartition := Setoid G.Vertex

/-- Free boundary: every block is a singleton. -/
@[instance_reducible] def freeBoundary : BoundaryPartition G where
  r u v := u = v
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Fully wired boundary: all vertices belong to one block. -/
@[instance_reducible] def wiredBoundary : BoundaryPartition G where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- The unordered endpoint relation contributed by one labelled edge. -/
def Joins (e : G.Edge) (u v : G.Vertex) : Prop :=
  (G.source e = u ∧ G.target e = v) ∨
    (G.source e = v ∧ G.target e = u)

lemma Joins.symm {e : G.Edge} {u v : G.Vertex} (h : G.Joins e u v) :
    G.Joins e v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The graph whose components are exactly the open/wired FK components.
Wiring connections are present independently of the configuration. -/
def connectionGraph (ξ : BoundaryPartition G) (ω : Configuration G) :
    SimpleGraph G.Vertex where
  Adj u v := u ≠ v ∧ (ξ.r u v ∨ ∃ e, ω e = true ∧ G.Joins e u v)
  symm := ⟨by
    rintro u v ⟨huv, h⟩
    refine ⟨huv.symm, ?_⟩
    rcases h with h | ⟨e, he, hjoin⟩
    · exact Or.inl (ξ.symm h)
    · exact Or.inr ⟨e, he, hjoin.symm⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

/-- Number of open components after boundary wiring, including isolated
vertices. -/
noncomputable def componentCount (ξ : BoundaryPartition G) (ω : Configuration G) : ℕ :=
  Nat.card (G.connectionGraph ξ ω).ConnectedComponent

lemma connectionGraph_mono {ξ : BoundaryPartition G} {ω η : Configuration G}
    (hωη : ω ≤ η) : G.connectionGraph ξ ω ≤ G.connectionGraph ξ η := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hwire | ⟨e, he, hjoin⟩
  · exact Or.inl hwire
  · refine Or.inr ⟨e, ?_, hjoin⟩
    have hle := hωη e
    rw [Bool.le_iff_imp] at hle
    exact hle he

/-- Opening edges can only decrease the number of wired components. -/
lemma componentCount_anti {ξ : BoundaryPartition G} {ω η : Configuration G}
    (hωη : ω ≤ η) : G.componentCount ξ η ≤ G.componentCount ξ ω := by
  have hgraph := G.connectionGraph_mono (ξ := ξ) hωη
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le hgraph

lemma componentCount_pos [Nonempty G.Vertex] (ξ : BoundaryPartition G)
    (ω : Configuration G) : 0 < G.componentCount ξ ω := by
  exact Nat.card_pos

/-- The Bernoulli part of an unnormalised FK weight. -/
def edgeWeight (p : NNReal) (ω : Configuration G) : NNReal :=
  ∏ e, if ω e then p else 1 - p

/-- The exact finite FK weight, before normalization. -/
noncomputable def fkWeight (q p : NNReal) (ξ : BoundaryPartition G) (ω : Configuration G) : NNReal :=
  G.edgeWeight p ω * q ^ G.componentCount ξ ω

/-- The finite FK partition function. -/
noncomputable def partitionFunction (q p : NNReal) (ξ : BoundaryPartition G) : NNReal :=
  ∑ ω, G.fkWeight q p ξ ω

/-- All configurations have positive weight in the interior of the parameter
range. -/
lemma fkWeight_pos {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : BoundaryPartition G) (ω : Configuration G) : 0 < G.fkWeight q p ξ ω := by
  unfold fkWeight edgeWeight
  apply mul_pos
  · apply Finset.prod_pos
    intro e _
    split_ifs
    · exact hp₀
    · exact tsub_pos_of_lt hp₁
  · exact pow_pos hq _

/-- A reference configuration used to show that normalization is possible at
either endpoint of `0 ≤ p ≤ 1`. -/
noncomputable def referenceConfiguration (p : NNReal) : Configuration G :=
  fun _ => decide (0 < p)

@[simp] lemma referenceConfiguration_of_zero :
    G.referenceConfiguration 0 = fun _ => false := by
  ext e
  simp [referenceConfiguration]

lemma referenceConfiguration_of_pos {p : NNReal} (hp : 0 < p) :
    G.referenceConfiguration p = fun _ => true := by
  ext e
  simp [referenceConfiguration, hp]

/-- Normalization does not require pointwise positivity: one explicit
configuration has positive weight throughout `0 ≤ p ≤ 1`. -/
lemma fkWeight_reference_pos {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    0 < G.fkWeight q p ξ (G.referenceConfiguration p) := by
  classical
  unfold fkWeight edgeWeight
  apply mul_pos
  · by_cases hp₀ : p = 0
    · subst p
      apply Finset.prod_pos
      intro e _
      simp [referenceConfiguration]
    · have hp₀' : 0 < p := pos_iff_ne_zero.mpr hp₀
      apply Finset.prod_pos
      intro e _
      simp [referenceConfiguration, hp₀']
  · exact pow_pos hq _

lemma partitionFunction_pos {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : BoundaryPartition G) : 0 < G.partitionFunction q p ξ := by
  classical
  apply lt_of_lt_of_le (G.fkWeight_reference_pos (ξ := ξ) hq hp)
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)

/-- Normalize finite nonnegative weights knowing only that their total mass is
positive.  Zero-weight configurations are allowed, as required at `p = 0` and
`p = 1`. -/
noncomputable def normalizedPMFOfSumPos {Ω : Type*} [Fintype Ω]
    (w : Ω → NNReal) (hw : 0 < ∑ a, w a) : PMF Ω := by
  classical
  apply PMF.normalize (fun a => (w a : ℝ≥0∞))
  · rw [tsum_fintype]
    exact_mod_cast hw.ne'
  · simp [tsum_fintype]

@[simp] lemma normalizedPMFOfSumPos_apply {Ω : Type*} [Fintype Ω]
    (w : Ω → NNReal) (hw : 0 < ∑ a, w a) (a : Ω) :
    normalizedPMFOfSumPos w hw a = (w a : ℝ≥0∞) * (∑' b, (w b : ℝ≥0∞))⁻¹ := rfl

/-- The actual normalized finite FK probability mass function. -/
noncomputable def fkPMF {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : BoundaryPartition G) : PMF (Configuration G) :=
  normalizedPMFOfSumPos (G.fkWeight q p ξ) (by
    simpa only [partitionFunction] using G.partitionFunction_pos hq hp ξ)

/-- Exact FK point mass: Bernoulli edge product times `q` to the wired
component count, divided by the partition function. -/
lemma fkPMF_apply {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : BoundaryPartition G) (ω : Configuration G) :
    G.fkPMF hq hp ξ ω = (G.fkWeight q p ξ ω / G.partitionFunction q p ξ : NNReal) := by
  change (G.fkWeight q p ξ ω : ℝ≥0∞) *
    (∑' η, (G.fkWeight q p ξ η : ℝ≥0∞))⁻¹ = _
  rw [tsum_fintype, ENNReal.coe_div (G.partitionFunction_pos hq hp ξ).ne']
  simp [partitionFunction, div_eq_mul_inv]

/-- The corresponding probability measure on the finite discrete
configuration space. -/
noncomputable def fkMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : BoundaryPartition G) : Measure (Configuration G) :=
  (G.fkPMF hq hp ξ).toMeasure

instance fkMeasure_isProbabilityMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : BoundaryPartition G) : IsProbabilityMeasure (G.fkMeasure hq hp ξ) := by
  unfold fkMeasure
  infer_instance

@[simp] lemma fkMeasure_apply_singleton {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : BoundaryPartition G) (ω : Configuration G) :
    G.fkMeasure hq hp ξ {ω} = G.fkPMF hq hp ξ ω := by
  rw [fkMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- The all-closed and all-open configurations. -/
def allClosed : Configuration G := fun _ => false
def allOpen : Configuration G := fun _ => true

@[simp] lemma connectionGraph_free_allClosed :
    G.connectionGraph G.freeBoundary G.allClosed = ⊥ := by
  ext u v
  simp [connectionGraph, allClosed]

@[simp] lemma componentCount_free_allClosed :
    G.componentCount G.freeBoundary G.allClosed = Nat.card G.Vertex := by
  rw [componentCount, connectionGraph_free_allClosed]
  let e : G.Vertex ≃ (⊥ : SimpleGraph G.Vertex).ConnectedComponent :=
    Equiv.ofBijective (⊥ : SimpleGraph G.Vertex).connectedComponentMk (by
      constructor
      · intro u v huv
        exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.exact huv)
      · intro C
        exact C.exists_rep)
  exact (Nat.card_congr e).symm

lemma connectionGraph_wired_preconnected (ω : Configuration G) :
    (G.connectionGraph G.wiredBoundary ω).Preconnected := by
  intro u v
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.refl u
  · exact (show (G.connectionGraph G.wiredBoundary ω).Adj u v from
      ⟨huv, Or.inl trivial⟩).reachable

@[simp] lemma componentCount_wired [Nonempty G.Vertex] (ω : Configuration G) :
    G.componentCount G.wiredBoundary ω = 1 := by
  change Nat.card (G.connectionGraph G.wiredBoundary ω).ConnectedComponent = 1
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨(G.connectionGraph_wired_preconnected ω).subsingleton_connectedComponent,
      inferInstance⟩

lemma exists_open_of_ne_allClosed {ω : Configuration G} (hω : ω ≠ G.allClosed) :
    ∃ e, ω e = true := by
  classical
  by_contra h
  push Not at h
  apply hω
  funext e
  cases he : ω e <;> simp_all [allClosed]

lemma exists_closed_of_ne_allOpen {ω : Configuration G} (hω : ω ≠ G.allOpen) :
    ∃ e, ω e = false := by
  classical
  by_contra h
  push Not at h
  apply hω
  funext e
  cases he : ω e <;> simp_all [allOpen]

lemma fkWeight_eq_zero_of_open {q : NNReal} (ξ : BoundaryPartition G)
    {ω : Configuration G} {e : G.Edge} (he : ω e = true) :
    G.fkWeight q 0 ξ ω = 0 := by
  rw [fkWeight]
  apply mul_eq_zero_of_left
  rw [edgeWeight, Finset.prod_eq_zero_iff]
  exact ⟨e, Finset.mem_univ _, by simp [he]⟩

lemma fkWeight_eq_zero_of_closed {q : NNReal} (ξ : BoundaryPartition G)
    {ω : Configuration G} {e : G.Edge} (he : ω e = false) :
    G.fkWeight q 1 ξ ω = 0 := by
  rw [fkWeight]
  apply mul_eq_zero_of_left
  rw [edgeWeight, Finset.prod_eq_zero_iff]
  exact ⟨e, Finset.mem_univ _, by simp [he]⟩

lemma partitionFunction_zero {q : NNReal} (ξ : BoundaryPartition G) :
    G.partitionFunction q 0 ξ = G.fkWeight q 0 ξ G.allClosed := by
  classical
  unfold partitionFunction
  apply Finset.sum_eq_single G.allClosed
  · intro ω _ hω
    obtain ⟨e, he⟩ := G.exists_open_of_ne_allClosed hω
    exact G.fkWeight_eq_zero_of_open ξ he
  · simp

lemma partitionFunction_one {q : NNReal} (ξ : BoundaryPartition G) :
    G.partitionFunction q 1 ξ = G.fkWeight q 1 ξ G.allOpen := by
  classical
  unfold partitionFunction
  apply Finset.sum_eq_single G.allOpen
  · intro ω _ hω
    obtain ⟨e, he⟩ := G.exists_closed_of_ne_allOpen hω
    exact G.fkWeight_eq_zero_of_closed ξ he
  · simp

/-- At `p = 0`, the normalized FK law is concentrated on the all-closed
configuration, for every `q > 0` and every boundary partition. -/
theorem fkPMF_zero {q : NNReal} (hq : 0 < q) (ξ : BoundaryPartition G) :
    G.fkPMF (p := 0) hq zero_le ξ = PMF.pure G.allClosed := by
  classical
  have hw : G.fkWeight q 0 ξ G.allClosed ≠ 0 := by
    rw [← G.partitionFunction_zero ξ]
    exact (G.partitionFunction_pos (p := 0) hq zero_le ξ).ne'
  apply PMF.ext
  intro ω
  by_cases hω : ω = G.allClosed
  · subst ω
    rw [PMF.pure_apply_self, fkPMF_apply, partitionFunction_zero, div_self hw]
    rfl
  · obtain ⟨e, he⟩ := G.exists_open_of_ne_allClosed hω
    rw [PMF.pure_apply_of_ne _ _ hω, fkPMF_apply,
      G.fkWeight_eq_zero_of_open ξ he]
    simp

/-- At `p = 1`, the normalized FK law is concentrated on the all-open
configuration, for every `q > 0` and every boundary partition. -/
theorem fkPMF_one {q : NNReal} (hq : 0 < q) (ξ : BoundaryPartition G) :
    G.fkPMF (p := 1) hq le_rfl ξ = PMF.pure G.allOpen := by
  classical
  have hw : G.fkWeight q 1 ξ G.allOpen ≠ 0 := by
    rw [← G.partitionFunction_one ξ]
    exact (G.partitionFunction_pos hq le_rfl ξ).ne'
  apply PMF.ext
  intro ω
  by_cases hω : ω = G.allOpen
  · subst ω
    rw [PMF.pure_apply_self, fkPMF_apply, partitionFunction_one, div_self hw]
    rfl
  · obtain ⟨e, he⟩ := G.exists_closed_of_ne_allOpen hω
    rw [PMF.pure_apply_of_ne _ _ hω, fkPMF_apply,
      G.fkWeight_eq_zero_of_closed ξ he]
    simp

end LabelledMultigraph
end FK.Finite
