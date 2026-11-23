import FK.NoncoherentStabilization
import FK.ClassicalOne
import FK.PlanarForestDuality

/-!
# A noncoherent finite-volume limit need not be geometric DLR

On a finite graph, `GlobalAtMostOne` is vacuous.  The fully wired finite FK law
is not, however, the free finite FK law when `q ≠ 1`.  A constant finite-volume
sequence therefore gives an actual `IsFKLimit` satisfying global uniqueness but
not the canonical free/geometric DLR equation.

This is a counterexample to removing all coherence/geometry restrictions from
the remaining noncoherent fixed-source assertion in the present definitions.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.NoncoherentCounterexample

open FK.Finite FK.Finite.LabelledMultigraph
open ConventionGeometry ConventionTransport
open CurvatureVariance.Infra.Percolation

noncomputable section

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- DLR on a box with no exterior coordinates identifies the interior marginal
with the actual finite FK law at the unique exterior point. -/
theorem map_interiorRestriction_of_isDLR_of_subsingleton
    {E : Type*} [Countable E] (B : FiniteBox E) [Subsingleton B.Exterior]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ) :
    Measure.map B.interiorRestriction (μ : Measure (Configuration E)) =
      B.graph.fkMeasure hq hp (α default) := by
  classical
  apply Measure.ext
  intro A hA
  have hA' : MeasurableSet (B.interiorRestriction ⁻¹' A) :=
    B.measurable_interiorRestriction hA
  rw [Measure.map_apply B.measurable_interiorRestriction hA]
  rw [B.apply_of_isDLR hq hp α hα μ hμ hA']
  have hcond (η : B.Exterior) :
      (B.conditionalLaw hq hp α η : Measure (Configuration E))
          (B.interiorRestriction ⁻¹' A) = B.graph.fkMeasure hq hp (α default) A := by
    rw [← Measure.map_apply B.measurable_interiorRestriction hA,
      B.map_interiorRestriction_conditionalLaw hq hp α η]
    congr 2
    exact congrArg α (Subsingleton.elim η default)
  simp_rw [hcond]
  simp

/-- An all-closed configuration has only trivial open connections. -/
lemma openConnected_allClosed_iff {V : Type*} {G : SimpleGraph V} (x y : V) :
    OpenConnected G (fun _ => false) Set.univ x y ↔ x = y := by
  constructor
  · rintro ⟨p, hp⟩
    induction p with
    | nil => rfl
    | @cons a b c hab p ih =>
        have hopen := (isOpenIn_cons.mp hp).1.2
        simp at hopen
  · rintro rfl
    exact OpenConnected.refl _ _ _

/-- Finitely many vertices rule out infinite exterior clusters, without any
assumption on the configuration. -/
lemma globalAtMostOne_of_finite {V : Type*} (G : SimpleGraph V) [Finite V]
    (ω : Configuration G.edgeSet) : GlobalAtMostOne G ω := by
  intro x y hx _hy
  exact (hx (Set.toFinite _)).elim


/-- The complete simple graph on two vertices. -/
abbrev TwoVertexGraph : SimpleGraph Bool := ⊤

/-- Its unique labelled edge. -/
def twoVertexEdge : TwoVertexGraph.edgeSet :=
  ⟨s(false, true), by simp⟩

instance uniqueTwoVertexEdge : Unique TwoVertexGraph.edgeSet where
  default := twoVertexEdge
  uniq e := by
    apply Subtype.ext
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro x y he
    have hxy : x ≠ y := by simpa using he
    fin_cases x <;> fin_cases y <;> simp_all [twoVertexEdge]

/-- A finite box containing every edge of the two-vertex graph. -/
def oneEdgeBox : FiniteBox TwoVertexGraph.edgeSet where
  Vertex := Bool
  edges := Finset.univ
  source _ := false
  target _ := true

/-- The constant exhaustion by that exhaustive finite box. -/
def oneEdgeExhaustion : BoxExhaustion TwoVertexGraph.edgeSet where
  box _ := oneEdgeBox
  monotone := by
    intro _a _b _hab
    exact Finset.Subset.refl _
  covers e := ⟨0, Finset.mem_univ e⟩

/-- The canonical embedding of every box into the global two-vertex graph. -/
def oneEdgeBoxData : SimpleGraphBoxData TwoVertexGraph oneEdgeExhaustion.box where
  vertex _ := id
  endpoint _ e := by
    change s(false, true) = e.1.1
    rw [show e.1 = twoVertexEdge from Subsingleton.elim _ _]
    rfl

instance oneEdgeExteriorSubsingleton : Subsingleton oneEdgeBox.Exterior where
  allEq η ζ := by
    funext e
    exact (e.2 (Finset.mem_univ e.1)).elim

/-- At the unique exterior, whose box edges are all closed, the canonical free
assignment is literally the free boundary setoid. -/
lemma oneEdge_free_partition (η : oneEdgeBox.Exterior) :
    oneEdgeBoxData.free.partition 0 η = oneEdgeBox.graph.freeBoundary := by
  apply Setoid.ext
  intro x y
  change OpenConnected TwoVertexGraph (closeInside oneEdgeBox η) Set.univ x y ↔ x = y
  have hclosed : closeInside oneEdgeBox η = (fun _ => false) := by
    funext e
    have he : e ∈ oneEdgeBox.edges := Finset.mem_univ e
    simp [closeInside, FiniteBox.glue, he]
  rw [hclosed]
  exact openConnected_allClosed_iff x y

/-- The finite-volume law used for the constant arbitrary-boundary sequence. -/
noncomputable def wiredOneEdgeLimit : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet) :=
  oneEdgeBox.finiteVolumeLaw (q := 2) (p := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary

/-- This is a genuine arbitrary-boundary FK weak limit; no coherent convention
is involved. -/
theorem isFKLimit_wiredOneEdgeLimit :
    IsFKLimit oneEdgeExhaustion (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num)
      (fun _ => oneEdgeBox.graph.wiredBoundary) wiredOneEdgeLimit := by
  exact tendsto_const_nhds

/-- Its global at-most-one hypothesis holds trivially because the vertex type
is finite. -/
theorem ae_globalAtMostOne_wiredOneEdgeLimit :
    ∀ᵐ ω ∂(wiredOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)),
      GlobalAtMostOne TwoVertexGraph ω :=
  Eventually.of_forall (globalAtMostOne_of_finite TwoVertexGraph)


/-- The box's unique edge label. -/
def oneEdgeBoxEdge : oneEdgeBox.edges := ⟨twoVertexEdge, Finset.mem_univ _⟩

instance nonemptyOneEdgeBoxVertex : Nonempty oneEdgeBox.Vertex := ⟨false⟩

instance uniqueOneEdgeBoxEdge : Unique oneEdgeBox.edges where
  default := oneEdgeBoxEdge
  uniq e := Subtype.ext (Subsingleton.elim e.1 oneEdgeBoxEdge.1)

lemma oneEdge_componentCount_free_allOpen :
    oneEdgeBox.graph.componentCount oneEdgeBox.graph.freeBoundary
      oneEdgeBox.graph.allOpen = 1 := by
  apply componentCount_eq_one_of_preconnected _ _ _ false
  intro x y
  fin_cases x <;> fin_cases y
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    refine ⟨(by intro h; cases h), Or.inr ⟨oneEdgeBoxEdge, rfl, ?_⟩⟩
    exact Or.inr ⟨rfl, rfl⟩
  · apply SimpleGraph.Adj.reachable
    refine ⟨(by intro h; cases h), Or.inr ⟨oneEdgeBoxEdge, rfl, ?_⟩⟩
    exact Or.inl ⟨rfl, rfl⟩
  · exact SimpleGraph.Reachable.refl _

lemma oneEdge_componentCount_free_allClosed :
    oneEdgeBox.graph.componentCount oneEdgeBox.graph.freeBoundary
      oneEdgeBox.graph.allClosed = 2 := by
  rw [componentCount_free_allClosed]
  norm_num [oneEdgeBox]

lemma oneHalf_sub_oneHalf : (1 - 1 / 2 : NNReal) = 1 / 2 := by
  apply NNReal.eq
  norm_num [NNReal.coe_sub (show (1 / 2 : NNReal) ≤ 1 by norm_num)]

lemma oneEdge_free_weight_allOpen :
    oneEdgeBox.graph.fkWeight 2 (1 / 2 : NNReal) oneEdgeBox.graph.freeBoundary
      oneEdgeBox.graph.allOpen = 1 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    oneEdge_componentCount_free_allOpen, LabelledMultigraph.allOpen]

lemma oneEdge_free_weight_allClosed :
    oneEdgeBox.graph.fkWeight 2 (1 / 2 : NNReal) oneEdgeBox.graph.freeBoundary
      oneEdgeBox.graph.allClosed = 2 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    oneEdge_componentCount_free_allClosed, LabelledMultigraph.allClosed, oneEdgeBox,
    oneHalf_sub_oneHalf]

lemma oneEdge_wired_weight_allOpen :
    oneEdgeBox.graph.fkWeight 2 (1 / 2 : NNReal) oneEdgeBox.graph.wiredBoundary
      oneEdgeBox.graph.allOpen = 1 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    LabelledMultigraph.allOpen, componentCount_wired]

lemma oneEdge_wired_weight_allClosed :
    oneEdgeBox.graph.fkWeight 2 (1 / 2 : NNReal) oneEdgeBox.graph.wiredBoundary
      oneEdgeBox.graph.allClosed = 1 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    LabelledMultigraph.allClosed, componentCount_wired, oneHalf_sub_oneHalf]

local instance oneEdgeConfigurationFintype : Fintype oneEdgeBox.graph.Configuration :=
  oneEdgeBox.graph.instFintypeConfiguration

/-- Summing over configurations on the unique edge is summing over `Bool`. -/
lemma sum_oneEdgeConfiguration {M : Type*} [AddCommMonoid M]
    (f : oneEdgeBox.graph.Configuration → M) :
    (∑ ω, f ω) = f oneEdgeBox.graph.allOpen + f oneEdgeBox.graph.allClosed := by
  rw [← Equiv.sum_comp (Equiv.funUnique oneEdgeBox.graph.Edge Bool).symm f,
    Fintype.sum_bool]
  rfl

lemma oneEdge_free_partitionFunction :
    oneEdgeBox.graph.partitionFunction 2 (1 / 2 : NNReal)
      oneEdgeBox.graph.freeBoundary = 3 := by
  let f : oneEdgeBox.graph.Configuration → NNReal := fun ω =>
    oneEdgeBox.graph.fkWeight 2 (1 / 2 : NNReal) oneEdgeBox.graph.freeBoundary ω
  have hsum : (∑ ω, f ω) = f oneEdgeBox.graph.allOpen + f oneEdgeBox.graph.allClosed :=
    sum_oneEdgeConfiguration f
  unfold LabelledMultigraph.partitionFunction
  exact hsum.trans (by
    dsimp [f]
    rw [oneEdge_free_weight_allOpen, oneEdge_free_weight_allClosed]
    norm_num)

lemma oneEdge_wired_partitionFunction :
    oneEdgeBox.graph.partitionFunction 2 (1 / 2 : NNReal)
      oneEdgeBox.graph.wiredBoundary = 2 := by
  let f : oneEdgeBox.graph.Configuration → NNReal := fun ω =>
    oneEdgeBox.graph.fkWeight 2 (1 / 2 : NNReal) oneEdgeBox.graph.wiredBoundary ω
  have hsum : (∑ ω, f ω) = f oneEdgeBox.graph.allOpen + f oneEdgeBox.graph.allClosed :=
    sum_oneEdgeConfiguration f
  unfold LabelledMultigraph.partitionFunction
  exact hsum.trans (by
    dsimp [f]
    rw [oneEdge_wired_weight_allOpen, oneEdge_wired_weight_allClosed]
    norm_num)

lemma oneEdge_free_allOpen_mass :
    oneEdgeBox.graph.fkPMF (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary
        oneEdgeBox.graph.allOpen = (1 / 3 : NNReal) := by
  rw [LabelledMultigraph.fkPMF_apply, oneEdge_free_weight_allOpen,
    oneEdge_free_partitionFunction]

lemma oneEdge_wired_allOpen_mass :
    oneEdgeBox.graph.fkPMF (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary
        oneEdgeBox.graph.allOpen = (1 / 2 : NNReal) := by
  rw [LabelledMultigraph.fkPMF_apply, oneEdge_wired_weight_allOpen,
    oneEdge_wired_partitionFunction]

lemma oneEdge_free_fkMeasure_ne_wired :
    oneEdgeBox.graph.fkMeasure (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary ≠
    oneEdgeBox.graph.fkMeasure (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary := by
  intro h
  have hm := congrArg (fun ν : Measure oneEdgeBox.Interior =>
    ν {oneEdgeBox.graph.allOpen}) h
  simp only [LabelledMultigraph.fkMeasure,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    oneEdge_free_allOpen_mass, oneEdge_wired_allOpen_mass] at hm
  norm_num at hm

/-- The actual arbitrary-boundary FK limit is not DLR for its canonical
geometric free assignment.  This refutes the unrestricted interior implication
from `IsFKLimit` plus global at-most-one uniqueness to geometric DLR membership. -/
theorem wiredOneEdgeLimit_not_mem_free_dlr :
    wiredOneEdgeLimit ∉ DLRMeasures oneEdgeExhaustion oneEdgeBoxData.free
      (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) := by
  intro hmem
  have hD := hmem 0
  have hd := map_interiorRestriction_of_isDLR_of_subsingleton oneEdgeBox
    (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
    (oneEdgeBoxData.free.partition 0) (oneEdgeBoxData.free.measurable_partition 0)
    wiredOneEdgeLimit hD
  have hw : Measure.map oneEdgeBox.interiorRestriction
      (wiredOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)) =
      oneEdgeBox.graph.fkMeasure (q := 2) (p := (1 / 2 : NNReal))
        (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary := by
    simpa [wiredOneEdgeLimit, FiniteBox.finiteVolumeLaw] using
      oneEdgeBox.map_interiorRestriction_conditionalLaw
        (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        (fun _ => oneEdgeBox.graph.wiredBoundary) oneEdgeBox.closedExterior
  rw [hw, oneEdge_free_partition default] at hd
  exact oneEdge_free_fkMeasure_ne_wired hd.symm


/-- The same limit has at most one infinite component in every finite-box
exterior geometry, again trivially by finiteness. -/
theorem aeAtMostOne_geometry_wiredOneEdgeLimit :
    AEAtMostOne oneEdgeBoxData.geometry wiredOneEdgeLimit := by
  intro n
  filter_upwards [] with η
  intro x y hx _hy
  exact (hx (Set.toFinite _)).elim

/-- Stronger obstruction: the limit is not DLR for any geometrically valid
target assignment.  Convention transport would otherwise put it in the free
class, contradicting `wiredOneEdgeLimit_not_mem_free_dlr`. -/
theorem wiredOneEdgeLimit_not_mem_dlr_of_isGeometric
    (Φ : BoundaryAssignment oneEdgeExhaustion.box)
    (hΦ : IsGeometric oneEdgeBoxData.geometry Φ) :
    wiredOneEdgeLimit ∉ DLRMeasures oneEdgeExhaustion Φ
      (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) := by
  intro hmem
  have hfree : wiredOneEdgeLimit ∈ DLRMeasures oneEdgeExhaustion oneEdgeBoxData.free
      (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
    ConventionTransport.mem_dlrMeasures_of_atMostOne oneEdgeExhaustion
      oneEdgeBoxData.geometry Φ oneEdgeBoxData.free
      (by norm_num) (by norm_num) hΦ oneEdgeBoxData.free_isGeometric hmem
      aeAtMostOne_geometry_wiredOneEdgeLimit
  exact wiredOneEdgeLimit_not_mem_free_dlr hfree

/-- Packaged certificate of the exact obstruction: a genuine noncoherent FK
limit with global and exterior uniqueness whose law is excluded from every
geometric DLR class on its box data. -/
theorem oneEdge_noncoherent_counterexample :
    IsFKLimit oneEdgeExhaustion (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) (fun _ => oneEdgeBox.graph.wiredBoundary)
        wiredOneEdgeLimit ∧
    (∀ᵐ ω ∂(wiredOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)),
      GlobalAtMostOne TwoVertexGraph ω) ∧
    ∀ Φ : BoundaryAssignment oneEdgeExhaustion.box,
      IsGeometric oneEdgeBoxData.geometry Φ →
        wiredOneEdgeLimit ∉ DLRMeasures oneEdgeExhaustion Φ
          (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) :=
  ⟨isFKLimit_wiredOneEdgeLimit, ae_globalAtMostOne_wiredOneEdgeLimit,
    wiredOneEdgeLimit_not_mem_dlr_of_isGeometric⟩



end

end FK.InfiniteVolume.NoncoherentCounterexample

#print axioms FK.InfiniteVolume.NoncoherentCounterexample.map_interiorRestriction_of_isDLR_of_subsingleton
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.openConnected_allClosed_iff
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.globalAtMostOne_of_finite
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.oneEdge_free_partition
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.oneEdge_free_allOpen_mass
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.oneEdge_wired_allOpen_mass
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.oneEdge_free_fkMeasure_ne_wired
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.isFKLimit_wiredOneEdgeLimit
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.ae_globalAtMostOne_wiredOneEdgeLimit
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.wiredOneEdgeLimit_not_mem_free_dlr
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.aeAtMostOne_geometry_wiredOneEdgeLimit
#print axioms FK.InfiniteVolume.NoncoherentCounterexample.wiredOneEdgeLimit_not_mem_dlr_of_isGeometric

#print axioms FK.InfiniteVolume.NoncoherentCounterexample.oneEdge_noncoherent_counterexample
