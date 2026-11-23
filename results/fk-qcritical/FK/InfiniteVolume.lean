import FK.Proposition42
import FK.FiniteModel
import CurvatureVariance.Infra.Percolation.Connections

/-!
# Finite-volume FK kernels on an infinite labelled edge space

This module constructs the measure-theoretic bridge between the actual finite
labelled-multigraph FK laws and infinite configurations.  A finite box has a
finite vertex type and a finite set of global edge labels.  Loops and repeated
adjacencies are allowed; distinct labels in the global edge type remain
distinct edges.

The DLR equation is expressed after splitting a configuration into its exterior
and interior parts.  Thus no conditional-expectation convention and no
measurability assumption for a varying splice map is hidden in the statement.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume

universe u v

noncomputable section

/-- Infinite configurations on a type of labelled edges. -/
abbrev Configuration (E : Type*) := FKLimit.Configuration E

/-- A finite labelled-multigraph box embedded in a global labelled edge type.
The vertex type is arbitrary and finite.  Its boundary conditions are arbitrary
setoids on that vertex type, as in `FK.Finite.LabelledMultigraph`. -/
structure FiniteBox (E : Type*) where
  Vertex : Type*
  [fintypeVertex : Fintype Vertex]
  edges : Finset E
  source : edges → Vertex
  target : edges → Vertex

attribute [instance] FiniteBox.fintypeVertex

/-- Boundary partitions have the discrete measurable structure.  Keeping this
instance local avoids imposing a measurable structure on arbitrary setoids
elsewhere in the project. -/
local instance boundaryPartitionMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

/-- The type of setoids on a finite type is finite: it is their underlying
relations that matter, including for the regularity of a boundary convention. -/
local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- The finite graph underlying a box. -/
abbrev graph : FK.Finite.LabelledMultigraph where
  Vertex := B.Vertex
  Edge := B.edges
  source := B.source
  target := B.target

/-- Interior configurations of a finite box. -/
abbrev Interior := B.edges → Bool

/-- Exterior configurations, on precisely the complement of the box edges. -/
abbrev Exterior := {e : E // e ∉ B.edges} → Bool

/-- Arbitrary boundary partitions of the box. -/
abbrev BoundaryPartition := B.graph.BoundaryPartition

/-- Split a global configuration into exterior and interior restrictions. -/
def split : Configuration E → B.Exterior × B.Interior :=
  fun ω ↦ (fun e ↦ ω e.1, fun e ↦ ω e.1)

/-- Glue an exterior and an interior configuration, changing only box edges. -/
def glue : B.Exterior × B.Interior → Configuration E :=
  fun z e ↦ if he : e ∈ B.edges then z.2 ⟨e, he⟩ else z.1 ⟨e, he⟩

lemma glue_split (ω : Configuration E) : B.glue (B.split ω) = ω := by
  funext e
  simp only [glue, split]
  split_ifs <;> rfl

lemma split_glue (z : B.Exterior × B.Interior) : B.split (B.glue z) = z := by
  apply Prod.ext
  · funext e
    simp [split, glue, e.2]
  · funext e
    simp [split, glue]

/-- The canonical measurable identification of global configurations with the
product of exterior and interior configurations. -/
def splitEquiv : Configuration E ≃ᵐ B.Exterior × B.Interior where
  toEquiv :=
    { toFun := B.split
      invFun := B.glue
      left_inv := B.glue_split
      right_inv := B.split_glue }
  measurable_toFun := by
    apply Measurable.prod
    · exact Measurable.of_eval (fun e ↦ measurable_pi_apply e.1)
    · exact Measurable.of_eval (fun e ↦ measurable_pi_apply e.1)
  measurable_invFun := by
    apply Measurable.of_eval
    intro e
    change Measurable (fun z : ({e : E // e ∉ B.edges} → Bool) × (B.edges → Bool) ↦
      if he : e ∈ B.edges then z.2 ⟨e, he⟩ else z.1 ⟨e, he⟩)
    by_cases he : e ∈ B.edges
    · simp only [he, dite_true]
      exact (measurable_pi_apply (⟨e, he⟩ : B.edges)).comp measurable_snd
    · simp only [he, dite_false]
      exact (measurable_pi_apply (⟨e, he⟩ : {e : E // e ∉ B.edges})).comp measurable_fst

@[simp] lemma splitEquiv_apply (ω : Configuration E) :
    B.splitEquiv ω = B.split ω := rfl

@[simp] lemma splitEquiv_symm_apply (z : B.Exterior × B.Interior) :
    B.splitEquiv.symm z = B.glue z := rfl

/-- Exterior marginal of a law on global configurations. -/
noncomputable def exteriorMeasure (μ : ProbabilityMeasure (Configuration E)) :
    ProbabilityMeasure B.Exterior :=
  ProbabilityMeasure.map μ (fun ω ↦ (B.splitEquiv ω).1)

/-- The actual finite FK law, as a measure on interior configurations. -/
noncomputable def interiorFKMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) : Measure B.Interior :=
  B.graph.fkMeasure hq hp (α η)

/-- Regularity of the finite FK specification follows from finite discreteness
and measurability of the boundary assignment. -/
lemma measurable_interiorFKMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    Measurable (B.interiorFKMeasure hq hp α) := by
  exact (measurable_of_finite _).comp hα

/-- The actual finite FK Markov kernel from exterior to interior
configurations. -/
noncomputable def fkKernel {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    Kernel B.Exterior B.Interior where
  toFun := B.interiorFKMeasure hq hp α
  measurable' := B.measurable_interiorFKMeasure hq hp α hα

instance fkKernel_isMarkov {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    IsMarkovKernel (B.fkKernel hq hp α hα) where
  isProbabilityMeasure η := by
    exact FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp (α η)

@[simp] lemma fkKernel_apply {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) (η : B.Exterior) :
    B.fkKernel hq hp α hα η = B.graph.fkMeasure hq hp (α η) := rfl

lemma measurable_glue_const_left (η : B.Exterior) :
    Measurable (fun ω : B.Interior ↦ B.glue (η, ω)) := by
  exact B.splitEquiv.symm.measurable.comp (measurable_const.prodMk measurable_id)

/-- One conditional global law: retain the exterior `η` and sample the box
from its actual finite FK PMF with boundary partition `α η`. -/
noncomputable def conditionalLaw {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) :
    ProbabilityMeasure (Configuration E) :=
  ⟨Measure.map (fun ω : B.Interior ↦ B.glue (η, ω))
      (B.graph.fkMeasure hq hp (α η)),
    (Measure.isProbabilityMeasure_map_iff
      (μ := B.graph.fkMeasure hq hp (α η))
      (f := fun ω : B.Interior ↦ B.glue (η, ω))
      (B.measurable_glue_const_left η).aemeasurable).2
        (FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp (α η))⟩

/-- Exact DLR/comp-product equation for one finite box. -/
def IsDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) : Prop :=
  Measure.map B.splitEquiv (μ : Measure (Configuration E)) =
    (B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ B.fkKernel hq hp α hα

end FiniteBox


namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- A DLR law is the glue of its exterior marginal with the actual FK
specification. -/
lemma measure_eq_map_glue_compProd {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) :
    (μ : Measure (Configuration E)) =
      Measure.map B.glue ((B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ
        B.fkKernel hq hp α hα) := by
  exact B.splitEquiv.map_apply_eq_iff_map_symm_apply_eq.mp hμ

/-- Probability under a DLR law is the exterior integral of the conditional
global FK laws. -/
lemma apply_of_isDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) {A : Set (Configuration E)}
    (hA : MeasurableSet A) :
    (μ : Measure (Configuration E)) A =
      ∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
        ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  rw [B.measure_eq_map_glue_compProd hq hp α hα μ hμ,
    Measure.map_apply hg hA, Measure.compProd_apply (hg hA)]
  apply lintegral_congr
  intro η
  symm
  exact Measure.map_apply (B.measurable_glue_const_left η) hA

/-- A pointwise lower bound for every conditional global FK law integrates to
the same lower bound for every DLR law. -/
lemma measure_lower_bound_of_isDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) (ν : Measure (Configuration E))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hbound : ∀ η, ν A ≤ (B.conditionalLaw hq hp α η : Measure (Configuration E)) A) :
    ν A ≤ (μ : Measure (Configuration E)) A := by
  rw [B.apply_of_isDLR hq hp α hα μ hμ hA]
  calc
    ν A = ∫⁻ _η, ν A ∂(B.exteriorMeasure μ : Measure B.Exterior) := by simp
    _ ≤ ∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
        ∂(B.exteriorMeasure μ : Measure B.Exterior) := lintegral_mono hbound

/-- A pointwise upper bound for every conditional global FK law integrates to
the same upper bound for every DLR law. -/
lemma measure_upper_bound_of_isDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) (ν : Measure (Configuration E))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hbound : ∀ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A ≤ ν A) :
    (μ : Measure (Configuration E)) A ≤ ν A := by
  rw [B.apply_of_isDLR hq hp α hα μ hμ hA]
  calc
    (∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
        ∂(B.exteriorMeasure μ : Measure B.Exterior)) ≤
        ∫⁻ _η, ν A ∂(B.exteriorMeasure μ : Measure B.Exterior) := lintegral_mono hbound
    _ = ν A := by simp

/-- Uniform finite-volume lower comparisons pass to every DLR law. -/
theorem stochasticallyDominates_dlr_lower {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ lower : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hbound : ∀ η, FKLimit.StochasticallyDominates lower (B.conditionalLaw hq hp α η)) :
    FKLimit.StochasticallyDominates lower μ := by
  intro A hA hAup
  change ((μ : Measure (Configuration E)) A).toNNReal ≤
    ((lower : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  apply B.measure_upper_bound_of_isDLR hq hp α hα μ hμ
    (lower : Measure (Configuration E)) hA
  intro η
  exact FKLimit.ennreal_le_of_probabilityMeasure_apply_le (hbound η A hA hAup)

/-- Uniform finite-volume upper comparisons pass to every DLR law. -/
theorem stochasticallyDominates_dlr_upper {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ upper : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hbound : ∀ η, FKLimit.StochasticallyDominates (B.conditionalLaw hq hp α η) upper) :
    FKLimit.StochasticallyDominates μ upper := by
  intro A hA hAup
  change ((upper : Measure (Configuration E)) A).toNNReal ≤
    ((μ : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  apply B.measure_lower_bound_of_isDLR hq hp α hα μ hμ
    (upper : Measure (Configuration E)) hA
  intro η
  exact FKLimit.ennreal_le_of_probabilityMeasure_apply_le (hbound η A hA hAup)

/-- Two-sided finite-volume comparisons pass to every DLR law. -/
theorem two_sided_stochasticallyDominates_dlr {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ lower upper : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hLower : ∀ η, FKLimit.StochasticallyDominates lower (B.conditionalLaw hq hp α η))
    (hUpper : ∀ η, FKLimit.StochasticallyDominates (B.conditionalLaw hq hp α η) upper) :
    FKLimit.StochasticallyDominates lower μ ∧
      FKLimit.StochasticallyDominates μ upper :=
  ⟨B.stochasticallyDominates_dlr_lower hq hp α hα μ lower hμ hLower,
    B.stochasticallyDominates_dlr_upper hq hp α hα μ upper hμ hUpper⟩

end FiniteBox

/-- An exhaustion of a global labelled edge space by actual finite graph
boxes. -/
structure BoxExhaustion (E : Type u) where
  box : ℕ → FiniteBox.{u, v} E
  monotone : Monotone (fun n ↦ (box n).edges)
  covers : ∀ e : E, ∃ n, e ∈ (box n).edges

namespace BoxExhaustion

variable {E : Type*} (exh : BoxExhaustion E)

lemma eventually_mem (e : E) : ∀ᶠ n in atTop, e ∈ (exh.box n).edges := by
  obtain ⟨N, hN⟩ := exh.covers e
  filter_upwards [eventually_ge_atTop N] with n hn
  exact exh.monotone hn hN

lemma eventually_subset (S : Finset E) : ∀ᶠ n in atTop, S ⊆ (exh.box n).edges := by
  change ∀ᶠ n in atTop, ∀ e ∈ S, e ∈ (exh.box n).edges
  rw [Finset.eventually_all]
  exact fun e _ ↦ exh.eventually_mem e

end BoxExhaustion

/-- A measurable family of externally induced boundary partitions.  This is
precisely the regularity data needed by the local FK kernels.  The paper's
nesting compatibility for a full convention is intentionally not asserted by
this definition; it remains geometric input. -/
structure BoundaryAssignment {E : Type u} (box : ℕ → FiniteBox.{u, v} E) where
  partition : ∀ n, (box n).Exterior → (box n).BoundaryPartition
  measurable_partition : ∀ n, Measurable (partition n)

namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- The canonical closed exterior configuration used to regard a finite-volume
law as a law on all global edge labels.  The values outside the box do not
affect any finite-volume cylinder supported in the box. -/
def closedExterior : B.Exterior := fun _ ↦ false

/-- The actual finite FK law with a specified boundary partition, extended to
all global edge labels by closed exterior edges. -/
noncomputable def finiteVolumeLaw {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.BoundaryPartition) : ProbabilityMeasure (Configuration E) :=
  B.conditionalLaw hq hp (fun _ ↦ α) B.closedExterior

end FiniteBox

/-- An FK weak limit along the fixed genuine finite-box exhaustion, with an
arbitrary sequence of boundary setoids. -/
def IsFKLimit {E : Type*} [Countable E] (exh : BoxExhaustion E) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (μ : ProbabilityMeasure (Configuration E)) : Prop :=
  Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp (α n)) atTop (𝓝 μ)

/-- The set of all FK weak limits on a fixed box exhaustion. -/
def FKLimitMeasures {E : Type*} [Countable E] (exh : BoxExhaustion E) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) : Set (ProbabilityMeasure (Configuration E)) :=
  {μ | ∃ α, IsFKLimit exh hq hp α μ}

/-- The DLR laws for one measurable boundary assignment, with the exact DLR
equation required at every box of the exhaustion. -/
def DLRMeasures {E : Type*} (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    Set (ProbabilityMeasure (Configuration E)) :=
  {μ | ∀ n, (exh.box n).IsDLR hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ}

/-- A coherent convention at parameters `(p,q)`: in addition to measurability,
for nested boxes every larger finite FK law is DLR at the smaller box after the
intermediate edges have been sampled.  This is the law-level statement of the
finite FK specification's nesting compatibility. -/
structure BoundaryConvention {E : Type u} (exh : BoxExhaustion.{u, v} E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    extends BoundaryAssignment exh.box where
  compatible : ∀ m n, (exh.box m).edges ⊆ (exh.box n).edges →
    ∀ η : (exh.box n).Exterior,
      (exh.box m).IsDLR hq hp (partition m) (measurable_partition m)
        ((exh.box n).conditionalLaw hq hp (partition n) η)

/-- The DLR/Gibbs class for a coherent convention. -/
def GibbsMeasures {E : Type u} (exh : BoxExhaustion.{u, v} E)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : BoundaryConvention exh hq hp) : Set (ProbabilityMeasure (Configuration E)) :=
  DLRMeasures exh Φ.toBoundaryAssignment hq hp

/-- Finite-volume comparisons pass to an arbitrary FK weak limit. -/
theorem two_sided_stochasticallyDominates_fkLimit {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (μ lower upper : ProbabilityMeasure (Configuration E))
    (hμ : IsFKLimit exh hq hp α μ)
    (hLower : ∀ n, FKLimit.StochasticallyDominates lower
      ((exh.box n).finiteVolumeLaw hq hp (α n)))
    (hUpper : ∀ n, FKLimit.StochasticallyDominates
      ((exh.box n).finiteVolumeLaw hq hp (α n)) upper) :
    FKLimit.StochasticallyDominates lower μ ∧
      FKLimit.StochasticallyDominates μ upper := by
  constructor
  · exact FKLimit.stochasticallyDominates_of_tendsto hμ tendsto_const_nhds hLower
  · exact FKLimit.stochasticallyDominates_of_tendsto tendsto_const_nhds hμ hUpper

/-- Finite-volume comparisons pass uniformly to the entire FK-limit class. -/
theorem two_sided_stochasticallyDominates_of_mem_fkLimitMeasures
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ lower upper : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ FKLimitMeasures exh hq hp)
    (hLower : ∀ (α : ∀ n, (exh.box n).BoundaryPartition) n,
      FKLimit.StochasticallyDominates lower ((exh.box n).finiteVolumeLaw hq hp (α n)))
    (hUpper : ∀ (α : ∀ n, (exh.box n).BoundaryPartition) n,
      FKLimit.StochasticallyDominates ((exh.box n).finiteVolumeLaw hq hp (α n)) upper) :
    FKLimit.StochasticallyDominates lower μ ∧
      FKLimit.StochasticallyDominates μ upper := by
  obtain ⟨α, hα⟩ := hμ
  exact two_sided_stochasticallyDominates_fkLimit exh hq hp α μ lower upper hα
    (hLower α) (hUpper α)

/-- Finite-volume comparisons pass uniformly to every DLR law for a fixed
measurable boundary assignment. -/
theorem two_sided_stochasticallyDominates_of_mem_dlrMeasures
    {E : Type*} (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ lower upper : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hLower : ∀ n η, FKLimit.StochasticallyDominates lower
      ((exh.box n).conditionalLaw hq hp (Φ.partition n) η))
    (hUpper : ∀ n η, FKLimit.StochasticallyDominates
      ((exh.box n).conditionalLaw hq hp (Φ.partition n) η) upper) :
    FKLimit.StochasticallyDominates lower μ ∧
      FKLimit.StochasticallyDominates μ upper := by
  exact (exh.box 0).two_sided_stochasticallyDominates_dlr hq hp
    (Φ.partition 0) (Φ.measurable_partition 0) μ lower upper (hμ 0)
    (hLower 0) (hUpper 0)

/-- Finite-volume comparisons pass to every Gibbs law for a coherent
convention. -/
theorem two_sided_stochasticallyDominates_of_mem_gibbsMeasures
    {E : Type u} (exh : BoxExhaustion.{u, v} E) {q p : NNReal}
    {hq : 0 < q} {hp : p ≤ 1} (Φ : BoundaryConvention exh hq hp)
    {μ lower upper : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ GibbsMeasures exh Φ)
    (hLower : ∀ n η, FKLimit.StochasticallyDominates lower
      ((exh.box n).conditionalLaw hq hp (Φ.partition n) η))
    (hUpper : ∀ n η, FKLimit.StochasticallyDominates
      ((exh.box n).conditionalLaw hq hp (Φ.partition n) η) upper) :
    FKLimit.StochasticallyDominates lower μ ∧
      FKLimit.StochasticallyDominates μ upper := by
  exact two_sided_stochasticallyDominates_of_mem_dlrMeasures exh
    Φ.toBoundaryAssignment hq hp hμ hLower hUpper

/-- Weak-limit and coherent-convention Gibbs laws on a fixed exhaustion.  This
is the direct model of the paper's union of FK limit measures and convention-
dependent DLR classes, without quotienting away boundary assignments. -/
def LimitOrGibbsMeasures {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    Set (ProbabilityMeasure (Configuration E)) :=
  FKLimitMeasures exh hq hp ∪
    {μ | ∃ Φ : BoundaryConvention exh hq hp, μ ∈ GibbsMeasures exh Φ}

namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- Restriction of a global configuration to the box's labelled edges. -/
def interiorRestriction : Configuration E → B.Interior :=
  fun ω ↦ (B.splitEquiv ω).2

lemma measurable_interiorRestriction : Measurable B.interiorRestriction :=
  measurable_snd.comp B.splitEquiv.measurable

@[simp] lemma interiorRestriction_glue (η : B.Exterior) (ω : B.Interior) :
    B.interiorRestriction (B.glue (η, ω)) = ω := by
  exact congrArg Prod.snd (B.split_glue (η, ω))

/-- The actual finite FK law packaged as a `ProbabilityMeasure`, retaining the
original arbitrary boundary setoid. -/
noncomputable def interiorFKProbabilityMeasure {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (α : B.BoundaryPartition) :
    ProbabilityMeasure B.Interior :=
  ⟨B.graph.fkMeasure hq hp α,
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp α⟩

/-- Conditioning on any exterior configuration leaves exactly the original
finite FK PMF as the interior marginal. -/
theorem map_interiorRestriction_conditionalLaw {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) :
    Measure.map B.interiorRestriction
        (B.conditionalLaw hq hp α η : Measure (Configuration E)) =
      B.graph.fkMeasure hq hp (α η) := by
  rw [show (B.conditionalLaw hq hp α η : Measure (Configuration E)) =
      Measure.map (fun ω : B.Interior ↦ B.glue (η, ω))
        (B.graph.fkMeasure hq hp (α η)) from rfl,
    Measure.map_map B.measurable_interiorRestriction (B.measurable_glue_const_left η)]
  have hfun : B.interiorRestriction ∘ (fun ω : B.Interior ↦ B.glue (η, ω)) = id := by
    funext ω
    exact B.interiorRestriction_glue η ω
  rw [hfun, Measure.map_id]

/-- `ProbabilityMeasure` form of the exact interior-marginal identity. -/
theorem probabilityMeasure_map_interiorRestriction_conditionalLaw {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) :
    ProbabilityMeasure.map (B.conditionalLaw hq hp α η) B.interiorRestriction =
      B.interiorFKProbabilityMeasure hq hp (α η) := by
  apply Subtype.ext
  exact B.map_interiorRestriction_conditionalLaw hq hp α η

/-- DLR equations can be transported through almost-everywhere equality of
their actual finite FK kernels. -/
lemma isDLR_of_ae_eq_kernels {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α β : B.Exterior → B.BoundaryPartition) (hα : Measurable α) (hβ : Measurable β)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hκ : B.fkKernel hq hp α hα =ᵐ[(B.exteriorMeasure μ : Measure B.Exterior)]
      B.fkKernel hq hp β hβ) : B.IsDLR hq hp β hβ μ := by
  unfold IsDLR at hμ ⊢
  rw [hμ]
  exact Measure.compProd_congr hκ

/-- Pointwise equality of boundary setoids identifies the corresponding FK
kernels, including their possibly different measurability proofs. -/
lemma fkKernel_eq_of_partition_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α β : B.Exterior → B.BoundaryPartition) (hα : Measurable α) (hβ : Measurable β)
    (η : B.Exterior) (hη : α η = β η) :
    B.fkKernel hq hp α hα η = B.fkKernel hq hp β hβ η := by
  simp only [fkKernel_apply, hη]

/-- Almost-everywhere equality of boundary partitions transports the DLR
 equation. -/
lemma isDLR_of_ae_partition_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α β : B.Exterior → B.BoundaryPartition) (hα : Measurable α) (hβ : Measurable β)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hη : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior), α η = β η) :
    B.IsDLR hq hp β hβ μ := by
  apply B.isDLR_of_ae_eq_kernels hq hp α β hα hβ μ hμ
  filter_upwards [hη] with η hη
  exact B.fkKernel_eq_of_partition_eq hq hp α β hα hβ η hη

end FiniteBox

/-- Membership in DLR classes depends only on the exterior almost-everywhere
boundary specification. -/
theorem mem_dlrMeasures_iff_of_ae_partition_eq {E : Type u}
    (exh : BoxExhaustion.{u, v} E) (Φ Ψ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hη : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior),
      Φ.partition n η = Ψ.partition n η) :
    μ ∈ DLRMeasures exh Φ hq hp ↔ μ ∈ DLRMeasures exh Ψ hq hp := by
  constructor
  · intro hμ n
    exact (exh.box n).isDLR_of_ae_partition_eq hq hp (Φ.partition n) (Ψ.partition n)
      (Φ.measurable_partition n) (Ψ.measurable_partition n) μ (hμ n) (hη n)
  · intro hμ n
    exact (exh.box n).isDLR_of_ae_partition_eq hq hp (Ψ.partition n) (Φ.partition n)
      (Ψ.measurable_partition n) (Φ.measurable_partition n) μ (hμ n)
      (Filter.Eventually.mono (hη n) fun _ h ↦ h.symm)

/-- The same almost-everywhere criterion transports membership of the Gibbs
class of coherent conventions. -/
theorem mem_gibbsMeasures_iff_of_ae_partition_eq {E : Type u}
    (exh : BoxExhaustion.{u, v} E) {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ Ψ : BoundaryConvention exh hq hp) {μ : ProbabilityMeasure (Configuration E)}
    (hη : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior),
      Φ.partition n η = Ψ.partition n η) :
    μ ∈ GibbsMeasures exh Φ ↔ μ ∈ GibbsMeasures exh Ψ := by
  exact mem_dlrMeasures_iff_of_ae_partition_eq exh Φ.toBoundaryAssignment
    Ψ.toBoundaryAssignment hq hp hη

/-! Elementary geometry of conventions at infinity. -/
namespace ConventionGeometry

open CurvatureVariance.Infra.Percolation

variable {V : Type*}

/-- `C` is the exterior-open-component partition and `I` says that the ambient
exterior cluster through a vertex is infinite.  A convention must merge every
open component. -/
def MergesOpenComponents (C α : Setoid V) : Prop := C ≤ α

/-- Distinct exterior components cannot be merged when at least one is finite. -/
def SeparatesFiniteComponents (C α : Setoid V) (IsInfinite : V → Prop) : Prop :=
  ∀ {x y}, ¬C.r x y → (¬IsInfinite x ∨ ¬IsInfinite y) → ¬α.r x y

/-- Any two vertices in infinite exterior components are related by the exterior
open-component setoid. -/
def AtMostOneInfiniteCluster (C : Setoid V) (IsInfinite : V → Prop) : Prop :=
  ∀ x y, IsInfinite x → IsInfinite y → C.r x y

lemma eq_openComponents_of_finite_separation (C α : Setoid V) (IsInfinite : V → Prop)
    (hmerge : MergesOpenComponents C α)
    (hsep : SeparatesFiniteComponents C α IsInfinite)
    (hunique : AtMostOneInfiniteCluster C IsInfinite) : α = C := by
  apply Setoid.ext
  intro x y
  constructor
  · intro hxy
    by_contra hC
    apply hsep hC ?_ hxy
    by_cases hx : IsInfinite x
    · exact Or.inr (fun hy ↦ hC (hunique x y hx hy))
    · exact Or.inl hx
  · intro hC
    exact hmerge hC

/-- Under at most one infinite exterior cluster, every two conventions satisfying
the paper's two compatibility constraints have the same boundary partition. -/
theorem convention_eq_of_atMostOneInfiniteCluster (C α β : Setoid V)
    (IsInfinite : V → Prop)
    (hmergeα : MergesOpenComponents C α)
    (hsepα : SeparatesFiniteComponents C α IsInfinite)
    (hmergeβ : MergesOpenComponents C β)
    (hsepβ : SeparatesFiniteComponents C β IsInfinite)
    (hunique : AtMostOneInfiniteCluster C IsInfinite) : α = β := by
  rw [eq_openComponents_of_finite_separation C α IsInfinite hmergeα hsepα hunique,
    eq_openComponents_of_finite_separation C β IsInfinite hmergeβ hsepβ hunique]

/-- Open walks are symmetric, including when constrained to a prescribed set of
edges. -/
lemma openConnected_symm {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set (Sym2 V)} {u v : V} (h : OpenConnected G ω A u v) :
    OpenConnected G ω A v u := by
  obtain ⟨p, hp⟩ := h
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons u v w huv p ih =>
    rw [isOpenIn_cons] at hp
    have htail : OpenConnected G ω A w v := ih hp.2
    have hhead : OpenConnected G ω A v u := by
      apply OpenConnected.of_adj huv.symm
      · simpa only [Sym2.eq_swap] using hp.1.1
      · simpa only [Sym2.eq_swap] using hp.1.2
    exact htail.trans hhead

/-- The exterior-open component setoid on an arbitrary boundary vertex set. -/
def exteriorOpenSetoid {S : Set V} (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (A : Set (Sym2 V)) : Setoid S where
  r x y := OpenConnected G ω A x.1 y.1
  iseqv :=
    ⟨fun x ↦ OpenConnected.refl ω A x.1,
      fun h ↦ openConnected_symm h,
      fun hxy hyz ↦ hxy.trans hyz⟩

/-- Infinitude is measured using the full ambient exterior cluster, not merely
its intersection with the boundary. -/
def ExteriorInfiniteCluster (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (A : Set (Sym2 V)) (x : V) : Prop :=
  {y | OpenConnected G ω A x y}.Infinite

/-- Instance of convention independence on an actual graph, with infinitude
measured by full ambient exterior clusters. -/
theorem exteriorOpenSetoid_eq_of_atMostOneInfiniteCluster {S : Set V}
    (G : SimpleGraph V) (ω : G.edgeSet → Bool) (A : Set (Sym2 V)) (α β : Setoid S)
    (hmergeα : MergesOpenComponents (exteriorOpenSetoid G ω A) α)
    (hsepα : SeparatesFiniteComponents (exteriorOpenSetoid G ω A) α
      (fun x ↦ ExteriorInfiniteCluster G ω A x.1))
    (hmergeβ : MergesOpenComponents (exteriorOpenSetoid G ω A) β)
    (hsepβ : SeparatesFiniteComponents (exteriorOpenSetoid G ω A) β
      (fun x ↦ ExteriorInfiniteCluster G ω A x.1))
    (hunique : AtMostOneInfiniteCluster (exteriorOpenSetoid (S := S) G ω A)
      (fun x : S ↦ ExteriorInfiniteCluster G ω A x.1)) : α = β := by
  exact convention_eq_of_atMostOneInfiniteCluster (exteriorOpenSetoid (S := S) G ω A) α β
    (fun x : S ↦ ExteriorInfiniteCluster G ω A x.1)
    hmergeα hsepα hmergeβ hsepβ hunique

/-- In the non-percolating case, all exterior clusters are finite.  Hence the
exterior convention-independence hypotheses hold without any uniqueness
argument at infinity. -/
lemma atMostOneInfiniteCluster_exterior_of_finite_openClusters {S : Set V}
    (G : SimpleGraph V) (ω : G.edgeSet → Bool) (A : Set (Sym2 V))
    (hω : ∀ x, {y | OpenConnected G ω Set.univ x y}.Finite) :
    AtMostOneInfiniteCluster (exteriorOpenSetoid (S := S) G ω A)
      (fun x : S ↦ ExteriorInfiniteCluster G ω A x.1) := by
  intro x y hx _hy
  have hx' : {z | OpenConnected G ω Set.univ x.1 z}.Infinite := by
    apply Set.Infinite.mono (s := {z | OpenConnected G ω A x.1 z})
    intro z hz
    exact OpenConnected.mono_edges hz (Set.subset_univ A)
    exact hx
  exact (hx' (hω x.1)).elim

end ConventionGeometry

end
end FK.InfiniteVolume
