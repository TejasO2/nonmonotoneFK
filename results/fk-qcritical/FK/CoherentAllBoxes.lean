import FK.EndpointGlobalFiniteEnergy
import FK.CoherentMixtures
import FK.TailChoquet

/-!
# Coherent FK specifications indexed by all finite boxes

The public DLR interface tests only the boxes in one chosen exhaustion.  This
module constructs the corresponding all-finite-box interface and proves that,
for a genuinely coherent all-box specification, testing the chosen exhaustion
is equivalent to testing every finite box.  The proof uses the exact DLR
mixture theorem; it does not assume local constancy or geometric uniqueness.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.CoherentAllBoxes

open ConventionGeometry ConventionTransport

noncomputable section

universe u v

local instance boundaryPartitionMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- The actual conditional global FK laws as a Markov kernel in their
exterior configuration. -/
noncomputable def conditionalLawKernel {E : Type*} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    Kernel B.Exterior (Configuration E) where
  toFun η := (B.conditionalLaw hq hp α η : Measure (Configuration E))
  measurable' := measurable_conditionalLaw B hq hp α hα

instance conditionalLawKernel_isMarkov {E : Type*} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    IsMarkovKernel (conditionalLawKernel B hq hp α hα) where
  isProbabilityMeasure η := by
    change IsProbabilityMeasure (B.conditionalLaw hq hp α η : Measure (Configuration E))
    infer_instance

@[simp] lemma conditionalLawKernel_apply {E : Type*} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (η : B.Exterior) :
    conditionalLawKernel B hq hp α hα η =
      (B.conditionalLaw hq hp α η : Measure (Configuration E)) := rfl

/-- A coherent specification on every finite labelled box.  Compatibility is
exactly the finite FK tower property used by `BoundaryConvention`, but it is
required for every nested pair, not only for pairs in a chosen exhaustion. -/
structure AllBoxConvention (E : Type u) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) where
  partition : ∀ B : FiniteBox.{u, v} E, B.Exterior → B.BoundaryPartition
  measurable_partition : ∀ B, Measurable (partition B)
  compatible : ∀ B C : FiniteBox.{u, v} E, B.edges ⊆ C.edges →
    ∀ η : C.Exterior, B.IsDLR hq hp (partition B) (measurable_partition B)
      (C.conditionalLaw hq hp (partition C) η)

/-- DLR equations for an all-finite-box coherent specification. -/
def AllBoxDLRMeasures {E : Type u} {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : AllBoxConvention.{u, v} E hq hp) :
    Set (ProbabilityMeasure (Configuration E)) :=
  {μ | ∀ B : FiniteBox.{u, v} E, B.IsDLR hq hp (Φ.partition B)
    (Φ.measurable_partition B) μ}

/-- Restriction of an all-box convention to a chosen genuine exhaustion. -/
def restriction {E : Type u} {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (exh : BoxExhaustion.{u, v} E) (Φ : AllBoxConvention.{u, v} E hq hp) :
    BoundaryConvention exh hq hp where
  partition n := Φ.partition (exh.box n)
  measurable_partition n := Φ.measurable_partition (exh.box n)
  compatible m n hmn := Φ.compatible (exh.box m) (exh.box n) hmn

/-- DLR at a larger box and pointwise DLR compatibility of all its exterior
conditional laws imply DLR at a smaller box.  The smaller specification is
fixed, so the accepted general mixture theorem applies without any geometric
or positivity hypothesis. -/
theorem isDLR_of_isDLR_of_compatible {E : Type*} [Countable E]
    (B C : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (β : C.Exterior → C.BoundaryPartition) (hβ : Measurable β)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : C.IsDLR hq hp β hβ μ)
    (hcompatible : ∀ η : C.Exterior,
      B.IsDLR hq hp α hα (C.conditionalLaw hq hp β η)) :
    B.IsDLR hq hp α hα μ := by
  let κ := conditionalLawKernel C hq hp β hβ
  let ρ : Measure C.Exterior := C.exteriorMeasure μ
  have hmix : CoherentMixtures.mixture ρ κ = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    ext A hA
    change (ρ.bind κ) A = (μ : Measure (Configuration E)) A
    rw [Measure.bind_apply hA κ.aemeasurable,
      C.apply_of_isDLR hq hp β hβ μ hμ hA]
    rfl
  have h := CoherentMixtures.isDLR_mixture B hq hp α hα ρ κ
    (fun η => hcompatible η)
  rw [hmix] at h
  exact h

/-- Testing one genuine exhaustion is equivalent to testing every finite box
for an all-box coherent specification. -/
theorem mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction
    {E : Type u} [Countable E] {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (exh : BoxExhaustion.{u, v} E) (Φ : AllBoxConvention.{u, v} E hq hp)
    (μ : ProbabilityMeasure (Configuration E)) :
    μ ∈ AllBoxDLRMeasures Φ ↔ μ ∈ GibbsMeasures exh (restriction exh Φ) := by
  constructor
  · intro hμ n
    exact hμ (exh.box n)
  · intro hμ B
    let S := B.edges
    have hevent : ∀ᶠ n in atTop, S ⊆ (exh.box n).edges := exh.eventually_subset S
    obtain ⟨n, hn⟩ := hevent.exists
    exact isDLR_of_isDLR_of_compatible B (exh.box n) hq hp
      (Φ.partition B) (Φ.measurable_partition B)
      (Φ.partition (exh.box n)) (Φ.measurable_partition (exh.box n)) μ
      (hμ n) (Φ.compatible B (exh.box n) hn)


/-- Exterior component geometry indexed independently by every finite box. -/
structure AllBoxExteriorGeometry (E : Type u) where
  components : ∀ B : FiniteBox.{u, v} E, B.Exterior → Setoid B.Vertex
  infinite : ∀ B : FiniteBox.{u, v} E, B.Exterior → B.Vertex → Prop

/-- The two source geometric requirements on an all-box specification. -/
def IsAllBoxGeometric {E : Type u} {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (geo : AllBoxExteriorGeometry.{u, v} E) (Φ : AllBoxConvention.{u, v} E hq hp) : Prop :=
  (∀ B η, MergesOpenComponents (geo.components B η) (Φ.partition B η)) ∧
  (∀ B η, SeparatesFiniteComponents (geo.components B η) (Φ.partition B η)
    (geo.infinite B η))

/-- Restrict all-box exterior geometry to a chosen exhaustion. -/
def restrictionGeometry {E : Type u} (exh : BoxExhaustion.{u, v} E)
    (geo : AllBoxExteriorGeometry.{u, v} E) : ExteriorGeometry exh.box where
  components n := geo.components (exh.box n)
  infinite n := geo.infinite (exh.box n)

lemma isGeometric_restriction {E : Type u} {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (exh : BoxExhaustion.{u, v} E) (geo : AllBoxExteriorGeometry.{u, v} E)
    (Φ : AllBoxConvention.{u, v} E hq hp) (hΦ : IsAllBoxGeometric geo Φ) :
    IsGeometric (restrictionGeometry exh geo) (restriction exh Φ).toBoundaryAssignment := by
  constructor
  · intro n η
    exact hΦ.1 (exh.box n) η
  · intro n η
    exact hΦ.2 (exh.box n) η

/-- Embeddings of every finite labelled box in one actual global simple graph. -/
structure AllBoxSimpleGraphBoxData {V : Type u} (G : SimpleGraph V) where
  vertex : ∀ B : FiniteBox.{u, v} G.edgeSet, B.Vertex → V
  endpoint : ∀ (B : FiniteBox.{u, v} G.edgeSet) (e : B.edges),
    s(vertex B (B.source e), vertex B (B.target e)) = e.1.1

namespace AllBoxSimpleGraphBoxData

variable {V : Type u} {G : SimpleGraph V}

/-- Exterior open-component geometry for every finite box, with the interior
closed exactly as in the accepted fixed-exhaustion graph construction. -/
def geometry (data : AllBoxSimpleGraphBoxData.{u, v} G) :
    AllBoxExteriorGeometry.{u, v} G.edgeSet where
  components B η := openPathSetoid G (closeInside B η) Set.univ (data.vertex B)
  infinite B η x := ExteriorInfiniteCluster G (closeInside B η) Set.univ (data.vertex B x)

/-- Restrict the all-box graph embeddings to one chosen exhaustion. -/
def restrictionData (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G) :
    SimpleGraphBoxData G exh.box where
  vertex n := data.vertex (exh.box n)
  endpoint n := data.endpoint (exh.box n)

lemma restrictionData_geometry (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G) :
    (restrictionData exh data).geometry = restrictionGeometry exh data.geometry := rfl

end AllBoxSimpleGraphBoxData

open AllBoxSimpleGraphBoxData

/-- All-box Gibbs-to-Gibbs convention transport under actual global
at-most-one-cluster uniqueness. -/
theorem mem_allBoxDLRMeasures_of_globalAtMostOne_of_le_one
    {V : Type u} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq hp)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact ConventionTransport.mem_gibbsMeasures_of_globalAtMostOne_of_le_one
    exh (restrictionData exh data) (restriction exh Φ) (restriction exh Ψ)
    (isGeometric_restriction exh data.geometry Φ hΦ)
    (isGeometric_restriction exh data.geometry Ψ hΨ) μ
    ((mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Φ μ).1 hμ) hglobal

/-- Source-domain coherent finite-volume weak limits, with the source and target
conventions and their geometric certificates indexed by every finite box.
The conclusion is the DLR equation at every finite box, not merely at the
chosen exhaustion used to perform the limit. -/
theorem mem_allBoxDLRMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq hp)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      ((restriction exh Φ).partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    exh (restrictionData exh data) hq hp (restriction exh Φ)
    (restriction exh Ψ).toBoundaryAssignment
    (isGeometric_restriction exh data.geometry Φ hΦ)
    (isGeometric_restriction exh data.geometry Ψ hΨ) η hμ hglobal

/-- All-box coherent fixed-specification DLR closure.  The filter of source
laws is arbitrary and nontrivial; the endpoint and interior parameter branches
are the accepted all-rate theorem applied to the restricted specifications. -/
theorem mem_allBoxDLRMeasures_of_tendsto_dlr_of_globalAtMostOne_of_le_one
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq hp)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  apply EndpointGlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne_of_le_one
    exh (restrictionData exh data) hq hp (restriction exh Φ).toBoundaryAssignment
    (restriction exh Ψ).toBoundaryAssignment
    (isGeometric_restriction exh data.geometry Φ hΦ)
    (isGeometric_restriction exh data.geometry Ψ hΨ) hμ _ hglobal
  filter_upwards [hDLR] with i hi
  exact (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Φ (μs i)).1 hi

end

end FK.InfiniteVolume.CoherentAllBoxes
