import FK.CoherentAllBoxes
import FK.EndpointGlobalFiniteEnergy

/-!
# Adapters for coherent FK specifications on all finite boxes

These are consequences of the independently checked all-box interface, not
extensions to noncoherent specifications.  The interior weak-limit adapter
retains the source and target geometric certificates and global uniqueness.
The endpoint adapters use the actual all-closed/all-open conditional limits;
their freedom from geometric hypotheses is specific to `p = 0` and `p = 1`.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.CoherentAllBoxes

open ConventionGeometry ConventionTransport
open AllBoxSimpleGraphBoxData

noncomputable section

universe u v

/-- The exhaustion used to test a fixed all-box coherent specification is
immaterial: its Gibbs classes on any two genuine exhaustions coincide. -/
theorem mem_gibbsMeasures_restriction_iff
    {E : Type u} [Countable E] {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (exh₀ exh₁ : BoxExhaustion.{u, v} E) (Φ : AllBoxConvention.{u, v} E hq hp)
    (μ : ProbabilityMeasure (Configuration E)) :
    μ ∈ GibbsMeasures exh₀ (restriction exh₀ Φ) ↔
      μ ∈ GibbsMeasures exh₁ (restriction exh₁ Φ) := by
  rw [← mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh₀ Φ μ,
    ← mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh₁ Φ μ]

/-- Closed-exterior coherent finite-volume weak limits, transported from one
all-box geometric specification to another.  The conclusion tests every
finite box, while the limit is taken along the chosen genuine exhaustion. -/
theorem mem_allBoxDLRMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne_of_le_one
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq hp)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      ((restriction exh Φ).partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne_of_le_one
    exh (restrictionData exh data) hq hp (restriction exh Φ)
    (restriction exh Ψ).toBoundaryAssignment
    (isGeometric_restriction exh data.geometry Φ hΦ)
    (isGeometric_restriction exh data.geometry Ψ hΨ) hμ hglobal

/-- Fixed-convention form of coherent arbitrary-exterior weak-limit closure.
The single geometric certificate is used for both source and target. -/
theorem mem_allBoxDLRMeasures_self_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      ((restriction exh Φ).partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Φ := by
  exact mem_allBoxDLRMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    exh data hq hp Φ Φ hΦ hΦ η hμ hglobal

/-- At zero edge rate, every coherent all-box target contains an arbitrary-
exterior weak limit from a coherent all-box source.  The limit is all closed,
so no graph geometry, local finiteness, or global-uniqueness input is needed. -/
theorem mem_allBoxDLRMeasures_of_tendsto_conditionalLaw_zero
    {V : Type u} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion.{u, v} G.edgeSet) {q : NNReal} (hq : 0 < q)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq (p := 0) bot_le)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 0) bot_le
      ((restriction exh Φ).partition n) (η n)) atTop (𝓝 μ)) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_zero_of_tendsto_conditionalLaw
    exh hq (restriction exh Φ).partition η (restriction exh Ψ).toBoundaryAssignment hμ

/-- At unit edge rate, every coherent all-box target contains an arbitrary-
exterior weak limit from a coherent all-box source.  The limit is all open,
so no graph geometry, local finiteness, or global-uniqueness input is needed. -/
theorem mem_allBoxDLRMeasures_of_tendsto_conditionalLaw_one
    {V : Type u} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion.{u, v} G.edgeSet) {q : NNReal} (hq : 0 < q)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq (p := 1) le_rfl)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 1) le_rfl
      ((restriction exh Φ).partition n) (η n)) atTop (𝓝 μ)) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_one_of_tendsto_conditionalLaw
    exh hq (restriction exh Φ).partition η (restriction exh Ψ).toBoundaryAssignment hμ

/-- At zero edge rate, an arbitrary nontrivial-filter weak limit of source
all-box DLR laws belongs to every coherent all-box target class. -/
theorem mem_allBoxDLRMeasures_of_tendsto_dlr_zero
    {V : Type u} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion.{u, v} G.edgeSet) {q : NNReal} (hq : 0 < q)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq (p := 0) bot_le)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ AllBoxDLRMeasures Φ) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  apply EndpointGlobalFiniteEnergy.mem_dlrMeasures_zero_of_tendsto_dlr
    exh (restriction exh Φ).toBoundaryAssignment (restriction exh Ψ).toBoundaryAssignment
    hq hμ
  filter_upwards [hDLR] with i hi
  exact (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Φ (μs i)).1 hi

/-- At unit edge rate, an arbitrary nontrivial-filter weak limit of source
all-box DLR laws belongs to every coherent all-box target class. -/
theorem mem_allBoxDLRMeasures_of_tendsto_dlr_one
    {V : Type u} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion.{u, v} G.edgeSet) {q : NNReal} (hq : 0 < q)
    (Φ Ψ : AllBoxConvention.{u, v} G.edgeSet hq (p := 1) le_rfl)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ AllBoxDLRMeasures Φ) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  apply EndpointGlobalFiniteEnergy.mem_dlrMeasures_one_of_tendsto_dlr
    exh (restriction exh Φ).toBoundaryAssignment (restriction exh Ψ).toBoundaryAssignment
    hq hμ
  filter_upwards [hDLR] with i hi
  exact (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Φ (μs i)).1 hi

end

end FK.InfiniteVolume.CoherentAllBoxes
