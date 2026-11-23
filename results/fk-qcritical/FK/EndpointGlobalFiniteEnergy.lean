import FK.GlobalFiniteEnergy
import FK.InteriorEndpointNormalization

/-!
# Endpoint completion for arbitrary-exterior and DLR weak limits

`GlobalFiniteEnergy` proves the interior-rate results. At the endpoints the
finite-energy point-mass floor degenerates, so this file uses the exact
finite-box endpoint laws instead. In particular, arbitrary exterior
configurations are allowed to vary with the exhaustion box.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.EndpointGlobalFiniteEnergy

open ConventionGeometry ConventionTransport
open FK.MainIntegration.Endpoint

noncomputable section

/-- A coordinate-open cylinder has zero mass in an arbitrary-exterior
zero-rate conditional-law weak limit. The exterior may depend on `n`. -/
theorem conditionalLawLimit_apply_open_zero {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 0) bot_le
      (α n) (η n)) atTop (𝓝 μ)) (e : E) :
    (μ : Measure (Configuration E)) {ω | ω e = true} = 0 := by
  let A : Set (Configuration E) := {ω | ω e = true}
  let μs : ℕ → ProbabilityMeasure (Configuration E) := fun n =>
    (exh.box n).conditionalLaw hq (p := 0) bot_le (α n) (η n)
  change Tendsto μs atTop (𝓝 μ) at hμ
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (isClopen_open e)
  change Tendsto (fun n => ENNReal.toNNReal (((μs n : ProbabilityMeasure (Configuration E)) :
    Measure (Configuration E)) A)) atTop
      (𝓝 (ENNReal.toNNReal (((μ : Measure (Configuration E)) A)))) at ht
  have hev : ∀ᶠ n in atTop, ENNReal.toNNReal (((μs n : ProbabilityMeasure
      (Configuration E)) : Measure (Configuration E)) A) = 0 := by
    filter_upwards [exh.eventually_mem e] with n hn
    dsimp [μs]
    rw [show A = {ω : Configuration E | ω e = true} from rfl,
        conditionalLaw_zero_apply_open (exh.box n) hq (α n) (η n) hn]
    rfl
  have hzero : ENNReal.toNNReal (((μ : Measure (Configuration E)) A)) = 0 :=
    tendsto_nhds_unique ht
      (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds)
  exact (((ENNReal.toNNReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _))

/-- A coordinate-closed cylinder has zero mass in an arbitrary-exterior
unit-rate conditional-law weak limit. The exterior may depend on `n`. -/
theorem conditionalLawLimit_apply_closed_one {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 1) le_rfl
      (α n) (η n)) atTop (𝓝 μ)) (e : E) :
    (μ : Measure (Configuration E)) {ω | ω e = false} = 0 := by
  let A : Set (Configuration E) := {ω | ω e = false}
  let μs : ℕ → ProbabilityMeasure (Configuration E) := fun n =>
    (exh.box n).conditionalLaw hq (p := 1) le_rfl (α n) (η n)
  change Tendsto μs atTop (𝓝 μ) at hμ
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
    (isClopen_closed e)
  change Tendsto (fun n => ENNReal.toNNReal (((μs n : ProbabilityMeasure (Configuration E)) :
    Measure (Configuration E)) A)) atTop
      (𝓝 (ENNReal.toNNReal (((μ : Measure (Configuration E)) A)))) at ht
  have hev : ∀ᶠ n in atTop, ENNReal.toNNReal (((μs n : ProbabilityMeasure
      (Configuration E)) : Measure (Configuration E)) A) = 0 := by
    filter_upwards [exh.eventually_mem e] with n hn
    dsimp [μs]
    rw [show A = {ω : Configuration E | ω e = false} from rfl,
        conditionalLaw_one_apply_closed (exh.box n) hq (α n) (η n) hn]
    rfl
  have hzero : ENNReal.toNNReal (((μ : Measure (Configuration E)) A)) = 0 :=
    tendsto_nhds_unique ht
      (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds)
  exact (((ENNReal.toNNReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _))

/-- Every zero-rate arbitrary-exterior conditional-law weak limit is the
all-closed point mass. Neither coherence nor a fixed exterior is needed. -/
theorem eq_closedLaw_of_tendsto_conditionalLaw_zero {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 0) bot_le
      (α n) (η n)) atTop (𝓝 μ)) : μ = closedLaw E := by
  apply eq_closedLaw_of_ae_closed
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simpa using conditionalLawLimit_apply_open_zero exh hq α η hμ e

/-- Every unit-rate arbitrary-exterior conditional-law weak limit is the
all-open point mass. Neither coherence nor a fixed exterior is needed. -/
theorem eq_openLaw_of_tendsto_conditionalLaw_one {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 1) le_rfl
      (α n) (η n)) atTop (𝓝 μ)) : μ = openLaw E := by
  apply eq_openLaw_of_ae_open
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  simpa using conditionalLawLimit_apply_closed_one exh hq α η hμ e

/-- Zero-rate arbitrary-exterior weak limits belong to every target DLR class. -/
theorem mem_dlrMeasures_zero_of_tendsto_conditionalLaw {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior) (Ψ : BoundaryAssignment exh.box)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 0) bot_le
      (α n) (η n)) atTop (𝓝 μ)) :
    μ ∈ DLRMeasures exh Ψ hq (p := 0) bot_le := by
  rw [eq_closedLaw_of_tendsto_conditionalLaw_zero exh hq α η hμ,
    dlrMeasures_zero_eq_singleton exh Ψ hq]
  exact Set.mem_singleton _

/-- Unit-rate arbitrary-exterior weak limits belong to every target DLR class. -/
theorem mem_dlrMeasures_one_of_tendsto_conditionalLaw {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior) (Ψ : BoundaryAssignment exh.box)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq (p := 1) le_rfl
      (α n) (η n)) atTop (𝓝 μ)) :
    μ ∈ DLRMeasures exh Ψ hq (p := 1) le_rfl := by
  rw [eq_openLaw_of_tendsto_conditionalLaw_one exh hq α η hμ,
    dlrMeasures_one_eq_singleton exh Ψ hq]
  exact Set.mem_singleton _

/-- A weak limit of zero-rate DLR laws on one fixed specification is the
all-closed point mass. This works over an arbitrary nontrivial filter. -/
theorem eq_closedLaw_of_tendsto_dlr_zero {E ι : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q : NNReal} (hq : 0 < q) {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq (p := 0) bot_le) :
    μ = closedLaw E := by
  have hev : ∀ᶠ i in l, μs i = closedLaw E := hDLR.mono fun i hi => by
    have hi' : μs i ∈ ({closedLaw E} : Set (ProbabilityMeasure (Configuration E))) := by
      rw [← dlrMeasures_zero_eq_singleton exh Φ hq]
      exact hi
    exact Set.mem_singleton_iff.mp hi'
  exact tendsto_nhds_unique hμ
    (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds)

/-- A weak limit of unit-rate DLR laws on one fixed specification is the
all-open point mass. This works over an arbitrary nontrivial filter. -/
theorem eq_openLaw_of_tendsto_dlr_one {E ι : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q : NNReal} (hq : 0 < q) {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq (p := 1) le_rfl) :
    μ = openLaw E := by
  have hev : ∀ᶠ i in l, μs i = openLaw E := hDLR.mono fun i hi => by
    have hi' : μs i ∈ ({openLaw E} : Set (ProbabilityMeasure (Configuration E))) := by
      rw [← dlrMeasures_one_eq_singleton exh Φ hq]
      exact hi
    exact Set.mem_singleton_iff.mp hi'
  exact tendsto_nhds_unique hμ
    (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds)

/-- Zero-rate weak closure for a fixed DLR specification, with arbitrary
target assignment. -/
theorem mem_dlrMeasures_zero_of_tendsto_dlr {E ι : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ Ψ : BoundaryAssignment exh.box)
    {q : NNReal} (hq : 0 < q) {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq (p := 0) bot_le) :
    μ ∈ DLRMeasures exh Ψ hq (p := 0) bot_le := by
  rw [eq_closedLaw_of_tendsto_dlr_zero exh Φ hq hμ hDLR,
    dlrMeasures_zero_eq_singleton exh Ψ hq]
  exact Set.mem_singleton _

/-- Unit-rate weak closure for a fixed DLR specification, with arbitrary
target assignment. -/
theorem mem_dlrMeasures_one_of_tendsto_dlr {E ι : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ Ψ : BoundaryAssignment exh.box)
    {q : NNReal} (hq : 0 < q) {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq (p := 1) le_rfl) :
    μ ∈ DLRMeasures exh Ψ hq (p := 1) le_rfl := by
  rw [eq_openLaw_of_tendsto_dlr_one exh Φ hq hμ hDLR,
    dlrMeasures_one_eq_singleton exh Ψ hq]
  exact Set.mem_singleton _

/-- All-rate arbitrary-exterior coherent weak-limit transport to a target
DLR class. The interior case is the new finite-energy theorem; the endpoints
are determined by their actual conditional laws. -/
theorem mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp) (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  by_cases hp₀ : 0 < p
  · by_cases hp₁ : p < 1
    · exact GlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne
        exh data hq hp₀ hp₁ Φ Ψ hΦ hΨ η hμ hglobal
    · have hp1 : p = 1 := le_antisymm hp (le_of_not_gt hp₁)
      subst p
      exact mem_dlrMeasures_one_of_tendsto_conditionalLaw exh hq Φ.partition η Ψ hμ
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp₀) zero_le
    subst p
    exact mem_dlrMeasures_zero_of_tendsto_conditionalLaw exh hq Φ.partition η Ψ hμ

/-- All-rate source-Gibbs form of arbitrary-exterior coherent weak-limit
transport. -/
theorem mem_gibbsMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : BoundaryConvention exh hq hp)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ.toBoundaryAssignment)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ GibbsMeasures exh Ψ := by
  exact mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    exh data hq hp Φ Ψ.toBoundaryAssignment hΦ hΨ η hμ hglobal

/-- All-rate closed-exterior specialization. No local constancy of the source
specification is assumed. -/
theorem mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne_of_le_one
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp) (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  apply mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
    exh data hq hp Φ Ψ hΦ hΨ (fun n => (exh.box n).closedExterior) _ hglobal
  simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using hμ

/-- All-rate weak closure of a fixed geometric FK specification. The endpoint
cases use eventual constancy of the approximating laws, not finite energy. -/
theorem mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne_of_le_one
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  by_cases hp₀ : 0 < p
  · by_cases hp₁ : p < 1
    · exact GlobalFiniteEnergy.mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne
        exh data hq hp₀ hp₁ Φ Ψ hΦ hΨ hμ hDLR hglobal
    · have hp1 : p = 1 := le_antisymm hp (le_of_not_gt hp₁)
      subst p
      exact mem_dlrMeasures_one_of_tendsto_dlr exh Φ Ψ hq hμ hDLR
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp₀) zero_le
    subst p
    exact mem_dlrMeasures_zero_of_tendsto_dlr exh Φ Ψ hq hμ hDLR

end

end FK.InfiniteVolume.EndpointGlobalFiniteEnergy
