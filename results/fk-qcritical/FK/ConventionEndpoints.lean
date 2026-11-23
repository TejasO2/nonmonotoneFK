import FK.ConventionTransport
import FK.EndpointIntegration

/-! Deterministic endpoint DLR classes; no convention geometry is needed. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.ConventionTransport

open FK.MainIntegration.Endpoint

noncomputable section

local instance endpointSetoidMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance endpointFiniteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

lemma fkMeasure_eq_dirac_allClosed {E : Type*} (B : FiniteBox E) {q : NNReal}
    (hq : 0 < q) (α : B.BoundaryPartition) :
    B.graph.fkMeasure hq (p := 0) bot_le α = Measure.dirac (fun _ => false) := by
  simp only [FK.Finite.LabelledMultigraph.fkMeasure,
    FK.Finite.LabelledMultigraph.fkPMF_zero, PMF.toMeasure_pure]
  rfl

lemma fkMeasure_eq_dirac_allOpen {E : Type*} (B : FiniteBox E) {q : NNReal}
    (hq : 0 < q) (α : B.BoundaryPartition) :
    B.graph.fkMeasure hq (p := 1) le_rfl α = Measure.dirac (fun _ => true) := by
  simp only [FK.Finite.LabelledMultigraph.fkMeasure,
    FK.Finite.LabelledMultigraph.fkPMF_one, PMF.toMeasure_pure]
  rfl

lemma exteriorMeasure_closedLaw {E : Type*} (B : FiniteBox E) :
    B.exteriorMeasure (closedLaw E) =
      ⟨Measure.dirac B.closedExterior, inferInstance⟩ := by
  apply Subtype.ext
  change Measure.map (Prod.fst ∘ B.splitEquiv) (Measure.dirac (fun _ => false)) = _
  rw [Measure.map_dirac' (measurable_fst.comp B.splitEquiv.measurable)]
  rfl

lemma exteriorMeasure_openLaw {E : Type*} (B : FiniteBox E) :
    B.exteriorMeasure (openLaw E) =
      ⟨Measure.dirac (fun _ => true), inferInstance⟩ := by
  apply Subtype.ext
  change Measure.map (Prod.fst ∘ B.splitEquiv) (Measure.dirac (fun _ => true)) = _
  rw [Measure.map_dirac' (measurable_fst.comp B.splitEquiv.measurable)]
  rfl

lemma isDLR_closedLaw_zero {E : Type*} (B : FiniteBox E) {q : NNReal} (hq : 0 < q)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    B.IsDLR hq (p := 0) bot_le α hα (closedLaw E) := by
  unfold FiniteBox.IsDLR
  rw [exteriorMeasure_closedLaw]
  ext s hs
  change (Measure.map B.splitEquiv (Measure.dirac (fun _ => false))) s =
    ((Measure.dirac B.closedExterior) ⊗ₘ B.fkKernel hq bot_le α hα) s
  rw [Measure.map_dirac' B.splitEquiv.measurable, Measure.compProd_apply hs, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hs)]
  change (Measure.dirac (B.splitEquiv (fun _ => false))) s =
    B.graph.fkMeasure hq bot_le (α B.closedExterior)
      (Prod.mk B.closedExterior ⁻¹' s)
  rw [fkMeasure_eq_dirac_allClosed]
  simp only [Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl

lemma isDLR_openLaw_one {E : Type*} (B : FiniteBox E) {q : NNReal} (hq : 0 < q)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    B.IsDLR hq (p := 1) le_rfl α hα (openLaw E) := by
  unfold FiniteBox.IsDLR
  rw [exteriorMeasure_openLaw]
  ext s hs
  change (Measure.map B.splitEquiv (Measure.dirac (fun _ => true))) s =
    ((Measure.dirac (fun _ => true)) ⊗ₘ B.fkKernel hq le_rfl α hα) s
  rw [Measure.map_dirac' B.splitEquiv.measurable, Measure.compProd_apply hs, lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left hs)]
  change (Measure.dirac (B.splitEquiv (fun _ => true))) s =
    B.graph.fkMeasure hq le_rfl (α (fun _ => true))
      (Prod.mk (fun _ => true) ⁻¹' s)
  rw [fkMeasure_eq_dirac_allOpen]
  simp only [Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl


/-- At zero rate every DLR class is exactly the all-closed point mass. -/
theorem dlrMeasures_zero_eq_singleton {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q : NNReal} (hq : 0 < q) :
    DLRMeasures exh Φ hq (p := 0) bot_le = {closedLaw E} := by
  ext μ
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hμ
    apply eq_closedLaw_of_ae_closed
    rw [ae_all_iff]
    intro e
    rw [ae_iff]
    simpa using dlr_apply_open_zero exh Φ hq hμ e
  · rintro rfl n
    exact isDLR_closedLaw_zero (exh.box n) hq (Φ.partition n) (Φ.measurable_partition n)

/-- At unit rate every DLR class is exactly the all-open point mass. -/
theorem dlrMeasures_one_eq_singleton {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q : NNReal} (hq : 0 < q) :
    DLRMeasures exh Φ hq (p := 1) le_rfl = {openLaw E} := by
  ext μ
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hμ
    apply eq_openLaw_of_ae_open
    rw [ae_all_iff]
    intro e
    rw [ae_iff]
    simpa using dlr_apply_closed_one exh Φ hq hμ e
  · rintro rfl n
    exact isDLR_openLaw_one (exh.box n) hq (Φ.partition n) (Φ.measurable_partition n)

/-- All-rate DLR transport for an actual global simple graph. Interior rates
use the full-support exterior argument; endpoint rates are deterministic. -/
theorem mem_dlrMeasures_of_globalAtMostOne_of_le_one {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ Ψ : BoundaryAssignment exh.box)
    (hΦ : IsGeometric data.geometry Φ) (hΨ : IsGeometric data.geometry Ψ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  by_cases hp₀ : 0 < p
  · by_cases hp₁ : p < 1
    · exact SimpleGraphBoxData.mem_dlrMeasures_of_global_atMostOne exh data hq hp₀ hp₁
        Φ Ψ hΦ hΨ μ hμ hglobal
    · have hp1 : p = 1 := le_antisymm hp (le_of_not_gt hp₁)
      subst p
      rw [dlrMeasures_one_eq_singleton exh Φ hq] at hμ
      rw [dlrMeasures_one_eq_singleton exh Ψ hq]
      exact hμ
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp₀) zero_le
    subst p
    rw [dlrMeasures_zero_eq_singleton exh Φ hq] at hμ
    rw [dlrMeasures_zero_eq_singleton exh Ψ hq]
    exact hμ

/-- All-rate Gibbs-to-Gibbs part of Proposition 1.8(2) for an actual global
simple graph. The only convention inputs are their actual nesting coherence
and the two geometric compatibility properties from the paper. -/
theorem mem_gibbsMeasures_of_globalAtMostOne_of_le_one {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ Ψ : BoundaryConvention exh hq hp)
    (hΦ : IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : IsGeometric data.geometry Ψ.toBoundaryAssignment)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ GibbsMeasures exh Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ GibbsMeasures exh Ψ := by
  exact mem_dlrMeasures_of_globalAtMostOne_of_le_one exh data hq hp
    Φ.toBoundaryAssignment Ψ.toBoundaryAssignment hΦ hΨ μ hμ hglobal

/-- At zero rate, even the weak-limit half is immediate: every FK weak limit
and every Gibbs law is the all-closed point mass. -/
theorem mem_gibbsMeasures_zero_of_mem_limitOrGibbs {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} {hq : 0 < q}
    (Ψ : BoundaryConvention exh hq (p := 0) bot_le)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ LimitOrGibbsMeasures exh hq (p := 0) bot_le) :
    μ ∈ GibbsMeasures exh Ψ := by
  change μ ∈ DLRMeasures exh Ψ.toBoundaryAssignment hq bot_le
  rw [limitOrGibbs_eq_closedLaw_zero exh hq hμ,
    dlrMeasures_zero_eq_singleton exh Ψ.toBoundaryAssignment hq]
  exact Set.mem_singleton _

/-- At unit rate, every FK weak limit and every Gibbs law is the all-open
point mass, so it lies in every convention's Gibbs class. -/
theorem mem_gibbsMeasures_one_of_mem_limitOrGibbs {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} {hq : 0 < q}
    (Ψ : BoundaryConvention exh hq (p := 1) le_rfl)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ LimitOrGibbsMeasures exh hq (p := 1) le_rfl) :
    μ ∈ GibbsMeasures exh Ψ := by
  change μ ∈ DLRMeasures exh Ψ.toBoundaryAssignment hq le_rfl
  rw [limitOrGibbs_eq_openLaw_one exh hq hμ,
    dlrMeasures_one_eq_singleton exh Ψ.toBoundaryAssignment hq]
  exact Set.mem_singleton _

end
end FK.InfiniteVolume.ConventionTransport
