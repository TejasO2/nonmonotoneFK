import FK.ConditionalLimitUniqueness

/-!
# Tail triviality and unconditional conditional probabilities

This file proves the measure-theoretic tail-triviality step in the proof of
Theorem 5.1 of Beffara--Faipeur--Oke (arXiv:2512.16486).  If a probability
measure assigns every event of a sub-sigma-algebra mass zero or one, then that
sigma-algebra is independent of the ambient sigma-algebra.  Consequently the
conditional probability of every ambient event is its unconditional mass.

The final theorem lifts this statement along the two marginals of a common
auxiliary probability space.  It constructs `CommonConditionalLimits` from
backward convergence to tail conditional expectations and eventual agreement,
without separately assuming the two unconditional limits.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

namespace FK

/-- A probability measure is zero--one on `m` when every `m`-measurable event
has measure zero or one.  For the tail sigma-algebra this is tail triviality. -/
def ZeroOneOn {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (m : MeasurableSpace Ω) (μ : @Measure Ω m₀) : Prop :=
  ∀ s : Set Ω, MeasurableSet[m] s → μ s = 0 ∨ μ s = 1

lemma ZeroOneOn.mono {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {m₁ m₂ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    (h : ZeroOneOn m₂ μ) (hm : m₁ ≤ m₂) : ZeroOneOn m₁ μ :=
  fun _s hs ↦ h _ (hm _ hs)

lemma zeroOneOn_bot {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : @Measure Ω m₀) [IsProbabilityMeasure μ] : ZeroOneOn ⊥ μ := by
  intro s hs
  rw [MeasurableSpace.measurableSet_bot_iff] at hs
  rcases hs with rfl | rfl <;> simp

/-- A zero--one sub-sigma-algebra is independent of every sigma-algebra on the
same probability space. -/
lemma ZeroOneOn.indep_left {Ω : Type*} {m₀ m₁ m₂ : MeasurableSpace Ω}
    (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
    (h : ZeroOneOn m₁ μ) (hm : m₁ ≤ m₀) : Indep m₁ m₂ μ := by
  rw [Indep_iff]
  intro s t hs ht
  rcases h s hs with hs0 | hs1
  · have hst0 : μ (s ∩ t) = 0 := measure_mono_null inter_subset_left hs0
    calc
      μ (s ∩ t) = 0 := hst0
      _ = μ s * μ t := by rw [hs0, zero_mul]
  · have hs_meas : MeasurableSet[m₀] s := hm _ hs
    have hae : ∀ᵐ x ∂μ, x ∈ s := by
      rw [ae_iff]
      change μ sᶜ = 0
      exact (prob_compl_eq_zero_iff hs_meas).2 hs1
    rw [Measure.measure_inter_eq_of_ae hae, hs1, one_mul]

/-- Tail triviality makes conditional probabilities unconditionally constant.
This is the final equality in the displayed backward-martingale computation in
Theorem 5.1 of the paper. -/
theorem condExp_indicator_of_zeroOneOn
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ] {mTail : MeasurableSpace Ω} (hm : mTail ≤ m₀)
    (htail : ZeroOneOn mTail μ) {A : Set Ω} (hA : MeasurableSet[m₀] A) :
    μ⟦A | mTail⟧ =ᵐ[μ] fun _ ↦ μ.real A := by
  have hind : Indep m₀ mTail μ := (htail.indep_left μ hm).symm
  have h := condExp_indep_eq (μ := μ)
    (f := Set.indicator A fun _ ↦ (1 : ℝ)) (m := m₀) (m₁ := m₀) (m₂ := mTail)
    le_rfl hm (stronglyMeasurable_const.indicator hA) hind
  simpa only [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one] using h

/-- Construct common unconditional conditional limits from backward
convergence to tail conditional expectations.  `X` and `Y` are the two
configuration coordinates on the common auxiliary probability space.  The
only convergence inputs are the backward-martingale limits; tail triviality
identifies their limits with the two unconditional masses. -/
theorem commonConditionalLimits_of_zeroOneOn
    {Ω Θ : Type*} {m₀ : MeasurableSpace Ω} [MeasurableSpace Θ]
    (μ ν : @Measure Ω m₀) (ρ : Measure Θ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (mTail : MeasurableSpace Ω) (hm : mTail ≤ m₀)
    (X Y : Θ → Ω) (hX : @Measurable Θ Ω _ m₀ X) (hY : @Measurable Θ Ω _ m₀ Y)
    (hXμ : @Measure.map Θ Ω _ m₀ X ρ = μ) (hYν : @Measure.map Θ Ω _ m₀ Y ρ = ν)
    (hμtail : ZeroOneOn mTail μ) (hνtail : ZeroOneOn mTail ν)
    (cylinders : Set (Set Ω)) (hcyl : ∀ A ∈ cylinders, MeasurableSet[m₀] A)
    (hseq : ∀ A ∈ cylinders, ∃ f g : ℕ → Θ → ℝ,
      (∀ᵐ z ∂ρ, Tendsto (fun n ↦ f n z) atTop (𝓝 ((μ⟦A | mTail⟧) (X z)))) ∧
      (∀ᵐ z ∂ρ, Tendsto (fun n ↦ g n z) atTop (𝓝 ((ν⟦A | mTail⟧) (Y z)))) ∧
      (∀ᵐ z ∂ρ, (fun n ↦ f n z) =ᶠ[atTop] (fun n ↦ g n z))) :
    @CommonConditionalLimits Ω Θ m₀ _ μ ν ρ cylinders := by
  let _ : MeasurableSpace Ω := m₀
  refine { sequences := ?_ }
  intro A hA
  obtain ⟨f, g, hf, hg, hfg⟩ := hseq A hA
  refine ⟨f, g, ?_, ?_, hfg⟩
  · have hμcond := condExp_indicator_of_zeroOneOn hm hμtail (hcyl A hA)
    have hlift : ∀ᵐ z ∂ρ, (μ⟦A | mTail⟧) (X z) = μ.real A := by
      exact (Measure.tendsto_ae_map (μ := ρ) hX.aemeasurable).eventually (by
        rwa [hXμ])
    filter_upwards [hf, hlift] with z hz hzeq
    simpa only [Measure.real, hzeq] using hz
  · have hνcond := condExp_indicator_of_zeroOneOn hm hνtail (hcyl A hA)
    have hlift : ∀ᵐ z ∂ρ, (ν⟦A | mTail⟧) (Y z) = ν.real A := by
      exact (Measure.tendsto_ae_map (μ := ρ) hY.aemeasurable).eventually (by
        rwa [hYν])
    filter_upwards [hg, hlift] with z hz hzeq
    simpa only [Measure.real, hzeq] using hz

/-- Measure equality from eventual free-boundary agreement and backward
convergence to a common tail, when both extremal marginals are tail trivial. -/
theorem measure_eq_of_backwardConditionalLimits_of_zeroOneOn
    {Ω Θ : Type*} {m₀ : MeasurableSpace Ω} [MeasurableSpace Θ]
    (μ ν : @Measure Ω m₀) (ρ : Measure Θ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (mTail : MeasurableSpace Ω) (hm : mTail ≤ m₀)
    (X Y : Θ → Ω) (hX : @Measurable Θ Ω _ m₀ X) (hY : @Measurable Θ Ω _ m₀ Y)
    (hXμ : @Measure.map Θ Ω _ m₀ X ρ = μ) (hYν : @Measure.map Θ Ω _ m₀ Y ρ = ν)
    (hμtail : ZeroOneOn mTail μ) (hνtail : ZeroOneOn mTail ν)
    (cylinders : Set (Set Ω)) (hcyl : ∀ A ∈ cylinders, MeasurableSet[m₀] A)
    (hgen : m₀ = MeasurableSpace.generateFrom cylinders) (hpi : IsPiSystem cylinders)
    (hseq : ∀ A ∈ cylinders, ∃ f g : ℕ → Θ → ℝ,
      (∀ᵐ z ∂ρ, Tendsto (fun n ↦ f n z) atTop (𝓝 ((μ⟦A | mTail⟧) (X z)))) ∧
      (∀ᵐ z ∂ρ, Tendsto (fun n ↦ g n z) atTop (𝓝 ((ν⟦A | mTail⟧) (Y z)))) ∧
      (∀ᵐ z ∂ρ, (fun n ↦ f n z) =ᶠ[atTop] (fun n ↦ g n z))) : μ = ν := by
  exact @measure_eq_of_commonConditionalLimits Ω Θ m₀ _ μ ν ρ _ _ _ cylinders hgen hpi
    (commonConditionalLimits_of_zeroOneOn μ ν ρ mTail hm X Y hX hY hXμ hYν
      hμtail hνtail cylinders hcyl hseq)

end FK
