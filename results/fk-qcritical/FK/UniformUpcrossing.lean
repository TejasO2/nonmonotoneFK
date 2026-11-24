import FK.ReverseMartingale

/-!
# A filtration-uniform upcrossing bound

The fixed-filtration reverse-martingale upcrossing estimate of
`FK.ReverseMartingale` has a right-hand side which, for an indicator
`g = 1_C`, is bounded by `b / (K (b - a))` uniformly over the filtration and
the reversal horizon.  This is the estimate needed when the exhaustion
`S_n(ω₃)` depends on an external configuration `ω₃`: for each fixed `ω₃` the
bound is the same, so the upcrossing events can be integrated over `ω₃`
without a measurable choice of the reverse-martingale null set.

This file proves the uniform bound.  It does not prove the joint
measurability of `(ω, η) ↦ μ[1_C | outsideSigma (S_n(η))] ω`, which is the
remaining input for the random-exhaustion argument; the bound is stated for an
arbitrary antitone family of σ-algebras so that it can be applied fibrewise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace FK

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Filtration-uniform upcrossing bound.**  For `0 ≤ g ≤ 1` and an interval
`[a,b] ⊆ [0,1]`, the probability of at least `K` upcrossings of a finite
reverse conditional-expectation process is at most `b / (K (b - a))`,
independently of the antitone filtration `G` and of the horizon `N`. -/
theorem measureReal_upcrossingsBefore_le_uniform
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    {g : Ω → ℝ} (hg_meas : AEStronglyMeasurable g μ)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (K N : ℕ) (hK : 0 < K) :
    μ.real {ω | (K : ℝ) ≤ (upcrossingsBefore (-b) (-a)
      (fun k ω => -(μ[g | G (N - k)]) ω) (N + 1) ω : ℝ)} ≤
      b / ((K : ℝ) * (b - a)) := by
  refine (measureReal_reverse_upcrossingsBefore_le G hG hGm g a b hab K N hK).trans ?_
  have hbpos : 0 < b := lt_of_le_of_lt ha hab
  have hg_int : Integrable g μ := by
    refine ⟨hg_meas, HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω)]
    exact hg1 ω
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ (μ[g | G 0]) ω :=
    condExp_nonneg (Eventually.of_forall hg0)
  have hleone : ∀ᵐ ω ∂μ, (μ[g | G 0]) ω ≤ 1 := by
    have h := condExp_mono (μ := μ) (m := G 0) (f := g) (g := fun _ => (1 : ℝ))
      hg_int (integrable_const 1) (Eventually.of_forall hg1)
    filter_upwards [h] with ω hω
    rw [condExp_const (hGm 0) (1 : ℝ)] at hω
    simpa using hω
  have hbounded : (fun ω => (b - (μ[g | G 0]) ω)⁺) ≤ᵐ[μ] (fun _ => b) := by
    filter_upwards [hnonneg] with ω hω
    have hle : b - (μ[g | G 0]) ω ≤ b := by linarith
    exact max_le hle hbpos.le
  have hInt : ∫ ω, (b - (μ[g | G 0]) ω)⁺ ∂μ ≤ b := by
    have hf_int : Integrable (fun ω => (b - (μ[g | G 0]) ω)⁺) μ := by
      refine ⟨?_, HasFiniteIntegral.of_bounded (C := b) ?_⟩
      · have h1 : StronglyMeasurable (fun ω => (μ[g | G 0]) ω) :=
          stronglyMeasurable_condExp.mono (hGm 0)
        exact ((measurable_const.sub h1.measurable).max measurable_const).aestronglyMeasurable
      · filter_upwards [hnonneg] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hle : b - (μ[g | G 0]) ω ≤ b := by linarith
        exact max_le hle hbpos.le
    calc ∫ ω, (b - (μ[g | G 0]) ω)⁺ ∂μ ≤ ∫ _ω, b ∂μ :=
          integral_mono_ae hf_int (integrable_const b) hbounded
      _ = b := by simp
  exact div_le_div_of_nonneg_right hInt (mul_nonneg (Nat.cast_nonneg K) (sub_pos.2 hab).le)

end FK

/-! ## Axiom audit -/

#print axioms FK.measureReal_upcrossingsBefore_le_uniform
