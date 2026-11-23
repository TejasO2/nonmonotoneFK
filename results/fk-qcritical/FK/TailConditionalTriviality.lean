import FK.NewestModulesValidation
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Simultaneous tail triviality of tail conditional laws

The proof is the countable-field covariance argument of Berti--Rigo,
*0--1 laws for regular conditional distributions*, Theorem 15.  It uses only
countable generating algebras for the exterior filtration and backward
martingale convergence; the exterior tail is never assumed countably
generated and no uncountable intersection of null sets is used.
-/

open Filter Set MeasureTheory ProbabilityTheory FKLimit
open scoped ENNReal NNReal Topology ProbabilityTheory symmDiff

namespace FK

universe u

/-- A canonical countable algebra generating a countably generated measurable
space.  The measurable-space argument is explicit so that this can be used for
sub-sigma-algebras of a fixed ambient space. -/
noncomputable def generatingSetAlgebra {Ω : Type*} (m : MeasurableSpace Ω)
    [h : @MeasurableSpace.CountablyGenerated Ω m] : Set (Set Ω) :=
  generateSetAlgebra (@MeasurableSpace.countableGeneratingSet Ω m h)

lemma countable_generatingSetAlgebra {Ω : Type*} (m : MeasurableSpace Ω)
    [h : @MeasurableSpace.CountablyGenerated Ω m] :
    (generatingSetAlgebra m).Countable :=
  countable_generateSetAlgebra
    (@MeasurableSpace.countable_countableGeneratingSet Ω m h)

lemma isSetAlgebra_generatingSetAlgebra {Ω : Type*} (m : MeasurableSpace Ω)
    [h : @MeasurableSpace.CountablyGenerated Ω m] :
    IsSetAlgebra (generatingSetAlgebra m) :=
  isSetAlgebra_generateSetAlgebra

lemma generateFrom_generatingSetAlgebra {Ω : Type*} (m : MeasurableSpace Ω)
    [h : @MeasurableSpace.CountablyGenerated Ω m] :
    m = MeasurableSpace.generateFrom (generatingSetAlgebra m) := by
  rw [generatingSetAlgebra, generateFrom_generateSetAlgebra_eq]
  exact (@MeasurableSpace.generateFrom_countableGeneratingSet Ω m h).symm

lemma measurableSet_of_mem_generatingSetAlgebra {Ω : Type*} (m : MeasurableSpace Ω)
    [h : @MeasurableSpace.CountablyGenerated Ω m]
    {A : Set Ω} (hA : A ∈ generatingSetAlgebra m) : MeasurableSet[m] A := by
  rw [generateFrom_generatingSetAlgebra m]
  exact MeasurableSpace.measurableSet_generateFrom hA

/-- Finite-measure approximation by the canonical generating algebra. -/
lemma exists_mem_generatingSetAlgebra_symmDiff_lt_sameSpace
    {Ω : Type*} {m : MeasurableSpace Ω}
    [h : @MeasurableSpace.CountablyGenerated Ω m]
    (μ : @Measure Ω m) [IsFiniteMeasure μ]
    {H : Set Ω} (hH : MeasurableSet[m] H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ generatingSetAlgebra m, μ (H ∆ A) < ENNReal.ofReal ε := by
  have hdense : μ.MeasureDense (generatingSetAlgebra m) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ
      (isSetAlgebra_generatingSetAlgebra m) (generateFrom_generatingSetAlgebra m)
  exact hdense.approx H hH (measure_ne_top μ H) ε hε

/-- Finite-measure approximation by the canonical generating algebra, with
both the approximation mass and the original mass evaluated on the ambient
measurable space. -/
lemma exists_mem_generatingSetAlgebra_symmDiff_lt
    {Ω : Type*} {m m₀ : MeasurableSpace Ω}
    [h : @MeasurableSpace.CountablyGenerated Ω m]
    (μ : @Measure Ω m₀) [IsFiniteMeasure μ] (hm : m ≤ m₀)
    {H : Set Ω} (hH : MeasurableSet[m] H) {ε : ℝ} (hε : 0 < ε) :
    ∃ A ∈ generatingSetAlgebra m, μ (H ∆ A) < ENNReal.ofReal ε := by
  let ν : @Measure Ω m := @Measure.trim Ω m m₀ μ hm
  letI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  obtain ⟨A, hA, hlt⟩ := exists_mem_generatingSetAlgebra_symmDiff_lt_sameSpace
    ν hH hε
  refine ⟨A, hA, ?_⟩
  change ν (H ∆ A) < ENNReal.ofReal ε at hlt
  have heq : ν (H ∆ A) = μ (H ∆ A) :=
    trim_measurableSet_eq hm (hH.symmDiff (measurableSet_of_mem_generatingSetAlgebra m hA))
  rwa [heq] at hlt

end FK


namespace FK

/-- Conditional covariance against an `m₁`-measurable test event is bounded by
the conditional `L¹` distance between the `m₁`- and `m`-conditional laws. -/
lemma abs_condExp_inter_covariance_le
    {Ω : Type*} {m m₁ m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ] (hm : m ≤ m₀) (hm₁ : m₁ ≤ m₀) (hmm₁ : m ≤ m₁)
    {A C : Set Ω} (hA : MeasurableSet[m₁] A) (hC : MeasurableSet[m₀] C) :
    (fun ω ↦ |(μ⟦A ∩ C | m⟧) ω - (μ⟦A | m⟧) ω * (μ⟦C | m⟧) ω|) ≤ᵐ[μ]
      μ[fun ω ↦ |(μ⟦C | m₁⟧) ω - (μ⟦C | m⟧) ω| | m] := by
  let f : Ω → ℝ := A.indicator fun _ ↦ 1
  let g : Ω → ℝ := C.indicator fun _ ↦ 1
  let z : Ω → ℝ := μ[g | m₁] - μ[g | m]
  have hA₀ : MeasurableSet[m₀] A := hm₁ A hA
  have hfm : Measurable[m₁] f := measurable_const.indicator hA
  have hfm₀ : Measurable f := measurable_const.indicator hA₀
  have hgm₀ : Measurable g := measurable_const.indicator hC
  have hfint : Integrable f μ := (integrable_const 1).indicator hA₀
  have hgint : Integrable g μ := (integrable_const 1).indicator hC
  have hfbdd : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ A <;> simp [f, Set.indicator, hω]
  have hgbdd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ C <;> simp [g, Set.indicator, hω]
  have hfgint : Integrable (f * g) μ := hgint.bdd_mul hfm₀.aestronglyMeasurable hfbdd
  have hzint : Integrable z μ := integrable_condExp.sub integrable_condExp
  have hfzint : Integrable (f * z) μ := hzint.bdd_mul hfm₀.aestronglyMeasurable hfbdd
  have hfbint : Integrable (f * μ[g | m]) μ :=
    integrable_condExp.bdd_mul hfm₀.aestronglyMeasurable hfbdd
  have hfbnint : Integrable (f * μ[g | m₁]) μ :=
    integrable_condExp.bdd_mul hfm₀.aestronglyMeasurable hfbdd
  have hpull : μ[f * g | m₁] =ᵐ[μ] f * μ[g | m₁] :=
    condExp_mul_of_aestronglyMeasurable_left hfm.aestronglyMeasurable hfgint hgint
  have hmain : μ[f * μ[g | m₁] | m] =ᵐ[μ] μ[f * g | m] := by
    calc
      μ[f * μ[g | m₁] | m] =ᵐ[μ] μ[μ[f * g | m₁] | m] :=
        condExp_congr_ae hpull.symm
      _ =ᵐ[μ] μ[f * g | m] := condExp_condExp_of_le hmm₁ hm₁
  have hright : μ[f * μ[g | m] | m] =ᵐ[μ] μ[f | m] * μ[g | m] :=
    condExp_mul_of_aestronglyMeasurable_right
      stronglyMeasurable_condExp.aestronglyMeasurable hfbint hfint
  have hcov : μ[f * z | m] =ᵐ[μ] μ[f * g | m] - μ[f | m] * μ[g | m] := by
    calc
      μ[f * z | m] =ᵐ[μ] μ[f * μ[g | m₁] - f * μ[g | m] | m] := by
        apply condExp_congr_ae
        filter_upwards [] with ω
        simp only [z, Pi.sub_apply, Pi.mul_apply, mul_sub]
      _ =ᵐ[μ] μ[f * μ[g | m₁] | m] - μ[f * μ[g | m] | m] :=
        condExp_sub hfbnint hfbint m
      _ =ᵐ[μ] μ[f * g | m] - μ[f | m] * μ[g | m] := hmain.sub hright
  have hle : (fun ω ↦ |(f * z) ω|) ≤ᵐ[μ] (fun ω ↦ |z ω|) := by
    filter_upwards [] with ω
    have hfabs : |f ω| ≤ (1 : ℝ) := by
      by_cases hω : ω ∈ A <;> simp [f, Set.indicator, hω]
    calc
      |(f * z) ω| = |f ω| * |z ω| := by rw [Pi.mul_apply, abs_mul]
      _ ≤ 1 * |z ω| := mul_le_mul_of_nonneg_right hfabs (abs_nonneg _)
      _ = |z ω| := one_mul _
  have hmono : μ[fun ω ↦ |(f * z) ω| | m] ≤ᵐ[μ] μ[fun ω ↦ |z ω| | m] :=
    condExp_mono hfzint.abs hzint.abs hle
  have hinter : (A ∩ C).indicator (fun _ : Ω ↦ (1 : ℝ)) = f * g := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωC : ω ∈ C <;>
      simp [f, g, hωA, hωC]
  rw [hinter]
  change (fun ω ↦ |(μ[f * g | m]) ω - (μ[f | m]) ω * (μ[g | m]) ω|) ≤ᵐ[μ]
    μ[fun ω ↦ |z ω| | m]
  filter_upwards [hcov, abs_condExp_ae_le_condExp_abs (μ := μ) (m := m) (f * z),
    hmono] with ω hcovω habsω hmonoω
  have hcovω' : (μ[f * g | m]) ω - (μ[f | m]) ω * (μ[g | m]) ω =
      (μ[f * z | m]) ω := hcovω.symm
  rw [hcovω']
  exact habsω.trans hmonoω

end FK


namespace FKLimit

universe uE

/-- Exterior σ-algebras on a countable edge type are countably generated. -/
instance countablyGeneratedOutsideSigma {E : Type uE} [Countable E] (S : Finset E) :
    @MeasurableSpace.CountablyGenerated (Configuration E) (outsideSigma S) := by
  unfold outsideSigma
  exact MeasurableSpace.CountablyGenerated.comap _

end FKLimit

namespace FK.InfiniteVolume

open FK

universe u

/-- Difference between the exterior and tail conditional probabilities of one
ambient event. -/
noncomputable def exteriorIndicatorDiscrepancy {E : Type u}
    (μ : Measure (Configuration E)) (S : ℕ → Finset E) (C : Set (Configuration E)) (n : ℕ) :
    Configuration E → ℝ := fun ω ↦
  |(μ⟦C | FKLimit.outsideSigma (S n)⟧) ω - (μ⟦C | FKLimit.tailSigma⟧) ω|

/-- Conditional `L¹` size of `exteriorIndicatorDiscrepancy` on the tail. -/
noncomputable def tailDisintegrationError {E : Type u}
    (μ : Measure (Configuration E)) (S : ℕ → Finset E)
    (C : Set (Configuration E)) (n : ℕ) : Configuration E → ℝ :=
  μ[exteriorIndicatorDiscrepancy μ S C n | FKLimit.tailSigma]

/-- The RCP covariance bound for all test events in one exterior algebra. -/
lemma ae_tailConditionalKernel_covariance_le {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) (S : ℕ → Finset E)
    {C : Set (Configuration E)} (hC : MeasurableSet C) (n : ℕ)
    {A : Set (Configuration E)} (hA : MeasurableSet[FKLimit.outsideSigma (S n)] A) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      |(tailConditionalKernel μ ω).real (A ∩ C) -
        (tailConditionalKernel μ ω).real A * (tailConditionalKernel μ ω).real C| ≤
        tailDisintegrationError (μ : Measure (Configuration E)) S C n ω := by
  have hA₀ : MeasurableSet A := FKLimit.outsideSigma_le (S n) A hA
  have hcov := FK.abs_condExp_inter_covariance_le
    (μ := (μ : Measure (Configuration E))) FKLimit.tailSigma_le
    (FKLimit.outsideSigma_le (S n)) (FKLimit.tailSigma_le_outsideSigma (S n)) hA hC
  have hκA : (fun ω ↦ (tailConditionalKernel μ ω).real A) =ᵐ[(μ : Measure (Configuration E))]
      (μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧ :=
    condExpKernel_ae_eq_condExp FKLimit.tailSigma_le hA₀
  have hκC : (fun ω ↦ (tailConditionalKernel μ ω).real C) =ᵐ[(μ : Measure (Configuration E))]
      (μ : Measure (Configuration E))⟦C | FKLimit.tailSigma⟧ :=
    condExpKernel_ae_eq_condExp FKLimit.tailSigma_le hC
  have hκAC : (fun ω ↦ (tailConditionalKernel μ ω).real (A ∩ C)) =ᵐ[(μ : Measure (Configuration E))]
      (μ : Measure (Configuration E))⟦A ∩ C | FKLimit.tailSigma⟧ :=
    condExpKernel_ae_eq_condExp FKLimit.tailSigma_le (hA₀.inter hC)
  change (fun ω ↦ |((μ : Measure (Configuration E))⟦A ∩ C | FKLimit.tailSigma⟧) ω -
    ((μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) ω *
      ((μ : Measure (Configuration E))⟦C | FKLimit.tailSigma⟧) ω|) ≤ᵐ[(μ : Measure (Configuration E))]
    tailDisintegrationError (μ : Measure (Configuration E)) S C n at hcov
  filter_upwards [hcov, hκA, hκC, hκAC] with ω hcovω hAω hCω hACω
  rw [hAω, hCω, hACω]
  exact hcovω

/-- A subsequence along which the conditional covariance control for a fixed
ambient event tends to zero almost surely. -/
lemma exists_tailDisintegrationError_subsequence {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E))
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {C : Set (Configuration E)} (hC : MeasurableSet C) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun k ↦ tailDisintegrationError (μ : Measure (Configuration E)) S C (u k) ω)
        atTop (𝓝 0) := by
  let Z : ℕ → Configuration E → ℝ := fun n ↦
    (μ : Measure (Configuration E))⟦C | FKLimit.outsideSigma (S n)⟧ -
      (μ : Measure (Configuration E))⟦C | FKLimit.tailSigma⟧
  let R : ℕ → Configuration E → ℝ := fun n ↦
    tailDisintegrationError (μ : Measure (Configuration E)) S C n
  have hZm (n : ℕ) : AEStronglyMeasurable (Z n) (μ : Measure (Configuration E)) := by
    dsimp [Z]
    exact (((stronglyMeasurable_condExp (μ := (μ : Measure (Configuration E)))
      (m := FKLimit.outsideSigma (S n))).mono (FKLimit.outsideSigma_le _)).sub
        ((stronglyMeasurable_condExp (μ := (μ : Measure (Configuration E)))
          (m := FKLimit.tailSigma)).mono FKLimit.tailSigma_le)).aestronglyMeasurable
  have hZ : Tendsto (fun n ↦ eLpNorm (Z n) 1 (μ : Measure (Configuration E)))
      atTop (𝓝 0) := FKLimit.tendsto_eLpNorm_one_condExp_indicator_outside_to_tail
        S hS hcof hC
  have hRle (n : ℕ) : eLpNorm (R n) 1 (μ : Measure (Configuration E)) ≤
      eLpNorm (Z n) 1 (μ : Measure (Configuration E)) := by
    calc
      eLpNorm (R n) 1 (μ : Measure (Configuration E)) ≤
          eLpNorm (fun ω ↦ |Z n ω|) 1 (μ : Measure (Configuration E)) := by
        exact eLpNorm_condExp_le_eLpNorm _ le_rfl
      _ = eLpNorm (Z n) 1 (μ : Measure (Configuration E)) := by
        simpa only [Real.norm_eq_abs] using eLpNorm_norm (Z n) (hZm n)
  have hR : Tendsto (fun n ↦ eLpNorm (R n) 1 (μ : Measure (Configuration E)))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hZ
      (fun _ ↦ bot_le) hRle
  have hRin : TendstoInMeasure (μ : Measure (Configuration E)) R atTop 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    simpa only [Pi.zero_apply, sub_zero] using hR
  obtain ⟨u, hu, hμu⟩ := hRin.exists_seq_tendsto_ae
  refine ⟨u, hu, ?_⟩
  simpa only [R, Pi.zero_apply] using hμu

end FK.InfiniteVolume


namespace FK

/-- Real covariance of two events under a finite measure. -/
noncomputable def measureRealCovariance {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : @Measure Ω m₀) (A B : Set Ω) : ℝ :=
  |μ.real (A ∩ B) - μ.real A * μ.real B|

lemma measureRealCovariance_comm {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (μ : @Measure Ω m₀) (A B : Set Ω) :
    measureRealCovariance μ A B = measureRealCovariance μ B A := by
  simp only [measureRealCovariance, Set.inter_comm, mul_comm]

/-- Approximating the first event in a covariance costs at most twice its
symmetric-difference mass. -/
lemma measureRealCovariance_le_left_approx
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
    {H A B : Set Ω} (hH : MeasurableSet H) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    measureRealCovariance μ H B ≤ measureRealCovariance μ A B + 2 * μ.real (H ∆ A) := by
  have h_inter : |μ.real (H ∩ B) - μ.real (A ∩ B)| ≤ μ.real (H ∆ A) := by
    calc
      |μ.real (H ∩ B) - μ.real (A ∩ B)| ≤ μ.real ((H ∩ B) ∆ (A ∩ B)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hH.inter hB).nullMeasurableSet (hA.inter hB).nullMeasurableSet
      _ = μ.real ((H ∆ A) ∩ B) := by rw [inter_symmDiff_distrib_right]
      _ ≤ μ.real (H ∆ A) := measureReal_mono inter_subset_left
  have h_mul : |μ.real H * μ.real B - μ.real A * μ.real B| ≤ μ.real (H ∆ A) := by
    have hdiff : |μ.real H - μ.real A| ≤ μ.real (H ∆ A) :=
      abs_measureReal_sub_le_measureReal_symmDiff hH.nullMeasurableSet hA.nullMeasurableSet
    have hB_abs : |μ.real B| ≤ (1 : ℝ) := by
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
    calc
      |μ.real H * μ.real B - μ.real A * μ.real B| =
          |μ.real H - μ.real A| * |μ.real B| := by rw [← sub_mul, abs_mul]
      _ ≤ |μ.real H - μ.real A| := mul_le_of_le_one_right (abs_nonneg _) hB_abs
      _ = |μ.real A - μ.real H| := abs_sub_comm _ _
      _ ≤ μ.real (A ∆ H) :=
        abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hH.nullMeasurableSet
      _ = μ.real (H ∆ A) := by rw [symmDiff_comm]
  unfold measureRealCovariance
  calc
    |μ.real (H ∩ B) - μ.real H * μ.real B| ≤
        |μ.real (H ∩ B) - μ.real (A ∩ B)| +
          |μ.real (A ∩ B) - μ.real H * μ.real B| := abs_sub_le _ _ _
    _ ≤ |μ.real (H ∩ B) - μ.real (A ∩ B)| +
          (|μ.real (A ∩ B) - μ.real A * μ.real B| +
            |μ.real A * μ.real B - μ.real H * μ.real B|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ ≤ μ.real (H ∆ A) + |μ.real (A ∩ B) - μ.real A * μ.real B| + μ.real (H ∆ A) := by
      have h_mul' : |μ.real A * μ.real B - μ.real H * μ.real B| ≤ μ.real (H ∆ A) := by
        rw [abs_sub_comm]
        exact h_mul
      linarith
    _ = |μ.real (A ∩ B) - μ.real A * μ.real B| + 2 * μ.real (H ∆ A) := by ring

end FK

namespace FK.InfiniteVolume

open FK

universe u

/-- Covariance bounds and an a.e.-null error subsequence for one ambient
countable-algebra test event. -/
lemma exists_tail_covariance_control {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E))
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {C : Set (Configuration E)} (hC : MeasurableSet C) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      (∀ n A, A ∈ generatingSetAlgebra (FKLimit.outsideSigma (S n)) →
        measureRealCovariance (tailConditionalKernel μ ω) A C ≤
          tailDisintegrationError (μ : Measure (Configuration E)) S C n ω) ∧
      Tendsto (fun k ↦ tailDisintegrationError (μ : Measure (Configuration E)) S C (u k) ω)
        atTop (𝓝 0) := by
  obtain ⟨u, hu, hlim⟩ := exists_tailDisintegrationError_subsequence μ S hS hcof hC
  have hbound : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ∀ n A, A ∈ generatingSetAlgebra (FKLimit.outsideSigma (S n)) →
        measureRealCovariance (tailConditionalKernel μ ω) A C ≤
          tailDisintegrationError (μ : Measure (Configuration E)) S C n ω := by
    rw [ae_all_iff]
    intro n
    rw [ae_ball_iff (countable_generatingSetAlgebra (FKLimit.outsideSigma (S n)))]
    intro A hA
    exact ae_tailConditionalKernel_covariance_le μ S hC n
      (measurableSet_of_mem_generatingSetAlgebra _ hA)
  exact ⟨u, hu, hbound.and hlim⟩

end FK.InfiniteVolume


namespace FK.InfiniteVolume

open FK

universe u

/-- Almost every tail RCP fibre is simultaneously zero--one on the entire
exterior tail.  The tail itself is not assumed countably generated. -/
theorem ae_zeroOneOn_tailConditionalKernel {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E))
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.ZeroOneOn FKLimit.tailSigma (tailConditionalKernel μ ω) := by
  classical
  let 𝒞 : Set (Set (Configuration E)) :=
    generatingSetAlgebra (MeasurableSpace.pi : MeasurableSpace (Configuration E))
  have h𝒞 : 𝒞.Countable := countable_generatingSetAlgebra _
  have hcontrol : ∀ C ∈ 𝒞, ∃ u : ℕ → ℕ, StrictMono u ∧
      ∀ᵐ ω ∂(μ : Measure (Configuration E)),
        (∀ n A, A ∈ generatingSetAlgebra (FKLimit.outsideSigma (S n)) →
          measureRealCovariance (tailConditionalKernel μ ω) A C ≤
            tailDisintegrationError (μ : Measure (Configuration E)) S C n ω) ∧
        Tendsto (fun k ↦ tailDisintegrationError (μ : Measure (Configuration E)) S C (u k) ω)
          atTop (𝓝 0) := by
    intro C hC
    exact exists_tail_covariance_control μ S hS hcof
      (measurableSet_of_mem_generatingSetAlgebra _ hC)
  choose u hu hgood using hcontrol
  have hall : ∀ᵐ ω ∂(μ : Measure (Configuration E)), ∀ C (hC : C ∈ 𝒞),
      (∀ n A, A ∈ generatingSetAlgebra (FKLimit.outsideSigma (S n)) →
        measureRealCovariance (tailConditionalKernel μ ω) A C ≤
          tailDisintegrationError (μ : Measure (Configuration E)) S C n ω) ∧
      Tendsto (fun k ↦ tailDisintegrationError (μ : Measure (Configuration E)) S C (u C hC k) ω)
        atTop (𝓝 0) := (ae_ball_iff h𝒞).2 hgood
  filter_upwards [hall] with ω hω
  let Q : Measure (Configuration E) := tailConditionalKernel μ ω
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  intro H hH
  have hH₀ : MeasurableSet H := FKLimit.tailSigma_le H hH
  have hcovzero : measureRealCovariance Q H H = 0 := by
    apply eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)
    intro ε hε
    have hε8 : 0 < ε / 8 := by positivity
    obtain ⟨C, hCmem, hCδ⟩ := exists_mem_generatingSetAlgebra_symmDiff_lt
      Q le_rfl hH₀ hε8
    have hCfull : MeasurableSet C := measurableSet_of_mem_generatingSetAlgebra _ hCmem
    have hCδreal : Q.real (H ∆ C) < ε / 8 :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top Q (H ∆ C))).1 hCδ
    have hboundlim := hω C hCmem
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hboundlim.2 (ε / 4) (by positivity)
    let n : ℕ := u C hCmem N
    have hR : tailDisintegrationError (μ : Measure (Configuration E)) S C n ω < ε / 4 := by
      calc
        tailDisintegrationError (μ : Measure (Configuration E)) S C n ω ≤
            |tailDisintegrationError (μ : Measure (Configuration E)) S C n ω| :=
          le_abs_self _
        _ < ε / 4 := by
          simpa only [n, Real.dist_eq, sub_zero] using hN N le_rfl
    have hHout : MeasurableSet[FKLimit.outsideSigma (S n)] H :=
      FKLimit.tailSigma_le_outsideSigma (S n) H hH
    obtain ⟨A, hAmem, hAδ⟩ := exists_mem_generatingSetAlgebra_symmDiff_lt
      Q (FKLimit.outsideSigma_le (S n)) hHout hε8
    have hAfull : MeasurableSet A := FKLimit.outsideSigma_le (S n) A
      (measurableSet_of_mem_generatingSetAlgebra (FKLimit.outsideSigma (S n)) hAmem)
    have hAδreal : Q.real (H ∆ A) < ε / 8 :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top Q (H ∆ A))).1 hAδ
    have hcov : measureRealCovariance Q A C ≤
        tailDisintegrationError (μ : Measure (Configuration E)) S C n ω := by
      exact hboundlim.1 n A hAmem
    have hleft : measureRealCovariance Q H H ≤
        measureRealCovariance Q A H + 2 * Q.real (H ∆ A) :=
      measureRealCovariance_le_left_approx Q hH₀ hAfull hH₀
    have hright : measureRealCovariance Q A H ≤
        measureRealCovariance Q A C + 2 * Q.real (H ∆ C) := by
      rw [measureRealCovariance_comm Q A H, measureRealCovariance_comm Q A C]
      exact measureRealCovariance_le_left_approx Q hH₀ hCfull hAfull
    change |Q.real (H ∩ H) - Q.real H * Q.real H| ≤ ε
    dsimp [measureRealCovariance] at hleft hright hcov
    nlinarith
  have hsq : Q.real H = Q.real H * Q.real H := by
    unfold measureRealCovariance at hcovzero
    rw [Set.inter_self, abs_eq_zero] at hcovzero
    exact sub_eq_zero.mp hcovzero
  have hfactor : Q.real H * (1 - Q.real H) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · left
    exact (measureReal_eq_zero_iff).1 hzero
  · right
    have hreal : Q.real H = 1 := by linarith
    exact (ENNReal.toReal_eq_one_iff (Q H)).1 hreal

/-- Bundled `ProbabilityMeasure` form of simultaneous tail-fibre triviality. -/
theorem ae_zeroOneOn_tailConditionalLaw {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E))
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.ZeroOneOn FKLimit.tailSigma
        (tailConditionalLaw μ ω : Measure (Configuration E)) := by
  exact ae_zeroOneOn_tailConditionalKernel μ S hS hcof

end FK.InfiniteVolume


namespace FK.InfiniteVolume

open FK

universe u v

local instance tailConditionalTrivialityBoundaryMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

/-- Almost-everywhere convergence of finite-FK exterior conditional
probabilities for a tail-trivial DLR law.  This is the tail-triviality
hypothesis form of the extremal-law theorem in `ReverseMartingale`. -/
theorem tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_zeroOneOn_dlr
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (htail : FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (Configuration E)))
    {A : Set (Configuration E)} {T : Finset E}
    (hAT : FKLimit.DependsOnCoordinates A T) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ ((exh.box n).conditionalLaw hq hp (Φ.partition n)
        (FKLimit.exteriorRestriction (exh.box n).edges ω) :
        Measure (Configuration E)).real A) atTop
        (𝓝 ((μ : Measure (Configuration E)).real A)) := by
  let S : ℕ → Finset E := fun n ↦ (exh.box n).edges
  have hcof : ∀ T : Finset E, ∃ n, T ⊆ S n := by
    intro T
    exact (exh.eventually_subset T).exists
  have hbase := FKLimit.tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn
    (μ := (μ : Measure (Configuration E))) S exh.monotone hcof
    hAT.measurableSet htail
  have hid : ∀ᵐ ω ∂(μ : Measure (Configuration E)), ∀ n,
      T ⊆ (exh.box n).edges →
      ((μ : Measure (Configuration E))⟦A |
        FKLimit.outsideSigma (exh.box n).edges⟧) ω =
        ((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real A := by
    rw [ae_all_iff]
    intro n
    by_cases hn : T ⊆ (exh.box n).edges
    · filter_upwards [(exh.box n).condExp_of_dependsOn_edges_of_isDLR hq hp
        (Φ.partition n) (Φ.measurable_partition n) μ (hμ n) (hAT.mono hn)] with ω hω
      exact fun _ ↦ hω
    · exact Eventually.of_forall fun _ h ↦ (hn h).elim
  filter_upwards [hbase, hid] with ω hlim hidω
  apply hlim.congr'
  filter_upwards [exh.eventually_subset T] with n hn
  exact hidω n hn

/-- If the actual finite-FK exterior conditional probabilities of a DLR law
converge almost surely to a constant, that constant is the law's unconditional
mass. -/
theorem measureReal_eq_of_tendsto_exteriorConditionalLaw
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ν : ProbabilityMeasure (Configuration E)) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    {A : Set (Configuration E)} {T : Finset E}
    (hAT : FKLimit.DependsOnCoordinates A T) {a : ℝ}
    (hlim : ∀ᵐ ω ∂(ν : Measure (Configuration E)),
      Tendsto (fun n ↦ ((exh.box n).conditionalLaw hq hp (Φ.partition n)
        (FKLimit.exteriorRestriction (exh.box n).edges ω) :
        Measure (Configuration E)).real A) atTop (𝓝 a)) :
    (ν : Measure (Configuration E)).real A = a := by
  let F : ℕ → Configuration E → ℝ := fun n ω ↦
    ((exh.box n).conditionalLaw hq hp (Φ.partition n)
      (FKLimit.exteriorRestriction (exh.box n).edges ω) :
      Measure (Configuration E)).real A
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (ν : Measure (Configuration E)) := by
    exact ((measurable_conditionalLaw_apply (exh.box n) hq hp
      (Φ.partition n) (Φ.measurable_partition n) hAT.measurableSet).comp
        (FKLimit.measurable_exteriorRestriction
          (exh.box n).edges)).ennreal_toReal.stronglyMeasurable.aestronglyMeasurable
  have hFb (n : ℕ) : ∀ᵐ ω ∂(ν : Measure (Configuration E)), ‖F n ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hInt : (fun n ↦ ∫ ω, F n ω ∂(ν : Measure (Configuration E))) =ᶠ[atTop]
      fun _ ↦ (ν : Measure (Configuration E)).real A := by
    filter_upwards [exh.eventually_subset T] with n hn
    have hid := (exh.box n).condExp_of_dependsOn_edges_of_isDLR hq hp
      (Φ.partition n) (Φ.measurable_partition n) ν (hν n) (hAT.mono hn)
    calc
      (∫ ω, F n ω ∂(ν : Measure (Configuration E))) =
          ∫ ω, ((ν : Measure (Configuration E))⟦A |
            FKLimit.outsideSigma (exh.box n).edges⟧) ω
            ∂(ν : Measure (Configuration E)) := integral_congr_ae hid.symm
      _ = ∫ ω, A.indicator 1 ω ∂(ν : Measure (Configuration E)) :=
        integral_condExp (FKLimit.outsideSigma_le _)
      _ = (ν : Measure (Configuration E)).real A := integral_indicator_one hAT.measurableSet
  have hIntLim : Tendsto (fun n ↦ ∫ ω, F n ω ∂(ν : Measure (Configuration E)))
      atTop (𝓝 ((ν : Measure (Configuration E)).real A)) :=
    tendsto_const_nhds.congr' hInt.symm
  have hdom : Tendsto (fun n ↦ ∫ ω, F n ω ∂(ν : Measure (Configuration E)))
      atTop (𝓝 (∫ _ω, a ∂(ν : Measure (Configuration E)))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) hFm
      (integrable_const 1) hFb
    exact hlim
  have ha : (∫ _ω, a ∂(ν : Measure (Configuration E))) = a := by simp
  rw [ha] at hdom
  exact tendsto_nhds_unique hIntLim hdom

/-- Tail-trivial DLR laws are extremal in the DLR simplex. -/
theorem isExtremalIn_dlr_of_zeroOneOn_tail
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (htail : FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (Configuration E))) :
    FK.IsExtremalIn
      ((fun ν : ProbabilityMeasure (Configuration E) ↦
        (ν : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)) := by
  refine ⟨⟨μ, hμ, rfl⟩, ?_⟩
  intro ν hν ρ hρ c d hc hd hcd hdecomp
  rcases hν with ⟨ν, hν, rfl⟩
  have hνμ : (ν : Measure (Configuration E)) ≪ (μ : Measure (Configuration E)) := by
    have hac : (ν : Measure (Configuration E)) ≪ c • (ν : Measure (Configuration E)) :=
      Measure.absolutelyContinuous_smul hc
    apply hac.trans
    rw [hdecomp]
    exact Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl _
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I J
  have hmass : (ν : Measure (Configuration E)).real (MeasureTheory.cylinder I J) =
      (μ : Measure (Configuration E)).real (MeasureTheory.cylinder I J) := by
    apply measureReal_eq_of_tendsto_exteriorConditionalLaw exh Φ hq hp ν hν
      (dependsOnCoordinates_cylinder I J)
    exact hνμ.ae_le
      (tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_zeroOneOn_dlr
        exh Φ hq hp μ hμ htail (dependsOnCoordinates_cylinder I J))
  rw [← ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (ν : Measure (Configuration E)) _)
    (measure_ne_top (μ : Measure (Configuration E)) _)]
  exact hmass

/-- Extremality and tail triviality coincide on the DLR simplex. -/
theorem isExtremalIn_dlr_iff_zeroOneOn_tail
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    FK.IsExtremalIn
      ((fun ν : ProbabilityMeasure (Configuration E) ↦
        (ν : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)) ↔
      FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (Configuration E)) :=
  ⟨zeroOneOn_tailSigma_of_extremal_dlr exh Φ hq hp μ hμ,
    isExtremalIn_dlr_of_zeroOneOn_tail exh Φ hq hp μ hμ⟩

end FK.InfiniteVolume


namespace FK.InfiniteVolume

open FK

universe u v

/-- Almost every tail fibre of an arbitrary DLR law is an extremal DLR law. -/
theorem ae_isExtremalIn_dlr_tailConditionalLaw
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.IsExtremalIn
        ((fun ν : ProbabilityMeasure (Configuration E) ↦
          (ν : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (tailConditionalLaw μ ω : Measure (Configuration E)) := by
  let S : ℕ → Finset E := fun n ↦ (exh.box n).edges
  have hcof : ∀ T : Finset E, ∃ n, T ⊆ S n := by
    intro T
    exact (exh.eventually_subset T).exists
  filter_upwards [ae_mem_dlrMeasures_tailConditionalLaw exh Φ hq hp μ hμ,
    ae_zeroOneOn_tailConditionalLaw μ S exh.monotone hcof] with ω hDLR htail
  exact isExtremalIn_dlr_of_zeroOneOn_tail exh Φ hq hp
    (tailConditionalLaw μ ω) hDLR htail

/-- The existing RCP barycenter is a genuine Choquet decomposition: almost
every random law in its source representation is extremal DLR. -/
theorem dlr_tailChoquet_decomposition
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    (∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.IsExtremalIn
        ((fun ν : ProbabilityMeasure (Configuration E) ↦
          (ν : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (tailConditionalLaw μ ω : Measure (Configuration E))) ∧
      ∀ A : Set (Configuration E), MeasurableSet A →
        (∫⁻ ν, (ν : Measure (Configuration E)) A ∂(tailLawDistribution μ :
          Measure (ProbabilityMeasure (Configuration E)))) =
          (μ : Measure (Configuration E)) A := by
  exact ⟨ae_isExtremalIn_dlr_tailConditionalLaw exh Φ hq hp μ hμ,
    fun A hA ↦ lintegral_tailLawDistribution μ hA⟩

/-- Uniqueness of an extremal DLR law implies uniqueness of the whole DLR
class, by the actual tail Choquet decomposition. -/
theorem eq_dlr_of_extremal_unique
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ μ₀ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hunique : ∀ ν : ProbabilityMeasure (Configuration E),
      FK.IsExtremalIn
        ((fun ξ : ProbabilityMeasure (Configuration E) ↦
          (ξ : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (ν : Measure (Configuration E)) → ν = μ₀) :
    μ = μ₀ := by
  exact eq_dlr_of_ae_isExtremal_tailConditionalLaw exh Φ hq hp μ μ₀ hunique
    (ae_isExtremalIn_dlr_tailConditionalLaw exh Φ hq hp μ hμ)

/-- Almost every tail fibre of an arbitrary DLR law lies in the normalized
active-device weak-limit class, with no separate fibre-extremality premise. -/
theorem ae_mem_fkLimitMeasures_tailConditionalLaw
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      tailConditionalLaw μ ω ∈ FKLimitMeasures exh hq hp := by
  filter_upwards [ae_mem_dlrMeasures_tailConditionalLaw exh Φ hq hp μ hμ,
    ae_isExtremalIn_dlr_tailConditionalLaw exh Φ hq hp μ hμ] with ω hDLR hext
  exact mem_fkLimitMeasures_of_extremal_dlr exh Φ hq hp (tailConditionalLaw μ ω) hDLR hext

end FK.InfiniteVolume
