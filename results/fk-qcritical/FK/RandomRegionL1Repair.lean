import FK.RandomRegionConvergence

/-!
# Repairing the exterior-net input of the random-region comparison

`FK/RandomRegionConvergence.lean` reduces the final step of Theorem 5.1 to
`HasNetExteriorConvergence μ A`, i.e. to the assertion that, off one `μ`-null
set, every exterior conditional `μ⟦A | outsideSigma S⟧` converges to `μ.real A`
along the net of *all* finite edge sets `S`.

That assertion is **false**; `RESULTS.md` contains a probability-normalised
counterexample on the fair coin product law, where the net oscillates between
`0` and `1` on a full-measure set although `μ.real A = 1/2`.

The present file proves the repair.  The comparison needs far less than
almost-everywhere convergence of the net: it is enough that the exterior
conditionals converge to the masses *in mean along the coupling parameter*,
together with the a.e.-eventual agreement of the coupled points.  Mean
convergence in the parameter is exactly what the region-uniform `L¹` estimate
already in the repository supplies (it is uniform in the region, hence in any
region family), so this removes the unprovable hypothesis.

Nothing here uses `sorry`, custom axioms, `unsafe`, or a trust option.  The
statements are phrased in the FK vocabulary (`Configuration`, `outsideSigma`,
`tailSigma`) so that they transport verbatim into the project.
-/

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace FKNetRepair

open FKLimit

/-! ## 1. The abstract repair

If two sequences of `[0,1]`-valued random variables converge *in mean* to the
constants `c` and `d` and agree eventually at almost every point, then `c = d`.
No almost-everywhere convergence of either sequence is needed. -/

theorem real_eq_real_of_tendsto_integral_abs
    {Θ : Type*} [MeasurableSpace Θ] {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {f g : ℕ → Θ → ℝ} {c d : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) ρ) (hg : ∀ n, AEStronglyMeasurable (g n) ρ)
    (hfb : ∀ᵐ z ∂ρ, ∀ n, |f n z| ≤ 1) (hgb : ∀ᵐ z ∂ρ, ∀ n, |g n z| ≤ 1)
    (hf1 : Tendsto (fun n => ∫ z, |f n z - c| ∂ρ) atTop (𝓝 0))
    (hg1 : Tendsto (fun n => ∫ z, |g n z - d| ∂ρ) atTop (𝓝 0))
    (hagree : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop, f n z = g n z) :
    c = d := by
  have hfint : ∀ n, Integrable (f n) ρ :=
    fun n => Integrable.of_bound (hf n) 1 (hfb.mono fun z hz => hz n)
  have hgint : ∀ n, Integrable (g n) ρ :=
    fun n => Integrable.of_bound (hg n) 1 (hgb.mono fun z hz => hz n)
  have hfz : Tendsto (fun n => ∫ z, (f n z - c) ∂ρ) atTop (𝓝 0) := by
    have hle : ∀ n, ‖∫ z, (f n z - c) ∂ρ‖ ≤ ∫ z, |f n z - c| ∂ρ := by
      intro n
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    exact squeeze_zero_norm hle hf1
  have hgz : Tendsto (fun n => ∫ z, (g n z - d) ∂ρ) atTop (𝓝 0) := by
    have hle : ∀ n, ‖∫ z, (g n z - d) ∂ρ‖ ≤ ∫ z, |g n z - d| ∂ρ := by
      intro n
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    exact squeeze_zero_norm hle hg1
  have hfmean : Tendsto (fun n => ∫ z, f n z ∂ρ) atTop (𝓝 c) := by
    have heq : ∀ n, ∫ z, f n z ∂ρ - c = ∫ z, (f n z - c) ∂ρ := by
      intro n
      rw [integral_sub (hfint n) (integrable_const c), integral_const,
        probReal_univ, one_smul]
    have h2 : Tendsto (fun n => (∫ z, f n z ∂ρ - c) + c) atTop (𝓝 (0 + c)) := by
      have h4 := hfz.add (tendsto_const_nhds (x := c))
      simpa only [← heq] using h4
    simpa using h2
  have hgmean : Tendsto (fun n => ∫ z, g n z ∂ρ) atTop (𝓝 d) := by
    have heq : ∀ n, ∫ z, g n z ∂ρ - d = ∫ z, (g n z - d) ∂ρ := by
      intro n
      rw [integral_sub (hgint n) (integrable_const d), integral_const,
        probReal_univ, one_smul]
    have h2 : Tendsto (fun n => (∫ z, g n z ∂ρ - d) + d) atTop (𝓝 (0 + d)) := by
      have h4 := hgz.add (tendsto_const_nhds (x := d))
      simpa only [← heq] using h4
    simpa using h2
  have hdiff : Tendsto (fun n => ∫ z, (f n z - g n z) ∂ρ) atTop (𝓝 0) := by
    have hmeas : ∀ n, AEStronglyMeasurable (fun z => f n z - g n z) ρ :=
      fun n => (hf n).sub (hg n)
    have hbound : ∀ n, ∀ᵐ z ∂ρ, ‖f n z - g n z‖ ≤ (fun _ => (2 : ℝ)) z := by
      intro n
      filter_upwards [hfb, hgb] with z hz1 hz2
      rw [Real.norm_eq_abs]
      calc |f n z - g n z| ≤ |f n z| + |g n z| := abs_sub _ _
        _ ≤ 1 + 1 := by linarith [hz1 n, hz2 n]
        _ = 2 := by norm_num
    have hlim : ∀ᵐ z ∂ρ, Tendsto (fun n => f n z - g n z) atTop
        (𝓝 ((fun _ => (0 : ℝ)) z)) := by
      filter_upwards [hagree] with z hz
      have hzero : (fun n => f n z - g n z) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
        filter_upwards [hz] with n hn
        simp only [hn, sub_self]
      exact tendsto_const_nhds.congr' hzero.symm
    have := tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ)) hmeas
      (integrable_const 2) hbound hlim
    simpa using this
  have hA : Tendsto (fun n => ∫ z, f n z ∂ρ - ∫ z, g n z ∂ρ) atTop (𝓝 (c - d)) :=
    hfmean.sub hgmean
  have hB : Tendsto (fun n => ∫ z, f n z ∂ρ - ∫ z, g n z ∂ρ) atTop (𝓝 0) := by
    have heq : ∀ n, ∫ z, f n z ∂ρ - ∫ z, g n z ∂ρ = ∫ z, (f n z - g n z) ∂ρ :=
      fun n => (integral_sub (hfint n) (hgint n)).symm
    simpa only [heq] using hdiff
  have hcd : c - d = 0 := tendsto_nhds_unique hA hB
  linarith

/-! ## 2. Bounds and the FK form of the repair -/

/-- Exterior conditional probabilities of an event are almost surely bounded by
`1`; transporting along the coupling gives the bound for the coupled
compositions, uniformly in the region. -/
theorem ae_bdd_condExp_comp
    {E : Type*} [Countable E]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    {A : Set (Configuration E)}
    {Θ : Type*} [MeasurableSpace Θ] {ρ : Measure Θ}
    (X : Θ → Configuration E) (hX : AEMeasurable X ρ) (hXμ : Measure.map X ρ = μ)
    (S : ℕ → Θ → Finset E) :
    ∀ᵐ z ∂ρ, ∀ n : ℕ, |((μ)⟦A | outsideSigma (S n z)⟧) (X z)| ≤ 1 := by
  haveI := Finset.countable (α := E)
  have hpoint : ∀ T : Finset E, ∀ᵐ ω ∂μ, |((μ)⟦A | outsideSigma T⟧) ω| ≤ 1 := by
    intro T
    have h := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := μ) (m := outsideSigma T)
      (R := (1 : ℝ)) (f := A.indicator fun _ => (1 : ℝ)) (by
        filter_upwards with ω
        by_cases hω : ω ∈ A <;> simp [Set.indicator, hω])
    simpa using h
  have hall : ∀ᵐ ω ∂μ, ∀ T : Finset E, |((μ)⟦A | outsideSigma T⟧) ω| ≤ 1 :=
    eventually_countable_forall.2 hpoint
  have hset : {ω : Configuration E | ∀ T : Finset E,
      |((μ)⟦A | outsideSigma T⟧) ω| ≤ 1}
      = ⋂ T : Finset E, {ω : Configuration E | |((μ)⟦A | outsideSigma T⟧) ω| ≤ 1} := by
    ext ω
    simp
  have hmeas : MeasurableSet {ω : Configuration E |
      ∀ T : Finset E, |((μ)⟦A | outsideSigma T⟧) ω| ≤ 1} := by
    rw [hset]
    refine MeasurableSet.iInter fun T => ?_
    have hsm : StronglyMeasurable (fun ω => ((μ)⟦A | outsideSigma T⟧) ω) :=
      (stronglyMeasurable_condExp (m := outsideSigma T) (μ := μ)
        (f := A.indicator fun _ => (1 : ℝ))).mono (outsideSigma_le T)
    exact hsm.measurable.abs measurableSet_Iic
  have hall' : ∀ᵐ ω ∂(Measure.map X ρ), ∀ T : Finset E,
      |((μ)⟦A | outsideSigma T⟧) ω| ≤ 1 := by
    rw [hXμ]
    exact hall
  refine ((ae_map_iff hX hmeas).mp hall').mono ?_
  intro z hz n
  exact hz (S n z)

/-- **The repaired comparison step.**  If the exterior conditional probabilities
of `A` converge to the two masses in mean along the coupling parameter and agree
eventually at the coupled points, the masses agree.  Compare
`FK.RandomRegion.real_eq_real_of_eventual_regionAgreement`, which assumes
almost-everywhere convergence at the coupled points; the mean convergence used
here is what the region-uniform `L¹` estimate supplies. -/
theorem real_eq_real_of_L1_regionAgreement
    {E : Type*} [Countable E]
    {Θ : Type*} [MeasurableSpace Θ] {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    (μ ν : Measure (Configuration E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : ℕ → Θ → Finset E) (X Y : Θ → Configuration E)
    (hX : AEMeasurable X ρ) (hXμ : Measure.map X ρ = μ)
    (hY : AEMeasurable Y ρ) (hYν : Measure.map Y ρ = ν)
    {A : Set (Configuration E)}
    (hμmeas : ∀ n, AEStronglyMeasurable
      (fun z => ((μ)⟦A | outsideSigma (S n z)⟧) (X z)) ρ)
    (hνmeas : ∀ n, AEStronglyMeasurable
      (fun z => ((ν)⟦A | outsideSigma (S n z)⟧) (Y z)) ρ)
    (hμL1 : Tendsto (fun n => ∫ z, |((μ)⟦A | outsideSigma (S n z)⟧) (X z)
      - μ.real A| ∂ρ) atTop (𝓝 0))
    (hνL1 : Tendsto (fun n => ∫ z, |((ν)⟦A | outsideSigma (S n z)⟧) (Y z)
      - ν.real A| ∂ρ) atTop (𝓝 0))
    (hagree : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      ((μ)⟦A | outsideSigma (S n z)⟧) (X z) =
        ((ν)⟦A | outsideSigma (S n z)⟧) (Y z)) :
    μ.real A = ν.real A :=
  real_eq_real_of_tendsto_integral_abs hμmeas hνmeas
    (ae_bdd_condExp_comp (A := A) μ X hX hXμ S)
    (ae_bdd_condExp_comp (A := A) ν Y hY hYν S)
    hμL1 hνL1 hagree

/-! ## 3. From the region-uniform estimate to the mean convergence -/

/-- **A region-uniform `L¹` estimate gives mean convergence along every cofinal
exhaustion.**  This turns
`FK.RandomRegion.exists_finset_eLpNorm_condExp_outside_to_tail_le` into the
hypothesis of `real_eq_real_of_tendsto_integral_abs`. -/
theorem tendsto_integral_abs_of_uniform
    {E : Type*} [Countable E]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    {A : Set (Configuration E)} {c : ℝ}
    (huni : ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
      ∫ ω, |((μ)⟦A | outsideSigma S⟧) ω - c| ∂μ ≤ ε)
    (σ : ℕ → Finset E) (hmono : Monotone σ) (hcof : ∀ T : Finset E, ∃ n, T ⊆ σ n) :
    Tendsto (fun n => ∫ ω, |((μ)⟦A | outsideSigma (σ n)⟧) ω - c| ∂μ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := huni (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hcof K
  refine ⟨N, fun n hn => ?_⟩
  have hsub : K ⊆ σ n := Subset.trans hN (hmono hn)
  have h := hK (σ n) hsub
  have hnn : 0 ≤ ∫ ω, |((μ)⟦A | outsideSigma (σ n)⟧) ω - c| ∂μ :=
    integral_nonneg fun ω => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **Bridge from the `eLpNorm` form to integrals.**  The repository's
region-uniform estimate is stated as `eLpNorm … 1 μ ≤ ofReal ε`; the repair
consumes the integral form. -/
theorem integral_abs_le_of_eLpNorm_le
    {E : Type*} [Countable E]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    {f : Configuration E → ℝ} {ε : ℝ} (hf : Integrable f μ) (hε : 0 ≤ ε)
    (h : eLpNorm f 1 μ ≤ ENNReal.ofReal ε) :
    ∫ ω, |f ω| ∂μ ≤ ε := by
  have h1 : ENNReal.ofReal (∫ ω, |f ω| ∂μ) = eLpNorm f 1 μ := by
    calc
      ENNReal.ofReal (∫ ω, |f ω| ∂μ) = ∫⁻ ω, ‖f ω‖ₑ ∂μ :=
        ofReal_integral_norm_eq_lintegral_enorm hf
      _ = eLpNorm f 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  rw [← h1] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp h

/-- **Unconditional comparison along a fixed exhaustion.**  Under the two
region-uniform `L¹` estimates (supplied by tail triviality via
`FK.RandomRegion.exists_finset_eLpNorm_condExp_outside_to_tail_le` and
`FKLimit.condExp_indicator_of_zeroOneOn_tailSigma`) and eventual agreement at
the coupled points of any common coupling, the masses of `A` agree.  No net
convergence and no almost-everywhere sequential convergence is assumed. -/
theorem real_eq_real_of_uniform_regionAgreement
    {E : Type*} [Countable E]
    {Θ : Type*} [MeasurableSpace Θ] {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    (μ ν : Measure (Configuration E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (σ : ℕ → Finset E) (hmono : Monotone σ) (hcof : ∀ T : Finset E, ∃ n, T ⊆ σ n)
    (X Y : Θ → Configuration E)
    (hX : AEMeasurable X ρ) (hXμ : Measure.map X ρ = μ)
    (hY : AEMeasurable Y ρ) (hYν : Measure.map Y ρ = ν)
    {A : Set (Configuration E)}
    (hμmeas : ∀ n, AEStronglyMeasurable
      (fun z => ((μ)⟦A | outsideSigma (σ n)⟧) (X z)) ρ)
    (hνmeas : ∀ n, AEStronglyMeasurable
      (fun z => ((ν)⟦A | outsideSigma (σ n)⟧) (Y z)) ρ)
    (huniμ : ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
      ∫ ω, |((μ)⟦A | outsideSigma S⟧) ω - μ.real A| ∂μ ≤ ε)
    (huniν : ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
      ∫ ω, |((ν)⟦A | outsideSigma S⟧) ω - ν.real A| ∂ν ≤ ε)
    (hagree : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      ((μ)⟦A | outsideSigma (σ n)⟧) (X z) =
        ((ν)⟦A | outsideSigma (σ n)⟧) (Y z)) :
    μ.real A = ν.real A := by
  have hμmap : ∀ n, ∫ z, |((μ)⟦A | outsideSigma (σ n)⟧) (X z) - μ.real A| ∂ρ
      = ∫ ω, |((μ)⟦A | outsideSigma (σ n)⟧) ω - μ.real A| ∂μ := by
    intro n
    have hsm1 : StronglyMeasurable (fun ω => ((μ)⟦A | outsideSigma (σ n)⟧) ω) :=
      (stronglyMeasurable_condExp (m := outsideSigma (σ n)) (μ := μ)
        (f := A.indicator fun _ => (1 : ℝ))).mono (outsideSigma_le (σ n))
    have hsm2 : StronglyMeasurable (fun _ : Configuration E => μ.real A) :=
      stronglyMeasurable_const
    have hsm : AEStronglyMeasurable
        (fun ω => |((μ)⟦A | outsideSigma (σ n)⟧) ω - μ.real A|) μ :=
      ((hsm1.sub hsm2).measurable.abs).aestronglyMeasurable
    have h := integral_map (μ := ρ) (φ := X) hX
      (f := fun ω => |((μ)⟦A | outsideSigma (σ n)⟧) ω - μ.real A|) (by
        rw [hXμ]; exact hsm)
    rw [hXμ] at h
    exact h.symm
  have hνmap : ∀ n, ∫ z, |((ν)⟦A | outsideSigma (σ n)⟧) (Y z) - ν.real A| ∂ρ
      = ∫ ω, |((ν)⟦A | outsideSigma (σ n)⟧) ω - ν.real A| ∂ν := by
    intro n
    have hsm1 : StronglyMeasurable (fun ω => ((ν)⟦A | outsideSigma (σ n)⟧) ω) :=
      (stronglyMeasurable_condExp (m := outsideSigma (σ n)) (μ := ν)
        (f := A.indicator fun _ => (1 : ℝ))).mono (outsideSigma_le (σ n))
    have hsm2 : StronglyMeasurable (fun _ : Configuration E => ν.real A) :=
      stronglyMeasurable_const
    have hsm : AEStronglyMeasurable
        (fun ω => |((ν)⟦A | outsideSigma (σ n)⟧) ω - ν.real A|) ν :=
      ((hsm1.sub hsm2).measurable.abs).aestronglyMeasurable
    have h := integral_map (μ := ρ) (φ := Y) hY
      (f := fun ω => |((ν)⟦A | outsideSigma (σ n)⟧) ω - ν.real A|) (by
        rw [hYν]; exact hsm)
    rw [hYν] at h
    exact h.symm
  refine real_eq_real_of_L1_regionAgreement μ ν (fun n _ => σ n) X Y hX hXμ hY hYν
    hμmeas hνmeas ?_ ?_ hagree
  · simp only [hμmap]
    exact tendsto_integral_abs_of_uniform μ huniμ σ hmono hcof
  · simp only [hνmap]
    exact tendsto_integral_abs_of_uniform ν huniν σ hmono hcof

/-! ## 4. Configuration-dependent regions under an independent region parameter

The region family of Theorem 5.1 is cut out by an auxiliary configuration.  When
the region parameter is independent of the coupled configuration, Fubini reduces
the mean convergence at the coupled points to the region-uniform estimate, with
no net statement anywhere.  The statement is phrased for the product
`ρ₃.prod ρ₁` (region parameter first); `Measure.prod_swap` identifies it with
`ρ₁.prod ρ₃`. -/
theorem tendsto_integral_abs_coupled_prod
    {E : Type*} [Countable E]
    {Θ₁ Θ₃ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₃]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    (ρ₁ : Measure Θ₁) [IsProbabilityMeasure ρ₁]
    (ρ₃ : Measure Θ₃) [IsProbabilityMeasure ρ₃]
    (X : Θ₁ → Configuration E) (hX : AEMeasurable X ρ₁) (hXμ : Measure.map X ρ₁ = μ)
    {A : Set (Configuration E)} {c : ℝ}
    (S : ℕ → Θ₃ → Finset E)
    (hS : ∀ z, Monotone fun n => S n z)
    (hcof : ∀ z, ∀ T : Finset E, ∃ n, T ⊆ S n z)
    (huni : ∀ ε > 0, ∃ K : Finset E, ∀ S' : Finset E, K ⊆ S' →
      ∫ ω, |((μ)⟦A | outsideSigma S'⟧) ω - c| ∂μ ≤ ε)
    (hbc : ∀ᵐ z₁ ∂ρ₁, ∀ T : Finset E, |((μ)⟦A | outsideSigma T⟧) (X z₁)| ≤ 1)
    (hF : ∀ n, StronglyMeasurable (fun z : Θ₃ × Θ₁ =>
      |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c|)) :
    Tendsto (fun n => ∫ z : Θ₃ × Θ₁,
      |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c| ∂(ρ₃.prod ρ₁)) atTop (𝓝 0) := by
  -- the pointwise bound in the configuration variable, for every region
  have hb_abs : ∀ n, ∀ᵐ z ∂(ρ₃.prod ρ₁),
      |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c| ≤ 1 + |c| := by
    intro n
    have hmeas : MeasurableSet {z : Θ₃ × Θ₁ |
        |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c| ≤ 1 + |c|} :=
      (hF n).measurable measurableSet_Iic
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hmeas).mpr ?_
    filter_upwards with z₃
    filter_upwards [hbc] with z₁ hz₁
    have h1 : |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁)| ≤ 1 := hz₁ (S n z₃)
    calc |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c|
        ≤ |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁)| + |c| := abs_sub _ _
      _ ≤ 1 + |c| := by linarith
  have hbound : ∀ n, ∀ᵐ z ∂(ρ₃.prod ρ₁),
      ‖|((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c|‖ ≤ 1 + |c| := by
    intro n
    filter_upwards [hb_abs n] with z hz
    simpa only [Real.norm_eq_abs, abs_abs] using hz
  have hFint : ∀ n, Integrable (fun z : Θ₃ × Θ₁ =>
      |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c|) (ρ₃.prod ρ₁) :=
    fun n => Integrable.of_bound (hF n).aestronglyMeasurable (1 + |c|) (hbound n)
  -- Fubini: the product integral is the ρ₃-mean of the ρ₁-integrals
  have hstep : ∀ n, ∫ z : Θ₃ × Θ₁,
        |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - c| ∂(ρ₃.prod ρ₁)
      = ∫ z₃, (∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁) ∂ρ₃ :=
    fun n => integral_prod _ (hFint n)
  -- for a fixed region the ρ₁-integral is the μ-integral
  have hinner : ∀ (n : ℕ) (z₃ : Θ₃),
      ∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁
        = ∫ ω, |((μ)⟦A | outsideSigma (S n z₃)⟧) ω - c| ∂μ := by
    intro n z₃
    have hsm1 : StronglyMeasurable (fun ω => ((μ)⟦A | outsideSigma (S n z₃)⟧) ω) :=
      (stronglyMeasurable_condExp (m := outsideSigma (S n z₃)) (μ := μ)
        (f := A.indicator fun _ => (1 : ℝ))).mono (outsideSigma_le (S n z₃))
    have hsm2 : StronglyMeasurable (fun _ : Configuration E => c) := stronglyMeasurable_const
    have hsm : AEStronglyMeasurable
        (fun ω => |((μ)⟦A | outsideSigma (S n z₃)⟧) ω - c|) μ :=
      ((hsm1.sub hsm2).measurable.abs).aestronglyMeasurable
    have h := integral_map (μ := ρ₁) (φ := X) hX
      (f := fun ω => |((μ)⟦A | outsideSigma (S n z₃)⟧) ω - c|) (by
        rw [hXμ]; exact hsm)
    rw [hXμ] at h
    exact h.symm
  -- pointwise convergence of the ρ₃-integrand
  have hlim : ∀ᵐ z₃ ∂ρ₃, Tendsto (fun n =>
      ∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁) atTop (𝓝 0) := by
    filter_upwards with z₃
    simp only [hinner]
    exact tendsto_integral_abs_of_uniform μ huni (fun n => S n z₃) (hS z₃) (hcof z₃)
  -- measurability and boundedness of the ρ₃-integrand
  have hmeas3 : ∀ n, AEStronglyMeasurable
      (fun z₃ => ∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁) ρ₃ :=
    fun n => (hF n).integral_prod_right.aestronglyMeasurable
  have hbound3 : ∀ n, ∀ᵐ z₃ ∂ρ₃,
      ‖∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁‖ ≤ 1 + |c| := by
    intro n
    filter_upwards with z₃
    have hpt : ∀ᵐ z₁ ∂ρ₁,
        ‖|((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c|‖ ≤ 1 + |c| := by
      filter_upwards [hbc] with z₁ hz₁
      have h1 : |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁)| ≤ 1 := hz₁ (S n z₃)
      have h2 : |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ≤ 1 + |c| := by
        calc |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c|
            ≤ |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁)| + |c| := abs_sub _ _
          _ ≤ 1 + |c| := by linarith
      simpa only [Real.norm_eq_abs, abs_abs] using h2
    have hpair : Measurable (fun z₁ : Θ₁ => (z₃, z₁)) :=
      Measurable.prod (f := fun z₁ : Θ₁ => (z₃, z₁)) measurable_const measurable_id
    have hcomp : StronglyMeasurable (fun z₁ : Θ₁ =>
        |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c|) :=
      (hF n).comp_measurable hpair
    have hint : Integrable (fun z₁ : Θ₁ =>
        ‖|((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c|‖) ρ₁ :=
      (Integrable.of_bound hcomp.aestronglyMeasurable (1 + |c|) hpt).norm
    calc ‖∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁‖
        ≤ ∫ z₁, ‖|((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c|‖ ∂ρ₁ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z₁, (1 + |c|) ∂ρ₁ := integral_mono_ae hint (integrable_const _) hpt
      _ = 1 + |c| := by simp
  -- dominated convergence in the region parameter
  have hmain : Tendsto (fun n => ∫ z₃,
      (∫ z₁, |((μ)⟦A | outsideSigma (S n z₃)⟧) (X z₁) - c| ∂ρ₁) ∂ρ₃)
      atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun _ : Θ₃ => 1 + |c|) hmeas3
      (integrable_const (1 + |c|)) hbound3 hlim
    simpa using this
  refine hmain.congr' ?_
  filter_upwards with n
  exact (hstep n).symm

/-- **The comparison theorem with a configuration-dependent region family, no net
hypothesis.**  Two tail-trivial laws whose exterior conditionals of `A` agree
eventually at the coupled points of a coupling in which the region parameter is
independent of the coupled pair have the same mass of `A`.  All inputs other than
the agreement are consequences of the region-uniform `L¹` estimate.  This is the
replacement for `FK.RandomRegion.measure_eq_of_netExteriorConvergence`, whose net
hypothesis is false. -/
theorem real_eq_real_of_prodRegionAgreement
    {E : Type*} [Countable E]
    {Θ₁ Θ₃ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₃]
    (μ ν : Measure (Configuration E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ₁ : Measure Θ₁) [IsProbabilityMeasure ρ₁] (ρ₃ : Measure Θ₃) [IsProbabilityMeasure ρ₃]
    (X Y : Θ₁ → Configuration E) (hX : Measurable X) (hXμ : Measure.map X ρ₁ = μ)
    (hY : Measurable Y) (hYν : Measure.map Y ρ₁ = ν)
    (S : ℕ → Θ₃ → Finset E) (hS : ∀ z, Monotone fun n => S n z)
    (hcof : ∀ z, ∀ T : Finset E, ∃ n, T ⊆ S n z)
    {A : Set (Configuration E)}
    (hμmeas : ∀ n, AEStronglyMeasurable
      (fun z : Θ₃ × Θ₁ => ((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2)) (ρ₃.prod ρ₁))
    (hνmeas : ∀ n, AEStronglyMeasurable
      (fun z : Θ₃ × Θ₁ => ((ν)⟦A | outsideSigma (S n z.1)⟧) (Y z.2)) (ρ₃.prod ρ₁))
    (hbcμ : ∀ᵐ z₁ ∂ρ₁, ∀ T : Finset E, |((μ)⟦A | outsideSigma T⟧) (X z₁)| ≤ 1)
    (hbcν : ∀ᵐ z₁ ∂ρ₁, ∀ T : Finset E, |((ν)⟦A | outsideSigma T⟧) (Y z₁)| ≤ 1)
    (hFμ : ∀ n, StronglyMeasurable (fun z : Θ₃ × Θ₁ =>
      |((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) - μ.real A|))
    (hFν : ∀ n, StronglyMeasurable (fun z : Θ₃ × Θ₁ =>
      |((ν)⟦A | outsideSigma (S n z.1)⟧) (Y z.2) - ν.real A|))
    (huniμ : ∀ ε > 0, ∃ K : Finset E, ∀ S' : Finset E, K ⊆ S' →
      ∫ ω, |((μ)⟦A | outsideSigma S'⟧) ω - μ.real A| ∂μ ≤ ε)
    (huniν : ∀ ε > 0, ∃ K : Finset E, ∀ S' : Finset E, K ⊆ S' →
      ∫ ω, |((ν)⟦A | outsideSigma S'⟧) ω - ν.real A| ∂ν ≤ ε)
    (hagree : ∀ᵐ z ∂(ρ₃.prod ρ₁), ∀ᶠ n in atTop,
      ((μ)⟦A | outsideSigma (S n z.1)⟧) (X z.2) =
        ((ν)⟦A | outsideSigma (S n z.1)⟧) (Y z.2)) :
    μ.real A = ν.real A := by
  have hsnd : Measure.map Prod.snd (ρ₃.prod ρ₁) = ρ₁ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hmapX : Measure.map (fun z : Θ₃ × Θ₁ => X z.2) (ρ₃.prod ρ₁) = μ := by
    have h1 : Measure.map (fun z : Θ₃ × Θ₁ => X z.2) (ρ₃.prod ρ₁)
        = Measure.map X (Measure.map Prod.snd (ρ₃.prod ρ₁)) := by
      rw [Measure.map_map hX measurable_snd]
      rfl
    rw [h1, hsnd, hXμ]
  have hmapY : Measure.map (fun z : Θ₃ × Θ₁ => Y z.2) (ρ₃.prod ρ₁) = ν := by
    have h1 : Measure.map (fun z : Θ₃ × Θ₁ => Y z.2) (ρ₃.prod ρ₁)
        = Measure.map Y (Measure.map Prod.snd (ρ₃.prod ρ₁)) := by
      rw [Measure.map_map hY measurable_snd]
      rfl
    rw [h1, hsnd, hYν]
  refine real_eq_real_of_L1_regionAgreement μ ν (fun n (z : Θ₃ × Θ₁) => S n z.1)
    (fun (z : Θ₃ × Θ₁) => X z.2) (fun (z : Θ₃ × Θ₁) => Y z.2)
    (hX.comp measurable_snd).aemeasurable hmapX (hY.comp measurable_snd).aemeasurable hmapY
    hμmeas hνmeas ?_ ?_ hagree
  · exact tendsto_integral_abs_coupled_prod μ ρ₁ ρ₃ X hX.aemeasurable hXμ S hS hcof
      huniμ hbcμ hFμ
  · exact tendsto_integral_abs_coupled_prod ν ρ₁ ρ₃ Y hY.aemeasurable hYν S hS hcof
      huniν hbcν hFν

end FKNetRepair

/-! ## Axiom audit -/

#print axioms FKNetRepair.real_eq_real_of_tendsto_integral_abs
#print axioms FKNetRepair.ae_bdd_condExp_comp
#print axioms FKNetRepair.real_eq_real_of_L1_regionAgreement
#print axioms FKNetRepair.tendsto_integral_abs_of_uniform
#print axioms FKNetRepair.integral_abs_le_of_eLpNorm_le
#print axioms FKNetRepair.real_eq_real_of_uniform_regionAgreement
#print axioms FKNetRepair.tendsto_integral_abs_coupled_prod
#print axioms FKNetRepair.real_eq_real_of_prodRegionAgreement
