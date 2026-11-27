import FK.MovingClopenRate

/-! Moving-rate limits and DLR from a dominating law with vanishing escape tails. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace FK.InfiniteVolume.MovingClopenRate

open FK.InfiniteVolume.OneEdgeNoEscape

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

local instance boundaryPartitionMeasurableSpaceMovingDominated (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} [Countable E]

/-- Dominated-tail form of `openBit_eq_limitRate_of_clopen_escape`. -/
theorem openBit_eq_limitRate_of_dominated_escape_eventual
    (B : FiniteBox E) (e : B.edges)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C lower : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    {esc : ℕ → Set (Configuration E)}
    (hCcl : ∀ n, IsClopen (C n)) (hlowerCl : ∀ m, IsClopen (lower m))
    (hlowerMono : Monotone lower)
    (hUnion : ∀ ω, (∃ m, ω ∈ lower m) ↔ ω ∈ Cinf)
    (hsub : ∀ m, ∀ᶠ n in atTop, lower m ⊆ C n)
    (hsdiff : ∀ m, ∀ᶠ n in atTop, C n \ lower m ⊆ esc m)
    (hescMeas : ∀ m, MeasurableSet (esc m)) (hescUp : ∀ m, IsUpperSet (esc m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν (μs n))
    (hν : Tendsto (fun m => ((ν : Measure (Configuration E)) (esc m)).toReal) atTop (𝓝 0))
    (hfin : ∀ (n : ℕ) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs n : Measure (Configuration E)) =
        ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β (C n) ω) * g (B.splitOff e ω)
          ∂(μs n : Measure (Configuration E)))
    (φ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (hφ : ∀ y, 0 ≤ φ y) :
    (∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E))) =
      ∫ ω, twoValuedRate α β Cinf ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)) := by
  let a : ℕ → ℝ := fun n => ∫ ω, B.openBitTest e φ ω ∂(μs n : Measure (Configuration E))
  let b : ℕ → ℝ := fun m => ∫ ω, twoValuedRate α β (lower m) ω * B.offTest e φ ω
    ∂(μ : Measure (Configuration E))
  let K : ℝ := |α - β| * ‖φ‖
  let r : ℕ → ℝ := fun m => K * ((ν : Measure (Configuration E)) (esc m)).toReal +
    1 / (m + 1 : ℝ)
  have hC0 : ∀ n ω, 0 ≤ twoValuedRate α β (C n) ω := fun n ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (C n) ω).1
  have hC1 : ∀ n ω, twoValuedRate α β (C n) ω ≤ 1 := fun n ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (C n) ω).2
  have ha : Tendsto a atTop (𝓝 (∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E)))) := by
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
      (BoundedContinuousFunction.mkOfCompact ⟨B.openBitTest e φ, B.continuous_openBitTest e φ⟩)
  have hb : Tendsto b atTop
      (𝓝 (∫ ω, twoValuedRate α β Cinf ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    · intro m
      exact ((continuous_twoValuedRate α β (hlowerCl m)).measurable.mul
        (B.measurable_offTest e φ)).aestronglyMeasurable
    · exact integrable_const ‖φ‖
    · intro m
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ twoValuedRate α β (lower m) ω *
        B.offTest e φ ω from mul_nonneg
          (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (lower m) ω).1 (hφ _))]
      simpa only [one_mul] using (show twoValuedRate α β (lower m) ω * B.offTest e φ ω ≤ 1 * ‖φ‖ from
        mul_le_mul (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (lower m) ω).2
          (B.offTest_le_norm e φ hφ ω) (hφ _) zero_le_one)
    · filter_upwards with ω
      exact (tendsto_twoValuedRate_of_monotone_union hlowerMono hUnion ω).mul_const _
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => K * ((ν : Measure (Configuration E)) (esc m)).toReal)
        atTop (𝓝 (K * 0)) := hν.const_mul K
    have h2 : Tendsto (fun m : ℕ => 1 / (m + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [r, mul_zero, add_zero] using h1.add h2
  have hbound : ∀ m, ∀ᶠ n in atTop, |a n - b m| ≤ r m := by
    intro m
    let c : ℕ → ℝ := fun n => ∫ ω, twoValuedRate α β (lower m) ω * B.offTest e φ ω
      ∂(μs n : Measure (Configuration E))
    have hc : Tendsto c atTop (𝓝 (b m)) := by
      exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
        (BoundedContinuousFunction.mkOfCompact
          ⟨fun ω => twoValuedRate α β (lower m) ω * B.offTest e φ ω,
            (continuous_twoValuedRate α β (hlowerCl m)).mul (B.continuous_offTest e φ)⟩)
    have hs : 0 < (1 / (m + 1 : ℝ)) := by positivity
    have hclose : ∀ᶠ n in atTop, |c n - b m| ≤ 1 / (m + 1 : ℝ) := by
      have ht : Tendsto (fun n => |c n - b m|) atTop (𝓝 |b m - b m|) :=
        (hc.sub tendsto_const_nhds).abs
      simp only [sub_self, abs_zero] at ht
      exact (tendsto_order.1 ht).2 _ hs |>.mono fun n hn => le_of_lt hn
    filter_upwards [hsub m, hsdiff m, hclose] with n hsubn hdiffn hcn
    have hstage : a n = ∫ ω, twoValuedRate α β (C n) ω * B.offTest e φ ω
        ∂(μs n : Measure (Configuration E)) := by
      exact B.finiteStage_real e μs (fun n => twoValuedRate α β (C n))
        (fun n => continuous_twoValuedRate α β (hCcl n)) hC0 hC1 hfin n φ hφ
    have herr : |a n - c n| ≤ K * ((μs n : Measure (Configuration E)) (C n \ lower m)).toReal := by
      rw [hstage]
      exact abs_integral_twoValuedRate_sub_mul_offTest_le B e hα0 hαβ hβ1
        (hCcl n) (hlowerCl m) hsubn φ hφ (μs n : Measure (Configuration E))
    have hle : ((μs n : Measure (Configuration E)) (C n \ lower m)) ≤
        ((ν : Measure (Configuration E)) (esc m)) := by
      calc
        ((μs n : Measure (Configuration E)) (C n \ lower m)) ≤
            ((μs n : Measure (Configuration E)) (esc m)) := measure_mono hdiffn
        _ ≤ ((ν : Measure (Configuration E)) (esc m)) :=
          FKLimit.ennreal_le_of_probabilityMeasure_apply_le (hdom n (esc m) (hescMeas m) (hescUp m))
    have herr' : |a n - c n| ≤ K * ((ν : Measure (Configuration E)) (esc m)).toReal :=
      herr.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hle) hK0)
    calc
      |a n - b m| = |(a n - c n) + (c n - b m)| := by congr 1; ring
      _ ≤ |a n - c n| + |c n - b m| := abs_add_le _ _
      _ ≤ K * ((ν : Measure (Configuration E)) (esc m)).toReal + 1 / (m + 1 : ℝ) :=
        add_le_add herr' hcn
      _ = r m := rfl
  exact FKModel.eq_of_tendsto_of_eventually_abs_sub_le ha hb hr hbound

/-- Dominated-tail form of `openBit_eq_limitRate_of_clopen_escape`. -/
theorem openBit_eq_limitRate_of_dominated_escape
    (B : FiniteBox E) (e : B.edges)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C lower : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    {esc : ℕ → Set (Configuration E)}
    (hCcl : ∀ n, IsClopen (C n)) (hlowerCl : ∀ m, IsClopen (lower m))
    (hlowerMono : Monotone lower)
    (hUnion : ∀ ω, (∃ m, ω ∈ lower m) ↔ ω ∈ Cinf)
    (hsub : ∀ m n, m ≤ n → lower m ⊆ C n)
    (hsdiff : ∀ m n, m ≤ n → C n \ lower m ⊆ esc m)
    (hescMeas : ∀ m, MeasurableSet (esc m)) (hescUp : ∀ m, IsUpperSet (esc m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν (μs n))
    (hν : Tendsto (fun m => ((ν : Measure (Configuration E)) (esc m)).toReal) atTop (𝓝 0))
    (hfin : ∀ (n : ℕ) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs n : Measure (Configuration E)) =
        ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β (C n) ω) * g (B.splitOff e ω)
          ∂(μs n : Measure (Configuration E)))
    (φ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (hφ : ∀ y, 0 ≤ φ y) :
    (∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E))) =
      ∫ ω, twoValuedRate α β Cinf ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)) := by
  let a : ℕ → ℝ := fun n => ∫ ω, B.openBitTest e φ ω ∂(μs n : Measure (Configuration E))
  let b : ℕ → ℝ := fun m => ∫ ω, twoValuedRate α β (lower m) ω * B.offTest e φ ω
    ∂(μ : Measure (Configuration E))
  let K : ℝ := |α - β| * ‖φ‖
  let r : ℕ → ℝ := fun m => K * ((ν : Measure (Configuration E)) (esc m)).toReal +
    1 / (m + 1 : ℝ)
  have hC0 : ∀ n ω, 0 ≤ twoValuedRate α β (C n) ω := fun n ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (C n) ω).1
  have hC1 : ∀ n ω, twoValuedRate α β (C n) ω ≤ 1 := fun n ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (C n) ω).2
  have ha : Tendsto a atTop (𝓝 (∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E)))) := by
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
      (BoundedContinuousFunction.mkOfCompact ⟨B.openBitTest e φ, B.continuous_openBitTest e φ⟩)
  have hb : Tendsto b atTop
      (𝓝 (∫ ω, twoValuedRate α β Cinf ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    · intro m
      exact ((continuous_twoValuedRate α β (hlowerCl m)).measurable.mul
        (B.measurable_offTest e φ)).aestronglyMeasurable
    · exact integrable_const ‖φ‖
    · intro m
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ twoValuedRate α β (lower m) ω *
        B.offTest e φ ω from mul_nonneg
          (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (lower m) ω).1 (hφ _))]
      simpa only [one_mul] using (show twoValuedRate α β (lower m) ω * B.offTest e φ ω ≤ 1 * ‖φ‖ from
        mul_le_mul (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (lower m) ω).2
          (B.offTest_le_norm e φ hφ ω) (hφ _) zero_le_one)
    · filter_upwards with ω
      exact (tendsto_twoValuedRate_of_monotone_union hlowerMono hUnion ω).mul_const _
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => K * ((ν : Measure (Configuration E)) (esc m)).toReal)
        atTop (𝓝 (K * 0)) := hν.const_mul K
    have h2 : Tendsto (fun m : ℕ => 1 / (m + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [r, mul_zero, add_zero] using h1.add h2
  have hbound : ∀ m, ∀ᶠ n in atTop, |a n - b m| ≤ r m := by
    intro m
    let c : ℕ → ℝ := fun n => ∫ ω, twoValuedRate α β (lower m) ω * B.offTest e φ ω
      ∂(μs n : Measure (Configuration E))
    have hc : Tendsto c atTop (𝓝 (b m)) := by
      exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
        (BoundedContinuousFunction.mkOfCompact
          ⟨fun ω => twoValuedRate α β (lower m) ω * B.offTest e φ ω,
            (continuous_twoValuedRate α β (hlowerCl m)).mul (B.continuous_offTest e φ)⟩)
    have hs : 0 < (1 / (m + 1 : ℝ)) := by positivity
    have hclose : ∀ᶠ n in atTop, |c n - b m| ≤ 1 / (m + 1 : ℝ) := by
      have ht : Tendsto (fun n => |c n - b m|) atTop (𝓝 |b m - b m|) :=
        (hc.sub tendsto_const_nhds).abs
      simp only [sub_self, abs_zero] at ht
      exact (tendsto_order.1 ht).2 _ hs |>.mono fun n hn => le_of_lt hn
    filter_upwards [eventually_ge_atTop m, hclose] with n hmn hcn
    have hstage : a n = ∫ ω, twoValuedRate α β (C n) ω * B.offTest e φ ω
        ∂(μs n : Measure (Configuration E)) := by
      exact B.finiteStage_real e μs (fun n => twoValuedRate α β (C n))
        (fun n => continuous_twoValuedRate α β (hCcl n)) hC0 hC1 hfin n φ hφ
    have herr : |a n - c n| ≤ K * ((μs n : Measure (Configuration E)) (C n \ lower m)).toReal := by
      rw [hstage]
      exact abs_integral_twoValuedRate_sub_mul_offTest_le B e hα0 hαβ hβ1
        (hCcl n) (hlowerCl m) (hsub m n hmn) φ hφ (μs n : Measure (Configuration E))
    have hle : ((μs n : Measure (Configuration E)) (C n \ lower m)) ≤
        ((ν : Measure (Configuration E)) (esc m)) := by
      calc
        ((μs n : Measure (Configuration E)) (C n \ lower m)) ≤
            ((μs n : Measure (Configuration E)) (esc m)) := measure_mono (hsdiff m n hmn)
        _ ≤ ((ν : Measure (Configuration E)) (esc m)) :=
          FKLimit.ennreal_le_of_probabilityMeasure_apply_le (hdom n (esc m) (hescMeas m) (hescUp m))
    have herr' : |a n - c n| ≤ K * ((ν : Measure (Configuration E)) (esc m)).toReal :=
      herr.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hle) hK0)
    calc
      |a n - b m| = |(a n - c n) + (c n - b m)| := by congr 1; ring
      _ ≤ |a n - c n| + |c n - b m| := abs_add_le _ _
      _ ≤ K * ((ν : Measure (Configuration E)) (esc m)).toReal + 1 / (m + 1 : ℝ) :=
        add_le_add herr' hcn
      _ = r m := rfl
  exact FKModel.eq_of_tendsto_of_eventually_abs_sub_le ha hb hr hbound

/-- General per-edge assembly from the real limiting-rate identity. -/
theorem onePoint_edge_of_limitRate
    (B : FiniteBox E) (e : B.edges) {q p : NNReal}
    (μ : ProbabilityMeasure (Configuration E)) (ρ : Configuration E → ℝ)
    (hcontId : ∀ (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ), (∀ y, 0 ≤ φ y) →
      ∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E)) =
        ∫ ω, ρ ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)))
    (hρmeas : Measurable ρ) (hρ0 : ∀ ω, 0 ≤ ρ ω) (hρ1 : ∀ ω, ρ ω ≤ 1)
    (αspec : B.Exterior → B.BoundaryPartition)
    (hrate : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ρ ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0) ∂(μ : Measure (Configuration E)) =
      ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) := by
  have hν := B.map_splitOff_restrict_eq_withDensity e μ ρ hρmeas hρ0 hρ1 hcontId
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  have hAmeas : MeasurableSet {ω : Configuration E | B.splitBit e ω = true} :=
    (measurableSet_singleton true).preimage (B.measurable_splitBit e)
  calc
    (∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
        ∂(μ : Measure (Configuration E))) =
        ∫⁻ y, g y ∂(((μ : Measure (Configuration E)).restrict
          {ω | B.splitBit e ω = true}).map (B.splitOff e)) := by
      rw [MeasureTheory.lintegral_map hg (B.measurable_splitOff e)]
      rw [show ∫⁻ ω in {ω : Configuration E | B.splitBit e ω = true},
            g (B.splitOff e ω) ∂(μ : Measure (Configuration E)) =
          ∫⁻ ω, {ω : Configuration E | B.splitBit e ω = true}.indicator
              (fun ω => g (B.splitOff e ω)) ω ∂(μ : Measure (Configuration E)) from
        (MeasureTheory.lintegral_indicator (μ := (μ : Measure (Configuration E)))
          hAmeas (fun ω => g (B.splitOff e ω))).symm]
      refine lintegral_congr fun ω => ?_
      by_cases h : B.splitBit e ω = true
      · rw [Set.indicator_of_mem (by exact h)]
        rw [show (bif B.splitBit e ω then g (B.splitOff e ω) else 0) = g (B.splitOff e ω)
          from by rw [h]; rfl]
      · rw [Set.indicator_of_notMem (by exact h)]
        have hf : B.splitBit e ω = false := by rwa [Bool.not_eq_true] at h
        rw [show (bif B.splitBit e ω then g (B.splitOff e ω) else 0) = 0
          from by rw [hf]; rfl]
    _ = ∫⁻ y, g y ∂(((μ : Measure (Configuration E)).withDensity
          (fun ω => ENNReal.ofReal (ρ ω))).map (B.splitOff e)) := by rw [hν]
    _ = ∫⁻ ω, ENNReal.ofReal (ρ ω) * g (B.splitOff e ω) ∂(μ : Measure (Configuration E)) := by
      rw [MeasureTheory.lintegral_map hg (B.measurable_splitOff e)]
      exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul (μ : Measure (Configuration E))
        (f := fun ω => ENNReal.ofReal (ρ ω)) (ENNReal.measurable_ofReal.comp hρmeas)
        (g := fun a => g (B.splitOff e a)) (hg.comp (B.measurable_splitOff e))
    _ = ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hrate] with ω hω
      exact congrArg (fun c => ENNReal.ofReal c * g (B.splitOff e ω)) hω

/-- Box-level DLR from a moving escape family controlled by a dominating law. -/
theorem isDLR_of_dominated_escape_moving
    (B : FiniteBox E) {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    (αspec : B.Exterior → B.BoundaryPartition) (hαspec : Measurable αspec)
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C lower : (e : B.edges) → ℕ → Set (Configuration E)}
    {Cinf : (e : B.edges) → Set (Configuration E)}
    {esc : (e : B.edges) → ℕ → Set (Configuration E)}
    (hCcl : ∀ (e : B.edges) n, IsClopen (C e n))
    (hlowerCl : ∀ (e : B.edges) m, IsClopen (lower e m))
    (hlowerMono : ∀ (e : B.edges), Monotone (lower e))
    (hUnion : ∀ (e : B.edges) ω, (∃ m, ω ∈ lower e m) ↔ ω ∈ Cinf e)
    (hsub : ∀ (e : B.edges) m n, m ≤ n → lower e m ⊆ C e n)
    (hsdiff : ∀ (e : B.edges) m n, m ≤ n → C e n \ lower e m ⊆ esc e m)
    (hescMeas : ∀ (e : B.edges) m, MeasurableSet (esc e m))
    (hescUp : ∀ (e : B.edges) m, IsUpperSet (esc e m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν (μs n))
    (hν : ∀ (e : B.edges),
      Tendsto (fun m => ((ν : Measure (Configuration E)) (esc e m)).toReal) atTop (𝓝 0))
    (hfin : ∀ (e : B.edges) (n : ℕ)
      (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs n : Measure (Configuration E)) =
        ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β (C e n) ω) * g (B.splitOff e ω)
          ∂(μs n : Measure (Configuration E)))
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      twoValuedRate α β (Cinf e) ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    B.IsDLR hq hp₁.le αspec hαspec μ := by
  refine B.isDLR_of_hasOnePointConditionals hq hp₀ hp₁ αspec hαspec μ ?_
  refine (B.hasOnePointConditionals_iff_bif αspec μ).mpr ?_
  intro e g hg
  let ρ : Configuration E → ℝ := twoValuedRate α β (Cinf e)
  have hcontId : ∀ (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ), (∀ y, 0 ≤ φ y) →
      ∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E)) =
        ∫ ω, ρ ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)) := by
    intro φ hφ
    exact openBit_eq_limitRate_of_dominated_escape B e μ hμ hα0 hαβ hβ1
      (hCcl e) (hlowerCl e) (hlowerMono e) (hUnion e) (hsub e) (hsdiff e)
      (hescMeas e) (hescUp e) ν hdom (hν e) (hfin e) φ hφ
  have hun : Cinf e = ⋃ m, lower e m := by
    ext ω
    rw [Set.mem_iUnion]
    exact (hUnion e ω).symm
  have hm : MeasurableSet (Cinf e) := by
    rw [hun]
    exact MeasurableSet.iUnion fun m => (hlowerCl e m).isOpen.measurableSet
  exact onePoint_edge_of_limitRate B e μ ρ hcontId
    (Measurable.ite hm measurable_const measurable_const)
    (fun ω => (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (Cinf e) ω).1)
    (fun ω => (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (Cinf e) ω).2)
    αspec (hrate e) g hg
/-- Box-level DLR from a moving escape family controlled by a dominating law. -/
theorem isDLR_of_dominated_escape_eventual_moving
    (B : FiniteBox E) {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    (αspec : B.Exterior → B.BoundaryPartition) (hαspec : Measurable αspec)
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C lower : (e : B.edges) → ℕ → Set (Configuration E)}
    {Cinf : (e : B.edges) → Set (Configuration E)}
    {esc : (e : B.edges) → ℕ → Set (Configuration E)}
    (hCcl : ∀ (e : B.edges) n, IsClopen (C e n))
    (hlowerCl : ∀ (e : B.edges) m, IsClopen (lower e m))
    (hlowerMono : ∀ (e : B.edges), Monotone (lower e))
    (hUnion : ∀ (e : B.edges) ω, (∃ m, ω ∈ lower e m) ↔ ω ∈ Cinf e)
    (hsub : ∀ (e : B.edges) m, ∀ᶠ n in atTop, lower e m ⊆ C e n)
    (hsdiff : ∀ (e : B.edges) m, ∀ᶠ n in atTop, C e n \ lower e m ⊆ esc e m)
    (hescMeas : ∀ (e : B.edges) m, MeasurableSet (esc e m))
    (hescUp : ∀ (e : B.edges) m, IsUpperSet (esc e m))
    (ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν (μs n))
    (hν : ∀ (e : B.edges),
      Tendsto (fun m => ((ν : Measure (Configuration E)) (esc e m)).toReal) atTop (𝓝 0))
    (hfin : ∀ (e : B.edges) (n : ℕ)
      (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs n : Measure (Configuration E)) =
        ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β (C e n) ω) * g (B.splitOff e ω)
          ∂(μs n : Measure (Configuration E)))
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      twoValuedRate α β (Cinf e) ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    B.IsDLR hq hp₁.le αspec hαspec μ := by
  refine B.isDLR_of_hasOnePointConditionals hq hp₀ hp₁ αspec hαspec μ ?_
  refine (B.hasOnePointConditionals_iff_bif αspec μ).mpr ?_
  intro e g hg
  let ρ : Configuration E → ℝ := twoValuedRate α β (Cinf e)
  have hcontId : ∀ (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ), (∀ y, 0 ≤ φ y) →
      ∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E)) =
        ∫ ω, ρ ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)) := by
    intro φ hφ
    exact openBit_eq_limitRate_of_dominated_escape_eventual B e μ hμ hα0 hαβ hβ1
      (hCcl e) (hlowerCl e) (hlowerMono e) (hUnion e) (hsub e) (hsdiff e)
      (hescMeas e) (hescUp e) ν hdom (hν e) (hfin e) φ hφ
  have hun : Cinf e = ⋃ m, lower e m := by
    ext ω
    rw [Set.mem_iUnion]
    exact (hUnion e ω).symm
  have hm : MeasurableSet (Cinf e) := by
    rw [hun]
    exact MeasurableSet.iUnion fun m => (hlowerCl e m).isOpen.measurableSet
  exact onePoint_edge_of_limitRate B e μ ρ hcontId
    (Measurable.ite hm measurable_const measurable_const)
    (fun ω => (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (Cinf e) ω).1)
    (fun ω => (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (Cinf e) ω).2)
    αspec (hrate e) g hg

end

end FK.InfiniteVolume.MovingClopenRate
