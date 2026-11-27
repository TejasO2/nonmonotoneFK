import FK.MovingClopenRate

/-! Limiting two-valued rates without a monotone boundary schedule.

This version of the moving-clopen argument assumes only eventual inclusion and
escape bounds, and makes no order assumption on the two rates.  It therefore
covers both FK orientations `q < 1` and `q > 1`, as well as `q = 1`.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace FK.InfiniteVolume.GeneralMovingClopenRate

attribute [local instance] Classical.decEq Classical.propDecidable

local instance boundaryPartitionMeasurableSpaceMoving (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

open FK.InfiniteVolume.OneEdgeNoEscape

noncomputable section

variable {E : Type*} [Countable E]

omit [Countable E] in
/-- A two-valued function with both values in `[0,1]` takes values in `[0,1]`,
without any ordering assumption on the two values. -/
lemma twoValuedRate_mem_unit {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (C : Set (Configuration E)) (ω : Configuration E) :
    twoValuedRate α β C ω ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : ω ∈ C
  · simpa [twoValuedRate, h] using And.intro hα0 hα1
  · simpa [twoValuedRate, h] using And.intro hβ0 hβ1

lemma integral_indicator_const_real {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Set X) (hs : MeasurableSet s) (c : ℝ) :
    (∫ x, s.indicator (fun _ => c) x ∂μ) = c * (μ s).toReal := by
  rw [MeasureTheory.integral_indicator hs, MeasureTheory.setIntegral_const]
  simp only [MeasureTheory.Measure.real, smul_eq_mul]
  ring

/-- Fixed-stage error between two two-valued rates tested against a nonnegative
bounded continuous function of the off-edge data. -/
lemma abs_integral_twoValuedRate_sub_mul_offTest_le
    (B : FiniteBox E) (e : B.edges)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hα1 : α ≤ 1) (hβ1 : β ≤ 1)
    {C L : Set (Configuration E)} (hC : IsClopen C) (hL : IsClopen L)
    (hsub : L ⊆ C)
    (φ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (hφ : ∀ y, 0 ≤ φ y) (μ : Measure (Configuration E)) [IsFiniteMeasure μ] :
    |(∫ ω, twoValuedRate α β C ω * B.offTest e φ ω ∂μ) -
      (∫ ω, twoValuedRate α β L ω * B.offTest e φ ω ∂μ)| ≤
        (|α - β| * ‖φ‖) * (μ (C \ L)).toReal := by
  have hC0 : ∀ ω, 0 ≤ twoValuedRate α β C ω := fun ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 C ω).1
  have hC1 : ∀ ω, twoValuedRate α β C ω ≤ 1 := fun ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 C ω).2
  have hL0 : ∀ ω, 0 ≤ twoValuedRate α β L ω := fun ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 L ω).1
  have hL1 : ∀ ω, twoValuedRate α β L ω ≤ 1 := fun ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 L ω).2
  have hCi : Integrable (fun ω => twoValuedRate α β C ω * B.offTest e φ ω) μ :=
    B.integrable_rate_mul e _ hC0 hC1 (continuous_twoValuedRate α β hC).measurable φ hφ μ
  have hLi : Integrable (fun ω => twoValuedRate α β L ω * B.offTest e φ ω) μ :=
    B.integrable_rate_mul e _ hL0 hL1 (continuous_twoValuedRate α β hL).measurable φ hφ μ
  have hmeas : MeasurableSet (C \ L) := hC.isOpen.measurableSet.diff hL.isOpen.measurableSet
  have hpoint : ∀ ω,
      |(twoValuedRate α β C ω * B.offTest e φ ω) -
        (twoValuedRate α β L ω * B.offTest e φ ω)| ≤
      (C \ L).indicator (fun _ => |α - β| * ‖φ‖) ω := by
    intro ω
    by_cases hωL : ω ∈ L
    · have hωC : ω ∈ C := hsub hωL
      simp [twoValuedRate, hωL, hωC]
    · by_cases hωC : ω ∈ C
      · have hω : ω ∈ C \ L := ⟨hωC, hωL⟩
        simp only [twoValuedRate, hωC, hωL, ite_true, ite_false,
          Set.indicator_of_mem hω]
        rw [← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ B.offTest e φ ω from hφ _)]
        exact mul_le_mul_of_nonneg_left (B.offTest_le_norm e φ hφ ω) (abs_nonneg _)
      · simp [twoValuedRate, hωL, hωC]
  rw [← MeasureTheory.integral_sub hCi hLi]
  calc
    |(∫ ω, (twoValuedRate α β C ω * B.offTest e φ ω -
        twoValuedRate α β L ω * B.offTest e φ ω) ∂μ)| ≤
        ∫ ω, |(twoValuedRate α β C ω * B.offTest e φ ω -
          twoValuedRate α β L ω * B.offTest e φ ω)| ∂μ :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ ω, (C \ L).indicator (fun _ => |α - β| * ‖φ‖) ω ∂μ := by
      exact MeasureTheory.integral_mono ((hCi.sub hLi).abs)
        ((integrable_const _).indicator hmeas) hpoint
    _ = (|α - β| * ‖φ‖) * (μ (C \ L)).toReal :=
      integral_indicator_const_real μ _ hmeas _

omit [Countable E] in
/-- Pointwise convergence of the rates attached to an increasing clopen family
with union `Cinf`. -/
lemma tendsto_twoValuedRate_of_monotone_union
    {α β : ℝ} {lower : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hmono : Monotone lower)
    (hUnion : ∀ ω, (∃ m, ω ∈ lower m) ↔ ω ∈ Cinf) (ω : Configuration E) :
    Tendsto (fun m => twoValuedRate α β (lower m) ω) atTop
      (𝓝 (twoValuedRate α β Cinf ω)) := by
  by_cases h : ω ∈ Cinf
  · obtain ⟨m, hm⟩ := (hUnion ω).mpr h
    have hev : ∀ᶠ n in atTop, twoValuedRate α β (lower n) ω = α := by
      filter_upwards [eventually_ge_atTop m] with n hn
      simp [twoValuedRate, hmono hn hm]
    have hlim : twoValuedRate α β Cinf ω = α := by simp [twoValuedRate, h]
    rw [hlim]
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  · have hn : ∀ m, ω ∉ lower m := fun m hm => h ((hUnion ω).mp ⟨m, hm⟩)
    have hev : ∀ᶠ n in atTop, twoValuedRate α β (lower n) ω = β := by
      filter_upwards [] with n
      simp [twoValuedRate, hn]
    have hlim : twoValuedRate α β Cinf ω = β := by simp [twoValuedRate, h]
    rw [hlim]
    exact Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds

/-- The moving-clopen one-edge limit identity.  No monotonicity of the stage
connection events is assumed.  Fixed lower approximants and vanishing clopen
escape tails replace the old no-mass-escape/scalar argument. -/
theorem openBit_eq_limitRate_of_clopen_escape
    (B : FiniteBox E) (e : B.edges)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hα1 : α ≤ 1) (hβ1 : β ≤ 1)
    {C lower : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    {esc : ℕ → Set (Configuration E)}
    (hCcl : ∀ n, IsClopen (C n)) (hlowerCl : ∀ m, IsClopen (lower m))
    (hlowerMono : Monotone lower)
    (hUnion : ∀ ω, (∃ m, ω ∈ lower m) ↔ ω ∈ Cinf)
    (hsub : ∀ m, ∀ᶠ n in atTop, lower m ⊆ C n)
    (hsdiff : ∀ m, ∀ᶠ n in atTop, C n \ lower m ⊆ esc m)
    (hescCl : ∀ m, IsClopen (esc m)) (hescAnti : Antitone esc)
    (hescNull : (μ : Measure (Configuration E)) (⋂ m, esc m) = 0)
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
  let r : ℕ → ℝ := fun m => K * ((μ : Measure (Configuration E)) (esc m)).toReal +
    2 * (1 / (m + 1 : ℝ))
  have hC0 : ∀ n ω, 0 ≤ twoValuedRate α β (C n) ω := fun n ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 (C n) ω).1
  have hC1 : ∀ n ω, twoValuedRate α β (C n) ω ≤ 1 := fun n ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 (C n) ω).2
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
          (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 (lower m) ω).1 (hφ _))]
      simpa only [one_mul] using (show twoValuedRate α β (lower m) ω * B.offTest e φ ω ≤ 1 * ‖φ‖ from
        mul_le_mul (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 (lower m) ω).2
          (B.offTest_le_norm e φ hφ ω) (hφ _) zero_le_one)
    · filter_upwards with ω
      exact (tendsto_twoValuedRate_of_monotone_union hlowerMono hUnion ω).mul_const _
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => K * ((μ : Measure (Configuration E)) (esc m)).toReal)
        atTop (𝓝 (K * 0)) :=
      (ClopenEscape.tendsto_measure_toReal_escape (μ : Measure (Configuration E))
        hescCl hescAnti hescNull).const_mul K
    have h2 : Tendsto (fun m : ℕ => 2 * (1 / (m + 1 : ℝ))) atTop
        (𝓝 (2 * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
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
    have hesc : Tendsto (fun n => K * ((μs n : Measure (Configuration E)) (esc m)).toReal)
        atTop (𝓝 (K * ((μ : Measure (Configuration E)) (esc m)).toReal)) :=
      (ClopenEscape.tendsto_measure_toReal_of_isClopen (hescCl m) hμ).const_mul K
    have hescs : ∀ᶠ n in atTop, K * ((μs n : Measure (Configuration E)) (esc m)).toReal ≤
        K * ((μ : Measure (Configuration E)) (esc m)).toReal + 1 / (m + 1 : ℝ) := by
      have hlt : K * ((μ : Measure (Configuration E)) (esc m)).toReal <
          K * ((μ : Measure (Configuration E)) (esc m)).toReal + 1 / (m + 1 : ℝ) := by linarith
      exact (tendsto_order.1 hesc).2 _ hlt |>.mono fun n hn => le_of_lt hn
    filter_upwards [hsub m, hsdiff m, hclose, hescs] with n hsubmn hdiffmn hcn hen
    have hstage : a n = ∫ ω, twoValuedRate α β (C n) ω * B.offTest e φ ω
        ∂(μs n : Measure (Configuration E)) := by
      exact B.finiteStage_real e μs (fun n => twoValuedRate α β (C n))
        (fun n => continuous_twoValuedRate α β (hCcl n)) hC0 hC1 hfin n φ hφ
    have herr : |a n - c n| ≤ K * ((μs n : Measure (Configuration E)) (C n \ lower m)).toReal := by
      rw [hstage]
      exact abs_integral_twoValuedRate_sub_mul_offTest_le B e hα0 hβ0 hα1 hβ1
        (hCcl n) (hlowerCl m) (hsubmn) φ hφ (μs n : Measure (Configuration E))
    have hmeasure : ((μs n : Measure (Configuration E)) (C n \ lower m)).toReal ≤
        ((μs n : Measure (Configuration E)) (esc m)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hdiffmn))
    have herr' : |a n - c n| ≤ K * ((μs n : Measure (Configuration E)) (esc m)).toReal :=
      herr.trans (mul_le_mul_of_nonneg_left hmeasure hK0)
    calc
      |a n - b m| = |(a n - c n) + (c n - b m)| := by congr 1; ring
      _ ≤ |a n - c n| + |c n - b m| := abs_add_le _ _
      _ ≤ K * ((μs n : Measure (Configuration E)) (esc m)).toReal + 1 / (m + 1 : ℝ) :=
        add_le_add herr' hcn
      _ ≤ (K * ((μ : Measure (Configuration E)) (esc m)).toReal + 1 / (m + 1 : ℝ)) +
          1 / (m + 1 : ℝ) := add_le_add hen le_rfl
      _ = r m := by dsimp [r]; ring
  exact FKModel.eq_of_tendsto_of_eventually_abs_sub_le ha hb hr hbound


/-- Exact per-edge one-point conditional identity for a possibly non-monotone
finite-volume boundary schedule. -/
theorem onePoint_edge_of_clopen_escape
    (B : FiniteBox E) (e : B.edges)
    {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hα1 : α ≤ 1) (hβ1 : β ≤ 1)
    {C lower : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    {esc : ℕ → Set (Configuration E)}
    (hCcl : ∀ n, IsClopen (C n)) (hlowerCl : ∀ m, IsClopen (lower m))
    (hlowerMono : Monotone lower)
    (hUnion : ∀ ω, (∃ m, ω ∈ lower m) ↔ ω ∈ Cinf)
    (hsub : ∀ m, ∀ᶠ n in atTop, lower m ⊆ C n)
    (hsdiff : ∀ m, ∀ᶠ n in atTop, C n \ lower m ⊆ esc m)
    (hescCl : ∀ m, IsClopen (esc m)) (hescAnti : Antitone esc)
    (hescNull : (μ : Measure (Configuration E)) (⋂ m, esc m) = 0)
    (hfin : ∀ (n : ℕ) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs n : Measure (Configuration E)) =
        ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β (C n) ω) * g (B.splitOff e ω)
          ∂(μs n : Measure (Configuration E)))
    (αspec : B.Exterior → B.BoundaryPartition)
    (hrate : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      twoValuedRate α β Cinf ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0) ∂(μ : Measure (Configuration E)) =
      ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) := by
  let ρ : Configuration E → ℝ := twoValuedRate α β Cinf
  have hcontId : ∀ (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ), (∀ y, 0 ≤ φ y) →
      ∫ ω, B.openBitTest e φ ω ∂(μ : Measure (Configuration E)) =
        ∫ ω, ρ ω * B.offTest e φ ω ∂(μ : Measure (Configuration E)) := by
    intro φ hφ
    exact openBit_eq_limitRate_of_clopen_escape B e μ hμ hα0 hβ0 hα1 hβ1
      hCcl hlowerCl hlowerMono hUnion hsub hsdiff hescCl hescAnti hescNull hfin φ hφ
  have hρmeas : Measurable ρ := by
    have hun : Cinf = ⋃ m, lower m := by
      ext ω
      rw [Set.mem_iUnion]
      exact (hUnion ω).symm
    have hm : MeasurableSet Cinf := by
      rw [hun]
      exact MeasurableSet.iUnion fun m => (hlowerCl m).isOpen.measurableSet
    exact Measurable.ite hm measurable_const measurable_const
  have hρ0 : ∀ ω, 0 ≤ ρ ω := fun ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 Cinf ω).1
  have hρ1 : ∀ ω, ρ ω ≤ 1 := fun ω =>
    (twoValuedRate_mem_unit hα0 hβ0 hα1 hβ1 Cinf ω).2
  have hν := B.map_splitOff_restrict_eq_withDensity e μ ρ hρmeas hρ0 hρ1 hcontId
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

/-- Box-level DLR from a moving clopen escape family.  The stage events need
not be monotone; only their fixed lower approximants are monotone. -/
theorem isDLR_of_clopen_escape_moving
    (B : FiniteBox E) {q p : NNReal}
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    (μ : ProbabilityMeasure (Configuration E)) (hμ : Tendsto μs atTop (𝓝 μ))
    (αspec : B.Exterior → B.BoundaryPartition) (hαspec : Measurable αspec)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hα1 : α ≤ 1) (hβ1 : β ≤ 1)
    {C lower : (e : B.edges) → ℕ → Set (Configuration E)}
    {Cinf : (e : B.edges) → Set (Configuration E)}
    {esc : (e : B.edges) → ℕ → Set (Configuration E)}
    (hCcl : ∀ (e : B.edges) n, IsClopen (C e n))
    (hlowerCl : ∀ (e : B.edges) m, IsClopen (lower e m))
    (hlowerMono : ∀ (e : B.edges), Monotone (lower e))
    (hUnion : ∀ (e : B.edges) ω, (∃ m, ω ∈ lower e m) ↔ ω ∈ Cinf e)
    (hsub : ∀ (e : B.edges) m, ∀ᶠ n in atTop, lower e m ⊆ C e n)
    (hsdiff : ∀ (e : B.edges) m, ∀ᶠ n in atTop, C e n \ lower e m ⊆ esc e m)
    (hescCl : ∀ (e : B.edges) m, IsClopen (esc e m))
    (hescAnti : ∀ (e : B.edges), Antitone (esc e))
    (hescNull : ∀ (e : B.edges), (μ : Measure (Configuration E)) (⋂ m, esc e m) = 0)
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
  exact onePoint_edge_of_clopen_escape B e μ hμ hα0 hβ0 hα1 hβ1
    (hCcl e) (hlowerCl e) (hlowerMono e) (hUnion e) (hsub e) (hsdiff e)
    (hescCl e) (hescAnti e) (hescNull e) (hfin e) αspec (hrate e) g hg


end

end FK.InfiniteVolume.GeneralMovingClopenRate
