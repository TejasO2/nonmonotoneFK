import FK.InfiniteVolume
import FK.EssentialWindow

/-!
# Orientation-safe integration of enhanced FK comparisons

This module removes three API gaps between the abstract phase assembly and
its implementations: duplicate product/window definitions, reversed naming of
lower/upper stochastic comparisons, and the conversion from device parameters
to `FK.Phases` weights.  It proves reductions only where finite enhanced
comparisons are genuinely still inputs; it does not claim the paper's main
theorems unconditionally.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.MainIntegration

/-- The two independently introduced infinite product laws are definitionally
identical.  In particular, `true` has probability `r e` in both. -/
theorem phases_bernoulliProduct_eq_fkLimit {E : Type*} (r : E → unitInterval) :
    FK.Phases.bernoulliProduct r = FKLimit.bernoulliProduct r := rfl

/-- The duplicate upper-window predicates are the same proposition. -/
theorem theorem14_upperWindow_eq_essentialWindow {E : Type*}
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) :
    FK.Theorem14.UpperWindow A pc Eb Ee n m q hq =
      FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq := rfl

/-- The duplicate lower-window predicates are the same proposition. -/
theorem theorem14_lowerWindow_eq_essentialWindow {E : Type*}
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) :
    FK.Theorem14.LowerWindow A pc Eb Ee n m q hq =
      FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq := rfl

/-- `FK.Phases.StochLe` and the infinite-volume domination predicate have
opposite argument conventions; with the arguments reversed they are equivalent. -/
theorem stochLe_iff_stochasticallyDominates {E : Type*}
    (μ ν : ProbabilityMeasure (E → Bool)) :
    FK.Phases.StochLe μ ν ↔ FKLimit.StochasticallyDominates ν μ := by
  constructor
  · intro h A hmeas hA
    change ((μ : Measure (E → Bool)) A).toNNReal ≤ ((ν : Measure (E → Bool)) A).toNNReal
    exact (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
      (h hA hmeas)
  · intro h A hA hmeas
    exact FK.EssentialWindow.measure_le_of_stochasticallyDominates h hmeas hA

/-- Uniform finite-box comparisons give `FK.Phases.StochLe` for every member
of the union of the FK weak-limit and coherent-convention Gibbs classes. -/
theorem two_sided_stochLe_of_mem_limitOrGibbsMeasures
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ lower upper : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ FK.InfiniteVolume.LimitOrGibbsMeasures exh hq hp)
    (hLimitLower : ∀ (α : ∀ n, (exh.box n).BoundaryPartition) n,
      FKLimit.StochasticallyDominates ((exh.box n).finiteVolumeLaw hq hp (α n)) lower)
    (hLimitUpper : ∀ (α : ∀ n, (exh.box n).BoundaryPartition) n,
      FKLimit.StochasticallyDominates upper ((exh.box n).finiteVolumeLaw hq hp (α n)))
    (hGibbsLower : ∀ (Φ : FK.InfiniteVolume.BoundaryConvention exh hq hp) n η,
      FKLimit.StochasticallyDominates
        ((exh.box n).conditionalLaw hq hp (Φ.partition n) η) lower)
    (hGibbsUpper : ∀ (Φ : FK.InfiniteVolume.BoundaryConvention exh hq hp) n η,
      FKLimit.StochasticallyDominates upper
        ((exh.box n).conditionalLaw hq hp (Φ.partition n) η)) :
    FK.Phases.StochLe lower μ ∧ FK.Phases.StochLe μ upper := by
  rcases hμ with hμ | ⟨Φ, hμ⟩
  · have h := FK.InfiniteVolume.two_sided_stochasticallyDominates_of_mem_fkLimitMeasures
      exh hq hp hμ hLimitUpper hLimitLower
    exact ⟨(stochLe_iff_stochasticallyDominates lower μ).2 h.2,
      (stochLe_iff_stochasticallyDominates μ upper).2 h.1⟩
  · have h := FK.InfiniteVolume.two_sided_stochasticallyDominates_of_mem_gibbsMeasures
      exh Φ hμ (hGibbsUpper Φ) (hGibbsLower Φ)
    exact ⟨(stochLe_iff_stochasticallyDominates lower μ).2 h.2,
      (stochLe_iff_stochasticallyDominates μ upper).2 h.1⟩

/-- Correctly oriented weak-limit form of Proposition 4.2(1).  The lower
finite comparison bounds each finite-volume law from below by the enhanced
star parameters, and the upper comparison bounds it from above by the enhanced
cycle parameters.  The conclusion is `star-enhanced ≼ μ ≼ cycle-enhanced`.

The existing `Proposition42` lemmas are used with their mathematically
appropriate roles: `upper_bound_of_finiteVolume` proves the lower stochastic
comparison and `lower_bound_of_finiteVolume` proves the upper one. -/
theorem proposition_4_2_lt_of_oriented_finite_comparisons
    {E : Type*} [Countable E]
    (exh : FKLimit.EdgeExhaustion E) (Sstar Scycle : Set E)
    (Dstar Dcycle : E → Finset E)
    (starAdmissible cycleAdmissible : ℕ → E → Prop)
    {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : p < FKLimit.fkSingletonParameter p q) (Delta L : ℕ)
    (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    {μs : ℕ → ProbabilityMeasure (E → Bool)}
    {μ : ProbabilityMeasure (E → Bool)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hLower : ∀ n, FKLimit.CylinderDominates (μs n)
      (FKLimit.bernoulliProduct (FKLimit.activeParameters exh Sstar Dstar starAdmissible
        (FKLimit.unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
        (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar) n)))
    (hUpper : ∀ n, FKLimit.CylinderDominates
      (FKLimit.bernoulliProduct (FKLimit.activeParameters exh Scycle Dcycle cycleAdmissible
        (FKLimit.unitParameters (fun _ : E ↦ FKLimit.fkSingletonParameter p q)
          (fun _ ↦ (FKLimit.fkSingletonParameter_pos hp hq).le)
          (fun _ ↦ (FKLimit.fkSingletonParameter_lt_one hp hq).le))
        (FKLimit.ltUpperParameters p q hp hq hpp L Scycle) n)) (μs n)) :
    FKLimit.StochasticallyDominates μ
      (FKLimit.bernoulliProduct (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar)) ∧
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct (FKLimit.ltUpperParameters p q hp hq hpp L Scycle)) μ := by
  constructor
  · have hselect :
        FKLimit.selectParameters
          (FKLimit.unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
          (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar) Sstar =
            FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar := by
      apply FKLimit.selectParameters_raisedOn_unit
    have h := FKLimit.upper_bound_of_finiteVolume exh Sstar Dstar starAdmissible
      (FKLimit.unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
      (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar)
      (fun e he ↦ (hStar e he).1) hstarAdm hμ hLower
    rwa [hselect] at h
  · have hselect :
        FKLimit.selectParameters
          (FKLimit.unitParameters (fun _ : E ↦ FKLimit.fkSingletonParameter p q)
            (fun _ ↦ (FKLimit.fkSingletonParameter_pos hp hq).le)
            (fun _ ↦ (FKLimit.fkSingletonParameter_lt_one hp hq).le))
          (FKLimit.ltUpperParameters p q hp hq hpp L Scycle) Scycle =
            FKLimit.ltUpperParameters p q hp hq hpp L Scycle := by
      apply FKLimit.selectParameters_loweredOn_unit
    have h := FKLimit.lower_bound_of_finiteVolume exh Scycle Dcycle cycleAdmissible
      (FKLimit.unitParameters (fun _ : E ↦ FKLimit.fkSingletonParameter p q)
        (fun _ ↦ (FKLimit.fkSingletonParameter_pos hp hq).le)
        (fun _ ↦ (FKLimit.fkSingletonParameter_lt_one hp hq).le))
      (FKLimit.ltUpperParameters p q hp hq hpp L Scycle)
      (fun e he ↦ (hCycle e he).1) hcycleAdm hμ hUpper
    rwa [hselect] at h

/-- Correctly oriented weak-limit form of Proposition 4.2(2), with
cycle-enhanced parameters below `μ` and cutset-enhanced parameters above it. -/
theorem proposition_4_2_gt_of_oriented_finite_comparisons
    {E : Type*} [Countable E]
    (exh : FKLimit.EdgeExhaustion E) (Sstar Scycle : Set E)
    (Dstar Dcycle : E → Finset E)
    (starAdmissible cycleAdmissible : ℕ → E → Prop)
    {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : FKLimit.fkSingletonParameter p q < p) (Delta L : ℕ)
    (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    {μs : ℕ → ProbabilityMeasure (E → Bool)}
    {μ : ProbabilityMeasure (E → Bool)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hLower : ∀ n, FKLimit.CylinderDominates (μs n)
      (FKLimit.bernoulliProduct (FKLimit.activeParameters exh Scycle Dcycle cycleAdmissible
        (FKLimit.unitParameters (fun _ : E ↦ FKLimit.fkSingletonParameter p q)
          (fun _ ↦ (FKLimit.fkSingletonParameter_pos hp hq).le)
          (fun _ ↦ (FKLimit.fkSingletonParameter_lt_one hp hq).le))
        (FKLimit.gtLowerParameters p q hp hq hpp L Scycle) n)))
    (hUpper : ∀ n, FKLimit.CylinderDominates
      (FKLimit.bernoulliProduct (FKLimit.activeParameters exh Sstar Dstar starAdmissible
        (FKLimit.unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
        (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar) n)) (μs n)) :
    FKLimit.StochasticallyDominates μ
      (FKLimit.bernoulliProduct (FKLimit.gtLowerParameters p q hp hq hpp L Scycle)) ∧
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar)) μ := by
  constructor
  · have hselect :
        FKLimit.selectParameters
          (FKLimit.unitParameters (fun _ : E ↦ FKLimit.fkSingletonParameter p q)
            (fun _ ↦ (FKLimit.fkSingletonParameter_pos hp hq).le)
            (fun _ ↦ (FKLimit.fkSingletonParameter_lt_one hp hq).le))
          (FKLimit.gtLowerParameters p q hp hq hpp L Scycle) Scycle =
            FKLimit.gtLowerParameters p q hp hq hpp L Scycle := by
      apply FKLimit.selectParameters_raisedOn_unit
    have h := FKLimit.upper_bound_of_finiteVolume exh Scycle Dcycle cycleAdmissible
      (FKLimit.unitParameters (fun _ : E ↦ FKLimit.fkSingletonParameter p q)
        (fun _ ↦ (FKLimit.fkSingletonParameter_pos hp hq).le)
        (fun _ ↦ (FKLimit.fkSingletonParameter_lt_one hp hq).le))
      (FKLimit.gtLowerParameters p q hp hq hpp L Scycle)
      (fun e he ↦ (hCycle e he).1) hcycleAdm hμ hLower
    rwa [hselect] at h
  · have hselect :
        FKLimit.selectParameters
          (FKLimit.unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
          (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar) Sstar =
            FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar := by
      apply FKLimit.selectParameters_loweredOn_unit
    have h := FKLimit.lower_bound_of_finiteVolume exh Sstar Dstar starAdmissible
      (FKLimit.unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
      (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar)
      (fun e he ↦ (hStar e he).1) hstarAdm hμ hUpper
    rwa [hselect] at h

/-- Equation (2) and the two enhancement profiles agree with the abstract
phase parameters in the `p < p'` case. -/
theorem ltLowerParameters_eq_lowerWeights
    {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : p < FKLimit.fkSingletonParameter p q)
    (Sstar Scycle : Set E) (Delta L : ℕ) :
    FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar =
      FK.Phases.lowerWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq := by
  have hbranch : p ≤ FK.Enhancement.fkPrime p q := hpp.le
  ext e
  change FKLimit.raisedOn p (FKLimit.starEpsilon p q Delta) Sstar e =
    FK.Phases.lowerWeightsReal Sstar Scycle (Delta - 1) (L - 1) p q e
  rw [FK.Phases.lowerWeightsReal_of_le hbranch]
  by_cases he : e ∈ Sstar <;>
    simp [FKLimit.raisedOn, FKLimit.starEpsilon, FKLimit.fkSingletonParameter,
      FK.Enhancement.fkPrime, FK.Enhancement.cutsetEnhancement, he]

/-- The upper `p < p'` profile is the phase upper profile with
`n = Δ - 1`, `m = L - 1`. -/
theorem ltUpperParameters_eq_upperWeights
    {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : p < FKLimit.fkSingletonParameter p q)
    (Sstar Scycle : Set E) (Delta L : ℕ) :
    FKLimit.ltUpperParameters p q hp hq hpp L Scycle =
      FK.Phases.upperWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq := by
  have hbranch : p ≤ FK.Enhancement.fkPrime p q := hpp.le
  ext e
  change FKLimit.loweredOn (FKLimit.fkSingletonParameter p q)
    (FKLimit.cycleEpsilon p q L) Scycle e =
      FK.Phases.upperWeightsReal Sstar Scycle (Delta - 1) (L - 1) p q e
  rw [FK.Phases.upperWeightsReal_of_le hbranch]
  by_cases he : e ∈ Scycle <;>
    simp [FKLimit.loweredOn, FKLimit.cycleEpsilon, FKLimit.fkSingletonParameter,
      FK.Enhancement.fkPrime, FK.Enhancement.pathEnhancement, he]

/-- The lower `p' < p` profile is the phase lower profile. -/
theorem gtLowerParameters_eq_lowerWeights
    {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : FKLimit.fkSingletonParameter p q < p)
    (Sstar Scycle : Set E) (Delta L : ℕ) :
    FKLimit.gtLowerParameters p q hp hq hpp L Scycle =
      FK.Phases.lowerWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq := by
  have hbranch : FK.Enhancement.fkPrime p q < p := hpp
  ext e
  change FKLimit.raisedOn (FKLimit.fkSingletonParameter p q)
    (FKLimit.cycleEpsilon p q L) Scycle e =
      FK.Phases.lowerWeightsReal Sstar Scycle (Delta - 1) (L - 1) p q e
  rw [FK.Phases.lowerWeightsReal_of_ge hbranch]
  by_cases he : e ∈ Scycle <;>
    simp [FKLimit.raisedOn, FKLimit.cycleEpsilon, FKLimit.fkSingletonParameter,
      FK.Enhancement.fkPrime, FK.Enhancement.pathEnhancement, he]

/-- The upper `p' < p` profile is the phase upper profile. -/
theorem gtUpperParameters_eq_upperWeights
    {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : FKLimit.fkSingletonParameter p q < p)
    (Sstar Scycle : Set E) (Delta L : ℕ) :
    FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar =
      FK.Phases.upperWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq := by
  have hbranch : FK.Enhancement.fkPrime p q < p := hpp
  ext e
  change FKLimit.loweredOn p (FKLimit.starEpsilon p q Delta) Sstar e =
    FK.Phases.upperWeightsReal Sstar Scycle (Delta - 1) (L - 1) p q e
  rw [FK.Phases.upperWeightsReal_of_ge hbranch]
  by_cases he : e ∈ Sstar <;>
    simp [FKLimit.loweredOn, FKLimit.starEpsilon, FKLimit.fkSingletonParameter,
      FK.Enhancement.fkPrime, FK.Enhancement.cutsetEnhancement, he]

/-- Convert the corrected `p < p'` weak-limit sandwich to the exact
`FK.Phases` laws used in `FK.Theorem14.ComparisonInput`. -/
theorem proposition_4_2_lt_phase_sandwich_of_oriented_limit
    {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : p < FKLimit.fkSingletonParameter p q)
    (Sstar Scycle : Set E) (Delta L : ℕ) {μ : ProbabilityMeasure (E → Bool)}
    (h : FKLimit.StochasticallyDominates μ
        (FKLimit.bernoulliProduct (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar)) ∧
      FKLimit.StochasticallyDominates
        (FKLimit.bernoulliProduct (FKLimit.ltUpperParameters p q hp hq hpp L Scycle)) μ) :
    FK.Phases.StochLe (FK.Phases.bernoulliProduct
      (FK.Phases.lowerWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq)) μ ∧
    FK.Phases.StochLe μ (FK.Phases.bernoulliProduct
      (FK.Phases.upperWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq)) := by
  constructor
  · have h' := (stochLe_iff_stochasticallyDominates
      (FKLimit.bernoulliProduct (FKLimit.ltLowerParameters p q hp hq hpp Delta Sstar)) μ).2 h.1
    rw [ltLowerParameters_eq_lowerWeights hp hq hpp Sstar Scycle Delta L] at h'
    exact h'
  · have h' := (stochLe_iff_stochasticallyDominates μ
      (FKLimit.bernoulliProduct (FKLimit.ltUpperParameters p q hp hq hpp L Scycle))).2 h.2
    rw [ltUpperParameters_eq_upperWeights hp hq hpp Sstar Scycle Delta L] at h'
    exact h'

/-- The `p' < p` companion of `proposition_4_2_lt_phase_sandwich_of_oriented_limit`. -/
theorem proposition_4_2_gt_phase_sandwich_of_oriented_limit
    {E : Type*} {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : 0 < q)
    (hpp : FKLimit.fkSingletonParameter p q < p)
    (Sstar Scycle : Set E) (Delta L : ℕ) {μ : ProbabilityMeasure (E → Bool)}
    (h : FKLimit.StochasticallyDominates μ
        (FKLimit.bernoulliProduct (FKLimit.gtLowerParameters p q hp hq hpp L Scycle)) ∧
      FKLimit.StochasticallyDominates
        (FKLimit.bernoulliProduct (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar)) μ) :
    FK.Phases.StochLe (FK.Phases.bernoulliProduct
      (FK.Phases.lowerWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq)) μ ∧
    FK.Phases.StochLe μ (FK.Phases.bernoulliProduct
      (FK.Phases.upperWeights Sstar Scycle (Delta - 1) (L - 1) hp.1.le hp.2.le hq)) := by
  constructor
  · have h' := (stochLe_iff_stochasticallyDominates
      (FKLimit.bernoulliProduct (FKLimit.gtLowerParameters p q hp hq hpp L Scycle)) μ).2 h.1
    rw [gtLowerParameters_eq_lowerWeights hp hq hpp Sstar Scycle Delta L] at h'
    exact h'
  · have h' := (stochLe_iff_stochasticallyDominates μ
      (FKLimit.bernoulliProduct (FKLimit.gtUpperParameters p q hp hq hpp Delta Sstar))).2 h.2
    rw [gtUpperParameters_eq_upperWeights hp hq hpp Sstar Scycle Delta L] at h'
    exact h'

end FK.MainIntegration
