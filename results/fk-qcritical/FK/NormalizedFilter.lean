import FK.FiniteModel

/-! # Real masses after filtering a normalized finite weight law -/

open scoped BigOperators ENNReal
open MeasureTheory
open FK.Finite.LabelledMultigraph

namespace FK.Finite.FilteredWeight

/-- Filtering a normalized finite nonnegative-weight PMF on `T` and then taking
an ordinary finite mass gives the ratio of the unnormalised weights on `C ∩ T`
and `T`.  The global and conditional normalisations cancel exactly. -/
theorem normalizedPMFOfSumPos_filter_toMeasure_real
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [DecidableEq α] (w : α → NNReal) (hw : 0 < ∑ a, w a)
    (T C : Set α) [DecidablePred (· ∈ T)] [DecidablePred (· ∈ C)]
    (hT : ∃ a ∈ T, a ∈ (normalizedPMFOfSumPos w hw).support) :
    ((normalizedPMFOfSumPos w hw).filter T hT).toMeasure.real C =
      (∑ a, if a ∈ C ∩ T then (w a : ℝ) else 0) /
        (∑ a, if a ∈ T then (w a : ℝ) else 0) := by
  classical
  let μ : PMF α := normalizedPMFOfSumPos w hw
  let z : ℝ≥0∞ := ∑' a, (w a : ℝ≥0∞)
  let d : ℝ≥0∞ := ∑' a, T.indicator μ a
  have hd : d ≠ ∞ := by
    dsimp only [d]
    rw [tsum_fintype]
    apply ENNReal.sum_ne_top.mpr
    intro a _
    by_cases ha : a ∈ T
    · rw [Set.indicator_of_mem ha]
      exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem ha]
      exact ENNReal.zero_ne_top
  have hμ (a : α) : (μ a).toReal = (w a : ℝ) / z.toReal := by
    dsimp only [μ]
    rw [normalizedPMFOfSumPos_apply, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  have hnum :
      (∑ a, (C.indicator (μ.filter T hT) a).toReal) =
        (∑ a, if a ∈ C ∩ T then (μ a).toReal else 0) * d.toReal⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases haC : a ∈ C
    · by_cases haT : a ∈ T
      · simp only [Set.indicator_of_mem haC, PMF.filter_apply,
          Set.indicator_of_mem haT, haC, haT, Set.mem_inter_iff,
          ENNReal.toReal_mul, ENNReal.toReal_inv]
        exact congrArg (fun x : ℝ => (μ a).toReal * x)
          (by rfl : d.toReal⁻¹ = d.toReal⁻¹)
      · have ha : a ∉ C ∩ T := fun h => haT h.2
        simp [haC, haT, ha, PMF.filter_apply]
    · have ha : a ∉ C ∩ T := fun h => haC h.1
      simp [haC, ha]
  have hden : d.toReal = ∑ a, if a ∈ T then (μ a).toReal else 0 := by
    dsimp only [d]
    rw [ENNReal.tsum_toReal_eq (fun a ↦ by
      by_cases ha : a ∈ T
      · rw [Set.indicator_of_mem ha]
        exact PMF.apply_ne_top _ _
      · rw [Set.indicator_of_notMem ha]
        exact ENNReal.zero_ne_top)]
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ T <;> simp [ha]
  have hsum : ((μ.filter T hT).toMeasure.real C) =
      (∑ a, if a ∈ C ∩ T then (μ a).toReal else 0) /
        (∑ a, if a ∈ T then (μ a).toReal else 0) := by
    rw [Measure.real, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
    · rw [hnum, hden, div_eq_mul_inv]
    · intro a _
      by_cases ha : a ∈ C
      · rw [Set.indicator_of_mem ha]
        exact PMF.apply_ne_top _ _
      · rw [Set.indicator_of_notMem ha]
        exact ENNReal.zero_ne_top
  rw [hsum]
  simp only [hμ]
  rw [show (∑ a, if a ∈ C ∩ T then (w a : ℝ) / z.toReal else 0) =
      (∑ a, if a ∈ C ∩ T then (w a : ℝ) else 0) / z.toReal by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp]
  rw [show (∑ a, if a ∈ T then (w a : ℝ) / z.toReal else 0) =
      (∑ a, if a ∈ T then (w a : ℝ) else 0) / z.toReal by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp]
  have hz : z.toReal ≠ 0 := by
    apply ENNReal.toReal_ne_zero.mpr
    constructor
    · dsimp only [z]
      rw [tsum_fintype]
      exact_mod_cast hw.ne'
    · dsimp only [z]
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr (fun a _ ↦ ENNReal.coe_ne_top)
  obtain ⟨a, haT, ha⟩ := hT
  have hwa : w a ≠ 0 := by
    intro hzero
    have hzero' : μ a = 0 := by
      dsimp only [μ]
      rw [normalizedPMFOfSumPos_apply, hzero]
      simp
    exact ha hzero'
  have hM : (∑ a, if a ∈ T then (w a : ℝ) else 0) ≠ 0 := by
    apply ne_of_gt
    apply Finset.sum_pos'
    · intro i _
      split_ifs <;> positivity
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      simp only [haT, ite_true]
      exact_mod_cast (pos_iff_ne_zero.mpr hwa)
  field_simp

end FK.Finite.FilteredWeight
