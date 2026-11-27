import FK.CactusPaths
import FK.AGTree.Invariant

/-!
# Exact criticality and strict window on the triangle cactus
-/

namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation FK.AGImplant
open scoped ENNReal NNReal unitInterval Sym2 Topology

/-- Real-valued mass under the original-bond law. -/
noncomputable abbrev actualPr (r : Fin 3 → unitInterval) (A : Set (graph.edgeSet → Bool)) : ℝ :=
  (actualLaw r).real A

lemma measurableSet_effectivePerc : MeasurableSet {η : G.edgeSet → Bool | Perc η} := by
  have hset : {η : G.edgeSet → Bool | Perc η} =
      ⋃ u : V, {η : G.edgeSet → Bool | InfiniteClusterAt η u} := by
    ext η
    simp only [Perc, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  exact MeasurableSet.iUnion (fun u => measurableSet_infiniteClusterAt u)
/-- The actual infinite-cluster event has exactly the probability given by the
five-regular junction tree at the effective rate. -/
theorem actualPr_percolation (r : Fin 3 → unitInterval) :
    actualPr r {ω | ActualPerc ω} =
      Ultra.pr (fun _ => effectiveRate r) {η : G.edgeSet → Bool | Perc η} := by
  have hset : {ω | ActualPerc ω} = effective ⁻¹' {η : G.edgeSet → Bool | Perc η} := by
    ext ω
    exact actualPerc_iff_effective ω
  rw [hset]
  change ((actualLaw r) (effective ⁻¹' {η : G.edgeSet → Bool | Perc η})).toReal =
    ((Ultra.law (fun _ => effectiveRate r)) {η : G.edgeSet → Bool | Perc η}).toReal
  rw [← Measure.map_apply measurable_effective measurableSet_effectivePerc,
    map_effective]

lemma quarter_branch_lt {x : ℝ} (hx : 0 ≤ x) : 3 * x + 4 * x ^ 2 < 1 ↔ x < 1 / 4 := by
  have hid : 1 - 3 * x - 4 * x ^ 2 = (1 - 4 * x) * (1 + x) := by ring
  constructor
  · intro h
    by_contra hn
    have hxx : 1 / 4 ≤ x := le_of_not_gt hn
    have hp : (1 - 4 * x) * (1 + x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith
  · intro h
    have hp : 0 < (1 - 4 * x) * (1 + x) := mul_pos (by linarith) (by linarith)
    nlinarith

lemma quarter_branch_gt {x : ℝ} (hx : 0 ≤ x) : 1 < 3 * x + 4 * x ^ 2 ↔ 1 / 4 < x := by
  have hid : 1 - 3 * x - 4 * x ^ 2 = (1 - 4 * x) * (1 + x) := by ring
  constructor
  · intro h
    by_contra hn
    have hxx : x ≤ 1 / 4 := le_of_not_gt hn
    have hp : 0 ≤ (1 - 4 * x) * (1 + x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · intro h
    have hp : (1 - 4 * x) * (1 + x) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith

lemma quarter_branch_eq {x : ℝ} (hx : 0 ≤ x) : 3 * x + 4 * x ^ 2 = 1 ↔ x = 1 / 4 := by
  have hid : 1 - 3 * x - 4 * x ^ 2 = (1 - 4 * x) * (1 + x) := by ring
  constructor
  · intro h
    have hp : (1 - 4 * x) * (1 + x) = 0 := by nlinarith
    have hzero : 1 - 4 * x = 0 := by
      have hx1 : 0 < 1 + x := by linarith
      exact (mul_eq_zero.mp hp).resolve_right (ne_of_gt hx1)
    linarith
  · intro h
    subst x
    norm_num

/-- Exact original-cactus criterion at effective rate one quarter. -/
theorem actualPr_quarter (r : Fin 3 → unitInterval) :
    ((effectiveRate r : ℝ) < 1 / 4 → actualPr r {ω | ActualPerc ω} = 0) ∧
      (1 / 4 < (effectiveRate r : ℝ) → 0 < actualPr r {ω | ActualPerc ω}) ∧
      ((effectiveRate r : ℝ) = 1 / 4 → actualPr r {ω | ActualPerc ω} = 0) := by
  let x : Fin 2 → unitInterval := fun _ => effectiveRate r
  have hx : (x 0 : ℝ) = (effectiveRate r : ℝ) := rfl
  have hx1 : (x 1 : ℝ) = (effectiveRate r : ℝ) := rfl
  constructor
  · intro hlt
    rw [actualPr_percolation]
    apply (two_rate_criterion x).1
    rw [hx, hx1]
    have hb := (quarter_branch_lt (unitInterval.nonneg (effectiveRate r))).mpr hlt
    convert hb using 1 <;> ring
  · constructor
    · intro hgt
      rw [actualPr_percolation]
      apply (two_rate_criterion x).2
      rw [hx, hx1]
      have hb := (quarter_branch_gt (unitInterval.nonneg (effectiveRate r))).mpr hgt
      convert hb using 1 <;> ring
    · intro heq
      rw [actualPr_percolation]
      apply (two_rate_criterion_full x).2.2
      · rw [hx, hx1]
        have hb := (quarter_branch_eq (unitInterval.nonneg (effectiveRate r))).mpr heq
        convert hb using 1 <;> ring
      · rw [hx, heq]
        norm_num

/-- Homogeneous rate on all three bonds of every triangle. -/
def homogeneousRates (p : unitInterval) : Fin 3 → unitInterval := fun _ => p

/-- The direct bond is decremented (with truncation), the two spoke bonds are
left unchanged. -/
noncomputable def penaltyRates (p ε : unitInterval) : Fin 3 → unitInterval :=
  ![⟨max 0 ((p : ℝ) - (ε : ℝ)), by
    exact ⟨le_max_left _ _, max_le (by norm_num)
      (by linarith [unitInterval.le_one p, unitInterval.nonneg ε])⟩⟩, p, p]

@[simp] lemma homogeneousRates_apply (p : unitInterval) (k : Fin 3) :
    homogeneousRates p k = p := rfl

lemma effectiveRate_homogeneous (p : unitInterval) :
    (effectiveRate (homogeneousRates p) : ℝ) = (p : ℝ) + (p : ℝ) ^ 2 - (p : ℝ) ^ 3 := by
  simp [effectiveRate, homogeneousRates]
  ring

end Ultra.TriangleCactus


namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation FK.AGImplant
open scoped ENNReal NNReal unitInterval Sym2 Topology

/-- Effective rate of a homogeneous triangle, as a real polynomial. -/
def tri (x : ℝ) : ℝ := x + x ^ 2 - x ^ 3

lemma tri_strict_of_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ 1) :
    tri x < tri y := by
  have hy0 : 0 < y := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hx2 : x * x ≤ x := by nlinarith
  have hy2 : y * y ≤ y := by nlinarith
  have hpq : x * y < 1 := by
    calc
      x * y < y * y := mul_lt_mul_of_pos_right hxy hy0
      _ ≤ 1 := by nlinarith
  have hfac : 0 < 1 + x + y - (x * x + x * y + y * y) := by nlinarith
  have hid : tri y - tri x = (y - x) * (1 + x + y - (x * x + x * y + y * y)) := by
    simp [tri]
    ring
  have hp : 0 < (y - x) * (1 + x + y - (x * x + x * y + y * y)) :=
    mul_pos (sub_pos.mpr hxy) hfac
  nlinarith

lemma tri_continuous : Continuous tri := by
  unfold tri
  fun_prop

/-- There is a genuine homogeneous critical rate strictly between 0 and 1. -/
theorem exists_homogeneous_critical :
    ∃ p : unitInterval, (1 / 5 : ℝ) < (p : ℝ) ∧ (p : ℝ) < 1 / 4 ∧
      tri (p : ℝ) = 1 / 4 := by
  have hmem : (1 / 4 : ℝ) ∈ Set.Icc (tri (1 / 5)) (tri (1 / 4)) := by
    norm_num [tri]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc
    (show (1 / 5 : ℝ) ≤ 1 / 4 by norm_num) tri_continuous.continuousOn hmem
  have hlo : (1 / 5 : ℝ) < x := by
    by_contra hn
    have heq : x = 1 / 5 := le_antisymm (le_of_not_gt hn) hx.1
    subst x
    norm_num [tri] at hfx
  have hhi : x < 1 / 4 := by
    by_contra hn
    have heq : x = 1 / 4 := le_antisymm hx.2 (le_of_not_gt hn)
    subst x
    norm_num [tri] at hfx
  refine ⟨⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, hlo, hhi, hfx⟩

/-- The homogeneous critical rate, realized by the intermediate-value theorem. -/
noncomputable def pc0 : unitInterval := Classical.choose exists_homogeneous_critical

lemma pc0_gt_fifth : (1 / 5 : ℝ) < (pc0 : ℝ) :=
  (Classical.choose_spec exists_homogeneous_critical).1

lemma pc0_lt_quarter : (pc0 : ℝ) < 1 / 4 :=
  (Classical.choose_spec exists_homogeneous_critical).2.1

lemma tri_pc0 : tri (pc0 : ℝ) = 1 / 4 :=
  (Classical.choose_spec exists_homogeneous_critical).2.2

lemma pc0_pos : 0 < (pc0 : ℝ) := by linarith [pc0_gt_fifth]

lemma pc0_lt_one : (pc0 : ℝ) < 1 := by linarith [pc0_lt_quarter]

lemma effectiveRate_homogeneous_pc0 :
    (effectiveRate (homogeneousRates pc0) : ℝ) = 1 / 4 := by
  rw [effectiveRate_homogeneous]
  exact tri_pc0

/-- Exact three-way criticality of the homogeneous original-bond product. -/
theorem homogeneous_criticality :
    (∀ p : unitInterval, (p : ℝ) < pc0 →
        actualPr (homogeneousRates p) {ω | ActualPerc ω} = 0) ∧
      (∀ p : unitInterval, pc0 < (p : ℝ) →
        0 < actualPr (homogeneousRates p) {ω | ActualPerc ω}) ∧
      (actualPr (homogeneousRates pc0) {ω | ActualPerc ω} = 0) := by
  refine ⟨?_, ?_, (actualPr_quarter _).2.2 effectiveRate_homogeneous_pc0⟩
  · intro p hp
    apply (actualPr_quarter _).1
    have ht := tri_strict_of_lt (unitInterval.nonneg p) hp pc0_lt_one.le
    rw [effectiveRate_homogeneous]
    show tri (p : ℝ) < 1 / 4
    rw [tri_pc0] at ht
    exact ht
  · intro p hp
    apply (actualPr_quarter _).2.1
    have ht := tri_strict_of_lt pc0_pos.le hp (unitInterval.le_one p)
    rw [effectiveRate_homogeneous]
    show 1 / 4 < tri (p : ℝ)
    rw [tri_pc0] at ht
    exact ht

end Ultra.TriangleCactus


namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation FK.AGImplant
open scoped ENNReal NNReal unitInterval Sym2 Topology

lemma penaltyRates_zero_coe (p ε : unitInterval) (hεp : (ε : ℝ) ≤ (p : ℝ)) :
    ((penaltyRates p ε 0 : unitInterval) : ℝ) = (p : ℝ) - (ε : ℝ) := by
  simp [penaltyRates, max_eq_right (sub_nonneg.mpr hεp)]

lemma effectiveRate_penalty (p ε : unitInterval) (hεp : (ε : ℝ) ≤ (p : ℝ)) :
    (effectiveRate (penaltyRates p ε) : ℝ) =
      (p : ℝ) + (p : ℝ) ^ 2 - (p : ℝ) ^ 3 - (ε : ℝ) * (1 - (p : ℝ) ^ 2) := by
  simp only [coe_effectiveRate]
  rw [penaltyRates_zero_coe p ε hεp]
  norm_num [penaltyRates]
  ring

lemma one_sub_effectiveRate_penalty (p ε : unitInterval) (hεp : (ε : ℝ) ≤ (p : ℝ)) :
    1 - (effectiveRate (penaltyRates p ε) : ℝ) =
      (1 - (p : ℝ)) * (1 - (p : ℝ) ^ 2) + (ε : ℝ) * (1 - (p : ℝ) ^ 2) := by
  rw [effectiveRate_penalty p ε hεp]
  ring

lemma pc0_failure : (1 - (pc0 : ℝ)) * (1 - (pc0 : ℝ) ^ 2) = 3 / 4 := by
  have h := tri_pc0
  unfold tri at h
  nlinarith

/-- A uniform Lipschitz bound on the homogeneous triangle failure on `[0,1]`. -/
lemma failure_drop_le_three {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (1 - x) * (1 - x ^ 2) - (1 - y) * (1 - y ^ 2) ≤ 3 * (y - x) := by
  have hy0 : 0 ≤ y := by linarith
  have hfac : 1 + x + y - x ^ 2 - x * y - y ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
  have hid : (1 - x) * (1 - x ^ 2) - (1 - y) * (1 - y ^ 2) =
      (y - x) * (1 + x + y - x ^ 2 - x * y - y ^ 2) := by ring
  rw [hid]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac (sub_nonneg.mpr hxy)

/-- **Strict enhancement window on the original cactus bonds.**  If `0 < ε < pc`,
then for an explicit positive `δ`, decrementing the direct bond of every triangle
by `ε` keeps the actual cactus product subcritical throughout `[pc, pc+δ)`. -/
theorem strict_direct_penalty_window (ε : unitInterval)
    (hε0 : 0 < (ε : ℝ)) (hεpc : (ε : ℝ) < (pc0 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : unitInterval, (pc0 : ℝ) ≤ (p : ℝ) →
      (p : ℝ) < (pc0 : ℝ) + δ →
        actualPr (penaltyRates p ε) {ω | ActualPerc ω} = 0 := by
  let δ : ℝ := min ((1 / 4 - (pc0 : ℝ)) / 2) ((ε : ℝ) / 4)
  have hδ0 : 0 < δ := lt_min (by linarith [pc0_lt_quarter]) (by linarith)
  refine ⟨δ, hδ0, ?_⟩
  intro p hpc hp
  have hδleft : δ ≤ (1 / 4 - (pc0 : ℝ)) / 2 := min_le_left _ _
  have hδright : δ ≤ (ε : ℝ) / 4 := min_le_right _ _
  have htop : (pc0 : ℝ) + δ < 1 / 4 := by
    calc
      (pc0 : ℝ) + δ ≤ (pc0 : ℝ) + (1 / 4 - (pc0 : ℝ)) / 2 :=
        add_le_add (le_refl _) hδleft
      _ < 1 / 4 := by linarith [pc0_lt_quarter]
  have hpq : (p : ℝ) < 1 / 4 := hp.trans htop
  have hεp : (ε : ℝ) ≤ (p : ℝ) := by linarith
  have hdiff : (p : ℝ) - (pc0 : ℝ) < δ := by linarith
  have hdrop := failure_drop_le_three (x := (pc0 : ℝ)) (y := (p : ℝ))
    pc0_pos.le hpc (unitInterval.le_one p)
  rw [pc0_failure] at hdrop
  have hsmall : 3 * ((p : ℝ) - (pc0 : ℝ)) < 3 * ((ε : ℝ) / 4) := by linarith
  have hsq : (p : ℝ) ^ 2 < 1 / 16 := by
    have hp1 : 0 < 1 / 4 - (p : ℝ) := by linarith
    have hp2 : 0 < 1 / 4 + (p : ℝ) := by have := unitInterval.nonneg p; linarith
    nlinarith [mul_pos hp1 hp2]
  have hside : (16 : ℝ) / 16 * (ε : ℝ) < (ε : ℝ) * (1 - (p : ℝ) ^ 2) +
      (ε : ℝ) / 16 := by
    have hmul : (ε : ℝ) * (1 - 1 / 16) < (ε : ℝ) * (1 - (p : ℝ) ^ 2) :=
      mul_lt_mul_of_pos_left (by linarith) hε0
    nlinarith
  have hfailure : 3 / 4 < (1 - (p : ℝ)) * (1 - (p : ℝ) ^ 2) +
      (ε : ℝ) * (1 - (p : ℝ) ^ 2) := by
    nlinarith
  apply (actualPr_quarter _).1
  have hid := one_sub_effectiveRate_penalty p ε hεp
  linarith

end Ultra.TriangleCactus
