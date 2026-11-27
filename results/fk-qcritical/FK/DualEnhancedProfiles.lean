import FK.SourceWindow
import FK.PlanarAllBoxDuality

/-!
# Enhanced profiles under planar parameter duality

The lower enhanced Bernoulli product used in the proof of Theorem 1.11 has an
exact complementary description.  At the planar parameter `p* = 1 - p'`, it is
the upper enhanced product with the star and cycle roles exchanged.  The two
cutset/path exponents are exchanged as well.  This is the scalar and product-law
part of Section 5.2; no dual device geometry is assumed.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.Planar.EnhancedProfiles

open FK.InfiniteVolume
open FK.Configuration
open FK.SourceUniqueness
open CurvatureVariance.Infra.Percolation

noncomputable section

/-- Complementation also reverses minima and maxima in this order. -/
lemma min_one_sub_eq_one_sub_max (a b : ℝ) :
    min (1 - a) (1 - b) = 1 - max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_right (sub_le_sub_left h 1)]
  · rw [max_eq_left h, min_eq_left (sub_le_sub_left h 1)]

/-- The two parameter names used by the phase and planar libraries coincide. -/
lemma fkPrime_eq_prime (p q : ℝ) :
    FK.Enhancement.fkPrime p q = FK.prime q p := rfl

lemma fkPrime_dual_real {q p : ℝ} (hq : 0 < q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FK.Enhancement.fkPrime (FK.dual q p) q = 1 - p := by
  rw [fkPrime_eq_prime]
  exact FK.prime_dual hq hp0 hp1

lemma dual_eq_one_sub_fkPrime {q p : ℝ} (hq : 0 < q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FK.dual q p = 1 - FK.Enhancement.fkPrime p q := by
  rw [fkPrime_eq_prime]
  exact FK.dual_eq_one_sub_prime (FK.denominator_ne_zero hq hp0 hp1)

/-- In the `q ≤ 1` branch, complementing the primal lower profile gives the
upper profile at `p*`.  Notice the exchange `(Eb,Ee,n,m) ↦ (Ee,Eb,m,n)`. -/
theorem one_sub_lowerWeightsReal_eq_upperWeightsReal_dual_of_q_le_one
    {E : Type*} (Eb Ee : Set E) (n m : ℕ) {q p : ℝ}
    (hq : 0 < q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : q ≤ 1) (e : E) :
    1 - FK.Phases.lowerWeightsReal Eb Ee n m p q e =
      FK.Phases.upperWeightsReal Ee Eb m n (FK.dual q p) q e := by
  have hpp : p ≤ FK.Enhancement.fkPrime p q :=
    FK.Enhancement.le_fkPrime_of_q_le_one hp0 hp1 hq hq1
  have hd0 : 0 ≤ FK.dual q p := FK.dual_nonneg hq hp0 hp1
  have hd1 : FK.dual q p ≤ 1 := FK.dual_le_one hq hp0 hp1
  have hd := dual_eq_one_sub_fkPrime hq hp0 hp1
  have hd' := fkPrime_dual_real hq hp0 hp1
  have hdd : FK.dual q p ≤ FK.Enhancement.fkPrime (FK.dual q p) q := by
    rw [hd', hd]
    exact sub_le_sub_left hpp 1
  rw [FK.Phases.lowerWeightsReal_of_le hpp,
    FK.Phases.upperWeightsReal_of_le hdd]
  have hmin : min (FK.dual q p) (FK.Enhancement.fkPrime (FK.dual q p) q) =
      1 - max p (FK.Enhancement.fkPrime p q) := by
    rw [hd', hd]
    exact (min_one_sub_eq_one_sub_max _ _).trans (by rw [max_comm])
  have habs : |FK.Enhancement.fkPrime (FK.dual q p) q - FK.dual q p| =
      |FK.Enhancement.fkPrime p q - p| := by
    rw [hd', hd]
    congr 1
    ring
  by_cases he : e ∈ Eb
  · simp only [he, if_pos]
    rw [FK.Enhancement.cutsetEnhancement, FK.Enhancement.pathEnhancement,
      hmin, habs, hd']
    ring
  · simp only [he, if_neg, if_false, add_zero, sub_zero]
    exact hd'.symm

/-- In the `1 ≤ q` branch the same exchange identity holds; the active set is
now the second primal set and the active exponent is the second exponent. -/
theorem one_sub_lowerWeightsReal_eq_upperWeightsReal_dual_of_one_le_q
    {E : Type*} (Eb Ee : Set E) (n m : ℕ) {q p : ℝ}
    (hq : 0 < q) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq1 : 1 ≤ q) (e : E) :
    1 - FK.Phases.lowerWeightsReal Eb Ee n m p q e =
      FK.Phases.upperWeightsReal Ee Eb m n (FK.dual q p) q e := by
  have hpp : FK.Enhancement.fkPrime p q ≤ p :=
    FK.Enhancement.fkPrime_le_of_one_le_q hp0 hp1 hq hq1
  have hd := dual_eq_one_sub_fkPrime hq hp0 hp1
  have hd' := fkPrime_dual_real hq hp0 hp1
  rcases lt_or_eq_of_le hpp with hpp' | heq
  · have hdd' : FK.Enhancement.fkPrime (FK.dual q p) q < FK.dual q p := by
      rw [hd', hd]
      exact sub_lt_sub_left hpp' 1
    rw [FK.Phases.lowerWeightsReal_of_ge hpp',
      FK.Phases.upperWeightsReal_of_ge hdd']
    have hmax : max (FK.dual q p) (FK.Enhancement.fkPrime (FK.dual q p) q) =
        1 - min p (FK.Enhancement.fkPrime p q) := by
      rw [hd', hd]
      exact (FK.max_one_sub_eq_one_sub_min _ _).trans (by rw [min_comm])
    have habs : |FK.Enhancement.fkPrime (FK.dual q p) q - FK.dual q p| =
        |FK.Enhancement.fkPrime p q - p| := by
      rw [hd', hd]
      congr 1
      ring
    by_cases he : e ∈ Ee
    · simp only [he, if_pos]
      rw [FK.Enhancement.pathEnhancement, FK.Enhancement.cutsetEnhancement,
        hmax, habs]
      have hc : 1 - (1 - min p (FK.Enhancement.fkPrime p q)) =
          min p (FK.Enhancement.fkPrime p q) := by ring
      rw [hc, hd]
      ring
    · simp [he, hd]
  · have hle : p ≤ FK.Enhancement.fkPrime p q := heq.ge
    have hdr : FK.dual q p = FK.Enhancement.fkPrime (FK.dual q p) q := by
      rw [hd', hd, heq]
    rw [FK.Phases.lowerWeightsReal_of_le hle,
      FK.Phases.upperWeightsReal_of_le hdr.le]
    have hz : |FK.Enhancement.fkPrime p q - p| = 0 := by
      rw [heq, sub_self, abs_zero]
    have hz' : |FK.Enhancement.fkPrime (FK.dual q p) q - FK.dual q p| = 0 := by
      rw [← hdr, sub_self, abs_zero]
    by_cases he : e ∈ Eb
    · simp only [he, if_pos]
      rw [FK.Enhancement.cutsetEnhancement, FK.Enhancement.pathEnhancement, hz, hz']
      simp [hd']
    · simp only [he, if_neg, if_false, add_zero, sub_zero]
      exact hd'.symm

/-- Membership in an image along an edge equivalence. -/
lemma mem_image_equiv {E F : Type*} (edge : E ≃ F) (S : Set E) (f : F) :
    f ∈ edge '' S ↔ edge.symm f ∈ S := by
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa
  · intro hf
    exact ⟨edge.symm f, hf, edge.apply_symm_apply f⟩

/-- Unit-interval form of the complementary profile identity for `q < 1`. -/
theorem sigma_lowerWeights_eq_upperWeights_dualParameter_q_lt_one
    {E F : Type*} (edge : E ≃ F) (Eb Ee : Set E) (n m : ℕ)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    (fun f => σ (FK.Phases.lowerWeights Eb Ee n m
      (show 0 ≤ (p : ℝ) by positivity) (show (p : ℝ) ≤ 1 by exact_mod_cast hp1.le)
      (show 0 < (q : ℝ) by exact_mod_cast hq) (edge.symm f))) =
      FK.Phases.upperWeights (edge '' Ee) (edge '' Eb) m n
        (show 0 ≤ ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) by positivity)
        (show ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) ≤ 1 by
          exact_mod_cast FK.FinitePlane.dualParameter_le_one hq hp1.le)
        (show 0 < (q : ℝ) by exact_mod_cast hq) := by
  funext f
  apply Subtype.ext
  change 1 - FK.Phases.lowerWeightsReal Eb Ee n m (p : ℝ) (q : ℝ) (edge.symm f) =
    FK.Phases.upperWeightsReal (edge '' Ee) (edge '' Eb) m n
      ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) (q : ℝ) f
  rw [FK.FinitePlane.coe_dualParameter hq hp1.le]
  rw [one_sub_lowerWeightsReal_eq_upperWeightsReal_dual_of_q_le_one
    Eb Ee n m (show 0 < (q : ℝ) by exact_mod_cast hq)
    (show 0 ≤ (p : ℝ) by positivity) (show (p : ℝ) ≤ 1 by exact_mod_cast hp1.le)
    (show (q : ℝ) ≤ 1 by exact_mod_cast hq1.le) (edge.symm f)]
  unfold FK.Phases.upperWeightsReal
  simp only [mem_image_equiv]

/-- Unit-interval form of the complementary profile identity for `1 < q`. -/
theorem sigma_lowerWeights_eq_upperWeights_dualParameter_one_lt_q
    {E F : Type*} (edge : E ≃ F) (Eb Ee : Set E) (n m : ℕ)
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q) :
    (fun f => σ (FK.Phases.lowerWeights Eb Ee n m
      (show 0 ≤ (p : ℝ) by positivity) (show (p : ℝ) ≤ 1 by exact_mod_cast hp1.le)
      (show 0 < (q : ℝ) by exact_mod_cast (lt_trans zero_lt_one hq1)) (edge.symm f))) =
      FK.Phases.upperWeights (edge '' Ee) (edge '' Eb) m n
        (show 0 ≤ ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) by positivity)
        (show ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) ≤ 1 by
          exact_mod_cast FK.FinitePlane.dualParameter_le_one
            (lt_trans zero_lt_one hq1) hp1.le)
        (show 0 < (q : ℝ) by exact_mod_cast (lt_trans zero_lt_one hq1)) := by
  let hq : 0 < q := lt_trans zero_lt_one hq1
  funext f
  apply Subtype.ext
  change 1 - FK.Phases.lowerWeightsReal Eb Ee n m (p : ℝ) (q : ℝ) (edge.symm f) =
    FK.Phases.upperWeightsReal (edge '' Ee) (edge '' Eb) m n
      ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) (q : ℝ) f
  rw [FK.FinitePlane.coe_dualParameter hq hp1.le]
  rw [one_sub_lowerWeightsReal_eq_upperWeightsReal_dual_of_one_le_q
    Eb Ee n m (show 0 < (q : ℝ) by exact_mod_cast hq)
    (show 0 ≤ (p : ℝ) by positivity) (show (p : ℝ) ≤ 1 by exact_mod_cast hp1.le)
    (show 1 ≤ (q : ℝ) by exact_mod_cast hq1.le) (edge.symm f)]
  unfold FK.Phases.upperWeightsReal
  simp only [mem_image_equiv]

end

end FK.Planar.EnhancedProfiles
