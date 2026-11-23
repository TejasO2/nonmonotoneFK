import Mathlib

/-!
# Parameter identities for planar FK duality

This file formalizes the scalar identities used in Section 5.2 of
Beffara--Faipeur--Oke. The graph and measure theory are deliberately not
encoded here: these are exact lemmas about the FK parameters `p`, `p'`, and
`p*`.
-/

namespace FK

/-- The parameter occurring in the singleton conditional law off a cut edge. -/
noncomputable def prime (q p : ℝ) : ℝ := p / (p + q * (1 - p))

/-- The planar dual parameter, determined by
`p / (1 - p) * p* / (1 - p*) = q`. -/
noncomputable def dual (q p : ℝ) : ℝ := q * (1 - p) / (p + q * (1 - p))

lemma denominator_pos {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 < p + q * (1 - p) := by
  by_cases hp : p = 0
  · simpa [hp] using hq
  · have hp' : 0 < p := lt_of_le_of_ne hp₀ (Ne.symm hp)
    have hprod : 0 ≤ q * (1 - p) := mul_nonneg hq.le (sub_nonneg.mpr hp₁)
    linarith

lemma denominator_ne_zero {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    p + q * (1 - p) ≠ 0 :=
  (denominator_pos hq hp₀ hp₁).ne'

/-- Section 5.2, displayed computation before equation (12): `p' + p* = 1`. -/
lemma prime_add_dual {q p : ℝ} (h : p + q * (1 - p) ≠ 0) :
    prime q p + dual q p = 1 := by
  rw [prime, dual, ← add_div]
  exact div_self h

lemma dual_eq_one_sub_prime {q p : ℝ} (h : p + q * (1 - p) ≠ 0) :
    dual q p = 1 - prime q p := by
  have h' := prime_add_dual h
  linarith

lemma prime_eq_one_sub_dual {q p : ℝ} (h : p + q * (1 - p) ≠ 0) :
    prime q p = 1 - dual q p := by
  have h' := prime_add_dual h
  linarith

lemma dual_nonneg {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ dual q p := by
  exact div_nonneg (mul_nonneg hq.le (sub_nonneg.mpr hp₁))
    (denominator_pos hq hp₀ hp₁).le

lemma prime_nonneg {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ prime q p := by
  exact div_nonneg hp₀ (denominator_pos hq hp₀ hp₁).le

lemma dual_pos {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    0 < dual q p := by
  exact div_pos (mul_pos hq (sub_pos.mpr hp₁)) (denominator_pos hq hp₀ hp₁.le)

lemma prime_pos {q p : ℝ} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    0 < prime q p := by
  exact div_pos hp₀ (denominator_pos hq hp₀.le hp₁)

lemma dual_le_one {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    dual q p ≤ 1 := by
  have h := prime_nonneg hq hp₀ hp₁
  rw [dual_eq_one_sub_prime (denominator_ne_zero hq hp₀ hp₁)]
  linarith

lemma prime_le_one {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    prime q p ≤ 1 := by
  have h := dual_nonneg hq hp₀ hp₁
  rw [prime_eq_one_sub_dual (denominator_ne_zero hq hp₀ hp₁)]
  linarith

lemma dual_lt_one {q p : ℝ} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    dual q p < 1 := by
  have h := prime_pos hq hp₀ hp₁
  rw [dual_eq_one_sub_prime (denominator_ne_zero hq hp₀.le hp₁)]
  linarith

/-- The denominator obtained when applying `prime` to the dual parameter. -/
lemma dual_denominator {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    dual q p + q * (1 - dual q p) = q / (p + q * (1 - p)) := by
  have h := denominator_ne_zero hq hp₀ hp₁
  rw [dual]
  field_simp [h]
  ring

/-- Section 5.2: `(p*)' = 1-p`. -/
lemma prime_dual {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    prime q (dual q p) = 1 - p := by
  have h := denominator_ne_zero hq hp₀ hp₁
  rw [prime, dual_denominator hq hp₀ hp₁, dual]
  field_simp

/-- Planar FK duality is involutive on the scalar parameter. -/
lemma dual_dual {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    dual q (dual q p) = p := by
  have hden : dual q p + q * (1 - dual q p) ≠ 0 := by
    rw [dual_denominator hq hp₀ hp₁]
    exact div_ne_zero hq.ne' (denominator_ne_zero hq hp₀ hp₁)
  have h := prime_add_dual hden
  rw [prime_dual hq hp₀ hp₁] at h
  linarith

lemma dual_mem_Icc {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    dual q p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨dual_nonneg hq hp₀ hp₁, dual_le_one hq hp₀ hp₁⟩

lemma prime_mem_Icc {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    prime q p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨prime_nonneg hq hp₀ hp₁, prime_le_one hq hp₀ hp₁⟩

/-- The odds form of the defining equation for `p*`. -/
lemma odds_mul_odds {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hpne₀ : p ≠ 0) (hpne₁ : p ≠ 1) :
    (p / (1 - p)) * (dual q p / (1 - dual q p)) = q := by
  have h := denominator_ne_zero hq hp₀ hp₁
  have hp' : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpne₁)
  have h₁ : 1 - dual q p = prime q p := by
    have := prime_add_dual (denominator_ne_zero hq hp₀ hp₁)
    linarith
  rw [h₁, prime, dual]
  field_simp [h, hp', hpne₀]

/-- Cross-multiplied dual odds, valid also at `p = 0` and `p = 1`. -/
lemma dual_odds_cross {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    q * (1 - p) * (1 - dual q p) = p * dual q p := by
  have h := denominator_ne_zero hq hp₀ hp₁
  rw [dual]
  field_simp [h]
  ring

/-- Complementation reverses minima and maxima. -/
lemma max_one_sub_eq_one_sub_min (a b : ℝ) :
    max (1 - a) (1 - b) = 1 - min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (sub_le_sub_left h 1)]
  · rw [min_eq_right h, max_eq_right (sub_le_sub_left h 1)]

/-- The exact maximum identity underlying the parameter-window conversion in
Theorem 1.11. -/
lemma max_dual_prime_dual {q p : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    max (dual q p) (prime q (dual q p)) = 1 - min p (prime q p) := by
  rw [prime_dual hq hp₀ hp₁,
    dual_eq_one_sub_prime (denominator_ne_zero hq hp₀ hp₁)]
  exact max_one_sub_eq_one_sub_min (prime q p) p |>.trans (by rw [min_comm])

/-- The condition in Theorem 1.11 is exactly the subcritical window for the
 dual parameters. Here `c` is `pc(G*)` and `δ` is the paper's `δ''`. -/
lemma parameter_window_iff {q p c δ : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) :
    min p (prime q p) > 1 - c - δ ↔
      max (dual q p) (prime q (dual q p)) < c + δ := by
  have h := max_dual_prime_dual hq hp₀ hp₁ (q := q) (p := p)
  constructor
  · intro h'
    have h'' : 1 - min p (prime q p) < c + δ := by linarith
    rwa [← h] at h''
  · intro h'
    rw [h] at h'
    linarith

end FK
