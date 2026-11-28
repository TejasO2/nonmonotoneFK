import BBRAG.Shell
import BBRAG.Animals
import BBRAG.Measure

/-!
# `p_c^site(ℤ^d) < 1` (Peierls argument)

For `p` close to `1`, the probability that the origin is open but its cluster is finite is at most
`∑_n n · (2d(d+1)+1)^(2n) (1-p)^n < p`.
-/

open MeasureTheory ProbabilityTheory unitInterval

namespace BBR

variable {d : ℕ}

/-- The probability that all sites of a finite set `S` are closed is `(1 - p)^|S|`. -/
private lemma peierls_prob_allClosed (S : Finset (Site d)) (p : I) :
    sitePerc d p {ω | ∀ x ∈ S, x ∉ ω} = ENNReal.ofReal ((1 - (p : ℝ)) ^ S.card) := by
  have h := sitePerc_cyl S ∅ (Finset.empty_subset S) p
  have hset : {ω : Set (Site d) | ∀ x ∈ S, (x ∈ ω ↔ x ∈ (∅ : Finset (Site d)))} =
      {ω | ∀ x ∈ S, x ∉ ω} := by
    ext ω; simp
  rw [hset] at h
  rw [h]
  congr 1
  simp [wt]

/-- The probability that the origin is open is `p`. -/
private lemma peierls_prob_origin_open (p : I) :
    sitePerc d p {ω | (0 : Site d) ∈ ω} = ENNReal.ofReal (p : ℝ) := by
  have h := sitePerc_cyl {(0 : Site d)} {0} (Finset.Subset.refl _) p
  have hset : {ω : Set (Site d) | ∀ x ∈ ({0} : Finset (Site d)),
      (x ∈ ω ↔ x ∈ ({0} : Finset (Site d)))} = {ω | (0 : Site d) ∈ ω} := by
    ext ω; simp
  rw [hset] at h
  rw [h]
  congr 1
  simp [wt]

/-- **Peierls bound.** The probability that the origin is open and its open cluster is finite is
at most `∑_n n r^n` with `r = (2d(d+1)+1)^2 (1 - p)`. -/
private lemma peierls_finite_cluster_prob_le (hd : 2 ≤ d) (p : I) :
    sitePerc d p {ω | (0 : Site d) ∈ ω ∧ {x | ContainsPath ω 0 x}.Finite} ≤
      ∑' n : ℕ, ENNReal.ofReal
        ((n : ℝ) * ((((2 * d * (d + 1) + 1) ^ 2 : ℕ) : ℝ) * (1 - (p : ℝ))) ^ n) := by
  have hc := fun (x : Site d) (n : ℕ) => conn2_count x n
  choose F hF hFc using hc
  set D : ℕ := 2 * d * (d + 1) + 1
  set q : ℝ := 1 - (p : ℝ) with hq
  have hq0 : 0 ≤ q := by
    have := p.2.2
    simp only [hq]; linarith
  -- the closed shells of size `n` through `(k+1) e₁`
  let G : ℕ → ℕ → Finset (Finset (Site d)) := fun n k =>
    (F (((k : ℤ) + 1) • (e1 : Site d)) n).filter (fun S => S.card = n)
  let E : ℕ → Set (Set (Site d)) := fun n =>
    ⋃ k ∈ Finset.range n, ⋃ S ∈ G n k, {ω | ∀ x ∈ S, x ∉ ω}
  have hsub : {ω : Set (Site d) | (0 : Site d) ∈ ω ∧ {x | ContainsPath ω 0 x}.Finite} ⊆
      ⋃ n, E n := by
    rintro ω ⟨h0, hfin⟩
    obtain ⟨S, hS, hconn, k, hk, hmem⟩ := finite_cluster_shell hd ω h0 hfin
    simp only [E, Set.mem_iUnion]
    exact ⟨S.card, k, Finset.mem_range.2 hk, S,
      Finset.mem_filter.2 ⟨hF _ _ S hconn hmem rfl, rfl⟩, hS⟩
  have hE : ∀ n, sitePerc d p (E n) ≤
      ENNReal.ofReal ((n : ℝ) * (((D ^ 2 : ℕ) : ℝ) * q) ^ n) := by
    intro n
    calc sitePerc d p (E n)
        ≤ ∑ k ∈ Finset.range n, sitePerc d p (⋃ S ∈ G n k, {ω | ∀ x ∈ S, x ∉ ω}) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ S ∈ G n k, sitePerc d p {ω | ∀ x ∈ S, x ∉ ω} := by
          gcongr with k hk
          exact measure_biUnion_finset_le _ _
      _ = ∑ k ∈ Finset.range n, ∑ S ∈ G n k, ENNReal.ofReal (q ^ n) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun S hS => ?_
          rw [peierls_prob_allClosed]
          simp only [G, Finset.mem_filter] at hS
          rw [hS.2]
      _ = ∑ k ∈ Finset.range n, ((G n k).card : ENNReal) * ENNReal.ofReal (q ^ n) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range n, ((D ^ (2 * n) : ℕ) : ENNReal) * ENNReal.ofReal (q ^ n) := by
          gcongr with k hk
          exact (Finset.card_filter_le _ _).trans (hFc _ _)
      _ = ENNReal.ofReal ((n : ℝ) * (((D ^ 2 : ℕ) : ℝ) * q) ^ n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_pow,
            ENNReal.ofReal_mul (by positivity), ← Nat.cast_pow, ENNReal.ofReal_natCast, ← pow_mul]
  calc _ ≤ sitePerc d p (⋃ n, E n) := measure_mono hsub
    _ ≤ ∑' n, sitePerc d p (E n) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hE

/-- If the origin is open with probability `p`, but its cluster is finite with probability less
than `p`, then `θ(p) ≠ 0`. -/
private lemma peierls_theta0_ne_zero_of_lt (p : I)
    (h : sitePerc d p {ω | (0 : Site d) ∈ ω ∧ {x | ContainsPath ω 0 x}.Finite} <
      ENNReal.ofReal (p : ℝ)) : theta0 d p ≠ 0 := by
  have hsplit : {ω : Set (Site d) | (0 : Site d) ∈ ω} ⊆ {ω | OriginInInfiniteCluster ω} ∪
      {ω | (0 : Site d) ∈ ω ∧ {x | ContainsPath ω 0 x}.Finite} := by
    intro ω h0
    by_cases hinf : OriginInInfiniteCluster ω
    · exact Or.inl hinf
    · exact Or.inr ⟨h0, Set.not_infinite.1 hinf⟩
  have hle := (measure_mono (μ := sitePerc d p) hsplit).trans (measure_union_le _ _)
  rw [peierls_prob_origin_open] at hle
  intro h0
  unfold theta0 at h0
  rw [ENNReal.toReal_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · rw [h0, zero_add] at hle
    exact (lt_irrefl _ (hle.trans_lt h))
  · have : IsProbabilityMeasure (sitePerc d p) := by unfold sitePerc; infer_instance
    exact measure_ne_top _ _ h0

theorem pcSite_lt_one (hd : 2 ≤ d) : pcSite d < 1 := by
  set X : ℝ := (((2 * d * (d + 1) + 1) ^ 2 : ℕ) : ℝ) with hX
  have hX1 : (1 : ℝ) ≤ X := by
    have : 1 ≤ (2 * d * (d + 1) + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [hX]; exact_mod_cast this
  set c : ℝ := 1 / (16 * X) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hXc : X * c = 1 / 16 := by
    rw [hc]; field_simp
  have hc1 : c ≤ 1 / 16 := by nlinarith
  -- for `p > 1 - c`, the Peierls bound is smaller than `p`, so `θ(p) ≠ 0`
  have key : ∀ p : I, 1 - c < (p : ℝ) → theta0 d p ≠ 0 := by
    intro p hp
    set q : ℝ := 1 - (p : ℝ) with hq
    set r : ℝ := X * q with hr
    have hq0 : 0 ≤ q := by have := p.2.2; simp only [hq]; linarith
    have hqc : q < c := by simp only [hq]; linarith
    have hr0 : 0 ≤ r := mul_nonneg (by linarith) hq0
    have hr1 : r ≤ 1 / 16 := by
      have : r ≤ X * c := mul_le_mul_of_nonneg_left hqc.le (by linarith)
      linarith
    have hrn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
    have hsum : ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * r ^ n) =
        ENNReal.ofReal (r / (1 - r) ^ 2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hr0 n))
        (hasSum_coe_mul_geometric_of_norm_lt_one hrn).summable,
        tsum_coe_mul_geometric_of_norm_lt_one hrn]
    have hbound : r / (1 - r) ^ 2 < p := by
      have h1 : (1 : ℝ) / 2 ≤ (1 - r) ^ 2 := by nlinarith
      have h2 : (1 : ℝ) / 2 ≤ p := by linarith
      rw [div_lt_iff₀ (by linarith)]
      nlinarith [mul_le_mul h2 h1 (by norm_num) (by linarith)]
    have hC : sitePerc d p {ω | (0 : Site d) ∈ ω ∧ {x | ContainsPath ω 0 x}.Finite} ≤
        ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * r ^ n) := peierls_finite_cluster_prob_le hd p
    rw [hsum] at hC
    refine peierls_theta0_ne_zero_of_lt p (hC.trans_lt ?_)
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (div_nonneg hr0 (sq_nonneg _))]
    exact hbound
  have hpc : pcSite d ≤ 1 - c := by
    unfold pcSite
    apply Real.sSup_le
    · rintro x ⟨p, rfl, hp⟩
      exact not_lt.1 fun hlt => key p hlt hp
    · linarith
  linarith

end BBR
