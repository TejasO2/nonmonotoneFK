import Mathlib

/-! Standalone aggregate of the four checked modules in this directory. -/

/-! Source module: `DevicePacking.lean`. -/

/-!
# Maximal packings of enhancement devices

This file isolates the deterministic part of the proof of Theorem 1.4 in
Beffara--Faipeur--Oke (arXiv:2512.16486). A device has a support on edges and
one distinguished pivotal edge. A maximal pairwise-disjoint family of devices
exists by Zorn's lemma. Every admissible device meets a selected device. With
an integer-valued edge distance satisfying the triangle inequality, a uniform
local supply of devices and a uniform device diameter therefore imply that every
edge is at bounded distance from the set of chosen pivotal edges.

No countability or finiteness assumption is needed for the maximal packing.
-/

namespace FK.DevicePacking

open Set

variable {Edge Device : Type*}

/-- Families contained in `D` whose device supports are pairwise disjoint. -/
def Admissible (support : Device → Set Edge) (D : Set Device) (s : Set Device) : Prop :=
  s ⊆ D ∧ s.PairwiseDisjoint support

/-- A maximal pairwise-disjoint subfamily of an arbitrary family of devices. -/
theorem exists_maximal_pairwiseDisjoint (support : Device → Set Edge) (D : Set Device) :
    ∃ M : Set Device, Maximal (Admissible support D) M := by
  let S : Set (Set Device) := {s | Admissible support D s}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hcc hcne
    refine ⟨⋃₀ c, ?_, fun s hs ↦ subset_sUnion_of_mem hs⟩
    constructor
    · exact sUnion_subset fun s hs ↦ (hcS hs).1
    · rw [hcc.pairwiseDisjoint_sUnion]
      exact fun s hs ↦ (hcS hs).2
  obtain ⟨M, -, hM⟩ := zorn_subset_nonempty S hchain ∅
    ⟨empty_subset D, pairwiseDisjoint_empty⟩
  exact ⟨M, hM⟩

/-- A device outside a maximal packing meets some device in the packing. -/
theorem intersects_of_notMem_of_maximal {support : Device → Set Edge} {D M : Set Device}
    (hM : Maximal (Admissible support D) M) {d : Device} (hdD : d ∈ D) (hdM : d ∉ M) :
    ∃ m ∈ M, (support d ∩ support m).Nonempty := by
  by_contra h
  have hnone : ∀ m ∈ M, ¬ (support d ∩ support m).Nonempty := by
    intro m hm hnm
    exact h ⟨m, hm, hnm⟩
  have hdis : ∀ m ∈ M, d ≠ m → Disjoint (support d) (support m) := by
    intro m hm _
    exact disjoint_left.mpr fun _ heD heM ↦ hnone m hm ⟨_, heD, heM⟩
  have hpair : (insert d M).PairwiseDisjoint support :=
    pairwiseDisjoint_insert.mpr ⟨hM.prop.2, hdis⟩
  have hadm : Admissible support D (insert d M) :=
    ⟨insert_subset hdD hM.prop.1, hpair⟩
  have heq : M = insert d M := hM.eq_of_le hadm (subset_insert d M)
  apply hdM
  rw [heq]
  exact mem_insert d M

/-- The geometric packing statement in the proof of Theorem 1.4. The chosen
pivotal edges are `pivot '' M`. The final two conclusions say, respectively,
that all auxiliary edges of a selected device remain unenhanced and that every
edge is within distance `K + R` of a chosen pivotal edge. -/
theorem exists_uniform_device_packing
    (support : Device → Set Edge) (D : Set Device) (pivot : Device → Edge)
    (hpivot : ∀ d, pivot d ∈ support d)
    (edgeDist : Edge → Edge → ℕ)
    (htriangle : ∀ a b c, edgeDist a c ≤ edgeDist a b + edgeDist b c)
    (K R : ℕ)
    (hlocal : ∀ e, ∃ d ∈ D, ∀ f ∈ support d, edgeDist e f ≤ K)
    (hdiam : ∀ d ∈ D, ∀ f ∈ support d, edgeDist f (pivot d) ≤ R) :
    ∃ M : Set Device, M ⊆ D ∧ M.PairwiseDisjoint support ∧
      (∀ d ∈ M, ∀ e ∈ support d, e ≠ pivot d → e ∉ pivot '' M) ∧
      (∀ d ∈ D, ∃ m ∈ M, (support d ∩ support m).Nonempty) ∧
      (∀ e, ∃ e' ∈ pivot '' M, edgeDist e e' ≤ K + R) := by
  obtain ⟨M, hM⟩ := exists_maximal_pairwiseDisjoint support D
  have hMD : M ⊆ D := hM.prop.1
  have hmeet : ∀ d ∈ D, ∃ m ∈ M, (support d ∩ support m).Nonempty := by
    intro d hdD
    by_cases hdM : d ∈ M
    · exact ⟨d, hdM, pivot d, hpivot d, hpivot d⟩
    · exact intersects_of_notMem_of_maximal hM hdD hdM
  have haux : ∀ d ∈ M, ∀ e ∈ support d, e ≠ pivot d → e ∉ pivot '' M := by
    intro d hdM e heD he
    rintro ⟨m, hmM, hme⟩
    have hmE : e ∈ support m := by simpa only [← hme] using hpivot m
    have hdm : d = m := by
      by_contra hne
      exact (disjoint_left.mp (hM.prop.2 hdM hmM hne)) heD hmE
    subst m
    exact he hme.symm
  refine ⟨M, hMD, hM.prop.2, haux, hmeet, ?_⟩
  intro e
  obtain ⟨d, hdD, hdclose⟩ := hlocal e
  obtain ⟨m, hmM, f, hfd, hfm⟩ := hmeet d hdD
  refine ⟨pivot m, ⟨m, hmM, rfl⟩, ?_⟩
  calc
    edgeDist e (pivot m) ≤ edgeDist e f + edgeDist f (pivot m) := htriangle e f (pivot m)
    _ ≤ K + R := Nat.add_le_add (hdclose f hfd) (hdiam m (hMD hmM) f hfm)

end FK.DevicePacking

/-! Source module: `EnhancementArithmetic.lean`. -/

/-!
# Algebra and bounds for the FK enhancement parameters

For `fkPrime p q = p / (p + q * (1 - p))`, this file proves the exact sign
relation between `p`, `fkPrime p q` and `q`, together with positivity and
probability bounds for the two enhancement sizes in Proposition 4.2 of
Beffara--Faipeur--Oke. Here `n` is the number of auxiliary edges in a device;
instantiating it with `Δ - 1` or `L - 1` gives the formulas in the paper.
-/

namespace FK.Enhancement

noncomputable section

open scoped Real

/-- The FK one-edge conditional probability when the endpoints are not connected
without the edge. -/
def fkPrime (p q : ℝ) : ℝ := p / (p + q * (1 - p))

/-- Enhancement obtained from one of `n` auxiliary edges being closed. -/
def cutsetEnhancement (p q : ℝ) (n : ℕ) : ℝ :=
  |fkPrime p q - p| * (1 - max p (fkPrime p q)) ^ n

/-- Enhancement obtained from all of `n` auxiliary edges being open. -/
def pathEnhancement (p q : ℝ) (n : ℕ) : ℝ :=
  |fkPrime p q - p| * min p (fkPrime p q) ^ n

lemma denominator_pos {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) :
    0 < p + q * (1 - p) := by
  have hqp : 0 ≤ q * (1 - p) := mul_nonneg hq.le (sub_nonneg.mpr hp1)
  by_cases hpz : p = 0
  · simp [hpz, hq]
  · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    nlinarith

lemma fkPrime_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) :
    0 ≤ fkPrime p q := div_nonneg hp0 (denominator_pos hp0 hp1 hq).le

lemma fkPrime_le_one {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) :
    fkPrime p q ≤ 1 := by
  rw [fkPrime, div_le_one (denominator_pos hp0 hp1 hq)]
  have hqp : 0 ≤ q * (1 - p) := mul_nonneg hq.le (sub_nonneg.mpr hp1)
  nlinarith

lemma fkPrime_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) :
    0 < fkPrime p q := div_pos hp0 (denominator_pos hp0.le hp1 hq)

lemma fkPrime_lt_one {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hq : 0 < q) :
    fkPrime p q < 1 := by
  rw [fkPrime, div_lt_one (denominator_pos hp0 hp1.le hq)]
  have hqp : 0 < q * (1 - p) := mul_pos hq (sub_pos.mpr hp1)
  nlinarith

/-- Exact difference formula used to determine all enhancement signs. -/
lemma fkPrime_sub (p q : ℝ) (hd : p + q * (1 - p) ≠ 0) :
    fkPrime p q - p = p * (1 - p) * (1 - q) / (p + q * (1 - p)) := by
  unfold fkPrime
  field_simp [hd]
  ring

/-- The same difference formula with the opposite sign. -/
lemma sub_fkPrime (p q : ℝ) (hd : p + q * (1 - p) ≠ 0) :
    p - fkPrime p q = p * (1 - p) * (q - 1) / (p + q * (1 - p)) := by
  unfold fkPrime
  field_simp [hd]
  ring

lemma lt_fkPrime_iff {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    p < fkPrime p q ↔ q < 1 := by
  have hd : 0 < p + q * (1 - p) := denominator_pos hp0.le hp1.le hq
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  constructor
  · intro h
    have hpq : 0 < p * (1 - p) * (1 - q) / (p + q * (1 - p)) := by
      rw [← fkPrime_sub p q hd.ne']
      exact sub_pos.mpr h
    have hn : 0 < p * (1 - p) * (1 - q) := (div_pos_iff_of_pos_right hd).mp hpq
    have hq' : 0 < 1 - q := (mul_pos_iff_of_pos_left hpp).mp hn
    linarith
  · intro h
    have hn : 0 < p * (1 - p) * (1 - q) := by
      apply mul_pos hpp
      linarith
    have hpq : 0 < p * (1 - p) * (1 - q) / (p + q * (1 - p)) := div_pos hn hd
    rw [← fkPrime_sub p q hd.ne'] at hpq
    linarith

lemma fkPrime_lt_iff {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkPrime p q < p ↔ 1 < q := by
  have hd : 0 < p + q * (1 - p) := denominator_pos hp0.le hp1.le hq
  have hpp : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  constructor
  · intro h
    have hpq : 0 < p * (1 - p) * (q - 1) / (p + q * (1 - p)) := by
      rw [← sub_fkPrime p q hd.ne']
      exact sub_pos.mpr h
    have hn : 0 < p * (1 - p) * (q - 1) := (div_pos_iff_of_pos_right hd).mp hpq
    have hq' : 0 < q - 1 := (mul_pos_iff_of_pos_left hpp).mp hn
    linarith
  · intro h
    have hn : 0 < p * (1 - p) * (q - 1) := by
      apply mul_pos hpp
      linarith
    have hpq : 0 < p * (1 - p) * (q - 1) / (p + q * (1 - p)) := div_pos hn hd
    rw [← sub_fkPrime p q hd.ne'] at hpq
    linarith

lemma fkPrime_one (p : ℝ) : fkPrime p 1 = p := by
  unfold fkPrime
  have hd : p + (1 : ℝ) * (1 - p) = 1 := by ring
  rw [hd, div_one]

lemma fkPrime_eq_self_iff {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkPrime p q = p ↔ q = 1 := by
  constructor
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (ne_of_gt ((lt_fkPrime_iff hp0 hp1 hq).mpr h)) heq
    · exact (ne_of_gt ((fkPrime_lt_iff hp0 hp1 hq).mpr h)) heq.symm
  · rintro rfl
    exact fkPrime_one p

/-- Every power weight between zero and one scales the FK gap without increasing it. -/
lemma scaled_gap_le {p q c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    |fkPrime p q - p| * c ^ n ≤ |fkPrime p q - p| := by
  calc
    |fkPrime p q - p| * c ^ n ≤ |fkPrime p q - p| * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hc0 hc1) (abs_nonneg _)
    _ = |fkPrime p q - p| := mul_one _

lemma scaled_gap_nonneg {p q c : ℝ} (hc0 : 0 ≤ c) (n : ℕ) :
    0 ≤ |fkPrime p q - p| * c ^ n :=
  mul_nonneg (abs_nonneg _) (pow_nonneg hc0 n)

lemma cutsetEnhancement_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q)
    (n : ℕ) : 0 ≤ cutsetEnhancement p q n := by
  apply scaled_gap_nonneg
  exact sub_nonneg.mpr (max_le hp1 (fkPrime_le_one hp0 hp1 hq))

lemma pathEnhancement_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q)
    (n : ℕ) : 0 ≤ pathEnhancement p q n := by
  apply scaled_gap_nonneg
  exact le_min hp0 (fkPrime_nonneg hp0 hp1 hq)

lemma cutsetEnhancement_le_gap {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q)
    (n : ℕ) : cutsetEnhancement p q n ≤ |fkPrime p q - p| := by
  apply scaled_gap_le
  · exact sub_nonneg.mpr (max_le hp1 (fkPrime_le_one hp0 hp1 hq))
  · have hmax0 : 0 ≤ max p (fkPrime p q) := le_max_of_le_left hp0
    nlinarith

lemma pathEnhancement_le_gap {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q)
    (n : ℕ) : pathEnhancement p q n ≤ |fkPrime p q - p| := by
  apply scaled_gap_le
  · exact le_min hp0 (fkPrime_nonneg hp0 hp1 hq)
  · exact min_le_left _ _ |>.trans hp1

/-- For `q ≤ 1`, `p ≤ p'`, including the parameter endpoints. -/
lemma le_fkPrime_of_q_le_one {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    p ≤ fkPrime p q := by
  have hd : 0 < p + q * (1 - p) := denominator_pos hp0 hp1 hq0
  have hn : 0 ≤ p * (1 - p) * (1 - q) :=
    mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) (sub_nonneg.mpr hq1)
  have hpq : 0 ≤ p * (1 - p) * (1 - q) / (p + q * (1 - p)) := div_nonneg hn hd.le
  rw [← fkPrime_sub p q hd.ne'] at hpq
  linarith

/-- For `1 ≤ q`, `p' ≤ p`, including the parameter endpoints. -/
lemma fkPrime_le_of_one_le_q {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : 1 ≤ q) :
    fkPrime p q ≤ p := by
  have hd : 0 < p + q * (1 - p) := denominator_pos hp0 hp1 hq0
  have hn : 0 ≤ p * (1 - p) * (q - 1) :=
    mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) (sub_nonneg.mpr hq1)
  have hpq : 0 ≤ p * (1 - p) * (q - 1) / (p + q * (1 - p)) := div_nonneg hn hd.le
  rw [← sub_fkPrime p q hd.ne'] at hpq
  linarith

/-- In the `q < 1` regime, both enhanced probabilities lie between `p` and `p'`. -/
lemma enhanced_probabilities_of_q_lt_one {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    p + cutsetEnhancement p q n ≤ fkPrime p q ∧
      p ≤ fkPrime p q - pathEnhancement p q n := by
  have hp' : p ≤ fkPrime p q := le_fkPrime_of_q_le_one hp0 hp1.le hq0 hq1.le
  have habs : |fkPrime p q - p| = fkPrime p q - p := abs_of_nonneg (sub_nonneg.mpr hp')
  constructor
  · have hle := cutsetEnhancement_le_gap hp0 hp1.le hq0 n
    rw [habs] at hle
    linarith
  · have hle := pathEnhancement_le_gap hp0 hp1.le hq0 n
    rw [habs] at hle
    linarith

/-- In the `q > 1` regime, both enhanced probabilities lie between `p'` and `p`. -/
lemma enhanced_probabilities_of_one_lt_q {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : 1 < q) (n : ℕ) :
    fkPrime p q + pathEnhancement p q n ≤ p ∧
      fkPrime p q ≤ p - cutsetEnhancement p q n := by
  have hp' : fkPrime p q < p := (fkPrime_lt_iff hp0 hp1 hq0).mpr hq1
  have habs : |fkPrime p q - p| = p - fkPrime p q := by
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hp')]
  constructor
  · have hle := pathEnhancement_le_gap hp0.le hp1.le hq0 n
    rw [habs] at hle
    linarith
  · have hle := cutsetEnhancement_le_gap hp0.le hp1.le hq0 n
    rw [habs] at hle
    linarith

lemma enhanced_bounds_of_le {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (h : p ≤ fkPrime p q) (n : ℕ) :
    p + cutsetEnhancement p q n ≤ fkPrime p q ∧
      p ≤ fkPrime p q - pathEnhancement p q n := by
  have habs : |fkPrime p q - p| = fkPrime p q - p := abs_of_nonneg (sub_nonneg.mpr h)
  constructor
  · have hle := cutsetEnhancement_le_gap hp0 hp1 hq n
    rw [habs] at hle
    linarith
  · have hle := pathEnhancement_le_gap hp0 hp1 hq n
    rw [habs] at hle
    linarith

lemma enhanced_bounds_of_ge {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (h : fkPrime p q ≤ p) (n : ℕ) :
    fkPrime p q + pathEnhancement p q n ≤ p ∧
      fkPrime p q ≤ p - cutsetEnhancement p q n := by
  have habs : |fkPrime p q - p| = p - fkPrime p q := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
  constructor
  · have hle := pathEnhancement_le_gap hp0 hp1 hq n
    rw [habs] at hle
    linarith
  · have hle := cutsetEnhancement_le_gap hp0 hp1 hq n
    rw [habs] at hle
    linarith

lemma cutsetEnhancement_of_le {p q : ℝ} (h : p ≤ fkPrime p q) (n : ℕ) :
    cutsetEnhancement p q n = (fkPrime p q - p) * (1 - fkPrime p q) ^ n := by
  simp [cutsetEnhancement, max_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]

lemma pathEnhancement_of_le {p q : ℝ} (h : p ≤ fkPrime p q) (n : ℕ) :
    pathEnhancement p q n = (fkPrime p q - p) * p ^ n := by
  simp [pathEnhancement, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]

lemma cutsetEnhancement_of_ge {p q : ℝ} (h : fkPrime p q ≤ p) (n : ℕ) :
    cutsetEnhancement p q n = (p - fkPrime p q) * (1 - p) ^ n := by
  simp [cutsetEnhancement, max_eq_left h, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr h)]

lemma pathEnhancement_of_ge {p q : ℝ} (h : fkPrime p q ≤ p) (n : ℕ) :
    pathEnhancement p q n = (p - fkPrime p q) * fkPrime p q ^ n := by
  simp [pathEnhancement, min_eq_right h, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr h)]

lemma cutsetEnhancement_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hne : q ≠ 1) (n : ℕ) : 0 < cutsetEnhancement p q n := by
  have hp'ne : fkPrime p q - p ≠ 0 := sub_ne_zero.mpr
    (mt (fkPrime_eq_self_iff hp0 hp1 hq).mp hne)
  have hp'lt : fkPrime p q < 1 := fkPrime_lt_one hp0.le hp1 hq
  apply mul_pos (abs_pos.mpr hp'ne) (pow_pos _ n)
  exact sub_pos.mpr (max_lt hp1 hp'lt)

lemma pathEnhancement_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hne : q ≠ 1) (n : ℕ) : 0 < pathEnhancement p q n := by
  have hp'ne : fkPrime p q - p ≠ 0 := sub_ne_zero.mpr
    (mt (fkPrime_eq_self_iff hp0 hp1 hq).mp hne)
  apply mul_pos (abs_pos.mpr hp'ne) (pow_pos _ n)
  exact lt_min hp0 (fkPrime_pos hp0 hp1.le hq)

end
end FK.Enhancement

/-! Source module: `ExtendedPhases.lean`. -/

/-!
# Abstract reduction for Theorem 1.4 (extended phases)

The product laws in this file are genuine inhomogeneous Bernoulli product
probability measures, built with `Measure.infinitePi`.  The FK family and the
infinite-cluster event remain parameters because their graph/DLR definitions
are outside this direction.  The two window hypotheses are the exact inputs
that the proof of Theorem 1.4 obtains from essential-enhancement theory.  They
are hypotheses, not definitions asserting a critical-point shift.

`lowerWeightsReal` and `upperWeightsReal` are the two one-parameter weights in
Proposition 4.2: for `p ≤ p'`, they are `p + ε^b 1_{E^b}` and `p' - ε^e 1_{E^e}`;
for `p' ≤ p`, they are `p' + ε^e 1_{E^e}` and `p - ε^b 1_{E^b}`.
-/

namespace FK.Phases

open Set MeasureTheory ProbabilityTheory
open FK.Enhancement
open Classical

noncomputable section

/-- A Boolean edge configuration. -/
abbrev EdgeConfiguration (E : Type*) := E → Bool

/-- Increasing events under pointwise inclusion of open-edge sets. -/
def IsIncreasingEvent {E : Type*} (A : Set (EdgeConfiguration E)) : Prop :=
  ∀ ⦃ω η⦄, ω ≤ η → ω ∈ A → η ∈ A

/-- Stochastic domination, tested on every measurable increasing event. -/
abbrev StochLe {E : Type*} (μ ν : ProbabilityMeasure (EdgeConfiguration E)) : Prop :=
  ∀ ⦃A⦄, IsIncreasingEvent A → MeasurableSet A →
    (μ : Measure (EdgeConfiguration E)) A ≤ (ν : Measure (EdgeConfiguration E)) A

lemma StochLe.refl {E : Type*} (μ : ProbabilityMeasure (EdgeConfiguration E)) : StochLe μ μ :=
  fun _ _ _ ↦ le_rfl

lemma StochLe.trans {E : Type*} {μ ν ξ : ProbabilityMeasure (EdgeConfiguration E)}
    (hμν : StochLe μ ν) (hνξ : StochLe ν ξ) : StochLe μ ξ :=
  fun _ hA hmeas ↦ (hμν hA hmeas).trans (hνξ hA hmeas)

/-- The inhomogeneous Bernoulli product measure with probability `r e` that
edge `e` is open.  No countability hypothesis on `E` is needed by `infinitePi`. -/
def bernoulliProduct {E : Type*} (r : E → unitInterval) :
    ProbabilityMeasure (EdgeConfiguration E) :=
  ⟨Measure.infinitePi (fun e ↦ bernoulliMeasure true false (r e)), inferInstance⟩

lemma map_eval_bernoulliProduct {E : Type*} (r : E → unitInterval) (e : E) :
    Measure.map (fun ω : EdgeConfiguration E ↦ ω e) (bernoulliProduct r : Measure _) =
      bernoulliMeasure true false (r e) := by
  change Measure.map (fun ω : EdgeConfiguration E ↦ ω e)
    (Measure.infinitePi (fun e ↦ bernoulliMeasure true false (r e))) = _
  exact Measure.infinitePi_map_eval _ e

/-- Coordinates of `bernoulliProduct` are jointly independent. -/
lemma iIndepFun_coordinates_bernoulliProduct {E : Type*} (r : E → unitInterval) :
    iIndepFun (fun e (ω : EdgeConfiguration E) ↦ ω e) (bernoulliProduct r : Measure _) := by
  change iIndepFun (fun e (ω : EdgeConfiguration E) ↦ ω e)
    (Measure.infinitePi (fun e ↦ bernoulliMeasure true false (r e)))
  exact iIndepFun_infinitePi (P := fun e ↦ bernoulliMeasure true false (r e))
    (X := fun _ (b : Bool) ↦ b) (fun _ ↦ measurable_id)

/-- Lower product weights in Proposition 4.2. -/
def lowerWeightsReal {E : Type*} (Eb Ee : Set E) (n m : ℕ) (p q : ℝ) (e : E) : ℝ :=
  if p ≤ fkPrime p q then
    p + if e ∈ Eb then cutsetEnhancement p q n else 0
  else
    fkPrime p q + if e ∈ Ee then pathEnhancement p q m else 0

/-- Upper product weights in Proposition 4.2. -/
def upperWeightsReal {E : Type*} (Eb Ee : Set E) (n m : ℕ) (p q : ℝ) (e : E) : ℝ :=
  if p ≤ fkPrime p q then
    fkPrime p q - if e ∈ Ee then pathEnhancement p q m else 0
  else
    p - if e ∈ Eb then cutsetEnhancement p q n else 0

lemma lowerWeightsReal_of_le {E : Type*} {Eb Ee : Set E} {n m : ℕ} {p q : ℝ}
    (h : p ≤ fkPrime p q) (e : E) :
    lowerWeightsReal Eb Ee n m p q e =
      p + if e ∈ Eb then cutsetEnhancement p q n else 0 := by
  simp [lowerWeightsReal, h]

lemma lowerWeightsReal_of_ge {E : Type*} {Eb Ee : Set E} {n m : ℕ} {p q : ℝ}
    (h : fkPrime p q < p) (e : E) :
  lowerWeightsReal Eb Ee n m p q e =
    fkPrime p q + if e ∈ Ee then pathEnhancement p q m else 0 := by
  simp [lowerWeightsReal, not_le_of_gt h]

lemma upperWeightsReal_of_le {E : Type*} {Eb Ee : Set E} {n m : ℕ} {p q : ℝ}
    (h : p ≤ fkPrime p q) (e : E) :
    upperWeightsReal Eb Ee n m p q e =
      fkPrime p q - if e ∈ Ee then pathEnhancement p q m else 0 := by
  simp [upperWeightsReal, h]

lemma upperWeightsReal_of_ge {E : Type*} {Eb Ee : Set E} {n m : ℕ} {p q : ℝ}
    (h : fkPrime p q < p) (e : E) :
    upperWeightsReal Eb Ee n m p q e =
      p - if e ∈ Eb then cutsetEnhancement p q n else 0 := by
  simp [upperWeightsReal, not_le_of_gt h]

lemma lowerWeightsReal_mem {E : Type*} {Eb Ee : Set E} {n m : ℕ}
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (e : E) :
    0 ≤ lowerWeightsReal Eb Ee n m p q e ∧
      lowerWeightsReal Eb Ee n m p q e ≤ 1 := by
  have hp'0 : 0 ≤ fkPrime p q := fkPrime_nonneg hp0 hp1 hq
  have hp'1 : fkPrime p q ≤ 1 := fkPrime_le_one hp0 hp1 hq
  by_cases h : p ≤ fkPrime p q
  · rw [lowerWeightsReal_of_le h]
    by_cases he : e ∈ Eb
    · simp only [if_pos he]
      exact ⟨add_nonneg hp0 (cutsetEnhancement_nonneg hp0 hp1 hq n),
        ((enhanced_bounds_of_le hp0 hp1 hq h n).1).trans hp'1⟩
    · simp [he, hp0, hp1]
  · have h' : fkPrime p q < p := lt_of_not_ge h
    rw [lowerWeightsReal_of_ge h']
    by_cases he : e ∈ Ee
    · simp only [if_pos he]
      exact ⟨add_nonneg hp'0 (pathEnhancement_nonneg hp0 hp1 hq m),
        ((enhanced_bounds_of_ge hp0 hp1 hq h'.le m).1).trans hp1⟩
    · simp [he, hp'0, hp'1]

lemma upperWeightsReal_mem {E : Type*} {Eb Ee : Set E} {n m : ℕ}
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (e : E) :
    0 ≤ upperWeightsReal Eb Ee n m p q e ∧
      upperWeightsReal Eb Ee n m p q e ≤ 1 := by
  have hp'0 : 0 ≤ fkPrime p q := fkPrime_nonneg hp0 hp1 hq
  have hp'1 : fkPrime p q ≤ 1 := fkPrime_le_one hp0 hp1 hq
  by_cases h : p ≤ fkPrime p q
  · rw [upperWeightsReal_of_le h]
    by_cases he : e ∈ Ee
    · simp only [if_pos he]
      exact ⟨hp0.trans (enhanced_bounds_of_le hp0 hp1 hq h m).2,
        sub_le_iff_le_add.mpr (hp'1.trans (le_add_of_nonneg_right
          (pathEnhancement_nonneg hp0 hp1 hq m)))⟩
    · simp [he, hp'0, hp'1]
  · have h' : fkPrime p q < p := lt_of_not_ge h
    rw [upperWeightsReal_of_ge h']
    by_cases he : e ∈ Eb
    · simp only [if_pos he]
      exact ⟨hp'0.trans (enhanced_bounds_of_ge hp0 hp1 hq h'.le n).2,
        sub_le_iff_le_add.mpr (hp1.trans (le_add_of_nonneg_right
          (cutsetEnhancement_nonneg hp0 hp1 hq n)))⟩
    · simp [he, hp0, hp1]

/-- The valid unit-interval version of `lowerWeightsReal`. -/
def lowerWeights {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) : E → unitInterval :=
  fun e ↦ ⟨lowerWeightsReal Eb Ee n m p q e,
    (lowerWeightsReal_mem (Eb := Eb) (Ee := Ee) (n := n) (m := m) hp0 hp1 hq e).1,
    (lowerWeightsReal_mem (Eb := Eb) (Ee := Ee) (n := n) (m := m) hp0 hp1 hq e).2⟩

/-- The valid unit-interval version of `upperWeightsReal`. -/
def upperWeights {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) : E → unitInterval :=
  fun e ↦ ⟨upperWeightsReal Eb Ee n m p q e,
    (upperWeightsReal_mem (Eb := Eb) (Ee := Ee) (n := n) (m := m) hp0 hp1 hq e).1,
    (upperWeightsReal_mem (Eb := Eb) (Ee := Ee) (n := n) (m := m) hp0 hp1 hq e).2⟩

@[simp] lemma coe_lowerWeights {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (e : E) :
    (lowerWeights Eb Ee n m hp0 hp1 hq e : ℝ) = lowerWeightsReal Eb Ee n m p q e := rfl

@[simp] lemma coe_upperWeights {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (e : E) :
    (upperWeights Eb Ee n m hp0 hp1 hq e : ℝ) = upperWeightsReal Eb Ee n m p q e := rfl

/-- Domination by a subcritical law transfers absence of infinite clusters. -/
lemma subcritical_of_stochLe {E : Type*} {A : Set (EdgeConfiguration E)}
    {φ μ : ProbabilityMeasure (EdgeConfiguration E)}
    (hdom : StochLe φ μ) (hA : IsIncreasingEvent A) (hmeas : MeasurableSet A)
    (hμ : (μ : Measure _) A = 0) : (φ : Measure _) A = 0 := by
  apply le_antisymm
  · simpa [hμ] using hdom hA hmeas
  · exact bot_le

/-- Domination from below by a supercritical law transfers existence of an
infinite cluster with probability one. -/
lemma supercritical_of_stochLe {E : Type*} {A : Set (EdgeConfiguration E)}
    {μ φ : ProbabilityMeasure (EdgeConfiguration E)}
    (hdom : StochLe μ φ) (hA : IsIncreasingEvent A) (hmeas : MeasurableSet A)
    (hμ : (μ : Measure _) A = 1) : (φ : Measure _) A = 1 := by
  apply le_antisymm prob_le_one
  simpa [hμ] using hdom hA hmeas

/-- Conditional abstract form of Theorem 1.4 for a fixed `q ≠ 1`.
`fk p q` must be instantiated by the set of all FK limit and Gibbs measures;
`A` is the increasing infinite-cluster event.  The comparison hypothesis is
Proposition 4.2 with `n = Δ - 1`, `m = L - 1`. The two window hypotheses are
precisely the remaining essential-enhancement inputs. -/
theorem extended_phases_of_comparison_and_essentialEnhancement
    {E : Type*} (A : Set (EdgeConfiguration E)) (pc : ℝ)
    (fk : ℝ → ℝ → Set (ProbabilityMeasure (EdgeConfiguration E)))
    (Eb Ee : Set E) (n m : ℕ)
    (hA : IsIncreasingEvent A) (hmeas : MeasurableSet A)
    (q : ℝ) (hq : 0 < q) (_hq1 : q ≠ 1)
    (hcompare : ∀ p (hp : p ∈ Icc (0 : ℝ) 1) φ, φ ∈ fk p q →
      StochLe (bernoulliProduct (lowerWeights Eb Ee n m hp.1 hp.2 hq)) φ ∧
      StochLe φ (bernoulliProduct (upperWeights Eb Ee n m hp.1 hp.2 hq)))
    (hupper_window : ∃ δ' > 0, ∀ p (hp : p ∈ Icc (0 : ℝ) 1),
      max p (fkPrime p q) < pc + δ' →
      (bernoulliProduct (upperWeights Eb Ee n m hp.1 hp.2 hq) : Measure _) A = 0)
    (hlower_window : ∃ δ > 0, ∀ p (hp : p ∈ Icc (0 : ℝ) 1),
      pc - δ < min p (fkPrime p q) →
      (bernoulliProduct (lowerWeights Eb Ee n m hp.1 hp.2 hq) : Measure _) A = 1) :
    ∃ δ, ∃ δ', 0 < δ ∧ 0 < δ' ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), max p (fkPrime p q) < pc + δ' →
        ∃ μ : ProbabilityMeasure (EdgeConfiguration E), (μ : Measure _) A = 0 ∧
          (∀ φ ∈ fk p q, StochLe φ μ) ∧ (∀ φ ∈ fk p q, (φ : Measure _) A = 0)) ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), pc - δ < min p (fkPrime p q) →
        ∃ μ : ProbabilityMeasure (EdgeConfiguration E), (μ : Measure _) A = 1 ∧
          (∀ φ ∈ fk p q, StochLe μ φ) ∧ (∀ φ ∈ fk p q, (φ : Measure _) A = 1)) := by
  obtain ⟨δ', hδ', hupper⟩ := hupper_window
  obtain ⟨δ, hδ, hlower⟩ := hlower_window
  refine ⟨δ, δ', hδ, hδ', ?_, ?_⟩
  · intro p hp hpwindow
    let μ := bernoulliProduct (upperWeights Eb Ee n m hp.1 hp.2 hq)
    have hμ : (μ : Measure _) A = 0 := hupper p hp hpwindow
    refine ⟨μ, hμ, ?_, ?_⟩
    · intro φ hφ
      exact (hcompare p hp φ hφ).2
    · intro φ hφ
      exact subcritical_of_stochLe ((hcompare p hp φ hφ).2) hA hmeas hμ
  · intro p hp hpwindow
    let μ := bernoulliProduct (lowerWeights Eb Ee n m hp.1 hp.2 hq)
    have hμ : (μ : Measure _) A = 1 := hlower p hp hpwindow
    refine ⟨μ, hμ, ?_, ?_⟩
    · intro φ hφ
      exact (hcompare p hp φ hφ).1
    · intro φ hφ
      exact supercritical_of_stochLe ((hcompare p hp φ hφ).1) hA hmeas hμ

end
end FK.Phases

/-! Source module: `Theorem14Devices.lean`. -/

/-!
# Theorem 1.4 from uniform devices and explicit external inputs

This file connects the maximal-device construction to the abstract phase
reduction.  The assumptions `hlocalStar` and `hlocalCycle` are the uniform local
cover properties obtained in the paper from quasi-transitivity.  The predicates
`UpperWindow` and `LowerWindow` isolate essential-enhancement theory.  No graph
or percolation theorem is asserted merely by a definition: the comparison,
essentialness and window hypotheses are all visible in
`extended_phases_from_uniform_devices`.

Set `n = Δ - 1`, `m = L - 1`, and use star/cycle devices with their pivotal-edge
choices to match the proof on pages 21--22 of arXiv:2512.16486.
-/

namespace FK.Theorem14

open Set MeasureTheory ProbabilityTheory
open FK.Enhancement FK.Phases FK.DevicePacking
open Classical

noncomputable section

/-- Every edge of a set has the prescribed essentialness property. -/
def AllEssential {E : Type*} (essential : E → Prop) (S : Set E) : Prop :=
  ∀ e ∈ S, essential e

/-- Positive-density geometric condition used by essential enhancements: every
edge is at uniformly bounded distance from an enhanced edge. -/
def BoundedDistance {E : Type*} (edgeDist : E → E → ℕ) (S : Set E) : Prop :=
  ∃ R, ∀ e, ∃ e' ∈ S, edgeDist e e' ≤ R

/-- The auxiliary-edge condition in Proposition 4.2 for selected devices. -/
def AuxiliaryFree {E Device : Type*} (support : Device → Set E) (pivot : Device → E)
    (M : Set Device) : Prop :=
  ∀ d ∈ M, ∀ e ∈ support d, e ≠ pivot d → e ∉ pivot '' M

/-- Exact upper-window input for Theorem 1.4(1). -/
def UpperWindow {E : Type*} (A : Set (EdgeConfiguration E)) (pc : ℝ)
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) : Prop :=
  ∃ δ' > 0, ∀ p (hp : p ∈ Icc (0 : ℝ) 1),
    max p (fkPrime p q) < pc + δ' →
    (bernoulliProduct (upperWeights Eb Ee n m hp.1 hp.2 hq) : Measure _) A = 0

/-- Exact lower-window input for Theorem 1.4(2). -/
def LowerWindow {E : Type*} (A : Set (EdgeConfiguration E)) (pc : ℝ)
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) : Prop :=
  ∃ δ > 0, ∀ p (hp : p ∈ Icc (0 : ℝ) 1),
    pc - δ < min p (fkPrime p q) →
    (bernoulliProduct (lowerWeights Eb Ee n m hp.1 hp.2 hq) : Measure _) A = 1

/-- Exact infinite-volume comparison supplied by Proposition 4.2. -/
def ComparisonInput {E : Type*}
    (fk : ℝ → ℝ → Set (ProbabilityMeasure (EdgeConfiguration E)))
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) : Prop :=
  ∀ p (hp : p ∈ Icc (0 : ℝ) 1) φ, φ ∈ fk p q →
    StochLe (bernoulliProduct (lowerWeights Eb Ee n m hp.1 hp.2 hq)) φ ∧
    StochLe φ (bernoulliProduct (upperWeights Eb Ee n m hp.1 hp.2 hq))

/-- The two conclusions of Theorem 1.4 for a fixed `q`. -/
def ExtendedPhaseStatement {E : Type*} (A : Set (EdgeConfiguration E)) (pc : ℝ)
    (fk : ℝ → ℝ → Set (ProbabilityMeasure (EdgeConfiguration E)))
    (q : ℝ) : Prop :=
  ∃ δ, ∃ δ', 0 < δ ∧ 0 < δ' ∧
    (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), max p (fkPrime p q) < pc + δ' →
      ∃ μ : ProbabilityMeasure (EdgeConfiguration E), (μ : Measure _) A = 0 ∧
        (∀ φ ∈ fk p q, StochLe φ μ) ∧ (∀ φ ∈ fk p q, (φ : Measure _) A = 0)) ∧
    (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), pc - δ < min p (fkPrime p q) →
      ∃ μ : ProbabilityMeasure (EdgeConfiguration E), (μ : Measure _) A = 1 ∧
        (∀ φ ∈ fk p q, StochLe μ φ) ∧ (∀ φ ∈ fk p q, (φ : Measure _) A = 1))

/-- Geometric reduction for Theorem 1.4 with the external probabilistic inputs
kept explicit.  In the application to the paper, `essential` is the
Aizenman--Grimmett essential-enhancement property and the two `*AG` arguments
are supplied by the strict critical-point shift for bounded-distance essential
enhancements. -/
theorem extended_phases_from_uniform_devices
    {E StarDevice CycleDevice : Type*}
    (A : Set (EdgeConfiguration E)) (pc : ℝ)
    (fk : ℝ → ℝ → Set (ProbabilityMeasure (EdgeConfiguration E)))
    (starSupport : StarDevice → Set E) (starDevices : Set StarDevice)
    (starPivot : StarDevice → E)
    (cycleSupport : CycleDevice → Set E) (cycleDevices : Set CycleDevice)
    (cyclePivot : CycleDevice → E)
    (essential : E → Prop) (n m : ℕ)
    (hstarPivot : ∀ d, starPivot d ∈ starSupport d)
    (hcyclePivot : ∀ d, cyclePivot d ∈ cycleSupport d)
    (hstarEssential : ∀ d, essential (starPivot d))
    (hcycleEssential : ∀ d, essential (cyclePivot d))
    (edgeDist : E → E → ℕ)
    (htriangle : ∀ a b c, edgeDist a c ≤ edgeDist a b + edgeDist b c)
    (Ks Rs Kc Rc : ℕ)
    (hlocalStar : ∀ e, ∃ d ∈ starDevices, ∀ f ∈ starSupport d, edgeDist e f ≤ Ks)
    (hdiamStar : ∀ d ∈ starDevices, ∀ f ∈ starSupport d,
      edgeDist f (starPivot d) ≤ Rs)
    (hlocalCycle : ∀ e, ∃ d ∈ cycleDevices, ∀ f ∈ cycleSupport d, edgeDist e f ≤ Kc)
    (hdiamCycle : ∀ d ∈ cycleDevices, ∀ f ∈ cycleSupport d,
      edgeDist f (cyclePivot d) ≤ Rc)
    (hA : IsIncreasingEvent A) (hmeas : MeasurableSet A)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≠ 1)
    (hcompare : ∀ (Ms : Set StarDevice) (Mc : Set CycleDevice),
      Ms ⊆ starDevices → Mc ⊆ cycleDevices →
      AuxiliaryFree starSupport starPivot Ms →
      AuxiliaryFree cycleSupport cyclePivot Mc →
      ComparisonInput fk (starPivot '' Ms) (cyclePivot '' Mc) n m q hq)
    (hstarAGupper : ∀ (Eb Ee : Set E),
      AllEssential essential Eb → AllEssential essential Ee →
      BoundedDistance edgeDist Eb → BoundedDistance edgeDist Ee →
      UpperWindow A pc Eb Ee n m q hq)
    (hcycleAGlower : ∀ (Eb Ee : Set E),
      AllEssential essential Eb → AllEssential essential Ee →
      BoundedDistance edgeDist Eb → BoundedDistance edgeDist Ee →
      LowerWindow A pc Eb Ee n m q hq) :
    ExtendedPhaseStatement A pc fk q := by
  obtain ⟨Ms, hMsD, hMsPair, hMsAux, hMsMeet, hMsDense⟩ :=
    exists_uniform_device_packing starSupport starDevices starPivot hstarPivot
      edgeDist htriangle Ks Rs hlocalStar hdiamStar
  obtain ⟨Mc, hMcD, hMcPair, hMcAux, hMcMeet, hMcDense⟩ :=
    exists_uniform_device_packing cycleSupport cycleDevices cyclePivot hcyclePivot
      edgeDist htriangle Kc Rc hlocalCycle hdiamCycle
  have hstarAll : AllEssential essential (starPivot '' Ms) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hstarEssential d
  have hcycleAll : AllEssential essential (cyclePivot '' Mc) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hcycleEssential d
  have hstarBounded : BoundedDistance edgeDist (starPivot '' Ms) :=
    ⟨Ks + Rs, hMsDense⟩
  have hcycleBounded : BoundedDistance edgeDist (cyclePivot '' Mc) :=
    ⟨Kc + Rc, hMcDense⟩
  exact extended_phases_of_comparison_and_essentialEnhancement
    A pc fk (starPivot '' Ms) (cyclePivot '' Mc) n m hA hmeas q hq hq1
    (hcompare Ms Mc hMsD hMcD hMsAux hMcAux)
    (hstarAGupper _ _ hstarAll hcycleAll hstarBounded hcycleBounded)
    (hcycleAGlower _ _ hstarAll hcycleAll hstarBounded hcycleBounded)

end
end FK.Theorem14
