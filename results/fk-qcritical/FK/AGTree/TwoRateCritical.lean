import FK.AGTree.SharpThreshold

/-!
# The exact two-rate critical curve of the activated two-class tree

The two-class tree `Ultra.G` carries the bond law `Ultra.law r`: class-`0` (base) edges are
open with probability `r 0 = b`, class-`1` (activation) edges with probability `r 1 = s`,
independently.  The existing development proves the *base* threshold (`s = 0`):
`2 b < 1` gives no percolation and `1 < 2 b` gives percolation.

Here we prove the exact two-rate criterion: percolation on `Perc` holds iff the branching
mean matrix `A = !![2b, 2s; 3b, s]` has spectral radius above one, which for this matrix is
equivalent to `1 < 2 b + s + 4 b s`.  Hence the enhanced (activated) critical base rate at
activation rate `s` is exactly `(1 - s) / (2 + 4 s)`, strictly below the base value `1/2` for
every positive activation rate: the activation class is *essential*.

The two directions of the strict criterion are proved by different arguments:

* **subcritical** (`2b + s + 4bs < 1`): the first-moment (Boole) inequality
  `pr{Fwd v (n+1)} ≤ 2b pr{Fwd v₀ n} + 2s pr{Fwd v₁ n}` at a class-`0` vertex and
  `≤ 3b pr{Fwd v₀ n} + s pr{Fwd v₁ n}` at a class-`1` vertex, together with the explicit
  barrier vector `(1+s, 1+b)`, which the mean matrix maps *below itself* precisely when
  `2b + s + 4bs ≤ 1`;
* **supercritical** (`1 < 2b + s + 4bs`): an explicit sub-fixed point of the exact
  branching recursion, built from the mean-matrix vector `(1+s, 1+b)` scaled down by an
  explicit small `t`;
* **critical** (`2b + s + 4bs = 1`, `b > 0`): first-moment methods degenerate at criticality,
  so this direction instead uses the *exact* fixed-point equations of the two class cluster
  probabilities (`cluster_fixed_zero`, `cluster_fixed_one`), multiplied by the left Perron
  vector `(1-s, 2s)` of the mean matrix at criticality.  The Perron-weighted sum of the two
  second-order remainders `Q₀ = (u+v-uv)² + 2uv` and `Q₁ = u(v(3-3u+u²) + u(3-u))` vanishes,
  and each is nonnegative on `[0,1]²`, so `u = bx = 0` and `v = sy = 0`: there is no
  percolation on the curve.

Every proof is complete; the only axioms are the three standard ones
(`propext`, `Classical.choice`, `Quot.sound`), checked at the end of the file, at default
heartbeat limits.

Main results:

* `two_rate_criterion`, `two_rate_criterion_full` — the two-rate phase criterion, strict on
  both sides plus the critical curve;
* `critical_curve`, `critical_curve_div` — at activation `s` the base rate is subcritical
  below `critBase s = (1-s)/(2+4s)` and supercritical above it;
* `critBase_zero`, `critBase_half`, `critBase_endpoints`, `critBase_continuousOn` — the
  phase boundary is the continuous curve from `(0, 1/2)` to `(1, 0)`;
* `critBase_strict_decrease`, `critBase_essential` — every positive activation rate strictly
  lowers the critical base rate, with the decrement bound `b_c(s) ≤ 1/2 - s/4`;
* `enhanced_window`, `enhancement_strict_at_some_base`, `tree_reference_shift` — the
  AG-style conclusion: at a base rate strictly below `1/2` the activated law percolates while
  the unactivated law does not;
* `percolation_at_paper_point`, `no_percolation_at_tenth_half`, `naive_bound_insufficient` —
  the paper's point `(3/10, 1/2)` is supercritical with exact critical base `1/8`, while
  `(1/10, 1/2)` is subcritical although the crude one-type bound `3b + 2s > 1` fails to see it;
* `base_criterion_agrees` — consistency with the previously proved sharp base threshold;
* `cluster_fixed`, `cluster_fixed_rep`, `cluster_fixed_zero`, `cluster_fixed_one`,
  `pr_fwd_class`, `pr_cluster_class` — class dependence of the forward/cluster probabilities
  and the exact two-class fixed-point equations.

Not covered here: the single degenerate corner `(b, s) = (0, 1)` of the critical curve.  There
every activation edge is open and every activation vertex has an activation child, so the
forward cluster of the root is infinite deterministically and the law percolates; the strict
inequality in `percolation_zero_of_lt` therefore cannot be relaxed to `≤`, and this one point
is the only case of `2b + s + 4bs = 1` not decided in this file (all cases with `b > 0` are
decided by `percolation_zero_of_critical`).  The deterministic-path argument for the corner is
elementary but not formalised here.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal unitInterval Topology

/-! ### Vertex classes -/

/-- `v` ends in a letter of class `j`. -/
def VClass (v : V) (j : Fin 2) : Prop := ∃ a : A, v.w.getLast? = some a ∧ acls a = j

lemma vclass_snoc (v : V) (b : A) (h : v.Valid b) : VClass (v.snoc b h) (acls b) :=
  ⟨b, V.getLast?_snoc v b h, rfl⟩

lemma vclass_ne_nil {v : V} {j : Fin 2} (h : VClass v j) : v.w ≠ [] := by
  obtain ⟨a, ha, _⟩ := h
  intro h0
  rw [h0] at ha
  simp at ha

lemma vclass_last {v : V} {j : Fin 2} (h : VClass v j) (hv : v.w ≠ []) : acls (v.w.getLast hv) = j := by
  obtain ⟨a, ha, hc⟩ := h
  have h1 : a = v.w.getLast hv := by
    rw [List.getLast?_eq_some_getLast hv] at ha
    exact (Option.some.inj ha).symm
  rw [← h1]
  exact hc

lemma vclass_unique {v : V} {j j' : Fin 2} (h : VClass v j) (h' : VClass v j') : j = j' := by
  obtain ⟨a, ha, hc⟩ := h
  obtain ⟨a', ha', hc'⟩ := h'
  rw [ha] at ha'
  have : a = a' := Option.some.inj ha'
  rw [← hc, ← hc', this]

/-- Exact count of valid letters of a class at a vertex. -/
lemma valid_class_card {v : V} (hv : v.w ≠ []) (j : Fin 2) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = j)).card =
      dcount j - (if acls (v.w.getLast hv) = j then 1 else 0) :=
  card_valid_class hv j

lemma valid_class_zero_card_zero {v : V} (h : VClass v 0) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = 0)).card = 2 := by
  have hv := vclass_ne_nil h
  rw [valid_class_card hv (0 : Fin 2), vclass_last h hv, dcount_zero]
  simp

lemma valid_class_zero_card_one {v : V} (h : VClass v 0) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = 1)).card = 2 := by
  have hv := vclass_ne_nil h
  rw [valid_class_card hv (1 : Fin 2), vclass_last h hv, dcount_one]
  simp [show (0 : Fin 2) ≠ 1 from by decide]

lemma valid_class_one_card_zero {v : V} (h : VClass v 1) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = 0)).card = 3 := by
  have hv := vclass_ne_nil h
  rw [valid_class_card hv (0 : Fin 2), vclass_last h hv, dcount_zero]
  simp [show (1 : Fin 2) ≠ 0 from by decide]

lemma valid_class_one_card_one {v : V} (h : VClass v 1) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = 1)).card = 1 := by
  have hv := vclass_ne_nil h
  rw [valid_class_card hv (1 : Fin 2), vclass_last h hv, dcount_one]
  simp


/-! ### Sums and products over class fibres -/

/-- A sum of a class-constant function over a set of letters splits into the two classes. -/
lemma sum_class_const (T : Finset A) (h : Fin 2 → ℝ) :
    ∑ a ∈ T, h (acls a) =
      ((T.filter (fun a => acls a = 0)).card : ℝ) * h 0 +
        ((T.filter (fun a => acls a = 1)).card : ℝ) * h 1 := by
  rw [← Finset.sum_fiberwise' T acls h, Fin.sum_univ_two]
  simp only [Finset.sum_const, nsmul_eq_mul]

/-- A product of a class-constant function over a set of letters splits into the two classes. -/
lemma prod_class_const (T : Finset A) (h : Fin 2 → ℝ) :
    ∏ a ∈ T, h (acls a) =
      h 0 ^ (T.filter (fun a => acls a = 0)).card *
        h 1 ^ (T.filter (fun a => acls a = 1)).card := by
  rw [← Finset.prod_fiberwise' T acls h, Fin.prod_univ_two]
  simp only [Finset.prod_const]

/-- The `if valid` sum over the five letters at a vertex. -/
lemma sum_if_valid_nd (v : V) (h : Fin 2 → ℝ) :
    ∑ a : A, (if v.Valid a then h (acls a) else 0) =
      ((Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 0)).card : ℝ) * h 0 +
        ((Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 1)).card : ℝ) * h 1 := by
  rw [← Finset.sum_filter, sum_class_const]
  rw [Finset.filter_filter, Finset.filter_filter]

/-- The `if valid` sum in dependent-`if` form. -/
lemma sum_if_valid (v : V) (h : Fin 2 → ℝ) :
    ∑ a : A, (if hv : v.Valid a then h (acls a) else 0) =
      ((Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 0)).card : ℝ) * h 0 +
        ((Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 1)).card : ℝ) * h 1 := by
  rw [show (∑ a : A, (if hv : v.Valid a then h (acls a) else 0)) =
      ∑ a : A, (if v.Valid a then h (acls a) else 0) from
    Finset.sum_congr rfl (fun a _ => by by_cases hv : v.Valid a <;> simp [hv])]
  exact sum_if_valid_nd v h

/-- The `if valid` product over the five letters at a vertex. -/
lemma prod_if_valid_nd (v : V) (h : Fin 2 → ℝ) :
    ∏ a : A, (if v.Valid a then h (acls a) else 1) =
      h 0 ^ (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 0)).card *
        h 1 ^ (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 1)).card := by
  rw [← Finset.prod_filter, prod_class_const]
  rw [Finset.filter_filter, Finset.filter_filter]

/-- The `if valid` product in dependent-`if` form. -/
lemma prod_if_valid (v : V) (h : Fin 2 → ℝ) :
    ∏ a : A, (if hv : v.Valid a then h (acls a) else 1) =
      h 0 ^ (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 0)).card *
        h 1 ^ (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 1)).card := by
  rw [show (∏ a : A, (if hv : v.Valid a then h (acls a) else 1)) =
      ∏ a : A, (if v.Valid a then h (acls a) else 1) from
    Finset.prod_congr rfl (fun a _ => by by_cases hv : v.Valid a <;> simp [hv])]
  exact prod_if_valid_nd v h


/-! ### Supercritical direction: an explicit sub-fixed point forces percolation -/

/-- Elementary two-variable inequality for the class-`0` recursion. -/
lemma poly_sq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    2 * (x + y) - 3 * (x ^ 2 + y ^ 2) ≤ 1 - (1 - x) ^ 2 * (1 - y) ^ 2 := by
  nlinarith [sq_nonneg (x - y),
    mul_nonneg (mul_nonneg hx hy) (by nlinarith : (0:ℝ) ≤ 2 * x + 2 * y - x * y)]

/-- Elementary two-variable inequality for the class-`1` recursion. -/
lemma poly_cu (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    3 * x + y - 5 * (x ^ 2 + y ^ 2) ≤ 1 - (1 - x) ^ 3 * (1 - y) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (2 * x - y),
    mul_nonneg (pow_nonneg hx 3) (by linarith : (0:ℝ) ≤ 1 - y),
    mul_nonneg (mul_nonneg (pow_nonneg hx 2) hy) (by linarith : (0:ℝ) ≤ 3 - x)]

/-- **Uniform lower bounds from a sub-fixed point.**  If the class failure-complement pair `e`
satisfies the two one-step inequalities, then every vertex of class `j` reaches every forward
level with probability at least `e j`, and the root reaches every level with probability at
least `e 1`. -/
theorem fwd_ge_of_sub_fixed (r : Fin 2 → unitInterval) (e : Fin 2 → ℝ)
    (he0 : 0 ≤ e 0) (he1 : 0 ≤ e 1)
    (hbe : (r 0 : ℝ) * e 0 ≤ 1) (hse : (r 1 : ℝ) * e 1 ≤ 1)
    (h0 : e 0 ≤ 1 - (1 - (r 0 : ℝ) * e 0) ^ 2 * (1 - (r 1 : ℝ) * e 1) ^ 2)
    (h1 : e 1 ≤ 1 - (1 - (r 0 : ℝ) * e 0) ^ 3 * (1 - (r 1 : ℝ) * e 1)) :
    (∀ (n : ℕ) (v : V) (j : Fin 2), VClass v j → e j ≤ pr r {ω | Fwd ω v n}) ∧
      (∀ n : ℕ, e 1 ≤ pr r {ω | Fwd ω V.root n}) := by
  classical
  have key : ∀ n : ℕ,
      (∀ (v : V) (j : Fin 2), VClass v j → e j ≤ pr r {ω | Fwd ω v n}) ∧
        (e 1 ≤ pr r {ω | Fwd ω V.root n}) := by
    intro n
    induction n with
    | zero =>
      have hp2 : (0:ℝ) ≤ (1 - (r 0 : ℝ) * e 0) ^ 2 * (1 - (r 1 : ℝ) * e 1) ^ 2 := by positivity
      have hp3 : (0:ℝ) ≤ (1 - (r 0 : ℝ) * e 0) ^ 3 * (1 - (r 1 : ℝ) * e 1) := by positivity
      have hle0 : e 0 ≤ 1 := by linarith
      have hle1 : e 1 ≤ 1 := by linarith
      refine ⟨fun v j _ => ?_, ?_⟩
      · rw [pr_fwd_zero]
        have hj : j = 0 ∨ j = 1 := by omega
        rcases hj with rfl | rfl
        · exact hle0
        · exact hle1
      · rw [pr_fwd_zero]; exact hle1
    | succ n ih =>
      obtain ⟨ihv, _⟩ := ih
      have hstep : ∀ (u : V) (a : A),
          (if h : u.Valid a then 1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 1) ≤
            (if h : u.Valid a then 1 - (r (acls a) : ℝ) * e (acls a) else 1) := by
        intro u a
        by_cases hv : u.Valid a
        · rw [dif_pos hv, dif_pos hv]
          have hchild : e (acls a) ≤ pr r {ω | Fwd ω (u.snoc a hv) n} :=
            ihv (u.snoc a hv) (acls a) (vclass_snoc u a hv)
          have hr : (0:ℝ) ≤ (r (acls a) : ℝ) := unitInterval.nonneg _
          nlinarith [mul_le_mul_of_nonneg_left hchild hr]
        · rw [dif_neg hv, dif_neg hv]
      have hprod : ∀ u : V,
          pr r {ω | ¬ Fwd ω u (n + 1)} ≤
            (1 - (r 0 : ℝ) * e 0) ^
                (Finset.univ.filter (fun a : A => u.Valid a ∧ acls a = 0)).card *
              (1 - (r 1 : ℝ) * e 1) ^
                (Finset.univ.filter (fun a : A => u.Valid a ∧ acls a = 1)).card := by
        intro u
        rw [measure_notFwd_succ]
        refine le_trans (prod_le_prod_real (s := Finset.univ)
          (f := fun a : A => if h : u.Valid a then
            1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 1)
          (g := fun a : A => if h : u.Valid a then 1 - (r (acls a) : ℝ) * e (acls a) else 1)
          (fun a _ => if_step_nonneg r u a n) (fun a _ => hstep u a)) ?_
        have hpv := prod_if_valid u (fun j : Fin 2 => 1 - (r j : ℝ) * e j)
        simpa using le_of_eq hpv
      have hcompl : ∀ u : V, pr r {ω | Fwd ω u (n + 1)} = 1 - pr r {ω | ¬ Fwd ω u (n + 1)} := by
        intro u
        have h := pr_compl_eq r {ω : G.edgeSet → Bool | Fwd ω u (n + 1)} (measurableSet_fwd u (n + 1))
        have hset : ({ω : G.edgeSet → Bool | Fwd ω u (n + 1)})ᶜ = {ω | ¬ Fwd ω u (n + 1)} := rfl
        rw [hset] at h; linarith
      refine ⟨fun v j hvj => ?_, ?_⟩
      · rw [hcompl v]
        have hc := hprod v
        have hj : j = 0 ∨ j = 1 := by omega
        rcases hj with rfl | rfl
        · rw [valid_class_zero_card_zero hvj, valid_class_zero_card_one hvj] at hc
          linarith [h0, hc]
        · rw [valid_class_one_card_zero hvj, valid_class_one_card_one hvj] at hc
          linarith [h1, hc]
      · rw [hcompl V.root]
        have hc := hprod V.root
        rw [card_valid_root (0 : Fin 2), card_valid_root (1 : Fin 2), dcount_zero, dcount_one] at hc
        have hb1 : (0:ℝ) ≤ 1 - (r 1 : ℝ) * e 1 := by linarith
        have hb2 : (1:ℝ) - (r 1 : ℝ) * e 1 ≤ 1 := by
          have := unitInterval.nonneg (r 1); nlinarith
        have hbb : (0:ℝ) ≤ 1 - (r 0 : ℝ) * e 0 := by linarith
        have hsq : (1 - (r 0 : ℝ) * e 0) ^ 3 * (1 - (r 1 : ℝ) * e 1) ^ 2 ≤
            (1 - (r 0 : ℝ) * e 0) ^ 3 * (1 - (r 1 : ℝ) * e 1) := by
          have hp : (1 - (r 1 : ℝ) * e 1) ^ 2 ≤ (1 - (r 1 : ℝ) * e 1) := by
            nlinarith [sq_nonneg (1 - (r 1 : ℝ) * e 1)]
          have h3 : (0:ℝ) ≤ (1 - (r 0 : ℝ) * e 0) ^ 3 := by positivity
          nlinarith
        linarith [h1, hsq, hc]
  exact ⟨fun n => (key n).1, fun n => (key n).2⟩


/-! ### The explicit sub-fixed point and the supercritical half -/

/-- **An explicit sub-fixed point of the two-class recursion.**  On the supercritical side
`1 < 2b + s + 4bs` the mean-matrix vector `w = (1+s, 1+b)` satisfies
`(Aw)_j = w_j + D` with `D = 2b + s + 4bs - 1 > 0`; scaling it down by an explicit small `t`
turns the linear slack `tD` into a genuine sub-fixed point of the nonlinear recursion.

This is a pure real-variable statement (no probability), so the numerical work is isolated
from the measure-theoretic application. -/
lemma exists_sub_fixed (b s : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hD : 1 < 2 * b + s + 4 * b * s) :
    ∃ e : Fin 2 → ℝ, 0 < e 0 ∧ 0 < e 1 ∧ b * e 0 ≤ 1 ∧ s * e 1 ≤ 1 ∧
      e 0 ≤ 1 - (1 - b * e 0) ^ 2 * (1 - s * e 1) ^ 2 ∧
      e 1 ≤ 1 - (1 - b * e 0) ^ 3 * (1 - s * e 1) := by
  classical
  set D : ℝ := 2 * b + s + 4 * b * s - 1 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; linarith
  set w : Fin 2 → ℝ := ![1 + s, 1 + b] with hwdef
  have hw0 : w 0 = 1 + s := rfl
  have hw1 : w 1 = 1 + b := rfl
  have hw0pos : 0 < w 0 := by rw [hw0]; linarith
  have hw1pos : 0 < w 1 := by rw [hw1]; linarith
  have hw0le : w 0 ≤ 2 := by rw [hw0]; linarith
  have hw1le : w 1 ≤ 2 := by rw [hw1]; linarith
  set K : ℝ := b ^ 2 * w 0 ^ 2 + s ^ 2 * w 1 ^ 2 with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hAw0 : 2 * b * w 0 + 2 * s * w 1 = w 0 + D := by
    rw [hw0, hw1, hDdef]; ring
  have hAw1 : 3 * b * w 0 + s * w 1 = w 1 + D := by
    rw [hw0, hw1, hDdef]; ring
  set t : ℝ := min (1 / 2) (D / (6 * (K + 1))) with htdef
  have ht0 : 0 < t := by
    rw [htdef]; exact lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := by rw [htdef]; exact min_le_left _ _
  have htK : 5 * (t * K) ≤ D := by
    have h1 : t ≤ D / (6 * (K + 1)) := by rw [htdef]; exact min_le_right _ _
    have h2 : (0:ℝ) < 6 * (K + 1) := by positivity
    have h3 : t * (6 * (K + 1)) ≤ D := (le_div_iff₀ h2).mp h1
    nlinarith [hK0, h3, ht0]
  refine ⟨![t * w 0, t * w 1], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 0 < t * w 0
    positivity
  · show 0 < t * w 1
    positivity
  · show b * (t * w 0) ≤ 1
    have hbt : b * t ≤ 1 / 2 := by
      have p1 : b * t ≤ 1 * t := mul_le_mul_of_nonneg_right hb1 ht0.le
      have p2 : (1:ℝ) * t ≤ 1 * (1/2) := by linarith [ht1]
      linarith [p1, p2]
    have h1 : (b * t) * w 0 ≤ (1 / 2) * 2 := mul_le_mul hbt hw0le (by positivity) (by norm_num)
    have h2 : b * (t * w 0) = (b * t) * w 0 := by ring
    rw [h2]; linarith [h1]
  · show s * (t * w 1) ≤ 1
    have hst : s * t ≤ 1 / 2 := by
      have p1 : s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs1 ht0.le
      have p2 : (1:ℝ) * t ≤ 1 * (1/2) := by linarith [ht1]
      linarith [p1, p2]
    have h1 : (s * t) * w 1 ≤ (1 / 2) * 2 := mul_le_mul hst hw1le (by positivity) (by norm_num)
    have h2 : s * (t * w 1) = (s * t) * w 1 := by ring
    rw [h2]; linarith [h1]
  · show t * w 0 ≤ 1 - (1 - b * (t * w 0)) ^ 2 * (1 - s * (t * w 1)) ^ 2
    have hx0 : (0:ℝ) ≤ b * (t * w 0) := by positivity
    have hy0 : (0:ℝ) ≤ s * (t * w 1) := by positivity
    have hx1 : b * (t * w 0) ≤ 1 := by
      have hbt : b * t ≤ 1 / 2 := by
        have p1 : b * t ≤ 1 * t := mul_le_mul_of_nonneg_right hb1 ht0.le
        have p2 : (1:ℝ) * t ≤ 1 * (1/2) := by linarith [ht1]
        linarith [p1, p2]
      have h1 : (b * t) * w 0 ≤ (1 / 2) * 2 := mul_le_mul hbt hw0le (by positivity) (by norm_num)
      have h2 : b * (t * w 0) = (b * t) * w 0 := by ring
      rw [h2]; linarith [h1]
    have hy1 : s * (t * w 1) ≤ 1 := by
      have hst : s * t ≤ 1 / 2 := by
        have p1 : s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs1 ht0.le
        have p2 : (1:ℝ) * t ≤ 1 * (1/2) := by linarith [ht1]
        linarith [p1, p2]
      have h1 : (s * t) * w 1 ≤ (1 / 2) * 2 := mul_le_mul hst hw1le (by positivity) (by norm_num)
      have h2 : s * (t * w 1) = (s * t) * w 1 := by ring
      rw [h2]; linarith [h1]
    have hp := poly_sq (b * (t * w 0)) (s * (t * w 1)) hx0 hy0 hx1 hy1
    have hsq : (b * (t * w 0)) ^ 2 + (s * (t * w 1)) ^ 2 = t ^ 2 * K := by
      rw [hKdef]; ring
    have hlin : 2 * (b * (t * w 0) + s * (t * w 1)) = t * (w 0 + D) := by
      rw [← hAw0]; ring
    have hstep : 0 ≤ t * (D - 3 * (t * K)) := mul_nonneg ht0.le (by nlinarith [htK])
    nlinarith [hp, hsq, hlin, hstep]
  · show t * w 1 ≤ 1 - (1 - b * (t * w 0)) ^ 3 * (1 - s * (t * w 1))
    have hx0 : (0:ℝ) ≤ b * (t * w 0) := by positivity
    have hy0 : (0:ℝ) ≤ s * (t * w 1) := by positivity
    have hx1 : b * (t * w 0) ≤ 1 := by
      have hbt : b * t ≤ 1 / 2 := by
        have p1 : b * t ≤ 1 * t := mul_le_mul_of_nonneg_right hb1 ht0.le
        have p2 : (1:ℝ) * t ≤ 1 * (1/2) := by linarith [ht1]
        linarith [p1, p2]
      have h1 : (b * t) * w 0 ≤ (1 / 2) * 2 := mul_le_mul hbt hw0le (by positivity) (by norm_num)
      have h2 : b * (t * w 0) = (b * t) * w 0 := by ring
      rw [h2]; linarith [h1]
    have hy1 : s * (t * w 1) ≤ 1 := by
      have hst : s * t ≤ 1 / 2 := by
        have p1 : s * t ≤ 1 * t := mul_le_mul_of_nonneg_right hs1 ht0.le
        have p2 : (1:ℝ) * t ≤ 1 * (1/2) := by linarith [ht1]
        linarith [p1, p2]
      have h1 : (s * t) * w 1 ≤ (1 / 2) * 2 := mul_le_mul hst hw1le (by positivity) (by norm_num)
      have h2 : s * (t * w 1) = (s * t) * w 1 := by ring
      rw [h2]; linarith [h1]
    have hp := poly_cu (b * (t * w 0)) (s * (t * w 1)) hx0 hy0 hx1 hy1
    have hsq : (b * (t * w 0)) ^ 2 + (s * (t * w 1)) ^ 2 = t ^ 2 * K := by
      rw [hKdef]; ring
    have hlin : 3 * (b * (t * w 0)) + s * (t * w 1) = t * (w 1 + D) := by
      rw [← hAw1]; ring
    have hstep : 0 ≤ t * (D - 5 * (t * K)) := mul_nonneg ht0.le (by nlinarith [htK])
    nlinarith [hp, hsq, hlin, hstep]

/-- **Percolation above the two-rate curve.**  If `1 < 2b + s + 4bs` then the activated law
percolates with positive probability. -/
theorem percolation_pos_of_one_lt (r : Fin 2 → unitInterval)
    (hlt : 1 < 2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ)) :
    0 < pr r {ω : G.edgeSet → Bool | Perc ω} := by
  obtain ⟨e, he0, he1, hbe, hse, h0, h1⟩ :=
    exists_sub_fixed (r 0 : ℝ) (r 1 : ℝ) (unitInterval.nonneg _) (unitInterval.le_one _)
      (unitInterval.nonneg _) (unitInterval.le_one _) hlt
  have hkey := fwd_ge_of_sub_fixed r e he0.le he1.le hbe hse h0 h1
  have hlim : e 1 ≤ pr r {ω | Cluster ω V.root} :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (pr_cluster_tendsto r V.root)
      (Eventually.of_forall (fun n => hkey.2 n))
  have hmono : pr r {ω | Cluster ω V.root} ≤ pr r {ω : G.edgeSet → Bool | Perc ω} :=
    pr_mono r (fun ω hω => ⟨V.root, cluster_infinite hω⟩)
  linarith

/-! ### Subcritical direction: two-class first-moment bounds and the barrier vector -/

/-- One step of the two-class linear (mean-matrix) bound, in class coordinates:
`0` for a vertex whose last letter is a base letter, `1` for an activation letter. -/
noncomputable def bndStep (b s : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![2 * b * x 0 + 2 * s * x 1, 3 * b * x 0 + s * x 1]

lemma bndStep_zero (b s : ℝ) (x : Fin 2 → ℝ) : bndStep b s x 0 = 2 * b * x 0 + 2 * s * x 1 := rfl
lemma bndStep_one (b s : ℝ) (x : Fin 2 → ℝ) : bndStep b s x 1 = 3 * b * x 0 + s * x 1 := rfl

/-- The linear bound sequence started at `(1,1)` (level zero has probability one). -/
noncomputable def bndSeq (b s : ℝ) : ℕ → Fin 2 → ℝ
  | 0 => fun _ => 1
  | (n + 1) => bndStep b s (bndSeq b s n)

/-- The barrier sequence started at the mean-matrix vector `(1+s, 1+b)`. -/
noncomputable def topSeq (b s : ℝ) : ℕ → Fin 2 → ℝ
  | 0 => ![1 + s, 1 + b]
  | (n + 1) => bndStep b s (topSeq b s n)

@[simp] lemma bndSeq_zero (b s : ℝ) : bndSeq b s 0 = fun _ => 1 := rfl
@[simp] lemma bndSeq_succ (b s : ℝ) (n : ℕ) : bndSeq b s (n + 1) = bndStep b s (bndSeq b s n) := rfl
@[simp] lemma topSeq_zero (b s : ℝ) : topSeq b s 0 = ![1 + s, 1 + b] := rfl
@[simp] lemma topSeq_succ (b s : ℝ) (n : ℕ) : topSeq b s (n + 1) = bndStep b s (topSeq b s n) := rfl

lemma topSeq_zero_zero (b s : ℝ) : topSeq b s 0 0 = 1 + s := rfl
lemma topSeq_zero_one (b s : ℝ) : topSeq b s 0 1 = 1 + b := rfl

/-- The mean-matrix step is monotone in a nonnegative parameter regime. -/
lemma bndStep_mono {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) {x y : Fin 2 → ℝ}
    (h0 : x 0 ≤ y 0) (h1 : x 1 ≤ y 1) :
    bndStep b s x 0 ≤ bndStep b s y 0 ∧ bndStep b s x 1 ≤ bndStep b s y 1 := by
  constructor
  · rw [bndStep_zero, bndStep_zero]
    nlinarith
  · rw [bndStep_one, bndStep_one]
    nlinarith

/-- The mean-matrix vector `(1+s, 1+b)` is mapped below itself exactly on the subcritical side
`2b + s + 4bs ≤ 1`. -/
lemma bndStep_top_zero_le {b s : ℝ} (hD : 2 * b + s + 4 * b * s ≤ 1) :
    bndStep b s (![1 + s, 1 + b] : Fin 2 → ℝ) 0 ≤ (1 + s) ∧
      bndStep b s (![1 + s, 1 + b] : Fin 2 → ℝ) 1 ≤ (1 + b) := by
  constructor
  · rw [bndStep_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · rw [bndStep_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith

/-- The barrier sequence is antitone. -/
lemma topSeq_antitone {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hD : 2 * b + s + 4 * b * s ≤ 1) :
    ∀ n : ℕ, topSeq b s (n + 1) 0 ≤ topSeq b s n 0 ∧ topSeq b s (n + 1) 1 ≤ topSeq b s n 1 := by
  intro n
  induction n with
  | zero =>
    simpa using bndStep_top_zero_le (b := b) (s := s) hD
  | succ n ih =>
    simpa using bndStep_mono (b := b) (s := s) hb hs ih.1 ih.2

/-- The linear bound is dominated by the barrier. -/
lemma bndSeq_le_top {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) :
    ∀ n : ℕ, bndSeq b s n 0 ≤ topSeq b s n 0 ∧ bndSeq b s n 1 ≤ topSeq b s n 1 := by
  intro n
  induction n with
  | zero =>
    constructor
    · rw [bndSeq_zero, topSeq_zero_zero]; simp only [Pi.one_apply]; linarith
    · rw [bndSeq_zero, topSeq_zero_one]; simp only [Pi.one_apply]; linarith
  | succ n ih =>
    simpa using bndStep_mono (b := b) (s := s) hb hs ih.1 ih.2


/-- **Two-class first-moment bound.**  The forward-cluster probability at level `n` of a
vertex of class `j` is at most the `j`-th component of the linear recursion. -/
theorem pr_fwd_le_bnd (r : Fin 2 → unitInterval) :
    ∀ (n : ℕ) (v : V) (j : Fin 2),
      VClass v j → pr r {ω | Fwd ω v n} ≤ bndSeq (r 0 : ℝ) (r 1 : ℝ) n j := by
  intro n
  induction n with
  | zero => intro v j _; rw [pr_fwd_zero]; exact le_refl 1
  | succ n ih =>
    intro v j hvj
    refine le_trans (pr_fwd_succ_le r v n) ?_
    have hmono : ∀ a : A,
        (if hv : v.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (v.snoc a hv) n} else 0) ≤
          (if hv : v.Valid a then
            (r (acls a) : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n (acls a) else 0) := by
      intro a
      by_cases hv : v.Valid a
      · rw [dif_pos hv, dif_pos hv]
        exact mul_le_mul_of_nonneg_left (ih (v.snoc a hv) (acls a) (vclass_snoc v a hv))
          (unitInterval.nonneg _)
      · rw [dif_neg hv, dif_neg hv]
    refine le_trans (Finset.sum_le_sum (fun a _ => hmono a)) ?_
    have hsum : (∑ a : A, (if hv : v.Valid a then
        (r (acls a) : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n (acls a) else 0)) =
        ((Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 0)).card : ℝ) *
            ((r 0 : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n 0) +
          ((Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 1)).card : ℝ) *
            ((r 1 : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n 1) :=
      sum_if_valid v (fun j : Fin 2 => (r j : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n j)
    rw [hsum, bndSeq_succ]
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl
    · rw [valid_class_zero_card_zero hvj, valid_class_zero_card_one hvj, bndStep_zero]
      push_cast
      nlinarith
    · rw [valid_class_one_card_zero hvj, valid_class_one_card_one hvj, bndStep_one]
      push_cast
      nlinarith


/-- The barrier sequence stays nonnegative. -/
lemma topSeq_nonneg {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) :
    ∀ n : ℕ, 0 ≤ topSeq b s n 0 ∧ 0 ≤ topSeq b s n 1 := by
  intro n
  induction n with
  | zero =>
    constructor
    · rw [topSeq_zero_zero]; linarith
    · rw [topSeq_zero_one]; linarith
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rw [topSeq_succ, bndStep_zero]; nlinarith [ih.1, ih.2]
    · rw [topSeq_succ, bndStep_one]; nlinarith [ih.1, ih.2]

/-- First-moment bound at the root (three base and two activation children). -/
theorem pr_fwd_root_le_bnd (r : Fin 2 → unitInterval) (n : ℕ) :
    pr r {ω | Fwd ω V.root (n + 1)} ≤
      3 * (r 0 : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n 0 +
        2 * (r 1 : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n 1 := by
  refine le_trans (pr_fwd_succ_le r V.root n) ?_
  have hmono : ∀ a : A,
      (if hv : V.root.Valid a then
        (r (acls a) : ℝ) * pr r {ω | Fwd ω (V.root.snoc a hv) n} else 0) ≤
        (if hv : V.root.Valid a then
          (r (acls a) : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n (acls a) else 0) := by
    intro a
    by_cases hv : V.root.Valid a
    · rw [dif_pos hv, dif_pos hv]
      exact mul_le_mul_of_nonneg_left
        (pr_fwd_le_bnd r n (V.root.snoc a hv) (acls a) (vclass_snoc V.root a hv))
        (unitInterval.nonneg _)
    · rw [dif_neg hv, dif_neg hv]
  refine le_trans (Finset.sum_le_sum (fun a _ => hmono a)) ?_
  have hsum : (∑ a : A, (if hv : V.root.Valid a then
      (r (acls a) : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n (acls a) else 0)) =
      ((Finset.univ.filter (fun a : A => V.root.Valid a ∧ acls a = 0)).card : ℝ) *
          ((r 0 : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n 0) +
        ((Finset.univ.filter (fun a : A => V.root.Valid a ∧ acls a = 1)).card : ℝ) *
          ((r 1 : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n 1) :=
    sum_if_valid V.root (fun j : Fin 2 => (r j : ℝ) * bndSeq (r 0 : ℝ) (r 1 : ℝ) n j)
  rw [hsum, card_valid_root (0 : Fin 2), card_valid_root (1 : Fin 2), dcount_zero, dcount_one]
  push_cast
  nlinarith

/-- **Subcritical direction.**  If `2b + s + 4bs < 1` the activated law does not percolate. -/
theorem percolation_zero_of_lt (r : Fin 2 → unitInterval)
    (hlt : 2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) < 1) :
    pr r {ω : G.edgeSet → Bool | Perc ω} = 0 := by
  classical
  set b : ℝ := (r 0 : ℝ) with hbdef
  set s : ℝ := (r 1 : ℝ) with hsdef
  have hr0 : (r 0 : ℝ) = b := hbdef.symm
  have hr1 : (r 1 : ℝ) = s := hsdef.symm
  have hb0 : 0 ≤ b := by rw [hbdef]; exact unitInterval.nonneg _
  have hs0 : 0 ≤ s := by rw [hsdef]; exact unitInterval.nonneg _
  have hDle : 2 * b + s + 4 * b * s ≤ 1 := hlt.le
  have hnn := topSeq_nonneg (b := b) (s := s) hb0 hs0
  have hanti0 : Antitone (fun n => topSeq b s n 0) :=
    antitone_nat_of_succ_le (fun n => (topSeq_antitone hb0 hs0 hDle n).1)
  have hanti1 : Antitone (fun n => topSeq b s n 1) :=
    antitone_nat_of_succ_le (fun n => (topSeq_antitone hb0 hs0 hDle n).2)
  set L0 : ℝ := ⨅ n, topSeq b s n 0 with hL0def
  set L1 : ℝ := ⨅ n, topSeq b s n 1 with hL1def
  have hbdd0 : BddBelow (Set.range (fun n => topSeq b s n 0)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hnn n).1⟩
  have hbdd1 : BddBelow (Set.range (fun n => topSeq b s n 1)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hnn n).2⟩
  have htend0 : Tendsto (fun n => topSeq b s n 0) atTop (𝓝 L0) := tendsto_atTop_ciInf hanti0 hbdd0
  have htend1 : Tendsto (fun n => topSeq b s n 1) atTop (𝓝 L1) := tendsto_atTop_ciInf hanti1 hbdd1
  have hL00 : 0 ≤ L0 := le_ciInf (fun n => (hnn n).1)
  have hcomp0 : ∀ n : ℕ, topSeq b s (n + 1) 0 =
      2 * b * topSeq b s n 0 + 2 * s * topSeq b s n 1 := by
    intro n; rw [topSeq_succ, bndStep_zero]
  have hcomp1 : ∀ n : ℕ, topSeq b s (n + 1) 1 =
      3 * b * topSeq b s n 0 + s * topSeq b s n 1 := by
    intro n; rw [topSeq_succ, bndStep_one]
  have hshift0 : Tendsto (fun n => topSeq b s (n + 1) 0) atTop (𝓝 L0) :=
    htend0.comp (tendsto_add_atTop_nat 1)
  have hshift1 : Tendsto (fun n => topSeq b s (n + 1) 1) atTop (𝓝 L1) :=
    htend1.comp (tendsto_add_atTop_nat 1)
  have hrhs0 : Tendsto (fun n => 2 * b * topSeq b s n 0 + 2 * s * topSeq b s n 1) atTop
      (𝓝 (2 * b * L0 + 2 * s * L1)) :=
    (htend0.const_mul (2 * b)).add (htend1.const_mul (2 * s))
  have hrhs1 : Tendsto (fun n => 3 * b * topSeq b s n 0 + s * topSeq b s n 1) atTop
      (𝓝 (3 * b * L0 + s * L1)) :=
    (htend0.const_mul (3 * b)).add (htend1.const_mul s)
  have e0 : L0 = 2 * b * L0 + 2 * s * L1 := by
    refine tendsto_nhds_unique hshift0 ?_
    simpa only [hcomp0] using hrhs0
  have e1 : L1 = 3 * b * L0 + s * L1 := by
    refine tendsto_nhds_unique hshift1 ?_
    simpa only [hcomp1] using hrhs1
  have hL0zero : L0 = 0 := by
    rcases lt_or_ge 0 L0 with hpos | hnonpos
    · exfalso
      have h2 : L1 * (1 - s) = 3 * b * L0 := by nlinarith [e1]
      have h3 : L0 * (1 - s) = 2 * b * L0 * (1 - s) + 6 * b * L0 * s := by nlinarith [e0, h2]
      have h4 : (1 - s) = 2 * b * (1 - s) + 6 * b * s := by
        have h5 : L0 * (1 - s) = L0 * (2 * b * (1 - s) + 6 * b * s) := by linarith [h3]
        exact mul_left_cancel₀ (ne_of_gt hpos) h5
      nlinarith [h4, hlt]
    · linarith [hL00]
  have hL1zero : L1 = 0 := by
    have h2 : L1 * (1 - s) = 3 * b * L0 := by nlinarith [e1]
    rw [hL0zero] at e0 h2
    nlinarith [e0, h2]
  have hfwd : ∀ (v : V) (j : Fin 2), VClass v j → pr r {ω | Cluster ω v} = 0 := by
    intro v j hvj
    refine le_antisymm ?_ (pr_nonneg r _)
    have htend := pr_cluster_tendsto r v
    have hlim : Tendsto (fun n => topSeq b s n j) atTop (𝓝 0) := by
      rcases (show j = 0 ∨ j = 1 from by omega) with rfl | rfl
      · simpa only [hL0zero] using htend0
      · simpa only [hL1zero] using htend1
    refine le_of_tendsto_of_tendsto htend hlim (Filter.Eventually.of_forall (fun n => ?_))
    refine le_trans (pr_fwd_le_bnd r n v j hvj) ?_
    have hbl := bndSeq_le_top (b := b) (s := s) hb0 hs0 n
    have hb : bndSeq (r 0 : ℝ) (r 1 : ℝ) n = bndSeq b s n := by rw [hr0, hr1]
    rw [hb]
    rcases (show j = 0 ∨ j = 1 from by omega) with rfl | rfl
    · exact hbl.1
    · exact hbl.2
  have hroot : pr r {ω | Cluster ω V.root} = 0 := by
    refine le_antisymm ?_ (pr_nonneg r _)
    have htend := pr_cluster_tendsto r V.root
    have hlim : Tendsto (fun n => 3 * b * topSeq b s n 0 + 2 * s * topSeq b s n 1) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => 3 * b * topSeq b s n 0 + 2 * s * topSeq b s n 1) atTop
          (𝓝 (3 * b * L0 + 2 * s * L1)) :=
        (htend0.const_mul (3 * b)).add (htend1.const_mul (2 * s))
      simpa only [hL0zero, hL1zero, mul_zero, add_zero] using h1
    have hshift : Tendsto (fun n => pr r {ω | Fwd ω V.root (n + 1)}) atTop
        (𝓝 (pr r {ω | Cluster ω V.root})) :=
      htend.comp (tendsto_add_atTop_nat 1)
    refine le_of_tendsto_of_tendsto hshift hlim (Filter.Eventually.of_forall (fun n => ?_))
    refine le_trans (pr_fwd_root_le_bnd r n) ?_
    have hbl := bndSeq_le_top (b := b) (s := s) hb0 hs0 n
    rw [hr0, hr1]
    nlinarith [hbl.1, hbl.2, hb0, hs0]
  have hset : {ω : G.edgeSet → Bool | Perc ω} = ⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m} := by
    ext ω
    simp only [Perc, Set.mem_setOf_eq, Set.mem_iUnion]
    exact infinite_iff_exists_cluster ω
  rw [hset]
  have hmu : law r (⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m}) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_iUnion_le (fun m : V => {ω : G.edgeSet → Bool | Cluster ω m})) ?_
    have hz : ∀ m : V, law r {ω : G.edgeSet → Bool | Cluster ω m} = 0 := by
      intro m
      by_cases hne : m.w = []
      · have hm : m = V.root := V.ext hne
        subst hm
        exact measure_eq_zero_of_pr_eq_zero hroot
      · exact measure_eq_zero_of_pr_eq_zero
          (hfwd m (acls (m.w.getLast hne)) ⟨m.w.getLast hne, List.getLast?_eq_some_getLast hne, rfl⟩)
    simp only [hz]
    simp
  rw [pr, measureReal_def, hmu, ENNReal.toReal_zero]


/-! ### The exact two-rate criterion and the enhanced critical base rate -/

/-- **The two-rate criterion.**  On the two-class tree, the activated two-rate bond law
percolates exactly on the supercritical side of the branching mean matrix
`A = !![2b, 2s; 3b, s]`, whose spectral radius crosses one at `2b + s + 4bs = 1`.
Both implications are proved below by genuinely different arguments. -/
theorem two_rate_criterion (r : Fin 2 → unitInterval) :
    (2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) < 1 →
        pr r {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
      (1 < 2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) →
        0 < pr r {ω : G.edgeSet → Bool | Perc ω}) :=
  ⟨percolation_zero_of_lt r, percolation_pos_of_one_lt r⟩

lemma enhRate_zero (p s : unitInterval) : ((enhRate p s) 0 : ℝ) = (p : ℝ) := by
  simp [enhRate]

lemma enhRate_one (p s : unitInterval) : ((enhRate p s) 1 : ℝ) = (s : ℝ) := by
  simp [enhRate]

/-- The critical base rate as a function of the activation rate, `b_c(s) = (1-s)/(2+4s)`. -/
noncomputable def critBase (s : ℝ) : ℝ := (1 - s) / (2 + 4 * s)

/-- **The exact critical curve of the activated two-class tree.**  At activation rate `s` the
base rate `p` is subcritical below `b_c(s) = (1-s)/(2+4s)` and supercritical above it, in both
cases for the *same* percolation event `Perc` and the *same* normalized independent bond law
`law (enhRate p s)`. -/
theorem critical_curve (s : unitInterval) :
    (∀ p : unitInterval, (p : ℝ) * (2 + 4 * (s : ℝ)) < 1 - (s : ℝ) →
        pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
      (∀ p : unitInterval, 1 - (s : ℝ) < (p : ℝ) * (2 + 4 * (s : ℝ)) →
        0 < pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω}) := by
  constructor
  · intro p hp
    refine percolation_zero_of_lt _ ?_
    rw [enhRate_zero, enhRate_one]
    linarith
  · intro p hp
    refine percolation_pos_of_one_lt _ ?_
    rw [enhRate_zero, enhRate_one]
    linarith

/-- The critical curve in division form. -/
theorem critical_curve_div (s : unitInterval) :
    (∀ p : unitInterval, (p : ℝ) < critBase (s : ℝ) →
        pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
      (∀ p : unitInterval, critBase (s : ℝ) < (p : ℝ) →
        0 < pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω}) := by
  have hpos : (0:ℝ) < 2 + 4 * (s : ℝ) := by
    have := unitInterval.nonneg s; linarith
  constructor
  · intro p hp
    refine (critical_curve s).1 p ?_
    rw [critBase] at hp
    exact (lt_div_iff₀ hpos).mp hp
  · intro p hp
    refine (critical_curve s).2 p ?_
    rw [critBase] at hp
    exact (div_lt_iff₀ hpos).mp hp

/-- The unactivated critical base rate is `1/2`, recovering the sharp base threshold. -/
theorem critBase_zero : critBase 0 = 1 / 2 := by
  rw [critBase]; norm_num

/-- **Essential activation.**  Every positive activation rate strictly lowers the critical base
rate, with the explicit decrement bound `b_c(s) ≤ 1/2 - s/4`. -/
theorem critBase_strict_decrease {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hs : 0 < s) :
    critBase s < 1 / 2 ∧ critBase s ≤ 1 / 2 - s / 4 := by
  have hpos : (0:ℝ) < 2 + 4 * s := by linarith
  have hlt : critBase s < 1 / 2 := by
    rw [critBase, div_lt_iff₀ hpos]
    nlinarith
  have hle : critBase s ≤ 1 / 2 - s / 4 := by
    rw [critBase, div_le_iff₀ hpos]
    nlinarith
  exact ⟨hlt, hle⟩

/-- **The strict enhanced window.**  For every positive activation rate `s` and every base rate
strictly above `b_c(s)` but strictly below the unactivated threshold `1/2`, the activated law
percolates while the unactivated law at the same base rate does not. -/
theorem enhanced_window (s : unitInterval) (p : unitInterval)
    (hp1 : critBase (s : ℝ) < (p : ℝ)) (hp2 : (p : ℝ) < 1 / 2) :
    0 < pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω} ∧
      pr (enhRate p 0) {ω : G.edgeSet → Bool | Perc ω} = 0 := by
  refine ⟨(critical_curve_div s).2 p hp1, ?_⟩
  refine (critical_curve 0).1 p ?_
  have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  rw [h0]
  linarith

/-- At activation rate `1/2` the critical base rate is exactly `1/8`. -/
theorem critBase_half : critBase (1 / 2) = 1 / 8 := by
  rw [critBase]; norm_num

/-- The paper's point `(3/10, 1/2)` lies strictly above the exact critical curve, hence
percolates; this regenerates the previously known strict shift from the exact criterion. -/
theorem percolation_at_paper_point :
    0 < pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} := by
  refine percolation_pos_of_one_lt _ ?_
  rw [enhRate_zero, enhRate_one]
  have hp : (p0 : ℝ) = 3 / 10 := rfl
  have hs : (s0 : ℝ) = 1 / 2 := rfl
  rw [hp, hs]; norm_num

/-- A genuinely new nonpercolation point: base rate `1/10` with activation `1/2`.  The naive
first-moment test fails here (`2 * (1/10) + 2 * (1/2) = 6/5 > 1` in the crude one-type bound),
and the sharp *base* theorem at activation zero says nothing about it; the two-class criterion
gives nonpercolation because `2/10 + 1/2 + 4/20 = 9/10 < 1`. -/
theorem no_percolation_at_tenth_half :
    pr (enhRate ⟨1 / 10, by norm_num⟩ ⟨1 / 2, by norm_num⟩)
      {ω : G.edgeSet → Bool | Perc ω} = 0 := by
  refine (critical_curve ⟨1 / 2, by norm_num⟩).1 ⟨1 / 10, by norm_num⟩ ?_
  norm_num

/-- Consistency with the previously proved sharp base threshold at activation zero. -/
theorem base_criterion_agrees (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) :
    (2 * (r 0 : ℝ) < 1 → pr r {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
      (1 < 2 * (r 0 : ℝ) → 0 < pr r {ω : G.edgeSet → Bool | Perc ω}) := by
  constructor
  · intro h
    exact percolation_zero_of_lt r (by rw [h1]; linarith)
  · intro h
    exact percolation_pos_of_one_lt r (by rw [h1]; linarith)

/-! ### Activation monotonicity, essential enhancement and sharpness remarks -/

/-- The critical base rate is antitone in the activation rate. -/
theorem critBase_antitone {s s' : ℝ} (hs : 0 < 2 + 4 * s) (hss' : s ≤ s') :
    critBase s' ≤ critBase s := by
  have hs'pos : (0:ℝ) < 2 + 4 * s' := by linarith
  rw [critBase, critBase]
  refine (div_le_div_iff₀ hs'pos hs).mpr ?_
  nlinarith

/-- **The activation class is essential.**  For every positive activation rate the critical
base rate is strictly below the unactivated critical value `1/2`. -/
theorem critBase_essential (s : unitInterval) (hs : 0 < (s : ℝ)) :
    critBase (s : ℝ) < critBase 0 := by
  rw [critBase_zero]
  exact (critBase_strict_decrease (unitInterval.nonneg s) (unitInterval.le_one s) hs).1

/-- **Strict enhancement at a fixed base rate.**  For every positive activation rate there is a
base rate at which activation changes the qualitative outcome: the activated law percolates
while the unactivated law at the very same base rate does not. -/
theorem enhancement_strict_at_some_base (s : unitInterval) (hs : 0 < (s : ℝ)) :
    ∃ p : unitInterval, 0 < pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω} ∧
      pr (enhRate p 0) {ω : G.edgeSet → Bool | Perc ω} = 0 := by
  have hlt := critBase_essential s hs
  have hlt2 : critBase (s : ℝ) < 1 / 2 := by rw [← critBase_zero]; exact hlt
  have hb0 : 0 ≤ critBase (s : ℝ) := by
    rw [critBase]
    apply div_nonneg
    · have := unitInterval.le_one s; linarith
    · positivity
  have hb1 : critBase (s : ℝ) ≤ 1 := by
    rw [critBase]
    rw [div_le_one (by positivity : (0:ℝ) < 2 + 4 * (s : ℝ))]
    have := unitInterval.nonneg s
    linarith
  set p : ℝ := (critBase (s : ℝ) + 1 / 2) / 2 with hpdef
  have hpgt : critBase (s : ℝ) < p := by rw [hpdef]; linarith
  have hplt : p < 1 / 2 := by rw [hpdef]; linarith
  have hp0 : 0 ≤ p := by rw [hpdef]; linarith
  have hp1 : p ≤ 1 := by linarith
  exact ⟨⟨p, hp0, hp1⟩, (enhanced_window s ⟨p, hp0, hp1⟩ hpgt hplt).1,
    (enhanced_window s ⟨p, hp0, hp1⟩ hpgt hplt).2⟩

/-- **The one-type first-moment bound is not the criterion.**  At base rate `1/10` with
activation `1/2` the crude single-type bound gives `3b + 2s = 13/10 > 1` (so it cannot certify
nonpercolation), and yet the exact two-class criterion certifies nonpercolation because
`2b + s + 4bs = 9/10 < 1`.  Hence the two-class refinement in `bndSeq` is not cosmetic. -/
theorem naive_bound_insufficient :
    1 < 3 * ((1 / 10 : ℝ)) + 2 * ((1 / 2 : ℝ)) ∧
      pr (enhRate ⟨1 / 10, by norm_num⟩ ⟨1 / 2, by norm_num⟩)
        {ω : G.edgeSet → Bool | Perc ω} = 0 :=
  ⟨by norm_num, no_percolation_at_tenth_half⟩

/-- The exact critical base rate at activation `1/2` is `1/8`, and the paper's base rate `3/10`
lies strictly above it, while it is strictly below the unactivated threshold `1/2`. -/
theorem critical_comparison_at_half :
    critBase (1 / 2) = 1 / 8 ∧ (1 / 8 : ℝ) < 3 / 10 ∧ (3 / 10 : ℝ) < 1 / 2 := by
  refine ⟨critBase_half, by norm_num, by norm_num⟩


/-- The critical curve depends continuously on the activation rate on `[0, ∞)`. -/
theorem critBase_continuousOn : ContinuousOn critBase (Set.Ici (0:ℝ)) := by
  intro x hx
  have hx0 : (0:ℝ) ≤ x := hx
  have hden : (2 + 4 * x) ≠ 0 := by positivity
  unfold critBase
  exact ContinuousAt.continuousWithinAt
    (ContinuousAt.div (by fun_prop) (by fun_prop) hden)

/-- The phase boundary runs from `(0, 1/2)` to `(1, 0)`. -/
theorem critBase_endpoints : critBase 0 = 1 / 2 ∧ critBase 1 = 0 := by
  refine ⟨critBase_zero, ?_⟩
  rw [critBase]; norm_num

/-- At full activation the critical base rate is `0`: even a vanishing base rate percolates. -/
theorem percolation_at_full_activation (p : unitInterval) (hp : 0 < (p : ℝ)) :
    0 < pr (enhRate p 1) {ω : G.edgeSet → Bool | Perc ω} := by
  refine percolation_pos_of_one_lt _ ?_
  rw [enhRate_zero, enhRate_one]
  have hp1 : (p : ℝ) ≤ 1 := unitInterval.le_one p
  norm_num
  linarith


/-- **The Aizenman--Grimmett-style strict shift, exactly, in the tree class.**  For every
positive activation rate the *activated* two-rate law percolates at a base rate that is
strictly below `1/2`, the critical base rate of the unactivated law.  So in this model class
the AG reference input is a theorem with an exact critical curve, not a hypothesis. -/
theorem tree_reference_shift (s : unitInterval) (hs : 0 < (s : ℝ)) :
    ∃ p : unitInterval, 0 < (p : ℝ) ∧ (p : ℝ) < 1 / 2 ∧
      0 < pr (enhRate p s) {ω : G.edgeSet → Bool | Perc ω} := by
  have hlt : critBase (s : ℝ) < 1 / 2 := by
    rw [← critBase_zero]; exact critBase_essential s hs
  have hb0 : 0 ≤ critBase (s : ℝ) := by
    rw [critBase]
    apply div_nonneg
    · have := unitInterval.le_one s; linarith
    · positivity
  refine ⟨⟨(critBase (s : ℝ) + 1 / 2) / 2, by linarith, by linarith⟩, by linarith, by linarith, ?_⟩
  exact (critical_curve_div s).2 _ (by linarith)

/-! ### Class dependence of the forward-cluster probabilities -/

/-- A canonical vertex of each class. -/
def rep : Fin 2 → V
  | 0 => ⟨[Sum.inl 0], reduced_singleton _⟩
  | 1 => ⟨[Sum.inr 0], reduced_singleton _⟩

lemma vclass_rep (j : Fin 2) : VClass (rep j) j := by
  fin_cases j
  · exact ⟨Sum.inl 0, rfl, rfl⟩
  · exact ⟨Sum.inr 0, rfl, rfl⟩

/-- The exact count of valid letters does not depend on the vertex, only on its class. -/
lemma valid_class_card_eq {v v' : V} {c : Fin 2} (h : VClass v c) (h' : VClass v' c) (j : Fin 2) :
    (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = j)).card =
      (Finset.univ.filter (fun a : A => v'.Valid a ∧ acls a = j)).card := by
  have hj : j = 0 ∨ j = 1 := by omega
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hc with rfl | rfl
  · rcases hj with rfl | rfl
    · rw [valid_class_zero_card_zero h, valid_class_zero_card_zero h']
    · rw [valid_class_zero_card_one h, valid_class_zero_card_one h']
  · rcases hj with rfl | rfl
    · rw [valid_class_one_card_zero h, valid_class_one_card_zero h']
    · rw [valid_class_one_card_one h, valid_class_one_card_one h']

/-- The failure product at a vertex, with the child probabilities replaced by class values. -/
lemma prod_child (r : Fin 2 → unitInterval) (n : ℕ) (v : V) (q : Fin 2 → ℝ)
    (hq : ∀ (a : A) (h : v.Valid a), pr r {ω | Fwd ω (v.snoc a h) n} = q (acls a)) :
    ∏ a : A, (if h : v.Valid a then
        1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (v.snoc a h) n} else 1) =
      (1 - (r 0 : ℝ) * q 0) ^
          (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 0)).card *
        (1 - (r 1 : ℝ) * q 1) ^
          (Finset.univ.filter (fun a : A => v.Valid a ∧ acls a = 1)).card := by
  have hcongr : ∏ a : A, (if h : v.Valid a then
      1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (v.snoc a h) n} else 1) =
      ∏ a : A, (if h : v.Valid a then 1 - (r (acls a) : ℝ) * q (acls a) else 1) := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    by_cases hv : v.Valid a
    · rw [dif_pos hv, dif_pos hv, hq a hv]
    · rw [dif_neg hv, dif_neg hv]
  rw [hcongr]
  exact prod_if_valid v (fun j : Fin 2 => 1 - (r j : ℝ) * q j)

/-- **Class dependence of the level-`n` forward probabilities.** -/
theorem pr_fwd_class (r : Fin 2 → unitInterval) :
    ∀ (n : ℕ) (v v' : V) (c : Fin 2), VClass v c → VClass v' c →
      pr r {ω | Fwd ω v n} = pr r {ω | Fwd ω v' n} := by
  intro n
  induction n with
  | zero => intro v v' c _ _; rw [pr_fwd_zero, pr_fwd_zero]
  | succ n ih =>
    intro v v' c hv hv'
    have hcompl : ∀ u : V, pr r {ω | Fwd ω u (n + 1)} = 1 - pr r {ω | ¬ Fwd ω u (n + 1)} := by
      intro u
      have h := pr_compl_eq r {ω : G.edgeSet → Bool | Fwd ω u (n + 1)} (measurableSet_fwd u (n + 1))
      have hset : ({ω : G.edgeSet → Bool | Fwd ω u (n + 1)})ᶜ = {ω | ¬ Fwd ω u (n + 1)} := rfl
      rw [hset] at h; linarith
    have hqv : ∀ (a : A) (h : v.Valid a),
        pr r {ω | Fwd ω (v.snoc a h) n} =
          (fun j : Fin 2 => pr r {ω | Fwd ω (rep j) n}) (acls a) := by
      intro a h
      exact ih (v.snoc a h) (rep (acls a)) (acls a) (vclass_snoc v a h) (vclass_rep (acls a))
    have hqv' : ∀ (a : A) (h : v'.Valid a),
        pr r {ω | Fwd ω (v'.snoc a h) n} =
          (fun j : Fin 2 => pr r {ω | Fwd ω (rep j) n}) (acls a) := by
      intro a h
      exact ih (v'.snoc a h) (rep (acls a)) (acls a) (vclass_snoc v' a h) (vclass_rep (acls a))
    rw [hcompl v, hcompl v', measure_notFwd_succ, measure_notFwd_succ,
      prod_child r n v (fun j : Fin 2 => pr r {ω | Fwd ω (rep j) n}) hqv,
      prod_child r n v' (fun j : Fin 2 => pr r {ω | Fwd ω (rep j) n}) hqv']
    rw [valid_class_card_eq hv hv' (0 : Fin 2), valid_class_card_eq hv hv' (1 : Fin 2)]

/-! ### Class dependence of the cluster probabilities and the exact fixed-point equation -/

/-- Class dependence of the infinite forward-cluster probabilities. -/
theorem pr_cluster_class (r : Fin 2 → unitInterval) (v v' : V) (c : Fin 2)
    (h : VClass v c) (h' : VClass v' c) :
    pr r {ω | Cluster ω v} = pr r {ω | Cluster ω v'} := by
  have h1 := pr_cluster_tendsto r v
  have h2 := pr_cluster_tendsto r v'
  have hfun : (fun n => pr r {ω | Fwd ω v n}) = (fun n => pr r {ω | Fwd ω v' n}) := by
    funext n; exact pr_fwd_class r n v v' c h h'
  rw [hfun] at h1
  exact tendsto_nhds_unique h1 h2

/-- The product of the failure factors over the valid letters, as a limit statement. -/
lemma tendsto_prod_valid (r : Fin 2 → unitInterval) (u : V) :
    Tendsto (fun n => ∏ a ∈ (Finset.univ.filter (fun a : A => u.Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n})) atTop
      (𝓝 (∏ a ∈ (Finset.univ.filter (fun a : A => u.Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Cluster ω (childOf u a)}))) :=
  tendsto_finset_prod _ (fun a _ =>
    ((pr_cluster_tendsto r (childOf u a)).const_mul _).const_sub 1)

/-- **The exact fixed-point equation for the forward-cluster probability.** -/
theorem cluster_fixed (r : Fin 2 → unitInterval) (u : V) :
    pr r {ω | Cluster ω u} =
      1 - ∏ a ∈ (Finset.univ.filter (fun a : A => u.Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Cluster ω (childOf u a)}) := by
  classical
  have hlim := tendsto_prod_valid r u
  have hshift : Tendsto (fun n => pr r {ω | Fwd ω u (n + 1)}) atTop
      (𝓝 (pr r {ω | Cluster ω u})) :=
    (pr_cluster_tendsto r u).comp (tendsto_add_atTop_nat 1)
  have hstep : (fun n => pr r {ω | Fwd ω u (n + 1)}) =
      fun n => 1 - ∏ a ∈ (Finset.univ.filter (fun a : A => u.Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n}) := by
    funext n
    have hcompl : pr r {ω | Fwd ω u (n + 1)} = 1 - pr r {ω | ¬ Fwd ω u (n + 1)} := by
      have h := pr_compl_eq r {ω : G.edgeSet → Bool | Fwd ω u (n + 1)} (measurableSet_fwd u (n + 1))
      have hset : ({ω : G.edgeSet → Bool | Fwd ω u (n + 1)})ᶜ = {ω | ¬ Fwd ω u (n + 1)} := rfl
      rw [hset] at h; linarith
    rw [hcompl, measure_notFwd_succ]
    congr 1
    have hconv : (∏ a : A, (if h : u.Valid a then
        1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 1)) =
        ∏ a : A, (if h : u.Valid a then
          1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 1) := by
      refine Finset.prod_congr rfl (fun a _ => ?_)
      by_cases hv : u.Valid a
      · rw [dif_pos hv, dif_pos hv, childOf_eq hv]
      · rw [dif_neg hv, dif_neg hv]
    rw [hconv]
    exact (Finset.prod_filter (s := (Finset.univ : Finset A)) (p := fun a : A => u.Valid a)
      (f := fun a : A => 1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n})).symm
  rw [hstep] at hshift
  exact tendsto_nhds_unique hshift (tendsto_const_nhds.sub hlim)

/-- The fixed-point equation at a canonical vertex of class `c`, with the class values. -/
theorem cluster_fixed_rep (r : Fin 2 → unitInterval) (c : Fin 2) :
    pr r {ω | Cluster ω (rep c)} =
      1 - ∏ a ∈ (Finset.univ.filter (fun a : A => (rep c).Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Cluster ω (rep (acls a))}) := by
  rw [cluster_fixed]
  congr 1
  refine Finset.prod_congr rfl (fun a ha => ?_)
  have hv : (rep c).Valid a := (Finset.mem_filter.1 ha).2
  rw [pr_cluster_class r (childOf (rep c) a) (rep (acls a)) (acls a)]
  · rw [childOf_eq hv]
    exact vclass_snoc (rep c) a hv
  · exact vclass_rep (acls a)


/-! ### The critical case: the fixed-point equations have only the zero solution -/

/-- The class-`0` fixed-point equation at the canonical class-`0` vertex. -/
theorem cluster_fixed_zero (r : Fin 2 → unitInterval) :
    pr r {ω | Cluster ω (rep 0)} =
      1 - (1 - (r 0 : ℝ) * pr r {ω | Cluster ω (rep 0)}) ^ 2 *
        (1 - (r 1 : ℝ) * pr r {ω | Cluster ω (rep 1)}) ^ 2 := by
  have h := cluster_fixed_rep r 0
  have h2 := prod_class_const (Finset.univ.filter (fun a : A => (rep 0).Valid a))
    (fun j : Fin 2 => 1 - (r j : ℝ) * pr r {ω | Cluster ω (rep j)})
  have h1 : (∏ a ∈ (Finset.univ.filter (fun a : A => (rep 0).Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Cluster ω (rep (acls a))})) =
      ∏ a ∈ (Finset.univ.filter (fun a : A => (rep 0).Valid a)),
        (fun j : Fin 2 => 1 - (r j : ℝ) * pr r {ω | Cluster ω (rep j)}) (acls a) :=
    Finset.prod_congr rfl (fun a _ => rfl)
  rw [h1, h2] at h
  rw [Finset.filter_filter, Finset.filter_filter] at h
  rw [valid_class_zero_card_zero (vclass_rep 0), valid_class_zero_card_one (vclass_rep 0)] at h
  exact h

/-- The class-`1` fixed-point equation at the canonical class-`1` vertex. -/
theorem cluster_fixed_one (r : Fin 2 → unitInterval) :
    pr r {ω | Cluster ω (rep 1)} =
      1 - (1 - (r 0 : ℝ) * pr r {ω | Cluster ω (rep 0)}) ^ 3 *
        (1 - (r 1 : ℝ) * pr r {ω | Cluster ω (rep 1)}) := by
  have h := cluster_fixed_rep r 1
  have h2 := prod_class_const (Finset.univ.filter (fun a : A => (rep 1).Valid a))
    (fun j : Fin 2 => 1 - (r j : ℝ) * pr r {ω | Cluster ω (rep j)})
  have h1 : (∏ a ∈ (Finset.univ.filter (fun a : A => (rep 1).Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Cluster ω (rep (acls a))})) =
      ∏ a ∈ (Finset.univ.filter (fun a : A => (rep 1).Valid a)),
        (fun j : Fin 2 => 1 - (r j : ℝ) * pr r {ω | Cluster ω (rep j)}) (acls a) :=
    Finset.prod_congr rfl (fun a _ => rfl)
  rw [h1, h2] at h
  rw [Finset.filter_filter, Finset.filter_filter] at h
  rw [valid_class_one_card_zero (vclass_rep 1), valid_class_one_card_one (vclass_rep 1)] at h
  simpa using h


lemma perron_identity {b s x y u v : ℝ} (hu : u = b * x) (hv : v = s * y)
    (hD : 2 * b + s + 4 * b * s = 1) :
    (1 - s) * x + 2 * s * y = (1 - s) * (2 * u + 2 * v) + 2 * s * (3 * u + v) := by
  have key : (1 - s) * x + 2 * s * y - ((1 - s) * (2 * u + 2 * v) + 2 * s * (3 * u + v))
      = x * (1 - 2 * b - s - 4 * b * s) := by
    rw [hu, hv]; ring
  have h1 : 1 - 2 * b - s - 4 * b * s = 0 := by linarith
  have hzero : (1 - s) * x + 2 * s * y - ((1 - s) * (2 * u + 2 * v) + 2 * s * (3 * u + v)) = 0 := by
    rw [key, h1]; ring
  linarith [hzero]

lemma critical_sum {b s x y u v P R : ℝ} (hu : u = b * x) (hv : v = s * y)
    (hD : 2 * b + s + 4 * b * s = 1) (e0 : x = 1 - P) (e1 : y = 1 - R) :
    (1 - s) * (2 * (u + v) - (1 - P)) + 2 * s * ((3 * u + v) - (1 - R)) = 0 := by
  have hperron := perron_identity hu hv hD
  have h2 : (1 - s) * x + 2 * s * y = (1 - s) * (1 - P) + 2 * s * (1 - R) := by rw [e0, e1]
  linarith [hperron, h2]

lemma critical_remainder_zero {s Q0 Q1 : ℝ} (hs0 : 0 ≤ s) (hs : s < 1)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1)
    (hsum : (1 - s) * Q0 + 2 * s * Q1 = 0) : Q0 = 0 := by
  have h1 : (0:ℝ) ≤ (1 - s) * Q0 := mul_nonneg (by linarith) hQ0
  have h2 : (0:ℝ) ≤ 2 * s * Q1 := mul_nonneg (by linarith) hQ1
  have h3 : (1 - s) * Q0 = 0 := by linarith
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h (by linarith)
  · exact h

lemma Q0_factor {u v P : ℝ} (hP : P = (1 - u) ^ 2 * (1 - v) ^ 2) :
    2 * (u + v) - (1 - P) = (u + v - u * v) ^ 2 + 2 * u * v := by
  rw [hP]; ring

lemma Q1_factor {u v R : ℝ} (hR : R = (1 - u) ^ 3 * (1 - v)) :
    (3 * u + v) - (1 - R) = u * (v * (3 - 3 * u + u ^ 2) + (3 * u - u ^ 2)) := by
  rw [hR]; ring

/-- Step 1: on the critical curve the first second-order remainder vanishes. -/
lemma critical_remainder_vanishes {b s x y u v P R : ℝ}
    (hb : 0 < b) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hD : 2 * b + s + 4 * b * s = 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hu : u = b * x) (hv : v = s * y)
    (e0 : x = 1 - P) (e1 : y = 1 - R)
    (hP : P = (1 - u) ^ 2 * (1 - v) ^ 2) (hR : R = (1 - u) ^ 3 * (1 - v)) :
    2 * (u + v) - (1 - P) = 0 := by
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hu1 : u ≤ 1 := by rw [hu]; nlinarith
  have hv1 : v ≤ 1 := by rw [hv]; nlinarith
  have hslt : s < 1 := by
    rcases lt_or_eq_of_le hs1 with h | h
    · exact h
    · exfalso; rw [h] at hD; nlinarith
  have hsum := critical_sum hu hv hD e0 e1
  have hQ0 : 0 ≤ 2 * (u + v) - (1 - P) := by rw [Q0_factor hP]; positivity
  have hQ1 : 0 ≤ (3 * u + v) - (1 - R) := by
    rw [Q1_factor hR]
    have h3 : (0:ℝ) ≤ 3 - 3 * u + u ^ 2 := by nlinarith [sq_nonneg (u - 3 / 2)]
    have h5 : (0:ℝ) ≤ v * (3 - 3 * u + u ^ 2) := mul_nonneg hv0 h3
    have h4 : (0:ℝ) ≤ 3 * u - u ^ 2 := by nlinarith
    exact mul_nonneg hu0 (by linarith)
  exact critical_remainder_zero hs0 hslt hQ0 hQ1 hsum

/-- Step 2: the vanishing first remainder forces `u = v = 0`. -/
lemma critical_u_v_zero {u v P : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hP : P = (1 - u) ^ 2 * (1 - v) ^ 2) (hQ0 : 2 * (u + v) - (1 - P) = 0) :
    u = 0 ∧ v = 0 := by
  rw [Q0_factor hP] at hQ0
  have huv : u * v = 0 := by nlinarith [hQ0, mul_nonneg hu0 hv0]
  have hsum0 : u + v - u * v = 0 := by nlinarith [hQ0]
  have huzero : u = 0 := by nlinarith
  have hvzero : v = 0 := by nlinarith
  exact ⟨huzero, hvzero⟩

/-- (Pure algebra.)  At the critical parameters `2b + s + 4bs = 1` the two fixed-point
equations force the cluster probabilities to vanish. -/
lemma critical_fixed_zero (b s x y : ℝ) (hb : 0 < b) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hD : 2 * b + s + 4 * b * s = 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (e0 : x = 1 - (1 - b * x) ^ 2 * (1 - s * y) ^ 2)
    (e1 : y = 1 - (1 - b * x) ^ 3 * (1 - s * y)) :
    x = 0 ∧ y = 0 := by
  set P : ℝ := (1 - b * x) ^ 2 * (1 - s * y) ^ 2 with hP
  set R : ℝ := (1 - b * x) ^ 3 * (1 - s * y) with hR
  have e0' : x = 1 - P := e0
  have e1' : y = 1 - R := e1
  have hQ0 := critical_remainder_vanishes (b := b) (s := s) (x := x) (y := y)
    (u := b * x) (v := s * y) (P := P) (R := R) hb hs0 hs1 hD hx0 hx1 hy0 hy1
    rfl rfl e0' e1' hP hR
  have hu0 : 0 ≤ b * x := by positivity
  have hv0 : 0 ≤ s * y := by positivity
  have hP' : P = (1 - b * x) ^ 2 * (1 - s * y) ^ 2 := hP
  obtain ⟨huzero, hvzero⟩ := critical_u_v_zero (u := b * x) (v := s * y) (P := P) hu0 hv0 hP' hQ0
  have hx : x = 0 := by
    rcases mul_eq_zero.1 huzero with h | h
    · exact absurd h (ne_of_gt hb)
    · exact h
  have hR1 : R = 1 := by rw [hR, hx, hvzero]; norm_num
  have hy : y = 0 := by rw [e1', hR1]; ring
  exact ⟨hx, hy⟩

/-- **Nonpercolation at the critical curve.**  If `2b + s + 4bs = 1` and the base rate is
positive then the activated law does not percolate.  (The only critical boundary point with
`b = 0` is the degenerate corner `(0, 1)`, where every activation edge is open; it is not
covered by this argument.) -/
theorem percolation_zero_of_critical (r : Fin 2 → unitInterval)
    (hD : 2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) = 1)
    (hb : 0 < (r 0 : ℝ)) :
    pr r {ω : G.edgeSet → Bool | Perc ω} = 0 := by
  classical
  have hcrit := critical_fixed_zero (r 0 : ℝ) (r 1 : ℝ)
    (pr r {ω | Cluster ω (rep 0)}) (pr r {ω | Cluster ω (rep 1)})
    hb (unitInterval.nonneg _) (unitInterval.le_one _)
    hD (pr_nonneg r _) (pr_le_one r _) (pr_nonneg r _) (pr_le_one r _)
    (cluster_fixed_zero r) (cluster_fixed_one r)
  obtain ⟨h0, h1⟩ := hcrit
  have hclass : ∀ (v : V) (c : Fin 2), VClass v c → pr r {ω | Cluster ω v} = 0 := by
    intro v c hc
    have hEq := pr_cluster_class r v (rep c) c hc (vclass_rep c)
    rw [hEq]
    rcases (show c = 0 ∨ c = 1 from by omega) with rfl | rfl
    · exact h0
    · exact h1
  have hroot : pr r {ω | Cluster ω V.root} = 0 := by
    rw [cluster_fixed]
    have hprod : (∏ a ∈ (Finset.univ.filter (fun a : A => V.root.Valid a)),
        (1 - (r (acls a) : ℝ) * pr r {ω | Cluster ω (childOf V.root a)})) = 1 := by
      refine Finset.prod_eq_one (fun a ha => ?_)
      have hv : V.root.Valid a := (Finset.mem_filter.1 ha).2
      have hchild : pr r {ω | Cluster ω (childOf V.root a)} = 0 := by
        rw [childOf_eq hv]
        exact hclass _ (acls a) (vclass_snoc V.root a hv)
      rw [hchild, mul_zero, sub_zero]
    rw [hprod]; ring
  have hset : {ω : G.edgeSet → Bool | Perc ω} = ⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m} := by
    ext ω
    simp only [Perc, Set.mem_setOf_eq, Set.mem_iUnion]
    exact infinite_iff_exists_cluster ω
  rw [hset]
  have hmu : law r (⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m}) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_iUnion_le (fun m : V => {ω : G.edgeSet → Bool | Cluster ω m})) ?_
    have hz : ∀ m : V, law r {ω : G.edgeSet → Bool | Cluster ω m} = 0 := by
      intro m
      by_cases hne : m.w = []
      · have hm : m = V.root := V.ext hne
        subst hm
        exact measure_eq_zero_of_pr_eq_zero hroot
      · exact measure_eq_zero_of_pr_eq_zero
          (hclass m (acls (m.w.getLast hne)) ⟨m.w.getLast hne, List.getLast?_eq_some_getLast hne, rfl⟩)
    simp only [hz]
    simp
  rw [pr, measureReal_def, hmu, ENNReal.toReal_zero]

/-- **The complete two-rate criterion.**  Subcritical below `2b + s + 4bs = 1`, percolating
above it, and nonpercolating on the curve whenever the base rate is positive: the enhanced
critical curve `2b + s + 4bs = 1` is exact except at the degenerate corner `(b, s) = (0, 1)`. -/
theorem two_rate_criterion_full (r : Fin 2 → unitInterval) :
    (2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) < 1 →
        pr r {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
      (1 < 2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) →
        0 < pr r {ω : G.edgeSet → Bool | Perc ω}) ∧
      (2 * (r 0 : ℝ) + (r 1 : ℝ) + 4 * (r 0 : ℝ) * (r 1 : ℝ) = 1 → 0 < (r 0 : ℝ) →
        pr r {ω : G.edgeSet → Bool | Perc ω} = 0) :=
  ⟨percolation_zero_of_lt r, percolation_pos_of_one_lt r, percolation_zero_of_critical r⟩

end Ultra

#print axioms Ultra.two_rate_criterion
#print axioms Ultra.critical_curve
#print axioms Ultra.critical_curve_div
#print axioms Ultra.critBase_strict_decrease
#print axioms Ultra.critBase_essential
#print axioms Ultra.enhancement_strict_at_some_base
#print axioms Ultra.enhanced_window
#print axioms Ultra.no_percolation_at_tenth_half
#print axioms Ultra.naive_bound_insufficient
#print axioms Ultra.percolation_at_paper_point
#print axioms Ultra.critical_comparison_at_half
#print axioms Ultra.critBase_continuousOn
#print axioms Ultra.critBase_endpoints
#print axioms Ultra.percolation_at_full_activation
#print axioms Ultra.tree_reference_shift
#print axioms Ultra.cluster_fixed_zero
#print axioms Ultra.cluster_fixed_one
#print axioms Ultra.critical_fixed_zero
#print axioms Ultra.percolation_zero_of_critical
#print axioms Ultra.two_rate_criterion_full
