import FK.AGTree.Interface

/-!
# Base nonpercolation on the two-class tree

For the bond law of the two-class tree (`law r`: class-`0` edges open with probability `r 0`,
class-`1` edges with probability `r 1`) we prove that **no infinite open cluster exists** as
soon as the class-`1` rate vanishes and `3 * r 0 < 1`:

* `pr_fwd_le`: `pr{Fwd u n} ≤ (3 r₀)^n` from the exact branching recursion
  `measure_notFwd_succ` and the union (Boole) bound `1 - ∏(1-x) ≤ Σ x`, using that at most
  three of the five letters at any vertex are class `0`;
* `pr_cluster_zero`: hence every forward cluster has probability zero;
* `pr_percolation_zero`: by `infinite_iff_exists_cluster` and countability of the vertex
  type, the event that *some* infinite open cluster exists has probability zero.

At `r₀ = 3/10` this gives `3 r₀ = 9/10 < 1`, i.e. base nonpercolation, which
`TreeShift` compares with the activated percolation point.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-! ### The Boolean-union product bound -/

/-- A product of factors `1 - x i` with `x i ≥ 0` is at most one. -/
theorem prod_one_sub_le_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    ∏ i ∈ s, (1 - x i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha0 : 0 ≤ x a := h0 a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP0 : 0 ≤ ∏ i ∈ s, (1 - x i) :=
      Finset.prod_nonneg (fun i hi => by linarith [hs0 i hi, hs1 i hi])
    have hP1 := ih hs0 hs1
    rw [Finset.prod_insert ha]
    nlinarith

/-- For `x ∈ [0,1]`, `1 - ∏ (1 - x) ≤ ∑ x`. -/
theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∏ i ∈ s, (1 - x i) ≤ ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha0 : 0 ≤ x a := h0 a (Finset.mem_insert_self a s)
    have ha1 : x a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hs1 : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP0 : 0 ≤ ∏ i ∈ s, (1 - x i) :=
      Finset.prod_nonneg (fun i hi => by linarith [hs1 i hi])
    have hP1 : ∏ i ∈ s, (1 - x i) ≤ 1 := prod_one_sub_le_one s x hs0 hs1
    have hIH := ih hs0 hs1
    have hmul : x a * (∏ i ∈ s, (1 - x i)) ≤ x a := by
      calc x a * (∏ i ∈ s, (1 - x i)) ≤ x a * 1 :=
            mul_le_mul_of_nonneg_left hP1 ha0
        _ = x a := mul_one _
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    nlinarith [hIH, hmul]

/-! ### The one-step bound on forward clusters -/

/-- The failure bound for one step: writing `x a` for the weight-mass of the child `a`, the
probability that the forward cluster reaches one more level is at most `∑ x a`. -/
theorem pr_fwd_succ_le (r : Fin 2 → unitInterval) (u : V) (n : ℕ) :
    pr r {ω | Fwd ω u (n + 1)} ≤
      ∑ a : A, if h : u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0 := by
  classical
  have hcompl : pr r {ω | Fwd ω u (n + 1)} =
      1 - pr r {ω | ¬ Fwd ω u (n + 1)} := by
    have h := pr_compl_eq r {ω | Fwd ω u (n + 1)} (measurableSet_fwd u (n + 1))
    have hset : {ω : G.edgeSet → Bool | Fwd ω u (n + 1)}ᶜ = {ω | ¬ Fwd ω u (n + 1)} := rfl
    rw [hset] at h
    linarith
  rw [hcompl, measure_notFwd_succ]
  have hprod : (∏ a : A, if h : u.Valid a then
      1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 1) =
      ∏ a : A, (1 - (if h : u.Valid a then
        (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0)) := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    by_cases hv : u.Valid a
    · rw [dif_pos hv, dif_pos hv]
    · rw [dif_neg hv, dif_neg hv, sub_zero]
  rw [hprod]
  refine le_trans (one_sub_prod_le_sum Finset.univ
    (fun a => if h : u.Valid a then
      (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0)
    (fun a _ => ?_) (fun a _ => ?_))
    (le_of_eq (Finset.sum_congr rfl (fun a _ => rfl)))
  · by_cases hv : u.Valid a
    · rw [dif_pos hv]
      exact mul_nonneg (unitInterval.nonneg _) (pr_nonneg r _)
    · rw [dif_neg hv]
  · by_cases hv : u.Valid a
    · rw [dif_pos hv]
      have hr1 : (r (acls a) : ℝ) ≤ 1 := unitInterval.le_one _
      have hp1 : pr r {ω | Fwd ω (u.snoc a hv) n} ≤ 1 := pr_le_one r _
      have hp0 : 0 ≤ pr r {ω | Fwd ω (u.snoc a hv) n} := pr_nonneg r _
      nlinarith
    · rw [dif_neg hv]
      exact zero_le_one

/-- At most three of the five letters are both valid at `u` and of class `0`. -/
lemma card_valid_class_zero (u : V) :
    ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card ≤ 3 := by
  classical
  have hsub : (Finset.univ.filter (fun a : A => u.Valid a ∧ acls a = 0)) ⊆
      (Finset.univ.filter (fun a : A => acls a = 0)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.2
  have hcard := Finset.card_le_card hsub
  rwa [card_class (0 : Fin 2), dcount_zero] at hcard

/-- **Uniform forward-cluster bound.**  With no open class-`1` edges, the forward cluster
probability decays geometrically at rate `3 r₀`. -/
theorem pr_fwd_le (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) :
    ∀ (n : ℕ) (u : V), pr r {ω | Fwd ω u n} ≤ (3 * (r 0 : ℝ)) ^ n := by
  intro n
  induction n with
  | zero =>
    intro u
    rw [show {ω : G.edgeSet → Bool | Fwd ω u 0} = Set.univ from by
      ext ω; simp [fwd_zero], pr_univ]
    simp
  | succ n ih =>
    intro u
    have hstep := pr_fwd_succ_le r u n
    refine le_trans hstep ?_
    -- the sum over class-`0` letters only
    have hzero : ∀ a : A, acls a ≠ 0 →
        (if h : u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0) = 0 := by
      intro a ha
      by_cases hv : u.Valid a
      · rw [dif_pos hv]
        have hac : acls a = 1 := by
          apply Fin.ext
          have h2 : (acls a).val < 2 := (acls a).isLt
          have h3 : (acls a).val ≠ 0 := fun h0 => ha (Fin.ext (by rw [h0]; rfl))
          omega
        rw [hac, h1]
        simp
      · rw [dif_neg hv]
    have hsum_eq : ∑ a : A,
        (if h : u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0) =
        ∑ a ∈ Finset.univ.filter (fun a : A => acls a = 0),
          (if h : u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)).symm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact hzero a ha
    rw [hsum_eq]
    have hterm : ∀ a ∈ Finset.univ.filter (fun a : A => acls a = 0),
        (if h : u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 0) ≤
          (r 0 : ℝ) * (3 * (r 0 : ℝ)) ^ n := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      by_cases hv : u.Valid a
      · rw [dif_pos hv]
        have hac : acls a = 0 := ha
        rw [hac]
        exact mul_le_mul_of_nonneg_left (ih (u.snoc a hv)) (unitInterval.nonneg _)
      · rw [dif_neg hv]
        have hr0 : (0:ℝ) ≤ (r 0 : ℝ) := unitInterval.nonneg _
        have hp : (0:ℝ) ≤ (3 * (r 0 : ℝ)) ^ n := pow_nonneg (by linarith) n
        exact mul_nonneg hr0 hp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hcard : (Finset.univ.filter (fun a : A => acls a = 0)).card ≤ 3 := by
      rw [card_class (0 : Fin 2), dcount_zero]
    have hconst : ∑ a ∈ Finset.univ.filter (fun a : A => acls a = 0),
        ((r 0 : ℝ) * (3 * (r 0 : ℝ)) ^ n) =
        (((Finset.univ.filter (fun a : A => acls a = 0)).card : ℕ) : ℝ) *
          ((r 0 : ℝ) * (3 * (r 0 : ℝ)) ^ n) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hcardR : (((Finset.univ.filter (fun a : A => acls a = 0)).card : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast hcard
    have hmass : 0 ≤ (r 0 : ℝ) * (3 * (r 0 : ℝ)) ^ n :=
      mul_nonneg (unitInterval.nonneg _) (pow_nonneg (by linarith [unitInterval.nonneg (r 0)]) n)
    calc (((Finset.univ.filter (fun a : A => acls a = 0)).card : ℕ) : ℝ) *
          ((r 0 : ℝ) * (3 * (r 0 : ℝ)) ^ n)
        ≤ 3 * ((r 0 : ℝ) * (3 * (r 0 : ℝ)) ^ n) := by
          exact mul_le_mul_of_nonneg_right hcardR hmass
      _ = (3 * (r 0 : ℝ)) ^ (n + 1) := by ring

/-! ### Vanishing of the forward cluster -/

theorem pr_cluster_zero (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0)
    (hlt : 3 * (r 0 : ℝ) < 1) (u : V) : pr r {ω : G.edgeSet → Bool | Cluster ω u} = 0 := by
  refine le_antisymm ?_ (pr_nonneg r _)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
  have hmono : pr r {ω : G.edgeSet → Bool | Cluster ω u} ≤ pr r {ω | Fwd ω u n} :=
    pr_mono r (fun ω hω => hω n)
  have hb := pr_fwd_le r h1 n u
  linarith

/-- `pr`-zero sets are null for the underlying measure. -/
lemma measure_eq_zero_of_pr_eq_zero {r : Fin 2 → unitInterval} {A : Set (G.edgeSet → Bool)}
    (h : pr r A = 0) : law r A = 0 := by
  rw [pr, measureReal_def] at h
  rcases (ENNReal.toReal_eq_zero_iff _).1 h with h' | h'
  · exact h'
  · exact absurd h' (measure_ne_top (law r) A)

instance : Countable V :=
  Function.Injective.countable (f := fun v : V => v.w) (fun v w h => V.ext h)

/-- **Base nonpercolation.**  If the class-`1` rate vanishes and `3 r₀ < 1`, then almost
surely every open cluster is finite; in particular there is no infinite open cluster. -/
theorem pr_percolation_zero (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0)
    (hlt : 3 * (r 0 : ℝ) < 1) :
    pr r {ω : G.edgeSet → Bool | ∃ u : V, InfiniteClusterAt ω u} = 0 := by
  classical
  have hset : {ω : G.edgeSet → Bool | ∃ u : V, InfiniteClusterAt ω u} =
      ⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact infinite_iff_exists_cluster ω
  rw [hset]
  have hmu : law r (⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m}) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_iUnion_le (fun m : V => {ω : G.edgeSet → Bool | Cluster ω m})) ?_
    have hz : ∀ m : V, law r {ω : G.edgeSet → Bool | Cluster ω m} = 0 :=
      fun m => measure_eq_zero_of_pr_eq_zero (pr_cluster_zero r h1 hlt m)
    simp only [hz]
    simp
  rw [pr, measureReal_def, hmu, ENNReal.toReal_zero]

/-- Almost surely all open clusters are finite. -/
theorem ae_finite_clusters (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0)
    (hlt : 3 * (r 0 : ℝ) < 1) :
    ∀ᵐ ω ∂(law r), ∀ u : V, FiniteClusterAt ω u := by
  rw [MeasureTheory.ae_iff]
  have hset : {ω : G.edgeSet → Bool | ¬ ∀ u : V, FiniteClusterAt ω u} =
      {ω : G.edgeSet → Bool | ∃ u : V, InfiniteClusterAt ω u} := by
    ext ω
    simp only [Set.mem_setOf_eq, not_forall]
    rfl
  rw [hset]
  exact measure_eq_zero_of_pr_eq_zero (pr_percolation_zero r h1 hlt)

end Ultra
