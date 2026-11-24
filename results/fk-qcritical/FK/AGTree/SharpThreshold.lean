import FK.AGTree.ShiftThreshold

/-!
# The exact critical value `1/2` of the base two-class tree

For the base law (`r 1 = 0`) the forward cluster of a vertex of class `0` branches only along
class-`0` letters, of which exactly `2` are valid (the third one is the vertex's own last
letter); hence the effective branching factor is `2 r₀` rather than `5 r₀`.  This file makes
that count exact:

* `pr_fwd_le_two`: `pr{Fwd u (n+1)} ≤ 3 r₀ (2 r₀)^n` and `pr{Fwd v n} ≤ (2 r₀)^n` for
  class-`0` vertices `v`;
* `pr_percolation_zero_of_two_mul_lt_one`: no infinite open cluster for `2 r₀ < 1`;
* `pr_cluster_pos_of_one_lt_two_mul`: for `1 < 2 r₀` the forward cluster of every vertex has
  positive probability, from the fixed-point estimate `(1 - r₀ ε)² ≤ 1 - ε` for
  `ε = (2 r₀ - 1) / (2 r₀²)`.

Together these give the exact critical value `r₀ = 1/2` of the base law.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-! ### The class of a vertex -/

/-- `v` ends in a letter of class `0`. -/
def ClassZero (v : V) : Prop := ∃ a : A, v.w.getLast? = some a ∧ acls a = 0

lemma classZero_snoc {v : V} {b : A} (h : v.Valid b) (hb : acls b = 0) :
    ClassZero (v.snoc b h) := ⟨b, V.getLast?_snoc v b h, hb⟩

lemma classZero_ne_nil {v : V} (h : ClassZero v) : v.w ≠ [] := by
  obtain ⟨a, ha, _⟩ := h
  intro h0
  rw [h0] at ha
  simp at ha

lemma classZero_last {v : V} (h : ClassZero v) (hv : v.w ≠ []) : acls (v.w.getLast hv) = 0 := by
  obtain ⟨a, ha, hc⟩ := h
  have h1 : a = v.w.getLast hv := by
    rw [List.getLast?_eq_some_getLast hv] at ha
    exact (Option.some.inj ha).symm
  rw [← h1]
  exact hc

/-- At a vertex of class `0` at most two letters are both valid and of class `0`. -/
lemma card_classZero_le_two {v : V} (h : ClassZero v) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = 0)).card ≤ 2 := by
  have hv := classZero_ne_nil h
  have hc := card_valid_class (v := v) hv (0 : Fin 2)
  rw [classZero_last h hv] at hc
  rw [hc, dcount_zero]
  simp

/-- The child of `u` along the letter `a`; the junk value at invalid letters is `u`. -/
noncomputable def childOf (u : V) (a : A) : V := if h : u.Valid a then u.snoc a h else u

lemma childOf_eq {u : V} {a : A} (h : u.Valid a) : childOf u a = u.snoc a h := by
  rw [childOf, dif_pos h]

lemma classZero_childOf {u : V} {a : A} (h : u.Valid a) (ha : acls a = 0) :
    ClassZero (childOf u a) := by
  rw [childOf_eq h]
  exact classZero_snoc h ha

/-- The branching recursion with `childOf`. -/
theorem pr_fwd_succ_le_childOf (r : Fin 2 → unitInterval) (u : V) (n : ℕ) :
    pr r {ω | Fwd ω u (n + 1)} ≤
      ∑ a : A, if u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 0 := by
  refine le_trans (pr_fwd_succ_le r u n) (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hv : u.Valid a
  · rw [if_pos hv, dif_pos hv, childOf_eq hv]
  · rw [if_neg hv, dif_neg hv]

/-- Only class-`0` letters contribute when the class-`1` rate vanishes. -/
theorem pr_fwd_succ_le_filter (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) (u : V) (n : ℕ) :
    pr r {ω | Fwd ω u (n + 1)} ≤
      ∑ a ∈ (Finset.univ : Finset A).filter (fun a => acls a = 0),
        if u.Valid a then (r 0 : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 0 := by
  classical
  refine le_trans (pr_fwd_succ_le_childOf r u n) ?_
  have hzero : ∀ a : A, acls a ≠ 0 →
      (if u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 0) = 0 := by
    intro a ha
    by_cases hv : u.Valid a
    · rw [if_pos hv]
      have hac : acls a = 1 := by
        apply Fin.ext
        have h2 : (acls a).val < 2 := (acls a).isLt
        have h3 : (acls a).val ≠ 0 := fun h0 => ha (Fin.ext (by rw [h0]; rfl))
        omega
      rw [hac, h1]
      simp
    · rw [if_neg hv]
  have heq : (∑ a : A,
        if u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 0) =
      ∑ a ∈ (Finset.univ : Finset A).filter (fun a => acls a = 0),
        (if u.Valid a then (r (acls a) : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 0) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact hzero a ha
  rw [heq]
  refine Finset.sum_le_sum (fun a ha => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  have hac : acls a = 0 := ha
  by_cases hv : u.Valid a
  · rw [if_pos hv, if_pos hv, hac]
  · rw [if_neg hv, if_neg hv]

/-- A finite sum bounded by `card * X`. -/
lemma sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ) (X : ℝ) (hf : ∀ i ∈ s, f i ≤ X) :
    ∑ i ∈ s, f i ≤ s.card * X := by
  calc ∑ i ∈ s, f i ≤ ∑ _i ∈ s, X := Finset.sum_le_sum hf
    _ = s.card * X := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The class-`0` part of the branching recursion is bounded by `card * (r₀ * X₀)`. -/
lemma filter_sum_le {r : Fin 2 → unitInterval} {u : V} {n : ℕ} {X₀ : ℝ}
    (hX₀ : 0 ≤ X₀) (hρ : 0 ≤ (r 0 : ℝ))
    (hchild : ∀ a : A, acls a = 0 → ∀ h : u.Valid a,
      pr r {ω | Fwd ω (u.snoc a h) n} ≤ X₀) :
    (∑ a ∈ (Finset.univ : Finset A).filter (fun a => acls a = 0),
        if u.Valid a then (r 0 : ℝ) * pr r {ω | Fwd ω (childOf u a) n} else 0) ≤
      (((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card : ℕ) *
        ((r 0 : ℝ) * X₀) := by
  classical
  rw [← Finset.sum_filter]
  have hset : ((Finset.univ : Finset A).filter (fun a => acls a = 0)).filter (fun a => u.Valid a) =
      (Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  refine sum_le_card_mul _ _ _ (fun a ha => ?_)
  have hmem := Finset.mem_filter.1 ha
  obtain ⟨hval, hac⟩ := hmem.2
  refine mul_le_mul_of_nonneg_left ?_ hρ
  rw [childOf_eq hval]
  exact hchild a hac hval

/-! ### Sharp nonpercolation for `2 r₀ < 1` -/

theorem pr_fwd_le_two (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) :
    ∀ n : ℕ, (∀ v : V, ClassZero v → pr r {ω | Fwd ω v n} ≤ (2 * (r 0 : ℝ)) ^ n) ∧
      (∀ u : V, pr r {ω | Fwd ω u (n + 1)} ≤ 3 * (r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ n) := by
  intro n
  have hρ0 : (0:ℝ) ≤ (r 0 : ℝ) := unitInterval.nonneg _
  induction n with
  | zero =>
    constructor
    · intro v _
      rw [show {ω : G.edgeSet → Bool | Fwd ω v 0} = Set.univ from by
        ext ω; simp [fwd_zero], pr_univ]
      norm_num
    · intro u
      refine le_trans (pr_fwd_succ_le_filter r h1 u 0) ?_
      have hb := filter_sum_le (r := r) (u := u) (n := 0) (X₀ := 1) (by norm_num) hρ0
        (fun a _ h => by
          rw [show {ω : G.edgeSet → Bool | Fwd ω (u.snoc a h) 0} = Set.univ from by
            ext ω; simp [fwd_zero], pr_univ])
      have hcard : ((((Finset.univ : Finset A).filter
          (fun a => u.Valid a ∧ acls a = 0)).card : ℕ) : ℝ) ≤ 3 := by
        have h2 : ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card ≤ 3 := by
          have h3 : ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card ≤
              ((Finset.univ : Finset A).filter (fun a => acls a = 0)).card := by
            refine Finset.card_le_card ?_
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
            exact ha.2
          have h4 : ((Finset.univ : Finset A).filter (fun a => acls a = 0)).card = 3 := by
            rw [card_class (0 : Fin 2), dcount_zero]
          omega
        exact_mod_cast h2
      refine le_trans hb ?_
      have hmass : (0:ℝ) ≤ (r 0 : ℝ) * 1 := by linarith
      calc ((((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card : ℕ) : ℝ) *
            ((r 0 : ℝ) * 1)
          ≤ 3 * ((r 0 : ℝ) * 1) := mul_le_mul_of_nonneg_right hcard hmass
        _ = 3 * (r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ 0 := by ring
  | succ n ih =>
    obtain ⟨ihA, _⟩ := ih
    have hA : ∀ v : V, ClassZero v →
        pr r {ω | Fwd ω v (n + 1)} ≤ (2 * (r 0 : ℝ)) ^ (n + 1) := by
      intro v hv
      refine le_trans (pr_fwd_succ_le_filter r h1 v n) ?_
      have hb := filter_sum_le (r := r) (u := v) (n := n) (X₀ := (2 * (r 0 : ℝ)) ^ n)
        (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * (r 0 : ℝ)) n) hρ0
        (fun a ha h => by
          rw [← childOf_eq h]
          exact ihA _ (classZero_childOf h ha))
      have hcard : ((((Finset.univ : Finset A).filter
          (fun a => v.Valid a ∧ acls a = 0)).card : ℕ) : ℝ) ≤ 2 := by
        have h2 := card_classZero_le_two hv
        exact_mod_cast h2
      refine le_trans hb ?_
      have hmass : (0:ℝ) ≤ (r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ n :=
        mul_nonneg hρ0 (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * (r 0 : ℝ)) n)
      calc ((((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = 0)).card : ℕ) : ℝ) *
            ((r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ n)
          ≤ 2 * ((r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ n) :=
            mul_le_mul_of_nonneg_right hcard hmass
        _ = (2 * (r 0 : ℝ)) ^ (n + 1) := by ring
    refine ⟨hA, fun u => ?_⟩
    refine le_trans (pr_fwd_succ_le_filter r h1 u (n + 1)) ?_
    have hb := filter_sum_le (r := r) (u := u) (n := n + 1) (X₀ := (2 * (r 0 : ℝ)) ^ (n + 1))
      (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * (r 0 : ℝ)) (n + 1)) hρ0
      (fun a ha h => by
        rw [← childOf_eq h]
        exact hA _ (classZero_childOf h ha))
    have hcard : ((((Finset.univ : Finset A).filter
        (fun a => u.Valid a ∧ acls a = 0)).card : ℕ) : ℝ) ≤ 3 := by
      have h2 : ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card ≤ 3 := by
        have h3 : ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card ≤
            ((Finset.univ : Finset A).filter (fun a => acls a = 0)).card := by
          refine Finset.card_le_card ?_
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact ha.2
        have h4 : ((Finset.univ : Finset A).filter (fun a => acls a = 0)).card = 3 := by
          rw [card_class (0 : Fin 2), dcount_zero]
        omega
      exact_mod_cast h2
    refine le_trans hb ?_
    have hmass : (0:ℝ) ≤ (r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ (n + 1) :=
      mul_nonneg hρ0 (pow_nonneg (by linarith : (0:ℝ) ≤ 2 * (r 0 : ℝ)) (n + 1))
    calc ((((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card : ℕ) : ℝ) *
          ((r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ (n + 1))
        ≤ 3 * ((r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right hcard hmass
      _ = 3 * (r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ (n + 1) := by ring

theorem pr_fwd_le_two_root (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) (n : ℕ) (u : V) :
    pr r {ω | Fwd ω u n} ≤ 3 * (2 * (r 0 : ℝ)) ^ n := by
  match n with
  | 0 =>
    rw [show {ω : G.edgeSet → Bool | Fwd ω u 0} = Set.univ from by
      ext ω; simp [fwd_zero], pr_univ]
    norm_num
  | (k + 1) =>
    have hb := ((pr_fwd_le_two r h1) k).2 u
    refine le_trans hb ?_
    have hρ : (0:ℝ) ≤ (r 0 : ℝ) := unitInterval.nonneg _
    have h2 : (0:ℝ) ≤ 2 * (r 0 : ℝ) := by linarith
    have hX : (0:ℝ) ≤ 3 * (2 * (r 0 : ℝ)) ^ k := by positivity
    calc 3 * (r 0 : ℝ) * (2 * (r 0 : ℝ)) ^ k
        = (3 * (2 * (r 0 : ℝ)) ^ k) * (r 0 : ℝ) := by ring
      _ ≤ (3 * (2 * (r 0 : ℝ)) ^ k) * (2 * (r 0 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hX
      _ = 3 * (2 * (r 0 : ℝ)) ^ (k + 1) := by rw [pow_succ]; ring

/-- **Sharp base nonpercolation**: for `2 r₀ < 1` no infinite open cluster exists. -/
theorem pr_percolation_zero_of_two_mul_lt_one (r : Fin 2 → unitInterval)
    (h1 : (r 1 : ℝ) = 0) (hlt : 2 * (r 0 : ℝ) < 1) :
    pr r {ω : G.edgeSet → Bool | Perc ω} = 0 := by
  classical
  have hcluster : ∀ u : V, pr r {ω : G.edgeSet → Bool | Cluster ω u} = 0 := by
    intro u
    refine le_antisymm ?_ (pr_nonneg r _)
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by linarith : (0:ℝ) < ε / 3) hlt
    have hmono : pr r {ω : G.edgeSet → Bool | Cluster ω u} ≤ pr r {ω | Fwd ω u n} :=
      pr_mono r (fun ω hω => hω n)
    have hb := pr_fwd_le_two_root r h1 n u
    have h3 : 3 * (2 * (r 0 : ℝ)) ^ n < ε := by linarith
    linarith
  have hset : {ω : G.edgeSet → Bool | Perc ω} = ⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m} := by
    ext ω
    simp only [Perc, Set.mem_setOf_eq, Set.mem_iUnion]
    exact infinite_iff_exists_cluster ω
  rw [hset]
  have hmu : law r (⋃ m : V, {ω : G.edgeSet → Bool | Cluster ω m}) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_iUnion_le (fun m : V => {ω : G.edgeSet → Bool | Cluster ω m})) ?_
    have hz : ∀ m : V, law r {ω : G.edgeSet → Bool | Cluster ω m} = 0 :=
      fun m => measure_eq_zero_of_pr_eq_zero (hcluster m)
    simp only [hz]
    simp
  rw [pr, measureReal_def, hmu, ENNReal.toReal_zero]



/-! ### Percolation for `1 < 2 r₀` and the exact critical value -/

/-- A product comparison for nonnegative factors. -/
theorem prod_le_prod_of_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hle : ∀ i ∈ s, f i ≤ g i) (hg0 : ∀ i ∈ s, 0 ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hfa : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
    have hga : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
    have hle' : ∀ i ∈ s, f i ≤ g i := fun i hi => hle i (Finset.mem_insert_of_mem hi)
    have hPf : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hfs
    have hPg : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg hgs
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : f a * ∏ i ∈ s, f i ≤ g a * ∏ i ∈ s, f i :=
      mul_le_mul_of_nonneg_right (hle a (Finset.mem_insert_self a s)) hPf
    have h2 : g a * ∏ i ∈ s, f i ≤ g a * ∏ i ∈ s, g i :=
      mul_le_mul_of_nonneg_left (ih hfs hle' hgs) hga
    linarith

/-- The margin `ε = (2 r₀ - 1)/(2 r₀²)` at which the one-step map `1 - x ↦ (1 - r₀ x)²`
contracts below `1`. -/
noncomputable def epsOf (r : Fin 2 → unitInterval) : ℝ :=
  (2 * (r 0 : ℝ) - 1) / (2 * (r 0 : ℝ) ^ 2)

lemma epsOf_pos {r : Fin 2 → unitInterval} (hρ : 1 < 2 * (r 0 : ℝ)) : 0 < epsOf r := by
  have h2 : (0:ℝ) < 2 * (r 0 : ℝ) ^ 2 := by
    have : (0:ℝ) < (r 0 : ℝ) := by linarith
    positivity
  rw [epsOf]
  exact div_pos (by linarith) h2

lemma epsOf_le_one {r : Fin 2 → unitInterval} (hρ : 1 < 2 * (r 0 : ℝ)) : epsOf r ≤ 1 := by
  have h2 : (0:ℝ) < 2 * (r 0 : ℝ) ^ 2 := by
    have : (0:ℝ) < (r 0 : ℝ) := by linarith
    positivity
  rw [epsOf, div_le_one h2]
  nlinarith [sq_nonneg ((r 0 : ℝ) - 1/2)]

/-- The contraction inequality `(1 - r₀ ε)² ≤ 1 - ε`. -/
lemma epsOf_contract {r : Fin 2 → unitInterval} (hρ : 1 < 2 * (r 0 : ℝ)) :
    (1 - (r 0 : ℝ) * epsOf r) ^ 2 ≤ 1 - epsOf r := by
  have hρpos : (0:ℝ) < (r 0 : ℝ) := by linarith
  have h2 : (0:ℝ) < 2 * (r 0 : ℝ) ^ 2 := by positivity
  have hnum : (0:ℝ) < 2 * (r 0 : ℝ) - 1 := by linarith
  have key : (r 0 : ℝ) ^ 2 * epsOf r = (2 * (r 0 : ℝ) - 1) / 2 := by
    rw [epsOf]
    field_simp
  nlinarith [key, epsOf_pos hρ, hnum]

lemma epsOf_mul_le_one {r : Fin 2 → unitInterval} (hρ : 1 < 2 * (r 0 : ℝ)) :
    (r 0 : ℝ) * epsOf r ≤ 1 := by
  have hρpos : (0:ℝ) < (r 0 : ℝ) := by linarith
  have h2 : (0:ℝ) < 2 * (r 0 : ℝ) ^ 2 := by positivity
  have hnum : (0:ℝ) < 2 * (r 0 : ℝ) - 1 := by linarith
  have h1 : (r 0 : ℝ) * epsOf r = (2 * (r 0 : ℝ) - 1) / (2 * (r 0 : ℝ)) := by
    rw [epsOf]
    field_simp
  have h3 : (0:ℝ) < 2 * (r 0 : ℝ) := by linarith
  rw [h1, div_le_one h3]
  linarith

/-- At any vertex at least two letters are both valid and of class `0`. -/
lemma two_le_card_valid_class_zero (u : V) :
    2 ≤ ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card := by
  classical
  rcases eq_or_ne u.w [] with h0 | h0
  · have hu : u = V.root := V.ext h0
    subst hu
    have hset : ((Finset.univ : Finset A).filter (fun a => V.root.Valid a ∧ acls a = 0)) =
        (Finset.univ : Finset A).filter (fun a => acls a = 0) := by
      refine Finset.filter_congr (fun a _ => ?_)
      exact ⟨fun h => h.2, fun h => ⟨root_valid a, h⟩⟩
    rw [hset, card_class (0 : Fin 2), dcount_zero]
    norm_num
  · have hc := card_valid_class (v := u) h0 (0 : Fin 2)
    rw [hc, dcount_zero]
    split_ifs <;> norm_num

/-- One-step estimate: if the children reach level `n` with probability at least `ε`, then `u`
fails to reach level `n+1` with probability at most `(1 - r₀ ε)²`. -/
theorem pr_notFwd_succ_le (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : (r 0 : ℝ) * ε ≤ 1) (u : V) (n : ℕ)
    (hP : ∀ (a : A) (h : u.Valid a), acls a = 0 →
      ε ≤ pr r {ω | Fwd ω (u.snoc a h) n}) :
    pr r {ω | ¬ Fwd ω u (n + 1)} ≤ (1 - (r 0 : ℝ) * ε) ^ 2 := by
  classical
  have hρ0 : (0:ℝ) ≤ (r 0 : ℝ) := unitInterval.nonneg _
  rw [measure_notFwd_succ]
  have hf0 : ∀ a ∈ (Finset.univ : Finset A),
      0 ≤ (if h : u.Valid a then 1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 1) := by
    intro a _
    by_cases hv : u.Valid a
    · rw [dif_pos hv]
      have hr : (r (acls a) : ℝ) ≤ 1 := unitInterval.le_one _
      have hp : pr r {ω | Fwd ω (u.snoc a hv) n} ≤ 1 := pr_le_one r _
      have hp0 : 0 ≤ pr r {ω | Fwd ω (u.snoc a hv) n} := pr_nonneg r _
      nlinarith
    · rw [dif_neg hv]
      exact zero_le_one
  have hle : ∀ a ∈ (Finset.univ : Finset A),
      (if h : u.Valid a then 1 - (r (acls a) : ℝ) * pr r {ω | Fwd ω (u.snoc a h) n} else 1) ≤
        (if u.Valid a ∧ acls a = 0 then 1 - (r 0 : ℝ) * ε else 1) := by
    intro a _
    by_cases hv : u.Valid a
    · rw [dif_pos hv]
      by_cases hc : acls a = 0
      · rw [if_pos ⟨hv, hc⟩, hc]
        have hp := hP a hv hc
        have hmul : (r 0 : ℝ) * ε ≤ (r 0 : ℝ) * pr r {ω | Fwd ω (u.snoc a hv) n} :=
          mul_le_mul_of_nonneg_left hp hρ0
        linarith
      · have hc1 : acls a = 1 := by
          apply Fin.ext
          have h2 : (acls a).val < 2 := (acls a).isLt
          have h3 : (acls a).val ≠ 0 := fun h0 => hc (Fin.ext (by rw [h0]; rfl))
          omega
        rw [if_neg (fun h => hc h.2), hc1, h1]
        simp
    · rw [dif_neg hv]
      rw [if_neg (fun h => hv h.1)]
  have hg0 : ∀ a ∈ (Finset.univ : Finset A),
      0 ≤ (if u.Valid a ∧ acls a = 0 then 1 - (r 0 : ℝ) * ε else 1) := by
    intro a _
    by_cases h : u.Valid a ∧ acls a = 0
    · rw [if_pos h]; linarith
    · rw [if_neg h]
      exact zero_le_one
  have hprod := prod_le_prod_of_le (Finset.univ : Finset A) _ _ hf0 hle hg0
  refine le_trans hprod ?_
  have hpow := prod_ite_pow (fun a : A => u.Valid a ∧ acls a = 0) (1 - (r 0 : ℝ) * ε)
  rw [hpow]
  have hk : 2 ≤ ((Finset.univ : Finset A).filter (fun a => u.Valid a ∧ acls a = 0)).card :=
    two_le_card_valid_class_zero u
  have h1' : (0:ℝ) ≤ 1 - (r 0 : ℝ) * ε := by linarith
  have h2' : 1 - (r 0 : ℝ) * ε ≤ 1 := by
    have := mul_nonneg hρ0 hε0
    linarith
  exact pow_le_pow_of_le_one h1' h2' hk

/-- **Percolation for `1 < 2 r₀`.**  Every vertex lies in an infinite forward cluster with
probability at least `ε = (2 r₀ - 1)/(2 r₀²)`. -/
theorem pr_fwd_ge_eps (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0)
    (hρ : 1 < 2 * (r 0 : ℝ)) :
    ∀ (n : ℕ) (u : V), epsOf r ≤ pr r {ω | Fwd ω u n} := by
  intro n
  induction n with
  | zero => intro u; rw [pr_fwd_zero]; exact epsOf_le_one hρ
  | succ n ih =>
    intro u
    have hcompl := pr_compl_eq r {ω : G.edgeSet → Bool | Fwd ω u (n + 1)}
      (measurableSet_fwd u (n + 1))
    have hset : ({ω : G.edgeSet → Bool | Fwd ω u (n + 1)})ᶜ = {ω | ¬ Fwd ω u (n + 1)} := rfl
    rw [hset] at hcompl
    have hupper := pr_notFwd_succ_le r h1 (le_of_lt (epsOf_pos hρ)) (epsOf_mul_le_one hρ) u n
      (fun a h ha => ih (u.snoc a h))
    have hcontr := epsOf_contract hρ
    linarith

/-- **Percolation for `1 < 2 r₀`**: the root cluster has positive probability. -/
theorem pr_cluster_pos_of_one_lt_two_mul (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0)
    (hρ : 1 < 2 * (r 0 : ℝ)) (u : V) : 0 < pr r {ω : G.edgeSet → Bool | Cluster ω u} := by
  have htend := pr_cluster_tendsto r u
  have hlim : epsOf r ≤ pr r {ω | Cluster ω u} := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
    filter_upwards with n
    exact pr_fwd_ge_eps r h1 hρ n u
  linarith [epsOf_pos hρ]

/-- **The exact critical value of the base two-class tree.**  For the law with no open
class-`1` edges the percolation probability vanishes for `2 r₀ < 1` and is positive for
`1 < 2 r₀`. -/
theorem base_critical_one_half (r : Fin 2 → unitInterval) (h1 : (r 1 : ℝ) = 0) :
    (2 * (r 0 : ℝ) < 1 → pr r {ω : G.edgeSet → Bool | Perc ω} = 0) ∧
      (1 < 2 * (r 0 : ℝ) → 0 < pr r {ω : G.edgeSet → Bool | Perc ω}) := by
  constructor
  · intro hlt
    exact pr_percolation_zero_of_two_mul_lt_one r h1 hlt
  · intro hgt
    have hpos := pr_cluster_pos_of_one_lt_two_mul r h1 hgt V.root
    have hmono : pr r {ω : G.edgeSet → Bool | Cluster ω V.root} ≤
        pr r {ω : G.edgeSet → Bool | Perc ω} :=
      pr_mono r (fun ω hω => ⟨V.root, cluster_infinite hω⟩)
    linarith

end Ultra
