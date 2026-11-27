import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Set
open scoped BigOperators

namespace LatticeBoxes

variable {d : ℕ}

abbrev V (d : ℕ) := Fin d → ℤ

/-- Translation of one lattice coordinate by an integer. -/
def shift (x : V d) (i : Fin d) (a : ℤ) : V d := Function.update x i (x i + a)

lemma shift_apply_same (x : V d) (i : Fin d) (a : ℤ) : shift x i a i = x i + a := by
  simp [shift]

lemma shift_apply_ne (x : V d) {i j : Fin d} (h : j ≠ i) (a : ℤ) :
    shift x i a j = x j := by simp [shift, h]

lemma shift_shift_comm (x : V d) {i j : Fin d} (h : i ≠ j) (a b : ℤ) :
    shift (shift x i a) j b = shift (shift x j b) i a := by
  funext k
  by_cases hki : k = i
  · subst k; simp [shift, Function.update_apply, h]
  · by_cases hkj : k = j
    · subst k; simp [shift, hki]
    · simp [shift, hki, hkj]

lemma shift_zero (x : V d) (i : Fin d) : shift x i 0 = x := by
  funext j
  by_cases h : j = i
  · subst j; simp [shift]
  · simp [shift, h]

lemma shift_add (x : V d) (i : Fin d) (a b : ℤ) :
    shift (shift x i a) i b = shift x i (a + b) := by
  funext j
  by_cases h : j = i
  · subst j; simp [shift, add_assoc]
  · simp [shift, h]

/-- The usual nearest-neighbour lattice. -/
def lattice (d : ℕ) : SimpleGraph (V d) where
  Adj x y := ∃ i : Fin d, y = shift x i 1 ∨ y = shift x i (-1)
  symm := ⟨by
    rintro x y ⟨i, rfl | rfl⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [shift_add]
      simpa using (shift_zero x i).symm
    · refine ⟨i, Or.inl ?_⟩
      rw [shift_add]
      simpa using (shift_zero x i).symm⟩
  loopless := ⟨by
    rintro x ⟨i, h | h⟩
    · have hi := congrFun h i
      simp [shift] at hi
    · have hi := congrFun h i
      simp [shift] at hi⟩

lemma step_adj (x : V d) (i : Fin d) (a : ℤ) (ha : a = 1 ∨ a = -1) :
    (lattice d).Adj x (shift x i a) := by
  rcases ha with rfl | rfl
  · exact ⟨i, Or.inl rfl⟩
  · exact ⟨i, Or.inr rfl⟩

lemma step_adj_neg (x : V d) (i : Fin d) (a : ℤ) (ha : a = 1 ∨ a = -1) :
    (lattice d).Adj (shift x i a) x := (step_adj x i a ha).symm

/-- Vertices of the centered `ℓ∞` box. -/
def InBox (R : ℤ) (x : V d) : Prop := ∀ i, |x i| ≤ R

lemma inBox_of_between {R : ℤ} {x y w : V d} (hx : InBox R x) (hy : InBox R y)
    (i : Fin d) (a : ℤ)
    (hbetween : x i ≤ x i + a ∧ x i + a ≤ y i ∨ y i ≤ x i + a ∧ x i + a ≤ x i)
    (hother : ∀ j ≠ i, w j = x j) (hw : w i = x i + a) :
    InBox R w := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [hw, abs_le]
    have hx' := abs_le.mp (hx i)
    have hy' := abs_le.mp (hy i)
    omega
  · rw [hother j hji]
    exact hx j

lemma InBox.shift_toward {R : ℤ} {x y : V d} (hx : InBox R x) (hy : InBox R y)
    (i : Fin d) (a : ℤ)
    (hbetween : x i ≤ x i + a ∧ x i + a ≤ y i ∨ y i ≤ x i + a ∧ x i + a ≤ x i) :
    InBox R (shift x i a) := by
  apply inBox_of_between hx hy i a hbetween
  · intro j hji; exact shift_apply_ne x hji a
  · exact shift_apply_same x i a

/-- Taxicab distance, used only as an induction measure. -/
def dist (x y : V d) : ℕ := ∑ i : Fin d, (x i - y i).natAbs

lemma dist_eq_zero {x y : V d} (h : dist x y = 0) : x = y := by
  funext i
  have hz : ∀ j ∈ Finset.univ, (x j - y j).natAbs = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h
  have hi := hz i (Finset.mem_univ i)
  omega

lemma exists_coordinate_ne {x y : V d} (h : x ≠ y) : ∃ i, x i ≠ y i := by
  by_contra hn
  push Not at hn
  exact h (funext hn)

lemma dist_step_toward {x y : V d} (i : Fin d) (a : ℤ)
    (hdist : (x i + a - y i).natAbs + a.natAbs = (x i - y i).natAbs) :
    dist (shift x i a) y + a.natAbs = dist x y := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
  unfold dist
  rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add _ _ hi]
  have hs : (∑ j ∈ Finset.univ.erase i, (shift x i a j - y j).natAbs) =
      ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    simp [shift_apply_ne x hne a]
  rw [hs]
  have hv : shift x i a i = x i + a := shift_apply_same x i a
  rw [hv, Nat.add_assoc, hdist]

/-- The unit step pointing from `x i` toward `y i`; the nonzero case is the
only one in which it is used. -/
def toward (x y : V d) (i : Fin d) : ℤ := if x i < y i then 1 else -1

lemma toward_unit (x y : V d) (i : Fin d) : toward x y i = 1 ∨ toward x y i = -1 := by
  unfold toward; split_ifs <;> simp

lemma toward_ne_zero (x y : V d) (i : Fin d) : toward x y i ≠ 0 := by
  rcases toward_unit x y i with h | h <;> rw [h] <;> norm_num

lemma toward_between {x y : V d} (i : Fin d) (hne : x i ≠ y i) :
    x i ≤ x i + toward x y i ∧ x i + toward x y i ≤ y i ∨
      y i ≤ x i + toward x y i ∧ x i + toward x y i ≤ x i := by
  unfold toward
  split_ifs with h
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

lemma toward_dist_one {x y : V d} (i : Fin d) (hne : x i ≠ y i) :
    (x i + toward x y i - y i).natAbs + (toward x y i).natAbs =
      (x i - y i).natAbs := by
  unfold toward
  split_ifs with h <;> simp <;> omega

lemma toward_dist_two {x y : V d} (i : Fin d) (hne : x i ≠ y i)
    (htwo : 2 ≤ (x i - y i).natAbs) :
    (x i + toward x y i + toward x y i - y i).natAbs + 2 =
      (x i - y i).natAbs := by
  unfold toward
  split_ifs with h <;> omega

lemma dist_toward_one {x y : V d} (i : Fin d) (hne : x i ≠ y i) :
    dist (shift x i (toward x y i)) y + 1 = dist x y := by
  have h := toward_dist_one i hne
  have hn : (toward x y i).natAbs = 1 := by
    rcases toward_unit x y i with hu | hu <;> simp [hu]
  have hh := dist_step_toward i (toward x y i) h
  rwa [hn] at hh

lemma dist_toward_two {x y : V d} (i : Fin d) (hne : x i ≠ y i)
    (htwo : 2 ≤ (x i - y i).natAbs) :
    dist (shift (shift x i (toward x y i)) i (toward x y i)) y + 2 = dist x y := by
  have h := toward_dist_two i hne htwo
  rw [shift_add]
  have hn : (toward x y i + toward x y i).natAbs = 2 := by
    rcases toward_unit x y i with hu | hu <;> simp [hu]
  have hd : (x i + (toward x y i + toward x y i) - y i).natAbs +
      (toward x y i + toward x y i).natAbs = (x i - y i).natAbs := by
    rw [hn]
    convert h using 1 <;> ring
  have hh := dist_step_toward (x := x) (y := y) i (toward x y i + toward x y i) hd
  rwa [hn] at hh

lemma ne_shift_toward_of_coordinate_ne {x y z : V d} {i j : Fin d}
    (hji : j ≠ i) (a : ℤ) (hz : z = shift x i a) (hne : x j ≠ y j) :
    shift x j (toward x y j) ≠ z := by
  intro h
  have h' := congrFun (h.trans hz) j
  simp [shift, Function.update_apply, hji] at h'
  have ht := toward_ne_zero x y j
  omega

lemma toward_between_two {x y : V d} (i : Fin d) (hne : x i ≠ y i)
    (htwo : 2 ≤ (x i - y i).natAbs) :
    x i ≤ x i + toward x y i + toward x y i ∧
        x i + toward x y i + toward x y i ≤ y i ∨
      y i ≤ x i + toward x y i + toward x y i ∧
        x i + toward x y i + toward x y i ≤ x i := by
  unfold toward
  split_ifs with h <;> omega

/-- A second-coordinate sign pointing strictly inside the box. -/
def inward (R : ℤ) (z : V d) (j : Fin d) : ℤ := if z j < R then 1 else -1

lemma inward_unit (R : ℤ) (z : V d) (j : Fin d) : inward R z j = 1 ∨ inward R z j = -1 := by
  unfold inward; split_ifs <;> simp

lemma inward_ne_zero (R : ℤ) (z : V d) (j : Fin d) : inward R z j ≠ 0 := by
  rcases inward_unit R z j with h | h <;> rw [h] <;> norm_num

lemma inBox_shift_inward {R : ℤ} {z : V d} (hRpos : 1 ≤ R) (hz : InBox R z) (j : Fin d) :
    InBox R (shift z j (inward R z j)) := by
  intro k
  by_cases hkj : k = j
  · subst k
    rw [shift_apply_same]
    have hz' := abs_le.mp (hz j)
    rw [abs_le]
    unfold inward
    by_cases h : z j < R
    · rw [ite_eq_left h]
      change -R ≤ z j + 1 ∧ z j + 1 ≤ R
      constructor <;> linarith [hz'.1, hz'.2]
    · rw [ite_eq_right h]
      have hR : R ≤ z j := le_of_not_gt h
      have hEq : z j = R := le_antisymm hz'.2 hR
      rw [hEq]
      change -R ≤ R - 1 ∧ R - 1 ≤ R
      constructor
      · rw [neg_le_sub_iff_le_add]
        omega
      · omega
  · rw [shift_apply_ne z hkj]
    exact hz k

lemma shift_inward_ne (R : ℤ) (z : V d) (j : Fin d) :
    shift z j (inward R z j) ≠ z := by
  intro h
  have h' := congrFun h j
  rw [shift_apply_same] at h'
  have hn := inward_ne_zero R z j
  omega

lemma exists_other_coordinate {i : Fin d} (hd : 2 ≤ d) : ∃ j : Fin d, j ≠ i := by
  have hc : 1 < Fintype.card (Fin d) := by
    simp only [Fintype.card_fin]
    omega
  exact Fintype.exists_ne_of_one_lt_card hc i


lemma one_le_box_of_two {R : ℤ} {x y : V d} (hx : InBox R x) (hy : InBox R y)
    (i : Fin d) (htwo : 2 ≤ (x i - y i).natAbs) : 1 ≤ R := by
  have hx' := abs_le.mp (hx i)
  have hy' := abs_le.mp (hy i)
  have htwoZ : (2 : ℤ) ≤ ((x i - y i).natAbs : ℤ) := by exact_mod_cast htwo
  by_cases hxy : x i ≤ y i
  · have hnon : 0 ≤ y i - x i := by omega
    have hcomm : x i - y i = -(y i - x i) := by ring
    rw [hcomm, Int.natAbs_neg, Int.natAbs_of_nonneg hnon] at htwoZ
    omega
  · have hnon : 0 ≤ x i - y i := by omega
    rw [Int.natAbs_of_nonneg hnon] at htwoZ
    omega

/-- Any two vertices other than `z` in a two-or-higher dimensional lattice box
are joined by a walk staying in the box and avoiding `z`.  The proof constructs
the walk by induction on taxicab distance. -/
theorem exists_box_walk_avoiding (hd : 2 ≤ d) {R : ℤ} (z : V d) :
    ∀ (N : ℕ) (x y : V d), dist x y ≤ N → InBox R x → InBox R y →
      x ≠ z → y ≠ z →
      ∃ p : (lattice d).Walk x y,
        (∀ w ∈ p.support, InBox R w) ∧ z ∉ p.support := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro x y hN hx hy hxz hyz
    by_cases hxy : x = y
    · subst y
      refine ⟨SimpleGraph.Walk.nil, ?_, ?_⟩
      · intro w hw
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        subst w
        exact hx
      · simpa using hxz.symm
    · obtain ⟨i, hi⟩ := exists_coordinate_ne hxy
      let a : ℤ := toward x y i
      let w : V d := shift x i a
      have haunit : a = 1 ∨ a = -1 := toward_unit x y i
      have hwbox : InBox R w := InBox.shift_toward hx hy i a (toward_between i hi)
      have hwadj : (lattice d).Adj x w := step_adj x i a haunit
      have hwdist : dist w y + 1 = dist x y := dist_toward_one i hi
      by_cases hwz : w = z
      · by_cases hyi : y i = z i
        · have hxother : ∃ j : Fin d, j ≠ i ∧ x j ≠ y j := by
            by_contra hn
            apply hyz
            funext k
            by_cases hki : k = i
            · subst k; exact hyi
            · have hxk : x k = y k := by
                by_contra hk
                exact hn ⟨k, hki, hk⟩
              calc
                y k = x k := hxk.symm
                _ = w k := by simp [w, shift_apply_ne x hki a]
                _ = z k := by rw [hwz]
          obtain ⟨j, hji, hjne⟩ := hxother
          let u : V d := shift x j (toward x y j)
          have huunit : toward x y j = 1 ∨ toward x y j = -1 := toward_unit x y j
          have hubox : InBox R u := InBox.shift_toward hx hy j _ (toward_between j hjne)
          have hudist : dist u y + 1 = dist x y := dist_toward_one j hjne
          have hune : u ≠ z := ne_shift_toward_of_coordinate_ne hji a hwz.symm hjne
          have hlt : dist u y < N := by omega
          obtain ⟨q, hqbox, hqz⟩ := ih (dist u y) hlt u y le_rfl hubox hy hune hyz
          refine ⟨SimpleGraph.Walk.cons (step_adj x j _ huunit) q, ?_, ?_⟩
          · intro v hv
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
            rcases hv with rfl | hv
            · exact hx
            · exact hqbox v hv
          · simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
            exact ⟨hxz.symm, hqz⟩
        · have htwo : 2 ≤ (x i - y i).natAbs := by
            have hdone := toward_dist_one i hi
            by_contra hn
            have hone : (x i - y i).natAbs = 1 := by omega
            rw [hone] at hdone
            have hzero : (x i + a - y i).natAbs = 0 := by
              change (x i + toward x y i - y i).natAbs = 0
              omega
            have heq : x i + a = y i := by omega
            apply hyi
            calc
              y i = x i + a := heq.symm
              _ = w i := by dsimp [w]; rw [shift_apply_same]
              _ = z i := by rw [hwz]
          have hRpos : 1 ≤ R := one_le_box_of_two hx hy i htwo
          let w2 : V d := shift z i a
          have hw2def : shift w i a = w2 := by rw [hwz]
          have hw2box : InBox R w2 := by
            rw [← hw2def, shift_add]
            apply InBox.shift_toward hx hy i (a + a)
            simpa only [a, ← add_assoc] using toward_between_two i hi htwo
          have hw2dist : dist w2 y + 2 = dist x y := by
            rw [← hw2def]
            exact dist_toward_two i hi htwo
          have hw2z : w2 ≠ z := by
            intro h
            have hc := congrFun h i
            rw [show w2 i = z i + a from shift_apply_same z i a] at hc
            have hn := toward_ne_zero x y i
            omega
          have hlt : dist w2 y < N := by omega
          obtain ⟨q, hqbox, hqz⟩ := ih (dist w2 y) hlt w2 y le_rfl hw2box hy hw2z hyz
          obtain ⟨j, hji⟩ := exists_other_coordinate (i := i) hd
          let t : ℤ := inward R z j
          let u : V d := shift x j t
          let v : V d := shift u i a
          let w3 : V d := shift v i a
          have htunit : t = 1 ∨ t = -1 := inward_unit R z j
          have hxj : x j = z j := by
            calc
              x j = w j := by simp [w, shift_apply_ne x hji a]
              _ = z j := by rw [hwz]
          have ht_eq : t = inward R x j := by change (if z j < R then (1 : ℤ) else -1) = if x j < R then 1 else -1; rw [hxj]
          have hubox : InBox R u := by
            change InBox R (shift x j t)
            rw [ht_eq]
            exact inBox_shift_inward hRpos hx j
          have hvz : v = shift z j t := by
            change shift (shift x j t) i a = shift z j t
            rw [← hwz]
            exact (shift_shift_comm x (i := i) (j := j) hji.symm a t).symm
          have hw2j : w2 j = z j := by
            exact shift_apply_ne z (i := i) (j := j) hji a
          have hw3z : w3 = shift w2 j t := by
            change shift v i a = shift w2 j t
            rw [hvz]
            change shift (shift z j t) i a = shift (shift z i a) j t
            exact (shift_shift_comm z (i := i) (j := j) hji.symm a t).symm
          have hvbox : InBox R v := by
            rw [hvz]
            exact inBox_shift_inward hRpos (hwz ▸ hwbox) j
          have hw3box : InBox R w3 := by
            rw [hw3z]
            have ht2 : t = inward R w2 j := by change (if z j < R then (1 : ℤ) else -1) = if w2 j < R then 1 else -1; rw [hw2j]
            rw [ht2]
            exact inBox_shift_inward hRpos hw2box j
          have hune : u ≠ z := by
            intro h
            have hc := congrFun h j
            have ht0 := inward_ne_zero R z j
            change shift x j t j = z j at hc
            rw [shift_apply_same, hxj] at hc
            change t ≠ 0 at ht0
            omega
          have hvne : v ≠ z := by rw [hvz]; exact shift_inward_ne R z j
          have hw3ne : w3 ≠ z := by
            rw [hw3z]
            intro h
            have hc := congrFun h j
            rw [shift_apply_same, hw2j] at hc
            have ht0 := inward_ne_zero R z j
            change t ≠ 0 at ht0
            omega
          have hlast : shift w3 j (-t) = w2 := by
            rw [hw3z, shift_add]
            simp [shift_zero]
          have h1 : (lattice d).Adj x u := step_adj x j t htunit
          have h2 : (lattice d).Adj u v := step_adj u i a haunit
          have h3 : (lattice d).Adj v w3 := step_adj v i a haunit
          have h4 : (lattice d).Adj w3 w2 := by
            rw [← hlast]
            have hnt : -t = 1 ∨ -t = -1 := by rcases htunit with h | h <;> simp [h]
            exact step_adj w3 j (-t) hnt
          refine ⟨SimpleGraph.Walk.cons h1
            (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3
              (SimpleGraph.Walk.cons h4 q))), ?_, ?_⟩
          · intro r hr
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hr
            rcases hr with rfl | rfl | rfl | rfl | hr
            · exact hx
            · exact hubox
            · exact hvbox
            · exact hw3box
            · exact hqbox r hr
          · simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
            exact ⟨hxz.symm, hune.symm, hvne.symm, hw3ne.symm, hqz⟩
      · have hlt : dist w y < N := by omega
        obtain ⟨q, hqbox, hqz⟩ := ih (dist w y) hlt w y le_rfl hwbox hy hwz hyz
        refine ⟨SimpleGraph.Walk.cons hwadj q, ?_, ?_⟩
        · intro v hv
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hx
          · exact hqbox v hv
        · simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hxz.symm, hqz⟩

/-- The induced lattice graph on a box with one distinguished vertex deleted. -/
def puncturedBox (R : ℤ) (z : V d) : SimpleGraph {x : V d // InBox R x ∧ x ≠ z} :=
  (lattice d).induce {x | InBox R x ∧ x ≠ z}

/-- Puncturing any vertex leaves the box graph preconnected in dimension at
least two. -/
theorem puncturedBox_preconnected (hd : 2 ≤ d) {R : ℤ} (z : V d) :
    (puncturedBox (d := d) R z).Preconnected := by
  rintro ⟨x, hxbox, hxz⟩ ⟨y, hybox, hyz⟩
  obtain ⟨p, hpbox, hpz⟩ := exists_box_walk_avoiding hd z (dist x y) x y
    le_rfl hxbox hybox hxz hyz
  have hs : ∀ w ∈ p.support, w ∈ {x : V d | InBox R x ∧ x ≠ z} := by
    intro w hw
    exact ⟨hpbox w hw, fun hwz => hpz (hwz ▸ hw)⟩
  exact ⟨p.induce _ hs⟩

/-- The same statement with the puncture represented as removal from the
ambient box, which is the vertex-connectivity form used by the AG linkage
campaign. -/
theorem reachable_induce_box_diff_singleton (hd : 2 ≤ d) {R : ℤ} (z : V d)
    (x y : {w : V d // InBox R w ∧ w ≠ z}) :
    ((lattice d).induce {w | InBox R w ∧ w ≠ z}).Reachable x y :=
  puncturedBox_preconnected hd z x y

end LatticeBoxes
