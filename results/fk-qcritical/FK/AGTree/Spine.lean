import FK.AGTree.EdgeClass

/-!
# A bi-infinite spine in the two-class tree

The reduced-word tree contains an explicit double ray: alternate two distinct
base letters.  Going right from the root we use the word `a b a b …`; going left
we use `b a b a …`.  This file constructs the alternating words, proves they are
reduced, and assembles them into a `FK.EssentialEnhancement.DoubleRay`.  The edge
at the root on this spine is the pivot needed for the essential-enhancement
device constructions.
-/

namespace Ultra

open V

/-! ### Alternating words -/

/-- The letter in position `n` of the alternating word starting with `x`. -/
def altNext (x y : A) (n : ℕ) : A := if n % 2 = 0 then x else y

/-- The alternating word of length `n` starting with `x`. -/
def altWord (x y : A) (n : ℕ) : List A := (List.range n).map (altNext x y)

@[simp] lemma altWord_zero (x y : A) : altWord x y 0 = [] := rfl

lemma altNext_succ (x y : A) (k : ℕ) : altNext x y (k + 1) = altNext y x k := by
  have h1 : (k + 1) % 2 = 0 ↔ ¬ (k % 2 = 0) := by omega
  unfold altNext
  show (if (k + 1) % 2 = 0 then x else y) = (if k % 2 = 0 then y else x)
  by_cases hk : k % 2 = 0
  · rw [if_neg (by omega), if_pos hk]
  · rw [if_pos (h1.mpr hk), if_neg hk]

lemma altWord_cons (x y : A) (n : ℕ) : altWord x y (n + 1) = x :: altWord y x n := by
  simp only [altWord, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 2
  funext k
  exact altNext_succ x y k

lemma altWord_succ (x y : A) (n : ℕ) :
    altWord x y (n + 1) = altWord x y n ++ [altNext x y n] := by
  simp only [altWord, List.range_succ, List.map_append, List.map_cons, List.map_nil]

@[simp] lemma altWord_length (x y : A) (n : ℕ) : (altWord x y n).length = n := by
  simp [altWord]

lemma altWord_head? (x y : A) (n : ℕ) :
    (altWord x y n).head? = if n = 0 then none else some x := by
  cases n with
  | zero => simp [altWord]
  | succ n => rw [altWord_cons]; simp

lemma altWord_getLast? (x y : A) : ∀ n : ℕ,
    (altWord x y n).getLast? = if n = 0 then none else some (altNext x y (n - 1))
  | 0 => by simp [altWord]
  | n + 1 => by
    rw [altWord_succ, List.getLast?_concat]
    simp

/-- Consecutive alternating letters differ. -/
lemma altNext_ne {x y : A} (hxy : x ≠ y) (n : ℕ) :
    altNext x y n ≠ altNext x y (n + 1) := by
  have h2 : ((n + 1) % 2 = 0) ↔ ¬ (n % 2 = 0) := by omega
  unfold altNext
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_neg (by omega)]
    exact hxy
  · rw [if_neg hn, if_pos (h2.mpr hn)]
    exact Ne.symm hxy

/-- Alternating words are reduced. -/
lemma altWord_reduced {x y : A} (hxy : x ≠ y) : ∀ n : ℕ, Reduced (altWord x y n)
  | 0 => by simp
  | n + 1 => by
    rw [altWord_succ]
    refine (Reduced.snoc_iff _ _).mpr ⟨altWord_reduced hxy n, ?_⟩
    by_cases hn : altWord x y n = []
    · exact Or.inl hn
    · refine Or.inr ?_
      have hne0 : n ≠ 0 := by
        rintro rfl
        exact hn (by simp [altWord])
      rw [altWord_getLast?, if_neg hne0]
      have hne : altNext x y (n - 1) ≠ altNext x y n := by
        have h := altNext_ne hxy (n - 1)
        rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne0)] at h
      intro h
      exact hne (Option.some.inj h)

/-! ### The spine -/

/-- The bi-infinite alternating spine through the root: nonnegative indices run
through `x y x y …`, negative indices through `y x y x …`. -/
def spine (x y : A) (hxy : x ≠ y) (n : ℤ) : V :=
  if hn : 0 ≤ n then ⟨altWord x y n.toNat, altWord_reduced hxy n.toNat⟩
  else ⟨altWord y x (-n).toNat, altWord_reduced (Ne.symm hxy) (-n).toNat⟩

lemma spine_of_nonneg {x y : A} {hxy : x ≠ y} {n : ℤ} (hn : 0 ≤ n) :
    (spine x y hxy n).w = altWord x y n.toNat := by
  rw [spine, dif_pos hn]

lemma spine_of_neg {x y : A} {hxy : x ≠ y} {n : ℤ} (hn : ¬ 0 ≤ n) :
    (spine x y hxy n).w = altWord y x (-n).toNat := by
  rw [spine, dif_neg hn]

lemma spine_length {x y : A} (hxy : x ≠ y) (n : ℤ) :
    (spine x y hxy n).w.length = n.natAbs := by
  by_cases hn : 0 ≤ n
  · rw [spine_of_nonneg hn, altWord_length]
    omega
  · rw [spine_of_neg hn, altWord_length]
    omega

/-- Consecutive spine vertices are adjacent. -/
theorem spine_adj {x y : A} (hxy : x ≠ y) (n : ℤ) :
    G.Adj (spine x y hxy n) (spine x y hxy (n + 1)) := by
  by_cases hn : 0 ≤ n
  · -- both indices are nonnegative
    have h1 : (0 : ℤ) ≤ n + 1 := by omega
    refine adj_of_snoc (c := altNext x y n.toNat) ?_
    rw [spine_of_nonneg h1, spine_of_nonneg hn]
    have hnat : (n + 1).toNat = n.toNat + 1 := by omega
    rw [hnat, altWord_succ]
  · -- both indices are negative
    have hn' : n < 0 := not_le.mp hn
    by_cases hnm1 : n = -1
    · refine adj_of_parent (c := y) ?_
      subst hnm1
      rw [spine_of_neg (by norm_num), spine_of_nonneg (by norm_num)]
      simp [altWord, altNext]
    · have hle : n ≤ -2 := by omega
      have hn1 : ¬ (0 : ℤ) ≤ n + 1 := by omega
      refine adj_of_parent (c := altNext y x (-(n + 1)).toNat) ?_
      rw [spine_of_neg hn, spine_of_neg hn1]
      have hnat : (-n).toNat = (-(n + 1)).toNat + 1 := by omega
      rw [hnat, altWord_succ]

lemma spine_zero {x y : A} (hxy : x ≠ y) : spine x y hxy (0 : ℤ) = V.root := by
  apply V.ext
  rw [spine_of_nonneg (by norm_num)]
  simp [V.root]

lemma spine_one {x y : A} (hxy : x ≠ y) :
    spine x y hxy (1 : ℤ) = ⟨[x], reduced_singleton x⟩ := by
  apply V.ext
  rw [spine_of_nonneg (by norm_num)]
  norm_num [altWord, altNext]

/-- Spine vertices are pairwise distinct. -/
theorem spine_injective {x y : A} (hxy : x ≠ y) : Function.Injective (spine x y hxy) := by
  intro n m hnm
  have hlen : n.natAbs = m.natAbs := by
    rw [← spine_length hxy n, ← spine_length hxy m, hnm]
  by_cases hn : 0 ≤ n <;> by_cases hm : 0 ≤ m
  · omega
  · exfalso
    have hword : altWord x y n.toNat = altWord y x (-m).toNat := by
      rw [← spine_of_nonneg (hxy := hxy) hn, ← spine_of_neg (hxy := hxy) (by omega)]
      exact congrArg V.w hnm
    have hhead := congrArg List.head? hword
    rw [altWord_head?, altWord_head?] at hhead
    have h1 : n.toNat ≠ 0 := by
      intro h0
      omega
    have h2 : (-m).toNat ≠ 0 := by
      intro h0
      omega
    rw [if_neg h1, if_neg h2] at hhead
    exact hxy (Option.some.inj hhead)
  · exfalso
    have hword : altWord y x (-n).toNat = altWord x y m.toNat := by
      rw [← spine_of_neg (hxy := hxy) (by omega), ← spine_of_nonneg (hxy := hxy) hm]
      exact congrArg V.w hnm
    have hhead := congrArg List.head? hword
    rw [altWord_head?, altWord_head?] at hhead
    have h2 : m.toNat ≠ 0 := by
      intro h0
      omega
    have h1 : (-n).toNat ≠ 0 := by
      intro h0
      omega
    rw [if_neg h1, if_neg h2] at hhead
    exact hxy (Option.some.inj hhead).symm
  · omega

/-- The two base letters used by the spine. -/
def spineA : A := Sum.inl 0

def spineB : A := Sum.inl 1

lemma spineA_ne_spineB : spineA ≠ spineB := by decide

/-- The explicit double ray through the root. -/
def doubleRay : FK.EssentialEnhancement.DoubleRay G where
  vertex := spine spineA spineB spineA_ne_spineB
  vertex_injective := spine_injective spineA_ne_spineB
  adj := spine_adj spineA_ne_spineB

/-- The root's `spineA`-edge lies on the double ray. -/
theorem onDoubleRay_rootEdge :
    FK.EssentialEnhancement.OnDoubleRay (childE ⟨(V.root, spineA), (by left; rfl)⟩) := by
  refine ⟨doubleRay, 0, ?_⟩
  apply Subtype.ext
  show s(V.root, V.root.snoc spineA (by left; rfl)) =
    s(spine spineA spineB spineA_ne_spineB 0, spine spineA spineB spineA_ne_spineB (0 + 1))
  rw [show ((0 : ℤ) + 1) = 1 from rfl, spine_zero spineA_ne_spineB,
    spine_one spineA_ne_spineB, root_snoc_eq]

end Ultra
