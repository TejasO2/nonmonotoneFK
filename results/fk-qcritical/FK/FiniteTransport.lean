import Mathlib

/-!
# A finite transportation lemma with real weights

Given finite types `X`, `Y`, a relation `R : X → Y → Prop` and nonnegative masses
`a : X → ℝ`, `b : Y → ℝ` of equal total mass, the Hall condition
`a(S) ≤ b(N_R(S))` for all finite `S ⊆ X` is sufficient for the existence of a
nonnegative matrix `π : X → Y → ℝ` with row sums `a`, column sums `b` and support
contained in `R`.

The proof is an elementary tight-set induction (no linear programming duality).
This is the combinatorial core of the hard direction of Strassen's theorem.
-/

namespace FiniteTransport

universe u

variable {X Y : Type u}

/-- The `R`-neighbourhood of a finite set. -/
def Nbr [Fintype Y] [DecidableEq Y] (R : X → Y → Prop) [DecidableRel R] (S : Finset X) : Finset Y :=
  S.biUnion (fun x => Finset.univ.filter (R x))

section Basic

variable [Fintype Y] [DecidableEq Y] {R : X → Y → Prop} [DecidableRel R]

lemma mem_Nbr {S : Finset X} {y : Y} : y ∈ Nbr R S ↔ ∃ x ∈ S, R x y := by
  simp [Nbr]

lemma Nbr_mono {S S' : Finset X} (h : S ⊆ S') : Nbr R S ⊆ Nbr R S' := by
  intro y hy
  rw [mem_Nbr] at hy ⊢
  obtain ⟨x, hx, hR⟩ := hy
  exact ⟨x, h hx, hR⟩

lemma Nbr_empty : Nbr R (∅ : Finset X) = ∅ := by
  simp [Nbr]

lemma Nbr_singleton (x : X) : Nbr R ({x} : Finset X) = Finset.univ.filter (R x) := by
  simp [Nbr]

end Basic

/-- The conclusion shape of the transportation lemma. -/
def IsTransport [Fintype X] [Fintype Y] (R : X → Y → Prop) (a : X → ℝ) (b : Y → ℝ)
    (π : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = a x) ∧ (∀ y, ∑ x, π x y = b y) ∧
    (∀ x y, ¬ R x y → π x y = 0)

/-- **Tight-set splitting step.**  If `U ⊆ S` is a nonempty proper set on which the Hall
inequality is tight, the problem splits into the two independent problems
`(U, N U)` and `(S \ U, T \ N U)`. -/
theorem split_tight {X Y : Type u} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]
    {R : X → Y → Prop} [DecidableRel R] {a : X → ℝ} {b : Y → ℝ} {S : Finset X} {T : Finset Y}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hsa : ∀ x, a x ≠ 0 ↔ x ∈ S) (hsb : ∀ y, b y ≠ 0 ↔ y ∈ T)
    (hsum : ∑ x ∈ S, a x = ∑ y ∈ T, b y)
    (hHall : ∀ U, U ⊆ S → ∑ x ∈ U, a x ≤ ∑ y ∈ Nbr R U, b y)
    {U : Finset X} (hUS : U ⊆ S) (hUne : U.Nonempty) (hUneS : U ≠ S)
    (htight : ∑ x ∈ U, a x = ∑ y ∈ Nbr R U, b y)
    (ih : ∀ (S' : Finset X) (T' : Finset Y) (a' : X → ℝ) (b' : Y → ℝ),
        S'.card + T'.card < S.card + T.card →
        (∀ x, 0 ≤ a' x) → (∀ y, 0 ≤ b' y) →
        (∀ x, a' x ≠ 0 ↔ x ∈ S') → (∀ y, b' y ≠ 0 ↔ y ∈ T') →
        (∑ x ∈ S', a' x = ∑ y ∈ T', b' y) →
        (∀ U', U' ⊆ S' → ∑ x ∈ U', a' x ≤ ∑ y ∈ Nbr R U', b' y) →
        ∃ π : X → Y → ℝ, IsTransport R a' b' π) :
    ∃ π : X → Y → ℝ, IsTransport R a b π := by
  classical
  have hzero_a : ∀ x, x ∉ S → a x = 0 := by
    intro x hx
    by_contra hc
    exact hx ((hsa x).mp hc)
  have hzero_b : ∀ y, y ∉ T → b y = 0 := by
    intro y hy
    by_contra hc
    exact hy ((hsb y).mp hc)
  -- the two subproblems
  set a₁ : X → ℝ := fun x => if x ∈ U then a x else 0 with ha₁
  set b₁ : Y → ℝ := fun y => if y ∈ Nbr R U ∩ T then b y else 0 with hb₁
  set a₂ : X → ℝ := fun x => if x ∈ S \ U then a x else 0 with ha₂
  set b₂ : Y → ℝ := fun y => if y ∈ T \ Nbr R U then b y else 0 with hb₂
  have hv₁ : ∀ x, a₁ x = if x ∈ U then a x else 0 := fun x => by rw [ha₁]
  have hv₁b : ∀ y, b₁ y = if y ∈ Nbr R U ∩ T then b y else 0 := fun y => by rw [hb₁]
  have hv₂ : ∀ x, a₂ x = if x ∈ S \ U then a x else 0 := fun x => by rw [ha₂]
  have hv₂b : ∀ y, b₂ y = if y ∈ T \ Nbr R U then b y else 0 := fun y => by rw [hb₂]
  -- cardinalities of the subproblems
  have hcard1 : U.card + (Nbr R U ∩ T).card < S.card + T.card := by
    have h1 : U.card < S.card := by
      have hle : U.card ≤ S.card := Finset.card_le_card hUS
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (Finset.eq_of_subset_of_card_le hUS (le_of_eq h.symm)) hUneS
    have h2 : (Nbr R U ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have hcard2 : (S \ U).card + (T \ Nbr R U).card < S.card + T.card := by
    have hUpos : 0 < U.card := Finset.card_pos.mpr hUne
    have hUle : U.card ≤ S.card := Finset.card_le_card hUS
    have h1 : (S \ U).card ≤ S.card - U.card := by
      rw [Finset.card_sdiff]
      have h2 : U ∩ S = U := Finset.inter_eq_left.mpr hUS
      rw [h2]
    have h2 : (T \ Nbr R U).card ≤ T.card := by
      rw [Finset.card_sdiff]
      exact Nat.sub_le _ _
    omega
  -- nonnegativity of the subproblem masses
  have hnn₁ : ∀ x, 0 ≤ a₁ x := by
    intro x
    rw [hv₁ x]
    by_cases h : x ∈ U
    · rw [if_pos h]; exact ha x
    · rw [if_neg h]
  have hnn₁b : ∀ y, 0 ≤ b₁ y := by
    intro y
    rw [hv₁b y]
    by_cases h : y ∈ Nbr R U ∩ T
    · rw [if_pos h]; exact hb y
    · rw [if_neg h]
  have hnn₂ : ∀ x, 0 ≤ a₂ x := by
    intro x
    rw [hv₂ x]
    by_cases h : x ∈ S \ U
    · rw [if_pos h]; exact ha x
    · rw [if_neg h]
  have hnn₂b : ∀ y, 0 ≤ b₂ y := by
    intro y
    rw [hv₂b y]
    by_cases h : y ∈ T \ Nbr R U
    · rw [if_pos h]; exact hb y
    · rw [if_neg h]
  -- supports
  have hsupp₁ : ∀ x, a₁ x ≠ 0 ↔ x ∈ U := by
    intro x
    rw [hv₁ x]
    by_cases h : x ∈ U
    · rw [if_pos h]; exact (hsa x).trans (iff_of_true (hUS h) h)
    · rw [if_neg h]; exact iff_of_false (by simp) h
  have hsupp₁b : ∀ y, b₁ y ≠ 0 ↔ y ∈ Nbr R U ∩ T := by
    intro y
    rw [hv₁b y]
    by_cases h : y ∈ Nbr R U ∩ T
    · rw [if_pos h]; exact (hsb y).trans (iff_of_true (Finset.mem_inter.mp h).2 h)
    · rw [if_neg h]; exact iff_of_false (by simp) h
  have hsupp₂ : ∀ x, a₂ x ≠ 0 ↔ x ∈ S \ U := by
    intro x
    rw [hv₂ x]
    by_cases h : x ∈ S \ U
    · rw [if_pos h]; exact (hsa x).trans (iff_of_true (Finset.mem_sdiff.mp h).1 h)
    · rw [if_neg h]; exact iff_of_false (by simp) h
  have hsupp₂b : ∀ y, b₂ y ≠ 0 ↔ y ∈ T \ Nbr R U := by
    intro y
    rw [hv₂b y]
    by_cases h : y ∈ T \ Nbr R U
    · rw [if_pos h]; exact (hsb y).trans (iff_of_true (Finset.mem_sdiff.mp h).1 h)
    · rw [if_neg h]; exact iff_of_false (by simp) h
  -- mass balance of the two subproblems
  have hsum1 : ∑ x ∈ U, a₁ x = ∑ y ∈ Nbr R U ∩ T, b₁ y := by
    have h1 : ∑ x ∈ U, a₁ x = ∑ x ∈ U, a x :=
      Finset.sum_congr rfl (fun x hx => by rw [hv₁ x, if_pos hx])
    have h2 : ∑ y ∈ Nbr R U ∩ T, b₁ y = ∑ y ∈ Nbr R U ∩ T, b y :=
      Finset.sum_congr rfl (fun y hy => by rw [hv₁b y, if_pos hy])
    have h3 : ∑ y ∈ Nbr R U ∩ T, b y = ∑ y ∈ Nbr R U, b y := by
      refine Finset.sum_subset Finset.inter_subset_left (fun y hy hy' => ?_)
      exact hzero_b y (fun hyT => hy' (Finset.mem_inter.mpr ⟨hy, hyT⟩))
    rw [h1, h2, h3, htight]
  have hsum2 : ∑ x ∈ S \ U, a₂ x = ∑ y ∈ T \ Nbr R U, b₂ y := by
    have h1 : ∑ x ∈ S \ U, a₂ x = ∑ x ∈ S \ U, a x :=
      Finset.sum_congr rfl (fun x hx => by rw [hv₂ x, if_pos hx])
    have h2 : ∑ y ∈ T \ Nbr R U, b₂ y = ∑ y ∈ T \ Nbr R U, b y :=
      Finset.sum_congr rfl (fun y hy => by rw [hv₂b y, if_pos hy])
    have h3 : ∑ y ∈ T ∩ Nbr R U, b y = ∑ y ∈ Nbr R U, b y := by
      refine Finset.sum_subset Finset.inter_subset_right (fun y hy hy' => ?_)
      exact hzero_b y (fun hyT => hy' (Finset.mem_inter.mpr ⟨hyT, hy⟩))
    have h4 : ∑ x ∈ S \ U, a x + ∑ x ∈ U, a x = ∑ x ∈ S, a x :=
      Finset.sum_sdiff hUS
    have h5 : ∑ y ∈ T \ (T ∩ Nbr R U), b y + ∑ y ∈ T ∩ Nbr R U, b y = ∑ y ∈ T, b y :=
      Finset.sum_sdiff Finset.inter_subset_left
    have h6 : T \ (T ∩ Nbr R U) = T \ Nbr R U := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [h6] at h5
    rw [h1, h2]
    linarith
  -- Hall conditions of the two subproblems
  have hHall1 : ∀ V, V ⊆ U → ∑ x ∈ V, a₁ x ≤ ∑ y ∈ Nbr R V, b₁ y := by
    intro V hV
    have h1 : ∑ x ∈ V, a₁ x = ∑ x ∈ V, a x :=
      Finset.sum_congr rfl (fun x hx => by rw [hv₁ x, if_pos (hV hx)])
    have h2 : ∑ y ∈ Nbr R V, b₁ y = ∑ y ∈ Nbr R V, b y := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hyU : y ∈ Nbr R U := Nbr_mono hV hy
      rw [hv₁b y]
      by_cases hT : y ∈ T
      · rw [if_pos (Finset.mem_inter.mpr ⟨hyU, hT⟩)]
      · have hnotin : y ∉ Nbr R U ∩ T := fun hc => hT (Finset.mem_inter.mp hc).2
        rw [if_neg hnotin, hzero_b y hT]
    rw [h1, h2]
    exact hHall V (hV.trans hUS)
  have hHall2 : ∀ V, V ⊆ S \ U → ∑ x ∈ V, a₂ x ≤ ∑ y ∈ Nbr R V, b₂ y := by
    intro V hV
    have h1 : ∑ x ∈ V, a₂ x = ∑ x ∈ V, a x :=
      Finset.sum_congr rfl (fun x hx => by rw [hv₂ x, if_pos (hV hx)])
    have h2 : ∑ y ∈ Nbr R V, b₂ y = ∑ y ∈ Nbr R V \ Nbr R U, b y := by
      have hpt : ∀ y ∈ Nbr R V, b₂ y = if y ∈ Nbr R U then 0 else b y := by
        intro y hy
        rw [hv₂b y]
        by_cases hyU : y ∈ Nbr R U
        · have : y ∉ T \ Nbr R U := by simp [hyU]
          rw [if_neg this, if_pos hyU]
        · by_cases hyT : y ∈ T
          · rw [if_pos (Finset.mem_sdiff.mpr ⟨hyT, hyU⟩), if_neg hyU]
          · rw [hzero_b y hyT, if_neg hyU]; simp
      rw [Finset.sum_congr rfl hpt, Finset.sum_ite]
      rw [Finset.sum_const_zero, zero_add]
      rw [show (∑ y ∈ Nbr R V with ¬ y ∈ Nbr R U, b y) = ∑ y ∈ Nbr R V \ Nbr R U, b y from by
        rw [Finset.sdiff_eq_filter]]
    have hVU : V ∪ U ⊆ S := Finset.union_subset (hV.trans Finset.sdiff_subset) hUS
    have hdisj : Disjoint V U := by
      rw [Finset.disjoint_left]
      intro x hx hxU
      exact (Finset.mem_sdiff.mp (hV hx)).2 hxU
    have hU1 : ∑ x ∈ V ∪ U, a x = ∑ x ∈ V, a x + ∑ x ∈ U, a x := Finset.sum_union hdisj
    have hdisj2 : Disjoint (Nbr R V \ Nbr R U) (Nbr R U) := by
      rw [Finset.disjoint_left]
      intro y hy hyU
      exact (Finset.mem_sdiff.mp hy).2 hyU
    have hAB : (Nbr R V \ Nbr R U) ∪ Nbr R U = Nbr R V ∪ Nbr R U := by
      ext y
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hU2 : ∑ y ∈ Nbr R (V ∪ U), b y
        = ∑ y ∈ Nbr R V \ Nbr R U, b y + ∑ y ∈ Nbr R U, b y := by
      rw [← Finset.sum_union hdisj2, hAB]
      congr 1
      ext y
      simp only [Nbr, Finset.mem_biUnion, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨x, hx | hx, hR⟩
        · exact Or.inl ⟨x, hx, hR⟩
        · exact Or.inr ⟨x, hx, hR⟩
      · rintro (⟨x, hx, hR⟩ | ⟨x, hx, hR⟩)
        · exact ⟨x, Or.inl hx, hR⟩
        · exact ⟨x, Or.inr hx, hR⟩
    have hmain := hHall (V ∪ U) hVU
    rw [hU1, hU2, htight] at hmain
    rw [h1, h2]
    linarith
  obtain ⟨π₁, hπ₁⟩ := ih U _ a₁ b₁ hcard1 hnn₁ hnn₁b hsupp₁ hsupp₁b hsum1 hHall1
  obtain ⟨π₂, hπ₂⟩ := ih (S \ U) (T \ Nbr R U) a₂ b₂ hcard2 hnn₂ hnn₂b hsupp₂ hsupp₂b hsum2 hHall2
  refine ⟨fun x y => π₁ x y + π₂ x y, ?_, ?_, ?_, ?_⟩
  · intro x y; exact add_nonneg (hπ₁.1 x y) (hπ₂.1 x y)
  · intro x
    rw [Finset.sum_add_distrib, hπ₁.2.1 x, hπ₂.2.1 x, hv₁ x, hv₂ x]
    by_cases h1 : x ∈ U
    · have h2 : x ∉ S \ U := by simp [h1]
      rw [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : x ∈ S \ U
      · rw [if_neg h1, if_pos h2, zero_add]
      · have hxS : x ∉ S := by
          by_contra hc
          exact h2 (by simp [hc, h1])
        rw [if_neg h1, if_neg h2, add_zero, hzero_a x hxS]
  · intro y
    rw [Finset.sum_add_distrib, hπ₁.2.2.1 y, hπ₂.2.2.1 y, hv₁b y, hv₂b y]
    by_cases h1 : y ∈ Nbr R U ∩ T
    · have h2 : y ∉ T \ Nbr R U := by simp [(Finset.mem_inter.mp h1).1]
      rw [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : y ∈ T \ Nbr R U
      · rw [if_neg h1, if_pos h2, zero_add]
      · have hyT : y ∉ T := by
          by_contra hc
          exact h2 (Finset.mem_sdiff.mpr ⟨hc, fun hcU => h1 (Finset.mem_inter.mpr ⟨hcU, hc⟩)⟩)
        rw [if_neg h1, if_neg h2, add_zero, hzero_b y hyT]
  · intro x y hR
    show π₁ x y + π₂ x y = 0
    rw [hπ₁.2.2.2 x y hR, hπ₂.2.2.2 x y hR, add_zero]


/-- **Main induction.**  Feasibility of the transportation problem with support data. -/
theorem transport_aux :
    ∀ (n : ℕ) (X Y : Type u) [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]
      (R : X → Y → Prop) [DecidableRel R] (a : X → ℝ) (b : Y → ℝ)
      (S : Finset X) (T : Finset Y),
      S.card + T.card ≤ n →
      (∀ x, 0 ≤ a x) → (∀ y, 0 ≤ b y) →
      (∀ x, a x ≠ 0 ↔ x ∈ S) → (∀ y, b y ≠ 0 ↔ y ∈ T) →
      (∑ x ∈ S, a x = ∑ y ∈ T, b y) →
      (∀ U, U ⊆ S → ∑ x ∈ U, a x ≤ ∑ y ∈ Nbr R U, b y) →
      ∃ π : X → Y → ℝ, IsTransport R a b π := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro X Y _ _ _ _ R _ a b S T hcard ha hb hsa hsb hsum hHall
  classical
  have IH : ∀ (S' : Finset X) (T' : Finset Y) (a' : X → ℝ) (b' : Y → ℝ),
      S'.card + T'.card < n →
      (∀ x, 0 ≤ a' x) → (∀ y, 0 ≤ b' y) →
      (∀ x, a' x ≠ 0 ↔ x ∈ S') → (∀ y, b' y ≠ 0 ↔ y ∈ T') →
      (∑ x ∈ S', a' x = ∑ y ∈ T', b' y) →
      (∀ U', U' ⊆ S' → ∑ x ∈ U', a' x ≤ ∑ y ∈ Nbr R U', b' y) →
      ∃ π : X → Y → ℝ, IsTransport R a' b' π :=
    fun S' T' a' b' hlt =>
      ih (S'.card + T'.card) hlt X Y R a' b' S' T' le_rfl
  have hzero_a : ∀ x, x ∉ S → a x = 0 := by
    intro x hx
    by_contra hc
    exact hx ((hsa x).mp hc)
  have hzero_b : ∀ y, y ∉ T → b y = 0 := by
    intro y hy
    by_contra hc
    exact hy ((hsb y).mp hc)
  have IH' : ∀ (S' : Finset X) (T' : Finset Y) (a' : X → ℝ) (b' : Y → ℝ),
      S'.card + T'.card < S.card + T.card →
      (∀ x, 0 ≤ a' x) → (∀ y, 0 ≤ b' y) →
      (∀ x, a' x ≠ 0 ↔ x ∈ S') → (∀ y, b' y ≠ 0 ↔ y ∈ T') →
      (∑ x ∈ S', a' x = ∑ y ∈ T', b' y) →
      (∀ U', U' ⊆ S' → ∑ x ∈ U', a' x ≤ ∑ y ∈ Nbr R U', b' y) →
      ∃ π : X → Y → ℝ, IsTransport R a' b' π :=
    fun S' T' a' b' hlt => IH S' T' a' b' (lt_of_lt_of_le hlt hcard)
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- no row mass at all
    have ha0 : ∀ x, a x = 0 := by
      intro x
      by_contra hc
      have hx : x ∈ S := (hsa x).mp hc
      rw [hS] at hx
      exact absurd hx (by simp)
    have hb0 : ∀ y, b y = 0 := by
      intro y
      by_cases hy : y ∈ T
      · have hsum0 : ∑ y ∈ T, b y = 0 := by rw [← hsum, hS]; simp
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hb i)).mp hsum0 y hy
      · by_contra hc
        exact hy ((hsb y).mp hc)
    refine ⟨fun _ _ => 0, ?_, ?_, ?_, ?_⟩
    · intro x y; exact le_refl 0
    · intro x; rw [Finset.sum_const_zero, ha0 x]
    · intro y; rw [Finset.sum_const_zero, hb0 y]
    · intro x y _; rfl
  · by_cases htight : ∃ U, U ⊆ S ∧ U.Nonempty ∧ U ≠ S ∧ ∑ x ∈ U, a x = ∑ y ∈ Nbr R U, b y
    · obtain ⟨U, hUS, hUne, hUneS, htighteq⟩ := htight
      exact split_tight ha hb hsa hsb hsum hHall hUS hUne hUneS htighteq IH'
    · -- no tight proper subset: subtract the point mass `t` at a certified pair
      obtain ⟨x₀, hx₀S⟩ := hS
      have hx₀pos : 0 < a x₀ := by
        have hne : a x₀ ≠ 0 := (hsa x₀).mpr hx₀S
        exact lt_of_le_of_ne (ha x₀) (Ne.symm hne)
      have hHall0 : a x₀ ≤ ∑ y ∈ Nbr R ({x₀} : Finset X), b y := by
        have h := hHall _ (Finset.singleton_subset_iff.mpr hx₀S)
        rwa [Finset.sum_singleton] at h
      have hex : ∃ y ∈ Nbr R ({x₀} : Finset X), 0 < b y := by
        by_contra hc
        have hc' : ∀ y ∈ Nbr R ({x₀} : Finset X), b y ≤ 0 := by
          intro y hy
          by_contra h
          exact hc ⟨y, hy, lt_of_not_ge h⟩
        have hle : ∑ y ∈ Nbr R ({x₀} : Finset X), b y ≤ 0 := Finset.sum_nonpos hc'
        linarith
      obtain ⟨y₀, hy₀N, hy₀pos⟩ := hex
      have hy₀T : y₀ ∈ T := (hsb y₀).mp (ne_of_gt hy₀pos)
      have hRy₀ : R x₀ y₀ := by
        obtain ⟨x, hx, hRx⟩ := mem_Nbr.mp hy₀N
        rw [Finset.mem_singleton] at hx
        subst hx
        exact hRx
      -- the slack family and its minimum
      set Vset : Finset (Finset X) := (S.erase x₀).powerset.filter (fun V => y₀ ∈ Nbr R V) with hVset
      set slack : Finset X → ℝ := fun V => (∑ y ∈ Nbr R V, b y) - (∑ x ∈ V, a x) with hslack
      set t : ℝ := (insert (a x₀) (insert (b y₀) (Vset.image slack))).min' (by simp) with ht
      have hmem_set : ∀ V ∈ Vset, slack V ∈ insert (a x₀) (insert (b y₀) (Vset.image slack)) := by
        intro V hV
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hV))
      have ht_le_a : t ≤ a x₀ := by
        rw [ht]; exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      have ht_le_b : t ≤ b y₀ := by
        rw [ht]
        exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have ht_le_slack : ∀ V ∈ Vset, t ≤ slack V := fun V hV => by
        rw [ht]; exact Finset.min'_le _ _ (hmem_set V hV)
      have hVset_sub : ∀ V ∈ Vset, V ⊆ S ∧ x₀ ∉ V ∧ y₀ ∈ Nbr R V := by
        intro V hV
        rw [hVset, Finset.mem_filter, Finset.mem_powerset] at hV
        refine ⟨hV.1.trans (Finset.erase_subset _ _), ?_, hV.2⟩
        intro hx
        exact (Finset.mem_erase.mp (hV.1 hx)).1 rfl
      have ht_pos : 0 < t := by
        have hmem : t ∈ insert (a x₀) (insert (b y₀) (Vset.image slack)) := by
          rw [ht]; exact Finset.min'_mem _ _
        rcases Finset.mem_insert.mp hmem with heq | hmem'
        · rw [heq]; exact hx₀pos
        rcases Finset.mem_insert.mp hmem' with heq | hmem''
        · rw [heq]; exact hy₀pos
        obtain ⟨V, hV, hVs⟩ := Finset.mem_image.mp hmem''
        rw [← hVs]
        obtain ⟨hVS, hx₀V, hy₀NV⟩ := hVset_sub V hV
        have hVne : V.Nonempty := by
          obtain ⟨x, hx, -⟩ := mem_Nbr.mp hy₀NV
          exact ⟨x, hx⟩
        have hVneS : V ≠ S := fun h => hx₀V (h ▸ hx₀S)
        have hne : (∑ x ∈ V, a x) ≠ (∑ y ∈ Nbr R V, b y) := fun he =>
          htight ⟨V, hVS, hVne, hVneS, he⟩
        have hlt : (∑ x ∈ V, a x) < (∑ y ∈ Nbr R V, b y) :=
          lt_of_le_of_ne (hHall V hVS) hne
        simp only [hslack]; linarith
      -- the reduced masses
      set a' : X → ℝ := fun x => a x - if x = x₀ then t else 0 with ha'
      set b' : Y → ℝ := fun y => b y - if y = y₀ then t else 0 with hb'
      have hva' : ∀ x, a' x = a x - (if x = x₀ then t else 0) := fun x => by rw [ha']
      have hvb' : ∀ y, b' y = b y - (if y = y₀ then t else 0) := fun y => by rw [hb']
      have hnn_a' : ∀ x, 0 ≤ a' x := by
        intro x
        rw [hva' x]
        by_cases h : x = x₀
        · rw [if_pos h, h]; linarith
        · rw [if_neg h, sub_zero]; exact ha x
      have hnn_b' : ∀ y, 0 ≤ b' y := by
        intro y
        rw [hvb' y]
        by_cases h : y = y₀
        · rw [if_pos h, h]; linarith
        · rw [if_neg h, sub_zero]; exact hb y
      have hsum' : ∑ x ∈ S, a' x = ∑ y ∈ T, b' y := by
        have h1 : ∑ x ∈ S, a' x = (∑ x ∈ S, a x) - t := by
          rw [Finset.sum_congr rfl (fun x _ => hva' x), Finset.sum_sub_distrib,
            Finset.sum_ite_eq', if_pos hx₀S]
        have h2 : ∑ y ∈ T, b' y = (∑ y ∈ T, b y) - t := by
          rw [Finset.sum_congr rfl (fun y _ => hvb' y), Finset.sum_sub_distrib,
            Finset.sum_ite_eq', if_pos hy₀T]
        rw [h1, h2, hsum]
      have hHall' : ∀ U, U ⊆ S → ∑ x ∈ U, a' x ≤ ∑ y ∈ Nbr R U, b' y := by
        intro U hUS
        have h1 : ∑ x ∈ U, a' x = (∑ x ∈ U, a x) - (if x₀ ∈ U then t else 0) := by
          rw [Finset.sum_congr rfl (fun x _ => hva' x), Finset.sum_sub_distrib,
            Finset.sum_ite_eq']
        have h2 : ∑ y ∈ Nbr R U, b' y
            = (∑ y ∈ Nbr R U, b y) - (if y₀ ∈ Nbr R U then t else 0) := by
          rw [Finset.sum_congr rfl (fun y _ => hvb' y), Finset.sum_sub_distrib,
            Finset.sum_ite_eq']
        have hHU := hHall U hUS
        rw [h1, h2]
        by_cases hx : x₀ ∈ U
        · rw [if_pos hx]
          by_cases hy : y₀ ∈ Nbr R U
          · rw [if_pos hy]; linarith
          · rw [if_neg hy]; linarith
        · rw [if_neg hx]
          by_cases hy : y₀ ∈ Nbr R U
          · rw [if_pos hy]
            have hUV : U ∈ Vset := by
              rw [hVset, Finset.mem_filter, Finset.mem_powerset]
              exact ⟨Finset.subset_erase.mpr ⟨hUS, hx⟩, hy⟩
            have hsl := ht_le_slack U hUV
            simp only [hslack] at hsl
            linarith
          · rw [if_neg hy]; linarith
      -- either the support drops, or a tight set appears
      have hrec : ∃ π' : X → Y → ℝ, IsTransport R a' b' π' := by
        by_cases hdrop : a' x₀ = 0 ∨ b' y₀ = 0
        · set S' : Finset X := S.filter (fun x => a' x ≠ 0) with hS'
          set T' : Finset Y := T.filter (fun y => b' y ≠ 0) with hT'
          have hsuppS' : ∀ x, a' x ≠ 0 ↔ x ∈ S' := by
            intro x
            rw [hS', Finset.mem_filter]
            constructor
            · intro h
              refine ⟨?_, h⟩
              by_contra hxS
              exact h (by rw [hva' x, if_neg (fun hx => hxS (by rw [hx]; exact hx₀S)), hzero_a x hxS, sub_zero])
            · exact fun h => h.2
          have hsuppT' : ∀ y, b' y ≠ 0 ↔ y ∈ T' := by
            intro y
            rw [hT', Finset.mem_filter]
            constructor
            · intro h
              refine ⟨?_, h⟩
              by_contra hyT
              exact h (by rw [hvb' y, if_neg (fun hy => hyT (by rw [hy]; exact hy₀T)), hzero_b y hyT, sub_zero])
            · exact fun h => h.2
          have hsubS : S' ⊆ S := by rw [hS']; exact Finset.filter_subset _ _
          have hsubT : T' ⊆ T := by rw [hT']; exact Finset.filter_subset _ _
          have hcard' : S'.card + T'.card < n := by
            have hlt1 : S'.card ≤ S.card := Finset.card_le_card hsubS
            have hlt2 : T'.card ≤ T.card := Finset.card_le_card hsubT
            have hproper : S'.card + T'.card < S.card + T.card := by
              rcases hdrop with hd | hd
              · have hne : S' ≠ S := by
                  intro he
                  have hmem : x₀ ∈ S' := by rw [he]; exact hx₀S
                  exact ((hsuppS' x₀).mpr hmem) hd
                have hc : S'.card < S.card := by
                  rcases lt_or_eq_of_le hlt1 with h | h
                  · exact h
                  · exact absurd (Finset.eq_of_subset_of_card_le hsubS (le_of_eq h.symm)) hne
                omega
              · have hne : T' ≠ T := by
                  intro he
                  have hmem : y₀ ∈ T' := by rw [he]; exact hy₀T
                  exact ((hsuppT' y₀).mpr hmem) hd
                have hc : T'.card < T.card := by
                  rcases lt_or_eq_of_le hlt2 with h | h
                  · exact h
                  · exact absurd (Finset.eq_of_subset_of_card_le hsubT (le_of_eq h.symm)) hne
                omega
            omega
          have hsum'' : ∑ x ∈ S', a' x = ∑ y ∈ T', b' y := by
            rw [Finset.sum_subset hsubS (fun x _ hx' => by
                  by_contra hc; exact hx' ((hsuppS' x).mp hc)),
                Finset.sum_subset hsubT (fun y _ hy' => by
                  by_contra hc; exact hy' ((hsuppT' y).mp hc)), hsum']
          have hHall'' : ∀ U, U ⊆ S' → ∑ x ∈ U, a' x ≤ ∑ y ∈ Nbr R U, b' y :=
            fun U hU => hHall' U (hU.trans hsubS)
          exact IH S' T' a' b' hcard' hnn_a' hnn_b' hsuppS' hsuppT' hsum'' hHall''
        · have hdrop₁ : a' x₀ ≠ 0 := fun h => hdrop (Or.inl h)
          have hdrop₂ : b' y₀ ≠ 0 := fun h => hdrop (Or.inr h)
          have ht_ne_a : t ≠ a x₀ := by
            intro he
            exact hdrop₁ (by rw [hva' x₀, if_pos rfl, he, sub_self])
          have ht_ne_b : t ≠ b y₀ := by
            intro he
            exact hdrop₂ (by rw [hvb' y₀, if_pos rfl, he, sub_self])
          have hmem : t ∈ insert (a x₀) (insert (b y₀) (Vset.image slack)) := by
            rw [ht]; exact Finset.min'_mem _ _
          have ht_slack : t ∈ Vset.image slack := by
            rcases Finset.mem_insert.mp hmem with h | h
            · exact absurd h ht_ne_a
            rcases Finset.mem_insert.mp h with h | h
            · exact absurd h ht_ne_b
            · exact h
          obtain ⟨V₀, hV₀, hV₀t⟩ := Finset.mem_image.mp ht_slack
          obtain ⟨hV₀S, hx₀V₀, hy₀V₀⟩ := hVset_sub V₀ hV₀
          have hV₀ne : V₀.Nonempty := by
            obtain ⟨x, hx, -⟩ := mem_Nbr.mp hy₀V₀
            exact ⟨x, hx⟩
          have hV₀neS : V₀ ≠ S := fun h => hx₀V₀ (h ▸ hx₀S)
          have hsa' : ∀ x, a' x ≠ 0 ↔ x ∈ S := by
            intro x
            constructor
            · intro h
              by_contra hxS
              exact h (by rw [hva' x, if_neg (fun hx => hxS (by rw [hx]; exact hx₀S)), hzero_a x hxS, sub_zero])
            · intro hx
              by_cases hxx : x = x₀
              · rw [hxx]; exact hdrop₁
              · rw [hva' x, if_neg hxx, sub_zero]
                exact (hsa x).mpr hx
          have hsb' : ∀ y, b' y ≠ 0 ↔ y ∈ T := by
            intro y
            constructor
            · intro h
              by_contra hyT
              exact h (by rw [hvb' y, if_neg (fun hy => hyT (by rw [hy]; exact hy₀T)), hzero_b y hyT, sub_zero])
            · intro hy
              by_cases hyy : y = y₀
              · rw [hyy]; exact hdrop₂
              · rw [hvb' y, if_neg hyy, sub_zero]
                exact (hsb y).mpr hy
          have htight' : ∑ x ∈ V₀, a' x = ∑ y ∈ Nbr R V₀, b' y := by
            have h1 : ∑ x ∈ V₀, a' x = ∑ x ∈ V₀, a x := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              rw [hva' x, if_neg (fun h => hx₀V₀ (by rw [← h]; exact hx)), sub_zero]
            have h2 : ∑ y ∈ Nbr R V₀, b' y = (∑ y ∈ Nbr R V₀, b y) - t := by
              rw [Finset.sum_congr rfl (fun y _ => hvb' y), Finset.sum_sub_distrib,
                Finset.sum_ite_eq', if_pos hy₀V₀]
            have h3 : t = (∑ y ∈ Nbr R V₀, b y) - (∑ x ∈ V₀, a x) := by
              simpa only [hslack] using hV₀t.symm
            rw [h1, h2, h3]
            ring
          exact split_tight hnn_a' hnn_b' hsa' hsb' hsum' hHall' hV₀S hV₀ne hV₀neS htight' IH'
      obtain ⟨π', hπ'⟩ := hrec
      -- add the point mass back
      have hinner : ∀ x, ∑ y, (if x = x₀ ∧ y = y₀ then t else 0) = if x = x₀ then t else 0 := by
        intro x
        rw [show (∑ y, (if x = x₀ ∧ y = y₀ then t else 0))
            = ∑ y, (if y = y₀ then (if x = x₀ then t else 0) else 0) from by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          by_cases h1 : x = x₀ <;> by_cases h2 : y = y₀ <;> simp [h1, h2]]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ y₀)]
      have hinner2 : ∀ y, ∑ x, (if x = x₀ ∧ y = y₀ then t else 0) = if y = y₀ then t else 0 := by
        intro y
        rw [show (∑ x, (if x = x₀ ∧ y = y₀ then t else 0))
            = ∑ x, (if x = x₀ then (if y = y₀ then t else 0) else 0) from by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          by_cases h1 : x = x₀ <;> by_cases h2 : y = y₀ <;> simp [h1, h2]]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ x₀)]
      refine ⟨fun x y => π' x y + (if x = x₀ ∧ y = y₀ then t else 0), ?_, ?_, ?_, ?_⟩
      · intro x y
        exact add_nonneg (hπ'.1 x y) (by split <;> simp [ht_pos.le])
      · intro x
        show ∑ y, (π' x y + (if x = x₀ ∧ y = y₀ then t else 0)) = a x
        rw [Finset.sum_add_distrib, hπ'.2.1 x, hinner x, hva' x]
        ring
      · intro y
        show ∑ x, (π' x y + (if x = x₀ ∧ y = y₀ then t else 0)) = b y
        rw [Finset.sum_add_distrib, hπ'.2.2.1 y, hinner2 y, hvb' y]
        ring
      · intro x y hR
        have hne : ¬ (x = x₀ ∧ y = y₀) := by
          rintro ⟨rfl, rfl⟩
          exact hR hRy₀
        show π' x y + (if x = x₀ ∧ y = y₀ then t else 0) = 0
        rw [hπ'.2.2.2 x y hR, if_neg hne, add_zero]

/-- **The finite transportation lemma.**  Real-weighted Hall condition implies feasibility. -/
theorem exists_transport {X Y : Type u} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]
    {R : X → Y → Prop} [DecidableRel R] {a : X → ℝ} {b : Y → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (hsum : ∑ x, a x = ∑ y, b y)
    (hHall : ∀ U : Finset X, ∑ x ∈ U, a x ≤ ∑ y ∈ Nbr R U, b y) :
    ∃ π : X → Y → ℝ, IsTransport R a b π := by
  classical
  set S : Finset X := Finset.univ.filter (fun x => a x ≠ 0) with hS
  set T : Finset Y := Finset.univ.filter (fun y => b y ≠ 0) with hT
  have hsa : ∀ x, a x ≠ 0 ↔ x ∈ S := by
    intro x; rw [hS]; simp
  have hsb : ∀ y, b y ≠ 0 ↔ y ∈ T := by
    intro y; rw [hT]; simp
  have hsum' : ∑ x ∈ S, a x = ∑ y ∈ T, b y := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by
          by_contra hc; exact hx ((hsa x).mp hc)),
        hsum,
        ← Finset.sum_subset (Finset.subset_univ T) (fun y _ hy => by
          by_contra hc; exact hy ((hsb y).mp hc))]
  exact transport_aux (S.card + T.card) X Y R a b S T le_rfl ha hb hsa hsb hsum'
    (fun U _ => hHall U)

section Strassen

open MeasureTheory

variable {α : Type u} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The order relation of a preorder, as a decidable binary relation. -/
def LeRel (α : Type u) [LE α] : α → α → Prop := fun x y => x ≤ y

noncomputable instance instDecidableLeRel (α : Type u) [LE α] : DecidableRel (LeRel α) :=
  Classical.decRel (LeRel α)

lemma lrel_iff {α : Type u} [LE α] {x y : α} : LeRel α x y ↔ x ≤ y := Iff.rfl

/-- The `≤`-neighbourhood of a set of configurations is an upper set. -/
lemma nbr_upper [PartialOrder α] (S : Finset (α)) :
    IsUpperSet (↑(Nbr (LeRel α) S) : Set (α)) := by
  intro a b hab ha
  rw [Finset.mem_coe, mem_Nbr] at ha ⊢
  obtain ⟨x, hx, hxa⟩ := ha
  exact ⟨x, hx, le_trans (lrel_iff.mp hxa) hab⟩

/-- **Strassen's theorem, hard direction, on a finite preorder.**
If `μ` is stochastically dominated by `ν` (all upper events), then there is a
coupling with exact marginals whose coordinates are ordered almost surely. -/
theorem finite_strassen [PartialOrder α] (μ ν : Measure (α)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (α), IsUpperSet A → μ A ≤ ν A) :
    ∃ κ : Measure ((α) × (α)), IsProbabilityMeasure κ ∧
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧ ∀ᵐ z ∂κ, z.1 ≤ z.2 := by
  classical
  set a : (α) → ℝ := fun x => (μ {x}).toReal with ha
  set b : (α) → ℝ := fun y => (ν {y}).toReal with hb
  have ha0 : ∀ x, 0 ≤ a x := fun x => ENNReal.toReal_nonneg
  have hb0 : ∀ y, 0 ≤ b y := fun y => ENNReal.toReal_nonneg
  have ha1 : ∑ x, a x = 1 := by
    have h1 : ∑ x, a x = (∑ x, μ {x}).toReal := by
      rw [ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]
    rw [h1, MeasureTheory.sum_measure_singleton]
    simp
  have hb1 : ∑ y, b y = 1 := by
    have h1 : ∑ y, b y = (∑ y, ν {y}).toReal := by
      rw [ENNReal.toReal_sum (fun y _ => measure_ne_top ν _)]
    rw [h1, MeasureTheory.sum_measure_singleton]
    simp
  have hsum : ∑ x, a x = ∑ y, b y := by rw [ha1, hb1]
  have hHall : ∀ S : Finset (α), ∑ x ∈ S, a x ≤ ∑ y ∈ Nbr (LeRel α) S, b y := by
    intro S
    have h1 : ∑ x ∈ S, a x = (μ ↑S).toReal := by
      rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top μ _), MeasureTheory.sum_measure_singleton]
    have h2 : ∑ y ∈ Nbr (LeRel α) S, b y = (ν ↑(Nbr (LeRel α) S)).toReal := by
      rw [← ENNReal.toReal_sum (fun y _ => measure_ne_top ν _), MeasureTheory.sum_measure_singleton]
    rw [h1, h2]
    refine ENNReal.toReal_mono (measure_ne_top ν _) ?_
    refine le_trans (measure_mono ?_) (hdom _ (nbr_upper S))
    intro x hx
    exact Finset.mem_coe.mpr (mem_Nbr.mpr ⟨x, Finset.mem_coe.mp hx, lrel_iff.mpr le_rfl⟩)
  obtain ⟨π, hπ⟩ := FiniteTransport.exists_transport (R := LeRel α) ha0 hb0 hsum hHall
  -- the candidate coupling
  set κ : Measure ((α) × (α)) :=
    ∑ p : (α) × (α), ENNReal.ofReal (π p.1 p.2) • Measure.dirac p with hκ
  have hκ_apply : ∀ S : Set ((α) × (α)), MeasurableSet S →
      κ S = ∑ p : (α) × (α),
        (if p ∈ S then ENNReal.ofReal (π p.1 p.2) else 0) := by
    intro S hS
    have hsum_apply : ∀ (s : Finset ((α) × (α)))
        (g : (α) × (α) → Measure ((α) × (α))),
        (∑ p ∈ s, g p) S = ∑ p ∈ s, g p S := by
      intro s g
      induction s using Finset.induction with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Measure.add_apply, ih]
    rw [hκ, hsum_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Measure.smul_apply, Measure.dirac_apply]
    by_cases h : p ∈ S
    · simp [Set.indicator_of_mem h, h]
    · simp [Set.indicator_of_notMem h, h]
  have hκ_univ : κ Set.univ = 1 := by
    rw [hκ_apply Set.univ MeasurableSet.univ]
    simp only [Set.mem_univ, if_true]
    rw [Fintype.sum_prod_type' (f := fun a b => ENNReal.ofReal (π a b))]
    rw [show (∑ x, ∑ y, ENNReal.ofReal (π x y))
        = ∑ x, ENNReal.ofReal (∑ y, π x y) from by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => hπ.1 x y)]]
    rw [show (∑ x, ENNReal.ofReal (∑ y : α, π x y))
        = ENNReal.ofReal (∑ x, ∑ y, π x y) from
      (ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hπ.1 x y))).symm]
    rw [show (∑ x, ∑ y, π x y) = ∑ x, a x from by
      exact Finset.sum_congr rfl (fun x _ => hπ.2.1 x)]
    rw [ha1, ENNReal.ofReal_one]
  refine ⟨κ, ?_, ?_, ?_, ?_⟩
  · exact MeasureTheory.isProbabilityMeasure_iff.mpr hκ_univ
  · apply Measure.ext_of_singleton
    intro x
    rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
    rw [hκ_apply _ (MeasurableSet.preimage (measurableSet_singleton x) measurable_fst)]
    rw [show (∑ p : (α) × (α),
          (if p ∈ Prod.fst ⁻¹' ({x} : Set (α)) then ENNReal.ofReal (π p.1 p.2) else 0))
        = ∑ p : (α) × (α), (if p.1 = x then ENNReal.ofReal (π p.1 p.2) else 0) from by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h : p.1 = x <;> simp [h]]
    rw [Fintype.sum_prod_type' (f := fun a b => if a = x then ENNReal.ofReal (π a b) else 0)]
    rw [show (∑ x_1, ∑ y, (if x_1 = x then ENNReal.ofReal (π x_1 y) else 0))
        = ∑ x_1, (if x_1 = x then ∑ y, ENNReal.ofReal (π x_1 y) else 0) from by
      refine Finset.sum_congr rfl (fun x_1 _ => ?_)
      by_cases h : x_1 = x <;> simp [h]]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ x)]
    rw [show (∑ y, ENNReal.ofReal (π x y)) = ENNReal.ofReal (∑ y, π x y) from
      (ENNReal.ofReal_sum_of_nonneg (fun y _ => hπ.1 x y)).symm]
    rw [hπ.2.1 x, ha]
    exact ENNReal.ofReal_toReal (measure_ne_top μ {x})
  · apply Measure.ext_of_singleton
    intro y
    rw [Measure.map_apply measurable_snd (measurableSet_singleton y)]
    rw [hκ_apply _ (MeasurableSet.preimage (measurableSet_singleton y) measurable_snd)]
    rw [show (∑ p : (α) × (α),
          (if p ∈ Prod.snd ⁻¹' ({y} : Set (α)) then ENNReal.ofReal (π p.1 p.2) else 0))
        = ∑ p : (α) × (α), (if p.2 = y then ENNReal.ofReal (π p.1 p.2) else 0) from by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h : p.2 = y <;> simp [h]]
    rw [Fintype.sum_prod_type' (f := fun a b => if b = y then ENNReal.ofReal (π a b) else 0)]
    rw [Finset.sum_comm]
    rw [show (∑ y_1, ∑ x, (if y_1 = y then ENNReal.ofReal (π x y_1) else 0))
        = ∑ y_1, (if y_1 = y then ∑ x, ENNReal.ofReal (π x y_1) else 0) from by
      refine Finset.sum_congr rfl (fun y_1 _ => ?_)
      by_cases h : y_1 = y <;> simp [h]]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ y)]
    rw [show (∑ x, ENNReal.ofReal (π x y)) = ENNReal.ofReal (∑ x, π x y) from
      (ENNReal.ofReal_sum_of_nonneg (fun x _ => hπ.1 x y)).symm]
    rw [hπ.2.2.1 y, hb]
    exact ENNReal.ofReal_toReal (measure_ne_top ν {y})
  · rw [MeasureTheory.ae_iff]
    rw [hκ_apply _ (Set.toFinite _).measurableSet]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    by_cases h : ¬ p.1 ≤ p.2
    · have hm : p ∈ {a : (α) × (α) | ¬ a.1 ≤ a.2} := h
      rw [if_pos hm, hπ.2.2.2 p.1 p.2 h, ENNReal.ofReal_zero]
    · have hm : p ∉ {a : (α) × (α) | ¬ a.1 ≤ a.2} := h
      rw [if_neg hm]

end Strassen

section Corollaries

open MeasureTheory

/-- **Strassen's hard direction for finite Boolean products.**  Configurations are
`E → Bool` with the pointwise order, as in the FK model. -/
theorem finite_strassen_boolean {E : Type u} [Fintype E] (μ ν : Measure (E → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (E → Bool), IsUpperSet A → μ A ≤ ν A) :
    ∃ κ : Measure ((E → Bool) × (E → Bool)), IsProbabilityMeasure κ ∧
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧ ∀ᵐ z ∂κ, z.1 ≤ z.2 := by
  classical
  exact finite_strassen μ ν hdom

/-- **Strassen's hard direction, `ProbabilityMeasure` form.**  Matches the project
convention `FKLimit.StochasticallyDominates ν μ` (upper-set inequality `μ A ≤ ν A`)
on a finite configuration space. -/
theorem finite_strassen_probabilityMeasure {E : Type u} [Fintype E]
    (μ ν : ProbabilityMeasure (E → Bool))
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A →
      (μ : Measure (E → Bool)) A ≤ (ν : Measure (E → Bool)) A) :
    ∃ κ : Measure ((E → Bool) × (E → Bool)), IsProbabilityMeasure κ ∧
      κ.map Prod.fst = (μ : Measure (E → Bool)) ∧
      κ.map Prod.snd = (ν : Measure (E → Bool)) ∧ ∀ᵐ z ∂κ, z.1 ≤ z.2 := by
  classical
  exact finite_strassen (μ : Measure (E → Bool)) (ν : Measure (E → Bool))
    (fun A hA => hdom A (Set.toFinite _).measurableSet hA)

end Corollaries

section Countable

open MeasureTheory

/-- **Converse direction.**  An ordered coupling with exact marginals implies domination
on all measurable upper sets. -/
theorem stochasticallyDominates_of_orderedCoupling {α : Type u} [MeasurableSpace α] [Preorder α]
    {μ ν : Measure α} {κ : Measure (α × α)} (hfst : κ.map Prod.fst = μ)
    (hsnd : κ.map Prod.snd = ν) (hord : ∀ᵐ z ∂κ, z.1 ≤ z.2) :
    ∀ A : Set α, MeasurableSet A → IsUpperSet A → μ A ≤ ν A := by
  intro A hA hup
  rw [← hfst, ← hsnd, Measure.map_apply measurable_fst hA, Measure.map_apply measurable_snd hA]
  refine measure_mono_ae ?_
  filter_upwards [hord] with z hz hzA
  exact hup hz hzA

/-- **Strassen's theorem (finite preorders), both directions.** -/
theorem finite_strassen_iff {α : Type u} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [PartialOrder α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∀ A : Set α, IsUpperSet A → μ A ≤ ν A) ↔
      ∃ κ : Measure (α × α), IsProbabilityMeasure κ ∧ κ.map Prod.fst = μ ∧
        κ.map Prod.snd = ν ∧ ∀ᵐ z ∂κ, z.1 ≤ z.2 := by
  classical
  constructor
  · exact fun h => finite_strassen μ ν h
  · rintro ⟨κ, -, hfst, hsnd, hord⟩ A hA
    exact stochasticallyDominates_of_orderedCoupling hfst hsnd hord A (Set.toFinite _).measurableSet hA

/-- **Countable coordinate set, finite cylinders.**  If `μ` is stochastically dominated
by `ν` on the countable configuration space `E → Bool`, then for every finite coordinate
set `S` the two `S`-marginals admit an ordered coupling with exact marginals. -/
theorem exists_cylinder_ordered_coupling {E : Type u} [Countable E]
    (μ ν : Measure (E → Bool)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A → μ A ≤ ν A)
    (S : Finset E) :
    ∃ π : Measure ((S → Bool) × (S → Bool)), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ.map (fun x (i : S) => x i) ∧
      π.map Prod.snd = ν.map (fun x (i : S) => x i) ∧
      ∀ᵐ z ∂π, z.1 ≤ z.2 := by
  classical
  have hmeas : Measurable (fun (x : E → Bool) (i : S) => x i) := by fun_prop
  haveI hμ : IsProbabilityMeasure (μ.map (fun (x : E → Bool) (i : S) => x i)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  haveI hν : IsProbabilityMeasure (ν.map (fun (x : E → Bool) (i : S) => x i)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  have hup : ∀ A : Set (S → Bool), IsUpperSet A →
      IsUpperSet ((fun (x : E → Bool) (i : S) => x i) ⁻¹' A) := by
    intro A hA x y hxy hx
    exact hA (fun i => hxy ↑i) hx
  refine finite_strassen (μ.map (fun x (i : S) => x i)) (ν.map (fun x (i : S) => x i)) ?_
  intro A hA
  have hAmeas : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [Measure.map_apply hmeas hAmeas, Measure.map_apply hmeas hAmeas]
  exact hdom _ (hAmeas.preimage hmeas) (hup A hA)

end Countable

section Transfer

open MeasureTheory
open scoped ENNReal

/-- An ordered coupling with exact marginals makes every measurable increasing
nonnegative observable monotone in expectation. -/
theorem lintegral_le_of_orderedCoupling {α : Type u} [MeasurableSpace α] [Preorder α]
    {μ ν : Measure α} {κ : Measure (α × α)} (hfst : κ.map Prod.fst = μ)
    (hsnd : κ.map Prod.snd = ν) (hord : ∀ᵐ z ∂κ, z.1 ≤ z.2)
    {f : α → ℝ≥0∞} (hf : Measurable f) (hmono : Monotone f) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ y, f y ∂ν := by
  rw [← hfst, ← hsnd, lintegral_map hf measurable_fst, lintegral_map hf measurable_snd]
  exact lintegral_mono_ae (hord.mono fun z hz => hmono hz)

/-- **Increasing observables are monotone**, finite preorder form (no integrability or
boundedness hypothesis, since the coupling is produced internally). -/
theorem lintegral_le_of_stochasticallyDominates {α : Type u} [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [PartialOrder α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ A : Set α, IsUpperSet A → μ A ≤ ν A)
    {f : α → ℝ≥0∞} (hf : Measurable f) (hmono : Monotone f) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ y, f y ∂ν := by
  classical
  obtain ⟨κ, -, hfst, hsnd, hord⟩ := finite_strassen μ ν h
  exact lintegral_le_of_orderedCoupling hfst hsnd hord hf hmono

/-- **Endpoint form.**  An upper event of measure zero for the dominating measure is
null for the dominated one. -/
theorem measure_zero_of_stochasticallyDominates {α : Type u} [MeasurableSpace α]
    [Preorder α] {μ ν : Measure α}
    (h : ∀ A : Set α, MeasurableSet A → IsUpperSet A → μ A ≤ ν A) {A : Set α}
    (hA : MeasurableSet A) (hup : IsUpperSet A) (hν : ν A = 0) : μ A = 0 :=
  le_antisymm (hν ▸ h A hA hup) (by simp)

/-- **Edge-configuration form** (`Set V` with inclusion) for a finite edge type, matching
`FK` bond configurations rather than `V → Bool`. -/
theorem finite_strassen_setConfig {V : Type u} [Fintype V] [DecidableEq V]
    (μ ν : Measure (Set V)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (Set V), IsUpperSet A → μ A ≤ ν A) :
    ∃ κ : Measure (Set V × Set V), IsProbabilityMeasure κ ∧
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧ ∀ᵐ z ∂κ, z.1 ⊆ z.2 := by
  classical
  obtain ⟨κ, hprob, hfst, hsnd, hord⟩ := finite_strassen μ ν hdom
  exact ⟨κ, hprob, hfst, hsnd, hord⟩

end Transfer

end FiniteTransport
