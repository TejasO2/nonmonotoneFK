import BBRAG.Defs

/-!
# Parity of edge counts of closed walks

If every unit square of `ℤ^d` has an even number of `e`-edges, then every closed walk has an even
number of `e`-steps.

Proof: write the walk as its start site and its list of unit steps. Swapping two consecutive steps
changes the count by the count of a unit square, or by an even number, so the parity of the count
does not change when the steps are reordered. A closed nonempty list of unit steps contains a step
`u` together with its opposite `-u`; moving `-u` right after `u` and then deleting the pair (an
out-and-back move, which adds an even number to the count) gives a shorter closed walk with the
same parity.
-/

namespace BBR

variable {d : ℕ}

/-! ### Walks as a start site and a list of steps -/

/-- The steps `x₁ - x₀, x₂ - x₁, …` of a sequence of sites `x₀, x₁, x₂, …`. -/
private def stepsOf : List (Site d) → List (Site d)
  | x :: y :: t => (y - x) :: stepsOf (y :: t)
  | _ => []

/-- The number of `e`-steps of the walk that starts at `x` and makes the steps `l`. -/
private def stepCount (e : Site d → Site d → Prop) [DecidableRel e] : Site d → List (Site d) → ℕ
  | _, [] => 0
  | x, u :: l => (if e x (x + u) then 1 else 0) + stepCount e (x + u) l

private theorem edgeCount_eq_stepCount (e : Site d → Site d → Prop) [DecidableRel e] :
    ∀ (x : Site d) (t : List (Site d)), edgeCount e (x :: t) = stepCount e x (stepsOf (x :: t))
  | _, [] => rfl
  | x, y :: t => by
    simp only [edgeCount, stepsOf, stepCount, add_sub_cancel]
    rw [edgeCount_eq_stepCount e y t]

private theorem getLast?_eq_add_sum_stepsOf :
    ∀ (x : Site d) (t : List (Site d)), (x :: t).getLast? = some (x + (stepsOf (x :: t)).sum)
  | x, [] => by simp [stepsOf]
  | x, y :: t => by
    rw [List.getLast?_cons_cons, getLast?_eq_add_sum_stepsOf y t]
    simp only [stepsOf, List.sum_cons, ← add_assoc, add_sub_cancel]

private theorem isUnitVec_of_mem_stepsOf :
    ∀ (x : Site d) (t : List (Site d)), (x :: t).IsChain Adj → ∀ u ∈ stepsOf (x :: t), IsUnitVec u
  | x, [] => by simp [stepsOf]
  | x, y :: t => by
    intro h u hu
    rw [List.isChain_cons_cons] at h
    simp only [stepsOf, List.mem_cons] at hu
    rcases hu with rfl | hu
    · obtain ⟨v, hv, rfl⟩ := (adj_iff_exists_unitVec x y).mp h.1
      rwa [add_sub_cancel_left]
    · exact isUnitVec_of_mem_stepsOf y t h.2 u hu

/-! ### Parity is invariant under reordering the steps -/

private theorem ite_comm_of_symm (e : Site d → Site d → Prop) [DecidableRel e]
    (hsym : ∀ x y, e x y ↔ e y x) (x y : Site d) :
    (if e x y then 1 else 0 : ℕ) = if e y x then 1 else 0 :=
  if_congr (hsym x y) rfl rfl

/-- Swapping two consecutive unit steps does not change the parity of the count. -/
private theorem stepCount_swap (e : Site d → Site d → Prop) [DecidableRel e]
    (hsym : ∀ x y, e x y ↔ e y x)
    (hsq : ∀ x a b : Site d, IsUnitVec a → IsUnitVec b → Orth a b →
      Even (edgeCount e [x, x + a, x + a + b, x + b, x]))
    (a b : Site d) (ha : IsUnitVec a) (hb : IsUnitVec b) (y : Site d) (l : List (Site d)) :
    stepCount e y (a :: b :: l) % 2 = stepCount e y (b :: a :: l) % 2 := by
  by_cases hba : b = a
  · rw [hba]
  by_cases hna : b = -a
  · subst hna
    simp only [stepCount, add_neg_cancel_right, neg_add_cancel_right]
    rw [ite_comm_of_symm e hsym (y + a) y, ite_comm_of_symm e hsym (y + -a) y]
    omega
  · have h := hsq y a b ha hb ⟨hba, hna⟩
    rw [Nat.even_iff] at h
    simp only [edgeCount] at h
    rw [ite_comm_of_symm e hsym (y + a + b) (y + b), ite_comm_of_symm e hsym (y + b) y] at h
    simp only [stepCount]
    rw [add_right_comm y b a]
    omega

/-- Reordering the unit steps of a walk does not change the parity of the count. -/
private theorem stepCount_perm (e : Site d → Site d → Prop) [DecidableRel e]
    (hsym : ∀ x y, e x y ↔ e y x)
    (hsq : ∀ x a b : Site d, IsUnitVec a → IsUnitVec b → Orth a b →
      Even (edgeCount e [x, x + a, x + a + b, x + b, x]))
    {l l' : List (Site d)} (h : l.Perm l') :
    (∀ u ∈ l, IsUnitVec u) → ∀ x, stepCount e x l % 2 = stepCount e x l' % 2 := by
  induction h with
  | nil => intro _ _; rfl
  | cons a _ ih =>
    intro hu x
    have := ih (fun u hu' => hu u (List.mem_cons_of_mem a hu')) (x + a)
    simp only [stepCount]
    omega
  | swap a b l =>
    intro hu x
    exact stepCount_swap e hsym hsq b a (hu b (by simp)) (hu a (by simp)) x l
  | trans h₁ _ ih₁ ih₂ =>
    intro hu x
    rw [ih₁ hu x, ih₂ (fun u hu' => hu u (h₁.symm.subset hu')) x]

/-! ### A closed list of unit steps contains a step and its opposite -/

private theorem nonneg_mul_sum_apply (i : Fin d) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∀ t : List (Site d), (∀ v ∈ t, IsUnitVec v) → (Pi.single i (-s) : Site d) ∉ t →
      0 ≤ s * t.sum i := by
  intro t
  induction t with
  | nil => intro _ _; simp
  | cons v t ih =>
    intro hv hn
    have h1 := ih (fun w hw => hv w (List.mem_cons_of_mem v hw))
      (fun h => hn (List.mem_cons_of_mem v h))
    obtain ⟨j, r, hr, rfl⟩ := (isUnitVec_iff v).mp (hv v List.mem_cons_self)
    have h2 : 0 ≤ s * (Pi.single j r : Site d) i := by
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same]
        have hrs : r ≠ -s := fun hrs => hn (by rw [hrs]; exact List.mem_cons_self)
        rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> omega
      · rw [Pi.single_eq_of_ne hij]
        simp
    rw [List.sum_cons, Pi.add_apply, mul_add]
    linarith

private theorem neg_mem_of_sum_eq_zero (u : Site d) (t : List (Site d))
    (hu : ∀ v ∈ u :: t, IsUnitVec v) (hs : (u :: t).sum = 0) : -u ∈ t := by
  obtain ⟨i, s, hs1, rfl⟩ := (isUnitVec_iff u).mp (hu u List.mem_cons_self)
  by_contra hne
  rw [← Pi.single_neg] at hne
  have h3 := nonneg_mul_sum_apply i s hs1 t (fun v hv => hu v (List.mem_cons_of_mem _ hv)) hne
  have h4 := congrFun hs i
  rw [List.sum_cons, Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at h4
  rcases hs1 with rfl | rfl <;> omega

/-! ### Closed lists of unit steps have an even count -/

private theorem even_stepCount (e : Site d → Site d → Prop) [DecidableRel e]
    (hsym : ∀ x y, e x y ↔ e y x)
    (hsq : ∀ x a b : Site d, IsUnitVec a → IsUnitVec b → Orth a b →
      Even (edgeCount e [x, x + a, x + a + b, x + b, x])) :
    ∀ (n : ℕ) (l : List (Site d)), l.length = n → (∀ u ∈ l, IsUnitVec u) → l.sum = 0 →
      ∀ x, Even (stepCount e x l) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hlen hu hsum x
  cases l with
  | nil => exact ⟨0, rfl⟩
  | cons u t =>
    have hmem := neg_mem_of_sum_eq_zero u t hu hsum
    have hperm : (u :: t).Perm (u :: -u :: t.erase (-u)) := (List.perm_cons_erase hmem).cons u
    have hpar := stepCount_perm e hsym hsq hperm hu x
    have hsum' : (t.erase (-u)).sum = 0 := by
      have h1 := (List.perm_cons_erase hmem).sum_eq
      rw [List.sum_cons] at hsum h1
      rw [h1, ← add_assoc, add_neg_cancel, zero_add] at hsum
      exact hsum
    have hlen' : (t.erase (-u)).length < n := by
      rw [List.length_erase_of_mem hmem]
      simp only [List.length_cons] at hlen
      omega
    have ih' := ih _ hlen' (t.erase (-u)) rfl
      (fun v hv => hu v (List.mem_cons_of_mem u (List.erase_subset hv))) hsum' x
    rw [Nat.even_iff] at ih' ⊢
    simp only [stepCount, add_neg_cancel_right] at hpar ⊢
    rw [ite_comm_of_symm e hsym (x + u) x] at hpar
    omega

theorem even_edgeCount_closed (e : Site d → Site d → Prop) [DecidableRel e]
    (hsym : ∀ x y, e x y ↔ e y x)
    (hsq : ∀ x a b : Site d, IsUnitVec a → IsUnitVec b → Orth a b →
      Even (edgeCount e [x, x + a, x + a + b, x + b, x]))
    (P : List (Site d)) (hP : IsWalk P) (hcl : P.head? = P.getLast?) :
    Even (edgeCount e P) := by
  obtain ⟨hne, hch⟩ := hP
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hsum : (stepsOf (x :: t)).sum = 0 := by
    rw [getLast?_eq_add_sum_stepsOf, List.head?_cons, Option.some_inj] at hcl
    exact left_eq_add.mp hcl
  rw [edgeCount_eq_stepCount]
  exact even_stepCount e hsym hsq _ _ rfl (isUnitVec_of_mem_stepsOf x t hch) hsum x

end BBR
