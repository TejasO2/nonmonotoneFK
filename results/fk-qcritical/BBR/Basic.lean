import BBR.Defs

/-!
# Basic API: norms, adjacency, unit vectors, walks and paths

General facts about the definitions of `BBR.Defs`, used throughout.
-/

namespace BBR

variable {d : ℕ}

/-! ### The ℓ¹ norm and distance -/

@[simp] theorem mem_ball {c x : Site d} {r : ℤ} : x ∈ ball c r ↔ dist1 x c ≤ r := Iff.rfl

@[simp] theorem mem_sphere {c x : Site d} {r : ℤ} : x ∈ sphere c r ↔ dist1 x c = r := Iff.rfl

instance (c : Site d) (r : ℤ) : DecidablePred (· ∈ ball c r) :=
  fun x => inferInstanceAs (Decidable (dist1 x c ≤ r))

instance (c : Site d) (r : ℤ) : DecidablePred (· ∈ sphere c r) :=
  fun x => inferInstanceAs (Decidable (dist1 x c = r))

theorem norm1_nonneg (x : Site d) : 0 ≤ norm1 x :=
  Finset.sum_nonneg fun i _ => abs_nonneg (x i)

@[simp] theorem norm1_zero : norm1 (0 : Site d) = 0 := by
  simp [norm1]

theorem norm1_eq_zero_iff (x : Site d) : norm1 x = 0 ↔ x = 0 := by
  rw [norm1, Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (x i)]
  simp [funext_iff]

@[simp] theorem norm1_neg (x : Site d) : norm1 (-x) = norm1 x := by
  simp [norm1]

theorem norm1_add_le (x y : Site d) : norm1 (x + y) ≤ norm1 x + norm1 y := by
  rw [norm1, norm1, norm1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (x i) (y i)

theorem norm1_smul (t : ℤ) (x : Site d) : norm1 (t • x) = |t| * norm1 x := by
  simp [norm1, abs_mul, Finset.mul_sum]

theorem abs_apply_le_norm1 (x : Site d) (i : Fin d) : |x i| ≤ norm1 x :=
  Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

theorem norm1_update (x : Site d) (j : Fin d) (t : ℤ) :
    norm1 (Function.update x j t) = norm1 x - |x j| + |t| := by
  have h1 := Finset.add_sum_erase Finset.univ (fun i => |Function.update x j t i|)
    (Finset.mem_univ j)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => |x i|) (Finset.mem_univ j)
  have h3 : ∑ i ∈ Finset.univ.erase j, |Function.update x j t i| =
      ∑ i ∈ Finset.univ.erase j, |x i| :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self] at h1
  rw [norm1, norm1]
  linarith

theorem dist1_comm (x y : Site d) : dist1 x y = dist1 y x := by
  rw [dist1, dist1, ← neg_sub, norm1_neg]

@[simp] theorem dist1_self (x : Site d) : dist1 x x = 0 := by
  simp [dist1]

theorem dist1_nonneg (x y : Site d) : 0 ≤ dist1 x y :=
  norm1_nonneg _

theorem dist1_eq_zero_iff (x y : Site d) : dist1 x y = 0 ↔ x = y := by
  rw [dist1, norm1_eq_zero_iff, sub_eq_zero]

theorem dist1_triangle (x y z : Site d) : dist1 x z ≤ dist1 x y + dist1 y z := by
  have h := norm1_add_le (x - y) (y - z)
  rwa [sub_add_sub_cancel] at h

@[simp] theorem dist1_add_right (x y v : Site d) : dist1 (x + v) (y + v) = dist1 x y := by
  simp [dist1]

@[simp] theorem dist1_zero_right (x : Site d) : dist1 x 0 = norm1 x := by
  simp [dist1]

theorem dist1_update_left (x y : Site d) (j : Fin d) (t : ℤ) :
    dist1 (Function.update x j t) y = dist1 x y - |x j - y j| + |t - y j| := by
  have h : Function.update x j t - y = Function.update (x - y) j (t - y j) := by
    ext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  rw [dist1, h, norm1_update, dist1]
  simp

theorem abs_norm1_sub_le_dist1 (x y : Site d) : |norm1 x - norm1 y| ≤ dist1 x y := by
  have h1 := norm1_add_le (x - y) y
  have h2 := norm1_add_le (y - x) x
  rw [sub_add_cancel] at h1 h2
  have h3 : norm1 (y - x) = dist1 x y := by rw [dist1, ← norm1_neg, neg_sub]
  rw [abs_le]
  constructor <;> linarith [show norm1 (x - y) = dist1 x y from rfl]

theorem abs_sub_apply_le_dist1 (x y : Site d) (i : Fin d) : |x i - y i| ≤ dist1 x y :=
  abs_apply_le_norm1 (x - y) i

/-! ### Unit vectors and `e1` -/

private theorem norm1_single (i : Fin d) (s : ℤ) : norm1 (Pi.single i s : Site d) = |s| := by
  have h : (Pi.single i s : Site d) = Function.update (0 : Site d) i s := rfl
  rw [h, norm1_update]
  simp

theorem isUnitVec_single (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    IsUnitVec (Pi.single i s : Site d) := by
  rw [IsUnitVec, norm1_single]
  rcases hs with rfl | rfl <;> simp

theorem isUnitVec_iff (u : Site d) :
    IsUnitVec u ↔ ∃ (i : Fin d) (s : ℤ), (s = 1 ∨ s = -1) ∧ u = Pi.single i s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hc
      push Not at hc
      have : u = 0 := funext hc
      rw [IsUnitVec, this, norm1_zero] at h
      exact zero_ne_one h
    have h1 := Finset.add_sum_erase Finset.univ (fun j => |u j|) (Finset.mem_univ i)
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, |u j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg (u j)
    have hui : 1 ≤ |u i| := Int.one_le_abs hi
    rw [IsUnitVec, norm1] at h
    have hui1 : |u i| = 1 := by linarith
    have hrest0 : ∑ j ∈ Finset.univ.erase i, |u j| = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg (u j)] at hrest0
    refine ⟨i, u i, (abs_eq zero_le_one).mp hui1, ?_⟩
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Pi.single_eq_of_ne hj]
      exact abs_eq_zero.mp (hrest0 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  · rintro ⟨i, s, hs, rfl⟩
    exact isUnitVec_single i hs

theorem IsUnitVec.neg {u : Site d} (h : IsUnitVec u) : IsUnitVec (-u) := by
  rwa [IsUnitVec, norm1_neg]

theorem add_single_eq_update (x : Site d) (i : Fin d) (s : ℤ) :
    x + Pi.single i s = Function.update x i (x i + s) := by
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h, Function.update_of_ne h]

theorem e1_eq_single (hd : 1 ≤ d) : (e1 : Site d) = Pi.single ⟨0, by omega⟩ 1 := by
  ext j
  simp [e1, Pi.single_apply, Fin.ext_iff]

theorem norm1_smul_e1 (hd : 1 ≤ d) (m : ℤ) : norm1 (m • (e1 : Site d)) = |m| := by
  rw [norm1_smul, e1_eq_single hd, norm1_single]
  simp

/-! ### Adjacency -/

theorem adj_comm {x y : Site d} : Adj x y ↔ Adj y x := by
  rw [Adj, Adj, dist1_comm]

theorem adj_irrefl (x : Site d) : ¬ Adj x x := by
  simp [Adj]

theorem adj_iff_exists_unitVec (x y : Site d) : Adj x y ↔ ∃ u, IsUnitVec u ∧ y = x + u := by
  constructor
  · intro h
    refine ⟨y - x, ?_, (add_sub_cancel x y).symm⟩
    rwa [Adj, dist1_comm] at h
  · rintro ⟨u, hu, rfl⟩
    rw [Adj, dist1_comm, dist1, add_sub_cancel_left]
    exact hu

@[simp] theorem adj_add_right (x y v : Site d) : Adj (x + v) (y + v) ↔ Adj x y := by
  rw [Adj, Adj, dist1_add_right]

/-- Adjacent sites lie in consecutive layers. -/
theorem adj_layer {x y : Site d} (h : Adj x y) (c : Site d) :
    dist1 y c = dist1 x c + 1 ∨ dist1 y c = dist1 x c - 1 := by
  obtain ⟨u, hu, rfl⟩ := (adj_iff_exists_unitVec x y).mp h
  obtain ⟨i, s, hs, rfl⟩ := (isUnitVec_iff u).mp hu
  rw [add_single_eq_update, dist1_update_left]
  rcases hs with rfl | rfl
  · rcases abs_cases (x i + 1 - c i) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (x i - c i) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  · rcases abs_cases (x i + -1 - c i) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (x i - c i) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem adj_mem_ball_succ {x y c : Site d} {r : ℤ} (hx : x ∈ ball c r) (h : Adj x y) :
    y ∈ ball c (r + 1) := by
  rw [mem_ball] at hx ⊢
  rcases adj_layer h c with h1 | h1 <;> linarith

/-- The `2d` neighbours of a site. -/
def nbrs (x : Site d) : Finset (Site d) :=
  (Finset.univ ×ˢ ({1, -1} : Finset ℤ)).image (fun p => x + Pi.single p.1 p.2)

theorem mem_nbrs {x y : Site d} : y ∈ nbrs x ↔ Adj x y := by
  rw [nbrs, Finset.mem_image, adj_iff_exists_unitVec]
  constructor
  · rintro ⟨⟨i, s⟩, hp, rfl⟩
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hp
    exact ⟨_, isUnitVec_single i hp, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, s, hs, rfl⟩ := (isUnitVec_iff u).mp hu
    exact ⟨(i, s), by simpa using hs, rfl⟩

theorem card_nbrs (x : Site d) : (nbrs x).card = 2 * d := by
  rw [nbrs, Finset.card_image_of_injOn]
  · simp [Finset.card_product, mul_comm]
  · rintro ⟨i, s⟩ hp ⟨j, t⟩ hq heq
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, true_and,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp hq
    have h : (Pi.single i s : Site d) = Pi.single j t := add_left_cancel heq
    have hs0 : s ≠ 0 := by rcases hp with rfl | rfl <;> norm_num
    have hij : i = j := by
      by_contra hij
      have := congrFun h i
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
      exact hs0 this
    subst hij
    have := congrFun h i
    rw [Pi.single_eq_same, Pi.single_eq_same] at this
    rw [this]

/-! ### Balls -/

theorem ball_mono {c : Site d} {r s : ℤ} (h : r ≤ s) : ball c r ⊆ ball c s := by
  intro x hx
  rw [mem_ball] at hx ⊢
  linarith

theorem ball_finite (c : Site d) (r : ℤ) : (ball c r).Finite := by
  refine (Set.Finite.pi fun i => Set.finite_Icc (c i - r) (c i + r)).subset ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have h1 := abs_sub_apply_le_dist1 x c i
  have h2 : dist1 x c ≤ r := hx
  rw [abs_le] at h1
  constructor <;> linarith

theorem mem_translate {A : Set (Site d)} {v y : Site d} : y ∈ translate A v ↔ y - v ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨y - v, h, sub_add_cancel y v⟩

/-! ### Walks and paths -/

private theorem isPath_singleton (x : Site d) : IsPath [x] :=
  ⟨⟨List.cons_ne_nil x [], List.isChain_singleton x⟩, List.nodup_singleton x⟩

/-- Every walk contains a path with the same end sites. -/
private theorem IsWalk.exists_path_subset {P : List (Site d)} (hP : IsWalk P) {x y : Site d}
    (hx : P.head? = some x) (hy : P.getLast? = some y) :
    ∃ Q : List (Site d), IsPath Q ∧ Q.head? = some x ∧ Q.getLast? = some y ∧ ∀ z ∈ Q, z ∈ P := by
  induction P generalizing x with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst hy
      exact ⟨[a], isPath_singleton a, rfl, rfl, fun z hz => hz⟩
    | cons b l =>
      have hab : Adj a b := hP.2.rel
      have hW : IsWalk (b :: l) := ⟨List.cons_ne_nil b l, hP.2.of_cons⟩
      rw [List.getLast?_cons_cons] at hy
      obtain ⟨Q, hQ, hQx, hQy, hQP⟩ := ih hW rfl hy
      by_cases haQ : a ∈ Q
      · obtain ⟨s, t, rfl⟩ := List.append_of_mem haQ
        refine ⟨a :: t, ⟨⟨List.cons_ne_nil a t, hQ.1.2.right_of_append⟩,
          hQ.2.sublist (List.sublist_append_right s _)⟩, rfl, ?_, ?_⟩
        · rwa [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil a t)] at hQy
        · intro z hz
          exact List.mem_cons_of_mem a (hQP z (List.mem_append_right s hz))
      · obtain ⟨t, rfl⟩ : ∃ t, Q = b :: t := by
          cases Q with
          | nil => simp at hQx
          | cons q t =>
            simp only [List.head?_cons, Option.some.injEq] at hQx
            exact ⟨t, by rw [hQx]⟩
        refine ⟨a :: b :: t, ⟨⟨List.cons_ne_nil _ _, List.IsChain.cons_cons hab hQ.1.2⟩,
          List.nodup_cons.mpr ⟨haQ, hQ.2⟩⟩, rfl, ?_, ?_⟩
        · rwa [List.getLast?_cons_cons]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (hQP z hz)

theorem containsPath_iff_walk (A : Set (Site d)) (x y : Site d) :
    ContainsPath A x y ↔
      ∃ P : List (Site d), IsWalk P ∧ P.head? = some x ∧ P.getLast? = some y ∧ ∀ z ∈ P, z ∈ A := by
  constructor
  · rintro ⟨P, hP, hx, hy, hA⟩
    exact ⟨P, hP.1, hx, hy, hA⟩
  · rintro ⟨P, hP, hx, hy, hA⟩
    obtain ⟨Q, hQ, hQx, hQy, hQP⟩ := hP.exists_path_subset hx hy
    exact ⟨Q, hQ, hQx, hQy, fun z hz => hA z (hQP z hz)⟩

theorem ContainsPath.mem_left {A : Set (Site d)} {x y : Site d} (h : ContainsPath A x y) : x ∈ A := by
  obtain ⟨P, -, hx, -, hA⟩ := h
  exact hA x (List.mem_of_mem_head? hx)

theorem ContainsPath.mem_right {A : Set (Site d)} {x y : Site d} (h : ContainsPath A x y) :
    y ∈ A := by
  obtain ⟨P, -, -, hy, hA⟩ := h
  exact hA y (List.mem_of_mem_getLast? hy)

theorem containsPath_refl {A : Set (Site d)} {x : Site d} (hx : x ∈ A) : ContainsPath A x x :=
  ⟨[x], isPath_singleton x, rfl, rfl, fun z hz => by rw [List.mem_singleton.mp hz]; exact hx⟩

theorem ContainsPath.symm {A : Set (Site d)} {x y : Site d} (h : ContainsPath A x y) :
    ContainsPath A y x := by
  obtain ⟨P, hP, hx, hy, hA⟩ := h
  refine ⟨P.reverse, ⟨⟨by simpa using hP.1.1, ?_⟩, List.nodup_reverse.mpr hP.2⟩,
    by simpa using hy, by simpa using hx, fun z hz => hA z (List.mem_reverse.mp hz)⟩
  rw [List.isChain_reverse]
  exact hP.1.2.imp fun a b h => adj_comm.mp h

theorem ContainsPath.trans {A : Set (Site d)} {x y z : Site d} (h₁ : ContainsPath A x y)
    (h₂ : ContainsPath A y z) : ContainsPath A x z := by
  obtain ⟨P, hP, hx, hy, hA⟩ := h₁
  obtain ⟨Q, hQ, hy', hz, hB⟩ := h₂
  obtain ⟨t, rfl⟩ : ∃ t, Q = y :: t := by
    cases Q with
    | nil => simp at hy'
    | cons q t =>
      simp only [List.head?_cons, Option.some.injEq] at hy'
      exact ⟨t, by rw [hy']⟩
  rw [containsPath_iff_walk]
  refine ⟨P ++ t, ⟨by simp [hP.1.1], hP.1.2.append hQ.1.2.of_cons ?_⟩, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [hy, Option.mem_def, Option.some.injEq] at ha
    subst ha
    exact hQ.1.2.rel_head? hb
  · rw [List.head?_append, hx]
    rfl
  · cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hz
      subst hz
      simpa using hy
    | cons b t =>
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rwa [List.getLast?_cons_cons] at hz
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hA w h
    · exact hB w (List.mem_cons_of_mem y h)

theorem ContainsPath.mono {A B : Set (Site d)} {x y : Site d} (hAB : A ⊆ B)
    (h : ContainsPath A x y) : ContainsPath B x y := by
  obtain ⟨P, hP, hx, hy, hA⟩ := h
  exact ⟨P, hP, hx, hy, fun z hz => hAB (hA z hz)⟩

theorem containsPath_of_adj {A : Set (Site d)} {x y : Site d} (hx : x ∈ A) (hy : y ∈ A)
    (h : Adj x y) : ContainsPath A x y := by
  have hxy : x ≠ y := by
    rintro rfl
    exact adj_irrefl x h
  refine ⟨[x, y], ⟨⟨by simp, List.isChain_pair.mpr h⟩, by simp [hxy]⟩, rfl, rfl, ?_⟩
  intro z hz
  rcases List.mem_pair.mp hz with rfl | rfl
  · exact hx
  · exact hy

private theorem ContainsPath.translate_add {A : Set (Site d)} {x y : Site d}
    (h : ContainsPath A x y) (v : Site d) : ContainsPath (translate A v) (x + v) (y + v) := by
  obtain ⟨P, hP, hx, hy, hA⟩ := h
  refine ⟨P.map (· + v), ⟨⟨by simpa using hP.1.1, ?_⟩, hP.2.map (add_left_injective v)⟩,
    by simp [hx], by simp [hy], ?_⟩
  · rw [List.isChain_map]
    exact hP.1.2.imp fun a b h => (adj_add_right a b v).mpr h
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact ⟨w, hA w hw, rfl⟩

theorem containsPath_translate {A : Set (Site d)} {x y : Site d} (v : Site d) :
    ContainsPath (translate A v) (x + v) (y + v) ↔ ContainsPath A x y := by
  constructor
  · intro h
    have h' := h.translate_add (-v)
    have hA : translate (translate A v) (-v) = A := by
      ext z
      simp [mem_translate]
    rwa [hA, add_neg_cancel_right, add_neg_cancel_right] at h'
  · intro h
    exact h.translate_add v

/-- Cutting a path short along a chord `P[i] ~ P[j]`, `i < j`, gives a path `P[0..i] ++ P[j..]`
with the same end sites. -/
private theorem IsPath.shortcut {P : List (Site d)} (hP : IsPath P) {i j : ℕ} (hj : j < P.length)
    (hij : i < j) (hadj : Adj (P[i]'(hij.trans hj)) P[j]) :
    IsPath (P.take (i + 1) ++ P.drop j) ∧ (P.take (i + 1) ++ P.drop j).head? = P.head? ∧
      (P.take (i + 1) ++ P.drop j).getLast? = P.getLast? ∧
      (P.take (i + 1) ++ P.drop j).length = i + 1 + (P.length - j) ∧
      ∀ z ∈ P.take (i + 1) ++ P.drop j, z ∈ P := by
  have hi : i < P.length := hij.trans hj
  have hdrop : P.drop j ≠ [] := by simp; omega
  refine ⟨⟨⟨by simp [hdrop], (hP.1.2.take (i + 1)).append (hP.1.2.drop j) ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [List.getLast?_take] at ha
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.getElem?_eq_getElem hi,
      Option.some_or, Option.mem_def, Option.some.injEq] at ha
    rw [List.head?_drop, List.getElem?_eq_getElem hj, Option.mem_def, Option.some.injEq] at hb
    subst ha hb
    exact hadj
  · have hsub : List.Sublist (P.take (i + 1) ++ P.drop j) P := by
      conv_rhs => rw [← List.take_append_drop j P]
      exact (List.take_sublist_take_left (by omega)).append (List.Sublist.refl _)
    exact hP.2.sublist hsub
  · rw [List.head?_append, List.head?_take]
    rcases P with _ | ⟨a, l⟩
    · simp at hi
    · simp
  · rw [List.getLast?_append_of_ne_nil _ hdrop, List.getLast?_drop]
    simp only [ite_eq_right_iff]
    omega
  · simp
    omega
  · intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact List.mem_of_mem_take h
    · exact List.mem_of_mem_drop h

/-- A set containing a path from `x` to `y` contains an induced path from `x` to `y`
(a shortest one). -/
theorem ContainsPath.exists_induced {A : Set (Site d)} {x y : Site d} (h : ContainsPath A x y) :
    ∃ P : List (Site d), IsInducedPath P ∧ P.head? = some x ∧ P.getLast? = some y ∧
      ∀ z ∈ P, z ∈ A := by
  classical
  have hex : ∃ n, ∃ P : List (Site d), IsPath P ∧ P.head? = some x ∧ P.getLast? = some y ∧
      (∀ z ∈ P, z ∈ A) ∧ P.length = n := by
    obtain ⟨P, hP, hx, hy, hA⟩ := h
    exact ⟨P.length, P, hP, hx, hy, hA, rfl⟩
  obtain ⟨P, hP, hx, hy, hA, hlen⟩ := Nat.find_spec hex
  refine ⟨P, ⟨hP, ?_⟩, hx, hy, hA⟩
  intro i j hi hj hij hadj
  obtain ⟨hQ, hQx, hQy, hQlen, hQP⟩ := hP.shortcut hj (by omega) hadj
  have hmin := Nat.find_min' hex ⟨_, hQ, hQx.trans hx, hQy.trans hy,
    fun z hz => hA z (hQP z hz), rfl⟩
  omega

/-- Discrete intermediate value property: a walk passes through every intermediate layer. -/
theorem IsWalk.exists_layer {P : List (Site d)} (hP : IsWalk P) {x y : Site d}
    (hx : P.head? = some x) (hy : P.getLast? = some y) (c : Site d) {s : ℤ}
    (hs : min (dist1 x c) (dist1 y c) ≤ s ∧ s ≤ max (dist1 x c) (dist1 y c)) :
    ∃ z ∈ P, dist1 z c = s := by
  induction P generalizing x with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    by_cases has : dist1 a c = s
    · exact ⟨a, List.mem_cons_self, has⟩
    cases l with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hy
      subst hy
      simp only [min_self, max_self] at hs
      exact absurd (le_antisymm hs.1 hs.2) has
    | cons b l =>
      have hab : Adj a b := hP.2.rel
      have hW : IsWalk (b :: l) := ⟨List.cons_ne_nil b l, hP.2.of_cons⟩
      rw [List.getLast?_cons_cons] at hy
      have hlayer := adj_layer hab c
      obtain ⟨z, hz, hzs⟩ := ih hW rfl hy (by omega)
      exact ⟨z, List.mem_cons_of_mem a hz, hzs⟩

theorem siteConnected_singleton (x : Site d) : SiteConnected ({x} : Set (Site d)) := by
  intro a ha b hb
  rw [Set.mem_singleton_iff] at ha hb
  subst ha hb
  exact containsPath_refl rfl

theorem SiteConnected.union {A B : Set (Site d)} (hA : SiteConnected A) (hB : SiteConnected B)
    (h : (A ∩ B).Nonempty) : SiteConnected (A ∪ B) := by
  obtain ⟨z, hzA, hzB⟩ := h
  have key : ∀ x ∈ A ∪ B, ContainsPath (A ∪ B) x z := by
    rintro x (hx | hx)
    · exact (hA x hx z hzA).mono Set.subset_union_left
    · exact (hB x hx z hzB).mono Set.subset_union_right
  intro x hx y hy
  exact (key x hx).trans (key y hy).symm

theorem IsWalk.siteConnected {P : List (Site d)} (hP : IsWalk P) :
    SiteConnected {x | x ∈ P} := by
  -- every site of a walk is joined inside the walk to its first site
  have key : ∀ (P : List (Site d)), IsWalk P → ∀ a, P.head? = some a → ∀ x ∈ P,
      ContainsPath {z | z ∈ P} a x := by
    intro P
    induction P with
    | nil => exact fun h => absurd rfl h.1
    | cons b l ih =>
      intro hW a ha x hx
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst ha
      rcases List.mem_cons.mp hx with rfl | hx
      · exact containsPath_refl List.mem_cons_self
      · cases l with
        | nil => simp at hx
        | cons c l =>
          have hbc : Adj b c := hW.2.rel
          have hW' : IsWalk (c :: l) := ⟨List.cons_ne_nil c l, hW.2.of_cons⟩
          have h1 : ContainsPath {z | z ∈ b :: c :: l} c x :=
            (ih hW' c rfl x hx).mono fun z hz => List.mem_cons_of_mem b hz
          exact (containsPath_of_adj List.mem_cons_self
            (List.mem_cons_of_mem b List.mem_cons_self) hbc).trans h1
  obtain ⟨a, ha⟩ : ∃ a, P.head? = some a := by
    cases P with
    | nil => exact absurd rfl hP.1
    | cons a l => exact ⟨a, rfl⟩
  intro x hx y hy
  exact (key P hP a ha x hx).symm.trans (key P hP a ha y hy)

/-- A monotone lattice path: from `x` to `y` there is a path of length `|x - y|` whose sites lie
coordinatewise between `x` and `y`. -/
theorem exists_monotone_path (x y : Site d) :
    ∃ P : List (Site d), IsPath P ∧ P.head? = some x ∧ P.getLast? = some y ∧
      (P.length : ℤ) = dist1 x y + 1 ∧
      ∀ z ∈ P, ∀ i, min (x i) (y i) ≤ z i ∧ z i ≤ max (x i) (y i) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, dist1 x y = n :=
    ⟨(dist1 x y).toNat, (Int.toNat_of_nonneg (dist1_nonneg x y)).symm⟩
  induction n generalizing x with
  | zero =>
    have hxy : x = y := (dist1_eq_zero_iff x y).mp (by simpa using hn)
    subst hxy
    refine ⟨[x], isPath_singleton x, rfl, rfl, by simp, ?_⟩
    intro z hz i
    rw [List.mem_singleton.mp hz]
    simp
  | succ n ih =>
    have hxy : x ≠ y := by
      rintro rfl
      simp at hn
      omega
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc
      push Not at hc
      exact hxy (funext hc)
    -- one step from `x` towards `y` in coordinate `i`
    obtain ⟨s, hs1, hs2, hs3⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ |x i + s - y i| = |x i - y i| - 1 ∧
        ∀ t, min (x i + s) (y i) ≤ t → t ≤ max (x i + s) (y i) →
          min (x i) (y i) ≤ t ∧ t ≤ max (x i) (y i) ∧ t ≠ x i := by
      rcases lt_or_gt_of_ne hi with h | h
      · refine ⟨1, Or.inl rfl, ?_, ?_⟩
        · rw [abs_of_nonpos (by omega), abs_of_neg (by omega)]
          ring
        · intro t h1 h2
          rw [min_eq_left (by omega)] at h1
          rw [max_eq_right (by omega)] at h2
          rw [min_eq_left h.le, max_eq_right h.le]
          omega
      · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
        · rw [abs_of_nonneg (by omega), abs_of_pos (by omega)]
          ring
        · intro t h1 h2
          rw [min_eq_right (by omega)] at h1
          rw [max_eq_left (by omega)] at h2
          rw [min_eq_right h.le, max_eq_left h.le]
          omega
    obtain ⟨x', hx'⟩ : ∃ x', x' = x + Pi.single i s := ⟨_, rfl⟩
    have hadj : Adj x x' := (adj_iff_exists_unitVec x x').mpr ⟨_, isUnitVec_single i hs1, hx'⟩
    have hx'i : x' i = x i + s := by simp [hx']
    have hx'j : ∀ j, j ≠ i → x' j = x j := fun j hj => by simp [hx', Pi.single_eq_of_ne hj]
    have hdist : dist1 x' y = n := by
      rw [hx', add_single_eq_update, dist1_update_left, hs2, hn]
      push_cast
      ring
    obtain ⟨P', hP', hh', hl', hlen', hbd'⟩ := ih x' hdist
    obtain ⟨t, rfl⟩ : ∃ t, P' = x' :: t := by
      cases P' with
      | nil => simp at hh'
      | cons q t =>
        simp only [List.head?_cons, Option.some.injEq] at hh'
        exact ⟨t, by rw [hh']⟩
    have hxnot : x ∉ x' :: t := by
      intro hx
      obtain ⟨h1, h2⟩ := hbd' x hx i
      rw [hx'i] at h1 h2
      exact (hs3 _ h1 h2).2.2 rfl
    refine ⟨x :: x' :: t, ⟨⟨List.cons_ne_nil _ _, List.IsChain.cons_cons hadj hP'.1.2⟩,
      List.nodup_cons.mpr ⟨hxnot, hP'.2⟩⟩, rfl, ?_, ?_, ?_⟩
    · rwa [List.getLast?_cons_cons]
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen' ⊢
      rw [hn]
      rw [hdist] at hlen'
      push_cast
      linarith
    · intro z hz j
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨min_le_left _ _, le_max_left _ _⟩
      · obtain ⟨h1, h2⟩ := hbd' z hz j
        by_cases hj : j = i
        · subst hj
          rw [hx'i] at h1 h2
          obtain ⟨h3, h4, -⟩ := hs3 _ h1 h2
          exact ⟨h3, h4⟩
        · rw [hx'j j hj] at h1 h2
          exact ⟨h1, h2⟩

/-- Balls are connected. -/
theorem siteConnected_ball (c : Site d) (r : ℤ) : SiteConnected (ball c r) := by
  have key : ∀ x ∈ ball c r, ContainsPath (ball c r) x c := by
    intro x hx
    obtain ⟨P, hP, hx', hc, -, hbd⟩ := exists_monotone_path x c
    refine ⟨P, hP, hx', hc, fun z hz => ?_⟩
    rw [mem_ball] at hx ⊢
    refine le_trans ?_ hx
    unfold dist1 norm1
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h1, h2⟩ := hbd z hz i
    simp only [Pi.sub_apply]
    rcases le_total (x i) (c i) with h | h
    · rw [min_eq_left h] at h1
      rw [max_eq_right h] at h2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [min_eq_right h] at h1
      rw [max_eq_left h] at h2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  intro x hx y hy
  exact (key x hx).trans (key y hy).symm

end BBR
