import BBRAG.Defs

/-!
# Counting sets connected at distance at most two

The number of finite sets of size `n` that contain a given site and are connected for `Adj2` is
at most `(2d(d+1) + 1)^(2n)` (each is the site set of a closed `Adj2`-walk of length `2(n-1)`).

Proof: a finite `Adj2`-connected set `S ∋ x` is grown from `{x}` one site at a time, always adding
a site of `S` at `ℓ¹` distance at most two from the current set; inserting the detour `u → v → u`
into the current closed walk at a visit of `u` adds `v` at the cost of two steps. Hence `S` is the
site set of a walk from `x` with `2(|S| - 1)` steps, each step in the ball `B_2(0)`, which has
`2d(d+1) + 1` sites; and there are at most `|B_2(0)|^m` walks with `m` steps from `x`.
-/

namespace BBR

variable {d : ℕ}

/-! ### The ℓ¹ balls of radius at most two around the origin -/

/-- The ℓ¹ ball `B_r(0)` of `ℤ^d` as a finset. -/
private noncomputable def ballFin (d : ℕ) (r : ℤ) : Finset (Site d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-r) r).filter (fun v => norm1 v ≤ r)

private theorem mem_ballFin {r : ℤ} {v : Site d} : v ∈ ballFin d r ↔ norm1 v ≤ r := by
  unfold ballFin
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  exact abs_le.mp ((abs_apply_le_norm1 v i).trans h)

/-- Prepending a first coordinate. -/
private def consSite (a : ℤ) (w : Site d) : Site (d + 1) := Fin.cons a w

private theorem norm1_succ (v : Site (d + 1)) : norm1 v = |v 0| + norm1 (Fin.tail v) := by
  unfold norm1
  rw [Fin.sum_univ_succ]
  rfl

private theorem mem_image_consSite {r r' : ℤ} {v : Site (d + 1)} (hv : v ∈ ballFin (d + 1) r)
    (a : ℤ) (ha : v 0 = a) (hr : r - |a| ≤ r') : v ∈ (ballFin d r').image (consSite a) := by
  rw [Finset.mem_image]
  refine ⟨Fin.tail v, ?_, ?_⟩
  · rw [mem_ballFin] at hv ⊢
    rw [norm1_succ, ha] at hv
    linarith
  · rw [← ha]
    exact Fin.cons_self_tail v

private theorem card_ballFin_dim_zero (r : ℤ) : (ballFin 0 r).card ≤ 1 :=
  Finset.card_le_one.mpr fun _ _ _ _ => funext fun i => i.elim0

private theorem card_ballFin_zero (d : ℕ) : (ballFin d 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  rw [mem_ballFin] at ha hb
  rw [(norm1_eq_zero_iff a).mp (le_antisymm ha (norm1_nonneg a)),
    (norm1_eq_zero_iff b).mp (le_antisymm hb (norm1_nonneg b))]

private theorem card_ballFin_one : ∀ d : ℕ, (ballFin d 1).card ≤ 2 * d + 1
  | 0 => (card_ballFin_dim_zero 1).trans (by norm_num)
  | d + 1 => by
    have ih := card_ballFin_one d
    have h0 := card_ballFin_zero d
    have hsub : ballFin (d + 1) 1 ⊆ (ballFin d 1).image (consSite 0) ∪
        (ballFin d 0).image (consSite 1) ∪ (ballFin d 0).image (consSite (-1)) := by
      intro v hv
      have h : |v 0| ≤ 1 := (abs_apply_le_norm1 v 0).trans (mem_ballFin.mp hv)
      have hcases : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = -1 := by
        rcases abs_le.mp h with ⟨h1, h2⟩
        omega
      simp only [Finset.mem_union]
      rcases hcases with h | h | h
      · exact Or.inl (Or.inl (mem_image_consSite hv 0 h (by norm_num)))
      · exact Or.inl (Or.inr (mem_image_consSite hv 1 h (by norm_num)))
      · exact Or.inr (mem_image_consSite hv (-1) h (by norm_num))
    calc (ballFin (d + 1) 1).card
        ≤ ((ballFin d 1).image (consSite 0) ∪ (ballFin d 0).image (consSite 1) ∪
            (ballFin d 0).image (consSite (-1))).card := Finset.card_le_card hsub
      _ ≤ (ballFin d 1).card + (ballFin d 0).card + (ballFin d 0).card := by
          refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
          exact (Finset.card_union_le _ _).trans
            (add_le_add Finset.card_image_le Finset.card_image_le)
      _ ≤ 2 * (d + 1) + 1 := by omega

private theorem card_ballFin_two : ∀ d : ℕ, (ballFin d 2).card ≤ 2 * d * (d + 1) + 1
  | 0 => (card_ballFin_dim_zero 2).trans (by norm_num)
  | d + 1 => by
    have ih := card_ballFin_two d
    have h1 := card_ballFin_one d
    have h0 := card_ballFin_zero d
    have hsub : ballFin (d + 1) 2 ⊆ (ballFin d 2).image (consSite 0) ∪
        (ballFin d 1).image (consSite 1) ∪ (ballFin d 1).image (consSite (-1)) ∪
        (ballFin d 0).image (consSite 2) ∪ (ballFin d 0).image (consSite (-2)) := by
      intro v hv
      have h : |v 0| ≤ 2 := (abs_apply_le_norm1 v 0).trans (mem_ballFin.mp hv)
      have hcases : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = -1 ∨ v 0 = 2 ∨ v 0 = -2 := by
        rcases abs_le.mp h with ⟨h1, h2⟩
        omega
      simp only [Finset.mem_union]
      rcases hcases with h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_image_consSite hv 0 h (by norm_num)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_image_consSite hv 1 h (by norm_num)))))
      · exact Or.inl (Or.inl (Or.inr (mem_image_consSite hv (-1) h (by norm_num))))
      · exact Or.inl (Or.inr (mem_image_consSite hv 2 h (by norm_num)))
      · exact Or.inr (mem_image_consSite hv (-2) h (by norm_num))
    calc (ballFin (d + 1) 2).card
        ≤ ((ballFin d 2).image (consSite 0) ∪ (ballFin d 1).image (consSite 1) ∪
            (ballFin d 1).image (consSite (-1)) ∪ (ballFin d 0).image (consSite 2) ∪
            (ballFin d 0).image (consSite (-2))).card := Finset.card_le_card hsub
      _ ≤ (ballFin d 2).card + (ballFin d 1).card + (ballFin d 1).card + (ballFin d 0).card +
            (ballFin d 0).card := by
          refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
          refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
          refine (Finset.card_union_le _ _).trans (add_le_add ?_ Finset.card_image_le)
          exact (Finset.card_union_le _ _).trans
            (add_le_add Finset.card_image_le Finset.card_image_le)
      _ ≤ 2 * (d + 1) * (d + 1 + 1) + 1 := by nlinarith

/-- An `Adj2`-step is a step in `B_2(0)`. -/
private theorem sub_mem_ballFin_of_adj2 {u v : Site d} (h : Adj2 u v) : v - u ∈ ballFin d 2 :=
  mem_ballFin.mpr ((dist1_comm v u).trans_le h.2)

/-! ### Walks with steps in a finite set -/

/-- The walks from `y` with `m` steps, each step in `D`, as lists of sites. -/
private noncomputable def walksFin (D : Finset (Site d)) : ℕ → Site d → Finset (List (Site d))
  | 0, y => {[y]}
  | m + 1, y => D.biUnion fun δ => (walksFin D m (y + δ)).image (List.cons y)

private theorem card_walksFin (D : Finset (Site d)) :
    ∀ (m : ℕ) (y : Site d), (walksFin D m y).card ≤ D.card ^ m
  | 0, y => by simp [walksFin]
  | m + 1, y => by
    rw [walksFin]
    calc (D.biUnion fun δ => (walksFin D m (y + δ)).image (List.cons y)).card
        ≤ ∑ δ ∈ D, ((walksFin D m (y + δ)).image (List.cons y)).card := Finset.card_biUnion_le
      _ ≤ ∑ _δ ∈ D, D.card ^ m :=
          Finset.sum_le_sum fun δ _ => Finset.card_image_le.trans (card_walksFin D m (y + δ))
      _ = D.card ^ (m + 1) := by rw [Finset.sum_const, smul_eq_mul, pow_succ, mul_comm]

private theorem mem_walksFin (D : Finset (Site d)) :
    ∀ (L : List (Site d)) (y : Site d), (y :: L).IsChain (fun a b => b - a ∈ D) →
      y :: L ∈ walksFin D L.length y
  | [], y, _ => by simp [walksFin]
  | z :: L, y, h => by
    rw [List.isChain_cons_cons] at h
    rw [List.length_cons, walksFin, Finset.mem_biUnion]
    refine ⟨z - y, h.1, ?_⟩
    rw [Finset.mem_image]
    refine ⟨z :: L, ?_, rfl⟩
    rw [add_sub_cancel]
    exact mem_walksFin D L z h.2

/-! ### Growing an `Adj2`-connected set along a closed walk -/

/-- A chain that starts in `T` and ends outside `T` has a step from `T` to its complement. -/
private theorem exists_step_out {R : Site d → Site d → Prop} {T : Finset (Site d)} :
    ∀ (P : List (Site d)) (a : Site d), (a :: P).IsChain R → a ∈ T →
      (∀ b ∈ (a :: P).getLast?, b ∉ T) → ∃ u v, v ∈ a :: P ∧ u ∈ T ∧ v ∉ T ∧ R u v
  | [], a, _, ha, hl => absurd ha (hl a (by simp))
  | b :: P, a, hc, ha, hl => by
    rw [List.isChain_cons_cons] at hc
    by_cases hb : b ∈ T
    · obtain ⟨u, v, hv, huT, hvT, huv⟩ := exists_step_out P b hc.2 hb (by simpa using hl)
      exact ⟨u, v, List.mem_cons_of_mem a hv, huT, hvT, huv⟩
    · exact ⟨a, b, by simp, ha, hb, hc.1⟩

/-- If `T ⊊ S` contains `x` and `S` is `Adj2`-connected, some site of `S \ T` is `Adj2`-adjacent
to a site of `T`. -/
private theorem exists_adj2_out {S T : Finset (Site d)} (hS : Conn2 (↑S : Set (Site d)))
    {x : Site d} (hxT : x ∈ T) (hTS : T ⊆ S) (hne : T ≠ S) :
    ∃ u ∈ T, ∃ v ∈ S, v ∉ T ∧ Adj2 u v := by
  obtain ⟨s, hsS, hsT⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
  obtain ⟨P, hh, hl, hc, hP⟩ := hS x (hTS hxT) s hsS
  cases P with
  | nil => simp at hh
  | cons a P =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    obtain ⟨u, v, hv, huT, hvT, huv⟩ := exists_step_out P a hc hxT (by
      intro b hb
      rw [hl, Option.mem_some_iff] at hb
      rw [← hb]
      exact hsT)
    exact ⟨u, huT, v, hP v hv, hvT, huv⟩

/-- Inserting the detour `u → v → u` into a walk at a visit of `u`. -/
private theorem exists_detour {R : Site d → Site d → Prop} {L : List (Site d)} {u v : Site d}
    (hu : u ∈ L) (hc : L.IsChain R) (huv : R u v) (hvu : R v u) :
    ∃ L' : List (Site d), L'.head? = L.head? ∧ L'.IsChain R ∧ (∀ z, z ∈ L' ↔ z = v ∨ z ∈ L) ∧
      L'.length = L.length + 2 := by
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hu
  refine ⟨s ++ u :: v :: u :: t, ?_, ?_, ?_, ?_⟩
  · cases s <;> simp
  · rw [List.isChain_split] at hc ⊢
    exact ⟨hc.1, List.IsChain.cons_cons huv (List.IsChain.cons_cons hvu hc.2)⟩
  · intro z
    simp only [List.mem_append, List.mem_cons]
    tauto
  · simp only [List.length_append, List.length_cons]
    omega

/-- A finite `Adj2`-connected set `S ∋ x` has subsets of every size `k + 1 ≤ |S|` that are the site
sets of walks from `x` with `2k` steps, each step in `B_2(0)`. -/
private theorem exists_walk_of_conn2 {S : Finset (Site d)} (hS : Conn2 (↑S : Set (Site d)))
    {x : Site d} (hx : x ∈ S) :
    ∀ k : ℕ, k + 1 ≤ S.card → ∃ T ⊆ S, T.card = k + 1 ∧ ∃ L : List (Site d),
      L.head? = some x ∧ L.IsChain (fun a b => b - a ∈ ballFin d 2) ∧ (∀ z, z ∈ L ↔ z ∈ T) ∧
      L.length = 2 * k + 1
  | 0, _ => ⟨{x}, by simpa using hx, by simp, [x], rfl, List.isChain_singleton x, by simp, rfl⟩
  | k + 1, hk => by
    obtain ⟨T, hTS, hTc, L, hLh, hLc, hLT, hLl⟩ := exists_walk_of_conn2 hS hx k (by omega)
    have hxT : x ∈ T := (hLT x).mp (List.mem_of_mem_head? hLh)
    have hne : T ≠ S := by
      rintro rfl
      omega
    obtain ⟨u, huT, v, hvS, hvT, huv⟩ := exists_adj2_out hS hxT hTS hne
    obtain ⟨L', h1, h2, h3, h4⟩ := exists_detour ((hLT u).mpr huT) hLc
      (sub_mem_ballFin_of_adj2 huv) (mem_ballFin.mpr huv.2)
    refine ⟨insert v T, Finset.insert_subset hvS hTS, ?_, L', h1.trans hLh, h2, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvT, hTc]
    · intro z
      rw [h3, Finset.mem_insert, hLT]
    · rw [h4, hLl]
      ring

theorem conn2_count (x : Site d) (n : ℕ) :
    ∃ F : Finset (Finset (Site d)),
      (∀ S : Finset (Site d), Conn2 (↑S : Set (Site d)) → x ∈ S → S.card = n → S ∈ F) ∧
      F.card ≤ (2 * d * (d + 1) + 1) ^ (2 * n) := by
  refine ⟨(walksFin (ballFin d 2) (2 * (n - 1)) x).image List.toFinset, ?_, ?_⟩
  · intro S hS hx hn
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
    obtain ⟨T, hTS, hTc, L, hLh, hLc, hLT, hLl⟩ :=
      exists_walk_of_conn2 hS hx (S.card - 1) (by omega)
    have hTS' : T = S := Finset.eq_of_subset_of_card_le hTS (by omega)
    rw [Finset.mem_image]
    cases L with
    | nil => simp at hLh
    | cons a L =>
      simp only [List.head?_cons, Option.some.injEq] at hLh
      rw [hLh] at hLc hLT
      have hlen : L.length = 2 * (n - 1) := by
        simp only [List.length_cons] at hLl
        omega
      refine ⟨x :: L, hlen ▸ mem_walksFin _ L x hLc, ?_⟩
      ext z
      rw [List.mem_toFinset, hLT, hTS']
  · calc ((walksFin (ballFin d 2) (2 * (n - 1)) x).image List.toFinset).card
        ≤ (walksFin (ballFin d 2) (2 * (n - 1)) x).card := Finset.card_image_le
      _ ≤ (ballFin d 2).card ^ (2 * (n - 1)) := card_walksFin _ _ _
      _ ≤ (2 * d * (d + 1) + 1) ^ (2 * (n - 1)) := Nat.pow_le_pow_left (card_ballFin_two d) _
      _ ≤ (2 * d * (d + 1) + 1) ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)

end BBR
