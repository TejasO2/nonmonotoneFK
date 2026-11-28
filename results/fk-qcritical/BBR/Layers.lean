import BBR.Basic

/-!
# Lemma 2.3: two consecutive layers

We walk from any site `y` of `A = (S_n ∪ S_{n+1}) ∩ {x : x_i > s}` to `n e_i` inside `A`, changing
one coordinate by one unit at each step, as in the proof of the paper:

* while `y_i < 0`: from `S_n` move a coordinate `y_j`, `j ≠ i`, one unit away from `0`; from
  `S_{n+1}` raise `y_i` by one;
* while `y_i ≥ 0`: from `(n+1) e_i` step to `n e_i`; from another site of `S_{n+1}` move a nonzero
  coordinate `y_j`, `j ≠ i`, one unit towards `0`; from `S_n` raise `y_i` by one.

The coordinate `y_i` never decreases, except in the final step from `(n+1) e_i` to `n e_i`, so the
walk stays in `A`. Termination is controlled by the potential `2 (n + 1 - y_i) + ε(y)`, where
`ε(y) = 1` if `y_i < 0` and `|y| = n`, or `y_i ≥ 0` and `|y| = n + 1`, and `ε(y) = 0` otherwise. It
drops at every step except the final one.
-/

namespace BBR

variable {d : ℕ}

/-- Changing one coordinate by `±1` gives an adjacent site. -/
private theorem adj_update_add_unit (y : Site d) (j : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Adj y (Function.update y j (y j + σ)) := by
  rw [← add_single_eq_update]
  exact (adj_iff_exists_unitVec _ _).2 ⟨_, isUnitVec_single j hσ, rfl⟩

/-- If from every site of `A` other than `t` one can step inside `A` either to `t` or to a site of
smaller potential, then `A` contains a path from each of its sites to `t`. -/
private theorem containsPath_of_descent {A : Set (Site d)} {t : Site d} (Φ : Site d → ℕ)
    (hstep : ∀ y ∈ A, y ≠ t → ∃ y' ∈ A, Adj y y' ∧ (y' = t ∨ Φ y' < Φ y)) :
    ∀ y ∈ A, ContainsPath A y t := by
  suffices H : ∀ k : ℕ, ∀ y ∈ A, Φ y < k → ContainsPath A y t from
    fun y hy => H _ y hy (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => exact fun y _ hk => absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    intro y hy hk
    by_cases hyt : y = t
    · subst hyt
      exact containsPath_refl hy
    obtain ⟨y', hy', hadj, h⟩ := hstep y hy hyt
    rcases h with h | h
    · subst h
      exact containsPath_of_adj hy hy' hadj
    · exact (containsPath_of_adj hy hy' hadj).trans (ih y' hy' (by omega))

/-- The potential controlling the walk from a site of `S_n ∪ S_{n+1}` to `n e_i`. -/
private def layerPot (n : ℤ) (i : Fin d) (y : Site d) : ℕ :=
  Int.toNat (2 * (n + 1 - y i) +
    if y i < 0 then (if norm1 y = n then 1 else 0) else (if norm1 y = n + 1 then 1 else 0))

/-- One step of the walk: from any site `y` of `A` one can step inside `A` either to `n e_i` or to a
site of smaller potential. -/
private theorem two_layers_step (hd : 2 ≤ d) (n : ℤ) (hn : 1 ≤ n) (i : Fin d) (s : ℤ)
    (hs : s < n) (y : Site d) (hy : (norm1 y = n ∨ norm1 y = n + 1) ∧ s < y i) :
    ∃ y' ∈ {x : Site d | (norm1 x = n ∨ norm1 x = n + 1) ∧ s < x i}, Adj y y' ∧
      (y' = n • (Pi.single i 1 : Site d) ∨ layerPot n i y' < layerPot n i y) := by
  obtain ⟨hyn, hys⟩ := hy
  have hyi : |y i| ≤ norm1 y := abs_apply_le_norm1 y i
  rcases lt_or_ge (y i) 0 with hneg | hnonneg
  · -- `y_i < 0`
    have hai : |y i| = -y i := abs_of_neg hneg
    rcases hyn with hyn | hyn
    · -- `|y| = n`: move a coordinate `y_j`, `j ≠ i`, one unit away from `0`
      obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega) i
      obtain ⟨σ, hσ, hσabs⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ |y j + σ| = |y j| + 1 := by
        rcases le_or_gt 0 (y j) with h | h
        · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h, abs_of_nonneg (by omega)]⟩
        · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h, abs_of_neg (by omega)]; ring⟩
      have h1 : Function.update y j (y j + σ) i = y i := Function.update_of_ne hji.symm _ _
      have h2 := norm1_update y j (y j + σ)
      refine ⟨Function.update y j (y j + σ), ⟨Or.inr (by omega), by omega⟩,
        adj_update_add_unit y j hσ, Or.inr ?_⟩
      unfold layerPot
      split_ifs <;> omega
    · -- `|y| = n + 1`: raise `y_i` by one
      have h1 : Function.update y i (y i + 1) i = y i + 1 := Function.update_self _ _ _
      have h2 := norm1_update y i (y i + 1)
      have h3 : |y i + 1| = -(y i + 1) := abs_of_nonpos (by omega)
      refine ⟨Function.update y i (y i + 1), ⟨Or.inl (by omega), by omega⟩,
        adj_update_add_unit y i (Or.inl rfl), Or.inr ?_⟩
      unfold layerPot
      split_ifs <;> omega
  · -- `y_i ≥ 0`
    have hai : |y i| = y i := abs_of_nonneg hnonneg
    rcases hyn with hyn | hyn
    · -- `|y| = n`: raise `y_i` by one
      have h1 : Function.update y i (y i + 1) i = y i + 1 := Function.update_self _ _ _
      have h2 := norm1_update y i (y i + 1)
      have h3 : |y i + 1| = y i + 1 := abs_of_nonneg (by omega)
      refine ⟨Function.update y i (y i + 1), ⟨Or.inr (by omega), by omega⟩,
        adj_update_add_unit y i (Or.inl rfl), Or.inr ?_⟩
      unfold layerPot
      split_ifs <;> omega
    · -- `|y| = n + 1`
      by_cases hex : ∃ j, j ≠ i ∧ y j ≠ 0
      · -- move a nonzero coordinate `y_j`, `j ≠ i`, one unit towards `0`
        obtain ⟨j, hji, hj0⟩ := hex
        obtain ⟨σ, hσ, hσabs⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ |y j + σ| = |y j| - 1 := by
          rcases lt_or_gt_of_ne hj0 with h | h
          · exact ⟨1, Or.inl rfl, by rw [abs_of_neg h, abs_of_nonpos (by omega)]; ring⟩
          · exact ⟨-1, Or.inr rfl, by rw [abs_of_pos h, abs_of_nonneg (by omega)]; ring⟩
        have h1 : Function.update y j (y j + σ) i = y i := Function.update_of_ne hji.symm _ _
        have h2 := norm1_update y j (y j + σ)
        refine ⟨Function.update y j (y j + σ), ⟨Or.inl (by omega), by omega⟩,
          adj_update_add_unit y j hσ, Or.inr ?_⟩
        unfold layerPot
        split_ifs <;> omega
      · -- `y = (n+1) e_i`: step to `n e_i`
        push Not at hex
        have hnorm : norm1 y = |y i| :=
          Finset.sum_eq_single i (fun k _ hk => by simp [hex k hk]) (by simp)
        have heq : n • (Pi.single i 1 : Site d) = Function.update y i (y i + -1) := by
          ext k
          by_cases hk : k = i
          · subst hk
            simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
              Function.update_self]
            omega
          · simp [hk, hex k hk]
        refine ⟨n • (Pi.single i 1 : Site d), ⟨Or.inl ?_, ?_⟩, ?_, Or.inl rfl⟩
        · rw [heq, norm1_update]
          rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ y i + -1)]
          omega
        · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          omega
        · rw [heq]
          exact adj_update_add_unit y i (Or.inr rfl)

/-- **Lemma 2.3.** Let `d ≥ 2`, `n ≥ 1`, `i` a coordinate and `s < n` an integer. Then
`A = (S_n ∪ S_{n+1}) ∩ {x : x_i > s}` contains `n e_i` and is connected. -/
theorem two_layers (hd : 2 ≤ d) (n : ℤ) (hn : 1 ≤ n) (i : Fin d) (s : ℤ) (hs : s < n) :
    n • (Pi.single i 1 : Site d) ∈ {x : Site d | (norm1 x = n ∨ norm1 x = n + 1) ∧ s < x i} ∧
      SiteConnected {x : Site d | (norm1 x = n ∨ norm1 x = n + 1) ∧ s < x i} := by
  have hu : norm1 (Pi.single i 1 : Site d) = 1 := isUnitVec_single i (Or.inl rfl)
  have ht : n • (Pi.single i 1 : Site d) ∈
      {x : Site d | (norm1 x = n ∨ norm1 x = n + 1) ∧ s < x i} := by
    refine ⟨Or.inl ?_, ?_⟩
    · rw [norm1_smul, hu, abs_of_pos (by omega), mul_one]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      exact hs
  have hpath := containsPath_of_descent (layerPot n i)
    (fun y hy _ => two_layers_step hd n hn i s hs y hy)
  exact ⟨ht, fun x hx y hy => (hpath x hx).trans (hpath y hy).symm⟩

/-- **Lemma 2.3**, last assertion: `S_n ∪ S_{n+1}` is connected. -/
theorem two_layers_connected (hd : 2 ≤ d) (n : ℤ) (hn : 1 ≤ n) :
    SiteConnected {x : Site d | norm1 x = n ∨ norm1 x = n + 1} := by
  have hset : {x : Site d | norm1 x = n ∨ norm1 x = n + 1} =
      {x : Site d | (norm1 x = n ∨ norm1 x = n + 1) ∧ -n - 2 < x ⟨0, by omega⟩} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun hx => ⟨hx, ?_⟩, fun hx => hx.1⟩
    have h1 := abs_apply_le_norm1 x ⟨0, by omega⟩
    have h2 := neg_abs_le (x ⟨0, by omega⟩)
    omega
  rw [hset]
  exact (two_layers hd n hn ⟨0, by omega⟩ (-n - 2) (by omega)).2

end BBR
