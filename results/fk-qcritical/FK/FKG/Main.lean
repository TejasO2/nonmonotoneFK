/-
Part of the FK formalization campaign (member m8, direction d8).

# The finite-product FKG theorem: main induction

This file proves `FKGstmt n` for every `n` by induction on the number of
coordinates, and then transports the result to an arbitrary finite index type.
-/
import FK.FKG.Basic

set_option linter.style.haveILetI false

namespace FinFKG

open Finset

/-! ### Helper identities for the induction step -/

/-- Splitting a weighted sum over `Fin (n+1) → Bool` into its two slices. -/
lemma sum_cons_mul {n : ℕ} (P f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x, P x * f x = (∑ y : Fin n → Bool, P (Fin.cons (α := fun _ => Bool) false y) *
        f (Fin.cons (α := fun _ => Bool) false y)) +
      ∑ y : Fin n → Bool, P (Fin.cons (α := fun _ => Bool) true y) *
        f (Fin.cons (α := fun _ => Bool) true y) := by
  rw [sum_cons (fun x => P x * f x), Finset.sum_add_distrib]

/-- A slice sum equals the total slice mass times the normalized slice sum. -/
lemma slice_smul {n : ℕ} (P f : (Fin (n + 1) → Bool) → ℝ) (b : Bool) (L : ℝ)
    (hL0 : L ≠ 0) :
    L * (∑ y : Fin n → Bool, (P (Fin.cons (α := fun _ => Bool) b y) / L) *
        f (Fin.cons (α := fun _ => Bool) b y)) =
      ∑ y : Fin n → Bool, P (Fin.cons (α := fun _ => Bool) b y) *
        f (Fin.cons (α := fun _ => Bool) b y) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  calc L * ((P (Fin.cons (α := fun _ => Bool) b y) / L) * f (Fin.cons (α := fun _ => Bool) b y))
      = (P (Fin.cons (α := fun _ => Bool) b y) / L) * L *
          f (Fin.cons (α := fun _ => Bool) b y) := by ring
    _ = P (Fin.cons (α := fun _ => Bool) b y) * f (Fin.cons (α := fun _ => Bool) b y) := by
        rw [div_mul_cancel₀ _ hL0]

/-- The three-factor analogue of `slice_smul`. -/
lemma slice_smul3 {n : ℕ} (P f g : (Fin (n + 1) → Bool) → ℝ) (b : Bool) (L : ℝ)
    (hL0 : L ≠ 0) :
    L * (∑ y : Fin n → Bool, (P (Fin.cons (α := fun _ => Bool) b y) / L) *
        f (Fin.cons (α := fun _ => Bool) b y) * g (Fin.cons (α := fun _ => Bool) b y)) =
      ∑ y : Fin n → Bool, P (Fin.cons (α := fun _ => Bool) b y) *
        f (Fin.cons (α := fun _ => Bool) b y) * g (Fin.cons (α := fun _ => Bool) b y) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  calc L * ((P (Fin.cons (α := fun _ => Bool) b y) / L) * f (Fin.cons (α := fun _ => Bool) b y) *
        g (Fin.cons (α := fun _ => Bool) b y))
      = (P (Fin.cons (α := fun _ => Bool) b y) / L) * L *
          (f (Fin.cons (α := fun _ => Bool) b y) * g (Fin.cons (α := fun _ => Bool) b y)) := by ring
    _ = P (Fin.cons (α := fun _ => Bool) b y) *
          (f (Fin.cons (α := fun _ => Bool) b y) * g (Fin.cons (α := fun _ => Bool) b y)) := by
        rw [div_mul_cancel₀ _ hL0]
    _ = P (Fin.cons (α := fun _ => Bool) b y) * f (Fin.cons (α := fun _ => Bool) b y) *
          g (Fin.cons (α := fun _ => Bool) b y) := by ring

/-- The lattice condition is preserved by multiplication with a positive
constant. -/
lemma LC.const_mul {n : ℕ} {P : (Fin n → Bool) → ℝ} (hP : LC n P) {c : ℝ} (hc : 0 < c) :
    LC n fun x => c * P x := by
  intro x y
  have h := hP x y
  have hc2 : 0 ≤ c * c := mul_nonneg (le_of_lt hc) (le_of_lt hc)
  calc c * P x * (c * P y) = c * c * (P x * P y) := by ring
    _ ≤ c * c * (P (x ⊔ y) * P (x ⊓ y)) := mul_le_mul_of_nonneg_left h hc2
    _ = c * P (x ⊔ y) * (c * P (x ⊓ y)) := by ring

/-! ### The induction step -/

lemma fkg_succ {n : ℕ} (hFKG : FKGstmt n) : FKGstmt (n + 1) := by
  intro P hpos hlc f g hf hg hf0 hg0
  -- slice masses
  set L0 : ℝ := ∑ y : Fin n → Bool, P (Fin.cons (α := fun _ => Bool) false y) with hL0def
  set L1 : ℝ := ∑ y : Fin n → Bool, P (Fin.cons (α := fun _ => Bool) true y) with hL1def
  have hL0pos : 0 < L0 := by
    rw [hL0def]
    exact Finset.sum_pos (fun y _ => hpos _) Finset.univ_nonempty
  have hL1pos : 0 < L1 := by
    rw [hL1def]
    exact Finset.sum_pos (fun y _ => hpos _) Finset.univ_nonempty
  -- normalized slices
  set ν0 : (Fin n → Bool) → ℝ :=
    fun y => P (Fin.cons (α := fun _ => Bool) false y) / L0 with hν0def
  set ν1 : (Fin n → Bool) → ℝ :=
    fun y => P (Fin.cons (α := fun _ => Bool) true y) / L1 with hν1def
  have hν0pos : ∀ y, 0 < ν0 y := fun y => div_pos (hpos _) hL0pos
  have hν1pos : ∀ y, 0 < ν1 y := fun y => div_pos (hpos _) hL1pos
  have hν0sum : ∑ y, ν0 y = 1 := by
    rw [hν0def, ← Finset.sum_div, hL0def]
    exact div_self (ne_of_gt hL0pos)
  have hν1sum : ∑ y, ν1 y = 1 := by
    rw [hν1def, ← Finset.sum_div, hL1def]
    exact div_self (ne_of_gt hL1pos)
  -- slices of the observables
  set f0 : (Fin n → Bool) → ℝ := fun y => f (Fin.cons (α := fun _ => Bool) false y)
    with hf0def
  set f1 : (Fin n → Bool) → ℝ := fun y => f (Fin.cons (α := fun _ => Bool) true y)
    with hf1def
  set g0 : (Fin n → Bool) → ℝ := fun y => g (Fin.cons (α := fun _ => Bool) false y)
    with hg0def
  set g1 : (Fin n → Bool) → ℝ := fun y => g (Fin.cons (α := fun _ => Bool) true y)
    with hg1def
  have hf0mono : Monotone f0 := by
    intro x y hxy
    exact hf (cons_le_cons (by decide) hxy)
  have hf1mono : Monotone f1 := by
    intro x y hxy
    exact hf (cons_le_cons le_rfl hxy)
  have hg0mono : Monotone g0 := by
    intro x y hxy
    exact hg (cons_le_cons (by decide) hxy)
  have hg1mono : Monotone g1 := by
    intro x y hxy
    exact hg (cons_le_cons le_rfl hxy)
  have hf0nn : ∀ y, 0 ≤ f0 y := fun y => hf0 _
  have hf1nn : ∀ y, 0 ≤ f1 y := fun y => hf0 _
  have hg0nn : ∀ y, 0 ≤ g0 y := fun y => hg0 _
  have hg1nn : ∀ y, 0 ≤ g1 y := fun y => hg0 _
  have hf01 : ∀ y, f0 y ≤ f1 y := fun y => hf (cons_mono_false_true y)
  have hg01 : ∀ y, g0 y ≤ g1 y := fun y => hg (cons_mono_false_true y)
  -- lattice condition and MLR for the normalized slices
  have hlc0 : LC n fun y => P (Fin.cons (α := fun _ => Bool) false y) := LC.slice hlc false
  have hlcν0 : LC n ν0 := by
    have h := LC.const_mul hlc0 (c := 1 / L0) (by positivity)
    have hfun : (fun x => (1 / L0) * P (Fin.cons (α := fun _ => Bool) false x)) = ν0 := by
      funext y
      rw [hν0def]
      ring
    rwa [hfun] at h
  have hlcν1 : LC n ν1 := by
    have h := LC.const_mul (LC.slice hlc true) (c := 1 / L1) (by positivity)
    have hfun : (fun x => (1 / L1) * P (Fin.cons (α := fun _ => Bool) true x)) = ν1 := by
      funext y
      rw [hν1def]
      ring
    rwa [hfun] at h
  have hmlrν : ∀ x y, ν0 x * ν1 y ≤ ν1 (x ⊔ y) * ν0 (x ⊓ y) := by
    intro x y
    have h := mlr_LC hlc x y
    have hL0ne : L0 ≠ 0 := ne_of_gt hL0pos
    have hL1ne : L1 ≠ 0 := ne_of_gt hL1pos
    have hpos' : (0:ℝ) < L0 * L1 := mul_pos hL0pos hL1pos
    have e1 : ν0 x * ν1 y * (L0 * L1) =
        P (Fin.cons (α := fun _ => Bool) false x) *
          P (Fin.cons (α := fun _ => Bool) true y) := by
      rw [hν0def, hν1def]
      simp only
      field_simp
    have e2 : ν1 (x ⊔ y) * ν0 (x ⊓ y) * (L0 * L1) =
        P (Fin.cons (α := fun _ => Bool) true (x ⊔ y)) *
          P (Fin.cons (α := fun _ => Bool) false (x ⊓ y)) := by
      rw [hν0def, hν1def]
      simp only
      field_simp
    have key : ν0 x * ν1 y * (L0 * L1) ≤ ν1 (x ⊔ y) * ν0 (x ⊓ y) * (L0 * L1) := by
      rw [e1, e2]
      exact h
    exact le_of_mul_le_mul_right key hpos'
  -- the six slice quantities
  set F0 : ℝ := ∑ y, ν0 y * f0 y with hF0def
  set F1 : ℝ := ∑ y, ν1 y * f1 y with hF1def
  set G0 : ℝ := ∑ y, ν0 y * g0 y with hG0def
  set G1 : ℝ := ∑ y, ν1 y * g1 y with hG1def
  set M0 : ℝ := ∑ y, ν0 y * f0 y * g0 y with hM0def
  set M1 : ℝ := ∑ y, ν1 y * f1 y * g1 y with hM1def
  have hcompf : (∑ y, ν0 y * f1 y) ≤ F1 := by
    have key := comparison hFKG ν0 ν1 hν0pos (fun y => le_of_lt (hν1pos y)) hlcν0 hmlrν
      f1 hf1mono hf1nn
    rw [hν0sum, hν1sum, mul_one, one_mul] at key
    exact key
  have hcompg : (∑ y, ν0 y * g1 y) ≤ G1 := by
    have key := comparison hFKG ν0 ν1 hν0pos (fun y => le_of_lt (hν1pos y)) hlcν0 hmlrν
      g1 hg1mono hg1nn
    rw [hν0sum, hν1sum, mul_one, one_mul] at key
    exact key
  have hF : F0 ≤ F1 := by
    have h1 : F0 ≤ ∑ y, ν0 y * f1 y := by
      rw [hF0def]
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf01 y) (le_of_lt (hν0pos y)))
    exact le_trans h1 hcompf
  have hG : G0 ≤ G1 := by
    have h1 : G0 ≤ ∑ y, ν0 y * g1 y := by
      rw [hG0def]
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hg01 y) (le_of_lt (hν0pos y)))
    exact le_trans h1 hcompg
  have hM0 : F0 * G0 ≤ M0 := by
    have key := hFKG ν0 hν0pos hlcν0 f0 g0 hf0mono hg0mono hf0nn hg0nn
    rw [hν0sum, one_mul] at key
    rw [hF0def, hG0def, hM0def]
    exact key
  have hM1 : F1 * G1 ≤ M1 := by
    have key := hFKG ν1 hν1pos hlcν1 f1 g1 hf1mono hg1mono hf1nn hg1nn
    rw [hν1sum, one_mul] at key
    rw [hF1def, hG1def, hM1def]
    exact key
  -- assemble
  have hstep : L0 * (F0 * G0) + L1 * (F1 * G1) ≤ L0 * M0 + L1 * M1 :=
    add_le_add (mul_le_mul_of_nonneg_left hM0 (le_of_lt hL0pos))
      (mul_le_mul_of_nonneg_left hM1 (le_of_lt hL1pos))
  have hA : ∑ x, P x * f x = L0 * F0 + L1 * F1 := by
    rw [sum_cons_mul]
    rw [slice_smul P f false L0 (ne_of_gt hL0pos),
      slice_smul P f true L1 (ne_of_gt hL1pos)]
  have hB : ∑ x, P x * g x = L0 * G0 + L1 * G1 := by
    rw [sum_cons_mul]
    rw [slice_smul P g false L0 (ne_of_gt hL0pos),
      slice_smul P g true L1 (ne_of_gt hL1pos)]
  have hC0 : (∑ y : Fin n → Bool, (P (Fin.cons (α := fun _ => Bool) false y) *
      f (Fin.cons (α := fun _ => Bool) false y)) * g (Fin.cons (α := fun _ => Bool) false y))
      = L0 * M0 := by
    rw [← slice_smul3 P f g false L0 (ne_of_gt hL0pos), hM0def]
  have hC1 : (∑ y : Fin n → Bool, (P (Fin.cons (α := fun _ => Bool) true y) *
      f (Fin.cons (α := fun _ => Bool) true y)) * g (Fin.cons (α := fun _ => Bool) true y))
      = L1 * M1 := by
    rw [← slice_smul3 P f g true L1 (ne_of_gt hL1pos), hM1def]
  have hC : ∑ x, P x * f x * g x = L0 * M0 + L1 * M1 := by
    rw [sum_cons_mul (fun x => P x * f x) g, hC0, hC1]
  have hZ : ∑ x, P x = L0 + L1 := by
    rw [sum_cons P, Finset.sum_add_distrib, hL0def, hL1def]
  have key := chebyshev_two (le_of_lt hL0pos) (le_of_lt hL1pos) hF hG
  calc (∑ x, P x * f x) * (∑ x, P x * g x)
      = (L0 * F0 + L1 * F1) * (L0 * G0 + L1 * G1) := by rw [hA, hB]
    _ ≤ (L0 + L1) * (L0 * F0 * G0 + L1 * F1 * G1) := key
    _ = (L0 + L1) * (L0 * (F0 * G0) + L1 * (F1 * G1)) := by ring
    _ ≤ (L0 + L1) * (L0 * M0 + L1 * M1) := by
        apply mul_le_mul_of_nonneg_left hstep
        linarith
    _ = (∑ x, P x) * (∑ x, P x * f x * g x) := by rw [hZ, hC]

/-! ### The base case and the main theorem -/

lemma fkg_zero : FKGstmt 0 := by
  intro P hpos hlc f g hf hg hf0 hg0
  have hsub : Subsingleton (Fin 0 → Bool) :=
    ⟨fun a b => by funext i; exact i.elim0⟩
  have := hsub
  haveI := hsub
  have hpt : Nonempty (Fin 0 → Bool) := ⟨fun i => i.elim0⟩
  obtain ⟨x₀⟩ := hpt
  have hconst : ∀ h : (Fin 0 → Bool) → ℝ, (∑ x, h x) = h x₀ :=
    fun h => Fintype.sum_subsingleton h x₀
  rw [hconst (fun x => P x * f x), hconst (fun x => P x * g x), hconst P,
    hconst (fun x => P x * f x * g x)]
  nlinarith [hpos x₀]

/-- **The finite-product FKG theorem.** -/
theorem fkg_fin : ∀ n, FKGstmt n
  | 0 => fkg_zero
  | n + 1 => fkg_succ (fkg_fin n)

end FinFKG
