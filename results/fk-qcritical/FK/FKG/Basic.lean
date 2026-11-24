/-
Part of the FK formalization campaign (member m8, direction d8).

# The finite-product FKG theorem

For a strictly positive weight `P` on a finite Boolean product `Fin n → Bool`
satisfying the lattice condition (log-supermodularity)

  `P (x ⊔ y) * P (x ⊓ y) ≥ P x * P y`,

increasing nonnegative functions are positively correlated:

  `(∑ P f) * (∑ P g) ≤ (∑ P) * (∑ P f g)`.

The proof is by induction on the number of coordinates.  The induction step
splits the last coordinate, uses the lattice condition to get a monotone
likelihood ratio between the two conditional slices, applies the induction
hypothesis to the slices, and finishes with the two-point Chebyshev identity.
No Hall-type theorem, no linear-programming duality, no coupling and no
rational approximation is used.
-/
import Mathlib

namespace FinFKG

open Finset

/-! ### Two-point Chebyshev (Harris) step -/

/-- The exact two-point Chebyshev identity, in the form used in the induction
step of the FKG theorem. -/
lemma chebyshev_two {l0 l1 a0 a1 b0 b1 : ℝ} (h0 : 0 ≤ l0) (h1 : 0 ≤ l1)
    (ha : a0 ≤ a1) (hb : b0 ≤ b1) :
    (l0 * a0 + l1 * a1) * (l0 * b0 + l1 * b1) ≤
      (l0 + l1) * (l0 * a0 * b0 + l1 * a1 * b1) := by
  have h : 0 ≤ l0 * l1 * (a1 - a0) * (b1 - b0) :=
    mul_nonneg (mul_nonneg (mul_nonneg h0 h1) (sub_nonneg.2 ha)) (sub_nonneg.2 hb)
  nlinarith [h]

/-! ### Splitting off one coordinate -/

/-- `Bool × (Fin n → Bool) ≃ (Fin (n+1) → Bool)` by consing the first
coordinate. -/
def consEquiv (n : ℕ) : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by
    have h : Fin.tail (Fin.cons (α := fun _ => Bool) p.1 p.2) = p.2 := by
      funext i
      simp [Fin.tail]
    simp [h]
  right_inv x := by
    simp

/-- `Fin (n+1) → Bool` splits into the two coordinate slices. -/
lemma sum_cons {M : Type*} [AddCommMonoid M] (g : (Fin (n + 1) → Bool) → M) :
    ∑ x, g x = ∑ y : Fin n → Bool, (g (Fin.cons (α := fun _ => Bool) false y) +
      g (Fin.cons (α := fun _ => Bool) true y)) := by
  have h1 : (∑ x : Fin (n + 1) → Bool, g x) =
      ∑ p : Bool × (Fin n → Bool), g (Fin.cons (α := fun _ => Bool) p.1 p.2) := by
    refine Fintype.sum_equiv (consEquiv n).symm (fun x => g x) (fun p => g (Fin.cons p.1 p.2)) ?_
    intro x
    simp [consEquiv]
  have h2 : (∑ p : Bool × (Fin n → Bool), g (Fin.cons (α := fun _ => Bool) p.1 p.2))
      = ∑ b : Bool, ∑ y : Fin n → Bool, g (Fin.cons (α := fun _ => Bool) b y) :=
    Fintype.sum_prod_type _
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show (∑ b : Bool, g (Fin.cons (α := fun _ => Bool) b y)) =
    g (Fin.cons (α := fun _ => Bool) false y) + g (Fin.cons (α := fun _ => Bool) true y)
  rw [Fintype.sum_bool, add_comm]

/-! ### Pointwise lattice algebra of `Fin.cons` -/

lemma cons_sup (b : Bool) (y y' : Fin n → Bool) :
    (Fin.cons (α := fun _ => Bool) b y ⊔ Fin.cons (α := fun _ => Bool) b y') =
      Fin.cons (α := fun _ => Bool) b (y ⊔ y') := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]

lemma cons_inf (b : Bool) (y y' : Fin n → Bool) :
    (Fin.cons (α := fun _ => Bool) b y ⊓ Fin.cons (α := fun _ => Bool) b y') =
      Fin.cons (α := fun _ => Bool) b (y ⊓ y') := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]

lemma cons_sup_mixed (y y' : Fin n → Bool) :
    (Fin.cons (α := fun _ => Bool) true y ⊔ Fin.cons (α := fun _ => Bool) false y') =
      Fin.cons (α := fun _ => Bool) true (y ⊔ y') := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]

lemma cons_inf_mixed (y y' : Fin n → Bool) :
    (Fin.cons (α := fun _ => Bool) true y ⊓ Fin.cons (α := fun _ => Bool) false y') =
      Fin.cons (α := fun _ => Bool) false (y ⊓ y') := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [Fin.cons_zero, Fin.cons_succ]

lemma cons_le_cons {b b' : Bool} {y y' : Fin n → Bool}
    (hb : b ≤ b') (hy : y ≤ y') :
    Fin.cons (α := fun _ => Bool) b y ≤ Fin.cons (α := fun _ => Bool) b' y' := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [Fin.cons_zero] using hb
  · intro j
    simpa [Fin.cons_succ] using hy j

lemma cons_mono_false_true (y : Fin n → Bool) :
    Fin.cons (α := fun _ => Bool) false y ≤ Fin.cons (α := fun _ => Bool) true y :=
  cons_le_cons (by decide) le_rfl

/-! ### The two theorem statements -/

/-- The lattice condition (log-supermodularity) on `Fin n → Bool`. -/
def LC (n : ℕ) (P : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x y, P x * P y ≤ P (x ⊔ y) * P (x ⊓ y)

/-- The FKG conclusion for a positive weight on `Fin n → Bool`. -/
def FKGstmt (n : ℕ) : Prop :=
  ∀ (P : (Fin n → Bool) → ℝ), (∀ x, 0 < P x) → LC n P →
    ∀ f g : (Fin n → Bool) → ℝ, Monotone f → Monotone g →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      (∑ x, P x * f x) * (∑ x, P x * g x) ≤ (∑ x, P x) * (∑ x, P x * f x * g x)

/-- The lattice condition passes to a coordinate slice. -/
lemma LC.slice {n : ℕ} {P : (Fin (n + 1) → Bool) → ℝ} (hP : LC (n + 1) P) (b : Bool) :
    LC n fun y => P (Fin.cons (α := fun _ => Bool) b y) := by
  intro x y
  have h := hP (Fin.cons (α := fun _ => Bool) b x) (Fin.cons (α := fun _ => Bool) b y)
  rwa [cons_sup, cons_inf] at h

/-- The lattice condition gives a monotone likelihood ratio between the two
slices at a fixed coordinate. -/
lemma mlr_LC {n : ℕ} {P : (Fin (n + 1) → Bool) → ℝ} (hP : LC (n + 1) P)
    (x y : Fin n → Bool) :
    P (Fin.cons (α := fun _ => Bool) false x) * P (Fin.cons (α := fun _ => Bool) true y) ≤
      P (Fin.cons (α := fun _ => Bool) true (x ⊔ y)) *
        P (Fin.cons (α := fun _ => Bool) false (x ⊓ y)) := by
  have h := hP (Fin.cons (α := fun _ => Bool) true y) (Fin.cons (α := fun _ => Bool) false x)
  rw [cons_sup_mixed, cons_inf_mixed] at h
  calc P (Fin.cons (α := fun _ => Bool) false x) * P (Fin.cons (α := fun _ => Bool) true y)
      = P (Fin.cons (α := fun _ => Bool) true y) * P (Fin.cons (α := fun _ => Bool) false x) := by
        ring
    _ ≤ P (Fin.cons (α := fun _ => Bool) true (y ⊔ x)) *
          P (Fin.cons (α := fun _ => Bool) false (y ⊓ x)) := h
    _ = P (Fin.cons (α := fun _ => Bool) true (x ⊔ y)) *
          P (Fin.cons (α := fun _ => Bool) false (x ⊓ y)) := by rw [sup_comm, inf_comm]

/-! ### Holley-type comparison from the FKG inequality -/

/-- If `Q₁/Q₀` is increasing (monotone likelihood ratio), then increasing
observables have larger `Q₁`-sums than `Q₀`-sums.  This is the "comparison"
step used in the induction below; it is derived from the FKG inequality for
`Q₀` applied to the likelihood ratio itself. -/
lemma comparison {n : ℕ} (hFKG : FKGstmt n)
    (Q0 Q1 : (Fin n → Bool) → ℝ) (h0 : ∀ x, 0 < Q0 x) (h1 : ∀ x, 0 ≤ Q1 x)
    (hlc : LC n Q0) (hmlr : ∀ x y, Q0 x * Q1 y ≤ Q1 (x ⊔ y) * Q0 (x ⊓ y))
    (f : (Fin n → Bool) → ℝ) (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) :
    (∑ x, Q0 x * f x) * (∑ x, Q1 x) ≤ (∑ x, Q0 x) * (∑ x, Q1 x * f x) := by
  set h : (Fin n → Bool) → ℝ := fun x => Q1 x / Q0 x with hh
  have h0ne : ∀ x, Q0 x ≠ 0 := fun x => ne_of_gt (h0 x)
  have hmono : Monotone h := by
    intro x y hxy
    have hxy' : Q1 x / Q0 x ≤ Q1 y / Q0 y := by
      rw [div_le_div_iff₀ (h0 x) (h0 y)]
      have h := hmlr y x
      rw [sup_eq_left.mpr hxy, inf_eq_right.mpr hxy] at h
      calc Q1 x * Q0 y = Q0 y * Q1 x := by ring
        _ ≤ Q1 y * Q0 x := h
    exact hxy'
  have hnonneg : ∀ x, 0 ≤ h x := fun x => div_nonneg (h1 x) (le_of_lt (h0 x))
  have key := hFKG Q0 h0 hlc f h hf hmono hf0 hnonneg
  have hsum_h : ∑ x, Q0 x * h x = ∑ x, Q1 x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hh]
    simp only
    exact mul_div_cancel₀ _ (h0ne x)
  have hsum_fh : ∑ x, Q0 x * f x * h x = ∑ x, Q1 x * f x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hh]
    simp only
    calc Q0 x * f x * (Q1 x / Q0 x)
        = f x * (Q0 x * (Q1 x / Q0 x)) := by ring
      _ = Q1 x * f x := by rw [mul_div_cancel₀ (Q1 x) (h0ne x), mul_comm]
  rw [hsum_h, hsum_fh] at key
  exact key

end FinFKG
