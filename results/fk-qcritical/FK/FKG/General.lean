/-
Part of the FK formalization campaign (member m8, direction d8).

# FKG/Harris/Holley on an arbitrary finite Boolean product

`Fin n → Bool` is replaced by `ι → Bool` for an arbitrary finite type `ι`,
by transporting along a fixed equivalence `ι ≃ Fin (card ι)`.  On top of the
general FKG inequality we record the two standard consequences used in
percolation theory:

* **Harris' inequality**: product Bernoulli weights satisfy the lattice
  condition with equality, so increasing events are positively correlated.
* **Holley's comparison**: if the likelihood ratio `Q/P` is increasing, then
  increasing observables have larger `Q`-expectations.
-/
import FK.FKG.Main

namespace FinFKG

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Transport to an arbitrary finite index type -/

/-- `(Fin (card ι) → Bool) ≃ (ι → Bool)` induced by a fixed numbering. -/
def finCongr (e : ι ≃ Fin (Fintype.card ι)) : (Fin (Fintype.card ι) → Bool) ≃ (ι → Bool) where
  toFun z := fun i => z (e i)
  invFun x := fun j => x (e.symm j)
  left_inv z := by
    funext j
    simp
  right_inv x := by
    funext i
    simp

/-- **The finite-product FKG theorem**, for an arbitrary finite index type. -/
theorem fkg_of_lattice {P : (ι → Bool) → ℝ} (hpos : ∀ x, 0 < P x)
    (hlc : ∀ x y, P x * P y ≤ P (x ⊔ y) * P (x ⊓ y))
    (f g : (ι → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∑ x, P x * f x) * (∑ x, P x * g x) ≤ (∑ x, P x) * (∑ x, P x * f x * g x) := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  set ψ := finCongr e with hψ
  set Q : (Fin (Fintype.card ι) → Bool) → ℝ := fun z => P (ψ z) with hQ
  set F : (Fin (Fintype.card ι) → Bool) → ℝ := fun z => f (ψ z) with hF
  set G : (Fin (Fintype.card ι) → Bool) → ℝ := fun z => g (ψ z) with hG
  have hsup : ∀ z z' : Fin (Fintype.card ι) → Bool, (ψ z ⊔ ψ z') = ψ (z ⊔ z') := by
    intro z z'
    funext i
    simp [hψ, finCongr, Pi.sup_apply]
  have hinf : ∀ z z' : Fin (Fintype.card ι) → Bool, (ψ z ⊓ ψ z') = ψ (z ⊓ z') := by
    intro z z'
    funext i
    simp [hψ, finCongr, Pi.inf_apply]
  have hQlc : LC (Fintype.card ι) Q := by
    intro z z'
    have h := hlc (ψ z) (ψ z')
    rw [hsup, hinf] at h
    exact h
  have hFmono : Monotone F := by
    intro z z' hzz
    refine hf ?_
    intro i
    exact hzz (e i)
  have hGmono : Monotone G := by
    intro z z' hzz
    refine hg ?_
    intro i
    exact hzz (e i)
  have key := fkg_fin (Fintype.card ι) Q (fun z => hpos _) hQlc F G hFmono hGmono
    (fun z => hf0 _) (fun z => hg0 _)
  have t1 : (∑ z, Q z * F z) = ∑ x : ι → Bool, P x * f x := by
    have h : ∀ z, Q z * F z = P (ψ z) * f (ψ z) := fun z => by simp [hQ, hF]
    rw [Finset.sum_congr rfl (fun z _ => h z), Equiv.sum_comp ψ (fun x : ι → Bool => P x * f x)]
  have t2 : (∑ z, Q z * G z) = ∑ x : ι → Bool, P x * g x := by
    have h : ∀ z, Q z * G z = P (ψ z) * g (ψ z) := fun z => by simp [hQ, hG]
    rw [Finset.sum_congr rfl (fun z _ => h z), Equiv.sum_comp ψ (fun x : ι → Bool => P x * g x)]
  have t3 : (∑ z, Q z) = ∑ x : ι → Bool, P x := by
    have h : ∀ z, Q z = P (ψ z) := fun z => by simp [hQ]
    rw [Finset.sum_congr rfl (fun z _ => h z), Equiv.sum_comp ψ (fun x : ι → Bool => P x)]
  have t4 : (∑ z, Q z * F z * G z) = ∑ x : ι → Bool, P x * f x * g x := by
    have h : ∀ z, Q z * F z * G z = P (ψ z) * f (ψ z) * g (ψ z) := fun z => by simp [hQ, hF, hG]
    rw [Finset.sum_congr rfl (fun z _ => h z), Equiv.sum_comp ψ (fun x : ι → Bool => P x * f x * g x)]
  rw [t1, t2, t3, t4] at key
  exact key

/-! ### Harris' inequality for product measures -/

/-- The product Bernoulli weight. -/
noncomputable def bernWeight (p : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, (if x i then p i else 1 - p i)

/-- One-coordinate factor: the two-point lattice condition holds with equality
for a Bernoulli weight. -/
theorem bernoulli_factor (p : ℝ) (a b : Bool) :
    (if a then p else 1 - p) * (if b then p else 1 - p) =
      (if (a ⊔ b) then p else 1 - p) * (if (a ⊓ b) then p else 1 - p) := by
  cases a <;> cases b <;> simp [mul_comm]

omit [DecidableEq ι] in
/-- The product Bernoulli weight satisfies the lattice condition (with
equality). -/
theorem bernoulli_lc (p : ι → ℝ) :
    ∀ x y : ι → Bool, bernWeight p x * bernWeight p y =
      bernWeight p (x ⊔ y) * bernWeight p (x ⊓ y) := by
  intro x y
  simp only [bernWeight, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => bernoulli_factor (p i) (x i) (y i))

/-- **Harris' inequality** for a product Bernoulli weight on a finite Boolean
product: increasing nonnegative observables are positively correlated. -/
theorem harris (p : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (f g : (ι → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∑ x, bernWeight p x * f x) * (∑ x, bernWeight p x * g x) ≤
      (∑ x, bernWeight p x) * (∑ x, bernWeight p x * f x * g x) := by
  refine fkg_of_lattice (P := bernWeight p) (fun x => ?_)
    (fun x y => le_of_eq (bernoulli_lc p x y)) f g hf hg hf0 hg0
  simp only [bernWeight]
  refine Finset.prod_pos (fun i _ => ?_)
  by_cases h : x i
  · simpa [h] using hp0 i
  · simpa [h] using sub_pos.mpr (hp1 i)

/-! ### Holley's comparison theorem -/

/-- **Holley's comparison theorem** on a finite Boolean product: if the
likelihood ratio `Q/P` is increasing, then increasing observables have larger
`Q`-weighted sums.  Proved by applying the FKG inequality to `P` and the
likelihood ratio itself. -/
theorem holley {P Q : (ι → Bool) → ℝ} (hP : ∀ x, 0 < P x) (hQ : ∀ x, 0 ≤ Q x)
    (hlc : ∀ x y, P x * P y ≤ P (x ⊔ y) * P (x ⊓ y))
    (hmlr : ∀ x y, P x * Q y ≤ Q (x ⊔ y) * P (x ⊓ y))
    (f : (ι → Bool) → ℝ) (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) :
    (∑ x, P x * f x) * (∑ x, Q x) ≤ (∑ x, P x) * (∑ x, Q x * f x) := by
  set h : (ι → Bool) → ℝ := fun x => Q x / P x with hh
  have hPne : ∀ x, P x ≠ 0 := fun x => ne_of_gt (hP x)
  have hmono : Monotone h := by
    intro x y hxy
    have hxy' : Q x / P x ≤ Q y / P y := by
      rw [div_le_div_iff₀ (hP x) (hP y)]
      have h := hmlr y x
      rw [sup_eq_left.mpr hxy, inf_eq_right.mpr hxy] at h
      calc Q x * P y = P y * Q x := by ring
        _ ≤ Q y * P x := h
    exact hxy'
  have hnonneg : ∀ x, 0 ≤ h x := fun x => div_nonneg (hQ x) (le_of_lt (hP x))
  have key := fkg_of_lattice hP hlc f h hf hmono hf0 hnonneg
  have hsum_h : ∑ x, P x * h x = ∑ x, Q x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hh]
    simp only
    exact mul_div_cancel₀ _ (hPne x)
  have hsum_fh : ∑ x, P x * f x * h x = ∑ x, Q x * f x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hh]
    simp only
    calc P x * f x * (Q x / P x) = f x * (P x * (Q x / P x)) := by ring
      _ = f x * Q x := by rw [mul_div_cancel₀ (Q x) (hPne x)]
      _ = Q x * f x := by ring
  rw [hsum_h, hsum_fh] at key
  exact key

end FinFKG
