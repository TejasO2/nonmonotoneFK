/-
Part of the FK formalization campaign (member m8, direction d8).

# The antitone (decreasing-observable) form of the FKG inequality

The FKG theorem is stated for increasing observables.  Since the configuration
space is finite, every observable is bounded, so the decreasing form follows by
shifting: writing `F = M - f`, `G = M - g` with `f`, `g` increasing and
nonnegative, the FKG inequality for `f`, `g` is *algebraically equivalent* to
the same inequality for `F`, `G` (the `M`-dependent terms cancel because the
`P`-masses on both sides agree).  We record the decreasing form because closed
events are decreasing.

**Remark (not formalized as a theorem, because it is false).**
The mirror statement "a log-submodular weight gives *negative* association of
increasing observables" does **not** follow and is false in general: on the
one-coordinate space the lattice condition is vacuous (both sides are the same
product), and yet for a weight with `P(0) = a > 0`, `P(1) = b > 0` and the
increasing observable `f = g = 𝟙{1}` one has `∑ P f g · ∑ P = (a+b)b` while
`(∑ P f)(∑ P g) = b²`, so the correlation is strictly positive.  This is the
log-submodular regime of the random-cluster weight with `q < 1`, so no
association conclusion is claimed there; only the reversed lattice condition
itself (`fkWeight_lc_rev` in `FKCluster.lean`).
-/
import FK.FKG.General

namespace FinFKG

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Antitone FKG**: under a log-supermodular positive weight, decreasing
nonnegative observables are positively correlated
(`∑ P F · ∑ P G ≤ ∑ P · ∑ P F G`). -/
theorem fkg_antitone {P : (ι → Bool) → ℝ} (hpos : ∀ x, 0 < P x)
    (hlc : ∀ x y, P x * P y ≤ P (x ⊔ y) * P (x ⊓ y))
    (F G : (ι → Bool) → ℝ) (hF : Antitone F) (hG : Antitone G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x) :
    (∑ x, P x * F x) * (∑ x, P x * G x) ≤ (∑ x, P x) * (∑ x, P x * F x * G x) := by
  classical
  set Z : ℝ := ∑ x, P x with hZ
  set A : ℝ := ∑ x, P x * F x with hA
  set B : ℝ := ∑ x, P x * G x with hB
  set C : ℝ := ∑ x, P x * F x * G x with hC
  set M : ℝ := (∑ x, F x) + (∑ x, G x) + 1 with hM
  have hFM : ∀ x, F x ≤ M := by
    intro x
    have h1 : F x ≤ ∑ y, F y :=
      Finset.single_le_sum (f := F) (fun i _ => hF0 i) (Finset.mem_univ x)
    have h2 : (0:ℝ) ≤ ∑ y, G y := Finset.sum_nonneg (fun i _ => hG0 i)
    simp only [hM]
    linarith
  have hGM : ∀ x, G x ≤ M := by
    intro x
    have h1 : G x ≤ ∑ y, G y :=
      Finset.single_le_sum (f := G) (fun i _ => hG0 i) (Finset.mem_univ x)
    have h2 : (0:ℝ) ≤ ∑ y, F y := Finset.sum_nonneg (fun i _ => hF0 i)
    simp only [hM]
    linarith
  have hfmono : Monotone fun x => M - F x := by
    intro x y hxy
    have := hF hxy
    linarith
  have hgmono : Monotone fun x => M - G x := by
    intro x y hxy
    have := hG hxy
    linarith
  have hfnn : ∀ x, 0 ≤ M - F x := fun x => by have := hFM x; linarith
  have hgnn : ∀ x, 0 ≤ M - G x := fun x => by have := hGM x; linarith
  have key := fkg_of_lattice hpos hlc (fun x => M - F x) (fun x => M - G x)
    hfmono hgmono hfnn hgnn
  have e1 : ∑ x, P x * (M - F x) = M * Z - A := by
    have hpt : ∀ x, P x * (M - F x) = P x * M - P x * F x := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp only [hZ, hA]
    ring
  have e2 : ∑ x, P x * (M - G x) = M * Z - B := by
    have hpt : ∀ x, P x * (M - G x) = P x * M - P x * G x := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp only [hZ, hB]
    ring
  have e3 : ∑ x, P x * (M - F x) * (M - G x) = M * M * Z - M * A - M * B + C := by
    have hpt : ∀ x, P x * (M - F x) * (M - G x) =
        (M * M * P x - M * (P x * F x)) - M * (P x * G x) + P x * F x * G x :=
      fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [e1, e2, e3] at key
  have expand : (M * Z - A) * (M * Z - B) - Z * (M * M * Z - M * A - M * B + C) =
      A * B - Z * C := by ring
  nlinarith [key, expand]

end FinFKG
