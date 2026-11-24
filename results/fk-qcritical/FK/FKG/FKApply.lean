/-
Part of the FK formalization campaign (member m8, direction d8).

# Consequences of the cluster-count supermodularity for the FK weight

From the exact pair identity

  `w (x ⊔ y) * w (x ⊓ y) = w x * w y * q ^ Δ`

(where `Δ = k(x∨y) + k(x∧y) - k(x) - k(y) ≥ 0` by cluster-count
supermodularity) we obtain

* `q ≥ 1`: the lattice condition (log-supermodularity), hence positive
  association of the finite random-cluster measure (`fkWeight_lc`,
  `fk_association`);
* `q ≤ 1`: the reversed lattice condition (log-submodularity)
  (`fkWeight_lc_rev`).  No association conclusion is drawn here; see the
  remark in `Mirror.lean` for why the reversed condition does not give one.

The pair identity also gives **monotonicity in the edge activity** via Holley's
comparison: for `c₁ ≤ c₂` the increasing observables have larger `c₂`-sums
(`fk_mono_activity`).  In the usual random-cluster parametrization
`c = p/(1-p)` this is monotonicity in `p` at fixed `q ≥ 1`.
-/
import FK.FKG.FKCluster
import FK.FKG.Mirror

namespace FinFKG

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Exact pair identity for the FK weight.**  The supermodularity defect `Δ`
of the cluster count is exactly the excess cluster weight produced by
replacing the pair `(x, y)` by `(x ⊔ y, x ⊓ y)`. -/
theorem fkWeight_pair_eq {c q : ℝ} (ends : E → V × V) (x y : E → Bool) :
    ∃ Δ : ℕ, clusterCount ends (openSet x ∪ openSet y) +
        clusterCount ends (openSet x ∩ openSet y) =
        (clusterCount ends (openSet x) + clusterCount ends (openSet y)) + Δ ∧
      fkWeight c q ends (x ⊔ y) * fkWeight c q ends (x ⊓ y) =
        fkWeight c q ends x * fkWeight c q ends y * q ^ Δ := by
  classical
  obtain ⟨Δ, hΔ⟩ := Nat.exists_eq_add_of_le
    (clusterCount_supermodular ends (openSet x) (openSet y))
  refine ⟨Δ, hΔ, ?_⟩
  have hsu : openSet (x ⊔ y) = openSet x ∪ openSet y := openSet_sup x y
  have hin : openSet (x ⊓ y) = openSet x ∩ openSet y := openSet_inf x y
  have hcard : (openSet x ∪ openSet y).card + (openSet x ∩ openSet y).card =
      (openSet x).card + (openSet y).card := Finset.card_union_add_card_inter _ _
  have step : fkWeight c q ends (x ⊔ y) * fkWeight c q ends (x ⊓ y) =
      c ^ ((openSet x ∪ openSet y).card + (openSet x ∩ openSet y).card) *
        q ^ (clusterCount ends (openSet x ∪ openSet y) +
          clusterCount ends (openSet x ∩ openSet y)) := by
    simp only [fkWeight, hsu, hin]
    exact fkWeight_pair c q _ _ _ _
  have step2 : fkWeight c q ends x * fkWeight c q ends y * q ^ Δ =
      c ^ ((openSet x).card + (openSet y).card) *
        q ^ ((clusterCount ends (openSet x) + clusterCount ends (openSet y)) + Δ) := by
    have h1 : fkWeight c q ends x * fkWeight c q ends y =
        c ^ ((openSet x).card + (openSet y).card) *
          q ^ (clusterCount ends (openSet x) + clusterCount ends (openSet y)) := by
      simp only [fkWeight]
      exact fkWeight_pair c q _ _ _ _
    rw [h1, mul_assoc, ← pow_add]
  rw [step, step2, hcard, hΔ]

/-- The FK weight is log-supermodular when `q ≥ 1`. -/
theorem fkWeight_lc {c q : ℝ} (hc : 0 < c) (hq : 1 ≤ q) (ends : E → V × V) :
    ∀ x y : E → Bool, fkWeight c q ends x * fkWeight c q ends y ≤
      fkWeight c q ends (x ⊔ y) * fkWeight c q ends (x ⊓ y) := by
  intro x y
  obtain ⟨Δ, -, hid⟩ := fkWeight_pair_eq ends x y
  rw [hid]
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have h1 : (1:ℝ) ≤ q ^ Δ := one_le_pow₀ hq
  have h2 : 0 ≤ fkWeight c q ends x * fkWeight c q ends y :=
    le_of_lt (mul_pos (fkWeight_pos hc hq0 ends x) (fkWeight_pos hc hq0 ends y))
  calc fkWeight c q ends x * fkWeight c q ends y
      = fkWeight c q ends x * fkWeight c q ends y * 1 := by ring
    _ ≤ fkWeight c q ends x * fkWeight c q ends y * q ^ Δ :=
        mul_le_mul_of_nonneg_left h1 h2

/-- The FK weight satisfies the **reversed** lattice condition when `q ≤ 1`
(log-submodularity, the regime `q < 1` of the paper). -/
theorem fkWeight_lc_rev {c q : ℝ} (hc : 0 < c) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (ends : E → V × V) :
    ∀ x y : E → Bool, fkWeight c q ends (x ⊔ y) * fkWeight c q ends (x ⊓ y) ≤
      fkWeight c q ends x * fkWeight c q ends y := by
  intro x y
  obtain ⟨Δ, -, hid⟩ := fkWeight_pair_eq ends x y
  rw [hid]
  have h1 : q ^ Δ ≤ 1 := pow_le_one₀ (le_of_lt hq0) hq1
  have h2 : 0 ≤ fkWeight c q ends x * fkWeight c q ends y :=
    le_of_lt (mul_pos (fkWeight_pos hc hq0 ends x) (fkWeight_pos hc hq0 ends y))
  calc fkWeight c q ends x * fkWeight c q ends y * q ^ Δ
      ≤ fkWeight c q ends x * fkWeight c q ends y * 1 :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = fkWeight c q ends x * fkWeight c q ends y := by ring

/-! ### Monotonicity in the edge activity -/

/-- **Monotone likelihood ratio in the edge activity**: raising the edge
activity `c₁ ≤ c₂` makes the FK weight more concentrated on configurations with
more open edges. -/
theorem fkWeight_mlr {c1 c2 q : ℝ} (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hq : 1 ≤ q)
    (ends : E → V × V) :
    ∀ x y : E → Bool, fkWeight c1 q ends x * fkWeight c2 q ends y ≤
      fkWeight c2 q ends (x ⊔ y) * fkWeight c1 q ends (x ⊓ y) := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  intro x y
  set a := (openSet x).card with ha
  set b := (openSet y).card with hb
  set i := (openSet x ∩ openSet y).card with hi
  set u := (openSet x ∪ openSet y).card with hu
  set ks := clusterCount ends (openSet x) with hks
  set kt := clusterCount ends (openSet y) with hkt
  set ku := clusterCount ends (openSet x ∪ openSet y) with hku
  set ki := clusterCount ends (openSet x ∩ openSet y) with hki
  have hai : i ≤ a := by
    rw [ha, hi]
    exact Finset.card_le_card (Finset.inter_subset_left ..)
  have hbi : i ≤ b := by
    rw [hb, hi]
    exact Finset.card_le_card (Finset.inter_subset_right ..)
  have hcard : u + i = a + b := by
    rw [ha, hb, hi, hu]
    exact Finset.card_union_add_card_inter _ _
  have hk : ks + kt ≤ ku + ki := by
    rw [hks, hkt, hku, hki]
    exact clusterCount_supermodular ends (openSet x) (openSet y)
  -- the `c`-part of the likelihood ratio is increasing
  have hcpart : c1 ^ a * c2 ^ b ≤ c2 ^ u * c1 ^ i := by
    have hd1 : a = (a - i) + i := (Nat.sub_add_cancel hai).symm
    have hd2 : b = (b - i) + i := (Nat.sub_add_cancel hbi).symm
    have hu' : u = a - i + (b - i) + i := by omega
    have key : c1 ^ (a - i) * c2 ^ (b - i) ≤ c2 ^ (a - i) * c2 ^ (b - i) := by
      have h := pow_le_pow_left₀ (le_of_lt hc1) hc12 (a - i)
      exact mul_le_mul_of_nonneg_right h (le_of_lt (pow_pos hc2 _))
    have h_lhs : c1 ^ a * c2 ^ b = (c1 ^ (a - i) * c2 ^ (b - i)) * (c1 * c2) ^ i := by
      conv_lhs => rw [hd1, hd2]
      rw [mul_pow, pow_add, pow_add]
      ring
    have h_rhs : c2 ^ u * c1 ^ i = (c2 ^ (a - i) * c2 ^ (b - i)) * (c2 * c1) ^ i := by
      conv_lhs => rw [hu']
      rw [mul_pow, pow_add, pow_add]
      ring
    calc c1 ^ a * c2 ^ b
        = (c1 ^ (a - i) * c2 ^ (b - i)) * (c1 * c2) ^ i := h_lhs
      _ ≤ (c2 ^ (a - i) * c2 ^ (b - i)) * (c2 * c1) ^ i := by
          have h2 : (c1 * c2) ^ i = (c2 * c1) ^ i := by rw [mul_comm c1 c2]
          rw [h2]
          exact mul_le_mul_of_nonneg_right key (le_of_lt (pow_pos (mul_pos hc2 hc1) i))
      _ = c2 ^ u * c1 ^ i := by rw [← h_rhs]
  have hqpart : q ^ (ks + kt) ≤ q ^ (ku + ki) := pow_le_pow_right₀ hq hk
  calc fkWeight c1 q ends x * fkWeight c2 q ends y
      = (c1 ^ a * c2 ^ b) * q ^ (ks + kt) := by
        simp only [fkWeight, ha, hb, hks, hkt]
        rw [mul_mul_mul_comm, ← pow_add]
    _ ≤ (c2 ^ u * c1 ^ i) * q ^ (ku + ki) := by
        exact mul_le_mul hcpart hqpart (le_of_lt (pow_pos hq0 (ks + kt)))
          (le_of_lt (mul_pos (pow_pos hc2 u) (pow_pos hc1 i)))
    _ = fkWeight c2 q ends (x ⊔ y) * fkWeight c1 q ends (x ⊓ y) := by
        simp only [fkWeight, hu, hi, hku, hki, openSet_sup, openSet_inf]
        rw [mul_mul_mul_comm, ← pow_add]

/-- **Holley's comparison for the FK weight**: increasing the edge activity
increases the expectations of increasing observables.  In the random-cluster
parametrization `c = p / (1 - p)` this is monotonicity in `p` at fixed `q ≥ 1`,
in the unnormalized (weighted-sum) form; the normalized form follows by
dividing by the two total masses. -/
theorem fk_mono_activity {c1 c2 q : ℝ} (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hq : 1 ≤ q)
    (ends : E → V × V) (f : (E → Bool) → ℝ) (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) :
    (∑ ω, fkWeight c1 q ends ω * f ω) * (∑ ω, fkWeight c2 q ends ω) ≤
      (∑ ω, fkWeight c1 q ends ω) * (∑ ω, fkWeight c2 q ends ω * f ω) := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact holley (fun ω => fkWeight_pos hc1 hq0 ends ω)
    (fun ω => le_of_lt (fkWeight_pos hc2 hq0 ends ω))
    (fkWeight_lc hc1 hq ends) (fkWeight_mlr hc1 hc12 hq ends) f hf hf0

/-- **Positive association of the finite random-cluster measure for `q ≥ 1`.**
Increasing nonnegative observables are positively correlated under the FK
weight with edge activity `c > 0` and cluster weight `q ≥ 1`. -/
theorem fk_association {c q : ℝ} (hc : 0 < c) (hq : 1 ≤ q) (ends : E → V × V)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∑ ω, fkWeight c q ends ω * f ω) * (∑ ω, fkWeight c q ends ω * g ω) ≤
      (∑ ω, fkWeight c q ends ω) *
        (∑ ω, fkWeight c q ends ω * f ω * g ω) :=
  fkg_of_lattice (P := fkWeight c q ends)
    (fun ω => fkWeight_pos hc (lt_of_lt_of_le zero_lt_one hq) ends ω)
    (fkWeight_lc hc hq ends) f g hf hg hf0 hg0

/-- Indicator of an event, as a real-valued observable. -/
noncomputable def indicator (A : (E → Bool) → Prop) [DecidablePred A] (ω : E → Bool) : ℝ :=
  if A ω then 1 else 0

/-- Event form of positive association: increasing events are positively
correlated under the finite random-cluster weight for `q ≥ 1`. -/
theorem fk_association_events {c q : ℝ} (hc : 0 < c) (hq : 1 ≤ q) (ends : E → V × V)
    {A B : (E → Bool) → Prop} [DecidablePred A] [DecidablePred B]
    (hA : ∀ x y : E → Bool, x ≤ y → A x → A y)
    (hB : ∀ x y : E → Bool, x ≤ y → B x → B y) :
    (∑ ω, fkWeight c q ends ω * indicator A ω) *
        (∑ ω, fkWeight c q ends ω * indicator B ω) ≤
      (∑ ω, fkWeight c q ends ω) *
        (∑ ω, fkWeight c q ends ω * indicator A ω * indicator B ω) := by
  refine fk_association hc hq ends (indicator A) (indicator B) ?_ ?_ ?_ ?_
  · intro x y hxy
    by_cases h : A x
    · have h' : A y := hA x y hxy h
      simp only [indicator, h, h']
      simp
    · simp only [indicator, h]
      split_ifs <;> simp_all
  · intro x y hxy
    by_cases h : B x
    · have h' : B y := hB x y hxy h
      simp only [indicator, h, h']
      simp
    · simp only [indicator, h]
      split_ifs <;> simp_all
  · intro x
    simp only [indicator]
    split_ifs <;> simp_all
  · intro x
    simp only [indicator]
    split_ifs <;> simp_all

end FinFKG
