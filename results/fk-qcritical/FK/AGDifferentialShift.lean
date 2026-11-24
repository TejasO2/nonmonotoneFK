/-
Worker m4 contribution, formalization of arXiv:2512.16486.

# Aizenman--Grimmett strict shift from a uniform finite-volume differential bound

The paper's Theorem 1.4 is reduced in `FK.EssentialWindow`/`FK.AGWindow` to a
family of "strict critical shift" inputs `hAG`: for every small decrement
`ε > 0` there is a base `b > p_c` such that the product law with edge weights
`b - ε` on an enhanced edge set and `b` elsewhere gives zero mass to the
percolation event (and symmetrically for increments).

This file proves that those inputs follow from a *local, pointwise and
uniform-in-box differential inequality*, which is the form in which the
essential-enhancement estimate of Aizenman--Grimmett is proved: along the
trade curve `(b, ε) ↦ (b + c·s, ε + s)` the finite-volume connection
probabilities are non-increasing (resp. non-decreasing for the increment
trade), with one constant `c > 0` uniform in the approximation index.

Nothing here asserts the differential inequality itself.  What is proved is
the implication `uniform trade bound ⇒ strict shift`, with the sign and
quantifier bookkeeping (`b > p_c`, `ε ≤ b`, `b ≤ 1`, endpoint safety) done
in full, and the concrete profile masses of `FK.EssentialWindow` used as the
infinite-volume objects.
-/
import FK.AGWindow
import FK.EssentialWindow

open Set MeasureTheory Filter
open scoped ENNReal NNReal unitInterval Topology

namespace FK.AGDifferentialShift

noncomputable section

/-! ## Profile weights -/

/-- Total version of the paper's decrement profile: weights `b - ε` on `S` and
`b` elsewhere, clamped into `[0,1]`.  The clamp is inactive under the
side conditions of `decrementWeight_eq`. -/
def decrementWeight {E : Type*} (S : Set E) (b ε : ℝ) : E → unitInterval :=
  fun e => by
    classical
    exact ⟨max 0 (min 1 (if e ∈ S then b - ε else b)),
      le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Total version of the increment profile: weights `a + ε` on `S` and `a`
elsewhere, clamped into `[0,1]`. -/
def incrementWeight {E : Type*} (S : Set E) (a ε : ℝ) : E → unitInterval :=
  fun e => by
    classical
    exact ⟨max 0 (min 1 (if e ∈ S then a + ε else a)),
      le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Under the side conditions of the profile the clamp is inactive. -/
theorem decrementWeight_eq {E : Type*} (S : Set E) {b ε : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hε0 : 0 ≤ ε) (hεb : ε ≤ b) :
    decrementWeight S b ε = FK.EssentialWindow.decrementProfile S b ε hb0 hb1 hε0 hεb := by
  funext e
  apply Subtype.ext
  simp only [decrementWeight, FK.EssentialWindow.decrementProfile]
  by_cases he : e ∈ S
  · simp only [ite_eq_left he]
    rw [min_eq_right (show b - ε ≤ 1 by linarith),
      max_eq_right (show (0:ℝ) ≤ b - ε by linarith)]
  · simp only [ite_eq_right he]
    rw [min_eq_right hb1, max_eq_right hb0]

/-- Under the side conditions of the profile the clamp is inactive. -/
theorem incrementWeight_eq {E : Type*} (S : Set E) {a ε : ℝ}
    (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε) (haε1 : a + ε ≤ 1) :
    incrementWeight S a ε = FK.EssentialWindow.incrementProfile S a ε ha0 hε0 haε1 := by
  funext e
  apply Subtype.ext
  simp only [incrementWeight, FK.EssentialWindow.incrementProfile]
  by_cases he : e ∈ S
  · simp only [ite_eq_left he]
    rw [min_eq_right (show a + ε ≤ 1 by linarith),
      max_eq_right (show (0:ℝ) ≤ a + ε by linarith)]
  · simp only [ite_eq_right he]
    rw [min_eq_right (by linarith), max_eq_right ha0]

/-- The increment profile is the decrement profile of the complementary set,
at base `a + ε`. -/
theorem incrementWeight_eq_decrementWeight_compl {E : Type*} (S : Set E) (a ε : ℝ) :
    incrementWeight S a ε = decrementWeight Sᶜ (a + ε) ε := by
  funext e
  apply Subtype.ext
  simp only [incrementWeight, decrementWeight]
  classical
  by_cases he : e ∈ S
  · have hc : e ∉ Sᶜ := by simpa using he
    simp only [ite_eq_left he, ite_eq_right hc]
  · have hc : e ∈ Sᶜ := by simpa using he
    simp only [ite_eq_right he, ite_eq_left hc]
    ring_nf

/-! ## Profile masses -/

/-- Mass in `ℝ` of a configuration event under the decrement profile. -/
def mass {E : Type*} (A : Set (E → Bool)) (S : Set E) (b ε : ℝ) : ℝ :=
  ((FKLimit.bernoulliProduct (decrementWeight S b ε) : Measure (E → Bool)) A).toReal

/-- The decrement mass as a function on the parameter plane, in the shape used
for Fréchet derivatives. -/
def massPair {E : Type*} (A : Set (E → Bool)) (S : Set E) : ℝ × ℝ → ℝ :=
  fun u => mass A S u.1 u.2

/-- Mass in `ℝ` of a configuration event under the increment profile. -/
def incMass {E : Type*} (A : Set (E → Bool)) (S : Set E) (a ε : ℝ) : ℝ :=
  ((FKLimit.bernoulliProduct (incrementWeight S a ε) : Measure (E → Bool)) A).toReal

/-- The decrement mass is the mass of the paper's `decrementProfile`. -/
theorem mass_eq_decrementProfile {E : Type*} (A : Set (E → Bool)) (S : Set E)
    {b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hε0 : 0 ≤ ε) (hεb : ε ≤ b) :
    mass A S b ε =
      ((FKLimit.bernoulliProduct
        (FK.EssentialWindow.decrementProfile S b ε hb0 hb1 hε0 hεb) :
          Measure (E → Bool)) A).toReal := by
  rw [mass, decrementWeight_eq S hb0 hb1 hε0 hεb]

/-- The increment mass is the mass of the paper's `incrementProfile`. -/
theorem incMass_eq_incrementProfile {E : Type*} (A : Set (E → Bool)) (S : Set E)
    {a ε : ℝ} (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε) (haε1 : a + ε ≤ 1) :
    incMass A S a ε =
      ((FKLimit.bernoulliProduct
        (FK.EssentialWindow.incrementProfile S a ε ha0 hε0 haε1) :
          Measure (E → Bool)) A).toReal := by
  rw [incMass, incrementWeight_eq S ha0 hε0 haε1]

/-- The increment mass is a decrement mass of the complementary set. -/
theorem incMass_eq_mass_compl {E : Type*} (A : Set (E → Bool)) (S : Set E) (a ε : ℝ) :
    incMass A S a ε = mass A Sᶜ (a + ε) ε := by
  rw [incMass, mass, incrementWeight_eq_decrementWeight_compl]

/-- Masses are nonnegative. -/
theorem mass_nonneg {E : Type*} (A : Set (E → Bool)) (S : Set E) (b ε : ℝ) :
    0 ≤ mass A S b ε := ENNReal.toReal_nonneg

/-- Masses are at most one. -/
theorem mass_le_one {E : Type*} (A : Set (E → Bool)) (S : Set E) (b ε : ℝ) :
    mass A S b ε ≤ 1 := by
  rw [mass]
  simpa using ENNReal.toReal_mono (by simp) (prob_le_one (μ := (FKLimit.bernoulliProduct
    (decrementWeight S b ε) : Measure (E → Bool))) (s := A))

/-! ## Discharging the approximation-convergence hypothesis -/

/-- Continuity from below for the profile masses: if `An` is an increasing
sequence of events with union `A`, the masses of `An` converge to the mass of
`A`.  This discharges the hypothesis `hconv` of the shift theorems from
pointwise union data on the events. -/
theorem bernoulliProduct_tendsto_toReal_of_iUnion {E : Type*} [Countable E]
    (r : E → unitInterval) (A : Set (E → Bool)) (An : ℕ → Set (E → Bool))
    (hmono : Monotone An) (hUnion : A = ⋃ n, An n) :
    Tendsto (fun n => (((FKLimit.bernoulliProduct r : Measure (E → Bool)) (An n)).toReal))
      atTop (𝓝 (((FKLimit.bernoulliProduct r : Measure (E → Bool)) A).toReal)) := by
  have htend : Tendsto (fun n => ((FKLimit.bernoulliProduct r : Measure (E → Bool)) (An n)))
      atTop (𝓝 (((FKLimit.bernoulliProduct r : Measure (E → Bool)) (⋃ n, An n)))) :=
    tendsto_measure_iUnion_atTop hmono
  have hfin : (((FKLimit.bernoulliProduct r : Measure (E → Bool)) (⋃ n, An n))) ≠ ∞ :=
    measure_ne_top _ _
  have hcomp := (ENNReal.tendsto_toReal hfin).comp htend
  rw [hUnion]
  simpa [Function.comp_def] using hcomp

/-- Continuity from below for the decrement profile masses. -/
theorem mass_tendsto_of_iUnion {E : Type*} [Countable E] (A : Set (E → Bool))
    (An : ℕ → Set (E → Bool)) (S : Set E) (b ε : ℝ)
    (hmono : Monotone An) (hUnion : A = ⋃ n, An n) :
    Tendsto (fun n => mass (An n) S b ε) atTop (𝓝 (mass A S b ε)) :=
  bernoulliProduct_tendsto_toReal_of_iUnion (decrementWeight S b ε) A An hmono hUnion

/-- Continuity from below for the increment profile masses. -/
theorem incMass_tendsto_of_iUnion {E : Type*} [Countable E] (A : Set (E → Bool))
    (An : ℕ → Set (E → Bool)) (S : Set E) (a ε : ℝ)
    (hmono : Monotone An) (hUnion : A = ⋃ n, An n) :
    Tendsto (fun n => incMass (An n) S a ε) atTop (𝓝 (incMass A S a ε)) :=
  bernoulliProduct_tendsto_toReal_of_iUnion (incrementWeight S a ε) A An hmono hUnion

/-! ## Monotonicity of the profile mass in the decrement -/

/-- A larger decrement gives pointwise smaller weights. -/
theorem decrementWeight_anti {E : Type*} (S : Set E) {b ε ε' : ℝ} (h : ε ≤ ε') :
    decrementWeight S b ε' ≤ decrementWeight S b ε := by
  intro e
  simp only [decrementWeight]
  apply Subtype.coe_le_coe.mp
  simp only
  classical
  by_cases he : e ∈ S
  · simp only [ite_eq_left he]
    exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
  · simp only [ite_eq_right he]
    exact le_rfl

/-- For an increasing event, a larger decrement cannot increase the mass. -/
theorem mass_anti_decrement {E : Type*} [Countable E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) (S : Set E) {b ε ε' : ℝ}
    (h : ε ≤ ε') :
    mass A S b ε' ≤ mass A S b ε := by
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
    (r := decrementWeight S b ε') (s := decrementWeight S b ε)
    (decrementWeight_anti S h)
  have hle := FK.EssentialWindow.measure_le_of_stochasticallyDominates hdom hmeas hA
  rw [mass, mass]
  exact ENNReal.toReal_mono (by simp) hle

/-- A larger increment gives pointwise larger weights. -/
theorem incrementWeight_mono {E : Type*} (S : Set E) {a ε ε' : ℝ} (h : ε ≤ ε') :
    incrementWeight S a ε ≤ incrementWeight S a ε' := by
  intro e
  simp only [incrementWeight]
  apply Subtype.coe_le_coe.mp
  simp only
  classical
  by_cases he : e ∈ S
  · simp only [ite_eq_left he]
    exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
  · simp only [ite_eq_right he]
    exact le_rfl

/-- For an increasing event, a larger increment cannot decrease the mass. -/
theorem incMass_mono_increment {E : Type*} [Countable E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) (S : Set E) {a ε ε' : ℝ}
    (h : ε ≤ ε') :
    incMass A S a ε ≤ incMass A S a ε' := by
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
    (r := incrementWeight S a ε) (s := incrementWeight S a ε')
    (incrementWeight_mono S h)
  have hle := FK.EssentialWindow.measure_le_of_stochasticallyDominates hdom hmeas hA
  rw [incMass, incMass]
  exact ENNReal.toReal_mono (by simp) hle

/-- At zero decrement the profile mass does not depend on the enhanced set. -/
theorem mass_zero_eq {E : Type*} (A : Set (E → Bool)) (S S' : Set E) (b : ℝ) :
    mass A S b 0 = mass A S' b 0 := by
  have h : decrementWeight S b 0 = decrementWeight S' b 0 := by
    funext e
    apply Subtype.ext
    simp [decrementWeight]
  rw [mass, mass, h]

/-- At zero increment the increment mass is the homogeneous base mass. -/
theorem incMass_zero {E : Type*} (A : Set (E → Bool)) (S : Set E) (a : ℝ) :
    incMass A S a 0 = mass A S a 0 := by
  rw [incMass_eq_mass_compl]
  have h : a + 0 = a := by ring
  rw [h]
  exact mass_zero_eq A Sᶜ S a

/-- The increment mass is the decrement mass of the complementary set. -/
theorem incMassPair_eq {E : Type*} (A : Set (E → Bool)) (S : Set E) (u : ℝ × ℝ) :
    incMass A S u.1 u.2 = mass A Sᶜ (u.1 + u.2) u.2 := incMass_eq_mass_compl A S u.1 u.2

/-! ## The mean value lemma on a segment -/

/-- Lagrange mean value theorem, contrapositive form: non-positive derivative on a
segment implies the function does not increase along it. -/
theorem le_of_deriv_nonpos {F F' : ℝ → ℝ} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hderiv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt F (F' t) t)
    (hcont : ContinuousOn F (Icc t₀ t₁))
    (hF' : ∀ t ∈ Ioo t₀ t₁, F' t ≤ 0) : F t₁ ≤ F t₀ := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F F' ht hcont hderiv
  have hle : F' c ≤ 0 := hF' c hc
  rw [hslope] at hle
  have hpos : (0:ℝ) < t₁ - t₀ := sub_pos.mpr ht
  have hnonpos : F t₁ - F t₀ ≤ 0 := by
    by_contra h
    push Not at h
    exact absurd hle (not_le.mpr (div_pos h hpos))
  linarith

/-- The analogous monotone form: non-negative derivative on a segment implies the
function does not decrease along it. -/
theorem le_of_deriv_nonneg {F F' : ℝ → ℝ} {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hderiv : ∀ t ∈ Ioo t₀ t₁, HasDerivAt F (F' t) t)
    (hcont : ContinuousOn F (Icc t₀ t₁))
    (hF' : ∀ t ∈ Ioo t₀ t₁, 0 ≤ F' t) : F t₀ ≤ F t₁ := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F F' ht hcont hderiv
  have hle : 0 ≤ F' c := hF' c hc
  rw [hslope] at hle
  have hpos : (0:ℝ) < t₁ - t₀ := sub_pos.mpr ht
  have hnonneg : 0 ≤ F t₁ - F t₀ := by
    by_contra h
    push Not at h
    exact absurd hle (not_le.mpr (div_neg_of_neg_of_pos h hpos))
  linarith

/-! ## Differentiating finite-volume masses along a trade line -/

section Line

variable {E : Type*}

/-- Derivative of a finite-volume profile mass along an affine line in the
parameter plane, from the Fréchet derivative of the mass as a function of
`(b, ε)`.  The line must stay in the region `0 ≤ ε ≤ b ≤ 1`. -/
theorem line_hasDerivAt (_A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (massPair (An n) S) (L n b ε) (b, ε))
    {p q b₀ ε₀ : ℝ} {t₀ t₁ : ℝ}
    (hregion : ∀ t ∈ Icc t₀ t₁, 0 ≤ ε₀ + q * t ∧ ε₀ + q * t ≤ b₀ + p * t ∧
      b₀ + p * t ≤ 1)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + p * s, ε₀ + q * s))
      ((L n (b₀ + p * t) (ε₀ + q * t)) (p, q)) t := by
  obtain ⟨h1, h2, h3⟩ := hregion t ht
  have hf := hderiv n (b₀ + p * t) (ε₀ + q * t) h1 h2 h3
  have hγ : HasDerivAt (fun s : ℝ => (b₀ + p * s, ε₀ + q * s)) (p, q) t := by
    have hlin : HasDerivAt (fun s : ℝ => b₀ + p * s) p t := by
      simpa using (hasDerivAt_const_mul (x := t) p).const_add b₀
    have hlin' : HasDerivAt (fun s : ℝ => ε₀ + q * s) q t := by
      simpa using (hasDerivAt_const_mul (x := t) q).const_add ε₀
    exact hlin.prodMk hlin'
  exact hf.comp_hasDerivAt t hγ

end Line

/-- The increment mass as a function on the parameter plane. -/
def incMassPair {E : Type*} (A : Set (E → Bool)) (S : Set E) : ℝ × ℝ → ℝ :=
  fun u => incMass A S u.1 u.2

/-- Masses of the increment profile are nonnegative. -/
theorem incMass_nonneg {E : Type*} (A : Set (E → Bool)) (S : Set E) (a ε : ℝ) :
    0 ≤ incMass A S a ε := ENNReal.toReal_nonneg

/-- Masses of the increment profile are at most one. -/
theorem incMass_le_one {E : Type*} (A : Set (E → Bool)) (S : Set E) (a ε : ℝ) :
    incMass A S a ε ≤ 1 := by
  rw [incMass_eq_mass_compl]
  exact mass_le_one A Sᶜ (a + ε) ε

/-- Derivative of a finite-volume increment mass along an affine line in the
`(a, ε)` parameter plane. -/
theorem incLine_hasDerivAt (_A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      HasFDerivAt (incMassPair (An n) S) (L n a ε) (a, ε))
    {p q a₀ ε₀ : ℝ} {t₀ t₁ : ℝ}
    (hregion : ∀ t ∈ Icc t₀ t₁, 0 ≤ a₀ + p * t ∧ 0 ≤ ε₀ + q * t ∧
      a₀ + p * t + (ε₀ + q * t) ≤ 1)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    HasDerivAt ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + p * s, ε₀ + q * s))
      ((L n (a₀ + p * t) (ε₀ + q * t)) (p, q)) t := by
  obtain ⟨h1, h2, h3⟩ := hregion t ht
  have hf := hderiv n (a₀ + p * t) (ε₀ + q * t) h1 h2 h3
  have hγ : HasDerivAt (fun s : ℝ => (a₀ + p * s, ε₀ + q * s)) (p, q) t := by
    have hlin : HasDerivAt (fun s : ℝ => a₀ + p * s) p t := by
      simpa using (hasDerivAt_const_mul (x := t) p).const_add a₀
    have hlin' : HasDerivAt (fun s : ℝ => ε₀ + q * s) q t := by
      simpa using (hasDerivAt_const_mul (x := t) q).const_add ε₀
    exact hlin.prodMk hlin'
  exact hf.comp_hasDerivAt t hγ

/-! ## The strict increment shift -/

/-- **Strict increment shift from a uniform differential bound.**

This is the enhancement estimate in its natural form: lowering the base at rate
`c` while raising the increment at rate one along `(a, ε) ↦ (a - c·s, ε + s)`
does not decrease the finite-volume connection probability.  The conclusion is
the strict shift used by `FK.AGWindow.lowerWindow_of_AG_q_lt_one` and
`lowerWindow_of_AG_one_lt_q`. -/
theorem exists_supercritical_increment
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      HasFDerivAt (incMassPair (An n) S) (L n a ε) (a, ε))
    (htrade : ∀ (n : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      0 ≤ (L n a ε) (-c, 1))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1 - pc) / 2) (hεpc : ε < pc / 2) :
    ∃ a, 0 ≤ a ∧ a < pc ∧ a + ε ≤ 1 ∧ incMass A S a ε = 1 := by
  set a₀ : ℝ := pc + c * ε / 2 with ha₀
  set a₁ : ℝ := pc - c * ε / 2 with ha₁
  have hεpc1 : ε < 1 - pc := by linarith
  have ha₀pc : pc < a₀ := by rw [ha₀]; nlinarith
  have ha₀1 : a₀ ≤ 1 := by rw [ha₀]; nlinarith
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; nlinarith
  have ha₁pc : a₁ < pc := by rw [ha₁]; nlinarith
  have hεa₁ : a₁ + ε ≤ 1 := by rw [ha₁]; nlinarith
  refine ⟨a₁, ha₁0, ha₁pc, hεa₁, ?_⟩
  have hregionClean : ∀ t ∈ Icc (0:ℝ) ε, 0 ≤ a₀ + (-c) * t ∧ 0 ≤ 0 + 1 * t ∧
      a₀ + (-c) * t + (0 + 1 * t) ≤ 1 := by
    intro t ht
    obtain ⟨ht0, htε⟩ := ht
    have h1 : 0 ≤ a₀ + (-c) * t := by
      have : (-c) * t ≥ (-c) * ε := by nlinarith
      have h0 : a₀ + (-c) * ε = a₁ := by rw [ha₀, ha₁]; ring
      nlinarith
    have h2 : 0 ≤ 0 + 1 * t := by linarith
    have h3 : a₀ + (-c) * t + (0 + 1 * t) ≤ 1 := by
      have hle : (-c) * t ≤ (-c) * 0 := by nlinarith
      have : a₀ + (-c) * t + (0 + 1 * t) ≤ a₀ + 0 + (0 + 1 * ε) := by nlinarith
      have h4 : a₀ + 0 + (0 + 1 * ε) = pc + c * ε / 2 + ε := by rw [ha₀]; ring
      nlinarith
    exact ⟨h1, h2, h3⟩
  have hstep : ∀ n, incMass (An n) S a₁ ε ≥ incMass (An n) S a₀ 0 := by
    intro n
    have hcont : ContinuousOn
        ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) (Icc 0 ε) :=
      fun t ht => (incLine_hasDerivAt A An S L hderiv hregionClean n ht).continuousAt.continuousWithinAt
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))
          ((L n (a₀ + (-c) * t) (0 + 1 * t)) (-c, 1)) t :=
      fun t ht => incLine_hasDerivAt A An S L hderiv hregionClean n (Ioo_subset_Icc_self ht)
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        0 ≤ ((L n (a₀ + (-c) * t) (0 + 1 * t)) (-c, 1)) := by
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hregionClean t (Ioo_subset_Icc_self ht)
      exact htrade n (a₀ + (-c) * t) (0 + 1 * t) h1 h2 h3
    have hval := le_of_deriv_nonneg hε0 hderiv' hcont hbound
    have h₁ : ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) ε =
        incMass (An n) S a₁ ε := by
      change incMass (An n) S (a₀ + (-c) * ε) (0 + 1 * ε) = incMass (An n) S a₁ ε
      rw [show a₀ + (-c) * ε = a₁ by rw [ha₀, ha₁]; ring,
        show 0 + 1 * ε = ε by ring]
    have h₀ : ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) 0 =
        incMass (An n) S a₀ 0 := by
      change incMass (An n) S (a₀ + (-c) * 0) (0 + 1 * 0) = incMass (An n) S a₀ 0
      norm_num
    rw [h₁, h₀] at hval
    exact hval
  have hlow : incMass A S a₀ 0 ≤ incMass A S a₁ ε :=
    le_of_tendsto_of_tendsto (hconv a₀ 0) (hconv a₁ ε)
      (Eventually.of_forall (fun n => hstep n))
  rw [hbase a₀ ha₀pc ha₀1] at hlow
  exact le_antisymm (incMass_le_one A S a₁ ε) hlow

/-! ## The strict decrement shift -/

section Shift

variable {E : Type*}

/-- **Strict decrement shift from a uniform differential bound.**

`An n` are finite-support (in particular cylinder) increasing approximations of the
target event `A`, `mass (An n) S b ε` is the mass under the profile with weights
`b - ε` on `S` and `b` elsewhere, and `L n b ε` is its Fréchet derivative in
`(b, ε)`.  The hypothesis `htrade` is the finite-volume essential-enhancement
estimate: moving along `(b, ε) ↦ (b + c·s, ε + s)`, i.e. raising the base at rate
`c` while raising the decrement at rate one, does not increase the connection
probability.  The conclusion is the strict shift `hAG` used by
`FK.AGWindow.upperWindow_of_AG_q_lt_one`. -/
theorem exists_subcritical_decrement
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (massPair (An n) S) (L n b ε) (b, ε))
    (htrade : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 → (L n b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2) (hε1 : ε < (1 - pc) / 2) :
    ∃ b, pc < b ∧ b ≤ 1 ∧ ε ≤ b ∧ mass A S b ε = 0 := by
  set b₀ : ℝ := pc - c * ε / 2 with hb₀
  set b₁ : ℝ := pc + c * ε / 2 with hb₁
  have hcε : 0 < c * ε := mul_pos hc0 hε0
  have hεpc' : ε ≤ pc := by linarith
  have hb₀pc2 : pc / 2 ≤ b₀ := by rw [hb₀]; nlinarith
  have hb₀0 : 0 ≤ b₀ := le_trans (by linarith) hb₀pc2
  have hb₀pc : b₀ < pc := by rw [hb₀]; nlinarith
  have hb₁pc : pc < b₁ := by rw [hb₁]; nlinarith
  have hb₁1 : b₁ ≤ 1 := by rw [hb₁]; nlinarith
  have hεb₁ : ε ≤ b₁ := by rw [hb₁]; nlinarith
  refine ⟨b₁, hb₁pc, hb₁1, hεb₁, ?_⟩
  have hregionClean : ∀ t ∈ Icc (0:ℝ) ε, 0 ≤ t ∧ t ≤ b₀ + c * t ∧
      b₀ + c * t ≤ 1 := by
    intro t ht
    obtain ⟨ht0, htε⟩ := ht
    have ht_pc : t ≤ pc / 2 := le_trans htε hεpc.le
    have h1 : t ≤ b₀ + c * t := by
      have : t ≤ b₀ := le_trans ht_pc hb₀pc2
      nlinarith
    have h2 : b₀ + c * t ≤ 1 := by
      have hct : c * t ≤ c * ε := by nlinarith
      have hb₀eq : b₀ + c * ε = b₁ := by rw [hb₀, hb₁]; ring
      nlinarith
    exact ⟨ht0, h1, h2⟩
  have hregion : ∀ t ∈ Icc (0:ℝ) ε, 0 ≤ 0 + 1 * t ∧ 0 + 1 * t ≤ b₀ + c * t ∧
      b₀ + c * t ≤ 1 := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hregionClean t ht
    exact ⟨by linarith, by linarith, h3⟩
  have hstep : ∀ n, mass (An n) S b₁ ε ≤ mass (An n) S b₀ 0 := by
    intro n
    have hcont : ContinuousOn
        ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) (Icc 0 ε) :=
      fun t ht => (line_hasDerivAt A An S L hderiv hregion n ht).continuousAt.continuousWithinAt
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s))
          ((L n (b₀ + c * t) (0 + 1 * t)) (c, 1)) t :=
      fun t ht => line_hasDerivAt A An S L hderiv hregion n (Ioo_subset_Icc_self ht)
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        ((L n (b₀ + c * t) (0 + 1 * t)) (c, 1)) ≤ 0 := by
      intro t ht
      obtain ⟨h1, h2, h3⟩ := hregionClean t (Ioo_subset_Icc_self ht)
      exact htrade n (b₀ + c * t) (0 + 1 * t) (by linarith) (by linarith) h3
    have hval := le_of_deriv_nonpos hε0 hderiv' hcont hbound
    have h₁ : ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) ε =
        mass (An n) S b₁ ε := by
      change mass (An n) S (b₀ + c * ε) (0 + 1 * ε) = mass (An n) S b₁ ε
      rw [show b₀ + c * ε = b₁ by rw [hb₀, hb₁]; ring, show 0 + 1 * ε = ε by ring]
    have h₀ : ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) 0 =
        mass (An n) S b₀ 0 := by
      change mass (An n) S (b₀ + c * 0) (0 + 1 * 0) = mass (An n) S b₀ 0
      norm_num
    rw [h₁, h₀] at hval
    exact hval
  have hub : mass A S b₁ ε ≤ mass A S b₀ 0 :=
    le_of_tendsto_of_tendsto (hconv b₁ ε) (hconv b₀ 0) (Eventually.of_forall hstep)
  rw [hbase b₀ hb₀0 hb₀pc] at hub
  exact le_antisymm hub (mass_nonneg A S b₁ ε)

end Shift

/-! ## Producing the `FK.AGWindow` strict-shift inputs -/

section Wrapper

variable {E : Type*} [Countable E]

/-- The decrement strict shift in exactly the shape consumed by
`FK.EssentialWindow.upperWindow_of_AG_q_lt_one` and
`upperWindow_of_AG_one_lt_q`. -/
theorem decrement_AGInput
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (massPair (An n) S) (L n b ε) (b, ε))
    (htrade : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 → (L n b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < pc / 2 →
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
  intro ε hε0 hεpc
  set ε' : ℝ := min ε ((1 - pc) / 4) with hε'
  have hε'0 : 0 < ε' := lt_min hε0 (by linarith)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'pc : ε' < pc / 2 := lt_of_le_of_lt hε'ε hεpc
  have hε'1 : ε' < (1 - pc) / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨b, hpcb, hb1, hε'b, hmass⟩ :=
    exists_subcritical_decrement A An S pc c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv
      hbase ε' hε'0 hε'pc hε'1
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  have hεb : ε ≤ b := by linarith
  refine ⟨b, hpcb, hb1, hεb, ?_⟩
  have hmono : mass A S b ε ≤ mass A S b ε' := mass_anti_decrement hA hmeas S hε'ε
  have hzero : mass A S b ε = 0 :=
    le_antisymm (by rw [hmass] at hmono; exact hmono) (mass_nonneg A S b ε)
  have hm : ((FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
      hb0 hb1 hε0.le hεb) : Measure (E → Bool)) A) = 0 := by
    have h := hzero
    rw [mass_eq_decrementProfile A S hb0 hb1 hε0.le hεb] at h
    rcases (ENNReal.toReal_eq_zero_iff _).mp h with h' | h'
    · exact h'
    · exact absurd h' (measure_ne_top _ _)
  exact hm

/-- The increment strict shift in exactly the shape consumed by
`FK.EssentialWindow.lowerWindow_of_AG_q_lt_one` and `lowerWindow_of_AG_one_lt_q`. -/
theorem increment_AGInput
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      HasFDerivAt (incMassPair (An n) S) (L n a ε) (a, ε))
    (htrade : ∀ (n : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      0 ≤ (L n a ε) (-c, 1))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < (1 - pc) / 2 →
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ _hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
          ha0 hε0.le haε1) : Measure (E → Bool)) A = 1 := by
  intro ε hε0 hεpc
  set ε' : ℝ := min ε (min (pc / 4) ((1 - pc) / 4)) with hε'
  have hε'0 : 0 < ε' := lt_min hε0 (lt_min (by linarith) (by linarith))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'pc : ε' < pc / 2 := by
    have h1 : ε' ≤ pc / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hε'1 : ε' < (1 - pc) / 2 := by
    have h1 : ε' ≤ (1 - pc) / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨a, ha0, _hapc, haε1, hmass⟩ :=
    exists_supercritical_increment A An S pc c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv
      hbase ε' hε'0 hε'1 hε'pc
  have haε1' : a + ε ≤ 1 := by linarith
  refine ⟨a, ha0, _hapc, haε1', ?_⟩
  have hmono : incMass A S a ε' ≤ incMass A S a ε := incMass_mono_increment hA hmeas S hε'ε
  have hone : incMass A S a ε = 1 :=
    le_antisymm (incMass_le_one A S a ε) (by rw [hmass] at hmono; exact hmono)
  have hm : ((FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
      ha0 hε0.le haε1') : Measure (E → Bool)) A) = 1 := by
    have h := hone
    rw [incMass_eq_incrementProfile A S ha0 hε0.le haε1'] at h
    exact (ENNReal.toReal_eq_one_iff _).mp h
  exact hm

end Wrapper

/-! ## Windows from the differential bound -/

section Windows

variable {E : Type*} [Countable E]

/-- Upper parameter window for `q < 1` from the uniform decrement trade bound. -/
theorem upperWindow_of_decrementTrade_q_lt_one
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (k : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (massPair (An k) Ee) (L k b ε) (b, ε))
    (htrade : ∀ (k : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 → (L k b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto (fun k => mass (An k) Ee b ε) atTop
      (𝓝 (mass A Ee b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A Ee b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.upperWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (decrement_AGInput A An Ee pc c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv hbase hA hmeas)

/-- Lower parameter window for `q < 1` from the uniform increment trade bound. -/
theorem lowerWindow_of_incrementTrade_q_lt_one
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (k : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      HasFDerivAt (incMassPair (An k) Eb) (L k a ε) (a, ε))
    (htrade : ∀ (k : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      0 ≤ (L k a ε) (-c, 1))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun k => incMass (An k) Eb a ε) atTop
      (𝓝 (incMass A Eb a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A Eb a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.lowerWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (increment_AGInput A An Eb pc c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv hbase hA hmeas)

/-- Upper parameter window for `1 < q` from the uniform decrement trade bound. -/
theorem upperWindow_of_decrementTrade_one_lt_q
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (k : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (massPair (An k) Eb) (L k b ε) (b, ε))
    (htrade : ∀ (k : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 → (L k b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto (fun k => mass (An k) Eb b ε) atTop
      (𝓝 (mass A Eb b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A Eb b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.upperWindow_of_AG_one_lt_q A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (decrement_AGInput A An Eb pc c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv hbase hA hmeas)

/-- Lower parameter window for `1 < q` from the uniform increment trade bound. -/
theorem lowerWindow_of_incrementTrade_one_lt_q
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (k : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      HasFDerivAt (incMassPair (An k) Ee) (L k a ε) (a, ε))
    (htrade : ∀ (k : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      0 ≤ (L k a ε) (-c, 1))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun k => incMass (An k) Ee a ε) atTop
      (𝓝 (incMass A Ee a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A Ee a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.lowerWindow_of_AG_one_lt_q A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (increment_AGInput A An Ee pc c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv hbase hA hmeas)

end Windows

/-! ## Non-vacuity of the hypothesis package

The hypotheses of the two shift theorems are consistent: the empty event (or the
full event) satisfies all of them, with zero derivative data.  These instances
do not assert anything about percolation; they certify that the theorem is not
an artefact of contradictory hypotheses. -/

section Nonvacuous

variable {E : Type*}

/-- The empty event satisfies the full decrement hypothesis package. -/
theorem decrement_hypotheses_consistent (S : Set E) (pc c : ℝ)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2) (hε1 : ε < (1 - pc) / 2) :
    ∃ b, pc < b ∧ b ≤ 1 ∧ ε ≤ b ∧ mass (∅ : Set (E → Bool)) S b ε = 0 := by
  have hmass : ∀ (b ε : ℝ), mass (∅ : Set (E → Bool)) S b ε = 0 := by
    intro b ε
    simp [mass]
  refine exists_subcritical_decrement (∅ : Set (E → Bool)) (fun _ => (∅ : Set (E → Bool))) S pc c hpc0 hpc1
    hc0 hc1 (fun _ _ _ => 0)
    (fun n b ε _ _ _ => ?_) (fun n b ε _ _ _ => le_refl (0:ℝ)) (fun b ε => ?_)
    (fun b _ _ => hmass b 0) ε hε0 hεpc hε1
  · exact HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (𝕜 := ℝ) (c := (0:ℝ))
      (x := (b, ε))) (Eventually.of_forall (fun u => by simp [massPair, hmass]))
  · exact tendsto_const_nhds

/-- The full event satisfies the full increment hypothesis package. -/
theorem increment_hypotheses_consistent (S : Set E) (pc c : ℝ)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1 - pc) / 2) (hεpc : ε < pc / 2) :
    ∃ a, 0 ≤ a ∧ a < pc ∧ a + ε ≤ 1 ∧ incMass (Set.univ : Set (E → Bool)) S a ε = 1 := by
  have hone : ∀ (a ε : ℝ), incMass (Set.univ : Set (E → Bool)) S a ε = 1 := by
    intro a ε
    rw [incMass]
    simp
  refine exists_supercritical_increment (Set.univ : Set (E → Bool))
    (fun _ => (Set.univ : Set (E → Bool))) S pc c
    hpc0 hpc1 hc0 hc1 (fun _ _ _ => 0)
    (fun n a ε _ _ _ => ?_) (fun n a ε _ _ _ => le_refl (0:ℝ)) (fun a ε => ?_)
    (fun a _ _ => hone a 0) ε hε0 hε1 hεpc
  · exact HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_const (𝕜 := ℝ) (c := (1:ℝ))
      (x := (a, ε))) (Eventually.of_forall (fun u => by simp [incMassPair, hone]))
  · exact tendsto_const_nhds

end Nonvacuous

end

end FK.AGDifferentialShift
