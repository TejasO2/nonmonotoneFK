import FK.AGPeeling
import FK.ClosedCutsetBridge

/-!
# Finite Margulis--Russo formulas for independent Boolean products

The polynomial `eventWeight` below is defined for arbitrary real parameters.
On the unit cube it is exactly the probability of the event under the
inhomogeneous Bernoulli product. Differentiating this polynomial, rather than
a quotient by `p` or `1-p`, gives formulas valid at `p = 0` and `p = 1` too.

These are finite-volume product-measure ingredients only.  They do not assert
an Aizenman--Grimmett ratio bound, an essential-enhancement theorem, or a
strict shift of a critical point.
-/

open Set MeasureTheory
open scoped Classical BigOperators ENNReal unitInterval

namespace FK.MargulisRussoFinite

open FK.Finite.Comparison
open FK.EssentialEnhancement
open FK.AGPeeling

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The (possibly signed, outside the unit interval) Bernoulli factor. -/
def coordinateWeight (r : ℝ) (b : Bool) : ℝ := if b then r else 1 - r

@[simp] lemma coordinateWeight_true (r : ℝ) : coordinateWeight r true = r := by
  simp [coordinateWeight]

@[simp] lemma coordinateWeight_false (r : ℝ) : coordinateWeight r false = 1 - r := by
  simp [coordinateWeight]

/-- Weight of a finite Boolean configuration under a product with parameters `r`. -/
def configurationWeight (r : E → ℝ) (ω : E → Bool) : ℝ :=
  ∏ e, coordinateWeight (r e) (ω e)

/-- The finite product polynomial of an arbitrary event. -/
def eventWeight (r : E → ℝ) (A : Set (E → Bool)) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ A then configurationWeight r ω else 0

/-- Recombine an off-edge configuration with the bit at `e`. -/
def splice (e : E) (off : Glauber.OffConfig Bool E e) (b : Bool) : E → Bool :=
  (Glauber.configSplit Bool e).symm (off, b)

omit [Fintype E] in
@[simp] lemma splice_same (e : E) (off : Glauber.OffConfig Bool E e) (b : Bool) :
    splice e off b e = b := by
  simp [splice, Glauber.configSplit, Equiv.funSplitAt_symm_apply]

omit [Fintype E] in
@[simp] lemma splice_off (e : E) (off : Glauber.OffConfig Bool E e) (b : Bool)
    (a : {a : E // a ≠ e}) : splice e off b a.1 = off a := by
  simp [splice, Glauber.configSplit, Equiv.funSplitAt_symm_apply, a.2]

omit [Fintype E] in
lemma splice_eq_forceEdge (e : E) (off : Glauber.OffConfig Bool E e) (b : Bool) :
    splice e off b = forceEdge (splice e off false) e b := by
  classical
  ext a
  by_cases h : a = e
  · subst a
    simp
  · simp [forceEdge, splice, Glauber.configSplit,
      Equiv.funSplitAt_symm_apply, h]

/-- Product of all factors except the one at `e`. -/
def offConfigurationWeight (r : E → ℝ) (e : E)
    (off : Glauber.OffConfig Bool E e) : ℝ :=
  ∏ a, coordinateWeight (r a.1) (off a)

lemma configurationWeight_splice (r : E → ℝ) (e : E)
    (off : Glauber.OffConfig Bool E e) (b : Bool) :
    configurationWeight r (splice e off b) =
      coordinateWeight (r e) b * offConfigurationWeight r e off := by
  rw [configurationWeight, Fintype.prod_eq_mul_prod_subtype_ne _ e]
  simp only [splice_same]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  simp

/-- Off-edge polynomial obtained by forcing the distinguished bit to `b`. -/
def offEventWeight (r : E → ℝ) (e : E) (A : Set (E → Bool)) (b : Bool) : ℝ := by
  classical
  exact ∑ off : Glauber.OffConfig Bool E e,
    if splice e off b ∈ A then offConfigurationWeight r e off else 0

/-- Exact coordinate decomposition, including at zero and one. -/
theorem eventWeight_eq_coordinate (r : E → ℝ) (A : Set (E → Bool)) (e : E) :
    eventWeight r A = r e * offEventWeight r e A true +
      (1 - r e) * offEventWeight r e A false := by
  classical
  rw [eventWeight, ← Equiv.sum_comp (Glauber.configSplit Bool e).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  rw [offEventWeight, offEventWeight]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro off _
  rw [show ((Glauber.configSplit Bool e).symm (off, true)) = splice e off true from rfl,
    show ((Glauber.configSplit Bool e).symm (off, false)) = splice e off false from rfl,
    configurationWeight_splice, configurationWeight_splice]
  by_cases ht : splice e off true ∈ A <;>
    by_cases hf : splice e off false ∈ A <;> simp [ht, hf]

/-- The off-edge weight does not see the parameter at its omitted coordinate. -/
lemma offConfigurationWeight_update (r : E → ℝ) (e : E) (x : ℝ)
    (off : Glauber.OffConfig Bool E e) :
    offConfigurationWeight (Function.update r e x) e off =
      offConfigurationWeight r e off := by
  apply Finset.prod_congr rfl
  intro a _
  rw [Function.update_of_ne a.2]

lemma offEventWeight_update (r : E → ℝ) (e : E) (A : Set (E → Bool))
    (b : Bool) (x : ℝ) :
    offEventWeight (Function.update r e x) e A b = offEventWeight r e A b := by
  unfold offEventWeight
  apply Finset.sum_congr rfl
  intro off _
  rw [offConfigurationWeight_update]

/-- One-coordinate Margulis--Russo derivative for an arbitrary event.  For an
increasing event the derivative is the off-edge pivotal probability; no
monotonicity hypothesis is needed for the algebraic identity itself. -/
theorem hasDerivAt_eventWeight_update (r : E → ℝ) (A : Set (E → Bool)) (e : E) :
    HasDerivAt (fun x => eventWeight (Function.update r e x) A)
      (offEventWeight r e A true - offEventWeight r e A false) (r e) := by
  have hfun : (fun x => eventWeight (Function.update r e x) A) =
      (fun x => x * offEventWeight r e A true +
        (1 - x) * offEventWeight r e A false) := by
    funext x
    rw [eventWeight_eq_coordinate (r := Function.update r e x) (A := A) e]
    simp only [Function.update_self, offEventWeight_update]
  rw [hfun]
  convert ((hasDerivAt_id (r e)).mul_const (offEventWeight r e A true)).add
    (((hasDerivAt_const (r e) (1 : ℝ)).sub (hasDerivAt_id (r e))).mul_const
      (offEventWeight r e A false)) using 1
  · funext x
    rfl
  · ring

/-- On the unit cube the product polynomial is the existing real-mass finite
Bernoulli probability. -/
lemma eventWeight_eq_boolProduct_event (r : E → ℝ)
    (hr : ∀ e, r e ∈ Set.Icc (0 : ℝ) 1) (A : Set (E → Bool)) :
    eventWeight r A = (boolProduct r hr).event A := by
  simp only [eventWeight, OpenPath.FinProb.event, configurationWeight, boolProduct,
    OpenPath.FinProb.pi_mass, boolLaw, coordinateWeight]

/-- Off-edge pivotality does not depend on the bit originally at `e`. -/
def OffPivotal (A : Set (E → Bool)) (e : E)
    (off : Glauber.OffConfig Bool E e) : Prop :=
  splice e off true ∈ A ∧ splice e off false ∉ A

/-- The off-edge product mass of the pivotal configurations. -/
def offPivotalWeight (r : E → ℝ) (e : E) (A : Set (E → Bool)) : ℝ := by
  classical
  exact ∑ off : Glauber.OffConfig Bool E e,
    if OffPivotal A e off then offConfigurationWeight r e off else 0

omit [Fintype E] in
lemma splice_false_le_true (e : E) (off : Glauber.OffConfig Bool E e) :
    splice e off false ≤ splice e off true := by
  intro a
  by_cases h : a = e
  · subst a
    simp
  · rw [splice_off e off false ⟨a, h⟩, splice_off e off true ⟨a, h⟩]

omit [Fintype E] in
lemma offPivotal_iff_pivotal (A : Set (E → Bool)) (e : E)
    (off : Glauber.OffConfig Bool E e) :
    OffPivotal A e off ↔ Pivotal A e (splice e off false) := by
  simp only [OffPivotal, Pivotal, ← splice_eq_forceEdge]

/-- **Increasing-event form:** the forced-open/closed difference is precisely
the off-edge pivotal polynomial. -/
theorem offEventWeight_sub_eq_offPivotalWeight {A : Set (E → Bool)}
    (hA : IsUpperSet A) (r : E → ℝ) (e : E) :
    offEventWeight r e A true - offEventWeight r e A false =
      offPivotalWeight r e A := by
  classical
  rw [offEventWeight, offEventWeight, offPivotalWeight, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro off _
  have hfalse_true : splice e off false ∈ A → splice e off true ∈ A :=
    fun h => hA (splice_false_le_true e off) h
  by_cases hf : splice e off false ∈ A
  · have ht : splice e off true ∈ A := hfalse_true hf
    simp [OffPivotal, ht, hf]
  · by_cases ht : splice e off true ∈ A
    · simp [OffPivotal, ht, hf]
    · simp [OffPivotal, ht, hf]

/-- The derivative in the increasing case is pivotal mass. -/
theorem hasDerivAt_eventWeight_update_of_isUpperSet {A : Set (E → Bool)}
    (hA : IsUpperSet A) (r : E → ℝ) (e : E) :
    HasDerivAt (fun x => eventWeight (Function.update r e x) A)
      (offPivotalWeight r e A) (r e) := by
  rw [← offEventWeight_sub_eq_offPivotalWeight hA]
  exact hasDerivAt_eventWeight_update r A e

/-- Total off-edge product weight is one, even before restricting parameters
to the unit interval. -/
lemma sum_offConfigurationWeight (r : E → ℝ) (e : E) :
    (∑ off : Glauber.OffConfig Bool E e, offConfigurationWeight r e off) = 1 := by
  unfold offConfigurationWeight
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool, coordinateWeight_true, coordinateWeight_false]
  simp

lemma offConfigurationWeight_nonneg {r : E → ℝ}
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) (e : E)
    (off : Glauber.OffConfig Bool E e) : 0 ≤ offConfigurationWeight r e off := by
  apply Finset.prod_nonneg
  intro a _
  cases h : off a
  · simp [coordinateWeight_false, (hr a.1).2]
  · simp [coordinateWeight_true, (hr a.1).1]

lemma offPivotalWeight_nonneg {A : Set (E → Bool)} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    0 ≤ offPivotalWeight r e A := by
  classical
  apply Finset.sum_nonneg
  intro off _
  by_cases h : OffPivotal A e off
  · simpa [h] using offConfigurationWeight_nonneg hr e off
  · simp [h]

lemma offPivotalWeight_le_one {A : Set (E → Bool)} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    offPivotalWeight r e A ≤ 1 := by
  classical
  rw [← sum_offConfigurationWeight r e]
  unfold offPivotalWeight
  apply Finset.sum_le_sum
  intro off _
  by_cases h : OffPivotal A e off
  · simp [h]
  · simpa [h] using offConfigurationWeight_nonneg hr e off

/-- Per-coordinate differential boundedness, including at the endpoints. -/
theorem offPivotalWeight_mem_Icc {A : Set (E → Bool)} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    offPivotalWeight r e A ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨offPivotalWeight_nonneg hr e, offPivotalWeight_le_one hr e⟩

/-- The product polynomial agrees with the real probability under the actual
inhomogeneous `Measure.pi` Bernoulli law. -/
theorem eventWeight_eq_bernoulliProduct_toReal (rates : E → I)
    (A : Set (E → Bool)) :
    eventWeight (fun e => (rates e : ℝ)) A =
      (FKEnhancement.bernoulliProduct rates A).toReal := by
  rw [← FKEnhancement.toPMF_boolProduct_toMeasure rates,
    OpenPath.FinProb.toPMF_event]
  exact eventWeight_eq_boolProduct_event (fun e => (rates e : ℝ))
    (fun e => (rates e).2) A

omit [Fintype E] in
lemma forceEdge_splice (e : E) (off : Glauber.OffConfig Bool E e)
    (b c : Bool) : forceEdge (splice e off b) e c = splice e off c := by
  classical
  ext a
  by_cases h : a = e
  · subst a
    simp
  · simp [forceEdge, h, splice_off e off b ⟨a, h⟩, splice_off e off c ⟨a, h⟩]

omit [Fintype E] in
lemma pivotal_splice_iff (A : Set (E → Bool)) (e : E)
    (off : Glauber.OffConfig Bool E e) (b : Bool) :
    Pivotal A e (splice e off b) ↔ OffPivotal A e off := by
  simp only [Pivotal, OffPivotal, forceEdge_splice]

/-- The off-edge pivotal polynomial is exactly the (full-configuration)
polynomial probability of the usual pivotal event. -/
theorem eventWeight_pivotal (r : E → ℝ) (A : Set (E → Bool)) (e : E) :
    eventWeight r {ω | Pivotal A e ω} = offPivotalWeight r e A := by
  classical
  rw [eventWeight, ← Equiv.sum_comp (Glauber.configSplit Bool e).symm,
    Fintype.sum_prod_type]
  unfold offPivotalWeight
  apply Finset.sum_congr rfl
  intro off _
  change (∑ b : Bool, if Pivotal A e (splice e off b) then
      configurationWeight r (splice e off b) else 0) =
    if OffPivotal A e off then offConfigurationWeight r e off else 0
  simp_rw [configurationWeight_splice]
  have hp (b : Bool) : Pivotal A e (splice e off b) ↔ OffPivotal A e off :=
    pivotal_splice_iff A e off b
  by_cases h : OffPivotal A e off
  · simp [hp, h]
    ring
  · simp [hp, h]

/-- Usual full-pivot mass form of the increasing one-coordinate derivative. -/
theorem hasDerivAt_eventWeight_update_pivotal {A : Set (E → Bool)}
    (hA : IsUpperSet A) (r : E → ℝ) (e : E) :
    HasDerivAt (fun x => eventWeight (Function.update r e x) A)
      (eventWeight r {ω | Pivotal A e ω}) (r e) := by
  rw [eventWeight_pivotal]
  exact hasDerivAt_eventWeight_update_of_isUpperSet hA r e

/-- Slope of the one-coordinate Bernoulli polynomial. -/
def coordinateSlope (b : Bool) : ℝ := if b then 1 else -1

lemma hasDerivAt_coordinateWeight (b : Bool) (p : ℝ) :
    HasDerivAt (fun t => coordinateWeight t b) (coordinateSlope b) p := by
  cases b
  · convert (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p) using 1
    · funext x
      rfl
    · simp [coordinateSlope]
  · convert hasDerivAt_id p using 1
    · funext x
      rfl
    · simp [coordinateSlope]

lemma hasDerivAt_configurationWeight_const (ω : E → Bool) (p : ℝ) :
    HasDerivAt (fun t => configurationWeight (fun _ => t) ω)
      (∑ e, (∏ j ∈ Finset.univ.erase e, coordinateWeight p (ω j)) *
        coordinateSlope (ω e)) p := by
  simpa [configurationWeight, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun e t => coordinateWeight t (ω e))
      (f' := fun e => coordinateSlope (ω e))
      (fun e _ => hasDerivAt_coordinateWeight (ω e) p))

lemma hasDerivAt_eventWeight_const_raw (A : Set (E → Bool)) (p : ℝ) :
    HasDerivAt (fun t => eventWeight (fun _ => t) A)
      (∑ ω, if ω ∈ A then
        ∑ e, (∏ j ∈ Finset.univ.erase e, coordinateWeight p (ω j)) *
          coordinateSlope (ω e) else 0) p := by
  classical
  unfold eventWeight
  apply HasDerivAt.fun_sum
  intro ω _
  by_cases hω : ω ∈ A
  · simpa only [hω, ite_true] using hasDerivAt_configurationWeight_const ω p
  · simpa [hω] using hasDerivAt_const p (0 : ℝ)

lemma offConfigurationWeight_eq_prod_erase (r : E → ℝ) (e : E)
    (off : Glauber.OffConfig Bool E e) (b : Bool) :
    offConfigurationWeight r e off =
      ∏ a ∈ Finset.univ.erase e, coordinateWeight (r a) (splice e off b a) := by
  rw [Finset.prod_subtype (p := fun a : E => a ≠ e) (Finset.univ.erase e)
    (fun a => by simp [Finset.mem_erase])
    (fun a => coordinateWeight (r a) (splice e off b a))]
  apply Finset.prod_congr rfl
  intro a _
  rw [splice_off]

/-- Reindexing the raw derivative of one configuration over the coordinates
other than `e`. -/
lemma sum_configurationWeight_slope (A : Set (E → Bool)) (p : ℝ) (e : E) :
    (∑ ω, if ω ∈ A then
      (∏ j ∈ Finset.univ.erase e, coordinateWeight p (ω j)) *
        coordinateSlope (ω e) else 0) =
      offEventWeight (fun _ => p) e A true -
        offEventWeight (fun _ => p) e A false := by
  classical
  rw [← Equiv.sum_comp (Glauber.configSplit Bool e).symm, Fintype.sum_prod_type]
  rw [offEventWeight, offEventWeight, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro off _
  change (∑ b : Bool, if splice e off b ∈ A then
      (∏ j ∈ Finset.univ.erase e, coordinateWeight p (splice e off b j)) *
        coordinateSlope (splice e off b e) else 0) = _
  simp_rw [← offConfigurationWeight_eq_prod_erase (fun _ => p) e off]
  by_cases ht : splice e off true ∈ A <;>
    by_cases hf : splice e off false ∈ A <;>
    simp [ht, hf, coordinateSlope]

/-- **Homogeneous finite Margulis--Russo formula.**  The derivative of the
probability polynomial along all coordinates is the sum of the off-edge
pivotal polynomials. -/
theorem hasDerivAt_eventWeight_const {A : Set (E → Bool)}
    (hA : IsUpperSet A) (p : ℝ) :
    HasDerivAt (fun t => eventWeight (fun _ => t) A)
      (∑ e, offPivotalWeight (fun _ => p) e A) p := by
  convert hasDerivAt_eventWeight_const_raw A p using 1
  symm
  calc
    (∑ ω, if ω ∈ A then
        ∑ e, (∏ j ∈ Finset.univ.erase e, coordinateWeight p (ω j)) *
          coordinateSlope (ω e) else 0) =
        ∑ ω, ∑ e, if ω ∈ A then
          (∏ j ∈ Finset.univ.erase e, coordinateWeight p (ω j)) *
            coordinateSlope (ω e) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : ω ∈ A <;> simp [hω]
    _ = ∑ e, ∑ ω, if ω ∈ A then
          (∏ j ∈ Finset.univ.erase e, coordinateWeight p (ω j)) *
            coordinateSlope (ω e) else 0 := Finset.sum_comm
    _ = ∑ e, (offEventWeight (fun _ => p) e A true -
          offEventWeight (fun _ => p) e A false) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_configurationWeight_slope A p e
    _ = ∑ e, offPivotalWeight (fun _ => p) e A := by
      apply Finset.sum_congr rfl
      intro e _
      exact offEventWeight_sub_eq_offPivotalWeight hA (fun _ => p) e

/-- Equivalent homogeneous formula using the usual full-configuration pivotal
events. -/
theorem hasDerivAt_eventWeight_const_pivotal {A : Set (E → Bool)}
    (hA : IsUpperSet A) (p : ℝ) :
    HasDerivAt (fun t => eventWeight (fun _ => t) A)
      (∑ e, eventWeight (fun _ => p) {ω | Pivotal A e ω}) p := by
  convert hasDerivAt_eventWeight_const hA p using 1
  apply Finset.sum_congr rfl
  intro e _
  exact eventWeight_pivotal (fun _ => p) A e

/-- Pivot probabilities are bounded by one and their sum by the number of
coordinates; this is the elementary differential-boundedness step. -/
theorem sum_offPivotalWeight_nonneg {A : Set (E → Bool)} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ ∑ e, offPivotalWeight r e A := by
  apply Finset.sum_nonneg
  intro e _
  exact offPivotalWeight_nonneg hr e

theorem sum_offPivotalWeight_le_card {A : Set (E → Bool)} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1) :
    (∑ e, offPivotalWeight r e A) ≤ Fintype.card E := by
  calc
    (∑ e, offPivotalWeight r e A) ≤ ∑ _e : E, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact offPivotalWeight_le_one hr e
    _ = Fintype.card E := by simp

/-- A canonical arbitrary extension of a real number to a unit-interval
parameter, used only to formulate the derivative within `[0,1]` of the actual
measure-valued law. -/
def clampUnit (t : ℝ) : I := if h : t ∈ I then ⟨t, h⟩ else 0

lemma clampUnit_of_mem {t : ℝ} (ht : t ∈ I) : clampUnit t = ⟨t, ht⟩ := by
  simp [clampUnit, ht]

/-- The measure-valued Bernoulli probability has the pivotal derivative within
the unit interval, including one-sided derivatives at its endpoints. -/
theorem hasDerivWithinAt_bernoulliProduct_const {A : Set (E → Bool)}
    (hA : IsUpperSet A) (p : ℝ) (hp : p ∈ I) :
    HasDerivWithinAt
      (fun t => (FKEnhancement.bernoulliProduct (fun _ : E => clampUnit t) A).toReal)
      (∑ e, offPivotalWeight (fun _ => p) e A) I p := by
  have heq (t : ℝ) (ht : t ∈ I) :
      (FKEnhancement.bernoulliProduct (fun _ : E => clampUnit t) A).toReal =
        eventWeight (fun _ => t) A := by
    rw [show (fun _ : E => clampUnit t) = (fun _ : E => (⟨t, ht⟩ : I)) by
      funext e
      exact clampUnit_of_mem ht]
    exact (eventWeight_eq_bernoulliProduct_toReal (fun _ : E => (⟨t, ht⟩ : I)) A).symm
  exact (hasDerivAt_eventWeight_const hA p).hasDerivWithinAt.congr
    (fun t ht => heq t ht) (heq p hp)

/-- Vary only one coordinate of an inhomogeneous unit-interval rate profile. -/
def updateUnitRate (r : E → ℝ) (hr : ∀ a, r a ∈ I) (e : E) (t : ℝ) : E → I :=
  Function.update (fun a => ⟨r a, hr a⟩) e (clampUnit t)

omit [Fintype E] in
lemma coe_updateUnitRate_of_mem (r : E → ℝ) (hr : ∀ a, r a ∈ I)
    (e : E) (t : ℝ) (ht : t ∈ I) :
    (fun a => (updateUnitRate r hr e t a : ℝ)) = Function.update r e t := by
  funext a
  by_cases h : a = e
  · subst a
    simp [updateUnitRate, clampUnit_of_mem ht]
  · simp [updateUnitRate, Function.update_of_ne h]

/-- Inhomogeneous selected-coordinate Margulis--Russo formula for the actual
independent product probability.  By taking the index type to be a sum type,
this covers separate bond and enhancement-activation coordinates without
changing their rates or forgetting independence. -/
theorem hasDerivWithinAt_bernoulliProduct_update {A : Set (E → Bool)}
    (hA : IsUpperSet A) (r : E → ℝ) (hr : ∀ a, r a ∈ I) (e : E) :
    HasDerivWithinAt
      (fun t => (FKEnhancement.bernoulliProduct (updateUnitRate r hr e t) A).toReal)
      (offPivotalWeight r e A) I (r e) := by
  have heq (t : ℝ) (ht : t ∈ I) :
      (FKEnhancement.bernoulliProduct (updateUnitRate r hr e t) A).toReal =
        eventWeight (Function.update r e t) A := by
    calc
      (FKEnhancement.bernoulliProduct (updateUnitRate r hr e t) A).toReal =
          eventWeight (fun a => (updateUnitRate r hr e t a : ℝ)) A :=
        (eventWeight_eq_bernoulliProduct_toReal (updateUnitRate r hr e t) A).symm
      _ = eventWeight (Function.update r e t) A := by
        rw [coe_updateUnitRate_of_mem r hr e t ht]
  exact (hasDerivAt_eventWeight_update_of_isUpperSet hA r e).hasDerivWithinAt.congr
    (fun t ht => heq t ht) (heq (r e) (hr e))

/-- Full-pivot probability form of the inhomogeneous selected-coordinate
formula. -/
theorem hasDerivWithinAt_bernoulliProduct_update_pivotal {A : Set (E → Bool)}
    (hA : IsUpperSet A) (r : E → ℝ) (hr : ∀ a, r a ∈ I) (e : E) :
    HasDerivWithinAt
      (fun t => (FKEnhancement.bernoulliProduct (updateUnitRate r hr e t) A).toReal)
      ((FKEnhancement.bernoulliProduct (fun a => (⟨r a, hr a⟩ : I))
        {ω | Pivotal A e ω}).toReal) I (r e) := by
  convert hasDerivWithinAt_bernoulliProduct_update hA r hr e using 1
  rw [← eventWeight_pivotal]
  exact (eventWeight_eq_bernoulliProduct_toReal (fun a => (⟨r a, hr a⟩ : I)) _).symm

/-- Full-pivot probability form of the actual measure-valued derivative. -/
theorem hasDerivWithinAt_bernoulliProduct_const_pivotal {A : Set (E → Bool)}
    (hA : IsUpperSet A) (p : ℝ) (hp : p ∈ I) :
    HasDerivWithinAt
      (fun t => (FKEnhancement.bernoulliProduct (fun _ : E => clampUnit t) A).toReal)
      (∑ e, (FKEnhancement.bernoulliProduct (fun _ : E => (⟨p, hp⟩ : I))
        {ω | Pivotal A e ω}).toReal) I p := by
  convert hasDerivWithinAt_bernoulliProduct_const hA p hp using 1
  apply Finset.sum_congr rfl
  intro e _
  rw [← eventWeight_pivotal]
  exact (eventWeight_eq_bernoulliProduct_toReal (fun _ : E => (⟨p, hp⟩ : I)) _).symm

/-- Normalization of the product polynomial itself. -/
@[simp] theorem eventWeight_univ (r : E → ℝ) : eventWeight r Set.univ = 1 := by
  classical
  unfold eventWeight configurationWeight
  simp only [Set.mem_univ, ite_true]
  rw [← Fintype.prod_sum]
  simp [coordinateWeight]

@[simp] theorem eventWeight_empty (r : E → ℝ) : eventWeight r ∅ = 0 := by
  simp [eventWeight]

/-- The present formulas apply verbatim to the actual lower enhanced product
rate profile; its certificate-dependent edge rates are not replaced by a
homogeneous model. -/
theorem eventWeight_eq_lowerEnhancedLaw_toReal
    (K : E → FKEnhancement.Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (A : Set (E → Bool)) :
    eventWeight (fun e => (FKEnhancement.lowerEnhancedRates K enhanced hp e : ℝ)) A =
      (FKEnhancement.lowerEnhancedLaw K enhanced hp A).toReal :=
  eventWeight_eq_bernoulliProduct_toReal
    (FKEnhancement.lowerEnhancedRates K enhanced hp) A

/-- The corresponding exact normalization for the actual upper enhanced
product law. -/
theorem eventWeight_eq_upperEnhancedLaw_toReal
    (K : E → FKEnhancement.Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (A : Set (E → Bool)) :
    eventWeight (fun e => (FKEnhancement.upperEnhancedRates K enhanced hp e : ℝ)) A =
      (FKEnhancement.upperEnhancedLaw K enhanced hp A).toReal :=
  eventWeight_eq_bernoulliProduct_toReal
    (FKEnhancement.upperEnhancedRates K enhanced hp) A

end
end FK.MargulisRussoFinite
