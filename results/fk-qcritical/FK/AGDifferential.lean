import FK.AGEdgeGadget

/-!
# The finite AG differential comparison for the one-edge OR gadget

For the explicit enhancement `ωe OR αe`, this module combines the finite
Margulis--Russo formula with the one-edge bond/activation pivot transport.
It proves

    ∂s τ ≥ (δ / 2) ∂p τ

for every finite increasing event and for the actual enhanced finite-arm
event, with endpoint-safe product-polynomial derivatives.  At unit-cube
parameters the derivative coefficients are probabilities under the genuine
normalized bond/activation product law.

This is the finite differential step for this particular OR enhancement.
Arbitrary bounded-range annular implantation, the infinite-volume limit, and
the general Aizenman--Grimmett strict critical-point shift are not asserted.
-/

open Set
open scoped Classical BigOperators

namespace FK.AGGadget

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison
open FK.MargulisRussoFinite

universe u v

/-- Joint rates with all bond coordinates equal to `t` and activation profile
`s`. -/
def leftRates {E : Type u} {F : Type v} (s : F → ℝ) (t : ℝ) : E ⊕ F → ℝ :=
  Sum.elim (fun _ => t) s

/-- Joint rates with bond profile `r` and all activation coordinates equal to
`t`. -/
def rightRates {E : Type u} {F : Type v} (r : E → ℝ) (t : ℝ) : E ⊕ F → ℝ :=
  Sum.elim r (fun _ => t)

@[simp] lemma leftRates_inl {E : Type u} {F : Type v} (s : F → ℝ) (t : ℝ) (e : E) :
    leftRates s t (Sum.inl e : E ⊕ F) = t := rfl

@[simp] lemma leftRates_inr {E : Type u} {F : Type v} (s : F → ℝ) (t : ℝ) (f : F) :
    leftRates s t (Sum.inr f : E ⊕ F) = s f := rfl

@[simp] lemma rightRates_inl {E : Type u} {F : Type v} (r : E → ℝ) (t : ℝ) (e : E) :
    rightRates r t (Sum.inl e : E ⊕ F) = r e := rfl

@[simp] lemma rightRates_inr {E : Type u} {F : Type v} (r : E → ℝ) (t : ℝ) (f : F) :
    rightRates r t (Sum.inr f : E ⊕ F) = t := rfl

/-- Raw product derivative when every bond coordinate moves together. -/
lemma hasDerivAt_configurationWeight_left
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (s : F → ℝ) (χ : JointConfig E F) (t : ℝ) :
    HasDerivAt (fun x => configurationWeight (leftRates s x) χ)
      (∑ e : E, (∏ j ∈ Finset.univ.erase (Sum.inl e),
        coordinateWeight (leftRates s t j) (χ j)) *
          coordinateSlope (χ (Sum.inl e))) t := by
  have hderiv (x : E ⊕ F) :
      HasDerivAt (fun y => coordinateWeight (leftRates s y x) (χ x))
        (match x with
          | Sum.inl e => coordinateSlope (χ (Sum.inl e))
          | Sum.inr _ => 0) t := by
    cases x with
    | inl e => exact hasDerivAt_coordinateWeight _ _
    | inr f =>
        simpa using hasDerivAt_const t (coordinateWeight (s f) (χ (Sum.inr f)))
  simpa [configurationWeight, smul_eq_mul, Fintype.sum_sum_type] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun x y => coordinateWeight (leftRates s y x) (χ x))
      (f' := fun x => match x with
        | Sum.inl e => coordinateSlope (χ (Sum.inl e))
        | Sum.inr _ => 0)
      (fun x _ => hderiv x))

/-- Raw product derivative when every activation coordinate moves together. -/
lemma hasDerivAt_configurationWeight_right
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (r : E → ℝ) (χ : JointConfig E F) (t : ℝ) :
    HasDerivAt (fun x => configurationWeight (rightRates r x) χ)
      (∑ f : F, (∏ j ∈ Finset.univ.erase (Sum.inr f),
        coordinateWeight (rightRates r t j) (χ j)) *
          coordinateSlope (χ (Sum.inr f))) t := by
  have hderiv (x : E ⊕ F) :
      HasDerivAt (fun y => coordinateWeight (rightRates r y x) (χ x))
        (match x with
          | Sum.inl _ => 0
          | Sum.inr f => coordinateSlope (χ (Sum.inr f))) t := by
    cases x with
    | inl e =>
        simpa using hasDerivAt_const t (coordinateWeight (r e) (χ (Sum.inl e)))
    | inr f => exact hasDerivAt_coordinateWeight _ _
  simpa [configurationWeight, smul_eq_mul, Fintype.sum_sum_type] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun x y => coordinateWeight (rightRates r y x) (χ x))
      (f' := fun x => match x with
        | Sum.inl _ => 0
        | Sum.inr f => coordinateSlope (χ (Sum.inr f)))
      (fun x _ => hderiv x))

/-- Raw derivative of an arbitrary event under simultaneous bond variation. -/
lemma hasDerivAt_eventWeight_left_raw
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (s : F → ℝ) (A : Set (JointConfig E F)) (t : ℝ) :
    HasDerivAt (fun x => eventWeight (leftRates s x) A)
      (∑ χ, if χ ∈ A then ∑ e : E,
        (∏ j ∈ Finset.univ.erase (Sum.inl e),
          coordinateWeight (leftRates s t j) (χ j)) *
            coordinateSlope (χ (Sum.inl e)) else 0) t := by
  classical
  unfold eventWeight
  apply HasDerivAt.fun_sum
  intro χ _
  by_cases hχ : χ ∈ A
  · simpa only [hχ, ite_true] using hasDerivAt_configurationWeight_left s χ t
  · simpa [hχ] using hasDerivAt_const t (0 : ℝ)

/-- Raw derivative of an arbitrary event under simultaneous activation
variation. -/
lemma hasDerivAt_eventWeight_right_raw
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (r : E → ℝ) (A : Set (JointConfig E F)) (t : ℝ) :
    HasDerivAt (fun x => eventWeight (rightRates r x) A)
      (∑ χ, if χ ∈ A then ∑ f : F,
        (∏ j ∈ Finset.univ.erase (Sum.inr f),
          coordinateWeight (rightRates r t j) (χ j)) *
            coordinateSlope (χ (Sum.inr f)) else 0) t := by
  classical
  unfold eventWeight
  apply HasDerivAt.fun_sum
  intro χ _
  by_cases hχ : χ ∈ A
  · simpa only [hχ, ite_true] using hasDerivAt_configurationWeight_right r χ t
  · simpa [hχ] using hasDerivAt_const t (0 : ℝ)

/-- Inhomogeneous form of the single-coordinate raw slope reindexing. -/
lemma sum_configurationWeight_slope_general
    {E : Type u} [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (r : E → ℝ) (e : E) :
    (∑ ω, if ω ∈ A then
      (∏ j ∈ Finset.univ.erase e, coordinateWeight (r j) (ω j)) *
        coordinateSlope (ω e) else 0) =
      offEventWeight r e A true - offEventWeight r e A false := by
  classical
  rw [← Equiv.sum_comp (Glauber.configSplit Bool e).symm, Fintype.sum_prod_type]
  rw [offEventWeight, offEventWeight, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro off _
  change (∑ b : Bool, if splice e off b ∈ A then
      (∏ j ∈ Finset.univ.erase e, coordinateWeight (r j) (splice e off b j)) *
        coordinateSlope (splice e off b e) else 0) = _
  simp_rw [← offConfigurationWeight_eq_prod_erase r e off]
  by_cases ht : splice e off true ∈ A <;>
    by_cases hf : splice e off false ∈ A <;>
    simp [ht, hf, coordinateSlope]

/-- Bond Margulis--Russo derivative for a joint increasing event. -/
theorem hasDerivAt_eventWeight_left_pivotal
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    {A : Set (JointConfig E F)} (hA : IsUpperSet A) (s : F → ℝ) (t : ℝ) :
    HasDerivAt (fun x => eventWeight (leftRates s x) A)
      (∑ e : E, eventWeight (leftRates s t) {χ | Pivotal A (Sum.inl e) χ}) t := by
  classical
  convert hasDerivAt_eventWeight_left_raw s A t using 1
  symm
  calc
    (∑ χ, if χ ∈ A then ∑ e : E,
        (∏ j ∈ Finset.univ.erase (Sum.inl e),
          coordinateWeight (leftRates s t j) (χ j)) *
            coordinateSlope (χ (Sum.inl e)) else 0) =
        ∑ χ, ∑ e : E, if χ ∈ A then
          (∏ j ∈ Finset.univ.erase (Sum.inl e),
            coordinateWeight (leftRates s t j) (χ j)) *
              coordinateSlope (χ (Sum.inl e)) else 0 := by
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : χ ∈ A <;> simp [hχ]
    _ = ∑ e : E, ∑ χ, if χ ∈ A then
          (∏ j ∈ Finset.univ.erase (Sum.inl e),
            coordinateWeight (leftRates s t j) (χ j)) *
              coordinateSlope (χ (Sum.inl e)) else 0 := Finset.sum_comm
    _ = ∑ e : E, (offEventWeight (leftRates s t) (Sum.inl e) A true -
          offEventWeight (leftRates s t) (Sum.inl e) A false) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_configurationWeight_slope_general A (leftRates s t) (Sum.inl e)
    _ = ∑ e : E, offPivotalWeight (leftRates s t) (Sum.inl e) A := by
      apply Finset.sum_congr rfl
      intro e _
      exact offEventWeight_sub_eq_offPivotalWeight hA (leftRates s t) (Sum.inl e)
    _ = ∑ e : E, eventWeight (leftRates s t) {χ | Pivotal A (Sum.inl e) χ} := by
      apply Finset.sum_congr rfl
      intro e _
      exact (eventWeight_pivotal (leftRates s t) A (Sum.inl e)).symm

/-- Activation Margulis--Russo derivative for a joint increasing event. -/
theorem hasDerivAt_eventWeight_right_pivotal
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    {A : Set (JointConfig E F)} (hA : IsUpperSet A) (r : E → ℝ) (t : ℝ) :
    HasDerivAt (fun x => eventWeight (rightRates r x) A)
      (∑ f : F, eventWeight (rightRates r t) {χ | Pivotal A (Sum.inr f) χ}) t := by
  classical
  convert hasDerivAt_eventWeight_right_raw r A t using 1
  symm
  calc
    (∑ χ, if χ ∈ A then ∑ f : F,
        (∏ j ∈ Finset.univ.erase (Sum.inr f),
          coordinateWeight (rightRates r t j) (χ j)) *
            coordinateSlope (χ (Sum.inr f)) else 0) =
        ∑ χ, ∑ f : F, if χ ∈ A then
          (∏ j ∈ Finset.univ.erase (Sum.inr f),
            coordinateWeight (rightRates r t j) (χ j)) *
              coordinateSlope (χ (Sum.inr f)) else 0 := by
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : χ ∈ A <;> simp [hχ]
    _ = ∑ f : F, ∑ χ, if χ ∈ A then
          (∏ j ∈ Finset.univ.erase (Sum.inr f),
            coordinateWeight (rightRates r t j) (χ j)) *
              coordinateSlope (χ (Sum.inr f)) else 0 := Finset.sum_comm
    _ = ∑ f : F, (offEventWeight (rightRates r t) (Sum.inr f) A true -
          offEventWeight (rightRates r t) (Sum.inr f) A false) := by
      apply Finset.sum_congr rfl
      intro f _
      exact sum_configurationWeight_slope_general A (rightRates r t) (Sum.inr f)
    _ = ∑ f : F, offPivotalWeight (rightRates r t) (Sum.inr f) A := by
      apply Finset.sum_congr rfl
      intro f _
      exact offEventWeight_sub_eq_offPivotalWeight hA (rightRates r t) (Sum.inr f)
    _ = ∑ f : F, eventWeight (rightRates r t) {χ | Pivotal A (Sum.inr f) χ} := by
      apply Finset.sum_congr rfl
      intro f _
      exact (eventWeight_pivotal (rightRates r t) A (Sum.inr f)).symm

/-- At unit-cube parameters, the product polynomial on joint configurations is
exactly the event probability for the actual independent joint law. -/
lemma eventWeight_eq_uniformJointLaw_event
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (C : Set (JointConfig E E)) :
    eventWeight (leftRates (fun _ : E => s) p) C =
      (jointLaw (fun _ => p) (fun _ => s) (fun _ => hp) (fun _ => hs)).event C := by
  have hr : ∀ x, leftRates (E := E) (fun _ : E => s) p x ∈ Icc (0 : ℝ) 1 := by
    intro x
    cases x <;> simp [hp, hs]
  rw [eventWeight_eq_boolProduct_event _ hr]
  have hlaw : boolProduct (leftRates (fun _ : E => s) p) hr =
      jointLaw (fun _ : E => p) (fun _ => s) (fun _ => hp) (fun _ => hs) := by
    apply OpenPath.FinProb.ext
    intro χ
    simp only [boolProduct, jointLaw, OpenPath.FinProb.pi_mass]
    apply Finset.prod_congr rfl
    intro x _
    cases x <;> simp [leftRates]
  rw [hlaw]

/-- The bond derivative of an enhanced increasing event, represented as the
expected number of bond pivots under the normalized uniform joint law. -/
theorem hasDerivAt_enhancedEventWeight_bond
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    {B : Set (E → Bool)} (hB : IsUpperSet B) :
    HasDerivAt (fun t => eventWeight (leftRates (fun _ : E => s) t) (enhancedEvent B))
      (∑ e : E,
        (jointLaw (fun _ => p) (fun _ => s) (fun _ => hp) (fun _ => hs)).event
          {χ | EdgePivotal (enhancedEvent B) e χ}) p := by
  convert hasDerivAt_eventWeight_left_pivotal (E := E) (F := E)
    (A := enhancedEvent B) (isUpperSet_enhancedEvent hB) (fun _ : E => s) p using 1
  apply Finset.sum_congr rfl
  intro e _
  exact (eventWeight_eq_uniformJointLaw_event (E := E) p s hp hs
    {χ | Pivotal (enhancedEvent B) (Sum.inl e) χ}).symm

/-- The activation derivative of an enhanced increasing event, represented as
the expected number of activation pivots under the same joint law. -/
theorem hasDerivAt_enhancedEventWeight_activation
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    {B : Set (E → Bool)} (hB : IsUpperSet B) :
    HasDerivAt (fun t => eventWeight (rightRates (fun _ : E => p) t) (enhancedEvent B))
      (∑ e : E,
        (jointLaw (fun _ => p) (fun _ => s) (fun _ => hp) (fun _ => hs)).event
          {χ | ActivationPivotal (enhancedEvent B) e χ}) s := by
  have h := hasDerivAt_eventWeight_right_pivotal (E := E) (F := E)
    (A := enhancedEvent B) (isUpperSet_enhancedEvent hB) (fun _ : E => p) s
  have heq : rightRates (fun _ : E => p) s = leftRates (fun _ : E => s) p := by
    funext x
    cases x <;> rfl
  rw [heq] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro e _
  exact (eventWeight_eq_uniformJointLaw_event (E := E) p s hp hs
    {χ | Pivotal (enhancedEvent B) (Sum.inr e) χ}).symm

/-- **Finite AG differential comparison for the OR gadget.**  The two
`HasDerivAt` conclusions are proved internally, not assumed.  Their derivative
coefficients `Dp` and `Ds` are the genuine expected pivot counts and satisfy
`Ds ≥ (δ/2) Dp`, the finite analogue of equation (3) in the AG argument. -/
theorem enhancedEvent_differential_comparison
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ b : Bool, δ ≤ (boolLaw p hp).mass b)
    (hactivation : ∀ b : Bool, δ ≤ (boolLaw s hs).mass b)
    {B : Set (E → Bool)} (hB : IsUpperSet B) :
    let μ := jointLaw (fun _ : E => p) (fun _ => s) (fun _ => hp) (fun _ => hs)
    let Dp := ∑ e : E, μ.event {χ | EdgePivotal (enhancedEvent B) e χ}
    let Ds := ∑ e : E, μ.event {χ | ActivationPivotal (enhancedEvent B) e χ}
    HasDerivAt (fun t => eventWeight (leftRates (fun _ : E => s) t) (enhancedEvent B)) Dp p ∧
      HasDerivAt (fun t => eventWeight (rightRates (fun _ : E => p) t) (enhancedEvent B)) Ds s ∧
      (δ / 2) * Dp ≤ Ds := by
  classical
  dsimp only
  refine ⟨hasDerivAt_enhancedEventWeight_bond p s hp hs hB,
    hasDerivAt_enhancedEventWeight_activation p s hp hs hB, ?_⟩
  have h := sum_edgePivotal_event_mul_le (fun _ : E => p) (fun _ => s)
    (fun _ => hp) (fun _ => hs) δ hδ
    (fun _ b => hbond b) (fun _ b => hactivation b) B
  dsimp only at h
  dsimp only [jointLaw]
  linarith

/-- A continuous positive uniform lower bound for all four coordinate masses
when `0 < p,s < 1`. -/
def orMinorant (p s : ℝ) : ℝ := min (min p (1 - p)) (min s (1 - s))

lemma continuous_orMinorant : Continuous (fun x : ℝ × ℝ => orMinorant x.1 x.2) := by
  unfold orMinorant
  fun_prop

lemma orMinorant_nonneg {p s : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ orMinorant p s := by
  exact le_min (le_min hp.1 (sub_nonneg.mpr hp.2))
    (le_min hs.1 (sub_nonneg.mpr hs.2))

lemma orMinorant_pos {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s < 1) : 0 < orMinorant p s := by
  exact lt_min (lt_min hp0 (sub_pos.mpr hp1)) (lt_min hs0 (sub_pos.mpr hs1))

lemma orMinorant_le_bondLaw {p s : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (b : Bool) :
    orMinorant p s ≤ (boolLaw p hp).mass b := by
  cases b
  · rw [boolLaw_false]
    exact (min_le_left _ _).trans (min_le_right _ _)
  · rw [boolLaw_true]
    exact (min_le_left _ _).trans (min_le_left _ _)

lemma orMinorant_le_activationLaw {p s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (b : Bool) :
    orMinorant p s ≤ (boolLaw s hs).mass b := by
  cases b
  · rw [boolLaw_false]
    exact (min_le_right _ _).trans (min_le_right _ _)
  · rw [boolLaw_true]
    exact (min_le_right _ _).trans (min_le_left _ _)

/-- Interior-rate form with the explicit strictly positive comparison function
`orMinorant p s / 2`; no separate mass-minorant hypotheses remain. -/
theorem enhancedEvent_differential_comparison_pos
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hs0 : 0 < s) (hs1 : s < 1)
    {B : Set (E → Bool)} (hB : IsUpperSet B) :
    let δ := orMinorant p s
    let μ := jointLaw (fun _ : E => p) (fun _ => s) (fun _ => hp) (fun _ => hs)
    let Dp := ∑ e : E, μ.event {χ | EdgePivotal (enhancedEvent B) e χ}
    let Ds := ∑ e : E, μ.event {χ | ActivationPivotal (enhancedEvent B) e χ}
    0 < δ ∧
      HasDerivAt (fun t => eventWeight (leftRates (fun _ : E => s) t) (enhancedEvent B)) Dp p ∧
      HasDerivAt (fun t => eventWeight (rightRates (fun _ : E => p) t) (enhancedEvent B)) Ds s ∧
      (δ / 2) * Dp ≤ Ds := by
  have hδ := orMinorant_pos hp0 hp1 hs0 hs1
  have h := enhancedEvent_differential_comparison p s hp hs (orMinorant p s)
    hδ.le (fun b => orMinorant_le_bondLaw hp b)
    (fun b => orMinorant_le_activationLaw hs b) hB
  dsimp only at h ⊢
  exact ⟨hδ, h.1, h.2.1, h.2.2⟩

/-- The same finite differential comparison for the actual enhanced one-arm
event on a graph with finitely many edges. -/
theorem enhancedArm_differential_comparison
    {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    (o : V) (n : ℕ)
    (p s : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ b : Bool, δ ≤ (boolLaw p hp).mass b)
    (hactivation : ∀ b : Bool, δ ≤ (boolLaw s hs).mass b) :
    let μ := jointLaw (fun _ : G.edgeSet => p) (fun _ => s) (fun _ => hp) (fun _ => hs)
    let Dp := ∑ e : G.edgeSet, μ.event {χ | EdgePivotal (enhancedArmEvent G o n) e χ}
    let Ds := ∑ e : G.edgeSet, μ.event {χ | ActivationPivotal (enhancedArmEvent G o n) e χ}
    HasDerivAt (fun t => eventWeight (leftRates (fun _ : G.edgeSet => s) t)
        (enhancedArmEvent G o n)) Dp p ∧
      HasDerivAt (fun t => eventWeight (rightRates (fun _ : G.edgeSet => p) t)
        (enhancedArmEvent G o n)) Ds s ∧
      (δ / 2) * Dp ≤ Ds := by
  exact enhancedEvent_differential_comparison p s hp hs δ hδ hbond hactivation
    (CurvatureVariance.Infra.Percolation.isUpperSet_armEvent o n)

end FK.AGGadget
