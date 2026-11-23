import FK.AGDifferential

/-!
# Integration of the finite one-edge OR comparison along straight curves

The differential inequality is integrated on an explicit line whose bond rate
has derivative `-c` and whose activation rate has derivative `1`.  No ODE or
infinite-volume statement is used.
-/

open Set
open scoped Classical BigOperators

namespace FK.AGGadget

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison
open FK.MargulisRussoFinite

universe u v

noncomputable section

/-- Joint product rates on the comparison line `(p - c*t, s + t)`. -/
def diagonalRates {E : Type u} {F : Type v} (p s c t : ℝ) : E ⊕ F → ℝ :=
  leftRates (fun _ => s + t) (p - c * t)

@[simp] lemma diagonalRates_inl {E : Type u} {F : Type v}
    (p s c t : ℝ) (e : E) : diagonalRates p s c t (Sum.inl e : E ⊕ F) = p - c * t := rfl

@[simp] lemma diagonalRates_inr {E : Type u} {F : Type v}
    (p s c t : ℝ) (f : F) : diagonalRates p s c t (Sum.inr f : E ⊕ F) = s + t := rfl

/-- The derivative of a coordinate weight along the comparison line. -/
def diagonalSlope {E : Type u} {F : Type v} (c : ℝ)
    (χ : JointConfig E F) (x : E ⊕ F) : ℝ :=
  match x with
  | Sum.inl e => -c * coordinateSlope (χ (Sum.inl e))
  | Sum.inr f => coordinateSlope (χ (Sum.inr f))

/-- Raw product derivative along the comparison line. -/
lemma hasDerivAt_configurationWeight_diagonal
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (p s c : ℝ) (χ : JointConfig E F) (t : ℝ) :
    HasDerivAt (fun x => configurationWeight (diagonalRates p s c x) χ)
      (∑ x : E ⊕ F, (∏ j ∈ Finset.univ.erase x,
        coordinateWeight (diagonalRates p s c t j) (χ j)) * diagonalSlope c χ x) t := by
  have hderiv (x : E ⊕ F) :
      HasDerivAt (fun y => coordinateWeight (diagonalRates p s c y x) (χ x))
        (diagonalSlope c χ x) t := by
    cases x with
    | inl e =>
        have hp : HasDerivAt (fun x : ℝ => p - c * x) (-c) t := by
          convert (hasDerivAt_const t p).sub
            ((hasDerivAt_const t c).mul (hasDerivAt_id t)) using 1
          · ext x
            rfl
          · ring
        have h := (hasDerivAt_coordinateWeight (χ (Sum.inl e)) (p - c * t)).comp t hp
        simpa [Function.comp_def, diagonalSlope, mul_comm] using h
    | inr f =>
        have hs : HasDerivAt (fun x : ℝ => s + x) 1 t := by
          simpa using (hasDerivAt_id t).const_add s
        have h := (hasDerivAt_coordinateWeight (χ (Sum.inr f)) (s + t)).comp t hs
        simpa [Function.comp_def, diagonalSlope] using h
  simpa [configurationWeight, diagonalRates, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun x y => coordinateWeight (diagonalRates p s c y x) (χ x))
      (f' := fun x => diagonalSlope c χ x)
      (fun x _ => hderiv x))

/-- Raw diagonal derivative, already separated into the bond and activation
contributions. -/
theorem hasDerivAt_eventWeight_diagonal_raw
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (p s c : ℝ) (A : Set (JointConfig E F)) (t : ℝ) :
    HasDerivAt (fun x => eventWeight (diagonalRates p s c x) A)
      ((-c) * (∑ χ, if χ ∈ A then ∑ e : E,
        (∏ j ∈ Finset.univ.erase (Sum.inl e),
          coordinateWeight (diagonalRates p s c t j) (χ j)) *
            coordinateSlope (χ (Sum.inl e)) else 0) +
        (∑ χ, if χ ∈ A then ∑ f : F,
        (∏ j ∈ Finset.univ.erase (Sum.inr f),
          coordinateWeight (diagonalRates p s c t j) (χ j)) *
            coordinateSlope (χ (Sum.inr f)) else 0)) t := by
  classical
  have hsum :
      HasDerivAt (fun x => eventWeight (diagonalRates p s c x) A)
        (∑ χ, if χ ∈ A then ∑ x : E ⊕ F,
          (∏ j ∈ Finset.univ.erase x,
            coordinateWeight (diagonalRates p s c t j) (χ j)) *
              diagonalSlope c χ x else 0) t := by
    unfold eventWeight
    apply HasDerivAt.fun_sum
    intro χ _
    by_cases hχ : χ ∈ A
    · simpa only [hχ, ite_true] using hasDerivAt_configurationWeight_diagonal p s c χ t
    · simpa [hχ] using hasDerivAt_const t (0 : ℝ)
  convert hsum using 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hχ : χ ∈ A
  · simp only [hχ, ite_true, Fintype.sum_sum_type]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [diagonalSlope]
    ring
  · simp [hχ]

-- The two standalone coefficient identities below keep the line-derivative
-- proof within the default heartbeat budget.
/-- Bond raw derivative equals the bond-pivot weight (standalone to keep the
line-derivative proof within the default heartbeat budget). -/
lemma eventWeight_left_raw_eq_pivotal
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    {A : Set (JointConfig E F)} (hA : IsUpperSet A) (s : F → ℝ) (p : ℝ) :
    (∑ χ, if χ ∈ A then ∑ e : E,
      (∏ j ∈ Finset.univ.erase (Sum.inl e),
        coordinateWeight (leftRates s p j) (χ j)) *
          coordinateSlope (χ (Sum.inl e)) else 0) =
      ∑ e : E, eventWeight (leftRates s p) {χ | Pivotal A (Sum.inl e) χ} := by
  exact (hasDerivAt_eventWeight_left_raw s A p).unique
    (hasDerivAt_eventWeight_left_pivotal hA s p)

/-- Activation raw derivative equals the activation-pivot weight. -/
lemma eventWeight_right_raw_eq_pivotal
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    {A : Set (JointConfig E F)} (hA : IsUpperSet A) (r : E → ℝ) (s : ℝ) :
    (∑ χ, if χ ∈ A then ∑ f : F,
      (∏ j ∈ Finset.univ.erase (Sum.inr f),
        coordinateWeight (rightRates r s j) (χ j)) *
          coordinateSlope (χ (Sum.inr f)) else 0) =
      ∑ f : F, eventWeight (rightRates r s) {χ | Pivotal A (Sum.inr f) χ} := by
  exact (hasDerivAt_eventWeight_right_raw r A s).unique
    (hasDerivAt_eventWeight_right_pivotal hA r s)

/-- Pivotal form of the derivative along the comparison line. -/
theorem hasDerivAt_eventWeight_diagonal_pivotal
    {E : Type u} {F : Type v} [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F]
    (p s c : ℝ) {A : Set (JointConfig E F)} (hA : IsUpperSet A) (t : ℝ) :
    HasDerivAt (fun x => eventWeight (diagonalRates p s c x) A)
      ((-c) * (∑ e : E, eventWeight (diagonalRates p s c t)
        {χ | Pivotal A (Sum.inl e) χ}) +
       (∑ f : F, eventWeight (diagonalRates p s c t)
        {χ | Pivotal A (Sum.inr f) χ})) t := by
  classical
  have hbEq := eventWeight_left_raw_eq_pivotal (E := E) (F := F)
    hA (fun _ => s + t) (p - c * t)
  have hl : leftRates (E := E) (F := F) (fun _ : F => s + t) (p - c * t) =
      diagonalRates (E := E) (F := F) p s c t := rfl
  rw [hl] at hbEq
  have haEq := eventWeight_right_raw_eq_pivotal (E := E) (F := F)
    hA (fun _ : E => p - c * t) (s + t)
  have hr : rightRates (E := E) (F := F) (fun _ : E => p - c * t) (s + t) =
      diagonalRates (E := E) (F := F) p s c t := by
    funext x
    cases x <;> rfl
  rw [hr] at haEq
  have hraw := hasDerivAt_eventWeight_diagonal_raw p s c A t
  rw [hbEq, haEq] at hraw
  exact hraw

/-- A strictly positive speed available throughout the closed interior box
`[a,b]^2`, for `0 < a` and `b < 1`. -/
def interiorComparisonSpeed (a b : ℝ) : ℝ := min a (1 - b) / 2

lemma interiorComparisonSpeed_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    0 ≤ interiorComparisonSpeed a b := by
  exact div_nonneg (le_min ha (sub_nonneg.mpr hb)) (by norm_num)

lemma interiorComparisonSpeed_pos {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    0 < interiorComparisonSpeed a b := by
  exact div_pos (lt_min ha (sub_pos.mpr hb)) (by norm_num)

lemma interiorComparisonSpeed_le_orMinorant {a b p s : ℝ}
    (hp : p ∈ Icc a b) (hs : s ∈ Icc a b) :
    interiorComparisonSpeed a b ≤ orMinorant p s / 2 := by
  have hmin : min a (1 - b) ≤ orMinorant p s := by
    apply le_min
    · apply le_min
      · exact (min_le_left _ _).trans hp.1
      · exact (min_le_right _ _).trans (sub_le_sub_left hp.2 1)
    · apply le_min
      · exact (min_le_left _ _).trans hs.1
      · exact (min_le_right _ _).trans (sub_le_sub_left hs.2 1)
  exact div_le_div_of_nonneg_right hmin (by norm_num)

/-- Convexity calculation for the comparison line: membership of both
endpoints in `[a,b]^2` gives membership at every intermediate parameter. -/
lemma diagonal_parameters_mem_Icc {p s c a b T t : ℝ} (hc : 0 ≤ c)
    (ht : t ∈ Icc (0 : ℝ) T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - c * T ∈ Icc a b) (hsT : s + T ∈ Icc a b) :
    p - c * t ∈ Icc a b ∧ s + t ∈ Icc a b := by
  have hct : 0 ≤ c * t := mul_nonneg hc ht.1
  have hctT : 0 ≤ c * (T - t) := mul_nonneg hc (sub_nonneg.mpr ht.2)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [hpT.1]
  · nlinarith [hp0.2]
  · exact le_trans hs0.1 (by linarith [ht.1])
  · exact le_trans (by linarith [ht.2] : s + t ≤ s + T) hsT.2

/-- Nonnegativity of the directional derivative at a point of the closed
interior box.  The proof is a direct consequence of the established finite
one-edge OR pivot comparison. -/
lemma enhanced_pivotSlope_nonneg_of_box
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s a b : ℝ) {B : Set (E → Bool)} (hB : IsUpperSet B)
    (ha : 0 < a) (hb : b < 1) (hp : p ∈ Icc a b) (hs : s ∈ Icc a b) :
    0 ≤ (-interiorComparisonSpeed a b) *
        (∑ e : E, eventWeight (leftRates (fun _ : E => s) p)
          {χ | Pivotal (enhancedEvent B) (Sum.inl e) χ}) +
      (∑ e : E, eventWeight (leftRates (fun _ : E => s) p)
        {χ | Pivotal (enhancedEvent B) (Sum.inr e) χ}) := by
  classical
  have hp01 : p ∈ Icc (0 : ℝ) 1 := ⟨ha.le.trans hp.1, hp.2.trans hb.le⟩
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha.le.trans hs.1, hs.2.trans hb.le⟩
  let μ := jointLaw (fun _ : E => p) (fun _ => s) (fun _ => hp01) (fun _ => hs01)
  let Dp := ∑ e : E, μ.event {χ | EdgePivotal (enhancedEvent B) e χ}
  let Ds := ∑ e : E, μ.event {χ | ActivationPivotal (enhancedEvent B) e χ}
  have hDp : 0 ≤ Dp := by
    exact Finset.sum_nonneg fun e _ => μ.event_nonneg _
  have hcomp : (orMinorant p s / 2) * Dp ≤ Ds := by
    have h := enhancedEvent_differential_comparison p s hp01 hs01
      (orMinorant p s) (orMinorant_nonneg hp01 hs01)
      (fun b => orMinorant_le_bondLaw hp01 b)
      (fun b => orMinorant_le_activationLaw hs01 b) hB
    exact h.2.2
  have hbw : (∑ e : E, eventWeight (leftRates (fun _ : E => s) p)
      {χ | Pivotal (enhancedEvent B) (Sum.inl e) χ}) = Dp := by
    dsimp only [Dp, μ]
    apply Finset.sum_congr rfl
    intro e _
    exact eventWeight_eq_uniformJointLaw_event p s hp01 hs01
      {χ | Pivotal (enhancedEvent B) (Sum.inl e) χ}
  have haw : (∑ e : E, eventWeight (leftRates (fun _ : E => s) p)
      {χ | Pivotal (enhancedEvent B) (Sum.inr e) χ}) = Ds := by
    dsimp only [Ds, μ]
    apply Finset.sum_congr rfl
    intro e _
    exact eventWeight_eq_uniformJointLaw_event p s hp01 hs01
      {χ | Pivotal (enhancedEvent B) (Sum.inr e) χ}
  have hc := interiorComparisonSpeed_le_orMinorant hp hs
  have hmul := mul_le_mul_of_nonneg_right hc hDp
  rw [hbw, haw]
  linarith

/-- **Finite comparison-curve integration.**  Along the explicit line
`t ↦ (p - min(a,1-b)t/2, s+t)`, the enhanced-event polynomial is monotone on
`[0,T]`.  Both endpoints are required to lie in the same closed interior box
`[a,b]^2`; convexity then supplies every intermediate parameter bound. -/
theorem monotoneOn_enhancedEventWeight_diagonal
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s a b T : ℝ) {B : Set (E → Bool)} (hB : IsUpperSet B)
    (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - interiorComparisonSpeed a b * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn
      (fun t => eventWeight (diagonalRates p s (interiorComparisonSpeed a b) t)
        (enhancedEvent B)) (Icc (0 : ℝ) T) := by
  classical
  let c := interiorComparisonSpeed a b
  let Dp : ℝ → ℝ := fun t => ∑ e : E, eventWeight (diagonalRates p s c t)
    {χ | Pivotal (enhancedEvent B) (Sum.inl e) χ}
  let Ds : ℝ → ℝ := fun t => ∑ e : E, eventWeight (diagonalRates p s c t)
    {χ | Pivotal (enhancedEvent B) (Sum.inr e) χ}
  have hc : 0 ≤ c := interiorComparisonSpeed_nonneg ha.le hb.le
  have hderiv (t : ℝ) :
      HasDerivAt (fun x => eventWeight (diagonalRates p s c x) (enhancedEvent B))
        ((-c) * Dp t + Ds t) t := by
    exact hasDerivAt_eventWeight_diagonal_pivotal p s c
      (isUpperSet_enhancedEvent hB) t
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T)
    (f' := fun t => (-c) * Dp t + Ds t)
  · intro t _
    exact (hderiv t).continuousAt.continuousWithinAt
  · intro t _
    exact (hderiv t).hasDerivWithinAt
  · intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := interior_subset ht
    have hbox := diagonal_parameters_mem_Icc hc htcc hp0 hs0 hpT hsT
    exact enhanced_pivotSlope_nonneg_of_box (p - c * t) (s + t) a b hB
      ha hb hbox.1 hbox.2

/-- Endpoint form of comparison-curve integration for the endpoint-safe
product polynomial. -/
theorem enhancedEventWeight_diagonal_le
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s a b T : ℝ) {B : Set (E → Bool)} (hB : IsUpperSet B)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - interiorComparisonSpeed a b * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (leftRates (fun _ : E => s) p) (enhancedEvent B) ≤
      eventWeight (leftRates (fun _ : E => s + T)
        (p - interiorComparisonSpeed a b * T)) (enhancedEvent B) := by
  have hmono := monotoneOn_enhancedEventWeight_diagonal p s a b T hB ha hb
    hp0 hs0 hpT hsT
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hmemT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have h := hmono h0 hmemT hT
  simpa [diagonalRates] using h

/-- Normalized finite-probability endpoint comparison.  The two
`eventWeight_eq_uniformJointLaw_event` rewrites are explicit, so neither end
is being treated as an unnormalized polynomial probability. -/
theorem enhancedEvent_jointLaw_diagonal_le
    {E : Type u} [Fintype E] [DecidableEq E]
    (p s a b T : ℝ) {B : Set (E → Bool)} (hB : IsUpperSet B)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - interiorComparisonSpeed a b * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hp01 : p ∈ Icc (0 : ℝ) 1) (hs01 : s ∈ Icc (0 : ℝ) 1)
    (hpT01 : p - interiorComparisonSpeed a b * T ∈ Icc (0 : ℝ) 1)
    (hsT01 : s + T ∈ Icc (0 : ℝ) 1) :
    (jointLaw (fun _ : E => p) (fun _ => s) (fun _ => hp01) (fun _ => hs01)).event
        (enhancedEvent B) ≤
      (jointLaw (fun _ : E => p - interiorComparisonSpeed a b * T)
        (fun _ => s + T) (fun _ => hpT01) (fun _ => hsT01)).event
        (enhancedEvent B) := by
  rw [← eventWeight_eq_uniformJointLaw_event p s hp01 hs01 (enhancedEvent B),
    ← eventWeight_eq_uniformJointLaw_event
      (p - interiorComparisonSpeed a b * T) (s + T) hpT01 hsT01 (enhancedEvent B)]
  exact enhancedEventWeight_diagonal_le p s a b T hB ha hb hT hp0 hs0 hpT hsT

/-- The normalized comparison on the actual enhanced finite-arm event. -/
theorem enhancedArm_jointLaw_diagonal_le
    {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableEq G.edgeSet]
    (o : V) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - interiorComparisonSpeed a b * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hp01 : p ∈ Icc (0 : ℝ) 1) (hs01 : s ∈ Icc (0 : ℝ) 1)
    (hpT01 : p - interiorComparisonSpeed a b * T ∈ Icc (0 : ℝ) 1)
    (hsT01 : s + T ∈ Icc (0 : ℝ) 1) :
    (jointLaw (fun _ : G.edgeSet => p) (fun _ => s)
        (fun _ => hp01) (fun _ => hs01)).event (enhancedArmEvent G o n) ≤
      (jointLaw (fun _ : G.edgeSet => p - interiorComparisonSpeed a b * T)
        (fun _ => s + T) (fun _ => hpT01) (fun _ => hsT01)).event
        (enhancedArmEvent G o n) := by
  exact enhancedEvent_jointLaw_diagonal_le p s a b T
    (CurvatureVariance.Infra.Percolation.isUpperSet_armEvent o n)
    ha hb hT hp0 hs0 hpT hsT hp01 hs01 hpT01 hsT01

end
end FK.AGGadget
