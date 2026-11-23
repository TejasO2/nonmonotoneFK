import FK.AGSleevedAnnulus
import FK.AGCurveIntegration

/-!
# Selected-coordinate differential assembly for annular sleeves

For a fixed finite selection `S`, the simultaneous sleeve construction compares
all selected base-bond pivots with one shared activation pivot.  This module
sums those comparisons and uses only the corresponding selected base bonds in
a comparison line; the added spoke bonds remain fixed.  The final normalization
is by `2 ^ S.card * S.card`, reflecting that all selected pivots use the same
activation.  No infinite-volume limit or critical-point shift is asserted.
-/

open Set
open scoped Classical BigOperators Sym2

namespace FK.AGImplant.Sleeve

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation

universe u v w

/-- The exact summed finite-product comparison for one shared sleeve.  The
factor `S.card` on the right is necessary because every selected base bond is
compared with the same activation-pivot event. -/
theorem openConnected_annulus_sum_edgePivotal_event_mul_le
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : Unit → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : Finset H.edgeSet) {a b : V ⊕ H.edgeSet} :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ S.card * (∑ e ∈ S, μ.event {χ | EdgePivotal
        (deviceEvent (support H S)
          {ω | OpenConnected (graph H) ω Set.univ a b}) (baseEdge H e) χ}) ≤
      ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ) * μ.event {χ | ActivationPivotal
        (deviceEvent (support H S)
          {ω | OpenConnected (graph H) ω Set.univ a b}) () χ} := by
  classical
  dsimp only
  calc
    δ ^ S.card * (∑ e ∈ S, (OpenPath.FinProb.pi (Sum.elim bond activation)).event
        {χ | EdgePivotal (deviceEvent (support H S)
          {ω | OpenConnected (graph H) ω Set.univ a b}) (baseEdge H e) χ}) =
        ∑ e ∈ S, δ ^ S.card * (OpenPath.FinProb.pi (Sum.elim bond activation)).event
          {χ | EdgePivotal (deviceEvent (support H S)
            {ω | OpenConnected (graph H) ω Set.univ a b}) (baseEdge H e) χ} := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _e ∈ S, ((2 ^ S.card : ℕ) : ℝ) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal (deviceEvent (support H S)
              {ω | OpenConnected (graph H) ω Set.univ a b}) () χ} := by
      apply Finset.sum_le_sum
      intro e he
      exact openConnected_annulus_edgePivotal_event_mul_le H bond activation δ hδ
        hbond hactivation S he
    _ = ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal (deviceEvent (support H S)
              {ω | OpenConnected (graph H) ω Set.univ a b}) () χ} := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The corresponding exact summation for the repository's actual one-arm
event on a finite sleeved graph. -/
theorem deviceArmEvent_annulus_sum_edgePivotal_event_mul_le
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (bond : (graph H).edgeSet → OpenPath.FinProb Bool)
    (activation : Unit → OpenPath.FinProb Bool)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbond : ∀ e b, δ ≤ (bond e).mass b)
    (hactivation : ∀ z b, δ ≤ (activation z).mass b)
    (S : Finset H.edgeSet) {o : V ⊕ H.edgeSet} (n : ℕ) :
    let μ := OpenPath.FinProb.pi (Sum.elim bond activation)
    δ ^ S.card * (∑ e ∈ S, μ.event {χ | EdgePivotal
        (deviceArmEvent (graph H) (support H S) o n) (baseEdge H e) χ}) ≤
      ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ) * μ.event {χ | ActivationPivotal
        (deviceArmEvent (graph H) (support H S) o n) () χ} := by
  classical
  dsimp only
  calc
    δ ^ S.card * (∑ e ∈ S, (OpenPath.FinProb.pi (Sum.elim bond activation)).event
        {χ | EdgePivotal (deviceArmEvent (graph H) (support H S) o n)
          (baseEdge H e) χ}) =
        ∑ e ∈ S, δ ^ S.card * (OpenPath.FinProb.pi (Sum.elim bond activation)).event
          {χ | EdgePivotal (deviceArmEvent (graph H) (support H S) o n)
            (baseEdge H e) χ} := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _e ∈ S, ((2 ^ S.card : ℕ) : ℝ) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal (deviceArmEvent (graph H) (support H S) o n) () χ} := by
      apply Finset.sum_le_sum
      intro e he
      exact deviceArmEvent_annulus_edgePivotal_event_mul_le H bond activation δ hδ
        hbond hactivation S he n
    _ = ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ) *
          (OpenPath.FinProb.pi (Sum.elim bond activation)).event {χ |
            ActivationPivotal (deviceArmEvent (graph H) (support H S) o n) () χ} := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Rates on an affine line in the finite product cube. -/
def affineRates {X : Type w} (r v : X → ℝ) (t : ℝ) : X → ℝ :=
  fun x => r x + t * v x

/-- Raw derivative of one configuration weight along an arbitrary affine line. -/
lemma hasDerivAt_configurationWeight_affine
    {X : Type w} [Fintype X] [DecidableEq X]
    (r v : X → ℝ) (χ : X → Bool) (t : ℝ) :
    HasDerivAt (fun y => configurationWeight (affineRates r v y) χ)
      (∑ x, (∏ j ∈ Finset.univ.erase x,
        coordinateWeight (affineRates r v t j) (χ j)) *
          (v x * coordinateSlope (χ x))) t := by
  classical
  have hderiv (x : X) :
      HasDerivAt (fun y => coordinateWeight (affineRates r v y x) (χ x))
        (v x * coordinateSlope (χ x)) t := by
    have hline : HasDerivAt (fun y : ℝ => r x + y * v x) (v x) t := by
      convert (hasDerivAt_const t (r x)).add ((hasDerivAt_id t).mul_const (v x)) using 1
      · funext y
        rfl
      · ring
    have h := (hasDerivAt_coordinateWeight (χ x) (r x + t * v x)).comp t hline
    simpa [affineRates, Function.comp_def, mul_comm] using h
  simpa [configurationWeight, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun x y => coordinateWeight (affineRates r v y x) (χ x))
      (f' := fun x => v x * coordinateSlope (χ x))
      (fun x _ => hderiv x))

/-- Raw derivative of an arbitrary finite product polynomial along an affine
line. -/
lemma hasDerivAt_eventWeight_affine_raw
    {X : Type w} [Fintype X] [DecidableEq X]
    (r v : X → ℝ) (A : Set (X → Bool)) (t : ℝ) :
    HasDerivAt (fun y => eventWeight (affineRates r v y) A)
      (∑ χ, if χ ∈ A then ∑ x,
        (∏ j ∈ Finset.univ.erase x,
          coordinateWeight (affineRates r v t j) (χ j)) *
            (v x * coordinateSlope (χ x)) else 0) t := by
  classical
  unfold eventWeight
  apply HasDerivAt.fun_sum
  intro χ hχmem
  by_cases hχ : χ ∈ A
  · simpa only [hχ, ite_true] using
      hasDerivAt_configurationWeight_affine r v χ t
  · simpa [hχ] using hasDerivAt_const t (0 : ℝ)

/-- **Affine finite Margulis--Russo formula.**  Every coordinate velocity is
explicit, so setting a velocity to zero proves that the corresponding bond is
held fixed. -/
theorem hasDerivAt_eventWeight_affine_pivotal
    {X : Type w} [Fintype X] [DecidableEq X]
    (r v : X → ℝ) {A : Set (X → Bool)} (hA : IsUpperSet A) (t : ℝ) :
    HasDerivAt (fun y => eventWeight (affineRates r v y) A)
      (∑ x, v x * eventWeight (affineRates r v t) {χ | Pivotal A x χ}) t := by
  classical
  convert hasDerivAt_eventWeight_affine_raw r v A t using 1
  symm
  calc
    (∑ χ, if χ ∈ A then ∑ x,
        (∏ j ∈ Finset.univ.erase x,
          coordinateWeight (affineRates r v t j) (χ j)) *
            (v x * coordinateSlope (χ x)) else 0) =
        ∑ χ, ∑ x, v x * (if χ ∈ A then
          (∏ j ∈ Finset.univ.erase x,
            coordinateWeight (affineRates r v t j) (χ j)) *
              coordinateSlope (χ x) else 0) := by
      apply Finset.sum_congr rfl
      intro χ hχmem
      by_cases hχ : χ ∈ A
      · simp only [hχ, ite_true]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      · simp [hχ]
    _ = ∑ x, v x * (∑ χ, if χ ∈ A then
          (∏ j ∈ Finset.univ.erase x,
            coordinateWeight (affineRates r v t j) (χ j)) *
              coordinateSlope (χ x) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχmem
      rw [Finset.mul_sum]
    _ = ∑ x, v x * (offEventWeight (affineRates r v t) x A true -
          offEventWeight (affineRates r v t) x A false) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [FK.AGGadget.sum_configurationWeight_slope_general]
    _ = ∑ x, v x * offPivotalWeight (affineRates r v t) x A := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [offEventWeight_sub_eq_offPivotalWeight hA]
    _ = ∑ x, v x * eventWeight (affineRates r v t) {χ | Pivotal A x χ} := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [eventWeight_pivotal]

/-- Velocity zero outside a selected finite set of bonds, `-c` on those
bonds, and one on the unique activation. -/
def selectedVelocity {E : Type u} [DecidableEq E] (T : Finset E) (c : ℝ) :
    E ⊕ Unit → ℝ :=
  Sum.elim (fun e => if e ∈ T then -c else 0) (fun _ => 1)

/-- The selected velocities turn the general affine pivot sum into one bond
sum and one activation-pivot probability. -/
lemma sum_selectedVelocity_mul {E : Type u} [Fintype E] [DecidableEq E]
    (T : Finset E) (c : ℝ) (W : E ⊕ Unit → ℝ) :
    (∑ x, selectedVelocity T c x * W x) =
      (-c) * (∑ e ∈ T, W (Sum.inl e)) + W (Sum.inr ()) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [selectedVelocity, Sum.elim_inl, Sum.elim_inr, one_mul]
  rw [show (∑ z : Unit, W (Sum.inr z)) = W (Sum.inr ()) by simp]
  congr 1
  calc
    (∑ e : E, (if e ∈ T then -c else 0) * W (Sum.inl e)) =
        ∑ e ∈ T, (if e ∈ T then -c else 0) * W (Sum.inl e) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ T)
      intro e he heT
      simp [heT]
    _ = ∑ e ∈ T, (-c) * W (Sum.inl e) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [he]
    _ = (-c) * (∑ e ∈ T, W (Sum.inl e)) := by
      rw [Finset.mul_sum]

/-- Only base bonds in `annulus H S` move on the sleeve comparison line.
Every added spoke and every unselected base bond stays at rate `p`. -/
noncomputable def sleeveLine {V : Type u} (H : SimpleGraph V) [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (p s c t : ℝ) : (graph H).edgeSet ⊕ Unit → ℝ :=
  Sum.elim (fun e => if e ∈ annulus H S then p - c * t else p) (fun _ => s + t)

/-- The direct line formula is an affine line with the selected velocities. -/
lemma sleeveLine_eq_affine {V : Type u} (H : SimpleGraph V)
    [DecidableEq (graph H).edgeSet] (S : Finset H.edgeSet) (p s c t : ℝ) :
    sleeveLine H S p s c t =
      affineRates (sleeveLine H S p s c 0)
        (selectedVelocity (annulus H S) c) t := by
  classical
  funext x
  cases x with
  | inl e =>
      by_cases he : e ∈ annulus H S
      · simp [sleeveLine, affineRates, selectedVelocity, he]
        ring
      · simp [sleeveLine, affineRates, selectedVelocity, he]
  | inr z =>
      simp [sleeveLine, affineRates, selectedVelocity]

/-- Selected-coordinate derivative of any increasing event on a finite
sleeved graph. -/
theorem hasDerivAt_eventWeight_sleeveLine_pivotal
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (p s c : ℝ)
    {A : Set (JointConfig (graph H).edgeSet Unit)} (hA : IsUpperSet A) (t : ℝ) :
    HasDerivAt (fun y => eventWeight (sleeveLine H S p s c y) A)
      ((-c) * (∑ e ∈ annulus H S,
          eventWeight (sleeveLine H S p s c t) {χ | Pivotal A (Sum.inl e) χ}) +
        eventWeight (sleeveLine H S p s c t) {χ | Pivotal A (Sum.inr ()) χ}) t := by
  classical
  have hfun : (fun y => eventWeight (sleeveLine H S p s c y) A) =
      (fun y => eventWeight (affineRates (sleeveLine H S p s c 0)
        (selectedVelocity (annulus H S) c) y) A) := by
    funext y
    rw [sleeveLine_eq_affine]
  have h := hasDerivAt_eventWeight_affine_pivotal
    (sleeveLine H S p s c 0) (selectedVelocity (annulus H S) c) hA t
  rw [sum_selectedVelocity_mul] at h
  rw [hfun, sleeveLine_eq_affine H S p s c t]
  exact h

/-- Reindex an image-of-annulus sum by the selected base edges.  Stating the
image directly keeps its decidable-equality instance explicit. -/
lemma sum_image_eventWeight_baseEdge
    {V : Type u} (H : SimpleGraph V) [DecidableEq (graph H).edgeSet]
    [Fintype (graph H).edgeSet] (S : Finset H.edgeSet)
    (r : (graph H).edgeSet ⊕ Unit → ℝ)
    (A : Set (JointConfig (graph H).edgeSet Unit)) :
    (∑ e ∈ S.image (baseEdge H), eventWeight r {χ | Pivotal A (Sum.inl e) χ}) =
      ∑ e ∈ S, eventWeight r {χ | EdgePivotal A (baseEdge H e) χ} := by
  change (∑ e ∈ S.image (baseEdge H), eventWeight r {χ | Pivotal A (Sum.inl e) χ}) =
    ∑ e ∈ S, eventWeight r {χ | Pivotal A (Sum.inl (baseEdge H e)) χ}
  exact Finset.sum_image (baseEdge_injective H).injOn

/-- A single positive minorant for both bits of every rate in `[a,b]`. -/
def sleeveMinorant (a b : ℝ) : ℝ := min a (1 - b)

lemma sleeveMinorant_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    0 ≤ sleeveMinorant a b :=
  le_min ha (sub_nonneg.mpr hb)

lemma sleeveMinorant_pos {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    0 < sleeveMinorant a b :=
  lt_min ha (sub_pos.mpr hb)

lemma sleeveMinorant_le_boolLaw {a b q : ℝ} (hq : q ∈ Icc a b)
    (hq01 : q ∈ Icc (0 : ℝ) 1) (bit : Bool) :
    sleeveMinorant a b ≤ (boolLaw q hq01).mass bit := by
  cases bit
  · change sleeveMinorant a b ≤ 1 - q
    exact (min_le_right a (1 - b)).trans (sub_le_sub_left hq.2 1)
  · change sleeveMinorant a b ≤ q
    exact (min_le_left a (1 - b)).trans hq.1

/-- The normalized speed available from one shared activation and `S.card`
simultaneous sleeve comparisons. -/
noncomputable def sleeveComparisonSpeed {α : Type u} (a b : ℝ) (S : Finset α) : ℝ :=
  (sleeveMinorant a b) ^ S.card /
    (((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ))

lemma sleeveComparisonSpeed_pos {α : Type u} {a b : ℝ} {S : Finset α}
    (hS : S.Nonempty) (ha : 0 < a) (hb : b < 1) :
    0 < sleeveComparisonSpeed a b S := by
  apply div_pos (pow_pos (sleeveMinorant_pos ha hb) _)
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  positivity

lemma sleeveComparisonSpeed_nonneg {α : Type u} {a b : ℝ} {S : Finset α}
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    0 ≤ sleeveComparisonSpeed a b S := by
  apply div_nonneg (pow_nonneg (sleeveMinorant_nonneg ha hb) _)
  positivity

/-- Every rate on the selected sleeve line lies in the same box when its two
bond values and its activation value do. -/
lemma sleeveLine_mem_box {V : Type u} (H : SimpleGraph V)
    [DecidableEq (graph H).edgeSet] (S : Finset H.edgeSet)
    {p s c t a b : ℝ} (hp : p ∈ Icc a b) (hmove : p - c * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) (x : (graph H).edgeSet ⊕ Unit) :
    sleeveLine H S p s c t x ∈ Icc a b := by
  cases x with
  | inl e =>
      by_cases he : e ∈ annulus H S
      · simpa [sleeveLine, he] using hmove
      · simpa [sleeveLine, he] using hp
  | inr z => simpa [sleeveLine] using hs

/-- On the unit cube the selected sleeve-line polynomial is exactly the
normalized independent bond/activation product probability. -/
lemma eventWeight_sleeveLine_eq_pi
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, sleeveLine H S p s c t x ∈ Icc (0 : ℝ) 1)
    (A : Set (JointConfig (graph H).edgeSet Unit)) :
    eventWeight (sleeveLine H S p s c t) A =
      (OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw (sleeveLine H S p s c t (Sum.inl e)) (hr (Sum.inl e)))
        (fun z => boolLaw (sleeveLine H S p s c t (Sum.inr z)) (hr (Sum.inr z))))).event A := by
  have hlaw : boolProduct (sleeveLine H S p s c t) hr =
      OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw (sleeveLine H S p s c t (Sum.inl e)) (hr (Sum.inl e)))
        (fun z => boolLaw (sleeveLine H S p s c t (Sum.inr z)) (hr (Sum.inr z)))) := by
    unfold boolProduct
    congr 1
    funext x
    cases x <;> rfl
  rw [eventWeight_eq_boolProduct_event (sleeveLine H S p s c t) hr, hlaw]

/-- Convexity supplies all intermediate selected-line rates from its
endpoints. -/
lemma sleeveLine_parameters_mem_box {p s c a b T t : ℝ} (hc : 0 ≤ c)
    (ht : t ∈ Icc (0 : ℝ) T) (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - c * T ∈ Icc a b) (hsT : s + T ∈ Icc a b) :
    p - c * t ∈ Icc a b ∧ s + t ∈ Icc a b :=
  FK.AGGadget.diagonal_parameters_mem_Icc hc ht hp0 hs0 hpT hsT

/-- **Normalized sleeve differential comparison.**  On an interior box and
for nonempty `S`, the selected line's bond derivative is controlled by the
one shared activation derivative with the exact annular exponent and shared
activation multiplicity. -/
lemma deviceArmEvent_sleevePivotSlope_nonneg_of_box
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (hS : S.Nonempty) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b t : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Icc a b) (hmove : p - sleeveComparisonSpeed a b S * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) :
    let c := sleeveComparisonSpeed a b S
    0 ≤ (-c) * (∑ e ∈ S, eventWeight (sleeveLine H S p s c t)
        {χ | EdgePivotal (deviceArmEvent (graph H) (support H S) o n)
          (baseEdge H e) χ}) +
      eventWeight (sleeveLine H S p s c t) {χ | ActivationPivotal
        (deviceArmEvent (graph H) (support H S) o n) () χ} := by
  classical
  dsimp only
  let c := sleeveComparisonSpeed a b S
  let r := sleeveLine H S p s c t
  let Dp := ∑ e ∈ S, eventWeight r
    {χ | EdgePivotal (deviceArmEvent (graph H) (support H S) o n) (baseEdge H e) χ}
  let Pa := eventWeight r
    {χ | ActivationPivotal (deviceArmEvent (graph H) (support H S) o n) () χ}
  let den : ℝ := ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ)
  have hrbox : ∀ x, r x ∈ Icc a b := by
    intro x
    exact sleeveLine_mem_box H S hp hmove hs x
  have hr : ∀ x, r x ∈ Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨ha.le.trans (hrbox x).1, (hrbox x).2.trans hb.le⟩
  let bond := fun e => boolLaw (r (Sum.inl e)) (hr (Sum.inl e))
  let activation := fun z => boolLaw (r (Sum.inr z)) (hr (Sum.inr z))
  have hminor : 0 < sleeveMinorant a b := sleeveMinorant_pos ha hb
  have hbond : ∀ e bit, sleeveMinorant a b ≤ (bond e).mass bit := by
    intro e bit
    exact sleeveMinorant_le_boolLaw (hrbox (Sum.inl e)) (hr (Sum.inl e)) bit
  have hactivation : ∀ z bit, sleeveMinorant a b ≤ (activation z).mass bit := by
    intro z bit
    exact sleeveMinorant_le_boolLaw (hrbox (Sum.inr z)) (hr (Sum.inr z)) bit
  have hsum := deviceArmEvent_annulus_sum_edgePivotal_event_mul_le H bond activation
    (sleeveMinorant a b) hminor.le hbond hactivation S n (o := o)
  dsimp only at hsum
  have hevent (C : Set (JointConfig (graph H).edgeSet Unit)) :
      (OpenPath.FinProb.pi (Sum.elim bond activation)).event C = eventWeight r C := by
    simpa only [bond, activation, r] using
      (eventWeight_sleeveLine_eq_pi H S p s c t hr C).symm
  simp_rw [hevent] at hsum
  change (sleeveMinorant a b) ^ S.card * Dp ≤ den * Pa at hsum
  change 0 ≤ (-c) * Dp + Pa
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hden0 : den ≠ 0 := ne_of_gt hden
  have hcδ : c * den = (sleeveMinorant a b) ^ S.card := by
    change ((sleeveMinorant a b) ^ S.card / den) * den =
      (sleeveMinorant a b) ^ S.card
    exact div_mul_cancel₀ _ hden0
  have hmul : c * Dp ≤ Pa := by
    refine le_of_mul_le_mul_right (a := den) ?_ hden
    calc
      (c * Dp) * den = (c * den) * Dp := by ring
      _ = (sleeveMinorant a b) ^ S.card * Dp := by rw [hcδ]
      _ ≤ den * Pa := hsum
      _ = Pa * den := by ring
  linarith

/-- **Finite comparison curve for the sleeved one-arm event.**  Only selected
base bonds decrease; every spoke and every other base bond remains fixed. -/
theorem monotoneOn_deviceArmEvent_sleeveLine
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (hS : S.Nonempty) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn (fun t => eventWeight
      (sleeveLine H S p s (sleeveComparisonSpeed a b S) t)
      (deviceArmEvent (graph H) (support H S) o n)) (Icc (0 : ℝ) T) := by
  classical
  let c := sleeveComparisonSpeed a b S
  let Dp : ℝ → ℝ := fun t => ∑ e ∈ S, eventWeight (sleeveLine H S p s c t)
    {χ | EdgePivotal (deviceArmEvent (graph H) (support H S) o n) (baseEdge H e) χ}
  let Pa : ℝ → ℝ := fun t => eventWeight (sleeveLine H S p s c t)
    {χ | ActivationPivotal (deviceArmEvent (graph H) (support H S) o n) () χ}
  have hc : 0 ≤ c := sleeveComparisonSpeed_nonneg ha.le hb.le
  have hderiv (t : ℝ) :
      HasDerivAt (fun y => eventWeight (sleeveLine H S p s c y)
        (deviceArmEvent (graph H) (support H S) o n)) ((-c) * Dp t + Pa t) t := by
    have h := hasDerivAt_eventWeight_sleeveLine_pivotal H S p s c
      (isUpperSet_deviceArmEvent (graph H) (support H S) o n) t
    have himage : annulus H S = S.image (baseEdge H) := by
      ext e
      simp [annulus]
    rw [himage, sum_image_eventWeight_baseEdge] at h
    exact h
  change MonotoneOn (fun t => eventWeight (sleeveLine H S p s c t)
    (deviceArmEvent (graph H) (support H S) o n)) (Icc (0 : ℝ) T)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T)
    (f' := fun t => (-c) * Dp t + Pa t)
  · intro t ht
    exact (hderiv t).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t).hasDerivWithinAt
  · intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := interior_subset ht
    have hbox := sleeveLine_parameters_mem_box hc htcc hp0 hs0 hpT hsT
    exact deviceArmEvent_sleevePivotSlope_nonneg_of_box H S hS o n p s a b t
      ha hb hp0 hbox.1 hbox.2

/-- Endpoint form of the sleeve comparison curve on the product-polynomial
probability, including endpoint-safe rates. -/
theorem deviceArmEventWeight_sleeveLine_le
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (hS : S.Nonempty) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (sleeveLine H S p s (sleeveComparisonSpeed a b S) 0)
        (deviceArmEvent (graph H) (support H S) o n) ≤
      eventWeight (sleeveLine H S p s (sleeveComparisonSpeed a b S) T)
        (deviceArmEvent (graph H) (support H S) o n) := by
  have hmono := monotoneOn_deviceArmEvent_sleeveLine H S hS o n p s a b T
    ha hb hp0 hs0 hpT hsT
  have hmem0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hmemT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  exact hmono hmem0 hmemT hT

/-- The same endpoint comparison for actual normalized finite independent
bond/activation product laws. -/
theorem deviceArmEvent_productLaw_sleeveLine_le
    {V : Type u} (H : SimpleGraph V)
    [Fintype (graph H).edgeSet] [DecidableEq (graph H).edgeSet]
    (S : Finset H.edgeSet) (hS : S.Nonempty) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, sleeveLine H S p s (sleeveComparisonSpeed a b S) T x ∈ Icc (0 : ℝ) 1) :
    (OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw
          (sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 (Sum.inl e))
          (hr0 (Sum.inl e)))
        (fun z => boolLaw
          (sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 (Sum.inr z))
          (hr0 (Sum.inr z))))).event
        (deviceArmEvent (graph H) (support H S) o n) ≤
      (OpenPath.FinProb.pi (Sum.elim
        (fun e => boolLaw
          (sleeveLine H S p s (sleeveComparisonSpeed a b S) T (Sum.inl e))
          (hrT (Sum.inl e)))
        (fun z => boolLaw
          (sleeveLine H S p s (sleeveComparisonSpeed a b S) T (Sum.inr z))
          (hrT (Sum.inr z))))).event
        (deviceArmEvent (graph H) (support H S) o n) := by
  rw [← eventWeight_sleeveLine_eq_pi H S p s (sleeveComparisonSpeed a b S) 0 hr0,
    ← eventWeight_sleeveLine_eq_pi H S p s (sleeveComparisonSpeed a b S) T hrT]
  exact deviceArmEventWeight_sleeveLine_le H S hS o n p s a b T ha hb hT
    hp0 hs0 hpT hsT

end FK.AGImplant.Sleeve
