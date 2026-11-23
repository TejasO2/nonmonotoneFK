import Mathlib

/-! Standalone aggregate of the five checked direction-B files.
Generated only by concatenating their declarations; see README.md. -/

/- ===== ClosedCutset.lean ===== -/


/-!
# The deterministic closed-cutset update from Proposition 3.1

A configuration is a Boolean function on an arbitrary edge type.  The predicate
`K e ω` is the FK connection event for `e` in `ω`; it is deliberately kept
abstract so that the file applies to finite multigraphs and arbitrary boundary
wiring.  `IsClosedCutset` is the exact semantic property used in the paper:
closure of every edge of `χ` forces `K e` to fail.
-/

namespace FKEnhancement

open scoped BigOperators

abbrev Configuration (E : Type*) := E → Bool

/-- A Boolean edge opened by the strict threshold rule `u < r`. -/
noncomputable def threshold (u r : ℝ) : Bool := decide (u < r)

@[simp] theorem threshold_eq_true (u r : ℝ) : threshold u r = true ↔ u < r := by
  simp [threshold]

@[simp] theorem threshold_eq_false (u r : ℝ) : threshold u r = false ↔ r ≤ u := by
  simp [threshold, not_lt]

 theorem threshold_mono {u r s : ℝ} (hrs : r ≤ s) : threshold u r ≤ threshold u s := by
  rw [Bool.le_iff_imp]
  intro h
  exact (threshold_eq_true _ _).2 (lt_of_lt_of_le ((threshold_eq_true _ _).1 h) hrs)

/-- The two possible FK singleton thresholds: `p` on the connection event and
`p'` off it. -/
noncomputable def fkRate (K : E → Configuration E → Prop) (e : E)
    (p p' : ℝ) (ω : Configuration E) : ℝ := by
  classical
  exact if K e ω then p else p'

/-- One FK heat-bath update, sharing the uniform variable with other updates. -/
noncomputable def fkUpdate [DecidableEq E] (K : E → Configuration E → Prop) (e : E)
    (p p' u : ℝ) (ω : Configuration E) : Configuration E :=
  Function.update ω e (threshold u (fkRate K e p p' ω))

/-- A product-measure update at one edge. -/
noncomputable def productUpdate [DecidableEq E] (e : E) (r u : ℝ)
    (ω : Configuration E) : Configuration E :=
  Function.update ω e (threshold u r)

/-- `χ` is a closed cutset certificate for `K e`: if all its edges are closed,
the connection event for `e` is impossible. -/
def IsClosedCutset (K : E → Configuration E → Prop) (e : E)
    (χ : Set E) : Prop :=
  ∀ ω : Configuration E, (∀ a ∈ χ, ω a = false) → ¬ K e ω

/-- The cutsets allowed in Proposition 3.1 avoid `e` and all enhanced edges. -/
def IsAuxiliary (enhanced : Set E) (e : E) (χ : Set E) : Prop :=
  χ ⊆ {a | a ∉ enhanced ∧ a ≠ e}

/-- The family denoted `Q_Eb(e)` in the paper. -/
def CutsetFamily (K : E → Configuration E → Prop) (enhanced : Set E)
    (e : E) : Set (Set E) :=
  {χ | IsAuxiliary enhanced e χ ∧ IsClosedCutset K e χ}

/-- There is an allowed cutset all of whose edges are closed in `ω`. -/
def HasClosedCutset (K : E → Configuration E → Prop) (enhanced : Set E)
    (e : E) (ω : Configuration E) : Prop :=
  ∃ χ ∈ CutsetFamily K enhanced e, ∀ a ∈ χ, ω a = false

/-- Closed-cutset certificates propagate to smaller configurations. -/
theorem HasClosedCutset.mono {K : E → Configuration E → Prop}
    {enhanced : Set E} {e : E} {ω η : Configuration E} (hωη : ω ≤ η)
    (h : HasClosedCutset K enhanced e η) : HasClosedCutset K enhanced e ω := by
  rcases h with ⟨χ, hχ, hclosed⟩
  refine ⟨χ, hχ, ?_⟩
  intro a ha
  have hle : ω a ≤ η a := hωη a
  rw [Bool.le_iff_imp] at hle
  cases hωa : ω a with
  | false => rfl
  | true =>
      have hηa := hle hωa
      rw [hclosed a ha] at hηa
      contradiction

/-- The enhanced product update.  The certificate is tested in the supplied
upper configuration, exactly as in the coupled dynamics; the updated
configuration itself can be either the lower or the upper approximation. -/
noncomputable def enhancedProductUpdate [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (baseRate p' u : ℝ) (certificate ω : Configuration E) : Configuration E := by
  classical
  exact productUpdate e
    (if HasClosedCutset K enhanced e certificate then p' else baseRate) u ω

/-- The coupled update used at an enhanced edge.  Its three coordinates are the
lower product approximation, the FK configuration, and the upper product
approximation. -/
noncomputable def coupledEnhancedUpdate [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' u : ℝ) (y x z : Configuration E) :
    Configuration E × Configuration E × Configuration E := by
  classical
  exact (enhancedProductUpdate K enhanced e (min p p') p' u z y,
    fkUpdate K e p p' u x,
    enhancedProductUpdate K enhanced e (max p p') p' u z z)

/-- A non-enhanced (auxiliary) update uses the lower and upper endpoint rates. -/
noncomputable def coupledProductUpdate [DecidableEq E]
    (K : E → Configuration E → Prop) (e : E) (p p' u : ℝ)
    (y x z : Configuration E) : Configuration E × Configuration E × Configuration E :=
  (productUpdate e (min p p') u y, fkUpdate K e p p' u x,
    productUpdate e (max p p') u z)

private theorem fkUpdate_between [DecidableEq E]
    (K : E → Configuration E → Prop) (e : E) (p p' u : ℝ)
    (y x z : Configuration E) (a : E) (ha : a = e) :
    productUpdate e (min p p') u y a ≤ fkUpdate K e p p' u x a ∧
      fkUpdate K e p p' u x a ≤ productUpdate e (max p p') u z a := by
  subst a
  simp only [productUpdate, fkUpdate, Function.update_self]
  by_cases hK : K e x
  · simp only [fkRate, hK, if_true]
    exact ⟨threshold_mono (min_le_left p p'), threshold_mono (le_max_left p p')⟩
  · simp only [fkRate, hK, if_false]
    exact ⟨threshold_mono (min_le_right p p'), threshold_mono (le_max_right p p')⟩

/-- The per-coordinate comparison for an auxiliary update. -/
theorem coupledProductUpdate_le [DecidableEq E]
    (K : E → Configuration E → Prop) (e : E) (p p' u : ℝ)
    {y x z : Configuration E} (hyx : y ≤ x) (hxz : x ≤ z) :
    let t := coupledProductUpdate K e p p' u y x z
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  dsimp only [coupledProductUpdate]
  constructor <;> intro a
  · by_cases ha : a = e
    · exact (fkUpdate_between K e p p' u y x z a ha).1
    · simpa [productUpdate, fkUpdate, Function.update_of_ne ha] using hyx a
  · by_cases ha : a = e
    · exact (fkUpdate_between K e p p' u y x z a ha).2
    · simpa [productUpdate, fkUpdate, Function.update_of_ne ha] using hxz a

/-- This is the exact order-preservation step of the closed-cutset coupling in
Proposition 3.1.  No monotonicity of `K` is needed: the cutset certificate is
transferred from `z` to `x` using only `x ≤ z`. -/
theorem coupledEnhancedUpdate_le [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' u : ℝ) {y x z : Configuration E} (hyx : y ≤ x) (hxz : x ≤ z) :
    let t := coupledEnhancedUpdate K enhanced e p p' u y x z
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  classical
  dsimp only [coupledEnhancedUpdate]
  by_cases hc : HasClosedCutset K enhanced e z
  · have hcx : HasClosedCutset K enhanced e x := hc.mono hxz
    rcases hcx with ⟨χ, hχ, hclosed⟩
    have hK : ¬ K e x := hχ.2 x hclosed
    simp only [enhancedProductUpdate, productUpdate, fkUpdate, hc, if_true]
    constructor <;> intro a
    · by_cases ha : a = e
      · subst a
        simp only [Function.update_self, fkRate, hK, if_false]
        exact le_rfl
      · simpa [Function.update_of_ne ha] using hyx a
    · by_cases ha : a = e
      · subst a
        simp only [Function.update_self, fkRate, hK, if_false]
        exact le_rfl
      · simpa [Function.update_of_ne ha] using hxz a
  · simp only [enhancedProductUpdate, productUpdate, hc, if_false]
    exact coupledProductUpdate_le K e p p' u hyx hxz

end FKEnhancement


/- ===== EnhancedProbability.lean ===== -/


/-!
# Exact enhanced-edge probabilities

The uniform random variable is the canonical probability measure on
`unitInterval`.  Independence of the uniform variable and the old auxiliary
configuration is represented by the product measure `volume.prod μ`.
-/

namespace FKEnhancement

open MeasureTheory Set
open scoped unitInterval ENNReal

/-- The event that the enhanced product update opens its distinguished edge.
Before the update, the certificate event is `C`; its rate is `exceptional` on
`C` and `base` outside `C`. -/
noncomputable def enhancedOpenEvent {Ω : Type*} (base exceptional : I)
    (C : Set Ω) : Set (I × Ω) := by
  classical
  exact {a | (if a.2 ∈ C then threshold a.1 exceptional else threshold a.1 base) = true}

/-- The complementary event: the enhanced product update closes its edge. -/
noncomputable def enhancedClosedEvent {Ω : Type*} (base exceptional : I)
    (C : Set Ω) : Set (I × Ω) := by
  classical
  exact {a | (if a.2 ∈ C then threshold a.1 exceptional else threshold a.1 base) = false}

theorem enhancedClosedEvent_eq_compl {Ω : Type*} (base exceptional : I)
    (C : Set Ω) : enhancedClosedEvent base exceptional C = (enhancedOpenEvent base exceptional C)ᶜ := by
  classical
  ext a
  simp only [enhancedClosedEvent, enhancedOpenEvent, mem_compl_iff, mem_ofPred_eq]
  cases (if a.2 ∈ C then threshold a.1 exceptional else threshold a.1 base) <;> simp

/-- The scalar enhancement in Proposition 3.1 when `c` is the probability of a
closed-cutset certificate. -/
noncomputable def closedCutsetEnhancement (p p' c : ℝ) : ℝ := |p' - p| * c

@[simp] theorem closedCutsetEnhancement_of_le {p p' c : ℝ} (h : p ≤ p') :
    closedCutsetEnhancement p p' c = (p' - p) * c := by
  rw [closedCutsetEnhancement, abs_of_nonneg (sub_nonneg.mpr h)]

@[simp] theorem closedCutsetEnhancement_of_ge {p p' c : ℝ} (h : p' ≤ p) :
    closedCutsetEnhancement p p' c = (p - p') * c := by
  rw [closedCutsetEnhancement, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]

/-- In the `p ≤ p'` case, the open event splits into the always-open interval
below `p` and the additional interval below `p'` on the certificate. -/
theorem enhancedOpenEvent_eq_of_le {Ω : Type*} {p p' : I} (hp : p ≤ p')
    (C : Set Ω) :
    enhancedOpenEvent p p' C = (Iio p ×ˢ (univ : Set Ω)) ∪ (Ico p p' ×ˢ C) := by
  classical
  ext a
  rcases a with ⟨u, z⟩
  by_cases hz : z ∈ C
  · simp only [enhancedOpenEvent, hz, if_true, mem_ofPred_eq, threshold_eq_true,
      mem_union, mem_prod, mem_Iio, mem_univ, and_true, mem_Ico]
    constructor
    · intro h
      by_cases hup : u < p
      · exact Or.inl hup
      · exact Or.inr ⟨le_of_not_gt hup, h⟩
    · rintro (h | ⟨-, h⟩)
      · exact lt_of_lt_of_le h hp
      · exact h
  · simp [enhancedOpenEvent, hz, threshold_eq_true]

/-- In the `p' ≤ p` case, the closed event splits into the always-closed
interval above `p` and the additional interval above `p'` on the certificate. -/
theorem enhancedClosedEvent_eq_of_le {Ω : Type*} {p' p : I} (hp : p' ≤ p)
    (C : Set Ω) :
    enhancedClosedEvent p p' C = (Ici p ×ˢ (univ : Set Ω)) ∪ (Ico p' p ×ˢ C) := by
  classical
  ext a
  rcases a with ⟨u, z⟩
  by_cases hz : z ∈ C
  · simp only [enhancedClosedEvent, hz, if_true, mem_ofPred_eq, threshold_eq_false,
      mem_union, mem_prod, mem_Ici, mem_univ, and_true, mem_Ico]
    constructor
    · intro h
      by_cases hpu : p ≤ u
      · exact Or.inl hpu
      · exact Or.inr ⟨h, lt_of_not_ge hpu⟩
    · rintro (h | ⟨h, -⟩)
      · exact le_trans hp h
      · exact h
  · simp [enhancedClosedEvent, hz, threshold_eq_false]

private theorem disjoint_Iio_prod_Ico_prod {Ω : Type*} (p p' : I)
    (C : Set Ω) : Disjoint (Iio p ×ˢ (univ : Set Ω)) (Ico p p' ×ˢ C) := by
  rw [Set.disjoint_left]
  rintro ⟨u, z⟩ hu hu'
  exact (not_lt_of_ge hu'.1.1) hu.1

private theorem disjoint_Ici_prod_Ico_prod {Ω : Type*} (p' p : I)
    (C : Set Ω) : Disjoint (Ici p ×ˢ (univ : Set Ω)) (Ico p' p ×ˢ C) := by
  rw [Set.disjoint_left]
  rintro ⟨u, z⟩ hu hu'
  exact (not_le_of_gt hu'.1.2) hu.1

/-- **Lower-enhancement probability.**  If `p ≤ p'` and `C` has probability
`μ C`, the edge opened by the enhanced update has probability
`p + (p' - p) * μ C`.  This is the exact calculation yielding
`p + ε̂_e` in part (1) of Proposition 3.1. -/
theorem measure_enhancedOpenEvent_of_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p p' : I} (hp : p ≤ p')
    {C : Set Ω} (hC : MeasurableSet C) :
    (volume.prod μ) (enhancedOpenEvent p p' C) =
      ENNReal.ofReal (p : ℝ) + ENNReal.ofReal ((p' : ℝ) - p) * μ C := by
  rw [enhancedOpenEvent_eq_of_le hp,
    measure_union (disjoint_Iio_prod_Ico_prod p p' C) (measurableSet_Ico.prod hC),
    Measure.prod_prod, Measure.prod_prod, unitInterval.volume_Iio,
    unitInterval.volume_Ico]
  simp

/-- **Upper-enhancement probability.**  If `p' ≤ p`, the edge closed by the
enhanced update has probability `1 - p + (p - p') * μ C`.  This is the exact
calculation yielding `1 - p + ε̂_e` in part (2) of Proposition 3.1. -/
theorem measure_enhancedClosedEvent_of_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p' p : I} (hp : p' ≤ p)
    {C : Set Ω} (hC : MeasurableSet C) :
    (volume.prod μ) (enhancedClosedEvent p p' C) =
      ENNReal.ofReal (1 - (p : ℝ)) + ENNReal.ofReal ((p : ℝ) - p') * μ C := by
  rw [enhancedClosedEvent_eq_of_le hp,
    measure_union (disjoint_Ici_prod_Ico_prod p' p C) (measurableSet_Ico.prod hC),
    Measure.prod_prod, Measure.prod_prod, unitInterval.volume_Ici,
    unitInterval.volume_Ico]
  simp

/-- The enhanced open probability is bounded by `p'`, so the stated lower
product law can be coupled below the `p'`-product law. -/
theorem enhancedOpenRate_le {p p' c : ℝ} (_hp : 0 ≤ p) (hpp' : p ≤ p')
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    p + closedCutsetEnhancement p p' c ≤ p' := by
  rw [closedCutsetEnhancement_of_le hpp']
  have hmul : (p' - p) * c ≤ (p' - p) * 1 :=
    mul_le_mul_of_nonneg_left hc1 (sub_nonneg.mpr hpp')
  linarith

/-- In the reverse case the enhanced open rate `p - ε` lies between `p'`
and `p`, giving the coupling in the other direction. -/
theorem enhancedOpenRate_bounds_of_ge {p p' c : ℝ} (_hp : p ≤ 1) (_hp' : 0 ≤ p')
    (hp'p : p' ≤ p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    p' ≤ p - closedCutsetEnhancement p p' c ∧
      p - closedCutsetEnhancement p p' c ≤ p := by
  rw [closedCutsetEnhancement_of_ge hp'p]
  constructor
  · have hmul : (p - p') * c ≤ (p - p') * 1 :=
      mul_le_mul_of_nonneg_left hc1 (sub_nonneg.mpr hp'p)
    linarith
  · exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hp'p) hc0)

end FKEnhancement


/- ===== ProductMeasure.lean ===== -/


/-!
# Inhomogeneous Bernoulli product laws on configurations

The rate of each edge belongs to `unitInterval`; `true` is open and `false` is
closed.  The law is the finite product of Mathlib's Bernoulli measures, not an
axiomatized family of marginal probabilities.
-/

namespace FKEnhancement

open MeasureTheory Set
open scoped unitInterval ENNReal ProbabilityTheory BigOperators

/-- The independent inhomogeneous Bernoulli bond law on `E → Bool`. -/
noncomputable def bernoulliProduct {E : Type*} [Fintype E] (rates : E → I) :
    Measure (Configuration E) :=
  Measure.pi (fun e => Ber(true, false, rates e))

instance {E : Type*} [Fintype E] (rates : E → I) :
    IsProbabilityMeasure (bernoulliProduct rates) := by
  unfold bernoulliProduct
  infer_instance

/-- The cylinder on which all edges of the finite set `χ` are closed. -/
def closedCylinder {E : Type*} (χ : Finset E) : Set (Configuration E) :=
  ((χ : Set E).pi fun _ => {false})

@[simp] theorem mem_closedCylinder {E : Type*} {χ : Finset E}
    {ω : Configuration E} : ω ∈ closedCylinder χ ↔ ∀ a ∈ χ, ω a = false := by
  simp [closedCylinder]

/-- Evaluation at an edge has the prescribed Bernoulli law. -/
theorem bernoulliProduct_map_eval {E : Type*} [Fintype E] [DecidableEq E]
    (rates : E → I) (e : E) :
    (bernoulliProduct rates).map (Function.eval e) = Ber(true, false, rates e) := by
  exact (measurePreserving_eval (fun e => Ber(true, false, rates e)) e).map_eq

/-- The probability that a given edge is open is exactly its parameter. -/
theorem bernoulliProduct_apply_open {E : Type*} [Fintype E] [DecidableEq E]
    (rates : E → I) (e : E) :
    bernoulliProduct rates {ω | ω e = true} = unitInterval.toNNReal (rates e) := by
  change bernoulliProduct rates (Function.eval e ⁻¹' {true}) = _
  rw [← Measure.map_apply (measurable_pi_apply e) (by simp),
    bernoulliProduct_map_eval]
  simp

/-- Product formula for a closed-edge cylinder. -/
theorem bernoulliProduct_closedCylinder {E : Type*} [Fintype E]
    (rates : E → I) (χ : Finset E) :
    bernoulliProduct rates (closedCylinder χ) =
      ∏ a ∈ χ, Ber(true, false, rates a) ({false} : Set Bool) := by
  simp [bernoulliProduct, closedCylinder, Measure.pi_pi_finset]

/-- A finite closed cylinder has positive probability whenever each of its edge
rates is strictly below one. -/
theorem bernoulliProduct_closedCylinder_pos {E : Type*} [Fintype E]
    (rates : E → I) (χ : Finset E) (hrates : ∀ a ∈ χ, rates a < 1) :
    0 < bernoulliProduct rates (closedCylinder χ) := by
  rw [bernoulliProduct_closedCylinder, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro a ha
  have h : Ber(true, false, rates a) ({false} : Set Bool) =
      unitInterval.toNNReal (σ (rates a)) := by simp
  have hpos : 0 < Ber(true, false, rates a) ({false} : Set Bool) := by
    rw [h, ENNReal.coe_pos, ← NNReal.coe_pos, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq]
    exact sub_pos.mpr (hrates a ha)
  exact ne_of_gt hpos

/-- The closed-cutset event appearing in the enhancement parameter. -/
def certificateEvent {E : Type*} (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) : Set (Configuration E) :=
  {ω | HasClosedCutset K enhanced e ω}

/-- One permitted finite cutset with all closed probabilities positive forces
the full existential certificate event to have positive probability. -/
theorem bernoulliProduct_certificateEvent_pos {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (rates : E → I) (χ : Finset E)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e)
    (hrates : ∀ a ∈ χ, rates a < 1) :
    0 < bernoulliProduct rates (certificateEvent K enhanced e) := by
  apply lt_of_lt_of_le (bernoulliProduct_closedCylinder_pos rates χ hrates)
  apply measure_mono
  intro ω hω
  exact ⟨(χ : Set E), hχ, fun a ha => hω a (by exact_mod_cast ha)⟩

end FKEnhancement

namespace FKEnhancement

open MeasureTheory Set
open scoped unitInterval ENNReal ProbabilityTheory BigOperators

/-- The real-valued probability of a closed-cutset certificate. -/
noncomputable def certificateProbability {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (rates : E → I) : ℝ :=
  (bernoulliProduct rates (certificateEvent K enhanced e)).toReal

theorem certificateProbability_nonneg {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (rates : E → I) : 0 ≤ certificateProbability K enhanced e rates :=
  ENNReal.toReal_nonneg

theorem certificateProbability_le_one {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (rates : E → I) : certificateProbability K enhanced e rates ≤ 1 := by
  have h : bernoulliProduct rates (certificateEvent K enhanced e) ≤ 1 := by
    calc
      bernoulliProduct rates (certificateEvent K enhanced e) ≤
          bernoulliProduct rates Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  simpa [certificateProbability] using ENNReal.toReal_mono (by simp) h

theorem certificateProbability_pos {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (rates : E → I) (χ : Finset E)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e)
    (hrates : ∀ a ∈ χ, rates a < 1) :
    0 < certificateProbability K enhanced e rates := by
  exact ENNReal.toReal_pos
    (ne_of_gt (bernoulliProduct_certificateEvent_pos K enhanced e rates χ hχ hrates))
    (measure_ne_top _ _)

end FKEnhancement


/- ===== StochasticDomination.lean ===== -/


/-!
# Ordered couplings and stochastic domination

This file isolates the measure-theoretic step used at the end of the proof of
Proposition 3.1: a coupling whose first coordinate is almost surely below its
second gives domination on every increasing event.
-/

namespace FKEnhancement

open MeasureTheory Set Filter

/-- Stochastic domination on increasing events, with measurability made
explicit.  On the finite configuration space `{0,1}^E` every set satisfies the
measurability premise, recovering the definition in the paper. -/
def StochasticallyDominates {α : Type*} [MeasurableSpace α] [LE α]
    (μ ν : Measure α) : Prop :=
  ∀ A : Set α, MeasurableSet A → IsUpperSet A → μ A ≤ ν A

theorem StochasticallyDominates.refl {α : Type*} [MeasurableSpace α] [LE α]
    (μ : Measure α) : StochasticallyDominates μ μ := by
  intro A _ _
  exact le_rfl

theorem StochasticallyDominates.trans {α : Type*} [MeasurableSpace α] [LE α]
    {μ ν ξ : Measure α} (hμν : StochasticallyDominates μ ν)
    (hνξ : StochasticallyDominates ν ξ) : StochasticallyDominates μ ξ := by
  intro A hA hupper
  exact (hμν A hA hupper).trans (hνξ A hA hupper)

/-- **Strassen's easy direction.**  If `κ` has first marginal `μ`, second
marginal `ν`, and orders its coordinates almost surely, then `μ` is dominated
by `ν` on all increasing measurable events.  No independence or finiteness
assumption on the probability space is needed. -/
theorem stochasticallyDominates_of_coupling {α : Type*} [MeasurableSpace α]
    [Preorder α] (μ ν : Measure α) (κ : Measure (α × α))
    (hfst : κ.map Prod.fst = μ) (hsnd : κ.map Prod.snd = ν)
    (horder : ∀ᵐ a ∂κ, a.1 ≤ a.2) : StochasticallyDominates μ ν := by
  intro A hA hupper
  rw [← hfst, ← hsnd, Measure.map_apply measurable_fst hA,
    Measure.map_apply measurable_snd hA]
  apply measure_mono_ae
  filter_upwards [horder] with a ha
  intro haA
  exact hupper ha haA

/-- A version for probability mass functions on discrete configuration spaces.
The coupling is itself a `PMF`, and the two `PMF.map` assumptions are exactly
its marginal laws. -/
theorem stochasticallyDominates_of_pmf_coupling {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [Preorder α]
    (μ ν : PMF α) (κ : PMF (α × α))
    (hfst : κ.map Prod.fst = μ) (hsnd : κ.map Prod.snd = ν)
    (horder : ∀ a : α × α, κ a ≠ 0 → a.1 ≤ a.2) :
    StochasticallyDominates μ.toMeasure ν.toMeasure := by
  apply stochasticallyDominates_of_coupling μ.toMeasure ν.toMeasure κ.toMeasure
  · rw [PMF.toMeasure_map Prod.fst κ measurable_fst, hfst]
  · rw [PMF.toMeasure_map Prod.snd κ measurable_snd, hsnd]
  · rw [ae_iff, κ.toMeasure_apply_eq_zero_iff (Set.to_countable _).measurableSet,
      Set.disjoint_left]
    intro a ha hbad
    exact hbad (horder a ha)

end FKEnhancement

namespace FKEnhancement

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-- On a finite discrete state space, the real mass of a set is the finite sum
of the PMF values on that set. -/
theorem pmf_toReal_toMeasure_eq_sum {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] [DiscreteMeasurableSpace α]
    (π : PMF α) (A : Set α) :
    (π.toMeasure A).toReal = ∑ a, (A.indicator π a).toReal := by
  classical
  rw [PMF.toMeasure_apply_fintype]
  apply ENNReal.toReal_sum
  intro a _
  simp only [Set.indicator_apply]
  split
  · exact PMF.apply_ne_top π a
  · simp

/-- Pointwise convergence of PMF masses on a finite discrete state space gives
convergence of the real probability of every event. -/
theorem tendsto_pmf_toReal_toMeasure {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α] [DiscreteMeasurableSpace α]
    (π : PMF α) (πn : ℕ → PMF α)
    (hπ : ∀ a, Tendsto (fun n => (πn n a).toReal) atTop (𝓝 (π a).toReal))
    (A : Set α) :
    Tendsto (fun n => ((πn n).toMeasure A).toReal) atTop (𝓝 (π.toMeasure A).toReal) := by
  classical
  simp_rw [pmf_toReal_toMeasure_eq_sum]
  apply tendsto_finsetSum Finset.univ
  intro a _
  by_cases ha : a ∈ A
  · simpa [Set.indicator_of_mem ha] using hπ a
  · simp [Set.indicator_of_notMem ha]

/-- **Finite-time ordered couplings pass to marginal limits.**  This is the
last analytical step needed in the proof of Proposition 3.1: it is enough to
construct, along any sequence of times tending to infinity, ordered coupled
triples whose lower/FK (or FK/upper) marginal laws converge to the two target
laws.  No limit coupling or FKG property is required. -/
theorem stochasticallyDominates_of_tendsto_pmf_couplings {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    [DiscreteMeasurableSpace α] [Preorder α]
    (μ ν : PMF α) (μn νn : ℕ → PMF α) (κn : ℕ → PMF (α × α))
    (hfst : ∀ n, (κn n).map Prod.fst = μn n)
    (hsnd : ∀ n, (κn n).map Prod.snd = νn n)
    (horder : ∀ n a, κn n a ≠ 0 → a.1 ≤ a.2)
    (hμ : ∀ a, Tendsto (fun n => (μn n a).toReal) atTop (𝓝 (μ a).toReal))
    (hν : ∀ a, Tendsto (fun n => (νn n a).toReal) atTop (𝓝 (ν a).toReal)) :
    StochasticallyDominates μ.toMeasure ν.toMeasure := by
  intro A hA hupper
  have hdom : ∀ n, StochasticallyDominates (μn n).toMeasure (νn n).toMeasure := by
    intro n
    exact stochasticallyDominates_of_pmf_coupling (μn n) (νn n) (κn n)
      (hfst n) (hsnd n) (horder n)
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  exact le_of_tendsto_of_tendsto'
    (tendsto_pmf_toReal_toMeasure μ μn hμ A)
    (tendsto_pmf_toReal_toMeasure ν νn hν A)
    (fun n => ENNReal.toReal_mono (measure_ne_top _ _) (hdom n A hA hupper))

end FKEnhancement

namespace FKEnhancement

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-- The three-marginal form of the limit argument in Proposition 3.1.  The
hypotheses describe only the coupled finite-time dynamics: the three marginal
projections, almost-sure ordering on the support, and convergence of each
marginal.  The two limiting comparison inequalities are conclusions, not
assumptions. -/
theorem sandwich_domination_of_tendsto_pmf_triples {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    [DiscreteMeasurableSpace α] [Preorder α]
    (lower fk upper : PMF α) (lowerN fkN upperN : ℕ → PMF α)
    (joint : ℕ → PMF (α × α × α))
    (hlower : ∀ n, (joint n).map (fun t => t.1) = lowerN n)
    (hfk : ∀ n, (joint n).map (fun t => t.2.1) = fkN n)
    (hupper : ∀ n, (joint n).map (fun t => t.2.2) = upperN n)
    (horder : ∀ n t, joint n t ≠ 0 → t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)
    (hlowerLim : ∀ a, Tendsto (fun n => (lowerN n a).toReal) atTop
      (𝓝 (lower a).toReal))
    (hfkLim : ∀ a, Tendsto (fun n => (fkN n a).toReal) atTop
      (𝓝 (fk a).toReal))
    (hupperLim : ∀ a, Tendsto (fun n => (upperN n a).toReal) atTop
      (𝓝 (upper a).toReal)) :
    StochasticallyDominates lower.toMeasure fk.toMeasure ∧
      StochasticallyDominates fk.toMeasure upper.toMeasure := by
  let lowerPair : ℕ → PMF (α × α) := fun n =>
    (joint n).map (fun t => (t.1, t.2.1))
  let upperPair : ℕ → PMF (α × α) := fun n =>
    (joint n).map (fun t => (t.2.1, t.2.2))
  have lowerFst : ∀ n, (lowerPair n).map Prod.fst = lowerN n := by
    intro n
    simpa [lowerPair, PMF.map_comp, Function.comp_def] using hlower n
  have lowerSnd : ∀ n, (lowerPair n).map Prod.snd = fkN n := by
    intro n
    simpa [lowerPair, PMF.map_comp, Function.comp_def] using hfk n
  have upperFst : ∀ n, (upperPair n).map Prod.fst = fkN n := by
    intro n
    simpa [upperPair, PMF.map_comp, Function.comp_def] using hfk n
  have upperSnd : ∀ n, (upperPair n).map Prod.snd = upperN n := by
    intro n
    simpa [upperPair, PMF.map_comp, Function.comp_def] using hupper n
  have lowerOrder : ∀ n a, lowerPair n a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    have ha' : a ∈ (lowerPair n).support := ha
    change a ∈ ((joint n).map (fun t => (t.1, t.2.1))).support at ha'
    rw [PMF.mem_support_map_iff] at ha'
    rcases ha' with ⟨t, ht, rfl⟩
    exact (horder n t ht).1
  have upperOrder : ∀ n a, upperPair n a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    have ha' : a ∈ (upperPair n).support := ha
    change a ∈ ((joint n).map (fun t => (t.2.1, t.2.2))).support at ha'
    rw [PMF.mem_support_map_iff] at ha'
    rcases ha' with ⟨t, ht, rfl⟩
    exact (horder n t ht).2
  exact ⟨stochasticallyDominates_of_tendsto_pmf_couplings lower fk lowerN fkN
      lowerPair lowerFst lowerSnd lowerOrder hlowerLim hfkLim,
    stochasticallyDominates_of_tendsto_pmf_couplings fk upper fkN upperN
      upperPair upperFst upperSnd upperOrder hfkLim hupperLim⟩

end FKEnhancement


/- ===== Proposition31.lean ===== -/


/-!
# Proposition 3.1: exact rates and the coupled-limit comparison

This file gives the exact cutset enhancement and the lower/upper inhomogeneous
product laws from the paper.  The two main comparison theorems take as input the
finite-time ordered couplings supplied by the Glauber construction and conclude
the limiting stochastic comparison.  Construction and invariance of those
couplings are deliberately explicit inputs, not hidden in a definition.
-/

namespace FKEnhancement

open MeasureTheory Set Filter
open scoped unitInterval ENNReal ProbabilityTheory BigOperators Topology

/-- Product-measure probability of a closed-cutset certificate, using the
`max(p,p')` law exactly as in Proposition 3.1. -/
noncomputable def cutsetWeight {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I) (e : E) : ℝ :=
  certificateProbability K enhanced e (fun _ => max p p')

/-- The enhancement `ε̂_e = |p'-p| P_max(∃χ closed)`. -/
noncomputable def cutsetEpsilon {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I) (e : E) : ℝ :=
  closedCutsetEnhancement (p : ℝ) (p' : ℝ) (cutsetWeight K enhanced p p' e)

theorem cutsetWeight_nonneg {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I) (e : E) :
    0 ≤ cutsetWeight K enhanced p p' e :=
  certificateProbability_nonneg _ _ _ _

theorem cutsetWeight_le_one {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I) (e : E) :
    cutsetWeight K enhanced p p' e ≤ 1 :=
  certificateProbability_le_one _ _ _ _

/-- The real open rate of the lower product law in the case `p ≤ p'`. -/
noncomputable def lowerEnhancedRate {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I) (e : E) : ℝ := by
  classical
  exact if e ∈ enhanced then (p : ℝ) + cutsetEpsilon K enhanced p p' e else p

/-- The real open rate of the upper product law in the case `p' ≤ p`. -/
noncomputable def upperEnhancedRate {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I) (e : E) : ℝ := by
  classical
  exact if e ∈ enhanced then (p : ℝ) - cutsetEpsilon K enhanced p p' e else p

theorem lowerEnhancedRate_nonneg {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (_hp : p ≤ p') (e : E) : 0 ≤ lowerEnhancedRate K enhanced p p' e := by
  classical
  simp only [lowerEnhancedRate]
  split_ifs
  · exact add_nonneg p.2.1 (mul_nonneg (abs_nonneg _) (cutsetWeight_nonneg K enhanced p p' e))
  · exact p.2.1

theorem lowerEnhancedRate_le {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (e : E) : lowerEnhancedRate K enhanced p p' e ≤ (p' : ℝ) := by
  classical
  simp only [lowerEnhancedRate]
  split_ifs
  · exact enhancedOpenRate_le p.2.1 hp (cutsetWeight_nonneg K enhanced p p' e)
      (cutsetWeight_le_one K enhanced p p' e)
  · exact hp

theorem upperEnhancedRate_nonneg {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) : 0 ≤ upperEnhancedRate K enhanced p p' e := by
  classical
  simp only [upperEnhancedRate]
  split_ifs
  · exact p'.2.1.trans (enhancedOpenRate_bounds_of_ge p.2.2 p'.2.1 hp
      (cutsetWeight_nonneg K enhanced p p' e) (cutsetWeight_le_one K enhanced p p' e)).1
  · exact p.2.1

theorem upperEnhancedRate_le_one {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) : upperEnhancedRate K enhanced p p' e ≤ 1 := by
  classical
  simp only [upperEnhancedRate]
  split_ifs
  · exact le_trans (enhancedOpenRate_bounds_of_ge p.2.2 p'.2.1 hp
      (cutsetWeight_nonneg K enhanced p p' e) (cutsetWeight_le_one K enhanced p p' e)).2 p.2.2
  · exact p.2.2

/-- The exact lower product rates `p + ε̂_e 1_{e∈Ê}` when `p ≤ p'`. -/
noncomputable def lowerEnhancedRates {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') : E → I := fun e =>
  ⟨lowerEnhancedRate K enhanced p p' e,
    lowerEnhancedRate_nonneg K enhanced hp e,
    (lowerEnhancedRate_le K enhanced hp e).trans p'.2.2⟩

/-- The exact upper product rates `p - ε̂_e 1_{e∈Ê}` when `p' ≤ p`. -/
noncomputable def upperEnhancedRates {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) : E → I := fun e =>
  ⟨upperEnhancedRate K enhanced p p' e,
    upperEnhancedRate_nonneg K enhanced hp e,
    upperEnhancedRate_le_one K enhanced hp e⟩

/-- The lower enhanced product law in part (1) of Proposition 3.1. -/
noncomputable def lowerEnhancedLaw {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') : Measure (Configuration E) :=
  bernoulliProduct (lowerEnhancedRates K enhanced hp)

/-- The upper enhanced product law in part (2) of Proposition 3.1. -/
noncomputable def upperEnhancedLaw {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) : Measure (Configuration E) :=
  bernoulliProduct (upperEnhancedRates K enhanced hp)

/-- **Proposition 3.1(1), coupled-dynamics form.**  Given finite-time couplings
of the lower enhanced law to the FK law, with the lower coordinate almost surely
below the FK coordinate and with both marginal limits, the limiting enhanced
product law is stochastically below the FK law on all increasing events. -/
theorem closedCutset_lower_comparison_of_tendsto_dynamics {E : Type*}
    [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (lower fk : PMF (Configuration E))
    (lowerN fkN : ℕ → PMF (Configuration E))
    (joint : ℕ → PMF (Configuration E × Configuration E))
    (hlowerLaw : lower.toMeasure = lowerEnhancedLaw K enhanced hp)
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = fkN n)
    (horder : ∀ n a, joint n a ≠ 0 → a.1 ≤ a.2)
    (hlowerLim : ∀ ω, Tendsto (fun n => (lowerN n ω).toReal) atTop
      (𝓝 (lower ω).toReal))
    (hfkLim : ∀ ω, Tendsto (fun n => (fkN n ω).toReal) atTop
      (𝓝 (fk ω).toReal)) :
    StochasticallyDominates (lowerEnhancedLaw K enhanced hp) fk.toMeasure := by
  rw [← hlowerLaw]
  exact stochasticallyDominates_of_tendsto_pmf_couplings lower fk lowerN fkN joint
    hfst hsnd horder hlowerLim hfkLim

/-- **Proposition 3.1(2), coupled-dynamics form.**  With the opposite ordered
couplings and marginal limits, the FK law is stochastically below the upper
enhanced product law on all increasing events. -/
theorem closedCutset_upper_comparison_of_tendsto_dynamics {E : Type*}
    [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (fk upper : PMF (Configuration E))
    (fkN upperN : ℕ → PMF (Configuration E))
    (joint : ℕ → PMF (Configuration E × Configuration E))
    (hupperLaw : upper.toMeasure = upperEnhancedLaw K enhanced hp)
    (hfst : ∀ n, (joint n).map Prod.fst = fkN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, joint n a ≠ 0 → a.1 ≤ a.2)
    (hfkLim : ∀ ω, Tendsto (fun n => (fkN n ω).toReal) atTop
      (𝓝 (fk ω).toReal))
    (hupperLim : ∀ ω, Tendsto (fun n => (upperN n ω).toReal) atTop
      (𝓝 (upper ω).toReal)) :
    StochasticallyDominates fk.toMeasure (upperEnhancedLaw K enhanced hp) := by
  rw [← hupperLaw]
  exact stochasticallyDominates_of_tendsto_pmf_couplings fk upper fkN upperN joint
    hfst hsnd horder hfkLim hupperLim

/-- A permitted finite cutset with positive closed probability gives strictly
positive enhancement whenever `p ≠ p'`.  This isolates the graph-theoretic input
needed for a non-identically-zero enhancement in Theorem 1.2. -/
theorem cutsetEpsilon_pos {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (p p' : I)
    (hp : p ≠ p') (e : E) (χ : Finset E)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e)
    (hrates : ∀ a ∈ χ, max p p' < (1 : I)) :
    0 < cutsetEpsilon K enhanced p p' e := by
  have hpne : (p' : ℝ) ≠ (p : ℝ) := by
    intro h
    apply hp
    exact Subtype.ext h.symm
  rw [cutsetEpsilon, closedCutsetEnhancement]
  apply mul_pos (abs_pos.mpr (sub_ne_zero.mpr hpne))
  exact certificateProbability_pos K enhanced e (fun _ => max p p') χ hχ
    (fun a ha => hrates a ha)

end FKEnhancement

namespace FKEnhancement

open MeasureTheory Set Filter
open scoped unitInterval ENNReal ProbabilityTheory BigOperators Topology

/-- Exact enhanced-edge open marginal in the `p ≤ p'` case, expressed using
the same `lowerEnhancedRate` that defines `lowerEnhancedLaw`.  This is the
enhanced-edge part of the stationarity calculation in the paper. -/
theorem measure_enhancedOpenEvent_eq_lowerEnhancedRate {E : Type*}
    [Fintype E] (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') {e : E} (he : e ∈ enhanced) :
    let μ := bernoulliProduct (fun _ : E => max p p')
    (volume.prod μ) (enhancedOpenEvent p p' (certificateEvent K enhanced e)) =
      ENNReal.ofReal (lowerEnhancedRate K enhanced p p' e) := by
  let μ := bernoulliProduct (fun _ : E => max p p')
  dsimp only
  rw [measure_enhancedOpenEvent_of_le μ hp MeasurableSet.of_discrete]
  simp only [lowerEnhancedRate, he, if_true, cutsetEpsilon, cutsetWeight,
    closedCutsetEnhancement_of_le hp, certificateProbability]
  rw [ENNReal.ofReal_add p.2.1 (mul_nonneg (sub_nonneg.mpr hp) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (sub_nonneg.mpr hp), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Exact enhanced-edge closed marginal in the `p' ≤ p` case.  It is the
complement of `upperEnhancedRate`, matching `1-p+ε̂_e` in the paper. -/
theorem measure_enhancedClosedEvent_eq_one_sub_upperEnhancedRate {E : Type*}
    [Fintype E] (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) {e : E} (he : e ∈ enhanced) :
    let μ := bernoulliProduct (fun _ : E => max p p')
    (volume.prod μ) (enhancedClosedEvent p p' (certificateEvent K enhanced e)) =
      ENNReal.ofReal (1 - upperEnhancedRate K enhanced p p' e) := by
  let μ := bernoulliProduct (fun _ : E => max p p')
  dsimp only
  rw [measure_enhancedClosedEvent_of_le μ hp MeasurableSet.of_discrete]
  simp only [upperEnhancedRate, he, if_true, cutsetEpsilon, cutsetWeight,
    closedCutsetEnhancement_of_ge hp, certificateProbability]
  have hreal : 1 - ((p : ℝ) - ((p : ℝ) - p') *
      (bernoulliProduct (fun _ : E => max p p') (certificateEvent K enhanced e)).toReal) =
      1 - (p : ℝ) + ((p : ℝ) - p') *
        (bernoulliProduct (fun _ : E => max p p') (certificateEvent K enhanced e)).toReal := by
    ring
  rw [hreal, ENNReal.ofReal_add (sub_nonneg.mpr p.2.2)
      (mul_nonneg (sub_nonneg.mpr hp) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (sub_nonneg.mpr hp), ENNReal.ofReal_toReal (measure_ne_top _ _)]

end FKEnhancement
