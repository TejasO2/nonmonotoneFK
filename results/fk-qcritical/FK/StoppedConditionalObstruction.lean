import FK.AdaptiveMarginalObstruction

/-!
# The stopped joint exterior has a different conditional marginal

This module constructs the natural stopped-history sigma algebra for the
one-coordinate ordered coupling used by `AdaptiveMarginalObstruction`.  On the
upper-open stratum the selected region is full, so no lower exterior coordinate
is revealed.  On the upper-closed stratum it is empty, so the lower coordinate
is revealed.  The upper selection itself is revealed in both cases.

The conditional expectation under this genuine joint stopped sigma algebra is
`2/3` on upper-open, not the original fair-marginal value `1/2`.  Its integral
nevertheless satisfies the tower identity and is `1/2`.  Thus the stopped-sigma
repair requires a conditional-marginal identification; the joint stopped
sigma algebra alone does not supply it.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

noncomputable section

namespace FKLimit.StoppedConditionalObstruction

open FKLimit.CouplingSealCounterexample

/-- Order and the two marginals alone force every lower-open sample into the
upper-open stratum.  This is valid for an arbitrary ordered coupling. -/
theorem lower_open_inter_upper_open_of_ordered
    {ν : Measure (Bool × Bool)}
    (hlower : ν {z | z.1 = true} = 1 / 2)
    (horder : ∀ᵐ z ∂ν, z.1 ≤ z.2) :
    ν {z | z.1 = true ∧ z.2 = true} = 1 / 2 := by
  have hbad : ν {z | ¬ z.1 ≤ z.2} = 0 := ae_iff.mp horder
  have hdiff : ν ({z | z.1 = true} \ {z | z.2 = true}) = 0 := by
    have heq : {z : Bool × Bool | ¬ z.1 ≤ z.2} =
        {z | z.1 = true} \ {z | z.2 = true} := by
      ext z
      rcases z with ⟨a, b⟩
      cases a <;> cases b <;> simp
    rw [← heq]
    exact hbad
  have hsum := measure_inter_add_sdiff (μ := ν) {z | z.1 = true}
    (t := {z | z.2 = true}) MeasurableSet.of_discrete
  rw [hdiff, add_zero, hlower] at hsum
  exact hsum

/-- Consequently the stopped upper-open conditional lower mass is forced to be
`2/3` for every coupling with the stated marginals and almost-sure order. -/
theorem conditional_lower_open_of_ordered
    {ν : Measure (Bool × Bool)}
    (hlower : ν {z | z.1 = true} = 1 / 2)
    (hupper : ν {z | z.2 = true} = 3 / 4)
    (horder : ∀ᵐ z ∂ν, z.1 ≤ z.2) :
    ν {z | z.1 = true ∧ z.2 = true} / ν {z | z.2 = true} = 2 / 3 := by
  rw [lower_open_inter_upper_open_of_ordered hlower horder, hupper]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- The stopped history.  The first bit is the upper selection.  If it is open,
the selected region is full and the second bit is a dummy.  If it is closed,
the selected region is empty and the second bit is the revealed lower bit. -/
def history (z : Bool × Bool) : Bool × Bool :=
  (z.2, if z.2 then true else z.1)

/-- The actual stopped-history sigma algebra on the joint configuration. -/
abbrev stoppedSigma : MeasurableSpace (Bool × Bool) :=
  MeasurableSpace.comap history inferInstance

/-- The original lower-open observable. -/
def lowerObservable (z : Bool × Bool) : ℝ := if z.1 then 1 else 0

/-- The upper-open observable. -/
def upperObservable (z : Bool × Bool) : ℝ := if z.2 then 1 else 0

/-- Conditional expectation against the stopped joint history. -/
def stoppedStage (z : Bool × Bool) : ℝ :=
  if z.2 then 2 / 3 else lowerObservable z

/-- The original fair-marginal stage value from the fixed-region calculation. -/
def originalStage (z : Bool × Bool) : ℝ := if z.2 then 1 / 2 else 0

/-- This is literally the fixed-region stage already audited in
`AdaptiveMarginalObstruction`, transported back to its Boolean coordinates. -/
lemma originalStage_eq_stageValue_region (z : Bool × Bool) :
    originalStage z = AdaptiveMarginalObstruction.stageValue
      (AdaptiveMarginalObstruction.region (AdaptiveMarginalObstruction.config z.2)) := by
  cases h : z.2 <;>
    simp [originalStage, AdaptiveMarginalObstruction.stageValue,
      AdaptiveMarginalObstruction.region, h]

@[simp] lemma history_open (b : Bool) : history (b, true) = (true, true) := by
  simp [history]

@[simp] lemma history_closed (b : Bool) : history (b, false) = (false, b) := by
  simp [history]

lemma measurable_history : Measurable history := measurable_of_finite _

lemma stoppedSigma_le : stoppedSigma ≤ (inferInstance : MeasurableSpace (Bool × Bool)) := by
  exact measurable_history.comap_le

lemma stoppedStage_eq_comp : stoppedStage =
    (fun h : Bool × Bool => if h.1 then 2 / 3 else if h.2 then 1 else 0) ∘ history := by
  funext z
  rcases z with ⟨a, b⟩
  cases a <;> cases b <;> rfl

lemma measurable_stoppedStage : Measurable[stoppedSigma] stoppedStage := by
  rw [stoppedStage_eq_comp]
  exact (measurable_of_finite _).comp (comap_measurable history)

lemma stronglyMeasurable_stoppedStage : StronglyMeasurable[stoppedSigma] stoppedStage :=
  measurable_stoppedStage.stronglyMeasurable

lemma integrable_lowerObservable : Integrable lowerObservable law.toMeasure :=
  Integrable.of_finite

lemma integrableOn_stoppedStage (s : Set (Bool × Bool)) :
    IntegrableOn stoppedStage s law.toMeasure := Integrable.of_finite

/-- The candidate stopped value has exactly the defining set-integral identity
of conditional expectation on every stopped-history measurable set. -/
theorem setIntegral_stoppedStage {s : Set (Bool × Bool)}
    (hs : MeasurableSet[stoppedSigma] s) :
    (∫ z in s, stoppedStage z ∂law.toMeasure) =
      ∫ z in s, lowerObservable z ∂law.toMeasure := by
  rcases hs with ⟨t, ht, rfl⟩
  rw [← integral_indicator (MeasurableSet.of_discrete),
    ← integral_indicator (MeasurableSet.of_discrete)]
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  by_cases hopen : (true, true) ∈ t <;>
    by_cases hff : (false, false) ∈ t <;>
    by_cases hft : (false, true) ∈ t <;>
    simp [Set.indicator, history, stoppedStage, lowerObservable,
      Fintype.sum_prod_type, hopen, hff, hft] <;>
    norm_num [ENNReal.toReal_div]

/-- The exact conditional expectation under the stopped joint sigma algebra. -/
theorem stoppedStage_ae_eq_condExp :
    stoppedStage =ᵐ[law.toMeasure]
      law.toMeasure[lowerObservable | stoppedSigma] := by
  exact ae_eq_condExp_of_forall_setIntegral_eq stoppedSigma_le
    integrable_lowerObservable (fun s _ _ => integrableOn_stoppedStage s)
    (fun s hs _ => setIntegral_stoppedStage hs)
    stronglyMeasurable_stoppedStage.aestronglyMeasurable

/-- At the positive-mass upper-open sample `(false, true)`, the actual stopped
conditional expectation is exactly `2/3`, not merely almost everywhere equal
to a function taking that value. -/
theorem condExp_lowerObservable_false_true :
    law.toMeasure[lowerObservable | stoppedSigma] (false, true) = 2 / 3 := by
  have hpoint : stoppedStage (false, true) =
      law.toMeasure[lowerObservable | stoppedSigma] (false, true) := by
    by_contra hne
    have hnull : law.toMeasure {z | ¬ stoppedStage z =
        law.toMeasure[lowerObservable | stoppedSigma] z} = 0 :=
      ae_iff.mp stoppedStage_ae_eq_condExp
    have hsub : ({(false, true)} : Set (Bool × Bool)) ⊆
        {z | ¬ stoppedStage z = law.toMeasure[lowerObservable | stoppedSigma] z} := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact hne
    have hle := measure_mono (μ := law.toMeasure) hsub
    rw [hnull, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete] at hle
    simp only [law_ft] at hle
    norm_num at hle
  rw [← hpoint]
  norm_num [stoppedStage, lowerObservable]

/-- A general stopped-tower criterion: identifying a candidate stage with the
actual joint conditional expectation, rather than merely with an original
marginal conditional expectation, is sufficient for its average to be the
original observable's average. -/
theorem integral_stage_eq_integral_observable_of_ae_eq_condExp
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {P : Measure[m₀] Ω} [IsFiniteMeasure P]
    (hm : m ≤ m₀) {f g : Ω → ℝ} (h : g =ᵐ[P] P[f | m]) :
    (∫ ω, g ω ∂P) = ∫ ω, f ω ∂P := by
  rw [integral_congr_ae h, integral_condExp hm]

/-- Two candidates compared through one properly stopped joint stage have equal
observable integrals as soon as the same stage is the actual stopped joint
conditional expectation of both observables.  No product coupling, DLR
replacement, or fixed-stage averaging assumption occurs in this criterion. -/
theorem integral_eq_of_common_stopped_stage
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {P : Measure[m₀] Ω} [IsFiniteMeasure P]
    (hm : m ≤ m₀) {f₁ f₂ g : Ω → ℝ}
    (h₁ : g =ᵐ[P] P[f₁ | m]) (h₂ : g =ᵐ[P] P[f₂ | m]) :
    (∫ ω, f₁ ω ∂P) = ∫ ω, f₂ ω ∂P := by
  exact (integral_stage_eq_integral_observable_of_ae_eq_condExp hm h₁).symm.trans
    (integral_stage_eq_integral_observable_of_ae_eq_condExp hm h₂)

/-- The stopped joint tower identity is exact. -/
theorem integral_stoppedStage :
    (∫ z, stoppedStage z ∂law.toMeasure) = 1 / 2 := by
  have h : (∫ z, stoppedStage z ∂law.toMeasure) =
      ∫ z, lowerObservable z ∂law.toMeasure :=
    integral_stage_eq_integral_observable_of_ae_eq_condExp
      (m := stoppedSigma) stoppedSigma_le stoppedStage_ae_eq_condExp
  rw [h, PMF.integral_eq_sum]
  simp [lowerObservable, Fintype.sum_prod_type]

/-- The original fair-marginal stage still has the previously observed `3/8`
average, now expressed on the Boolean pair. -/
theorem integral_originalStage :
    (∫ z, originalStage z ∂law.toMeasure) = 3 / 8 := by
  rw [PMF.integral_eq_sum]
  simp [originalStage, Fintype.sum_prod_type]
  norm_num [ENNReal.toReal_div]

/-- The original lower-open integral is the fair mass `1/2`. -/
theorem integral_lowerObservable :
    (∫ z, lowerObservable z ∂law.toMeasure) = 1 / 2 := by
  rw [PMF.integral_eq_sum]
  simp [lowerObservable, Fintype.sum_prod_type]

/-- The original stage is not the stopped joint conditional expectation. -/
theorem originalStage_not_ae_eq_condExp :
    ¬ originalStage =ᵐ[law.toMeasure]
      law.toMeasure[lowerObservable | stoppedSigma] := by
  intro h
  have hint : (∫ z, originalStage z ∂law.toMeasure) =
      ∫ z, lowerObservable z ∂law.toMeasure :=
    integral_stage_eq_integral_observable_of_ae_eq_condExp (m := stoppedSigma) stoppedSigma_le h
  rw [integral_originalStage, integral_lowerObservable] at hint
  norm_num at hint

/-- The discrepancy is visible on a positive-mass upper-open sample. -/
theorem originalStage_ne_stoppedStage_at_false_true :
    originalStage (false, true) ≠ stoppedStage (false, true) := by
  norm_num [originalStage, stoppedStage, lowerObservable]

/-- The stopped correction exactly accounts for the former `1/8` mass defect. -/
theorem original_stage_mass_defect :
    (∫ z, lowerObservable z ∂law.toMeasure) -
      (∫ z, originalStage z ∂law.toMeasure) = 1 / 8 := by
  rw [integral_lowerObservable, integral_originalStage]
  norm_num

end FKLimit.StoppedConditionalObstruction

#print axioms FKLimit.StoppedConditionalObstruction.lower_open_inter_upper_open_of_ordered
#print axioms FKLimit.StoppedConditionalObstruction.conditional_lower_open_of_ordered
#print axioms FKLimit.StoppedConditionalObstruction.originalStage_eq_stageValue_region
#print axioms FKLimit.StoppedConditionalObstruction.setIntegral_stoppedStage
#print axioms FKLimit.StoppedConditionalObstruction.stoppedStage_ae_eq_condExp
#print axioms FKLimit.StoppedConditionalObstruction.condExp_lowerObservable_false_true
#print axioms FKLimit.StoppedConditionalObstruction.integral_stage_eq_integral_observable_of_ae_eq_condExp
#print axioms FKLimit.StoppedConditionalObstruction.integral_eq_of_common_stopped_stage
#print axioms FKLimit.StoppedConditionalObstruction.integral_stoppedStage
#print axioms FKLimit.StoppedConditionalObstruction.integral_originalStage
#print axioms FKLimit.StoppedConditionalObstruction.originalStage_not_ae_eq_condExp
#print axioms FKLimit.StoppedConditionalObstruction.original_stage_mass_defect
