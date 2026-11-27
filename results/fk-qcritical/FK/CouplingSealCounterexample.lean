import FK.ConditionallyIndependentOrderedCoupling

/-!
# Ordered coupling need not preserve a free interior on an attained stratum

This is an adversarial finite component for the exploration step proposed for
Theorem 5.1.  A one-edge free Bernoulli law has open probability `1/2`.  It is
strictly dominated by the Bernoulli law with open probability `3/4`.  The PMF
below is an ordered coupling of these laws.  Nevertheless, on the upper-open
stratum the lower edge is open with probability `2/3`, not `1/2`.

On a graph consisting of disjoint single edges, every union of whole edges has
closed exterior frontier, and an upper configuration with an open edge gives a
sealed component containing that edge.  Thus the calculation is a counterexample
to the general assertion that an arbitrary ordered coupling has the
free-boundary Markov property on an attained closed-frontier/open-cluster
stratum.  It is not a counterexample to uniqueness in Theorem 5.1: the one-edge
free specification is of course unique.  Thus any adaptive argument which uses
this joint conditional law needs a special coupling or a different argument;
Strassen order and the marginal DLR equations alone do not supply it.  The file
does not rule out an argument using only the original marginal conditionals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FKLimit.CouplingSealCounterexample

/-- Joint masses for `(lower, upper)`:
`(true,true) ↦ 1/2`, `(false,true) ↦ 1/4`,
`(false,false) ↦ 1/4`, `(true,false) ↦ 0`. -/
noncomputable def weight : Bool × Bool → ℝ≥0∞
  | (true, true) => 1 / 2
  | (false, true) => 1 / 4
  | (false, false) => 1 / 4
  | (true, false) => 0

lemma weight_sum : ∑ z, weight z = 1 := by
  simp only [weight, Fintype.sum_prod_type, Fintype.sum_bool]
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_div]

noncomputable def law : PMF (Bool × Bool) := PMF.ofFintype weight weight_sum

@[simp] lemma law_tt : law (true, true) = 1 / 2 := by
  simp [law, weight]

@[simp] lemma law_ft : law (false, true) = 1 / 4 := by
  simp [law, weight]

@[simp] lemma law_ff : law (false, false) = 1 / 4 := by
  simp [law, weight]

@[simp] lemma law_tf : law (true, false) = 0 := by
  simp [law, weight]

lemma open_lower : law.toMeasure {z | z.1 = true} = 1 / 2 := by
  rw [PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type]

lemma open_upper : law.toMeasure {z | z.2 = true} = 3 / 4 := by
  rw [PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_div]

lemma order_violation : law.toMeasure {z | z.1 = true ∧ z.2 = false} = 0 := by
  rw [PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type]

lemma open_lower_and_upper : law.toMeasure {z | z.1 = true ∧ z.2 = true} = 1 / 2 := by
  rw [PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type]

/-- The two lower open strata are equally likely, so the lower marginal is the
free fair law. -/
lemma fair_lower_two_closed_strata :
    law.toMeasure {z | z.1 = true} = law.toMeasure {z | z.1 = false} := by
  have hfalse : law.toMeasure {z | z.1 = false} = 1 / 2 := by
    rw [PMF.toMeasure_apply_fintype]
    simp [Fintype.sum_prod_type]
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add]
  rw [open_lower, hfalse]

/-- On the attained upper-open stratum, the normalized lower-open probability
is `2/3`. -/
theorem conditional_lower_open_on_upper_open :
    law.toMeasure {z | z.1 = true ∧ z.2 = true} /
      law.toMeasure {z | z.2 = true} = 2 / 3 := by
  rw [open_lower_and_upper, open_upper]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- In particular, the attained-stratum lower law is not the original free
fair law. -/
theorem conditional_lower_open_ne_free :
    law.toMeasure {z | z.1 = true ∧ z.2 = true} /
      law.toMeasure {z | z.2 = true} ≠ law.toMeasure {z | z.1 = true} := by
  rw [conditional_lower_open_on_upper_open, open_lower]
  intro h
  have hreal := congrArg ENNReal.toReal h
  norm_num [ENNReal.toReal_div] at hreal

end FKLimit.CouplingSealCounterexample
