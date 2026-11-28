# The stopped joint conditional versus the original marginal stage

`FK.StoppedConditionalObstruction` complements the fixed-stage averaging
counterexample by conditioning on the **joint stopped history** rather than
on an original marginal's upper-selected region. It identifies precisely what
that change restores and what remains unproved for a general common-dominant
uniqueness argument.

## The genuine joint stopped history

For the ordered Boolean pair `z = (lower, upper)`, the upper bit selects the
finite region. On upper-open the region is full; on upper-closed it is empty.
The joint history records the upper bit and, on upper-closed only, the lower
bit. Its induced measurable space is the actual comap `stoppedSigma`.

`setIntegral_stoppedStage` verifies the desired set-integral identity on every
stopped-history measurable set. This proves
`stoppedStage_ae_eq_condExp`: the explicit stage is almost surely the actual
joint conditional expectation. It is not just a stage chosen to have the right
integral.

Order forces every lower-open sample to be upper-open. Consequently the
stopped upper-open fibre consists of two samples, with masses $1/4$ and
$1/2$. The stopped lower-open conditional probability is therefore

$$(1/2)/(3/4)=2/3.
$$

`condExp_lowerObservable_false_true` recovers this value at the positive-mass
sample `(false,true)`, not merely almost everywhere. The ratio is also proved
for any coupling with the same fair lower and $3/4$ upper marginal and
almost-sure order, not just for the displayed PMF.

## Original mass and the exact defect

The prior original-marginal DLR-like stage is $1/2$ on upper-open and zero on
the closed empty region. `originalStage_eq_stageValue_region` identifies it
literally with the preceding `AdaptiveMarginalObstruction` stage. It has
integral $3/8$ and differs from the actual stopped joint conditional, whose
integral is correctly $1/2$. The former $1/8$ discrepancy remains visible in
`original_stage_mass_defect`; there is also a direct proof that the original
stage is not almost surely the stopped joint conditional expectation.

Thus a genuine stopped sigma algebra alone does not justify replacing a
marginal conditional expectation by the joint one, nor does stochastic order
supply that replacement.

## The general sufficient condition

Two generic theorems make the needed hypothesis explicit. If `g` is almost
surely the conditional expectation of `f` against a stopped sigma algebra,
then `integral_stage_eq_integral_observable_of_ae_eq_condExp` gives equality of
their integrals by the tower property. If the same `g` is the actual stopped
joint conditional expectation of two candidate observables,
`integral_eq_of_common_stopped_stage` proves that their integrals coincide.

This is only a sufficient condition, not a construction. The remaining
mathematical task for a DLR uniqueness proof is to construct the appropriate
stopped couplings and identify the common free-interior FK law as this joint
conditional for both candidates, or to provide another controlled limit. The
finite diagnostic supplies neither those identifications, a cofinal exhaustion,
an arbitrary non-DLR dominant, nor a uniqueness theorem or Theorem 5.1
counterexample.

All 12 listed declarations were independently rebuilt using pinned Lean 4.35
and default heartbeats. Every axiom list is exactly `propext`,
`Classical.choice`, and `Quot.sound`.
