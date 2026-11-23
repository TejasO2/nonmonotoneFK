# Finite Margulis–Russo component (direction C)

## Result and scope

`MargulisRussoFinite.lean` proves finite product-measure differentiation formulas for `Bool`-valued configurations and identifies them with the repository's actual finite `Measure.pi` Bernoulli law. It uses no theorem named after a whole-paper reduction and makes no critical-shift claim.

Principal declarations in `FK.MargulisRussoFinite`:

- `eventWeight_eq_coordinate` and `hasDerivAt_eventWeight_update`: exact one-coordinate affine decomposition and derivative for an **arbitrary** event. The algebraic derivative does not assume monotonicity.
- `offEventWeight_sub_eq_offPivotalWeight`, `eventWeight_pivotal`, and `hasDerivAt_eventWeight_update_pivotal`: for increasing events, the forced-open/closed derivative is the off-edge pivotal mass, equivalently the mass of the usual full-configuration `FK.AGPeeling.Pivotal` event.
- `hasDerivAt_eventWeight_const_pivotal`: the homogeneous derivative is the sum of the full pivotal-event masses.
- `hasDerivWithinAt_bernoulliProduct_update_pivotal`: the same formula for the actual inhomogeneous Bernoulli `Measure.pi` law while varying one selected coordinate within `[0,1]`. The arbitrary index type may be `E ⊕ F`, so bond and activation coordinates and their independent product structure are preserved.
- `hasDerivWithinAt_bernoulliProduct_const_pivotal`: actual homogeneous measure-valued form, including one-sided endpoint derivatives.
- `sum_offPivotalWeight_nonneg` and `sum_offPivotalWeight_le_card`: pivot-sum bounds `0 ≤ ∑' e, I_e ≤ Fintype.card E` on the unit cube.
- `eventWeight_eq_bernoulliProduct_toReal`: exact probability normalization through `FKEnhancement.toPMF_boolProduct_toMeasure`.
- `eventWeight_eq_lowerEnhancedLaw_toReal` and `eventWeight_eq_upperEnhancedLaw_toReal`: exact specializations to the actual certificate-dependent lower/upper enhanced product rate profiles.

## Hypotheses removed and hypotheses that remain

There is no interior-rate assumption `0 < p < 1`, no division by `p`, `1-p`, or a Radon–Nikodym density, no analyticity assumption, and no separate independence hypothesis: independence comes from the actual `Measure.pi` definition. Differentiating an unrestricted real polynomial avoids endpoint divisions. Finite discrete configuration spaces need no additional event-measurability input.

`IsUpperSet A` remains where the derivative is identified with nonnegative pivotal mass; it is not needed for `hasDerivAt_eventWeight_update`. Probability statements retain only the actual unit-interval bounds. `Fintype E` and `DecidableEq E` remain because these are finite formulas.

The enhanced-law normalization theorems concern fixed enhanced rate profiles. The selected-coordinate derivative can be instantiated at those profiles, but it does **not** claim a total derivative with respect to the global FK parameters when certificate probabilities themselves vary. Infinite-volume limits, AG bounded-fibre ratio estimates, essential enhancement, `hAG`, and strict critical-point shifts remain open; none is a concealed hypothesis or conclusion here.

## Reproduction

From `results/fk-qcritical/` with Lean 4.35 and the repository Elan:

```sh
export ELAN_HOME="$PWD/../../.scratch/elan"
export PATH="$PWD/../../.scratch/elan/bin:$PATH"
lake env lean ../../.ultramath/smwsl2nwy/m2/MargulisRussoFinite.lean
lake env bash -c 'cd ../../.ultramath/smwsl2nwy/m2 &&
  lean -o MargulisRussoFinite.olean MargulisRussoFinite.lean &&
  export LEAN_PATH="$PWD:$LEAN_PATH" &&
  lean MargulisRussoFiniteAudit.lean | tee MargulisRussoFiniteAudit.log'
```

`MargulisRussoFiniteAudit.lean` audits 18 declarations. The final audit reports only `propext`, `Classical.choice`, and `Quot.sound`. All generated artifacts stay in this member directory.
