# Direction D: finite AG comparison-curve integration

## Result

`AGCurveIntegration.lean` integrates the established finite one-edge OR
comparison along an explicit oriented straight line.  Put

```
c(a,b) = min(a, 1-b) / 2
p(t) = p - c(a,b) * t
s(t) = s + t.
```

For a finite increasing event `B`, the main endpoint inequality is

```
τ(p,s) ≤ τ(p-c(a,b)T, s+T),   0 ≤ T.
```

Here `τ` is the polynomial probability of `enhancedEvent B`, and the normalized
corollary replaces it by `OpenPath.FinProb.event` under the actual `jointLaw`.
The finite-arm corollary further specializes `B` to the actual graph arm event.

The orientation matters: this is a nontrivial trade-off between *decreasing*
the bond rate and increasing the activation rate.  It is not the immediate
coordinatewise monotonicity obtained by increasing both rates.

## Proof structure

- `diagonalRates` and `diagonalSlope` define the line and its coordinate
  derivatives.
- `hasDerivAt_configurationWeight_diagonal` differentiates the finite product
  directly.  Thus no joint-differentiability or ODE-existence hypothesis is
  introduced.
- `hasDerivAt_eventWeight_diagonal_pivotal` identifies the derivative as
  `(-c) Dp + Ds`, where `Dp` and `Ds` are the bond and activation pivot weights.
- `interiorComparisonSpeed_le_orMinorant` proves
  `c(a,b) ≤ orMinorant(p,s)/2` throughout `[a,b]^2`.
  `diagonal_parameters_mem_Icc` proves that endpoint membership in this box
  implies membership at every intermediate parameter.
- `enhanced_pivotSlope_nonneg_of_box` applies
  `enhancedEvent_differential_comparison`, nonnegativity of the normalized
  bond-pivot count, and explicit `eventWeight_eq_uniformJointLaw_event`
  identities to prove `(-c)Dp + Ds ≥ 0`.
- `monotoneOn_enhancedEventWeight_diagonal` applies the real mean-value
  monotonicity theorem on `Icc 0 T`.
- `enhancedEvent_jointLaw_diagonal_le` explicitly normalizes both endpoints;
  `enhancedArm_jointLaw_diagonal_le` is the actual finite-arm statement.

## Precise residual hypotheses

The integrated result assumes:

- finitely many edge/activation coordinates and an increasing base event;
- `0 < a` and `b < 1` (the endpoint hypotheses imply `a ≤ b`);
- `0 ≤ T`;
- `(p,s)` and `(p-c(a,b)T,s+T)` both belong to `[a,b]^2`;
- for the normalized theorems, explicit unit-cube proofs at both endpoints
  (also supplied as arguments);
- for the arm corollary, `Fintype G.edgeSet` and `DecidableEq G.edgeSet`.

`interiorComparisonSpeed_pos` proves `c(a,b) > 0`, but this does **not** imply a
strict probability gap: the relevant pivot counts can vanish.  This module
claims no infinite-volume limit, no interchange of limits, no arbitrary
bounded-range enhancement implantation, and no unrestricted critical-point
shift.  It remains specifically about the exact one-edge OR enhancement.

## Verification

Lean 4.35.0, default heartbeats, with no shared-results edits.  From
`results/fk-qcritical/`:

```sh
export ELAN_HOME="$PWD/../../.scratch/elan"
export PATH="$ELAN_HOME/bin:$PATH"
lake env bash -c 'set -euo pipefail; cd ../../.ultramath/smwsrcx3i/m1;
  lean -o AGCurveIntegration.olean AGCurveIntegration.lean;
  export LEAN_PATH="$PWD:$LEAN_PATH";
  lean AGCurveIntegrationAudit.lean | tee AGCurveIntegrationAudit.txt'
```

The source build and import-based audit passed.  All 19 declarations in the
audit report exactly `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
`admit`, `unsafe`, or new `axiom` is used.
