# Bounded-coordinate infinite-graph bridge

## Deliverable

`AGBoundedCoordinateBridge.lean` imports only the accepted public modules
`FK.AGMultiDeviceIndependence` and `FK.AGSleeveInfinite` (and their accepted
transitive dependencies). It contains no `sorry`, `admit`, `unsafe`, custom
axiom, or heartbeat override.

The main declarations are:

- `FK.AGImplant.Sleeve.BoundedCoordinate.infiniteProductLaw_deviceArmEvent_independentLine_le`
- `FK.AGImplant.Sleeve.BoundedCoordinate.infiniteProductLaw_independentPercolation_independentLine_le`

Let `H` be a simple graph, let `S i` be finite selected bond sets for a finite
index type `ι`, and suppose all `S i` have the same positive cardinality `R`.
The constructions use the actual sleeved simple graph `Sleeve.graph H`, with a
separate activation coordinate for every `i`. Base parameters decrease from
`p` to `p-c*t` only on the union of the selected base annuli; every activation
increases from `s` to `s+t`; all other bonds remain at `p`. The speed is the
existing exact constant
`c = independentComparisonSpeed a b R = min a (1-b)^R / (2^R * R)` (with the
power applying to `min a (1-b)`), under the stated interior-box hypotheses.
The conclusion compares the corresponding probabilities under the actual
`Measure.infinitePi` laws, first for every finite arm and then for enhanced
percolation.

For the arm theorem, `H` is connected and locally finite; countable `V` is
added for the continuity-from-above percolation theorem. The sleeved graph's
connectedness and local finiteness come from the existing geometric proofs.
There is no finiteness assumption on the base graph's vertices or edges.

## What is actually new

The accepted indexed finite-volume differential theorem uses a disjoint-annulus
rewriting to replace a union sum by an indexed double sum. This file proves the
infinite-graph comparison **without disjointness**.

The key general lemma is `sum_biUnion_le_of_nonneg`: for nonnegative weights,
a sum over a finite union is at most the indexed double sum. In the differential
proof, the desired activation-pivot lower bound controls the indexed double
sum. The larger double sum can therefore replace the union sum without any
overlap factor. The lemma `traceFinset_baseSupport_eq_biUnion` identifies the
trace of the union with the union of traces exactly, including repeated annuli.
This is not an assumed bounded-overlap estimate.

The proof also supplies:

1. an explicit finite coordinate trace for each arm on an arbitrary infinite
   locally finite base graph;
2. exact per-device annular-pivot to independent-activation-pivot transport on
   that trace, with constants `min(a,1-b)^R` and `2^R*R`;
3. the normalized nonnegative derivative and monotone endpoint curve;
4. exact identification with the normalized infinite-product finite marginals;
5. measurability of the indexed device map and continuity from above for the
   actual percolation events.

No derivative is passed through the infinite-volume limit. The arm
inequalities are proved first at every radius, and only their measures are
passed to the intersection by continuity from above.

## Residual scope (not proved)

- The activation index is finite and all devices have the same positive
  annulus cardinality `R`; the endpoint rates must satisfy the explicit box
  hypotheses.
- There is no infinite-index comparison, reference zero/one percolation law,
  essential-enhancement theorem for arbitrary infinite device packings, or
  strict critical-point shift.
- No derivative/limit interchange is hidden in these residuals. Extending to
  infinite `ι` requires a separate limiting argument and is not asserted here.
- Uniform bounded degree is not needed for this finite-index theorem. Local
  finiteness supplies finite arm traces, and finite index supplies the other
  finiteness needed for the derivative sums.

## Separate source comparison

The primary HTML `.scratch/source-review/paper-v1.html` was inspected
separately from `docs/PROOF-STATUS.md`, especially Section 1.2 around the
paragraph citing Aizenman--Grimmett essential enhancements (HTML lines about
435--437) and the statement of Theorem 1.4. That source step invokes an
infinite-volume essential-enhancement/reference theory to retain subcriticality
or supercriticality after a small parameter change. The present theorem proves
only its exact finite-index infinite-product comparison bridge on the explicit
sleeved construction. It does not establish that external reference theory,
the positive-density infinite packing conclusion, or Theorem 1.4. Thus it is a
scoped result, not a renaming of `hAG` and not a completed numbered theorem.

## Verification

From this member directory, run `./verify.sh`. It invokes the installed Lean
4.35.0 binary with the project's existing Lake paths and writes no shared file.
The final run succeeded with default heartbeats. `build.log` records these seven
audited declarations, each with exactly `[propext, Classical.choice, Quot.sound]`:

- `sum_biUnion_le_of_nonneg`
- `trace_sum_pivot_event_mul_le`
- `tracePivotSlope_nonneg_of_box`
- `monotoneOn_traceEventWeight_independentLine`
- `infiniteProductLaw_deviceArmEvent_independentLine_le`
- `tendsto_infiniteProductLaw_deviceArmEvent_independent`
- `infiniteProductLaw_independentPercolation_independentLine_le`

The run began at public base `bc165faf5edd9ce57bd655f2ce23884c977b17b0`.
The shared checkout subsequently advanced to `4c273b9d253c8f7bde0aa14be5f2c34730d14fae`;
the final check used that checkout's public imports. The four directly relevant
AG source modules are byte-identical at those two commits. No shared source,
build configuration, or toolchain file was edited.
