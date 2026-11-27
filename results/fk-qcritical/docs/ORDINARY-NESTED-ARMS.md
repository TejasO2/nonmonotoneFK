# Ordinary nested cutsets and the finite arm bound

Public modules: `FK.NestedAdaptiveGood`, `FK.NestedMetricWindow`, and
`FK.SourceNestedWindow`.

This provides a genuine ordinary nested finite coupling and finite equation
(9)-type estimate, at `0 < q` and interior `0 < p < 1`. It does **not** yet
prove `SourceUniqueness.NestedEquationNine`, the global vanishing-arm result,
Theorem 1.9, or Theorem 1.10.

## Exact induced-region free marginal

`NestedSumGeometry` describes a nested induced small labelled graph, an outside
edge family, and the embedded small graph in their common large graph.
`map_smallReadout_fkPMF` proves that restriction of the large free-region FK
law to its embedded small internal edges is exactly the ordinary free FK law
of that small region, with no fresh-vertex substitute.

The mathematical point is the exact component-count split. The core condition
prevents every outside edge from having an endpoint in the embedded small
region. Consequently the large free connection graph splits into:

- an isomorphic copy of the small free graph; and
- a residual graph on the complement using exactly the residual internal
  edges.

This gives `componentCount_split`. Edge weights, cluster weights and partition
functions then factor explicitly. The first marginal of the resulting finite
weighted product is the desired ordinary FK law.

`outer_eq_of_fiber_frontierExhausted` proves the genuinely maximal stopped
upper frontier does not change after arbitrary hidden bits are resumed. Every
external boundary edge was already revealed at the maximal stop, so hidden
bits cannot enlarge its open closed region.

## Common maximal-cutset good identity and outside copying

`window_small_free_interiors` proves each lower stopped free-interior marginal
separately, with its exact exterior/wiring conditions. It does not assert an
unconditional joint free law on an arbitrary upper-dependent stratum.

`window_good_intersection` then proves equality of arbitrary ordinary
small-interior event masses on supported maximal closed-frontier strata.
`windowCopyTriple` copies the upper coordinate on **every outside coordinate**
while leaving small coordinates of the synchronized second component intact.
It preserves exact big FK first and upper Bernoulli third marginals, and exact
small FK restriction of the middle component. It does not claim an independent
full outside marginal which the synchronized coupling need not have.

`windowCopyTriple_good_cylinder` compares cylinder events only when all base
edges are enclosed in the maximal unexplored region. The finite bound
`windowCopyTriple_abs_sub_le_arm` then bounds the big/small cylinder mass
difference by an explicit upper-Bernoulli open arm from a base-edge endpoint
to the exploration roots.

## Ordinary metric and arbitrary induced source boxes

`nestedBoxGeometry` derives the sum-edge geometry from ordinary nested finite
boxes. `metricNestedGeometry` specializes it to centered metric boxes, with
joint roots on a radius shell. The source-boundary versions use exact
`HasSourceBoundaryClass` singleton hypotheses on all relevant interior
vertices.

`sourceNestedGeometry` generalizes to arbitrary induced source boxes with
explicit core and joint root requirements. `sourceNested_abs_sub_le_arm_of_nest`
specializes to the canonical `VertexExhaustion.nest`, with its source boundary
class hypotheses proved rather than assumed as metric-sphere conditions.

## What is still missing

The remaining bridge is geometric/measure-theoretic, not another
free-interior theorem:

1. transport the finite upper-Bernoulli product and its arm through the exact
   large-box reindexing to the actual global Bernoulli `ProbabilityMeasure`;
2. identify or bound `upperArm` by the source `boundaryConnection` /
   `farConnection` probability, truncating an open path at the small source
   boundary; and then
3. pass to nonpercolation vanishing and the literal nested estimate used in
   `SourceUniqueness`.

These finite results do not prove AG or supply arbitrary global DLR support.

## Verification

Nine fully-qualified principal audits are in `Audit.lean`. The complete
three-stage fresh build was independently rerun with pinned Lean 4.35 and
reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
`admit`, `unsafe`, `native_decide`, custom axiom or heartbeat override is used.
Run `./check.sh` from `results/fk-qcritical` for the public gate.
