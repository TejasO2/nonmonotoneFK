# Canonical metric geometry for nested FK comparisons

`NestedMetricGeometry.lean` is the complete source. It imports the public
`FK.NestedFiniteAssembly`, `FK.ConventionTransport`, and `FK.MaximalStrata`
interfaces. On integration, place it at `FK/NestedMetricGeometry.lean`.

## Proved contents

- `metricBox` and `metricBoxExhaustion` construct actual finite labelled boxes
  and an edge exhaustion on any connected locally finite simple graph.
  `metricBoxData` proves exact global endpoints and global-vertex injectivity.
- `outsideGraph`, `nestedEdgeEquiv`, and `nestedEdgeEquiv_inl` construct the
  literal edge difference `EΔ ⊕ EO ≃ EΣ`, with exact agreement on every common
  global edge label.
- `closedLocalEvent` gives a finite-support event an exact closed-exterior
  local realization. The far-connection version is proved by truncating an
  open walk at its first radius-`r` vertex
  (`farConnection_dependsOnCoordinates_metricBox`).
- `dataWidth` covers both a fixed cylinder base and its finite root set.
  Canonical scales are `r = m + dataWidth` and arbitrary `n ≥ r`; all base
  containment and nesting facts are proved.
- `metricNestedTriple` is the actual FK/FK/Bernoulli triple at these scales.
  `finiteBox_cylinder_abs_sub_le_farConnection_canonical_of_good` and
  `metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le` instantiate the
  integrated finite estimate, internally proving `he` and `hU`.
- `probabilityMeasure_eq_of_nested_finiteRootArm_bounds_reindexed` adds the
  necessary base-dependent reindexing `d I`. Its proof composes genuine
  cylinder convergence with `Tendsto (d I) atTop atTop`.
- `eq_of_isFKLimit_metricBox_of_nested_good` uses `d J m = m + dataWidth`,
  proves that map tends to infinity, converts far connections to finite-root
  arms, and concludes equality of two actual FK limits on the same centered
  metric exhaustion, with arbitrary boundary sequences.
- `OpenPathGeometry` transports actual free-boundary reachability along
  labelled open paths. Failure of `maximalSplitStratum` yields a right-to-left
  open path using `mem_outerRegion_iff` directly.
- `nestedOpenPathMap` constructs the global path map for the canonical nested
  equivalence. `bad_maximalSplit_subset_closedLocalEvent` then **proves hD**
  for a split presentation with an exact endpoint map, left vertices in the
  finite roots, and right vertices beyond the requested radius.
- `metricBox_cylinder_abs_sub_le_farConnection_of_maximalSplit_good_of_le`
  specializes to the actual pulled-back maximal split stratum and discharges
  `hD` from that certificate. Only `hgood` remains as the finite stochastic
  premise in this wrapper.

## Exact residuals and scope

The final weak-limit equality theorem keeps `hgood`, the exceptional inclusion
`hD`, and a zero-percolation premise for the upper Bernoulli rate explicit.
The maximal-stratum finite wrapper removes `hD`, but requires the displayed
finite split/edge equivalence, exact endpoint map, and root/radius coverage.
`NestedMetricRegionSplit` subsequently constructs a genuine radial split with
whole-ball roots at the same radius. The fixed-small-root/growing-radius
refinement, and proving `hgood` in the common-upper coupling, are not claimed.
Nor is a full Theorem 1.9, arbitrary two-exhaustion theorem, or joined
maximal-stratum/weak-limit conclusion claimed beyond the stated hypotheses.

## Verification

Run `bash check.sh` from this member directory. It performs a one-file Lean
4.35 check with `warningAsError=true`, refreshes `audit-output.txt`, and scans
for forbidden declarations/placeholders and heartbeat overrides. The run used
for this report passed. All 14 printed principal audits contain exactly
`propext`, `Classical.choice`, and `Quot.sound`; there are no other axioms.
The repository-wide `check.sh` was not run, and no shared result file was
modified.
