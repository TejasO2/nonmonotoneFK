# Clopen and dominated escape bounds

Public modules: `FK.ClopenEscape` and `FK.ClusterEscape`, in the
`FK.InfiniteVolume` subnamespaces of the same names. These supply generic
no-mass-escape and percolation infrastructure for the one-edge route to box
DLR, not the whole weak-limit branch of Proposition 1.8(2).

## Two far-vanishing mechanisms

`ClopenEscape.farVanishing_of_clopen_escape` transfers a decreasing clopen
escape family with null intersection along weak convergence. The key estimate
bounds every sufficiently late stage mass of the unexplained connection by a
fixed clopen escape mass, which then converges to the limiting law's mass.
`noEscape_of_clopen_escape` turns this into the upper limsup bound consumed by
`OneEdgeNoEscape`. The estimates do not need monotone stage rates; the existing
one-point wrapper does require increasing stage connection events to identify
its limiting two-valued rate.

The other route, `farVanishing_of_dominated_escape` and
`noEscape_of_dominated_escape`, assumes only that the escape events are
measurable, increasing in the configuration and dominated by a fixed law. The
dominating law's vanishing escape tails then bound every stage directly.
`tendsto_measure_toReal_escape_of_measurable` dispenses with clopenness for the
fixed dominating law. `isDLR_of_dominated_escape_of_null_escape` packages the
result with a nonpercolating dominating law, and the clopen route has a
whole-exhaustion `mem_dlrMeasures_of_clopen_escape` wrapper.

## Actual cluster geometry

`ClusterEscape` proves:

* a cluster is infinite exactly when it meets the outside of every set in an
  increasing cofinal finite exhaustion;
* if both clusters escape and the finite connection event fails, the
  intersection over scales has no configuration with at most one infinite
  cluster, hence has measure zero under that hypothesis;
* a wired walk with all external relations supported outside a finite set
  either gives an ordinary open connection inside the set or forces both
  clusters to meet its complement; and
* escaping-cluster events are measurable, increasing, and have vanishing mass
  along the exhaustion under nonpercolation at the root.

These lemmas do not need local finiteness. The exterior-relation walk lemma is
for direct wiring, not yet for the source's exterior open-walk connectivity
partition with realized merge paths.

## Remaining inputs

The following are not proved by this package:

1. `hfin`, the finite-stage FK one-point identity at the actual smaller box
   (including coherent nested-box transport);
2. `hsdiff`, the genuine source connectivity-partition escape inclusion,
   including arbitrary interior boundary constraints and realization of
   exterior walks;
3. the rate identification and, where source conventions vary, an alternative
   to the increasing-connection-event wrapper; and
4. in the general weak-limit regime, an actual clopen escape family. The
   dominated variant addresses the separately assumed nonpercolating-
   domination regime, not arbitrary at-most-one-cluster alone.

There is consequently no source-faithful Proposition 1.8(2), Theorem 1.10 or
other main-paper theorem asserted. The exact sources were independently rebuilt
with default heartbeats under Lean 4.35.0, and all 21 selected principal audits
contain only `propext`, `Classical.choice` and `Quot.sound`.
