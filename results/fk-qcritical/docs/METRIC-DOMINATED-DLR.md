# Prime-dominated metric weak-limit DLR closure

Public modules: `FK.GraphConnectionTransport`, `FK.NestedStageConnection`,
`FK.StageEscapeGeometry`, `FK.StageEventGeometry`, `FK.StageContainment`,
`FK.DominatedOuterAssembly`, `FK.MetricGrowingFamily`,
`FK.MetricStageGeometry`, `FK.MetricGeometryExtensions`,
`FK.PrimeStageDomination`, `FK.DominatedLimitNonpercolation`, and
`FK.PrimeMetricAutoGlobal`, all principally in namespace `FK.NestedFinDLR`.

This package proves a genuine **restricted metric-exhaustion DLR theorem** from
actual nested finite FK specifications and actual Bernoulli products. It is not
a general Proposition 1.8(2), an all-finite-box coherent-Gibbs theorem, or a
proof of any numbered main theorem.

## Strongest finite-stage-free corollary

Let `G` be a countable connected locally finite simple graph and choose a
center `o`. Fix `0 < q < 1` and `0 < p < 1`, and suppose:

1. `μ` is an actual `IsFKLimit` along the canonical `metricBoxExhaustion hG o`
   for the finite-stage **free** schedule `graph.freeBoundary`;
2. for every vertex `x`, the homogeneous prime parameter satisfies
   `primeUnitInterval hq hp1 < criticalProb G x` strictly; and
3. `Ψ` is a `BoundaryAssignment` on these metric boxes satisfying the actual
   merge/separation predicate `IsGeometric`.

Then
`mem_dlrMeasures_of_subcritical_prime_metric_freeStage_autoGlobal` proves

```lean
μ ∈ DLRMeasures (NestedMetricGeometry.metricBoxExhaustion hG o) Ψ hq hp1.le
```

There is no separate exterior-support or global at-most-one-cluster hypothesis
in this corollary. Free finite-stage setoids satisfy exterior support vacuously.
The same prime-majorant assumption that controls the finite-path escape errors
also yields almost-sure nonpercolation and hence `GlobalAtMostOne` for `μ`.
The theorem still assumes the weak limit `hμ`; it does not prove its existence.

The more general externally supported theorem
`mem_dlrMeasures_of_subcritical_prime_metric_outerStage_autoGlobal` permits an
arbitrary setoid schedule subject to `ExternallySupportedOn`, with the other
hypotheses unchanged. The abstract-majorant version
`mem_dlrMeasures_of_dominated_metric_outerStage_of_nonpercolating_majorant`
uses a law `ν` dominating every finite stage and having zero infinite-cluster
mass at every root. The original variants in `PrimeStageDomination` retain an
explicit `hglobal` argument; the strengthened wrappers derive it.

## What edge-complement support means

`ExternallySupportedOn data a` requires that every nonreflexive related pair
has an incident graph edge outside `B.edges` at each endpoint. This is not
unconditionally the same as having a neighbour outside `B.Vertex`. In
particular, `metricBox` can omit an edge joining two vertices that are both in
the box. Thus the predicate describes the exact condition used by the escape
argument, rather than silently identifying every schedule with a paper-style
outer-vertex-boundary schedule.

`externallySupportedOn_free` proves the condition for genuine finite-stage free
boundaries. `not_externallySupportedOn_wiredBoundary` gives the complementary
obstruction: a fully wired boundary fails when a pair of distinct box vertices
has an endpoint with no exterior incident edge. Consequently the support
hypothesis cannot simply be removed for arbitrary schedules.

## Principal proof components

1. **Nested finite specification.** `isDLR_finiteVolumeLaw_nested` and the
   growing-family one-point identity give the exact one-edge two-valued rates
   at every large stage. The small boundary is the actual induced boundary,
   not a free or wired replacement.
2. **Event geometry.** `stage_specificationConnectionEvent_iff_outer` identifies
   the induced specification event with outer-box reachability after closing
   the selected edge. Global wired and canonical free-component transports
   distinguish `closeOutside`, bottom wiring, and exterior components carefully.
3. **Escape estimates.** Finite lower events are clopen and exhaust the free
   off-edge connection event. An outer connection unexplained by an inner path
   forces a cluster to leave a fixed finite set when nonreflexive boundary
   pairs avoid that set. A uniform nonpercolating majorant bounds these errors.
4. **Finite prime domination.** Empty enhancement in the canonical upper-path
   comparison gives arbitrary-boundary finite FK domination by the homogeneous
   Bernoulli product at `prime(q,p)` for `q < 1`. A closed-exterior truncation
   lifts the local upper-event inequality to all measurable upper events on the
   globally extended finite-volume law, including the empty-edge case.
5. **DLR closure.** The dominated moving-rate limit supplies the exact free DLR
   identity at each metric box. Global at-most-one-cluster uniqueness transports
   this to every supplied geometric assignment on the same exhaustion.
6. **Derived uniqueness.** `rootwise_nonpercolating_of_dominated_fkLimit` passes
   rootwise nonpercolation from a uniform majorant to the weak limit.
   `ae_globalAtMostOne_of_rootwise_nonpercolating` takes a countable
   intersection of full-measure root events, yielding global uniqueness (and
   in fact almost-sure nonpercolation) without an extra hypothesis.

## Remaining source-level gaps

The conclusion checks DLR equations only at boxes of the canonical metric
exhaustion. `IsGeometric` supplies the two exterior-component properties, but
`Ψ` is still a `BoundaryAssignment`, not a constructed all-box coherent
`BoundaryConvention`. No nesting compatibility at arbitrary finite boxes is
generated by this theorem.

General Proposition 1.8(2) would also need arbitrary parameters, arbitrary
exhaustions and source weak-limit boundary schedules, an all-finite-region
convention target, and the source's existing-Gibbs input branch. Those are not
proved here. This restricted package does not itself assemble classical strong
uniqueness. The later arbitrary abstract nested equation-(9) and all-parameter
source packages instead give [the completed classical source-scope theorem](CLASSICAL-SUBCRITICAL.md),
without solving the independent enhanced/general dominant obligations. No general
AG shift, planar conclusion, or Theorem 1.4/1.10/1.11/5.1 claim follows from
metric DLR membership alone.
