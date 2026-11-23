# Direction 1 — fibre-wired ordinary nested `hgood`: the shell obstruction

Self-contained module: `lean/MetricRegionGood.lean` (Lean 4.35.0, project imports,
default heartbeats, no `sorry`/`admit`/`axiom`/`unsafe`). All 22 audited
declarations report exactly `[propext, Classical.choice, Quot.sound]`
(`lean/audit.log`).

## Question

Can the accepted common-upper nested `hgood`
(`FK.Exploration.NestedCoupledGood.fkNestedOrderedTriple_good_rightExtended_twoSided`,
`FK/NestedCommonUpperGood.lean`) be instantiated on **ordinary nested metric boxes**
`metricBox hG o r ⊆ metricBox hG o N`, so that the new pullback/fibre-wired source
law of `FK/OrdinaryNestedGluing.lean` supplies `hgood` for the actual metric
finite-volume comparison? The downstream consumers
(`NestedBadRootArmVanishing`, `NestedMetricRegionSplit`,
`NestedBadRootAttachment`) are all conditional on exactly that identity.

## Answer (negative, with the positive counterpart)

The accepted theorem's large graph is a **right extension** of the smaller graph
by a graph on a *disjoint vertex summand* (`rightExtendedGraph sT tT GO`,
vertices `(U ⊕ K) ⊕ GO.Vertex`, and `map_splitConfig_fkPMF_disjointSum` is used
essentially). For ordinary metric boxes this presentation fails, for an exactly
identified reason.

1. `newEdge_avoids_region` — every edge of `metricBox hG o N` that is not in
   `metricBox hG o r` has both endpoints at graph distance `≥ r` (and hence, for
   `R ≤ r`, outside the open ball of radius `R`). This is the property the
   *region*-based good-intersection argument actually needs, and it is proved.
2. `endpoint_inSmallV_of_dist_eq` (shell obstruction) — but such an edge with an
   endpoint at distance **exactly `r`** has that endpoint among the *smaller
   box's own vertices*: that endpoint is `inc v` for an explicit
   `v : (metricBox hG o r).Vertex`. So the added block cannot be placed on the
   vertex complement.
3. `LineInstance.lineGraph_shell_obstruction` — the obstruction is non-vacuous:
   on the semi-infinite line (`NestedRadialCounterexample.lineGraph`), scales
   `r = 1 < N = 2`, the complementary edge `1–2` has endpoint `1`, a vertex of
   the radius-1 box. Hence the added block cannot be a graph on the fresh
   summand `New` there, so the right-extension presentation (and with it the
   accepted `hgood`) is unavailable for that pair.
4. `newEdge_fresh_of_shell` — the exact extra hypothesis under which the
   accepted presentation *is* available: if every endpoint of every
   complementary edge has distance `≥ r + 1`, then added edges are supported on
   the fresh vertex type `New = (large).Vertex \ range inc`, and `GO` is a
   genuine fresh graph. Ordinary metric boxes violate this as soon as a
   complementary edge meets the distance-`r` shell, as on the line graph above;
   the condition is a genuine restriction on the geometric scales, not a
   definitional consequence.
5. `vSmallSumNew`, `inc_injective` — the vertex bijection
   `(metricBox hG o r).Vertex ⊕ New ≃ (metricBox hG o N).Vertex` exists in
   general (noninjective-inclusion gluing).
6. `smallGraphEq` (+ `small_source_eq`, `small_target_eq`) — **positive bridge
   for the smaller box**: with the region-split exterior-first enumeration
   `jD = exteriorFirst ≫ edgeEquiv ≫ edgeIndex` of `(metricBox hG o r).edges`,
   the ordinary radius-`r` metric box *is* the vertex transport of the two-sided
   ambient `transportedAmbient si ti so xo` along the region vertex equivalence
   `vertexEquiv (inBall hG o R r)`. So every theorem stated for the accepted
   two-sided ambient (`NestedCommonUpperGood`, `NestedArbitraryInterior`,
   `StoppedInterior`) applies to the actual smaller metric box with the
   pulled-back boundary; only the *larger* side fails.

## Coordinator scope clarification

`newEdge_fresh_of_shell` proves only that both endpoints of a complementary edge avoid the smaller vertex type. It does not by itself instantiate `fkNestedOrderedTriple_good_rightExtended_twoSided`, identify the no-cross source with the ordinary fibre-wired pullback source, or establish common-upper `hgood`. In addition to this geometry mismatch, `hgood` would need an identity for the appropriate new boundary source law. The generalized free-region continuation identified below remains **unproved**.

## Exact residual

`hgood` for ordinary metric boxes cannot be obtained by instantiating the
accepted two-sided theorem. What is missing is one generalized
interior-continuation lemma: after the exterior prefix (the smaller box's
exterior bits, in the closed maximal stratum) and given the common upper
configuration, the **region** marginal of the larger box's filtered FK law is the
free region law, even though the added edges are incident to the *right* (shell)
part. Item 1 supplies the geometric hypothesis that makes this true (the region
is separated from everything by closed edges, since added edges avoid it); items
2–3 show that no vertex-summand presentation can replace it. This is a
generalization of `FK.Exploration.NestedCoupledGood.pair_interior_continuation_rightExtended_twoSided`
in which `GO`'s edges are allowed to meet `K` but not `U`.

## Integration

The file is written as module `FK.MetricRegionGood` (namespace
`FK.MetricRegionGood`, subnamespace `FK.MetricRegionGood.LineInstance`) and only
imports `FK.NestedCommonUpperGood`, `FK.NestedMetricRegionSplit`,
`FK.OrdinaryNestedGluing`, `FK.NestedRadialCounterexample`. To integrate, copy
`lean/MetricRegionGood.lean` to `results/fk-qcritical/FK/MetricRegionGood.lean`
and `lake build FK`. It was checked under exactly that module name with
`lean -R try -o build/FK/MetricRegionGood.olean try/FK/MetricRegionGood.lean`
(exit 0).

## Reproduction

```sh
TC=/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0
R=<repo>/results/fk-qcritical
LEAN_PATH=$R/.lake/build/lib/lean:$TC/lib/lean:<each $R/.lake/packages/*/.lake/build/lib/lean>
$TC/bin/lean lean/MetricRegionGood.lean
```
The VM's default `lean` on `PATH` is 4.33.1 and cannot read the project's 4.35
olean files; the pinned 4.35 toolchain above must be used with the project's own
Mathlib build tree.
