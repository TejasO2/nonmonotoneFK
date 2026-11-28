# Multi-centre arm/pruning obstruction

The counterexamples in `FK.MultiCentreForestObstruction` and
`FK.InfiniteTriangleWithRays` show that the current `ThreeWayArms` predicate
alone cannot supply the simultaneous forest used by
`markedCount_le_of_encounterForest`. They do not refute Burton–Keane
uniqueness or an argument using stronger exterior-separated trifurcations.

## Finite triangle with pendants

The six-vertex lollipop graph has a triangle at centres 0, 1 and 2 and one
pendant vertex at each centre. In the all-open configuration, the three
incident edges at every centre are proved to be genuine open three-way arms at
scale one. Their endpoints are distinct, the walks are paths, and pairwise
intersections are only the centre.

Ambient degree three at each centre creates the obstruction: any spanning
subgraph retaining degree at least three at all three centres has every
ambient neighbour at each centre. In particular, all three triangle edges
survive, so `not_isAcyclic_of_degree_three` constructs a three-cycle. This is
stronger than failure of one pruning algorithm; no such forest exists in the
ambient graph. `arms_and_no_encounter_forest` packages the arm and no-forest
statements.

## All-scale triangle with rays

The infinite version replaces each pendant by an infinite simple ray. Every
centre has one arm on its own ray and two arms through the other cores onto
their rays. The arms at one centre are pairwise disjoint away from that centre,
but paths at different centres can share the triangle, so global disjointness
is not hidden in the proof.

Exact support formulas, pathness and pairwise separation are proved. The ray
level is Lipschitz along graph edges, so distance from a centre to ray index
$n$ is at least $n+1$, which certifies arms at every scale rather than one
finite radius. `allScalesAtAllCentres` supplies the actual `ThreeWayArms`
predicate at all three cores and every natural-number scale.

Local finiteness is constructed explicitly. Any locally finite spanning
subgraph whose three centre degrees are at least three again retains the whole
triangle, so it remains cyclic.

## Consequence and remaining problem

A general multi-centre construction needs extra exterior separation,
correlated choices that avoid such cycles, or a different counting argument.
Simply unioning the arms and deleting cycles can destroy a required third arm.
The examples challenge the proposed pruning inference, not the forest counting
theorem itself and not the Burton–Keane claim. No three-infinite-cluster,
Følner, root-transitive, cluster-constancy or global uniqueness hypothesis is
manufactured from them.

All 17 principal declarations across both sources were independently rebuilt
with Lean 4.35/default heartbeats and use only `propext`,
`Classical.choice`, and `Quot.sound`.
