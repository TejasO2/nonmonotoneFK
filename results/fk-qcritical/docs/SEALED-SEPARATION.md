# Vertex-sealed circuits and the closed-ray obstruction

Public module: `FK.SealedSeparation`. This package gives a rigorous negative
result for the older crossing-controlled geometric interface and a valid,
weaker sealed-circuit uniqueness interface with concrete positive instances.
All claims are pointwise, not statements about random configurations.

## Closed paths rule out crossing-controlled exhaustions

`SeparatorOpenCircuit.crossing` forces every edge arc meeting a candidate
barrier to be one of the circuit labels; `label_open` forces that label to be
open. Along a closed walk, every realized arc therefore avoids the barrier, so
a closed walk can never leave its inside. This is
`mem_inside_of_closedWalk`, proved directly by walk induction.

Consequently, an infinite closed path with distinct vertices cannot coexist
with a cofinal crossing-controlled circuit exhaustion: the finite inside would
contain all its vertices. The constructive proof does not assume a Jordan
curve, a metric shell, or a particular barrier shape.

For `PlanarTarget.staircaseConfig` on the square lattice this gives
`staircase_no_separatorCircuitExhaustion` and
`staircase_no_sphericalOpenCircuit`, at every centre. The existing dual graph
still has no infinite open cluster, while the original primal configuration is
open-connected and hence has at most one infinite open cluster. This is a
failure of the **geometric interface**, not of the uniqueness conclusion.

## The sealed condition

`SealedOpenCircuit R ω C S` retains open labels and `OpenLabelConnected`, but
replaces crossing control by
"an edge whose arc meets the barrier either carries a circuit label or has an
endpoint incident to such a label".

An open path from inside then either stays inside or reaches a circuit vertex.
Because it reaches that vertex anyway, closed barrier arcs no longer need to be
forbidden or replaced by intervening open paths. This is what the older
crossing-control interface could not accommodate.

`openConnected_of_two_infinite_of_sealedOpenCircuit` uses finite vertex
preimages inside and on the barrier to select outer points from both infinite
components, and joins them through those labels. Therefore
`HasSealedCircuitExhaustion` implies `GlobalAtMostOne`. Crossing-controlled
circuits are a strict special case of sealed circuits.

`dualNonpercolationForcesPrimalAtMostOne_of_sealedExhaustion` remains a
conditional adapter: it assumes the sealed-family construction for every dual-
nonpercolating configuration. That general family is **not** constructed here,
so there is no general planar Theorem 1.11 conclusion.

## Actual box construction

On the square lattice, `boxBorder k` consists of the tangential lattice edges
at $\ell^\infty$ level $k$. Its outside and inside are genuine level-set path
components of $(\mathbb R\times\mathbb R)\setminus\{|z|_\infty=k\}$. Its labels
are open-connected by explicit horizontal and vertical walks along borders,
not by an asserted combinatorial duality certificate.

For a barrier-crossing step the proof uses exact norm inequalities: either an
endpoint lies on the level set, or the whole edge stays beyond it. A level-$k$
vertex is incident to a border edge for $k\ge1$, satisfying the sealed field.
Finite vertex preimages are computed explicitly and every Euclidean ball fits
inside one of these integer boxes.

`hasSealedCircuitExhaustion_staircase` supplies this appropriate family on the
same staircase that avoids the older interface, and gives an additional proof
of `GlobalAtMostOne` in that configuration. Generalizing,
`globalAtMostOne_of_boxBorder_open` holds whenever arbitrarily large box
borders consist of open edges. A bounded closed-edge set is a special case.
The latter instance overlaps existing bounded-support results; the unbounded
ray instance and the general box-border construction are the new content.

## Remaining mathematical obligation

The general construction of sealed cofinal circuits from dual nonpercolation
is still open. Almost-sure exclusion of infinite closed primal paths is not
formalized, so this package neither rules out a probabilistic route nor shows
that it would give primal uniqueness. Continuous embeddings/generalizations to
non-grid graphs and genuine FK probabilistic conclusions are also out of scope.

## Verification

The exact source was independently rebuilt under Lean 4.35/current public
imports and all 34 audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The misspelled theorem name appearing in
one header comment has been corrected without changing any statement or proof.
Run `./check.sh` for the full release check.
