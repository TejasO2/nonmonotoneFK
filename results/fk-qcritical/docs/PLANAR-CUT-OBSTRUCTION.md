# The strict all-open-cut construction is not generally available

Public module: `FK.PlanarCutObstruction`. This is a deterministic graph-theoretic
obstruction to one proposed proof interface for Theorem 1.11. It neither proves nor
refutes the paper's planar uniqueness theorem or its at-most-one-cluster conclusion.

## Exact cut algebra

For any simple graph $G$, edge configuration $\omega$, and vertex set $A$,
`orientedCut_open_iff` proves

$$
(\forall e\in\delta A,\ \omega(e)=\mathrm{true})
\iff \text{no closed edge has exactly one endpoint in }A.
$$

Equivalently, if $x\in A$ then every vertex reachable from $x$ using closed edges is
still in $A$. Thus `finite_closedComponent_of_finite_openCut` proves that a finite
all-open cut through $x$ forces the entire closed-edge component of $x$ to be finite.
The condition is forbidden by a single infinite closed component whenever a criterion
must serve all vertices.

## The staircase blocks every finite shape

The already-public `PlanarTarget.staircaseConfig` closes the primal ray
$(k,0)\to(k+1,0)$ for $k\in\mathbb N$ and opens all other primal edges. It has no
infinite dual-open cluster under the exact `gridCrossEquiv` edge pairing.

The new component proves:

- `staircase_closedComponent_infinite`: that closed ray is infinite;
- `no_finite_openCut_at_origin`: **no** finite set containing $(0,0)$ has an entirely
  open oriented cut;
- `staircase_exteriorInfinite_origin`: nevertheless, the origin belongs to an infinite
  primal open cluster, using the existing genuine open-connectivity proof.

Consequently the all-open-cut construction hypothesized by
`CutSeparation.dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction` cannot be
produced from dual nonpercolation on the square lattice. The analogous negations for
cuts required only for pairs with infinite clusters and for covering the cut by an
open-connected label set are proved as well.

This is stronger than the earlier fixed-shell obstruction: it applies to every finite
$A$, not just $\ell^1$ diamonds or a prescribed norm family. Conversely, the existing
`InfiniteOpenCircuitUniqueness` theorem remains valid when its additional spherical
open-circuit hypotheses actually hold. The obstruction does not give an infinite
second cluster on the staircase or falsify `GlobalAtMostOne` there.

## Complementary square-grid example

`stripConfig` closes exactly the vertical edges $(a,0)\to(a,1)$ for $a\in\mathbb Z$.
The component proves explicitly that:

- the corresponding dual horizontal row is open and infinite;
- the two primal rows $y=0$ and $y=1$ each contain infinite open clusters;
- no open primal walk crosses the strip, so the configuration is not
  `GlobalAtMostOne`.

Hence dual nonpercolation cannot simply be dropped from the abstract planar target.
This is an explicit deterministic example, not a statement about a random FK law.

## What the reformulations do and do not do

The module also records an open-incident check and an algebraic disconnectedness
characterization. The main conclusion is already supplied by the public module
`FK.WeakOpenCut`: only vertices incident to **open** edges of a finite cut need be
open-connected. Here `exists_openCut_iff_openConnected` adds its exact pairwise
converse, taking $A=\{x,y\}$ when the pair is already connected. It therefore must
not be mistaken for a derivation of the weak criterion from dual nonpercolation.

Similarly, `globalAtMostOne_of_no_separating_closedCut` uses the open component of
one vertex as a closed separating cut when a pair is not connected. Its hypothesis
retains the original connectivity obligation; it is not a finite-component filling
or Jordan construction. The actual continuous/configurable planar work described in
[the proof status](PROOF-STATUS.md) remains open.

## Verification and scope

The exact source was independently rebuilt using the pinned Lean 4.35 toolchain at
default heartbeats against the current public imports. All 38 fully qualified
principal declarations appear in `Audit.lean`; the independent audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom axiom,
`unsafe`, `native_decide`, or changed trust setting is used. Run `./check.sh` for the
full integration checks.
