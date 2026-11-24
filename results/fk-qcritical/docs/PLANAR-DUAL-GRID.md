Public modules are the six new `FK.*` files. There are 26 principal independent audits; the coordinator added explicit `gridCrossEquiv` and `finite_neighborSet` checks because their advertised signatures had no worker audit. Finite closed-set and positive-shell consequences are real. The staircase obstructs a fixed-norm circuit family, not the planar target, because its primal graph is proved open-connected.

# Planar dual nonpercolation on the square lattice — verified instances and an obstruction

Member `m5`, direction d2 (direction 7 of the campaign brief). All results below
are Lean 4.35 theorems in this directory, compiled against the pinned
`results/fk-qcritical` build (`lean-toolchain` v4.35.0, `LEAN_PATH` from
`$HOME/.fk_lean_path`). Every audited declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`, `admit`,
custom axiom, `unsafe` or `native_decide`.

## Files and build

| File | Content |
|---|---|
| `FiniteOpenEdges.lean` | general graph lemma: a finite open edge set has finite open components |
| `GridOpenCuts.lean` | diamond (ℓ¹) open cuts on `gridGraph`; `GlobalAtMostOne` from cofinally many open diamond shells; finite-closed-edge instance; separator-interface instantiation |
| `GridDualIncidence.lean` | the exact face–dual edge equivalence of the square lattice, its inverse, local finiteness |
| `PlanarTarget.lean` | dual-open = primal-closed; dual nonpercolation from a finite closed set; the non-all-open instance of the planar target; the staircase obstruction |
| `WeakOpenCut.lean` | the cut criterion tightened: only the vertices incident with the **open** part of the cut need be open-connected |
| `StaircaseConnected.lean` | the staircase configuration is a positive instance of the target's conclusion (open graph connected) even though no diamond shell is all-open |

Build (from this directory):

```
./build.sh GridOpenCuts GridDualIncidence PlanarTarget WeakOpenCut StaircaseConnected
```

`build.sh` puts this directory in front of `$HOME/.fk_lean_path` and uses the
pinned toolchain binary `$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`.

## What is proved

### 1. Diamond shells are finite open cuts

* `GridOpenCuts.diamondBall k = {p | lvl p ≤ k}` is finite
  (`finite_diamondBall`), and
  `GridOpenCuts.orientedCut_diamondBall_subset_diamondCut`:
  the oriented edge cut of the ℓ¹ ball is exactly a subset of the diamond
  crossing set, i.e. every edge leaving the ball joins ℓ¹ level `k` to `k + 1`.
* `GridOpenCuts.globalAtMostOne_of_cofinal_diamondCuts`: if for any two
  vertices there is an open diamond shell beyond both levels, then the two
  vertices are open-connected.  Proof: instantiate
  `FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts_through_labelSet`
  with `A = diamondBall k`, `C = diamondCut k`, using the crossing containment
  and `GridFrontier.diamondCut_openLabelConnected`.
* `GridOpenCuts.globalAtMostOne_of_eventually_open_diamondCuts`: the eventual
  form (there is `K` with `diamondCut k` open for all `k ≥ K`).
* `GridOpenCuts.globalAtMostOne_of_finite_closedEdges`: **if only finitely many
  edges of a square-lattice configuration are closed, then there is at most one
  infinite open cluster.**  This is a genuine non-all-open instance of the cut
  criterion; the configuration may close arbitrarily many edges inside a large
  diamond.
* `GridOpenCuts.separatorOpenCircuit_diamond_of_open` and
  `hasSeparatorCircuitExhaustion_of_open_diamondCuts`: the geometric
  `SeparatorOpenCircuit` / `HasSeparatorCircuitExhaustion` interface is
  instantiated without assuming the all-open configuration, so the interface is
  not vacuous.

### 2. Exact face–dual incidence for the square lattice

`GridDualIncidence` builds the bond dual of the square lattice as an explicit
edge-type equivalence.

* `dualLo p q`, `dualHi p q` are the two unit-square centres adjacent to the
  lattice edge through `p` and `q`; both are symmetric functions of the
  unordered pair, so they lift through `Sym2.lift` to `crossVal`/`crossEdge`
  (`GridDualIncidence.crossEdge`).
* `uncrossLo`, `uncrossHi`, `uncrossEdge` are the inverse construction
  (the lattice edge crossed by a face edge).
* `uncrossPair_dualLo_dualHi` and `crossPair_uncrossLo_uncrossHi` are the two
  round trips, proved by the four cases of `gridAdj`; they give
  **`gridCrossEquiv : gridGraph.edgeSet ≃ gridDual.edgeSet`**
  (`gridDual` is the shifted lattice, literally the same graph).
  This is exact primal/dual edge incidence: each primal edge is crossed by
  exactly one dual edge and conversely, with no arbitrary pairing and no outer
  face.
* `finite_neighborSet`: the dual graph is locally finite (every vertex has a
  finite neighbour set).

### 3. The planar target in a genuine non-all-open class

* `PlanarTarget.dual_openSet_eq_image_closed`: for the exact face–dual
  equivalence, the dual-open edges are precisely the images of the primal-closed
  edges.
* `PlanarTarget.noInfiniteOpenCluster_dual_of_finite_closedEdges`: a
  configuration with finitely many closed edges has **no infinite dual-open
  cluster** (its dual-open edge set is finite).
* `PlanarTarget.dualNonpercolation_imp_atMostOne_of_finite_closedEdges` and
  `dualNonpercolationForcesPrimalAtMostOne_of_finite_closedEdges`:
  for `ω` with finitely many closed edges,
  `FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω)` holds
  **and** `GlobalAtMostOne gridGraph ω` follows.  This is an instance of the
  recorded source-facing target `FK.Planar.DualNonpercolationForcesPrimalAtMostOne`
  on a genuine dual pair, with a non-all-open hypothesis class.

### 4. The obstruction: dual nonpercolation does not give open diamond shells

* `PlanarTarget.staircaseConfig` closes exactly the horizontal edges
  `(k,0)–(k+1,0)`, `k ∈ ℕ` (the positive `x`-axis ray).
* `PlanarTarget.staircase_dual_nonpercolation`: this configuration has **no
  infinite dual-open cluster**.  The dual-open edges are the single face edges
  `{(k,−1),(k,0)}`; distinct ones share no face
  (`dualStaircaseEdge_no_shared_face`), so the uniqueness hypothesis of
  `PlanarTarget.finite_openComponent_of_unique_incident` applies.  That lemma is
  a general criterion: if any two open edges sharing a vertex coincide, then in
  a locally finite graph every open component is finite.
* `PlanarTarget.exists_closed_mem_diamondCut`: every ℓ¹ diamond shell
  `diamondCut k` contains the closed staircase edge `staircaseEdge k`.
* Combining,
  **`PlanarTarget.exists_dualNonpercolating_noOpenDiamondCut`**:
  there is a square-lattice configuration with no infinite dual-open cluster on
  which *every* diamond shell carries a closed edge.

## Consequence: the fixed ℓ¹ level-set geometry cannot prove the general target

The last theorem is the exact obstruction the direction asked for.  Dual
nonpercolation does **not** imply the cofinal-all-open-diamond-cut hypothesis
used by `globalAtMostOne_of_cofinal_diamondCuts`.  So any proof of the full
`FK.Planar.DualNonpercolationForcesPrimalAtMostOne` on the square lattice must
produce a **configuration-dependent** separating circuit (the primal boundary of
a finite dual-open component, or a filled-in Jordan region), not a fixed level
set of a norm.  This matches the classical picture: a primal *ray* of closed
edges does not separate the plane, but it intersects every cofinal family of
fixed convex shells.

### 5. A sharpened cut criterion

`WeakOpenCut.globalAtMostOne_of_finite_openCut_on_openVertices`: a finite cut
through two vertices suffices when the vertices incident with the *open* edges
of the oriented cut are mutually open-connected.  The proof only ever traverses
an edge that an infinite open cluster actually crosses, and an open cluster can
only cross an open edge
(`WeakOpenCut.exists_open_orientedCut_vertex_of_walk`).  The published criterion
is recovered as the special case where the whole cut is open
(`WeakOpenCut.globalAtMostOne_of_finite_openCuts`), so the new statement is a
strict generalisation and is the form which survives a few closed cut edges.

### 6. The staircase configuration satisfies the target's conclusion

`StaircaseConnected.staircase_witness` collects, for the same staircase
configuration that realizes the obstruction:

* `FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv staircaseConfig)`
  (no infinite dual-open cluster);
* `GlobalAtMostOne gridGraph staircaseConfig` — at most one infinite primal-open
  cluster, proved by explicit open lattice walks: every vertex reaches the
  origin along an open row (`row_open`, `horiz_open`) and an open column
  (`col_open`, `vert_open`), see `staircase_connected`;
* the closed set is **infinite** (`staircase_infinite_closed`), so the finite
  closed set theorem does not apply here;
* a closed edge lies in every diamond shell (`exists_closed_mem_diamondCut`).

So the obstruction is a limitation of the fixed `ℓ¹` shell method, not a
counterexample to the planar target: there are configurations with an infinite
closed set and no all-open shell for which the conclusion still holds.

## What remains (precise statement of the missing input)

The general target is still open.  In the notation of this development the one
missing deterministic statement is:

> For every `ω : gridGraph.edgeSet → Bool` with
> `FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω)` and
> every two vertices `x y`, there is a finite `A ⊆ GridV` with
> `x, y ∈ A`, every edge of `CutSeparation.orientedCut gridGraph A` open, and
> all oriented-cut-incident vertices mutually open-connected.

By `FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts` (or by
its sharpened form `WeakOpenCut.globalAtMostOne_of_finite_openCut_on_openVertices`)
this would immediately give `GlobalAtMostOne gridGraph ω`; by
`dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction` it would give the
recorded target.  The obstruction shows the witness `A` cannot be a ball of a
fixed norm; by `GridOpenCuts.orientedCut_diamondBall_subset_diamondCut` the
natural remaining candidate is the *filled* region enclosed by the outer
boundary of a finite dual-open component, whose boundary cycle would have to be
proved to be a single open-connected label set — the planar Jordan/filling step
that this file does not attempt.

## Audit

`#print axioms` is issued at the end of each module for every main declaration.
A clean full build is

```
./build.sh FiniteOpenEdges GridOpenCuts GridDualIncidence PlanarTarget WeakOpenCut StaircaseConnected
```

which exits 0 with no errors and no `sorry`/`admit`/custom axiom/`unsafe`/
`native_decide` anywhere in these files; all audited declarations report exactly

```
[propext, Classical.choice, Quot.sound]
```

Only `if_pos`/`if_neg` deprecation warnings are emitted (Lean 4.35 renamed them
to `ite_eq_left`/`ite_eq_right`); they are cosmetic and the replacements behave
identically.
