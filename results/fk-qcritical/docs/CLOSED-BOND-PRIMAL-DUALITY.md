# Closed-bond graph and finite primal left-reachable duality

Public module: `FK.PrimalClosedDuality` (namespace
`FK.PlaneTopology.PrimalClosedDuality`). This supplies the primal half of the
finite square-lattice duality that `FK.CutCrossingDuality` explicitly leaves
open, on the very same `DVert`/`DAdj` data.

## Model and hypotheses

`ω : gridGraph.edgeSet → Bool` is an open-bond configuration of the square
lattice, on the genuine `gridGraph` edge type that `gridCrossEquiv` pairs with
the face-dual edges. The box is the vertex rectangle `[0,k+1] × [0,n]`;
`primalGraph ω k n` is its open subgraph and `leftReach ω k n` is the set `A` of
vertices reachable from the left wall by **open primal paths inside the box**.

No probability, FK law, `q`, planarity or Jordan input is used. The only
hypotheses are `0 < n` and, per theorem, either

* `∀ v ∈ rightWall k n, v ∉ leftReach ω k n` — the right wall is outside `A`
  (nothing is assumed about the left wall: every left-wall vertex is in `A` by
  the empty open path), or
* `¬ (closedGraph ω k n).Reachable (inr 0) (inr 1)` — no closed-bond path from
  below the box to above it.

## Proved

**Cut sides are closed bonds.** `hCut_boxMem_closed` and `vCut_boxMem_closed`:
a side of a cell on which the membership function of `A` changes is a closed
primal bond, in the exact `hCut`/`vCut` coordinates of the released module.
Equivalently: an open bond can never have exactly one endpoint in `A`.

**The closed-bond graph.** `closedGraph ω k n` has the same vertices as the
released `cutGraph`, with cells adjacent across a **closed** shared bond and the
below/above vertices adjacent across a closed bond of the bottom/top row. It is
a simple graph (`DClosed_symm`, `DClosed_irrefl`), and

```
DAdj_le_closed : DAdj (boxMem ω k n) k n x y → (closedGraph ω k n).Adj x y
```

is the closed-bond inclusion of the release notes, for exactly the `A` the
duality needs. `boxMem` is `A`'s characteristic function with the left column
extended to all of `ℤ` (inside) and the right column extended to all of `ℤ`
(outside), which is what the released whole-column hypotheses ask for;
`boxMem_left_col` proves the left extension unconditionally.

**Crossing and duality.**

* `closed_crossing_of_walls` — the exact wall premise gives a closed-bond path
  below → above, through the released `reachable_of_cut_le`.
* `exists_open_crossing_of_no_closed_dual` and
  `exists_primal_open_walk_of_no_closed_dual` — **if the closed-bond graph has no
  below-to-above path, the primal configuration carries an open walk from the
  left wall to the right wall inside the box.**
* `exists_open_crossing_of_no_closed_crossing_any` — the box-uniform form: if no
  box at all admits a closed below-to-above crossing, every box admits an open
  primal left-to-right walk.

**Genuine plane incidence.** Cells are labelled by the dual lattice points
`cellPt c = (c.1, c.2)`, and the exterior vertices of `DVert` by the rows
`belowPt c = (c.1, -1)` and `abovePt c = (c.1, n)`. `crossEdge_vert_bond` and
`crossEdge_horiz_bond` compute the crossed dual edge of a bond; then

* `gridAdj_cellPt` — a closed cell-to-cell step is a genuine unit step of the
  dual lattice;
* `closed_edge_crossed`, `closed_bottom_crossed`, `closed_top_crossed` — every
  closed step **is** the `gridCrossEquiv` image of a closed primal bond, joining
  the cell centre to another cell centre or to the exterior-row point of its own
  column;
* `closed_edge_dualOpen`, `closed_bottom_dualOpen`, `closed_top_dualOpen` — the
  same edges are open in the dual configuration `dualConfig gridCrossEquiv ω`
  (`dualOpen_iff_closed`, `bondClosed_iff_dualOpen`);
* `row_reachable`, `row_vertices_reachable`, `belowRow_infinite`,
  `aboveRow_infinite`, `belowRow_inter_neighbors_finite`,
  `aboveRow_inter_neighbors_finite`, `belowPt_eq_iff` — the exterior rows are
  infinite, connected, locally finite dual regions, and the two outer vertices of
  `DVert` are quotients of them, not pretended dual vertices.

**Monotonicity and consistency.** `leftReach_mono` and `closedGraph_anti`: more
open bonds enlarge `A` and remove closed dual edges. The all-open configuration
(`closedGraph_allOpen_no_adj`, `allOpen_no_closed_crossing`,
`allOpen_right_reachable`, `allOpen_duality_instance`) and the all-closed
configuration (`noAdj_allClosed`, `allClosed_right_not_reachable`,
`allClosed_closed_crossing`) are checked instances: in the first, the duality
hypothesis holds and its conclusion is verified both through the theorem and
independently along the open bottom row; in the second, the closed-crossing
theorem's hypothesis holds and its conclusion is produced in the graph with the
most closed edges.

## What still is not proved

The **converse** direction is supplied by the completed
[finite box crossing duality](FINITE-BOX-DUALITY.md): closed paths become
chains for the [sealed parity barrier](BOX-SEAM-SEPARATION.md), and primal
walks map into its box graph. Together they prove the full finite equivalence
and the exclusive dichotomy for $n>0$ on this same collapsed-dual model.
Nothing here gives `GlobalAtMostOne`,
Theorem 1.11, dual nonpercolation ⇒ primal percolation, an infinite-volume
compactness step, or any FK measure-theoretic statement. The outer vertices of
`DVert` remain collapsed: the row facts above say exactly what an un-collapsing
would need, but the un-collapsed dual graph is not constructed.

## Verification

The module was rebuilt under Lean 4.35 against the current public imports at
default heartbeats. Its 44 fully qualified principal declarations are printed by
`#print axioms` at the end of the file and depend only on `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, `admit`, custom axiom, `unsafe`,
`native_decide`, or heartbeat/trust override is present.
