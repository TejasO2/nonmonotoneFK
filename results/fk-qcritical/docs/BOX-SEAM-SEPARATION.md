# Sealed barriers and finite box seam separation

Public module: `FK.BoxSeamSeparation` (namespace
`FK.PlaneTopology.BoxSeam`). This supplies a finite planar obstruction to
left-to-right open paths, by an explicit parity potential rather than a Jordan
curve theorem.

## Model and hypotheses

The box has vertices `Fin (k+2) × Fin (n+1)` and cells
`Fin (k+1) × Fin n`. A `Seam` assigns an element of `ZMod 2` to every horizontal
bond `(i,j)–(i+1,j)` (`mh i j`) and vertical bond `(i,j)–(i,j+1)` (`mv i j`).
The values record parity, not real-valued weights.

A seam is a **sealed barrier** when its values vanish on both vertical walls,
it has even parity around every box cell, and its total parity along the bottom
row is odd. No probability, FK law, infinite graph or dual-percolation premise
is used.

## Parity separation

For the potential

$$\Phi(x,y)=\sum_{i<x}mh(i,0)+\sum_{j<y}mv(x,j),$$

`Seam.Phi_vert` and `Seam.Phi_horiz` show that its coboundary is the seam.
The horizontal identity is where even parity around cells is used. Consequently
`Phi_const_of_adj` says that a zero-seam primal step preserves $\Phi$.

The wall and bottom-row conditions force $\Phi=0$ on the left wall and $\Phi=1$
on the right wall. `no_path` therefore proves that no walk in
`boxGraph S`—the box graph with the seam bonds deleted—joins the two walls.

`cutSeam` turns the cut bonds of a labelling into a seam. `cutSeam_evenAround`,
`cutSeam_wallLeft`, `cutSeam_wallRight` and `cutSeam_oddBottom` verify its
barrier conditions, and `cutBonds_separate` gives the resulting separation.
This is a separation theorem, not by itself a second proof of the existence
of a cut-graph crossing.

## Closed cell-chain barriers

A `CellChain` is an injective sequence of cells, consecutive cells share a side,
its first cell is on the bottom row and its last cell is on the top row.
`chainSeam` consists of the bonds crossed by its steps together with the bottom
bond of its first cell and the top bond of its last cell.

`chainSeam_evenAround`, `chainSeam_wallLeft`, `chainSeam_wallRight` and
`chainSeam_oddBottom` prove that it is sealed. The endpoint counts are the
parity versions of the usual two visits per cell and one bottom-row entry.
`closed_chain_blocks` then takes arbitrary `openH openV : ℕ → ℕ → Bool`; if
every open bond has zero `chainSeam` parity, no open primal walk can join the
left and right walls.

`single_row_closed_barrier` is a concrete instance: for one row of cells,
closing the bottom and top bond of one cell blocks every open left-to-right
walk.

## Finite uniqueness delimitation

`two_crossing_clusters_no_barrier` considers two or more rows with only the
bottom and top horizontal rows open, and proves:

* both rows give open left-to-right reachability;
* their left endpoints are not open-connected;
* every bottom-row horizontal bond has zero closed-bond seam parity.

Thus the direct bar to a closed chain entering from below does not enforce
uniqueness of a left-to-right crossing cluster. The last clause in this module
is the explicit bottom-row computation; a theorem literally quantified over
`PrimalClosedDuality.closedGraph` still needs the bridge described below. This
finite-box counterexample is not a refutation of `GlobalAtMostOne` or of
Theorem 1.11: global uniqueness can instead use a cofinal/sealed family of
separators.

## Exact boundary of this component

This file does **not** yet extract a `CellChain` from a below-to-above path in
`PrimalClosedDuality.closedGraph`; in particular, its collapsed outer vertices
must be handled correctly in that conversion. It also does not supply the map
from `primalGraph` to `boxGraph`. Those are the remaining steps needed to apply
`closed_chain_blocks` to the preceding
[primal/closed-bond module](CLOSED-BOND-PRIMAL-DUALITY.md).

No uncollapsing of exterior dual rows, `gridCrossEquiv` transport, infinite
volume, compactness, cofinal barrier family, `GlobalAtMostOne`, FK measure or
Theorem 1.11 is claimed here.

## Verification

The exact source was independently rebuilt under Lean 4.35 against the pinned
imports at default heartbeats. Its 11 fully qualified principal declaration
audits depend only on `propext`, `Classical.choice` and `Quot.sound`. No `sorry`,
`admit`, custom axiom, `unsafe`, `native_decide`, or heartbeat/trust override
is present.
