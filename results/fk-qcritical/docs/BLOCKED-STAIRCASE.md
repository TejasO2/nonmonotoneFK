# Closed staircase rays and the star-to-adjacency upgrade

Public module: `FK.BlockedStaircase` (namespace
`FK.PlaneTopology.BlockedStaircase`), imported only through
`FK.GridDualConfigBridge` for the underlying square-lattice and dual APIs.
This is deterministic combinatorial planar topology, not a primal circuit
construction or a probabilistic uniqueness theorem.

## Shared closed bonds between corner cells

`sideLo` and `sideHi` name the two cells incident to a primal bond.
`CellClosed_sideCells` proves that a genuinely closed bond joins those two
cells in `cellClosedGraph`; directional normal forms identify the side cells
explicitly.

For a perpendicular turn, `corner` selects a cell incident to both bonds. In a
`StaircaseRay`, closed primal edges turn at every vertex. `cell_succ_reachable`
then links successive corner cells either by equality or by the closed bond
shared by the two turns. If the corner map is injective, its range proves an
infinite closed-cell component, and `exists_infinite_dualCluster` transports
that statement to dual-open connectivity for
`dualConfig gridCrossEquiv`. Dual nonpercolation therefore forbids the
injective staircase.

`StaircaseBarrierExists` is an explicit predicate, not an axiom. Its supplied
form says that two distinct infinite open clusters are separated by such an
injective closed staircase. Conditional on this geometric input,
`globalAtMostOne_of_staircaseBarriers` proves the repository's actual
`GlobalAtMostOne` from dual nonpercolation. The conditional wrapper documents
what the new local lemma buys; it does not discharge the geometry.

## What remains

The missing planar input is the topological construction of a blocking closed
barrier between distinct infinite clusters, with the turn and injectivity
properties actually used. This is not the same as constructing primal-open
finite circuits enclosing a root. Straight runs and additional perpendicular
bonds would require further consistent-side bookkeeping; the current theorem
only covers turns at every step.

The square-lattice strip crossings already available are still not circuits.
Exterior-face selection, Jordan separation/cofinal circuits, the general
embedding/certificate interfaces, and the FK measure assembly of Theorem
1.11 remain open. No statement about dual-parameter transport, essential
enhancement or a stochastic configuration is made by this local result.

The exact source was independently rebuilt under pinned Lean 4.35.0 with
default heartbeats. All ten principal axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`; warnings are style/deprecation lints.
