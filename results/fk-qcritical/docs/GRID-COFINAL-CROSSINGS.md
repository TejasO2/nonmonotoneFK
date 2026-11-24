# Un-collapsed finite box duality and cofinal primal crossings

Public modules:

* `FK.GridBoxCrossing` (namespace `FK.PlaneTopology.GridBoxCrossing`)
* `FK.GridDualCofinal` (namespace `FK.PlaneTopology.GridCofinalCrossing`)
* `FK.GridDualConfigBridge` (namespace `FK.PlaneTopology.GridDualConfigBridge`)

## From collapsed exterior vertices to actual cells

`DCell k n` now consists of genuine `GridV` cells `0≤i≤k`, `-1≤j≤n`.
`DCellStep` uses genuine closed primal bonds of the box, so the top and bottom
exterior rows no longer appear as artificial outer vertices.
`primalOpenCrossing_iff_no_dualBoxCrossing` therefore expresses exactly the
finite crossing dichotomy on this un-collapsed cell box.

Both maps are proved. `DCellStep_toD` collapses a closed cell step to the former
closed graph. In the other direction, an interior step can be lifted directly,
while exterior visits must preserve reachability. The `Inv` argument tracks that
an honest path starts below and reaches the top through the correct final link;
repeated visits to the collapsed below vertex do not artificially connect
columns or relabel the primal box.

`GridDualCofinal` then gives genuine fixed-width consequences of bounded closed
components. A closed cell walk from row $-1$ up to at least row $0$ must visit
row $0$. Because finitely many row-zero cells have finite components whose top
rows are bounded, arbitrarily tall closed crossings force an infinite global
closed-cell component. Contrapositively, all components finite gives
`primalOpenCrossing_cofinally`: for every width, primal open crossings exist at
every sufficiently large height.

The last module identifies this global closed cell graph with the ordinary
`dualConfig gridCrossEquiv` open connectivity, by calculating the exact uncrossed
primal bond. It transfers `NoInfiniteOpenCluster` to the same cofinal crossings
in the repository's usual percolation language.

## The remaining global planar step

This is not yet a circuit family or `GlobalAtMostOne`. These are strip
crossings, not primal-open circuits enclosing a fixed centre in a cofinal
family. Turning them into circuits/sealers or a two-hypothesis closed-boundary
interface, then proving uniqueness, remains open. The package says nothing
about FK measure duality, essential enhancement or Proposition 1.8.

All three sources were independently rebuilt with pinned Lean 4.35 and public
imports. The resulting 16 principal axiom reports contain only the standard
foundational axioms.
