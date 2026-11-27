# Exact triangle-cactus percolation transport

Public modules: `FK.TreeEdgeTransitive`, `FK.CactusGraph`, `FK.CactusMeasure`,
and `FK.CactusPaths`, namespace `Ultra.TriangleCactus`.

Each adjacency of the existing reduced-word five-regular tree is expanded to a
triangle, with its original direct bond and two independent spoke bonds. This
is an explicit graph with local finiteness, connectedness and quasi-transitivity.
The triangular expansion is not silently replaced by the underlying tree at the
model or percolation-event level.

`map_effective` shows that the original inhomogeneous independent-bond product
on these triples pushes forward to the exact five-regular base/activation
product used by `Ultra.AGTree.TwoRateCritical`. On one block the effective rate
is $r_0+r_1r_2-r_0r_1r_2$, with the three Boolean variables independent.
`actualPerc_iff_effective` proves that an open infinite cluster in the original
triangle cactus exists exactly when the effective junction connections
percolate. Direct bonds lift effective paths; every midpoint two-step detour
offers the spoke bypass; and a finite-fibred cluster argument handles the
reverse inclusion.

These are genuinely independent-bond and graph-geometric results necessary for
the block-critical computation. They do not by themselves supply the strict
critical-window algebra, matching enhancements/bond-distance packing, or the
general Aizenman–Grimmett theorem sought by the current campaign. The exact
parameter and enhanced-set assumptions must accompany any later shift.
