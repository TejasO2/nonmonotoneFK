# Exact triangle-cactus criticality and strict window

Public modules: `FK.TreeEdgeTransitive`, `FK.CactusGraph`, `FK.CactusMeasure`,
`FK.CactusPaths`, `FK.CactusShift`, and `FK.CactusGeometry`, namespace
`Ultra.TriangleCactus`.

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

## Homogeneous criticality and a direct-bond penalty window

`CactusShift` upgrades the transport result to exact original-bond criticality.
For a homogeneous rate $p$ on all three bonds of each triangle, the effective
rate is $p+p^2-p^3$. The declaration `homogeneous_criticality` realizes its
critical rate `pc0` by the intermediate-value theorem strictly between $1/5$
and $1/4$, and proves nonpercolation below and at `pc0` and positive
percolation probability above it. The underlying exact tree criterion is
`two_rate_criterion_full`, already proved in the repository, rather than an
additional critical-shift hypothesis.

For every $0<\varepsilon<\mathrm{pc0}$, `strict_direct_penalty_window` decrements only
the direct bond to $p-\varepsilon$, leaves both spokes at rate $p$, and takes

$$
\delta=\min\left(\frac{1/4-\mathrm{pc0}}2,\frac{\varepsilon}4\right)>0.
$$

It proves nonpercolation on the actual cactus for every
$\mathrm{pc0}\le p<\mathrm{pc0}+\delta$. The exact effective failure is
$(1-p)(1-p^2)+\varepsilon(1-p^2)$; a uniform Lipschitz estimate keeps it
above the tree threshold $3/4$ throughout the window. Within this parameter
range the truncation in the real definition of the penalty is inactive.

`CactusGeometry` supplies the corresponding geometry on original bonds. Each
direct bond lies on an actual double ray and in an actual cycle of length three.
The direct triangles form a source-separated device family, and every actual
bond has line-graph distance at most one from the direct family. The final
`triangle_cactus_model` packages connectedness, local finiteness as finite
neighbour sets, quasi-transitivity, infinitude, $0<\mathrm{pc0}<1$, this
geometry, and the strict window.

## Scope

This is a complete independent-Bernoulli theorem for this explicit Husimi
triangle cactus over the five-regular junction tree. (Each old junction has ten
neighbours in the expanded graph; “five-regular” describes the junction tree.)
It is **not** the general Aizenman–Grimmett theorem, an
essential-enhancement result for arbitrary quasi-transitive graphs, an `hAG`
construction, or Theorem 1.4 of the paper. No general AG/FK/DLR conclusion is
inferred from the model-specific strict shift.
