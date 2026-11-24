# Random-region measurability and cluster-union exhaustions

Public modules: `FK.RandomExhaustion` and `FK.ClosedFrontierExhaustion`.
These provide conditional-probability and graph-geometric helpers for the
random-region arguments of Theorem 5.1. They do not prove Theorem 5.1.

## Countable random regions

`FK.measurable_family_apply` packages a countably indexed measurable family as
one jointly measurable map. Applied to exterior conditional expectations and a
measurable `Finset`-valued region, it gives
`FKLimit.measurable_randomRegion_condExp`: the exterior conditional probability
is jointly measurable in the sample configuration and the region parameter.

`FKLimit.ae_condExp_eq_of_frontier_projection` transfers a fixed-region
conditional identity to any coupling with the relevant first marginal. The
argument puts a countable union of `μ`-null failure sets above the coupling; it
does not use a random tower identity. The two-law variant
`ae_condExp_eq_of_dominated_coupling_frontier` establishes almost-sure equality
of both exterior conditional probabilities with one region-dependent value
`g S`, for an ordered coupling whose top configuration has a closed frontier.
The fixed-region free-boundary identification and `g` remain explicit inputs.

For a **product** coupling, Fubini and the fixed-region tower property give
`integral_condExp_randomRegion_prod`. With tail triviality, increasing
measurable regions and almost-sure cofinality,
`tendsto_ae_condExp_randomRegion_prod` gives reverse-martingale convergence.
The integral identity under the ordered coupling instead has right-hand side
`∫ g (T n η) ∂ℙ`. Product and ordered couplings serve different conclusions;
the module does not combine them.

## Closed-frontier geometry

`ClosedFrontierExhaustion` works on a countable simple graph, directly on
configurations of its edge type. `reachUnion ω Vn` is the union of open
clusters of a finite vertex set. The module proves vertex-membership
measurability, monotonicity, finiteness when every open cluster is finite,
and the key closure fact: every open edge with one endpoint in this union has
both endpoints there. `regionSet` is the corresponding edge region, with
monotonicity, cofinality along a vertex exhaustion and finiteness.

These regions need not be connected and this is deliberate: closed frontier,
not connectedness, is enough for the free-boundary reasoning. The module does
not link the simple-graph edge representation to every boundary-convention
API or package the finite sets as a measurable `Finset`-valued map. Nor does
it construct the adaptive exploration from the paper's maximal closed cutset.

The remaining global argument must instantiate the DLR/free-region identity,
carry out the finite-region packaging, and identify the unordered limit against
the ordered coupling rather than assuming the product-coupling conclusion.
The tower discussion in the submitted README is not an impossibility theorem
for the paper, and no assertion that the source is false is made here.
