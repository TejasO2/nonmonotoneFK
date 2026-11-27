# Finite source regions and ordered-kernel domination

Public modules: `FK.SourceRegions` and `FK.OrderedKernelNonpercolation`.
These prove geometric, finite-region and domination inputs to Theorem 5.1; they
do not assemble that theorem by themselves.

## Source conventions at every finite vertex region

`SourceConvention` uses the exact canonical `boxOf s` for every finite `s : Finset V`
of a countable locally finite simple graph. Its compatibility clause is the
finite FK tower condition at every nested pair. `SourceDLRMeasures` requires
actual DLR at every such box.
`IsSourceGeometry` includes both Section 1.3 conditions: exterior open
components are merged, and distinct exterior components are separated if at
least one is finite. The canonical region's vertices are a subtype, hence the
embedding into the ambient graph is injective.

At a closed frontier, `sourcePartition_restrict_eq_bot` proves that these
conditions give the discrete boundary partition. Every nontrivial exterior
walk from a region vertex would cross the closed frontier. A boundary
component is therefore singleton and finite, so finite-component separation
forces distinct vertices into different blocks. `sourceInteriorFKMeasure_restrict_eq_free`
and its global variant identify the actual conditional finite FK law with the
free law. This uses a **general convention**, not a change to the free or
wired convention as an assumption.

`ae_condExp_eq_freeCylinderMass_of_closedBoundary` identifies the fixed-box
conditional expectation for a box-supported event at a.e. sample outside the
DLR null set. The free cylinder value is law independent on a closed frontier.
This is not a random-region tower identity.

## Measurable finite regions

`finiteOrEmpty` packages a finite set, with an explicit empty fallback at an
infinite event. Its fibres and measurability are proved. `reachUnionFinset`
and `regionEdgeFinset` package the union of open clusters based at a finite
vertex exhaustion and the graph edges inside it. These are genuine measurable
`Finset`-valued maps. On finite clusters,
`regionEdgeFinset_eq_box_edges` gives the exact edge set used by the DLR box.
The theorem `ae_packagedRegion_data` combines closed frontiers, monotonicity,
finite-support cofinality and that edge-box equality.

## Nonpercolation inheritance along an ordered fibre

`OrderedKernelNonpercolation` proves: a decreasing property of the dominating
configuration holds in almost every ordered conditional fibre. For
`FK.NonPercolating G`, this gives both `K_i(η)`-a.e. nonpercolation and the
corresponding statement under the integrated dominated law. Its marginal
identity is the actual `(ρ ⊗ₘ K).map Prod.snd = μ`. It does not identify the
fibre with the second marginal, and it does not assert DLR, a shared coupled
filtration, or a common reverse-martingale limit.

The remaining ordered-fibre common-limit proof must use the region identities
and reverse projections at the law carried by the fibre. Such a limit need not
be the original law's tail conditional or a pointwise unconditional mass.
