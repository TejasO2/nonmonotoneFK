# Good intersection on exterior-refined strata

Public module: `FK.NestedExteriorStrata` (namespace
`FK.Exploration.RefinedStrata`). The module works with the normalized finite FK
measures and the actual `fkNestedOrderedTriple`, not a renamed conditional law.

## Scope and hypotheses

Use the same graph class as
`NestedCommonUpperGood.fkNestedOrderedTriple_good_rightExtended_twoSided`:
a two-sided ambient graph with the displayed no-cross boundary and its
right-disjoint extension. The parameters satisfy $0<q$ and $0<p<1$.

Write
$\mathrm{SepExt}=\{e\mid\mathrm{Separated}(e)\}$, the exterior configurations
whose open edges avoid the interior. The only added hypothesis is
$E\subseteq\mathrm{SepExt}$. For an arbitrary region event $A$ and the third
event $M_E=\{\rho\mid\mathrm{exteriorConfig}(\rho)\in E\}$, the component proves

$$
\Pr_L[A\cap M_E]=\Pr_\Delta[A\cap M_E].
$$

Here the two probabilities are for the genuine first/third and second/third
marginals of the actual ordered triple. These are
`good_intersection_exteriorStratum`,
`good_intersection_rightExtended_pairs_exteriorStratum`, and
`fkNestedOrderedTriple_good_rightExtended_exteriorStratum`, at the prefix, pair,
and ordered-triple levels respectively.
`fkNestedOrderedTriple_abs_sub_le_of_exteriorStratum` feeds that identity into
the existing equation-(9) theorem without any coupling premise.

## Proof mechanism

The prefix argument compares each remainder with the same free interior FK law.
The upper exterior bits are fixed by the prefix, so membership in $E$ is stable
across a continuation. On branches in $E$, the inclusion $E\subseteq\mathrm{SepExt}$
places the configuration on the separated maximal split stratum, where the
already-proved regional continuation theorem applies. Both sides therefore reduce
to the same prefix weight times the same free-event probability. Their common
Bernoulli upper marginal identifies the two sums.

Setting $E=\mathrm{SepExt}$ recovers
`fkNestedOrderedTriple_good_rightExtended_maximalStratum`, the previous
maximal-stratum statement. `sepExt_eq_univ_of_right` proves the refinement is
non-vacuous: when every exterior label has its right endpoint in the exterior
summand, every exterior configuration is separated and hence every subset is
admissible.

## Exact residuals

This is the good-intersection identity only for **exterior-only refinements**. It
does not cover a third event that also constrains upper interior coordinates,
whose joint interior law may differ between the two sides. Pointwise separation
cannot be dropped, as the existing `ConfinedStrataObstruction` and
`ConditionalLaw` examples demonstrate.

The graph class is the existing right-disjoint two-sided extension. This module
does not construct ordinary nested metric boxes, establish their hgood identity,
construct a DLR limit, or prove Theorem 1.9/1.10. Board suggestions about
grafting and shell geometry are not formal impossibility theorems and are not
treated here as such.

## Verification

The exact source was independently rebuilt on pinned Lean 4.35 at default
heartbeats. Its 10 fully qualified principal declarations are included in
`Audit.lean`; each audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. No custom trust declarations or altered heartbeat limits are used.
The complete repository check is `./check.sh`.
