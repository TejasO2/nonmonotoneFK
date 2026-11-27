# Finite adaptive nested exploration

Public modules: `AdaptiveDisintegration`, `AdaptiveFK`, `AdaptiveStopping`,
`RegionFiberTransport`, `AdaptiveRegion`, `AdaptiveFrontier`, `AdaptiveTriple`,
`AdaptiveTripleStopping`, `AdaptiveGood`, `IndependentProductConditional`,
`IndependentProductFilter`, `NestedProductRegion`, `NestedAdaptiveCore`,
`NestedAdaptiveMarginals`, and `StoppedSeal`.

This is a substantial finite adaptive-coupling and stopped free-boundary
library within the general exploration programme. It is **not** a completed
Lemma 2.1(3), equation (9), Theorem 1.9, or Theorem 1.10.

## Adaptive process and stopped free interiors

Partial assignments support arbitrary next-edge strategies dependent on the
revealed upper history. `bind_bit_cond` supplies the exact arbitrary-edge
tower identity. The adaptive FK/Bernoulli ordered coupling preserves both exact
finite-configuration marginals and pointwise order, along with the FK upper
one-bit bound and the constant Bernoulli conditional bit at any revealed fibre.

The stopped process factors through its resumed residual process. Adaptive
closed regions stop at genuine closed frontiers, and every supported stopped
state has equal revealed sets, lower/upper order, and no revealed interior
edge. Its residual interior law is exactly the free-region FK law. This is not
the earlier fixed-shell estimate or a root-outward argument.

## Good intersection and nested marginals

`fkAdaptiveTriple` synchronizes two FK laws to a common adaptive upper history,
with all three marginals and both order relations proved.
`fkAdaptiveTriple_good_intersection` compares first-interior and second-interior
observations separately on each stopped stratum. It does not average over an
upper-open stratum or assume a shared joint conditional law from order alone.
The two arbitrary outer setoids only need to be free on the stopped interior;
the remaining signatures/hypotheses require that directly where used.

Independent products have exact left/right singleton conditionals. Conditioning
on a summed partial history factors through the two partial-history conditionals,
and projection outside the small coordinates recovers the original left
conditional. The FK upper conditional estimate persists on every mixed revealed
history.

`nestedAdaptiveTriple` uses the actual transported big FK law, a small FK law
independently extended by Bernoulli coordinates, and the transported upper
Bernoulli product. Its explicit extension does not require right-disjoint or
fresh vertices. The final marginal theorems recover:

* the original big FK first marginal by the transported configuration map;
* the exact small FK law by left restriction of the second marginal;
* the original upper Bernoulli third marginal.

The stopped independently extended small law has the small free-region
conditional law whenever its history has no small-internal assignments, all
small-external assignments, the required trivial boundary relation, and a
sealed exterior. The deterministic stopped exterior seal is exported separately.

## Exact non-results

This package does not yet provide the full induced-region compatibility and
free-law transport across ordinary nested boxes. A draft dependent-graph
transport failed and is not included. In particular, the final nested `hgood`
for ordinary nested subboxes is not established here.

The second nested coordinate also need not equal the upper coordinate on all
outside labels. A separate identity or compatible input would be required for
that equality; it is not made part of `nestedAdaptiveTriple`'s statement.

Consequently the following remain outside the accepted mathematical scope:
ordinary nested metric/source instantiation of Lemma 2.1(3), the final
equation-(9) bound, vanishing nested arm errors, infinite-volume DLR assembly,
and strong uniqueness. The final assembly in `SourceUniqueness` still needs
those finite exploration inputs, and the strict AG window remains independent.
