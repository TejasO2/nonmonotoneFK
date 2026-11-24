# Shell-first exploration continuation and pair good intersections

Public module: `FK.NestedRegionExploration`. It proves the free-interior
continuation identity for a **shell-first** enumeration of an ordinary nested
split graph: first the smaller box's shell labels, then the region labels,
then the labels added in the larger box.

Added labels may meet the shell. They need avoid the region (`AddedAvoid`),
and the ambient boundary setoid is confined so a block touching the region is
contained there. This is where the earlier `MetricRegionGood` shell obstruction
is handled without pretending the added labels use fresh vertices.

`extendLower_shellHistory_eq_region` shows that the region coordinates after a
separated shell history have the free region FK law. `prefixCylinder_big`
computes the same event as `shellStratum`; filtering the history step, mapping
it through the split-graph equivalence, and applying the confined-stratum
theorem supplies the continuation. `pair_interior_continuation_bigAnn` gives
the FK/Bernoulli ordered pair version.

`good_intersection_annFirst` compares the resulting region/stratum masses by
using the common free law and the Bernoulli second marginal normalization.
`good_intersection_annFirstPairs` exposes this in the actual `fkUpperPair`
configuration laws, rather than merely postulating a good stratum equality.

## Remaining obligations

This module does not establish the final `fkNestedOrderedTriple` identity.
Although the edge restriction has an explicit helper `nestedExploreEquiv`, the
final triple graph types/projection packaging are not supplied. The concrete
metric split (`hconf`, `hθ`, `AddedAvoid`, root/arm behavior and eventual
vanishing) is still to instantiate. Hence it does not prove Lemma 2.1,
equation (9), Theorem 1.9, or DLR/strong uniqueness.

The source was independently rebuilt with pinned Lean 4.35. Its seven principal
export audits use only standard foundational axioms.
