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

## Ordinary confined nested triple and equation-(9) component

New public modules `FK.GenericNestedGood`, `FK.CanonicalEquality`, and
`FK.OrdinaryNestedTriple` finish the common-upper packaging of this finite
component. The first glues first/upper and smaller/upper ordered pairs through
literally the same third configuration and derives equation (9) whenever their
pair good-intersection identity holds. The second identifies the canonical
finite FK nested triple with that explicit glued triple. The third instantiates
the shell-first `good_intersection_annFirstPairs` identity on an ordinary
region-confined split, with added labels allowed to meet the shell but avoid
the region. It produces `nestedOrderedTriple_good_annFirst` and
`nested_annFirst_abs_sub_le`.

All the geometric assumptions remain visible: `hconf`, `hθ`, `AddedAvoid`, and
`ExteriorHasRight`. The public confinement-necessity and confined-strata
obstructions preclude dropping them. This does not assert arbitrary-setoid
metric nesting, construct the adaptive maximal cutset, or make the resulting
arm error vanish. Metric/weak-limit/strong-uniqueness assembly remains open.

## Remaining obligations

The remaining work is the adaptive maximal-cutset construction, instantiation
of the finite confined identities on genuine nested metric boxes and source
boundary schedules, and vanishing of the resulting fixed-root arm error under
subcritical nonpercolation. The new finite equation-(9) component is not a proof
of Lemma 2.1, Theorem 1.9, or DLR/strong uniqueness.

The source was independently rebuilt with pinned Lean 4.35. Its seven principal
export audits use only standard foundational axioms.
