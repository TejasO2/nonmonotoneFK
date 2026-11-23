# Arbitrary-index edge-unique packed sleeves

## Finite incident traces

`InfinitePackedSleeves.lean` treats an actual independent family of sleeve
activations indexed by an arbitrary type, without an index finiteness or
countability assumption. `EdgeUnique` says that each graph bond belongs to the
complete template of at most one device. On a finite metric edge trace `L`,
`card_incidentFinset_le` chooses an incident edge for every device and uses
edge uniqueness to obtain an injection into `L`; at most `|L|` devices occur.
The localized arm therefore omits no relevant activation coordinate and the
outside-device contribution to its finite polynomial and derivative is zero.
No infinite derivative sum is formed.

The module also contains exact local/global comparison-line identities,
trace-wise finite differential comparisons, the selected-coordinate speed,
and arm endpoint inequalities. The three elaboration repairs from the earlier
handoff were included in its independently compiled source; no mathematical
hypothesis was weakened to make those repairs.

## Measurability and actual percolation

For a bond in a device template, `addsEdge_independentSupport_iff_of_mem`
identifies activation precisely with that one device's coordinate.
`measurable_deviceConfig_independentSupport_of_edgeUnique` consequently proves
measurability of the actual enhanced configuration with no countability of
the device index: a bond uses either one specified measurable activation
coordinate or its ordinary bond coordinate.

`globalPercolationEvent` is the preimage of the genuine infinite open cluster
under this enhancement. It is proved equal to the decreasing intersection of
finite enhanced arms. `tendsto_infiniteProductLaw_deviceArmEvent_global` uses
measurability and continuity from above for the actual infinite-product law.
`infiniteProductLaw_globalPercolation_globalLine_le` then passes the proved
one-arm comparison through those limits to the non-strict enhanced
percolation comparison. Only probabilities are passed through limits.

For actual uniform packing, `packedSleevesSet` includes every selected graph
automorphism, not just a finite subset. Whole translated-template pairwise
disjointness implies edge uniqueness and exact common cardinality, giving
`infiniteProductLaw_packedSetPercolation_globalLine_le` for arbitrary `M`.

The displayed graph connectivity/local finiteness/countability, common positive
annulus cardinality, unit-rate endpoint and exposed parameter-box hypotheses
remain. This is a comparison under edge uniqueness or disjoint translations,
not a construction of a positive-density packing, a reference law, `hAG`, or a
strict critical shift.

## Verification

The exact 1,097-line source was independently rebuilt using pinned Lean
4.35.0 and default heartbeats. Twenty principal declarations were separately
audited and passed the repository's allowed-axiom checker. No placeholders,
unsafe/custom axioms, or elaboration overrides occur. The release check repeats
those audits on the public import.
