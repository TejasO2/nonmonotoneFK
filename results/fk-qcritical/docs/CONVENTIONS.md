# Direction F: geometric convention transport (Proposition 1.8(2))

## Files and verification

- `ConventionTransport.lean`: geometry, measurable graph conventions, actual
  DLR/Gibbs transport, and the interior global-to-exterior uniqueness argument.
- `ConventionEndpoints.lean`: deterministic endpoint DLR classes, all-rate
  transport, and the two endpoint weak-limit conclusions.
- `ConventionTransportAudit.lean`: kernel axiom audit of the principal chain.
- `check.sh`: rebuilds both modules with the repository Elan/Lean 4.35 pins and
  writes `ConventionTransportAudit.log`.

Run `bash check.sh` from this member directory. The final build completed and
all audited declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Neither module contains `sorry`, `admit`, `unsafe`, or a new
axiom. No repository source was edited.

Source comparison used [arXiv:2512.16486v1, Proposition
1.8](https://arxiv.org/html/2512.16486v1). Its item (2) makes both a
`Gibbs under one convention => Gibbs under every convention` assertion and a
separate assertion for weak-limit measures.

## New interface

`ExteriorGeometry` gives, for every finite box and exterior configuration,
the actual exterior component setoid and infinitude predicate. `IsGeometric`
imposes exactly the paper's two properties using the existing
`ConventionGeometry` declarations:

- `MergesOpenComponents`;
- `SeparatesFiniteComponents`.

These are not inferred from `BoundaryAssignment.measurable_partition`.
`SimpleGraphBoxData` embeds each finite labelled box into an actual global
`SimpleGraph`, with an explicit endpoint identity for every labelled box edge.
Its `geometry` uses actual open walks after closing the box interior.
`free` and `wired` construct measurable free and wired-at-infinity assignments;
`free_isGeometric` and `wired_isGeometric` prove their compatibility. The
finite-box FK measures and their arbitrary boundary setoids are unchanged.

The generic results `partition_eq_free_of_atMostOne`,
`partition_eq_of_atMostOne`, `mem_dlrMeasures_of_atMostOne`, and
`mem_gibbsMeasures_of_atMostOne` apply to arbitrary global edge types and
finite labelled boxes. They use the existing exact `IsDLR` comp-product
identity and almost-everywhere equality of boundary partitions, not an
identification of incompatible exterior laws.

## Genuine hypothesis reductions

For `0 < p < 1`, `ae_forall_interior_of_ae_glue` uses
`Measure.ae_ae_of_ae_compProd`: almost-every goodness of glued configurations
gives almost-every exterior section goodness. Full support is not assumed:
`fkMeasure_singleton_pos` proves it from positivity of the actual normalized
finite FK PMF. Consequently
`SimpleGraphBoxData.aeAtMostOne_geometry_of_global` derives every exterior
marginal's at-most-one-cluster property from the genuine global a.s. event
`GlobalAtMostOne`. This removes the earlier `AEAtMostOne` hypothesis as well
as any separate full-support/measurable-section input.

`SimpleGraphBoxData.mem_dlrMeasures_of_global_atMostOne` and
`...mem_gibbsMeasures_of_global_atMostOne` use that reduction. Direct free
and wired DLR corollaries are also proved.

At `p = 0` and `p = 1`,
`isDLR_closedLaw_zero`/`isDLR_openLaw_one` verify the exact DLR equations
directly. The Dirac comp-product calculation uses the general measurable
section formula and does **not** assume measurable singletons on an infinite
exterior configuration space. Hence `dlrMeasures_zero_eq_singleton` and
`dlrMeasures_one_eq_singleton` identify the entire DLR classes with the
all-closed/all-open point masses.

Combining the interior and deterministic endpoint branches,
`mem_dlrMeasures_of_globalAtMostOne_of_le_one` and
`mem_gibbsMeasures_of_globalAtMostOne_of_le_one` cover every `p <= 1`.
Their remaining inputs are the actual source DLR/Gibbs membership, `q > 0`,
`p <= 1`, countable global vertices, compatible box embeddings, source and
target geometric certificates, the source coherent-nesting data for the Gibbs
form, and the source law's global a.s. at-most-one-cluster event. No separate
exterior uniqueness, full-support, or target-uniqueness hypothesis remains.

The endpoint weak-limit assertions are also closed:
`mem_gibbsMeasures_zero_of_mem_limitOrGibbs` and
`mem_gibbsMeasures_one_of_mem_limitOrGibbs` start from the actual
`LimitOrGibbsMeasures` union and use its already-proved deterministic endpoint
characterization.

## Scope not claimed

This does not prove all of Proposition 1.8(2). For interior parameters, the
passage from an arbitrary member of `FKLimitMeasures` to a DLR/Gibbs member is
still missing. Only the Gibbs-to-Gibbs assertion is proved throughout
`[0,1]`; the weak-limit assertion is proved at the two endpoints. The global
graph construction is specialized to countable simple graphs. The generic
DLR transport preserves arbitrary labelled finite boxes, but no global
infinite labelled-multigraph connectivity model is constructed here.
Likewise, existence of coherent nesting for the canonical free/wired
assignments is not asserted: they are `BoundaryAssignment`s unless separate
compatibility data is supplied. No strong-uniqueness, planar-duality, or
whole-paper theorem is claimed.

## Scoped interior weak-limit progress

`FK/InteriorWeakLimit.lean` now proves weak closure for continuous FK
specifications and, in particular, for locally constant boundary partitions.
Its canonical coherent weak-limit and graph-transport theorems are documented
in [Interior weak-limit closure](INTERIOR-WEAK-LIMIT.md). The nonlocal and
arbitrary-boundary interior cases remain open as described above.
