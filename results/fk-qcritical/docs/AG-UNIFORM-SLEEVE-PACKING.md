# Uniform packing of genuine AG annular sleeves

Source: `AGUniformSleevePacking.lean` (public import `FK.AGSleevedAnnulus`).

## Proved construction

Fix a simple base graph `H`, a finite seed set `S` of base bonds, and a seed
bond `e₀ ∈ S`.  The complete template is

```lean
template H S = annulus H S ∪ edges H S
```

Its annulus and activation edges are internally disjoint, its exact cardinality
is `S.card + (edges H S).card`, and its cardinality is at most `3 * S.card`.

The lifted automorphism `Sleeve.automorphism H φ` transports `baseEdge H e` to
`baseEdge H (φ.mapEdgeSet e)`.  Canonical endpoint orientation can reverse, so
`automorphism_map_spokes` proves that the two spokes are either preserved or
exchanged.  This yields exact transport of annuli, activation edges and whole
templates:

```lean
translateSupport (automorphism H φ) (template H S)
  = template H (S.map φ.mapEdgeSet.toEmbedding)
```

Every edge of the sleeved graph has line-graph distance at most one from an
embedded base bond (`exists_baseEdge_dist_le_one`).  Assuming `H.Connected` and
edge-transitivity of `H`, this gives a uniform local cover using only lifted
base automorphisms.  If `baseEdge H e₀` is on a double ray, then
`exists_uniform_sleeve_packing` constructs a family `M` of base automorphisms
such that:

- the selected **whole** templates, including both annuli and activation edges,
  are pairwise disjoint;
- the distinguished embedded base pivots are at bounded line-graph distance
  from every edge and remain on double rays;
- every selected template has at most `3 * S.card` edges;
- `pivot_injOn_of_uniform_packing` proves that distinct selected templates have
  distinct distinguished pivots.

For every finite subfamily `F` of the packing,
`card_biUnion_packedTemplates` gives the exact no-overlap sum

```text
|⋃φ∈F template (image φ S)|
  = ∑φ∈F (|S| + |edges (image φ S)|).
```

The uniform upper bound is `|F| * (3 * |S|)`, and
`card_filter_mem_packedTemplates_le_one` proves pointwise that an edge belongs
to at most one selected template.  These finite accounting statements take a
`DecidableEq (graph H).edgeSet` instance, available by `classical`.

## Scope and residuals

This is deterministic packing geometry for the explicitly constructed sleeved
graph.  It does not assume or prove a support-contained replacement theorem,
an arbitrary-original-graph rerouting theorem, a general quasi-transitive
packing theorem, or a strict critical-point shift.

The remaining AG work is to attach one independent activation coordinate to
each selected template, sum the actual pivot probability inequalities with the
appropriate normalization, derive and integrate the differential comparison,
and construct the infinite-volume reference law.  None of those stochastic or
analytic consequences is claimed here.

The separate `AGMultiDeviceIndependence` module now proves the finite
independent-law/marginal and normalized multi-device differential parts of
that program; it does not discharge the remaining infinite-volume reference
law.

## Verification

`./compile.sh` builds only `AGUniformSleevePacking.olean` with the repository's
pinned Lean 4.35.0 environment and default heartbeats.  `./audit.sh` elaborates
`AGUniformSleevePackingAudit.lean` and writes
`AGUniformSleevePackingAudit.txt`.  All 13 principal declarations report only
`propext`, `Classical.choice`, and `Quot.sound`.  A source scan found no
`sorry`, `admit`, `unsafe`, new `axiom`, or heartbeat override.  No full-project
build was run.
