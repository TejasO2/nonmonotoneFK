# Common-upper good intersection: right-disjoint two-sided class

## Result proved

`NestedCommonUpperGood.lean` constructs the actual common-upper nested-triple
`hgood` identity on the following explicit class, without a good-intersection
premise:

- the smaller graph is the transported separated split graph used by
  `NestedArbitraryInterior`;
- the larger graph is `rightExtendedGraph sT tT GO`, with canonical nested edge
  equivalence `(rightExtendedIndex GO).symm`;
- the left boundary is an arbitrary shared `θ : Setoid U`;
- the smaller and larger interior sides may use independent right setoids
  `ζS` and `ζL`, and the additional graph has its own boundary `χ`;
- `B` is an interior event and `C` is the canonical upper maximal split
  stratum.

The final theorem is
`FK.Exploration.NestedCoupledGood.fkNestedOrderedTriple_good_rightExtended_twoSided`.
It proves for `t := fkNestedOrderedTriple ...` exactly

```text
t.dist.toMeasure (first ⁻¹' B ∩ third ⁻¹' (restrictΔ e ⁻¹' C))
  = t.dist.toMeasure (second ⁻¹' B ∩ third ⁻¹' (restrictΔ e ⁻¹' C)).
```

This is a scoped graph-compatible result, not a whole-paper uniqueness theorem.

## Proof structure

1. Exterior-prefix conditioning gives the same normalized region-interior law
   on maximal strata, including after adjoining `GO`.
2. The history-level theorem
   `good_intersection_rightExtended_twoSided` compares the two good masses by
   summing over exterior prefixes and their common Bernoulli second marginal.
   It has independent right setoids on the two sides.
3. `good_intersection_rightExtended_pairs_twoSided` transports this identity to
   actual `fkUpperPair` graph configurations.
4. The final theorem projects the nested glued triple to its first/third and
   second/third pairs. The latter restricts to the smaller pair via the public
   `extendPairDist_map_restrictΔ_pair` theorem.

The incomplete handoff was checked declaration by declaration. Its final proof
required a dependency reorder, a general (non-Fintype) infinite-fiber sum
argument, general measurable-map evaluation, and explicit history inference.
The nested-triple transport is new here.

## Verification and residuals

Compiled with Lean 4.35.0 at default heartbeats. `final-audit.log` contains the
successful run and 28 `#print axioms` reports, one for every declaration. Every
report uses only `propext`, `Classical.choice`, and `Quot.sound`. There are no
`sorry`, `admit`, `unsafe`, or custom axiom declarations.

Not proved here: the metric exploration-region split/`hend`/`hleft`/`hfar`
certificate, transport of arbitrary nested metric-box boundary assignments into
this compatible-cross class, zero percolation, or any infinite-volume theorem.
