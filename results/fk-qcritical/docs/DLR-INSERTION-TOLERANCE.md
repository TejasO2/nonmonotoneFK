# Genuine FK-DLR finite-pattern insertion tolerance

Public modules: `FK.DLRInsertionToleranceCore` and
`FK.DLRInsertionToleranceRegions`.

This proves actual FK finite energy at $q > 0$, $0 < p < 1$ for the exact DLR
interfaces in the project. It does not introduce a new insertion-tolerance
assumption, independence, stochastic monotonicity, nonpercolation, or
at-most-one-cluster premise.

## Central finite-box theorem

For a real public `FiniteBox B`, suppose the configuration law satisfies its
actual DLR identity and a finite pattern `j` is contained in `B.edges`.
`measure_pos_inter_forcedPattern_of_isDLR` proves every positive-measure event
depending only off `j` retains positive measure when `j`'s arbitrary Boolean
values are forced.

The proof is conditional-measure based:

1. `glue_forceInterior` identifies replacement inside the finite pattern with
   `Function.updateFinset` after gluing, preserving every other coordinate.
2. `updateFinset_mem_forcedPattern` shows the patched configuration belongs to
   the forced Boolean cylinder.
3. If the patched event were null, full-support positivity of every finite FK
   singleton mass would imply, on almost every exterior fibre, that no interior
   configuration can be patched into it.
4. Because the original event lives off the patch support, this forces its
   conditional mass on almost every such fibre to be zero.
5. `B.apply_of_isDLR` integrates the exact DLR formula to make the original
   event globally null, contradicting positivity.

This is not merely a Bernoulli independence trick. Strict positivity of every
finite FK configuration at interior parameters is used exactly where it is
needed.

## DLR classes and finite regions

`finitePatternInsertionTolerance_of_dlrMeasures` handles the actual
`DLRMeasures` of a `BoxExhaustion`; `..._of_gibbsMeasures` handles its
coherent-convention Gibbs class. The exhaustion contains every finite patch
after a sufficiently late stage.

`exists_boxOf_edges` proves every finite labelled edge set is contained in a
finite induced vertex-region box, simply by including its endpoint set.
Consequently,

- `finitePatternInsertionTolerance_of_canonicalRegionDLR` handles the exact
  public `ComparableNonpercolating.CanonicalRegionDLR` interface; and
- `finitePatternInsertionTolerance_of_sourceDLR` handles **every**
  `SourceRegions.SourceDLRMeasures Φ` at interior parameters. No
  `IsSourceGeometry` assumption is required for the finite-energy implication.

All values in the patterns may be arbitrary Booleans: this is not all-open-only.
The endpoint regimes $p=0$ and $p=1$ are not included.

## Positive encounter corollaries

`measure_pos_encounterEvent_of_canonicalRegionDLR` and
`measure_pos_encounterEvent_of_sourceDLR` feed the new property into the public
positive-encounter theorem. On a connected locally finite countable graph,
whenever the actual FK-DLR law assigns positive measure to the genuine
`ThreeInfiniteClusters` event, it assigns positive measure to the measurable
`EncounterEvent` with three-way arms at every scale.

These corollaries retain the positive three-cluster hypothesis. They do not
establish it or supply encounter-tree pruning, invariant encounter densities,
cluster-count constancy, a two-cluster merging argument, or an amenable/Følner
contradiction. Global Burton–Keane uniqueness and the planar FK theorem are
therefore not claimed. Arbitrary weak limits lacking the stated DLR
compatibility are explicitly outside this property.

## Verification

Ten fully-qualified principal declarations are in `Audit.lean`, all restricted
to `propext`, `Classical.choice`, and `Quot.sound`. The independent rebuild
elaborated both local modules using pinned Lean 4.35 and default heartbeats,
with the forbidden-source scan passing. The public gate is `./check.sh` from
`results/fk-qcritical`.
