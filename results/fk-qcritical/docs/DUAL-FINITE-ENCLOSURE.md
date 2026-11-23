# Metrically cofinal finite dual enclosures

## Artifact

`DualFiniteEnclosure.lean` compiles with the repository's pinned Lean 4.35
libraries and default heartbeats. It imports the integrated modules
`FK.PrimalOpenBoundary`, `FK.ClosedBoundaryEventually`,
`FK.NonlocalGeometry`, and `FK.StrongUniqueness`. No import source is copied
into the artifact.

The new recursive construction `connectedBases` enlarges finite connected
regions by prescribed finite sets. Applying the already integrated
open-cluster closure gives `closedBoundaryExhaustionOfBases`. Specializing the
bases to embedded integer-radius metric balls gives
`metricClosedBoundaryExhaustion`: unlike the enumeration-based construction,
this directly records metric cofinality and needs no `Countable V` instance.

## Main scoped result

`exists_metric_dual_boxes_with_primalOpen_boundaries` assumes:

- the prescribed dual configuration has no infinite open cluster;
- the ambient dual graph is nonempty, preconnected, and locally finite; and
- every ball centered at `c` has finite preimage under `dualVertex`.

It produces an existing `ClosedBoundaryExhaustion`, hence finite connected
regions with closed ambient boundary, monotonicity, and exhaustiveness. It
also proves all four additional properties:

1. box `n` contains every dual vertex embedded in `ball c n`;
2. the actual simple-edge `edgeCut` of every box is finite;
3. for every dual cut label `f`, the prescribed primal label `edge.symm f`
   is open in the original configuration; and
4. every dual-open component rooted in `ball c n` is contained in box `n`.

The proof of (3) uses the actual complemented `dualConfig` and the closed
ambient boundary. The proof of (4) uses reachability in the actual open graph,
not an assumed finiteness or enclosure conclusion.

## Verification

From `results/fk-qcritical`:

```bash
. ../../.scratch/elan/env
lake env lean ../../.ultramath/smwsv3inm/m6/DualFiniteEnclosure.lean
```

The 13 `#print axioms` outputs at the end of the source are recorded in
`DualFiniteEnclosure.audit.log`. Every one is exactly a subset of
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`,
`unsafe`, new axioms, heartbeat overrides, or dependency changes.

## Explicit residuals

This is a finite-simple-graph enclosure theorem, **not** the full infinite
planar uniqueness theorem. Still missing are:

1. construction of finite labelled plane-dual pairs and their
   `GraphicDualCertificate`, with exact compatibility between the global edge
   equivalence and each finite window;
2. the Jordan/outer-boundary argument selecting an enclosing primal circuit
   inside one of these cuts, together with its spherical geometry and cofinal
   radius;
3. transport through parallel-label collapse where applicable; and
4. primal ball-properness and the final `GlobalAtMostOne` assembly.

The artifact does not claim dual nonpercolation alone supplies a spherical
circuit exhaustion, and it does not prove `DualNonpercolationForcesPrimalAtMostOne`.
