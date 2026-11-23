# Right-disjoint two-sided metric finite boxes

## Deliverable

`NestedMetricRightExtension.lean` is self-contained under the public imports

```lean
import FK.NestedCommonUpperGood
import FK.NestedMetricRegionSplit
```

It does not import or reuse the unaccepted `NestedFactorization.lean` handoff.

## Constructed graph and explicit source laws

For a two-sided finite split `si, ti, so, xo`, let `T` be its exterior-first
transported ambient graph. Given `D`, a disjoint `O`, `jD : Fin (k+m) ≃ D`,
and `jO : GO.Edge ≃ O`, the file constructs:

- `smallBox`, whose edges are `D` and whose graph is `T`;
- `largeIndex`, which enumerates `D ∪ O` by `rightExtendedIndex`;
- `largeBox`, whose graph is exactly the accepted right extension of `T` by
  `GO`;
- `edgeEquiv = (rightExtendedIndex GO).symm`, with global-label compatibility
  proved by `edgeCompat`.

The small boundary law `smallSourceLaw θ ζ` is the accepted two-sided source
law with arbitrary shared left setoid `θ` and right setoid `ζ`. The large law
`largeSourceLaw θ ζ χ` uses the second right setoid and arbitrary added `χ`.
Thus these are the actual `φΔ`/`φΣ` laws, not arbitrary boundary partitions
linked by a new premise.

`internalLabels jD` is the finite image of all left/internal coordinates, and
`internalObservationEquiv` indexes it by `Fin m`. Its application computes
exactly `internalLabel`. Consequently an arbitrary cylinder on all internal
coordinates is available without an observation-compatibility assumption.

## Proved results

1. `large_preimage_boxCylinder` identifies the large global box cylinder with
   the exact interior event used by the common-upper theorem.
2. `good_rightExtended_twoSided` discharges `hgood` on these constructed boxes
   via the accepted
   `fkNestedOrderedTriple_good_rightExtended_twoSided`.
3. `rightOpenPathMap` constructs the open-path map on the actual right-extended
   labels. `bad_rightExtended_smallStratum_subset_closedLocalEvent` proves
   `hD`; it does not pretend that `edgeEquiv` is `nestedEdgeEquiv`.
4. `cylinder_abs_sub_le_rightExtended_internal_farConnection` combines those
   facts with finite-volume assembly. Its explicit geometric inputs are
   finite-coordinate dependence of the far-arm and the split endpoint/root/far
   maps.
5. `Radial.cylinder_abs_sub_le_radial_rightExtended_farConnection` specializes
   to the actual radial metric split. It uses `smallIndex` on the actual
   `metricBox hG o r` edges and discharges the endpoint, left-root, far-radius,
   exterior-right, good-intersection, exceptional-set, and
   finite-coordinate-dependence obligations. For a connected locally finite
   `G`, the remaining geometric scale input is just `R ≤ r`; the arm is
   `farConnection G (innerBall hG o R) o R`.

The radial statement compares actual closed-exterior finite-volume laws on
the same internal global cylinder. It is not a definition of an `hgood`
premise.

## Scope and residuals

- The added block `GO` and its disjoint labels `O` are given independently.
  No endpoint interpretation of `O` in the ambient graph `G` is asserted.
  Accordingly this does **not** identify `largeMetricBox` with an ordinary
  larger nested metric box.
- The boundary laws are precisely the no-cross two-sided family with shared
  left `θ`, independent right `ζS, ζL`, and added `χ`; arbitrary metric-box
  boundary assignments are not claimed to belong to this family.
- The theorem does not itself assemble DLR measures or prove strong
  uniqueness, and it does not convert a canonical nested outer box into a
  right-disjoint extension.
- The radial roots remain the whole `innerBall hG o R`. This is not a
  fixed-small-root growing-radius result and does not solve Direction D.

## Verification

Checked with the already-installed Lean **4.35.0**, default heartbeats, using
`lake env` only to read the project's public compiled imports. The command
elaborated the file directly and returned exit status 0 with no warnings.
`verification.txt` contains the complete output. All printed declarations,
including both cylinder/arm estimates, the good-intersection theorem, the
right-extended `hD` theorem, and the canonical observation constructions,
report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There are no `sorry`, `admit`, `unsafe`, new axioms, or heartbeat overrides.
No shared source, GitHub state, or project toolchain was changed.
