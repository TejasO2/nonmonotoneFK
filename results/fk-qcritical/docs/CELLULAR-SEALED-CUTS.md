# Cellular sealed cuts and dual-nonpercolation assembly

Public module: `FK.CellularSealedCuts`.

This is a **scoped geometric completion**, not a proof of all of Theorem 1.11.
It proves a new finite/global cellular enclosure theorem and assembles exact
cofinal cellular windows into the actual
`FK.InfiniteVolume.ConventionTransport.GlobalAtMostOne` on the original global
simple graph. The continuous-drawing-to-window construction remains open and
is listed below; it is not hidden in a metric sphere or an all-open-cut claim.

The older crossing-controlled spherical and even arbitrary-separator interfaces
are too strong: the accepted `FK.SealedSeparation` staircase example refutes
them. Here exit edges may be closed. Each exit from a finite region must only
have an endpoint incident to one open-connected circuit. This is exactly what
the finite face-potential and rotation-system arguments prove.

## Proved declarations

* `SealedRegion` packages a finite vertex region, an open-connected carrier,
  and the endpoint-sealing condition on every exit edge.
  `SealedRegion.exists_carrier_vertex_of_walk` and
  `globalAtMostOne_of_cofinal_sealedRegions` prove the sharp geometry-free
  infinite-cluster argument.
* `vertexOnLabels_or_vertexOnLabels_of_adj_not_faceInterior` proves the local
  one-step face-potential exit theorem, without assuming that the adjacency is
  open.
* `exists_sealedRegion_of_facePotential` globalizes a circuit and an exactly
  identified potential class. `exists_sealedRegion_enclosing_dualBox` constructs
  that class from a spherical rotation window and a connected saturated dual
  box. The result includes `C = vertexCut T`, `D ⊆ T`, finite `T`, nonempty
  `Tᶜ`, connected inside/outside face regions, and containment of all global
  vertices represented with every incident face in `D`. The primal vertex and
  label maps need not be injective.
* `DualRegionWindow` records exact local/global box incidence: injectivity of
  the dual vertex map, the membership equivalence, coverage of box vertices,
  and representation of every internal simple edge. Its theorems lift ambient
  walks and restrict the actual global closed-frontier rule to the local dual
  configuration.
* `exists_sealedRegion_of_metricDualBox` uses the accepted
  `planarDualMetricExhaustion`. Consequently dual nonpercolation, rather than an
  assumed local component-finiteness certificate, supplies the connected closed
  boxes.
* `globalAtMostOne_of_dualNonpercolation_of_cofinalCellularWindows` proves the
  original global `GlobalAtMostOne G ω` from dual nonpercolation and a cofinal
  family of exact cellular windows.

No disconnected, all-open, or staircase instantiation is used.

## Exact hypotheses of the final theorem

In addition to a preconnected locally finite nonempty dual graph and finite
preimages of dual metric balls, the final theorem takes, for each `n`:

1. a finite labelled multigraph `L n` and a `RotationSphere (L n)`;
2. a `LabelledDualPairEmbedding` into the fixed original primal/dual graphs;
3. a local face set `D n` exactly representing region `n` of the **constructed**
   metric closed-boundary exhaustion, through `DualRegionWindow`;
4. a specified local edge in the vertex cut of `D n` (so the finite enclosure
   is nonempty, not a cornered/empty-box certificate);
5. `InteriorEdgeCoverage` for every circuit face region below that cut: each
   global edge at a vertex all of whose incident faces lie in the region lifts
   to the finite window, with its other endpoint and label exactly preserved;
6. pairwise cofinality: for any two original primal vertices, some window has
   local preimages of both, with every incident local face in `D n`.

These are real geometric obligations. In particular, the file **does not yet
construct (1)–(6) from an arbitrary continuous plane embedding**. The installed
Mathlib has no Jordan-curve or continuous cellular-embedding/rotation theorem;
no such result is cited or assumed elsewhere in this artifact. The face-potential
argument avoids Jordan separation once exact rotation windows are present, but
it does not manufacture those windows analytically.

`hfreeDual`, dual strong uniqueness, equation (12), and enhanced phase bounds
are not inputs or outputs. They remain separate parts of full Theorem 1.11.
Thus this file does not claim full strong uniqueness, Theorem 1.11, or an AG
critical shift.

## Rebuild and audit

The twelve principal declaration audits appear in `Audit.lean`, using fully
qualified declaration names. Run `./check.sh` from `results/fk-qcritical`.
Every audited declaration depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`; there are no `sorry`, `admit`, `unsafe`,
`native_decide`, custom axioms, or heartbeat options.
