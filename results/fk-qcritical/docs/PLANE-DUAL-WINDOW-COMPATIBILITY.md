# Exact finite windows for global dual-open components

Deliverable: `PlaneDualWindowCompatibility.lean` (the suggested integrated
path is `FK/PlaneDualWindowCompatibility.lean`). It imports only the public
`FK.GlobalPrimalCompatibility`, `FK.DualFiniteEnclosure`, and
`FK.RotationSystemDuality` modules.

## Proved interfaces

* `LabelledDualPairEmbedding.exists_local_reachable_of_walk` lifts an open
  walk in the prescribed global simple dual graph to the finite labelled
  face-dual connection graph. Its inputs are injectivity of the dual vertex
  map and coverage of the actual rooted global component's vertices and
  internal edges. Neither path liftability nor component equality is assumed.
* `mem_openVertexComponent_iff_global` gives exact local/global component
  membership for represented vertices in both directions.
* `label_mem_globalEdgeCut_iff_mem_vertexCut` and
  `globalLabels_vertexCut_eq_globalEdgeCut_inter_range` identify the finite
  labelled component boundary with the actual `DualExhaustion.edgeCut` on all
  represented labels.
* `primal_globalLabels_subset_globalDualEdgeCut` transports those boundary
  labels through `edge.symm`.
* `ofRotationSystem` constructs a `LabelledDualPairEmbedding` for the actual
  rotation-system dual. Its dual label is definitionally
  `edge (primal label)`, so the global edge compatibility needs no extra
  field. `RotationSphere.graphicDualCertificate_of_rotationSphere` supplies
  the certificate required by the circuit existence theorem.
* `sphericalOpenCircuit_global_of_primalCircuit_subset_globalDualEdgeCut` and
  `exists_sphericalOpenCircuit_global_of_mem_globalDualEdgeCut` produce actual
  global spherical primal-open circuits from the global component cut.
* `DualExhaustion.coversGlobalDualComponent_of_planarDualMetricExhaustion`
  derives the coverage predicates from the constructed metric dual box,
  using its proved rooted-component containment. The required representability
  is boxwise: box vertices lie in the range of the dual vertex map, and every
  simple edge between represented box vertices has a local label.

## Explicit residuals / non-claims

The module does not construct plane embeddings from an arbitrary continuous
planar realization. It retains the injective dual vertex map, finite boxwise
vertex/edge incidence data, and (where circuits are asserted to exist)
`GraphicDualCertificate`. Positive radius, vertex-off-sphere, and
crossing-controlled Jordan geometry remain hypotheses. No cofinal Jordan
selection, primal metric properness, `GlobalAtMostOne`, or full Theorem 1.11
is claimed.

## Verification

The source was elaborated with the already-installed Lean 4.35.0 binary and
only the matching project `LEAN_PATH` (the VM default Lean 4.33.1 cannot read
these 4.35 oleans). The one-file check passed. The file audits every principal
declaration with `#print axioms`; every audit reports exactly
`[propext, Classical.choice, Quot.sound]`. No sorry/admit/unsafe/new axiom or
non-default heartbeat is present.
