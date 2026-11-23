# Global planar configuration compatibility

## Artifact

`GlobalPrimalCompatibility.lean` is self-contained apart from its single import
`FK.PrimalOpenBoundary`. No source file was copied into the shared result tree.
The imported module is the integrated version of the accepted
`smwsu3cov/m4/PrimalOpenBoundary.lean` artifact. The development also reuses the
existing `SimpleGraphBoxData` interface exposed by its transitive imports.

The file compiles with the repository Elan installation and pinned Lean
`4.35.0`, with default heartbeats. The one-target dependency build
`lake build FK.PrimalOpenBoundary` completed successfully. The logged source
compile and all twelve exact `#print axioms` results are in `audit-output.txt`.
Every audit lists only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved content

### Exact labelled-to-global collapse

`LabelledSimpleGraphEmbedding` consists of a finite labelled graph, a global
simple graph, a vertex map, a label map, and the endpoint identity. Neither map
is required to be injective.

- `label_eq_of_simpleEdge_eq`: labels identified by the finite simple-edge
  quotient have equal prescribed global labels. This handles parallel-label
  collapse without vertex injectivity.
- `simpleEdge_eq_of_label_eq`: with an explicitly assumed injective vertex map,
  equality of global labels gives equality in the finite simple-edge quotient.
- `simpleConfig_simpleEdge_eq_true_iff`: at a represented quotient edge, the
  finite disjunctive `simpleConfig` is open exactly when the original global
  edge is open. All parallel representatives use the restriction of the same
  global configuration.
- `SimpleGraphBoxData.toLabelledSimpleGraphEmbedding`: the repository's actual
  finite-box embedding data instantiates this interface without rebuilding the
  box or its edge subtype.

### Prescribed global dual configuration

`LabelledDualPairEmbedding` contains primal and face-dual embeddings related by
the prescribed global equivalence `edge : G.edgeSet ≃ GD.edgeSet`.
`dualRestriction_apply` proves the pointwise identity between the finite
complemented configuration and restriction of the actual global `dualConfig`.
`dual_restriction_eq_dualRestriction` identifies the two restriction maps.

`openConnected_globalDual_of_mem_openVertexComponent` then proves that a path
in an actual finite dual-open component gives global dual-open connectivity
between the embedded vertices. This is not merely an edge-value compatibility
statement.

### Circuit transport and global at-most-one

- `openConnected_global_of_reachable_setConfig` maps a local walk using only
  labels in `C` to a global open walk using only `LabelCarrier (label '' C)`.
  Its induction retains the precise edge and openness witnesses.
- `exists_vertexOnLabels_of_global` pulls incidence to a globalized label back
  to local incidence using the endpoint identity.
- `openLabelConnected_global_of_cycleMatroid_isCircuit` combines these with the
  accepted circuit-carrier theorem, proving global `OpenLabelConnected`, not
  ambient unrestricted reachability.
- `sphericalOpenCircuit_global_of_primalCircuit_subset_dualOpenComponentBoundary`
  turns a circuit in a finite dual-component boundary into a
  `SphericalOpenCircuit` of the original global graph/configuration. Radius,
  crossing control, and vertices off the sphere are explicit independent data.
- `hasOpenCircuitExhaustion_of_cofinal_globalizedBoundaries` handles a varying
  family of finite boxes while holding the global graphs, global configuration,
  and global edge equivalence fixed.
- `globalAtMostOne_of_cofinal_globalizedBoundaries` concludes the actual
  `GlobalAtMostOne G ω` from that finite-box supply and finite embedded-vertex
  preimages of balls. The conclusion is on the prescribed infinite/global
  graph, not on a finite quotient graph.

## Exact residuals

This is a configuration and circuit compatibility result, **not** the full
planar dual-nonpercolation theorem.

1. The hypothesis `hcofinal` still requires, for every radius, a finite
   dual-open component boundary containing a primal matroid circuit with the
   stated larger radius and global crossing/vertex-off-sphere data. No Jordan
   enclosure or cofinal geometric construction is claimed.
2. Only local-to-global dual path transport is proved here.
   `DualFiniteEnclosure` traps rooted global dual-open components in simple
   graph boxes, but those boxes/components must still be identified with local
   labelled plane-dual pairs and matching embeddings. Consequently global dual
   nonpercolation is not yet converted into `hcofinal`.
3. Properness of the global vertex realization remains the explicit `hproper`
   hypothesis.
4. The file does not assert
   `FK.Planar.DualNonpercolationForcesPrimalAtMostOne`, Theorem 1.11, or any
   stochastic FK measure statement.
5. Vertex injectivity is used only where explicitly stated for the reverse
   simple-edge/global-label implication; the main circuit transport does not
   assume it.
