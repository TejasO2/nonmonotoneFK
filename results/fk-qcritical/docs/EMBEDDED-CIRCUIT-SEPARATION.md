# Embedded circuit separation (direction G)

`EmbeddedCircuitSeparation.lean` is a self-contained Lean 4.35 module importing
`PlaneClusterTarget`, `PlaneCutCircuit`, `RotationSystemDuality`, and
`CircleSeparation`. It supplies a genuine continuous-path interface between
closed dual labels and primal open walks.

## Proved declarations

1. `OpenPathRealization` assigns an actual `Path` to every simple-graph edge.
   `CrossingControlledBy` says that every arc meeting a locus `K` has its label
   in the specified set. If those labels are closed,
   `joinedIn_compl_openConnected` proves that every global `OpenConnected` walk
   is realized in `Kᶜ`.
2. The sphere specializations prove inside/outside non-connection, confinement
   to the ball, finiteness of the open component when the vertex preimage of
   the ball is finite, and `not_exteriorInfiniteCluster_sphere` in the actual
   global percolation semantics.
3. `LabelledPathRealization` preserves every labelled source/target, including
   parallel labels. The analogous results use the actual
   `connectionGraph freeBoundary ω` and `openVertexComponent` definitions.
4. `SphericalDualCircuitGeometry` isolates the independent geometric input:
   positive radius, primal vertices off the sphere, and control of every primal
   arc crossing the sphere by that circuit's labels. Nothing constructs these
   fields from a matroid certificate.
5. `exists_dualOpen_circuit_boundary_openComponent_finite_of_spherical` combines
   this geometry with the existing finite cut/circuit theorem. For each chosen
   boundary label it obtains a genuine dual-open matroid circuit; all its
   labels are primal-closed by component saturation. Its finite-component
   conclusion is conditional on the root lying inside that circuit's ball.
6. `rotationSphere_exists_dualOpen_circuit_boundary_openComponent_finite`
   instantiates graphic duality with the actual spherical rotation-system
   certificate rather than assuming `GraphicDualCertificate` separately.

## Precisely remaining hypotheses

This is not a proof of `DualNonpercolationForcesPrimalAtMostOne`.
Dual nonpercolation is not an unused disguised hypothesis: it is simply not yet
used. A completion still needs an exhaustion argument producing the appropriate
closed dual circuits and resolving whether the root is inside the circuit
selected for a boundary edge. It must also supply continuous planar realizations
and their crossing/vertex-disjointness fields. Arbitrary Jordan circuits can use
the generic `K` avoidance lemmas, but this module proves only the metric-sphere
separation specialization already justified by `CircleSeparation`.
No facial-ear or sequential-exploration construction is included.

## Verification

The module was compiled to `.scratch/EmbeddedCircuitSeparation.olean` with the
repository Elan installation at `.scratch/elan`, through the 4.35 project's
`lake env`, with default heartbeat options. `EmbeddedCircuitSeparationAudit.lean`
was elaborated separately against that olean. Its saved output,
`EmbeddedCircuitSeparation.audit.txt`, reports exactly `propext`,
`Classical.choice`, and `Quot.sound` for all 14 substantive declarations.
No `sorry`, `admit`, `unsafe`, or new `axiom` declaration occurs in the module.
No shared-results file was edited.
