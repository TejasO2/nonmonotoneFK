# Exact cycle duality and finite cut circuits

## Labelled cycle/parallel certificates

`FK/ThetaDuality.lean` proves, for every existing `IsLabelledCycle G`, the
actual matroid equality `(G.cycleMatroid)✶ = (cycleDual G).cycleMatroid`.
The proof computes independent sets and complementary bases; matroid duality
is not supplied as an input. `graphicDualCertificate_cycle` and
`graphicDualCertificate_parallel` construct the actual
`GraphicDualCertificate` in both orientations, including nonempty faces and
all-open face-dual connectivity. Explicit one-loop and two-parallel-edge
instances are included.

This covers connected labelled cycles and their parallel-edge duals, not yet
longer-path generalized theta graphs, arbitrary embeddings or Whitney's
general planar matroid theorem.

## Cut/circuit interfaces

Given an existing `GraphicDualCertificate`, `FK/PlaneCutCircuit.lean` proves:

- `exists_isCocircuit_subset_vertexCut`: a cocircuit through any chosen edge
  of a labelled vertex cut and contained in that cut;
- `exists_faceDual_isCircuit_subset_vertexCut`: its actual face-dual circuit;
- `exists_dualOpen_isCircuit_subset_vertexCut`: for a union of primal open
  components, every circuit label is primal closed, hence dual open;
- `exists_dualOpen_circuit_boundary_openComponent`: the corresponding
  canonical component statement and connectivity after deleting any circuit
  label.

The construction uses a spanning forest outside the cut and a fundamental
cocircuit, retaining loops and parallel labels.

`FK/PlaneClusterTarget.lean` names but does **not prove** the deterministic
proposition that dual nonpercolation forces at most one primal infinite
cluster. A genuine plane drawing, embedded Jordan separation, local
finiteness, exhaustion-to-infinity and probability integration all remain
open. A matroid circuit is not silently identified with a Jordan curve.

All 20 planar declarations from these three modules are covered by the root
axiom audit; only standard Lean axioms are used.
