# Exact cycle, unicyclic and finite cut duality

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

All 20 planar declarations from these three modules, plus six principal
unicyclic/forest declarations, are covered by the root axiom audit; only
standard Lean axioms are used.

## Unicyclic graphs and pendant forests

`FK/UnicyclicForest.lean` introduces `UniqueCycleCertificate`, containing only
finite graph properties: a nonempty distinguished cycle, all-open connectivity,
forestness after deleting any one cycle label, and nonforestness of the
distinguished cycle. `UniqueCycleCertificate.dual_cycleMatroid` computes both
sides and proves exact matroid duality for the two-face graph whose cycle labels
are parallel edges and whose other labels are loops.

`attachMany` adds an arbitrary finite family of pendant vertex/label pairs at
prescribed old vertices. `attachMany_certificate` proves preservation of the
unique-cycle data using explicit walk transport and pendant bridge arguments.
`attachMany_graphicDualCertificate` independently assigns each new dual loop to
a face. Iteration therefore covers arbitrary finite rooted-forest attachments
to a connected unicyclic core. `threeLeafDigon_graphicDualCertificate` is an
explicit five-edge example. These assignments do not assert a general plane
embedding and do not close the multi-face or infinite-volume gaps.
