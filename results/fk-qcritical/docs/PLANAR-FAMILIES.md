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

## Spherical rotation systems and cellular exactness

`FK/RotationSystemDuality.lean` supplies a genuine combinatorial embedding
construction. A `RotationSystem` consists of oriented labelled darts, a
vertex-preserving rotation and one local rotation cycle at each vertex. Faces
are quotients by cycles of `rotation * reverse`, and `dualPair` computes the two
face incidences of every label. The code proves the $\mathbb F_2$ two-cell
boundary identity by dart reindexing, including loops, and proves all-open dual
connectivity from a primal walk. A `RotationSphere` adds connectedness,
nonemptiness and the actual spherical Euler relation, not a matroid-duality
premise. Its `graphicDualCertificate_of_rotationSphere` is therefore a general
finite labelled spherical-duality theorem.

The same module proves the underlying $\mathbb F_2$ incidence/forest,
complement-connectivity and rank facts. `FK/CellularExactnessRepair.lean` is a
second, independently constructed cellular formulation using a face-boundary
matrix, edge exactness and its transpose identification with the real face-dual
incidence. It proves rank-nullity duality, both complementary-base directions,
componentwise Euler identities and normalized FK-PMF duality. Facial nonemptiness
and connectivity remain separate where required. An independent replica of this
exactness route was also checked; one implementation is integrated to avoid
duplicate declarations.

## Wedge and cycle-chain assembly

`FK/WedgeDuality.lean` proves that matroid duality commutes with direct sums and
identifies the cycle matroid of an actual one-point graph union as a direct sum.
`graphicDualCertificate_wedge` simultaneously identifies two selected exterior
faces and proves the new dual connectivity. Pointed certified folds and
`graphicDualCertificate_cycleChain` cover every nonempty vertex-link chain of
connected labelled cycles, with loops and digons. `card_faces_cycleChainPair`
proves that a chain of $n$ blocks has $n+1$ faces. Geometric applications must
choose designated exterior faces to match their drawings; this is not a general
continuous plane realization.

The remaining step from an arbitrary continuous plane embedding to such
rotation/cell data, geometric Jordan separation, and the infinite dual/primal
cluster implication is still open.
