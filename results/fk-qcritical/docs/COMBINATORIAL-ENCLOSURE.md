# Combinatorial enclosing circuits and sealed path incidence

Public module: `FK.CombinatorialEnclosure`.

This proves a new finite cellular/rotation version of the planar enclosing
circuit construction. It is not a proof of Theorem 1.11 or a construction of
continuous global cofinal families from dual nonpercolation.

## Exact enclosure

For a finite `CellularSphere`, a primal circuit has an `F2` face potential
whose nonzero coboundary is precisely that circuit. The proof uses dependence
of the circuit in the graphic cycle matroid and the cellular primal/dual
range–kernel equality, after exchanging primal and dual.

Two potential classes therefore have exactly the circuit as their labelled
vertex cut. If the circuit came from the cut of an ambient-connected dual box,
one class contains the whole box. Consequently
`exists_primalOpenCircuit_enclosing_dualBox` constructs a primal-open circuit
and region satisfying:

* the circuit is contained in the original box cut and includes a prescribed
  boundary edge;
* the region contains the original dual box, is finite and proper, and has
  exactly the circuit as its cut;
* every circuit label is primal-open, and all its incident primal vertices
  are connected in the actual primal-open configuration.

The strengthened connected version proves ambient preconnectedness of both
region and complement. The proof uses circuit-minimality: a disconnected region
would give a proper nonempty smaller cut. There is no asserted spherical locus
or separately selected exterior face.

## Rotation, labelled global windows, and path incidence

`exists_primalOpenCircuit_enclosing_dualBox_of_rotationSphere` constructs the
required `GraphicDualCertificate` from rotation/Euler data rather than adding
it as an input. The compatible labelled global-window version transports
openness and `OpenLabelConnected` to the actual global graph, allowing parallel
labels to collapse.

The rotation section proves a sealed path-exit statement. A primal-open walk
starting with all incident faces at potential `a` and ending outside that class
must reach a vertex incident with the circuit, and the already traversed open
prefix connects the source to that vertex. Clearing primal adjacencies lifts
to dual paths on the same allowed labels using actual rotation permutations
and darts. This correctly uses circuit-vertex incidence, not the false claim
that deleting a shared circuit vertex disconnects every primal path.

## What remains outside this package

The following are still required for Theorem 1.11:

1. arbitrary continuous plane embeddings and compatible finite rotation-system
   windows around the relevant global dual-open component and its cut;
2. dual nonpercolation in those compatible windows, with exact global primal /
   dual incidence;
3. comparable cofinal global windows and the finite-primal-preimage/properness
   arguments needed to cover every global region;
4. combination of sealed hits into `GlobalAtMostOne`; and
5. dual-parameter/complement transport, enhanced product phase bounds, dual
   strong uniqueness, and the final exactly-one/strong-uniqueness assembly.

The separate finite planar and probabilistic modules supply the finite FK
window and transport pieces. They do not turn this local combinatorial circuit
into a global theorem by themselves.
