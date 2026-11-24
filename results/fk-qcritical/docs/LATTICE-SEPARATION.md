# Mod-2 lattice circuit separation

Public module: `FK.LatticeSeparation` (namespace `FK.LatticeSep.Circuit`).
This is deterministic square-lattice combinatorics, not the full plane-graph
geometry of Theorem 1.11.

## A combinatorial crossing parity

A `Circuit` consists of finite sets of oriented-index vertical and horizontal
lattice edges (orientation is bookkeeping only). `EvenDeg` requires every
vertex to have even incident degree, so it represents finite closed lattice
curves rather than an arbitrary edge set. `cellPar x y` counts, modulo two,
the vertical circuit edges strictly east of cell `(x,y)`.

`cellPar_succ` gives east-cell stepping: the previous and next cell parities
sum to the bit of the vertical edge between them. `handshake` proves the
horizontal stepping relation by summing the even-degree condition to the right
of a cell; horizontal terms telescope in `ZMod 2`. These are genuine local
crossing laws, not a metric-sphere assumption or an approximate winding number
in a different structure.

Along lattice walks, `vertexPar_step` (endpoints avoid `C`) and
`chain_vertexPar` prove parity invariance unless an incident vertex is met.
Consequently `exists_incident_of_walk` isolates a crossing point from parity 1
to parity 0, and `incident_of_openConnected` upgrades it to an incident
vertex *already open-connected to the start*. That last point is what makes
the later cluster argument usable.

## Up-to-right uniqueness from a cofinal circuit family

`openConnected_of_enclosed` starts from two parity-1 vertices with open walks
to arbitrary closed-parity right exteriors. Each walk must meet an incident
vertex, and the single incident-component hypothesis joins those vertices.
The cofinal version, `openConnected_of_cofinal_circuits`, packages this for
every finite set: if it is enclosed by an `EvenDeg` circuit whose incident
vertices are one open component, then any two vertices open-connected to
arbitrarily large right coordinates are open connected.

This supplies a deterministic separator/cluster engine and avoids using
`SphericalOpenCircuit` where those interfaces are unsatisfiable. It does not
construct the enclosing circuits from the dual model, select exterior faces,
verify arbitrary embeddings, or prove two disjoint infinite clusters produce
such structures. The hard remaining task is still dual-nonpercolation-to-
curved-circuit/family construction, with matched cluster conventions and
direction/reflection handling.

`unitSquare_evenDeg`, `unitSquare_cellPar`, `square2_cellPar` and
`allOpen_openConnected` demonstrate the parity convention on concrete curves
and give non-vacuous open-connectivity examples. They are checks of the
coding, not stochastic or source-device results.

All 16 principal axiom reports use only `propext`, `Classical.choice`, and
`Quot.sound`, with `openStep_adjacent` requiring none and the symmetry lemmas
using just `propext, Quot.sound`.
