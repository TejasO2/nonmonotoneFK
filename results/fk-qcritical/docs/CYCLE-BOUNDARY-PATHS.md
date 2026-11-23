# Cycle devices in finite labelled boxes

## Principal results

`CycleBoundaryPaths.lean` proves the finite-box cycle restriction requested for
Proposition 4.2:

* `FK.QuasiTransitive.exists_alternateWalk_of_mem_cycle` extracts an explicit
  complementary endpoint walk from any simple-graph cycle. Every edge of the
  walk belongs to the original cycle and has a label different from the pivot.
* `SimpleGraphBoxData.exists_underlyingWalk` lifts a global walk into a
  compatible finite labelled box when all its labels are in the box. The
  explicit hypothesis `hinj` is injectivity of the box vertex map; it is used to
  join consecutive lifted edges.
* `SimpleGraphBoxData.graphConnectionEvent_of_cyclePathOpen` proves the actual
  labelled FK connection event from openness of the localized cycle-minus-pivot
  support, for an arbitrary boundary partition.
* `FK.EnhancedTransport.cyclePathFamily_spec_of_active` consumes exactly the
  separated-cycle witness shape and `activeEdges`. It returns the required
  `OpenPath.AuxiliaryPaths`, the connection implication, and a path member with
  cardinality at most `L - 1`. Separation, not an added local-constancy
  assumption, gives the auxiliary-edge condition.
* `FK.EnhancedTransport.lt_dlr_upper_of_active_cyclePathFamily` is an
  integration check: it instantiates the existing
  `lt_dlr_upper_of_active_cycle_devices` with these certificates and obtains its
  stochastic upper DLR comparison.

## Scope and residuals

The construction requires a compatible `SimpleGraphBoxData` and injective box
vertex maps. Eventual device admissibility remains an input to the DLR theorem;
activity at a fixed scale supplies box containment for the finite certificate.
The main specification can also feed the other active-cycle comparison inputs,
but only the upper `p < p'` DLR application is packaged here. This is not a
claim of full Proposition 4.2, Theorem 1.4, or the remaining global enhancement
consequences.

## Verification

The file was elaborated with the repository's Lean 4.35.0 toolchain and default
heartbeats, without changing shared sources or running a shared build target.
`CycleBoundaryPaths.audit.log` records nine `#print axioms` results. Every
principal declaration, including the DLR application, uses only `propext`,
`Classical.choice`, and `Quot.sound`. A forbidden-placeholder/source scan over
the new Lean file reports no match.
