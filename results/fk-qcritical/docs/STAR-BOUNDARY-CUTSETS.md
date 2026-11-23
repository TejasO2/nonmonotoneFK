# Quasi-transitive star-device and finite-box audit

Source checked: Beffara--Faipeur--Oke, arXiv:2512.16486v1, Definition 4.1 and
the proof of Proposition 4.2.  The source defines a star-device as the full
incidence star, activates it only when it is contained in the finite box, and
uses the geometric boundary condition to prevent an off-pivot connection.
Crucially, the source boundary partition is on the geometric boundary
`partial Lambda`, not on every vertex of the box.

## Findings in the existing declarations

* `IsQuasiTransitive` is the actual finite-orbit definition, and
  `exists_separated_star_devices` uses actual incidence stars and actual
  automorphic translates.  `OnDoubleRay` is transported by graph
  automorphisms.  No mismatch was found in these meanings.
* `Delta` is an upper bound rather than a literal maximum degree, and the cycle
  theorem's `L` is the supplied seed length rather than the source's minimum.
  These still give the required finite exponents; they are not correctness
  errors.
* A real finite-box gap remains if one tries to derive star cutsets from
  `FKQuasiTransitiveDevices` alone.  `FiniteBox.BoundaryPartition` is an
  arbitrary `Setoid` on all box vertices.  If it identifies the star center
  with the other pivot endpoint, no closed cutset can refute
  `graphConnectionEvent`, even when all star auxiliaries are closed.
* `SimpleGraphBoxData` supplies the necessary endpoint compatibility, but its
  vertex map is not required to be injective.  Injectivity is needed to lift
  the singleton exterior component back to a singleton class of local box
  vertices.

The unrestricted fully wired example is formalized as
`not_isClosedCutset_wiredBoundary`: for every non-loop and every candidate set
`chi`, `IsClosedCutset` for `wiredBoundary` is false.  Thus this is a genuine
missing hypothesis, not merely an inconvenient proof interface.

## Compiling correction

`StarBoundaryCutset.lean` proves:

1. `starCutset_mem_cutsetFamily`: the erased actual local incidence star is an
   auxiliary closed cutset, provided the center has singleton boundary class;
   `card_starCutset_le` gives the `Delta - 1` bound.
2. `openConnected_eq_of_starContained` and
   `not_infinite_of_starContained`: after closing the box, a box-contained
   global star center has only itself in its exterior-open cluster.
3. `hasSingletonBoundaryClass_of_isGeometric`: every geometrically valid
   convention separates this finite component.  The canonical free and wired
   conventions have separate direct proofs as well.  These results assume an
   injective box vertex map.
4. `exists_starCutset_of_global_star`: constructs the actual local center from
   endpoint compatibility, transfers global separation to local auxiliary
   membership, and compares local/global star cardinalities.
5. `exists_starCutset_of_active_geometric`: discharges the exact active-star
   `hStarDevices` premise shape used by `Proposition42Interior`.

For a non-geometric arbitrary assignment,
`exists_starCutset_of_global_star` still applies with the explicit exact
singleton-class hypothesis at the selected center.  The counterexample shows
that this condition cannot be dropped in general.

## Residual scope

This is the star/cutset correction only.  It does not construct cycle paths,
prove a strict AG shift, or assemble the two-sided sandwich.  To combine it
with the global quasi-transitive theorem, retain the given exhaustion,
`SimpleGraphBoxData`, injectivity, geometric validity of the convention, DLR
hypothesis, and admissibility activation argument.  Separation, star witnesses,
and the uniform cardinality bound are already outputs of
`exists_separated_star_devices`.

## Verification

From the repository root, using its pinned Elan installation:

```sh
ROOT=$(cd ../../.. && pwd)
cd "$ROOT/results/fk-qcritical"
ELAN_HOME="$ROOT/.scratch/elan" "$ROOT/.scratch/elan/bin/lake" env lean \
  "$ROOT/.ultramath/smwsrcx3i/m5/StarBoundaryCutset.lean"
```

The final run exited 0.  A source scan found no `sorry`, `admit`, `unsafe`, or
axiom declaration.  Every `#print axioms` report in
`StarBoundaryCutset.audit.txt` contains only `propext`, `Classical.choice`, and
`Quot.sound`.
