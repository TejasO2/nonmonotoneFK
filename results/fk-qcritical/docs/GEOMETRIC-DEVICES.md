# Direction E: quasi-transitive geometric devices

## Deliverable

`FKQuasiTransitiveDevices.lean` imports `FK.AGEdgeGadget` and
`FK.Proposition42Interior` and introduces no parallel probability model.
Its graph hypothesis `FK.QuasiTransitive.IsQuasiTransitive G` is literally
`Finite (MulAction.orbitRel.Quotient (G ≃g G) V)`: finitely many vertex orbits
under the full automorphism group. It does not include bounded degree, local
cycles, or device-density conclusions as hypotheses.

The construction follows arXiv:2512.16486v1, Section 4, especially the
passages around lines 709–720 and 751–762 of `scratch/paper/main.tex`.

## Principal results

- `exists_degree_bound`: a connected, locally finite quasi-transitive graph has
  a natural-number bound on every vertex degree.
- `iso_edist_eq`, `iso_dist_eq`, `onDoubleRay_mapEdgeSet`: automorphisms
  preserve graph distance and transport actual double rays.
- `SimpleGraph.exists_lineGraph_walk_of_walk` and
  `SimpleGraph.lineGraph_dist_le_vertex_dist_add_one`: a length-`k` vertex walk
  joins arbitrary incident edges by a line-graph walk of length at most `k+1`.
- `exists_orbitEdge_close`: for any seed edge `e₀`, there is `K` such that every
  edge is within genuine `G.lineGraph.dist` distance `K` of some automorphic
  image of `e₀`.
- `exists_separated_template_devices`: maximal packing of all automorphic
  translates of a finite template gives `S` and finite supports `D` satisfying
  `FKLimit.IsSeparatedDeviceFamily S D`, bounded line-graph distance of `S`,
  double-ray membership of every selected pivot, the template cardinality
  bound, and explicit presentation of every selected support as a translate.
- `exists_separated_star_devices`: the preceding result specialized to the
  actual incidence finset `starDevice G v`. The conclusion packages a uniform
  degree bound `Delta`, separated double-ray active edges, bounded distance,
  `(D e).card ≤ Delta`, and an actual star center incident to each active edge.
- `exists_separated_cycle_devices`: specialization to the actual edge finset
  of a cycle walk. The conclusion takes `L = c₀.length` and supplies separated
  double-ray active edges, bounded distance, `(D e).card ≤ L`, and a genuine cycle
  `c` of length `L` with `D e = walkDevice c` and the active edge in `c.edges`.
- `card_auxiliary_le_pred`: deleting the pivot leaves at most `L - 1`
  auxiliary edges, exactly the shape of the two Proposition 4.2 exponents.

`Delta` is a uniform upper bound, not a claim that the chosen natural number is
computed as the literal global maximum. Likewise `L` is the length of the
supplied seed cycle, not an asserted minimum over all pivotal cycles. These are
sufficient uniform bounds for the enhancement estimates.

## Scope and remaining inputs

This is the graph/geometric device theorem, not Theorem 1.4 and not a strict
critical-point shift. It discharges the global separated-family, degree/size,
bounded-distance, and double-ray geometric obligations. It does **not** yet:

1. restrict these supports to each `InfiniteVolume.FiniteBox` and construct
   the finite `CutsetFamily` and `OpenPath.AuxiliaryPaths` certificates;
2. prove the star endpoint/boundary admissibility condition used in finite
   boxes or package the eventual activation predicates;
3. assemble the DLR/weak-limit stochastic comparisons, or prove the
   Aizenman–Grimmett strict critical-point window.

Thus integration into `Proposition42Interior` still requires items 1–2 and the
probabilistic work remains separate. The global separated-family interface and
its auxiliary cardinality bounds are proved here, not assumed.

## Verification

Checked independently with the repository's Lean 4.35 toolchain:

```sh
ROOT=$(cd ../../.. && pwd)
cd "$ROOT/results/fk-qcritical"
ELAN_HOME="$ROOT/.scratch/elan" \
  "$ROOT/.scratch/elan/bin/lake" env lean \
  "$ROOT/.ultramath/smwsq4fkq/m5/FKQuasiTransitiveDevices.lean"
```

The same successful run is captured in `audit.log`. All 14 `#print axioms`
reports for the principal declarations list only `propext`,
`Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`,
`unsafe`, or new axiom declaration. Only non-fatal style linter suggestions
were emitted.
