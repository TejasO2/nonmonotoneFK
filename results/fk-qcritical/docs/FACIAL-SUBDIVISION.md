# Facial edge subdivision

`FacialSubdivision.lean` is a Lean 4.35 module importing only the integrated
`FK.PlanarMatroid` development.

## Main construction

For a labelled dual pair `P` and `e : P.Edge`, `subdivPair P e` has:

- vertices `Option P.Vertex` and edge labels `Option P.Edge`;
- the old label `some e` as the first segment and `none` as the second;
- **exactly the old face type** `P.Face`;
- facial endpoints of `none` equal to those of `e`, so the two facial labels
  are parallel (including the case of two loops at one face).

This is the combinatorial image of subdividing a plane edge, not a declaration
that an arbitrary labelled graph is planar.

## Proved results

The proof computes the actual connection graphs. A projected primal
configuration opens `e` iff both segments are open; a projected facial
configuration opens it iff either parallel copy is open. Exact component and
open-cardinality formulas yield:

- `primal_isOpenForest_iff` and `faceDual_isOpenForest_iff`;
- `primal_indep_iff` and `faceDual_indep_iff`;
- `primal_isBase_iff` and `faceDual_isBase_iff`.

The set identity
`parallelSet P e B = (projectSet P e (Set.univ \ B))ᶜ`
then proves `dual_cycleMatroid_subdivPair` from an **old** certificate only.
`graphicDualCertificate_subdivPair` also supplies nonempty faces and all-open
facial connectivity. Loops, bridges, and parallel labels are included.

Coverage is precisely the closure of every already-certified family under
finite sequences of this single-edge operation. No general facial-ear
realization or general planar-duality theorem is claimed.

## Verification

`FacialSubdivision.olean` was built with the repository Elan toolchain, using
`-o .scratch/FacialSubdivision.olean`. `FacialSubdivisionAudit.lean` was
elaborated independently against that olean. All eight reported declarations
use only `propext`, `Classical.choice`, and `Quot.sound`; see
`FacialSubdivision.audit.txt`. A source scan found no `sorry`, `admit`,
`unsafe`, or new `axiom` declaration.
