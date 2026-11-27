# Continuous plane embeddings and the one-segment window

Public modules: `FK.ContinuousPlane`, `FK.PolygonalSegment`, and
`FK.OneSegmentWindow`.

This package introduces source-faithful finite continuous plane-arc embeddings
and constructs a fully checked **one-edge** spherical rotation window. It is a
local continuous-topology result, not a construction of arbitrary or cofinal
rotation windows and not a planar FK theorem.

## Finite continuous arc embeddings and actual faces

`JordanArc` is an injective continuous parametrization of the unit interval.
`FiniteArcEmbedding L` equips a finite labelled multigraph with injective vertex
points and Jordan arcs with the specified endpoints. Vertices cannot occur on a
nonincident arc; every intersection of distinct arcs is a common endpoint.
These are genuine continuous arcs, not abstract planar-graph witnesses.

The carrier is compact, so its complement is open. `Face` is the
`ConnectedComponents` quotient of the actual complementary subtype.
`face_eq_iff_joined` and `face_eq_iff_joinedIn` identify source faces with path
components. Local path-connectedness of the open complementary subtype gives
open faces. No rotation system or Jordan separation theorem is built into these
definitions.

## Explicit segment separation

`PolygonalSegment` proves for arbitrary `a ≠ b : ℝ × ℝ`:

> the complement of the straight segment `[a,b]` is path-connected.

The proof constructs a three-leg detour to a common point beyond `b` on the
supporting line. Affine side/progress coordinates handle both on-line and
off-line starting points. The middle leg has constant nonzero side coordinate;
the final leg reaches progress `2`, beyond the target endpoint. Every leg
therefore avoids the segment. This is an explicit proof, with no Jordan-curve
or cellular embedding certificate assumed.

Consequently `subsingleton_connectedComponents_compl_segment` and its nonempty
counterpart give exactly one actual complementary face.

## One-segment spherical rotation window

`OneSegment.graph` is the labelled multigraph with vertices `false`, `true` and
one unit edge. `sphere` is a genuine `RotationSphere`, with primal
connectedness, one face and Euler count $1+2=1+2$.

For a nondegenerate straight segment:

- `carrier_embedding` proves that the compact drawn carrier is exactly `[a,b]`;
- `faceEquiv` identifies the unique face-traversal quotient with the actual
  continuous complementary face;
- `primalEmbedding` gives exact incidence in the ambient
  `SimpleGraph.edge a b`;
- `interiorEdgeCoverage` proves the primal coverage predicate consumed by
  `CellularSealedCuts`, uniformly for every face region of this window.

## Exact limits and remaining gaps

1. Only one straight segment is constructed. Arbitrary finite forests,
   polygonal arcs/circuits and noncrossing finite graph embeddings remain open.
2. There is no extraction of a rotation system from an arbitrary continuous
   embedding, and no claim that abstract planarity supplies a continuous one.
3. No `DualRegionWindow`, pairwise-cofinal metric dual box, dual nonpercolation
   argument, or global `GlobalAtMostOne` conclusion is provided.
4. The geometric dual of the single bridge is a loop on the unique face. This
   example therefore does not directly fit the repository's
   simple-global-dual interface; its coverage theorem is deliberately stated
   for the primal embedding only.
5. General AG, equation (9), Theorems 1.10/1.11, dual uniqueness and the
   exactly-one-cluster conclusion are not addressed.

## Verification

`Audit.lean` contains thirteen fully-qualified principal declaration audits,
all using only `propext`, `Classical.choice`, and `Quot.sound`. The accepted
submission's complete clean rebuild was independently rerun at default
options; the public gate is `./check.sh` from `results/fk-qcritical`.
