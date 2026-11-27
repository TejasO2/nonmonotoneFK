# Nondegenerate triangle: continuous circuit and spherical rotation

Public modules: `FK.TriangleCircuit`, `FK.TriangleEmbedding`, and
`FK.TriangleRotation`.

This is a complete result for **every** `b : AffineBasis (Fin 3) ℝ Plane`—that
is, every ordered nondegenerate triangle in `ℝ × ℝ`. It is not the arbitrary
simple-polygon Jordan theorem.

## Exact two-sided plane separation

Define `solid b = convexHull ℝ (Set.range b)`, the three closed sides
`boundary b`, `inside b = interior (solid b)`, and
`outside b = (closure (solid b))ᶜ`.

The proved results include:

1. `frontier_solid`: the frontier is the union of all three segments, derived
   from affine-basis barycentric coordinates and the simplex surface
   decomposition.
2. `compl_boundary`: the carrier complement is the inside/outside union.
3. `not_joinedIn_inside_outside`: no path avoiding the sides crosses from
   inside to outside. A general connected-path/frontier lemma is proved
   directly, without invoking Jordan's theorem.
4. `isPathConnected_inside`: convex interior gives path connectedness.
5. `isPathConnected_outside`: radial projections carry every pair to a
   sufficiently distant sphere and a path on that sphere; convexity keeps the
   radial segments outside the solid. The general bounded-convex exterior
   version requires module rank greater than one.
6. `isBounded_inside` and `not_isBounded_outside`: the bounded inside is
   distinguished from the unbounded outside.

These witness two actual regions rather than assuming a two-face certificate.

## Faithful three-segment continuous embedding

`TriangleEmbedding.graph` is the cyclic labelled graph `0 → 1 → 2 → 0`.
Every vertex/embedding field is constructed using `straightArc`:

- injectivity of the three basis vertices;
- exact source/target endpoint compatibility;
- no nonincident vertex on an arc; and
- every intersection of two distinct side arcs is a common triangle vertex.

The last two facts rely on simplex face membership and linear independence of
the two side vectors at the relevant vertex. Thus `embedding b` is a genuine
`ContinuousPlane.FiniteArcEmbedding`, and `carrier_embedding` proves the
compact carrier is exactly `boundary b`.

Using `ConnectedComponents.equivOfIsClopenOfIsConnected`, `faceEquivBool`
identifies the embedding's real connected-component faces with `Bool`:
`false` is the outside, `true` the inside. Both are relatively clopen,
nonempty, path-connected regions in the complement.

## Exact six-dart rotation and face equivalence

`TriangleRotation` constructs the explicit involutive local rotation on all
six darts and verifies the required vertex cycles. Face traversal cycles the
three forward darts and, separately, the three reverse darts.

`faceOf_eq_iff_snd` identifies face orbits with the dart orientations, giving
`card_face = 2` and an exact `RotationSphere` with Euler identity
$2 + 3 = 3 + 2$. Finally

```lean
faceEquiv b : sphere.toRotationSystem.Face ≃ (embedding b).Face
```

composes the two Boolean-indexed equivalences. This is exact
combinatorial-to-continuous face incidence. It is intentionally not an
orientation-sensitive left/right/winding-number theorem.

## Explicit non-scope

Arbitrary simple polygons, concave polygons, general ray-crossing parity,
finite continuous graph embeddings and continuous rotation extraction are
still open. No `InteriorEdgeCoverage`, global simple-dual construction,
dual-box/cofinality, essential enhancement, or stochastic planarity theorem is
supplied. This is not Theorem 1.11, AG, Theorem 5.1, or equation (9).

## Verification

The 34 fully-qualified principal audits live in `Audit.lean`. Their only axiom
dependencies are `propext`, `Classical.choice`, and `Quot.sound`. A clean fresh
Lean 4.35 rebuild was independently rerun; the public gate is `./check.sh` from
`results/fk-qcritical`.
