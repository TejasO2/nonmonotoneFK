# Straight finite labelled forests: complement and rotation

Public modules: `ForestAttachment`, `ScaledDetour`, `ForestGeometry`,
`SegmentAttachment`, `ForestHistory`, `ForestCombinatorics`, `StraightForest`,
`ForestRotation`, and `ForestWindow`.

This package proves the actual plane-complement theorem for **every straight
finite labelled forest**, including disconnected forests and isolated vertices.
For connected forests with a dart it also constructs a spherical rotation and
identifies the combinatorial and actual unique plane faces. It is not a theorem
about arbitrary continuous embeddings or oriented dual incidence.

## Exact geometric input

`StraightFiniteArcEmbedding G` extends the existing
`ContinuousPlane.FiniteArcEmbedding` only by

```lean
range_segment : ∀ e, Set.range (arc e) =
  [point (G.source e) -[ℝ] point (G.target e)]
```

The embedding already supplies genuinely injective continuous arcs and the
source endpoint/noncrossing conditions. No rotation or path-connected
complement is assumed. A labelled forest (`IsLabelledForest`) has every label
as a bridge in the free all-open configuration. This correctly excludes loops
and parallel-edge cycles, detects disconnected forests, and proves endpoints
of each edge distinct, so no additional nondegeneracy premise is needed.

The main result is

```lean
isPathConnected_compl_carrier_of_isLabelledForest
  (hG : G.IsLabelledForest) (E : StraightFiniteArcEmbedding G) :
  IsPathConnected E.carrierᶜ
```

`face_subsingleton_of_isLabelledForest` and its nonempty counterpart therefore
give one actual `ConnectedComponents` face, including the zero-edge case and,
indeed, the empty graph.

## Explicit attachment mechanism

`ScaledDetour` parameterizes the one-segment detour: the normal offset may be
arbitrarily short and the common beyond-end basepoint may approach the free
endpoint.

For compact `K`, a segment with distinct endpoints `a,b`, and
`K ∩ [a,b] = {a}`, `isPathConnected_compl_union_segment_of_attached` proves
`Kᶜ` path connected implies `(K ∪ [a,b])ᶜ` path connected. Its proof:

1. pushes beyond the new free end into a small ball in the old open complement;
2. chooses a convex thickening of a safe tube, contained entirely in that
   complement;
3. controls normal displacement and extension in that tube; and
4. uses a local-link/component-clopen argument: every component must touch the
   attached segment, and every off-segment point near that segment joins one
   common exterior basepoint by a scaled detour.

This is not an assertion about arbitrary polygonal paths and does not invoke a
Jordan-curve theorem. `StraightAttachmentHistory` turns repeated endpoint
attachments and isolated starting components into compact carriers with
path-connected complements.

## Faithful labelled-leaf induction

`ForestCombinatorics` converts the bridge condition to acyclicity of the
underlying simple graph and obtains genuine labelled leaves from the finite
tree leaf theorem on the relevant connected component. Loops and parallel
labels are ruled out by the same bridge data.

Deleting a leaf removes exactly its vertex and one incident labelled edge.
The restricted `FiniteArcEmbedding` satisfies every endpoint/noncrossing
field with no transported equivalence assumptions; its carrier meets the
deleted straight edge exactly at its attachment vertex. The bridge condition
is preserved. Therefore induction on the number of labelled edges supplies
the full claim for arbitrary finite degree and arbitrary components.

## Spherical rotation from the forest rank argument

`incidenceRotation` finitely enumerates the incidence darts at each vertex and
rotates them in one local cycle. This constructs a genuine local rotation,
but **not a claimed geometric clockwise ordering**.

For a connected labelled forest, `card_face_le_one_rotation_of_isLabelledForest`
proves every valid rotation has at most one face. It uses

$$\operatorname{range}\delta_{G^*}\subseteq
  \ker\partial_G,$$

with the appropriate primal/dual faces. For a connected forest, the primal
cycle kernel is zero and incidence rank identities give
$|V|=|E|+1$. The dual incidence rank formula then forces a unique face.
The no-dart quotient is handled separately.

Given primal preconnectedness and `Nonempty (Dart G)`,
`incidenceRotationSphere` constructs an actual `RotationSphere`, including Euler
count from connected forest cardinality identities.

Finally `ForestWindow.faceEquiv` identifies this spherical rotation’s face with
the actual continuous complement face, using their independently proved
singleton and nonempty properties. No oriented left/right-side,
face-traversal-side or general `InteriorEdgeCoverage` result is asserted.

## Conspicuous limits

1. Only straight segment ranges are covered. Arbitrary continuous arcs and
   abstract planar graphs do not obtain a construction here.
2. Disconnected forests receive the complete complement theorem, but not a
   single `RotationSphere`: that API requires primal preconnectedness. A bare
   disjoint rotation would instead represent separate surfaces; no global wedge
   assembly is claimed.
3. A connected zero-edge graph lacks the required `Nonempty (Dart G)`, although
   its actual complement is path connected.
4. The incidence enumeration is not an angular order, and there is no general
   dual region, finite dual device, essentialness, cofinality, AG or stochastic
   FK conclusion. In particular this is not Theorem 1.11.

## Verification

All nine modules were independently rebuilt in dependency order with pinned
Lean 4.35 and default heartbeats. Nineteen fully-qualified principal axiom
reports each contain only `propext`, `Classical.choice`, and `Quot.sound`, using
no placeholders, custom axioms or option overrides. The public gate is
`./check.sh` from `results/fk-qcritical`.
