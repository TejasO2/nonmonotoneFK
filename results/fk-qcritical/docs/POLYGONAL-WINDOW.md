# An exact non-affine unit-square window

`FK.PolygonalWindow`, in namespace
`FK.PlaneTopology.Continuous.Polygonal.Square`, constructs a four-cycle plane
window. It extends the existing triangle and straight-forest components, but
does not yet assemble arbitrary simple polygons or any cofinal global family.

## Carrier, interior and exterior

The labelled graph is an oriented four-cycle on `Fin 4`, with the unit-square
vertices and four closed straight sides. Explicit affine/Jordan side arcs give
a source-faithful `FiniteArcEmbedding`: distinct sides meet only at their common
vertices, and the endpoint parameters are proved rather than assumed.

`frontier_solid` identifies the four closed sides with the topological frontier
of the closed unit rectangle by coordinate membership. `carrier_embedding`
then proves that the range of vertices and arcs is exactly that frontier. There
is no diagonal.

The actual complement splits into the topological open inside and the
complement of the closure outside. `isPathConnected_inside` and
`isBounded_inside` use convexity; `isPathConnected_outside` uses the existing
general convex-body radial argument, and `not_isBounded_outside` proves
unboundedness. No Jordan-separation axiom is introduced.

These open connected regions give `faceEquivBool : embedding.Face ≃ Bool`, an
equivalence with the actual connected-component quotient faces.

## Rotation and exact actual-face equivalence

The eight darts are split into two orientations. At each degree-two vertex,
`rotationSystem` exchanges the incoming and outgoing darts; proofs are explicit
at the four vertices and do not pass from a list's enumeration order to a
general angular ordering. Forward and reverse dart traversals each form one
four-cycle. `card_face = 2` and connectedness/Euler data therefore give an
actual spherical rotation system.

`sphere` packages that system, and `faceEquiv` matches its two combinatorial
faces with the real inside and outside through the two `Bool` identifications.

## Non-affine side parametrizations

`SideArcs` permits any continuous Jordan parametrization on each side with the
prescribed endpoints and range contained in that straight side. The earlier
intermediate-value segment coverage theorem forces the range to be the entire
segment, and generic `ArcReparametrization` preserves the embedding, carrier
and actual faces. `carrier_continuousEmbedding` and `continuousFaceEquiv` give
the same square window for every such presentation.

The concrete `quadraticSideArcs` reparametrizes each side by $t\mapsto t^2$ on
the interval. `quadraticSideArcs_arc_zero_ne_arc` proves that its bottom side
is genuinely different from the affine arc by evaluating at $t=1/2$. Thus the
non-affine interface is inhabited, while the geometric carrier is unchanged.

`interiorEdgeCoverage` proves the literal sealed-cell strict-interior condition
for every face region on the square's own canonical four-edge `globalGraph`.
It makes no coverage claim for a larger ambient graph.

## What remains open

This is a complete four-sided example, not a general simple-polygon induction.
No arbitrary curved-range arc is manufactured, no arbitrary continuous graph
rotation is extracted, and no arbitrary finite connected planar graph is
constructed. New global work would still need carrier/gluing and complement
region control, exact dual windows on metric dual boxes, pairwise-cofinal
strict interior coverage, properness and dual nonpercolation. None of those is
supplied by this file, and no FK/DLR or Theorem 1.11 conclusion follows.

All 20 listed declarations were independently rebuilt with pinned Lean 4.35
and default heartbeats. Each axiom report uses only `propext`,
`Classical.choice`, and `Quot.sound`.
