# Continuous arcs, segment coverage and reparametrization

The modules `FK.ContinuousSegmentWindow` and
`FK.ContinuousReparametrization` remove affine parametrization from two
existing continuous-plane windows. They preserve the exact geometric carrier
and its actual connected-component faces. These are finite local geometry
results, not the continuous/global construction required by Theorem 1.11.

## Segment coverage from continuity

`FK.PlaneTopology.Continuous.SegmentArc.range_eq_segment_of_continuous` takes
a Jordan arc $\gamma$ with distinct prescribed endpoints $a,b$ and
$\operatorname{range}\gamma\subseteq[a,b]$. It proves
$\operatorname{range}\gamma=[a,b]$.

The proof projects points of the straight segment onto their real progress
coordinate. That coordinate is continuous along $\gamma$ and runs from zero
to one, so the intermediate value theorem attains every intermediate value. A
segment point is uniquely determined by this coordinate. No affine
parametrization of $\gamma$ is assumed; injectivity is used only when this
arc is packaged as a source-faithful `FiniteArcEmbedding`.

For that arbitrary-param one-edge embedding, the module proves the exact
segment carrier, a one-element actual-face type, a `OneSegment.rotation.Face`
equivalence, and the literal `InteriorEdgeCoverage` premise consumed by the
sealed-cell interface. The ambient graph remains exactly
`SimpleGraph.edge a b`; no larger graph or dual graph is asserted.

## Range-preserving transport

`ArcReparametrization E` provides a new Jordan arc for every labelled edge of a
finite arc embedding `E`, with **both the same endpoints and the same range**.
`FiniteArcEmbedding.reparametrize` carries the original embedding structure to
those new arcs. Range equality turns an intersection on a new arc into one on
the old arc; the old endpoint properties and new-arc injectivity recover the
new endpoint parameters. Thus noncrossing is transported without enumerating
incident edges.

`carrier_reparametrize` proves exact carrier equality and
`faceEquivReparametrize` gives an equivalence of actual connected-component
quotient faces. The conclusion depends on identical ranges; equality of the
two endpoints alone would not justify it.

`Triangle.SideArcs` allows arbitrary continuous Jordan parametrizations of the
three straight sides of a nondegenerate affine-basis triangle. The segment
coverage theorem proves their range equalities, after which generic transport
produces `Triangle.continuousEmbedding`, its exact triangular-boundary carrier,
and `Triangle.continuousFaceEquiv` from the existing six-dart spherical
rotation faces to the actual continuous faces.

## Remaining planar obligations

This is not an arbitrary-curved-range realization: segment and triangle arcs
are contained in their prescribed straight ranges and only their
parametrizations are arbitrary. No angular/cyclic order is extracted from a
general continuous drawing, no arbitrary finite connected graph or infinite
embedding is constructed, and no `DualRegionWindow`, metric dual box,
primal/dual global equivalence, properness or pairwise-cofinal family follows.
The new coverage is only for the one-edge primal graph. Consequently no
cofinal sealed-window theorem, DLR/FK transfer, stochastic statement or
Theorem 1.11 conclusion is claimed.

Both sources were rebuilt sequentially under Lean 4.35 at default heartbeats.
All 21 listed axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`; the project-wide audit repeats these checks.
