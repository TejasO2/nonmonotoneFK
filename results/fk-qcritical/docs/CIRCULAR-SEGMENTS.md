# Straight dual arcs and circular loops

`FK/SegmentSeparation.lean` proves in every real normed space that a straight
segment from any point of an open metric ball to any exterior point has exactly
one sphere crossing on `[0,1]`. The crossing parameter is in `(0,1)`, earlier
parameters lie in the open ball, and later parameters lie strictly outside the
closed ball. Convexity of distance and the intermediate value theorem suffice;
strict convexity and a radial start point are not required.

`FK/CircleSeparation.lean` adds the concrete circle complement/path-component
lemmas. `FK/CircularSegmentCertificate.lean` packages a one-loop circular plane
embedding, labelled by its actual sphere, an arbitrary interior representative
and exterior representative. The two Boolean faces are proved to be exactly the
inside/outside path components. The generally non-radial straight dual arc has
one crossing and the exact inside-prefix/outside-suffix behavior. Its
`Certificate` also reuses the checked one-loop `GraphicDualCertificate`; it does
not assume matroid duality.

This is a concrete embedded circular example, not a general polygonal
Jordan-curve theorem or the infinite plane-cluster proposition. Twelve principal
declarations are included in the root axiom audit and use only standard axioms.
