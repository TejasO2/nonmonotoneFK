# Exact right-extension compatibility and obstructions

## Ordinary nested edge labels

`ordinaryNestedRightIndex` composes the finite right-block enumeration with the
already established canonical nested edge equivalence. The helper
`ordinaryNestedRightIndex_symm` gives the exact reduction after inverting that
enumeration. On the two summands,
`ordinaryNestedRightIndex_inl` and `ordinaryNestedRightIndex_inr` then prove
that the resulting large-box edge has respectively its original small-box or
outside-graph **global label**.

The equalities compare the underlying labels in the ambient edge type, rather
than asserting an ill-typed equality of `BS.edges` and `BD.edges` subtypes. This
was the principal correction needed during coordinator verification of the
original handoff. The completed file uses default heartbeats and no additional
assumptions.

## Source-law obstruction

`largeSourceLaw_inl_inr` and `largeSourceLaw_inr_inl` are definitional: there is
no relation between the small left summand and the fresh right vertex summand.
Accordingly `no_largeSourceLaw_comap_of_identified_left_right` proves that no
setoid on any target type pulls back to this source law along a vertex map that
identifies even one such left/right pair. Reflexivity of the target setoid would
force precisely the relation the source law lacks. The conclusion needs no FK
parameters or metric hypotheses.

## Metric vertex-type obstruction

For `GO = outsideGraph BS BD`, the fresh right vertices already form a copy of
the larger box's vertex type. The module proves that the split small metric
vertices have the cardinality of the original small-box vertices and that every
such box has its centre as a vertex. Therefore a right-disjoint vertex type has
`card small + card large` elements, while the ordinary larger metric box has
only `card large`. Since the small vertex type is inhabited,
`no_metric_rightExtended_vertexEquiv` rules out an equivalence between them.

These results clarify the exact incompatibility without weakening or refuting
the accepted right-disjoint finite-volume estimates. They do not supply a new
source specification, a positive metric identification, an arbitrary nested
boundary assignment, a finite-root vanishing theorem, or a uniqueness result.
An alternate geometric construction must genuinely resolve these edge/source
and vertex obstructions.

## Verification

The repaired exact file was independently rebuilt using pinned Lean 4.35.0 with
default heartbeats. Ten principal definitions/theorems were included in a
separate expanded axiom audit; each uses only `propext`, `Classical.choice`, and
`Quot.sound`. There are no placeholders, unsafe/custom axioms, or elaboration
overrides. The full release check verifies the public module and its audits.
