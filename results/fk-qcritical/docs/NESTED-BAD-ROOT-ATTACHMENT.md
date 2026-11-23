# Bad-only attachment and finite-root metric estimates

## Proved geometry and locality

`NestedBadRootAttachment.lean` first proves that open connection in the all-closed
configuration implies endpoint equality. Consequently, if the original
root-attachment condition is imposed for **every** configuration of a fixed
split, every left endpoint already has to belong to the root finset. This is an
exact obstruction to that overly strong premise, not a counterexample to the
finite-volume estimate.

The usable refinement `bad_maximalSplit_subset_closedLocalEvent_finiteRootArms_of_bad`
requires attachment only for configurations outside the maximal split stratum.
It preserves the supplied global graph, nested labels, endpoint identity,
bounded root radius, and separation of the right vertices. The all-closed nested
configuration is proved to be in the maximal stratum under the established
right-exterior condition, so it is not subjected to the attachment request.

The explicit finite support `finiteRootArmEdges` is the union of radius-$n$
metric supports around the roots. If all roots lie within distance $L$ of $o$,
that support lies in the metric box of radius $n+L$ about $o$. The module proves
finite-coordinate dependence, this metric-box localization, enlargement to any
containing observation box, and exact realization by closing the box exterior.

## Conditional probability estimates

`finiteBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad` and its centered
specialization `metricBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad`
bound an actual normalized FK cylinder difference by the upper-Bernoulli law of
the simultaneous finite-root arm event. The larger centered box has scale $N$,
the smaller has scale $r\le N$, and $n+L\le N$ supplies coordinate dependence.
The estimate discharges the geometric exceptional-set inclusion and locality;
it retains the exact coupled `hgood`, bad-configuration attachment, right-endpoint
and metric-separation hypotheses.

The fixed-root event can be combined with an established nonpercolation-vanishing
theorem when its hypotheses are met. This module does **not** prove that vanishing
under arbitrary geometry, identify a random exploration region with an FK box,
construct `hgood`, or conclude DLR/strong uniqueness. In particular it does not
revive the Hasse-path whole-ball argument refuted in
`NestedRadialCounterexample`.

## Verification

The exact 420-line candidate was independently compiled with pinned Lean
4.35.0 and default heartbeats. Its twelve principal definitions/theorems were
audited independently; every report uses only `propext`, `Classical.choice`, and
`Quot.sound`. No placeholder, custom axiom, unsafe declaration, or elaboration
override was introduced. The public release import and audits are checked by
the complete project release script.
