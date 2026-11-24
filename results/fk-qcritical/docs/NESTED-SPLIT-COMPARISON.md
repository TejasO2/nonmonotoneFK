# Fixed shell-first nested comparison

Public module: `FK.NestedSplitComparison`. This is a finite shell-first
coupling estimate and its ordered triple, not the paper's Lemma 2.1 or its
vanishing equation-(9) error.

For a split-shell graph with arbitrary boundary setoids, `AddedAvoid`,
`ExteriorHasRight` and positive interior FK parameters, the additional-label
extension and Bernoulli splitting lemmas compose with the existing
`good_intersection_annFirstPairs`. The resulting
`split_equation_nine_region` bounds the difference of larger/smaller FK masses
of any region-supported event by the upper-Bernoulli probability of **failure
of shell separation**. The proof supplies the pair equality from the shell
library, so no additional `hgood` input appears at this level.

`leibnizTriple` constructs a coupled FK/FK/Bernoulli triple with its two FK
coordinates below the third. Its second marginal restricted to the smaller
configuration is exactly the smaller FK law, and the same error estimate holds
through the triple. Free-boundary and superset-error corollaries are included.

## Scope limit

In an ordinary fixed-box instantiation the error says some open shell label
touches the selected region. This is a fixed boundary error, normally not the
far-connection arm and generally does **not** vanish as the outer boxes grow.
Calling this the completed equation (9), or turning its error into a
subcritical arm probability without constructing that inclusion, would be
incorrect.

Likewise the graphs are presented in the shell-first exploration order, not
yet transported to the actual nested metric boxes with their boundary
assignments. The adaptive maximal-closed-cutset exploration, its FK marginal
law and free interior continuation remain separate obligations. The report's
analysis of why that adaptive construction is needed is not a formal
impossibility theorem.
