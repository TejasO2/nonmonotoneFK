# Sharpness and non-vacuity of the reference AG interface

Public module: `FK.AGSharpness`. This is a comparison/dictionary and sanity
component for Theorem 1.4’s reference input, not the missing essential-
enhancement theorem or a paper's main_result.

## A single inhomogeneous Bernoulli input

`AGInput` exposes exactly the `hAG` form consumed by the q<1 upper reference
window. An increasing measurable event $A$ must remain null under a suitably
decremented product law with base strictly above $p_c$. `upperWindow_of_AGInput`
is the existing analytic reduction restated under that explicit name.

Enlarging an enhanced set preserves the input: additional decrements only
strengthen the zero-mass conclusion. Correspondingly, the star/cycle window
quantifiers are preserved under set inclusion. This shows why the maximal
device packing is the easiest one to consider, without proving it satisfies
the essential estimate.

`not_upperWindow_univ` and `not_AGInput_univ` exclude the trivial total event.
`not_AGInput_empty_percolating` shows that an enhanced empty set cannot
satisfy the input: above $p_c$ the product law percolates (using the already
proved `ReferenceBaseline` result). Hence neither trivial events nor absent
enhancement certify the interface accidentally.

## What a window conclusion forces

`exists_subcritical_decrement_of_upperWindow` extracts from `UpperWindow` a
base $b>p_c$ and a **strictly positive** decrement on `Ee` whose product law
has mass zero on $A$. The q<1 branch uses the actual parameter inverse and
the path-enhancement sign, then compares the genuine upper weights with the
decrement profile. Hence a strict enhanced nonpercolation statement is baked
into the window—it cannot be erased merely by weakening that interface.

For `1<q`, `exists_subcritical_decrement_of_upperWindow_one_lt_q` gives the
corresponding strictly positive decrement on `Eb`. This does not construct
these laws; it states what is available if the window is already supplied.

`upperWeights_indep_Eb` / `upperWindow_indep_Eb` record that, for $q\le1$,
the q-inverted upper objects do not use the star set, while the lower ones
use no cycle set (`lowerWeights_indep_Ee`, `lowerWindow_indep_Ee`). These are
literal consequences of the q≤1 parameter formula, not a relabelling of the
paper's proof. The documented device-family pairing is preserved.

## Full-device consistency checks

When every edge is enhanced, the decrement/increment profile collapses to a
homogeneous Bernoulli parameter. `AGInput_percolating_univ` chooses such a
parameter below the reference critical point and invokes
`PercolationRoot.percolation_percolating_eq_zero`, yielding
`upperWindow_percolating_univ`.
`lowerAGInput_percolating_univ` chooses a lower base still inside the
supercritical phase and invokes the independently proved infinite-cluster
full-mass result, yielding `lowerWindow_percolating_univ`.

These checked examples demonstrate that the interface and its assumptions are
inhabited for the actual percolation event on a connected locally finite
graph with critical parameter strictly between zero and one. They are not
source device packings, not an essential-enhancement proof, and not a strict
critical-point shift of the paper.

All 20 axiom reports from the independently rebuilt exact source contain only
`propext`, `Classical.choice`, and `Quot.sound`; only standard foundational
axioms are needed. Warnings are deprecation lints.
