# Actual AG profile-mass derivatives and the interior trade repair

Public module: `FK.AGMassDerivative` (namespace of the same name). It connects
the clamped reference masses of `FK.AGDifferentialShift` to
`FK.MargulisRussoFinite`. It is not an essential-enhancement theorem or a strict
critical-point shift.

## Product-polynomial and pivotal formulas

For finite edge types, `bernoulliProduct_eq_pi` identifies the real infinite
product law with the finite `Measure.pi` product, hence `mass_eq_eventWeight`
and `incMass_eq_eventWeight` identify the actual clamped masses with the
product polynomial, not with a surrogate expectation.

For an increasing event in the clamp-free interior, the Fréchet derivatives in
the decrement and increment planes are the Margulis–Russo coordinate
derivatives. In particular, `massPair_deriv_decomp` gives, in direction
$(u,v)$, the functional

$$u\,P_{\mathrm{total}}-v\,P_{\mathrm{on}},$$

and the increment analogue gives $u\,P_{\mathrm{total}}+v\,P_{\mathrm{on}}$.
Here $P_{\mathrm{total}}$ is the sum of off-configuration pivotal weights and
$P_{\mathrm{on}}$ is the sum on the selected enhancement set. The proof uses an
inhomogeneous one-coordinate MR identity and differentiates the full finite
product before summing; it does not assume that the desired trade sign holds.

`mass_eq_mass_restrict`, `incMass_eq_incMass_restrict` and their derivative
analogues extend these results to events depending on a finite support on an
arbitrary edge type. Their pivotal sums live on that support. They do not claim
an identification with any infinite `E`-indexed sum.

## Why the older closed-region derivative binder is unsatisfiable

The clamped coordinate weights are affine near a point only away from clamp
collisions. `mass_unitOpenEvent` computes the one-edge open-event mass exactly,
and `not_hasFDerivAt_massPair_clamp` differentiates along the collision line at
$(1/2,1/2)$. Along $(1/2+t,1/2-t)$ the mass becomes
$\max(0,2t)=t+|t|$, so no Fréchet derivative exists there.

Thus the previous requirement of differentiability throughout
$0\le\varepsilon\le b\le1$ cannot be discharged for the actual clamped mass.
That is a defect in an auxiliary reduction, not in the source paper.
`exists_subcritical_decrement_interior` and
`exists_supercritical_increment_interior` repair the mean-value argument by
asking for derivatives and trade signs only on the open region actually used,
while proving continuity of the actual profiles along the entire trade line.

## Conditional window reduction, not the AG theorem

`decrement_AGInput_of_pivotTrade` and its increment companion discharge the
interior derivative inputs when supplied the geometric pivot inequality
$cP_{\mathrm{total}}\le P_{\mathrm{on}}$. The four
`*Window_of_pivotTrade_*` wrappers then produce the existing upper/lower
window predicates for both signs of $q-1$. This removes a boundary-
differentiability obstacle and an auxiliary analytic premise; it does not
construct essential-device geometry.

Still explicit are:

* the real uniform pivot trade inequality `hpivot` for the enhanced devices;
* the nonpercolating/percolating baseline `hbase`, including `incMass=1` in
  the ordinary supercritical class; and
* finite-approximation convergence `hconv` on the intended arm events.

`pivotTrade_obstruction_empty` shows that the pivot inequality fails without
geometric content, while the empty/full-event instances merely check logical
consistency and say nothing about criticality. No `hAG`, Theorem 1.4, Theorem
1.10 or Theorem 1.11 conclusion follows directly.

The complete source and 51 principal axiom reports were independently rebuilt
under pinned Lean 4.35.0 at default heartbeats. Only the standard foundational
axioms occur; the only warning is an unused-binder linter message.
