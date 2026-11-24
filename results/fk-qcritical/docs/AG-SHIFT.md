# Conditional activation and deactivation shifts

Public module: `FK.AGShift`. This reformulates critical-window inputs for
inhomogeneous Bernoulli products and supplies conditional reductions. It does
not prove a strict critical shift or Theorem 1.4.

Clamped weight profiles express independent activation, deactivation and
constant increment/decrement profiles. `ActivationShift` and
`DeactivationShift` state the corresponding strict window conclusions for a
measurable increasing event. Monotonicity in the enhanced set is proved.
`hAGlower_of_activationShift` / `activationShift_of_hAGlower`, and their upper
analogues, establish exact equivalences with the existing window hypotheses.
The four parameter-window adapters and the extended-phase consequences follow
without hiding those hypotheses.

`PaperGraphHypotheses` records graph hypotheses at paper scope; the
`theorem_1_4_of_shifts_*` results keep both that input, the Proposition 4.2
comparison and the required two shift inputs explicit. The names are therefore
conditional reductions, not completed theorem declarations.

The root part proves disjoint-coordinate independence for an inhomogeneous
product and Kolmogorov zero–one for existence of an infinite cluster. Hence
the root-level `RootShift` implies activation shift for the existence event.
The converse, requiring root independence, is not claimed.

For terminology see [Balister–Bollobás–Riordan, *Essential enhancements
revisited*, arXiv:1402.0834](https://arxiv.org/abs/1402.0834). This machine-
checked interface does not establish that general enhancement conjecture or
settle its literature status. The essential-enhancement question remains.
