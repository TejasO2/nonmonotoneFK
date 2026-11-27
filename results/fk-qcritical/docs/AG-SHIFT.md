# Conditional activation and deactivation shifts

Public modules: `FK.AGShift` and `FK.AGSourceHypotheses`. These reformulate
critical-window inputs for inhomogeneous Bernoulli products and supply
conditional reductions. They do not prove a strict critical shift or Theorem 1.4.

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

## Source graph hypotheses

`FK.AGSourceHypotheses` proves `criticalProb_pos_of_quasiTransitive` from a
uniform vertex-degree bound and the established first-moment path-counting
argument. It then constructs `PaperGraphHypotheses.of_source` from the graph
assumptions stated in Theorem 1.4. Thus $0\lt p_c$ is a proved consequence,
not an extra assumption. The required two strict shift inputs remain open.

The external literature does not discharge those shifts automatically.
Balister–Bollobás–Riordan identify a false combinatorial rerouting step in the
original Aizenman–Grimmett argument, prove bond percolation on $\mathbb Z^d$,
and explicitly leave the general assertion open. Tomar's later work resolves
site percolation on $\mathbb Z^d$ in every dimension and on designated
periodic lattices, plus bond percolation on honeycomb, but not arbitrary
quasi-transitive bond profiles. Consequently a source-faithful completion
cannot merely cite either general enhancement framework.

For terminology see [Balister–Bollobás–Riordan, *Essential enhancements
revisited*, arXiv:1402.0834](https://arxiv.org/abs/1402.0834). This machine-
checked interface does not establish that general enhancement conjecture or
settle its literature status. The essential-enhancement question remains.
