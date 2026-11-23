# Errata, corrections, and representation choices

## Source

The comparison source is arXiv:2512.16486v1, dated 18 December 2025.
This file records known formalization repairs and intentional representation
choices. It does not currently record a mathematical error in the paper itself.

## Repairs within this formalization

### Bernoulli coordinate convention

`bernoulliMeasure true false (r e)` assigns `true` probability `r e`. Earlier
uses of `bernoulliMeasure false true` in the phase API accidentally made the
closed/open polarities complementary. The corrected declarations are tested
by `FK.Phases.bernoulliProduct_apply_open` and
`FK.Phases.bernoulliProduct_apply_closed` in `FK/PhasesCoordinate.lean`.
Do not reverse those coordinates when refactoring.

### Stochastic order and new versus legacy APIs

`FKLimit.StochasticallyDominates ν μ` means that ν dominates μ: for measurable
`A` satisfying `IsUpperSet A`, `μ A ≤ ν A`.

The original names `FKLimit.proposition_4_2_lt_of_finite_comparisons` and
`FKLimit.proposition_4_2_gt_of_finite_comparisons` have the opposite-sandwich
shape from the intended application. They remain only for compatibility and
carry warning docstrings. Use `FK.MainIntegration.proposition_4_2_*_of_oriented_limit`
and the corresponding real-event and class-level bridges.

### Generic projection lemmas

`OpenPath.FinProb.prod_map_fst` and `prod_map_snd` live in
`FK/JointProductInvariance.lean`, at the first common dependency of their
consumers. Earlier duplicate declarations in path/cutset modules conflicted
when both were imported by the same root. The statements have one canonical
implementation now; this repair changes no mathematical content.

## Representation choices and scope

### Discrete-time skeleton instead of continuous trajectories

The paper describes independent exponential edge clocks and their simultaneous
uniform update variables. The proofs here work with the finite Glauber jump
kernel `Glauber.modifiedJump`, indexed by a finite positive clock law and a
schedule that visits every edge. This supplies the convergence in distribution
needed for the comparisons; it does not claim a complete construction of the
continuous-time trajectories or their exponential random variables.

The stationary ordered outer pair is used as the initial law in the new
closed-cutset proofs. Ordinary FK starts at its relevant ordinary marginal and
converges by the arbitrary-initial-law FK convergence theorem. This avoids having
to prove convergence for the singular ordered-pair chain, not bypassing it with
an unsupported full-support assumption.

### Finite multigraphs and boundary setoids

The finite model uses finite vertex and labelled edge types, directed endpoint
assignments with an undirected `Joins` relation, and setoid boundary conditions.
This retains loops, parallel labels, and quotient wiring. The directed endpoint
presentation does not orient FK connectivity.

The theorems sometimes extend to degenerate configurations outside the paper's
nondegeneracy hypotheses. Those additional degenerate cases should not be
equated with the paper's positive-enhancement conclusions.

### General and scoped results

Arbitrary abstract-planar identities are not claimed when only forest Euler
identities, one-loop duals, or labelled cycles are proved. The term "actual"
means that the finite statement uses the normalized FK PMF on an explicit graph,
not that every planar or infinite-volume application has been established.

Similarly, a finite enhanced comparison for arbitrary `FinProb` clocks does not
by itself imply the full FK measure union statement. Transport to actual
measures, weak limits, and DLR kernels has to be checked in the corresponding
Lean declaration.

### Essential enhancements and cited inputs

The paper cites Aizenman–Grimmett essential-enhancement theory for the strict
reference-percolation shift. That mathematical input remains explicit as `hAG`
in `FK/AGWindow.lean`; an analytic window wrapper with argument `hAG` is **not**
an unconditional proof of Theorem 1.4. Device packing and continuity are real
proved components, but they do not supply the AG theorem.

### Noncoherent boundary limits and finite-box scope

`FK/NoncoherentCounterexample.lean` proves that the unrestricted implication
from an arbitrary-boundary `IsFKLimit` with global at-most-one uniqueness to
DLR membership under any geometric assignment is false. On the complete graph
with two vertices, the constant fully wired finite-volume sequence has an
all-open mass of $1/2$ at $q=2$, $p=1/2$, but the canonical free DLR law has
mass $1/3$. Every geometric DLR class is excluded by the exhaustive-box and
convention-transport arguments.

This counterexample concerns a **finite** graph. The source's specification
section begins with an infinite, connected, locally finite graph, so it does
not establish a mathematical error in Proposition 1.8. It is an obstruction to
deleting all geometric/coherent hypotheses in the current API. If the broad
union of FK limit and Gibbs classes is completed, their precise source-domain
and coherence restrictions must be preserved. The conditional
`NoncoherentStabilization` machinery deliberately retains those inputs.

### General tools assumed from Mathlib

Measure-theoretic and probability tools used from Mathlib carry their own
hypotheses and do not amount to a reference implementation of reverse
martingale convergence or Choquet decomposition. In particular,
the older `measure_eq_of_backwardConditionalLimits_of_extremal_dlr` still
requires conditional-limit sequence inputs. The new `FK.BackwardConditional`
module proves downward projection/$L^1$ convergence for $L^2$ observables and
the stronger `measure_eq_of_eventualOutsideAgreement_of_extremal_dlr` interface;
it still requires eventual agreement of the actual exterior conditional
probabilities, not a superseded identity declared as a hypothesis.

If later development uncovers a source error, record here the exact page,
statement, affected Lean declaration, and the repair. Keep formalization bugs
separate from errors attributed to the paper.

## Bare combinatorial dual nonpercolation is insufficient

`FK.OpenCutSeparation` reduces the useful cluster-count step to explicit finite
open connected cuts. `FK.StripDualCounterexample` shows that
`DualNonpercolationForcesPrimalAtMostOne` is false as an unconstrained property
of two graphs related by an arbitrary edge equivalence. Its strip's face-index
dual is not locally finite: the outer face has infinitely many neighbours.
A locally finite self-pairing gives the second refutation. These are restrictions
on the repository's bare target, not counterexamples to the paper's Theorem 1.11,
which assumes a genuine plane dual with local finiteness and geometric
separation. New constructions must retain those geometric hypotheses rather
than merely product-edge complementation.
