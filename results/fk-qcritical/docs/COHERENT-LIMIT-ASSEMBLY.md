# Weak-limit assembly by normalized binary mixtures

`CoherentLimitAssembly.lean` adds the analytic weak-convergence step missing
from convexity of an already specified limiting DLR class.

## Actual weak convergence and marginals

`tendsto_convexCombination` proves weak convergence of normalized binary convex
combinations of two probability-measure nets to the same convex combination of
their limits. The proof uses bounded continuous integrals and the exact linearity
of the mixture; the weight is fixed along each net. No compactness, tightness,
subsequence, or nontrivial-filter assumption is introduced.

`exteriorMeasure_convexCombination` identifies the exterior marginal of the
mixed law with exactly the same mixture of the exterior marginals.
`ae_convexCombination`, `ae_globalAtMostOne_convexCombination`, and
`aeAtMostOne_convexCombination` propagate a common almost-everywhere property,
global at-most-one-cluster uniqueness, and boxwise exterior uniqueness to the
mixed law.

## DLR and Gibbs assembly

For two DLR nets on one fixed specification,
`tendsto_and_mem_dlrMeasures_convexCombination` combines genuine weak
convergence of the mixed net, eventual DLR membership from mixture convexity,
and the exact mixed exterior law to establish DLR closure. Local constancy is
required at both component limits.

For two genuinely varying boundary assignments,
`tendsto_and_mem_dlrMeasures_convexCombination_of_locallyStabilizes` uses their
own smaller-box DLR equations and joint stabilization to a common target.
Every displayed source DLR, stabilization, and component-limit local-constancy
hypothesis is retained.

The conditional-law and closed-exterior `finiteVolumeLaw` versions construct an
explicit mixed weak limit from two potentially distinct coherent sources.
Componentwise `GlobalAtMostOne` and both source/target geometry certificates
transport both limits to any geometric target, and convexity assembles the
mixed limit's target Gibbs membership. Parameters range over $0<q$ and $p\le1$.

These results do not assert unrestricted noncoherent DLR membership, construct a
weak limit from compactness, make an infinite kernel mixture converge, prove
DLR uniqueness, or infer component uniqueness from the mixture. They remain
scoped assembly and closure theorems.

## Verification

The exact source was independently rebuilt with Lean 4.35.0 and default
heartbeats. Its nine principal audits passed the repository's allowed-axiom
script using only `propext`, `Classical.choice`, and `Quot.sound`. The public
release check repeats compilation, all audits, documentation checks, and the
forbidden-declaration scan.
