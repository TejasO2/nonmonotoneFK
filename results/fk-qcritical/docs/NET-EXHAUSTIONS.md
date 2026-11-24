# Simultaneous convergence on countably many exhaustions

Public module: `FK.NetExhaustions`.

`FKLimit.tendsto_ae_condExp_indicator_outside_to_tail_all_exhaustions` states
that, for any family $\{\Lambda_k\}_{k:\mathbb N}$ of monotone cofinal
exhaustions of the countable edge type, one joint $\mu$-null set outside which
all exterior conditional probabilities of the event $A$ converge to their tail
conditional. The proof is the simultaneous intersection of the genuine reverse
chain results available in `FK.ReverseMartingale`.

The tail-trivial specialization
`tendsto_ae_condExp_indicator_outside_to_real_all_exhaustions` gives the same
countably-simultaneous convergence to $\mu(A)$.

## Conditional net coverage

`hasNetExteriorConvergence_of_countable_exhaustions` also isolates the precise
conditional implication: if for every point either its net error is bounded by
an explicit threshold, or one of the countable chains fails to converge, then
the good countable simultaneous set forces the lettered net-error property.
This does *not* construct the arbitrary net-error threshold or prove it from
tail triviality.

The source-facing predicate `HasNetExteriorConvergence` targets $\mu(A)$ provided
tail triviality holds. These lemmas therefore complement, rather than replace,
that named assumption. Reverse-chain convergence on a countable list is not an
instruction to add new maximal-inequality assumptions.

## Open residual

The actual configuration-dependent coupling, its eventual local-conditional
identities and the direct or independent mean-convergence step required by
Theorem 5.1 remain separate. The long counterexample in the work report is
explicitly not present as Lean code and is not claimed as a verified project
result.

## Verification

The exact import was rebuilt against the public `FKLimit` and
`FK.RandomRegionConvergence` modules at Lean 4.35/default heartbeats. Three
principal proofs are included in `Audit.lean`; each reports only
`propext`, `Classical.choice`, and `Quot.sound`. Run `./check.sh`.
