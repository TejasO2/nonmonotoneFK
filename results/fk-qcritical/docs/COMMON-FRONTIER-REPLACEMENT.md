# Common DLR and frontier replacement criteria

`FK.CommonFrontierReplacement` is an exact obstruction diagnosis for the
general arbitrary-dominant uniqueness problem. It does **not** prove or refute
Theorem 5.1. In particular, it supplies neither a replacement law nor any
unit-total normalization for an arbitrary common dominant.

## Frontier minorisation already forces equality

For two canonical-region DLR laws $\mu,\kappa$ with their explicit
finite-region-on-finite-bases hypotheses, suppose every closed-frontier mass
at a finite base $s$ satisfies $\mu(\partial s\text{ closed})\le
\kappa(\partial s\text{ closed})$. The theorem

```lean
frontier_mass_eq_of_frontier_mass_le
```

proves equality at every base, and `eq_of_frontier_mass_le` then gives
$\mu=\kappa$. The finite-base region series has unit total on both sides and
the inequality is termwise; a finite-total series equality forces equality of
the term at the base itself. These hypotheses can be used for each DLR law
separately, so no global stochastic order is asserted.

Consequently `eq_iff_exists_common_frontier_minorant` proves that a common
canonical-DLR finite-base lower bound on all closed-frontier masses for two
candidates exists **if and only if the candidates are already equal**. The
reverse implication simply chooses their common value.

## A common DLR upper replacement is equally strong

For one geometric source convention, `eq_iff_exists_common_sourceDLR_dominant`
also gives an exact biconditional: a nonpercolating source-DLR law dominating
two nonpercolating candidates exists precisely when those candidates coincide.
The forward implication is two applications of the accepted comparable-law
uniqueness theorem; the converse is the common value.

The wrapper
`eq_iff_exists_common_sourceDLR_dominant_of_nonPercolating_upper` starts from
the exact arbitrary-upper setting: an arbitrary probability law $\rho$,
nonpercolating and above both candidates, with no DLR, unit-stratum-total,
independence or normalization assumption on $\rho$. Nonpercolation passes down
to the candidates, after which the same biconditional applies.

Thus dominated compactness, barycentre closure, or a generic series argument
cannot provide the requisite replacement without another local/adaptive
marginal theorem. This result does not prove that such a theorem fails. It
also does not construct a common DLR law $\kappa$, common frontier masses,
unit totals, or a random-filtration reverse-martingale argument.

The complete source was independently rebuilt with Lean 4.35/default
heartbeats; all five audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
