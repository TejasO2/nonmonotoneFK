# A conditional net-convergence comparison for random regions

Public module: `FK.RandomRegionConvergence`. This module compares probability
measures on the actual exterior configuration space along
configuration-dependent finite regions, but **does not prove the analytic net
convergence it requires**. It is a reduction, not a completion of Theorem 5.1
or Proposition 1.8(2).

## The genuinely uniform $L^1$ estimate

For a probability law $\mu$ on `Configuration E` and a measurable $A$, enlarging
the excluded edge set makes the exterior filtration smaller. The tower property
and conditional-expectation contraction therefore give

$$
\|\delta_S\|_1\le\|\delta_K\|_1,\qquad K\subseteq S,
$$

where
$\delta_S=\mu[A\mid\mathcal F_{S^c}]-\mu[A\mid\mathcal F_\infty]$.
The existing reverse-martingale convergence along *one* finite cofinal family
supplies a threshold $K$ for each $\varepsilon>0$ such that this is at most
$\varepsilon$ for **every** finite $S$ containing $K$. Two such regions differ by
at most $2\varepsilon$ in the $L^1$ metric. This is a genuine region-uniform
estimate; unlike net almost-everywhere convergence, no tail-triviality is used.

## The analytic input and its random-region use

The comparison deliberately assumes

```
HasNetExteriorConvergence μ A
```

which means that, off one $\mu$-null set,

$$
\forall\varepsilon>0\ \exists K\ \forall S\supseteq K:\quad
 \left|\mu[A\mid\mathcal F_{S^c}]\bigl(\omega\bigr)-\mu(A)\right|\le\varepsilon.
$$

`tendsto_of_net_exterior` carries such a statement along any monotone cofinal
family of finite edge sets. That family may vary with the auxiliary
configuration. The one exceptional set for a particular $(\mu,A)$ is pushed
forward by either coupling coordinate, so each probe supplies both coupled
convergences; eventual agreement at the coupled points then forces equal masses
of $A$. Doing this for every Boolean cylinder yields
`measure_eq_of_netExteriorConvergence`.

The input `HasNetExteriorConvergence` is an additional analytic hypothesis,
not a theorem from tail triviality alone. An independent-region comparison whose
fixed-region tail estimate yields mean convergence is now supplied by
`FK.RandomRegionL1Repair`. Countably many exhaustions also share one joint null
set via `FK.NetExhaustions`. A full directed-index upcrossing theorem is not
included, and countable-family coverage of the net property is not produced.

## Counterexamples to shortcuts, not to the source

The diagonal of normalized Lebesgue measure on $[0,1]$ is applied correctly.
`exists_probability_nullSections_fullDiagonal` proves that every vertical
section is null and hence $\pi_1\pi_2$-measure of the diagonal is zero under
independent product measure, while its diagonal self-coupling has measure one.
Consequently arbitrary marginal probabilities do not transfer a convergence
exceptional set to coupled points. This is not a counterexample to the actual
comparison, whose `HasNetExteriorConvergence` supplies one fixed exceptional
set independently of the coupling.

The finite atomic example `exists_directed_maximal_inequality_failure` uses
counting measure on `Fin k → Bool`: for each point it constructs a two-element
atom with conditional value $1/2$ for the singleton event at top, whose mass
under counting measure is $1$. This cautions against using a per-region Markov
bound as a complete net-maximal argument. The formal result does **not** state
that every conditional value in the construction is at most $1/2$, nor does it
prove the normalization-to-probability claims described in the worker report.
No general failure of net martingale convergence is inferred.

## Residual obligations

Prove the net upcrossing theorem, instantiate the actual geometric region
construction, and supply the eventual local-conditional comparison from its DLR
factors. Those steps, not reduction naming or the artifact of a coupling's
choice, remain necessary for Theorem 5.1 and Proposition 1.8(2).

## Verification

The revised exact submission was independently rebuilt and its 23 unique
principal axiom audits checked against public imports with Lean 4.35/default
heartbeats. Public commentary has additionally been corrected to preserve these
formal bounds. `Audit.lean` includes all 23 declarations; only standard axioms
are used. The full `./check.sh` validates this integration.
