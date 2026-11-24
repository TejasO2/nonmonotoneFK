# Mean convergence for random-region comparisons

Public module: `FK.RandomRegionL1Repair`. This is proved against the actual
`FKLimit` exterior algebras, not a vocabulary copy. It replaces a pointwise net
assumption with the weaker mean convergence that the random-region comparison
actually uses.

## Comparison at coupled points

Suppose $f_n$ and $g_n$ are two $[0,1]$-valued processes whose $L^1$ errors from
constants $c$ and $d$ converge to zero. Then $\mathbb E[f_n]\to c$ and
$\mathbb E[g_n]\to d$. If furthermore $f_n=g_n$ eventually almost everywhere,
uniform boundedness gives $\mathbb E[f_n-g_n]\to0$. Hence $c=d$.

This is `real_eq_real_of_tendsto_integral_abs` and its explicit FK formulation.
No pointwise directed-net convergence or null-set intersection is needed.
Conditional probabilities supply the uniform bound $[0,1]$ used by dominant
convergence and by pointwise zero-integrability.

## From the uniform tail estimate to mean convergence

The already-installed exterior remainder is uniform over regions containing $K$.
After choosing a tail threshold, every monotone cofinal indexed family admits an
integral-abs-error tending to zero. `tendsto_integral_abs_of_uniform` expresses
that directly. `integral_abs_le_of_eLpNorm_le` connects this to the actual
`eLpNorm` proof carefully, with the current Lean 4.35 measurability argument.

Tail triviality replaces the tail conditional by $\mu(A)$, so the corresponding
coupling input becomes the mean of the conditional at the coupled points rather
than a strong index-net statement. A fixed cofinal family only needs map
integrals and the comparison argument, under clear hypotheses.

## Independent region parameter

For a product auxiliary law $\rho_3\otimes\rho_1$, with the region chosen from
$z_3$ and the sampled configuration from $z_1$, Fubini reduces the coupled mean
to the integral of the pointwise-uniform $L^1$ estimate:

$$
\int_{z_3}\left(\int_\omega
 |\mu[A\mid\mathcal F_{S_n(z_3)^c}]\bigl(\omega\bigr)-\mu(A)|\,d\mu
 \right)d\rho_3.
$$

Independence of the coupled configuration from the region and the separate
marginal mappings are essential; no arbitrary coupling or simultaneous null set
follows. The measurability and domination conditions remain explicit in
`tendsto_integral_abs_coupled_prod` and `real_eq_real_of_prodRegionAgreement`.

The accompanying worker report discusses oscillating net conditionals, but
those examples are not included here as verified Lean code and are not part of
this module's claim. `HasNetExteriorConvergence` remains a separate strong
hypothesis. Nothing here is a martingale upcrossing theorem or a full Theorem
5.1 result. The actual ordered coupling and its local random-box identities
must be supplied by the geometric construction.

## Verification

The worker's standalone file was API-repaired by the coordinator. A heartbeat
override was removed, deprecated coordinate and norm-integral API was updated,
and it was compiled under default heartbeats with all eight principal
declarations audited. Replacing its duplicated type vocabulary with actual
`FKLimit` definitions and `FK.RandomRegionConvergence` yielded the same eight
standard-axiom proofs. Run `./check.sh`.
