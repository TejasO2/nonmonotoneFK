# The reference Bernoulli phase and supercritical baseline

Public modules: `FK.ReferenceBaseline` (namespace of the same name) and
`FK.ReferenceBaselinePercolating`. These concern the ordinary independent bond
model from which the reference AG enhancement starts, not the non-Bernoulli FK
measures at $q<1$.

## Above the root critical parameter

Let $\theta_o(p)$ be the product-law probability that $o$'s open cluster is
infinite. By definition of `criticalProb G o`, if $p$ is larger, $\theta_o(p)$
cannot vanish: no monotonicity in $p$ is used in this step. The same root cluster
is included in `ClusterCover.HasInfiniteCluster`, so that event has positive
probability. The already proved product-tail zero–one law upgrades it to full
mass:

$$p>p_c\Longrightarrow
  \mathbb P_p(\text{some open cluster is infinite})=1.$$

This key statement needs no connectedness, quasi-transitivity or sharpness
theorem. `percolation_nonPercolating_eq_zero_of_criticalProb_lt` gives the
complementary `NonPercolating` presentation, and the two ae lemmas express it
with almost-everywhere quantifiers.

## Event and root conventions

`clusterCriticalProb` uses the whole existence event as a supremum of
zero-mass parameters. The event-based supercritical statement holds without
connectivity. Monotonicity in the product parameter and the definition of the
supremum supply the zero-mass phase below it. The countable union of root events
identifies null existence with `∀ x, θ_x(p)=0`.

A separate force-one-edge-open argument proves the exact single-coordinate
factorization behind $p\theta_y(p)\le\theta_x(p)$ for adjacent $x,y$. At $p>0$,
percolation positivity is therefore constant along graph reachability. On a
connected graph, this equality identifies `clusterCriticalProb G` with
`criticalProb G o`; the resulting zero/one dichotomy away from criticality is
`percolation_hasInfiniteCluster_eq_one_iff_of_ne`. The critical case $p=p_c$ is
not decided.

For the zero enhanced parameter, `incMass_hasInfiniteCluster_eq_one` identifies
the profile with the ordinary supercritical product. More generally, clean
increment weights are pointwise above the clean unenhanced law, while increasing
percolation events preserve mass one. Hence
`incMass_hasInfiniteCluster_eq_one_of_nonneg` proves

$$\operatorname{incMass}(A,S,a,\varepsilon)=1
  \qquad(a>p_c,\ \varepsilon\ge0,\ a+\varepsilon\le1).$$

with $A$ the actual infinite-cluster event, not a convenient substitute. The
corresponding decreasing-profile subcritical comparison is
`mass_hasInfiniteCluster_eq_zero`.

The companion `FK.SubcriticalBaseline` proves
`Percolating G = HasInfiniteCluster`. `ReferenceBaselinePercolating` uses this
already verified equality to export `percolation_percolating_eq_one` and
`incMass_percolating_eq_one`, so the supercritical baseline is also available
in the event presentation consumed by the reference windows.

## Residual AG inputs

The two included $q<1$ window wrappers only remove the ordinary reference
baseline. They still contain the older full-domain derivative hypothesis and the
geometric trade/convergence inputs. The compact-window repair now requires
approximation-index-uniform pivot trade data instead. None of those geometric or
essential-enhancement steps is proved here, and there is no strict critical
shift, FK/DLR statement, Theorem 1.4, 1.10 or 1.11 claim.

All exact sources were independently rebuilt under pinned Lean 4.35.0 with
default heartbeats. The 43 principal audits (41 submitted plus two adapters)
contain only `propext`, `Classical.choice`, and `Quot.sound`.
