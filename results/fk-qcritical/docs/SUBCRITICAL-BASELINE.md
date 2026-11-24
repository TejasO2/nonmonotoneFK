# Bernoulli root independence and the subcritical reference baseline

Public module: `FK.SubcriticalBaseline` (namespace `FK.PercolationRoot`).
It proves a genuine product-measure phase fact needed by the reference AG
reduction, not an FK theorem or an essential-enhancement result.

## A finite-energy argument along a walk

For a fixed walk $\pi$ from $o$ to $x$, `Cluster.measure_infiniteCluster_mul_le`
proves

$$\theta_x(p)\,p^{|\pi|}\le\theta_o(p).$$

The proof forces exactly the edges of $\pi$ open. The walk-open cylinder and the
forced preimage of the infinite-cluster event depend on disjoint coordinate
sets, so independence factors their intersection exactly. On the walk-open
cylinder, forcing is the identity. This establishes `percolationProb_mul_le`
without invoking Harris/FKG or hiding a correlation premise.

At $p>0$, zero probability at one root therefore implies zero at every root.
The $p=0$ case is proved separately: the independent product is almost surely
all closed, and every open cluster is a singleton. Consequently
`criticalProb_eq_of_connected` shows that `criticalProb G o` is independent of
$o$ on a connected locally finite graph.

`percolating_measure_eq_one_iff_percolationProb_pos` also gives a global
zero–one dichotomy: the existence of some infinite cluster has full mass iff the
percolation probability at one root is nonzero. Root-independent zero probability
gives the null direction; the already verified `ClusterTail` zero–one law gives
the other. This dichotomy does not itself prove the supercritical baseline.

## Actual subcritical mass

At zero enhancement, `mass_zero_eq_percolation` identifies the clamped decrement
profile with the homogeneous Bernoulli product. Root independence extends the
existing below-critical statement at one root to every root, so

$$\mathbb P_b(\mathrm{Percolating}\;G)=0
  \qquad(0\le b<p_c(G)).$$

`mass_percolating_eq_zero` and `incMass_percolating_eq_zero` state this for the
actual `FK.EssentialWindow.Percolating G` mass used by the analytic reference
reduction. The event is existence of an infinite open cluster, not a fixed-root
arm. This discharges the subcritical reference `hbase` at a single root.

Single-root convenience versions of ae-nonpercolation and domination transfer
are included. `exists_subcritical_decrement_percolating` packages the baseline
into the older derivative wrapper, whose full-domain differentiability premise
is separately known to be unsatisfiable at clamp collisions; it is not an
instantiable AG proof.

Still unproved elsewhere are $a>p_c\Rightarrow\operatorname{incMass}=1$, the
uniform-in-approximation window pivot trade, arm-event convergence, and the
essential-enhancement strict reference shift. No Theorem 1.4, 1.9, 1.10, 1.11
or 5.1 follows from this phase fact alone.

The exact source and its 18 principal axiom reports were independently checked
with pinned Lean 4.35.0 at default heartbeats. Only `propext`,
`Classical.choice`, and `Quot.sound` occur.
