# Conditionally independent ordered couplings and a uniform upcrossing bound

Public modules: `FK.ConditionallyIndependentOrderedCoupling` (namespace
`FKLimit`, imported through `FK.StrassenCountable`) and `FK.UniformUpcrossing`
(namespace `FK`, imported through `FK.ReverseMartingale`). These are tools for
the proof of Theorem 5.1 of Beffara–Faipeur–Oke, arXiv:2512.16486v1, not that
theorem or a strong-uniqueness result.

## Ordered fibre product

For a countable coordinate type `E`, let configurations be `E → Bool` with
their pointwise order. If both probability measures $\mu_1,\mu_2$ are
stochastically dominated by a probability measure $\rho$ on increasing
measurable events, `exists_condIndepOrderedTriple` constructs a probability
law $\gamma$ on triples $(\omega_1,\omega_2,\eta)$ and two Markov kernels
$K_1,K_2$ such that:

* the three marginals are exactly $\mu_1$, $\mu_2$ and $\rho$;
* $\omega_1\le\eta$ and $\omega_2\le\eta$ hold $\gamma$-almost surely;
* $K_i(\eta)$ has full mass on the lower cone $\{\xi\mid \xi\le\eta\}$ for
  $\rho$-almost every $\eta$; and
* $\gamma$ is the pushforward of $\rho\otimes_m(K_1\times_k K_2)$ obtained by
  putting $\eta$ in the third coordinate.

The construction first applies `CountableStrassen` separately to $(\mu_i,\rho)$,
swaps the dominating coordinate to the front and uses `Measure.condKernel` to
disintegrate each ordered pair. The two fibres are combined with a product
kernel; no optimization over joint couplings is required.

`condIndepTripleLaw_fst`, `condIndepTripleLaw_snd` and
`condIndepTripleLaw_third` prove the marginals. The two `prodKernel_support_*`
theorems establish order support, and `condIndepTripleLaw_lintegral_mul` gives
the substantive conditional-independence identity

$$
\int f(\omega_1)g(\omega_2)\,d\gamma
 = \int \left(\int f\,dK_1(\eta)\right)
          \left(\int g\,dK_2(\eta)\right)d\rho(\eta).
$$

Conversely, projection of any ordered triple proves both dominations. Thus
`hasOrderedTriple_iff` identifies ordered-triple existence with precisely the
two ordinary dominations. Nonpercolation of $\rho$ is not needed to construct
this coupling; it matters for the later closed-boundary exhaustion.

The kernel $K_i(\eta)$ is a regular conditional law in the selected pairwise
coupling, **not** conditioning $\mu_i$ itself on the possibly null event
$\{\omega\le\eta\}$.

## Filtration-uniform reverse upcrossing estimate

`measureReal_upcrossingsBefore_le_uniform` considers any probability measure
$\mu$, any antitone sequence of sub-$\sigma$-algebras $G_n$, and a measurable
$0\le g\le1$. For $0\le a<b$ and positive $K$, it bounds by

$$\frac{b}{K(b-a)}$$

the probability of at least $K$ upcrossings of the finite reversed conditional
expectation process at horizon $N$. The bound uses the already verified reverse
martingale upcrossing estimate and controls its initial positive-part integral
by $b$. It is independent of both the filtration and $N$, allowing an estimate
to be applied fibrewise over an external configuration.

## Deliberate non-claims

Neither module proves Theorem 5.1. The following remain separate obligations:

1. a measurable exhaustion by finite regions with closed boundary under the
   nonpercolating dominating law;
2. identification of the relevant DLR conditional probabilities with the free
   finite-region law on the coupling fibres, including measurability;
3. the joint reverse-martingale and cylinder-mass argument for the two Gibbs
   laws; and
4. passage from extremal equality to the desired singleton Gibbs class, in the
   actual convention scope.

The uniform upcrossing theorem does not supply joint measurability or choose a
closed-boundary exhaustion. The region-kernel and coupling results likewise do
not substitute for the filtration and convergence steps.

Both exact sources were independently rebuilt with the project's pinned Lean
4.35.0 toolchain. Their 25 principal axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`, with no proof placeholders, custom axioms,
trust overrides or adjusted heartbeats.
