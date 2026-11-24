# Disintegration along a random closed region

Public module: `FK.RandomRegionKernel`. This turns the per-region DLR product
identities into one integral over all countable finite-region strata, without
using per-measure null-set intersections. It works with the actual FK Gibbs
measures and the actual geometric region `region G ω T`.

## Assumptions

Let $G$ be locally finite on a countable vertex type, fix a base set $T$, and
assume that $\mu$ satisfies the record
`InfiniteVolume.FiniteBox.IsDLR` at **every finite vertex region**, with the
boundary partition `exteriorPartition` induced by the exterior field. This is a
specific geometric DLR class, not every convention or every FK limit.

Given a measurable event $C$, the main result requires either that $C$ is
interior-supported on each allowed stratum or that it is a genuine global
cylinder whose base is contained in the corresponding box. Interior parameters
$p,q>0$ are used only for the attained-stratum probability normalization; the
factorization itself is stated for $q>0$ and $p\le1$.

## Exact conditional law

`regionIdx` codes a finite closed region and `cutAt` preserves all coordinates
outside it while closing its interior. A stratum `region = s` factors as
`frontierSet × connSet`, preserving the **forced interior connectivity**. The
conditional mass on that stratum is

$$
K_s(C)=\frac{\nu_s(A_C(s)\cap\mathrm{connSet}(s))}
  {\nu_s(\mathrm{connSet}(s))},
$$

where $A_C(s)$ is the interior readout of $C$ at the box. The module writes the
normalization with an inverse mass multiplying the numerator rather than
ordinary division. The free finite-volume FK measure $\nu_s$ is not used
without that connectivity restriction.

The full countable-strata identity is

$$
\mu\left(C\cap\bigcup_{\mathrm{Good}(s)}B_s(Y_s)\right)
 = \int_{\bigcup_{\mathrm{Good}(s)}B_s(Y_s)}
     K_{\mathrm{regionIdx}(\omega)}(C)\,d\mu(\omega),
$$

for an arbitrary family `Y s` of exterior measurable tests, with
$B_s(Y_s)=\{\mathrm{region}=s,\ \mathrm{cutAt}(s)\in Y_s\}$.
The integrand is measurable, and exterior tests are not shared across strata.
`region_cond_agree` gives the cross-multiplied conditional-probability identity
for any two measures in that same DLR class, without assuming positive stratum
mass. A cylinder version handles the source-facing finite predicates.

## Attained fibres

`regionKernelFun` is an actual measure-valued construction obtained by gluing
an interior law onto a prescribed exterior field. On every attained finite
stratum, its positive free-FK point mass makes this a probability measure at
$0<p<1$, $q>0$. Zero-mass or infinite-region conventions are separated rather
than silently divided by zero.

## Important residuals

This is not yet a complete registered regular conditional kernel on the whole
random region/exterior-field product. It is proved for measurable
interior-supported events and source-facing cylinders; arbitrary measurable $C$,
an unconditional globally packaged Markov kernel, and the infinite-region case
are not covered.

The module does not prove the one-joint-null reverse-martingale step, construct
the metric exhaustion, discharge the reduction from a general convention to the
specific exterior-partition DLR class, or prove Thm 5.1. The supplied event
$\{\nu_s(\mathrm{conn})=0\}$ is null and the attained strata are normalizable,
but these facts alone do not supply a coupled convergence theorem.

## Verification

The exact source was independently rebuilt on Lean 4.35 using current public
imports and default heartbeats. Its 28 fully qualified declarations are included
in `Audit.lean` and each reports only `propext`, `Classical.choice`, and
`Quot.sound`. No forbidden trust construction is used. Run `./check.sh`.
