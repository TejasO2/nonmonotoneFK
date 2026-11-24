# Positive critical probability on bounded-degree graphs

Public module: `FK.PcPos`, namespace `CurvatureVariance.Infra.Percolation`.
This formalizes the subcritical non-degeneracy of Remark 1.5 of
arXiv:2512.16486v1 using the repository's actual Bernoulli product,
`percolationProb`, and `criticalProb`.

## Assumptions and main results

Let $G$ be a connected, locally finite simple graph on a countable vertex type,
and fix a root $o$. Assume every vertex has at most $d$ neighbours, with $d>0$.
Then

$$
(p d<1)\quad\Longrightarrow\quad \theta_o(p)=0,
$$

$$
\frac1d\le p_c(G),
$$

and, consequently, $p_c(G)>0$. The first bound is
`percolationProb_eq_zero_of_mul_card_lt_one`; the others are
`inv_card_le_criticalProb`, `criticalProb_pos`, and
`exists_pos_percolationProb_eq_zero`.

No transitivity, invariance, FKG, planarity, or growth hypothesis is needed.
The bound $1/d$ is a first-moment estimate, not the sharper $1/(d-1)$ or a
computation of $p_c$.

For $q>0$, `exists_prime_lt_criticalProb` constructs an explicit positive
parameter $p_0=\min(1/2,q/(4d))$ such that for every $0<p<p_0$,

$$
\mathrm{FK.prime}(q,p)=\frac{p}{p+q(1-p)}<p_c(G).
$$

The estimate uses $\mathrm{FK.prime}(q,p)\le2p/q$ for $p\le1/2$ and
$2p/q<1/(2d)$ on this window. Thus the graph's subcritical window for the
**Bernoulli comparison rate** is nonempty.

## First-moment proof

`walkLists` enumerates self-avoiding adjacent vertex lists of length $n+1$ from
$o$; its cardinality is at most $d^n$. Taking a bypass and then a length-$n$
initial segment turns an arm event into one of finitely many such lists.

The cylinder requiring every edge of a list to be open has Bernoulli probability
$p^n$: nodup vertex lists with adjacent consecutive vertices contain exactly $n$
distinct edge coordinates. A finite union bound therefore gives

$$
\Pr[\mathrm{armEvent}(o,n)]\le(pd)^n.
$$

As $pd<1$, this tends geometrically to zero. The intersection of arm events,
which describes the infinite rooted cluster, therefore has measure zero. The
bound is obtained directly rather than by assuming independence of overlapping
arm events.

The principal theorems use classical decidability internally and impose no
`DecidableEq` requirement on the graph's vertex type. That typeclass is required
only for some list-level supporting declarations.

## Residuals

These results supply positive Bernoulli subcritical parameters and an explicit
comparison-rate window. They do **not** show that FK limits are dominated by the
comparison Bernoulli law, that FK Gibbs measures are unique or DLR, that the FK
model is at its own critical point, or that enhanced/AG monotonicity is strict.
Their paper role is to remove vacuity from a subcritical hypothesis, not to
supply those remaining theorems. No sharp critical constant or critical
behaviour is claimed.

## Verification

The exact source was rebuilt independently on Lean 4.35, and its 11 principal
and supporting declarations were elaborated with fully qualified
`#print axioms` commands. All report only `propext`, `Classical.choice`, and
`Quot.sound`. These 11 audits are included in `Audit.lean`. The module uses
default heartbeats and no forbidden or custom trust declarations. Run
`./check.sh` for the complete project verification.
