# Normalized finite-FK positive association and comparison

Public module: `FK.WiredFKG`. This closes the gap between the abstract
corank-weight FKG development and the actual normalized FK PMFs on labelled
multigraphs with arbitrary finite boundary wiring.

## Corank is the component count

For a finite endpoint map `ends : E → V × V` and edge set $s$,
`FinFKG.skeleton ends s` is the simple graph obtained by joining the endpoints
of $s$, discarding loops and parallel-edge multiplicities as appropriate. Then

$$
\operatorname{FinFKG.clusterCount}(ends,s)
  = \operatorname{Nat.card}(\mathrm{ConnectedComponent}(\operatorname{skeleton})).
$$

This is `FinFKG.clusterCount_eq_natCard_components`. It allows isolated vertices,
loops, and parallel labels; it does not assume simple endpoints.

The proof uses $\mathbb F_2$ linear algebra. For a component map $c$, the
fibre-sum map `compSum c` adds the coefficients of each component. Its kernel is
exactly the span of the edge-difference vectors: edge terms cancel along
walks, while vanishing on every fibre gives the converse. Surjectivity of the
component-sum map and rank-nullity then give the desired dimension identity.

## Arbitrary boundary setoids

Choose a representative of every boundary block and add one artificial edge per
vertex to its representative. These artificial edges carry no probabilistic FK
weight: a nonloop wiring edge is deterministically open, while a loop is absent
from the simple skeleton. Reachability in this augmented free skeleton agrees
exactly with reachability in `LabelledMultigraph.connectionGraph`.

Therefore, with the actual model definitions,

$$
\operatorname{componentCount}(\xi,\omega)
  = \#\pi_0(\mathrm{wiringSkeleton}(\xi,\omega))
  = \operatorname{corank}(\mathrm{augEnds},\mathrm{augConfig}).
$$

No quotient vertex type is required. `componentCount_supermodular` consequently
holds on the configuration lattice for every boundary setoid.

## Normalized FKG and stochastic comparisons

For $q\ge1$ and $0<p<1$, `fkWeightR_lc` combines supermodularity with the exact
Bernoulli product identity. The weight is identified pointwise with the actual
`G.fkWeight q p ξ ω`, and ordinary FK partition functions supply normalization.
The component proves:

- `fkPMF_association` and `fkPMF_association_events`: actual normalized positive
  association for increasing nonnegative observables and increasing events;
- `fkWeightR_mlr` and `fkPMF_expectation_mono_p`: monotone likelihood ratio and
  expectation monotonicity in the edge rate;
- `fkPMF_expectation_le_bernoulli` and `fkPMF_event_le_bernoulli`:

  $$
  \mathbb E_{\mathrm{FK}_{q,p,\xi}}[f]
    \le \mathbb E_{\mathrm{Bernoulli}(p)}[f]
  $$

  for increasing nonnegative $f$, with the corresponding inequality for every
  increasing event.

The orientation is important. Larger $q$ favours more clusters and hence closed
edges; in the one-edge example at $q=2$, $p=1/2$ the open-edge probability is
$1/3$, not $1/2$. Thus the opposite blanket domination cannot follow.

## $q<1$: reversal, not negative association

For $0<q\le1$, `fkWeightR_lc_rev` is an exact reversal of the lattice condition,
not an association theorem. Strict supermodularity makes the FKG lattice
condition fail for $0<q<1$. The established two-parallel-edge example explicitly
has component counts $1+1<1+2$ at its complementary configurations, and
`parallelGraph_lattice_condition_fails` witnesses that failure. No negative
association is inferred.

## Exact scope

All quantitative conclusions are finite and at interior $0<p<1$; association and
domination are at $q\ge1$. There is no infinite-volume, $q<1$ association,
enhanced critical-window, DLR, AG, or main-paper theorem claim. Ordinary
logical/classical instances are used internally, but no additional graph
quotient or trust axiom is assumed.

## Verification

The exact source was independently rebuilt using Lean 4.35 and current public
imports, at default heartbeats. The public `Audit.lean` contains its 17 fully
qualified principal declarations, including the event form of Bernoulli
domination. Every audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Run `./check.sh` for full project verification.
