# Edge-domain monotonicity and a stage-level no-escape lemma

Public module: `FK.EdgeDomainMonotonicity`, namespace
`FK.InfiniteVolume.NoEscape`. This gives exact finite graph-extension
algebra and an analytic no-escape implication. `FK.StageInstantiation` supplies the
fixed-vertex `finiteVolumeLaw` instantiation, but the actual far-connection geometry
remains missing.

## Isolated vertices and edge injections

The component-count decomposition treats isolated vertices explicitly: if all
edges of $H$ lie in $t$, then

$$
\#\pi_0(H)=\#\pi_0(H\!\upharpoonright_t)+\#\{v\mid v\notin t\}.
$$

Its proof constructs the component bijection rather than assuming an induced-
subgraph equivalence.

For any edge injection $\iota:E_1\hookrightarrow E_2$ with matching endpoints
and a configuration closed off its image, the wired connection graph and hence
`componentCount` agree with restriction to $E_1$. The closed extension `extA`
and coordinate restriction `res` therefore give the exact weighted factor

$$
w_2(C)=(1-p)^{\#\{\text{extra edges}\}}\,w_1(C\!\upharpoonright_{E_1}).
$$

The required finite-sum partition-function normalization identities are proved
as well, including the vertex-isolation bookkeeping needed for future graph-box
identification.

## Finite domain comparison under a named association hypothesis

`PosAssoc q p hq hp` is defined in this module as positive association at
$q\ge1$ for actual normalized FK measures on all finite labelled multigraphs
with arbitrary finite setoids. At $0<p<1$, the exact closed-stratum equality and
that property yield

$$
\mu_1(A)\le\mu_2(\iota^{-1}(A))
$$

for every increasing $A$. Only this shape and parameter direction is proved:
larger edge domain makes lifted increasing events **more** probable, not less.

The association input is a named definition here, not a proof of a new FKG
theorem. `FK.WiredFKG`, released separately, supplies related finite
positive-association tools for this graph class; that instantiation and the
connection to `finiteVolumeLaw` are not asserted by this module.

## Analytic no-escape reduction

Given convergence of stage laws to $\mu$, clopen increasing events $C_k$ whose
union is $C_\infty$, and the explicit stronger stage estimate

$$
m\le k \implies \operatorname{stage}_m(C_m)\le\operatorname{stage}_k(C_m),
$$

`noEscape_of_stage_mono` concludes that the real-valued limsup of
$\operatorname{stage}_k(C_k)$ is at most $\mu(C_\infty)$. The monotone stage
assumption is essential. Clopen weak convergence alone is not an FK no-escape
estimate; the existing moving-atom example shows why it does not control these
masses uniformly.

## Remaining obligations

The displayed edge-extension laws have now been connected to genuine
`FiniteBox.finiteVolumeLaw` for the fixed-vertex nested family by
`FK.StageInstantiation`, including `interiorRestriction` pushforwards. That still does not construct the actual
far-connection event geometry.
Instantiate that estimate on the actual nested FK far-connection events. Until
that is done, there is no uniform far-connection estimate, no completed all-box
DLR passage and no new Proposition 1.8(2) or numbered-theorem conclusion.

The identifier `sum_weight_closed_ext` is the coordinator's parser-safe rename
of `sum_weight_closed'`, with no mathematical change.

## Verification

The exact candidate was rebuilt through current public imports using Lean 4.35
and default heartbeats. Its 14 principal and supporting declarations are
audited in `Audit.lean` after the parser-safe name change; each uses only
`propext`, `Classical.choice`, and `Quot.sound`. Run `./check.sh` for the complete
integration check.
