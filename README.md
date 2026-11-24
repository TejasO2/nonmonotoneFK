# nonmonotoneFK: Lean formalization

This repository contains an ongoing Lean 4 formalization of Beffara–Faipeur–Oke,
*A New Bound for the Critical Point of the FK Model for q < 1*,
arXiv:2512.16486v1.

The source project and build instructions are in
[`results/fk-qcritical`](results/fk-qcritical/README.md). Start with its
[proof-status guide](results/fk-qcritical/docs/PROOF-STATUS.md): the actual
finite FK model, finite Theorem 1.2, enhanced dynamics, substantial
infinite-volume transport, finite duality, and critical-window components are
implemented; the whole-paper Theorems 1.4, 1.10, and 1.11 are not yet proved.

The two-class reduced-word tree now has an [exact two-rate critical curve](results/fk-qcritical/docs/AG-TWO-RATE-CRITICAL.md):
$2b+s+4bs<1$ gives nonpercolation, the reverse inequality gives positive open-cluster
percolation, and equality with $b>0$ gives nonpercolation. The critical base rate is
$(1-s)/(2+4s)$, strictly decreasing for positive activation. The corner $(0,1)$ is
excluded; this tree theorem is not the paper's general AG, FK-window or uniqueness result.

A new [planar cut analysis](results/fk-qcritical/docs/PLANAR-CUT-OBSTRUCTION.md)
shows that the strict all-open-cut construction is unsatisfiable for arbitrary finite
sets on the existing dual-nonpercolating staircase. This delimits a sufficient proof
interface, not the paper's planar theorem or its at-most-one-cluster conclusion.

Added [exterior-only good-intersection refinements](results/fk-qcritical/docs/NESTED-EXTERIOR-STRATA.md)
and a [bounded-degree first-moment bound](results/fk-qcritical/docs/BERNOULLI-PC-POSITIVE.md)
proving $1/d\le p_c$ and explicit subcritical comparison-rate parameters. These do
not establish ordinary nested-metric $hgood$, FK domination, or uniqueness.

The [finite normalized FKG bridge](results/fk-qcritical/docs/WIRED-FKG.md) now
identifies wired component counts with the $\mathbb F_2$ corank and proves
positive association and correctly oriented Bernoulli comparison at $q\ge1$.
It remains finite; its $q<1$ reversal is not negative association.

Additional releases add [random-region disintegration](results/fk-qcritical/docs/RANDOM-REGION-KERNEL.md)
on genuine countable strata and a [covering-based reference comparison](results/fk-qcritical/docs/AG-COVERING-REFERENCE.md)
for the sleeved Bernoulli model. The first is not yet full Theorem 5.1 assembly;
the second requires selecting every original bond, not merely positive density.

A [net-indexed region comparison](results/fk-qcritical/docs/NET-CONVERGENCE-INTERFACE.md)
is also included, but only conditionally on `HasNetExteriorConvergence`; the net
upcrossing/martingale theorem this needs is still open.

A separately published [edge-domain comparison](results/fk-qcritical/docs/EDGE-DOMAIN-MONOTONICITY.md)
uses an explicit finite association hypothesis and stage monotonicity. Its correspondence
with genuine `finiteVolumeLaw` exhaustion and no-mass-escape remains to be established.

The planar [vertex-sealed circuit release](results/fk-qcritical/docs/SEALED-SEPARATION.md)
both rules out the older crossing-controlled exhaustion by a closed ray and provides
a valid replacement interface with concrete open-box-border/staircase instances. It
does not construct the general sealed family from dual nonpercolation.

The new [isolated-vertex FK-law result](results/fk-qcritical/docs/ISOLATED-VERTEX-LAW.md)
proves normalized invariance under adding free new vertices, including genuine
`finiteVolumeLaw` equality, with a wired counterexample marking the boundary restriction.
The new [fixed-vertex stage results](results/fk-qcritical/docs/FINITE-STAGE-NO-ESCAPE.md)
supply association and no-mass-escape at $q\\ge1$ on genuine nested finite boxes,
including a fully unconditional $q=1$ loop instance. An [independent-region mean repair](results/fk-qcritical/docs/RANDOM-REGION-L1-REPAIR.md)
and [countable exhaustion theorem](results/fk-qcritical/docs/NET-EXHAUSTIONS.md)
address different convergence hypotheses, not the general far-connection/AG geometry.

The planar [finite cut-graph crossing](results/fk-qcritical/docs/CUT-CROSSING-DUALITY.md)
proves below-to-above dual connectivity from left/right wall separation, through exact
outer/cell degree counts and handshake. This is the foundation of the subsequent
finite box duality, not a proof of Theorem 1.11.

The follow-up [finite primal/closed-bond duality](results/fk-qcritical/docs/CLOSED-BOND-PRIMAL-DUALITY.md)
now instantiates left-reachability, proves every cut edge closed, and gives a primal open
left-to-right walk in the absence of a closed dual crossing. Exact `gridCrossEquiv` and
`dualConfig` incidence is included; global uniqueness and compactness remain open.

The complementary [sealed parity-barrier component](results/fk-qcritical/docs/BOX-SEAM-SEPARATION.md)
proves that a simple bottom-to-top closed cell chain blocks every open primal
left-to-right walk, using a $\mathbb Z/2$ potential.

The completed [finite box crossing duality](results/fk-qcritical/docs/FINITE-BOX-DUALITY.md)
joins these results. For $n>0$, an open primal left-to-right crossing exists
exactly when there is no closed below-to-above path, with the corresponding
exclusive dichotomy. This is the bounded collapsed-dual result, not an
un-collapsing, compactness, infinite primal non-switching-order, or
`GlobalAtMostOne` theorem.

The new [source-form Proposition 4.2](results/fk-qcritical/docs/PROPOSITION42-SOURCE.md)
constructs the uniform star/cycle enhanced comparisons for source-boundary weak
limits and DLR classes, together with the quasi-transitive separated devices.
It also records the source's swapped enhanced-set labels in the subsequent
Theorem 1.4 paragraph. The essential-enhancement strict shift remains unproved.

The [actual profile-mass derivatives](results/fk-qcritical/docs/AG-MASS-DERIVATIVE.md)
now identify finite/cylinder derivatives with pivotal masses and repair the previous
closed-domain differentiability premise on the interior. The geometric pivot trade
inequality and supercritical baseline remain missing. Moreover, minimal cycle devices
[refute the old whole-region pivot premise](results/fk-qcritical/docs/PIVOT-TRADE-WINDOW.md);
only a per-event compact-window repair and approximation-conditional shift exist.
This is a correction to the repository route, not essential enhancement or a source counterexample.

The [subcritical Bernoulli baseline](results/fk-qcritical/docs/SUBCRITICAL-BASELINE.md)
is now proved from finite energy along a fixed walk, including root-independent criticality.
The supercritical baseline remains open.

New bounded components also cover [clopen/dominated escape](results/fk-qcritical/docs/CLOPEN-ESCAPE.md),
[fixed-vertex monotone limit existence](results/fk-qcritical/docs/MONOTONE-LIMIT-EXISTENCE.md),
and [closed-staircase dual percolation](results/fk-qcritical/docs/BLOCKED-STAIRCASE.md).
The genuine FK finite-stage/source-partition instantiations, growing-vertex canonical limits,
and separating planar barrier remain open.

A [conditional planar DLR transport](results/fk-qcritical/docs/PLANAR-DLR-DUALITY.md)
now handles configuration complementation, composition-product kernels and singleton
adapters. It does not instantiate the paper's equation-(12) dual parameter/graph data,
establish the external-cluster conditions, or prove global uniqueness.

The latest bounded additions are [boundary-wiring order](results/fk-qcritical/docs/BOUNDARY-WIRING.md),
[finite specification nesting](results/fk-qcritical/docs/SPECIFICATION-NESTING.md),
[shell-first exploration](results/fk-qcritical/docs/NESTED-REGION-EXPLORATION.md),
[un-collapsed duality and cofinal crossings](results/fk-qcritical/docs/GRID-COFINAL-CROSSINGS.md),
and a [total arbitrary-event region kernel](results/fk-qcritical/docs/REGION-KERNEL-TOTAL.md).
The last proves an arbitrary-event disintegration identity and its dominated finite-region
form. The subsequent [conditional fibre-product coupling](results/fk-qcritical/docs/CONDITIONALLY-INDEPENDENT-COUPLING.md)
supplies the three-marginal ordered coupling and filtration-uniform upcrossing estimate;
the measurable random-region DLR assembly, metric exploitation, and final global/strong
uniqueness theorems remain open.

The [dual-parameter planar equation](results/fk-qcritical/docs/DUAL-PARAMETER-DUALITY.md)
now instantiates equation (12) at $p^*=1-p'$ exactly, including normalized FK relabelling,
its exterior-boundary conventions and DLR transport. The shared Euler input and global
planar/uniqueness arguments remain; this is the finite one-box result, not Theorem 1.11.

The new [infinite-volume FKG theorem](results/fk-qcritical/docs/INFINITE-VOLUME-FKG.md)
proves positive association for arbitrary weak FK limits at $q\ge1$ on every measurable
increasing pair, using cylinder continuity and inner-regularity. It does not construct
canonical limits or a DLR/uniqueness theorem.

Current release check: **9,365 build jobs**, **2,918 audited declarations**, and
**280 documented FK modules**.
 The audit accepts only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, or `unsafe` declaration is used in the formalization sources.
