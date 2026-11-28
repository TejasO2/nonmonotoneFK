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

The explicit Husimi triangle cactus now has an [exact homogeneous criticality and
direct-bond penalty window](results/fk-qcritical/docs/CACTUS-EFFECTIVE.md) on its actual
independent bonds, together with separated triangle/double-ray geometry at bounded
line-graph distance. It is a complete scoped cactus theorem, not the general AG
essential-enhancement shift or the paper's Theorem 1.4.

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
The [AG-interface sharpness checks](results/fk-qcritical/docs/AG-SHARPNESS.md)
confirm that the strict decrement content is not avoidable and supply full-
device non-vacuity examples, but do not prove the positive-density shift.

The [actual profile-mass derivatives](results/fk-qcritical/docs/AG-MASS-DERIVATIVE.md)
now identify finite/cylinder derivatives with pivotal masses and repair the previous
closed-domain differentiability premise on the interior. The geometric pivot trade
inequality and supercritical baseline remain missing. Moreover, minimal cycle devices
[refute the old whole-region pivot premise](results/fk-qcritical/docs/PIVOT-TRADE-WINDOW.md);
only a per-event compact-window repair and approximation-conditional shift exist.
This is a correction to the repository route, not essential enhancement or a source counterexample.

The [subcritical Bernoulli baseline](results/fk-qcritical/docs/SUBCRITICAL-BASELINE.md)
is now proved from finite energy along a fixed walk, including root-independent criticality.
`FK.ReferenceBaseline` also proves the ordinary [supercritical baseline](results/fk-qcritical/docs/REFERENCE-BASELINE.md).

New bounded components also cover [clopen/dominated escape](results/fk-qcritical/docs/CLOPEN-ESCAPE.md),
[fixed-vertex monotone limit existence](results/fk-qcritical/docs/MONOTONE-LIMIT-EXISTENCE.md),
and [closed-staircase dual percolation](results/fk-qcritical/docs/BLOCKED-STAIRCASE.md).
The genuine FK finite-stage/source-partition instantiations, growing-vertex canonical limits,
and separating planar barrier remain open.

The [normalized nested exterior mixture](results/fk-qcritical/docs/NESTED-MIXTURE.md)
now proves genuine growing-vertex free finite-volume weak limits using real
vertex/edge inclusions and normalized fibre conditioning. Source lattice boundary
fields, wired-family limits, and canonicality remain open.

A [DLR specification-deviation reduction](results/fk-qcritical/docs/SPECIFICATION-DEVIATION.md)
proves mean-insensitivity uniqueness and constant/free-convention singletons. The
vanishing input for the genuine varying convention is still open.

A [conditional dual-limit bridge](results/fk-qcritical/docs/DUAL-LIMIT.md)
now lifts external-boundary equation (12) through weak convergence and reduces
total FK-family uniqueness to dual uniqueness plus `hdualizable`. The closed
versus all-open exterior bookkeeping is explicit. Dual strong uniqueness,
Euler certificates, actual dualizability and the planar cluster separation
remain open.

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

Additional bounded packages prove [lattice circuit separation](results/fk-qcritical/docs/LATTICE-SEPARATION.md),
[frontier-mass determination](results/fk-qcritical/docs/FRONTIER-DETERMINATION.md),
and [fixed closed-boundary uniqueness](results/fk-qcritical/docs/COFINAL-FREE-BOUNDARY.md).
Their adaptive-region and cofinal-circuit obligations remain explicit.

Additional [source-region and ordered-fibre components](results/fk-qcritical/docs/ORDERED-FIBRE-CYLINDERS.md)
prove the integration/classification step once the source's ordered fibre limit
has been supplied. The [closed-frontier region packaging](results/fk-qcritical/docs/SOURCE-REGIONS.md)
gives general nested source conventions, correct finite `Finset` regions, and
ordered-kernel nonpercolation transfer; no completed global uniqueness or AG
critical shift follows from those inputs.

The random-region additions prove [joint conditional measurability](results/fk-qcritical/docs/RANDOM-EXHAUSTION.md)
and [finite sealed-region conditioning](results/fk-qcritical/docs/REGION-SEAL.md).
A [shell-first coupling bound](results/fk-qcritical/docs/NESTED-SPLIT-COMPARISON.md)
has its fixed shell-touching error, not the paper's vanishing arm event, and the
[AG shift interface](results/fk-qcritical/docs/AG-SHIFT.md) retains its two
critical-shift hypotheses. These are scoped building blocks, not completions
of Theorems 1.4, 1.9, 1.10 or 5.1.

The new [prime-dominated metric DLR package](results/fk-qcritical/docs/METRIC-DOMINATED-DLR.md)
proves nested-stage/free DLR closure from a nonpercolating stochastic majorant,
constructs the canonical metric growing family, and derives finite-stage prime
domination. Global uniqueness is now automatic, and the finite-stage-free
corollary removes exterior support as well. This remains restricted to metric
exhaustions and geometric boundary assignments, not general Proposition 1.8(2)
or Theorem 1.9.

[Source-union Proposition 1.8(2) is now proved](results/fk-qcritical/docs/PROPOSITION18-EXTERNAL.md):
actual exterior-configuration weak limits and coherent geometric Gibbs inputs with
`GlobalAtMostOne` belong to every coherent geometric all-box DLR target, at all
parameters. Unrelated noncoherent setoids remain excluded.

The new [exterior determination and planar assembly package](results/fk-qcritical/docs/PLANAR-ASSEMBLY.md)
adds finite convention-determining windows, almost-everywhere dual kernels and
all-box DLR transport, plus explicit primal/dual exactly-one-cluster assembly.
The enclosing-circuit, finite free duality, dual-uniqueness and phase hypotheses
remain explicit rather than being relabelled as a completed Theorem 1.11.

A second [nested outer-stage DLR proof](results/fk-qcritical/docs/GLOBAL-OUTER-CLOSURE.md)
supplies orientation-free moving-clopen rates and off-edge escape geometry. Its
source-form Proposition 1.8(2) remains explicitly tied to nested geometry and
edge-complement-supported boundaries. The same guide records an exact ordered-seal
counterexample relevant to Theorem 5.1's coupling route—not a refutation of the theorem.

The new [finite combinatorial enclosure theorem](results/fk-qcritical/docs/COMBINATORIAL-ENCLOSURE.md)
gives an exact cellular primal circuit with connected inside/outside and a
sealed path-hit statement. Arbitrary continuous global windows and cofinality
remain open, so Theorem 1.11 is still not claimed complete.

The follow-up [cellular sealed-cut assembly](results/fk-qcritical/docs/CELLULAR-SEALED-CUTS.md)
tolerates closed exit edges, restricts exact global closed frontiers to local
rotation windows, and constructs those windows' metric dual exhaustion from
actual dual nonpercolation. Pairwise-cofinal exact windows now yield the
original graph's `GlobalAtMostOne`. The required continuous embeddings,
strict-interior incidence and cofinality remain explicit inputs; finite free
duality, dual strong uniqueness and the enhancement/phase steps remain open.

A separate [dual-enhancement density theorem](results/fk-qcritical/docs/DUAL-ENHANCEMENT-DENSITY.md)
transports primal bounded-distance enhancement sets through exact local corner
links without assuming dual quasi-transitivity. This is a simple-dual graph
component; rotation data, finite-device duality and dual essentialness remain
unproved, as does Theorem 1.11.

The follow-up [dual source-window assembly](results/fk-qcritical/docs/PLANAR-SOURCE-WINDOW.md)
proves exact primal-lower/dual-upper enhanced profiles, all-source lower
comparison, conditional exactly-one-cluster windows and dual singleton windows.
The latter require matched dual devices, AG and literal equation (9); finite
free duality and the final dual-box/source and all-box compatibility still
remain. The separate primal/dual thresholds have not yet been combined into
an unconditional Theorem 1.11.

A small [continuous plane package](results/fk-qcritical/docs/CONTINUOUS-PLANE.md)
now defines actual finite Jordan-arc embeddings and complementary faces, proves
segment separation by an explicit detour, and constructs an exact one-edge
spherical window with primal incidence coverage. This is a useful local
realization check, not arbitrary continuous rotation extraction, cofinality or
a stochastic planar theorem.

A new [arbitrary-exhaustion strong-uniqueness bridge](results/fk-qcritical/docs/SOURCE-UNIQUENESS.md)
proves source-family singleton and nonpercolation from the literal nested
cylinder estimate and nonpercolating dominant. Compactness, boundary geometry,
exhaustion selection and Choquet are finished; Lemma 2.1 and AG remain as inputs.

The follow-up [source upper-window assembly](results/fk-qcritical/docs/SOURCE-WINDOW.md)
applies Prop 4.2 to every arbitrary-exhaustion source weak limit, identifies its
upper product with the AG window, handles the $p=0$ endpoint, and obtains one
positive radius uniformly over $p\le1$. This retains the actual AG strict shift
and nested equation (9) at every interior $p$; it is not unconditional Theorem
1.10.

A separate [deterministic-dominant uniqueness result](results/fk-qcritical/docs/DETERMINISTIC-DOMINATOR.md)
treats any geometric all-region source convention dominated by a Dirac mass at
a nonpercolating configuration, even one with infinitely many open edges. It
constructs an adaptive closed-frontier exhaustion and proves uniqueness within
that DLR class; its singleton wrappers require class membership. The general
random-dominant Theorem 5.1 remains unresolved.

A stronger [comparable-laws mechanism](results/fk-qcritical/docs/COMPARABLE-NONPERCOLATING.md)
now proves equality of any stochastically comparable, almost-surely
nonpercolating laws for one geometric all-region source convention. A
nonpercolating dominant **inside that DLR class** gives its singleton, using
normalized finite-base frontier strata rather than ordered-fibre martingales.
An arbitrary external common dominant and mutually unordered members remain
outside its scope, so general Theorem 5.1 is still unresolved.

A finite [arm-correction obstruction](results/fk-qcritical/docs/ARM-CORRECTION-OBSTRUCTION.md)
gives exact FK filtered masses $17/59$ and $21/71$ at $q=2$, $p=4/5$ on five
edges. Conditioning away a root-to-boundary arm therefore need not erase
boundary influence. This rejects one proposed repair, not closed-frontier
conditioning or the general theorem itself.

A new [local-pivot MSS and cylinder analysis package](results/fk-qcritical/docs/AG-LOCAL-PIVOT-MSS.md)
supplies uniform local modification trade constants and both clamp-free
arbitrary-coordinate increment/decrement windows. The local maps, uniformity,
convergence and baseline inputs remain open; it is not the general AG shift.

The earlier [finite adaptive nested exploration package](results/fk-qcritical/docs/ADAPTIVE-NESTED.md)
proved stopped free interiors, synchronized good intersections, and exact
nested transported marginal laws. The follow-up [ordinary nested-window package](results/fk-qcritical/docs/ORDINARY-NESTED-ARMS.md)
now proves exact induced small free laws, maximal-frontier stability, and
outside-coordinate copying. The follow-up [arbitrary nested global equation](results/fk-qcritical/docs/NESTED-GLOBAL-EQUATION-NINE.md)
proves the literal `NestedEquationNine` for every abstract NestedBox at interior
parameters, the exact `boundaryConnection` vanishing error, and the classical
source-family uniqueness assembly. The enhanced-profile coupling and AG strict
shift remain unresolved, so this is not all of Theorems 1.4 or 1.10.

A new [Burton–Keane component library](results/fk-qcritical/docs/BURTON-KEANE-COMPONENTS.md)
proves finite three-arm patches, positive encounters under explicit insertion
tolerance, and first-moment/Følner and finite-tree bounds. The separate
[DLR insertion-tolerance module](results/fk-qcritical/docs/DLR-INSERTION-TOLERANCE.md)
now proves actual finite-pattern finite energy for genuine FK-DLR laws at
interior parameters. The [encounter-tree package](results/fk-qcritical/docs/ENCOUNTER-TREE.md)
constructs an actual finite tree with centre degree at least three and all
leaves on the prescribed metric sphere. The follow-up
[automorphism and marked-forest package](results/fk-qcritical/docs/BURTON-KEANE-INVARIANCE.md)
proves actual $q=1$ source-law invariance, a conditional centre-local Følner
adapter, configurationwise forest bounds with a supplied forest, and a
finite-patch exactly-two argument. Its zero-mass exactly-two theorem requires
an explicit ergodic automorphism; its three-cluster theorem still requires the
multi-centre Følner bound. Full count constancy, general source invariance at
$q\ne1$ and a global BK theorem remain open.

The [affine-basis triangle package](results/fk-qcritical/docs/TRIANGLE-CIRCUIT.md)
proves genuine bounded/unbounded plane separation, a faithful three-segment
embedding, and an exact six-dart rotation/face equivalence. It is a complete
triangle instance, not arbitrary polygonal Jordan separation or a global dual
window construction.

The follow-up [straight-forest package](results/fk-qcritical/docs/STRAIGHT-FOREST.md)
proves path-connected complements for every straight labelled forest and
constructs connected spherical rotations/face equivalences from local incidence
ranks. Explicit tube attachment handles labelled-leaf induction, including
isolated and disconnected vertices. This still uses straight ranges, not
arbitrary continuous arcs or angular/dual incidence.

The [unit-total upper-law comparison](results/fk-qcritical/docs/ARBITRARY-FRONTIER-TOTAL.md)
makes a non-DLR upper law force common DLR frontier masses only when its
finite-base strata have unit totals. Nonpercolation does not itself supply that
property, so an arbitrary common-dominant Theorem 5.1 is still open.

The related [dominated source-compactness package](results/fk-qcritical/docs/DOMINATED-SOURCE-COMPACTNESS.md)
closes source-DLR laws under dominated weak limits, barycenters and coherent
conditional-stage subsequences. A two-sided stage sandwich produces a common
DLR dominant and cylinder equality, but an arbitrary global nonpercolating
dominant does not supply these finite-stage bounds.

An additional [endpoint-inclusive nested equation (9) route](results/fk-qcritical/docs/NESTED-GLOBAL-EQUATION-NINE.md)
now proves the literal estimate for every abstract `NestedBox` and every $0\le p\le1$
by arbitrary-boundary isolated-vertex deletion and an intersection-box transport.
It retains the actual observation roots and ordinary $\max(p,p')$ upper product;
it is not an enhanced adaptive coupling or an AG shift.

The new [interior classical subcritical source-uniqueness theorem](results/fk-qcritical/docs/CLASSICAL-SUBCRITICAL.md)
covers every $q>0$ and $0<p<1$ under the literal condition
$\max(p,p')<p_c(G,o)$. It proves a singleton full source family and a.s.
nonpercolation, without an artificial seed-edge premise. Empty-device
comparisons, nested equation (9), the $q=1$ Bernoulli classification and
edge-free handling replace any AG or enhanced input. Enhanced windows and
non-source conventions remain outside its scope. A stronger wrapper also
accepts actual nonpercolation of this ordinary upper product, or zero one-root
percolation probability at that rate; this includes the classical critical
exception $\theta_o(p_c)=0$ without going beyond $p_c$.

The [continuous arc transport package](results/fk-qcritical/docs/CONTINUOUS-REPARAMETRIZATION.md)
proves segment-range coverage by an intermediate-value argument and transports
exact carriers/actual faces through range-preserving Jordan parametrizations,
with segment and nondegenerate-triangle instances. It does not provide angular
extraction, arbitrary curved ranges, or the cofinal dual windows still needed
for Theorem 1.11.

A separate [common-frontier replacement analysis](results/fk-qcritical/docs/COMMON-FRONTIER-REPLACEMENT.md)
proves that constructing either a common DLR upper law or a common canonical-DLR
frontier minorant is already equivalent to pairwise uniqueness. This rules out
obtaining that replacement from compactness alone; it neither proves nor refutes
general Theorem 5.1.

Current release check: **9,523 build jobs**, **3,715 audited declarations**, and
**430 documented FK modules**.
 The audit accepts only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, or `unsafe` declaration is used in the formalization sources.
