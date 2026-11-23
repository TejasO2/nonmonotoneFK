# Proof status and remaining obligations

## Read this table correctly

The development targets arXiv:2512.16486v1. Its current state is a substantial
verified library, **not a completed formalization of every main result**.
Completion here is recorded at the source-result level. The finite Theorem 1.2
is now proved, but a finite Markov stratum or a critical-window reduction still
is not a proof of the higher-level main results.

The labels below have distinct meanings:

- **Proved:** the declaration is built and uses no `sorry`, custom axiom, or
  `unsafe` declaration; its stated mathematical scope is checked against the
  corresponding source passage.
- **Scoped result:** an unconditional result, but weaker or different from the
  paper's full claim.
- **Conditional:** the statement has an explicit mathematical input which is
  itself part of the requested theorem's proof.
- **Missing:** the implementation has not yet constructed the result or its
  necessary inputs.

All completed and conditional results are ordinary Lean theorems. The
classification, not a simplistic "has axioms" test, tells them apart.

## Numbered paper results

| Source | Current state | Existing entry point and remaining work |
|---|---|---|
| Eq. (1), Remark 1.1 on model | **Proved finite model**, general normalization | `FK/FiniteModel.lean`: normalized labelled-multigraph FK PMF/measure, including arbitrary setoid wiring. Endpoint laws and $q=1$ Bernoulli specialization are proved. Wiring is represented directly by the boundary setoid rather than requiring a separate quotient graph witness for every application. |
| Eq. (2) | **Proved** | `FK/FiniteConditional.lean`: both endpoint-connection branches yield exactly `p` or `p'`. Positive-mass off-edge fibers make the normalization explicit. |
| Eq. (3) | **Proved** | `FK/FiniteComparison.lean` has both inequalities over actual labelled multigraphs and arbitrary setoids. The `q=1` identity is in `FK/ClassicalOne.lean`. |
| **Theorem 1.2**, finite enhanced comparisons | **Proved for interior $0\lt p\lt1$ and $0\lt q$, $q\ne1$** | `FK.EnhancedComparisons.theorem_1_2_of_lt_one` proves the lower-cutset/upper-open-path inequalities for $q<1$; `theorem_1_2_of_one_lt_q` proves the reverse direction for $1<q$. Both produce a nonempty enhanced set with strict local enhancement and use actual normalized FK measures. `Theorem12Fidelity` exposes the corresponding raw enhancement families in the paper’s explicit $p+\\varepsilon$ and $p-\\varepsilon'$ notation, case by case. `hconn`/`htwo`/`hnotforest` are the wired non-tree and at-least-two-quotients hypotheses. |
| **Theorem 1.4**, extended phases | **Conditional; AG and assembly missing** | Device packing and route certificates, analytic decrement/increment monotonicity, phase-law bridges and percolation event are proved. `FK.EssentialWindow` and `FK.AGWindow` still require reference shift hypotheses. `FK/AGSleevedAnnulus.lean` constructs a genuine simple graph with a distinct two-edge bypass per base bond, one shared activation repairing any finite selected bond annulus, disjoint annulus/support, actual pivot conversions and exact finite-product ratios; connectedness/local finiteness are preserved and explicit vertex/edge transitivity gives quasi-transitivity. Uniform separated template packing, differential summation/integration and the infinite-volume reference law remain. `hAG` must be constructed, not renamed. |
| **Proposition 1.8(1)** | **Proved, including Choquet decomposition and uniqueness from extremal uniqueness** | `FK/ExtremalTail.lean` proves tail triviality and mixture uniqueness around actual DLR classes. `FK/ReverseMartingale.lean` proves full a.e. reverse conditional convergence using finite reversals and upcrossing bounds, genuine weak convergence of the actual exterior FK conditional laws, and `FK.InfiniteVolume.mem_fkLimitMeasures_of_extremal_dlr`. Thus every extremal DLR law is represented as a weak limit with a deterministically selected boundary sequence. `FK/ExteriorIdentification.lean` supplies the exact supported-event conversion. `FK/TailChoquet.lean` constructs the actual tail mixture and its barycenter identity. `FK/TailConditionalTriviality.lean` then proves simultaneous tail zero-one for a.e. tail RCP fibre by the covariance/backward-convergence argument of Berti–Rigo Theorem 15. Consequently almost every fibre is extremal DLR, every DLR law has an extremal tail-fibre Choquet decomposition, and extremal DLR uniqueness implies DLR uniqueness. The same fibres also belong to `FKLimitMeasures`. These results need no countably-generated-tail assumption or Giry extremal-locus measurability proof. |
| **Proposition 1.8(2)** | **All-rate coherent DLR closure and noncoherent exterior uniqueness proved; noncoherent fixed-source DLR membership remains** | `FK/GlobalFiniteEnergy.lean` derives exterior uniqueness from global uniqueness before DLR membership for coherent interior limits, and `FK/EndpointGlobalFiniteEnergy.lean` supplies exact deterministic arbitrary-exterior endpoint limits and all-rate coherent/fixed-specification DLR closure. Separately, `FK/NoncoherentFiniteEnergy.lean` proves a uniform closing bound for **every** finite FK boundary setoid using one-edge weight ratios and a proved $2^{|B|}$ fibre bound. This passes to arbitrary `IsFKLimit`s (whose boundaries need not cohere) and yields actual `AEAtMostOne` from global uniqueness before DLR membership at $0<p<1$. No fixed source convention or target DLR equation is inferred from this geometric conclusion. Coherent interior branches retain geometry, local finiteness and almost-sure global uniqueness; endpoints are handled directly rather than by positivity. The remaining interior problem is fixed-source DLR closure for unrelated boundary sequences. |
| **Theorem 1.9**, classical subcritical strong uniqueness | **Nested finite coupling and DLR/tail assembly proved; maximal-stratum equality and vanishing estimate missing** | `FK/NestedArmUniqueness.lean` proves finite-root and metric-crossing errors vanish under nonpercolation, Bernoulli nonpercolation from zero root probabilities, and equality of genuine FK weak limits under eventual nested arm bounds. `FK/NestedFiniteCoupling.lean` constructs the actual triple along `EΔ ⊕ EO ≃ EΣ`, including exact first/third marginals, exact FK second restriction to the smaller graph, and an equation-(9) estimate with the second restriction proved internally rather than assumed as `hsecond`. `FK/NestedBoundaryUniqueness.lean` proves DLR uniqueness from vanishing conditional-cylinder coupling errors using reverse convergence and the completed Choquet theorem. `FK/NestedArbitraryInterior.lean` proves arbitrary-boundary exterior filters and two-sided maximal-stratum laws, and `FK/NestedFiniteAssembly.lean` gives exact cylinder/Bernoulli/reindexing identities and the single-scale `farConnection` estimate between actual finiteVolumeLaw probabilities. `FK/NestedConditionalAssembly.lean` now transports outer/inner finite-volume estimates to the true exterior conditional kernels on the product law, composes them with reverse convergence, and proves fixed-class DLR uniqueness from pairwise vanishing far-connection estimates via Choquet. Coupled `hgood` and the actual nested geometry/index selection supplying those pairwise finite bounds remain required; full Theorem 1.9 is not inferred. |
| **Theorem 1.10** | **Incomplete** | Inherits the strong-uniqueness gaps above as well as the enhanced phase window and actual AG shift. There is no unconditional whole-theorem declaration to use. |
| **Theorem 1.11** | **Conditional; spherical rotation duality proved, arbitrary continuous embeddings and infinite-cluster work open** | `FK/PlanarMatroid.lean` constructs general finite labelled cycle matroids and proves graphic-matroid Euler/FK duality from a supplied certificate. `FK/ThetaDuality.lean` constructs exact certificates for labelled cycles and parallel duals; `FK/GeneralizedTheta.lean` proves length-two bundled-cycle duality, and `FK/ArbitraryLengthTheta.lean` extends it to arbitrary positive branch lengths by exact subdivision-chain cardinality. `FK/UnicyclicForest.lean` extends exact two-face certificates to connected unicyclic graphs with arbitrary finite rooted-forest attachments. `FK/RotationSystemDuality.lean` constructs actual face quotients from darts and proves `GraphicDualCertificate` for connected spherical rotation systems; `FK/CellularExactnessRepair.lean` gives the alternative exact-chain route. `FK/WedgeDuality.lean` adds one-point assembly and `FK/FacialSubdivision.lean` proves exact certificate preservation under primal subdivision/facial duplication. `FK/PlaneCutCircuit.lean` proves finite dual-open interface circuits from a supplied certificate. `FK/PlaneClusterTarget.lean` only names the remaining dual-nonpercolation implication. `FK/EmbeddedCircuitSeparation.lean` proves genuine path-realization avoidance and sphere-confinement, including finite-cluster consequences from dual-open boundary circuits when the root is enclosed. `FK/InfiniteOpenCircuitUniqueness.lean` proves `GlobalAtMostOne` from a cofinal connected primal-open circuit exhaustion and finite ball preimages, without hiding the exhaustion construction from dual nonpercolation. `FK/PrimalOpenBoundary.lean` proves that circuit carriers are genuinely open-connected and constructs primal-open circuits on boundaries of finite dual-open components, including spherical/cofinal wrappers under explicit geometric data. `FK/DualFiniteEnclosure.lean` now constructs metrically cofinal finite connected simple-graph dual boxes from dual nonpercolation, preconnectedness, local finiteness and dual ball-properness. Their edge cuts are finite, trap the corresponding rooted dual-open components, and map to genuinely primal-open labels via the actual global edge equivalence. `FK/GlobalPrimalCompatibility.lean` now handles noninjective parallel-label collapse and exact dual-configuration restriction through explicit labelled/global embeddings, transports circuit-connectedness to the original global graph, and concludes its actual `GlobalAtMostOne` from cofinal compatible boundary circuits and primal properness. `FK/PlaneDualWindowCompatibility.lean` additionally lifts global open walks under dual-vertex injectivity and component coverage, identifies labelled vertex cuts with actual global edge cuts, constructs rotation-system embeddings, and derives metric-box coverage from boxwise vertex/edge incidence. Realizing that incidence and the graphic certificate, the cofinal Jordan outer-circuit and radius data, and primal properness remain explicit inputs. Arbitrary continuous realizations, the full exhaustion argument from dual nonpercolation and full strong uniqueness remain open. |
| **Lemma 2.1** | **Nested coupling and substantial arbitrary-boundary filter laws proved; coupled `hgood` and arm estimate missing** | `FK/NestedFiniteCoupling.lean` constructs the actual FK/FK/Bernoulli triple for arbitrary finite boundary setoids and proves all marginal/restriction identities and conditional equation (9). `FK/NestedArbitraryInterior.lean` contracts the fixed exterior/wired graph to an effective boundary, preserving arbitrary cross relations, and obtains exact component/weight and normalized exterior-filter identities. Its two-sided specialization permits an arbitrary shared left setoid and independently arbitrary right setoids with no cross-summand wiring, and proves their normalized maximal-stratum configuration laws equal. General cross-wired comparison still needs effective-boundary compatibility, and transport through the common-upper nested coupling to `hgood` is not yet proved. The intended nested-box event and vanishing arm error also remain. |
| **Proposition 3.1(1)** | **Proved for interior parameters and exact finite dynamics inputs** | `FKEnhancement.graphConnectionEvent_lower_comparison` in `FK/LowerCutsetComparison.lean`: $0\lt q\lt1$, $0\lt r\lt1$, actual FK at parameters `(q,r)`, arbitrary enhanced set, positive clocks, full schedule, exact auxiliary enumeration. The ordinary FK stochastic comparison is against the lower enhanced product. |
| **Proposition 3.1(2)** | **Proved in the corresponding interior direction** | `FKEnhancement.graphConnectionEvent_upper_comparison` in `FK/UpperCutsetComparison.lean`: interior $q\gt1$ and $0\lt r\lt1$. It retains FK as the middle coordinate and the upper enhanced product as the dominant law. |
| **Proposition 3.2(1)** | **Proved for interior $q<1$ and $0\lt p\lt1$** | `FKEnhancement.graphConnectionEvent_upper_path_comparison` in `FK/UpperPathStationarity.lean`: actual FK PMF stochastically below the exact upper open-path enhancement. The ordered outer pair is stationary and the FK middle chain starts at its ordinary lower marginal. The canonical wrapper needs no explicit clock or schedule. |
| **Proposition 3.2(2)** | **Proved for interior $1<q$ and $0\lt p\lt1$** | `OpenPath.LowerPathCoupling.lower_path_comparison_of_one_lt_q` constructs the all-closed ordered joint path/FK dynamics and proves exact lower path-enhanced domination. No joint limit or externally supplied stationary coupling is assumed; the canonical wrapper constructs uniform clocks and schedules. |
| **Proposition 4.2** | **Geometric DLR star/cycle sandwiches and generic weak-limit transport proved; AG shift and final assembly remain** | `FK/Proposition42Interior.lean` and `FK/FKWeakLimitActiveDevices.lean` prove exact active-device comparisons for actual DLR laws and genuine `IsFKLimit`s. `FK/FKQuasiTransitiveDevices.lean` constructs separated global families and uniform bounds. `FK/StarBoundaryCutset.lean` and `FK/CycleBoundaryPaths.lean` supply genuine localized stars and complementary cycle walks with singleton-center wiring and injectivity restrictions kept explicit. `FK/GeometricActiveComparisons.lean` chooses canonical whole-device containment admissibility, proving it eventually and deriving every selected pivot's eventual activation. It completes both the $q<1$ star-lower/cycle-upper and $q>1$ cycle-lower/star-upper geometric DLR sandwiches, with quasi-transitive corollaries constructing the actual separated bounded-distance families. The geometric DLR law, box data, vertex-map injectivity and source graph hypotheses remain inputs. The AG strict shift and completed weak-limit/theorem assembly are not inferred. |

## What is already unconditional

These are substantive lemmas, not definitions of an assumed model:

- **Finite FK:** actual normalized FK PMFs/measure and weights, free/wired
  component calculations, exact off-edge conditionals, comparison with
  independent Bernoulli bounds, and $q=1$ specialization.
- **Glauber dynamics:** singleton conditional-refresh invariance, FK modified
  block invariance over $0\lt p\le1$, duplicate-free total refresh identities,
  positive-power reachability, variation contraction and arbitrary-initial-law
  convergence in the interior. A stationary-support variant permits zero mass
  away from the stationary support.
- **Closed-cutset comparison:** exact block-level product stationarity,
  identifications of certificate probabilities, order-preserving triple updates,
  and both final actual-model comparisons listed above. It does not need an
  enhanced limiting law or an externally supplied ordered joint process.
- **Enhancement witnesses:** explicit closed cutsets at nonloops after wiring,
  finite routes for nonforest graphs, rate identities and positivity in the
  appropriate q-direction. These witness the possibility of strict improvement
  but are not by themselves the comparison inequality.
- **Infinite volume:** actual finite-box FK kernels, arbitrary wiring
  partitions, measurability and DLR equations, coherent-convention uniqueness
  under at most one infinite exterior cluster, weak-limit/DLR class wrappers,
  and actual all-open/all-closed endpoint laws with endpoint enhanced
  comparisons.
- **Tail and mixtures:** ordered triple gluing, finite-exterior/tail sigma
  relations, exterior conditional DLR preservation, tail-zero-one for extremal
  DLR laws, and equality from a kernel mixture of a known common extremal law.
- **Geometric conventions:** actual exterior merge/finite-separation data and
  DLR/Gibbs transport under a global at-most-one-cluster hypothesis, with finite
  singleton positivity deriving exterior uniqueness from global uniqueness.
  Endpoint classes and the corresponding weak-limit implications are exact.
- **Exterior identification:** DLR conditioning is exactly the global FK
  conditional law on every event supported in a finite box, with arbitrary setoid
  wiring; exterior-to-unconditional $L^1$ convergence follows under extremality.
- **Downward conditioning:** common representatives on the tail infimum,
  decreasing orthogonal-projection convergence, exterior-to-tail $L^1$
  convergence for $L^2$ observables, and a stronger equality theorem for
  extremal DLR laws from eventual agreement of exterior conditional laws.
- **Exploration:** canonical outer regions are minimal closed regions;
  frontier edges are closed; separated events are exhausted by disjoint region
  strata; exterior-fiber conditioning is the correct `PMF.filter`; separated
  interior weights factor by a *fixed* exterior component count; hence the
  conditional interior law is the actual free-interior FK law. Graphs with
  loops, parallel labels, and setoid wiring are handled.
- **Closed-cutset and open-path comparisons:** stationary ordered pairs in both
  parameter directions, exact finite-time FK-middle marginals, full block
  invariance and limiting comparisons. `FK.CanonicalDynamics` enables all four
  propositions without supplied clock/schedule data.
- **Finite Theorem 1.2:** actual normalized FK measures in both directions, with
  strict enhancement at a selected edge of each nonempty enhancing family.
- **Finite Markov factorization:** actual free FK products on disjoint graphs,
  and the filtered FK law on all-closed exterior strata, including independent
  finite products for an arbitrary finite family of summands.
- **Planar matroid duality:** general finite labelled forests, independence,
  basis/rank and component identities, plus Euler and actual FK duality from a
  `GraphicDualCertificate`. This is substantive finite geometry, not a supplied
  general plane embedding or infinite-cluster theorem.
- **Planar special cases:** exact finite PMF duality for labelled forests with
  one-face loop duals and certified labelled cycles with two-face parallel
  duals; the latter includes a genuine two-vertex/two-edge example.
- **Critical-window components:** essential-edge versus double-ray geometry,
  bounded-distance device packing, enhancement continuity and uniform compact
  positivity, exact FK-parameter conversion and inverse formulas, monotone
  analytic profiles, the actual increasing percolation event, and the first-loss
  pivot-peeling, bounded-local probability transport and finite Margulis–Russo
  formulas in `FK.AGPeeling`, `FK.AGPivotTransport`, and `FK.MargulisRussoFinite`:
  $\delta^{|R|}$ likelihood ratios, fibre bounds $2^{|R|}$, and exact
  pivotal derivatives including endpoints. `FK.AGDifferential` also proves
  joint bond/activation derivatives and $(\delta/2)\,\partial_p\tau\le\partial_s\tau$
  from actual expected pivot counts for the one-edge OR gadget, plus its
  finite-arm specialization. `FK.AGInfiniteLimit` proves the exact normalized
  infinite OR-product marginal and its limiting percolation probability;
  exhaustion and derivative/limit interchange are still missing. `FK.AGStrictShiftExample`
  gives one concrete strict shift only for an explicitly inhomogeneous,
  non-locally-finite path/star product, not a general AG or locally finite shift.
  `FK.AGDeviceEssentiality` additionally proves genuine double-ray essentiality
  for shared activations and quasi-transitive template/star/cycle packings; the
  general strict reference shift is still missing.

## The remaining mathematical obligations

The repository should not be described as finished until at least these are
closed or the intended scope is explicitly narrowed:

1. **Aizenman–Grimmett reference theorem.** Construct the reference zero/one
   percolation conclusion for small decrements and increments of the essential
   enhanced product, including the semifinite/criticality hypotheses actually
   used. The new constructed-graph sleeve theorem gives real replacement
   geometry and exact pivot ratios, but not its uniform packing, summation,
   integration or reference law. The full reference argument remains needed.
2. **Proposition 4.2 completion and Aizenman–Grimmett bridge.** The geometric
   DLR star/cycle sandwiches, canonical containment/admissibility, localized
   certificates and quasi-transitive device packings are proved. Transport
   these through the intended FK weak-limit/theorem pipeline and obtain the
   essential-enhancement reference shift, rather than further weakening those
   already proved inputs.
3. **Complete Lemma 2.1.** Starting from the constructed nested finite coupling
   and exact single-scale finite-box bound, identify the common free interiors
   on genuine global maximal strata, discharge `hgood`, and instantiate the
   eventual nested indices/events with a vanishing conditional-cylinder error.
   The remaining work is not a second-marginal identity or a generic cylinder
   adapter; those are now proved.
4. **Convention and percolation geometry.** Complete Proposition 1.8(2)'s
   weak-limit half by obtaining fixed-source DLR membership for wholly
   unrelated interior boundary sequences, whether by local stabilization or a
   different valid argument. `NoncoherentFiniteEnergy` already supplies their
   exterior uniqueness without DLR; it does not construct the DLR source.
   All-rate coherent and deterministic endpoint closure remains separate.
   Proposition 1.8(1) and the DLR tail Choquet decomposition are already proved,
   so no further non-extremal Gibbs decomposition remains here.
5. **General planar topology.** Metric finite dual boxes, connected primal-open
   boundary circuits and an exact labelled/global configuration transport are
   now available. Instantiate that compatibility layer with actual plane-dual
   box embeddings and select a Jordan enclosing circuit with cofinal radius.
   The remaining geometric supply and primal properness must reach the original
   global configuration before `GlobalAtMostOne`; continuous-embedding and
   enhanced dual comparison inputs remain.
6. **Assemble numbered theorems.** After those inputs exist, make and audit
   explicit statements of Theorems 1.4, 1.10 and 1.11 (and the
   graph-qualified Theorem 1.9 as appropriate), with no leftover paper
   obligations hidden inside arguments named `hAG`, `hseq`, `hmaps`, `heuler`,
   and similar.

## How to check this table against the source

Read a displayed theorem statement in the paper, locate the named Lean module,
and expand every binder. If an implication supplies a step required by the
paper, the wrapper is conditional even if it compiles without `sorry`.
Conversely, extra hypotheses for an auxiliary proof algorithm (positive clock
law or full enumeration) can be instantiated canonically and need not indicate
an unproved paper hypothesis when the constructed enhanced law and finite FK
measure are unchanged. `FK.CanonicalDynamics` supplies precisely those
instances: uniform positive clock mass, a duplicate-free auxiliary list, and a
complete schedule on each nonempty finite edge type.

The source-specific corrections and representation conventions are in
[ERRATA-AND-DEVIATIONS.md](ERRATA-AND-DEVIATIONS.md). The axiom-check
instructions are in [START-HERE.md](START-HERE.md).
