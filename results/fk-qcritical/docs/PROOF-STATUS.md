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
| **Theorem 1.4**, extended phases | **Conditional; AG and assembly missing** | Device packing and route certificates, analytic decrement/increment monotonicity, phase-law bridges and percolation event are proved. `FK.EssentialWindow` and `FK.AGWindow` still require reference shift hypotheses. `hAG` must be constructed, not renamed. |
| **Proposition 1.8(1)** | **Incomplete; reverse convergence is now proved** | `FK/ExtremalTail.lean` proves tail triviality and mixture uniqueness around actual DLR classes. `FK/BackwardConditional.lean` proves downward $L^1$ convergence for $L^2$ observables along exterior sigma-algebras and uses subsequences, strengthening the uniqueness interface to eventual agreement of actual exterior conditional probabilities. The exterior conditional expectation is now identified with the actual finite FK conditional law on every supported event. Simultaneous weak limits and Choquet representation remain; backward convergence is no longer an input. |
| **Proposition 1.8(2)** | **Gibbs-to-Gibbs and endpoint weak limits proved; locally constant interior closure proved, general interior passage open** | `FK/ConventionTransport.lean` and `FK/ConventionEndpoints.lean` prove geometrically compatible convention transport under global at-most-one-cluster throughout $p\le1$, plus exact endpoint DLR classes and endpoint weak-limit transport. `FK/InteriorWeakLimit.lean` proves weak closure for continuous FK specifications, establishes continuity for locally constant boundary partitions, and shows canonical coherent weak limits in that scoped class are Gibbs. Arbitrary interior boundary sequences and nonlocal free/wired interior convergence remain open. The global connectivity model is a countable simple graph. |
| **Theorem 1.9**, classical subcritical strong uniqueness | **Conditional and graph-dependent** | Generic ordered coupling, closed-boundary exhaustion, tail-zero-one, and equation (9) infrastructure are proved. The actual ordered exploration coupling, identification of its conditional limit with DLR expectations, reverse convergence, Choquet decomposition, and graph-specific Bernoulli subcriticality still have to be combined. |
| **Theorem 1.10** | **Incomplete** | Inherits the strong-uniqueness gaps above as well as the enhanced phase window and actual AG shift. There is no unconditional whole-theorem declaration to use. |
| **Theorem 1.11** | **Conditional; finite matroid duality proved, embedding and infinite-cluster work open** | `FK/PlanarMatroid.lean` constructs general finite labelled cycle matroids, proves graphic-matroid Euler and actual FK duality. `GraphicDualCertificate` still must be constructed from the intended plane embedding. Dual exhaustion, dual-to-primal infinite-cluster control and full strong uniqueness remain open. |
| **Lemma 2.1** | **Geometry and Markov factorization proved; coupling missing** | See the exploration section below. `FK/MarkovFactorization.lean` also proves exact free-component products and closed-exterior conditional product laws. Sequential ordered coupling, preservation through its exploration, and the resulting conditional marginals remain to be proved. |
| **Proposition 3.1(1)** | **Proved for interior parameters and exact finite dynamics inputs** | `FKEnhancement.graphConnectionEvent_lower_comparison` in `FK/LowerCutsetComparison.lean`: $0\lt q\lt1$, $0\lt r\lt1$, actual FK at parameters `(q,r)`, arbitrary enhanced set, positive clocks, full schedule, exact auxiliary enumeration. The ordinary FK stochastic comparison is against the lower enhanced product. |
| **Proposition 3.1(2)** | **Proved in the corresponding interior direction** | `FKEnhancement.graphConnectionEvent_upper_comparison` in `FK/UpperCutsetComparison.lean`: interior $q\gt1$ and $0\lt r\lt1$. It retains FK as the middle coordinate and the upper enhanced product as the dominant law. |
| **Proposition 3.2(1)** | **Proved for interior $q<1$ and $0\lt p\lt1$** | `FKEnhancement.graphConnectionEvent_upper_path_comparison` in `FK/UpperPathStationarity.lean`: actual FK PMF stochastically below the exact upper open-path enhancement. The ordered outer pair is stationary and the FK middle chain starts at its ordinary lower marginal. The canonical wrapper needs no explicit clock or schedule. |
| **Proposition 3.2(2)** | **Proved for interior $1<q$ and $0\lt p\lt1$** | `OpenPath.LowerPathCoupling.lower_path_comparison_of_one_lt_q` constructs the all-closed ordered joint path/FK dynamics and proves exact lower path-enhanced domination. No joint limit or externally supplied stationary coupling is assumed; the canonical wrapper constructs uniform clocks and schedules. |
| **Proposition 4.2** | **DLR active-device sandwiches proved; weak-limit rate transport proved, full weak-limit device assembly open** | `FK/Proposition42Interior.lean` proves exact two-sided DLR comparisons for interior $q<1$ and $q>1$ from actual separated star/cycle devices, cardinality bounds and path semantics. `FK/WeakLimitCylinderTransport.lean` proves all four actual finite-to-weak-limit comparisons with exact enhanced-rate inputs and cylinder-profile convergence. These use normalized FK measures and canonical finite dynamics, with arbitrary DLR exterior marginals handled by compProd integration. The active-device weak-limit packaging and geometric construction of device hypotheses remain open. Older `FKLimit.proposition_4_2_*_of_finite_comparisons` are explicitly legacy opposite-sandwich reductions. |

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
  pivotal derivatives including endpoints. None is the strict critical shift itself.

## The remaining mathematical obligations

The repository should not be described as finished until at least these are
closed or the intended scope is explicitly narrowed:

1. **Aizenman–Grimmett reference theorem.** Construct the reference zero/one
   percolation conclusion for small decrements and increments of the essential
   enhanced product, including the semifinite/criticality hypotheses actually
   used. This is needed even though the paper cites the theory.
2. **Interior class-level Proposition 4.2.** Instantiate its finite-volume
   DLR/limit inputs using the actual enhanced comparisons, not another weaker
   abstract conditional.
3. **Complete Lemma 2.1.** Form the ordered sequential exploration coupling,
   identify its conditional free-interior laws on the actual exploration
   strata, and derive the equation-(9) coupling estimate needed by Theorem 1.9.
4. **Choquet decomposition and actual exterior identification.** Reverse
   conditional-expectation convergence and finite-box FK/exterior identification
   are proved. Establish the Choquet existence/representation
   part needed to infer ordinary DLR uniqueness from extremal uniqueness.
5. **Convention and percolation geometry.** Complete Proposition 1.8, connect
   nonpercolation to closed exterior regions in every intended class, and
   construct the relevant critical-window consequences.
6. **General planar topology.** Add a meaningful embedding/face model, prove
   Euler's relation and exterior-component duality, and show the absence of an
   infinite dual cluster forces at most one infinite primal cluster on the
   intended exhaustion. Supply infinite-volume sharpness and enhanced dual
   comparisons as needed. Finite forest/cycle duality is much weaker.
7. **Assemble numbered theorems.** After those inputs exist, make and audit
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
