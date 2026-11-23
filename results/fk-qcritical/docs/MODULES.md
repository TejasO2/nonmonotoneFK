# Module guide

Lean module `FK.X` is in `FK/X.lean`. `FK.lean` imports the public set of
modules and upstream library entry points, so `import FK` is the usual entry
point. `Audit.lean` is a separate executable audit; it is not a theorem root.
The following grouping is conceptual, not a synopsis of the paper's dependency
order. Read the actual imports when editing.

## Finite FK model and enhancement certificates

| Module | Role |
|---|---|
| `FiniteModel` | Labelled multigraphs, wiring setoids, configurations, components, normalized FK weights, PMFs and measures, endpoint identities. |
| `FiniteFiber` | Off-edge fibers and product-weight manipulations used for exact conditional normalization. |
| `ComponentUpdate` | Precise component changes after setting one edge, including endpoint-connectedness case splits. |
| `FiniteComponentCounts` | Additional actual multigraph component/counting facts, forest formulas and comparison support. |
| `FiniteConditional` | Equation (2), the exact ordinary FK singleton conditional. |
| `FiniteComparison` | Equation (3), stochastic bounds and exact conditional heat-bath bridge. |
| `ClassicalOne` | The $q=1$ FK law equals the product Bernoulli law. |
| `MultigraphEnhancement` | Closed-cutset and open-path certificates on wired labelled multigraphs, positivity of enhancement in the appropriate direction. |
| `CycleEnhancement` | Cycle-based certificate constructions and route supports. |
| `OpenPathEnhancement` | Finite-path enhancement definitions, rate identities and product-law comparison infrastructure. |
| `ConditionalLimitUniqueness` | Conditional-limit uniqueness tools used before the subsequent finite/infinite bridges. |

## Glauber dynamics and ordered finite couplings

| Module | Role |
|---|---|
| `Glauber` | Finite static laws, heat-bath updates, sequential clocks, invariance, irreducibility, aperiodicity, Doeblin contraction and convergence. |
| `FKGlauber` | Exact FK modified-block stationarity and arbitrary-initial-law convergence on actual finite graphs. |
| `OrderedFinite` | Ordered finite Bernoulli products, heat-bath order preservation and iteration. |
| `JointProductInvariance` | Independent finite products and their projections, full auxiliary refresh, exact enhanced-block product invariance in both directions. |
| `PathProductInvariance` | Path-specific block normal forms and exact sequential invariance of the lower path product. |
| `LowerPathStationarity` | Auxiliary path event probabilities and the actual lower path-product convergence theorem. |
| `LowerPathCoupling` | Ordered lower path/FK dynamics from all-closed state; exact marginal projections and Proposition 3.2(2) for $1\lt q$. |
| `UpperPathStationarity` | Stationary ordered upper-path pair, bit/FK transport, and Proposition 3.2(1) for $0\lt q\lt1$. |
| `CanonicalDynamics` | Uniform positive clocks, exact auxiliary list and complete schedule; wrappers for all four finite enhanced comparisons. |
| `Theorem12Less` | The finite enhanced comparison of Theorem 1.2 for $0\lt q\lt1$: strict lower cutset and strict upper path. |
| `Theorem12Greater` | The finite enhanced comparison of Theorem 1.2 for $1\lt q$: strict lower path and strict upper cutset. |
| `Theorem12Fidelity` | Normalized enhanced-rate profiles, unit-interval bounds and strict witnesses in the paper's $p+\varepsilon$ and $p-\varepsilon'$ notation for each case. |
| `Theorem12Audit` | Supplemental finite-comparison audit and statement-inspection commands. |
| `FidelityAudit` | Supplemental source-fidelity audit surface for weak limits, device transport, the AG edge gadget and planar special families. |
| `TripleCoupling` | General PMF ordered triple glue constructions and the associated inequality/ordering utilities. |
| `Coupling` | PMF coupling and stochastic-order tools. |
| `ClassicalCoupling` | Classical coupling/comparison helpers, closed region/nonpercolation support. |

## Enhanced comparisons (paper Section 3)

| Module | Role |
|---|---|
| `Proposition31All` | Cutset enhancement definitions, rates, exact averaged update families and limiting comparison infrastructure. |
| `Proposition32` | Open-path modified update framework and limiting comparison wrappers; some whole-comparison inputs remain conditional. |
| `ClosedCutsetBridge` | Actual FK connection-event bridges and one-edge ordinary/enhanced ordered triple updates. |
| `LowerCutsetChain` | Exact enhanced/auxiliary block normal forms, lower cutset stationary pair and stationary-support Doeblin contraction. |
| `LowerCutsetComparison` | Actual $0\lt q\lt1$ lower enhanced cutset comparison for interior edge weights, through stationary outer pair and FK convergence. |
| `UpperCutsetChain` | Auxiliary-coordinate restriction identities, exact certificate probability and upper pair stationarity for the reverse direction. |
| `UpperCutsetComparison` | Actual $1\lt q$ upper enhanced cutset comparison with FK always the middle marginal. |

## Uniqueness and exploration

| Module | Role |
|---|---|
| `ClosedBoundary` | Open-cluster regions, closed boundaries and related finite/infinite graph geometry. |
| `ClosedBoundaryEventually` | Regions eventually containing finite vertex sets and nonpercolation exhaustion. |
| `StrongUniqueness` | Measure inequalities from ordered triple couplings and closed-boundary exhaustion. |
| `TailTriviality` | Zero–one sigma-algebras, independence, tail-condition probabilities and conditional-limit uniqueness wrappers. |
| `ConfigurationTail` | Explicit finite-exterior sigma-algebras and their tail infimum. |
| `ExtremalTail` | Exterior-conditioning and conditioning-preserves-DLR, extremal-tail zero-one, and uniqueness from a mixture of a common extremal law. Choquet existence is not included. |
| `BackwardConditional` | Descending orthogonal projection and actual conditional-expectation $L^1$ convergence for $L^2$ observables; exterior-tail convergence and the strengthened extremal-DLR equality theorem. |
| `ReverseMartingale` | Full a.e. reverse conditional convergence via finite reversals/upcrossings, cylinder-based weak convergence, and the inclusion of every extremal DLR law in the genuine finite-FK weak-limit class. Non-extremal Choquet is not supplied. |
| `TailChoquet` | Actual tail regular conditional mixture, exact Giry barycenter and DLR membership of almost every tail fibre. Simultaneous tail zero-one/extremality remains open. |
| `NewestModulesValidation` | Measurable DLR locus, literal Giry DLR support and conditional uniqueness from a.e. extremal tail fibres. |
| `TailConditionalTriviality` | Berti–Rigo simultaneous tail zero-one via exterior algebra covariance/backward convergence, a.e. extremal DLR fibres, full Choquet decomposition, uniqueness from extremal uniqueness and tail-fibre weak-limit membership. |
| `ExteriorIdentification` | Exact exterior FK conditional expectations from DLR, for arbitrary supported events; extremal-DLR exterior-to-unconditional $L^1$ convergence with eventual support proved from the exhaustion. |
| `ExplorationGeometry` | Canonical outer open region, maximal separated interior, closed frontier and disjoint configuration strata. |
| `ExteriorMarkov` | Exact actual FK `PMF.filter` disintegration onto exterior fibers; exterior wiring and free interior boundary where nonincidence holds. |
| `FreeInterior` | Disjoint-sum component counting and equality of a separated interior law with the actual free FK law. |
| `CanonicalFreeInterior` | Joins canonical outer-region strata with exact free-interior conditioning. Does not yet construct the full ordered sequential exploration coupling. |
| `FiniteGraphTransport` | Simultaneous vertex/edge transport preserves the actual free FK PMF. |
| `MarkovFactorization` | Actual binary and finite-family independent FK products on disjoint sums, exact all-closed-exterior PMF filtering and conditional independent free-interior factors. |
| `ExplorationSequential` | Sequential finite PMF pair extension, marginals, lengths and support ordering utilities. |
| `CanonicalDisintegration` | Canonical next-bit/finite-prefix conditional disintegration for pointwise-positive finite configuration laws. |
| `ConditionalRate` | Exact next-bit conditional probability computations and reconstruction on off-edge fibers. |
| `FKSequentialCoupling` | Ordered finite FK upper pairs and actual FK/FK/Bernoulli ordered triples. |
| `StoppedInterior` | Upper-history continuation and exact free interior law on closed-cutset regions. |
| `ExplorationTriple` | Glued three-history processes with exact projections and pointwise truth of support order. |
| `MaximalStrata` | Genuine canonical maximal exploration strata, normalized free interior laws of both coordinates and all-closed support witnesses. |
| `WiredRightInterior` | Free-left/right-supported graph splitting, arbitrary boundary components and normalized FK factorization on maximal regions. |
| `TransportBoundary` | Pullback boundary setoids and transport of actual finite FK PMFs. |
| `WiredStoppedInterior` | Exact prefix-chain continuation for right-supported wiring. |
| `WiredMaximalStrata` | Both normalized maximal-stratum free interiors with two arbitrary supported setoids and internal positivity. |
| `RightWiredSequential` | Configuration-level right-wired ordered triples, exact marginals and support order. |
| `RightWiredGood` | Per-prefix continuation and the non-assumed good-intersection equality. |
| `RightWiredEquationNine` | Scoped right-wired equation (9) for the actual finite interior event and canonical maximal Bernoulli stratum. |
| `RightWiredRestriction` | Transport of that estimate to a restricted second marginal and arbitrary-setoid FK measure, with observation factorization and second-marginal identity explicit. |
| `NestedFiniteCoupling` | Actual nested FK/FK/upper-Bernoulli coupling along `EΔ ⊕ EO ≃ EΣ`, with arbitrary boundary setoids, exact second and joint restrictions, outside equality, and conditional equation (9) with internal `hsecond`. Genuine global maximal-stratum `hgood` and the vanishing arm error remain. |
| `NestedArbitraryInterior` | Effective-boundary reachability and exact FK weight/filter factorization for arbitrary cross wiring, plus actual maximal-stratum conditional-law equality for independently arbitrary right setoids with a shared arbitrary left setoid and no cross-summand wiring. Nested coupling transport and general cross-setoid compatibility remain. |
| `NestedCommonUpperGood` | Actual common-upper `hgood` on right-disjoint two-sided extensions, with arbitrary shared left setoid and independently varying right setoids. Builds prefix conditioning, exact pair-good-mass equality and nested-triple projection. Metric exploration compatibility and strong uniqueness remain. |
| `NestedFiniteAssembly` | Exact finite-box cylinder/FK and global/finite Bernoulli adapters, arbitrary-boundary graph reindexing, and single-scale nested cylinder/arm bounds for actual finiteVolumeLaw probabilities. `hgood`, event realization, eventual index geometry and vanishing-limit inputs remain. |
| `NestedMetricGeometry` | Constructed metric boxes/exhaustion with exact global endpoints, nested edge splits, finite arm realizations and observation widths. Supplies canonical two-scale/two-limit estimates and proves maximal-stratum error inclusion from an explicit endpoint/root-radius split. Intended exploration split and `hgood` remain. |
| `NestedMetricRegionSplit` | Canonical vertex-region/internal/external-edge decompositions and their radial instance, exact maximal-stratum separation with all-closed support and finite arm inclusion. Roots are the entire ball at radius R; no fixed-small-root growing-radius vanishing claim or `hgood` proof. |
| `NestedMetricRightExtension` | Right-extended finite boxes with actual small/large two-sided laws, exact internal observation cylinders, nested `hgood`, explicit open-path maps and maximal-stratum `hD`. Radial finite cylinder/arm bounds are proved without pretence that added labels form a standard larger metric box; full vanishing uniqueness remains. |
| `OrdinaryNestedGluing` | Exact normalized FK transport by surjective, possibly noninjective fibre-wired vertex gluing, with reachability/component-count identities and ordinary radial cylinder compatibility. The new source law still needs `hgood` and arm estimates. |
| `NestedMetricRightExtensionCompatibility` | Exact ordinary nested/right-extended edge-index identities and global-label calculations, both no-cross `largeSourceLaw` relations, a no-comap obstruction whenever left/right vertices are identified, and the cardinality obstruction to an ordinary metric/right-extended vertex equivalence. This delimits the model; it proves no positive gluing theorem. |
| `FixedRootObstruction` | On the semi-infinite path, one open radial crossing edge is outside the maximal stratum and forces bad-only root attachment to reach at least $R-1$. Includes the exact metricNestedEquiv form, no fixed root radius across scales, and positive whole-ball root attachment. Explored/random regions and `hgood` remain open. |
| `GeneralObstruction` | Graph-independent single-edge glue/open-walk identities and the obstruction to bad-only attachment from an external edge touching the split plus a disjoint far region vertex. Existence of that geometric configuration is an explicit input. |
| `NestedRadialCounterexample` | On the Hasse path, Bernoulli nonpercolation for every $p<1$ coexists with radial error mass at least $p$ at every positive radius. Includes exact distance/cut proofs and a root-attachment criterion producing genuine finite-root arms from failed maximal strata. |
| `NestedBadRootAttachment` | All-closed endpoint equality and the exact obstruction to all-configuration attachment; bad-only maximal-stratum fixed-root arms, explicit finite metric support, and nested/centered finite-volume cylinder estimates retaining `hgood`, bad-root attachment and endpoint geometry. No vanishing or strong-uniqueness inference. |
| `Theorem110Assembly` | One-sided ordered-coupling nonpercolation transfer, total DLR/FK-limit family uniqueness equivalence through Choquet, endpoint singleton families, and existence of some exhaustion with an FK weak limit by compactness. |
| `SubcriticalPercolation` | Bernoulli critical-monotonicity and $s<p_c\Rightarrow\theta(s)=0$, nonpercolation transfer to dominated FK limits, and a conditional Theorem 1.10 assembly retaining domination, Theorem 5.1, Prop 1.8(2) and fixed-class existence inputs. |
| `NestedBadRootArmVanishing` | Fixed-root one-scale centered cylinder errors tend to zero under Bernoulli nonpercolation, and two centered-exhaustion FK weak limits are equal under fully indexed split/endpoint/`hgood`/bad-only-root certificates. Conditional fixed-scale class only; split constructions remain inputs. |
| `NestedMetricConditionalAssembly` | Joins actual boundary/exterior evaluations of metric finite-volume laws to the diagonal conditional DLR assembly. Uses outer/inner scale `2n`, `m = 2n - width`, arm antitonicity and zero percolation; indexed maximal-split data discharge `hD`, leaving diagonal `hgood`. Fixed centered class only. |
| `NestedArmUniqueness` | Finite-root and metric-crossing errors vanish under nonpercolation, Bernoulli subcriticality from zero root-percolation, and weak-limit equality from nested bounds. |
| `NestedBoundaryUniqueness` | Conditional extremal and full DLR uniqueness from a vanishing conditional-cylinder coupling error, using reverse convergence and actual tail-extremal fibres. The finite coupling now exists; its free-interior equality and vanishing estimate remain inputs. |
| `NestedConditionalAssembly` | Outer/inner two-scale nested conditional errors, exact finiteVolume-to-exterior conversion on a product law, nonpercolation-vanishing arm errors and fixed-class DLR equality from pairwise finite-volume estimates. `hgood` and actual nested/index geometry still feed those finite bounds. |

## Infinite volume, conventions and endpoints
| `ExplorationAudit` | Supplemental principal audits for exploration/free-interior results; referenced by `Audit.lean`, not part of the normal proof API. |
| `RightWiredAudit` | Supplemental axiom surface for ordered triples, maximal strata, right-wired good equality and equation (9). |

## Infinite volume, conventions and endpoints

| Module | Role |
|---|---|
| `InfiniteVolume` | Finite-box measurability, FK kernels, DLR equations, weak-limit/coherent classes, integrated bounds and convention-uniqueness under at most one infinite exterior cluster. |
| `BernoulliFiniteBox` | Exact infinite Bernoulli product factorization into exterior and interior products; uniform local comparisons lifted to a full DLR law after matching exterior marginals. |
| `OnePointDetermination` | Full-support finite laws sharing singleton conditionals coincide; positivity forces full support and yields exact finite FK identification from the equation-(2) odds family. Includes heat-bath invariance equivalence and no infinite-limit claim. |
| `FullSupportNecessary` | Explicit distinct laws (`δ₀₀` and `(δ₀₀+δ₁₁)/2`) with a common one-edge conditional family, proving why positivity/full support is necessary for one-point determination. |
| `ConventionTransport` | Exterior-component geometry and geometrically certified free/wired conventions; DLR/Gibbs transport under global at-most-one-cluster using compProd sections and actual FK singleton positivity. |
| `ConventionEndpoints` | Deterministic endpoint DLR equations/classes, all-rate convention transport, and endpoint weak-limit transport. |
| `CoherentMixtures` | Arbitrary probability-weighted Markov-kernel mixtures and binary convexity of exact DLR/coherent classes, with actual kernel compProd and normalization. Coherent/global-uniqueness components may have different sources before target mixing. |
| `CoherentAllBoxes` | Genuine Markov kernel of global finite-box conditional laws, all-finite-box coherent conventions and DLR classes, exact larger-to-smaller-box DLR by the exterior conditional mixture, equivalence with testing any genuine exhaustion, and geometric/all-rate transport. Compatibility on every nested pair remains a real hypothesis. |
| `CoherentLimitAssembly` | Genuine weak convergence of normalized binary probability mixtures, exact exterior-marginal mixture and a.e. propagation, and DLR/Gibbs assembly for fixed, varying coherent and closed-exterior sources. All local constancy, stabilization, geometry and componentwise global-uniqueness hypotheses remain. |
| `CoherentAllBoxesAdapters` | Exhaustion-independence, all-box closed-exterior finite-volume and fixed-convention conditional-limit transport, and deterministic $p=0$/$p=1$ conditional/DLR weak-filter closures. No construction of conventions or noncoherent membership claim. |
| `InteriorWeakLimit` | Weak closure of actual DLR classes under continuous FK specifications; continuity for locally constant boundary partitions, canonical locally constant coherent weak limits, and geometric transport. Wholly unrelated noncoherent boundary sequences remain open. |
| `InteriorEndpointNormalization` | The same locally constant coherent weak-limit DLR transport extended from $0<p<1$ to every $p\\le1$ using the already proved endpoint transport. |
| `NonlocalGeometry` | Finite open-walk/component support stability and local constancy of every geometric boundary assignment at at-most-one-infinite-cluster exterior points. |
| `NonlocalWeakLimit` | Null-frontier cylinders and finite-index lower integrals, giving DLR weak closure with local constancy only a.e. under the limiting exterior law. |
| `NonlocalFiniteVolume` | Coherent arbitrary-exterior finite-volume weak limits under exterior at-most-one uniqueness, with target transport and closed-exterior specialization. Unrelated interior sequences remain open; all-rate completion follows in `EndpointGlobalFiniteEnergy`. |
| `GlobalFiniteEnergy` | Positive finite FK point-mass floors, close-box absolute continuity through weak limits, and pre-DLR global-to-exterior at-most-one uniqueness. Gives coherent arbitrary-exterior and fixed-specification DLR weak closure under global uniqueness for $0\lt p\lt1$; all-rate completion is supplied next. |
| `EndpointGlobalFiniteEnergy` | Exact arbitrary-exterior conditional-law limits at zero and one and fixed-specification DLR endpoint closure, plus all-rate coherent arbitrary-exterior Gibbs/DLR and fixed-specification closure. Does not solve interior noncoherent fixed-source DLR membership. |
| `NoncoherentFiniteEnergy` | Uniform one-edge FK closing ratios with no boundary coherence, exact $2^{|B|}$ fibre bounds, close-box absolute continuity through arbitrary `IsFKLimit`s, and pre-DLR global-to-exterior at-most-one uniqueness. Does not itself give fixed-source/target DLR membership. |
| `NoncoherentStabilization` | Joint local stabilization implies zero disagreement mass and convergence of varying lower integrals, yielding variable-source finite-box/exhaustion DLR closure and a geometric arbitrary-limit corollary under global uniqueness. Also strict countable-product and dense-probe diagonalization; induced specifications/full neighbourhood stabilization remain inputs. |
| `NoncoherentCounterexample` | Counterexample to the unrestricted fixed-source target: a constant fully wired one-edge `IsFKLimit` with global/exterior uniqueness that has no geometric DLR class. Exact free/wired mass calculations and exhaustive-box DLR obstruction; not a counterexample to the paper's infinite-graph theorem. |
| `NoncoherentClosedExceptional` | Nullity of the closure of constant-source disagreement characterizes stabilization; eventual agreement off a closed null set gives joint stabilization and varying-coherent-source/geometric/all-rate-specific DLR closure. A compact point-mass example has null dense disagreement and refutes the almost-everywhere-only shortcut. |
| `MainIntegration` | Correct paper stochastic direction, finite-to-limit comparison assemblies and device/phase weight conversions. |
| `EndpointIntegration` | Actual endpoint laws for the FK-limit/coherent-convention union and the enhanced comparisons at zero and one. |
| `Proposition42` | Infinite comparison and two-sided reduction machinery. The older declarations are valid legacy helpers, not a finished Proposition 4.2 for every intended enhanced input. |
| `EnhancedProducts` | Exact Bit/Fin2-to-Bool measure adapters and coordinatewise finite enhanced-product monotonicity. |
| `DLRCylinderTransport` | Box-local lower/upper comparisons through actual DLR compProd equations and finite-volume closed-exterior laws, without exterior-product equality. |
| `ActualDLRComparisons` | All four normalized DLR comparisons from canonical finite dynamics and exact cutset/open-path rates. |
| `DeviceBounds` | Closed/open cylinder product formulas and exact enhancement lower bounds from finite devices. |
| `Proposition42DLR` | Four active-device DLR comparisons with star/cycle parameter profiles. |
| `Proposition42Interior` | Two-sided active-device DLR sandwiches for interior $q<1$ and $q>1$. |
| `WeakLimitCylinderTransport` | All four actual finite-to-weak-limit enhanced comparisons with explicit exact-rate and cylinder-convergence inputs. |
| `FKWeakLimitActiveDevices` | All four active-profile weak-limit comparisons and both interior q sandwiches, deriving exact rates and cylinder convergence from explicit finite devices. |
| `Theorem11Abstract` | Abstract strong-uniqueness/planar-limit reduction with explicit remaining topology, duality and percolation inputs. |

## Duality, phases and critical windows

| Module | Role |
|---|---|
| `PlanarParameters` | Primal/dual FK parameter arithmetic. |
| `ConfigurationDuality` | Bernoulli and configuration duality maps. |
| `BernoulliDuality` | Product Bernoulli probabilities under the dual parameter and complemented configuration. |
| `FinitePlanarDuality` | Finite-plane weight proportions and normalized FK PMF duality. |
| `PlanarConditioning` | Conditioning on exterior fibres and the open-component boundary wiring mechanism. |
| `PlanarActual` | Connections between the finite-plane interfaces and the actual labelled FK model, including equation (12). |
| `ForestEuler` | Simple-graph forest Euler component/edge identities. |
| `LabelledForestEuler` | Labelled multigraph forest component identities with arbitrary wiring. |
| `PlanarForestDuality` | Actual FK dualities for labelled forests/loop duals and verified labelled cycles/parallel duals. Not general plane duality. |
| `PlanarMatroid` | Cycle matroids of arbitrary finite labelled multigraphs, exact forest/component/rank identities, graphic-dual Euler and actual FK duality. A `GraphicDualCertificate` is supplied; constructing it from a plane embedding and the infinite-volume arguments remain open. |
| `ThetaDuality` | Exact cycle-matroid duals and `GraphicDualCertificate`s for connected labelled cycles and their parallel-edge face duals, proved from explicit complementary bases. Not generalized theta or arbitrary plane duality. |
| `GeneralizedTheta` | Length-two internally disjoint terminal paths $K(2,|\iota|)$, explicit independence/bases/circuits and bundled-cycle matroid duality. Arbitrary path lengths are not covered. |
| `ConnectedCycleChainExhaustion` | One fixed connected locally finite square/pendant chain with a mixed configuration and proper realization: open-connected finite prefixes, cofinal spherical open circuits, an infinite component and fixed-configuration `GlobalAtMostOne`. Explicit geometry only. |
| `GeneralizedThetaWindow` | Exact two-branch circuits and bundled plane-dual certificates, explicit connected spherical realizations with open carriers, arc avoidance/crossing and closed-inner-branch non-all-open example. Finite rescaled windows only, no global Jordan/percolation conclusion. |
| `ArbitraryLengthTheta` | Indexed subdivision chains, exact origin-fibre cardinalities and graphic-dual certificates for arbitrary positive branch lengths, including a length-two-based alternative. |
| `UnicyclicForest` | Exact two-face graphic duality for connected unicyclic labelled multigraphs and arbitrary finite pendant-forest attachments, via graph certificates and explicit bridges. Not general plane embedding. |
| `CellularExactnessRepair` | Binary representability, exact face-boundary/transpose input, rank-nullity and exact cycle-matroid duality, with Euler and normalized FK corollaries. |
| `RotationSystemDuality` | Dart rotations, exact quotient faces and face-dual incidence, $\mathbb F_2$ two-cell identity, dual connectivity, and `GraphicDualCertificate` for spherical rotation systems. |
| `WedgeDuality` | Direct-sum matroid duality, primal/exterior-face one-point unions, pointed folds and exact cycle-chain certificates with face-count formulas. |
| `FacialSubdivision` | Primal subdivision and facial parallel extension: actual component, independence and basis computations preserving any existing graphic-dual certificate, including loops and parallel labels. |
| `CircleSeparation` | Metric-circle complement/path-component lemmas for concrete plane loops. |
| `SegmentSeparation` | Unique crossing of a straight segment from an open ball to an exterior point, with inside-prefix/exterior-suffix behavior, in arbitrary real normed spaces. |
| `CircularSegmentCertificate` | Concrete embedded circular-loop pair, exact face path components, non-radial dual arc and unique crossing, plus its one-loop graphic certificate. |
| `EmbeddedCircuitSeparation` | Actual edge-path realizations and crossing-controlled labels, sphere avoidance/finite-cluster theorems, and dual-open circuit separation with root-inside/exhaustion gaps explicit. |
| `OpenCutSeparation` | Geometry-free open cut criterion for at most one infinite cluster, companion closed-cut trapping and no-percolation, and spherical-circuit recovery. A finite dual-boundary construction remains the residual. |
| `StripDualCounterexample` | Connected locally finite three-row strip and face-index dual with infinite outer-face degree: dual nonpercolation coexists with two infinite primal components. Also the locally finite self-pairing counterexample to the bare graph-cardinality formulation; not a counterexample to Theorem 1.11. |
| `SeparatorCircuits` | Exact two-sided/complement-path-component interface, level-set and Minkowski-gauge convex-frontier separation, separator open-circuit uniqueness, conservative spherical adapters, scalable convex exhaustion, non-spherical strictness witnesses, and labelled dual/primal circuit transport. Actual embeddings/crossing/avoidance and dual nonpercolation remain. |
| `InfiniteOpenCircuitUniqueness` | Open-walk attachment to circuit labels and actual `GlobalAtMostOne` from cofinal connected primal-open spherical circuits with finite ball preimages. The exhaustion construction remains an input. |
| `PrimalOpenBoundary` | Connected circuit carriers, primal-open circuits on finite dual-open component boundaries, simple-edge collapse and cofinal spherical uniqueness assembly. Global box/Jordan construction, parallel-label compatibility and properness remain explicit inputs. |
| `DualFiniteEnclosure` | Metric properness and dual nonpercolation give monotone exhaustive finite connected dual boxes with closed boundaries. Their edge cuts are finite and primal-open under the prescribed global edge equivalence; rooted dual components are trapped. Labelled plane-dual and Jordan assembly remain. |
| `GlobalPrimalCompatibility` | Endpoint-preserving labelled/global embeddings with noninjective parallel collapse, exact restricted dual configurations, local-to-global open paths and global primal circuits. Converts cofinal compatible boundary circuits to actual global uniqueness under properness; constructing those circuits remains an input. |
| `PlaneDualWindowCompatibility` | Reverse global-to-local walk lifting under dual-vertex injectivity and component coverage, exact labelled vertexCut/global edgeCut equivalence, rotation-system embedding constructor and spherical boundary circuits from global component cuts. Metric enclosure supplies the coverage from box incidence; Jordan realization remains separate. |
| `JordanUnicyclicEnclosure` | Exact two-face exclusion forces the whole dual cut to be the unique primal-open cycle, with connectivity, spherical and polygonal metric proofs, and a fixed all-open scaled disjoint-union exhaustion. No general connected/dual-nonpercolating Jordan theorem. |
| `ConnectedUnicyclicWindow` | Exact equivalences cycle-open ↔ exterior exclusion ↔ full inside vertex cut equals the unique cycle, plus simple-quotient arc/crossing transport and a core-open/pendant-closed connected example with enclosure proofs. Finite rescaled windows only. |
| `PlaneCutCircuit` | Finite vertex-cut cocircuits and dual-open circuits transported through a supplied `GraphicDualCertificate`, including component-boundary reachability. No embedded Jordan or infinite-volume claim. |
| `PlaneClusterTarget` | Explicit definition of the still-unproved dual-nonpercolation/at-most-one-primal-cluster target. This module does not prove that proposition. |
| `PhasesCoordinate` | Regression proofs that Bernoulli(open)=rate and Bernoulli(closed)=complementary rate. |
| `EssentialEnhancement` | Essential edge as an edge on a double ray, and necessary finite-cycle/essential geometry. |
| `EssentialWindow` | Analytic profiles, compact-cover and positivity results, essential-enhancement and parameter comparison interfaces. |
| `AGWindow` | Actual percolation event, monotone bridge laws, FK-parameter inversions and window reductions that take strict reference shift `hAG` as input. |
| `MargulisRussoFinite` | Exact finite one-coordinate, selected-coordinate and homogeneous pivot derivatives, including endpoint one-sided derivatives and actual enhanced-rate normalizations. |
| `Theorem14` | Theorem 1.4-oriented finite critical-window wrappers; named-input hypotheses document what remains to be supplied. |
| `AGPeeling` | Deterministic first-loss pivot transfer for monotone finite events, including joint bond/activation coordinates and finite arm events. Does not prove the AG strict shift. |
| `AGEdgeGadget` | One-edge stochastic OR gadget, exact enhanced product law, bond-to-activation pivot conversion and finite summed pivot inequalities; essential double-ray activations and bounded-distance packing. Not general AG strict monotonicity. |
| `AGDifferential` | Joint bond/activation Margulis–Russo derivatives, positive interior minorant and $(\delta/2)\,\partial_p\tau\le\partial_s\tau$ from expected pivot counts, plus the genuine finite-arm specialization. No global strict shift. |
| `AGInfiniteLimit` | Nested-arm convergence to actual percolation, normalized infinite independent OR product and its exact Bernoulli marginal and enhanced percolation limit. No derivative-limit interchange. |
| `AGCurveIntegration` | Directional $(-c)D_p+D_s$ derivative and comparison-curve integration on interior boxes, normalized joint-law endpoint inequalities and finite-arm specialization. No strict gap claim. |
| `AGBoundedRangeImplant` | Shared-activation route/annular model, open-walk surgery and normalized bond-to-activation pivot bounds $\delta P\le2P$ and $\delta^{|R|}P\le2^{|R|}P$. Local sleeve construction remains separate. |
| `AGDeviceEssentiality` | Genuine double-ray essentiality for shared activations and quasi-transitive essential template/star/cycle packings, plus exact support-contained annular pivot comparisons. No strict-shift inference. |
| `AGSleevedAnnulus` | Constructed two-edge bypasses with one shared activation repairing every selected base bond, disjoint annulus/support, infinite-graph pivot conversions, exact finite-product ratios, and preserved local finiteness/connectivity. Vertex- and edge-transitive bases give quasi-transitivity; packing is supplied next. |
| `AGUniformSleevePacking` | Exact lifted-automorphism template transport including spoke reversal, and pairwise-disjoint whole-sleeve packings under base edge-transitivity with a double-ray seed. Includes bounded-distance pivots, size $\le3|S|$, no-overlap sums and pointwise overlap $\le1$; no stochastic/differential claim. |
| `AGSleeveDifferential` | Exact summed pivot bounds, general affine finite Margulis–Russo derivative and selected-coordinate slope for a single shared sleeve. Proves comparison-curve and actual normalized product endpoint inequalities with exact speed; multi-device/infinite-volume AG remains open. |
| `AGMultiDeviceIndependence` | Separately indexed activation product laws, exact profile/event marginals, per-device/total pivot estimates and normalized multi-device derivative/curve comparisons. Packed templates supply disjointness and exact/uniform base/activation support bounds; finite-device scope only. |
| `AGSleeveInfinite` | Exact finite-trace infinite-product laws, supported annular pivots and normalized trace comparisons, with genuine enhanced percolation by decreasing arms/continuity from above. One shared sleeve on connected locally finite countable graphs only; no multi-device reference strict shift. |
| `IndexedSleeveInfinite` | Finite indexed independent-activation marginals, supported trace/pivot/derivative and endpoint comparisons, and infinite-cluster comparisons through actual arms. Packed templates supply disjointness and exact moved-base size; no infinite-family/AG reference limit. |
| `AGPackingDensity` | Positive device density from bounded-distance cover/uniform small balls, inline matching density bounds, precise independent all-inactive cylinders, exponential tails, and finite graph/line-graph distance and local-finiteness bricks. |
| `AGPackingDensityExample` | Degree-two integer line with every bond AG-essential, three-periodic bounded-range devices at density $1/3$ and explicit activation-tail bounds; no critical-shift claim. |
| `AGPackedSleeveDensity` | Positive density of the actual uniform whole-template sleeve packing from pairwise-disjoint templates and bounded-distance cover; line-graph cover, uniform radius bound and linear growth remain explicit inputs. |
| `InfinitePackedSleeves` | Edge-unique arbitrary-index (not necessarily countable) measurable enhancement, finite incident trace bounds, exact decreasing-arm convergence and non-strict infinite-product arm/percolation comparison; also whole translated-template packing. No infinite derivative sum or reference strict shift. |
| `AGBoundedCoordinateBridge` | Overlap-tolerant bounded-coordinate comparison for finite independently activated families: nonnegative union sums, exact per-device pivot transport and differential curves, actual infinitePi arm/cluster comparisons by continuity from above. Common positive cardinality and finite devices remain; no full AG shift. |
| `AGFiniteReferenceCurve` | Actual finite-family monotone arm and percolation probabilities on the whole admissible independent comparison line, zero/nonzero phase propagation, and the explicit maximal time $T_{\max}=\min((p-a)/c,b-s)$ with both endpoint boxes. No infinite-index or strict critical conclusion. |
| `AGStrictShiftExample` | Concrete inhomogeneous path/star product with base critical $1$ and enhanced critical $0$ for $s>0$, using finite cylinders and second Borel–Cantelli. Not a generally applicable AG reference theorem. |
| `AGConstructedPathShift` | Homogeneous one-way path with independent ordinary bonds and one extra independent synchronized activation, giving exact percolation curve and a genuine strict shift to critical zero for every positive activation. The activation opens all edges: unbounded range, not bounded-range AG. |
| `BoundedRangeGraphShift` | Connected locally finite chained bundle graph with a two-edge route per bond/activation pair, exact independent OR products, and root percolation iff all bundles cross. Proves $p_c=1/2$ and enhanced $p_c=1/3$ at activation $1/4$, a one-edge-range strict shift. Deterministically open stems make the full graph law inhomogeneous; not the general AG theorem. |
| `FKQuasiTransitiveDevices` | True finite automorphism-orbit hypothesis, bounded degree, distance/ray transport and separated star/cycle device packing with uniform cardinal bounds. Finite-box certificate admissibility remains separate. |
| `StarBoundaryCutset` | Corrected finite local star cutsets, singleton-center boundary condition and a fully wired counterexample. Geometric/free/wired proofs use full-star containment and explicit vertex-map injectivity. |
| `CycleBoundaryPaths` | Complementary cycle walks lifted into compatible finite boxes, genuine auxiliary path families and the active-cycle upper DLR application under vertex-map injectivity. |
| `CycleBoundaryLowerPaths` | Lower open-path DLR comparison for $q>1$ and its two-sided geometric sandwich with actual complementary walks, star cutsets and exact parameter enhancement. |
| `GeometricActiveComparisons` | Canonical complete-device containment/admissibility and eventual activation, both geometric star/cycle DLR sandwiches and quasi-transitive packings with bounded-distance supply. The DLR law and all graph compatibility hypotheses remain explicit; no strict shift. |
| `AGPivotTransport` | Bounded-local fibres, independent-product probability ratio and activation-peel branch transport. An activation-free branch remains only an intermediate conclusion, not the global AG strict shift. |
| `MainIntegration` | Also the public adapter between the generic weak-limit and theorem-specific phase APIs. |

## Reused external code

`CurvatureVariance.Infra.Percolation.*` contains selected Scott
Armstrong/Ahmed Bou-Rabee percolation sources: product, connectivity, arm,
exploration and critical parameter interfaces.

`PercLib.Probability.Coupling.Monotone` supplies Tom Hutchcroft's monotone
product Bernoulli coupling, with the build dependencies it needs.

`OAI.Probability.CriticalPercolation.*` supplies a small selected closure from
OpenAI's math development: models and finite product-measure tools. Comparator
comparison files and files with intentional placeholders are not imported.

[THIRD_PARTY.md](../THIRD_PARTY.md) is the authoritative table of repositories,
revisions, licenses and included source groups. Nothing in those directories is
automatically a proof of any missing FK-specific theorem.
