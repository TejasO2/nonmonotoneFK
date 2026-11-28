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
| `UniformUpcrossing` | Filtration- and horizon-uniform upcrossing probability bound for reverse conditional expectations of $0\le g\le1$. This is a fibrewise martingale ingredient, not the random-region exhaustion, joint measurability, or Theorem 5.1 conclusion. |
| `RandomRegionConvergence` | Region-uniform tail-remainder estimates and an exact configuration-dependent-exhaustion comparison under the explicit `HasNetExteriorConvergence` input, which remains an assumption rather than a theorem from tail triviality. Includes a normalized diagonal-coupling obstruction and a finite atom Markov caution. |
| `RandomRegionL1Repair` | Replaces the pointwise net with the mean convergence genuinely used by the comparison. Bounded coupled conditionals plus eventual agreement identify the masses; tail-uniform estimates supply mean convergence for fixed exhaustions, and Fubini supplies it for an independent region parameter. Actual FKLimit types and default-heartbeat Lean 4.35 proofs, not a net upcrossing theorem. |
| `NetExhaustions` | Countably many exhaustions share one joint null set for both tail-conditional and tail-trivial-limit convergence. Includes a precise conditional criterion transferring such coverage to full net convergence, not a proof of it. |
| `TailChoquet` | Actual tail regular conditional mixture, exact Giry barycenter and DLR membership of almost every tail fibre. Simultaneous tail zero-one/extremality remains open. |
| `NewestModulesValidation` | Measurable DLR locus, literal Giry DLR support and conditional uniqueness from a.e. extremal tail fibres. |
| `ClusterCover` | Finite edge-avoiding cluster covers: finite edge changes preserve infinite open-cluster existence, directly in the walk semantics. |
| `ClusterTail` | Tail-measurable infinite existence and Kolmogorov zero–one for actual Bernoulli products. Ray and line counterexamples separate root/multiplicity events. |
| `TailSigmaBridge` | Exact tail-sigma characterization, Bernoulli 0–1, dichotomy and extremal DLR zero–one for existence; conditional at-most-one only, not Burton–Keane. |
| `ClusterTailExample` | Ray witness that a fixed root infinite cluster is not tail measurable. |
| `ClusterTailExample2` | Closing one integer-line edge splits one infinite cluster into two, so multiplicity sensing is not tail measurable; no constancy without graph invariance. |
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
| `SpecificationNesting` | General finite sub-box component-splitting and FK weight factorization with arbitrary boundary setoid and interior edges. Shows induced partition depends only on exterior and proves exact conditional FK-PMF ratios. Full conditional-filter/IsDLR packaging, vertex-level exhaustion compatibility and weak-limit Prop 1.8(2) remain. |
| `NestedRegionExploration` | Actual shell-first enumeration of an ordinary nested split. Filters the history continuation through the confined-stratum theorem to obtain free region FK interpolation and the pair good-intersection for region events. Metric/infinite-volume instantiation, triple-level identity and strong uniqueness remain open. |
| `NestedExteriorStrata` | Extends the same right-extended two-sided `hgood` to every exterior-only event contained in the separated stratum. The prefix proof preserves the exterior bits and matches the free interior continuation on both sides. Includes the resulting equation (9), the old maximal-stratum special case, and a nonvacuous right-summand case. Rectangle/metric nesting, restrictions on upper interior bits, DLR and uniqueness are not supplied. |
| `NestedFiniteAssembly` | Exact finite-box cylinder/FK and global/finite Bernoulli adapters, arbitrary-boundary graph reindexing, and single-scale nested cylinder/arm bounds for actual finiteVolumeLaw probabilities. `hgood`, event realization, eventual index geometry and vanishing-limit inputs remain. |
| `NestedMetricGeometry` | Constructed metric boxes/exhaustion with exact global endpoints, nested edge splits, finite arm realizations and observation widths. Supplies canonical two-scale/two-limit estimates and proves maximal-stratum error inclusion from an explicit endpoint/root-radius split. Intended exploration split and `hgood` remain. |
| `NestedMetricRegionSplit` | Canonical vertex-region/internal/external-edge decompositions and their radial instance, exact maximal-stratum separation with all-closed support and finite arm inclusion. Roots are the entire ball at radius R; no fixed-small-root growing-radius vanishing claim or `hgood` proof. |
| `NestedMetricRightExtension` | Right-extended finite boxes with actual small/large two-sided laws, exact internal observation cylinders, nested `hgood`, explicit open-path maps and maximal-stratum `hD`. Radial finite cylinder/arm bounds are proved without pretence that added labels form a standard larger metric box; full vanishing uniqueness remains. |
| `RandomClosedBoundary` | Configuration-dependent open-cluster regions and an explicit closed-boundary exhaustion from arbitrary cofinal finite connected bases; measurable strata, a.e. nonpercolation support, ordered-coupling closure and stack identities. Metric base instantiation and reverse-martingale assembly remain. |
| `RegionEdgeBox` | Finite interior edge boxes on actual closed-region frontiers, noninterior walk restriction and closed-free boundary facts, including eventual finite edge containment. |
| `FiniteVolumeDLR` | Actual finite-volume FK laws satisfy DLR at their own box with constant boundary, showing the fibre identity source class is inhabited. |
| `RegionStrata` | Walk restrictions through a closed region and exact random-region/product-stratum: frontier-closed exterior and forced interior connection. |
| `RegionFibre` | Measurable exterior extension and the actual exterior-induced boundary partition, with open-path fibre/countable-range measurability closure. |
| `RegionFibreIdentity` | Actual random-region DLR product identity: exterior restricted to frontier closure times free interior FK restricted to forced connectivity, plus one-box/free-frontier independence. All-box hypotheses remain. |
| `RandomRegionKernel` | Genuine random-region indices/exterior cutoffs with measurable finite strata and the correct forced interior connectivity. Proves per-stratum DLR factorization and a single countable-strata integral for arbitrary measurable interior-supported events and cylinders, with law-independent cross-multiplied conditionals and probability laws on attained strata. Not a full regular conditional kernel or Theorem 5.1; general C, reverse/martingale joint nulls, metric instantiation and general conventions remain. |
| `RegionKernelTotal` | Arbitrary measurable-event disintegration on all random-region strata, with explicit arbitrary-exterior slices and almost-finite-region/ordered-domination forms. Provides closed-frontier free-boundary conditional laws. Does not build the conditionally independent ordered coupling or the final tail/reverse-martingale uniqueness argument for Theorem 5.1. |
| `RegionFibreCounterexample` | Exact obstruction to the naive free random-region stratum: all-closed interior can be excluded by a nonbase vertex while free FK gives it positive mass. The cut-down by interior connection is necessary. |
| `RegionFiniteBox` | An actual `FiniteBox` on the closed region and exact exterior-partition/free-interior FK normalization. No random-fibre disintegration or Theorem 5.1 conclusion. |
| `ConfinedStrata` | Generalization to arbitrary separated exterior strata: pointwise factorization, fixed conditional region law on each stratum and the nested two-scale independence. Product prefix strata are a strict special case; no ordered-triple pretence. |
| `ConfinedStrataObstruction` | Two-vertex self-exterior-edge example with ambient weight $1/8$ vs proposed factorized $1/16$. Although confinement and matching hold, pointwise separation fails, so unrestricted continuation is impossible. |
| `ConditionalLaw` | Necessity of restricted-stratum capture of conditionals plus an explicit separated-failure example: conditioned region law differs from the free region FK specification. Finite scope only. |
| `PrefixContinuation` | Actual normalized prefix-filter marginal under boundary confinement, arbitrary-set factorization and same-region conditional FK law on every added stratum, including twoSidedBoundary. Nested-triple/metric/source transport and global `hgood` still remain. |
| `RegionConfinement` | Region continuation under arbitrary region setoid and explicit boundary confinement: confined reachability, interior graph/weight factorization and exact induced-region FK PMF. Prefix event/equivalence and weight-level continuation sums; no PMF prefix or `hgood` conclusion. |
| `ConfinementNecessary` | Cross-wired four-vertex obstruction with open exterior edge: the effective boundary is universal and cannot agree with the discrete region boundary, proving confinement cannot be removed. Auxiliary exact weight computation is documented separately. |
| `MetricInterior` | Any incident edge of a vertex at distance `<N` belongs to the radius-`N` metric box; hence such a vertex has no exterior boundary edge. Strict metric confinement of specific conventions is still to be checked. |
| `MetricRegionGood` | Metric complementary edges avoid the open region, distance-$r$ endpoints can violate right/fresh summands (with a line example), exact smaller-box two-sided graph transport, and the strict shell-freshness criterion. No generalized `hgood` or arm assertion. |
| `OrdinaryNestedGluing` | Exact normalized FK transport by surjective, possibly noninjective fibre-wired vertex gluing, with reachability/component-count identities and ordinary radial cylinder compatibility. The new source law still needs `hgood` and arm estimates. |
| `NestedMetricRightExtensionCompatibility` | Exact ordinary nested/right-extended edge-index identities and global-label calculations, both no-cross `largeSourceLaw` relations, a no-comap obstruction whenever left/right vertices are identified, and the cardinality obstruction to an ordinary metric/right-extended vertex equivalence. This delimits the model; it proves no positive gluing theorem. |
| `FixedRootObstruction` | On the semi-infinite path, one open radial crossing edge is outside the maximal stratum and forces bad-only root attachment to reach at least $R-1$. Includes the exact metricNestedEquiv form, no fixed root radius across scales, and positive whole-ball root attachment. Explored/random regions and `hgood` remain open. |
| `GeneralObstruction` | Graph-independent single-edge glue/open-walk identities and the obstruction to bad-only attachment from an external edge touching the split plus a disjoint far region vertex. Existence of that geometric configuration is an explicit input. |
| `NestedRadialCounterexample` | On the Hasse path, Bernoulli nonpercolation for every $p<1$ coexists with radial error mass at least $p$ at every positive radius. Includes exact distance/cut proofs and a root-attachment criterion producing genuine finite-root arms from failed maximal strata. |
| `NestedBadRootAttachment` | All-closed endpoint equality and the exact obstruction to all-configuration attachment; bad-only maximal-stratum fixed-root arms, explicit finite metric support, and nested/centered finite-volume cylinder estimates retaining `hgood`, bad-root attachment and endpoint geometry. No vanishing or strong-uniqueness inference. |
| `Theorem110Assembly` | One-sided ordered-coupling nonpercolation transfer, total DLR/FK-limit family uniqueness equivalence through Choquet, endpoint singleton families, and existence of some exhaustion with an FK weak limit by compactness. |
| `QOneLine` | Boundary-free normalized finite-box conditionals at $q=1$, fixed-exhaustion Bernoulli existence for every schedule, FK limit singletons, DLR membership/classification and the unique total FK family at every $p\le1$. No $q\ne1$ or subcritical claim. |
| `BoundaryRigidity` | Interior $p$: boundary-independence of finite FK laws forces $q=1$, via exact one-edge free/wired component weights and mass normalization. |
| `InfiniteSharpness` | A concrete one-box exhaustion at $q=2,p=1/2$ with two genuine different FK limits, proving the q-line collapse is essential for unrestricted schedules. |
| `Theorem110Strassen` | Bernoulli domination as event form ↔ genuine ordered coupling (via CountableStrassen), normalized transfer to a.s. no percolation, and general exhaustion-independent/geometric-family uniqueness assembly with h5_1/h518 retained. |
| `Theorem110GeomFamily` | Geometric convention FK-family, geometric weak limits of extremal DLR laws, Choquet identification, and a correct paper-class/subfamily containment. Arbitrary measurable-boundary union is not substituted. |
| `Theorem110Scope` | The one-edge unrestricted family has two limits and is not singleton, while geometric partitions/limits are necessarily free and exclude wired boundary. Shows why `FKFamilyGeom`, not arbitrary assignments, is needed. |
| `Theorem110OneEdgeInstance` | Nonvacuity: genuine finite-box conditional-law DLR, interior-restriction injectivity, free DLR class singleton, Bernoulli domination at $s=2/3$, and the full geometric Theorem 1.10 conclusion on that instance. |
| `PcPos` | Actual finite self-avoiding-walk enumeration and exact open cylinders give $\Pr(\mathrm{Arm}_n)\le(pd)^n$ whenever every vertex degree is at most $d$. Bernoulli percolation vanishes for $pd<1$, $1/d\le p_c$, and an explicit small-$p$ window has `FK.prime q p` below $p_c$ with no graph invariance or FKG. Bernoulli/comparison-rate only, no FK uniqueness. |
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
| `FKG.Basic` | Finite Boolean slice/reindexing machinery, lattice slices, monotone likelihood ratio, normalized Holley comparison and two-point Chebyshev identity. |
| `FKG.Main` | Complete finite-product FKG proof by induction on coordinates: positive log-supermodular weights give Harris-type covariance for increasing nonnegative observables. Unnormalized probability normalization is handled separately. |
| `FKG.General` | FKG on arbitrary finite Boolean index types, exact product-Bernoulli lattice condition/Harris and monotone-likelihood-ratio Holley comparison. |
| `FKG.FKCluster` | $\mathbb F_2$ edge span rank and corank, rank submodularity, corank supermodularity/antitonicity, empty corank and small examples. `WiredFKG` subsequently identifies the general corank with the actual component count. |
| `FKG.Mirror` | Antitone FKG form via bounded observables, with the explicit warning that a reversed lattice condition cannot be upgraded to negative association. |
| `FiniteTransport` | Finite weighted Hall transport and the genuine hard direction of Strassen on finite preorders and Boolean products, with exact probability marginals and order support. Includes iff characterization, finite-cylinder ordered couplings on countable coordinate types and domination transfer; the countable gluing/compactness step remains. |
| `StrassenCountable` | Full countable Strassen ordered coupling on Boolean products: finite-coordinate fibre gluing with exact prescribed ordered marginal, closed directed good sets and compact assembly, full pointwise-order support, asymptotic-projectivity for compatible cylinder systems and FK domination adapter. No FK-specific DLR theorem asserted. |
| `ConditionallyIndependentOrderedCoupling` | Disintegrates pairwise countable Strassen couplings over their common dominating marginal and takes the product kernel: three exact marginals, a.e. order, lower-cone support and a lintegral conditional-independence identity. Also proves ordinary ordered-triple existence iff both dominations hold. Does not construct the random closed-boundary filtration, DLR cones, or uniqueness assembly. |
| `CountableOrderedCoupling` | Finite-coordinate projection and graph/step disintegration identities and order-as-intersection for the countable Strassen extension; no gluing lemma claimed. |
| `WiredFKG` | Identity of the $\mathbb F_2$ corank with connected-component count, including arbitrary finite boundary setoids via deterministic block-representative wiring. Proves genuine normalized labelled-multigraph positive association, $p$-monotonicity and $\mathrm{FK}_q\le\mathrm{Bernoulli}(p)$ at $q\ge1$ with loops/parallel edges. $q<1$ supplies only the exact reversed/strict-obstruction lattice facts, no negative association. |
| `FreeFibre` | A.e. free-partition fibre identity for arbitrary measurable interior-supported events, directly from the actual DLR common integrand. Does not provide the random varying-filtration tower property. |
| `RegionFrontierDetermination` | Exact random-region stratum/fibre masses and countable-decomposition criterion: two laws with matching finitely-supported frontier-closed masses coincide. Does not obtain the common masses from ordered domination. |
| `CoFinalFreeUniqueness` | Reverse-martingale convergence for arbitrary DLR laws and uniqueness from an ordered triple with closed boundary boundaries infinitely often, including coherent/full-measure/subsingleton cases. Fixed exhaustion only, not adaptive regions. |
| `SourceConventionFree` | The source exterior-path partition is reference/free when every external incident edge is closed; sparse open-edge domination gives an honest special case. No general nonpercolating closed-boundary exhaustion is claimed. |
| `ClosedBoundaryObstruction` | A nonpercolating matching configuration on the integer line for which every finite interval has an open crossing edge, proving fixed box exhaustion cannot suffice without adaptive regions. |
| `LatticeSeparation` | Exactly verified mod-2 lattice circuit parity, handshake/avoidance-crossing, and at-most-one infinite open cluster from cofinal open incident-component circuits. Does not construct the required circuits; remaining Jordan/dual-nonpercolation geometry open. |
| `SpecificationDeviation` | DLR common-integrand/specification analysis and mean-deviation uniqueness, with cylinder generation, closed/constant/free conventions, increasing-event recovery and finite free/wired gap bounds. The vanishing inputs needed for Theorem 5.1 remain; it is not random-fibre uniqueness. |
| `GibbsOrder` | Boundary-wiring monotone likelihood ratio under $q\ge1$, using corank-rank diminishing returns and common new labelled-edge vectors. Proves finite-bounded/box/weak-limit free and wired sandwich and full Boolean cylinder agreement under mutual domination. Free/wired conditions are not global conventions; no canonical limit existence, cylinder-to-measure extension or at-most-one-cluster/final uniqueness claim. |
| `MonotoneLimitExistence` | Recovers exact pattern/cylinder masses from upper corners, derives weak convergence through closed-set cylinder approximations, and creates full-sequence FK weak limits from convergent or eventually monotone corners. No canonical free/wired construction. |
| `NestedMixture` | Aggregate for exterior-fibre normalization/mixture, nested-box transport and free-mass comparison, and full-sequence free FK limits of genuine growing vertex/edge families at $q\ge1$. Includes boundary-only wired setoid and path/loop instances; wired-family, canonicality, DLR and lattice boundary-field work remain. |
| `StageLawUpTBound` | Genuine finite-volume upper-corner monotonicity for a fixed finite vertex type with nested edge labels at $q\ge1$, through the verified FK edge-injection comparison. |
| `FixedVertexLimit` | Full-sequence FK weak-limit existence for a covering fixed-vertex nested-edge family and constant setoid, including the discrete/free one. Not growing-vertex or source-wired canonical limits. |
| `InfiniteVolumeFKG` | Actual arbitrary FK weak-limit positive association at $q\ge1$, covering all measurable increasing events. Finely supported box/event instances pass by clopen convergence then compact-neighborhood/inner-regularity to whole events. Includes up/down, parameter and abstract convergence-transfer forms and a non-vacuous $q=1$ instance. No limit existence, DLR or uniqueness conclusion. |
| `FKG.FKApply` | Exact corank-weight pair defect, log-supermodularity at $q\ge1$, reversed condition at $q\le1$, edge-activity Holley monotonicity and positive association for corank-weight increasing observables/events. The normalized labelled-multigraph instance is supplied by `WiredFKG`. |
| `OneEdgeNoEscape` | Sharp equivalence between the scalar conditional criterion and limsup/no-mass-escape, fixed-box far-vanishing, a moving-atom escape counterexample, and the exact two-valued equation-(2) rate orientation. Sufficient stabilization/event agreement/domination cases, not automatic FK escape bounds. |
| `ClopenEscape` | Converts clopen decreasing escape families and dominated increasing escape events into far vanishing, no-mass-escape and box-DLR reductions. Finite-stage identities, actual source escape inclusions and rate/event hypotheses remain explicit. |
| `ClusterEscape` | Infinite clusters meet every finite complement exhaustion, at-most-one-cluster kills the correct escape intersection, exterior-only wired walks force two escaping clusters, and nonpercolation kills their tails. Direct-wiring geometry only, not full source connectivity partitions. |
| `EdgeDomainMonotonicity` | Isolated-vertex component decomposition and exact closed-extension weight formulas leading to edge-injection monotonicity of normalized FK measures under explicit `PosAssoc`. Also a limsup/no-escape reduction from stage monotonicity. Does not instantiate `finiteVolumeLaw` exhaustions or prove the required model-specific far-connection estimate. The parser-safe identifier `sum_weight_closed_ext` preserves `sum_weight_closed'`. |
| `OneEdgeLimit` | Genuine finite-box one-point identity, sharp lower limit inequality for decreasing continuous rates, exact scalar criterion with arbitrary measurable off-edge tests, and box DLR under no-mass-escape and rate-identification inputs. Only liminf is automatic. |
| `StageInstantiation` | Proves model-level `PosAssoc` from the normalized FKG bridge and derives nested `finiteVolumeLaw` stage monotonicity for the fixed-vertex edge family. Gives a no-mass-escape theorem for increasing stage events at $q\\ge1$ and $0\\lt p\\le1$, with loop/parallel examples and a fully unconditional $q=1$ loop instance. Not `hfin`, general far-connection geometry, growing-vertex boxes, or general limit existence. |
| `FibreAssembly` | Actual exterior conditional-kernel disintegration: global equation-(2) singleton conditionals imply finite-box DLR, with a fibre-odds iff characterization. The boundary assignment and all integral hypotheses are explicit; infinite-limit conditional passage remains. |
| `IsolatedVertexLaw` | Carries arbitrary boundary setoids with completely free new vertices, proving an exact induced-connection graph isomorphism and component-count shift. Discards the resulting constant in actual normalized FK weights/PMFs and gives measure identities, including genuine `finiteVolumeLaw` equality for isolated-vertex boxes. Includes a one-edge wired counterexample. Does not instantiate `PosAssoc` or prove nested stage monotonicity/no-mass-escape. |
| `ForestBernoulli` | Exact normalized FK/weight factorization whenever component count plus open edges is constant; labelled free forests are Bernoulli at $p/(p+q(1-p))$, with exact partition functions, q-comparisons and a cycle non-affine obstruction. Arbitrary boundary setoids in the affine case; no infinite-volume extension. |
| `OnePointDetermination` | Full-support finite laws sharing singleton conditionals coincide; positivity forces full support and yields exact finite FK identification from the equation-(2) odds family. Includes heat-bath invariance equivalence and no infinite-limit claim. |
| `FullSupportNecessary` | Explicit distinct laws (`δ₀₀` and `(δ₀₀+δ₁₁)/2`) with a common one-edge conditional family, proving why positivity/full support is necessary for one-point determination. |
| `ConventionTransport` | Exterior-component geometry and geometrically certified free/wired conventions; DLR/Gibbs transport under global at-most-one-cluster using compProd sections and actual FK singleton positivity. |
| `ConventionEndpoints` | Deterministic endpoint DLR equations/classes, all-rate convention transport, and endpoint weak-limit transport. |
| `CoherentMixtures` | Arbitrary probability-weighted Markov-kernel mixtures and binary convexity of exact DLR/coherent classes, with actual kernel compProd and normalization. Coherent/global-uniqueness components may have different sources before target mixing. |
| `CoherentAllBoxes` | Genuine Markov kernel of global finite-box conditional laws, all-finite-box coherent conventions and DLR classes, exact larger-to-smaller-box DLR by the exterior conditional mixture, equivalence with testing any genuine exhaustion, and geometric/all-rate transport. Compatibility on every nested pair remains a real hypothesis. |
| `CoherentLimitAssembly` | Genuine weak convergence of normalized binary probability mixtures, exact exterior-marginal mixture and a.e. propagation, and DLR/Gibbs assembly for fixed, varying coherent and closed-exterior sources. All local constancy, stabilization, geometry and componentwise global-uniqueness hypotheses remain. |
| `CoherentAllBoxesAdapters` | Exhaustion-independence, all-box closed-exterior finite-volume and fixed-convention conditional-limit transport, and deterministic $p=0$/$p=1$ conditional/DLR weak-filter closures. No construction of conventions or noncoherent membership claim. |
| `FKLimitClosure` | Quantitative FK reconstruction error, weak DLR closure under eventual a.e. agreement with a continuous specification, compact/coarsened limit existence, and $\mathbb Z$ projection preparation. A global one-edge example proves raw measurable DLR classes need not be sequentially closed. |
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
| `Proposition42Source` | Source-scope Proposition 4.2. Constructs source finite star cutsets and cycle path families, proves both enhanced comparisons for weak limits with boundary-only partitions and DLR laws of source conventions, and assembles separated star/cycle devices for the quasi-transitive graph class. Includes exhaustion-free quantification and free/wired-at-infinity instances; does not assume arbitrary public `IsFKLimit`s are source-labelled, and does not establish the AG strict shift. |
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
| `PlanarDLRDuality` | Generic conditional DLR transport under pointwise configuration complementation. Includes measurable equivalences, composition-product pushforwards, dual-box kernels from normalized PMF identities, and edge-relabelling invariance of free component/open-edge counts. `eq_map_of_unique_dual` is a one-box conditional singleton adapter, not the actual equation-(12) instantiation or a global convention/planar theorem. |
| `DualParameterDuality` | Actual finite equation (12): arbitrary-boundary PMF relabelling, `planeBox` PMFs, $p^*=1-p'$, matched exterior open-component conventions and genuine dual-parameter DLR transportation. The Euler component relation remains input; no global circuit, reverse duality, primal-cluster or infinite strong-uniqueness conclusion. |
| `DualLimit` | Conditional-law and cylinder weak-limit form of equation (12), dual box exhaustion, complementation of FK limits, dual-to-primal uniqueness for total FK families, and all-box/general-exterior variants. `hdualizable`, dual uniqueness, Euler data and planar/AG hypotheses remain explicit; no Theorem 1.11 conclusion by itself. |
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
| `FiniteOpenEdges` | Finite open-edge sets have finite open components, independently of graph geometry. |
| `GridOpenCuts` | Exact ℓ¹-bounded cuts on the square lattice, cofinal open-shell uniqueness, finite closed-edge consequences and separator circuit instantiation. |
| `GridDualIncidence` | Exact square-lattice face-edge crossing bijection and inverse, with dual local finiteness; no arbitrary edge pairing. |
| `CutCrossingDuality` | Genuine finite-square-lattice dual-cut crossing. Uses cell/side incidence, row and cell degree calculations, and outer vertex bijections to connect below to above in the cut graph. Transfers that walk to every supergraph, including the subsequent closed-bond graph. Primal/global uniqueness is not supplied. |
| `PrimalClosedDuality` | Completes the finite primal half: every cut of left-reachability is closed, the closed graph contains the cutwalk, and its absence gives an open left-to-right primal walk inside the box. Includes exact `gridCrossEquiv`/`dualConfig` plane-incidence witnesses and all-open/all-closed instances. The converse is assembled in `FiniteBoxDuality`; compactness/cofinality, global uniqueness and outer-row uncollapsing remain separate. |
| `BoxSeamSeparation` | Finite parity-seam separation: a $\mathbb Z/2$ potential distinguishes left and right walls across any sealed seam. Instantiates it for cut-bond seams and simple bottom-to-top closed cell chains, whose crossed closed bonds block every open primal left-to-right walk. Includes one-row and two-crossing-cluster examples; `FiniteBoxDuality` supplies the `closedGraph` bridge. No exterior-row uncollapsing or global result. |
| `FiniteBoxDuality` | Complete finite-box primal/closed-dual crossing equivalence for the original `closedGraph`. Converts a closed path to a simple `CellChain` via `Walk.toPath`, proves all its seam bonds closed, maps primal open walks to the parity box, and proves both the equivalence and its exclusive dichotomy for $n>0$. Includes all-open/all-closed instances. Does not uncollapse the exterior rows, construct a cofinal family or prove `GlobalAtMostOne`. |
| `GridBoxCrossing` | Un-collapsed finite box crossing duality on genuine global `GridV` cells and closed bonds. Constructs both collapse and lift maps, keeping honest reachability through repeated exterior visits. Prove the resulting exclusive dichotomy, not the infinite uniqueness theorem. |
| `GridDualCofinal` | Global closed-cell graph and discrete row-intermediate-value argument. Finite components of the finite row-zero family force bounded height, so arbitrary-height closed crossings give an infinite component. Produces fixed-width primal crossings cofinally from finite dual components. |
| `GridDualConfigBridge` | Identifies global closed-cell adjacency and reachability with ordinary `dualConfig gridCrossEquiv` dual-open connectivity. Supplies cofinal primal crossings under actual dual nonpercolation; no circuits or `GlobalAtMostOne`. |
| `BlockedStaircase` | Turns an injective turn-at-every-step closed staircase ray into a genuinely infinite adjacency/dual-open component via shared closed bonds and corner cells. `StaircaseBarrierExists` remains an explicit unproved geometric input; no circuits, Jordan construction or Theorem 1.11. |
| `GridDualCofinal` | Global closed-cell graph and discrete row-intermediate-value argument. Finite components of the finite row-zero family force bounded height, hence arbitrary-height closed crossings give an infinite component. Produces fixed-width primal crossings cofinally from finite dual components. |
| `GridDualConfigBridge` | Identifies global closed-cell adjacency and reachability with ordinary `dualConfig gridCrossEquiv` dual-open connectivity. Supplies cofinal primal crossings under actual dual nonpercolation; no circuits or `GlobalAtMostOne`. |
| `BlockedStaircase` | Turns an injective turn-at-every-step closed staircase ray into a genuinely infinite adjacency/dual-open component via shared closed bonds and corner cells. `StaircaseBarrierExists` remains an explicit unproved geometric input; no circuits, Jordan construction or Theorem 1.11. |
| `PlanarTarget` | Primal-closed/dual-open transport and finite nonpercolating conclusions, plus the dual-nonpercolating staircase obstruction to fixed diamond shells. |
| `WeakOpenCut` | Sharpened uniqueness criterion requiring open connectivity only for vertices incident with the open part of a finite cut. |
| `PlanarCutObstruction` | Exact all-open-cut algebra: such a cut through $x$ must contain $x$'s entire closed-edge component. The existing staircase therefore refutes the strict all-open-cut construction on the square lattice, beyond fixed norm shells, without refuting the planar uniqueness theorem. The complementary vertical-strip configuration has dual percolation and two primal infinite clusters. The open-incident criterion is merely repackaged from `WeakOpenCut`, and the closed-separating-cut form does not solve the remaining planar implication. |
| `StaircaseConnected` | The dual-nonpercolating staircase ray has connected primal open graph but a closed edge on every shell, so fixed-norm exhaustion is insufficient. |
| `SealedSeparation` | Proves that infinite closed walks cannot escape crossing-controlled labels, hence ruling out the older crossing-controlled and spherical exhaustions on the staircase even though primal uniqueness holds. Introduces vertex-sealed circuits, requiring only a barrier-meeting label or incident vertex, with genuine finite inside/barrier bookkeeping and an independent box-border construction. Delivers sealed uniqueness, positive staircase and open-box-border instances. The general dual-nonpercolation-to-sealed-family construction remains open. |
| `GridFrontier` | Actual straight-segment square-lattice realization: $\ell^1$ affine steps and exact diamond crossing, open-connected staircase cut labels, closed-cut trapping, finite preimages, and all-open separator exhaustion as an interface check. Includes disconnected box-shell and fixed-diamond sharpness restrictions. No random cofinal exhaustion. |
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
| `AGSharpness` | Explicit single-law AG input, profile/device-set monotonicity, strict decrement extraction from `UpperWindow`, impossibility of trivial event/empty-set satisfaction, and full-device Bernoulli nonvacuity instances plus correct star/cycle dispatch. Supports the AG interface but proves no essential enhancement shift or packing. |
| `AGDifferentialShift` | Explicit differential trade-bound reduction giving strict decrements/increments and `hAG` terms for clamped Bernoulli profiles. Its old closed-region differentiability premise is unsatisfiable on clamp collisions; use the interior repair below rather than treating this wrapper as readily instantiable. The real uniform pivotal estimate and supercritical baseline remain. |
| `SubcriticalBaseline` | Walk-force-open finite-energy comparison giving root-independent Bernoulli critical probability, the existence/full-mass dichotomy, and the actual zero-enhancement subcritical Bernoulli baseline. Varying-window geometry and AG derivatives/convergence remain. |
| `ReferenceBaseline` | Ordinary Bernoulli supercritical phase from the root critical supremum plus product zero–one, full event/root critical comparisons, connected root independence and supercritical enhanced mass. No critical-case or FK/AG geometric claim. |
| `ReferenceBaselinePercolating` | Exact `Percolating G` adapters for the phase and enhanced supercritical baseline, using the already proved equality with `HasInfiniteCluster`. Not a strict-shift theorem. |
| `AGMassDerivative` | Actual Bernoulli/profile polynomial bridge, interior Fréchet derivatives and finite/cylinder pivotal trade formulas for clamped decrement/increment masses. Repairs the MVT reduction on the interior and proves the closed-region premise impossible on a clamp collision. Still conditional on geometric pivot trade, baseline and approximation inputs; no strict AG shift. |
| `PivotTradeObstruction` | Exact 2-cycle pivotal masses and an explicit refutation of the whole-region uniform decrement trade premise, with a concrete compact-window instance and increment-side non-obstruction. Not a source-paper counterexample. |
| `PivotTradeObstructionCycle3` | Exact simple-triangle pivotal masses and the same uniform-constant obstruction on an ordinary simple cycle device. Enhancement remains essential locally. |
| `PivotTradeWindow` | Continuity and positivity of pivotal masses, essentiality equivalence, and positive per-event pivot-trade constants on compact open-cube windows, with decrement/increment boxes. No approximation-sequence uniformity. |
| `PivotTradeAGRepair` | Rebuilt decrement mean-value argument using the actual interior derivative and pivot trade only on the critical compact window. Still requires one constant uniform in the approximation index, plus convergence and baseline. |
| `PivotTradeAGRepairIncrement` | Supercritical increment analogue of the window repair, with the same explicit geometric, convergence and baseline inputs. No strict critical shift or Theorem 1.4. |
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
| `AGCoveringReference` | Arbitrary-index monotone comparison of genuine sleeved-product arm/percolation probabilities under edge-uniqueness and the strong requirement `CoveringBase`: every original bond is selected. Gives the exact three-rate lowering of original bonds while spoke rates stay fixed, a decrement of the critical original-bond rate, a singleton edge-unique instance, and corrected spoke-pivot/trace transport. Not positive-density hAG, uniform-spoke enhancement, FK/DLR, or Theorem 1.4. |
| `AGBoundedCoordinateBridge` | Overlap-tolerant bounded-coordinate comparison for finite independently activated families: nonnegative union sums, exact per-device pivot transport and differential curves, actual infinitePi arm/cluster comparisons by continuity from above. Common positive cardinality and finite devices remain; no full AG shift. |
| `AGTree.Reduced` | Reduced-word vertices and three-base/two-activation letter classes of the explicit tree. |
| `AGTree.Graph` | Connectivity and bounded-degree/local-finiteness structure of the five-regular reduced-word tree. Vertex transitivity and the precise degree-five proof are supplied by the later automorphism modules. |
| `AGTree.Edges` | Exact edge/class bijections and independent class-rate products; block-disjoint independence of cylinder probabilities. |
| `AGTree.Fwd` | Forward-chain clusters, coordinate projection, measurability and level antitonicity. `AGTree.Interface` subsequently supplies the genuine open-cluster/ancestor description. |
| `AGTree.Model` | Exact branching recursion for the two-class forward failure probability at every depth, from actual block-disjoint subtree independence. |
| `AGTree.Criterion` | Valid-letter class cardinalities, monotone failure curves and cluster probability as decreasing level-limit. |
| `AGTree.Shift` | A general positive-cluster criterion from valid-child bounds and decreasing level convergence. |
| `AGTree.Interface` | Open subgraph/connection and genuine open-cluster definitions, common-ancestor paths, minimal-depth ancestor with infinite forward cluster, and root forward/infinite equivalence. |
| `AGTree.BaseNonpercolation` | Union bounds and forward recursion estimates giving base-cluster zero and a.s. finite clusters under average base degree below one, now importing the genuine connection interface. |
| `AGTree.ShiftThreshold` | Base nonpercolation at rates $(3/10,0)$ and positive activated open percolation at $(3/10,1/2)$, yielding a strict probability increase in same-event open percolation. The complete two-rate criterion is supplied by `AGTree.TwoRateCritical`. |
| `AGTree.SharpThreshold` | Exact base threshold at $r_0=1/2$ when activation is closed: uniform first-moment bound below the threshold and a seeded-contraction lower bound above it. Nothing claimed at the critical rate itself. |
| `AGTree.TwoRateCritical` | Exact two-class open-cluster critical curve on this tree: no percolation for $2b+s+4bs\lt1$, positive percolation above $1$, and no percolation on equality when $b\gt0$. Proves $\operatorname{critBase}(s)=(1-s)/(2+4s)$, its strict decrease for positive activation, and an enhanced-versus-base strict shift. The degenerate critical corner $(b,s)=(0,1)$ is excluded and not decided by the theorem. This is not a general AG `hAG`, FK critical-window, DLR or uniqueness result. |
| `AGTree.Aut` | Letter-prefix-with-cancellation and involutive graph isomorphisms over reduced words, preserving adjacency and root edge forms. |
| `AGTree.Transitive` | Arbitrary-word isomorphisms giving vertex transitivity, a single automorphism vertex orbit and actual quasi-transitive geometry. |
| `AGTree.Degree` | Root-to-arbitrary degree bound transfer, proving degree exactly five at every vertex. |
| `AGTree.EdgeClass` | Preservation of every edge letter/class/rate under word automorphisms and maps of child pointers. |
| `AGTree.Spine` | Explicit alternating doubly infinite ray carrying the base root edge, without any quasi-transitive classification assumption. |
| `AGTree.Devices` | Actual separated bounded-distance star supports of size at most five, sourced by double-ray support and degree five. |
| `AGTree.Invariant` | Automorphism-invariant normalized two-rate product and transport of open reachability: infinite-cluster probability is root-independent and uniformly zero/positive at the stated base/activated rates, not a new threshold theorem. |
| `AGTree.ThresholdExamples` | Concrete base rates $3/10$ below and $3/5$ above the critical value, proof of percolation at $3/5$, and threshold-crossing activation records. General AG `hAG` and FK conclusions are not asserted. |
| `AGTree.Main` | A concrete positive forward-cluster point for the $(3/10,1/2)$ two-rate activated law, later upgraded to genuine open-cluster percolation in `AGTree.Interface` and given its exact criterion in `AGTree.TwoRateCritical`. |
| `AGFiniteReferenceCurve` | Actual finite-family monotone arm and percolation probabilities on the whole admissible independent comparison line, zero/nonzero phase propagation, and the explicit maximal time $T_{\max}=\min((p-a)/c,b-s)$ with both endpoint boxes. No infinite-index or strict critical conclusion. |
| `AGStrictShiftExample` | Concrete inhomogeneous path/star product with base critical $1$ and enhanced critical $0$ for $s>0$, using finite cylinders and second Borel–Cantelli. Not a generally applicable AG reference theorem. |
| `TreeEdgeTransitive` | Explicit alphabet and prefix automorphisms give edge transitivity, and hence every edge of the five-regular reduced-word tree lies on a double ray. |
| `CactusGraph` | Original triangular expansion with two independent spoke bonds per edge; explicit bond equivalence, connectivity and quasi-transitivity, not attachment of a new abstract graph class. |
| `CactusMeasure` | Exact original independent-bond products and junction effective law with rate $r_0+r_1r_2-r_0r_1r_2$, including a genuine reindexing of named and actual bond spaces. |
| `CactusPaths` | Exact equivalence `ActualPerc ω ↔ Perc (effective ω)`, with direct-bond lifts, midpoint-spoke induction and a finite-fibre infinite-cluster proof. |
| `CactusShift` | Exact original-bond homogeneous criticality at effective rate $1/4$ and an explicit strict right window under a direct-bond penalty, for the Husimi triangle cactus only. Not the general AG theorem. |
| `CactusGeometry` | Actual direct-bond triangles and double rays, source-separated devices, and line-graph distance at most one from every original bond; packages the cactus graph, criticality, geometry and strict-window results. |
| `GraphConnectionTransport` | Exact arbitrary finite-boundary/global-wired reachability after closing the exterior, bottom-wiring identification, and canonical free-component transport. Finite combinatorial identities, not a weak-limit or geometric-convention theorem. |
| `NestedStageConnection` | Identifies the nested induced-specification one-edge event with outer-box reachability after closing the selected edge; retains genuine `NestedBox` transports and arbitrary outer partitions. |
| `FreeNestedGeometry` | Completion of source-union Proposition 1.8(2): configurationwise nested free Markov identity, arbitrary exterior-schedule DLR closure, and all-finite-box coherent-convention membership. Unrelated noncoherent setoid schedules remain excluded. |
| `StageEscapeGeometry` | Open/wired-walk transport and first-exit escape from finite vertex sets with only nonreflexive boundary pairs required to avoid the set. |
| `StageEventGeometry` | Clopen outer-stage and finite lower events, their cofinal exhaustion, and exact free-specification/global off-edge connection equivalences. |
| `StageContainment` | Eventual inner-to-outer event inclusion and the difference-to-escaping-cluster inclusion under nonreflexive far-wiring. |
| `DominatedOuterAssembly` | Fixed-box free DLR closure for dominated weak limits on genuine growing families, with explicit embedding compatibility, far-boundary, majorant and rootwise nonpercolation inputs. |
| `MetricGrowingFamily` | Canonical graph-metric boxes as a genuine nested growing family, with explicit vertex nesting and compatibility with the global metric-box embeddings. |
| `MetricStageGeometry` | Finite lower balls/supports, eventual far-wiring from edge-complement support, and free/geometric DLR closure for dominated weak limits on the metric exhaustion. Not an all-box Gibbs result. |
| `MetricGeometryExtensions` | Metric nesting coherence, finite-stage free-boundary support and far corollaries, and the fully wired exterior-support obstruction. |
| `PrimeStageDomination` | All-measurable-upper-event finite-volume domination from interior comparisons, arbitrary-boundary prime-Bernoulli majorants for $q\lt1$, and the original metric DLR wrappers with explicit global uniqueness. |
| `DominatedLimitNonpercolation` | Nonpercolation and almost-sure global at-most-one-cluster uniqueness inherited by dominated weak limits; removes the redundant global-uniqueness hypothesis from restricted metric closure. |
| `PrimeMetricAutoGlobal` | Prime-dominated and strictly subcritical metric DLR closure with automatic global uniqueness, plus the finite-stage-free corollary that also discharges edge-complement support. Restricted to the canonical metric exhaustion. |
| `AGConstructedPathShift` | Homogeneous one-way path with independent ordinary bonds and one extra independent synchronized activation, giving exact percolation curve and a genuine strict shift to critical zero for every positive activation. The activation opens all edges: unbounded range, not bounded-range AG. |
| `BoundedRangeGraphShift` | Connected locally finite chained bundle graph with a two-edge route per bond/activation pair, exact independent OR products, and root percolation iff all bundles cross. Proves $p_c=1/2$ and enhanced $p_c=1/3$ at activation $1/4$, a one-edge-range strict shift. Deterministically open stems make the full graph law inhomogeneous; not the general AG theorem. |
| `FKQuasiTransitiveDevices` | True finite automorphism-orbit hypothesis, bounded degree, distance/ray transport and separated star/cycle device packing with uniform cardinal bounds. Finite-box certificate admissibility remains separate. |
| `StarBoundaryCutset` | Corrected finite local star cutsets, singleton-center boundary condition and a fully wired counterexample. Geometric/free/wired proofs use full-star containment and explicit vertex-map injectivity. |
| `CycleBoundaryPaths` | Complementary cycle walks lifted into compatible finite boxes, genuine auxiliary path families and the active-cycle upper DLR application under vertex-map injectivity. |
| `CycleBoundaryLowerPaths` | Lower open-path DLR comparison for $q>1$ and its two-sided geometric sandwich with actual complementary walks, star cutsets and exact parameter enhancement. |
| `GeometricActiveComparisons` | Canonical complete-device containment/admissibility and eventual activation, both geometric star/cycle DLR sandwiches and quasi-transitive packings with bounded-distance supply. The DLR law and all graph compatibility hypotheses remain explicit; no strict shift. |
| `AGPivotTransport` | Bounded-local fibres, independent-product probability ratio and activation-peel branch transport. An activation-free branch remains only an intermediate conclusion, not the global AG strict shift. |
| `MainIntegration` | Also the public adapter between the generic weak-limit and theorem-specific phase APIs. |

| `RandomExhaustion` | Joint measurability of exterior conditional probabilities on countable random regions, fibre constancy under an arbitrary marginal coupling, and separate ordered/product integral and reverse-martingale results. Not the ordered-coupling limit or Theorem 5.1. |
| `ClosedFrontierExhaustion` | Measurable cluster-union vertex regions, closed frontier, cofinality and finite-cluster finiteness on a countable simple graph. No measurable `Finset` packaging or adaptive-cutset construction. |
| `RegionSeal` | Free-boundary Markov property on arbitrary finite labelled multigraphs: no-cross component split, weight factorization, and exact normalized interior fibres on sealed exteriors. Interior rates; no DLR/random-region assembly. |
| `NestedSplitComparison` | Bernoulli splitting, added-label extension and a true ordered triple for the fixed shell-first estimate. Its error is failure of shell separation, a generally nonvanishing boundary event, not the paper's arm error. |
| `AGShift` | Exact activation/deactivation ↔ constant-increment/decrement window reductions, inhomogeneous product cylinder independence and percolation zero–one, plus a root-shift implication. Both shifts and comparisons remain explicit hypotheses. |

| `OrderedKernelNonpercolation` | Decreasing/nonpercolation transfer along actual ordered Strassen conditional kernels, in both fibre and integrated forms. Fibres need not retain DLR or share the same specification. |
| `SourceRegions` | General nested source conventions at every finite vertex region, free boundary under merge/finite-component separation, and measurable random finite-`Finset` vertex and edge packaging with exact box identity. Fixed-region DLR only. |
| `GenericKernelReverseLimit` | `L²`, bounded-measurable and indicator forms of downward convergence for the actual conditional fibre law, including a dominated pair. Does not identify a common limit with the original marginal tail. |
| `FibreCylinder` | Integral/martingale tower conclusion for ordered fibre conditional limits, cylinder value identities and a region-explicit criterion. Its region/limit hypotheses remain visible. |
| `FibreClass` | Subsingleton and singleton-when-nonempty packaging of the ordered-fibre cylinder criterion. Does not construct a DLR element or identify its common limit. |

| `NestedTransportGeneral` | Vertex/edge reindexing of arbitrary-boundary finite FK connection graphs, component counts, weight factors and normalized pointwise/transformed laws. |
| `NestedFiniteDLR` | Exact nested FK exterior mixture/induced partition and `IsDLR` at the small box for every arbitrary boundary partition. Closed-exterior version included. |
| `GrowingFamilyDLR` | Induced schedules and eventual finite-stage DLR equations on genuine growing families; joint local stabilization and at-most-one-cluster input to the conditional weak-limit wrapper remain explicit. |
| `DLROnePoint` | Finite-box DLR comp-product integrals and exact off-edge two-valued rates for every exterior assignment, including the induced specification connection event. |
| `MovingDominatedRate` | Moving two-valued rates and box-DLR conclusion from actual domination plus a vanishing escape tail; retains stage/limit rate identifications and geometric tail input. |
| `LatticeBoxes` | Explicit ordinary nearest-neighbour paths supported in a punctured finite integer $\ell^\infty$ box in dimension at least two; induced punctured-box preconnectedness. No four-terminal fan or AG/FK critical-shift proof. |
| `MovingClopenRate` | Two-valued rates on moving clopen connection events and their edge-conditional/global limiting identities from genuine escape-tail vanishing. |
| `AGSourceHypotheses` | Derives $0\lt p_c$ from connected locally finite quasi-transitive geometry using the proved bounded-degree first-moment estimate, and constructs `PaperGraphHypotheses` from the source's stated inputs. No strict enhancement shift. |
| `FiniteExteriorDetermination` | Explicit finite edge windows that determine free exterior components and every geometric exterior convention at an at-most-one-infinite-cluster configuration. |
| `PlanarGlobalAssembly` | Measurability of no-infinite-cluster events, primal/dual stochastic-domination transfer, and almost-sure exactly-one-cluster conclusions under explicit planar geometry and phase inputs. |
| `PlanarAEKernelDuality` | Almost-everywhere dual FK-kernel/PMF transport using `Measure.compProd_congr`, including dual-parameter and arbitrary box-family versions. |
| `PlanarAllBoxDuality` | Full-support replacement of geometric source conventions by free exterior components, all-box dual DLR identification, and an enhanced primal/dual wrapper retaining actual circuit, duality and phase hypotheses. |
| `GeneralMovingClopenRate` | Orientation-free eventual moving-clopen rate limit and one-point DLR criterion using monotone lower events and vanishing clopen escape tails, without ordering the two rates. |
| `GlobalOuterGeometry` | Clopen finite arms, rooted finite-edge covers and off-edge uniqueness before DLR membership, plus free-convention identification and off-edge escaping-pair escape bounds. |
| `GlobalOuterAssembly` | Nested all-parameter source-form Proposition 1.8(2) through outer-stage clopen escape and coherent all-box targets; requires genuine nested geometry and edge-complement-supported stage boundaries. |
| `CouplingSealCounterexample` | Explicit ordered Bool×Bool coupling whose lower law on the attained upper-open stratum is not its original free marginal. Blocks an adaptive joint-free-seal shortcut, not Theorem 5.1 itself. |
| `GenericNestedGood` | Glues first/upper and smaller/upper ordered pairs through a literally common coordinate, giving nested good-intersection equality and the corresponding equation-(9) bound from a pair identity. |
| `CanonicalEquality` | Identifies the canonical finite FK nested ordered triple with the explicitly glued first/upper and smaller/upper nested triple. |
| `OrdinaryNestedTriple` | Ordinary region-confined finite nested common-upper identity and equation-(9) bound under explicit confinement, region restriction, added-label avoidance and exterior-shell incidence. Not metric nesting or Theorem 1.9. |
| `CombinatorialEnclosure` | Finite cellular enclosing primal circuits with complete cuts, connected inside/outside, primal-open carriers and sealed path incidence; rotation/global-labelled adapters. Continuous global windows, cofinality and full Theorem 1.11 remain open. |
| `CellularSealedCuts` | Closed-exit-edge tolerant sealed regions; exact ambient/local dual-window transport and closed-frontier restriction; metric dual exhaustion from actual dual nonpercolation; cofinal-window `GlobalAtMostOne`. Arbitrary continuous embeddings still must supply exact spherical rotation windows, strict-interior incidence and pairwise cofinality. Not full Theorem 1.11. |
| `DualEnhancementDensity` | Bounded-distance enhanced sets transported from primal to dual through exact local corner links and an edge equivalence, using primal quasi-transitivity only for a degree bound; the local/global Lipschitz property is characterized equivalently. Simple dual graphs and supplied corner data only; no dual essentialness, AG or Theorem 1.11. |
| `DualEnhancedProfiles` | Exact complementary enhanced-profile identities at $p^*=1-p’$, with star/cycle and exponent exchange, in both q regimes and under arbitrary edge equivalences. Profile algebra, not dual device geometry. |
| `SourceLowerWindow` | Lower source product identified with Prop 4.2, lower domination of every arbitrary-exhaustion/geometric source FK law, and exact complement to dual upper product. No extra final DLR hypothesis. |
| `PlanarSourceAssembly` | Almost-sure exactly-one-infinite-cluster windows for the whole primal source family from primal activation, dual deactivation and named planar separation. Separate primal/dual radii and geometry remain. |
| `DualSourceSingleton` | Standard dual source singleton/nonpercolation windows from supplied matched dual devices, dual AG and literal Eq9. Does not construct devices, hfreeDual, final dual-box/source membership or full Theorem 1.11. |
| `ContinuousPlane` | Faithful finite Jordan-arc embeddings in the plane, compact carriers and actual complementary faces/path components. No arbitrary-embedding rotation theorem. |
| `PolygonalSegment` | Explicit three-leg detours avoiding a nondegenerate straight segment, proving path-connectedness of its complement and uniqueness of its face. |
| `OneSegmentWindow` | Genuine continuous two-vertex/one-edge spherical rotation window with exact carrier, real/combinatorial face equivalence and primal interior edge coverage. One edge only; no cofinality, DualRegionWindow or simple loop-dual theorem. |
| `TriangleCircuit` | Affine-basis triangle frontier/separation, bounded convex inside and unbounded exterior path connectedness via radial/sphere paths. No general polygonal Jordan theorem. |
| `TriangleEmbedding` | Faithful straight noncrossing triangle embedding, exact three-side carrier, and two actual complementary clopen connected path faces identified with Bool. |
| `TriangleRotation` | Explicit six-dart triangle RotationSphere, two orientation face classes and exact combinatorial/continuous face equivalence. Not arbitrary general rotation extraction, interior coverage or stochastic dual assembly. |
| `ForestAttachment` | General local-link theorem for preconnected open sets with a closed attached obstacle. |
| `ScaledDetour` | Parameterized three-leg detours with scaled normal displacement and endpoints arbitrarily near the free segment endpoint. |
| `ForestGeometry` | Convex safe tubes and free-end extension bounds for one-endpoint straight attachments. |
| `SegmentAttachment` | One-endpoint segment attachment preserves path-connectedness of the complement. |
| `ForestHistory` | Attachment-history carriers are compact and have exactly one actual plane face. |
| `ForestCombinatorics` | Bridge-defined labelled forests are acyclic, exclude loops/parallel cycles, and have labelled leaves. |
| `StraightForest` | Straight edge-range embeddings; faithful leaf deletion and path-connected complements for every labelled forest, including disconnected/isolated cases. |
| `ForestRotation` | Finite enumeration incidence rotations and the coboundary-rank argument: connected labelled forests have one face and a spherical rotation when a dart exists. |
| `ForestWindow` | Equivalence of the constructed spherical forest face with the actual continuous one-face quotient; no angular traversal/incidence theorem. |
| `SourceEscape` | Arbitrary induced vertex exhaustions, genuine crossing nested boxes, source growth-family/exhaustion constructions, and vanishing complement-escape bounds. |
| `SourceBoundary` | Literal source outer-boundary events with closed-neighbourhood vanishing under nonpercolation, and equality of arbitrary source FK weak limits from the nested boundary estimate. |
| `SourceFamily` | Identifies source exterior-walk geometry with global box geometry, realizes source outer-boundary classes, and proves all-region source DLR compatibility on any exhaustion. |
| `SourceUniqueness` | Classical arbitrary-exhaustion strong-uniqueness assembly from the literal nested equation-(9) bound and a nonpercolating dominant, via source-limit existence and Choquet. The ordinary NestedEquationNine is proved by the newer global-nesting package; critical enhanced/window inputs remain separate. |
| `SourceWindow` | Source weak-limit tail transport, exact Prop 4.2 upper-product identification and arbitrary-exhaustion domination; zero-rate source uniqueness and uniform positive Theorem 1.10 windows. Discharges the separate dominant; the actual AG deactivation shift and nested equation (9) remain hypotheses. Not unconditional Theorem 1.10. |
| `DeterministicDominator` | All-region geometric source-DLR uniqueness under a Dirac nonpercolating dominant, via an adaptive closed-frontier exhaustion and free-at-closed-boundary convention equivalence. Supports infinitely many open primal edges, but not a general random dominant or weak limits; singleton forms require class membership. Not general Theorem 5.1. |
| `NormalizedFilter` | Exact finite conditional mass ratio after filtering a normalized nonnegative-weight PMF, cancelling global and conditional normalizations. |
| `ArmCorrectionObstruction` | Exact five-vertex FK computation at $q=2$, $p=4/5$: filtering on no root-to-boundary arm gives $17/59$ free versus $21/71$ with one wired boundary pair. Refutes the naive correction identity, not RegionSeal or Theorem 5.1. |
| `ComparableNonpercolating` | Equality of stochastically comparable nonpercolating canonical or geometric all-region DLR laws, via finite-base frontier-stratum total masses and normalized closed-frontier strata. Singleton when the nonpercolating dominant is itself DLR. Not an arbitrary common-dominant Theorem 5.1. |
| `ArbitraryFrontierTotal` | A non-DLR upper law with unit finite-base stratum totals has exactly the same frontier masses as each dominated canonical/all-region source DLR law, yielding cylinder equality. Unit totals unresolved for an arbitrary dominant; not general Theorem 5.1. |
| `DominatedSourceCompactness` | Nonpercolation-preserving closure of source DLR laws under domination, arbitrary probability-kernel mixtures and subsequential compactness; coherent conditional-stage DLR replacement and a common law under a two-sided stage sandwich. Arbitrary global domination does not supply its stage bounds. Not general Theorem 5.1. |
| `AGLocalPivotMSS` | Uniform finite local-pivot trade and exact bounded-fibre likelihood/candidate-overlap estimates from genuine local modification maps; no injectivity required and hmap survives explicitly. |
| `AGCylinderLocalPivot` | Arbitrary countable-coordinate cylinder derivative and decrement/increment mean-value arguments with finite-support pivot estimates, giving actual zero/one analytic window conclusions without constructing the maps. |
| `AdaptiveDisintegration` | Partial-history assignments, adaptive next-edge strategies, and exact arbitrary-edge tower/marginal/order facts independent of edge order. |
| `AdaptiveFK` | FK and Bernoulli one-bit conditional bounds on arbitrary exactly revealed partial assignments. |
| `AdaptiveStopping` | Adaptive ordered coupling and exact stop/resume disintegration of the remaining law. |
| `RegionFiberTransport` | Transport from conditional stopped exteriors to the actual bounded-interior configuration. |
| `AdaptiveRegion` | Region decomposition and free-region Markov factorization along adaptive closed regions. |
| `AdaptiveFrontier` | Closed-frontier nesting, equal revealed sets, order, absence of revealed interior edges, and stopped seal structure. |
| `AdaptiveTriple` | Synchronized adaptive FK/FK/Bernoulli triple with shared upper history and exact coordinate processes. |
| `AdaptiveTripleStopping` | Stopped/resumed synchronized triple and restricted-interior identities on stopped strata. |
| `AdaptiveGood` | Exact good-intersection equality for arbitrary unrevealed interior observables, proved separately on each stopped stratum and not averaged over an upper/open stratum. |
| `IndependentProductConditional` | Singleton conditionals of FK-tensor-Bernoulli products, with the FK upper bound retained on all mixed revealed histories. |
| `IndependentProductFilter` | Partial-history conditioning factors across independent joined products and recovers exact off-edge conditional marginals. |
| `NestedProductRegion` | The stopped independently extended small law has exactly the small free-region conditional law, under displayed history, wiring and seal hypotheses. |
| `NestedAdaptiveCore` | Transported big FK / independently extended small FK / common Bernoulli ordered triple, with no vertex-disjoint requirement. |
| `NestedAdaptiveMarginals` | Original big first/third marginals, exact small second restriction, and the original Bernoulli third law for the nested adaptive triple. Not outside-coordinate copying. |
| `StoppedSeal` | Deterministic seal of every stopped exterior under the adaptive closed-frontier decomposition. |
| `NestedAdaptiveGood` | Ordinary induced sum-edge nested geometry with exact small free FK marginal/component counts, maximal-frontier preservation, outside-coordinate copying and finite cylinder/arm estimate. No global Bernoulli-arm claim. |
| `NestedMetricWindow` | Canonical nested finite-box geometry and centered metric specialization of the finite arm bound, including actual source boundary singleton hypotheses. |
| `SourceNestedWindow` | Arbitrary induced source-box nesting and the canonical `VertexExhaustion.nest` finite arm bound. Needs separate global reindexing and identification with `boundaryConnection`. |
| `SourceGlobalWindow` | Exact observation-base induction, finite/global FK and Bernoulli reindexing, and canonical boundary-connection arm realization. Does not prove enhanced-profile or arbitrary-abstract nesting itself. |
| `ArbitrarySourceNestedWindow` | Arbitrary abstract NestedBox core, internal-endpoint and isolated-endpoint treatment, exact global boundaryConnection and finiteVolumeLaw arm bounds. No metric/canonical-exhaustion restriction. |
| `SourceNestedBounds` | Empty observation-base estimate and canonical eventual nested boundary bounds; strong uniqueness from ordinary nested coupling plus nonpercolation. |
| `SourceNestedEquationNine` | Literal SourceUniqueness.NestedEquationNine for every abstract NestedBox and interior p, all q>0. Exact global finite-volume and boundaryConnection bounds; no AG/critical enhancement claim. |
| `IsolatedBoundaryTransport` | Exact normalized FK PMF transport when deleting a vertex-only extension, including arbitrary wiring between retained and deleted vertices. Components wholly outside the retained range contribute only a cancelling factor. |
| `ArbitraryNestedEquationNine` | Independent intersection-box proof of literal NestedEquationNine for every abstract nesting and every $0\le p\le1$, with actual observation roots. Uses isolated-vertex deletion and direct endpoint calculations; not an enhanced-profile or AG theorem. |
| `ClassicalSubcriticalGt` | Full source-family singleton and nonpercolation for $q>1$ and $0<p<p_c(G,o)$. Empty Proposition 4.2(2) devices give the ordinary Bernoulli$(p)$ dominant, joined to arbitrary nested equation (9); root, connectedness and a seed edge remain explicit. |
| `TreeJunction` | Finite-tree three-way junctions with exact pairwise-support intersections at one centre. |
| `LeafJunction` | Three-leaf central graph and its central tree-junction construction, retaining incidence and separation data. |
| `BurtonKeaneGeometry` | Actual open simple three-arm geometry and support-disjoint pruning/splicing. |
| `LeafWalk` | Central-arm leaf stripping, support transport and separation maps used by the encounter construction. |
| `BurtonKeaneWeak` | Pruned splicing interface for three-way arm witnesses, with explicit local hypotheses. |
| `LeafArms` | Three-way arms at one fixed centre from central leaf attachments and separated external arms; corrected attachment-incidence interface. |
| `ExternalClusters` | Incidence-avoidance clusters and arbitrarily distant open arms. |
| `IncidenceGeometry` | Last-incidence suffix and avoidance geometry for distinct infinite clusters. |
| `IncidenceAttachment` | Explicit incidence attachments to finite windows, preserving outside connectivity information. |
| `ExternalRoot` | Finite incidence covering and original-root-preserving external attachment points for infinite components. |
| `InternalGeometry` | Actual internal edges/opening, preservation of incidence-avoiding open walks, insertion idempotence and exact finite coordinate patches. |
| `AssemblyBranch` | Exterior assembly branches and avoidance under modifications within a finite region. |
| `ConnectedSupport` | Finite connected vertex support joining three prescribed roots, without requiring prior cluster connection. |
| `TripleAssembly` | Three actual infinite separated clusters produce a finite internal patch with three open disjoint arms at one centre at every scale. |
| `PatchLifting` | Finite-pattern insertion tolerance, countable patch selection and Bernoulli finite-cylinder lifting; tolerance is an explicit measure hypothesis. |
| `EncounterProbability` | Countable-graph encounter measurability and positive encounter probability under insertion tolerance/three actual infinite clusters, with an interior-Bernoulli specialization. Not global at-most-one uniqueness. |
| `DLRInsertionToleranceCore` | Genuine DLR finite energy for arbitrary finite Boolean patches: exact finite-box glue/update identity and positive patched-event mass from strict finite FK positivity at interior parameters. Covers exhaustion DLR/Gibbs classes. |
| `DLRInsertionToleranceRegions` | Every finite edge set lies in a finite induced region, yielding insertion tolerance for canonical/all-region source-DLR laws, plus positive-encounter corollaries given positive three-infinite-cluster mass. No global uniqueness theorem. |
| `EncounterTreeConstruction` | From positive-scale three-way arms, construct a genuine finite tree using only first-exit traversed edges: open retained edges, centre degree≥3, all leaves on the radius sphere, support in the closed ball, and actual branch bounds by fixed finite sphere cardinality. Fixed centre/scale; no global Burton–Keane or multi-centre claim. |
| `FolnerFirstMoment` | Probability first-moment bound, Følner zero-density obstruction and explicit shift/homogeneous-event interface. |
| `TreeBranchBound` | Finite-tree degree-sum bound on branchpoints by leaves/boundary, by an integer rank/counting proof. |
| `EncounterTreeBound` | Adapter turning a supplied encounter tree with boundary leaves and high-degree marked vertices into a marked-count bound; tree geometry remains an input. |

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
