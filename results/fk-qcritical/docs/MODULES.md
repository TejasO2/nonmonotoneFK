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
| `ExteriorIdentification` | Exact exterior FK conditional expectations from DLR, for arbitrary supported events; extremal-DLR exterior-to-unconditional $L^1$ convergence with eventual support proved from the exhaustion. |
| `ExplorationGeometry` | Canonical outer open region, maximal separated interior, closed frontier and disjoint configuration strata. |
| `ExteriorMarkov` | Exact actual FK `PMF.filter` disintegration onto exterior fibers; exterior wiring and free interior boundary where nonincidence holds. |
| `FreeInterior` | Disjoint-sum component counting and equality of a separated interior law with the actual free FK law. |
| `CanonicalFreeInterior` | Joins canonical outer-region strata with exact free-interior conditioning. Does not yet construct the full ordered sequential exploration coupling. |
| `FiniteGraphTransport` | Simultaneous vertex/edge transport preserves the actual free FK PMF. |
| `MarkovFactorization` | Actual binary and finite-family independent FK products on disjoint sums, exact all-closed-exterior PMF filtering and conditional independent free-interior factors. |
| `ExplorationAudit` | Supplemental principal audits for exploration/free-interior results; referenced by `Audit.lean`, not part of the normal proof API. |

## Infinite volume, conventions and endpoints

| Module | Role |
|---|---|
| `InfiniteVolume` | Finite-box measurability, FK kernels, DLR equations, weak-limit/coherent classes, integrated bounds and convention-uniqueness under at most one infinite exterior cluster. |
| `BernoulliFiniteBox` | Exact infinite Bernoulli product factorization into exterior and interior products; uniform local comparisons lifted to a full DLR law after matching exterior marginals. |
| `ConventionTransport` | Exterior-component geometry and geometrically certified free/wired conventions; DLR/Gibbs transport under global at-most-one-cluster using compProd sections and actual FK singleton positivity. |
| `ConventionEndpoints` | Deterministic endpoint DLR equations/classes, all-rate convention transport, and endpoint weak-limit transport. |
| `InteriorWeakLimit` | Weak closure of actual DLR classes under continuous FK specifications; continuity for locally constant boundary partitions, canonical locally constant coherent weak limits, and geometric transport. The unrestricted nonlocal interior case remains open. |
| `InteriorEndpointNormalization` | The same locally constant coherent weak-limit DLR transport extended from $0<p<1$ to every $p\\le1$ using the already proved endpoint transport. |
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
| `UnicyclicForest` | Exact two-face graphic duality for connected unicyclic labelled multigraphs and arbitrary finite pendant-forest attachments, via graph certificates and explicit bridges. Not general plane embedding. |
| `CellularExactnessRepair` | Binary representability, exact face-boundary/transpose input, rank-nullity and exact cycle-matroid duality, with Euler and normalized FK corollaries. |
| `RotationSystemDuality` | Dart rotations, exact quotient faces and face-dual incidence, $\mathbb F_2$ two-cell identity, dual connectivity, and `GraphicDualCertificate` for spherical rotation systems. |
| `WedgeDuality` | Direct-sum matroid duality, primal/exterior-face one-point unions, pointed folds and exact cycle-chain certificates with face-count formulas. |
| `CircleSeparation` | Metric-circle complement/path-component lemmas for concrete plane loops. |
| `SegmentSeparation` | Unique crossing of a straight segment from an open ball to an exterior point, with inside-prefix/exterior-suffix behavior, in arbitrary real normed spaces. |
| `CircularSegmentCertificate` | Concrete embedded circular-loop pair, exact face path components, non-radial dual arc and unique crossing, plus its one-loop graphic certificate. |
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
| `FKQuasiTransitiveDevices` | True finite automorphism-orbit hypothesis, bounded degree, distance/ray transport and separated star/cycle device packing with uniform cardinal bounds. Finite-box certificate admissibility remains separate. |
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
