# FK model for $q \lt 1$: Lean formalization

A Lean 4 development based on Beffara–Faipeur–Oke, *A New Bound for the
Critical Point of the FK Model for q < 1*, arXiv:2512.16486v1.

**This is not yet a completed formalization of every main theorem in the paper.**
The actual finite FK model, both enhanced comparison propositions, and the finite
Theorem 1.2 are proved for interior edge weights and $0\lt q$, $q\ne1$. There are
also substantial dynamics, exploration, infinite-volume, reverse-conditioning,
and duality results. The whole-paper statements of Theorems 1.4, 1.10, and 1.11
remain open. Read [the proof-status guide](docs/PROOF-STATUS.md) before using a
theorem whose name resembles a result in the paper.

## Start here

- [Reading and repository guide](docs/START-HERE.md): prerequisites, build
  commands, notation, and how to find declarations.
- [Proof status and remaining obligations](docs/PROOF-STATUS.md): what is
  proved, what is conditional, and what is missing.
- [Module guide](docs/MODULES.md): the role of every project-owned module.
- [Theorem 1.2 fidelity review](docs/THEOREM12-FIDELITY.md): the source
  correspondence and normalized enhancement profiles.
- [Errata and representation choices](docs/ERRATA-AND-DEVIATIONS.md): the
  stochastic-order convention, parameter repairs, and continuous/discrete time.
- [Arbitrary nested global equation (9)](docs/NESTED-GLOBAL-EQUATION-NINE.md): arbitrary abstract nested boxes, exact observation roots and boundary-connection transport, and the source-family uniqueness corollary at interior $p$. An additional isolated-vertex deletion/intersection proof covers every $0\le p\le1$. No enhancement strict shift, continuous planar windows, or Theorem 1.10 final assembly.
- [Classical subcritical source uniqueness for every $q>0$](docs/CLASSICAL-SUBCRITICAL.md): proved at $p=0$, for strict $\max(p,p')<p_c(G,o)$ and all $0\le p<1$, and under the zero-$\theta$ critical exception. The source family is a singleton with a.s. nonpercolation. The all-open unit-rate singleton is also exact, with nonpercolation only under its actual hypothesis. No AG or enhanced window is used.
- [Ordinary nested cutsets and the finite arm bound](docs/ORDINARY-NESTED-ARMS.md): exact induced small free laws, genuine maximal-frontier stability, outside copying, and ordinary nested cylinder estimates at interior parameters. Global Bernoulli reindexing and arm-to-`boundaryConnection` transport remain open, so this is not yet Theorem 1.9 or 1.10.
- [Local-pivot MSS transport and cylinder analytic windows](docs/AG-LOCAL-PIVOT-MSS.md): bounded-local likelihood/candidate-overlap transport, uniform positive trade constants, and actual zero/one decrement/increment cylinder conclusions. Essentialness does not yet construct the maps; general AG rerouting remains open.
- [Cellular sealed cuts and dual-window assembly](docs/CELLULAR-SEALED-CUTS.md): closed-exit-edge tolerant global enclosures, exact dual-window transport, metric dual nonpercolation, and a cofinal-window at-most-one-cluster theorem. Exact continuous-embedding windows and cofinality are still required; not Theorem 1.11.
- [Straight finite labelled forests](docs/STRAIGHT-FOREST.md): path-connected complements for arbitrary straight labelled forests, including disconnected/isolated vertices, via explicit leaf-attachment induction; spherical connected forest rotations and actual face equivalence with a dart. The incidence enumeration is not an angular ordering; no arbitrary continuous global windows.
- [Affine-basis triangle circuit and rotation](docs/TRIANGLE-CIRCUIT.md): exact two-sided plane separation with bounded inside/unbounded outside, faithful arc embedding, six-dart rotation and face equivalence. A complete triangle instance, not general polygonal Jordan separation or arbitrary windows.
- [Continuous plane arcs and the one-segment window](docs/CONTINUOUS-PLANE.md): source-faithful finite arc embeddings, an explicit segment-complement path theorem, and an exact one-edge spherical rotation window with primal coverage. Arbitrary finite graph rotations and cofinal dual boxes remain unproved.
- [Continuous segment and triangle reparametrizations](docs/CONTINUOUS-REPARAMETRIZATION.md): arbitrary Jordan parametrizations of fixed straight segment/triangle ranges, exact actual-face equivalences and one-edge coverage. Not angular extraction, arbitrary curved ranges or cofinal dual windows.
- [Enhanced profiles and dual source-window assembly](docs/PLANAR-SOURCE-WINDOW.md): exact primal-lower/dual-upper profile exchange, all-source lower domination, conditional exactly-one-cluster and dual singleton windows. Dual device geometry, essential enhancement, Eq9, hfreeDual and final DLR compatibility remain inputs; not full Theorem 1.11.
- [Dual-enhancement density](docs/DUAL-ENHANCEMENT-DENSITY.md): density transport through local rotation/corner links without dual quasi-transitivity. The dual rotation data, finite comparison devices and essentialness remain unconstructed; scoped to simple dual graphs.
- [Finite peeling and probability-transport components](docs/AG-PIVOT-TRANSPORT.md): finite AG ingredients, not a strict critical-point shift.
- [Finite source regions](docs/SOURCE-REGIONS.md): source merge/separation, closed-frontier free boundary, measurable finite edge boxes and ordered-kernel nonpercolation transfer. General conventions, fixed-region DLR—not full Theorem 5.1.
- [Ordered-fibre cylinder integration](docs/ORDERED-FIBRE-CYLINDERS.md): unconditional event-mass equality from conditional-limit hypotheses and class packaging; actual ordered-fibre limit construction remains separate.
- [Countable Strassen ordered coupling](docs/STRASSEN-COUNTABLE.md): exact finite-fibre gluing plus directed compactness, giving normalized full-order couplings and FK domination adapters for countable configurations.
- [Fixed closed-boundary uniqueness](docs/COFINAL-FREE-BOUNDARY.md): source closed-boundary partition identity and fixed-exhaustion martingale uniqueness, plus an explicit matching obstruction. Adaptive regions and their varying filtrations still remain.
- [Free fibres and frontier-mass determination](docs/FRONTIER-DETERMINATION.md): arbitrary-event free-fibre identities and uniqueness from equal finite-region frontier masses; ordinary domination does not obtain that equality.
- [Mod-2 lattice circuit separation](docs/LATTICE-SEPARATION.md): verified parity handshake/crossing and deterministic uniqueness from enclosing incident-component circuits. The defining circuits from dual nonpercolation remain unconstructed.
- [DLR specification deviation](docs/SPECIFICATION-DEVIATION.md): common DLR integrands, mean-insensitivity uniqueness, free/wired deterministic gap bounds and increasing-event cylinder recovery. Still a reduction, not Theorem 5.1 or a random-fibre martingale assembly.
- [Conditionally independent ordered coupling](docs/CONDITIONALLY-INDEPENDENT-COUPLING.md): exact three-marginal fibre product over a common dominating law, conditional factorization and an ordered-triple/domination equivalence. Also proves a filtration-uniform reverse upcrossing bound; the random-exhaustion DLR and martingale assembly of Theorem 5.1 remains open.
- [Nested global outer-stage closure](docs/GLOBAL-OUTER-CLOSURE.md): a second source-form Proposition 1.8(2) path through orientation-free moving-clopen rates, clopen finite arms and external-support geometry; includes an exact ordered-seal counterexample showing why joint adaptive-seal reasoning needs a different argument.
- [Random-region conditional measurability](docs/RANDOM-EXHAUSTION.md): joint exterior conditional measurability, fixed-region fibre constancy and a separate product-coupling reverse martingale; also finite cluster-union regions with closed frontier. No Theorem 5.1 assembly.
- [Sealed-region finite Markov property](docs/REGION-SEAL.md): exact normalized free interior law on general finite graphs with boundary wiring, subject to explicit seal/no-wiring premises.
- [Fixed shell-first comparison](docs/NESTED-SPLIT-COMPARISON.md): the ordered-triple/marginal construction and shell-separation bound, with its nonvanishing error clearly distinguished from equation (9).
- [Conditional AG shift interface and source graph hypotheses](docs/AG-SHIFT.md): exact profile-shift equivalences and product-law zero–one step; positivity of $p_c$ is now proved from the paper's quasi-transitive graph hypotheses. The activation/deactivation strict shifts remain open, with the general-enhancement literature boundary documented.
- [Finite Strassen ordered transport](docs/FINITE-STRASSEN-TRANSPORT.md): explicit Hall transport and true ordered couplings on finite preorders/Boolean products, plus finite cylindrical coupling and disintegration preparation for the countable lift.
- [Finite FKG/Harris/Holley](docs/FINITE-FKG.md): finite-product positive association and monotone comparison, including corank-weight lattice conditions and edge activity; the normalized FK bridge is supplied below.
- [Infinite-volume FKG for FK weak limits](docs/INFINITE-VOLUME-FKG.md): arbitrary-schedule positive association on every increasing measurable pair at $q\ge1$, including endpoint parameters. The proof uses clopen limiting and compact-neighborhood/inner-regularity; it does not establish limit existence, DLR, Burton–Keane or uniqueness. Also covers parameter order and general weak-limit transfer.
- [Boundary-wiring order and free/wired sandwich](docs/BOUNDARY-WIRING.md): corank proof of coarsening monotonicity at $q\ge1$, actual box/weak-limit bounds, and Boolean cylinder equality after mutual domination. Canonical free/wired limits and final measure equality remain.
- [Normalized FK/FKG bridge](docs/WIRED-FKG.md): exact corank/component counts for arbitrary boundary setoids, normalized positive association and $p$-monotonicity at $q\ge1$, and correctly oriented Bernoulli domination. Includes the exact $q<1$ lattice reversal/obstruction, not a negative-association or infinite-volume claim.
- [Sharp no-mass-escape criterion](docs/ONE-EDGE-NO-ESCAPE.md): exact scalar/far-vanishing equivalences and a moving-atom counterexample, clarifying why genuine FK far-connection/geometry estimates remain indispensable.
- [Clopen and dominated escape bounds](docs/CLOPEN-ESCAPE.md): two proved far-vanishing mechanisms, wired-walk escaping-cluster lemmas and conditional box-DLR reductions. Not the genuine source connectivity-partition instantiation or general Proposition 1.8(2).
- [Cylinder and monotone limiting laws](docs/MONOTONE-LIMIT-EXISTENCE.md): full-sequence weak convergence from cylinder/upper-corner convergence and finite-edge nested monotonicity, including a fixed-vertex free-boundary FK limit.
- [Nested mixtures and growing-vertex free FK limits](docs/NESTED-MIXTURE.md): normalized exterior-fibre laws, real nested-box transport and monotone free-mass comparison, yielding a genuine full-sequence weak limit on finite path boxes. Boundary-field, wired-family and uniqueness/DLR statements remain open.
- [Blocked staircase topology](docs/BLOCKED-STAIRCASE.md): converts injective closed turn-at-every-step staircases to dual percolation. `StaircaseBarrierExists`, general circuits and global planar uniqueness remain unproved.
- [Edge-domain monotonicity](docs/EDGE-DOMAIN-MONOTONICITY.md): exact closed-extension weight algebra and edge-injection comparison under an explicit finite positive-association input, plus a stage-level no-escape implication. The genuine `finiteVolumeLaw` exhaustion and far-connection estimate remain unproved.
- [Isolated-vertex FK invariance](docs/ISOLATED-VERTEX-LAW.md): exactly the same normalized FK measure on adding isolated vertices with an arbitrary carried old boundary and free new vertices. Includes genuine `finiteVolumeLaw` preservation and the wired counterexample. `PosAssoc` and nested-stage no-escape remain separate.
- [Fixed-vertex finite-stage no-escape](docs/FINITE-STAGE-NO-ESCAPE.md): a proved normalized-FKG association adapter, genuine nested finite-volume monotonicity and the resulting no-escape theorem at $q\\ge1$, with concrete loop/parallel examples and a fully unconditional $q=1$ loop case. Geometric `hfin` and general limits remain.
- [Mean-convergence random-region repair](docs/RANDOM-REGION-L1-REPAIR.md): actual FKLimit-based comparison using bounded conditionals, tail-uniform mean estimates and Fubini under independence of the region parameter; no full directed-net claim.
- [Countable exhaustion convergence](docs/NET-EXHAUSTIONS.md): a joint null set for countably many reverse-chain exhaustions, plus a precise conditional criterion extending it to full net error control.
- [One-edge conditional limits](docs/ONE-EDGE-LIMIT.md): finite FK singleton identity, sharp antitone-rate one-sided limit and an exact scalar criterion feeding box DLR; no-mass-escape and exhaustion geometry remain explicit.
- [Finite-box fibre assembly](docs/FIBRE-ASSEMBLY.md): genuine conditional-kernel disintegration from equation-(2) singleton conditionals to finite-box DLR, including the converse odds characterization; no arbitrary infinite-limit theorem.
- [Forests are Bernoulli at the effective FK rate](docs/FOREST-BERNOULLI.md): exact normalized FK measure and partition-function factorization under an affine component count, with free-boundary labelled forests at every $q\gt0$ and the strict $q\lt1$ rate comparison.
- [Finite singleton-conditional determination](docs/ONE-POINT-DETERMINATION.md): exact positive finite FK identification from one-edge conditionals, heat-bath uniqueness, and the Dirac/mixed counterexample without full support; infinite conditional-limit assembly remains.
- [Geometric conventions and endpoint transport](docs/CONVENTIONS.md): DLR/Gibbs transport and endpoint weak limits, with the general interior weak-limit conversion still open.
- [Proposition 1.8(1) limiting laws](docs/PROPOSITION18.md): almost-everywhere reverse convergence and extremal DLR weak-limit representation, feeding the subsequently completed Choquet theory.
- [Proposition 1.8(2): source-union and all-box completion](docs/PROPOSITION18-EXTERNAL.md): configurationwise nested free Markov identity, all-rate DLR closure for arbitrary exterior-configuration schedules, and membership in every coherent geometric all-box target under `GlobalAtMostOne`. Unrelated noncoherent setoids remain outside the source class.
- [Net-indexed random-region comparison](docs/NET-CONVERGENCE-INTERFACE.md): a conditional comparison using uniform exterior tail estimates and configuration-dependent exhaustive regions. `HasNetExteriorConvergence` remains unresolved; the net martingale/upcrossing theorem is not proved.
- [Mean-convergence random-region repair](docs/RANDOM-REGION-L1-REPAIR.md): actual FKLimit-based comparison using bounded conditionals, tail-uniform mean estimates and Fubini under independence of the region parameter; no full directed-net claim.
- [Countable exhaustion convergence](docs/NET-EXHAUSTIONS.md): a joint null set for countably many reverse-chain exhaustions, plus a precise conditional criterion extending it to full net error control.
- [Tail conditional decomposition](docs/TAIL-CHOQUET.md): exact barycenter and DLR tail fibres, feeding the subsequent simultaneous-extremality proof.
- [Tail support and conditional uniqueness](docs/NEWEST-MODULES-VALIDATION.md): measurable DLR locus and literal Giry DLR support.
- [Percolation tail zero–one and sharpness](docs/CLUSTER-TAIL-ZERO-ONE.md): finite-cover invariance and Kolmogorov/extermal-DLR dichotomies for infinite existence, with examples separating root and multiplicity events.
- [Simultaneous tail triviality and Choquet](docs/TAIL-CONDITIONAL-TRIVIALITY.md): a.e. extremal tail fibres, full DLR decomposition and uniqueness from extremal uniqueness using Berti–Rigo Theorem 15.
- [Right-wired exploration](docs/RIGHT-WIRED-EXPLORATION.md): ordered FK/FK/Bernoulli coupling, maximal free interiors and scoped equation (9).
- [Nested arm limits and restriction](docs/NESTED-ASSEMBLY.md): restricted equation (9) and subcritical equality of genuine FK weak limits; the remaining event and error inputs are explicit.
- [Nested finite coupling](docs/NESTED-FINITE-COUPLING.md): exact nested marginals and second restriction, with equation (9) conditional only on the genuine maximal-stratum free-interior equality.
- [Arbitrary-boundary nested interiors](docs/NESTED-ARBITRARY-INTERIOR.md): effective-boundary FK filters and two-sided maximal-stratum laws; general cross-setoid comparison and common-upper transport subtleties remain.
- [Common-upper good intersection](docs/NESTED-COMMON-UPPER-GOOD.md): exact nested-triple `hgood` on right-disjoint two-sided extensions, including prefix conditioning and exact pair-mass comparison; metric/infinite-volume assembly remains.
- [Exterior-refined good intersections](docs/NESTED-EXTERIOR-STRATA.md): the same actual ordered-triple identity on every separated exterior-only refinement, with equation (9) and the previous maximal stratum recovered as a special case. Upper-interior restrictions and ordinary metric nesting remain unproved.
- [General specification nesting](docs/SPECIFICATION-NESTING.md): exact arbitrary finite component splitting and conditional FK ratios. The full DLR packaging and weak-limit convention bridge remain.
- [Exact nested DLR specifications](docs/NESTED-FINITE-DLR.md): arbitrary-boundary finite nesting, induced partitions, growing-family local DLR and moving clopen rates. The analytic stabilization/module-specific inputs remain required.
- [Shell-first nested exploration and confined triple](docs/NESTED-REGION-EXPLORATION.md): free-interior continuation, exact pair good-intersections, and the ordinary region-confined common-upper triple/equation-(9) component. Confinement, added-label avoidance and shell incidence are explicit; adaptive cutsets, metric transport and arm vanishing remain.
- [Finite adaptive nested exploration](docs/ADAPTIVE-NESTED.md): arbitrary-history adaptive triples, stopped free interiors and exact good intersections, independent-product conditional transport, and nested big/small/upper marginals. Induced-region compatibility, outside-coordinate copying and the ordinary adaptive equation remain unproved.
- [Nested finite-box assembly](docs/NESTED-FINITE-ASSEMBLY.md): exact cylinder/Bernoulli/reindexing adapters and a single-scale arm estimate with genuine geometric and `hgood` inputs.
- [Canonical nested metric geometry](docs/NESTED-METRIC-GEOMETRY.md): constructed centered finite boxes, nested edge splits, arm realizations and maximal-stratum inclusion from explicit split data; common-upper `hgood` remains.
- [Canonical metric-region split](docs/NESTED-METRIC-REGION-SPLIT.md): actual radial split, maximal-stratum separation and `hD`; uses full-ball roots at one radius, so no growing-radius vanishing theorem.
- [Right-extended nested boxes](docs/NESTED-METRIC-RIGHT-EXTENSION.md): concrete two-sided laws, exact internal cylinders, accepted `hgood`, and finite arm bounds, with added labels explicitly not identified with a standard larger metric box.
- [Right-extension compatibility](docs/NESTED-RIGHT-EXTENSION-COMPATIBILITY.md): exact ordinary nested edge labels, explicit no-cross source-law obstructions and the cardinality argument separating right-disjoint vertices from ordinary metric nesting.
- [Fixed-root split obstruction](docs/NESTED-FIXED-ROOT-OBSTRUCTION.md): a one-crossing-edge proof that whole-ball radial bad-only attachment forces growing roots on the path, plus the general geometric criterion; explored regions remain necessary.
- [Radial root obstruction](docs/NESTED-RADIAL-COUNTEREXAMPLE.md): nonvanishing whole-ball radial error on the Hasse path and a configuration-level root-attachment criterion yielding finite-root arms.
- [Conditional duality through weak limits](docs/DUAL-LIMIT.md): finite equation (12) lifted to conditional-law convergence and dual-family uniqueness, with exact closed/open exterior bookkeeping. Dualizability, Euler certificates, dual strong uniqueness and planar geometry remain open.
- [Total arbitrary-event region kernel](docs/REGION-KERNEL-TOTAL.md): arbitrary measurable events, almost-finite disintegration from a dominating ordered coupling, and free conditional laws on closed frontiers. The conditionally independent ordered coupling is now supplied by the preceding entry; the final Theorem 5.1 uniqueness proof remains.
- [Random-region disintegration](docs/RANDOM-REGION-KERNEL.md): a single countable-strata integral for interior-supported events and actual cylinders, with correct forced connectivity and normalized fibres on attained strata; full regular kernel packaging and the reverse-martingale assembly remain.
- [Random-region DLR fibre identities](docs/RANDOM-REGION-FIBRE.md): measurable induced partitions and exact stratum products, with the free law cut to interior connection; avoids the naive unconditional free-stratum claim.
- [Random closed-boundary regions](docs/RANDOM-CLOSED-BOUNDARY.md): measurable open-cluster regions and closed-boundary exhaustions, ordered-coupling free-boundary events, and exact free finite interior laws; disintegration/reverse convergence remain.
- [Confined exterior strata](docs/CONFINED-STRATA.md): conditional region law on arbitrary separated strata and nested independence, with exact $1/8$ versus $1/16$ obstruction proving pointwise separation is essential. Ordered-triple/metric work remains.
- [Normalized prefix region continuation](docs/PREFIX-CONTINUATION.md): confined region PMF and conditional factorization, by explicit prefix fibre sums and cancellation of the effective added weight; not yet the nested-triple identity.
- [Confinement-scoped region continuation](docs/REGION-CONFINEMENT.md): exact region FK law under arbitrary region setoid and boundary confinement, plus the cross-wiring obstruction and metric support facts; no arbitrary-convention `hgood` claim.
- [Metric-region shell obstruction](docs/NESTED-METRIC-REGION-GOOD.md): ordinary metric complements meet the smaller-box shell, while smaller boxes admit an exact two-sided graph transport; generalized region continuation and `hgood` remain unproved.
- [Ordinary nested gluing](docs/ORDINARY-NESTED-GLUING.md): exact normalized FK transport and ordinary large-box cylinder compatibility under fibre-wired vertex gluing, with new `hgood` and arm obligations.
- [Bad-only root attachment](docs/NESTED-BAD-ROOT-ATTACHMENT.md): finite metric support and conditional fixed-root cylinder estimates, with attachment only off the maximal stratum; no growing-radius vanishing or strong-uniqueness claim.
- [Boundary rigidity at $q=1$](docs/Q-ONE-BOUNDARY-RIGIDITY.md): boundary-free Bernoulli FK laws, fixed-exhaustion existence and unique FK limit/DLR classes for every boundary schedule and every $p\le1$, with sharp one-box counterexamples at other $q$.
- [Geometric-family Theorem 1.10 assembly](docs/THEOREM110-STRASSEN.md): event-domination lifts to ordered coupling, geometric uniqueness families, and a fully verified one-edge nonvacuity instance, with h5_1/h518 and source-faithful restrictions explicit.
- [Arbitrary-exhaustion classical strong uniqueness](docs/SOURCE-UNIQUENESS.md): literal boundary vanishing, nested weak-limit comparison, compactness, and Choquet. A completed source-family reduction to the actual nested equation-(9) estimate and nonpercolating AG window; those remain open.
- [Source upper-window assembly](docs/SOURCE-WINDOW.md): exact Prop 4.2 upper-law domination of every arbitrary source weak limit, the zero-rate endpoint, and uniform-radius Theorem 1.10 windows. The general AG deactivation shift and nested equation (9) are the remaining inputs, not completed results.
- [Finite arm-correction obstruction](docs/ARM-CORRECTION-OBSTRUCTION.md): exact finite FK filtered masses $17/59$ versus $21/71$ prove that conditioning away a root-to-boundary arm does not eliminate boundary influence. This is a rejected repair strategy, not a counterexample to general Theorem 5.1.
- [Finite encounter trees](docs/ENCOUNTER-TREE.md): actual three-arm first-exit prefixes produce a genuine finite tree with open edges, centre degree≥3 and leaves on the prescribed metric sphere. Includes exact tree/branch bounds by sphere cardinality and an all-scales specialization. No multi-centre or Følner conclusion.
- [Actual FK-DLR insertion tolerance](docs/DLR-INSERTION-TOLERANCE.md): positive arbitrary finite-Boolean patterns from the actual DLR comp-product identity, for exhaustion, Gibbs, canonical-region and all source-DLR classes at interior parameters. Direct positive-encounter corollaries; still no global uniqueness/count constancy. No independence or nonpercolation assumption.
- [Burton–Keane encounter and analytic components](docs/BURTON-KEANE-COMPONENTS.md): repaired finite three-arm patching, measurable positive encounters under explicit insertion tolerance, first-moment/Følner obstruction and finite-tree bounds. This does not derive FK insertion tolerance, encounter-tree geometry, cluster-count constancy, exact-two exclusion or global at-most-one.
- [Automorphism invariance, marked forests, and exactly two clusters](docs/BURTON-KEANE-INVARIANCE.md): actual $q=1$ source-law invariance and conditional Følner three-cluster exclusion; configurationwise disconnected-forest count and finite-patch exactly-two exclusion with an explicit ergodic shift. No full count constancy or general BK theorem.
- [Dominated source-DLR compactness](docs/DOMINATED-SOURCE-COMPACTNESS.md): closure under weak limits, barycenters, dominated subsequences and coherent conditional stages, with a common-law criterion under explicit two-sided stage sandwiches. Arbitrary global domination does not by itself supply these bounds.
- [Unit-total upper laws](docs/ARBITRARY-FRONTIER-TOTAL.md): domination forces common frontier masses if the non-DLR upper law has unit finite-base stratum totals. This property is not supplied by nonpercolation alone; the arbitrary common-dominant Theorem 5.1 remains open.
- [Common DLR and frontier replacement criteria](docs/COMMON-FRONTIER-REPLACEMENT.md): exact equivalences showing either a common source-DLR upper law or a common canonical-DLR frontier minorant already forces pairwise equality. This delimits compactness/barycentre replacement, not Theorem 5.1 itself.
- [Comparable nonpercolating DLR uniqueness](docs/COMPARABLE-NONPERCOLATING.md): finite-base closed-frontier strata and domination show comparable nonpercolating DLR laws are equal, including every geometric source convention. A nonpercolating dominant inside the same DLR class gives a singleton; an arbitrary external dominant and unordered members remain open.
- [Deterministic nonpercolating dominant](docs/DETERMINISTIC-DOMINATOR.md): source-DLR uniqueness under a Dirac dominant, constructed by adaptive closed-frontier exhaustion even with infinitely many open edges. Singleton forms require class membership; the general random-dominant Theorem 5.1 remains open.
- [Subcritical and strong-uniqueness assembly](docs/THEOREM110-ASSEMBLY.md): exact Bernoulli subcriticality, monotone-coupling transfer and Choquet uniqueness equivalence, with explicit Theorem 5.1/Prop 1.8(2)/domination/existence residuals.
- [Positive Bernoulli critical probability](docs/BERNOULLI-PC-POSITIVE.md): genuine bounded-degree first-moment path enumeration gives $1/d\le p_c$ and an explicit small-$p$ comparison-rate subcritical window on connected locally finite countable graphs. It supplies no FK domination, DLR, uniqueness, or criticality statement.
- [Subcritical reference baseline](docs/SUBCRITICAL-BASELINE.md): a walk force-open finite-energy proof gives root-independent Bernoulli criticality and the actual subcritical `Percolating G` mass. See also the companion [ordinary supercritical phase and baseline](docs/REFERENCE-BASELINE.md). The approximation-uniform window trade and strict AG shift remain open.
- [Bad-root arm vanishing](docs/NESTED-BAD-ROOT-ARM-VANISHING.md): growing-radius fixed-root cylinder errors vanish and centered FK limits agree under explicit indexed split, coupling and bad-root certificates; not a general strong-uniqueness theorem.
- [Metric conditional DLR assembly](docs/NESTED-METRIC-CONDITIONAL-ASSEMBLY.md): diagonal metric finite-volume comparison with fixed-class DLR uniqueness and maximal-split `hD` supplied; common-upper `hgood` remains.
- [Nested-boundary DLR uniqueness](docs/NESTED-BOUNDARY-UNIQUENESS.md): uniqueness from vanishing conditional-cylinder coupling errors using the completed Choquet theorem.
- [Nested conditional reverse assembly](docs/NESTED-CONDITIONAL-ASSEMBLY.md): outer/inner index maps and fixed-class DLR equality from actual pairwise finite-volume arm bounds, not an assumed vanishing conditional error.
- [Reconstruction and FK-limit closedness](docs/FK-LIMIT-CLOSURE.md): quantitative reconstruction error and DLR continuity, plus the explicit flip-partition example proving measurability alone does not make the DLR class sequentially closed.
- [Interior weak-limit closure](docs/INTERIOR-WEAK-LIMIT.md): continuous and locally constant FK specifications, plus $p\le1$ endpoint normalization; arbitrary unrelated noncoherent sequences remain open.
- [Source-fidelity review](docs/SOURCE-FIDELITY.md): independent statement/trust review of the new transport, AG and planar interfaces.
- [Nonlocal coherent weak limits](docs/NONLOCAL-WEAK-LIMITS.md): DLR closure using exterior at-most-one-cluster uniqueness instead of global local constancy.
- [Global uniqueness before DLR](docs/GLOBAL-FINITE-ENERGY.md): close-box finite energy for coherent arbitrary-exterior interior limits.
- [All-rate finite-energy weak closure](docs/ENDPOINT-GLOBAL-FINITE-ENERGY.md): deterministic arbitrary-exterior endpoint limits and coherent/fixed-specification DLR closure at all rates.
- [Noncoherent finite energy](docs/NONCOHERENT-FINITE-ENERGY.md): pre-DLR exterior uniqueness for arbitrary `IsFKLimit`s with global uniqueness; fixed-source DLR membership remains open.
- [Coherent and DLR mixtures](docs/COHERENT-MIXTURES.md): arbitrary Markov-kernel mixtures and convexity of FK DLR classes, plus coherent/global-uniqueness target mixing. The [source comparison](docs/COHERENT-MIXTURES-SOURCE.md) keeps the unrelated noncoherent branch separate.
- [All-box coherent specifications](docs/COHERENT-ALL-BOXES.md): exact all-finite-box DLR compatibility and exhaustion testing, geometric/finite-volume weak-limit transport and deterministic endpoint closure; no arbitrary noncoherent membership claim.
- [Coherent mixture weak limits](docs/COHERENT-LIMIT-ASSEMBLY.md): genuine weak convergence and exterior marginals of normalized binary mixtures, with fixed/varying coherent DLR and Gibbs assembly under the stated component hypotheses.
- [Noncoherent local stabilization](docs/NONCOHERENT-STABILIZATION.md): varying-source DLR closure under joint neighbourhood stabilization, with strict diagonal bookkeeping but no dense-probe shortcut to the full result.
- [Noncoherent fixed-source counterexample](docs/NONCOHERENT-COUNTEREXAMPLE.md): a one-edge fully wired limit excluded from every geometric DLR class; the unrestricted implication is false, while the paper's infinite-graph theorem is not refuted.
- [Closed-exception stabilization](docs/NONCOHERENT-CLOSED-EXCEPTIONAL.md): varying-coherent-source DLR closure under eventual agreement outside closed null sets, plus the exact compact counterexample showing that almost-everywhere agreement is insufficient.
- [Enhanced DLR and weak-limit transport](docs/ENHANCED-TRANSPORT.md): active-device DLR and weak-limit sandwiches, exact rates and cylinder transport.
- [Source-form Proposition 4.2](docs/PROPOSITION42-SOURCE.md): internally constructed star/cycle device certificates and uniform enhancements on both FK weak-limit and source-convention DLR classes, including quasi-transitive assembly. The AG strict shift remains open; the corrected device-pairing erratum is recorded.
- [AG interface sharpness](docs/AG-SHARPNESS.md): single-law input, strict decrement extraction from `UpperWindow`, set/device dispatch, and full-device Bernoulli consistency. Essential positive-density enhancement stays unproved.
- [Finite Margulis–Russo formulas](docs/MARGULIS-RUSSO.md): finite pivotal derivatives and exact normalization.
- [Dual-parameter equation (12)](docs/DUAL-PARAMETER-DUALITY.md): normalized FK relabelling, finite plane-box duality at the actual dual parameter, and conditional DLR/singleton transport with matching exterior conventions. Endpoints, global cluster inference, certificates and cofinal assembly remain open.
- [Conditional planar DLR transport](docs/PLANAR-DLR-DUALITY.md): configuration complementation, composition-product transport and dual-box PMF-to-kernel adapters. The actual equation-(12) dual-parameter/graph instantiation, planar cluster data and global uniqueness inputs remain open.
- [Exterior determination and planar assembly](docs/PLANAR-ASSEMBLY.md): explicit finite convention-determining windows, primal/dual phase and exactly-one-cluster transport, almost-everywhere dual kernels, and all-box convention replacement. General circuits, finite free duality, dual uniqueness and phase inputs remain open.
- [Combinatorial enclosing circuits](docs/COMBINATORIAL-ENCLOSURE.md): finite cellular exact cut with connected inside/outside, open-connected carrier, and sealed path incidence; rotation/global-labelled adapters. Continuous windows, cofinality and global assembly are not supplied.
- [Planar matroid and Euler duality](docs/PLANAR-MATROID.md): finite labelled duality, certificates, and the remaining embedding gap.
- [Planar matroid, rotation systems and cut circuits](docs/PLANAR-FAMILIES.md): spherical rotation duality, exact special families, cellular exactness and the remaining continuous/Jordan targets.
- [Circular dual-arc separation](docs/CIRCULAR-SEGMENTS.md): unique non-radial chord crossings and exact face path components.
- [Embedded circuit separation](docs/EMBEDDED-CIRCUIT-SEPARATION.md): path-realization avoidance, sphere confinement and the remaining enclosing-circuit exhaustion argument.
- [Finite open cuts and a dual counterexample](docs/OPEN-CUT-SEPARATION.md): geometry-free uniqueness cuts, spherical recovery, and the locally finite primal/non-locally finite face-dual strip refuting the unrestricted dual-nonpercolation target.
- [Strict open-cut obstruction](docs/PLANAR-CUT-OBSTRUCTION.md): every all-open cut must contain its vertices' closed-edge components, ruling out the strict cut-construction hypotheses on the existing staircase for every finite shape. Includes the complementary dual-percolating/two-primal-cluster square-grid strip; not a proof or refutation of Theorem 1.11.
- [Vertex-sealed circuits](docs/SEALED-SEPARATION.md): exact closed-ray refutation of the old crossing-controlled/spherical exhaustions, plus a valid weaker vertex-sealed uniqueness interface and actual box-border/staircase instances. General dual-nonpercolation-to-sealed-circuit construction remains open.
- [Finite cut-graph crossing](docs/CUT-CROSSING-DUALITY.md): an actual below-to-above dual-cut path on the square grid from exact cell/outer degree computations and graph handshake, with transfer to any supergraph. Its primal left-reachable instantiation is supplied by the next entry; global Jordan/compactness arguments are still required.
- [Finite primal/closed-bond duality](docs/CLOSED-BOND-PRIMAL-DUALITY.md): cut sides of left-reachability are proved closed, the closed-bond inclusion carries the cutwalk, and absence of a closed dual crossing gives an open left-to-right primal walk. Includes exact `gridCrossEquiv`/`dualConfig` incidence and both endpoint instances; its converse is supplied below.
- [Sealed parity barriers](docs/BOX-SEAM-SEPARATION.md): an explicit $\mathbb Z/2$ potential separates box walls across a sealed bond seam. Simple closed cell chains satisfy the seam conditions and block open primal crossings; cut-bond seams and a one-row instance are included. The bridge from the closed-bond graph to a cell chain is supplied below.
- [Un-collapsed duality and cofinal primal crossings](docs/GRID-COFINAL-CROSSINGS.md): genuine cell boxes in both reachability directions, crossing-to-infinite-component pigeonhole, and identification with actual dual nonpercolation; global circuit assembly remains open.
- [Finite box crossing duality](docs/FINITE-BOX-DUALITY.md): closed paths become simple cell chains, primal walks map into the parity box, and exactly one of the open left-to-right and closed below-to-above crossings exists in each box with $n>0$. Both constant configurations are checked instances. This is the bounded collapsed-dual result, not an un-collapsing, compactness argument, infinite primal non-switching-order statement, or `GlobalAtMostOne`.
- [Planar grid duals and shell obstruction](docs/PLANAR-DUAL-GRID.md): actual face-edge incidence plus finite uniqueness/nonpercolation results, and an obstruction proving that configuration-dependent Jordan filling, not fixed norm shells, is required.
- [Exact square-lattice frontiers](docs/GRID-FRONTIER.md): straight-segment $\ell^1$ diamond separation and open-connected staircase labels, plus closed-cut trapping; only an all-open cofinal interface check, with explicit restrictive sharpness results.
- [Two-sided separator circuits](docs/SEPARATOR-CIRCUITS.md): exact path-component separation, convex-frontier and spherical instances, scalable exhaustion and labelled dual transport; the general embedding and dual-nonpercolation inputs remain.
- [Infinite open-circuit uniqueness](docs/OPEN-CIRCUIT-UNIQUENESS.md): actual `GlobalAtMostOne` from cofinal primal-open spherical circuits.
- [Primal-open component boundaries](docs/PRIMAL-OPEN-BOUNDARY.md): connected primal circuits from finite dual-open component boundaries, with global finite-box/Jordan compatibility still explicit.
- [Metric finite dual enclosures](docs/DUAL-FINITE-ENCLOSURE.md): finite connected dual boxes with primal-open cuts from dual nonpercolation and properness; labelled plane-dual and Jordan selection remain.
- [Global planar configuration compatibility](docs/GLOBAL-PRIMAL-COMPATIBILITY.md): parallel-collapse and exact dual-restriction transport to a prescribed global graph, with cofinal Jordan geometry still required.
- [Plane-dual component windows](docs/PLANE-DUAL-WINDOW-COMPATIBILITY.md): exact global/local open-component and boundary-cut equivalence from injectivity, box incidence and component coverage, with rotation-system and spherical adapters.
- [Two-face Jordan enclosure](docs/JORDAN-UNICYCLIC-ENCLOSURE.md): unique primal-open boundary cycles and a concrete spherical digon/exhaustion; the fixed infinite example is disconnected and all-open, not the general planar theorem.
- [Connected square-chain exhaustion](docs/CONNECTED-CYCLE-CHAIN-EXHAUSTION.md): cofinal spherical open circuits and fixed-configuration `GlobalAtMostOne` on one properly realized connected locally finite mixed-state example.
- [Connected unicyclic windows](docs/CONNECTED-UNICYCLIC-WINDOW.md): exact cycle-open/exterior-exclusion/cut equivalences and a mixed-state pendant example with explicit enclosure, not a fixed infinite exhaustion.
- [Generalized-theta spherical windows](docs/GENERALIZED-THETA-WINDOW.md): two-branch circuits, bundled plane-dual certificates and explicit metric crossings, including a connected closed-inner-branch example; no fixed infinite Jordan exhaustion.
- [Facial subdivision](docs/FACIAL-SUBDIVISION.md): exact graphic-dual preservation under primal subdivision and facial-edge duplication.
- [One-edge AG gadget](docs/AG-EDGE-GADGET.md): exact enhanced product and finite pivot comparisons, not a global strict shift.
- [Finite AG differential comparison](docs/AG-DIFFERENTIAL.md): joint Margulis–Russo formulas, expected pivot coefficients and $(\delta/2)\,\partial_p\tau\le\partial_s\tau$.
- [Infinite OR-enhanced arm limits](docs/AG-INFINITE-LIMIT.md): exact independent-product marginal and percolation limit, without derivative-limit interchange.
- [Differential trade-bound reduction](docs/AG-DIFFERENTIAL-SHIFT.md): reference-profile masses, continuity from below and the strict shift from a signed finite-volume differential bound. The old closed-region derivative premise is unsatisfiable on clamp collisions; the follow-up repairs it on the interior. Geometric pivot trade remains open; the ordinary reference baselines are now proved.
- [Actual AG mass derivatives](docs/AG-MASS-DERIVATIVE.md): finite/cylinder profile derivatives with exact pivotal identification and the repaired interior trade reduction. The pivotal device inequality and final AG application remain.
- [Pivot-trade obstruction and compact-window repair](docs/PIVOT-TRADE-WINDOW.md): simple 2-cycle and triangle devices prove the old whole-region pivot premise false. Per-event compact constants exist, but approximation-uniform geometry remains open; the ordinary reference baselines are proved separately, with no strict shift claimed.
- [AG comparison-curve integration](docs/AG-CURVE-INTEGRATION.md): monotone finite enhanced probabilities along the explicit interior comparison line.
- [Bounded-range route implants](docs/AG-BOUNDED-RANGE-IMPLANT.md): shared-activation open-walk surgery and exact annular pivot probability bounds.
- [Essential shared-activation devices](docs/AG-DEVICE-ESSENTIALITY.md): genuine double-ray pivotality and quasi-transitive essential packings; support-contained annular bounds without a strict-shift claim.
- [Simultaneous annular sleeves](docs/AG-SLEEVED-ANNULUS.md): actual two-edge bypasses, disjoint-annulus pivot conversion and exact finite-product constants on a constructed graph; no AG shift conclusion.
- [Uniform sleeve packing](docs/AG-UNIFORM-SLEEVE-PACKING.md): disjoint whole templates from lifted base automorphisms, with bounded-distance pivots and exact finite-overlap accounting; no differential or probability conclusion.
- [Sleeve differential comparison](docs/AG-SLEEVE-DIFFERENTIAL.md): exact shared-activation pivot sums, selected-coordinate slope and normalized finite-product curve comparison, without an infinite-volume shift.
- [Synchronized path critical shift](docs/AG-CONSTRUCTED-PATH-SHIFT.md): a connected locally finite homogeneous path with a real normalized percolation curve and strict shift, whose activation opens every edge; not a bounded-range AG reference.
- [Bounded-range bundle critical shift](docs/AG-BOUNDED-RANGE-GRAPH-SHIFT.md): an explicit connected locally finite inhomogeneous graph with independent one-edge activations and exact critical shift from $1/2$ to $1/3$ at activation $1/4$; not the general AG theorem.
- [Independent multi-device activations](docs/AG-MULTI-DEVICE-INDEPENDENCE.md): genuine indexed product laws, per-device/total pivot estimates and finite multi-device differential comparisons with packed support bounds; no infinite-volume AG conclusion.
- [One-sleeve infinite-product comparison](docs/AG-SLEEVE-INFINITE.md): exact finite-trace support, normalized arm inequalities and infinite-cluster comparison through continuity from above, not the full AG reference shift.
- [Indexed independent sleeve limits](docs/INDEXED-SLEEVE-INFINITE.md): finite independent activation marginals and normalized arm/percolation comparisons on graph-infinite traces, with packed disjointness but no infinite-family/reference limit.
- [Quasi-transitive homogeneous tree geometry](docs/AG-TWO-CLASS-TREE-GEOMETRY.md): vertex-transitive reduced-word automorphisms, degree five, invariant rates, a double ray and bounded star packing; no enhanced threshold or `hAG` proof.
- [Two-class tree open-cluster threshold](docs/AG-TREE-THRESHOLD.md): genuine open-connectivity interface, base threshold at $1/2$, and strict activated percolation shift at $3/10$ with activation $1/2$; the exact two-rate result is supplied below.
- [Exact two-class tree critical curve](docs/AG-TWO-RATE-CRITICAL.md): subcritical/supercritical criterion $2b+s+4bs=1$, critical nonpercolation when $b\gt0$, exactly $\operatorname{critBase}(s)=(1-s)/(2+4s)$ and a strict enhanced-versus-base shift for every positive activation. The corner $(b,s)=(0,1)$ is excluded. This is not a general AG `hAG`, FK-window or uniqueness theorem.
- [Two-class activated tree branching](docs/AG-TWO-CLASS-TREE.md): a bounded-degree explicit tree with exact independent recursion, valid-child criterion and a positive activated forward-cluster point; no strict critical comparison yet.
- [Positive device density and activation tails](docs/PACKING-DENSITY-TAIL.md): covering-based density bounds and exact independent all-inactive probabilities, actual uniform-template packing, and a degree-two periodic essential-device example; no general critical-shift claim.
- [Arbitrary-index packed sleeves](docs/AG-INFINITE-PACKED-SLEEVES.md): edge-unique arbitrary-index measurable enhancement and non-strict arm/percolation comparison by finite incident traces and continuity from above, without an infinite derivative sum.
- [Finite independent reference curves](docs/AG-FINITE-REFERENCE-CURVE.md): monotone actual finite-family arm/percolation probabilities on the admissible comparison line, with a constructive maximal time and zero/nonzero phase propagation.
- [Covering reference comparison](docs/AG-COVERING-REFERENCE.md): arbitrary-index monotone global-line/percolation results when **every** original bond is selected, a critical-decrement for the constructed reference model, and corrected spoke-pivot/trace transport. Not positive-density hAG, uniform-spoke enhancement, or FK content.
- [Bounded-coordinate sleeve bridge](docs/AG-BOUNDED-COORDINATE-BRIDGE.md): overlap-tolerant finite-family arm/percolation comparisons through nonnegative union bounds and actual infinite-product marginals, without a full essential-enhancement/reference theorem.


- [Exact triangle-cactus criticality and strict window](docs/CACTUS-EFFECTIVE.md): original triangular-bond laws, effective independent rates, actual-infinite-cluster equivalence, exact homogeneous criticality, and a direct-bond penalty window, with source-separated triangles/double rays at bounded distance. This is a complete explicit-cactus result, not the general AG theorem or Theorem 1.4.
- [Prime-dominated metric weak-limit DLR closure](docs/METRIC-DOMINATED-DLR.md): actual nested-stage identities, finite prime-majorant comparison, finite-path escape estimates, automatic global uniqueness, and a finite-stage-free metric corollary. Restricted to canonical metric boxes and geometric boundary assignments; not general Proposition 1.8(2), all-box Gibbs, or Theorem 1.9.
- [Concrete strict critical shift](docs/AG-STRICT-SHIFT-EXAMPLE.md): base $p_c=1$ to enhanced $p_c=0$ on a path/star inhomogeneous product; not a uniform AG theorem.
- [Quasi-transitive device geometry](docs/GEOMETRIC-DEVICES.md): separated star/cycle devices and uniform bounds from genuine finite automorphism orbits.
- [Finite-box star cutsets](docs/STAR-BOUNDARY-CUTSETS.md): exact boundary-class repair, geometric/free/wired certificates and the unrestricted-wiring counterexample.
- [Finite-box cycle paths](docs/CYCLE-BOUNDARY-PATHS.md): complementary cycle walks, auxiliary path certificates and the active-cycle upper DLR application.
- [Lower-cycle DLR comparison](docs/CYCLE-BOUNDARY-LOWER-PATHS.md): the $q>1$ lower path inequality and geometric two-sided sandwich.
- [Punctured $\ell^\infty$ lattice boxes](docs/LATTICE-BOXES.md): explicit in-box path construction gives $2$-connected punctured lattice boxes, an ingredient for AG pivotal linkage—not the critical shift itself.
- [Geometric active comparisons](docs/GEOMETRIC-ACTIVE-COMPARISONS.md): canonical finite-box containment, eventual activation, both DLR sandwich directions and actual quasi-transitive packings.
- [Generalized theta duality](docs/GENERALIZED-THETA.md): exact bundled-cycle certificates for $K(2,|\iota|)$.
- [Arbitrary-length theta families](docs/ARBITRARY-LENGTH-THETA.md): exact positive branch lengths and subdivision-chain graphic duality.
- [Third-party sources](THIRD_PARTY.md): vendored code and exact commits.

## Verify the code

The project pins `leanprover/lean4:v4.35.0`. Run these commands from this
directory:

```sh
lake exe cache get
./check.sh
```

`check.sh` builds the `FK` root, elaborates `Audit.lean`, and scans the contained
Lean sources for proof placeholders and custom/unsafe axioms. The audit is an
axiom report, not a source-fidelity certificate; see the documentation for the
statements' precise scope. The accepted axioms are `propext`,
`Classical.choice`, and `Quot.sound` (some declarations need fewer).

## Layout

```text
FK.lean                         public import root
Audit.lean                      principal #print axioms commands
check.sh                        reproducible build/audit/scan
FK/                            project-specific Lean modules
CurvatureVariance/             selected FPP-variance percolation sources
PercLib/                       selected PercLib sources
OAI/                           selected OpenAI math sources
docs/                          reader guides, proof status, and provenance
licenses/                      vendored dependency licenses and notices
lakefile.toml                  library and dependency declarations
lake-manifest.json             pinned dependency revisions
lean-toolchain                 required Lean version
```

The `.lake/` build directory and dependency caches are deliberately not release
sources. Mathlib is downloaded from its pinned revision; the other nonstandard
import dependencies are included as source files under their original licenses.
