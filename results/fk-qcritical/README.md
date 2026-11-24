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
- [Finite peeling and probability-transport components](docs/AG-PIVOT-TRANSPORT.md): finite AG ingredients, not a strict critical-point shift.
- [Finite FKG/Harris/Holley](docs/FINITE-FKG.md): finite-product positive association and monotone comparison, including corank-weight lattice conditions and edge activity; component/actual-FK-PMF and infinite-volume connections remain.
- [Finite-box fibre assembly](docs/FIBRE-ASSEMBLY.md): genuine conditional-kernel disintegration from equation-(2) singleton conditionals to finite-box DLR, including the converse odds characterization; no arbitrary infinite-limit theorem.
- [Finite singleton-conditional determination](docs/ONE-POINT-DETERMINATION.md): exact positive finite FK identification from one-edge conditionals, heat-bath uniqueness, and the Dirac/mixed counterexample without full support; infinite conditional-limit assembly remains.
- [Geometric conventions and endpoint transport](docs/CONVENTIONS.md): DLR/Gibbs transport and endpoint weak limits, with the general interior weak-limit conversion still open.
- [Proposition 1.8(1) limiting laws](docs/PROPOSITION18.md): almost-everywhere reverse convergence and extremal DLR weak-limit representation, feeding the subsequently completed Choquet theory.
- [Tail conditional decomposition](docs/TAIL-CHOQUET.md): exact barycenter and DLR tail fibres, feeding the subsequent simultaneous-extremality proof.
- [Tail support and conditional uniqueness](docs/NEWEST-MODULES-VALIDATION.md): measurable DLR locus and literal Giry DLR support.
- [Simultaneous tail triviality and Choquet](docs/TAIL-CONDITIONAL-TRIVIALITY.md): a.e. extremal tail fibres, full DLR decomposition and uniqueness from extremal uniqueness using Berti–Rigo Theorem 15.
- [Right-wired exploration](docs/RIGHT-WIRED-EXPLORATION.md): ordered FK/FK/Bernoulli coupling, maximal free interiors and scoped equation (9).
- [Nested arm limits and restriction](docs/NESTED-ASSEMBLY.md): restricted equation (9) and subcritical equality of genuine FK weak limits; the remaining event and error inputs are explicit.
- [Nested finite coupling](docs/NESTED-FINITE-COUPLING.md): exact nested marginals and second restriction, with equation (9) conditional only on the genuine maximal-stratum free-interior equality.
- [Arbitrary-boundary nested interiors](docs/NESTED-ARBITRARY-INTERIOR.md): effective-boundary FK filters and two-sided maximal-stratum laws; general cross-setoid comparison and common-upper transport subtleties remain.
- [Common-upper good intersection](docs/NESTED-COMMON-UPPER-GOOD.md): exact nested-triple `hgood` on right-disjoint two-sided extensions, including prefix conditioning and exact pair-mass comparison; metric/infinite-volume assembly remains.
- [Nested finite-box assembly](docs/NESTED-FINITE-ASSEMBLY.md): exact cylinder/Bernoulli/reindexing adapters and a single-scale arm estimate with genuine geometric and `hgood` inputs.
- [Canonical nested metric geometry](docs/NESTED-METRIC-GEOMETRY.md): constructed centered finite boxes, nested edge splits, arm realizations and maximal-stratum inclusion from explicit split data; common-upper `hgood` remains.
- [Canonical metric-region split](docs/NESTED-METRIC-REGION-SPLIT.md): actual radial split, maximal-stratum separation and `hD`; uses full-ball roots at one radius, so no growing-radius vanishing theorem.
- [Right-extended nested boxes](docs/NESTED-METRIC-RIGHT-EXTENSION.md): concrete two-sided laws, exact internal cylinders, accepted `hgood`, and finite arm bounds, with added labels explicitly not identified with a standard larger metric box.
- [Right-extension compatibility](docs/NESTED-RIGHT-EXTENSION-COMPATIBILITY.md): exact ordinary nested edge labels, explicit no-cross source-law obstructions and the cardinality argument separating right-disjoint vertices from ordinary metric nesting.
- [Fixed-root split obstruction](docs/NESTED-FIXED-ROOT-OBSTRUCTION.md): a one-crossing-edge proof that whole-ball radial bad-only attachment forces growing roots on the path, plus the general geometric criterion; explored regions remain necessary.
- [Radial root obstruction](docs/NESTED-RADIAL-COUNTEREXAMPLE.md): nonvanishing whole-ball radial error on the Hasse path and a configuration-level root-attachment criterion yielding finite-root arms.
- [Random closed-boundary regions](docs/RANDOM-CLOSED-BOUNDARY.md): measurable open-cluster regions and closed-boundary exhaustions, ordered-coupling free-boundary events, and exact free finite interior laws; disintegration/reverse convergence remain.
- [Confinement-scoped region continuation](docs/REGION-CONFINEMENT.md): exact region FK law under arbitrary region setoid and boundary confinement, plus the cross-wiring obstruction and metric support facts; no arbitrary-convention `hgood` claim.
- [Metric-region shell obstruction](docs/NESTED-METRIC-REGION-GOOD.md): ordinary metric complements meet the smaller-box shell, while smaller boxes admit an exact two-sided graph transport; generalized region continuation and `hgood` remain unproved.
- [Ordinary nested gluing](docs/ORDINARY-NESTED-GLUING.md): exact normalized FK transport and ordinary large-box cylinder compatibility under fibre-wired vertex gluing, with new `hgood` and arm obligations.
- [Bad-only root attachment](docs/NESTED-BAD-ROOT-ATTACHMENT.md): finite metric support and conditional fixed-root cylinder estimates, with attachment only off the maximal stratum; no growing-radius vanishing or strong-uniqueness claim.
- [Subcritical and strong-uniqueness assembly](docs/THEOREM110-ASSEMBLY.md): exact Bernoulli subcriticality, monotone-coupling transfer and Choquet uniqueness equivalence, with explicit Theorem 5.1/Prop 1.8(2)/domination/existence residuals.
- [Bad-root arm vanishing](docs/NESTED-BAD-ROOT-ARM-VANISHING.md): growing-radius fixed-root cylinder errors vanish and centered FK limits agree under explicit indexed split, coupling and bad-root certificates; not a general strong-uniqueness theorem.
- [Metric conditional DLR assembly](docs/NESTED-METRIC-CONDITIONAL-ASSEMBLY.md): diagonal metric finite-volume comparison with fixed-class DLR uniqueness and maximal-split `hD` supplied; common-upper `hgood` remains.
- [Nested-boundary DLR uniqueness](docs/NESTED-BOUNDARY-UNIQUENESS.md): uniqueness from vanishing conditional-cylinder coupling errors using the completed Choquet theorem.
- [Nested conditional reverse assembly](docs/NESTED-CONDITIONAL-ASSEMBLY.md): outer/inner index maps and fixed-class DLR equality from actual pairwise finite-volume arm bounds, not an assumed vanishing conditional error.
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
- [Finite Margulis–Russo formulas](docs/MARGULIS-RUSSO.md): finite pivotal derivatives and exact normalization.
- [Planar matroid and Euler duality](docs/PLANAR-MATROID.md): finite labelled duality, certificates, and the remaining embedding gap.
- [Planar matroid, rotation systems and cut circuits](docs/PLANAR-FAMILIES.md): spherical rotation duality, exact special families, cellular exactness and the remaining continuous/Jordan targets.
- [Circular dual-arc separation](docs/CIRCULAR-SEGMENTS.md): unique non-radial chord crossings and exact face path components.
- [Embedded circuit separation](docs/EMBEDDED-CIRCUIT-SEPARATION.md): path-realization avoidance, sphere confinement and the remaining enclosing-circuit exhaustion argument.
- [Finite open cuts and a dual counterexample](docs/OPEN-CUT-SEPARATION.md): geometry-free uniqueness cuts, spherical recovery, and the locally finite primal/non-locally finite face-dual strip refuting the unrestricted dual-nonpercolation target.
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
- [Positive device density and activation tails](docs/PACKING-DENSITY-TAIL.md): covering-based density bounds and exact independent all-inactive probabilities, actual uniform-template packing, and a degree-two periodic essential-device example; no general critical-shift claim.
- [Arbitrary-index packed sleeves](docs/AG-INFINITE-PACKED-SLEEVES.md): edge-unique arbitrary-index measurable enhancement and non-strict arm/percolation comparison by finite incident traces and continuity from above, without an infinite derivative sum.
- [Finite independent reference curves](docs/AG-FINITE-REFERENCE-CURVE.md): monotone actual finite-family arm/percolation probabilities on the admissible comparison line, with a constructive maximal time and zero/nonzero phase propagation.
- [Bounded-coordinate sleeve bridge](docs/AG-BOUNDED-COORDINATE-BRIDGE.md): overlap-tolerant finite-family arm/percolation comparisons through nonnegative union bounds and actual infinite-product marginals, without a full essential-enhancement/reference theorem.


- [Concrete strict critical shift](docs/AG-STRICT-SHIFT-EXAMPLE.md): base $p_c=1$ to enhanced $p_c=0$ on a path/star inhomogeneous product; not a uniform AG theorem.
- [Quasi-transitive device geometry](docs/GEOMETRIC-DEVICES.md): separated star/cycle devices and uniform bounds from genuine finite automorphism orbits.
- [Finite-box star cutsets](docs/STAR-BOUNDARY-CUTSETS.md): exact boundary-class repair, geometric/free/wired certificates and the unrestricted-wiring counterexample.
- [Finite-box cycle paths](docs/CYCLE-BOUNDARY-PATHS.md): complementary cycle walks, auxiliary path certificates and the active-cycle upper DLR application.
- [Lower-cycle DLR comparison](docs/CYCLE-BOUNDARY-LOWER-PATHS.md): the $q>1$ lower path inequality and geometric two-sided sandwich.
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
