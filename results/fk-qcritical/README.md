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
- [Geometric conventions and endpoint transport](docs/CONVENTIONS.md): DLR/Gibbs transport and endpoint weak limits, with the general interior weak-limit conversion still open.
- [Proposition 1.8(1) limiting laws](docs/PROPOSITION18.md): almost-everywhere reverse convergence and extremal DLR weak-limit representation; non-extremal Choquet remains open.
- [Interior weak-limit closure](docs/INTERIOR-WEAK-LIMIT.md): continuous and locally constant FK specifications, plus $p\le1$ endpoint normalization; the nonlocal interior case remains open.
- [Source-fidelity review](docs/SOURCE-FIDELITY.md): independent statement/trust review of the new transport, AG and planar interfaces.
- [Enhanced DLR and weak-limit transport](docs/ENHANCED-TRANSPORT.md): active-device DLR and weak-limit sandwiches, exact rates and cylinder transport.
- [Finite Margulis–Russo formulas](docs/MARGULIS-RUSSO.md): finite pivotal derivatives and exact normalization.
- [Planar matroid and Euler duality](docs/PLANAR-MATROID.md): finite labelled duality, certificates, and the remaining embedding gap.
- [Planar matroid, rotation systems and cut circuits](docs/PLANAR-FAMILIES.md): spherical rotation duality, exact special families, cellular exactness and the remaining continuous/Jordan targets.
- [Circular dual-arc separation](docs/CIRCULAR-SEGMENTS.md): unique non-radial chord crossings and exact face path components.
- [One-edge AG gadget](docs/AG-EDGE-GADGET.md): exact enhanced product and finite pivot comparisons, not a global strict shift.
- [Finite AG differential comparison](docs/AG-DIFFERENTIAL.md): joint Margulis–Russo formulas, expected pivot coefficients and $(\delta/2)\,\partial_p\tau\le\partial_s\tau$.
- [Quasi-transitive device geometry](docs/GEOMETRIC-DEVICES.md): separated star/cycle devices and uniform bounds from genuine finite automorphism orbits.
- [Generalized length-two theta duality](docs/GENERALIZED-THETA.md): exact bundled-cycle certificates for $K(2,|\iota|)$.
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
