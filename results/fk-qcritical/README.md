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
- [Interior weak-limit closure](docs/INTERIOR-WEAK-LIMIT.md): continuous and locally constant FK specifications, with the nonlocal interior case still open.
- [Enhanced DLR and weak-limit transport](docs/ENHANCED-TRANSPORT.md): active-device DLR sandwiches and rate-exact weak-limit comparisons.
- [Finite Margulis–Russo formulas](docs/MARGULIS-RUSSO.md): finite pivotal derivatives and exact normalization.
- [Planar matroid and Euler duality](docs/PLANAR-MATROID.md): finite labelled duality, certificates, and the remaining embedding gap.
- [Cycle duality and finite cut circuits](docs/PLANAR-FAMILIES.md): exact special-family certificates and the remaining Jordan/infinite-cluster targets.
- [One-edge AG gadget](docs/AG-EDGE-GADGET.md): exact enhanced product and finite pivot comparisons, not a global strict shift.
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
