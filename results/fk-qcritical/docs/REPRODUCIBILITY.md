# Reproducibility and trust boundary

## Pins

- Lean toolchain: `leanprover/lean4:v4.35.0` in `lean-toolchain`.
- Mathlib: commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Other nonstandard sources: exact upstream revisions in `../THIRD_PARTY.md`,
  with source closures and licenses included.

## Commands

From the directory containing this documentation:

```sh
lake exe cache get
./check.sh
```

(Python 3 and a POSIX shell are used by `check.sh` for audit validation and
placeholder scanning.)
The first command materializes pinned dependency caches. A usual network
connection and enough disk space for Lean/Mathlib are required. After caches
exist, `lake build FK` builds only the aggregate, while `./check.sh` also runs
and mechanically checks the axiom audits and scans declaration syntax.

No scratch directory, VM-local absolute path, or locally installed Elan home
is required by the project source.

## Current verified source state

At the integration recorded here, the aggregate built **9,142 Lake jobs** and
`Audit.lean` audited **508 declarations**. One report (`reachable_iff_of_le_of_adj_reachable`)
uses no axioms; all others use a subset of `propext`, `Classical.choice`, and
`Quot.sound`. No new axiom, proof placeholder, or unsafe declaration was found
in the source scan. The checker now enforces the axiom-list restriction rather
than relying on manual inspection of the output.

The job count includes dependency/module bookkeeping and is not a count of
mathematical theorems. `Audit.lean` is a significant but selected audit surface,
not every declaration in the project. A paper result can also be fully proved
in Lean but have assumptions that make it conditional relative to the source;
consult `PROOF-STATUS.md`.

## Reused code and licenses

Mathlib is fetched normally by Lake at its pinned hash. The smaller closures
from `nitromannitol/FPP-variance`, `tomhutchcroft/perclib`, and `openai/math`
are vendored under the corresponding directories at the fixed commits
in `THIRD_PARTY.md`. Their licenses and original notices are under `licenses/`.
Files with intentional proof holes from upstream comparator tasks are not
imported or included in that closure.

The code follows a classical, noncomputable formalization style where needed.
No project-specific axioms or additional trust declarations are accepted by
the audit script. This establishes a narrow kernel trust guarantee only. It
does not validate the paper's informal prose or infer mathematical novelty.

## Clean-tree smoke test

A separate copy of the source tree, with `.lake/` excluded before dependency
cache initialization, was checked using `lake exe cache get` followed by
`./check.sh`. It passed the 9,128-job build and its then-current 428 axiom audits,
placeholder checks, and documentation checks. Its source contained no VM-local
absolute paths. That test does not change the proof-status limits above, and
its temporary build directory has been removed.
