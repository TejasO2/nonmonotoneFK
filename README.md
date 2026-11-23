# nonmonotoneFK: Lean formalization

This repository contains an ongoing Lean 4 formalization of Beffara–Faipeur–Oke,
*A New Bound for the Critical Point of the FK Model for q < 1*,
arXiv:2512.16486v1.

The source project and build instructions are in
[`results/fk-qcritical`](results/fk-qcritical/README.md). Start with its
[proof-status guide](results/fk-qcritical/docs/PROOF-STATUS.md): the actual
finite FK model, finite Theorem 1.2, enhanced dynamics, substantial
infinite-volume transport, finite duality, and critical-window components are
implemented; the whole-paper Theorems 1.4, 1.10, and 1.11 are not yet proved.

Current release check: **9,197 build jobs**, **977 audited declarations**, and
**139 documented FK modules**. The audit accepts only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, or `unsafe` declaration is used in the formalization sources.
