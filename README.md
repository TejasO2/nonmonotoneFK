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

The two-class reduced-word tree now has an [exact two-rate critical curve](results/fk-qcritical/docs/AG-TWO-RATE-CRITICAL.md):
$2b+s+4bs<1$ gives nonpercolation, the reverse inequality gives positive open-cluster
percolation, and equality with $b>0$ gives nonpercolation. The critical base rate is
$(1-s)/(2+4s)$, strictly decreasing for positive activation. The corner $(0,1)$ is
excluded; this tree theorem is not the paper's general AG, FK-window or uniqueness result.

A new [planar cut analysis](results/fk-qcritical/docs/PLANAR-CUT-OBSTRUCTION.md)
shows that the strict all-open-cut construction is unsatisfiable for arbitrary finite
sets on the existing dual-nonpercolating staircase. This delimits a sufficient proof
interface, not the paper's planar theorem or its at-most-one-cluster conclusion.

Current release check: **9,322 build jobs**, **2,269 audited declarations**, and
**236 documented FK modules**. The audit accepts only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, or `unsafe` declaration is used in the formalization sources.
