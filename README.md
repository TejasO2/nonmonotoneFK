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

Added [exterior-only good-intersection refinements](results/fk-qcritical/docs/NESTED-EXTERIOR-STRATA.md)
and a [bounded-degree first-moment bound](results/fk-qcritical/docs/BERNOULLI-PC-POSITIVE.md)
proving $1/d\le p_c$ and explicit subcritical comparison-rate parameters. These do
not establish ordinary nested-metric $hgood$, FK domination, or uniqueness.

The [finite normalized FKG bridge](results/fk-qcritical/docs/WIRED-FKG.md) now
identifies wired component counts with the $\mathbb F_2$ corank and proves
positive association and correctly oriented Bernoulli comparison at $q\ge1$.
It remains finite; its $q<1$ reversal is not negative association.

Additional releases add [random-region disintegration](results/fk-qcritical/docs/RANDOM-REGION-KERNEL.md)
on genuine countable strata and a [covering-based reference comparison](results/fk-qcritical/docs/AG-COVERING-REFERENCE.md)
for the sleeved Bernoulli model. The first is not yet full Theorem 5.1 assembly;
the second requires selecting every original bond, not merely positive density.

A [net-indexed region comparison](results/fk-qcritical/docs/NET-CONVERGENCE-INTERFACE.md)
is also included, but only conditionally on `HasNetExteriorConvergence`; the net
upcrossing/martingale theorem this needs is still open.

A separately published [edge-domain comparison](results/fk-qcritical/docs/EDGE-DOMAIN-MONOTONICITY.md)
uses an explicit finite association hypothesis and stage monotonicity. Its correspondence
with genuine `finiteVolumeLaw` exhaustion and no-mass-escape remains to be established.

The planar [vertex-sealed circuit release](results/fk-qcritical/docs/SEALED-SEPARATION.md)
both rules out the older crossing-controlled exhaustion by a closed ray and provides
a valid replacement interface with concrete open-box-border/staircase instances. It
does not construct the general sealed family from dual nonpercolation.

Current release check: **9,330 build jobs**, **2,430 audited declarations**, and
**245 documented FK modules**. The audit accepts only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom
axiom, or `unsafe` declaration is used in the formalization sources.
