# Source-form Proposition 4.2

Public module: `FK.Proposition42Source` (namespace `FK.Prop42Source`).
This proves the uniform star/cycle comparison theorem on pp. 20–21 of
arXiv:2512.16486v1, and constructs the separated devices for the
quasi-transitive graph class in the subsequent proof of Theorem 1.4. It does
**not** prove Aizenman–Grimmett essential enhancement or Theorem 1.4.

## Boundary and measure classes

The paper's `α_n` is a partition of the **actual boundary** `∂Λ_n`. The
project's finite-box model permits a setoid on every vertex. The definition
`HasSourceBoundaryClass` records the required restriction: a vertex whose full
global incidence star is contained in its box has a singleton partition class.
Particularly, no connection through an arbitrary mixed interior/boundary wiring
is inserted into a star cutset.

`hasSourceBoundaryClass_ofBoundaryPartition` extends any setoid on this literal
boundary to such a box partition. `sourceConvention_of_isGeometric`,
`sourceConvention_free` and `sourceConvention_wired` establish inclusion of
the existing geometric, free and wired-at-infinity conventions; the DLR proofs
do not require all of `IsGeometric`. This generalisation does not assert that
arbitrary public `IsFKLimit`s already satisfy the source boundary class, which
would be false for unrestricted all-vertex wiring.

`SourceFKMeasure` combines genuine weak limits having these boundary classes
with DLR measures of measurable source conventions. `IsSourceFKMeasure`, used by
`proposition_4_2_lt_forall` and `proposition_4_2_gt_forall`, existentially
quantify the exhaustion with its labelled edge cover, injective vertex map and
endpoint data. No canonical exhaustion is assumed merely to prove the
comparisons.

## Uniform comparisons and proof obligations discharged

For `q < 1` (equivalently `p < p'`) the result is

$$
\mathbb P_{p+\hat\varepsilon\mathbf1_{\hat E}}
  \preceq \mu \preceq
\mathbb P_{p'-\tilde\varepsilon\mathbf1_{\tilde E}},

and for `q > 1` the mirrored inequalities have
$\mathbb P_{p'+\tilde\varepsilon\mathbf1_{\tilde E}}$ below and
$\mathbb P_{p-\hat\varepsilon\mathbf1_{\hat E}}$ above. Here

$$\hat\varepsilon = |p'-p|(1-\max(p,p'))^{D-1},\qquad
\tilde\varepsilon = |p'-p|\min(p,p')^{L-1},$$

and $p'=p/(p+q(1-p))$. The enhanced parameter functions compute exactly these
formulas. An upper bound $D$ for the full star sizes and an upper bound $L$ for
the selected cycle sizes suffice; the paper's sharp constants are obtained by
choosing the maximal degree and shortest pivotal-cycle length respectively.

The star device comes from the global vertex incident with the selected pivotal
edge. `exists_starCutset_of_source_boundary` supplies the finite closed cutset
from that device, with at most $D-1$ edges; the singleton boundary class is the
only added boundary input and comes from the source's boundary partition.
The cycle path comes from an actual cycle of length $L$, with the selected
pivot removed and at most $L-1$ edges. Both are now constructed internally
rather than repeated as `hStarDevices`, `hCycleDevices`, or similar hypotheses.
The public weak-limit lemma then carries each cylinder comparison to the
limit; the DLR route uses conditioning directly on closed cutsets/open paths.

`proposition_4_2_lt_of_quasiTransitive` and its `gt` variant construct separated
star and cycle families, bounded-distance enhancement families, and the
two-sided comparison from the connected/quasi-transitive/pivotal-cycle inputs.
These are actual global simple-graph devices, not additional example-graph
critical-shift theorems.

## Erratum in the paragraph following the proposition

Page 22, in the proof of Theorem 1.4, asks for the upper comparison while
pairing $\hat{\varepsilon}$ with $\tilde E$ when $p>p'$, and $\tilde{\varepsilon}$
with $\hat E$ when $p<p'$. That reverses Proposition 4.2. The correct choices
are

* $(\hat\varepsilon,\hat E)$ when $p>p'$;
* $(\tilde\varepsilon,\tilde E)$ when $p<p'$.

The corresponding inequalities follow without further assumptions from the
proposition's two conjuncts. **Only the names are swapped in that explanatory
paragraph. This is a correction to the text applied by the formalization, not
a new hypothesis or a critical-shift claim.**

## Verification and remaining scope

The exact source was independently rebuilt under Lean 4.35 against current
public imports at default heartbeats, with no compiler warnings. All 18
principal declaration reports depend only on `propext`, `Classical.choice` and
`Quot.sound`; there are no proof placeholders, custom axioms, unsafe
declarations, `native_decide` or heartbeats overrides. The scoped
`warn.classDefReducibility false` commands affect only linter output.

The reference strict critical shift, proof/unification of Proposition 1.8(2),
and assembly of Theorems 1.4, 1.10 and 1.11 remain open. A clean comparison
report is not completion of the paper's main results.
