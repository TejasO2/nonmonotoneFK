# Bad-only fixed-root arm vanishing and centered FK-limit equality

## One-scale errors tend to zero

`NestedBadRootArmVanishing.lean` extends `NestedBadRootAttachment` with
`metricBox_cylinder_abs_sub_tendsto_zero_of_good_of_bad`. The same finite root
set and radius bound $L$ are used at every scale. At scale $n$, the larger and
smaller boxes are genuine centered metric boxes of radii $N(n)$ and $r(n)$;
$n+L\le N(n)$ supplies finite coordinate dependence, and the right split
vertices lie beyond radius $n+L$. Attachment is required only on configurations
outside the maximal split stratum.

The established one-scale finite-volume bound controls the absolute cylinder
error by the upper-Bernoulli mass of the fixed simultaneous root arms.
Almost-sure nonpercolation makes that fixed finite-root mass tend to zero. The
squeeze is on probabilities, not on a whole-ball radial error and not on a
derivative or an infinite sum. Every per-scale split, endpoint and `hgood`
identity remains a real hypothesis.

## Centered FK-limit equality

`eq_of_isFKLimit_metricBox_of_nested_good_of_bad_rootAttached` considers two
genuine `IsFKLimit`s for the same centered metric exhaustion, with their own
arbitrary boundary sequences. For each finite observation base $J$, the fixed
root set `roots J` and `dataWidth` select the smaller radius
$m+\mathrm{dataWidth}$. All sufficiently large centered metric boxes supply the
other side. Fully indexed split/endpoint/right-radius/bad-only-root and `hgood`
certificates control the eventual nested cylinder errors, and the established
reindexed finite-root assembly concludes $\mu=\nu$ from zero upper-Bernoulli
percolation at every vertex.

This is a substantial conditional fixed-centered-class result. It does not
construct the per-scale splits, prove `hgood` for ordinary metric boundary
assignments, supply the bad-only attachments, or infer arbitrary-exhaustion or
general strong uniqueness. No free-interior equality is used as a substitute
for root attachment. Theorem 1.9 remains incomplete.

## Verification

The worker's 420-line handoff prefix was checked byte-for-byte. Its original
source, including both appended theorems, was independently rebuilt with pinned
Lean 4.35.0/default heartbeats. For release the two additions are placed behind
the already verified public `FK.NestedBadRootAttachment` import rather than
duplicating its declarations. Both new principal audits independently passed
the repository's allowed-axiom checker. Every remaining geometric/coupling
input is displayed in the theorem statements.
