# Diagonal metric conditional DLR assembly

`NestedMetricConditionalAssembly.lean` joins the canonical centered metric
finite-volume estimates to `NestedConditionalAssembly`. It proves two fixed-class
DLR uniqueness theorems on that exhaustion; it does not prove general strong
uniqueness.

## Results

`eq_dlr_metricBox_of_diagonal_nested_good` assumes a connected countable
locally finite simple graph, a center, interior parameters `0 < q` and
`0 < p < 1`, two laws in one fixed `DLRMeasures` class, and zero root
percolation at the actual upper rate. The displayed diagonal `hgood` is an
explicit equality of first/good and second/good intersections of the real
nested FK/FK/Bernoulli coupling. The good-event complement inclusion `hD`
is also an input to this version.

Both scale maps are `n ↦ 2 * n`. For each observation base `J`, when
`n ≥ dataWidth G o J (roots J)`, the proof chooses
`m = 2 * n - dataWidth G o J (roots J)`. The smaller and larger finite boxes
therefore coincide at radius `2 * n`. The actual metric finite bound applies
to the corresponding `Φ.partition`/exterior-restriction evaluations, and
`farConnection_add_antitone` converts it to the error radius expected by the
conditional reverse assembly. The existing nonpercolation-to-one-arm theorem
supplies the vanishing error.

`eq_dlr_metricBox_of_diagonal_maximalSplit_good` has the same stochastic and
geometric fixed-class inputs but adds a fully `(J,m)`-indexed split
presentation: sources/targets, edge/reindexing equivalence, the actual pulled
back maximal stratum, endpoint map, left-root containment, and
right-beyond-radius coverage. It applies
`bad_maximalSplit_subset_closedLocalEvent` to **prove `hD`**. Only the displayed
diagonal common-upper `hgood` remains a stochastic premise; `hD` is not assumed
in this second theorem.

## Exact residuals

`NestedMetricRegionSplit` supplies a genuine canonical ball split, but with
whole-ball roots at the same radius. That scoped geometry does not supply the
growing-radius vanishing probability or the common-upper `hgood` by itself.
These theorems do not construct the intended exploration-region split,
establish common-upper `hgood`, prove fixed-source DLR for arbitrary
noncoherent weak limits, or assert Theorem 1.9/1.10. The maximal-split geometry
remains an explicit input, just as `hgood` remains explicit in both results.

## Verification

The source independently elaborated with the repository's pinned Lean 4.35.0
toolchain at default heartbeats. Both principal declarations were included in
the public `Audit.lean`; each reports only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, `unsafe`, new axiom, or heartbeat override is
present. The integrated `check.sh` verifies the complete build, axiom audit,
documentation coverage, and source scan.
