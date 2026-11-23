# Infinite-product limits for finitely indexed independent sleeves

## Deliverables and proof status

- `IndexedSleeveInfinite.lean` is the complete Lean source.
- `audit.log` is the successful axiom-check output.
- The target file compiles with the existing pinned Lean 4.35.0 toolchain and
  default heartbeats. No project source or shared result file was modified.
  The full 9219-job project check was not rerun, because this handoff is a
  standalone member file rather than an integrated public module.

All new declarations are proved. There is no `sorry`, `admit`, `unsafe`, custom
axiom, or heartbeat override in the source.

### Finite-index marginals and traces

`infiniteProductLaw_map_activationCoordinates` identifies the actual infinite
product's restriction to the subtype of all activation coordinates with the
finite Bernoulli product having the corresponding device-wise laws. The event
form is `infiniteProductLaw_activation_traceEvent`.

For a finite device type `ι`, `coordinates` contains the finite metric arm,
the union of all selected annuli, all activated spokes, and every activation
coordinate. `dependsOn_deviceArmEvent` proves that the enhanced arm is
measurable through this trace in the dependency sense used by the exact
infinite-product marginal theorem. The ambient sleeved graph's edge type need
not be finite.

### Exact pivot and support accounting

For each device `i`, closing only the `i`-th annulus sends a selected-base-bond
pivot to activation pivot `i`.
`trace_sum_edgePivotal_event_mul_le` gives the exact normalized bound
`δ^|Sᵢ|` on the sum and `2^|Sᵢ| |Sᵢ|` on its right side.

`sum_baseTrace_eq_sum_devices` proves that disjoint annuli give a
duplicate-free decomposition of moved-base pivot sums. Thus the simultaneous
finite-trace affine derivative has one activation term per device. The common
speed is exactly the accepted
`independentComparisonSpeed a b R = sleeveMinorant a b ^ R / (2^R * R)`,
where every annulus has the same positive size `R`.

For a finite part `F` of the actual whole-template automorphism packing,
`card_baseSupport_packed` proves the exact moved-base-support cardinality
`|F| * |S|`, with annulus disjointness obtained from the accepted packing.

### Infinite-product arm and percolation comparisons

Assume `H` is connected and locally finite, the device family is finite, its
annuli are pairwise disjoint and have common positive size `R`. Along
`indexedLine`, each selected annular bond moves from `p` towards `p - c*T`,
all other ordinary bonds stay at `p`, and every separate activation moves from
`s` towards `s + T`. All rates are required to lie in the stated interior box
`[a,b]`, with `0 < a` and `b < 1`.

`infiniteProductLaw_deviceArmEvent_indexedLine_le` compares actual normalized
independent-product probabilities of the enhanced arm at every radius `n`.
The proof identifies their finite-trace polynomials, proves monotonicity using
the exact finite derivative and pivot bound, and never takes an infinite-graph
derivative.

With `[Countable V]`,
`infiniteProductLaw_indexedPercolation_indexedLine_le` gives the same endpoint
inequality for the actual infinite-cluster event on the constructed sleeved
graph. Measurability of `deviceConfig` is proved for the finite indexed device
family. Continuity from above is applied separately to the two arms at every
radius; no derivative is passed through the limit.

`infiniteProductLaw_packedPercolation_indexedLine_le` specializes this result
to a finite subfamily of the accepted uniform whole-template packing. Its
geometric disjointness and equal-cardinality premises are proved, not repeated
as assumptions.

## Residual scope

- The device family is finite. This is not an infinite-product limit in the
  number of devices, an exhaustion of an infinite packing, or a summation
  theorem for infinitely many activation derivatives.
- Pairwise-disjoint annuli and a common positive annulus size are required for
  the displayed simultaneous common-speed comparison. Unequal sizes and
  overlap correction are not claimed here.
- This is a comparison for the explicitly constructed sleeved graph and its
  independent bond/activation product. It is not a theorem about an arbitrary
  essential enhancement or an FK/DLR law.
- The result does not prove reference zero/one percolation, a strict critical
  parameter shift, Theorem 1.4, or the full Aizenman–Grimmett reference
  theorem. The countable-vertex hypothesis applies to the infinite-cluster
  continuity statements, not to the finite-trace comparison.

`AGBoundedCoordinateBridge` removes the disjointness requirement at the cost of
using a nonnegative trace-union bound rather than exact disjoint-index sums.
It retains finite devices and a common positive annulus size; no infinite-device,
reference-percolation or critical-shift claim follows.

## Source comparison (separate from proof status)

This is the scoped indexed infinite-volume extension called for in Direction E
and addresses the finite-family part of the repository's remaining AG
obligation. No new source-paper equivalence is claimed. I did not perform a
new comparison against the primary paper HTML in this direction; the source
artifact to review is therefore the explicit Lean statement above, especially
its finite-family, disjointness, and uniform-size hypotheses, rather than a
paper theorem name.

## Verification

Using the already-installed `leanprover--lean4---v4.35.0` toolchain under
`$HOME/.elan/toolchains`, the target was compiled with `lake env lean` from
`results/fk-qcritical`. The exit status was zero and produced no warnings.

The following twelve declarations were audited: the activation marginal, arm
dependency, per-device pivot sum, disjoint trace decomposition, packed support
cardinality, trace slope, trace monotonicity, infinite-product arm comparison,
indexed device measurability, arm-limit continuity, generic indexed
percolation comparison, and packed percolation comparison. Every audit reports
exactly `[propext, Classical.choice, Quot.sound]`; see `audit.log`.
