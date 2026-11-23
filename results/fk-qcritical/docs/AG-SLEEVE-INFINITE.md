# Infinite-product arm and percolation comparison for one annular sleeve

`AGSleeveInfinite.lean` is self-contained Lean source importing only public
`FK.*` modules. It compiles with Lean 4.35 at the default 200,000 heartbeats.
The checked axiom output is in `audit-output.txt`.

## What is constructed and proved

1. `traceExtend`, `traceEvent`, `traceFinset` and `traceClose` give a finite
   coordinate trace of an arbitrary product configuration. The lemmas
   `pivotal_traceEvent`, `traceExtend_traceClose_annulus` and
   `traceClose_isLocalModification` prove exact pivot and local-surgery
   transport, rather than merely asserting their measurability or probability.
2. `infiniteProductLaw` is the actual inhomogeneous independent product on all
   bond/activation coordinates. `infiniteProductLaw_map_trace` identifies its
   finite marginal, and `infiniteProductLaw_traceEvent` /
   `eventWeight_traceEvent` identify the probability of every finitely
   dependent event with its finite product polynomial.
3. `SleeveTrace.coordinates` contains the actual metric arm edges, full sleeve
   annulus and bypass support, and the shared activation.
   `dependsOn_deviceArmEvent` proves that this finite set really supports the
   enhanced arm on `Sleeve.graph H`.
4. `sleeve_trace_sum_pivot_event_mul_le` proves the exact summed estimate
   `delta^|S| * sum(bond-pivot probabilities) <= 2^|S| * |S| *
   shared-activation-pivot probability`. The graph edge type is arbitrary.
   `sleeveTracePivotSlope_nonneg_of_box` and
   `monotoneOn_traceEventWeight_sleeveLine` prove the corresponding normalized
   differential and comparison curve with the unchanged speed
   `sleeveComparisonSpeed a b S`.
5. `infiniteProductLaw_deviceArmEvent_sleeveLine_le` transports the endpoint
   comparison to every actual infinite-product arm probability. The final
   `infiniteProductLaw_sleevePercolation_sleeveLine_le` passes it to the actual
   enhanced infinite-cluster event. The limit theorem
   `tendsto_infiniteProductLaw_deviceArmEvent` uses the proved decreasing
   intersection `sleevePercolationEvent_eq_iInter` and continuity from above.
   No derivative is interchanged with a limit.

The final hypotheses are exactly the nonempty finite selection, a countable
connected locally finite base graph, and the displayed parameter-box/rate
bounds. The graph is the accepted explicitly constructed `Sleeve.graph H`,
which is connected and locally finite by the existing sleeve geometry.

## Scope and remaining obligations

This is a **one-shared-sleeve limiting percolation comparison**. It is not a
multi-device independent-activation theorem, a zero/one reference law, a
strict critical-point shift, or the full AG reference theorem. Those remain
open; nothing here is named or presented as `hAG`. Existing single-sleeve and
packing results are left unchanged.

## Audits

The file prints axiom audits for the marginal identity, finite-support arm
locality, summed pivot estimate, normalized monotonicity, infinite arm and
percolation limits, and final percolation comparison. Every audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.
