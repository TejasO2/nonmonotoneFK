# Connected square-chain exhaustion on one fixed graph

The graph on `ℕ × Option (Fin 4)` consists of four-cycles with one pendant each,
joined by north-east connectors. It is connected and locally finite. Its fixed
configuration opens cycles/connectors and closes pendants, so it is not all open.

Blocks lie on origin-centred sup-norm squares of scale $4(n+1)$ with straight
segment arcs. Vertices avoid every selected half-integral sphere; metric-ball
preimages are finite. Early prefixes are finite and open-connected, and every
arc crossing a selected sphere is controlled by its corresponding prefix.

`sphericalOpenCircuit_prefix` hence gives an actual spherical open circuit at
radius $N+1/2$ for every `N`. These form a cofinal
`HasOpenCircuitExhaustion`, and `exteriorInfiniteCluster_zero` gives a real
infinite open component. The established open-circuit theorem concludes
fixed-configuration `GlobalAtMostOne` nonvacuously.

This is an explicit properly realized non-all-open example, not a construction
from dual nonpercolation, an arbitrary continuous/Jordan embedding theorem, or
a proof of Theorem 1.11.

## Verification

The exact source was independently rebuilt using Lean 4.35.0/default
heartbeats. The coordinator only fully qualified the worker's short audit
names. All 18 principal declarations passed with only the three standard Lean
axioms; forbidden declarations and placeholders are absent.
