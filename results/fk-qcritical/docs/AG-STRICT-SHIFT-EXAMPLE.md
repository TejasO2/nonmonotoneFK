# Direction (E): concrete strict critical-point shift

## Result

`AGStrictShiftExample.lean` constructs a connected simple graph on `ℕ` with:

- ordinary path edges `(n,n+1)`;
- enhancement-only star edges `(0,n+2)`.

The base inhomogeneous Bernoulli product assigns rate `p` to path edges and rate `0` to star edges. The enhanced product assigns rate `p` to path edges and independent rate `s` to star edges. At `s = 0` the two laws are proved equal (`enhancedLaw_zero_activation`).

For the actual `OpenConnected` root-percolation event, the file proves:

- `base_rootPercolates_null`: base percolation probability is zero for every `p < 1`;
- `base_rootPercolates_one`: it is one at `p = 1`;
- `enhanced_rootPercolates_one`: for every `p` and every `s > 0`, enhanced percolation has probability one;
- `baseCritical_eq_one` and `enhancedCritical_eq_zero` for the `sSup` critical-parameter convention copied from `Percolation.criticalProb`;
- `strict_critical_shift`: `enhancedCritical s < baseCritical` whenever `s > 0`.

`edge_eq_line_or_star` proves that there are no additional edge classes hidden in the rate-function fallback. The root percolation event is the repository's genuine `OpenConnected` event, not a substitute definition.

## Proof inputs

The base argument uses a reachable-walk cut at each closed path edge, exact finite-cylinder masses bounded by `P(open)^N`, convergence of those bounds to zero, and a countable union bound for zero-rate star openings. The enhanced argument derives `iIndepSet StarOpen` from the independent coordinates of `Measure.infinitePi` and applies Mathlib's second Borel–Cantelli theorem `measure_limsup_eq_one`. Infinitely many open direct root links imply an infinite actual open root cluster.

No finite differential comparison, curve integration, implant inequality, or infinite arm-limit theorem is used as a strictness premise. Those interfaces do not by themselves imply a general strict shift.

## Exact scope and residuals

This is an **inhomogeneous product model on a connected non-locally-finite graph**. It is not a proof of the homogeneous same-edge OR theorem, of a bounded-range/quasi-transitive AG theorem, or of any strict interior critical shift. The existing homogeneous OR marginal `AGGadget.orUnit p s` therefore remains only an exact parameter transformation, not a general strictness result.

For fixed `p < 1`, this example has `Θ(p,0) = 0` while `Θ(p,s) = 1` for every `s > 0`. Thus the activation-endpoint increment cannot satisfy a uniform finite derivative/difference-quotient bound. Strictness comes from the global geometry of infinitely many independent bypasses, not from differentiation. The non-locally-finite root also means the locally finite arm-limit API is intentionally inapplicable.

## Verification

Run from this directory:

```sh
./lean.sh AGStrictShiftExample.lean
```

`lean.sh` selects repository Elan toolchain `v4.35.0`, uses only read-only existing project build artifacts for imports, and leaves the heartbeat at Lean's default. The successful default-heartbeat build output is recorded in `AUDIT.txt`. The `#print axioms` commands at the end of the source audit all principal conclusions. A separate scan found no `sorry`, `admit`, `unsafe`, or new `axiom` declarations. No shared results file was edited.
