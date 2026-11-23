# Synchronized-activation strict shift on the homogeneous path

## Files

- `AGConstructedPathShift.lean` — complete Lean 4.35 source, importing only the public accepted `FK.AGInfiniteLimit` FK module plus Mathlib analysis.
- `check.sh` — local read-only checker using the already-installed Lean 4.35 toolchain and the project's existing compiled libraries. It does not build or edit shared sources.
- `AGConstructedPathShift.audit.txt` — output of the final compile and `#print axioms` checks.

## Exact scoped result

Let `rayGraph` be the simple graph on `ℕ` whose only edges are `(n,n+1)`. The file proves that it is connected and locally finite and that every edge is `rayEdge n`. Its ordinary law is homogeneous independent Bernoulli bond percolation with parameter `p`. The joint state is `(ω,α)`, where `α` is a single independent Bernoulli(`s`) activation; the enhanced bond configuration is `ω e || α`. This is a normalized product law, with no zero-rate enhancement-only edges and no inhomogeneous bond rates.

For the actual infinite root-cluster event, `jointLaw_enhancedPercolates` proves

```
θ_enh(p,s) = θ_base(p) + (1 - θ_base(p)) * s.
```

The serial-path geometry and finite-cylinder bounds prove `θ_base(p)=0` for `p<1` and `θ_base(1)=1`. Consequently `θ_enh(p,s)=s` for every `p<1`, including `p=0`, and `θ_enh(1,s)=1`. With the same `sSup` critical-parameter convention as the vendored percolation library, the principal theorem is

```
strict_critical_shift (s : unitInterval) (hs : 0 < s) :
    enhancedCritical s < baseCritical
```

and the component evaluations are `baseCritical = 1` and `enhancedCritical s = 0`. `baseCritical_eq_library_criticalProb` separately identifies the base definition with `CurvatureVariance.Infra.Percolation.criticalProb` through `percolationProb_eq`.

## Deliberate residual / non-claims

The one activation opens **all** path bonds and hence has unbounded range. The construction therefore does not prove the bounded-range/essential-enhancement Aizenman–Grimmett reference theorem supported by the accepted sleeve-packing files, and it does not construct a missing multi-device packing. It is a complete constructed-graph theorem with normalized bond/activation law, not a wrapper around such a reference theorem.

It does not reuse `FK.AGStrictShiftExample`: that module is not imported. There are no star edges, no enhancement-only graph edges, no `p=0` discontinuity in the law or the enhanced probability formula, no derivative/limit interchange, and no inhomogeneous path/star argument.

## Verification

The final source was compiled with default heartbeat options. The exact principal audit output is in `AGConstructedPathShift.audit.txt`; every checked declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. A token scan checks that the delivered Lean file has no `sorry`, `admit`, `unsafe`, or new `axiom` declaration.

To repeat from this member directory:

```
./check.sh AGConstructedPathShift.lean
```

No source-versus-paper fidelity claim beyond this explicitly scoped constructed example is made; the proof status above is separate from the source review. No unaccepted handoff file was used.
