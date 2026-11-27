# Arbitrary upper law: the unit-stratum-total comparison

Public module: `FK.ArbitraryFrontierTotal`.

This is a **conditional scoped result**, not the arbitrary-dominant completion
of Theorem 5.1.

For a probability law `ρ` on FK configurations define
`HasUnitStratumTotals hq hp ρ` by requiring, for every finite vertex subset `T`,
that the sum over all finite regions `s` of
`ComparableNonpercolating.stratumTerm hq hp ρ s T` is `1`. This isolates the
unit-total part of the random-region DLR identity without assuming that `ρ`
is source-DLR or canonical-region-DLR.

## Main statement

For a geometric all-region source convention on a connected locally finite
countable graph, with `0 < q` and `p ≤ 1`, suppose:

- `μ, ν ∈ SourceDLRMeasures Φ`;
- `ρ` is almost surely nonpercolating;
- `ρ` stochastically dominates both `μ` and `ν`; and
- `ρ` has `HasUnitStratumTotals hq hp`.

Then
`eq_of_sourceDLR_of_nonPercolating_unitStratumTotals_dominant` proves the
actual equality `μ = ν`, hence agreement on every cylinder.

Variants prove:

- equality of every canonical DLR law's frontier masses with those of the
  dominating unit-total law;
- equality of two canonical DLR laws with finite-base finiteness, with no
  source convention or connectedness required;
- equality of two source-DLR laws when their nonpercolation is supplied
  explicitly, without connectedness;
- downward nonpercolation on connected graphs using the existing countable
  ordered-coupling theorem.

The domination and unit-total assumptions are universally quantified over the
stated parameters, convention, laws and all finite bases/completions.

## Why it works

For fixed finite base `s`, write `f t = stratumTerm ρ s t` and
`g t = stratumTerm μ s t`. Closed-frontier events are decreasing, so
`ρ ≽ μ` gives `f t ≤ g t` at every completion `t`. The new unit-total condition
and canonical DLR/finite-region decomposition give identical total mass one.
Pointwise ordering plus equal finite totals forces every summand to agree.
At `t = s`, the free interior-connect factor is one, giving equal frontier
masses. The strengthened finite-base stratum decomposition then recovers all
finite-coordinate events. Apply it to both `μ` and `ν`.

No DLR identity for `ρ`, comparability of `μ` with `ν`, fixed exhaustion,
random filtration, ordered-fibre transfer, or vanishing of multiplicands is
used.

## Unresolved gap and diagnostic

An arbitrary common nonpercolating dominant need not have unit stratum totals.
Domination supplies only the ordered summands, not the missing unit total.
The remaining goal is to derive this condition from genuine DLR control
or avoid it, rather than rename it as full Theorem 5.1.

On a two-vertex, one-edge graph with `ρ = δ_open`, all configurations are
nonpercolating, and `ρ` dominates the free FK law. For base `{a}`, the small
region term vanishes and the full-region term carries the free one-edge open
mass `p / (p + q*(1-p))`, strictly less than `1` for `p < 1`. This demonstrates
that the proposed implication “nonpercolating implies unit stratum totals” is
false. It is **not** a Theorem 5.1 counterexample: the finite DLR class is
unique. The diagnostic is recorded in the mathematical review; the five
principal formal results concern the conditional comparison above.

## Verification

The five fully-qualified principal axiom audits occur once each in
`Audit.lean`, all restricted to `propext`, `Classical.choice`, and `Quot.sound`.
An independent fresh Lean 4.35 compilation and explicit report-count check
passed. Run `./check.sh` from `results/fk-qcritical` for the public gate.
