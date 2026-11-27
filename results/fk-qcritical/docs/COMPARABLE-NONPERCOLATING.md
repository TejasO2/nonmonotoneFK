# Comparable nonpercolating DLR laws

Public module: `FK.ComparableNonpercolating`.

This is a scoped uniqueness mechanism for arXiv:2512.16486v1 Theorem 5.1,
not a proof under an arbitrary dominating law.

## Main results

Throughout, `V` is countable, `G` is a locally finite simple graph, `0 < q`
and `p ≤ 1`.

1. `eq_of_stochasticallyDominates_of_canonicalRegionDLR`: if `μ` and `ρ`
   satisfy the canonical exterior-component DLR equations at every finite
   vertex region, their explorations from every **finite** base are almost
   surely finite, and `ρ` stochastically dominates `μ`, then `μ = ρ`.

2. `eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating`: for any
   `SourceConvention Φ` satisfying `IsSourceGeometry Φ`, if both laws belong
   to `SourceDLRMeasures Φ`, both are almost surely nonpercolating, and `ρ`
   dominates `μ`, then `μ = ρ`.

3. `sourceDlr_eq_singleton_of_mem_nonpercolating_dominant`: for connected `G`,
   if a nonpercolating `ρ` belongs to `SourceDLRMeasures Φ` and dominates every
   member of that class, the class is exactly `{ρ}`.

The last statement has existence supplied by the actual member `ρ`. It does
not require `ρ` to be Dirac, Bernoulli, prime-dominant or independent on any
region. It also does not infer a source weak-limit existence theorem.

## Finite-base frontier mechanism

A closed-frontier event is decreasing. If `ρ` dominates `μ`, the probability
of its complement is larger under `μ`, so its closed-frontier mass is larger
under `μ`. Finite-base explorations are almost surely finite under
nonpercolation.

For a finite base `s`, the forced interior-connection factor is trivial when
the explored region is `s` itself. The DLR identities therefore give a total
mass one decomposition over finite completions. Domination orders every
summand in the same direction, while the totals are equal. A nonnegative-series
argument forces equality term by term, including at `s`, hence equality of
every closed-frontier mass. The finite-base stratum decomposition then gives
equality on all finite-coordinate cylinder events.

The strengthened `FiniteRegionOnFiniteBases` interface does not require
finiteness of an exploration from an infinite base. Nor does it transfer a
null section through an ordered coupling, interpolate DLR identities to an
ordered fibre, or rely upon a reverse martingale along a correlated random
filtration.

For a general geometric source convention, nonpercolation makes all source
exterior components finite. Its merge and finite-separation rules then identify
it with the actual exterior-component partition almost everywhere; standard
DLR-kernel transport converts to the canonical form. The singleton wrapper
transfers nonpercolation downward using an accepted countable ordered coupling;
graph connectedness is needed only there.

## Exact remaining gap and source discipline

An arbitrary nonpercolating common dominant `P` need not belong to the source
DLR class, and two class members `μ` and `ν` need not be stochastically ordered
with one another. Neither hypothesis can be dropped from these theorems by
asserting it in prose. General Theorem 5.1 under such an arbitrary dominant is
still open. A subsequent argument must replace that dominant by one with the
necessary DLR/common-frontier structure, or derive the needed comparison
without the replacement.

The finite `ArmCorrectionObstruction` separately rules out one shortcut based
on conditioning away root-to-boundary arms. It does not conflict with the
proved normalized frontier-stratum comparison here.

Grimmett's Theorem 5.119 uses a special finite-volume product-cutset coupling
whose lower interiors are free on the maximal cut stratum. Arbitrary ordered
coupling alone does not supply that property. The new theorem avoids invoking
it, but also does not solve the arbitrary external-dominant generalization.

## Verification

Ten fully-qualified principal axiom audits are in `Audit.lean`, all restricted
to `propext`, `Classical.choice`, and `Quot.sound`. The fresh Lean 4.35 source
rebuild was independently rerun at default heartbeats; the public gate is
`./check.sh` from `results/fk-qcritical`.
