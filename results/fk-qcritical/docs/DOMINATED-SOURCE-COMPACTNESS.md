# Dominated source-DLR compactness and conditional-stage replacement

Public module: `FK.DominatedSourceCompactness`.

This is a compactness/DLR-replacement package, **not** the arbitrary-dominant
Theorem 5.1 and not a counterexample to it. It does not assert that an arbitrary
nonpercolating dominant is DLR, has unit stratum totals, or gives the required
conditional-stage bounds.

Unless otherwise noted, `V` is countable, `G` is locally finite, `0 < q`,
`p ≤ 1`, and `Φ` is a fixed `SourceConvention` satisfying `IsSourceGeometry`.
There is no connectedness or `q ≥ 1` assumption, and no interior restriction
`0 < p < 1`.

## What is actually proved

1. `ae_nonPercolating_closeInside`: closing a finite box preserves almost-sure
   nonpercolation by ordinary monotonicity, with no DLR hypothesis.
2. `aeAtMostOne_geometry_of_nonPercolating`: on a nonpercolating support there
   are no infinite exterior components, so the exterior uniqueness used by
   local identification holds vacuously.
3. `stochasticallyDominates_const_of_tendsto` and its lower-bound companion:
   stochastic upper and lower bounds pass through weak limits along a
   nontrivial filter, by cylinder continuity.
4. `mem_sourceDLR_of_tendsto_of_dominated`: a weak limit of source-DLR laws
   dominated by a nonpercolating law remains source DLR, dominated by that
   law, and almost surely nonpercolating.
5. `mem_sourceDLR_of_tendsto_of_eventually_dlr`: the same conclusion when the
   approximants are only eventually DLR at each fixed box of one exhaustion;
   coherence upgrades this to every finite vertex region.
6. `mem_sourceDLR_mixture_of_dominated`: arbitrary measurable probability-
   kernel barycenters, not merely binary mixtures, retain source DLR, common
   domination and nonpercolation when these hold for each output law.
7. `exists_subseq_tendsto_sourceDLR_of_dominated`: a dominated sequence has a
   strictly monotone convergent subsequence with all three properties.
8. `exists_subseq_tendsto_sourceDLR_of_conditionalLaw_dominated`: a coherent
   sequence of actual finite-volume conditional stages dominated by the same
   nonpercolating `ρ` has such a source-DLR subsequential limit. The stage
   domination is an explicit hypothesis; stages need not already be global
   DLR laws.
9. `exists_common_sourceDLR_dominant_of_conditionalLaw_sandwiched`: if every
   stage is **above both** input source-DLR laws `μ,ν` and below the common
   nonpercolating `ρ`, then a source-DLR limit `κ` is above both and satisfies
   `μ = κ = ν` by the comparable-nonpercolation theorem.

## Proof duties discharged

The closing-one-box result identifies the transformed configuration with the
actual `closeInside` image and preserves nonpercolation by deleting finitely
many edges, so it needs no DLR compatibility argument. Nonpercolating limit support supplies the local constancy needed
by nonlocal DLR identification at each box. Coherent source conventions
provide the earlier-box DLR identity of later finite-volume stages. Kernel
mixtures preserve the common upper bound on upper events integrationally.

## Exact unresolved obstruction

The original arbitrary hypothesis `μ ≼ P`, `ν ≼ P` does **not** provide the
stage bounds or any lower bounds in items 8–9. It is not proved that these
coherent stages can be selected from an arbitrary `P`, that unit stratum sums
are one, or that compactness creates a greatest source-DLR law. In particular,
there is no source-DLR replacement from `P` alone and no arbitrary-dominant
general uniqueness conclusion.

Likewise this module uses neither an assumed fixed closed-boundary exhaustion,
a random-filtration convergence theorem, nor ordered-fibre DLR null-section
transfers. Its compactness results are genuinely analytic but are conditional
on the explicitly displayed dominated/coherent-stage premises.

## Verification

Ten fully-qualified principal declarations are audited in `Audit.lean`, each
using only `propext`, `Classical.choice`, and `Quot.sound`. The pinned Lean
4.35 fresh rebuild was independently rerun. Use `./check.sh` from
`results/fk-qcritical` for the complete public check.
