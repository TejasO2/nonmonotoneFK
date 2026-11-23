# Proposition 1.8(1): verified result and scope

## Deliverable

`ReverseMartingale.lean` is a self-contained continuation compiled with the repository's Lean 4.35.0 toolchain. It resumes the earlier `ReverseMartingale` work and consolidates the required compactness lemmas from `KernelCompactness.lean` so that the final declarations have no local-module import dependency.

The principal paper-facing declaration is:

- `FK.InfiniteVolume.mem_fkLimitMeasures_of_extremal_dlr`: for a countable edge type, a genuine `BoxExhaustion`, any measurable `BoundaryAssignment`, `0 < q`, `p ≤ 1`, and an extremal element of the actual coerced `DLRMeasures` family, proves `μ ∈ FKLimitMeasures exh hq hp`.

Its direct almost-everywhere inputs and strengthening are also proved:

- `tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr`: full-sequence a.e. convergence of the actual exterior FK conditional-law mass on every finitely supported event to the unconditional mass.
- `tendsto_ae_exteriorConditionalLaw_probabilityMeasure_of_extremal_dlr`: simultaneous cylinder convergence, hence a.e. weak convergence of the actual `ProbabilityMeasure`-valued exterior finite FK laws to the original extremal DLR law.
- Selection of a configuration in the resulting nonempty full-measure set, followed by `tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw`, gives deterministic boundary partitions and the asserted `FKLimitMeasures` membership.

The reverse-martingale results proved here are:

- `FK.ae_not_frequently_alternating_condExp`.
- `FK.exists_ae_tendsto_condExp_iInf_of_bounded`.
- `FK.tendsto_ae_condExp_iInf_of_memLp_two_of_bounded`.
- `FK.tendsto_ae_condExp_indicator_iInf`.
- `FKLimit.tendsto_ae_condExp_indicator_outside_to_tail`.
- `FKLimit.tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn`.

The first result uses alternating visits, finite reversals, the uniform upcrossing Markov estimate, monotonicity of reversed upcrossings, and continuity from below. The pointwise limit is identified by convergence in measure and the existing `L¹` projection theorem. This is not a subsequence-only result.

Four inherited errors were repaired in the local copy: two simplifications of even-index expressions and two `WithTop.untopA` coercions at stopped crossing times.

## Topology and residual inputs

`Configuration E` is the Boolean product. `[Countable E]` supplies the metrizable product setting; compactness of `ProbabilityMeasure` is used through Prokhorov's theorem. Finite-base cylinders are proved clopen and form the cylinder family used for measure identification. The compactness proof takes a further subsequence of every subsequence and identifies its limit by cylinder masses, so the conclusion is convergence in the actual weak topology, not merely convergence of a named real-valued statistic.

The DLR theorems require exactly the actual DLR equations and extremality within the coerced DLR probability-measure family. No FKG inequality, positivity of `p`, coherent-specification compatibility, graph finiteness, or measurability of the random conditional-law map is assumed. No a.e. at-most-one-infinite-cluster hypothesis is used or asserted.

## Verification

Both source files were checked independently with `lake env lean` under ELAN toolchain `leanprover/lean4:v4.35.0` and default heartbeat settings:

- `KernelCompactness.lean`: success.
- `ReverseMartingale.lean`: success, warnings only (deprecation/linter warnings).

`AuditReverse.lean` contains the final source plus ten `#print axioms` commands. Its output is in `audit.log`. Both final DLR declarations and the general reverse/compactness entry points depend only on `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, `unsafe`, or new `axiom` declaration.

## Explicitly remaining

This completes the limiting-law statement and the `ex 𝒢 ⊂ 𝒲` inclusion of Proposition 1.8(1). Choquet existence and ordinary DLR uniqueness from extremal uniqueness were subsequently proved in `TailConditionalTriviality`, using simultaneous almost-everywhere tail extremality. Proposition 1.8(2), strong uniqueness, and the main graph theorems are outside this module. For the weak-limit half of Proposition 1.8(2), `GlobalFiniteEnergy` now handles coherent arbitrary-exterior sequences at $0\lt p\lt1$ under global uniqueness, and `EndpointGlobalFiniteEnergy` supplies exact arbitrary-exterior endpoint identification and all-rate coherent closure. For unrelated interior sequences, `NoncoherentFiniteEnergy` now derives exterior uniqueness from uniform local closing estimates; the unrestricted fixed-source target is refuted by `NoncoherentCounterexample`; a valid source-faithful proof must preserve geometric/coherent hypotheses.

## Integration note

The compactness and closed-exterior transport declarations from `KernelCompactness.lean` are deliberately consolidated at the end of `ReverseMartingale.lean` to provide one independently compilable proof of the final theorems. Integrate them only once, under one module name; do not import both local files verbatim with duplicate declarations. No shared-results file was edited.
