# Nonlocal interior weak limits (direction B)

## What is proved

`NonlocalGeometry.lean` proves a pointwise geometric fact on a countable locally finite simple graph. At an exterior configuration with at most one infinite component, every geometrically valid boundary assignment is eventually constant in the product topology. Nearby configurations are **not** required to satisfy uniqueness. The proof uses an open walk's finite support for connected pairs and the finite incident-edge support of a finite component for disconnected pairs; stability of that support also preserves finiteness of the component.

`NonlocalWeakLimit.lean` proves weak DLR closure without global local constancy:

- `tendsto_lintegral_indexed_of_tendsto`: lower integrals of a finite indexed statistic converge when the index is locally constant almost everywhere under the limiting law. Every fibre has null frontier, so the finite sum converges by the null-frontier portmanteau theorem.
- `isDLR_of_tendsto_of_ae_eventually_eq`: one-box FK-DLR closure when the boundary partition is locally constant almost everywhere under the limiting exterior law.
- `mem_dlrMeasures_of_tendsto_of_ae_eventually_eq`: the corresponding full-exhaustion statement.

The proof uses actual finite-base cylinders and the actual `reconstruct`/`compProd` FK equation. No stronger general bounded-continuity mapping theorem is asserted.

`NonlocalFiniteVolume.lean` assembles these results for an actual coherent `BoundaryConvention`, with a separately supplied exterior configuration at every larger box. Under `ConventionTransport.AEAtMostOne data.geometry μ` at the limit:

- `mem_gibbsMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne` proves Gibbs membership for the source convention, with no local-constancy hypothesis;
- `mem_dlrMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne` transports the same limit to any geometric target assignment;
- `mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_aeAtMostOne` specializes to canonical closed-exterior finite-volume laws.

Parameters above are `0 < q` and `p ≤ 1` under the stated exterior-uniqueness input. The source coherence field `BoundaryConvention.compatible` is used at each fixed small box eventually along the exhaustion.

`GlobalFiniteEnergy.lean` subsequently removes the separate `AEAtMostOne` input at interior edge parameters. For `0 < q` and `0 < p < 1`, it derives exterior uniqueness from global at-most-one uniqueness **before** proving DLR membership, using finite FK point-mass floors and close-box absolute continuity. It then proves source Gibbs/target DLR membership for coherent arbitrary-exterior finite-volume limits, and weak closure of a fixed geometric DLR specification under global uniqueness. In the latter, source DLR is proved first and convention transport second; there is no circular global-to-exterior DLR argument. Its 13 principal declarations use only the permitted standard axioms.

`EndpointGlobalFiniteEnergy.lean` completes the coherent arbitrary-exterior and fixed-specification results at all rates. At zero and one it proves stronger deterministic endpoint limits directly, with arbitrary time-varying boundaries or filters and without finite-energy positivity, coherence, geometry, or global uniqueness. It does not claim a standalone all-rate `AEAtMostOne` theorem.

## Exact residuals

This is still **not all of Proposition 1.8(2)**.

1. The global-uniqueness-to-exterior argument uses an interior positive point-mass floor. The endpoint module handles zero and one separately by exact deterministic conditional-law limits and singleton DLR classifications.
2. Fixed-source DLR closure still uses a coherent convention. For wholly unrelated boundary setoids, `NoncoherentFiniteEnergy` now proves exterior uniqueness by explicit closing ratios without DLR membership, but does not construct a fixed source or the DLR equation.
3. Target membership uses `mem_dlrMeasures_of_atMostOne`; the target is not restricted to locally constant assignments.

The unqualified noncoherent fixed-source implication is false, as proved in `NoncoherentCounterexample`: a constant fully wired one-edge bypass limit is in no geometric DLR class. Useful remaining work is therefore a source-faithful geometric/coherent formulation and its hypotheses, not proof of the deleted unconditional implication. `NoncoherentStabilization` correctly requires induced specifications and joint stabilization rather than dense probes alone; noncoherent exterior uniqueness does not replace the DLR equation.

## Independent verification

Lean 4.35.0 was selected by the repository's `.scratch/elan`. Compilations used default heartbeat settings and wrote `.olean` files only in this member directory. `AuditNonlocal.lean` audits nine principal declarations; all report exactly `propext`, `Classical.choice`, and `Quot.sound`. The combined build/audit output is in `audit.log`; the source scan is in `scan.log`.

Import order is `NonlocalGeometry`, then `NonlocalWeakLimit`, then `NonlocalFiniteVolume`. For an in-project integration, put the files under `FK/`, rename the two local imports accordingly, and add the finite-volume module to `FK.lean` and its principal declarations to `Audit.lean`.
