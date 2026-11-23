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

Parameters are `0 < q` and `p ≤ 1`. The source coherence field `BoundaryConvention.compatible` is used at each fixed small box eventually along the exhaustion.

## Exact residuals

This is a genuine nonlocal interior step, **not all of Proposition 1.8(2)**.

1. The geometric/analytic input is exterior at-most-one-infinite-component uniqueness, `AEAtMostOne`. Global at-most-one-cluster uniqueness is weaker before DLR is known: the existing global-to-exterior conversion `aeAtMostOne_geometry_of_global` itself takes a DLR law and cannot be used circularly here. A nested-box/finite-energy local-modification argument is still needed to obtain exterior uniqueness from global uniqueness for a weak limit.
2. The finite-volume sequence must arise from one coherent convention. Arbitrary unrelated boundary setoids `α n` are not shown to satisfy the needed eventual DLR equations or exterior stabilization.
3. The proved input implies target membership directly by `mem_dlrMeasures_of_atMostOne`; the target is not restricted to locally constant assignments.

The appropriate next step is finite-energy implantation for arbitrary finite-volume weak limits, followed by replacing `AEAtMostOne` with `GlobalAtMostOne` and then eliminating the convention-coherence restriction. Neither step is claimed here.

## Independent verification

Lean 4.35.0 was selected by the repository's `.scratch/elan`. Compilations used default heartbeat settings and wrote `.olean` files only in this member directory. `AuditNonlocal.lean` audits nine principal declarations; all report exactly `propext`, `Classical.choice`, and `Quot.sound`. The combined build/audit output is in `audit.log`; the source scan is in `scan.log`.

Import order is `NonlocalGeometry`, then `NonlocalWeakLimit`, then `NonlocalFiniteVolume`. For an in-project integration, put the files under `FK/`, rename the two local imports accordingly, and add the finite-volume module to `FK.lean` and its principal declarations to `Audit.lean`.
