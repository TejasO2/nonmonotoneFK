Public module `FK.FKLimitClosure`. Independently rebuilt and all ten principal declarations axiom-validated. The positive theorem assumes eventual a.e. agreement with a continuous target; the flip specification is not a geometric counterexample. Compactness uses genuine reindexing rather than fixed-exhaustion closedness.

# Weak closedness of finite-box FK DLR classes (swarm smwu0pw30, member m3)

Deliverable: `.ultramath/smwu0pw30/m3/FKLimitClosure.lean` (918 lines, self-contained
module; imports `FK.PlanarForestDuality` and `FK.InteriorWeakLimit` from the project).
No `sorry`/`admit`/custom axiom/`unsafe`; audit log in `audit.log`.

## Build

```
cd results/fk-qcritical
/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean \
  ../../.ultramath/smwu0pw30/m3/FKLimitClosure.lean
```
Uses the project's pinned toolchain (Lean 4.35.0) and existing `.lake` oleans; 3.4 s
on a warm cache, no `lake build` of the project needed. Axiom audit (`AuditVersion.lean`
= module + `#print axioms`) reports only `propext`, `Classical.choice`, `Quot.sound`
for all ten audited declarations.

## Main results

### 1. Quantitative stability of FK reconstruction (`FiniteBox` namespace)

* `reconMeasure B hq hp a ha nu` = `map glue (nu ⊗ actual FK kernel)`; the raw form of
  the repository's `reconstruct`, with `isDLR_iff_recon` identifying the existing
  `IsDLR` comp-product equation with invariance under reconstruction.
* `abs_integral_reconMeasure_sub_le`: if two measurable specifications agree off a
  measurable set `A` of exterior configurations, then for every bounded continuous `f`
  the glued laws differ by at most `2 * ‖f‖ * nu.real A`. Proof: split `nu` into
  `nu.restrict A + nu.restrict Aᶜ`, show the two reconstructions coincide on `Aᶜ`
  (`Measure.compProd_congr`), and bound each restricted piece by its mass.
* `integral_reconMeasure_eq_of_ae`: if `a = b` almost everywhere for `nu`, the test
  integrals of the two glued laws coincide (the case `nu.real A = 0`).

### 2. Weak closedness for asymptotically locally constant specifications

`FiniteBox.isDLR_of_tendsto_of_tendstoMeasure`: let `mu_i → mu` weakly, let each `mu_i`
be `B.IsDLR` for its own measurable `alpha_i`, let `beta` be measurable with
`Continuous (B.conditionalLaw hq hp beta)`, and let `alpha_i = beta` almost everywhere
for the exterior marginal of `mu_i` (eventually along the filter). Then `B.IsDLR beta mu`.

This is strictly weaker than the repository's `isDLR_of_tendsto` hypothesis: the
`alpha_i` need not be locally constant, nor equal to `beta`, only asymptotically equal
in measure. Corollaries:

* `..._of_isLocallyConstant` (uses `continuous_conditionalLaw_of_isLocallyConstant`);
* `mem_dlrMeasures_of_tendsto_of_tendstoMeasure`: exhaustion level, source assignment
  `Phi` vs target locally constant `Phi'`.

Mathematical content: reconstruction is the exterior integral of the conditional
integral; an a.e. change of specification changes each test integral by at most
`2‖f‖ * (exterior mass of the disagreement set)`, and continuity of `beta`'s
specification makes the limit functional continuous.

**Intended use (residual).** The remaining input for the campaign's interior
weak-limit conversion becomes: *the canonical free/open-component boundary partition
agrees a.e. with a fixed locally constant partition for the limit law* — which is what
nonpercolation / a.s. at-most-one-infinite-cluster and finite-connectivity bounds are
supposed to supply. That input is **not** proved here; no paper theorem is claimed.

### 3. Measurability alone is not enough (counterexample)

The one-edge box `oneEdgeBox : FiniteBox ℕ` has `Vertex = Bool`, a single labelled edge
`0` from `false` to `true`, and infinitely many exterior labels. All finite FK
computations are done at `q = 2`, `p = 1/2`:
`oneEdge_free_allOpen_mass = 1/3`, `oneEdge_wired_allOpen_mass = 1/2`,
`oneEdge_free_fkMeasure_ne_wired` (the free and wired one-edge laws differ).

`flipPartition : Exterior → Setoid Bool` is wired (`⊤`) exactly at the all-open exterior
configuration and free (`⊥`) elsewhere. It is `Measurable`
(`measurable_flipPartition`), the source set being a countable intersection of cylinders.
`extPerturb n` is the exterior configuration which is all open except at label `n+1`;
then `extPerturb n → extAllTrue` (`tendsto_extPerturb`), `extPerturb n ≠ extAllTrue`, so
`flipPartition (extPerturb n) = ⊥` while `flipPartition extAllTrue = ⊤`.

* `isDLR_reconPM_dirac`: each glued law `reconPM flipPartition (dirac eta)` is DLR for
  `flipPartition` (`exteriorMeasure_reconPM` computes its exterior marginal).
* `integral_openEdgeIndicator_fkMeasure`: the open-edge indicator integrates to the mass
  of the all-open box configuration (`1/3` free, `1/2` wired).
* `exists_weakLimit_not_isDLR_of_measurable` / `dlrClass_flipPartition_not_seqClosed`:
  a subsequence of the DLR laws converges weakly to `mu`; the exterior marginal of `mu`
  is the Dirac mass at `extAllTrue`; weak convergence forces the open-edge indicator
  integral to be `1/3`, while DLR membership would force `1/2`. Hence `mu` is not DLR.

So the DLR class of a **measurable** specification is not sequentially closed. This
upgrades the repository's disclaimer ("measurability alone does not justify passing the
DLR reconstruction through weak convergence", `docs/INTERIOR-WEAK-LIMIT.md`) from an
open gap to a theorem, and shows the local-constancy/continuity hypothesis in
`FiniteBox.isDLR_of_tendsto` cannot be dropped.

### 4. Infinite-volume limit structure

* `IsSubseqFKLimit`: subsequential FK limits along a fixed genuine exhaustion.
* `exists_isSubseqFKLimit`: for every exhaustion and every boundary-setoid sequence some
  subsequence of finite-volume laws has a weak limit (compactness only).
* `isFKLimit_of_isSubseqFKLimit`: such a limit is an `IsFKLimit` for the coarsened
  (reindexed) exhaustion, which is again a genuine exhaustion.

## Scope and residuals

1. No paper theorem is claimed. The positive closedness result is a strict weakening of
   the continuity hypothesis in the existing interior weak-limit module, not the general
   interior conversion of Proposition 1.8(2).
2. The hypothesis "asymptotically a.e. equal to a fixed locally constant specification"
   is not derived from percolation geometry here.
3. The counterexample is a *one-edge-box, fixed-parameter* statement. It does not refute
   any geometric/convention statement of the paper; the specification `flipPartition` is
   not induced by open clusters of the exterior configuration.
4. Full weak closedness of `FKLimitMeasures` (for varying boundary-setoid sequences) is
   not proved; only subsequential existence and the coarsening reindexing are.
5. Nothing outside `.ultramath/smwu0pw30/m3/` was modified; no toolchain, dependency or
   release change.
