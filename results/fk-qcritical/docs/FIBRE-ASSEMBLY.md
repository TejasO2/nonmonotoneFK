# Direction 4 (d3): finite-box disintegration from global singleton conditionals

Public module: `FK.FibreAssembly`. Twelve principal declarations were independently rebuilt and allowed-axiom checked before integration. This closes the residual **disintegration/fibre-assembly** step exactly as stated for an assigned measurable boundary function and its global off-edge one-point hypothesis; it does not turn the source's geometric limiting connectivity condition into that assignment, nor pass one-edge conditional integrals through an infinite-volume limit.


Files: `FibreAssembly.lean` (the development), `audit.log` (axiom audit),
`RESULTS.md` (this note). Everything is in the swarm member directory
`.ultramath/smwu0pw30/m7/`; nothing outside it was modified.

## What was missing, and what is now proved

`docs/ONE-POINT-DETERMINATION.md` (repository) records the residual of
Proposition 1.8(2) as two steps:

1. *limit passage*: pass the equation-(2) singleton conditionals of the finite
   laws to an infinite-volume `IsFKLimit`;
2. *fibre assembly*: from "the global one-edge conditional probabilities are the
   specification's" deduce `B.IsDLR hq hp α hα μ`, i.e. the comp-product identity
   `Measure.map B.splitEquiv μ = B.exteriorMeasure μ ⊗ₘ B.fkKernel hq hp α hα`,
   using the fibrewise content of `OnePointDetermination`.

This file closes step 2 completely, and additionally proves the converse, so the
one-point condition is *exactly* the DLR condition for a box (no weakening, no
rename).  Step 1 is untouched here (it belongs to direction 3).

## Main declarations (namespace `FK.InfiniteVolume.FiniteBox`)

Let `B : FiniteBox E` be a finite box (finite vertex type, finite set of global
edge labels, arbitrary `source`/`target`), `0 < q`, `0 < p < 1`,
`α : B.Exterior → B.BoundaryPartition` measurable (the boundary-partition space
carries its discrete σ-algebra), and `μ` a probability measure on the global
configuration space.  Write `B.boxMeasure μ := Measure.map B.splitEquiv μ` on
`B.Exterior × B.Interior` and `B.boxKernel μ := (B.boxMeasure μ).condKernel`.

* `key_identity` — the one-point hypothesis for a box edge `e`, tested against
  arbitrary measurable functions `g` of the off-edge configuration
  (`∫ 1_{e open} g(off) dμ = ∫ openRate(α(ext), e, off) · g(off) dμ`), implies
  the fibre odds identity of the exterior conditional law, tested against every
  measurable exterior set `S`:
  `∫_S κ{true} = ∫_S openRate(α η, e, o) · (κ{true} + κ{false})`.
* `ae_kernel_odds` — the a.e. pointwise version of that identity
  (`ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`).
* `isDLR_of_onePointConditionals` — **the direction's target**: the one-point
  hypothesis for every box edge implies `B.IsDLR hq hp₁.le α hα μ`.
* `isDLR_of_ae_fibre_odds`, `isDLR_of_fibreOdds` — the same conclusion from
  progressively weaker hypothesis forms; `isDLR_of_fibreOdds` assumes only the
  fibre odds identity, i.e. the one-point part (equation (2)) in the exterior
  conditional law.
* `ae_fkKernel_eq_condKernel` — `B.IsDLR` implies
  `B.fkKernel hq hp α hα =ᵐ[(B.boxMeasure μ).fst] (B.boxMeasure μ).condKernel`
  (`eq_condKernel_of_measure_eq_compProd`).
* `fibreOdds_of_isDLR` — **converse**: a DLR law satisfies the fibre odds
  identity.  (Uses `fkMeasure_singleton_odds` below.)
* `isDLR_iff_fibreOdds` — **characterisation**: for one box,
  `B.IsDLR hq hp₁.le α hα μ ↔ ∀ e o S, ∫_S κ{true} = ∫_S r_e(o)(κ{true}+κ{false})`.

Finite ingredients:

* `FKF.eq_fkPMF_of_fibre_odds` — a normalised `ℝ≥0∞` mass function on
  `G.Edge → Bool` whose one-edge fibres satisfy
  `m(off,true) = r(off)·(m(off,true)+m(off,false))` with the equation-(2) rate `r`
  is the actual finite FK mass.  (Reduces to the repository's
  `Glauber.FinProb.eq_fkPMF_of_openRate_odds`, whose `DecidableEq` convention is
  matched by a global classical `DecidableEq` instance in the file.)
* `FKF.fkMeasure_singleton_odds` — the actual finite random-cluster measure
  satisfies that fibre form of equation (2) in `ℝ≥0∞`, for an *arbitrary*
  boundary partition; obtained from `FKBridge.fk_hasEdgeConditional`.
* `measure_eq_of_singleton_eq`, `boxKernel_singleton_ne_top`,
  `boxKernel_sum_singleton`, `boxMeasure_fst`, `off_fibre_eq`,
  `measure_off_fibre`, `fibreConfig`, `splitOff`, `splitBit` — bookkeeping.

## Proof shape

1. `Measure.condKernel` disintegrates `ν = B.boxMeasure μ` along `B.splitEquiv`;
   `Measure.lintegral_condKernel` plus `Measure.setLIntegral_condKernel_eq_measure_prod`
   turn the global one-point integral identities into the odds identity of the
   exterior fibre law (`key_identity`).  Both bits of each box edge are handled
   by the single "true-bit" hypothesis: the false-bit identity is *derived* via
   `ENNReal` subtraction-free algebra.
2. A.e. pointwise odds for every (box edge, off-value) pair: finitely many
   `∀ᵐ` statements (`ae_kernel_odds`), combined by `Finset.induction_on`.  No
   countable null-set bookkeeping is needed: a box has finitely many edges, and
   `IsDLR` is a statement about the measure, not an a.e. statement, so several
   boxes are simply handled one at a time.
3. At a.e. exterior configuration the fibre law is a normalised mass on the
   finite configuration space whose fibre odds are the equation-(2) rates, so
   `eq_fkPMF_of_fibre_odds` identifies it with the finite FK mass; hence the
   fibre kernel equals `B.fkKernel` a.e.
4. `Measure.compProd_congr` plus `Measure.disintegrate` give the comp-product
   identity, i.e. `IsDLR`.
5. Converse: `IsDLR` gives `fkKernel =ᵐ condKernel`; a.e. substitution plus
   `fkMeasure_singleton_odds` gives the pointwise odds, and `lintegral_congr_ae`
   finishes.

## Exact build and audit

```
export LEAN_PATH=<repo>/results/fk-qcritical/.lake/build/lib/lean:<package build dirs>
$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean FibreAssembly.lean
$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean audit.lean
```
(`audit.lean` is `FibreAssembly.lean` plus `#print axioms` lines.)

* Lean 4.35.0, repository build artifacts, default heartbeats.
* `FibreAssembly.lean`: elaborates in about 4 s, exit 0.
* `#print axioms` for all ten main declarations: exactly
  `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, `admit`, `axiom`, `unsafe`.

## Scope and residuals (read this before quoting the result)

* Parameters are interior: `0 < q`, `0 < p < 1`.  Strict positivity of the
  equation-(2) specification is used (it is what makes the one-point part
  determine the finite law); endpoints are not covered, matching the recorded
  scope of `eq_fkPMF_of_openRate_odds`.
* The hypothesis is *relative to a boundary assignment* `α`.  The theorem does
  not construct `α`: to apply it to the FK model on an infinite graph one must
  supply the exterior-connectivity setoid of each exterior configuration
  (`α η` = "connected through edges outside the box"), i.e. the geometric/
  coherent-source input, and one must know that the box specification's
  equation-(2) rate computed with `α η` is the model's own one-point conditional.
  That identification is *not* formalised here: the repository's `FiniteBox` API
  has no global connectivity structure for an infinite edge type.  The theorem is
  therefore the exact "fibre assembly" step, not a proof of Proposition 1.8(2).
* Step 1 (limit passage) is not touched.
* The result is per box.  Deriving Gibbs membership for a countable family of
  boxes requires supplying the one-point hypothesis for each box; there is no
  joint measurability obstruction, since `IsDLR` is not an almost-everywhere
  statement.
* No paper-level numbered theorem is claimed.  In particular this is not
  Theorem 5.1, not Proposition 1.8(2), and not an infinite-volume uniqueness
  statement.

## Dependencies (exact)

* Imports: `FK.InfiniteVolume`, `FK.OnePointDetermination` (via `import` in
  `FibreAssembly.lean`); Lean `leanprover/lean4:v4.35.0`, repository
  `results/fk-qcritical` build artifacts, default heartbeats.
* Repository declarations used (not re-proved here): `FiniteBox.splitEquiv`,
  `FiniteBox.exteriorMeasure`, `FiniteBox.interiorFKMeasure`, `FiniteBox.fkKernel`,
  `FiniteBox.IsDLR`, `FiniteBox.fkKernel_apply` (`FK/InfiniteVolume.lean`);
  `Glauber.FinProb.eq_fkPMF_of_openRate_odds`,
  `Glauber.FinProb.edgeConditionals_strictlyPositive` (`FK/OnePointDetermination.lean`);
  `Glauber.FKBridge.openRate`, `openRate_mem_Icc`, `boolLaw_true`,
  `edgeConditionals`, `fk_hasEdgeConditional` (`FK/FKGlauber.lean`);
  `FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton`, `fkPMF` (`FK/FiniteModel.lean`);
  `Glauber.configSplit`, `outsideMassConj`, `HasConjConditional`,
  `HasEdgeConditional`, `ofPMF`, `ofPMF_mass` (`FK/Glauber.lean`).
* Mathlib declarations used: `MeasureTheory.Measure.condKernel`,
  `Measure.setLIntegral_condKernel_eq_measure_prod`, `Measure.lintegral_condKernel`,
  `Measure.disintegrate`, `Measure.compProd_congr`,
  `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`, `lintegral_map`,
  `lintegral_indicator`, `setLIntegral_const`, `lintegral_const_mul`,
  `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`, `sum_measure_singleton`.
* Nothing outside `.ultramath/smwu0pw30/m7/` is read-modified; the repository
  working tree, toolchain and dependencies are untouched.

## Reproduction

```
cd <repo>/results/fk-qcritical
export LEAN_PATH=$(pwd)/.lake/build/lib/lean:...   # package build dirs
lean ../../.ultramath/smwu0pw30/m7/FibreAssembly.lean     # ~4 s, exit 0
lean ../../.ultramath/smwu0pw30/m7/audit.lean             # ~4 s, 10 axiom lines
```

## Exhaustion-level packaging (added)

* `FK.InfiniteVolume.FiniteBox.HasOnePointConditionals` — the named hypothesis
  (equation-(2) one-point conditionals of one box and one boundary assignment).
* `FK.InfiniteVolume.FiniteBox.isDLR_of_hasOnePointConditionals` — that
  hypothesis gives `B.IsDLR`.
* `FK.InfiniteVolume.mem_dlrMeasures_of_hasOnePointConditionals` — for a genuine
  `BoxExhaustion` and a `BoundaryAssignment`, if every box of the exhaustion
  separately has the one-point conditionals of its prescribed assignment, then
  `μ ∈ DLRMeasures exh Φ hq hp₁.le`.  Countably many boxes are handled one at a
  time: `IsDLR` is a measure identity, so no joint null-set argument and no
  measurability of a box selector is needed.

This is the entry point for whoever supplies the one-point conditionals at
infinite volume (the limit-passage step): a single application yields the whole
DLR class membership.  Axiom audit: both new declarations depend only on
`propext, Classical.choice, Quot.sound`.
