Public module: `FK.PrefixContinuation`. All 13 principal declarations were rebuilt with Lean 4.35. The residual concern that the factorization was only a weight sum is now closed: the normalized `PMF.filter(·)` map is computed, the positive partition and conditioning normalization cancel, and the same region law survives additional added-stratum conditioning. What remains is the ordered-triple nested identity and metric convention confinement, not normalization.

# Direction 7 — prefix-confined PMF factorization and the common-upper identity

Member `m2` (swarm `smwu2ryc1`). Single source file: `PrefixContinuation.lean`
(module would be `FK.PrefixContinuation` on integration; it imports only
`FK.RegionConfinement`).

**Claim of this deliverable.** `docs/REGION-CONFINEMENT.md` records one exact
residual: the weight-level prefix factorization `ambientWeight_prefix_sum` was
proved, but

```text
PMF.map (fun ρ => ρ ∘ Sum.inl) ((G_big.fkPMF ζ).filter (prefixEvent ξS))
  = regionGraph.fkPMF θ
```

was not. That identity is proved here, together with the ambient common-upper
mass/conditional identities that a good-intersection comparison actually
consumes. Nothing about the nested-triple `hgood`, metric exploration transport,
DLR equations or infinite-volume limits is claimed.

## Verification

```sh
bash check.sh          # member-local: forbidden-token scan, lean -DwarningAsError=true, axiom report
```

* Toolchain: pinned Lean `v4.35.0` (`lean-toolchain` of `results/fk-qcritical`);
  `LEAN_PATH` = the project's built `.lake/build/lib/lean` plus its package builds.
* Default heartbeats: no `maxHeartbeats` override, no dependency or repo edit.
* `check.sh` output (`audit-output.txt`): **13 declarations reported**, each with
  exactly `[propext, Classical.choice, Quot.sound]`; zero warnings under
  `warningAsError=true`; the token scan finds no `sorry`, `admit`, `axiom`,
  `unsafe` or `native_decide`.

## Declarations

All in namespace `FK.RegionConfinement.PrefixContinuation`. Notation:
`I` = internal (region) edge labels, `W` = region vertices, `K` = outside
vertices, `k`/`a` = small-exterior/added label counts, `Gb` = the large ambient
graph `ambientOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo))`,
`P` = `Gb.fkPMF hq hp₁.le ζ`.

### 1. Support and the general prefix fibre sum

| Declaration | Statement |
|---|---|
| `prefixEvent_support_normalizedPMF` | the all-closed configuration carrying `ξS` lies in the prefix event and in the support of any positive finite normalized law |
| **`map_prefix_filter_normalizedPMF`** | for *any* positive finite weight `w` on `I ⊕ (Fin k ⊕ Fin a) → Bool`: `PMF.map (· ∘ Sum.inl) ((normalizedPMF w).filter (prefixEvent ξS)) = normalizedPMF (ω ↦ ∑ γ, w (glue ω (bigExterior ξS γ)))` |

The proof is an explicit `PMF.map_apply`/`PMF.filter_apply` computation in which
the ambient partition function cancels against the conditioning mass (the same
cancellation pattern as `FinitePlane.map_glue_conditionedPMF`, now with a second
sum over the added block; the fibre transfer is `tsum_prefix_fiber_fixed`).

### 2. The residual PMF identity (`docs/REGION-CONFINEMENT.md`)

| Declaration | Statement |
|---|---|
| **`prefix_filter_fkPMF_eq_region`** | under exactly the hypotheses of `ambientWeight_prefix_sum` (confinement `hconf`, matching `hθ`, separated small exterior bits `hsepS`, region-avoiding added labels `havoid`, interior parameters `0<q`, `0<p<1`): `PMF.map (· ∘ Sum.inl) ((Gb.fkPMF ζ).filter (prefixEvent ξS)) = (regionGraph si ti).fkPMF θ` |
| `prefix_filter_fkPMF_eq_region_twoSided` | the same for the project's standard `sumBoundary θ ζ` two-sided boundary, where confinement/matching are discharged internally |

Proof route: §1 with `w := Gb.fkWeight q p ζ`; then the fibre sums are
`c(γ)-weighted region weights` by `ambientWeight_prefix_sum`, and
`FinitePlane.normalizedPMF_map_eq_of_proportional` (`d = refl`, `c =` the
effective right-block weight) cancels the constant, giving
`normalizedPMF regionW = regionGraph.fkPMF θ` definitionally.

### 3. Pointwise and set-level factorization

| Declaration | Statement |
|---|---|
| `fkWeight_glue_prefix_eq` | `Gb.fkWeight q p ζ (glue ω (bigExterior ξS γ)) = edgeWeight p (1-p) (bigExterior ξS γ) * q ^ (components of rightConfinedGraph) * regionWeight ω` |
| `tsum_indicator_prefixEvent` | for **any** `F : (I ⊕ (Fin k ⊕ Fin a) → Bool) → ℝ≥0∞`: `∑ ρ, (prefixEvent ξS).indicator F ρ = ∑ (ω,γ), F (glue ω (bigExterior ξS γ))` |
| `prefixSet ξS A D` | the product event: prescribed small exterior bits, region bits in `A`, added bits in `D` |
| `addedWeight` | the effective added-block weight `edgeWeight · q ^ (rightConfinedGraph components)` |
| **`ambientWeight_set_factorization`** | for arbitrary `A ⊆ (I → Bool)`, `D ⊆ (Fin a → Bool)`: the ambient weight mass of `prefixSet ξS A D` is the product of the region weight mass of `A` and the added weight mass of `D` |

### 4. PMF-level common-upper identity

| Declaration | Statement |
|---|---|
| `fkPMF_mass_eq` | mass of any set under `Gb.fkPMF ζ` = ambient weight mass × inverse partition function |
| **`prefix_mass_factorization`** | `P(A region × prefix ξS × D added) = (regionGraph.fkPMF θ)(A) · P(prefix ξS ∧ D added)` |
| `prefix_mass_factorization_twoSided` | the same for the standard `sumBoundary` two-sided boundary |
| `map_filter_eq_of_mass_factorization` | general lemma: if `P`-masses of the traces `f ⁻¹' A ∩ T` factor as `c(A)` times the mass of `T`, then `(P.filter T).map f = c` |
| **`prefix_conditional_fkPMF_eq_region`** | conditioning `Gb.fkPMF ζ` on "small exterior bits `ξS` **and** added bits in `D`" (any `D` whose stratum has positive ambient mass) and reading off the region configuration gives exactly `(regionGraph si ti).fkPMF θ` |
| `prefix_conditional_fkPMF_eq_region_twoSided` | the same for the standard `sumBoundary θ ζ` two-sided boundary |

This is the mathematical content a common-upper good-intersection comparison
needs: **the region factor separates from the added-block stratum, and the
region law is the *same* region FK law for every stratum.** In the previous state
of the tree, the corresponding statement existed only for the right-extension /
vertex-fresh class (`pair_interior_continuation_rightExtended_twoSided`,
`fkNestedOrderedTriple_good_rightExtended_twoSided`); here it holds for an
arbitrary region setoid `θ` and an arbitrary region-confined boundary `ζ`, with
arbitrary exterior labels that may be incident with the (right summand of the)
small box.

## Hypotheses are not vacuous

* In-file witness (`section Nonvacuity`): region `Fin 2` with one internal edge
  `0–1`, outside block `Fin 2`, one small exterior label and one added label with
  endpoints in the outside block, `q = p = 1/2`, `θ = ζ = ⊥`, `ξS ≡ false`,
  `A = D = univ`; `prefix_mass_factorization_twoSided` applies.
* Independent exact rational computation (not part of the Lean audit) on the
  same geometry with `A = {internal edge open}`, `D = {added label open}`:
  both sides equal `4/21`, and the prefix-conditional region law is
  `(closed, open) = (1/3, 2/3)`, equal to the region FK law — consistent with the
  `2/3` free-region value recorded in `docs/REGION-CONFINEMENT.md`.

## What is *not* proved here (precise residuals)

1. **Triple-level `hgood`.** The identity used by
   `FK/NestedMetricRegionSplit.lean` (`NestedMetricGeometry.RegionSplit.Radial`,
   hypothesis `hgood`) is an equality of two `fkNestedOrderedTriple` marginals,
   `t.dist.toMeasure (first ⁻¹' B ∩ third ⁻¹' (restrictΔ e ⁻¹' C)) = t.dist.toMeasure
   (second ⁻¹' B ∩ third ⁻¹' (restrictΔ e ⁻¹' C))`. It is *not* derived here: that
   needs the ordered-triple/sequential gluing (`TripleCoupling`,
   `ExtendPair`-style extensions) on top of this file's ambient identities. What
   this file supplies is the region-factor separation and the equality of the
   region factor across strata, for the confined class.
2. **Metric exploration transport.** No claim that the metric-ball splits of
   `FK/MetricInterior.lean` or `FK/NestedMetricRegionSplit.lean` satisfy
   confinement; the confinement check for the standard conventions
   (`free`/`wired`/boundary-vertex `ConventionGeometry.partition` functions)
   remains unproved, exactly as recorded in `docs/REGION-CONFINEMENT.md`. The
   `twoSidedBoundary` specializations cover `sumBoundary`-shaped conventions
   (including free on both summands) but not arbitrary partitions.
3. **No DLR / infinite-volume / percolation conclusion.** The identities are
   finite-graph statements. No `FibreAssembly`, `HasOnePointConditionals`, DLR
   class, weak limit or `hgood`/`hD`/`hseq` input of `Theorem110Assembly` is
   claimed.
4. **No claim about the one-edge counterexample**; the confined hypothesis is
   used exactly as in `ConfinementNecessary` (non-confined boundaries are excluded
   and there the conclusion is false).

## Integration

Copy `PrefixContinuation.lean` to `results/fk-qcritical/FK/PrefixContinuation.lean`
(module `FK.PrefixContinuation`, namespace already
`FK.RegionConfinement.PrefixContinuation`; no new instances, no imports beyond
`FK.RegionConfinement`), then `lake build FK`. No release, dependency, toolchain
or heartbeat change is involved.
