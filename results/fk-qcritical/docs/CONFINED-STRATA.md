All three sources were independently rebuilt with `-DwarningAsError=true` on Lean 4.35, and 34 principal audits passed. This supplies arbitrary separated exterior strata rather than just product strata, plus conditional-region independence at two scales. Part 2 proves that factorization fails at exact weights $1/8$ versus $1/16$, and Part 3 derives conditional-region inequality. No ordered-triple or metric `hgood` is inferred.

# Direction 4 — confined prefix strata and the common-upper good identity

Member `m3`, swarm `smwu4rrf3`. Three source files, all Lean 4.35, no `sorry`,
no custom axiom, no `unsafe`, no `native_decide`, default heartbeats, only
`propext`, `Classical.choice`, `Quot.sound` (34 declarations audited).

```
src/ConfinedStrata.lean             -- Part 1: general stratification identities
src/ConfinedStrataObstruction.lean  -- Part 2: exact finite obstruction
src/ConditionalLaw.lean             -- Part 3: conditional law is not stratum-independent
src/Audit.lean                      -- consolidated #print axioms
```

Build (member-local; no repository edit):

```sh
P=results/fk-qcritical   # project root of the public repo
LP=$P/.lake/build/lib/lean
for p in $P/.lake/packages/*; do [ -d "$p/.lake/build/lib/lean" ] && LP="$LP:$p/.lake/build/lib/lean"; done
LP="$LP:.ultramath/smwu4rrf3/m3/src"
for f in ConfinedStrata ConfinedStrataObstruction ConditionalLaw Audit; do
  LEAN_PATH=$LP ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean \
    -DwarningAsError=true -o .ultramath/smwu4rrf3/m3/src/$f.olean \
    .ultramath/smwu4rrf3/m3/src/$f.lean
done
```

---

## What was asked and what was delivered

Direction 4 offered two acceptable outcomes: (a) lift `PrefixContinuation` to
the actual `fkNestedOrderedTriple`, proving the first/third versus second/third
good-intersection comparison while checking two nested `α < β` with confinement
throughout; or (b) exhibit an exact finite obstruction. This delivery is a
substantial part of (a) *plus* a complete (b), together with a proof that the
hypothesis (a) needs is not removable.

### Part 1 — the factor identity on arbitrary strata (`ConfinedStrata.lean`)

`FK/PrefixContinuation.lean` proves the common-upper identity only for strata of
the product form `A × {ξS} × D`. The triple good-intersection comparison
constrains the *third* coordinate by a stratum event, which is not such a
product. Two points are new here.

Restricted-stratum statement, proved:

* `fkWeight_glue_stratum` — at *any* exterior configuration `e`, the ambient FK
  weight factors as `extWeight e * regionWeight ω`, provided `e` is pointwise
  separated (`ExtSep`: every **open** small-exterior label avoids the region, and
  the added labels avoid it). This refines `fkWeight_glue_prefix_eq`.
* `stratum_weight_factorization` — the weight mass of
  `(region ∈ A) × (exterior ∈ E)` is `regionW(A) * extW(E)` for an **arbitrary**
  separated stratum `E`.
* `stratum_mass_factorization` — the same identity at the level of the actual
  FK law.
* `stratum_conditional_region_eq_region` — conditioning the ambient FK law on
  any separated stratum `E` and reading the region gives exactly
  `regionGraph.fkPMF θ`.
* `nested_strata_conditional_eq` — two nested admissible strata give the *same*
  conditional region law. This is the two-scale (α, β) check: enlarging the
  exterior box does not move the region factor.
* `prefixSet_eq_regionMask_inter_extMask` — the old product strata are the
  special case `E = bigExterior ξS '' D`, so the generalization is strict.

### Part 2 — the restriction cannot be dropped (`ConfinedStrataObstruction.lean`)

Explicit geometry: `W = Fin 2`, `K = Fin 0`, one interior edge `0 -- 1`, and one
exterior label **also** from `0` to `1`. Both boundary setoids are free. Then
`hconf`, `hθ` and region-avoidance of the added block all hold (proved:
`oConf`, `oTh_iff`, `oAdded`), but pointwise separation fails (`oE_not_sep`).

Exact weights at `q = p = 1/2`:

| quantity | value |
|---|---|
| `regionWeight (edge open)` | `1/4` (`oRegionW_open`) |
| `regionWeight (edge closed)` | `1/8` (`oRegionW_closed`) |
| ambient weight, both labels open | `1/8` (`oAmb_w_open`) |
| ambient weight, only exterior open | `1/8` (`oAmb_w_closed`) |
| effective exterior weight | `1/2` (`oExtWeight`) |

with both ambient component counts proved to be `1` (`oAmb_comp_one`). Hence

`oAmb.fkWeight (glue closed e) = 1/8` but
`extWeight e * regionWeight closed = 1/2 * 1/8 = 1/16`:

`fkWeight_glue_stratum_fails`. So `ExtSep` (the source `hsepS`) is a real
restriction and cannot be replaced by `hconf` alone.

### Part 3 — the conditional law is genuinely different (`ConditionalLaw.lean`)

`mass_eq_of_map_filter_eq` proves the *necessary* direction of
`map_filter_eq_of_mass_factorization`: if conditioning on `T` and pushing along
`f` gives `c`, then the `P`-mass of `f ⁻¹' A ∩ T` is `c A` times the `P`-mass of
`T`. Combined with the exact sums `oAmbSum_ext = 1/4`, `oAmbSum_AE = 1/8`,
`oRegionSum = 3/8`, `oRegionASum = 1/4` (from the four-configuration sum
`sum_amb`), the stratum identity would force

`(1/4) * (1/4) = (1/8) * (3/8)`, i.e. `1/16 = 3/64`.

Therefore `conditional_region_ne_region`:

```
((oAmbFK).filter (exterior-open stratum)).map (region projection) ≠ oRegFK
```

— on this stratum the conditional region law is **not**
`regionGraph.fkPMF θ`, although every other hypothesis of
`stratum_conditional_region_eq_region` holds. (Numerically the conditional edge
probability is `1/2`, the region FK value `2/3`; this is a reading of the same
numbers, not a separate Lean theorem.)

---

## Consequence for the nested-triple programme

A `hgood` comparison built on the confined class must constrain the
third-coordinate stratum to configurations whose **open** exterior labels avoid
the region. This is exactly the source `hsepS`, and Part 3 shows it is necessary,
not bookkeeping. In particular the right-extended class of
`FK/NestedCommonUpperGood.lean` (where `ExteriorHasRight` makes the condition
automatic) is *not* the same as the confined class, and the confined class alone
does not give `hgood` on the full maximal stratum.

## What is *not* proved here (exact residuals)

1. **No `fkNestedOrderedTriple` lift.** The triple-level equality
   `t.dist.toMeasure (first⁻¹ B ∩ third⁻¹ C) = t.dist.toMeasure (second⁻¹ B ∩ third⁻¹ C)`
   on the confined class is *not* constructed. The graph shape of
   `FK.NestedFiniteCoupling.fkNestedOrderedTriple` (large graph = disjoint sum of
   the smaller graph with `GO`) does not match the confined split (large graph =
   region edges plus boundary labels, whose FK weight factorizes only after
   marginalizing the exterior). A confined triple and its pair-continuation
   lemmas would have to be built from scratch; Part 1 supplies the region-factor
   separation and the stratum-independence of that factor, which is the input
   such a construction consumes.
2. **No metric confinement.** Nothing here proves that the metric-ball splits of
   `FK/NestedMetricRegionSplit.lean` satisfy `hconf`/`hθ`; that remains exactly
   as recorded in `docs/REGION-CONFINEMENT.md`.
3. **No DLR, no infinite-volume, no percolation conclusion.** Every statement is
   about actual finite normalized FK laws.
4. **Part 3 is one geometry at `q = p = 1/2`.** It is an obstruction, not a
   classification of when the conditional region law differs.

## Axiom audit

`src/Audit.lean` prints `#print axioms` for 34 declarations; 33 report exactly
`[propext, Classical.choice, Quot.sound]` and `oAdded` reports no axioms. `grep` over the three source
files finds no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or
`maxHeartbeats`. All three files also build under
`-DwarningAsError=true`.

## Integration

Copy the three files into `results/fk-qcritical/FK/` as
`ConfinedStrata.lean`, `ConfinedStrataObstruction.lean`, `ConditionalLaw.lean`
(modules `FK.ConfinedStrata`, `FK.ConfinedStrataObstruction`,
`FK.ConditionalLaw`; the namespace is already
`FK.RegionConfinement.ConfinedStrata` and imports are `FK.PrefixContinuation`
and `FK.ConfinementNecessary`), then `lake build FK`. No dependency, toolchain
or heartbeat change is involved.
