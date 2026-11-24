# Direction 1 — generalized free-region continuation: confinement, not freshness

Two Lean modules, pinned Lean 4.35.0, project imports, default heartbeats, no
`sorry`/`admit`/`axiom`/`unsafe`:

* `lean/RegionConfinement.lean` (module `FK.RegionConfinement`)
* `lean/ConfinementNecessary.lean` (same namespace; imports
  `FK.NestedCommonUpperGood`, `FK.PlanarForestDuality`)
* `lean/MetricInterior.lean` (same namespace; imports `FK.MetricRegionGood`)

All 32 audited declarations report exactly
`[propext, Classical.choice, Quot.sound]`; four are definitions and report no
axioms at all. `lean/Audit.lean` reproduces the audit.

## What the shell obstruction really means

`FK/MetricRegionGood.lean` proves `newEdge_avoids_region` (every complementary
large-box edge misses the open region) and `newEdge_fresh_of_shell` (the
distinct extra hypothesis under which the accepted right-extension `hgood`
applies), and shows on the semi-infinite line that the extra hypothesis fails on
ordinary metric boxes. The conclusion recorded in
`docs/NESTED-METRIC-REGION-GOOD.md` was that a *generalized free-region
continuation* is needed.

The results here show that the freshness condition is **not** what matters.
What matters is that the boundary setoid be *confined*: no block may contain a
region vertex together with a vertex outside the region.

Concretely, let `U` be the region vertex type, `K` the rest, and

```text
G_big  = ambientOfSum (splitSource si so) (splitTarget ti xo)
```

with internal labels `I` (both endpoints in the region, automatically, by
`splitSource`), arbitrary exterior labels `O`, arbitrary region setoid `θ`, and
a boundary `ζ : Setoid (U ⊕ K)` with

```text
confined   : ζ.r (Sum.inl c) y → ∃ c' : U, y = Sum.inl c'
matches θ  : ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c'
```

`sumBoundary θ ζ'` and `twoSidedBoundary θ ζ'` are instances. Exterior labels may
be *any* labels, in particular labels whose endpoints meet the right summand —
the shell-touching situation — and they may go to fresh vertices: fresh vertices
are simply part of `K`.

Proved (all with `0 < q`, `0 < p < 1` where probabilities appear):

| Declaration | Statement |
|---|---|
| `boundary_confined_reachable` | if every open exterior edge avoids the region, fixed-graph reachability between two region vertices is exactly `θ` |
| `fixedGraph_reachable_inRegion` | a fixed-graph path starting at a region vertex never leaves the region |
| `interiorGraph_confined_eq_sum` | the induced interior graph is `(regionGraph θ ω) ⊕g rightConfinedGraph`; `rightConfinedGraph` is the induced right block |
| `componentCount_split_confined` | component counts split with a fixed right contribution |
| `interiorWeight_confined_eq` | weight-level factorization by `q ^ (right components)` |
| `interior_fkPMF_eq_region_confined` | the induced interior FK law at a separated exterior configuration **is** the actual region FK law `regionGraph.fkPMF θ` |
| `filter_ambient_fkPMF_eq_map_glue_region_confined` | the whole graph's FK law conditioned on a separated exterior configuration pushes the region FK law forward |

This removes the fresh-vertex-summand restriction of
`fkNestedOrderedTriple_good_rightExtended_twoSided` and the free-boundary
restriction of `FreeInterior.interior_fkPMF_eq_region_free`; the region setoid
`θ` is arbitrary.

### Prefix form (the input the good-intersection assembly consumes)

Split the exterior labels as `Fin k ⊕ Fin a` — the small box's labels and the
added labels — and let `ξS : Fin k → Bool` be the small exterior configuration,
with the added labels avoided by the region. Then:

| Declaration | Statement |
|---|---|
| `prefixEvent`, `bigExterior`, `bigSo`, `bigXo` | the prefix event and the combined exterior maps |
| `eq_glue_of_mem_prefixEvent`, `prefixEquiv`, `prefixFiberEquiv` | the prefix event is a product of a region configuration and an added configuration; each fibre is the added configurations |
| `tsum_prefix_fiber`, `tsum_prefix_fiber_fixed` | sums over the prefix event, resp. one fibre of it, are sums over the added configurations |
| `separated_bigExterior` | separatedness of the small bits plus region-avoidance of the added labels gives separatedness of the whole exterior configuration |
| **`ambientWeight_prefix_sum`** | summing the large graph's FK weights at a fixed region configuration over **all** added configurations gives a constant — the effective right-block weight `∑_γ edgeWeight ξ_γ · q^{c_γ}` — times the region FK weight at `θ` |
| `prefixEvent_support` | the prefix event meets the support, so the conditional law exists |

### Exact residual

`ambientWeight_prefix_sum` is the weight-level content of the prefix
continuation. Turning it into the PMF statement

```text
PMF.map (fun ρ => ρ ∘ Sum.inl) ((G_big.fkPMF ζ).filter (prefixEvent ξS)) = regionGraph.fkPMF θ
```

is routine normalization (divide the fibre sums by their total; the constant
cancels). I did not finish that step here: the remaining work is Lean
plumbing of `PMF.filter_apply`/`PMF.map_apply` over the ambient graph term, not
mathematics. No statement in this file should be read as that PMF identity.

## Coordinator verification boundary

The formal `ConfinementNecessary` file proves non-confinement, universality of the effective boundary and the induced region boundary's disagreement with the discrete region boundary, together with exact component counts. Its separate rational computation was also rerun independently: at $p=q=1/2$ it gives induced region-edge probability $1/2$ and free-region probability $2/3$. That calculation is an exact supporting computation, **not** another audited Lean theorem. The standard-convention confinement check remains unproved; it must not be assumed merely because strict metric nesting removes boundary-incident edges.

## The confinement hypothesis is not removable

`lean/ConfinementNecessary.lean` builds the smallest obstruction: region
`{r0, r1}`, outside `{k0, k1}`, one region-internal edge `r0–r1`, one exterior
edge `k0–k1` (open, so the separated/maximal-stratum hypothesis holds), and the
boundary `crossWiring` that wires `ri` to `ki`.

Proved in Lean:

* `crossWiring_not_confined` — this boundary violates confinement;
* `cBd_universal` — the induced boundary of the open exterior fibre is
  universal, hence `cG_componentCount`: the interior graph has **one** component
  in every configuration;
* `induced_region_boundary_not_free` — the induced boundary relates the two
  region vertices although the region setoid is discrete.

The numerical failure was computed exactly (rational arithmetic, `Fraction`,
`verify_counterexample.py`, output below) using the library's own weight
formula `p^{#open} (1−p)^{#closed} q^{#components}`:

```text
induced interior weights: 1/4 1/4 Z = 1/2
induced P(e0 open | open exterior fibre) = 1/2
region weights: 1/4 1/8 Z = 3/8
region P(e0 open) = 2/3
weight ratio induced/region at open : closed = 1 2
```

so the induced interior law gives the region edge probability `1/2` where the
free region FK law gives `2/3`: the two weights are not proportional, and no
normalization can repair it.

**Consequence.** The residual obligation recorded in `docs/PROOF-STATUS.md`
item 3 — matching ordinary larger nested metric boxes *and arbitrary boundary
laws* to the compatible-cross class — cannot be discharged as stated. The
boundary class must be restricted.

`lean/MetricInterior.lean` supplies the geometry that makes the standard
conventions confined:

* `edge_mem_metricBox_of_dist_lt` — every global edge incident with a vertex at
  distance `< N` is an edge of the radius-`N` metric box;
* `not_exists_edge_outside_of_dist_lt` — so such a vertex has no incident edge
  outside the box: the box boundary, read as vertices with an edge leaving it,
  misses `innerBall hG o N`;
* `innerBall_subset_innerBall` — the region `innerBall R` consists of box
  vertices whenever `R ≤ N + 1`.

Hence, when `R ≤ r < N`, a region vertex has no edge leaving either box, so any
boundary convention whose partition wires only vertices that either have an edge
leaving the box or are joined through the (open) outside cannot put a region
vertex in a block with a non-region vertex — the free, wired and
boundary-vertex conventions all have that shape.  What is *not* formalized here
is the final step, that `ConventionGeometry`'s `partition` functions have
exactly that shape.

## Not proved here

* the prefix PMF identity above (only its weight-level core);
* the convention check that the standard boundary conventions are confined;
* any `hgood`, `hD`, `hseq` or infinite-volume conclusion; nothing here is a
  paper theorem.

## Build

```sh
R=<repo>/results/fk-qcritical
TC=/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0
LEAN_PATH=$R/.lake/build/lib/lean:$(ls -d $R/.lake/packages/*/.lake/build/lib/lean | tr '\n' ':'):$TC/lib/lean
$TC/bin/lean lean/RegionConfinement.lean        # 2.8 s
$TC/bin/lean lean/ConfinementNecessary.lean     # 2.5 s
$TC/bin/lean lean/MetricInterior.lean           # 2.2 s
$TC/bin/lean -o build/RegionConfinement.olean lean/RegionConfinement.lean
$TC/bin/lean -o build/ConfinementNecessary.olean lean/ConfinementNecessary.lean
$TC/bin/lean -o build/MetricInterior.olean lean/MetricInterior.lean
LEAN_PATH=build:$LEAN_PATH $TC/bin/lean lean/Audit.lean   # 32 declarations
python3 verify_counterexample.py
```

## Integration

`lean/RegionConfinement.lean` only needs `FK.NestedCommonUpperGood`;
`lean/ConfinementNecessary.lean` needs `FK.NestedCommonUpperGood` and
`FK.PlanarForestDuality`; `lean/MetricInterior.lean` needs
`FK.MetricRegionGood`. Copy as `results/fk-qcritical/FK/RegionConfinement.lean`,
`FK/ConfinementNecessary.lean`, `FK/MetricInterior.lean` and `lake build FK`.
`RegionConfinement` deliberately reuses the project's `InRegion`-style
definitions from its own namespace and introduces no new axioms or instances.
