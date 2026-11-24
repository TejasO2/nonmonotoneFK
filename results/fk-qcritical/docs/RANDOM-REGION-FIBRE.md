Public modules preserve the exact verified statements and standard axioms (40 principal audits). The all-finite-box DLR hypothesis for the stratum identity and the single frozen-box hypothesis for the frontier product are intentional. Extending either to a random reverse-martingale limit or to DLR only along a specified exhaustion is not covered. The positive factorization always cuts its interior law to the forced interior connection event.

# Random-region DLR fibre identity (direction 2)

Member `m8`, swarm `smwu4rrf3`. Direction 2 of the brief: *"using
`RandomClosedBoundary`, `RegionFiniteBox`, exact DLR and random measurable
strata, prove a genuine random-region conditional-kernel equality of
infinite-body FK law with finite free FK interior … handle strata/exterior split
and index dependence … if global DLR or a weaker law is needed, correct and state
it."*

Everything below is compiled and axiom-audited in this directory against the
repo's pinned Lean `4.35.0` and the pinned Mathlib checkout. Nothing outside this
directory was modified; no `sorry`, `admit`, custom axiom, `unsafe`,
`native_decide`, or heartbeat override is used.

## Files

| File | Content |
|---|---|
| `FiniteVolumeDLR.lean` | the actual finite-volume FK law is DLR at its own box (the hypothesis class is inhabited) |
| `RegionStrata.lean` | interior extension of a box configuration; open walks inside a closed region stay in the interior box; the exact stratum factorisation |
| `RegionFibre.lean` | measurability of `extendExterior`, `extendInterior`, the two stratum factors, and of the **actual** exterior-induced boundary partition `exteriorPartition` |
| `RegionFibreIdentity.lean` | the conditioning computation, the free-kernel identity, the product/rectangle/conditional forms, the law-independence of the kernel |
| `RegionFibreCounterexample.lean` | exact obstruction showing the free-measure correction is necessary |

Build and audit:

```bash
./check.sh        # ~13 s cold: rebuilds all four modules, greps forbidden constructs,
                  # runs #print axioms on 40 declarations and checks the axiom sets
```

The script uses `LEAN=/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`
and `LEAN_PATH="$(cat /workspace/nucleus/work/home/.fk_lean_path):$PWD/.scratch/lib"`.
Oleans go to `.scratch/lib` only so that later files can import earlier ones; to
integrate, place the four modules under `FK/` and prefix imports with `FK.`.

## Axiom audit

40 declarations are audited by `#print axioms` (1 in `FiniteVolumeDLR.lean`, 14 in
`RegionStrata.lean`, 7 in `RegionFibre.lean`, 13 in `RegionFibreIdentity.lean`,
5 in `RegionFibreCounterexample.lean`). Every one depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## Setting and conventions

* `G : SimpleGraph V` with `[G.LocallyFinite]`, `[Countable V]`, configurations
  `ω : G.edgeSet → Bool`, open connection the repo's
  `CurvatureVariance.Infra.Percolation.OpenConnected`.
* `region G ω T = ClosedRegion (openSubgraph G ω) T` — the paper's `S(ω)` for the
  base `T` (the repo's random closed region, `FK.RandomClosedBoundary`).
* `regionBox R hR : FK.InfiniteVolume.FiniteBox G.edgeSet` — vertex type `↥R`,
  edge labels `interiorEdgeSet G R`, chosen orientation. Its `Exterior` is
  `{e : G.edgeSet // e ∉ box.edges} → Bool`, its `Interior` is `box.edges → Bool`.
* `exteriorPartition R hR : Exterior → Setoid ↥R` — the boundary partition induced
  by the *actual open walks* of the exterior configuration
  (`FK.RandomClosedBoundary.exteriorPartition`).
* `IsDLR`, `fkKernel`, `exteriorMeasure`, `conditionalLaw`,
  `measure_eq_map_glue_compProd` — `FK.InfiniteVolume.FiniteBox`.

## Closed gap: `exteriorPartition` was not known measurable

`FK/RegionFiniteBox.lean` defines `exteriorPartition` but proves nothing about its
measurability, and `FiniteBox.IsDLR` requires `Measurable α`. Consequently
`fkKernel` could never be instantiated with the *actual* boundary condition of the
region box, which is exactly what residual (R1) of
`docs/RANDOM-CLOSED-BOUNDARY.md` needs.

`measurable_exteriorPartition` closes this. The route is:
`extendExterior` is measurable (each coordinate is either the constant `false` or a
projection); the fibre
`{η | exteriorPartition η = α}` equals
`⋂ x ⋂ y, {η | OpenConnected G (extendExterior η) (nonInteriorEdges R) x y ↔ α.r x y}`,
which is measurable by `measurableSet_openConnected`; the range of
`exteriorPartition` is countable because `Setoid ↥R` is finite, so preimages of
arbitrary sets are countable unions of fibres.

## The stratum factorisation

`frontierSet R hR η` (exterior condition):
`∀ e, (∃ x ∈ e, x ∈ R) → (∃ x ∈ e, x ∉ R) → extendExterior η e = false`,
i.e. the paper's `ω|∂R = 0`.

`interiorConnects R hR T i` (interior condition):
`∀ x ∈ R, ∃ t ∈ T, OpenConnected G (extendInterior i) (interiorEdgeSet G R) x t`,
i.e. every vertex of the region is open-connected to the base *inside* the region.

**`region_eq_iff` / `glue_preimage_region_eq`.** For `T ⊆ R` and
`z : Exterior × Interior`,

```
region G (glue z) T = R  ↔  frontierSet R hR z.1 ∧ interiorConnects R hR T z.2
```

so under `splitEquiv` the stratum of the random closed region is a genuine
**measurable rectangle**. The proof of `⇒` uses `frontier_closed` plus the new
walk lemma `isOpenIn_interiorEdgeSet` (an open walk between two vertices of a
closed-boundary region crosses only interior edges); the proof of `⇐` uses
`region_minimal` and `subset_region`.

## The fibre identity

`compProd_inter_prod`: if a kernel `κ` equals `ρ` on a measurable set `F`, then
`(μ ⊗ₘ κ)(S ∩ F ×ˢ I) = ((μ|F) ⊗ₘ const(ρ|I)) S`. This is the whole
conditional-independence computation; it is independent of the FK model.

`fkKernel_eq_free_of_frontierSet`: on `frontierSet`, the DLR kernel at the region
box **is** `fkMeasure freeBoundary` (via `exteriorPartition_eq_bot` and
`freeBoundary_eq_bot`).

**`map_splitEquiv_restrict_region_eq_prod` (main theorem).** Let `q > 0`,
`p ≤ 1`, `[Countable V]`, and let `μ` satisfy the DLR equations at the box of
**every finite region** `R` with the actual partition `exteriorPartition R hR`.
Then for every finite `R` and every base `T ⊆ R`,

```
map splitEquiv (μ ↾ {ω | region G ω T = R})
  = (extμ ↾ frontierExterior) .prod (freeFK ↾ interiorConnectSet)
```

Equivalently (`region_stratum_rect`), for measurable `U ⊆ Exterior`,
`W ⊆ Interior`:

```
μ({region = R} ∩ {ext ∈ U} ∩ {int ∈ W})
  = extμ(U ∩ frontierExterior) · freeFK(W ∩ interiorConnectSet)
```

So on the stratum: exterior and interior are **independent**; the exterior is the
exterior marginal restricted to the frontier-closed configurations; the interior
is the **free** finite-volume FK measure restricted to the interior connection
event. In particular `μ{region = R} = extμ(frontierExterior) · freeFK(I)`.

**`map_splitEquiv_restrict_frontierSet_prod` (the paper's step, unconditional).**
The free-interior statement needs DLR at *one* box only, and does **not** condition
on the region:

```
map splitEquiv (μ ↾ {frontier closed at R})
  = (extμ ↾ frontierExterior) .prod freeFK
```

i.e. conditionally on the exterior being frontier-closed at `R`, the interior is
the free FK measure and independent of the exterior. This is exactly
`ω|∂R = 0 ⇒ the interior law is the free random-cluster measure`, at the level of
the infinite-body law rather than the finite specification
(`interiorFKMeasure_eq_free` only proved the latter).

**Kernel independence of the law.** `region_stratum_cond` and
`region_stratum_kernel_independent` record that the conditional interior kernel on
the random-region stratum is the *same function* for every law in the class: for
two such `μ₁, μ₂` and any measurable `U`, `W`,

```
μ₁(stratum ∩ U × W) · μ₂(stratum ∩ U × univ)
  = μ₂(stratum ∩ U × W) · μ₁(stratum ∩ U × univ)
```

and, when `freeFK(I) ≠ 0`, the conditional probability is
`freeFK(W ∩ I) / freeFK(I)` — no dependence on `μ` or on `U`. `region_stratum_rect_stage`
is the index-`n` instance with base `base n`.

## Necessity of the correction (exact obstruction)

The source phrase "the conditional law in `S_n(ω)` is the free FK measure" cannot
be read as *"conditioning on the value of the random region, the interior is
free FK"*. Conditioning on the stratum also forces the interior connection event
`I`, and `I ≠ univ` as soon as `R` has a vertex outside the base.

`free_stratum_naive_false`: let `q > 0`, `0 < p < 1`, `T` nonempty, `x ∈ R`,
`x ∉ T`, and let `U` be a measurable exterior event with strictly positive
stratum exterior mass. Then

```
μ({region = R} ∩ {ext ∈ U} ∩ {int = allClosed}) = 0
      but     extμ(U ∩ frontierExterior) · freeFK{allClosed} ≠ 0
```

because `allClosed ∈ I` fails (`not_interiorConnects_allClosedInterior`: a
nondegenerate open walk needs an open edge) while `freeFK{allClosed} > 0` for
interior parameters (`regionFreeMeasure_allClosedInterior_ne_zero`, from
`fkWeight_pos` and `partitionFunction_pos`). So the free FK measure is exactly
right, but the stratum itself is the free measure **cut down to `I`**; the version
without the cut-down is false.

## The hypothesis class is inhabited

`FK.InfiniteVolume.finiteVolumeLaw_isDLR`: for every finite box `B` and every
constant boundary partition `α`, the genuine finite-volume FK law
`B.finiteVolumeLaw hq hp α` satisfies `B.IsDLR hq hp (fun _ => α) measurable_const`.
So the box-level DLR class used by the fibre identity contains the actual
finite-volume source laws of the model (the reflexive case of the DLR equation),
and no positivity or interior-parameter assumption is needed. The proof computes
`map splitEquiv (finiteVolumeLaw) = dirac(closedExterior) .prod ν` with
`ν = fkMeasure α` and substitutes the constant kernel.

## Feeding the ordered-triple step

`frontierSet_restrictExterior_of_le`: if `ω ≤ ω'` then the exterior restriction of
`ω` at the region `region G ω' T` of `ω'` satisfies `frontierSet`. Proof:
`region_closedBoundary_of_le` gives the closed boundary for `ω`, and
`frontier_closed` turns it into the labelled statement. This is the exact
labelled input `ωᵢ|∂S_n(ω₃) = 0` that
`map_splitEquiv_restrict_frontierSet_prod` consumes, for each dominated
coordinate. Passing from the single-coordinate statement to a joint statement
along a random exhaustion is *not* done here (it needs one joint null set and the
changing-region conditional limit, i.e. the ordered-triple direction).

## Precise remaining hypotheses

1. **Global DLR.** The random-region theorem assumes `μ` satisfies `IsDLR` at the
   box of *every* finite region `R`, with the actual partition
   `exteriorPartition R hR`. This is the standard "Gibbs at all finite boxes"
   condition; it is strictly stronger than `μ ∈ DLRMeasures exh Φ` for one fixed
   exhaustion, because the random region `region G ω (base n)` is in general not a
   box of the exhaustion. The unconditional frontier statement
   (`map_splitEquiv_restrict_frontierSet_prod`) needs only the **single** box `R`.
   Bridging "DLR at the exhaustion's boxes" to "DLR at the random region's box" is
   the ordered-triple/limit work of the other directions and is **not** done here.
2. **No limiting argument.** `μ` is an arbitrary probability measure satisfying the
   DLR equations; no FK weak-limit class (`IsFKLimit`, `FKLimitMeasures`) is
   instantiated, and no convergence, tightness, or no-mass-escape statement is
   claimed.
3. **No Theorem 5.1 conclusion.** Uniqueness of the Gibbs measure, the reverse
   martingale along the random exhaustion, and the ordered-triple comparison are
   not touched; only the fibre identity those steps consume is proved.
4. **Interior parameters.** The counterexample uses `0 < p < 1` (interior edge
   weights), as in the paper. The main fibre identity itself holds for all
   `0 < q`, `p ≤ 1`, including the degenerate endpoints.
5. **Base family.** `T` is an arbitrary base set with `T ⊆ R`; no connectedness,
   finiteness or monotonicity of `T` (or of `R`) is assumed beyond `R.Finite`,
   which is what `regionBox` requires. `region_stratum_rect_stage` records the
   index dependence for a base family `base : ℕ → Set V`.
