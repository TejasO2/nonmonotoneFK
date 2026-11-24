# Random closed-boundary exhaustion: measurability, free boundary, finite box

Public modules: `FK.RandomClosedBoundary`, `FK.RegionEdgeBox`, and `FK.RegionFiniteBox`, import-renamed only during release integration. All 39 principal audit lines were independently validated. The source-faithful gain is specifically the random-region **measurability** request: it is genuinely built from the configuration and base family, not declared by choosing an exhaustion.


Member `m4`, swarm `smwu0pw30`. Direction: **2 — random closed-boundary
exhaustion for a non-percolating configuration** (Theorem 5.1 of
arXiv:2512.16486).

This note records exactly what is proved, where, how to check it, and what is
still missing. All claims below were compiled and axiom-audited in this
directory; nothing outside my directory was modified.

## Files, imports, build

| File | Imports | Content |
|---|---|---|
| `RandomClosedBoundary.lean` | `FK.StrongUniqueness`, `FK.ExplorationGeometry`, `FK.InfiniteVolume`, `FK.ClosedBoundaryEventually` | random region, exhaustion constructor, measurability, a.e. package, strata, free-boundary setoid, stacking identities |
| `RegionEdgeBox.lean` | `RandomClosedBoundary`, `FK.NonlocalGeometry` | labelled interior edge box, frontier closed, finiteness, `freeBoundary = ⊥` |
| `RegionFiniteBox.lean` | `RegionEdgeBox` | vertex re-indexing to a `FK.InfiniteVolume.FiniteBox`, exterior-induced partition, **free interior FK law** |

Check everything with

```bash
./check.sh              # ~7.3 s warm, 3 Lean invocations, default heartbeats
```

which runs, from this directory, with
`LEAN=/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`
and `BASE=$(cat /workspace/nucleus/work/home/.fk_lean_path)`:

```bash
export LEAN_PATH="$BASE:$(pwd)/.scratch/lib"
$LEAN -o .scratch/lib/RandomClosedBoundary.olean RandomClosedBoundary.lean   # ~3.0 s
$LEAN -o .scratch/lib/RegionEdgeBox.olean RegionEdgeBox.lean                 # ~2.4 s
$LEAN -o .scratch/lib/RegionFiniteBox.olean RegionFiniteBox.lean             # ~2.9 s
```

The three `olean`s exist only so that the later files can import the earlier
ones; they are build artifacts of my directory.  To integrate into the package,
place the three modules under `FK/` and rewrite `import RandomClosedBoundary` to
`import FK.RandomClosedBoundary`, etc.

## Axiom audit

39 declarations are audited by `#print axioms` at the end of each file. Every
one depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`,
`admit`, custom axiom, `unsafe`, heartbeat override or dependency change.

## What is proved

Throughout `G : SimpleGraph V`, configurations are `ω : G.edgeSet → Bool`, and
open connection is the repo's `CurvatureVariance.Infra.Percolation.OpenConnected`.
`openSubgraph G ω = openGraph G (openSet ω)`.

1. **The region is the paper's `S(ω)`.**
   `region G ω T = ClosedRegion (openSubgraph G ω) T`, i.e. the union of the
   open clusters based at `T`; `mem_region_iff` states it as open connection to
   a base vertex.  It is minimal among sets containing `T` whose outgoing
   ambient edges are closed (`region_minimal`), finite when clusters are finite
   (`region_finite`), and connected when `T` is (`region_connected`).
2. **An explicit exhaustion, not a chosen one.**
   `closedBoundaryExhaustionOfRegion` builds a `FK.ClosedBoundaryExhaustion`
   from any cofinal family of finite connected bases; its `region n` is
   definitionally `region G ω (base n)` (`..._region`).  This is what makes the
   map `ω ↦ S_n(ω)` measurable below: no `Classical.choice` of an exhaustion
   intervenes.
3. **Measurability** (`[Countable V]`): `measurableSet_mem_region`,
   `measurableSet_region_subset`, `measurableSet_region_eq` (every stratum
   `{ω | region G ω T = S}`), and
   `measurable_region : Measurable (fun ω ↦ region G ω T)` into the measurable
   space of subsets.  This closes residual (R1.2) of
   `docs/THEOREM110-ASSEMBLY.md` ("no measurability of the closed-boundary
   exhaustion in `ω`").
4. **Almost-sure exhaustion package.**  `ae_exhaustion`: for a probability
   measure charging only `FK.NonPercolating G`, almost surely every stage is
   finite, connected, closed-boundary, the sequence is monotone and exhaustive —
   all from one null set.  `ae_eventually_contains_family`: for countably many
   fixed finite test vertex sets `W k`, almost surely each is contained in all
   sufficiently late regions (deterministic in `ω`, so no extra null set).
   `exists_edges_inside`: for a fixed finite edge set, all its endpoints are
   eventually inside the region — the "eventual containment of every edge".
   `measure_eq_tsum_finset` + `ae_region_finset`: the law of the random region
   is supported on countable (finite) regions and decomposes any measurable
   event into the strata `A ∩ {region = s}`; `region_subset_eq_iUnion_stratum`
   is the corresponding finite-stack set identity.
5. **The boundary step of the paper** ("`ω|∂S = 0` makes the boundary partition
   free").  `nonInteriorEdges S` is the set of ambient pairs with an endpoint
   outside `S`; this is exactly the complement of the box's interior labels.
   * `eq_of_isOpenIn_nonInterior`: an open walk inside non-interior edges
     joining two vertices of `S` is trivial.
   * `exteriorOpenSetoid_eq_bot`: if `S` has closed boundary in `ω`, then the
     setoid of exterior-open connections between vertices of `S` is `⊥`.
   * `freeBoundary_eq_bot`: the finite FK model's free boundary partition *is*
     `⊥`.  Hence `exteriorOpenSetoid_eq_bot` says exactly that a
     closed-boundary region induces the free finite-volume FK law.
   * `frontier_closed`: the literal labelled statement — every labelled edge
     incident with `R` but not interior to `R` is closed in `ω`.
6. **The exhaustion chosen from the dominating configuration.**
   `region_closedBoundary_of_le`: if `ω ≤ ω'` then the region built from `ω'`
   has closed boundary for `ω`.  `exteriorOpenSetoid_upperRegion_eq_bot` and
   `ae_upper_region_closed_for_lower`: almost surely in an ordered triple
   coupling `ω₁, ω₂ ≤ ω₃`, the exhaustion built from `ω₃` has closed boundary
   for both dominated coordinates, so both induced boundary partitions at that
   region are free.  This is the paper's `ωᵢ|∂S_n(ω₃) = 0`.
7. **Stacking / pushout identities.**  `region_union` (exploration is additive
   over unions of bases), `region_eq_self_of_closed`,
   `region_union_of_closed` (`region (S ∪ U) = S ∪ region U` for closed `S`),
   and `disjoint_region_of_subset_compl` (exploration started outside a closed
   region never enters it).  These are what allow an exploration to be run in
   stages without re-entering an exhausted region.
8. **Finite box and free interior law.**  For `[G.LocallyFinite]` and finite
   `R`: `interiorEdgeSet G R` is finite (`finite_interiorEdgeSet`),
   `exists_interiorEdgeSet_contains` makes any fixed finite edge set eventually
   interior, `ae_region_box` packages finiteness + closed frontier almost surely.
   `regionBox R hR` re-indexes the interior edges as a genuine
   `FK.InfiniteVolume.FiniteBox G.edgeSet` with vertex type `↥R` (endpoints via
   a chosen orientation, `edgeFst`, `edgeSnd`).
   `closedBoundary_of_forall_frontier_false` converts labelled frontier
   closedness into `ClosedBoundary`.  Finally
   `exteriorPartition_eq_bot` and `interiorFKMeasure_eq_free`: for an exterior
   configuration all of whose frontier edges are closed,

   ```
   (regionBox R hR).interiorFKMeasure hq hp (fun η => exteriorPartition η) η
     = (regionBox R hR).graph.fkMeasure hq hp freeBoundary
   ```

   i.e. the interior FK law with the exterior-induced boundary partition **is**
   the free FK law on the box, with no convention slip (the identification is
   the setoid identity plus `freeBoundary_eq_bot`).

## Residuals (what is *not* proved here)

1. **Disintegration.** `interiorFKMeasure_eq_free` is a statement about the
   finite specification.  Identifying the *conditional law* of an
   infinite-volume FK measure, `μ(· | F_{S_n^c})(ω)`, with that specification
   needs the `FK.InfiniteVolume.IsDLR`-style disintegration along the random
   box; it is not proved here (direction 4 territory).
2. **Reverse-martingale assembly along the random exhaustion.**  The
   measurable-selection inputs are here (`measurableSet_region_eq`,
   `ae_eventually_contains_family`, `exists_edges_inside`), but the convergence
   of `μᵢ(C | F_{S_n(ω₃)^c})(ωᵢ)` to the tail conditional, with one joint null
   set, is not formalized.
3. **No instantiation of a metric base family.**  The bases `T : ℕ → Set V` are
   abstract (finite, connected, monotone, cofinal).  `FK.DualFiniteEnclosure`
   already supplies metric realizations; I did not wire them in.
4. **No Theorem 5.1 conclusion.**  Uniqueness of the Gibbs measure is not
   claimed; the hard direction of Strassen's theorem (ordered coupling) is
   another member's direction, and I do not use it.
5. **`frontier_closed` is stated with explicit endpoint data.**  The hypothesis
   `∃ x ∈ e.1, x ∈ R` plus `∃ x ∈ e.1, x ∉ R` is the labelled "edge crosses the
   frontier" condition; it is equivalent to the pair-level statement used in
   `ClosedBoundary` but the conversion is proved only in the direction needed
   (`closedBoundary_of_forall_frontier_false`).
6. **`exteriorPartition` closes the box edges** when extending an exterior
   configuration; this is harmless because the allowed edge set
   `nonInteriorEdges R` contains no box label, but the corresponding locality
   lemma is inlined rather than exported.
