# Direction 6 report: open-cut separation and the dual-nonpercolation target

Seventeenth/eighteenth-stage FK formalization, member `m6`, direction 6
("planar dual nonpercolation to cofinal open circuits").

Everything here is new code in this directory. Nothing outside
`.ultramath/smwttt0li/m6/` was touched. Both files compile with the pinned
toolchain `leanprover/lean4:v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`
(the project's own `.lake`), with default heartbeats, and every `#print axioms`
report is exactly `[propext, Classical.choice, Quot.sound]`. No
`sorry`/`admit`/`axiom`/`unsafe` occurs.

Reproduce with (from `results/fk-qcritical`):

```
PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH \
  lake env lean <this-directory>/OpenCutSeparation.lean
PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH \
  lake env lean <this-directory>/StripDualCounterexample.lean
```

## 1. `OpenCutSeparation.lean` — the geometric content of the spherical chain

The published uniqueness chain (`FK/InfiniteOpenCircuitUniqueness.lean`,
`FK/PrimalOpenBoundary.lean`) proves `GlobalAtMostOne` from a cofinal family of
*metric-spherical* primal-open circuits. This file shows that the metric part
is inessential and isolates the exact combinatorial content.

* `orientedCut G A` — the oriented edge cut of a vertex set.
* `exists_orientedCut_vertex_of_walk` — **crossing lemma**: an open walk from a
  vertex in `A` to a vertex outside `A` traverses a cut edge, and the
  `A`-side endpoint of that edge is open-connected to the walk source by the
  open prefix.
* `globalAtMostOne_of_finite_openCuts` — **geometry-free uniqueness
  criterion**. On an *arbitrary* `SimpleGraph` (no planarity, no embedding, no
  properness, no spheres): if for every pair `x y` there is a finite `A ∋ x, y`
  whose oriented cut is entirely open and whose incident vertices are mutually
  open-connected, then `GlobalAtMostOne G ω`.
* `globalAtMostOne_of_finite_openCuts_on_infinite` — sharp form: the cut is
  only required for pairs `x, y` that really carry two infinite clusters;
  `globalAtMostOne_of_finite_openCuts` is its corollary.
* `finite_openCut_of_sphericalOpenCircuit` — an actual
  `SphericalOpenCircuit` at radius `r` produces such a cut with
  `A = vertex ⁻¹' ball c r` (the only geometry used is the intermediate value
  theorem for `t ↦ dist (arc t) c`, in `exists_mem_sphere_of_mem_ball_not_mem_ball`).
* `globalAtMostOne_of_openCircuitExhaustion_cut` — the existing spherical
  exhaustion theorem, re-derived through the cut form. The cut criterion is
  therefore a strict generalisation of the shape of hypothesis that the
  repository actually uses.
* `globalAtMostOne_of_finite_openCuts_through_labelSet` — the usable form
  matching the finite planar boundary output: it is enough that one
  open-connected label set `C` (`OpenLabelConnected`) contains the whole cut.
* `exists_orientedCut_edge_of_walk`, `openCluster_subset_of_closed_cut`,
  `noInfiniteOpenCluster_of_forall_finite_closedCut` — the **companion half**:
  if every edge leaving a finite `A` is closed then the open cluster of any
  vertex of `A` is contained in `A`, hence finite; if every vertex admits such
  a finite closed cut then there is no infinite open cluster at all.  Together
  with `globalAtMostOne_of_finite_openCuts` this is the complete combinatorial
  kit of the planar argument: closed cuts trap finite clusters, open cuts with
  connected cut-vertices join infinite ones.  No geometry is used in either
  half; geometry is only needed to produce the cuts.
* `dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction` — the source
  facing residual: the whole planar cluster-count step reduces to producing
  such finite open cuts from dual nonpercolation.

Consequence for the direction: the remaining geometric obligation is *not*
"find a Jordan circuit for a sphere"; it is exactly "produce a finite open cut
through any two prescribed vertices, with connected cut-vertices" (equivalently,
one open-connected label set containing all cut edges). Every existing and
future construction can be plugged in at that interface.

## 2. `StripDualCounterexample.lean` — the bare target is false

`FK/PlaneClusterTarget.lean` states

```
def DualNonpercolationForcesPrimalAtMostOne (G) (GD) (edge : G.edgeSet ≃ GD.edgeSet) : Prop :=
  ∀ ω, NoInfiniteOpenCluster GD (dualConfig edge ω) → GlobalAtMostOne G ω
```

with **no** geometric hypothesis at all. This file proves that predicate
false, twice.

### 2.1 Genuine planar strip and its genuine planar dual

`stripGraph` is the infinite three-row strip on `ℤ × Fin 3` (horizontals in
each row, rungs between consecutive rows), drawn with straight segments. It is
proved **connected** (`stripGraph_connected`) and **locally finite in the
neighbour-set sense** (`stripGraph_neighbourSet_finite`, at most five
neighbours).

`dualGraph` is its actual planar dual: vertices `none` (outer face) and
`some (i,k)` (`k : Fin 2`) for the bounded unit squares, with one dual edge per
primal edge joining the two faces adjacent to it:

| primal family | dual edge |
|---|---|
| `h0 i` bottom horizontal | `none` — `(i,0)` |
| `h1 i` middle horizontal | `(i,0)` — `(i,1)` |
| `h2 i` top horizontal | `(i,1)` — `none` |
| `v0 i` rung rows 0–1 | `(i-1,0)` — `(i,0)` |
| `v1 i` rung rows 1–2 | `(i-1,1)` — `(i,1)` |

Both edge sets are indexed by the same five families, giving an explicit global
bijection `edgeEquiv` (`edgeEquiv_pEdge : edgeEquiv (pEdge a) = dEdge a`).

Closing exactly the three horizontals that cross the column boundary `0 | 1`
(configuration `ω`):

* dual openness is exactly `a ∈ cutIdx` (`dualConfig_dEdge`), so the dual-open
  edges are the three among `{none, (0,0), (0,1)}` and every dual-open
  component is finite: `noInfiniteOpenCluster_dual`;
* the pinning map `side` (`0` on columns `≤ 0`, `1` above) is constant along
  every open edge (`side_eq_of_open`), so `(0,0)` and `(1,0)` are **not**
  open-connected (`not_openConnected_zero_one`) although both have infinite
  open clusters (`infiniteCluster_zero`, `infiniteCluster_one` via
  `openConnected_left`, `openConnected_right`).

Hence `not_globalAtMostOne` and

```
not_dualNonpercolationForcesPrimalAtMostOne :
  ¬ FK.Planar.DualNonpercolationForcesPrimalAtMostOne stripGraph dualGraph edgeEquiv
```

The hypothesis the source adds and the predicate omits is exactly what fails
here: the outer face has infinitely many boundary edges, so the dual is not
locally finite (`dualGraph_neighbourSet_none_infinite`). This matches the
source: Theorem 1.11 (`paper/main.tex` §1, HTML text line 243–244) explicitly
assumes "`G` is embedded in `ℝ²`, and its dual `G*` is locally finite", and the
deterministic step used in §5.2 is the sentence at HTML text line 571:
"Therefore, `ω*` has a.s. no infinite cluster, so `ω` has a.s. at most one
infinite cluster."

**Remark (not formalized).**  The strip also satisfies the paper's other graph
hypotheses of Theorem 1.4/1.11 informally: it is infinite, connected
(`stripGraph_connected`), locally finite (`stripGraph_neighbourSet_finite`),
quasi-transitive (two vertex orbits — rows `0,2` and row `1`; iterated
translations `(i,k) ↦ (i+n,k)` and the reflection `k ↦ 2-k` move `(0,0)` to
every vertex of rows `0,2` and `(0,1)` to every vertex of row `1`, while
degrees `3` and `4` separate the two classes), and it contains edges on a cycle
and on a doubly infinite path.  What fails is precisely the added hypothesis of
Theorem 1.11: `G*` locally finite.  The orbit count and the degree computation
are stated here as a remark and are not part of the compiled development.

### 2.2 Local finiteness alone is not a repair

Pairing the strip with **itself** by `Equiv.refl` gives a locally finite,
connected graph on both sides; dual openness is then primal closedness, and the
three closed edges span only six vertices, so again there is no infinite
dual-open component (`noInfiniteOpenCluster_self`), while the primal still has
two infinite open clusters. Hence

```
not_dualNonpercolationForcesPrimalAtMostOne_self :
  ¬ FK.PlaneTopology.StripDual.DualNonpercolationForcesPrimalAtMostOne
      stripGraph stripGraph (Equiv.refl stripGraph.edgeSet)
```

So no purely combinatorial predicate of the form "some graph with the same edge
cardinality has no infinite open cluster" can carry the planar cluster-count
step: the *geometric* duality (faces, incidences, local finiteness of the
actual dual, and separation) is essential.

## Formal geometric scope of the strip

The strip and its face-index dual are explicit simple graphs with an exact edge bijection. The face table is the standard lattice incidence pattern appropriate to the usual straight-line drawing; no general `OpenPathRealization`, arbitrary continuous-embedding, or Jordan-separation theorem is constructed or needed for the counterexample to the bare graph predicate. The quasi-transitivity remark elsewhere in this report remains unformalized. These limitations do not affect the component/cut computations.

## 3. Exact residual

Combining §1 and §2, the correct source-faithful target has two independent
inputs and cannot be weakened to a bare predicate:

1. **(planar geometry)** a genuine plane drawing of the infinite connected
   locally finite `G` whose dual `G*` is locally finite, with the actual edge
   correspondence;
2. **(separation from dual nonpercolation)** for every pair of vertices `x, y`
   and every configuration with no infinite dual-open cluster, a finite vertex
   set `A ∋ x, y` whose oriented cut is entirely primal-open and whose
   incident vertices are open-connected (or one open-connected label set
   containing the cut).

Impact: the only consumer of the bare predicate is
`FK/InfiniteOpenCircuitUniqueness.dualNonpercolationForcesPrimalAtMostOne_of_circuitConstruction`,
which *derives* it from a circuit construction; that hypothesis is not vacuous
and cannot be discharged for the strip.  No module in the repository asserts
the bare predicate, so nothing is unsound today; but no future proof of it for
a general `(G, GD, edge)` can exist, and any attempt must be per-instance with
the geometric hypotheses of §3.

Given 1 and 2, `globalAtMostOne_of_finite_openCuts` yields
`GlobalAtMostOne`, hence the `hgeometry` field consumed by
`FK.Planar.theorem_1_11_abstract` in `FK/Theorem11Abstract.lean`. Neither input is proved here; §2 shows that dropping
1 makes the statement false, and §2.2 shows that replacing it by a
cardinality/local-finiteness condition on an arbitrary "dual" is also false.

What *is* fully proved here: the reduction of the whole cluster-count step to
2, the recovery of the existing spherical route from it, and the two
refutations. No whole-paper theorem is claimed.
