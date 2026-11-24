# GridFrontier: exact diamond-frontier crossing control on the square lattice

Public module `FK.GridFrontier`. Its source was rebuilt independently and seventeen fully qualified main declarations passed the allowed-axiom script. This is a strict geometric addition, not a probability theorem: `globalAtMostOne_allOpen` checks the exhaustion instance on the trivial all-open configuration, while `openComponent_finite_of_diamondCut_closed` is the nonvacuous arbitrary-configuration consequence. Shifted-centre statements explicitly identified as hand checks in the worker report are not treated as formal results.


Direction 8 (planar grid/separator circuit realization), swarm `smwu0pw30`, member m2.
File: `GridFrontier.lean` (1208 lines, 73 declarations, no `sorry`/`admit`/`axiom`/`unsafe`).

## What is proved (all in Lean 4, namespace `FK.PlaneTopology.GridFrontier`)

### 1. The graph and the straight-line realization
* `GridV := ℤ × ℤ`, `gridAdj` (unit steps), `gridGraph : SimpleGraph GridV`, `gridVertex : GridV → ℝ × ℝ`
  injective, `gridRealization : OpenPathRealization gridGraph gridVertex` with every edge mapped to the
  straight segment `straightPath` (from `FK.JordanUnicyclicEnclosure`).

### 2. The diamond (`ℓ¹`) level function
* `l1 z = |z.1| + |z.2|`, `lvl p = p.1.natAbs + p.2.natAbs`, `lvl_cast : l1 (gridVertex p) = lvl p`.
* `l1_affine_step`: on **every** unit lattice segment the `ℓ¹` norm is affine,
  `l1 (segment p q t) = (1-t) l1 p + t l1 q`. This is the technical core; it rests on `abs_int_add_I`,
  `abs_int_sub_I` (the absolute value of an integer plus/minus an interpolation parameter is affine).
* `lvl_adj`: adjacent vertices have levels differing by exactly one (four `natAbs` cases).

### 3. Exact crossing characterisation (the geometric theorem)
* `diamondBarrier k = {z | l1 z = k + 1/2}` (`k : ℕ`), `diamondInside k = {l1 < k+1/2}`,
  `diamondOutside k = {k+1/2 < l1}`, and `diamondSep k : TwoSidedSeparation (ℝ × ℝ)` built from the
  **level-set intermediate value theorem** (`not_joinedIn_compl_levelSet_of_lt`) — no Jordan theorem.
* `gridVertex_off_diamond`: no lattice vertex lies on any half-integral diamond sphere.
* `crosses_diamondBarrier_iff`: an edge arc meets the diamond sphere **iff** its endpoints lie on
  levels `k` and `k+1`. (Both directions: half-parameter for the easy one; affineness plus
  integrality of the levels for the converse.)
* `diamondCut k` is the corresponding **edge label set**; `gridRealization_crossing_diamond` is the
  `CrossingControlledBy` instance.

### 4. The crossing labels are genuinely open-connected (the new geometric content)
* `conn_NE`, `conn_NW`, `conn_SW`, `conn_SE`: four monotone staircases. A level-`k` vertex in each
  quadrant reaches the corresponding hub `(k,0)`, `(0,k)`, `(-k,0)`, `(0,-k)` through crossing edges
  only; the hubs are then linked (`connected_to_hub_of_level`, `connected_to_hub`).
* `exists_inner_neighbour`: every level-`(k+1)` vertex has a level-`k` neighbour, which handles the
  outer vertices.
* `diamondCut_openLabelConnected`: **`OpenLabelConnected gridGraph ω (diamondCut k)`**, i.e. all
  vertices incident to the crossing labels are joined through crossing labels alone. On the square
  lattice the crossing set has `8k+4` edges (`k = 0`: 4) — hand-verified count, not formalized — and
  is a single connected staircase component, in contrast with the single-connector chain of
  `FK.ConnectedCycleChainExhaustion`.

### 5. Interface instances and consequences
* `separatorOpenCircuit_diamond k`: a genuine `SeparatorOpenCircuit` (all four fields) for the
  all-open configuration.
* `ball_subset_diamondInside`: `ball 0 ρ ⊆ diamondInside (⌈2ρ⌉₊+1)`; `finite_gridVertex_preimage_inside`.
* `hasSeparatorCircuitExhaustion_allOpen`: `HasSeparatorCircuitExhaustion` for the all-open square
  lattice about the origin; `globalAtMostOne_allOpen` is the resulting corollary. Both are
  *interface checks*: the percolation conclusion is trivial for the all-open configuration and is
  **not** claimed as a percolation theorem.
* `finite_diamondCut`: the crossing label set is finite.

### 6. The non-vacuous dual direction: a closed diamond cut traps the cluster
* `openComponent_finite_of_diamondCut_closed`: for **any** configuration `ω`, if every edge of
  `diamondCut k` is closed, then the open component of any vertex inside the diamond is finite.
  This is the geometric form of "closed (dual-open) circuit ⇒ no percolation" and is
  non-vacuous: it applies to every configuration with a closed diamond cut, e.g. the configuration
  open exactly on the diamond interior.
* `not_exteriorInfiniteCluster_of_diamondCut_closed`: the same vertex is in no infinite open cluster.

### 7. The `ℓ^∞` box cut is *not* open-connected (the precise missing property)
* `lvlInf p = max p.1.natAbs p.2.natAbs` (sup-norm level) and `boxCut k` = the edges joining
  sup-norm level `k` to level `k+1` — the label set of a square shell / of the oriented cut of the
  vertex box.
* `boxCut_levels`: a box-cut edge has levels `k` and `k+1`, in some order.
* `boxCut_corner_neighbours`, `boxCut_axis_neighbours`: the east corner `(k+1,0)` has exactly one
  box-cut neighbour `(k,0)`, and (for `k ≥ 1`) the axis point `(k,0)` has exactly one box-cut
  neighbour `(k+1,0)`.
* `boxCut_not_openLabelConnected`: for `k ≥ 1` and **every** configuration `ω`,
  `¬ OpenLabelConnected gridGraph ω (boxCut k)`. The two isolated box-cut edges through `(k,0)` and
  `(0,k)` lie in different components, so no walk using box-cut labels joins them. Consequently no
  `SeparatorOpenCircuit` can have the box-cut labels as its circuit: a square shell can trap a cluster
  (closed labels) but cannot be a connected open circuit. This is the precise missing property that
  forces the source's wired/enhanced labels (or a different shape) on a grid.

### 8. Sharpness: solid diamond shells cannot give a non-trivial cofinal exhaustion
* `exists_mem_diamondCut`: every edge of the lattice belongs to some diamond crossing set.
* `allOpen_of_diamondCuts_open`: if every diamond crossing set consists of open labels, the
  configuration is the all-open configuration. Hence exact crossing control by this one nested family
  is only available for the all-open configuration. (Hand check, not formalized: for a half-integer
  centre the "flat" edges cut the staircase cycle into two components — already at `k = 1` the
  crossing set is two stars — so `OpenLabelConnected` fails; a non-trivial configuration therefore
  needs either several centres per radius or the source's wired/enhanced labels.)

## Exact dependencies
* `import FK.SeparatorCircuits` (`TwoSidedSeparation`, `not_joinedIn_compl_levelSet_of_lt`,
  `OpenLabelConnected`, `SeparatorOpenCircuit`, `HasSeparatorCircuitExhaustion`,
  `globalAtMostOne_of_separatorCircuitExhaustion`, `mem_inside_of_openConnected_of_closed`,
  `GlobalAtMostOne`, `OpenConnected`, `LabelCarrier`, `VertexOnLabels`).
* `import FK.JordanUnicyclicEnclosure` (only `straightPath` and `segmentArc`).
* No other project module and no Mathlib file is imported directly; nothing outside
  `.ultramath/smwu0pw30/m2/` was modified.

## Build and audit
Toolchain `leanprover/lean4:v4.35.0` (the project's own, via `$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`),
`LEAN_PATH` = the project's `.lake/build/lib/lean` + its package build dirs + the toolchain core:

```
./build.sh -o GridFrontier.olean GridFrontier.lean      # 4.5 s wall (imports already elaborated), no warnings
./build.sh Audit.lean                                    # #print axioms on 18 main results
```

`#print axioms` on `diamondCut_openLabelConnected`, `separatorOpenCircuit_diamond`,
`hasSeparatorCircuitExhaustion_allOpen`, `globalAtMostOne_allOpen`, `allOpen_of_diamondCuts_open`,
`crosses_diamondBarrier_iff`, `gridVertex_off_diamond`, `exists_mem_diamondCut`,
`finite_gridVertex_preimage_inside`, `openComponent_finite_of_diamondCut_closed`,
`not_exteriorInfiniteCluster_of_diamondCut_closed`, `finite_diamondCut`, `l1_affine_step`, `lvl_adj`,
`boxCut_not_openLabelConnected`, `boxCut_corner_neighbours`, `boxCut_axis_neighbours`:
all report exactly `[propext, Classical.choice, Quot.sound]`.

## Scope and residuals
* **Not claimed**: any statement about a random/model-specific FK configuration, any measure-theoretic
  or almost-sure statement, any percolation criticality claim, Theorem 1.11, or nonpercolation on an
  arbitrary graph. The only infinite-cluster statement (`globalAtMostOne_allOpen`) is trivial for the
  all-open configuration and is recorded as an interface check.
* **Residual (geometric)**: a cofinal family that is simultaneously non-trivial (not all-open) and
  open-connected on the square lattice is not constructed here. The proved sharpness lemma shows a
  fixed nested diamond family cannot do it; the shifted-centre obstruction above is a hand check. The
  box-cut theorem shows that the square (`ℓ∞`) shell is not an option either.
* **Not formalized**: the crossing count `8k+4`; the identification of `boxCut k` with the actual
  crossing set of the `ℓ∞` shell (the disconnection result `boxCut_not_openLabelConnected` does not
  depend on it); translation of the whole development to an arbitrary integer centre.
