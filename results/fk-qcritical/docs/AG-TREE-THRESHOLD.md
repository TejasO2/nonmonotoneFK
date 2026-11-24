Public modules: `FK.AGTree.{Interface,BaseNonpercolation,ShiftThreshold,SharpThreshold,ThresholdExamples}`, with only worker-local import paths changed. All 33 principal declarations were independently rebuilt and allowed-axiom checked. The shift compares genuine open-cluster percolation: at the root `Cluster` and `InfiniteClusterAt` agree, while away from the root the theorem supplies an ancestor with infinite forward cluster. No quasi-transitivity, exact two-rate threshold, `hAG`, or DLR conclusion follows.

# Direction 6 (member m3, swarm smwu2ryc1): branching/percolation interface on `FK.AGTree`

All work is in this directory; nothing in `results/fk-qcritical` was modified.  The five
modules below are additive and import only `FK.AGTree.Main` plus each other.

| file | imports | content |
|---|---|---|
| `TreeInterface.lean` | `FK.AGTree.Main` | open subgraph, open connectivity, identity of forward/infinite clusters |
| `TreeBaseNonpercolation.lean` | `TreeInterface` | crude nonpercolation for `3 r₀ < 1`, a.s. finiteness |
| `TreeShift.lean` | `TreeBaseNonpercolation` | the percolation event `Perc`, base vs activated comparison |
| `TreeSharpThreshold.lean` | `TreeShift` | exact critical value `1/2` of the base law (both sides) |
| `TreeThresholdExamples.lean` | `TreeSharpThreshold` | concrete rates `3/10` (no percolation) and `3/5` (percolation) |
| `AuditTree.lean` | `TreeThresholdExamples` | `#print axioms` for 33 declarations |

Everything is in `namespace Ultra`, so on integration into the library the modules can be
renamed (e.g. `FK/AGTree/Interface.lean`, `FK/AGTree/BaseThreshold.lean`) without touching
names.  There is no `sorry`, `admit`, custom axiom, `unsafe` or `native_decide`.

## Build and axiom report

Checked with the pinned toolchain `leanprover/lean4:v4.35.0`
(`~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`) against the built library
`results/fk-qcritical/.lake/build/lib/lean`, in dependency order, from a clean output
directory: all six files elaborate with no errors (2.3–2.8 s each, mainly import time).

`AuditTree.lean` prints `#print axioms` for all 33 headline declarations; every one reports
exactly `[propext, Classical.choice, Quot.sound]`, and no declaration depends on any other
axiom (in particular not `sorryAx`).

## What is proved

### 1. The interface: `Cluster` is a genuine percolation notion (`TreeInterface.lean`)

* `eOf`, `OAdj ω v w` (open adjacency), `OReach ω u v` (`Relation.ReflTransGen` of open
  adjacency, i.e. connectivity in the open-edge subgraph), `clusterSet ω u`,
  `InfiniteClusterAt ω u` (the open cluster of `u` is infinite), `FiniteClusterAt`.
* `DownOpen ω m u` (`∃ l, u.w = m.w ++ l ∧ ChainOpen ω m l`), and
  **`oReach_iff_exists_downOpen : OReach ω u x ↔ ∃ m, DownOpen ω m u ∧ DownOpen ω m x`**
  (the shape of an open path in the rooted tree: a common open ancestor; proved by
  head-induction on `ReflTransGen`, with no acyclicity/Jordan input).
* `cluster_infinite : Cluster ω u → InfiniteClusterAt ω u`.
* **`exists_cluster_ancestor : InfiniteClusterAt ω u → ∃ t, Pref t.w u.w ∧ Cluster ω t`**
  (choose a vertex of minimal depth in the infinite open cluster; every vertex of the cluster
  is then an open descendant of it).  Consequences:
  `infinite_iff_exists_cluster : (∃ u, InfiniteClusterAt ω u) ↔ (∃ m, Cluster ω m)` and
  **`cluster_iff_infinite_root : Cluster ω V.root ↔ InfiniteClusterAt ω V.root`**.
* Supporting: `finite_lists_lt`, `finite_levels` (level sets are finite), `Fwd.mono`,
  `downOpen_fwd`, `fwd_vertex`.

### 2. Base nonpercolation (`TreeBaseNonpercolation.lean`, `TreeSharpThreshold.lean`)

`pr r A = (law r).real A`.  For `law r` (class-`0` edges open w.p. `r 0`, class-`1` with
`r 1`):

* `one_sub_prod_le_sum : 1 - ∏ (1 - x_i) ≤ ∑ x_i` for `x_i ∈ [0,1]` (Boole's inequality).
* `pr_fwd_succ_le` + `card_class`: `pr{Fwd u (n+1)} ≤ ∑_{valid class-0 letters} r₀·pr{Fwd child n}`.
* `pr_fwd_le : (r 1:ℝ) = 0 → pr r {Fwd u n} ≤ (3 r₀)^n` — uniform in the vertex.
* `pr_cluster_zero`, `pr_percolation_zero` (**`3 r₀ < 1` ⟹ `pr r {∃ u, InfiniteClusterAt} = 0`**),
  `ae_finite_clusters` (a.s. all open clusters are finite), `measure_eq_zero_of_pr_eq_zero`.
* Sharp version with the exact two-state count (`card_classZero_le_two`,
  `two_le_card_valid_class_zero`, `ClassZero`, `childOf`):
  `pr_fwd_le_two`, `pr_fwd_le_two_root : pr r {Fwd u n} ≤ 3 (2 r₀)^n`, hence
  **`pr_percolation_zero_of_two_mul_lt_one : (r 1 = 0) → 2 r₀ < 1 → pr r {Perc} = 0`**.

### 3. The percolation side and the exact critical value `1/2` (`TreeSharpThreshold.lean`)

* `epsOf r = (2 r₀ - 1)/(2 r₀²)`; `epsOf_pos`, `epsOf_le_one`, `epsOf_mul_le_one`, and the
  contraction **`epsOf_contract : (1 - r₀ ε)² ≤ 1 - ε`** for `1 < 2 r₀`.
* `pr_notFwd_succ_le`: if every class-`0` child reaches level `n` with probability `≥ ε`, then
  `pr{¬Fwd u (n+1)} ≤ (1 - r₀ ε)²` (product form `measure_notFwd_succ`, at least two valid
  class-`0` letters, `prod_le_prod_of_le`, `prod_ite_pow`).
* `pr_fwd_ge_eps : (r 1 = 0) → 1 < 2 r₀ → ε ≤ pr r {Fwd u n}` for **all** `n, u`
  (quantitative, uniform in the vertex), and by reverse convergence
  `pr_cluster_pos_of_one_lt_two_mul : 0 < pr r {Cluster ω u}`.
* **`base_critical_one_half : (r 1 = 0) → (2 r₀ < 1 → pr r {Perc} = 0) ∧ (1 < 2 r₀ → 0 < pr r {Perc})`**
  — the phase transition of the base (class-`1`-closed) law is exactly at `r₀ = 1/2`.

### 4. The strict base-vs-activated shift (`TreeShift.lean`, `TreeThresholdExamples.lean`)

* `Perc ω := ∃ u, InfiniteClusterAt ω u` (a genuine infinite open cluster, not a forward
  cluster).
* `base_rate_one`, `base_threshold`, `base_nonpercolation`,
  `base_nonpercolation_sharp : pr (enhRate p0 0) {Perc} = 0` at the paper's base rate `3/10`.
* `activated_percolation : 0 < pr (enhRate p0 s0) {Perc}` at rates `(3/10, 1/2)`, transferred
  from `Ultra.enh_cluster_pos` through `cluster_infinite` (interface).
* **`strict_critical_shift : pr (enhRate p0 0) {Perc} < pr (enhRate p0 s0) {Perc}`**,
  `activated_percolation_measure`, and `activation_moves_across_threshold`.
* `percolation at (3/10,0) = 0`, `percolation at (3/5,0) > 0`: `rates_straddle_half`,
  `perc_at_three_fifths`.

## Scope and precise residuals

* The results are for the actual two-class tree of `FK/AGTree` (five-regular reduced-word
  tree, class rates `r 0`, `r 1`), the actual product law `Ultra.law r`, and the actual open
  connectivity of the graph.  No quasi-transitivity is used or claimed: the `Fwd` bounds are
  uniform over all vertices, which is exactly what replaces a symmetry hypothesis here.  No
  bounded-range/AG reference theorem, no `hAG`, and no general lattice statement is claimed.
* At `r₀ = 1/2` (base law) nothing is claimed; the two-sided statement is strict on both
  sides.
* The activated law `(3/10, 1/2)` is proved to percolate (positive probability), but no exact
  critical value is claimed for the two-rate law; only the base law (class-`1` closed) has its
  exact threshold `1/2`.  The paper's enhanced/AG critical window is untouched.
* `Cluster` is identified with an infinite open cluster only at the root (`cluster_iff_infinite_root`);
  away from the root the correct statement is `exists_cluster_ancestor` (an infinite open
  cluster at `u` contains an ancestor with an infinite forward cluster), not equality: an
  infinite open cluster can leave `u` upwards.

## Reproducing the check

`check.sh <file>.lean` in this directory sets
`LEAN_PATH=.ol:<pinned lake paths of results/fk-qcritical>` (the pinned paths are cached in
`leanpath.txt`) and runs the v4.35.0 toolchain with `-o .ol/<file>.olean`, so later files can
`import` earlier ones.  Build order:

```
./check.sh TreeInterface.lean
./check.sh TreeBaseNonpercolation.lean
./check.sh TreeShift.lean
./check.sh TreeSharpThreshold.lean
./check.sh TreeThresholdExamples.lean
./check.sh AuditTree.lean
```

For library integration, move the six files into `results/fk-qcritical/FK/AGTree/` (adjusting
only the first `import` line of each: `FK.AGTree.Main`, `FK.AGTree.Interface`,
`FK.AGTree.BaseNonpercolation`, `FK.AGTree.ShiftThreshold`, `FK.AGTree.SharpThreshold`,
`FK.AGTree.ThresholdExamples`) and add them to `FK.lean`/`Audit.lean`; the `Ultra` namespace
and all declaration names stay unchanged.

`Probe*.lean`, `Test.lean` are scratch files, not part of the result.
