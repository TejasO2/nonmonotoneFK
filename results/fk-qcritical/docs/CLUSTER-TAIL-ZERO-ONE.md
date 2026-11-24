Public modules: `FK.ClusterCover`, `FK.ClusterTail`, `FK.TailSigmaBridge`, `FK.ClusterTailExample`, `FK.ClusterTailExample2`. The audit suffix is `percolation_hasInfiniteCluster_zero_one_pi`. All 30 principal declarations were independently rebuilt and allowed-axiom checked. Zero–one describes infinite existence only. The unique form uses `GlobalAtMostOne` as a hypothesis; no constancy/Burton–Keane consequence is inferred.

# Direction 9 — tail zero–one law for percolation events (Lean 4.35, FK project)

Status: complete and machine-checked for the registered direction. ~965 lines of
new Lean, no `sorry`/`admit`, no custom axiom, no `unsafe`, no `native_decide`.
Every audited declaration depends only on `propext`, `Classical.choice`,
`Quot.sound` (see `Audit.lean`, run by `build.sh`).

Nothing here modifies imported project sources.  Files import the repository
build (`FK.ExtremalTail`, `FK.ConventionTransport`,
`CurvatureVariance.Infra.Percolation.Critical`) and are compiled with the
project toolchain `leanprover/lean4:v4.35.0`.

## Mathematical content

Let `G` be a simple graph with countable vertex type, `ω : G.edgeSet → Bool` a
bond configuration, and `OpenConnected G ω A u v` the project's open-walk
connection.  Write

* `clusterAvoid G ω A x = {y | OpenConnected G ω (Set.univ \ A) x y}` (the open
  cluster of `x` computed while avoiding the edge set `A`),
* `HasInfiniteCluster G ω = ∃ x, (clusterAvoid G ω ∅ x).Infinite`.

**1. Finite-modification invariance (`ClusterCover.lean`).**
`clusterAvoid_cover_insert`: avoiding one extra edge `e = s(a,b)` splits the
cluster into the pieces through `x`, `a`, `b`.  Iterating,
`exists_finite_cover`: for finite `A` the full cluster of `x` is covered by
finitely many `A`-avoiding clusters.  Hence
`exists_infinite_cluster_avoid`: if the full cluster of some `x` is infinite,
some `A`-avoiding cluster is infinite; and
`hasInfiniteCluster_congr`: **`HasInfiniteCluster` is unchanged by modifying
finitely many edges.**  (This is the "removing finitely many edges from a
connected infinite graph leaves an infinite piece" step, in walk form and
without any ray/König argument.)

**2. Kolmogorov zero–one (`ClusterTail.lean`).**
`measurableSet_hasInfiniteCluster` (countable `V`) and
`isUpperSet_hasInfiniteCluster` (the event is increasing in `ω`).
`measure_eq_zero_or_one_of_cylinder_indep`: a measurable `A` that depends only
on the coordinates off every finite set and is independent of every cylinder
event satisfies `μ A = (μ A)²`.  The proof uses the project's
`measure_inter_eq_mul_of_dependsOn`, π-systems
`{A}` and `{B | B depends on finitely many coordinates}`, `IndepSets.indep'`,
and `MeasurableSpace.pi_eq_generateFrom_projections`.
Instances: `bernoulliProduct_eq_zero_or_one`;
`percolation_hasInfiniteCluster_zero_one`: **under i.i.d. Bernoulli(`p`) bond
percolation, the probability that an infinite open cluster exists is `0` or
`1`**; and `percolationProb_eq_zero_of_noInfiniteCluster`.

**3. Tail sigma-algebra bridge and the FK instance (`TailSigmaBridge.lean`).**
`measurableSet_outsideSigma_of_dependsOn` and
`dependsOn_of_measurableSet_outsideSigma` give the characterisation
`measurableSet_tailSigma_iff`:
`MeasurableSet[FKLimit.tailSigma] A ↔ MeasurableSet A ∧ ∀ finite S,
DependsOn (· ∈ A) Sᶜ`.
Consequences:
* `zeroOneOn_tailSigma_bernoulliProduct`:
  `FK.ZeroOneOn FKLimit.tailSigma (bernoulliProduct E p)` — the Kolmogorov
  zero–one law for the project's own tail sigma-algebra on edge configurations;
* `zero_one_hasInfiniteCluster_of_zeroOneOn_tail`: any tail zero–one law gives
  mass `0` or `1` to the existence of an infinite open cluster;
* `zero_one_hasInfiniteCluster_of_extremal_dlr`: **for an extremal DLR law of a
  finite-box FK specification on `G.edgeSet`, an infinite open cluster exists
  a.s. or a.s. does not exist** (uses the project's
  `FK.InfiniteVolume.zeroOneOn_tailSigma_of_extremal_dlr`);
* `percolation_dichotomy`: either an infinite cluster exists a.s. or `θ(o) = 0`
  for every root `o` (this is the legitimate form of "model-specific
  nonpercolation": a.s. nonexistence, not merely positive probability);
* `zero_one_hasUniqueInfiniteCluster_of_zeroOneOn_tail`: under a tail zero–one
  law which a.s. has at most one infinite cluster (`GlobalAtMostOne`), the event
  of possessing an infinite cluster has mass `0` or `1`.

**4. Sharpness (`ClusterTailExample.lean`, `ClusterTailExample2.lean`).**
* On the ray graph `rayGraph` (`ℕ`, neighbours differ by one), all-open has the
  root cluster `= univ`, while closing the single edge `{0,1}` leaves the root
  cluster `= {0}`; both configurations have an infinite cluster.  Hence
  `not_dependsOn_rootCluster`: **the event "the cluster of the root is infinite"
  is not finite-modification invariant and hence not tail measurable** — `θ` is
  not a tail event, and only the existence event can be treated by the 0–1 law.
* On the line graph `lineGraph` (`ℤ`, neighbours differ by one), closing the
  single edge `{0,1}` splits one infinite cluster into two:
  `twoInfiniteClusters_cut`, while `not_twoInfiniteClusters_allOpen` shows the
  all-open configuration has no two incomparable infinite clusters.  Hence
  `not_dependsOn_twoInfiniteClusters`: **"at least two infinite clusters" is not
  tail measurable**; the a.s. constancy of the number of infinite clusters must
  come from graph automorphisms/ergodicity, not from finite modification.

## Scope and residuals (not claimed)

* No `p_c` value is computed, no monotonicity in `p` (that needs the ordered
  coupling of direction 1), no "at most one infinite cluster" theorem: the
  Burton–Keane step is not proved here.  Only the *conditional* corollary
  `zero_one_hasUniqueInfiniteCluster_of_zeroOneOn_tail` uses `GlobalAtMostOne`
  as a hypothesis.
* No FK DLR statement is derived beyond the extremal tail zero–one input from
  the project; in particular no one-point/DLR identification for non-extremal
  laws, no strong uniqueness, no AG/reference shift.
* The zero–one law is for the *existence* event only; §4 proves that the root
  cluster and the "at least two clusters" events are genuinely outside its
  scope.

## Build

```
.ultramath/smwu2ryc1/m8/build.sh ClusterCover.lean ClusterTail.lean \
    TailSigmaBridge.lean ClusterTailExample.lean ClusterTailExample2.lean \
    Audit.lean
```
(runs `lake env lean` in `results/fk-qcritical` with this directory on
`LEAN_PATH`).  For repository integration, place the files in `FK/` and change
`import ClusterCover` → `import FK.ClusterCover`, `import ClusterTail` →
`import FK.ClusterTail`, `import TailSigmaBridge` → `import FK.TailSigmaBridge`,
`import ClusterTailExample` → `import FK.ClusterTailExample`; the namespaces
`FK.ClusterCover` / `FK.ClusterTail` already match that layout.
