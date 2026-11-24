Public modules: `FK.QOneLine`, `FK.BoundaryRigidity`, and `FK.InfiniteSharpness`. All 25 principal declarations were independently rebuilt and passed the standard-axiom audit. This completes **uniqueness at $q=1$ for all schedules and every $p\le1$**; it does not imply the subcritical part of Theorem 1.10 or a general `q\ne1` critical-window conclusion.

# The `q = 1` line of Theorem 1.10, unconditionally

Direction d9 (member m4, swarm smwu4rrf3).  Everything here compiles against the
pinned project `results/fk-qcritical` (Lean 4.35.0, project `.lake` build used
read-only) and uses only `propext`, `Classical.choice`, `Quot.sound`; there is no
`sorry`/`admit`/custom axiom/`unsafe`/`native_decide`.

Files
- `QOneLine.lean` — infinite-volume collapse at `q = 1`.
- `BoundaryRigidity.lean` — finite sharpness witness for `q ≠ 1`.
- `InfiniteSharpness.lean` — infinite-volume sharpness (two distinct `q = 2`
  FK limits for the one-box exhaustion).
- `Audit.lean`, `Audit-output.txt` — `#print axioms` for all 25 declarations
  (all clean: `propext`, `Classical.choice`, `Quot.sound`).
- `build.sh` — build + audit (runs from a clean environment; writes only here).

## 1. The mathematical point

At `q = 1` the wired-component weight is identically one, so the finite FK law is
a Bernoulli edge product *independent of the boundary partition*
(`FK.Finite.LabelledMultigraph.fkPMF_q_one`, `FK/ClassicalOne.lean`).  Feeding that
finite identity through the project's actual finite-box conditionals shows that
every infinite-volume object of Theorem 1.10 collapses to one law, for **every**
exhaustion and **every** boundary schedule — the adversarial-partition problem
disappears at this parameter line, and no compactness subsequence is needed.

## 2. Exact statements (all proved, axiom-clean)

Let `E` be countable, `B : FiniteBox E`, `p : NNReal`, `hp : p ≤ 1`, and write
`bernoulliConst p hp := FKLimit.bernoulliProduct (fun _ : E => unitOfNN p hp)`
(independent open probability `p` on every coordinate).

* `conditionalLaw_q_one_apply_eq_bernoulliProduct` (and its `Measure.real` form
  `conditionalLaw_q_one_real_eq_bernoulliProduct`): for every boundary assignment
  `α`, every exterior `η`, and every event `A` depending only on `T ⊆ B.edges`,
  `(B.conditionalLaw (q := 1) zero_lt_one hp α η) A = (bernoulliConst p hp) A`.
* `finiteVolumeLaw_q_one_real_eq_bernoulliProduct`: the same for
  `B.finiteVolumeLaw`, i.e. finite-volume FK asymptotics are boundary-free at
  `q = 1`.
* `isFKLimit_q_one`: for every `BoxExhaustion exh` and every
  `α : ∀ n, (exh.box n).BoundaryPartition`,
  `IsFKLimit exh (q := 1) zero_lt_one hp α (bernoulliConst p hp)` — the
  fixed-exhaustion limit exists for every boundary schedule (residual **(R2)**
  of `docs/THEOREM110-ASSEMBLY.md`, at `q = 1`).
* `eq_bernoulliConst_of_isFKLimit_q_one`: conversely every `q = 1` FK limit along
  a fixed exhaustion equals the Bernoulli product.
* `fkLimitMeasures_q_one_eq_singleton`:
  `FKLimitMeasures exh (q := 1) zero_lt_one hp = {bernoulliConst p hp}`.
* `exteriorMeasure_bernoulliConst`: the box exterior marginal of the Bernoulli
  product is the Bernoulli product on the complementary edges.
* `mem_dlrMeasures_q_one`: the Bernoulli product **is** DLR at `q = 1` for every
  measurable boundary assignment (the `q = 1` box specification is constant).
* `eq_bernoulliConst_of_mem_dlrMeasures_q_one`: every DLR law at `q = 1` is the
  Bernoulli product (residual **(R3)**, Gibbs membership, at `q = 1`).
* `dlrMeasures_q_one_eq_singleton`:
  `DLRMeasures exh Φ (q := 1) zero_lt_one hp = {bernoulliConst p hp}` for every
  `Φ : BoundaryAssignment exh.box` — this is `h5_1` (singleton DLR class of one
  convention) *and* `h518` at `q = 1`.
* `fkFamily_q_one_eq_singleton`, `existsUnique_fkFamily_q_one`:
  `FKFamily exh (q := 1) zero_lt_one hp = {bernoulliConst p hp}` and
  `∃! μ, μ ∈ FKFamily exh (q := 1) zero_lt_one hp`, for every exhaustion and every
  `p ≤ 1`.  **Strong uniqueness at `q = 1`, unconditionally** (the project's
  previous unconditional instances were the `p = 0` and `p = 1` endpoints).

## 3. Sharpness (why `q = 1` is exactly the boundary-free line)

`BoundaryRigidity.lean` uses the two-vertex one-edge labelled multigraph
`unitEdgeGraph` (`Vertex := Bool`, `Edge := Fin 1`, `source = false`,
`target = true`).  With the edge open both boundaries have one component; with
the edge closed the free boundary has two and the wired boundary one.  Hence the
FK point masses at `allOpen`, `allClosed` are `p q`, `(1-p) q^2` (free) and
`p q`, `(1-p) q` (wired); normalized agreement at both configurations forces
`q^2 = q`, i.e. `q = 1` for `q > 0`.

* `fkPMF_freeBoundary_ne_wiredBoundary`: for `0 < q`, `q ≠ 1`, `0 < p < 1`,
  `unitEdgeGraph.fkPMF hq hp freeBoundary ≠ unitEdgeGraph.fkPMF hq hp wiredBoundary`.
* `fkPMF_boundary_independent_of_q_one`, `fkPMF_boundary_independent_iff`:
  for interior `p` and `q > 0`, FK laws are boundary-independent on every finite
  labelled multigraph **iff** `q = 1` (at `p = 0, 1` both laws are point masses;
  that endpoint case is already in the project).

## 3b. Infinite-volume sharpness

`InfiniteSharpness.lean` uses the project's existing one-box exhaustion
(`FK.NoncoherentCounterexample.oneEdgeExhaustion`, `oneEdgeBox`) at `q = 2`,
`p = 1/2`:

* `isFKLimit_freeOneEdgeLimit`: the constant free schedule has the free
  finite-volume law as a genuine `IsFKLimit` (`tendsto_const_nhds`).
* `finiteVolumeLaw_free_ne_wired_oneEdge`: the free and wired finite-volume laws
  differ (their masses on the lift of the open interior configuration are `1/3`
  and `1/2`, reusing `oneEdge_free_allOpen_mass` / `oneEdge_wired_allOpen_mass`).
* `exists_two_fkLimits_oneEdge`: the FK limit class at `q = 2`, `p = 1/2` for
  that exhaustion contains two distinct laws.

So the `q = 1` collapse is a genuine parameter-line phenomenon and not an
artefact of the exhaustion or of the boundary conventions.

## 4. Precise remaining hypotheses (what this does *not* do)

1. Nothing is claimed for `q ≠ 1`.  The interior `q` case still needs the
   Theorem 5.1 machinery (random-region joint-null reverse martingale), the
   Prop. 1.8(2) arbitrary-boundary Gibbs identification, and the AG/`δ'` window
   of Theorem 1.4; `q = 1` bypasses all three because the finite law does not see
   the boundary.
2. Uniqueness only.  Theorem 1.10's conclusion also asserts that the unique law is
   *subcritical*; at `q = 1` the unique law is `Bernoulli(p)` and is
   supercritical for `p > p_c(G)`.  The subcriticality half therefore remains the
   Theorem 1.4/`hdom` input (untouched here), and the `q = 1` uniqueness statement
   must not be read as a subcriticality statement.
3. Integrability: the coordinator must move these files into `FK/` (adjusting the
   `import QOneLine` line) and add their lines to `Audit.lean`; statement names
   were chosen to avoid collisions (`FK.InfiniteVolume.QOne` namespace).

## 5. Provenance of the tools used

`fkPMF_q_one` (`FK/ClassicalOne.lean`), `bernoulliProductPMF_toMeasure`,
`bernoulliProduct_real_interior_preimage` (`FK/NestedFiniteAssembly.lean`),
`conditionalLaw_real_interior_preimage`, `eq_preimage_interiorRestriction_image`,
`apply_of_isDLR` (`FK/ExteriorIdentification.lean`, `FK/InfiniteVolume.lean`),
`map_splitEquiv_bernoulliProduct` (`FK/BernoulliFiniteBox.lean`),
`tendsto_probabilityMeasure_iff_cylinder_real_tendsto` (`FK/ReverseMartingale.lean`),
`ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto` (Mathlib Portmanteau),
`measure_ext_of_eq_on_boolCylinders` (`FK/ClassicalCoupling.lean`),
`eq_of_unique_fkLimit` (`FK/Theorem110Assembly.lean`), `Measure.compProd_const`
(Mathlib), and the component-count/weight lemmas of `FK/FiniteModel.lean` and
`FK/PlanarForestDuality.lean`.
