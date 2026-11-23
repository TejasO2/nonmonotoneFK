# Stage 18, direction 8 — Theorem 1.10/1.9 subcritical assembly

## Coordinator integration note

The public module names are `FK.Theorem110Assembly` and `FK.SubcriticalPercolation`; only the latter's worker-local import changed. `FK.InfiniteVolume.FKFamily` is a family over **all** measurable boundary assignments on one selected exhaustion, expressly larger than an exhaustion-independent paper family. Compactness is proved only for a suitable sub-exhaustion, not for an adversarially prescribed one. Endpoint singleton theorems are unconditional but do not fill the interior-rate gaps.


Direction: *source-faithful main-theorem synthesis from available inputs*.
Target taken: **Theorem 1.10** (and its input Theorem 1.9) of
arXiv:2512.16486v1, in the form "strong uniqueness when
`max (p, p') < p_c (G) + δ'`, and the unique FK measure is subcritical".

Everything here is compiled against the pinned project
`results/fk-qcritical` (Lean 4.35.0, project `.lake` build) with **no**
`sorry` / `admit` / `axiom` / `unsafe`.  Audit output is in
`audit18-output.txt`; every new declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## 1. What is proved

### 1.1 Subcritical Bernoulli percolation does not percolate

`CurvatureVariance.Infra.Percolation.criticalProb` is defined in the repository
as `sSup {p : I | θ (p) = 0}`.  The repository used, but never derived, the link
`s < p_c → θ (s) = 0`: it appears only as the *hypothesis* `hzero : ∀ x,
percolationProb G x p = 0` of
`FK.InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero`
(used by `NestedMetricGeometry`, `NestedMetricConditionalAssembly`,
`NestedBadRootArmVanishing`).  That link is supplied here.

* `isUpperSet_infiniteOpenCluster`, `measurableSet_infiniteOpenCluster`:
  `{ω | cluster of o infinite}` is a measurable upper set.
* `percolationProb_mono` : `p ≤ q → θ_o (p) ≤ θ_o (q)`, from the proved
  stochastic domination of infinite Bernoulli products with ordered parameters
  (`FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le`) plus
  `FK.EssentialWindow.measure_le_of_stochasticallyDominates`.
* `percolationProb_eq_zero_of_lt_criticalProb` : `s < criticalProb G o → θ_o (s) = 0`.
  Contrapositive: if `θ (s) ≠ 0`, monotonicity kills every zero of `θ` above
  `s`, so `p_c = sSup {θ = 0} ≤ s`.  This uses `Real.sSup_le`, so no
  nonemptiness of `{θ = 0}` is needed (this is why the proof avoids `θ (0) = 0`).
* `FK.ae_nonPercolating_percolation_of_lt_criticalProb` : below `p_c` at every
  root, `percolation G s` is a.s. non-percolating (composed with the existing
  `ae_nonPercolating_percolation_of_percolationProb_eq_zero`).
* `FK.ae_nonPercolating_of_orderedCoupling` : one-sided domination transfer of
  non-percolation (the existing `ae_nonPercolating_of_orderedTripleCoupling`
  needs *two* lower laws sharing an upper marginal; the paper's step needs one).
* `FK.ae_nonPercolating_of_dominated_by_subcritical` : any law monotonically
  coupled below a subcritical Bernoulli law is a.s. non-percolating.  This is
  the paper's "This implies that `φ`-a.s. there is no infinite cluster".
* `FK.InfiniteVolume.ae_nonPercolating_of_subcritical_domination` : the same
  statement uniformly over every FK limit measure of an exhaustion
  (`FKLimitMeasures exh hq hp`), i.e. the subcritical half of Theorem 1.10.

### 1.2 Strong uniqueness ⟺ uniqueness of the FK limit measure

The paper states after Proposition 1.8: "strong uniqueness is equivalent to the
uniqueness of the FK limit measure".  This is formalized.

* `FKFamily exh hq hp` : `⋃_Φ 𝒢^Φ ∪ 𝒲`, the union of every measurable
  boundary-convention DLR class with the weak-limit class.  The union is over
  *all* measurable boundary assignments (coherent or not), so it is larger than
  the paper's `FK (p,q)`; the result is therefore the stronger one.
* `eq_of_unique_fkLimit` : if every FK limit measure equals `μ₀`, then every
  member of `FKFamily` equals `μ₀`.  Uses the proved Proposition 1.8(1)
  inclusion `mem_fkLimitMeasures_of_extremal_dlr` and the proved tail Choquet
  decomposition `eq_dlr_of_extremal_unique`.  No class is assumed nonempty.
* `eq_of_unique_fkFamily` : the converse direction.
* `existsUnique_fkFamily_iff_existsUnique_fkLimit` : the `∃!` form.  The only
  extra input is `(FKLimitMeasures exh hq hp).Nonempty`, the standard
  compactness fact; it is *not* proved in the repository (see §3).

### 1.3 Theorem 1.10 modulo three named inputs

`FK.InfiniteVolume.theorem_1_10_modulo_theorem_5_1` and
`FK.InfiniteVolume.theorem_1_10_modulo_inputs` assemble the conclusion of
Theorem 1.10 from

1. `hdom` — the domination conclusion of Theorem 1.4(1) (through Theorem 1.2 and
   the enhanced comparisons) at a Bernoulli parameter below `p_c`;
2. `h5_1` — **Theorem 5.1** of the paper for one convention: its DLR class is a
   singleton (`DLRMeasures exh Φ hq hp = {μ₀}`);
3. `h518` — **Proposition 1.8(2)**: every FK limit measure is Gibbs for that
   convention.

The conclusion is `∃! μ, μ ∈ FKFamily` **and** `μ₀` is a.s. non-percolating.
The second half needs only (1) (plus (2),(3) to place `μ₀` in the limit class),
and the first half needs only (2),(3) — the two halves use disjoint inputs.
Neither input restates the conclusion: (2) is about a single convention class,
(3) is a Gibbs-property statement, while the conclusion is about the union over
*all* conventions.

### 1.4 Unconditional instances (non-vacuity of the assembly)

`fkFamily_zero_eq_singleton` : at `p = 0` the total FK family is exactly the
all-closed point mass, for every `q > 0` and every exhaustion.
`fkFamily_one_eq_singleton` : at `p = 1` it is exactly the all-open point mass.

These are complete instances of the paper's strong uniqueness with no remaining
input: every convention class collapses because the finite FK law at an endpoint
rate is a point mass independent of the boundary partition
(`ConventionTransport.dlrMeasures_zero_eq_singleton`,
`..._one_eq_singleton`), and every weak limit collapses by
`EndpointIntegration.limitOrGibbs_eq_closedLaw_zero` / `..._openLaw_one`.
They also show that the union `FKFamily` (all measurable assignments, coherent or
not) is the right total family.

## 2. Source faithfulness

* Theorem 1.10 (`paper-v1.html`, §1.3 and §5.1): "there exists `δ' > 0` such that
  one has strong uniqueness when `max (p,p') < p_c(G) + δ'` and the unique FK
  measure is subcritical".  Our conclusion has exactly these two components.
* Proposition 1.8(1)/(2) and the sentence relating strong uniqueness to
  uniqueness of the FK limit measure are the basis of §1.2.
* Theorem 5.1 ("Uniqueness through domination by a subcritical percolation") is
  the single remaining community input; §3 records exactly what a faithful
  formalization of it still needs.
* The `δ'` window itself (Theorem 1.4(1), hence the AG reference shift) is not
  touched here; `hdom` is its domination consequence, stated as an explicit
  input with the parameter `s < p_c` visible.

## 3. Residuals (what is *not* proved, precisely)

**(R1) Theorem 5.1 of the paper.**  `h5_1` above.  Its proof needs, for two
extremal Gibbs measures `μ₁, μ₂` and a monotone triple coupling with a
non-percolating upper law `ℙ`:

* the closed-boundary exhaustion of the upper configuration, giving finite
  regions `S_n (ω₃) ↑ G` with `ω₃ | ∂S_n = 0`;
* at such a region, both conditional laws are the same free finite-volume FK
  law, so the conditional masses of every cylinder agree eventually;
* reverse-martingale convergence along `n ↦ S_n (ω₃)` with limit the tail
  conditional, which is `μ_i (C)` by tail triviality of extremal laws.

Three concrete obstructions were identified in the current codebase:

1. **No boundary-edge notion in `FiniteBox`.**  `FiniteBox` records only the
   interior edge finset `edges`, the vertex type and `source`/`target`; the
   boundary is encoded solely in the *setoid-valued* `BoundaryPartition`.  So
   "`ω | ∂Λ = 0`" is not expressible at the `FiniteBox` level, and the paper's
   step "closed boundary ⇒ convention partition is discrete" has no statement
   to attach to.  The graph-level notions live elsewhere (`FK.ClosedBoundary`
   vertex regions, `ConventionGeometry.exteriorOpenSetoid`,
   `AllBoxSimpleGraphBoxData.geometry` with
   `openPathSetoid G (closeInside B η) Set.univ (data.vertex B)`), and the bridge
   from a `ClosedBoundary` vertex region to a `FiniteBox` with the matching
   `AllBoxSimpleGraphBoxData` embedding is not constructed.
2. **No measurability of the closed-boundary exhaustion in `ω`.**  The
   construction of `ClosedBoundaryExhaustion` in `FK.ClosedBoundary` is
   deterministic given a non-percolating `ω`, but no measurability statement for
   `ω ↦ S_n (ω)` is available.  Without it the "a.e. in the coupling" step (which
   is what replaces the false expectation identity
   `∫ μ_i (C | ℱ_{S_n^c}) dμ_i = μ_i (C)`) cannot be justified: the null set of
   the reverse martingale depends on the random region.
3. **Reverse martingale along a random exhaustion.**  Each fixed `ω₃` gives a
   decreasing sequence of σ-algebras `ℱ_{S_n (ω₃)^c}`, so the existing reverse
   martingale theorem applies fibrewise; the fibrewise-null sets must then be
   assembled into one joint-null set, which is exactly the measurability
   statement of (2).  `FK.ConditionalLimitUniqueness` has the final
   measure-theoretic step (`CommonConditionalLimits` ⇒ equality) but with the
   conditional-limit sequences supplied as an input; `FK.NestedBoundaryUniqueness`
   does the same along a *fixed* exhaustion with a vanishing-coupling-error
   hypothesis.

**(R2) Nonemptiness of the FK limit class.**  `exists_boxExhaustion_fkLimitMeasures_nonempty`
proves `∃ exh', (FKLimitMeasures exh' hq hp).Nonempty`: compactness of
`ProbabilityMeasure (Configuration E)` (an instance available here, used by
`ReverseMartingale.tendsto_probabilityMeasure_of_cylinder_tendsto`) gives a
convergent subsequence of any sequence of finite-volume laws, and the
subsequence is a genuine `BoxExhaustion`.  What is *not* available is
nonemptiness for an arbitrary *fixed* exhaustion: `IsFKLimit` demands
convergence along the whole sequence `n ↦ exh.box n`, and the per-box boundary
partitions can be chosen adversarially, so sequential compactness does not
apply.  This is why `hne` remains an explicit hypothesis in the fixed-exhaustion
`∃!` statements.  It also shows that the paper's exhaustion-independent `𝒲`
cannot be literally identified with `FKLimitMeasures exh` for one fixed `exh`.

**(R4) Strassen's theorem (domination as a coupling).**  `hdom` above is stated
in *coupling* form, which is the form the paper's proof of Theorem 5.1 uses
("it is possible to find a coupling `(ω₁,ω₂,ω₃)`").  The repository proves
Theorem 1.2's comparison inequalities in the *event* form
(`FKLimit.StochasticallyDominates`, `FK.Phases.StochLe`) and only the easy
direction of Strassen (`stochasticallyDominates_of_coupling`).  Passing from
event domination to an ordered coupling is Strassen's theorem, which is not
formalized (neither on a finite Boolean product, where it is finite max-flow /
Hall, nor in the infinite case, where it needs Prokhorov tightness plus a
diagonal argument).  Both `ae_nonPercolating_of_subcritical_domination` and
`theorem_1_10_modulo_inputs` therefore take `hdom` as an explicit input rather
than deriving it from the proved comparison inequalities.

**(R3) Proposition 1.8(2) for arbitrary-boundary weak limits.**  The `h518` input
above.  The repository proves the all-box Gibbs transport
`CoherentAllBoxes.mem_allBoxDLRMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one`,
which starts from limits of *convention-generated* conditional laws
`(exh.box n).conditionalLaw hq hp (Φ.partition n) (η n)` for a fixed exterior
sequence `η`.  The paper's `𝒲` allows an arbitrary sequence of boundary
partitions `α_n`, and the identification of such arbitrary-boundary limits with
convention-generated ones is not in the repository (and is not immediate: for
fixed `n` different `α_n` give genuinely different finite-volume laws).

## 4. Files

| file | contents |
|---|---|
| `Theorem110Assembly.lean` | `FK.ae_nonPercolating_of_orderedCoupling`; `FKFamily`; `freeAssignment`; `eq_of_unique_fkLimit`; `eq_of_unique_fkFamily`; `existsUnique_fkFamily_iff_existsUnique_fkLimit`; `theorem_1_10_modulo_theorem_5_1`; `fkFamily_zero_eq_singleton`; `fkFamily_one_eq_singleton`; `exists_boxExhaustion_fkLimitMeasures_nonempty` |
| `SubcriticalPercolation.lean` | `isUpperSet_/measurableSet_infiniteOpenCluster`; `percolationProb_mono`; `percolationProb_eq_zero_of_lt_criticalProb`; `ae_nonPercolating_percolation_of_lt_criticalProb`; `ae_nonPercolating_of_dominated_by_subcritical`; `ae_nonPercolating_of_subcritical_domination`; `theorem_1_10_modulo_inputs` |
| `Audit18.lean`, `audit18-output.txt` | exact `#print axioms` report for all 18 declarations |

Notation `FK` for a total FK family collides with the project's root namespace
`FK`; if these declarations are integrated, `FKFamily` should be renamed (for
example `FK.InfiniteVolume.FKTotalFamily`) and moved into `FK/` with its own
documentation entry and `Audit.lean` lines.

## 5. Build and audit

```bash
# project toolchain (Lean 4.35.0), no writes into the project tree:
LEAN_PATH=<fk-qcritical>/.lake/build/lib/lean:<each .lake/packages/*/.lake/build/lib/lean> \
  ~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -o /tmp/x.olean Theorem110Assembly.lean
```

Compile order: `Theorem110Assembly.lean`, then `SubcriticalPercolation.lean`,
then `Audit18.lean`.  Each takes about 2.5 s on this VM.  Nothing was written
inside `results/fk-qcritical`; the project's `.lake` build was used read-only.
