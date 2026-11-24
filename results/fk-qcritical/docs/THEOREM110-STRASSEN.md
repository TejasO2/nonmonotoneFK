Public modules: `FK.Theorem110Strassen`, `FK.Theorem110GeomFamily`, `FK.Theorem110Scope`, and `FK.Theorem110OneEdgeInstance`, with only inter-module imports renamed. The 58 declarations were independently rebuilt and audited with standard axioms. The containment `FKFamilyGeom ⊆ FKFamily` is proved, while the unrestricted union is **not** equated to the paper family: it can be non-singleton. This is a broad scoped assembly and a fully discharged one-edge instance; it is not an unconditional final-form Theorem 1.10 on arbitrary graphs.

# Stage 21, direction 8 — Theorem 1.10 assembly with the coupling input discharged

Member `m1`, swarm `smwu4rrf3`.  Target taken: **Theorem 1.10** of
arXiv:2512.16486v1 (and its Theorem 5.1 input), in the form "strong uniqueness
when `max (p,p') < p_c(G) + δ'`, and the unique FK measure is subcritical".

Everything below is compiled against the pinned project `results/fk-qcritical`
(Lean 4.35.0, project `.lake` build used read-only) with **no** `sorry`,
`admit`, custom axiom, `unsafe`, `native_decide`, or heartbeat override.  Audit
output is `audit-output.txt`: 58 declarations, each depending only on
`propext`, `Classical.choice`, `Quot.sound`.

## Files

| file | content |
|---|---|
| `Theorem110Strassen.lean` | Bernoulli reference law; coupling form ↔ event form (Strassen); event-form non-percolation transfer; `hdom` derived; Theorem 1.10 with `hdom` removed; exhaustion-independent family and theorem; 𝒲-nonemptiness after coarsening |
| `Theorem110GeomFamily.lean` | geometric convention subtype; geometric extremal DLR laws are geometric limits; `FKFamilyGeom`; Choquet uniqueness transfer inside the geometric class; Theorem 1.10 for the geometric family; containment `FKFamilyGeom ⊆ FKFamily` |
| `Theorem110Scope.lean` | exact one-edge computations at `q = p = 1/2`; free ≠ wired limits; unrestricted family is not a singleton; `p_c = 1` on the two-vertex graph; the wired convention is not geometric; the geometric family excludes the wired member |
| `Theorem110OneEdgeInstance.lean` | one-box DLR equation (`conditionalLaw_isDLR`, new and reusable); measure-level injectivity of the interior restriction; free DLR class on the one-edge exhaustion is a singleton; Bernoulli domination at `s = 2/3`; **`theorem_1_10_oneEdge`** — the assembled Theorem 1.10 with every input discharged on that example |
| `Audit.lean`, `audit-output.txt`, `check.sh` | axiom audit and rebuild script (`./check.sh`, ≈ 9 s warm) |

Build: `./check.sh` (uses
`/workspace/nucleus/work/home/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`
and `$(cat /workspace/nucleus/work/home/.fk_lean_path)`; writes only into this
directory).  To integrate, place the four modules under `FK/` and rewrite
`import Theorem110Strassen` / `import Theorem110GeomFamily` (and the
`import Theorem110Scope` / `Theorem110OneEdgeInstance` chain) to the `FK.` names.

## 1. Residual (R4) of `docs/THEOREM110-ASSEMBLY.md` is closed

The stage-18 assembly took as an input

```
hdom : ∀ φ ∈ FKLimitMeasures exh hq hp,
  ∃ γ, γ.map Prod.fst = φ ∧ γ.map Prod.snd = percolation G s ∧ γ-a.e. z.1 ≤ z.2
```

because the FK comparison theorems of the development produce the
*increasing-event* form (`FKLimit.StochasticallyDominates`) and the passage to a
coupling is Strassen's hard direction, which was not formalized then.

`FK/StrassenCountable.lean` now proves Strassen's hard direction on the
countable product.  This file packages it at the project convention:

* `bernoulliRef G s` — the subcritical Bernoulli reference law as a
  `ProbabilityMeasure (Configuration G.edgeSet)`;
* `BernoulliDominates G s φ` — the `ℝ≥0∞`-valued event form;
  `bernoulliDominates_iff_stochasticallyDominates` identifies it with
  `FKLimit.StochasticallyDominates` (both directions, through
  `ENNReal.toNNReal_le_toNNReal` and `ProbabilityMeasure.coeFn_def`);
* `exists_orderedCoupling_percolation_iff` — **coupling form ↔ event form**, via
  `CountableStrassen.strassen_iff` (the `IsProbabilityMeasure` side condition of
  Strassen is recovered from the marginal equation);
* `subcritical_domination_coupling_form` — exactly the `hdom` above, derived;
* `ae_nonPercolating_of_bernoulli_domination` — the paper's step "`φ`-a.s. there
  is no infinite cluster" straight from the event form, with **no** coupling:
  `NonPercolating G` is a lower set, so its complement is a measurable upper set
  on which the Bernoulli law vanishes below `p_c`;
* `theorem_1_10_of_subcritical_domination_inequality` — Theorem 1.10 with `hdom`
  replaced by the proved comparison (`hstoch`).

So the two formulations of the domination input are *equivalent*: neither hides
an extra hypothesis, and the assembly no longer needs an unexplained coupling.

## 2. Exhaustion-independent statement and 𝒲-nonemptiness

The paper's family is `⋃_Φ 𝒢^Φ ∪ 𝒲` with `Φ` ranging over boundary conditions
and `𝒲` over weak limits, neither attached to a fixed exhaustion.  The
repository's `FKLimitMeasures exh` is attached to one `exh` (and `BoxExhaustion`
fixes the whole sequence of boundary assignments).

* `FKFamilyAll` — the union of `FKFamily exh` over **all** box exhaustions;
* `theorem_1_10_exhaustion_independent` — strong uniqueness of `FKFamilyAll`
  plus a.s. non-percolation of the unique measure, from inputs quantified over
  every exhaustion: `hne` (limit class nonempty), `hstoch` (event-form
  comparison), `h5_1` (Theorem 5.1 for every convention) and `h518`
  (Proposition 1.8(2): every limit is Gibbs for some convention);
* `exists_subexhaustion_isFKLimit_of_assignments` — for an **arbitrary** sequence
  of boundary conventions on a fixed exhaustion, some coarsening has a genuine
  FK weak limit.  This is the source-faithful nonemptiness of `𝒲`; the existing
  `exists_boxExhaustion_fkLimitMeasures_nonempty` only covered the constant free
  assignment.

## 3. Exact scope obstruction: the unrestricted family is *not* the paper's family

Stage 18 used `FKFamily` = union over **all** measurable setoid-valued boundary
assignments, calling it "larger, therefore stronger".  That is wrong, and this
is now a theorem rather than a caveat.

On the two-vertex graph with one edge, the constant-box exhaustion
`oneEdgeExhaustion`, at `q = p = 1/2` (so `q < 1`):

* `criticalProb_twoVertex` : `p_c = 1` on this graph, so `p = 1/2` is deep in the
  subcritical range of the paper;
* `oneEdge_free_allOpen_mass_half` : the free finite FK law gives the edge mass
  `2/3`; `oneEdge_wired_allOpen_mass_half` : the wired law gives `1/2`; hence
  `oneEdge_free_fkMeasure_ne_wired_half`;
* `freeOneEdgeLimit`, `wiredOneEdgeLimitHalf` : the two constant-boundary
  finite-volume limits, both genuine FK weak limits
  (`isFKLimit_freeOneEdgeLimit`, `isFKLimit_wiredOneEdgeLimitHalf`);
* `freeOneEdgeLimit_ne_wiredOneEdgeLimitHalf` : they differ (through
  `interiorRestriction`);
* `fkLimitMeasures_oneEdge_not_existsUnique`,
  `fkFamily_oneEdge_not_existsUnique`,
  `fkFamilyAll_oneEdge_not_existsUnique` : consequently the class of FK limits,
  the total family, and the exhaustion-independent family all fail to be
  singletons — **for every choice of parameters the assembly could make**, since
  these are statements about the family itself.

The wired constant boundary setoid is not induced by any exterior configuration
of this exhaustion: `not_isGeometric_wiredConstantAssignment` proves that no
`IsGeometric` assignment (Proposition 1.6: merge open exterior components,
separate distinct finite exterior components) can be the wired one, because the
unique exterior configuration has all box edges closed.

### The corrected family

* `FKFamilyGeom exh data` — union of the DLR classes of geometric conventions
  with the **geometric weak limits** `IsGeometricFKLimit` (limits along
  `n ↦ Φ.partition n (η n)` for geometric `Φ`);
* `fkFamilyGeom_subset_fkFamily` — the containment that makes the stage-18 claim
  precise: it was a *stronger* statement about a bigger family, and it is false;
* `exists_isFKLimit_of_geometric_extremal` — Proposition 1.8(1) *inside the
  geometric class*: the witness sequence produced by the reverse-martingale
  theorem is `n ↦ Φ.partition n (η n)`, so extremal DLR laws of geometric
  conventions are geometric limits;
* `eq_of_unique_geometricFKLimit` — singleton geometric limit class forces the
  geometric family to be that point (Choquet over the geometric class);
* `theorem_1_10_geometric_family` — Theorem 1.10 for the geometric family:
  strong uniqueness plus a.s. non-percolation of the unique measure, from
  `hne`, `hstoch`, `h5_1` and `h518`, all over geometric conventions;
* `wiredOneEdgeLimitHalf_not_mem_fkFamilyGeom` — the correction actually repairs
  the one-edge example: every geometric convention of that exhaustion is the
  free one (`geometric_partition_eq_free`), every geometric limit is the free
  limit (`isGeometricFKLimit_eq_freeOneEdgeLimit`), and the spurious wired member
  is excluded.

Conclusion to record for the campaign: **a uniqueness conclusion in this
development must quantify the convention family geometrically
(`IsGeometric`), not over all measurable setoids.**  The unrestricted version is
false at interior parameters, independently of any percolation input.

## 4. The remaining analytic obstruction, exactly

After this stage the assembly's inputs are:

1. **`h5_1` — Theorem 5.1** of the paper: under domination by a subcritical
   Bernoulli law, the geometric DLR class of one convention is a singleton.
   The paper proves it by running, for two extremal DLR laws `μ₁, μ₂` and one
   ordered triple coupling `(ω₁, ω₂, ω₃)` with non-percolating `ω₃`, the
   conditional laws at the random closed region `S_n(ω₃)`.  What the repository
   lacks is exactly:

   * the disintegration identity `μᵢ(· | ℱ_{S_n(ω)ᶜ})(ω) =` free finite-box FK
     law on the random region `S_n(ω)` — `FK.RandomClosedBoundary` constructs the
     region and its measurability and
     `FK.RegionFiniteBox.interiorFKMeasure_eq_free` identifies the finite
     specification with the free law, but the conditional-law identity along a
     *random* box is not proved;
   * the joint-null assembly: fibrewise reverse-martingale convergence gives a
     null set depending on the random region; converting it into one null set of
     the coupling needs the measurable selection of `n ↦ S_n(ω)`
     (`FK.ConditionalLimitUniqueness` supplies the final step only with the
     conditional-limit sequences as an input, and
     `FK.NestedBoundaryUniqueness` does it along a *fixed* exhaustion).

   Both are analytic/probabilistic, not combinatorial; nothing in the present
   file assumes them.

2. **`h518` — Proposition 1.8(2)**: every geometric weak limit is Gibbs for the
   selected convention.  `FK.CoherentAllBoxes*` proves this from a source
   representation by the convention's own conditional laws plus global
   uniqueness; the unrestricted version is *refuted* by
   `FK.NoncoherentCounterexample.wiredOneEdgeLimit_not_mem_free_dlr`, and the
   geometric version is open (the one-edge example does not refute it: there all
   geometric limits are the free law).

3. **`hne`** — nonemptiness of the (geometric) limit class.  For limits taken
   after coarsening this is now free: `exists_subexhaustion_isFKLimit_of_assignments`.

Parameter scope in every statement above: `q > 0`, `0 < p ≤ 1`, and a Bernoulli
rate `s` with `(s : ℝ) < p_c(G, x)` at **every** vertex `x`; the family is
`FKFamilyGeom` (geometric conventions and geometric limits), and the conclusion
includes both the singleton statement and a.s. non-percolation of the unique
measure.

## 5. A non-vacuous instance at interior parameters

`Theorem110OneEdgeInstance.lean` discharges **all four** inputs of
`theorem_1_10_geometric_family` on the two-vertex graph at `q = p = 1/2`
(`p_c = 1`, so `p` is subcritical; `s = 2/3` and `2/3 < 1`):

* `conditionalLaw_isDLR` — a finite-volume conditional law is DLR for its own
  boundary assignment (`map split = dirac η ⊗ₘ fkKernel`).  This one-box
  equation was missing from the repository and is what makes `DLRMeasures`
  nonempty in concrete cases;
* `map_interiorRestriction_injective` — on a box already containing every edge
  of the graph, `interiorRestriction` is injective on measures (the exterior is
  a subsingleton and `glue` inverts it), so the interior FK law determines the
  global law;
* `dlrMeasures_oneEdge_free_singleton` — the free geometric convention has
  exactly one DLR law, namely `freeOneEdgeLimit`;
* `bernoulliDominates_oneEdge` — the free limit is below Bernoulli percolation
  at rate `2/3` on every increasing event (three cases: `∅`, `{allOpen}`,
  `univ`, with the exact masses `0`, `2/3`, `1`);
* `theorem_1_10_oneEdge` — the conclusion of Theorem 1.10 on this example: the
  geometric family is the singleton `{freeOneEdgeLimit}` and the unique law is
  a.s. non-percolating.

This is the same one-edge exhaustion on which the **unrestricted** family fails
(§3), so the example separates the two families and shows the geometric
restriction is exactly the one that makes the paper's conclusion true.

## 6. What is *not* claimed

* No unconditional theorem 1.10: `h5_1` and `h518` remain inputs.
* No claim that the one-edge example is a counterexample to the paper's Theorem
  1.10; it is a counterexample to the *unrestricted* family used at stage 18,
  and the reason is exactly that the wired boundary condition is not realizable
  by an exterior configuration.
* The stage-18 inclusions (`eq_of_unique_fkLimit`, Choquet decomposition,
  reverse martingale along a fixed exhaustion) are used as they are; nothing
  here reproves or duplicates them.
