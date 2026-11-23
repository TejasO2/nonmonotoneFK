# Geometric active comparisons with canonical containment admissibility

## Artifact and imports

- `GeometricActiveComparisons.lean` is self-contained new source in this member directory.
- Its only direct import is exactly `import FK.CycleBoundaryLowerPaths`. This supplies the integrated `StarBoundaryCutset`, `CycleBoundaryPaths`, `CycleBoundaryLowerPaths`, and (transitively through `StarBoundaryCutset`) `FKQuasiTransitiveDevices` declarations. No source was copied from `GlobalFiniteEnergy`, `NestedFiniteCoupling`, `PrimalOpenBoundary`, or any other member artifact.
- `GeometricActiveComparisons.compile.log` is the successful Lean 4.35.0 check and exact `#print axioms` output.

## Proved content

1. `ContainedAdmissible` sets finite-volume admissibility to containment of the entire finite device in the current box. `eventually_containedAdmissible` proves the condition eventually from `BoxExhaustion.eventually_subset`; no activation axiom or extra eventual hypothesis is introduced.
2. `mem_activeEdges_containedAdmissible` and its separated-family strengthening identify the exact activated-edge semantics. For separated devices, activation is equivalent to selection of the pivot plus containment of its whole device. `eventually_mem_activeEdges_containedAdmissible` proves eventual activation of every selected pivot.
3. `lt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained` fills the missing `q < 1` geometric DLR assembly: the lower Bernoulli product dominates the DLR law via actual star cutsets, and the DLR law dominates the upper product via actual complementary cycle paths, in the orientation defined by `FKLimit.StochasticallyDominates`.
4. `gt_dlr_sandwich_of_geometric_star_cyclePathFamily_contained` supplies the reverse-prime (`q > 1`) comparisons with the same canonical admissibility: lower cycle comparison, then upper star comparison.
5. The two `*_of_quasiTransitive_contained` theorems instantiate the existing genuine automorphism-packing constructors. Their existential conclusions retain separated families, bounded-line-graph-distance supply, uniform `Delta`/`L` cardinality bounds, actual incidence-star witnesses, actual cycle-walk witnesses, and the two exact stochastic comparisons. They do not merely quantify over abstract comparison premisses.

All eight declarations above have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom dependencies: the two general admissibility/activation lemmas, the separated activation and eventual activation lemmas, the two geometric sandwiches, and the two quasi-transitive sandwiches. See the audit section of the Lean source and its compile log for the exact outputs.

## Verification

Run from `results/fk-qcritical`:

```bash
export ELAN_HOME=../../.scratch/elan
export PATH="$ELAN_HOME/bin:$PATH"
lake build FK.CycleBoundaryLowerPaths
lake env lean ../../.ultramath/smwsv3inm/m2/GeometricActiveComparisons.lean
```

The first command was the only imported-target build; the second checks the new file with default heartbeats and prints all eight principal audits. `lean --version` reported 4.35.0. No `set_option maxHeartbeats`, `sorry`, `admit`, `unsafe`, or new axioms occur in the new source.

## Explicit residual scope

- The probabilistic input is an already supplied DLR law for the selected geometric boundary assignment. Existence, uniqueness, weak-limit transport, and endpoints `p = 0`, `p = 1`, `q = 1` are not addressed.
- The theorem still requires `0 < p < 1`, interior `q` with the indicated strict inequality, `Nonempty (exh.box n).edges` for every `n`, compatible `SimpleGraphBoxData`, injectivity of every local vertex map, and geometric validity `hΦ` of the boundary assignment.
- Star singleton-center wiring is derived from `hΦ`, complete star containment, and local-global vertex-map injectivity; no arbitrary-wired-setoid claim is made. Cycle auxiliary paths are the existing genuine lifted complementary cycle walks.
- The quasi-transitive corollaries assume connectivity, local finiteness, countability hypotheses, quasi-transitivity, and a seed double-ray edge incident to the chosen star center and contained in the supplied seed cycle. These graph facts are not derived anew.
- Only canonical complete-device containment admissibility is discharged. Other application-specific admissibility predicates remain possible inputs to the older general APIs.
- These are stochastic DLR comparison theorems, not an Aizenman–Grimmett strict critical-point shift and not a relabelled full Proposition 4.2 or Theorem 1.4.
