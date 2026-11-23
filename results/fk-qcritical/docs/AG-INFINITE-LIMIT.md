# Direction E: infinite-arm limiting layer

`AGInfiniteLimit.lean` imports the public `FK.AGDifferential` development and adds compiling declarations in `FK.AGGadget`.

## Proved

- `le_of_finite_arm_comparison`: if real finite-arm functions satisfy an inequality at every stage and have specified pointwise limits at both parameters, the limiting inequality holds. This is order closedness, not a claimed interchange of derivatives and limits.
- `tendsto_measure_armEvent` and `tendsto_armProb_percolationProb`: on a countable-vertex, connected, locally finite graph, the actual decreasing `armEvent` masses converge by continuity from above to the actual infinite-cluster mass / vendored `percolationProb`.
- `infinitePairedLaw` and `infiniteJointLaw`: normalized independent bond/activation products on an arbitrary edge index type, with no `Fintype` assumption. The latter lives on the same `JointConfig E E` used by the finite AG development.
- `prod_bernoulliMeasure_map_or` and `infiniteJointLaw_map_enhancedConfig`: the exact enhanced marginal is `bernoulliProduct E (orUnit p s)`, where the real value of `orUnit p s` is `p + (1-p)s`. The singleton-mass calculation includes `p,s = 0,1`.
- `infiniteJointLaw_enhancedArmEvent`: the actual `enhancedArmEvent G o n` mass equals `armProb G o (orUnit p s) n`, not a conclusion-shaped substitute event.
- `infiniteJointLaw_enhancedPercolationEvent` and `tendsto_enhancedArmEvent_percolationProb`: the actual enhanced infinite-cluster mass and the enhanced arm limit are exactly the original percolation probability at the effective OR rate.

## Exact residual hypotheses / nonclaims

Using `le_of_finite_arm_comparison` for an AG strict shift still requires (1) a genuinely proved finite-arm curve comparison for every `n`, and (2) pointwise convergence of the real normalized finite-arm functions at both endpoints. Direction D supplies at most item (1); this file does not assume it. The general lemma proves no differentiable limit and no strict positivity from non-strict inequalities alone.

The unconditional enhanced limit theorem takes place under the explicit infinite independent OR product. It does not identify this law with an exhaustion of the finite `jointLaw`s on nested boxes, does not establish a derivative limit, and does not prove arbitrary bounded-range implantation or the AG critical-point shift. Those are separate missing arguments, not hidden premises of the unconditional theorem.

## Verification

Run from `results/fk-qcritical/`, with repository Elan in `../../.scratch/elan` and all generated files confined to this member directory:

```sh
lake env lean ../../.ultramath/smwsrcx3i/m3/AGInfiniteLimit.lean
lake env bash -c 'cd ../../.ultramath/smwsrcx3i/m3 && lean -o AGInfiniteLimit.olean AGInfiniteLimit.lean'
lake env bash -c 'cd ../../.ultramath/smwsrcx3i/m3 && export LEAN_PATH="$PWD:$LEAN_PATH" && lean AGInfiniteLimitAudit.lean'
```

The source check and independent olean build use Lean 4.35.0 and default heartbeats. The audit prints each declaration's exact axioms. No `sorry`, `admit`, `unsafe`, or new `axiom` is used.
