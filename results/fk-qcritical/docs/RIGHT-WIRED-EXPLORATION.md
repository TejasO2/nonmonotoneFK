# Direction A: ordered exploration and right-wired interiors

This directory is self-contained; shared `results/` files were not edited. The work resumes `smwsl2nwy/m4` by copying its exploration sources here, fixing three real errors, and then extending the construction.

## Main new results

Files `RightWiredEquationNine.lean`, `RightWiredGood.lean`, `RightWiredSequential.lean`, `WiredMaximalStrata.lean`, `WiredStoppedInterior.lean`, `TransportBoundary.lean`, and `WiredRightInterior.lean` form the main new chain.

For finite `U,K`, `m,k`, interior/exterior endpoint lists `si,ti,so,xo`, interior `0<q`, `0<p<1`, `ExteriorHasRight so xo`, two arbitrary boundary setoids `ζ₁,ζ₂ : Setoid K`, and `A : Set (Fin m → Bool)`, put

- `G := ambientOfSum (splitSource si so) (splitTarget ti xo)`;
- `T := transportedAmbient si ti so xo`;
- `A' := (fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A`;
- `C := {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}`;
- `ν := (finIndexedGraph (U ⊕ K) (k+m) T.source T.target).bernoulliProductPMF (upperRateNN_le_one hq hp1.le)`.

The theorem **FK.Exploration.RightWiredEquationNine.equation_nine_rightWired** proves

```
|(rightWiredLaw si ti so xo hq hp1 ζ₁).toMeasure.real A' -
  (rightWiredLaw si ti so xo hq hp1 ζ₂).toMeasure.real A'| ≤ ν.toMeasure.real Cᶜ.
```

This is the shape of paper equation (9), not a wrapper with the good-law equality as a premise. The theorem `config_good_intersection_rightWired` discharges the required good-intersection equality, and `good_intersection_rightWired` proves it by conditioning on each exposed prefix and computing every continuation.

`rightWiredLaw` is the actual normalized FK PMF on transported finite labels with pull-backed right-supported wiring. Its exact semantics on the original sum-labelled graph is recorded by **map_toAmbient_rightWiredLaw**: its pushforward by `toAmbientConfig` is `G.fkPMF hq hp1.le (rightWiredBoundary si ti so xo ζ)`.

The packaged coupling **rightWiredTripleCoupling** has:

- exact first and second right-wired FK marginals (`rightWiredTriple_map_fst/map_snd`);
- exact actual Bernoulli-product upper marginal (`rightWiredTriple_map_thd`);
- pointwise `ω₁ ≤ ω₃` and `ω₂ ≤ ω₃` on support (`rightWiredTriple_ordered`).

## Genuine maximal strata and both interior laws

`MaximalStrata.lean` proves:

- `closedBoundary_right_of_separated`;
- `outerRegion_eq_right_of_separated`;
- `outerRegion_eq_right_iff_separated`;
- `mem_maximalSplitStratum_of_exterior_eq`.

Thus `maximalSplitStratum` is precisely the canonical maximal-region condition, not an assumed cutset certificate, and is stable under changing hidden interior bits.

`WiredMaximalStrata.lean` proves **normalized_maximalStratum_interiors_rightWired**: on the same normalized maximal upper-history event, both continued decoded FK interiors are literally `regionGraph.fkPMF hq hp1.le freeBoundary`. The two coordinates may use different `ζ₁,ζ₂`. Its only positivity witness has exactly the type of **maximalStratum_prefix_support_rightWired**, which supplies the all-closed supported stratum point internally. No free-interior or Markov conclusion is assumed.

## Why different ambient FK laws are allowed

`WiredRightInterior.lean` lets the left/interior vertices have free wiring while the right/exterior vertices have any setoid and there is no cross-summand wiring. It proves the direct graph split `connectionGraph_rightWired_eq_sum`, exact component and weight factorizations, and the filtered ambient law `filter_ambient_fkPMF_eq_map_glue_region_free_rightWired`. `TransportBoundary.lean` extends graph transport to arbitrary pullback boundary setoids (`map_transport_fkPMF`). `WiredStoppedInterior.lean` combines this with the exact canonical-prefix chain rule.

## Resumed-file repairs

The copied prior files now compile independently. Fixes include the direction of `ENNReal.tsum_mul_right` in `ExplorationSequential.bind_eq_self_of_forall_support`, an explicit `exteriorHistory` reduction in `StoppedInterior.normalized_upperStratum_interior`, and the theorem's final `calc` step.

## Verification

Using the repository Elan toolchain `leanprover/lean4:v4.35.0` and its pinned project `LEAN_PATH`, with `.olean` output under this member's `.scratch/oleans`, I deleted the old outputs and rebuilt these 16 targets sequentially at default heartbeats:

`ExplorationSequential`, `CanonicalDisintegration`, `ConditionalRate`, `FKSequentialCoupling`, `StoppedInterior`, `ExplorationTriple`, `MaximalStrata`, `WiredRightInterior`, `TransportBoundary`, `WiredStoppedInterior`, `WiredMaximalStrata`, `RightWiredSequential`, `RightWiredGood`, `RightWiredEquationNine`, `ExplorationAudit`, `RightWiredAudit`.

After adding `map_toAmbient_rightWiredLaw`, I rebuilt that module and all three downstream modules again. All commands exited 0. The final axiom output is in `.scratch/logs/RightWiredAudit.log`; all 25 declarations audited there use only `[propext, Classical.choice, Quot.sound]`. The resumed 29-declaration output in `.scratch/logs/ExplorationAudit.log` has the same three standard axioms. No `sorryAx` is present. A declaration-pattern scan over the `.lean` sources found no `sorry`, `admit`, `unsafe`, or new `axiom` declarations.

## Scope; not claimed as full Lemma 2.1

The result is a finite separated split-graph theorem with free-left/right-supported boundaries. It does **not** cover arbitrary setoids that wire left vertices or cross between left and right. The paper's nested-box instantiation `Λ ⊆ Δ ⊆ Σ`, including identification of the second marginal with `φ_Δ^τ` restricted to `E_Δ`, is not constructed here. The exploration proof is therefore still not full Lemma 2.1, and this work does not claim Theorems 1.4/1.8/1.9/1.10/1.11. It removes the free-interior and good-intersection premises for a strict scoped class, and provides a new nontrivial exact equation-(9) consequence for that class.
