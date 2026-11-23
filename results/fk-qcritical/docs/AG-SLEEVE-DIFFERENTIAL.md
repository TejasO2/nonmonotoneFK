# Selected-coordinate differential assembly for annular sleeves

## Deliverables

- `AGSleeveDifferential.lean` imports only the public modules `FK.AGSleevedAnnulus` and `FK.AGCurveIntegration` (plus their transitive imports). On integration it can be placed at `FK/AGSleeveDifferential.lean` without changing those imports.
- `Audit.lean` audits the eight principal declarations, with output in `audit-output.txt`.

All declarations are in `FK.AGImplant.Sleeve`. The source has no `sorry`, `admit`, `unsafe`, new axiom, heartbeat override, or `set_option`.

## Verified mathematical content

Let `R = S.card`, let `δ > 0` minorize both Boolean masses of every bond and activation law, and write `μ` for the actual independent `FinProb.pi` bond/activation law. The theorems `openConnected_annulus_sum_edgePivotal_event_mul_le` and `deviceArmEvent_annulus_sum_edgePivotal_event_mul_le` prove

```
δ^R * Σ_{e ∈ S} μ(EdgePivotal A (baseEdge H e))
  ≤ 2^R * R * μ(ActivationPivotal A ()).
```

Here `A` is respectively the actual open-connection device event or `deviceArmEvent`. The factor `R` is intentional: all selected bond pivots map to the same activation pivot.

The new affine Margulis–Russo theorem `hasDerivAt_eventWeight_affine_pivotal` gives the derivative along `r + t*v` as the velocity-weighted sum of pivotal probabilities. `selectedVelocity` is `-c` on the selected base-bond image, `1` on the sole activation, and `0` elsewhere. Hence `hasDerivAt_eventWeight_sleeveLine_pivotal` differentiates only selected base bonds and the activation; added spoke bonds and all unselected bonds stay fixed.

For a nonempty `S` and `0 < a`, `b < 1`, define

```
m(a,b) = min a (1-b)
c(a,b,S) = m(a,b)^R / (2^R * R).
```

On the line

```
bond e     = if e ∈ annulus H S then p - c*t else p
activation = s+t,
```

`deviceArmEvent_sleevePivotSlope_nonneg_of_box` proves

```
0 ≤ -c * Σ_{e ∈ S} eventWeight(EdgePivotal deviceArmEvent (baseEdge H e))
      + eventWeight(ActivationPivotal deviceArmEvent ()),
```

provided `p`, `p-c*t`, and `s+t` belong to `[a,b]`. `eventWeight_sleeveLine_eq_pi` proves that every such unit-cube coefficient is exactly a normalized `FinProb.pi` probability, with no normalization factor omitted.

Finally:

- `monotoneOn_deviceArmEvent_sleeveLine` proves monotonicity on `Icc 0 T` from endpoint membership in the interior box;
- `deviceArmEventWeight_sleeveLine_le` gives the endpoint polynomial comparison;
- `deviceArmEvent_productLaw_sleeveLine_le` gives the same comparison for the actual normalized independent product laws at the two endpoints. Its `hr0` and `hrT` arguments are the Boolean-cube membership witnesses needed to construct those finite laws, not a stochastic comparison hypothesis.

## Validation

Checked directly with the repository's existing `leanprover/lean4:v4.35.0` toolchain, using its existing dependency `.olean` files. I also produced the local `AGSleeveDifferential.olean` in this member directory and checked `Audit.lean` against that build.

Every audited principal theorem reports exactly:

```
[propext, Classical.choice, Quot.sound]
```

The declarations audited are:

1. `openConnected_annulus_sum_edgePivotal_event_mul_le`
2. `deviceArmEvent_annulus_sum_edgePivotal_event_mul_le`
3. `hasDerivAt_eventWeight_affine_pivotal`
4. `hasDerivAt_eventWeight_sleeveLine_pivotal`
5. `deviceArmEvent_sleevePivotSlope_nonneg_of_box`
6. `monotoneOn_deviceArmEvent_sleeveLine`
7. `deviceArmEventWeight_sleeveLine_le`
8. `deviceArmEvent_productLaw_sleeveLine_le`

## Explicit residuals

This is a finite, explicitly constructed sleeved-graph result for one shared activation and one selected annulus. It does **not** construct uniform separated sleeve packings, sum over a packing with finite overlap, interchange derivatives with infinite-volume limits, construct a reference infinite-volume law, or prove an AG critical shift. The nonempty-selection assumption is required for the displayed normalization by `R`; the summed pivot inequality itself does not require nonemptiness.
