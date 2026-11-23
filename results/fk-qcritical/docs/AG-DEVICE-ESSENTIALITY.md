# Essential bounded-range shared-activation devices

## Proved result

`AGDeviceEssentiality.lean` works in the actual model of
`FK.AGBoundedRangeImplant`: bonds and device activations are separate Boolean
coordinates, and an enhanced bond is open if its ordinary bond is open or an
active device support contains it.

The main local geometric theorem is

```
FK.AGImplant.deviceEssential_of_onDoubleRay
```

For arbitrary device supports and a selected activation `z`, if `support z`
contains an edge `e` lying on a simple double ray, then `z` is genuinely
`ActivationPivotal` for the actual `HasOpenDoubleRay` event.  The definition
`DeviceEssential` packages exactly this infinite-event statement.

The witness is not an abstract pivot hypothesis.  Its bond configuration is the
given double ray with `e` closed, and all activations are initially off.  With
`z` off, `deviceConfig_rayDeviceJoint_off` identifies the one-gap ray
configuration; `not_hasOpenDoubleRay_update_configuration_false` rules out every
double ray.  With `z` on, `deviceConfig_rayDeviceJoint_on_of_mem` opens `e`, and
`deviceConfig_rayDeviceJoint_on_of_not_mem` preserves all other ray bonds, so the
original double ray is open.  Supports of all other devices are arbitrary, and
finiteness of `support z` is not needed for this geometric step.

`allEssential_deviceEssential_of_separated` applies the construction to every
selected device in a separated family.  Three packing theorems then expose the
result for the existing quasi-transitive geometry:

* `exists_separated_essential_template_devices` retains the separated family,
  bounded line-graph distance, cardinality bound and automorphic translate
  witnesses of `exists_separated_template_devices`;
* `exists_separated_essential_star_devices` specializes to actual incidence
  stars and retains the uniform degree bound and star witnesses;
* `exists_separated_essential_cycle_devices` specializes to genuine simple
  cycles and retains the cycle length and walk-support witnesses.

All three return `FK.Theorem14.AllEssential` for the new shared-activation
essentiality predicate.  Thus this is an unconditional bounded-range local
essentiality construction combined with actual quasi-transitive packing, not
the path/star discontinuity example or a restatement of the one-edge OR gadget.

Two further theorems,
`openConnected_annular_edgePivotal_event_mul_le_of_support_subset` and
`deviceArmEvent_annular_edgePivotal_event_mul_le_of_support_subset`, discharge
the annular rerouting interface when every edge of the finite set `R` belongs
to the selected support.  Activation of that device opens each such edge
directly, supplying all endpoint connections required by `hreplace`.  The
conclusions retain the actual independent joint product law, open-connection or
one-arm event, likelihood ratio `δ ^ R.card`, and fibre factor `2 ^ R.card`.

## Precise residual AG blockers

No strict critical-point shift is claimed.  In particular:

1. This handles the repository's fixed-support shared-activation enhancement,
   not an arbitrary range-`r` local enhancement rule.  Support containment is a
   sufficient essentiality criterion for that model.
2. The general annular pivot implication still needs simultaneous replacement
   walks for source-open bonds whose ordinary coordinates are closed.  The new
   bounds solve only the robust special case `R ⊆ support z`; for a general
   annulus, the `hreplace` hypothesis in `AGBoundedRangeImplant` remains the
   precise local geometric interface.  Packing and essentiality alone do not
   construct these sleeves.
3. A reference AG shift additionally requires summing pivot comparisons,
   integration of the differential inequality, and the infinite-volume
   reference-law argument.  None is inferred from double-ray essentiality.

This distinction is mathematically necessary.  Balister–Bollobás–Riordan,
*Essential enhancements revisited* ([arXiv:1402.0834](https://arxiv.org/abs/1402.0834)),
shows that the original annular rerouting figure is false in general and leaves
the general site case open.  The theorem here does not use or assert that
invalid general rerouting claim.

## Independent verification

The module and audit are in this member directory.  `compile.sh` constructs an
independent olean under `.scratch/oleans`; it uses the repository Elan at
`.scratch/elan`, the pinned `leanprover/lean4:v4.35.0`, Lake's computed import
path, and default heartbeats.  `audit.sh` independently elaborates
`AGDeviceEssentialityAudit.lean` against that olean.

Both commands pass.  `AGDeviceEssentialityAudit.txt` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for all 17 principal/helper
declarations.  No shared-results file was edited and no full-project check was
run.
