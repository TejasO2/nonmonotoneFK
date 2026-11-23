# Enhanced finite-to-infinite comparison transport

These modules implement both the DLR and genuine FK weak-limit cases of
Proposition 4.2 from explicit finite star/cycle devices, plus generic rate-exact
transports for all four enhanced comparison branches. They do not claim Theorem
1.4, an AG strict critical shift, or construction of the graph devices.

## DLR active-device sandwiches

`FK/Proposition42Interior.lean` proves
`lt_dlr_sandwich_of_active_devices_interior` for interior `q < 1` and
`gt_dlr_sandwich_of_active_devices_interior` for interior `q > 1`. Their
conclusions use the existing `ltLowerParameters`, `ltUpperParameters`,
`gtLowerParameters`, and `gtUpperParameters` profiles in the orientation
`lower ≼ μ ≼ upper`.

The callers supply the actual DLR class, nonempty boxes, separated device
families, eventual admissibility, finite cutsets/paths with cardinality bounds,
and the path connection semantics. They do not supply finite stochastic
domination, equality with an exterior Bernoulli product, enhanced-rate bounds,
active-product convergence, clocks, schedules, or a proof of the strict
prime-parameter direction. The canonical finite FK comparisons supply those
steps internally.

The four separate declarations are in `FK/Proposition42DLR.lean`:

- `lt_dlr_lower_of_active_star_devices`;
- `lt_dlr_upper_of_active_cycle_devices`;
- `gt_dlr_lower_of_active_cycle_devices`;
- `gt_dlr_upper_of_active_star_devices`.

## Measure-theoretic mechanism

`FK/DLRCylinderTransport.lean` observes that the enhanced-product probability
of a box-supported event is independent of the exterior fibre. The existing
DLR compProd equation therefore yields a comparison with an arbitrary exterior
marginal. It never equates incompatible exterior laws.

`FK/WeakLimitCylinderTransport.lean` applies the box-local comparison to
`IsFKLimit`, using genuine weak convergence on finite-coordinate clopen events.
It proves four actual weak-limit declarations:

- `fkLimit_lower_cutset_comparison_of_rate_bound`;
- `fkLimit_upper_cutset_comparison_of_rate_bound`;
- `fkLimit_upper_path_comparison_of_rate_bound`;
- `fkLimit_lower_path_comparison_of_rate_bound`.

These retain exact coordinatewise enhanced-rate bounds and eventual
cylinder-profile equality as generic transports.

`FK/FKWeakLimitActiveDevices.lean` subsequently discharges both inputs in the
active-device setting. It proves the four `*_fkLimit_*_of_active_*_devices`
comparisons and both `*_fkLimit_sandwich_of_active_devices_interior` packages
using `IsFKLimit` directly. The active-product identity
`eventually_bernoulliProduct_active` and exact finite star/cycle rate bounds are
proved inside these declarations. Device existence and the AG strict shift are
still not supplied.

## Adapters and estimates

`FK/EnhancedProducts.lean` proves the exact Bool/Fin2 measure adapters and
finite-product monotonicity. `FK/ActualDLRComparisons.lean` instantiates the
actual canonical finite comparisons. `FK/DeviceBounds.lean` derives cutset and
path bounds from explicit closed/open cylinders with exact cardinality powers.
Labelled multigraphs and arbitrary boundary setoids are preserved.

## Verification and scope

The eight modules are public through `FK.lean`; sixteen principal final
declarations are audited in `Audit.lean`. Independently, every module was
compiled against
the pinned Lean 4.35 environment using the default heartbeat setting. All 51
module-level axiom reports used only `propext`, `Classical.choice`, and
`Quot.sound`. Run `./check.sh` from `results/fk-qcritical` to rebuild the full
project, rerun its public audit, validate documentation, and scan for forbidden
placeholders.
