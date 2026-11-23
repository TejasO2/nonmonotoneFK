# Lower cycle paths and the geometric `q > 1` DLR sandwich

`CycleBoundaryLowerPaths.lean` extends `CycleBoundaryPaths.lean` in the reverse
prime direction. It does not alter the finite-box cycle construction.

## Proved declarations

1. `FK.EnhancedTransport.gt_dlr_lower_of_active_cyclePathFamily` instantiates
   `gt_dlr_lower_of_active_cycle_devices` with the singleton family
   `cyclePathFamily`. Its auxiliary-edge condition comes from device separation;
   its connection implication is the actual labelled-multigraph complementary
   cycle walk. The same cycle witness gives the uniform `L - 1` cardinality
   bound. The conclusion is

   ```
   StochasticallyDominates μ
     (bernoulliProduct (gtLowerParameters p q hp hqR hpp L S)).
   ```

   Under the repository convention this says that the raised product profile is
   stochastically below `μ`. Away from `S` its parameter is `p'`; on `S` it is
   `p' + cycleEpsilon p q L`.

2. `..._interior` assumes only `0 < p < 1` and `1 < q` for the parameter inputs.
   It derives `0 < q` and the strict real inequality `p' < p` using
   `FKLimit.fkSingletonParameter_lt_self_iff`. The DLR hypothesis and the product
   profile use these constructed proofs, so there is no additional prime-sign
   hypothesis.

3. `gt_dlr_sandwich_of_geometric_star_cyclePathFamily` combines the lower cycle
   comparison with `gt_dlr_upper_of_active_star_devices`. The finite star input
   is constructed by `exists_starCutset_of_active_geometric`, not postulated.
   For a compatible simple-graph box exhaustion, an injective vertex map, and a
   geometric boundary assignment, the theorem gives both

   ```
   StochasticallyDominates μ lowerCycleProduct
   StochasticallyDominates upperStarProduct μ.
   ```

   The upper product uses `p - starEpsilon p q Delta` on the star set and `p`
   elsewhere. Canonical free and wired-at-infinity assignments satisfy the
   geometric assignment hypothesis by `SimpleGraphBoxData.free_isGeometric` and
   `wired_isGeometric`.

## Exact remaining inputs

The theorems retain countable vertices/edges as required by their respective
APIs, local finiteness for actual incidence stars, nonempty edge types at every
box scale, and injectivity of each box vertex map. Each family is supplied with
its separated-device proof, actual star or uniformly bounded cycle witnesses,
and eventual admissibility. For the sandwich the measure must belong to the
fixed exhaustion/assignment DLR class.

These are not claims that quasi-transitivity has already supplied activation,
that every FK weak limit is in that DLR class, or that the product parameters
are uniformly bounded away from the critical parameter. No general AG strict
shift, Theorem 1.4 completion, or global Gibbs/weak-limit conversion is asserted.

## Verification

The module was elaborated with the repository Lean 4.35.0 toolchain at default
heartbeats, using the integrated dependency oleans read-only and an isolated
member Elan home. `CycleBoundaryLowerPaths.compile.log` and
`CycleBoundaryLowerPaths.audit.log` record compilation and all three `#print
axioms` checks. Each principal declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`.
