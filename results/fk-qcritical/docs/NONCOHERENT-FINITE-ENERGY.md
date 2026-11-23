# Noncoherent finite energy and exterior uniqueness

## Scope

`NoncoherentFiniteEnergy.lean` proves the missing **pre-DLR** finite-energy and
global-to-exterior steps for an arbitrary `IsFKLimit`.  The finite-volume
boundary setoids may be unrelated; there is no source `BoundaryConvention`, no
nesting-compatibility hypothesis, and no preliminary DLR law.

This is not a claim of the complete weak-limit part of Proposition 1.8(2).
In particular, `aeAtMostOne_geometry_of_isFKLimit` concludes the repository's
actual `ConventionTransport.AEAtMostOne`, not membership in a fixed target
`DLRMeasures` class.

## New argument and principal declarations

The imports are exactly

```lean
import FK.GlobalFiniteEnergy
import FK.FiniteConditional
```

No declaration is copied from the accepted coherent finite-energy module.
The new proof proceeds as follows.

1. `closeFactor_mul_fkWeight_le` uses the exact one-edge connected and
   nonconnected FK weight formulas.  It gives a strictly positive lower ratio
   for closing one edge at `0 < q`, `0 < p < 1`, for every boundary setoid.
2. `closeFactor_pow_mul_fkWeight_le` iterates the ratio over a finite edge set.
3. `card_closeEdges_fiber_le` proves that closing a set `s` has fibres of size
   at most `2 ^ s.card`.  This many-to-one factor is essential; a weight ratio
   alone would not bound the pushforward.
4. `map_closeEdges_fkPMF_apply_le` and `measure_map_closeEdges_le` combine the
   normalized weight ratio and fibre bound into a uniform PMF/measure bound.
5. `embeddedEdges` and `closeBox_glue` identify global box closing with interior
   closing in any containing finite box.  Consequently
   `measure_map_closeBox_le_conditionalLaw` and
   `measure_map_closeBox_le_finiteVolumeLaw` have a multiplier depending only
   on the fixed smaller box, not on the outer box or its boundary setoid.
6. `measure_map_closeBox_le_of_isFKLimit` passes that uniform bound through the
   actual weak limit using the accepted continuous-map theorem.  Neither DLR
   compatibility nor coherence is an input.
7. `ae_globalAtMostOne_closeInside_of_isFKLimit` transports the closed-box
   almost-everywhere statement to exterior fibres.
   `aeAtMostOne_geometry_of_isFKLimit` then proves
   `ConventionTransport.AEAtMostOne data.geometry μ` from the actual global
   at-most-one-infinite-cluster event on a countable simple graph.

Theorems use `0 < q` and `0 < p < 1`, matching the positive local weight ratios.

## Exact residuals

- Fixed-source/fixed-target DLR membership for an arbitrary noncoherent
  `IsFKLimit` remains unproved.  No diagonal sequence of induced conditional
  specifications is constructed, and `AEAtMostOne` is not silently substituted
  for the DLR equation.
- The endpoint cases `p = 0` and `p = 1` are not covered: `closeFactor_pos`
  genuinely uses `0 < p < 1`.
- No coherent-sequence result, strong-uniqueness theorem, endpoint theorem,
  planar theorem, or active-device comparison is relabelled as this result.

## Verification

Run from this member directory:

```sh
./build_and_audit.sh
```

The script uses the repository Elan at `.scratch/elan`, the repository's pinned
imports, default heartbeat settings, one-file builds, and exact
`#print axioms` commands.  It writes outputs only in this member directory.
The 13 principal declarations in `AuditNoncoherentFiniteEnergy.lean` each report
exactly `propext`, `Classical.choice`, and `Quot.sound`; see
`AuditNoncoherentFiniteEnergy.log`.  No shared result, GitHub state, or pinned
dependency was changed.  A whole-repository build was not run.
