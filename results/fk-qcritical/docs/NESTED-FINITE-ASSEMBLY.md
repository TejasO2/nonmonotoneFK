# Nested finite-box cylinder and arm assembly

## Files and dependencies

- `NestedFiniteAssembly.lean`: the new development, 24 audited declarations.
- `NestedFiniteAssemblyAudit.lean`: exact `#print axioms` commands for those
  declarations.
- `NestedFiniteCoupling.lean`: an unmodified copy of the accepted artifact
  `.ultramath/smwsu3cov/m6/NestedFiniteCoupling.lean`, kept locally so the new
  module can import the independently accepted construction without a shared
  result edit.
- `.scratch/build-one.sh`: one-target build helper. It selects the repository
  Elan Lean 4.35.0 toolchain, obtains the project's pinned import path through
  `lake env`, and writes objects/logs only under this member's `.scratch/`.
- `check.sh`: fresh sequential rebuild, audit validation, and source scan.

The public module imports the integrated `FK.NestedFiniteCoupling` and the
modules `FK.NestedArmUniqueness`, `FK.BernoulliFiniteBox`, and
`FK.TransportBoundary`. Only the worker-local coupling import was changed;
the mathematical source and the accepted coupling are unchanged.

## What is proved

For any finite box `B`, `boxCylinder B J S hJ` is the exact interior readout
of the global cylinder `cylinder J S`. The development proves both its glue
and interior-restriction formulas and the identity

```lean
(B.finiteVolumeLaw hq hp α).real (cylinder J S) =
  (B.graph.fkPMF hq hp α).toMeasure.real (B.boxCylinder J S hJ).
```

For `j : Fin n ≃ B.edges`, `B.indexedGraph j` is definitionally the
`finIndexedGraph` expected by the accepted finite coupling. Its sources and
targets are the actual box sources and targets. `map_reindex_fkPMF` transports
an arbitrary box boundary setoid exactly (using the integrated arbitrary-
boundary graph transport), and `map_reindex_bernoulliProductPMF` proves the
analogous upper-product identity directly from the product weights. No
`hsecond` or measure-identification premise is introduced for these
reindexings.

The finite/global Bernoulli adapter proves equality of measures, not merely
coordinate probabilities:

```lean
Measure.map B.interiorRestriction
  (FKLimit.bernoulliProduct (fun _ => unitOfNN p hp)) =
  (B.graph.bernoulliProductPMF hp).toMeasure.
```

`reindex_preimage_boxCylinder_of_edge_compat` proves the complete nested
cylinder compatibility from the elementary condition on each cylinder edge:

```lean
e (Sum.inl (jD.symm iD)) = jS.symm iS.
```

Observation compatibility is therefore not assumed wholesale.

The principal generic result,
`finiteBox_cylinder_abs_sub_le_interiorUpper_of_good`, applies the accepted
actual nested triple. It removes the second-marginal obligation internally and
compares two actual closed-exterior `finiteVolumeLaw` probabilities on one
shared global cylinder. Its right side is an exact global Bernoulli mass.

Its graph specialization,
`finiteBox_cylinder_abs_sub_le_farConnection_of_good`, has conclusion

```lean
|(BS.finiteVolumeLaw hq hp₁.le α).real (cylinder J S) -
  (BD.finiteVolumeLaw hq hp₁.le β).real (cylinder J S)| ≤
(percolation G (unitOfNN (upperRateNN q p) _)).real
  (NestedAssembly.farConnection G roots center r).
```

Here `roots`, `center`, and `r` are arbitrary genuine event parameters. This
is exactly the one-`(n,m)` bound shape consumed by
`NestedArmUniqueness.eq_of_isFKLimit_of_nested_bernoulliArm_bounds` after
setting `r = m + width J`. The conversion between the two libraries' infinite
Bernoulli products is carried out explicitly at the `Measure.infinitePi` level.

## Scoped premises and explicit residual obligations

This is a substantial single-scale assembly step, **not** full Lemma 2.1,
Theorem 1.9, or a new unconditional uniqueness theorem.

1. `hgood` remains a real premise: equality of the first/good and second/good
   intersections in the constructed nested triple. This file does not prove
   the maximal-closed-cutset/common-free-interior theorem. Both box boundary
   setoids remain arbitrary and are only reindexed, never restricted to a
   right-wired class.
2. `he` requires the actual nested edge identification on the cylinder base;
   `hD` requires containment of the finite coupling's exceptional complement
   in the selected local arm realization; and `hU` identifies that realization
   with the actual global `farConnection` event. These are not discharged by a
   generic geometry assertion. The maximal-stratum/event identification is
   still required.
3. A user of the uniqueness interface must still choose the boxes at indices
   `n,m`, prove the preceding data uniformly/eventually in `n`, and supply the
   existing zero-percolation and `hwidth` hypotheses. No exhaustion-level or
   final weak-limit uniqueness statement is claimed here.
4. Parameters remain `0 < q` and `0 < p < 1`, matching the accepted finite FK
   coupling. No endpoint statement is made.

## Verification

The repository Lean is `4.35.0`. Compilations use default heartbeats and one
target per invocation. `.scratch/logs/NestedFiniteAssemblyAudit.log` contains
24 exact principal audits. Every report is precisely

```text
[propext, Classical.choice, Quot.sound]
```

There are no `sorry`, `admit`, `unsafe`, or new-axiom declarations. The final
fresh sequential rebuild and scan are run by `check.sh`; all generated files
are confined to this member directory.
