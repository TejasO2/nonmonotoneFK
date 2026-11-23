# Interior weak-limit closure

`FK/InteriorWeakLimit.lean` addresses one scoped part of Proposition 1.8(2)
from arXiv:2512.16486v1. It is not a proof of the full weak-limit assertion.

## DLR as a reconstruction equation

For a finite box `B`, `FiniteBox.reconstruct` glues the exterior marginal of a
law to the repository's actual finite FK kernel. The theorem
`FiniteBox.isDLR_iff_eq_reconstruct` identifies the existing comp-product DLR
equation with invariance under this reconstruction. No alternate specification
or abstract weak-limit predicate replaces the actual FK measure.

The analytic step is `FiniteBox.tendsto_reconstruct`. If
`B.conditionalLaw hq hp α` is continuous in the exterior configuration, then
reconstruction is weakly continuous. `FiniteBox.isDLR_of_tendsto` and
`mem_dlrMeasures_of_tendsto` consequently prove weak closure of the one-box
and exhaustion DLR classes under that continuity hypothesis.

For locally constant boundary partitions,
`continuous_conditionalLaw_of_isLocallyConstant` proves continuity by finite-FK
dominated convergence. The exterior configuration itself is not fixed.
Every constant boundary setoid is a special case.

## Coherent finite-volume weak limits

`mem_gibbsMeasures_of_tendsto_finiteVolumeLaw_of_isLocallyConstant` proves that
a genuine weak limit of the canonical closed-exterior finite-volume laws belongs
to its source Gibbs class, when the source `BoundaryConvention`'s partitions
are all locally constant. For each fixed small box, the proof uses the
convention's actual `compatible` nesting field at every sufficiently large box.
Compatibility for all boxes is not assumed simultaneously.

On an actual countable simple graph,
`mem_dlrMeasures_of_tendsto_of_globalAtMostOne` combines this with the proved
geometric DLR transport under an almost-sure global at-most-one-infinite-cluster
hypothesis. The target can be any geometric assignment.
`mem_dlrMeasures_wired_of_tendsto_of_globalAtMostOne` specializes to the actual
wired-at-infinity assignment. These theorems use `0 < p < 1` as required by the
interior transport API.

## What remains open

Local constancy is a sufficient extra hypothesis, not a theorem about every
FK specification. The canonical free and wired-at-infinity partitions depend on
nonlocal open-path and infinite-cluster events and have not been shown to give
continuous conditional laws. Measurability alone does not justify passing the
DLR reconstruction through weak convergence.

The scope also retains coherent canonical nesting and the specified canonical
closed-exterior sequence rather than an arbitrary finite-volume boundary
sequence. Global at-most-one-cluster is needed only for transport to another
geometric convention. Full Proposition 1.8(2), strong uniqueness, and the main
numbered theorems are not inferred.

## Verification

The module is public through `FK.lean`; its 21 declarations are audited in
`Audit.lean`. Run the complete repository check from `results/fk-qcritical`:

```sh
lake env lean FK/InteriorWeakLimit.lean
./check.sh
```

The submission was also copied to a separate scratch directory and compiled
independently against the pinned Lean 4.35 environment. Its audit reported only
`propext`, `Classical.choice`, and `Quot.sound`. Non-fatal Lean linter warnings
about unused section variables and `haveI` style are retained in the source.
