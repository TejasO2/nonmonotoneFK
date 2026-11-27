# Deterministic nonpercolating dominant: source-DLR uniqueness

Public module: `FK.DeterministicDominator`.

This proves a **scoped case of Theorem 5.1**, not the general theorem. The
stochastic dominant is a Dirac probability law at one fixed nonpercolating
configuration. No product coupling, independent-region parameter, ordered-fibre
limit, null-section transfer, or joint free-interior assertion is used.

The improvement over the earlier
`forall_eq_sourceConvention_of_dominated_finiteOpenEdges` is that the fixed
configuration may have **infinitely many open edges**. Adaptive cluster regions
work even when no boundary of a prescribed deterministic box exhaustion is ever
closed. Thus this module does not repeat the fixed-interval argument refuted by
`FK.ClosedBoundaryObstruction` for the matching configuration on the integer
line.

## Main statements

For a geometric all-finite-region source convention `Φ`, `0 < q` and `p ≤ 1`:

* `pairwise_eq_sourceDLR_of_dirac_nonPercolating` proves any two source DLR
  laws dominated by `diracProba η` are equal when `η` is nonpercolating.
* `subsingleton_sourceDLR_of_dirac_dominates` gives the subsingleton form from
  an explicitly supplied closed-frontier exhaustion.
* `sourceDlr_eq_singleton_of_dirac_nonPercolating` proves
  `SourceDLRMeasures Φ = {μ₀}` under the explicit additional hypothesis that
  `μ₀` belongs to this class.

The singleton statement therefore assumes class membership. It does not
manufacture a Gibbs law or establish nonemptiness.

The graph requirements are countability and local finiteness, with nonempty and
preconnected used for the nonpercolating convenience forms. The convention
must satisfy `IsSourceGeometry`, along with the existing all-region finite-FK
compatibility of `SourceConvention`. No metric, planar, FKG, finite-graph or
percolating-convention assumption is added.

## Proof architecture

1. `adaptiveVertexExhaustion` converts `FK.ClosedBoundaryExhaustion` to the
   actual public `VertexExhaustion`; no metric boxes are inserted.
2. `boundaryClosed_sourceBoundary_iff` identifies closed graph frontiers with
   the exact public `SourceBoundary` closed-edge predicate.
3. `isFreeAtClosedBoundary_assignment` proves every geometric all-region source
   convention, not merely the free or wired one, free at a closed frontier.
   Both the observed exterior and the all-closed reference exterior reduce to
   the free partition.
4. Every frontier is closed at the point mass of the fixed configuration. The
   accepted `forall_eq_of_dominated_frequently_boundaryClosed` theorem applies
   along the adaptive exhaustion, and `mem_sourceDLR_iff_mem_dlr_restrict`
   returns the conclusion to the all-region source class.

In the underlying ordered comparison, closure of the upper configuration is
inherited by both ordered marginals. This does **not** assert that the two
marginals share a joint free-interior law on arbitrary random upper strata;
that invalid inference is not needed here.

## Remaining scope and verification

The arbitrary random nonpercolating-dominant hypothesis of Theorem 5.1 remains
unresolved, as do weak-limit inclusion, Lemma 2.1 and the AG critical window.
All parameters and source boundary conventions in this result remain explicit.

The twelve principal declaration audits are in `Audit.lean`. Fresh compilation
under Lean 4.35 reports only `propext`, `Classical.choice`, and `Quot.sound`.
Run `./check.sh` from `results/fk-qcritical` for the public verification.
