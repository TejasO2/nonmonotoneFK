# Finite obstruction to a root-to-boundary correction identity

Public modules: `FK.NormalizedFilter` and `FK.ArmCorrectionObstruction`.

This is a fully checked **finite counterexample to a proposed shortcut**, not a
proof or refutation of general Theorem 5.1. The proposed shortcut says that,
after conditioning a finite FK law on the absence of an open path from cylinder
endpoints to the wired boundary, the cylinder's conditional law is independent
of the boundary partition. It is false even when the only wiring joins two
vertices in that boundary.

This does not contradict free conditioning at a genuinely closed frontier or
the accepted `RegionSeal` theorem. No infinite-volume measure, DLR class,
source convention, stochastic dominant, or nonpercolation hypothesis appears
in the example. In particular, it is not an FK/source counterexample to
Theorem 5.1.

## Exact computation

The labelled multigraph has vertices `Fin 5` and five edges, in this order:

```text
0--1, 0--2, 1--2, 2--3, 2--4.
```

The cylinder is the event that label `0`, edge `0--1`, is closed. The event
`good` excludes an open path from `{0,1}` to `{3,4}` in the primal open graph
with free boundary. At $q=2$ and $p=4/5$, compare the actual finite FK PMFs
with free boundary and with the setoid whose sole additional block is `{3,4}`.

Both laws are conditioned using the real `PMF.filter`. The main values are

$$\Pr_{\mathrm{free}}(0\text{ closed}\mid\text{good})=17/59,
\qquad
\Pr_{3\sim4}(0\text{ closed}\mid\text{good})=21/71.$$

These are `PMF.toMeasure.real` values, not surrogate weights. The raw scaled
restricted masses behind the ratios are respectively `544/1888` and
`336/1136`. The computations use ordinary `decide`, not `native_decide`.

The mechanism is visible: `good` does not force both edges `2--3` and `2--4`
to be closed. The root component can already be disconnected from vertex `2`.
The exterior normalizations therefore reweight the different root-cluster
strata differently. Sealed-region factorization alone does not yield a
correction bound by the probability of this root-to-boundary event; a repair
requires another common region/value or control of those strata.

## Reusable normalized-filter lemma

`normalizedPMFOfSumPos_filter_toMeasure_real` proves that filtering a
normalized finite nonnegative-weight PMF on `T`, then evaluating `C`, equals
the ratio of unnormalised weights on `C ∩ T` and on `T`. Both global and
conditional normalizations are cancelled. The supporting `T` point makes the
denominator nonzero. This connects exact integer weight sums to the actual
FK conditional-filter masses.

## Verification

Eleven fully-qualified principal declarations are printed in `Audit.lean`.
An independent clean Lean 4.35 rebuild with warnings treated as errors reports
only `propext`, `Classical.choice`, and `Quot.sound`, without `sorry`, `admit`,
`unsafe`, `native_decide`, custom axioms, or option overrides. The public gate
is `./check.sh` from `results/fk-qcritical`.
