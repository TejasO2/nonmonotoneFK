# Nested outer-stage DLR closure and ordered-seal obstruction

Public modules: `FK.GeneralMovingClopenRate`, `FK.GlobalOuterGeometry`,
`FK.GlobalOuterAssembly`, and the adversarial `FK.CouplingSealCounterexample`.

## Nested source-form Proposition 1.8(2)

`NestedFinDLR.GlobalClosure.proposition_1_8_2_growingFamily` takes a connected
locally finite simple graph, a genuine nested `GrowingFamily`, injective
compatible embeddings and two coherent geometric all-finite-box conventions.
For every `q > 0` and `p ≤ 1`, a law which is either already coherent-Gibbs or
an actual finite-volume weak limit belongs to every such target class whenever
`GlobalAtMostOne` holds almost surely.

Every weak-limit witness must satisfy `ExternallySupportedOn`: every
nonreflexive related pair has incident edges outside the current box at both
endpoints. This is not an invariant specification or a stabilization input; it
is the outer-boundary class needed by the escape proof. It deliberately excludes
unsupported setoids which wire deep interior vertices, including the earlier
fully wired one-edge obstruction. Raw `BoxExhaustion`s without nesting/embedding
data are not covered.

The result is DLR membership, not uniqueness and not Theorem 5.1. Canonical
metric-stage and all-finite-box adapters are included; endpoint rates use their
actual deterministic finite-volume laws. No nonpercolating dominant, prime
subcriticality, stochastic-order comparison, or neighbourhood-stabilization
hypothesis is used.

## Analytic and geometric mechanism

`GeneralMovingClopenRate.isDLR_of_clopen_escape_moving` supplies the one-point
DLR criterion with eventual lower-event inclusion and decreasing clopen escape
tails. The two rates need only lie in `[0,1]`; no ordering is assumed, so the
argument covers `q < 1`, `q = 1`, and `q > 1`.

The geometric package proves:

* open arms out of a finite locally finite vertex set are clopen;
* global at-most-one persists through a finite change of edges, via a rooted
  finite-edge cover;
* noncoherent finite energy gives post-deletion global uniqueness before DLR;
* every geometric target partition agrees with free exterior components on the
  relevant full-measure exterior fibres;
* a stage connection unexplained by an inner off-edge path leaves the finite
  region at both endpoints.

The required lower balls, finite edge supports and eventual far-boundary
condition are constructed internally. Actual larger-stage nested FK identities
provide the two-valued rate with no locally constant specification required.

This complements the independent exterior-configuration/finite-DLR route in
`FK.FreeNestedGeometry`: it proves a source-form all-box result through explicit
outer-stage escape instead of using only the constant-free stabilization route.

## Ordered-seal counterexample

`FKLimit.CouplingSealCounterexample` explicitly computes the Bool×Bool joint law
with masses `1/2`, `1/4`, `1/4`, and zero order violation. Its lower open mass
is `1/2`, upper open mass `3/4`, yet lower open mass conditioned on upper-open
is `(1/2)/(3/4)=2/3`. Thus an ordered coupling with the correct free/upper
marginals need not preserve the original free interior on an attained sealed
upper stratum.

This refutes a proposed adaptive-coupling inference, **not** Theorem 5.1 and
**not** the original-marginal fixed-region free DLR identity. Any alternative
uniqueness proof needs a specially constructed coupling or a different argument
using only the original conditional expectations. It must not simply transfer
the joint stratum's conditional law to the free marginal.
