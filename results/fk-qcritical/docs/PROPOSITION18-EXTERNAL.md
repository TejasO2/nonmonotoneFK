# Proposition 1.8(2): exterior-schedule and all-box completion

Public module: `FK.FreeNestedGeometry`, principally in namespace
`FK.NestedFinDLR`.

This proves Proposition 1.8(2) for the paper's two source branches: coherent
geometric Gibbs laws and weak limits of actual FK laws induced by exterior
configurations. The weak-limit branch covers arbitrary exterior schedules and
any genuine nested graph exhaustion, at every `q > 0` and `0 ≤ p ≤ 1`.
Assuming exactly almost-sure `GlobalAtMostOne`, each such measure belongs to
every supplied coherent geometric all-box target class.

This is not the earlier prime-subcritical metric special case. No
nonpercolating majorant, comparison in `q`, arm estimate, mass-escape input,
fixed exhaustion centre, or stabilization hypothesis is required for this
result.

## Main theorem

`AllBoxFKMeasureSource` has two constructors matching the source definition:

* `gibbs`: a coherent geometric `AllBoxConvention` and actual membership in
  `AllBoxDLRMeasures`;
* `externalLimit`: an arbitrary exterior configuration schedule and genuine
  weak convergence of the corresponding actual FK `conditionalLaw`s.

The final declaration
`proposition_1_8_2_allBox` takes a genuine `GrowingFamily`, an
`AllBoxSimpleGraphBoxData`, injective compatible exhaustion embeddings, any
`0 < q` and `0 ≤ p ≤ 1`, a coherent geometric all-box target, and
`GlobalAtMostOne` almost surely for the limiting law. Its conclusion is
`μ ∈ AllBoxDLRMeasures Φ`, so the DLR equation holds at every finite box, not
just at the selected exhaustion boxes.

The Gibbs constructor is discharged by the public all-box convention transport
theorem. The external-limit constructor uses the new nested free Markov proof
and the actual weak convergence input; weak-limit existence is not asserted.

## The two proof steps

`inducedBoundary_free_exteriorRestriction` proves, configuration by
configuration, that nested induction agrees with the canonical free
exterior-component partition when the embeddings commute with the genuine
`NestedBox` inclusion. The identity holds even with many infinite exterior
clusters: it is a path identity, not a uniqueness consequence.

`isDLR_free_conditionalLaw_nested` combines this with the actual finite nested
FK mixture theorem. Every larger-box FK law with its genuine free exterior
boundary satisfies the smaller canonical free DLR equation. For a fixed small
box this holds at every sufficiently large exhaustion stage and for every
member of an arbitrary exterior schedule.

For the limit, global finite energy converts `GlobalAtMostOne` into at-most-one
infinite exterior cluster on all exterior marginals. The public quasilocality
and noncoherent closure theorems then close the free DLR equations. The source
specifications are literally constant `data.free`, so the required local
stabilization is immediate. Finally, the proved geometric-convention transport
moves from free to the target. Endpoint rates use the deterministic
`EndpointGlobalFiniteEnergy` lemmas; the all-box conclusion follows from
coherence and the existing exhaustion test.

## Scope and the earlier counterexamples

The theorem deliberately does not include every public noncoherent
`IsFKLimit` made from unrelated arbitrary boundary setoids. Its weak-limit
laws are the paper's actual exterior-configuration FK laws. The public
one-edge fully wired counterexample concerns that broader, refuted class and
does not contradict this source-union theorem.

The target `Φ` is genuinely coherent and geometric. The proof neither invents
an all-box convention from a bare assignment nor replaces compatibility by the
weaker two exterior-component conditions alone. The restricted
prime-dominated metric closure in `PrimeMetricAutoGlobal` remains useful but
is strictly weaker than this general result.

No assertion about Theorem 5.1, Lemma 2.1, essential enhancement, planar
geometry, or graph-level strong uniqueness follows merely from this module.
