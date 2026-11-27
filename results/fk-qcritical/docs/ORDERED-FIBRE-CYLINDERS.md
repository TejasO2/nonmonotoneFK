# Cylinder masses from ordered-fibre limits

Public modules: `FK.FibreCylinder` and `FK.FibreClass`. These complete the
integration layer of the conditional-limit argument, not its region/coupling
construction.

`measureReal_eq_of_integral_condExp_ae_eq` integrates tail conditional
probabilities whose evaluations at two measurable maps agree almost surely on
a probability space with prescribed pushforwards. `integral_map` carries the
outer integral to each marginal and `integral_condExp` identifies it with the
unconditional event mass. No assertion converts a tail conditional into a
constant pointwise value, so tail triviality is unnecessary.

`ae_condExp_eq_of_tendsto_eventuallyEq` proves that two eventually agreeing
sequences with known tail-conditional limits have equal limits.
`OrderedTripleRegionCylinderLimits` makes its region support explicit: its
`T : ℕ → Configuration E → Finset E` comes from a **single dominating
configuration**, and its `g : Finset E → ℝ` is the common finite-region value
after a cylinder's support has entered that region. Both limits and eventual
agreement are present as hypotheses; they are not assumed to have been
constructed globally.

`probabilityMeasure_eq_of_orderedTriple_regionCylinderLimits` concludes
measure equality from this genuine per-cylinder input by extending from
finite-coordinate events to the full configuration sigma-algebra.
`FibreClass` lifts the criterion to subsingletons and proves that a nonempty
class with pairwise versions of the limit is a singleton.

This layer does not show that real disintegrated kernels already satisfy those
hypotheses. It also does not manufacture a DLR law when the class is empty;
the `Nonempty` premise is kept separate. For actual fibres, a generic
integrable observable under `K_i(η)` admits reverse projections. Identifying
their common limit remains a region-level step, not an automatic transfer of
the original law's martingale or tail conditional.
