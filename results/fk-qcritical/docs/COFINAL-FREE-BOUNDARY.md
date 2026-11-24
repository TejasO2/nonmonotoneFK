# Cofinal free-boundary uniqueness and its limitations

Public modules: `FK.CoFinalFreeUniqueness`, `FK.SourceConventionFree` and
`FK.ClosedBoundaryObstruction`. These prove a fixed-exhaustion form of the
closed-boundary uniqueness argument and identify the genuinely missing
adaptive-region step.

## From common closed boxes to common conditional expectations

`conditionalLaw_real_eq_of_boundaryClosed` proves that when an induced
boundary partition agrees with its closed-exterior reference partition,
a supported event's conditional mass is that exact reference value.
`tendsto_ae_exteriorConditionalLaw_of_dlr` proves reverse-martingale
convergence for a general DLR class, without demanding extremality: conditioning
outside of exhaustion boxes converges a.s. to tail conditional expectation.

At an ordered triple, a frequently closed top configuration has the same
closed indices in both lower configurations. Extracting a common strictly
increasing subsequence using `exists_strictMono_of_frequently`, equality of its
real conditional masses follows, while each tail conditional limit is also
preserved by the pushforward to its own marginal. A.e. uniqueness of limits
plus the two integrals of tail conditional expectation proves equality on all
Boolean cylinders (`eq_of_orderedTriple_frequently_boundaryClosed`).
`forall_eq_of_dominated_frequently_boundaryClosed` lifts this to dominated DLR
classes, with coherent and `Subsingleton` forms. The boundary-closed event is
decreasing, which is exactly the inheritance fact needed from stochastic
domination.

This argument needs no Choquet decomposition and no mean-insensitivity
hypothesis, nor does it sidestep martingales by a random tower identity: the
filtration is fixed by the exhaustion and convergence was already proved.
Nevertheless it depends on a genuine cofinal closed-boundary subsequence.

## The actual source convention and an honest special case

`SourceBoundary` selects external edges incident to the box's vertices.
`openPathSetoid_components_eq_of_closedBoundary` proves that if those edges
are closed, no open exterior walk joins distinct vertices of the box, so the
exterior open-path convention is exactly the reference one. The assembled
`sourceBoundaryAssignment` plugs that into `isFreeAtClosedBoundary_sourceConvention`.

If a configuration has only finitely many open edges it eventually has this
closed source boundary, because cofinal boxes eventually contain all open
edges. Consequently `forall_eq_sourceConvention_of_dominated_finiteOpenEdges`
proves uniqueness for such sparse dominating laws. That is a special,
inhabited but limited case, not the general subcritical/nonpercolating
regime. The constant/all-open non-vacuity checks similarly calibrate bits of
API, not the source proof's difficulty.

## Why adaptive regions are unavoidable

The matching configuration on the integer line has open edges exactly the
matching family $(2k,2k+1)$. Every cluster is finite, yet one of the two
crossing edges of each interval is open. The formal result
`no_percolation_without_closed_interval_boundary` therefore proves that
nonpercolation cannot imply closed boundaries for the fixed box exhaustion.

The complete paper argument still requires configuration-chosen connected
regions, their induced free DLR identity, joint measurability in the external
variable, and reverse-martingale identification along that varying filtration.
No such adaptive assembly is claimed here. Trying to replace that with this
fixed-exhaustion uniqueness theorem would be a scope error.

All 34 principal axiom reports compile against pinned Lean 4.35 and contain
only `propext`, `Classical.choice`, and `Quot.sound` (one uses fewer).
