# Arbitrary nested global equation (9)

Public modules: `FK.SourceGlobalWindow`, `FK.ArbitrarySourceNestedWindow`,
`FK.SourceNestedBounds`, and `FK.SourceNestedEquationNine`.

This package completes the ordinary nested global estimate behind Lemma 2.1,
at every $q>0$ and interior $0<p<1$, on countable graphs with local finiteness
where the existing source classes require it. It is not a proof of the separate
AG strict enhancement shift or the final Theorem 1.10 window.

## Interface and exact statement

The principal declaration is

```lean
FK.Adaptive.NestedSumGeometry.sourceNestedEquationNine
```

It proves the pre-existing

```lean
NestedEquationNine (G := G) hq hp₁.le
  (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le)
  (edgeRoots G)
```

The left-hand terms are the actual large and small `finiteVolumeLaw` cylinder
masses, extended to the global configuration space. The right-hand term is the
global Bernoulli probability of the literal `boundaryConnection` from the
finite endpoint set `edgeRoots K` of the observation edge set `K` to the boundary
of the *small* source region. The upper rate is $\max(p,p')$, not a generic rate
or a different enhanced profile.

No metric exhaustion, right-disjoint extension, reduced lattice, arbitrary-$q$
case split, alternate conditional `NestedEquationNine` shell, or added ordered
fibre requirement enters the statement. The underlying abstract nesting is
allowed to differ from the canonical inclusion of vertex regions.

## Arbitrary NestedBox geometry

The core is the set of star-contained vertices incident to an actual small-box
edge. `nested_vertex_eq_of_internal_endpoint` proves abstract nesting fixes
these vertices on their global labels, without any assumption of vertex-region
inclusion. This yields the induced-region conditions needed by the accepted
ordinary nested cutset coupling.

To transport an upper arm:

1. If a global path exits the small region, `inside_or_boundary_of_isOpenIn`
   truncates it at a literal region boundary.
2. If it stays inside, `exists_nested_endpoint_of_walk` follows it through the
   abstract nesting. Endpoints which fail star containment yield actual
   `IsRegionBoundary` witnesses.
3. A globally isolated non-core endpoint forces the open path to be trivial by
   `eq_of_openConnected_of_no_incident`, contradicting incidence of the
   observation edge, so that case cannot arise.

This addresses ordinary non-core, outside-small and isolated non-core targets
without identifying distinct global vertex labels. The arm image is bounded by
a finite-large-box-supported event, and its full global Bernoulli mass is in
turn bounded by the literal boundary-connection mass.

## Global mass conversion

`SourceGlobalWindow.lean` supplies:

- `sourceBase ≃ K`, restricting exactly the observation-edge base, not all
  small edges, so these roots do not grow with the nesting index;
- exact small and split-large cylinder identifications;
- `map_splitToInterior_fkPMF` and
  `map_splitToInterior_bernoulliProductPMF`, proving the original global
  marginal constructions; and
- global real mass computation for the finite large-box supported arm event as
  an interior-restricted global Bernoulli image.

The asserted small marginal is the accepted exact free-region FK law, including
component weights, not an independently constructed outside law.

`ArbitrarySourceNestedWindow.lean` proves both the abstract finite arm estimate
and `arbitrarySource_abs_sub_le_boundary`, its one-scale global form.
`SourceNestedBounds.lean` separately handles the empty observation base; no
exploration seed is required there.

## Consequences and remaining inputs

`canonicalSource_hasNestedBoundaryBounds` supplies the eventual nested
boundary-bound interface of `SourceUniqueness`, over arbitrary vertex
exhaustions and source boundary schedules.
`canonicalSource_existsUnique_sourceFKMeasures` combines this with the existing
compactness and Choquet steps. It proves existence and uniqueness in
`SourceFKMeasures` under countability, nonempty vertices and almost-sure
nonpercolation of the exact global upper product.

`source_tendsto_measureReal_boundaryConnection` proves the literal error tends
to zero for any fixed observation base and arbitrary cofinal vertex exhaustion,
under nonpercolation of that upper law.

These do not telescope to an unconditional critical-window Theorem 1.10:
one still needs its separate critical-window strict shift and either the
corresponding source upper stochastic comparator or a different enhanced
adaptive coupling. Directly substituting an enhanced profile into the uniform
adaptive bound is not a valid substitute. General AG, general Theorem 5.1,
planar continuous windows and Burton–Keane global cluster-count/asymptotic
arguments remain outside this component.

## Endpoint-inclusive intersection route

The additional public modules `FK.IsolatedBoundaryTransport` and
`FK.ArbitraryNestedEquationNine` give a second, independent proof and extend
all $q>0$ to every $0\le p\le1$:

```lean
FK.SourceUniqueness.nestedEquationNine_upperBernoulli
```

It proves the same literal `NestedEquationNine`, with `edgeRoots` and the
global Bernoulli product at `upperRateNN`, for arbitrary `NestedBox` witnesses
and without interior-rate hypotheses. The intersection of the two vertex
regions has exactly the small box's edges. The new deletion theorem carries
the normalized FK law to this smaller vertex type even when retained and
deleted vertices are arbitrarily wired: wholly deleted components depend only
on the fixed boundary, hence cancel in normalization. An intersection-region
boundary vertex is proved to be an original small-region boundary vertex, so
the required error event is not enlarged. Empty cylinders and $p=0,1$ are
handled directly by the all-closed/all-open finite FK laws.

This is still the ordinary constant-rate $\max(p,p')$ comparison. It supplies
no enhanced adaptive profile, essential-enhancement shift, or final enhanced
critical-window conclusion.

## Verification

The entire eight-stage chain (four new modules plus the four previously
accepted coupling/window stages) was independently rebuilt with pinned Lean
4.35 and default heartbeats. Its eight principal axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`, with no placeholders, custom
axioms or option overrides. The public gate is `./check.sh` from
`results/fk-qcritical`.
