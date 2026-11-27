# Arbitrary-exhaustion classical strong uniqueness

Public modules: `FK.SourceEscape`, `FK.SourceBoundary`, `FK.SourceFamily`, and
`FK.SourceUniqueness`.

This proves the analytic, graph-geometric, compactness, and Choquet parts of the
classical route to Theorem 1.10. A completed nonpercolation/window theorem and
the finite nested equation-(9) estimate remain as inputs; it is not an
unconditional Theorem 1.10 or proof of Lemma 2.1/AG. The newer
[source upper-window assembly](SOURCE-WINDOW.md) constructs the separate
stochastic dominant from Prop 4.2 and the AG deactivation shift, but leaves
those two substantive mathematical inputs explicit.

## The two genuine inputs

For a countable nonempty vertex type, a locally finite simple graph, `0 < q`,
and `p ≤ 1`, `theorem_1_10_modulo_AG_window_and_lemma_2_1` assumes:

1. a probability law `ρ` which almost surely has no infinite open cluster;
2. `NestedEquationNine hq hp ρ roots`, the literal finite nested estimate on
   actual nested induced boxes and inner-cylinder supports, for every arbitrary
   pair of source vertex exhaustions and source outer-boundary schedules;
3. `StochasticallyDominates ρ μ` for every source weak limit `μ`, with the
   convention that stage `μ(A) ≤ ρ(A)` on every measurable upper event.

It concludes a unique `μ₀` such that `SourceFKMeasures = {μ₀}` and, almost
surely, `μ₀` is nonpercolating.

The adaptive coupling/free-interior construction behind equation (9) is not
asserted by these modules. Correspondingly, the AG critical window, its
semifinite criticality, and its essential-enhancement geometry are not supplied.

## Literal nested boundary and crossing exhaustions

`IsRegionBoundary G R w` means that `w ∈ R` has a neighbour outside `R`.
`boundaryConnection` is exactly the event that a finite root set is openly
connected to this region boundary—not merely to the region complement.

The boundary events are decreasing once roots are included. Finite closed
neighbourhoods of the finite root clusters show that persistent connection to
this boundary creates an infinite root cluster. Hence their mass tends to zero
for every nonpercolating measure and arbitrary cofinal vertex exhaustion, with
no metric-ball assumption.

`VertexExhaustion.eventually_nest` provides actual nested induced boxes for
every fixed stage of one exhaustion inside every sufficiently late stage of
another exhaustion. `hasNestedBoundaryBounds_of_equationNine` implements the
source's `m`, then `n_m`, choice. The resulting arbitrary-exhaustion nested
cylinder estimate identifies two actual FK weak limits in the correct order:
first the outer index, then the inner region.

## Source family, compactness, and Choquet

`SourceWeakLimits` includes all induced vertex exhaustions and source `Π(∂Λ)`
boundary classes, but not unrelated arbitrary noncoherent setoids.
`SourceFKMeasures` adds geometric conventions with DLR equations at every
finite vertex region. The geometry transport identifies the source exterior
walk model with the global finite-box model, including exterior infinitude.

Compactness of the finite-volume laws produces a subsequence whose reindexed
regions remain a genuine vertex exhaustion and whose free boundaries are
source boundary classes. Thus source weak-limit existence is proved, not
assumed; it makes no claim about a particular original sequence.

For the Gibbs branch, an all-region coherent source convention can be tested
on any chosen exhaustion because its finite nested DLR compatibility supplies
`mem_sourceDLR_iff_mem_dlr_restrict`. This also preserves extremality classes.
The completed reverse-martingale representation then turns any extremal
all-region DLR law into a source weak limit. Since all weak limits agree, the
tail-Choquet theorem gives equality of every all-region DLR law.

Source-union Proposition 1.8(2) is proved elsewhere. This classical alternative
does not quote Theorem 5.1 or Proposition 1.8(2) to hide the remaining nested
estimate: that estimate and the strict AG window are exactly the remaining
main mathematical obligations.
