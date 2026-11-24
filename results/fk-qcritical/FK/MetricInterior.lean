/-
# Region vertices have no edge leaving the metric box

The negative result `ConfinementNecessary` shows that the region continuation of
`RegionConfinement` needs the boundary setoid to be *confined*.  This short file
isolates the one geometric fact that makes the standard boundary conventions
confined on nested metric boxes: a vertex of `metricBox hG o N` at distance
`< N` has no edge leaving the box, because every incident edge has an endpoint
at distance `< N` and a box edge is exactly an edge with such an endpoint.
-/

import FK.MetricRegionGood

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement

open FK.Finite FK.Finite.LabelledMultigraph
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry

variable {V : Type} {G : SimpleGraph V} [G.LocallyFinite]

/-- **No edge leaves the box at an interior vertex.**  If `x` is at graph
distance `< N` from the root then every global edge incident with `x` is an edge
of the radius-`N` metric box. -/
theorem edge_mem_metricBox_of_dist_lt {o : V} {hG : G.Connected} {N : ℕ} {x : V}
    (hx : G.dist o x < N) {e : G.edgeSet} (he : x ∈ e.1) :
    e ∈ (metricBox hG o N).edges :=
  (FK.MetricRegionGood.mem_metricBox_edges_iff (hG := hG)).2 ⟨x, he, hx⟩

/-- Consequently a vertex at distance `< N` has no incident edge outside the
box: the "boundary" of the box, read as vertices with an edge leaving it, misses
`innerBall hG o N` entirely. -/
theorem not_exists_edge_outside_of_dist_lt {o : V} {hG : G.Connected} {N : ℕ} {x : V}
    (hx : G.dist o x < N) :
    ¬ ∃ e : G.edgeSet, x ∈ e.1 ∧ e ∉ (metricBox hG o N).edges := by
  rintro ⟨e, he, hout⟩
  exact hout (edge_mem_metricBox_of_dist_lt hx he)

/-- The open region of radius `R` is a set of box vertices of the radius-`N`
box as soon as `R ≤ N + 1`. -/
theorem innerBall_subset_innerBall {o : V} {hG : G.Connected} {R N : ℕ}
    (hRN : R ≤ N + 1) :
    (CurvatureVariance.Infra.Percolation.innerBall hG o R : Set V) ⊆
      (CurvatureVariance.Infra.Percolation.innerBall hG o (N + 1) : Set V) := by
  intro x hx
  exact (CurvatureVariance.Infra.Percolation.mem_innerBall hG).2
    (((CurvatureVariance.Infra.Percolation.mem_innerBall hG).1 hx).trans_le hRN)

end FK.RegionConfinement
