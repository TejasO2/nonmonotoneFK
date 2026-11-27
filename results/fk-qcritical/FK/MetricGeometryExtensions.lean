import FK.MetricStageGeometry

/-! Reusable coherence and exterior-support boundary facts. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.ClusterEscape
open FK.NestedMixture

universe u

/-- The canonical metric nesting is coherent on vertices. -/
theorem metricGrowingFamily_nest_vert_comp
    {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {k n r : ℕ}
    (hkn : k ≤ n) (hnr : n ≤ r) (hkr : k ≤ r)
    (x : (metricBox hG o k).Vertex) :
    ((metricGrowingFamily hG o).nest n r hnr).vert
        (((metricGrowingFamily hG o).nest k n hkn).vert x) =
      ((metricGrowingFamily hG o).nest k r hkr).vert x := rfl

/-- The growing family's underlying edge exhaustion is exactly the canonical
metric-box exhaustion. -/
theorem metricGrowingFamily_exh
    {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) :
    (metricGrowingFamily hG o).exh = metricBoxExhaustion hG o := rfl

/-- Free boundary setoids satisfy exterior support vacuously: their only
related pairs are reflexive. -/
theorem externallySupportedOn_free
    {V : Type u} {G : SimpleGraph V} {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B)) :
    ExternallySupportedOn data B.graph.freeBoundary := by
  intro u v hne hrel
  exact (hne hrel).elim

/-- In particular, every canonical free metric stage is externally supported. -/
theorem externallySupportedOn_metric_free
    {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) (n : ℕ) :
    ExternallySupportedOn (constantBoxData (metricBoxData hG o) n)
      (metricBox hG o n).graph.freeBoundary :=
  externallySupportedOn_free _

/-- The far-stage conclusion for free boundaries needs no additional schedule
hypothesis. -/
theorem eventually_far_free_metric
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {b : ℕ}
    (e : (metricBox hG o b).edges) (m : ℕ) :
    ∀ᶠ n in atTop, ∀ u v : (metricBox hG o n).Vertex, u ≠ v →
      (metricBox hG o n).graph.freeBoundary.r u v →
      (metricBoxData hG o).vertex n u ∉ metricLowerK hG o e m ∧
      (metricBoxData hG o).vertex n v ∉ metricLowerK hG o e m :=
  eventually_far_of_externallySupportedOn_metric hG o
    (fun n => (metricBox hG o n).graph.freeBoundary)
    (fun n => externallySupportedOn_metric_free hG o n) e m

/-- Fully wired boundary is not externally supported when a box has two
vertices and one of them has no incident exterior edge. -/
theorem not_externallySupportedOn_wiredBoundary
    {V : Type u} {G : SimpleGraph V} {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B))
    (u v : B.Vertex) (hne : u ≠ v)
    (hu : ∀ e : G.edgeSet, e ∉ B.edges → data.vertex 0 u ∉ e.1) :
    ¬ ExternallySupportedOn data B.graph.wiredBoundary := by
  intro ha
  obtain ⟨⟨e, he, hue⟩, _⟩ := ha u v hne trivial
  exact hu e he hue
