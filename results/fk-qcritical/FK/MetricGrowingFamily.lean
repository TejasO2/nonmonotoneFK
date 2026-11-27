import FK.NestedMixture.Limit
import FK.NestedMetricGeometry
import FK.MetricInterior

/-! Canonical nested metric-box growing families. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.NestedMetricGeometry
open FK.NestedMixture

universe u

/-- The canonical nesting of two metric balls. -/
noncomputable def metricBox_nest {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {k n : ℕ} (hkn : k ≤ n) :
    NestedBox (metricBox hG o k) (metricBox hG o n) where
  edge_sub := by
    intro e he
    exact monotone_metricEdges hG o hkn he
  vert := fun x => ⟨x.1, by
    exact (CurvatureVariance.Infra.Percolation.mem_innerBall hG).2
      (((CurvatureVariance.Infra.Percolation.mem_innerBall hG).1 x.2).trans_le
        (Nat.add_le_add_right hkn 1))⟩
  vert_inj := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : (metricBox hG o n).Vertex => z.1) hxy
  src := by
    intro e
    apply Subtype.ext
    rfl
  tgt := by
    intro e
    apply Subtype.ext
    rfl

/-- Metric boxes form a genuine growing family, not merely an edge exhaustion. -/
noncomputable def metricGrowingFamily {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) : GrowingFamily.{u, u} G.edgeSet where
  box := metricBox hG o
  edges_mono := by
    intro k n hkn
    exact monotone_metricEdges hG o hkn
  covers := (metricBoxExhaustion hG o).covers
  nest := fun k n hkn => metricBox_nest hG o hkn

@[simp] lemma metricGrowingFamily_box {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) (n : ℕ) :
    (metricGrowingFamily hG o).box n = metricBox hG o n := rfl

/-- Canonical metric nesting agrees with the global vertex embeddings. -/
theorem metricGrowingFamily_compat {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {k n : ℕ} (hkn : k ≤ n)
    (x : (metricBox hG o k).Vertex) :
    (metricBoxData hG o).vertex n (((metricGrowingFamily hG o).nest k n hkn).vert x) =
      (metricBoxData hG o).vertex k x := rfl

end FK.NestedFinDLR
