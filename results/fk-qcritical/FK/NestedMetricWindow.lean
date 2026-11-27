import FK.NestedAdaptiveGood
import FK.MetricRegionGood
import FK.MetricInterior
import FK.Proposition42Source

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.Adaptive.NestedSumGeometry

open FK.Finite FK.Finite.LabelledMultigraph FK.Exploration.FKCoupling
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing

/-- Ordinary nested finite boxes determine the induced sum geometry. -/
noncomputable def nestedBoxGeometry {E : Type*} (BS BD : FiniteBox E)
    {nS nD : ℕ} (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (d : BD.Vertex → BS.Vertex)
    (hdinj : Function.Injective d) (hds : ∀ a, d (BD.source (jD a)) = BS.source ⟨(jD a).1, hBD (jD a).2⟩)
    (hdt : ∀ a, d (BD.target (jD a)) = BS.target ⟨(jD a).1, hBD (jD a).2⟩)
    (core : Set BD.Vertex)
    (houtS : ∀ o : (outsideGraph BS BD).Edge,
      BS.source ⟨o.1, o.2.1⟩ ∉ d '' core)
    (houtT : ∀ o : (outsideGraph BS BD).Edge,
      BS.target ⟨o.1, o.2.1⟩ ∉ d '' core) :
    NestedSumGeometry BS.Vertex (BD.indexedGraph jD) (outsideGraph BS BD) where
  source a := (BS.indexedGraph jS).source (nestedSplitEdgeEquiv BS BD jS jD hBD a)
  target a := (BS.indexedGraph jS).target (nestedSplitEdgeEquiv BS BD jS jD hBD a)
  vertex := d
  vertex_injective := hdinj
  source_inl a := by
    exact (nestedGluing_source BS BD jS jD hBD d hds (Sum.inl a)).symm
  target_inl a := by
    exact (nestedGluing_target BS BD jS jD hBD d hdt (Sum.inl a)).symm
  core := core
  not_core_of_source_inr := by
    intro o a ha hac
    apply houtS o
    refine ⟨a, hac, ?_⟩
    exact ha.trans (nestedGluing_source BS BD jS jD hBD d hds (Sum.inr o)).symm
  not_core_of_target_inr := by
    intro o a ha hac
    apply houtT o
    refine ⟨a, hac, ?_⟩
    exact ha.trans (nestedGluing_target BS BD jS jD hBD d hdt (Sum.inr o)).symm

open CurvatureVariance.Infra.Percolation
open FK.MetricRegionGood

variable {V : Type} {Gph : SimpleGraph V}

/-- Canonical induced geometry of two centered metric boxes. -/
noncomputable def metricNestedGeometry [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n) :
    NestedSumGeometry (metricBox hG o n).Vertex
      ((metricBox hG o r).indexedGraph (edgeIndex _))
      (outsideGraph (metricBox hG o n) (metricBox hG o r)) := by
  let BS := metricBox hG o n
  let BD := metricBox hG o r
  let d : BD.Vertex → BS.Vertex := metricVertexInclusion hG o hrn
  have hds : ∀ a, d (BD.source (edgeIndex _ a)) =
      BS.source ⟨(edgeIndex _ a).1, nested_metricBox_edges hG o hrn (edgeIndex _ a).2⟩ := by
    intro a
    exact metricVertexInclusion_source hG o hrn _ _
  have hdt : ∀ a, d (BD.target (edgeIndex _ a)) =
      BS.target ⟨(edgeIndex _ a).1, nested_metricBox_edges hG o hrn (edgeIndex _ a).2⟩ := by
    intro a
    exact metricVertexInclusion_target hG o hrn _ _
  have hdinj : Function.Injective d := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : BS.Vertex => x.1) hab
  have houtS : ∀ e : (outsideGraph BS BD).Edge,
      BS.source ⟨e.1, e.2.1⟩ ∉ d '' {x | Gph.dist o x.1 < r} := by
    rintro e ⟨x, hx, heq⟩
    have ha := @newEdge_avoids_region V Gph _ o hG r r n (le_refl r) e.1 e.2.1 e.2.2
    apply ha.1
    rw [← congrArg Subtype.val heq]
    exact hx
  have houtT : ∀ e : (outsideGraph BS BD).Edge,
      BS.target ⟨e.1, e.2.1⟩ ∉ d '' {x | Gph.dist o x.1 < r} := by
    rintro e ⟨x, hx, heq⟩
    have ha := @newEdge_avoids_region V Gph _ o hG r r n (le_refl r) e.1 e.2.1 e.2.2
    apply ha.2
    rw [← congrArg Subtype.val heq]
    exact hx
  exact nestedBoxGeometry BS BD (edgeIndex _) (edgeIndex _)
    (nested_metricBox_edges hG o hrn) d hdinj hds hdt {x | Gph.dist o x.1 < r} houtS houtT

/-- Radius shell used as the joint large/small exploration boundary. -/
def metricRoots [Gph.LocallyFinite] (hG : Gph.Connected) (o : V) (r n : ℕ) :
    Set (metricBox hG o n).Vertex := {x | r ≤ Gph.dist o x.1}

lemma metric_mem_core_of_mem_interior [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (k : Assignment (metricNestedGeometry hG o hrn).graph.Edge)
    (d : (metricBox hG o r).Vertex)
    (hd : (metricNestedGeometry hG o hrn).vertex d ∈
      interior (G := (metricNestedGeometry hG o hrn).graph)
        (metricRoots hG o r n) k) :
    d ∈ (metricNestedGeometry hG o hrn).core := by
  by_contra hn
  apply hd
  apply subset_closedRegion
  exact Nat.le_of_not_gt hn

/-- **Ordinary metric-box nested equation (9) with the direct arm bound. -/
theorem metricNested_abs_sub_le_arm [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (τ : ((metricBox hG o r).indexedGraph (edgeIndex _)).BoundaryPartition)
    (ξO : (outsideGraph (metricBox hG o n) (metricBox hG o r)).BoundaryPartition)
    (ξ : (metricNestedGeometry hG o hrn).graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (e₀ : ((metricBox hG o r).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (metricBox hG o n) (metricBox hG o r)).Edge)
    (hwireξ : ∀ k : Assignment (metricNestedGeometry hG o hrn).graph.Edge,
      ∀ v, v ∈ interior (G := (metricNestedGeometry hG o hrn).graph)
        (metricRoots hG o r n) k → ∀ w, ξ.r v w → v = w)
    (hwireτ : ∀ k : Assignment (metricNestedGeometry hG o hrn).graph.Edge,
      ∀ d, (metricNestedGeometry hG o hrn).vertex d ∈
        interior (G := (metricNestedGeometry hG o hrn).graph)
          (metricRoots hG o r n) k → ∀ w, τ.r d w → d = w)
    (J : Finset ((metricBox hG o r).indexedGraph (edgeIndex _)).Edge)
    (S : Set (J → Bool)) :
    let X := metricNestedGeometry hG o hrn
    abs ((X.graph.fkPMF hq hp₁.le ξ).toMeasure.real
        {ω | baseCylinder J S (fun d : ((metricBox hG o r).indexedGraph (edgeIndex _)).Edge => ω (Sum.inl d))} -
      (((metricBox hG o r).indexedGraph (edgeIndex _)).fkPMF hq hp₁.le τ).toMeasure.real
        (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (upperArm X J (metricRoots hG o r n)) := by
  intro X
  exact X.windowCopyTriple_abs_sub_le_arm τ ξO ξ hq hp₀ hp₁
    (metricRoots hG o r n) e₀
    (metric_mem_core_of_mem_interior hG o hrn) hwireξ hwireτ J S


lemma metric_large_hwire_of_source [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (hα : FK.Prop42Source.HasSourceBoundaryClass (metricBoxData hG o) α)
    (k : Assignment (metricNestedGeometry hG o hrn).graph.Edge)
    (v : (metricBox hG o n).Vertex)
    (hv : v ∈ interior (G := (metricNestedGeometry hG o hrn).graph)
      (metricRoots hG o r n) k) (w : (metricBox hG o n).Vertex)
    (hvw : ((metricBox hG o n).indexedBoundary (edgeIndex _) α).r v w) : v = w := by
  have hdist : Gph.dist o v.1 < r := by
    by_contra hn
    apply hv
    apply subset_closedRegion
    exact Nat.le_of_not_gt hn
  have hstar : (metricBoxData hG o).StarContained n v := by
    intro e he
    exact FK.RegionConfinement.edge_mem_metricBox_of_dist_lt
      (hG := hG) (N := n) (hdist.trans_le hrn) he
  exact (hα v hstar w hvw).symm

lemma metric_small_hwire_of_source [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (β : (metricBox hG o r).BoundaryPartition)
    (hβ : FK.Prop42Source.HasSourceBoundaryClass (metricBoxData hG o) β)
    (k : Assignment (metricNestedGeometry hG o hrn).graph.Edge)
    (d : (metricBox hG o r).Vertex)
    (hd : (metricNestedGeometry hG o hrn).vertex d ∈
      interior (G := (metricNestedGeometry hG o hrn).graph)
        (metricRoots hG o r n) k) (w : (metricBox hG o r).Vertex)
    (hdw : ((metricBox hG o r).indexedBoundary (edgeIndex _) β).r d w) : d = w := by
  have hcore := metric_mem_core_of_mem_interior hG o hrn k d hd
  have hstar : (metricBoxData hG o).StarContained r d := by
    intro e he
    exact FK.RegionConfinement.edge_mem_metricBox_of_dist_lt
      (hG := hG) (N := r) hcore he
  exact (hβ d hstar w hdw).symm

/-- Metric nested estimate at actual source boundary conventions. -/
theorem metricNested_abs_sub_le_arm_of_source [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) {r n : ℕ} (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (β : (metricBox hG o r).BoundaryPartition)
    (hα : FK.Prop42Source.HasSourceBoundaryClass (metricBoxData hG o) α)
    (hβ : FK.Prop42Source.HasSourceBoundaryClass (metricBoxData hG o) β)
    (ξO : (outsideGraph (metricBox hG o n) (metricBox hG o r)).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (e₀ : ((metricBox hG o r).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (metricBox hG o n) (metricBox hG o r)).Edge)
    (J : Finset ((metricBox hG o r).indexedGraph (edgeIndex _)).Edge)
    (S : Set (J → Bool)) :
    let X := metricNestedGeometry hG o hrn
    abs ((X.graph.fkPMF hq hp₁.le
        ((metricBox hG o n).indexedBoundary (edgeIndex _) α)).toMeasure.real
        {ω | baseCylinder J S (fun d : ((metricBox hG o r).indexedGraph (edgeIndex _)).Edge =>
          ω (Sum.inl d))} -
      (((metricBox hG o r).indexedGraph (edgeIndex _)).fkPMF hq hp₁.le
        ((metricBox hG o r).indexedBoundary (edgeIndex _) β)).toMeasure.real
        (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (upperArm X J (metricRoots hG o r n)) := by
  intro X
  exact metricNested_abs_sub_le_arm hG o hrn
    ((metricBox hG o r).indexedBoundary (edgeIndex _) β) ξO
    ((metricBox hG o n).indexedBoundary (edgeIndex _) α)
    hq hp₀ hp₁ e₀
    (metric_large_hwire_of_source hG o hrn α hα)
    (metric_small_hwire_of_source hG o hrn β hβ) J S

end FK.Adaptive.NestedSumGeometry
