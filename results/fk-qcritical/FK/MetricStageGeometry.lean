import FK.MetricGrowingFamily
import FK.DominatedOuterAssembly

/-! Metric lower balls, finite supports, and exterior-supported outer boundaries. -/

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

/-- A boundary setoid whose nonreflexive pairs have an edge outside
`B.edges` incident at each endpoint.  This is edge-complement support, not
literal outer-vertex support: in a metric box an omitted edge can join two
vertices that both belong to `B.Vertex`. -/
def ExternallySupportedOn {V : Type u} {G : SimpleGraph V} {B : FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G (fun _ : ℕ => B)) (a : B.BoundaryPartition) : Prop :=
  ∀ u v : B.Vertex, u ≠ v → a.r u v →
    (∃ e : G.edgeSet, e ∉ B.edges ∧ data.vertex 0 u ∈ e.1) ∧
    (∃ e : G.edgeSet, e ∉ B.edges ∧ data.vertex 0 v ∈ e.1)

section Metric

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable (hG : G.Connected) (o : V)

/-- Radius that puts both endpoints of one metric-box edge strictly inside the
lower ball at every scale. -/
noncomputable def metricLowerRadius {b : ℕ} (e : (metricBox hG o b).edges) : ℕ :=
  max (G.dist o ((metricBoxData hG o).vertex b ((metricBox hG o b).source e)))
    (G.dist o ((metricBoxData hG o).vertex b ((metricBox hG o b).target e))) + 1

/-- Lower finite vertex ball at scale `m`. -/
noncomputable def metricLowerK {b : ℕ} (e : (metricBox hG o b).edges) (m : ℕ) : Finset V :=
  innerBall hG o (metricLowerRadius hG o e + m)

/-- Finite edge support of every graph edge internal to the lower ball. -/
noncomputable def metricLowerS {b : ℕ} (e : (metricBox hG o b).edges) (m : ℕ) :
    Finset G.edgeSet :=
  (metricBox hG o (metricLowerRadius hG o e + m)).edges

lemma metricLowerK_mono {b : ℕ} (e : (metricBox hG o b).edges) :
    Monotone (metricLowerK hG o e) := by
  intro m n hmn x hx
  apply (mem_innerBall hG).2
  have h := (mem_innerBall hG).1 hx
  omega

lemma metricLowerK_cov {b : ℕ} (e : (metricBox hG o b).edges) (v : V) :
    ∃ m, v ∈ metricLowerK hG o e m := by
  refine ⟨G.dist o v + 1, (mem_innerBall hG).2 ?_⟩
  omega

lemma metricLowerK_endpoints {b : ℕ} (e : (metricBox hG o b).edges) (m : ℕ) :
    (metricBoxData hG o).vertex b ((metricBox hG o b).source e) ∈ metricLowerK hG o e m ∧
    (metricBoxData hG o).vertex b ((metricBox hG o b).target e) ∈ metricLowerK hG o e m := by
  have hs : G.dist o ((metricBoxData hG o).vertex b ((metricBox hG o b).source e)) <
      metricLowerRadius hG o e := by
    exact (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
  have ht : G.dist o ((metricBoxData hG o).vertex b ((metricBox hG o b).target e)) <
      metricLowerRadius hG o e := by
    exact (le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  constructor <;> apply (mem_innerBall hG).2 <;> omega

lemma metricLowerS_support {b : ℕ} (e : (metricBox hG o b).edges) (m : ℕ)
    (f : G.edgeSet) (hf : f.1 ∈ innerEdges (metricLowerK hG o e m)) :
    f ∈ metricLowerS hG o e m := by
  obtain ⟨u, hu, v, hv, heq⟩ := hf
  exact (mem_metricEdges hG o (metricLowerRadius hG o e + m) f).2
    ⟨u, by rw [heq]; exact Sym2.mem_mk_left u v, (mem_innerBall hG).1 hu⟩

/-- Exterior-supported outer boundary classes eventually avoid every lower
ball on all nonreflexive pairs. -/
lemma eventually_far_of_externallySupportedOn_metric
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    {b : ℕ} (e : (metricBox hG o b).edges) (m : ℕ) :
    ∀ᶠ n in atTop, ∀ u v : (metricBox hG o n).Vertex, u ≠ v → (a n).r u v →
      (metricBoxData hG o).vertex n u ∉ metricLowerK hG o e m ∧
      (metricBoxData hG o).vertex n v ∉ metricLowerK hG o e m := by
  filter_upwards [eventually_ge_atTop (metricLowerRadius hG o e + m)] with n hn
  intro u v hne hrel
  obtain ⟨⟨eu, heu, huI⟩, ⟨ev, hev, hvI⟩⟩ := ha n u v hne hrel
  constructor
  · intro hu
    apply heu
    exact (mem_metricEdges hG o n eu).2
      ⟨(metricBoxData hG o).vertex n u, by simpa only [constantBoxData_vertex] using huI,
        ((mem_innerBall hG).1 hu).trans_le hn⟩
  · intro hv
    apply hev
    exact (mem_metricEdges hG o n ev).2
      ⟨(metricBoxData hG o).vertex n v, by simpa only [constantBoxData_vertex] using hvI,
        ((mem_innerBall hG).1 hv).trans_le hn⟩

/-- Dominated weak limits along genuine metric boxes are free DLR whenever the
outer boundary partitions have the required edge-complement incidence support. -/
theorem isDLR_free_of_dominated_metric_outerStage
    {q p : NNReal} (hq : 0 < q) (hq1 : q < 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le a μ)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    (b : ℕ) (ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((metricBox hG o n).finiteVolumeLaw hq hp₁.le (a n)))
    (hnoPerc : ∀ x : V, (ν : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    (metricBox hG o b).IsDLR hq hp₁.le ((metricBoxData hG o).free.partition b)
      ((metricBoxData hG o).free.measurable_partition b) μ := by
  have hμ' : IsFKLimit (metricGrowingFamily hG o).exh hq hp₁.le a μ := hμ
  exact isDLR_free_of_dominated_growingFamily_outerStage
    (F := metricGrowingFamily hG o) (data := metricBoxData hG o)
    (hinj := metricBoxData_vertex_injective hG o)
    (K := fun e => metricLowerK hG o e) (S := fun e => metricLowerS hG o e)
    hq hq1 hp₀ hp₁ a hμ' (fun hkn x => metricGrowingFamily_compat hG o hkn x) b
    (fun e => metricLowerK_mono hG o e) (fun e => metricLowerK_cov hG o e)
    (fun e => metricLowerK_endpoints hG o e)
    (fun e m f hf => metricLowerS_support hG o e m f hf)
    (fun e m => eventually_far_of_externallySupportedOn_metric hG o a ha e m)
    ν hdom hnoPerc

/-- Whole-exhaustion free DLR closure for the same source-compatible metric
boundary schedules. -/
theorem mem_dlrMeasures_free_of_dominated_metric_outerStage
    {q p : NNReal} (hq : 0 < q) (hq1 : q < 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le a μ)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    (ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((metricBox hG o n).finiteVolumeLaw hq hp₁.le (a n)))
    (hnoPerc : ∀ x : V, (ν : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) (metricBoxData hG o).free hq hp₁.le := by
  intro b
  exact isDLR_free_of_dominated_metric_outerStage hG o hq hq1 hp₀ hp₁ a hμ ha b
    ν hdom hnoPerc

/-- Global at-most-one-cluster uniqueness transports the proved free DLR class
to every other geometric convention. -/
theorem mem_dlrMeasures_of_dominated_metric_outerStage
    {q p : NNReal} (hq : 0 < q) (hq1 : q < 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le a μ)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    (ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((metricBox hG o n).finiteVolumeLaw hq hp₁.le (a n)))
    (hnoPerc : ∀ x : V, (ν : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0)
    (Ψ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (hΨ : IsGeometric (metricBoxData hG o).geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) Ψ hq hp₁.le := by
  have hfree := mem_dlrMeasures_free_of_dominated_metric_outerStage hG o
    hq hq1 hp₀ hp₁ a hμ ha ν hdom hnoPerc
  exact ConventionTransport.SimpleGraphBoxData.mem_dlrMeasures_of_global_atMostOne
    (metricBoxExhaustion hG o) (metricBoxData hG o) hq hp₀ hp₁
    (metricBoxData hG o).free Ψ (metricBoxData hG o).free_isGeometric hΨ μ hfree hglobal

end Metric

end FK.NestedFinDLR
