import FK.MetricGeometryExtensions
import FK.EssentialWindow

/-! Nonpercolation and convention uniqueness inherited by dominated FK limits. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.NestedMetricGeometry

universe u

/-- One-sided stochastic majoration passes through an FK weak limit. -/
theorem stochasticallyDominates_fkLimit_of_stages
    {E : Type u} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : IsFKLimit exh hq hp a μ)
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((exh.box n).finiteVolumeLaw hq hp (a n))) :
    FKLimit.StochasticallyDominates ν μ :=
  FKLimit.stochasticallyDominates_of_tendsto hμ tendsto_const_nhds hdom

/-- The event that one specified root has an infinite open cluster is
measurable on a connected locally finite graph. -/
lemma measurableSet_rootInfiniteCluster
    {V : Type u} [Countable V] (G : SimpleGraph V) [G.LocallyFinite]
    (hG : G.Connected) (x : V) :
    MeasurableSet {ω : G.edgeSet → Bool |
      {z : V | OpenConnected G ω Set.univ x z}.Infinite} := by
  rw [setOf_infinite_eq_iInter_armEvent hG x]
  exact MeasurableSet.iInter fun n => measurableSet_armEvent x n

/-- The one-root infinite-cluster event is increasing. -/
lemma isUpperSet_rootInfiniteCluster
    {V : Type u} (G : SimpleGraph V) (x : V) :
    IsUpperSet {ω : G.edgeSet → Bool |
      {z : V | OpenConnected G ω Set.univ x z}.Infinite} := by
  intro ω η hωη hω
  apply Set.Infinite.mono (s := {z : V | OpenConnected G ω Set.univ x z})
  · intro z hz
    exact OpenConnected.mono_config hz hωη
  · exact hω

/-- Rootwise nonpercolation of a uniform majorant passes to every dominated
FK weak limit. -/
theorem rootwise_nonpercolating_of_dominated_fkLimit
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (exh : BoxExhaustion G.edgeSet)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : IsFKLimit exh hq hp a μ)
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((exh.box n).finiteVolumeLaw hq hp (a n)))
    (hnoPerc : ∀ x : V, (ν : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    ∀ x : V, (μ : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0 := by
  have hlim : FKLimit.StochasticallyDominates ν μ :=
    stochasticallyDominates_fkLimit_of_stages exh hq hp a μ ν hμ hdom
  intro x
  exact FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates hlim
    (measurableSet_rootInfiniteCluster G hG x)
    (isUpperSet_rootInfiniteCluster G x) (hnoPerc x)

/-- Rootwise null infinite-cluster events give almost-sure global at-most-one
cluster uniqueness (indeed, almost-sure nonpercolation). -/
theorem ae_globalAtMostOne_of_rootwise_nonpercolating
    {V : Type u} [Countable V] (G : SimpleGraph V)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hnoPerc : ∀ x : V, (μ : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω := by
  have hfin : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ∀ x : V, {z : V | OpenConnected G ω Set.univ x z}.Finite := by
    rw [ae_all_iff]
    intro x
    rw [ae_iff]
    simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.Infinite, not_not] using hnoPerc x
  filter_upwards [hfin] with ω hω
  intro x y hx _hy
  exact (hx (hω x)).elim

/-- A nonpercolating uniform majorant supplies the global uniqueness input of
convention transport automatically. -/
theorem ae_globalAtMostOne_of_dominated_fkLimit
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (exh : BoxExhaustion G.edgeSet)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : IsFKLimit exh hq hp a μ)
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((exh.box n).finiteVolumeLaw hq hp (a n)))
    (hnoPerc : ∀ x : V, (ν : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω :=
  ae_globalAtMostOne_of_rootwise_nonpercolating G
    (rootwise_nonpercolating_of_dominated_fkLimit hG exh hq hp a μ ν hμ hdom hnoPerc)

/-- Strengthened dominated metric closure: the global at-most-one-cluster
hypothesis is derived from the same nonpercolating majorant, not assumed. -/
theorem mem_dlrMeasures_of_dominated_metric_outerStage_of_nonpercolating_majorant
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hq1 : q < 1) (hp₀ : 0 < p) (hp₁ : p < 1)
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
    (hΨ : IsGeometric (metricBoxData hG o).geometry Ψ) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) Ψ hq hp₁.le := by
  have hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω :=
    ae_globalAtMostOne_of_dominated_fkLimit hG (metricBoxExhaustion hG o)
      hq hp₁.le a μ ν hμ hdom hnoPerc
  exact mem_dlrMeasures_of_dominated_metric_outerStage hG o hq hq1 hp₀ hp₁
    a hμ ha ν hdom hnoPerc Ψ hΨ hglobal
