import FK.PrimeStageDomination
import FK.DominatedLimitNonpercolation

/-! Metric prime-majorant closures with global uniqueness derived automatically. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.NestedMetricGeometry

universe u

/-- Prime-dominated metric limits need no separate global at-most-one-cluster
hypothesis: the prime product's nonpercolation is inherited by the limit. -/
theorem mem_dlrMeasures_of_prime_dominated_metric_outerStage_autoGlobal
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp1.le a μ)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    (hnoPerc : ∀ x : V,
      ((FKLimit.bernoulliProduct (fun _ : G.edgeSet => primeUnitInterval hq hp1) :
        ProbabilityMeasure (Configuration G.edgeSet)) : Measure (Configuration G.edgeSet))
        {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0)
    (Ψ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (hΨ : IsGeometric (metricBoxData hG o).geometry Ψ) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) Ψ hq hp1.le := by
  apply mem_dlrMeasures_of_dominated_metric_outerStage_of_nonpercolating_majorant
    hG o hq hq1 hp0 hp1 a hμ ha
    (FKLimit.bernoulliProduct (fun _ : G.edgeSet => primeUnitInterval hq hp1))
    _ hnoPerc Ψ hΨ
  intro n
  exact stochasticallyDominates_bernoulliPrime_finiteVolumeLaw
    (metricBox hG o n) hq hp0 hp1 hq1 (a n)

/-- Subcritical prime-rate metric closure with externally supported stages.
Both rootwise nonpercolation and global convention uniqueness are derived;
neither is an input. -/
theorem mem_dlrMeasures_of_subcritical_prime_metric_outerStage_autoGlobal
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp1.le a μ)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    (hs : ∀ x : V, ((primeUnitInterval hq hp1 : unitInterval) : ℝ) < criticalProb G x)
    (Ψ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (hΨ : IsGeometric (metricBoxData hG o).geometry Ψ) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) Ψ hq hp1.le :=
  mem_dlrMeasures_of_prime_dominated_metric_outerStage_autoGlobal
    hG o hq hq1 hp0 hp1 a hμ ha
    (bernoulliProduct_prime_noPerc_of_subcritical hG hq hp1 hs) Ψ hΨ

/-- For a genuinely free finite-stage schedule, exterior support is vacuous.
Only subcriticality of the prime product and geometricity of the target
convention remain beyond the weak limit and parameter hypotheses. -/
theorem mem_dlrMeasures_of_subcritical_prime_metric_freeStage_autoGlobal
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp1.le
      (fun n => (metricBox hG o n).graph.freeBoundary) μ)
    (hs : ∀ x : V, ((primeUnitInterval hq hp1 : unitInterval) : ℝ) < criticalProb G x)
    (Ψ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (hΨ : IsGeometric (metricBoxData hG o).geometry Ψ) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) Ψ hq hp1.le :=
  mem_dlrMeasures_of_subcritical_prime_metric_outerStage_autoGlobal
    hG o hq hq1 hp0 hp1 (fun n => (metricBox hG o n).graph.freeBoundary)
    hμ (fun n => externallySupportedOn_metric_free hG o n) hs Ψ hΨ
