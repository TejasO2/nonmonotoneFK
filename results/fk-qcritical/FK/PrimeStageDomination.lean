import FK.MetricStageGeometry
import FK.ActualDLRComparisons
import FK.GibbsOrder
import FK.SubcriticalPercolation

/-! Global stochastic majorants of finite-volume FK laws from interior comparisons. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Topology BigOperators

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume

universe u v

/-- The prime upper random-cluster rate as a unit-interval parameter. -/
noncomputable def primeUnitInterval {q p : NNReal} (hq : 0 < q) (hp1 : p < 1) : unitInterval :=
  ⟨FK.prime (q : ℝ) (p : ℝ),
    FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le)⟩

/-- An interior upper comparison against a Bernoulli product gives global
stochastic domination of the actual finite-volume law.  No finite-support
assumption on the test event is needed. -/
theorem stochasticallyDominates_finiteVolumeLaw_of_upper
    {E : Type u} [Countable E] (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (α : B.BoundaryPartition) (r : E → unitInterval)
    (hlocal : FKEnhancement.StochasticallyDominates (B.graph.fkMeasure hq hp α)
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1))) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r)
      (B.finiteVolumeLaw hq hp α) := by
  intro A hA hAup
  let T : Configuration E → Configuration E :=
    fun ω => B.glue (B.closedExterior, B.interiorRestriction ω)
  have hT : Measurable T :=
    (B.measurable_glue_const_left B.closedExterior).comp B.measurable_interiorRestriction
  have hTmono : ∀ {ω η : Configuration E}, ω ≤ η → T ω ≤ T η := by
    intro ω η hωη e
    by_cases he : e ∈ B.edges
    · simp only [T, FiniteBox.glue, he, dite_true]
      change (B.split ω).2 ⟨e, he⟩ ≤ (B.split η).2 ⟨e, he⟩
      exact hωη e
    · simp [T, FiniteBox.glue, he]
  have hTle : ∀ ω : Configuration E, T ω ≤ ω := by
    intro ω e
    by_cases he : e ∈ B.edges
    · simp only [T, FiniteBox.glue, he, dite_true]
      change (B.split ω).2 ⟨e, he⟩ ≤ ω e
      exact le_rfl
    · simp [T, FiniteBox.glue, FiniteBox.closedExterior, he]
  have hdep : FKLimit.DependsOnCoordinates (T ⁻¹' A) B.edges := by
    intro ω η hωη
    have hEq : T ω = T η := by
      funext e
      by_cases he : e ∈ B.edges
      · simp only [T, FiniteBox.glue, he, dite_true]
        exact hωη e he
      · simp [T, FiniteBox.glue, he]
    change (T ω ∈ A) ↔ (T η ∈ A)
    rw [hEq]
  have hAup' : IsUpperSet (T ⁻¹' A) := by
    intro ω η hωη hω
    exact hAup (hTmono hωη) hω
  have hA'meas : MeasurableSet (T ⁻¹' A) := hT hA
  have hmap : Measure.map T (B.finiteVolumeLaw hq hp α : Measure (Configuration E)) =
      (B.finiteVolumeLaw hq hp α : Measure (Configuration E)) := by
    rw [FiniteBox.finiteVolumeLaw_coe hq hp B α,
      Measure.map_map hT (B.measurable_glue_const_left B.closedExterior)]
    congr 1
    funext ξ
    simp [T]
  have hsub : T ⁻¹' A ⊆ A := by
    intro ω hω
    exact hAup (hTle ω) hω
  apply (FK.InfiniteVolume.probMeasure_apply_le_iff _ _ _).mpr
  calc
    (B.finiteVolumeLaw hq hp α : Measure (Configuration E)) A =
        (Measure.map T (B.finiteVolumeLaw hq hp α : Measure (Configuration E))) A :=
      congrArg (fun m : Measure (Configuration E) => m A) hmap.symm
    _ = (B.finiteVolumeLaw hq hp α : Measure (Configuration E)) (T ⁻¹' A) :=
      Measure.map_apply hT hA
    _ ≤ (FKLimit.bernoulliProduct r : Measure (Configuration E)) (T ⁻¹' A) := by
      apply (FK.InfiniteVolume.probMeasure_apply_le_iff _ _ _).mp
      exact B.le_apply_finiteVolumeLaw_local_upper hq hp α r hlocal hA'meas hAup' hdep
    _ ≤ (FKLimit.bernoulliProduct r : Measure (Configuration E)) A := measure_mono hsub

/-- Plain finite FK comparison by the homogeneous prime-rate product, obtained
from the canonical path comparison with empty enhancement. -/
theorem fkMeasure_le_bernoulliProduct_primeUnit
    (H : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (ξ : H.BoundaryPartition) (hne : Nonempty H.Edge) :
    FKEnhancement.StochasticallyDominates (H.fkMeasure hq hp1.le ξ)
      (FKEnhancement.bernoulliProduct (fun _ => primeUnitInterval hq hp1)) := by
  have hcomp :=
    FKEnhancement.CanonicalDynamics.graphConnectionEvent_upper_path_comparison_canonical
      H hq hp0 hp1 hq1 ξ ∅ (fun _ => (∅ : Set (Finset H.Edge)))
      (by intro e he; simp at he) (by intro e he; simp at he) hne
  rw [FK.EnhancedTransport.upperProductPMF_map_configToBool_toMeasure (∅ : Finset H.Edge)
    (⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩ : (p : ℝ) ∈ Set.Icc 0 1)
    (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity)
      (by exact_mod_cast hp1.le)).2
    (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
      (by exact_mod_cast hq) (by exact_mod_cast hp0) (by exact_mod_cast hp1)
      (by exact_mod_cast hq1)).le (fun _ => (∅ : Set (Finset H.Edge)))] at hcomp
  simp only [FK.Finite.LabelledMultigraph.fkMeasure, OpenPath.upperProductParameters,
    FKLimit.unitParameters, primeUnitInterval] at hcomp ⊢
  exact hcomp

/-- Explicit prime-rate Bernoulli majorant of every finite-volume FK stage,
at arbitrary boundary setoid, including the empty edge box. -/
theorem stochasticallyDominates_bernoulliPrime_finiteVolumeLaw
    {E : Type u} [Countable E] (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (α : B.BoundaryPartition) :
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct (fun _ => primeUnitInterval hq hp1))
      (B.finiteVolumeLaw hq hp1.le α) := by
  classical
  by_cases hne : Nonempty B.edges
  · apply stochasticallyDominates_finiteVolumeLaw_of_upper B hq hp1.le α
    exact fkMeasure_le_bernoulliProduct_primeUnit B.graph hq hp0 hp1 hq1 α hne
  · apply stochasticallyDominates_finiteVolumeLaw_of_upper B hq hp1.le α
    haveI : Subsingleton B.graph.Configuration :=
      ⟨fun ω η => funext (fun e => (hne ⟨e⟩).elim)⟩
    haveI : IsProbabilityMeasure (B.graph.fkMeasure hq hp1.le α) :=
      FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp1.le α
    have hEq : B.graph.fkMeasure hq hp1.le α =
        FKEnhancement.bernoulliProduct (fun _ : B.edges => primeUnitInterval hq hp1) := by
      apply MeasureTheory.Measure.ext
      intro s hs
      by_cases hempty : s = ∅
      · simp [hempty]
      · have huniv : s = Set.univ := by
          apply Set.eq_univ_iff_forall.mpr
          intro ω
          obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr hempty
          rwa [Subsingleton.elim ω η]
        simp [huniv]
    intro A hA hAup
    rw [hEq]

/-- Metric weak limits with edge-complement-supported boundaries are DLR on the
canonical metric exhaustion for every geometric boundary assignment, under
rootwise nonpercolation of the explicit prime-rate Bernoulli majorant. -/
theorem mem_dlrMeasures_of_prime_dominated_metric_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ∀ n, (NestedMetricGeometry.metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (NestedMetricGeometry.metricBoxExhaustion hG o) hq hp1.le a μ)
    (ha : ∀ n, ExternallySupportedOn
      (constantBoxData (NestedMetricGeometry.metricBoxData hG o) n) (a n))
    (hnoPerc : ∀ x : V,
      ((FKLimit.bernoulliProduct
        (fun _ : G.edgeSet => primeUnitInterval hq hp1) :
          ProbabilityMeasure (Configuration G.edgeSet)) : Measure (Configuration G.edgeSet))
        {ω | {z : V | CurvatureVariance.Infra.Percolation.OpenConnected G ω Set.univ x z}.Infinite} = 0)
    (Ψ : BoundaryAssignment (NestedMetricGeometry.metricBoxExhaustion hG o).box)
    (hΨ : ConventionTransport.IsGeometric (NestedMetricGeometry.metricBoxData hG o).geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures (NestedMetricGeometry.metricBoxExhaustion hG o) Ψ hq hp1.le := by
  apply mem_dlrMeasures_of_dominated_metric_outerStage hG o hq hq1 hp0 hp1 a hμ ha
    (FKLimit.bernoulliProduct (fun _ : G.edgeSet => primeUnitInterval hq hp1))
    _ hnoPerc Ψ hΨ hglobal
  intro n
  exact stochasticallyDominates_bernoulliPrime_finiteVolumeLaw
    (NestedMetricGeometry.metricBox hG o n) hq hp0 hp1 hq1 (a n)

/-- Rootwise nonpercolation of the prime product below the ordinary Bernoulli
critical probability at each root. -/
lemma bernoulliProduct_prime_noPerc_of_subcritical
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) {q p : NNReal} (hq : 0 < q) (hp1 : p < 1)
    (hs : ∀ x : V, ((primeUnitInterval hq hp1 : unitInterval) : ℝ) <
      CurvatureVariance.Infra.Percolation.criticalProb G x) :
    ∀ x : V,
      ((FKLimit.bernoulliProduct (fun _ : G.edgeSet => primeUnitInterval hq hp1) :
        ProbabilityMeasure (Configuration G.edgeSet)) : Measure (Configuration G.edgeSet))
        {ω | {z : V | CurvatureVariance.Infra.Percolation.OpenConnected G ω Set.univ x z}.Infinite} = 0 := by
  intro x
  have h := CurvatureVariance.Infra.Percolation.percolationProb_eq_zero_of_lt_criticalProb
    hG (hs x)
  rw [CurvatureVariance.Infra.Percolation.percolationProb_eq] at h
  exact h

/-- Subcritical-parameter form of the metric-exhaustion DLR theorem. -/
theorem mem_dlrMeasures_of_subcritical_prime_metric_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (a : ∀ n, (NestedMetricGeometry.metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (NestedMetricGeometry.metricBoxExhaustion hG o) hq hp1.le a μ)
    (ha : ∀ n, ExternallySupportedOn
      (constantBoxData (NestedMetricGeometry.metricBoxData hG o) n) (a n))
    (hs : ∀ x : V, ((primeUnitInterval hq hp1 : unitInterval) : ℝ) <
      CurvatureVariance.Infra.Percolation.criticalProb G x)
    (Ψ : BoundaryAssignment (NestedMetricGeometry.metricBoxExhaustion hG o).box)
    (hΨ : ConventionTransport.IsGeometric (NestedMetricGeometry.metricBoxData hG o).geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures (NestedMetricGeometry.metricBoxExhaustion hG o) Ψ hq hp1.le := by
  exact mem_dlrMeasures_of_prime_dominated_metric_outerStage hG o hq hq1 hp0 hp1 a hμ ha
    (bernoulliProduct_prime_noPerc_of_subcritical hG hq hp1 hs) Ψ hΨ hglobal

end FK.NestedFinDLR
