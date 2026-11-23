import FK.CoherentMixtures
import FK.NoncoherentStabilization
import FK.EndpointGlobalFiniteEnergy

/-!
# Assembly of coherent weak limits by normalized binary mixtures

The new analytic input is weak convergence of the actual binary mixture, not
merely convexity of a DLR class for an already specified limiting measure.
There are two consequences.  First, two genuinely varying boundary sources
with joint local stabilization have a common limiting specification for their
mixture.  Second, two arbitrary-exterior coherent conditional-law sequences
have an explicit mixed weak limit; global at-most-one-cluster uniqueness on
both components transports that limit to any geometric target specification.

Nothing here asserts DLR membership for an arbitrary noncoherent FK limit.
Every stabilization, geometric, and global-uniqueness hypothesis is retained.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.CoherentLimitAssembly

open CoherentMixtures NoncoherentStabilization ConventionTransport EndpointGlobalFiniteEnergy

noncomputable section

/-- Weak convergence is preserved by normalized binary convex combinations.
The approximating mixtures and the limiting mixture use the same weight. -/
theorem tendsto_convexCombination {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {ι : Type*} {l : Filter ι}
    {μs νs : ι → ProbabilityMeasure Ω} {μ ν : ProbabilityMeasure Ω}
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (t : unitInterval) :
    Tendsto (fun i => convexCombination (μs i) (νs i) t) l
      (𝓝 (convexCombination μ ν t)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hμ hν
  have hμ' := hμ f
  have hν' := hν f
  let c : NNReal := unitInterval.toNNReal t
  let d : NNReal := unitInterval.toNNReal (unitInterval.symm t)
  change Tendsto (fun i => ∫ ω, f ω ∂(c • (μs i : Measure Ω) +
    d • (νs i : Measure Ω))) l
      (𝓝 (∫ ω, f ω ∂(c • (μ : Measure Ω) + d • (ν : Measure Ω))))
  have hrewrite (P : ProbabilityMeasure Ω) (Q : ProbabilityMeasure Ω) :
      (∫ ω, f ω ∂(c • (P : Measure Ω) + d • (Q : Measure Ω))) =
        c • (∫ ω, f ω ∂(P : Measure Ω)) +
          d • (∫ ω, f ω ∂(Q : Measure Ω)) := by
    rw [integral_add_measure
      (f.integrable (P : Measure Ω)).smul_measure_nnreal
      (f.integrable (Q : Measure Ω)).smul_measure_nnreal,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp_rw [hrewrite]
  exact (hμ'.const_smul c).add (hν'.const_smul d)

/-- An almost-everywhere property common to both components holds for their
normalized binary convex combination. -/
theorem ae_convexCombination {Ω : Type*} [MeasurableSpace Ω]
    {P : Ω → Prop} (μ ν : ProbabilityMeasure Ω) (t : unitInterval)
    (hμ : ∀ᵐ ω ∂(μ : Measure Ω), P ω)
    (hν : ∀ᵐ ω ∂(ν : Measure Ω), P ω) :
    ∀ᵐ ω ∂(convexCombination μ ν t : Measure Ω), P ω := by
  rw [ae_iff] at hμ hν ⊢
  change ((unitInterval.toNNReal t • (μ : Measure Ω) +
    unitInterval.toNNReal (unitInterval.symm t) • (ν : Measure Ω)))
      {ω | ¬ P ω} = 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hμ, hν]
  simp

/-- The exterior marginal of a binary mixture is the binary mixture of its
exterior marginals, with exactly the same normalized weights. -/
theorem exteriorMeasure_convexCombination {E : Type*} (B : FiniteBox E)
    (μ ν : ProbabilityMeasure (Configuration E)) (t : unitInterval) :
    B.exteriorMeasure (convexCombination μ ν t) =
      convexCombination (B.exteriorMeasure μ) (B.exteriorMeasure ν) t := by
  let π : Configuration E → B.Exterior := fun ω => (B.splitEquiv ω).1
  have hπ : Measurable π := measurable_fst.comp B.splitEquiv.measurable
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map π
    (unitInterval.toNNReal t • (μ : Measure (Configuration E)) +
      unitInterval.toNNReal (unitInterval.symm t) • (ν : Measure (Configuration E))) =
    unitInterval.toNNReal t • Measure.map π (μ : Measure (Configuration E)) +
      unitInterval.toNNReal (unitInterval.symm t) • Measure.map π (ν : Measure (Configuration E))
  rw [Measure.map_add _ _ hπ,
    Measure.map_smul _ hπ.aemeasurable, Measure.map_smul _ hπ.aemeasurable]

/-- A common fixed specification has DLR weak closure for the actual mixed
sequence.  Its induced exterior law and the required local-constancy set are
computed directly from the two components; no geometric uniqueness is used. -/
theorem tendsto_and_mem_dlrMeasures_convexCombination
    {E ι : Type*} [Countable E] (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {l : Filter ι} [l.NeBot]
    {μs νs : ι → ProbabilityMeasure (Configuration E)}
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hDLRμ : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp)
    (hDLRν : ∀ᶠ i in l, νs i ∈ DLRMeasures exh Φ hq hp)
    (hlocalμ : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ :
      Measure (exh.box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, Φ.partition n ζ = Φ.partition n η)
    (hlocalν : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure ν :
      Measure (exh.box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, Φ.partition n ζ = Φ.partition n η)
    (t : unitInterval) :
    Tendsto (fun i => convexCombination (μs i) (νs i) t) l
        (𝓝 (convexCombination μ ν t)) ∧
      convexCombination μ ν t ∈ DLRMeasures exh Φ hq hp := by
  have hlim := tendsto_convexCombination hμ hν t
  refine ⟨hlim, NonlocalInterior.mem_dlrMeasures_of_tendsto_of_ae_eventually_eq
    exh Φ hq hp hlim ?_ ?_⟩
  · filter_upwards [hDLRμ, hDLRν] with i hμi hνi
    exact mem_dlrMeasures_convexCombination exh Φ hq hp _ _ t hμi hνi
  · intro n
    rw [exteriorMeasure_convexCombination]
    exact ae_convexCombination _ _ t (hlocalμ n) (hlocalν n)

/-- Two varying-source weak limits with joint local stabilization assemble
into an actual weakly convergent mixture for the same target specification.
The two source assignments may differ at every index. -/
theorem tendsto_and_mem_dlrMeasures_convexCombination_of_locallyStabilizes
    {E ι : Type*} [Countable E] (exh : BoxExhaustion E)
    (α β : ι → BoundaryAssignment exh.box) (γ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {l : Filter ι} [l.NeBot]
    {μs νs : ι → ProbabilityMeasure (Configuration E)}
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    (hDLRμ : ∀ n, ∀ᶠ i in l, (exh.box n).IsDLR hq hp
      ((α i).partition n) ((α i).measurable_partition n) (μs i))
    (hDLRν : ∀ n, ∀ᶠ i in l, (exh.box n).IsDLR hq hp
      ((β i).partition n) ((β i).measurable_partition n) (νs i))
    (hstabμ : ∀ n, LocallyStabilizes l
      ((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior)
      (fun i => (α i).partition n) (γ.partition n))
    (hstabν : ∀ n, LocallyStabilizes l
      ((exh.box n).exteriorMeasure ν : Measure (exh.box n).Exterior)
      (fun i => (β i).partition n) (γ.partition n))
    (hlocalμ : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ :
      Measure (exh.box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, γ.partition n ζ = γ.partition n η)
    (hlocalν : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure ν :
      Measure (exh.box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, γ.partition n ζ = γ.partition n η)
    (t : unitInterval) :
    Tendsto (fun i => convexCombination (μs i) (νs i) t) l
        (𝓝 (convexCombination μ ν t)) ∧
      convexCombination μ ν t ∈ DLRMeasures exh γ hq hp := by
  refine ⟨tendsto_convexCombination hμ hν t,
    mem_dlrMeasures_convexCombination exh γ hq hp μ ν t ?_ ?_⟩
  · exact mem_dlrMeasures_of_tendsto_of_locallyStabilizes
      exh α γ hq hp hμ hDLRμ hstabμ hlocalμ
  · exact mem_dlrMeasures_of_tendsto_of_locallyStabilizes
      exh β γ hq hp hν hDLRν hstabν hlocalν

/-- Two arbitrary-exterior coherent conditional-law sequences have an explicit
weakly convergent binary mixture.  Componentwise global at-most-one-cluster
uniqueness places both limits, and hence their mixture, in every geometric
target Gibbs class.  The source conventions and exterior configurations may
be genuinely different. -/
theorem tendsto_and_mem_gibbsMeasures_convexCombination_of_tendsto_conditionalLaw
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ Ψ Θ : BoundaryConvention exh hq hp)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ.toBoundaryAssignment)
    (hΘ : ConventionTransport.IsGeometric data.geometry Θ.toBoundaryAssignment)
    (η ζ : ∀ n, (exh.box n).Exterior)
    {μ ν : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hν : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (Ψ.partition n) (ζ n)) atTop (𝓝 ν))
    (hglobalμ : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω)
    (hglobalν : ∀ᵐ ω ∂(ν : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω)
    (t : unitInterval) :
    Tendsto (fun n => convexCombination
        ((exh.box n).conditionalLaw hq hp (Φ.partition n) (η n))
        ((exh.box n).conditionalLaw hq hp (Ψ.partition n) (ζ n)) t) atTop
        (𝓝 (convexCombination μ ν t)) ∧
      convexCombination μ ν t ∈ GibbsMeasures exh Θ := by
  refine ⟨tendsto_convexCombination hμ hν t,
    mem_gibbsMeasures_convexCombination exh Θ μ ν t ?_ ?_⟩
  · exact mem_gibbsMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
      exh data hq hp Φ Θ hΦ hΘ η hμ hglobalμ
  · exact mem_gibbsMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne_of_le_one
      exh data hq hp Ψ Θ hΨ hΘ ζ hν hglobalν

/-- Closed-exterior finite-volume specialization of coherent mixture
assembly.  This is a statement about ordinary `finiteVolumeLaw` sequences,
not only about an abstract limiting pair. -/
theorem tendsto_and_mem_gibbsMeasures_convexCombination_of_tendsto_finiteVolumeLaw
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ Ψ Θ : BoundaryConvention exh hq hp)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ.toBoundaryAssignment)
    (hΘ : ConventionTransport.IsGeometric data.geometry Θ.toBoundaryAssignment)
    {μ ν : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hν : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      (Ψ.partition n (exh.box n).closedExterior)) atTop (𝓝 ν))
    (hglobalμ : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω)
    (hglobalν : ∀ᵐ ω ∂(ν : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω)
    (t : unitInterval) :
    Tendsto (fun n => convexCombination
        ((exh.box n).finiteVolumeLaw hq hp
          (Φ.partition n (exh.box n).closedExterior))
        ((exh.box n).finiteVolumeLaw hq hp
          (Ψ.partition n (exh.box n).closedExterior)) t) atTop
        (𝓝 (convexCombination μ ν t)) ∧
      convexCombination μ ν t ∈ GibbsMeasures exh Θ := by
  apply tendsto_and_mem_gibbsMeasures_convexCombination_of_tendsto_conditionalLaw
    exh data Φ Ψ Θ hΦ hΨ hΘ (fun n => (exh.box n).closedExterior)
      (fun n => (exh.box n).closedExterior) _ _ hglobalμ hglobalν t
  · simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using hμ
  · simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using hν

/-- The mixed coherent limit also inherits almost-sure global
at-most-one-cluster uniqueness directly from its two components. -/
theorem ae_globalAtMostOne_convexCombination
    {V : Type*} {G : SimpleGraph V}
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet)) (t : unitInterval)
    (hμ : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω)
    (hν : ∀ᵐ ω ∂(ν : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    ∀ᵐ ω ∂(convexCombination μ ν t : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω :=
  ae_convexCombination μ ν t hμ hν

/-- Exterior geometric uniqueness propagates to the mixed law on every box.
The proof uses the exact mixed exterior marginal, not an additional null-set
assumption on the limit. -/
theorem aeAtMostOne_convexCombination
    {E : Type*} {box : ℕ → FiniteBox E} (geo : ExteriorGeometry box)
    (μ ν : ProbabilityMeasure (Configuration E)) (t : unitInterval)
    (hμ : AEAtMostOne geo μ) (hν : AEAtMostOne geo ν) :
    AEAtMostOne geo (convexCombination μ ν t) := by
  intro n
  rw [exteriorMeasure_convexCombination]
  exact ae_convexCombination _ _ t (hμ n) (hν n)

end

end FK.InfiniteVolume.CoherentLimitAssembly

#print axioms FK.InfiniteVolume.CoherentLimitAssembly.tendsto_convexCombination
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.ae_convexCombination
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.exteriorMeasure_convexCombination
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.tendsto_and_mem_dlrMeasures_convexCombination
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.tendsto_and_mem_dlrMeasures_convexCombination_of_locallyStabilizes
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.tendsto_and_mem_gibbsMeasures_convexCombination_of_tendsto_conditionalLaw
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.tendsto_and_mem_gibbsMeasures_convexCombination_of_tendsto_finiteVolumeLaw
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.ae_globalAtMostOne_convexCombination
#print axioms FK.InfiniteVolume.CoherentLimitAssembly.aeAtMostOne_convexCombination
