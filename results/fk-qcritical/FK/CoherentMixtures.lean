import FK.ConventionEndpoints

/-!
# Convexity and general mixtures of FK DLR laws

The DLR equation is linear in the exterior marginal. This file proves that
its class is closed not only under binary convex combinations, but under an
arbitrary probability-weighted Markov-kernel mixture. No coherence of the
boundary assignment is needed.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.CoherentMixtures

noncomputable section

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

local instance fintypeSetoid (V : Type*) [Finite V] : Fintype (Setoid V) :=
  Fintype.ofFinite _

/-- Pushforward commutes with a measurable kernel mixture. -/
lemma map_bind {ι Ω Χ : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    [MeasurableSpace Χ] (ρ : Measure ι) (κ : Kernel ι Ω)
    (f : Ω → Χ) (hf : Measurable f) :
    Measure.map f (ρ.bind κ) = ρ.bind (κ.map f) := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) κ.aemeasurable,
    Measure.bind_apply hs (κ.map f).aemeasurable]
  apply lintegral_congr
  intro i
  exact (Kernel.map_apply' κ hf i hs).symm

/-- A measure/kernel comp-product distributes over a mixture of its left
marginal. -/
lemma compProd_bind {ι Ω Χ : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    [MeasurableSpace Χ] (ρ : Measure ι) (κ : Kernel ι Ω) [IsMarkovKernel κ]
    (K : Kernel Ω Χ) [IsMarkovKernel K] [IsProbabilityMeasure ρ] :
    (ρ.bind κ) ⊗ₘ K = ρ.bind (κ ⊗ₖ Kernel.prodMkLeft ι K) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.lintegral_bind κ.aemeasurable
      (Kernel.measurable_kernel_prodMk_left hs).aemeasurable,
    Measure.bind_apply hs (κ ⊗ₖ Kernel.prodMkLeft ι K).aemeasurable]
  apply lintegral_congr
  intro i
  rw [Kernel.compProd_apply hs]
  rfl

/-- The comp-product with a varying left marginal, packaged directly as a
kernel composition product. -/
lemma compProd_eq_kernelCompProd {ι Ω Χ : Type*} [MeasurableSpace ι]
    [MeasurableSpace Ω] [MeasurableSpace Χ] (κ : Kernel ι Ω)
    (K : Kernel Ω Χ) [IsMarkovKernel κ] [IsMarkovKernel K] (i : ι) :
    (κ i) ⊗ₘ K = (κ ⊗ₖ Kernel.prodMkLeft ι K) i := by
  ext s hs
  rw [Measure.compProd_apply hs, Kernel.compProd_apply hs]
  rfl

/-- The probability law attached to one output of a Markov kernel. -/
noncomputable def outputLaw {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    (κ : Kernel ι Ω) [IsMarkovKernel κ] (i : ι) : ProbabilityMeasure Ω :=
  ⟨κ i, inferInstance⟩

/-- A probability-weighted mixture of the output laws of a Markov kernel. -/
noncomputable def mixture {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    (ρ : Measure ι) [IsProbabilityMeasure ρ] (κ : Kernel ι Ω) [IsMarkovKernel κ] :
    ProbabilityMeasure Ω :=
  ⟨ρ.bind κ, isProbabilityMeasure_bind κ.aemeasurable
    (ae_of_all _ fun _ => inferInstance)⟩

@[simp] lemma coe_mixture {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    (ρ : Measure ι) [IsProbabilityMeasure ρ] (κ : Kernel ι Ω) [IsMarkovKernel κ] :
    (mixture ρ κ : Measure Ω) = ρ.bind κ := rfl

@[simp] lemma outputLaw_toMeasure {ι Ω : Type*} [MeasurableSpace ι]
    [MeasurableSpace Ω] (κ : Kernel ι Ω) [IsMarkovKernel κ] (i : ι) :
    (outputLaw κ i : Measure Ω) = κ i := rfl

/-- The exact DLR equation is inherited by an arbitrary probability-weighted
Markov-kernel mixture of DLR laws. The boundary assignment and its FK kernel
are fixed; only the law being mixed varies. -/
theorem isDLR_mixture {E : Type*} (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {ι : Type*} [MeasurableSpace ι]
    (ρ : Measure ι) [IsProbabilityMeasure ρ]
    (κ : Kernel ι (Configuration E)) [IsMarkovKernel κ]
    (hκ : ∀ i, B.IsDLR hq hp α hα (outputLaw κ i)) :
    B.IsDLR hq hp α hα (mixture ρ κ) := by
  let π : Configuration E → B.Exterior := fun ω => (B.splitEquiv ω).1
  have hπ : Measurable π := measurable_fst.comp B.splitEquiv.measurable
  let K := B.fkKernel hq hp α hα
  haveI : IsMarkovKernel (κ.map π) := ProbabilityTheory.Kernel.IsMarkovKernel.map κ hπ
  haveI : IsMarkovKernel (κ.map B.splitEquiv) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map κ B.splitEquiv.measurable
  have hkernel : κ.map B.splitEquiv =
      (κ.map π) ⊗ₖ Kernel.prodMkLeft ι K := by
    apply Kernel.ext
    intro i
    rw [Kernel.map_apply _ B.splitEquiv.measurable, ← compProd_eq_kernelCompProd]
    change Measure.map B.splitEquiv (outputLaw κ i : Measure (Configuration E)) =
      (κ.map π i) ⊗ₘ K
    rw [Kernel.map_apply _ hπ]
    exact hκ i
  change Measure.map B.splitEquiv (ρ.bind κ) =
    (B.exteriorMeasure (mixture ρ κ) : Measure B.Exterior) ⊗ₘ K
  change Measure.map B.splitEquiv (ρ.bind κ) = (Measure.map π (ρ.bind κ)) ⊗ₘ K
  rw [map_bind ρ κ B.splitEquiv B.splitEquiv.measurable,
    map_bind ρ κ π hπ, hkernel, ← compProd_bind]

/-- DLR classes are closed under general Markov-kernel mixtures. -/
theorem mem_dlrMeasures_mixture {E : Type*} (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {ι : Type*} [MeasurableSpace ι]
    (ρ : Measure ι) [IsProbabilityMeasure ρ]
    (κ : Kernel ι (Configuration E)) [IsMarkovKernel κ]
    (hκ : ∀ i, outputLaw κ i ∈ DLRMeasures exh Φ hq hp) :
    mixture ρ κ ∈ DLRMeasures exh Φ hq hp := by
  intro n
  exact isDLR_mixture (exh.box n) hq hp (Φ.partition n)
    (Φ.measurable_partition n) ρ κ (fun i => hκ i n)

/-- General probability-weighted Markov-kernel mixtures preserve every
coherent convention's Gibbs class. -/
theorem mem_gibbsMeasures_mixture {E : Type*} (exh : BoxExhaustion E)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : BoundaryConvention exh hq hp)
    {ι : Type*} [MeasurableSpace ι]
    (ρ : Measure ι) [IsProbabilityMeasure ρ]
    (κ : Kernel ι (Configuration E)) [IsMarkovKernel κ]
    (hκ : ∀ i, outputLaw κ i ∈ GibbsMeasures exh Φ) :
    mixture ρ κ ∈ GibbsMeasures exh Φ :=
  mem_dlrMeasures_mixture exh Φ.toBoundaryAssignment hq hp ρ κ hκ

/-- A binary convex combination of probability measures, with weights
`t` and `1-t` from the unit interval. -/
noncomputable def convexCombination {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) (t : unitInterval) : ProbabilityMeasure Ω :=
  ⟨unitInterval.toNNReal t • (μ : Measure Ω) +
      unitInterval.toNNReal (unitInterval.symm t) • (ν : Measure Ω), inferInstance⟩

/-- Binary convexity of the exact finite-box DLR equation. -/
theorem isDLR_convexCombination {E : Type*} (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ ν : ProbabilityMeasure (Configuration E)) (t : unitInterval)
    (hμ : B.IsDLR hq hp α hα μ) (hν : B.IsDLR hq hp α hα ν) :
    B.IsDLR hq hp α hα (convexCombination μ ν t) := by
  let c : ℝ≥0∞ := (unitInterval.toNNReal t : NNReal)
  let d : ℝ≥0∞ := (unitInterval.toNNReal (unitInterval.symm t) : NNReal)
  change Measure.map B.splitEquiv (c • (μ : Measure (Configuration E)) +
    d • (ν : Measure (Configuration E))) = _
  rw [Measure.map_add _ _ B.splitEquiv.measurable,
    Measure.map_smul c B.splitEquiv.measurable.aemeasurable,
    Measure.map_smul d B.splitEquiv.measurable.aemeasurable, hμ, hν]
  let π : Configuration E → B.Exterior := fun ω => (B.splitEquiv ω).1
  have hπ : Measurable π := measurable_fst.comp B.splitEquiv.measurable
  change _ = (Measure.map π
    (c • (μ : Measure (Configuration E)) +
      d • (ν : Measure (Configuration E)))) ⊗ₘ B.fkKernel hq hp α hα
  rw [Measure.map_add _ _ hπ,
    Measure.map_smul c hπ.aemeasurable, Measure.map_smul d hπ.aemeasurable,
    Measure.compProd_add_left, Measure.compProd_smul_left, Measure.compProd_smul_left]
  rfl

/-- Binary convexity of a full exhaustion-indexed DLR class. -/
theorem mem_dlrMeasures_convexCombination {E : Type*} (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E)) (t : unitInterval)
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp) :
    convexCombination μ ν t ∈ DLRMeasures exh Φ hq hp := by
  intro n
  exact isDLR_convexCombination (exh.box n) hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ ν t (hμ n) (hν n)

/-- Mixture form of the coherent-Gibbs branch of Proposition 1.8(2).
Different components may use different coherent source conventions.  Each
component's global at-most-one hypothesis transports it to the common target;
general DLR mixture closure then assembles the whole mixture.  No arbitrary
noncoherent weak limit is included.-/
theorem mem_gibbsMeasures_mixture_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Ψ : BoundaryConvention exh hq hp)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ.toBoundaryAssignment)
    {ι : Type*} [MeasurableSpace ι]
    (ρ : Measure ι) [IsProbabilityMeasure ρ]
    (κ : Kernel ι (Configuration G.edgeSet)) [IsMarkovKernel κ]
    (hsource : ∀ i, ∃ Φ : BoundaryConvention exh hq hp,
      ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment ∧
      outputLaw κ i ∈ GibbsMeasures exh Φ)
    (hglobal : ∀ i, ∀ᵐ ω ∂(outputLaw κ i : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    mixture ρ κ ∈ GibbsMeasures exh Ψ := by
  apply mem_gibbsMeasures_mixture exh Ψ ρ κ
  intro i
  obtain ⟨Φ, hΦ, hi⟩ := hsource i
  exact ConventionTransport.mem_gibbsMeasures_of_globalAtMostOne_of_le_one
    exh data Φ Ψ hΦ hΨ (outputLaw κ i) hi (hglobal i)

/-- Every coherent convention's Gibbs class is convex, as asserted in the
paper immediately before Proposition 1.8. -/
theorem mem_gibbsMeasures_convexCombination {E : Type*} (exh : BoxExhaustion E)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : BoundaryConvention exh hq hp)
    (μ ν : ProbabilityMeasure (Configuration E)) (t : unitInterval)
    (hμ : μ ∈ GibbsMeasures exh Φ) (hν : ν ∈ GibbsMeasures exh Φ) :
    convexCombination μ ν t ∈ GibbsMeasures exh Φ :=
  mem_dlrMeasures_convexCombination exh Φ.toBoundaryAssignment hq hp μ ν t hμ hν

end

end FK.InfiniteVolume.CoherentMixtures

#print axioms FK.InfiniteVolume.CoherentMixtures.map_bind
#print axioms FK.InfiniteVolume.CoherentMixtures.compProd_bind
#print axioms FK.InfiniteVolume.CoherentMixtures.compProd_eq_kernelCompProd
#print axioms FK.InfiniteVolume.CoherentMixtures.isDLR_mixture
#print axioms FK.InfiniteVolume.CoherentMixtures.mem_dlrMeasures_mixture
#print axioms FK.InfiniteVolume.CoherentMixtures.mem_gibbsMeasures_mixture
#print axioms FK.InfiniteVolume.CoherentMixtures.isDLR_convexCombination
#print axioms FK.InfiniteVolume.CoherentMixtures.mem_dlrMeasures_convexCombination
#print axioms FK.InfiniteVolume.CoherentMixtures.mem_gibbsMeasures_convexCombination
#print axioms FK.InfiniteVolume.CoherentMixtures.mem_gibbsMeasures_mixture_of_globalAtMostOne
