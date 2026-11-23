import FK.TailChoquet
import FK.RightWiredEquationNine
import FK.AGBoundedRangeImplant

/-!
# Validation interfaces for the newest public modules

The first theorem is deliberately conditional on almost-everywhere extremality
of the actual tail conditional fibres. It does not assert simultaneous tail
properness, and it does not assume that the tail sigma-algebra is countably
generated. Under that explicit premise, extremal uniqueness implies equality
of the original probability measures by the actual RCP barycenter identity.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FK.InfiniteVolume

universe u v

local instance validationBoundaryMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

/-- If almost every actual tail conditional fibre is extremal in a class on
which `μ₀` is the only extremal probability law, then the mixed law is `μ₀`.
The a.e.-extremality premise is the remaining Choquet input, not a theorem
proved here. -/
theorem eq_of_ae_isExtremalIn_tailConditionalLaw
    {E : Type u} [Countable E]
    (μ μ₀ : ProbabilityMeasure (Configuration E))
    (S : Set (Measure (Configuration E)))
    (hunique : ∀ ν : ProbabilityMeasure (Configuration E),
      FK.IsExtremalIn S (ν : Measure (Configuration E)) → ν = μ₀)
    (hext : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.IsExtremalIn S (tailConditionalLaw μ ω : Measure (Configuration E))) :
    μ = μ₀ := by
  have heq : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      tailConditionalLaw μ ω = μ₀ :=
    hext.mono fun _ω hω ↦ hunique _ hω
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  have heqA : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      tailConditionalKernel μ ω A = (μ₀ : Measure (Configuration E)) A :=
    heq.mono fun _ω hω ↦ congrArg (fun ν : ProbabilityMeasure (Configuration E) ↦
      (ν : Measure (Configuration E)) A) hω
  have heqA_trim :
      ∀ᵐ ω ∂(tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma),
        tailConditionalKernel μ ω A = (μ₀ : Measure (Configuration E)) A :=
    ae_eq_trim_of_measurable FKLimit.tailSigma_le
      ((tailConditionalKernel μ).measurable_coe hA) measurable_const heqA
  calc
    (μ : Measure (Configuration E)) A =
        ∫⁻ ω, tailConditionalKernel μ ω A
          ∂(tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma) := by
      rw [← Measure.bind_apply (m := (tailIndexMeasure μ :
        @Measure (Configuration E) FKLimit.tailSigma)) hA
        (tailConditionalKernel μ).aemeasurable]
      exact congrArg (fun ν : Measure (Configuration E) ↦ ν A)
        (tailConditionalKernel_comp_trim μ).symm
    _ = ∫⁻ _ω, (μ₀ : Measure (Configuration E)) A
          ∂(tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma) :=
      lintegral_congr_ae heqA_trim
    _ = (μ₀ : Measure (Configuration E)) A := by simp

/-- DLR-specialized form: if extremal DLR uniqueness is known and the actual
tail fibres are extremal DLR almost everywhere, then the mixed law is the
unique law. The second hypothesis is precisely the remaining Choquet input. -/
theorem eq_dlr_of_ae_isExtremal_tailConditionalLaw
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ μ₀ : ProbabilityMeasure (Configuration E))
    (hunique : ∀ ν : ProbabilityMeasure (Configuration E),
      FK.IsExtremalIn
        ((fun ξ : ProbabilityMeasure (Configuration E) ↦
          (ξ : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (ν : Measure (Configuration E)) → ν = μ₀)
    (hext : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.IsExtremalIn
        ((fun ξ : ProbabilityMeasure (Configuration E) ↦
          (ξ : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (tailConditionalLaw μ ω : Measure (Configuration E))) :
    μ = μ₀ :=
  eq_of_ae_isExtremalIn_tailConditionalLaw μ μ₀ _ hunique hext

/-- Equality of two measurable families of probability laws on a Boolean
configuration space is measurable. Countable cylinders suffice, so there is
no uncountable intersection of measurable-null exceptional sets. -/
lemma measurableSet_eq_of_boolCylinders
    {ι X : Type u} [Countable ι] [MeasurableSpace X]
    (F G : X → Measure (Configuration ι))
    (hFprob : ∀ x, IsProbabilityMeasure (F x))
    (hGprob : ∀ x, IsProbabilityMeasure (G x))
    (hF : Measurable F) (hG : Measurable G) :
    MeasurableSet {x | F x = G x} := by
  have hcyl (I : Finset ι) (S : Set (I → Bool)) :
      MeasurableSet (MeasureTheory.cylinder I S) :=
    FKLimit.DependsOnCoordinates.measurableSet
      (dependsOnCoordinates_cylinder I S)
  have hset : {x | F x = G x} = ⋂ (I : Finset ι), ⋂ (S : Set (I → Bool)),
      {x | F x (MeasureTheory.cylinder I S) = G x (MeasureTheory.cylinder I S)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h I S
      exact congrArg (fun ν : Measure (Configuration ι) ↦
        ν (MeasureTheory.cylinder I S)) h
    · intro h
      let _ := hFprob x
      let _ := hGprob x
      exact FKModel.measure_ext_of_eq_on_boolCylinders (F x) (G x) h
  rw [hset]
  refine MeasurableSet.iInter fun I ↦ MeasurableSet.iInter fun S ↦ ?_
  exact measurableSet_eq_fun
    ((Measure.measurable_coe (hcyl I S)).comp hF)
    ((Measure.measurable_coe (hcyl I S)).comp hG)

/-- The exterior marginal is measurable as an ordinary measure-valued map. -/
lemma measurable_exteriorMeasure_toMeasure
    {E : Type u} (B : FiniteBox E) :
    Measurable (fun μ : ProbabilityMeasure (Configuration E) ↦
      (B.exteriorMeasure μ : Measure B.Exterior)) := by
  change Measurable (fun μ : ProbabilityMeasure (Configuration E) ↦
    Measure.map (fun ω ↦ (B.splitEquiv ω).1) (μ : Measure (Configuration E)))
  exact (Measure.measurable_map _
    (measurable_fst.comp B.splitEquiv.measurable)).comp measurable_subtype_coe

/-- Measurability of a composition-product with a fixed kernel, in the
measure argument. -/
lemma measurable_compProd_right {X A B : Type u}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (f : X → Measure A) (κ : Kernel A B) [IsSFiniteKernel κ]
    [∀ x, SFinite (f x)] (hf : Measurable f) :
    Measurable (fun x ↦ f x ⊗ₘ κ) := by
  rw [Measure.measurable_measure]
  intro s hs
  simp only [Measure.compProd_apply hs]
  exact (Measure.measurable_lintegral
    (Kernel.measurable_kernel_prodMk_left (κ := κ) hs)).comp hf

/-- The composition-product occurring in the DLR equation is measurable in
its global probability law. -/
lemma measurable_dlrCompProd {E : Type u}
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    Measurable (fun μ : ProbabilityMeasure (Configuration E) ↦
      (B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ B.fkKernel hq hp α hα) :=
  measurable_compProd_right _ _ (measurable_exteriorMeasure_toMeasure B)

/-- The fixed-box DLR locus is measurable in the Giry measurable structure. -/
lemma measurableSet_isDLR {E : Type u} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    MeasurableSet {μ : ProbabilityMeasure (Configuration E) |
      B.IsDLR hq hp α hα μ} := by
  let F : ProbabilityMeasure (Configuration E) → Measure (Configuration E) :=
    fun μ ↦ (μ : Measure (Configuration E))
  let G : ProbabilityMeasure (Configuration E) → Measure (Configuration E) :=
    fun μ ↦ Measure.map B.glue
      ((B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ B.fkKernel hq hp α hα)
  have hG : Measurable G :=
    (Measure.measurable_map B.glue B.splitEquiv.symm.measurable).comp
      (measurable_dlrCompProd B hq hp α hα)
  have hmeas : MeasurableSet {μ | F μ = G μ} :=
    measurableSet_eq_of_boolCylinders F G
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
      measurable_subtype_coe hG
  have hiff (μ : ProbabilityMeasure (Configuration E)) :
      B.IsDLR hq hp α hα μ ↔ F μ = G μ :=
    B.splitEquiv.map_apply_eq_iff_map_symm_apply_eq
  have hset : {μ : ProbabilityMeasure (Configuration E) |
      B.IsDLR hq hp α hα μ} = {μ | F μ = G μ} := Set.ext hiff
  rw [hset]
  exact hmeas

/-- The full countable family of DLR equations cuts out a measurable set. -/
lemma measurableSet_dlrMeasures {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    MeasurableSet (DLRMeasures exh Φ hq hp) := by
  have hset : DLRMeasures exh Φ hq hp =
      ⋂ n, {μ : ProbabilityMeasure (Configuration E) |
        (exh.box n).IsDLR hq hp (Φ.partition n) (Φ.measurable_partition n) μ} := by
    ext μ
    simp only [DLRMeasures, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun n ↦
    measurableSet_isDLR (exh.box n) hq hp (Φ.partition n) (Φ.measurable_partition n)

/-- The actual Giry mixing law is almost surely supported on DLR laws.
This is a support consequence of the already proved fibre-DLR theorem, not a
claim of fibre extremality or simultaneous properness on all tail events. -/
theorem ae_mem_dlrMeasures_tailLawDistribution {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    ∀ᵐ ν ∂(tailLawDistribution μ : Measure (ProbabilityMeasure (Configuration E))),
      ν ∈ DLRMeasures exh Φ hq hp := by
  have hDLR : MeasurableSet (DLRMeasures exh Φ hq hp) :=
    measurableSet_dlrMeasures exh Φ hq hp
  have hsource : ∀ᵐ ω ∂(tailIndexMeasure μ :
      @Measure (Configuration E) FKLimit.tailSigma),
      tailConditionalLaw μ ω ∈ DLRMeasures exh Φ hq hp := by
    have h := ae_mem_dlrMeasures_tailConditionalLaw exh Φ hq hp μ hμ
    rw [ae_iff] at h ⊢
    change ((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)
      {ω | tailConditionalLaw μ ω ∉ DLRMeasures exh Φ hq hp} = 0
    calc
      ((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)
          {ω | tailConditionalLaw μ ω ∉ DLRMeasures exh Φ hq hp} =
          (μ : Measure (Configuration E))
            {ω | tailConditionalLaw μ ω ∉ DLRMeasures exh Φ hq hp} :=
        trim_measurableSet_eq FKLimit.tailSigma_le
          (s := (tailConditionalLaw μ ⁻¹' DLRMeasures exh Φ hq hp)ᶜ)
          ((hDLR.preimage (measurable_tailConditionalLaw μ)).compl)
      _ = 0 := h
  change ∀ᵐ ν ∂(@Measure.map (Configuration E)
      (ProbabilityMeasure (Configuration E)) FKLimit.tailSigma _
      (tailConditionalLaw μ) (tailIndexMeasure μ :
        @Measure (Configuration E) FKLimit.tailSigma)),
    ν ∈ DLRMeasures exh Φ hq hp
  exact (ae_map_iff (measurable_tailConditionalLaw μ).aemeasurable hDLR).2 hsource

end FK.InfiniteVolume
