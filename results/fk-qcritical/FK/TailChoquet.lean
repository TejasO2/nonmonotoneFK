import FK.ReverseMartingale
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Regular conditional decomposition of DLR laws on the exterior tail

For a countable edge type, `tailConditionalKernel` is the genuine regular
conditional probability kernel on `FKLimit.tailSigma`.  It mixes back to the
original law and has a barycenter on the compact space of probability
measures.  If the original law is DLR, almost every fibre is proved to satisfy
the same exact finite-box DLR specification.  No extremality, local constancy,
or nesting compatibility of the boundary assignment is assumed.

The remaining Choquet issue is deliberately explicit: properness is proved on
each individual tail event, but simultaneous tail zero-one/extremality of the
fibres is not asserted.  The final theorem exposes precisely that missing
premise before applying the existing weak-limit theorem.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FK.InfiniteVolume

universe u v

local instance tailBoundaryMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

/-- The actual regular conditional probability kernel on the exterior tail. -/
noncomputable def tailConditionalKernel {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) :
    @Kernel (Configuration E) (Configuration E) FKLimit.tailSigma
      MeasurableSpace.pi :=
  condExpKernel (μ : Measure (Configuration E)) FKLimit.tailSigma

instance {E : Type u} [Countable E] (μ : ProbabilityMeasure (Configuration E)) :
    IsMarkovKernel (tailConditionalKernel μ) := by
  unfold tailConditionalKernel
  infer_instance

/-- The mixing law on tail-coordinate indices. -/
noncomputable def tailIndexMeasure {E : Type u}
    (μ : ProbabilityMeasure (Configuration E)) :
    @ProbabilityMeasure (Configuration E) FKLimit.tailSigma :=
  ⟨(μ : Measure (Configuration E)).trim FKLimit.tailSigma_le,
    isProbabilityMeasure_iff.2 (by
      rw [trim_measurableSet_eq FKLimit.tailSigma_le MeasurableSet.univ]
      exact measure_univ)⟩

/-- The tail RCP mixes back to the original law; no extremality is assumed. -/
theorem tailConditionalKernel_comp_trim {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) :
    tailConditionalKernel μ ∘ₘ
      (tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma) =
      (μ : Measure (Configuration E)) := by
  exact condExpKernel_comp_trim FKLimit.tailSigma_le

/-- The random law obtained by retaining a law's exterior marginal and
resampling a finite box with its actual FK specification. -/
noncomputable def dlrReconstructionKernel {ι E : Type*} [MeasurableSpace ι]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (κ : Kernel ι (Configuration E)) [IsSFiniteKernel κ] : Kernel ι (Configuration E) :=
  Kernel.map ((κ.map (fun ω ↦ (B.splitEquiv ω).1) ⊗ₖ
    (B.fkKernel hq hp α hα).prodMkLeft ι)) B.glue

lemma dlrReconstructionKernel_apply {ι E : Type*} [MeasurableSpace ι]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (κ : Kernel ι (Configuration E)) [IsSFiniteKernel κ] (x : ι) :
    dlrReconstructionKernel B hq hp α hα κ x =
      Measure.map B.glue (Measure.map (fun ω ↦ (B.splitEquiv ω).1) (κ x) ⊗ₘ
        B.fkKernel hq hp α hα) := by
  rw [dlrReconstructionKernel, Kernel.map_apply _
    (show Measurable B.glue from B.splitEquiv.symm.measurable)]
  congr 1
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.map_apply]
  rfl
  exact measurable_fst.comp B.splitEquiv.measurable

/-- The probability law on one tail fibre. -/
noncomputable def tailConditionalLaw {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) (ω : Configuration E) :
    ProbabilityMeasure (Configuration E) :=
  ⟨tailConditionalKernel μ ω, inferInstance⟩

@[simp] lemma coe_tailConditionalLaw {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) (ω : Configuration E) :
    (tailConditionalLaw μ ω : Measure (Configuration E)) = tailConditionalKernel μ ω := rfl

/-- FK reconstruction, with the source measurable space pinned to the tail. -/
noncomputable def tailReconstructionKernel {E : Type u} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) :
    @Kernel (Configuration E) (Configuration E) FKLimit.tailSigma MeasurableSpace.pi :=
  @dlrReconstructionKernel (Configuration E) E FKLimit.tailSigma B q p hq hp α hα
    (tailConditionalKernel μ) inferInstance

lemma tailReconstructionKernel_apply {E : Type u} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (ω : Configuration E) :
    tailReconstructionKernel B hq hp α hα μ ω =
      Measure.map B.glue ((B.exteriorMeasure (tailConditionalLaw μ ω) : Measure B.Exterior) ⊗ₘ
        B.fkKernel hq hp α hα) := by
  unfold tailReconstructionKernel
  exact @dlrReconstructionKernel_apply (Configuration E) E FKLimit.tailSigma B q p hq hp α hα
    (tailConditionalKernel μ) inferInstance ω

/-- A deterministic global configuration with a prescribed exterior and all
interior edges closed. -/
noncomputable def exteriorPointKernel {E : Type*} (B : FiniteBox E) :
    Kernel B.Exterior (Configuration E) :=
  Kernel.deterministic (fun η ↦ B.glue (η, fun _ ↦ false))
    (B.splitEquiv.symm.measurable.comp (measurable_id.prodMk measurable_const))

instance {E : Type*} (B : FiniteBox E) : IsMarkovKernel (exteriorPointKernel B) := by
  unfold exteriorPointKernel
  exact Kernel.isMarkovKernel_deterministic _

lemma dlrReconstructionKernel_exteriorPoint {E : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) (η : B.Exterior) :
    dlrReconstructionKernel B hq hp α hα (exteriorPointKernel B) η =
      (B.conditionalLaw hq hp α η : Measure (Configuration E)) := by
  rw [dlrReconstructionKernel_apply]
  change Measure.map B.glue (Measure.map (fun ω ↦ (B.splitEquiv ω).1)
    (Measure.dirac (B.glue (η, fun _ ↦ false))) ⊗ₘ B.fkKernel hq hp α hα) = _
  have hX : (B.splitEquiv (B.glue (η, fun _ ↦ false))).1 = η :=
    congrArg Prod.fst (B.split_glue (η, fun _ ↦ false))
  have hf : Measurable (fun ω : Configuration E ↦ (B.splitEquiv ω).1) :=
    measurable_fst.comp B.splitEquiv.measurable
  rw [Measure.map_dirac' hf, hX]
  ext A hA
  rw [Measure.map_apply (show Measurable B.glue from B.splitEquiv.symm.measurable) hA,
    Measure.dirac_compProd_apply (s := B.glue ⁻¹' A) (B.splitEquiv.symm.measurable hA)]
  change (B.graph.fkMeasure hq hp (α η)) (Prod.mk η ⁻¹' B.glue ⁻¹' A) =
    (Measure.map (fun ω : B.Interior ↦ B.glue (η, ω))
      (B.graph.fkMeasure hq hp (α η))) A
  rw [Measure.map_apply (B.measurable_glue_const_left η) hA]
  rfl

lemma measurable_conditionalLaw_apply {E : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    Measurable (fun η ↦ (B.conditionalLaw hq hp α η : Measure (Configuration E)) A) := by
  have h := (dlrReconstructionKernel B hq hp α hα (exteriorPointKernel B)).measurable_coe hA
  simpa only [dlrReconstructionKernel_exteriorPoint] using h

/-- Conditional global FK laws depend measurably on their exterior. -/
lemma measurable_conditionalLaw {E : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) :
    Measurable (fun η ↦ (B.conditionalLaw hq hp α η : Measure (Configuration E))) := by
  rw [Measure.measurable_measure]
  intro A hA
  exact measurable_conditionalLaw_apply B hq hp α hα hA

/-- Conditional global FK laws prescribe the exterior exactly. -/
lemma conditionalLaw_apply_inter_exterior {E : Type*} (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    (A : Set (Configuration E)) (hA : MeasurableSet A)
    (T : Set B.Exterior) (hT : MeasurableSet T) :
    (B.conditionalLaw hq hp α η : Measure (Configuration E))
        (A ∩ FKLimit.exteriorRestriction B.edges ⁻¹' T) =
      T.indicator (fun ζ ↦ (B.conditionalLaw hq hp α ζ : Measure (Configuration E)) A) η := by
  change (Measure.map (fun ω : B.Interior ↦ B.glue (η, ω))
    (B.graph.fkMeasure hq hp (α η))) (A ∩ FKLimit.exteriorRestriction B.edges ⁻¹' T) = _
  rw [Measure.map_apply (B.measurable_glue_const_left η)
    (hA.inter ((FKLimit.measurable_exteriorRestriction B.edges) hT))]
  by_cases hη : η ∈ T
  · have hpre : (fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹'
        (A ∩ FKLimit.exteriorRestriction B.edges ⁻¹' T) =
        (fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      have he : FKLimit.exteriorRestriction B.edges (B.glue (η, ξ)) = η := by
        funext e
        simp [FiniteBox.glue, FKLimit.exteriorRestriction, e.2]
      simp [he, hη]
    rw [hpre, Set.indicator_of_mem hη]
    exact (Measure.map_apply (B.measurable_glue_const_left η) hA).symm
  · have hpre : (fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹'
        (A ∩ FKLimit.exteriorRestriction B.edges ⁻¹' T) = ∅ := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      have he : FKLimit.exteriorRestriction B.edges (B.glue (η, ξ)) = η := by
        funext e
        simp [FiniteBox.glue, FKLimit.exteriorRestriction, e.2]
      exact hη (he ▸ h.2)
    rw [hpre, measure_empty, Set.indicator_of_notMem hη]

lemma dlrReconstructionKernel_apply_eq_lintegral {ι E : Type*} [MeasurableSpace ι]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (κ : Kernel ι (Configuration E)) [IsSFiniteKernel κ] (x : ι)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    dlrReconstructionKernel B hq hp α hα κ x A =
      ∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
        ∂Measure.map (fun ω ↦ (B.splitEquiv ω).1) (κ x) := by
  rw [dlrReconstructionKernel_apply,
    Measure.map_apply (show Measurable B.glue from B.splitEquiv.symm.measurable) hA,
    Measure.compProd_apply (s := B.glue ⁻¹' A) (B.splitEquiv.symm.measurable hA)]
  apply lintegral_congr
  intro η
  exact (Measure.map_apply (B.measurable_glue_const_left η) hA).symm

/-- Diagonal disintegration with a tail test set. -/
lemma setLIntegral_tailConditionalKernel {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) {H : Set (Configuration E)}
    (hH : MeasurableSet[FKLimit.tailSigma] H) {f : Configuration E → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ ω in H, ∫⁻ η, f η ∂tailConditionalKernel μ ω
      ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)) =
      ∫⁻ ω in H, f ω ∂(μ : Measure (Configuration E)) := by
  have hdiag : @Measurable (Configuration E) (Configuration E × Configuration E)
      MeasurableSpace.pi (FKLimit.tailSigma.prod MeasurableSpace.pi) Function.diag :=
    (measurable_id'' FKLimit.tailSigma_le).prodMk measurable_id
  have hs : @MeasurableSet (Configuration E × Configuration E)
      (FKLimit.tailSigma.prod MeasurableSpace.pi) (H ×ˢ Set.univ) :=
    hH.prod MeasurableSet.univ
  have hfs : @Measurable (Configuration E × Configuration E) ℝ≥0∞
      (FKLimit.tailSigma.prod MeasurableSpace.pi) _ (fun z ↦ f z.2) :=
    hf.comp measurable_snd
  have hcomp := Measure.setLIntegral_compProd
    (μ := (μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)
    (κ := tailConditionalKernel μ)
    (f := fun z : Configuration E × Configuration E ↦ f z.2)
    (hf.comp measurable_snd) hH MeasurableSet.univ
  simp only [Measure.restrict_univ] at hcomp
  rw [← hcomp]
  change (∫⁻ z in H ×ˢ Set.univ, f z.2
    ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le ⊗ₘ
      tailConditionalKernel μ)) = _
  rw [show tailConditionalKernel μ = condExpKernel (μ : Measure (Configuration E))
      FKLimit.tailSigma from rfl,
    compProd_trim_condExpKernel FKLimit.tailSigma_le]
  have hmap :
      (∫⁻ z in H ×ˢ Set.univ, f z.2
        ∂@Measure.map (Configuration E) (Configuration E × Configuration E)
          MeasurableSpace.pi (FKLimit.tailSigma.prod MeasurableSpace.pi)
          Function.diag (μ : Measure (Configuration E))) =
        ∫⁻ ω in Function.diag ⁻¹' (H ×ˢ Set.univ), f (Function.diag ω).2
          ∂(μ : Measure (Configuration E)) :=
    @setLIntegral_map (Configuration E) (Configuration E × Configuration E)
      MeasurableSpace.pi (FKLimit.tailSigma.prod MeasurableSpace.pi)
      (μ : Measure (Configuration E)) (fun z ↦ f z.2) Function.diag
      (H ×ˢ Set.univ) hs hfs hdiag
  simpa [Function.diag] using hmap

/-- Almost every tail fibre satisfies the tested FK reconstruction identity. -/
lemma ae_dlrReconstructionKernel_tail {E : Type u} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)), tailConditionalKernel μ ω A =
      tailReconstructionKernel B hq hp α hα μ ω A := by
  let X : Configuration E → B.Exterior := FKLimit.exteriorRestriction B.edges
  let c : B.Exterior → ℝ≥0∞ := fun η ↦
    (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
  have hX : Measurable X := FKLimit.measurable_exteriorRestriction B.edges
  have hc : Measurable c := measurable_conditionalLaw_apply B hq hp α hα hA
  have hcX : Measurable (fun ω ↦ c (X ω)) := hc.comp hX
  apply ae_of_ae_trim FKLimit.tailSigma_le
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (μ := (μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)
    ((tailConditionalKernel μ).measurable_coe hA)
    ((tailReconstructionKernel B hq hp α hα μ).measurable_coe hA)
  intro H hH _
  have hleft (ω : Configuration E) : tailConditionalKernel μ ω A =
      ∫⁻ η, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) η ∂tailConditionalKernel μ ω := by
    exact (lintegral_indicator_one (μ := tailConditionalKernel μ ω) hA).symm
  have hright (ω : Configuration E) :
      tailReconstructionKernel B hq hp α hα μ ω A =
        ∫⁻ ζ, c (X ζ) ∂tailConditionalKernel μ ω := by
    rw [tailReconstructionKernel]
    rw [@dlrReconstructionKernel_apply_eq_lintegral (Configuration E) E FKLimit.tailSigma
      B q p hq hp α hα (tailConditionalKernel μ) inferInstance ω A hA]
    exact lintegral_map hc hX
  have hsetL :
      (∫⁻ ω in H, tailConditionalKernel μ ω A
        ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)) =
        ∫⁻ ω in H, ∫⁻ η, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) η
          ∂tailConditionalKernel μ ω
        ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le) :=
    setLIntegral_congr_fun hH (fun ω _ ↦ hleft ω)
  have hsetR :
      (∫⁻ ω in H, tailReconstructionKernel B hq hp α hα μ ω A
        ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)) =
        ∫⁻ ω in H, ∫⁻ ζ, c (X ζ) ∂tailConditionalKernel μ ω
        ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le) :=
    setLIntegral_congr_fun hH (fun ω _ ↦ hright ω)
  rw [hsetL, hsetR,
    setLIntegral_tailConditionalKernel μ hH (measurable_const.indicator hA),
    setLIntegral_tailConditionalKernel μ hH hcX]
  have hHout : MeasurableSet[FKLimit.outsideSigma B.edges] H :=
    FKLimit.tailSigma_le_outsideSigma B.edges H hH
  obtain ⟨T, hT, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hHout
  change X ⁻¹' T = H at hpre
  rw [← hpre]
  calc
    (∫⁻ ω in X ⁻¹' T, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω
        ∂(μ : Measure (Configuration E))) = (μ : Measure (Configuration E)) (A ∩ X ⁻¹' T) := by
      calc
        _ = (μ : Measure (Configuration E)).restrict (X ⁻¹' T) A :=
          lintegral_indicator_one hA
        _ = _ := Measure.restrict_apply hA
    _ = ∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E))
        (A ∩ X ⁻¹' T) ∂(B.exteriorMeasure μ : Measure B.Exterior) :=
      B.apply_of_isDLR hq hp α hα μ hμ (hA.inter (hX hT))
    _ = ∫⁻ η, T.indicator c η ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
      apply lintegral_congr
      intro η
      exact conditionalLaw_apply_inter_exterior B hq hp α η A hA T hT
    _ = ∫⁻ η in T, c η ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
      rw [lintegral_indicator hT]
    _ = ∫⁻ ω in X ⁻¹' T, c (X ω) ∂(μ : Measure (Configuration E)) := by
      exact setLIntegral_map hT hc hX

/-- Almost every tail fibre of a DLR law is DLR for the same finite-box
specification.  No continuity or compatibility assumption on the boundary
partition is used. -/
theorem ae_isDLR_tailConditionalLaw {E : Type u} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      B.IsDLR hq hp α hα (tailConditionalLaw μ ω) := by
  have hI : ∀ I : Finset E, ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ∀ S : Set (I → Bool), tailConditionalKernel μ ω (MeasureTheory.cylinder I S) =
        tailReconstructionKernel B hq hp α hα μ ω (MeasureTheory.cylinder I S) := by
    intro I
    rw [ae_all_iff]
    intro S
    exact ae_dlrReconstructionKernel_tail B hq hp α hα μ hμ
      (FKLimit.DependsOnCoordinates.measurableSet
        (InfiniteVolume.dependsOnCoordinates_cylinder I S))
  filter_upwards [ae_all_iff.2 hI] with ω hω
  apply B.splitEquiv.map_apply_eq_iff_map_symm_apply_eq.mpr
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S
  have h := hω I S
  rw [tailReconstructionKernel_apply] at h
  exact h

/-- The whole infinite-volume DLR equation holds on almost every tail fibre. -/
theorem ae_mem_dlrMeasures_tailConditionalLaw {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      tailConditionalLaw μ ω ∈ DLRMeasures exh Φ hq hp := by
  change ∀ᵐ ω ∂(μ : Measure (Configuration E)), ∀ n,
    (exh.box n).IsDLR hq hp (Φ.partition n) (Φ.measurable_partition n)
      (tailConditionalLaw μ ω)
  rw [ae_all_iff]
  intro n
  exact ae_isDLR_tailConditionalLaw (exh.box n) hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ (hμ n)

/-- The fibre law is measurable for the Giry measurable structure on
`ProbabilityMeasure`. -/
noncomputable def tailLawDistribution {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) :
    ProbabilityMeasure (ProbabilityMeasure (Configuration E)) :=
  @ProbabilityMeasure.map (Configuration E) (ProbabilityMeasure (Configuration E))
    FKLimit.tailSigma _ (tailIndexMeasure μ) (tailConditionalLaw μ)

lemma measurable_tailConditionalLaw {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) :
    @Measurable (Configuration E) (ProbabilityMeasure (Configuration E))
      FKLimit.tailSigma _ (tailConditionalLaw μ) :=
  Measurable.subtype_mk (tailConditionalKernel μ).measurable

/-- Barycenter form of the genuine mixture on the compact space of
probability measures. -/
theorem lintegral_tailLawDistribution {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) {A : Set (Configuration E)}
    (hA : MeasurableSet A) :
    (∫⁻ ν, (ν : Measure (Configuration E)) A ∂(tailLawDistribution μ :
      Measure (ProbabilityMeasure (Configuration E)))) = (μ : Measure (Configuration E)) A := by
  have hEval : Measurable (fun ν : ProbabilityMeasure (Configuration E) ↦
      (ν : Measure (Configuration E)) A) :=
    (Measure.measurable_coe hA).comp measurable_subtype_coe
  change (∫⁻ ν, (ν : Measure (Configuration E)) A
    ∂@Measure.map (Configuration E) (ProbabilityMeasure (Configuration E))
      FKLimit.tailSigma _ (tailConditionalLaw μ)
      (tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma)) = _
  rw [@lintegral_map (Configuration E) (ProbabilityMeasure (Configuration E))
    FKLimit.tailSigma _ (tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma)
    (fun ν : ProbabilityMeasure (Configuration E) ↦ (ν : Measure (Configuration E)) A)
    (tailConditionalLaw μ) hEval (measurable_tailConditionalLaw μ)]
  change (∫⁻ ω, tailConditionalKernel μ ω A
    ∂(tailIndexMeasure μ : @Measure (Configuration E) FKLimit.tailSigma)) = _
  rw [← Measure.bind_apply (m := (tailIndexMeasure μ :
    @Measure (Configuration E) FKLimit.tailSigma)) hA (tailConditionalKernel μ).aemeasurable]
  exact congrArg (fun ν : Measure (Configuration E) ↦ ν A) (tailConditionalKernel_comp_trim μ)

/-- Properness on each individual tail event, with the null set depending on
that event.  This does not assert simultaneous properness on the entire tail. -/
lemma ae_tailConditionalKernel_apply_tail {E : Type u} [Countable E]
    (μ : ProbabilityMeasure (Configuration E)) {H : Set (Configuration E)}
    (hH : MeasurableSet[FKLimit.tailSigma] H) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)), tailConditionalKernel μ ω H =
      H.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  have hleft (ω : Configuration E) : tailConditionalKernel μ ω H =
      ∫⁻ η, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) η ∂tailConditionalKernel μ ω :=
    (lintegral_indicator_one (μ := tailConditionalKernel μ ω)
      (FKLimit.tailSigma_le H hH)).symm
  apply ae_of_ae_trim FKLimit.tailSigma_le
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (μ := (μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)
    ((tailConditionalKernel μ).measurable_coe (FKLimit.tailSigma_le H hH))
    (measurable_const.indicator hH)
  intro G hG _
  have hsetL :
      (∫⁻ ω in G, tailConditionalKernel μ ω H
        ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le)) =
        ∫⁻ ω in G, ∫⁻ η, H.indicator (fun _ ↦ (1 : ℝ≥0∞)) η
          ∂tailConditionalKernel μ ω
        ∂((μ : Measure (Configuration E)).trim FKLimit.tailSigma_le) :=
    setLIntegral_congr_fun hG (fun ω _ ↦ hleft ω)
  rw [hsetL, setLIntegral_tailConditionalKernel μ hG
    (measurable_const.indicator (FKLimit.tailSigma_le H hH))]
  exact (setLIntegral_trim FKLimit.tailSigma_le
    (measurable_const.indicator hH) hG).symm

/-- If the missing fibre-extremality assertion is supplied, the already
proved weak-limit theorem applies on almost every tail fibre. -/
theorem ae_mem_fkLimitMeasures_tailConditionalLaw_of_extremal
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      FK.IsExtremalIn
        ((fun ν : ProbabilityMeasure (Configuration E) ↦
          (ν : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
          (tailConditionalLaw μ ω : Measure (Configuration E)) →
        tailConditionalLaw μ ω ∈ FKLimitMeasures exh hq hp := by
  filter_upwards [ae_mem_dlrMeasures_tailConditionalLaw exh Φ hq hp μ hμ] with ω hω hext
  exact mem_fkLimitMeasures_of_extremal_dlr exh Φ hq hp (tailConditionalLaw μ ω) hω hext

end FK.InfiniteVolume
