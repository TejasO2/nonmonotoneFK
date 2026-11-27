import FK.PlanarGlobalAssembly

/-!
# Almost-everywhere planar kernel duality

Finite planar duality is available in the source argument only on typical
exterior configurations.  The public pointwise kernel transport is stronger
than necessary: its final product-measure identity depends on the kernels only
up to the exterior measure of the complemented law.  This file proves the
corresponding almost-everywhere kernel and FK-PMF transport theorems.

No convention is changed arbitrarily on the null set of bad exterior fibres,
and no fibre DLR property is assumed.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume

noncomputable section

variable {E : Type*} [Countable E]

local instance boundaryPartitionMeasurableSpaceAE (V : Type*) : MeasurableSpace (Setoid V) := ⊤

/-- Almost-everywhere form of `isDLR_map_cfgDual_core`. -/
theorem isDLR_map_cfgDual_core_ae (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (κD : Kernel B.Exterior B.Interior) [IsMarkovKernel κD]
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hk : ∀ᵐ η ∂(B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) :
      Measure B.Exterior),
      κD η = Measure.map (intDual B) (B.fkKernel hq hp α hα (extDual B η))) :
    Measure.map B.splitEquiv
        (↑(ProbabilityMeasure.map μ (cfgDual E)) : Measure (Configuration E)) =
      (B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) : Measure B.Exterior) ⊗ₘ κD := by
  classical
  unfold FiniteBox.IsDLR at hμ
  have hsplit : ((B.splitEquiv : Configuration E → B.Exterior × B.Interior) ∘
        (cfgDual E : Configuration E → Configuration E)) =
      (Prod.map (extDual B) (intDual B) :
          B.Exterior × B.Interior → B.Exterior × B.Interior) ∘
        (B.splitEquiv : Configuration E → B.Exterior × B.Interior) := by
    funext ω
    simp only [Function.comp_apply, FiniteBox.splitEquiv_apply, split_cfgDual, Prod.map]
  have hP : Measurable (Prod.map (extDual B) (intDual B) :
      B.Exterior × B.Interior → B.Exterior × B.Interior) :=
    ((extDual B).measurable.comp measurable_fst).prodMk
      ((intDual B).measurable.comp measurable_snd)
  have hkey : Measure.map ((B.splitEquiv : Configuration E → B.Exterior × B.Interior) ∘
        (cfgDual E : Configuration E → Configuration E))
        (μ : Measure (Configuration E)) =
      Measure.map (Prod.map (extDual B) (intDual B))
        (Measure.map (B.splitEquiv : Configuration E → B.Exterior × B.Interior)
          (μ : Measure (Configuration E))) := by
    rw [hsplit, ← Measure.map_map hP B.splitEquiv.measurable]
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_map B.splitEquiv.measurable (cfgDual E).measurable, hkey, hμ,
    map_prod_map_compProd (extDual B) (intDual B), ← exteriorMeasure_cfgDual]
  apply Measure.compProd_congr
  filter_upwards [hk] with η hη
  rw [Kernel.comap_apply, Kernel.map_apply (κ := B.fkKernel hq hp α hα)
    (f := ⇑(intDual B)) (intDual B).measurable, extDual_symm_eq]
  exact hη.symm

/-- Almost-everywhere FK-kernel transport to a dual box. -/
theorem isDLR_map_cfgDual_ae (B : FiniteBox E) (Vd : Type*) [Fintype Vd]
    (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hk : ∀ᵐ η ∂(B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) :
      Measure B.Exterior),
      (dualBox B Vd s t).fkKernel hq hp αD hαD η =
        Measure.map (intDual B) (B.fkKernel hq hp α hα (extDual B η))) :
    (dualBox B Vd s t).IsDLR hq hp αD hαD (ProbabilityMeasure.map μ (cfgDual E)) := by
  exact isDLR_map_cfgDual_core_ae (B := B) (q := q) (p := p) hq hp α hα
    ((dualBox B Vd s t).fkKernel hq hp αD hαD) μ hμ hk

/-- **Almost-everywhere equation (12) at the dual parameter.**  Only the
exterior fibres carrying the complemented primal law are tested. -/
theorem isDLR_map_cfgDual_dualParameter_of_ae (B : FiniteBox E) (Vd : Type*)
    [Fintype Vd] (s t : B.edges → Vd) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hpmf : ∀ᵐ η ∂(B.exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) :
      Measure B.Exterior), ∀ ω : B.Interior,
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD η) (intDual B ω)) :
    (dualBox B Vd s t).IsDLR hq (FK.FinitePlane.dualParameter_le_one hq hp)
      αD hαD (ProbabilityMeasure.map μ (cfgDual E)) := by
  apply isDLR_map_cfgDual_core_ae B hq hp α hα
    ((dualBox B Vd s t).fkKernel hq (FK.FinitePlane.dualParameter_le_one hq hp) αD hαD)
    μ hμ
  filter_upwards [hpmf] with η hη
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.map_apply (intDual B).measurable (measurableSet_singleton ω)]
  have hpre : ((intDual B) ⁻¹' {ω} : Set B.Interior) = {intDual B ω} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, intDual_invol]
    · intro h
      rw [h, intDual_invol]
  rw [hpre]
  change (dualBox B Vd s t).graph.fkMeasure hq
      (FK.FinitePlane.dualParameter_le_one hq hp) (αD η) {ω} =
    B.graph.fkMeasure hq hp (α (extDual B η)) {intDual B ω}
  rw [FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton,
    FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
  rw [hη (intDual B ω), intDual_invol]

/-- All-box almost-everywhere dual transport. -/
theorem isDLR_map_cfgDual_allBoxes_of_ae
    {ι : Type*} (box : ι → FiniteBox E)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)] (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ i, (box i).Exterior → (box i).BoundaryPartition)
    (hα : ∀ i, Measurable (α i))
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : ∀ i, (box i).IsDLR hq hp (α i) (hα i) μ)
    (hpmf : ∀ i, ∀ᵐ η ∂((box i).exteriorMeasure (ProbabilityMeasure.map μ (cfgDual E)) :
      Measure (box i).Exterior), ∀ ω : (box i).Interior,
      (box i).graph.fkPMF hq hp (α i (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD i η) (intDual (box i) ω)) :
    ∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
      (FK.FinitePlane.dualParameter_le_one hq hp) (αD i) (hαD i)
      (ProbabilityMeasure.map μ (cfgDual E)) := by
  intro i
  exact isDLR_map_cfgDual_dualParameter_of_ae (box i) (Vd i) (s i) (t i)
    hq hp (α i) (hα i) (αD i) (hαD i) μ (hμ i) (hpmf i)

end

end FK.InfiniteVolume
