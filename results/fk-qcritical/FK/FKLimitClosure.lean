import FK.PlanarForestDuality
import FK.InteriorWeakLimit

/-!
# Weak closedness of finite-box FK DLR classes, and limit-set structure

This file studies how DLR memberships at a single finite box behave under weak
convergence, and what can be said about the set of FK weak limits itself.

Main points.

* `FiniteBox.reconMeasure` is the raw glued measure
  `map glue (exterior measure ⊗ actual FK kernel)`; `FiniteBox.isDLR_iff_recon`
  identifies the repository's `IsDLR` with invariance under this operation.
* `FiniteBox.abs_integral_reconMeasure_sub_le` is the quantitative stability
  estimate: two boundary specifications which agree off a measurable set `A` of
  the exterior space give glued laws whose bounded-continuous test integrals
  differ by at most `2 * ‖f‖ * ν.real A`.
* `FiniteBox.isDLR_of_tendsto_of_tendstoMeasure` turns that estimate into weak
  closedness of the DLR class for a fixed *locally constant* specification,
  under the genuinely weaker hypothesis that the varying specifications agree
  with it asymptotically in measure instead of being locally constant
  themselves.

The hypothesis is not decorative: `FK.InfiniteVolume.LimitClosure.counterexample_*`
below exhibits a fixed measurable specification whose DLR class is *not*
weakly closed, so measurability alone cannot replace (asymptotic) local
constancy.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.LimitClosure

noncomputable section

local instance boundaryPartitionMeasurableSpaceLimit (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoidLimit (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FiniteBox

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- The glued global measure built from an arbitrary finite exterior measure and
the actual finite FK kernel of the box. -/
def reconMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (ν : Measure B.Exterior) : Measure (Configuration E) :=
  Measure.map B.glue (ν ⊗ₘ B.fkKernel hq hp α hα)

lemma reconMeasure_def {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (ν : Measure B.Exterior) :
    reconMeasure B hq hp α hα ν =
      Measure.map B.glue (ν ⊗ₘ B.fkKernel hq hp α hα) := rfl

/-- Gluing an exterior and an interior configuration is measurable. -/
lemma measurable_glue : Measurable B.glue := B.splitEquiv.symm.measurable

instance reconMeasure_isFiniteMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (ν : Measure B.Exterior) [IsFiniteMeasure ν] :
    IsFiniteMeasure (reconMeasure B hq hp α hα ν) := by
  unfold reconMeasure
  infer_instance

/-- Total mass of a glued law is the total mass of its exterior measure. -/
lemma reconMeasure_real_univ {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (ν : Measure B.Exterior) [IsFiniteMeasure ν] :
    (reconMeasure B hq hp α hα ν).real Set.univ = ν.real Set.univ := by
  have hmass : (reconMeasure B hq hp α hα ν) Set.univ = ν Set.univ := by
    unfold reconMeasure
    rw [Measure.map_apply (measurable_glue B) MeasurableSet.univ]
    simp only [Set.preimage_univ]
    rw [Measure.compProd_apply MeasurableSet.univ]
    simp only [Set.preimage_univ]
    have hone : (fun a : B.Exterior => (B.fkKernel hq hp α hα a) Set.univ) = fun _ => 1 := by
      funext a
      rw [FK.InfiniteVolume.FiniteBox.fkKernel_apply]
      haveI := FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp (α a)
      exact measure_univ
    rw [hone, lintegral_one]
  rw [Measure.real_def, Measure.real_def, hmass]

/-- The repository's `IsDLR` predicate is invariance of the law under
reconstruction from its exterior marginal. -/
theorem isDLR_iff_recon {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) :
    B.IsDLR hq hp α hα μ ↔
      (μ : Measure (Configuration E)) =
        reconMeasure B hq hp α hα (B.exteriorMeasure μ : Measure B.Exterior) := by
  constructor
  · intro h
    exact B.measure_eq_map_glue_compProd hq hp α hα μ h
  · intro h
    apply B.splitEquiv.map_apply_eq_iff_map_symm_apply_eq.mpr
    rw [h, reconMeasure_def]
    rfl

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- Specifications agreeing almost everywhere for the restricted exterior measure
give the same glued law on that restricted part. -/
lemma reconMeasure_restrict_congr {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {α β : B.Exterior → B.BoundaryPartition} (hα : Measurable α) (hβ : Measurable β)
    (ν : Measure B.Exterior) {A : Set B.Exterior}
    (hagree : ∀ᵐ η ∂(ν.restrict A), α η = β η) :
    reconMeasure B hq hp α hα (ν.restrict A) =
      reconMeasure B hq hp β hβ (ν.restrict A) := by
  rw [reconMeasure_def, reconMeasure_def]
  congr 1
  refine Measure.compProd_congr (hagree.mono ?_)
  intro η hη
  rw [FK.InfiniteVolume.FiniteBox.fkKernel_apply,
    FK.InfiniteVolume.FiniteBox.fkKernel_apply, hη]

/-- Splitting the exterior measure splits the glued law additively. -/
lemma reconMeasure_add {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (ν₁ ν₂ : Measure B.Exterior) [SFinite ν₁] [SFinite ν₂] :
    reconMeasure B hq hp α hα (ν₁ + ν₂) =
      reconMeasure B hq hp α hα ν₁ + reconMeasure B hq hp α hα ν₂ := by
  rw [reconMeasure_def, reconMeasure_def, reconMeasure_def, Measure.compProd_add_left,
    Measure.map_add _ _ (measurable_glue B)]

/-- **Quantitative stability of the glued law.**  If two measurable specifications
agree off a set `A` of exterior configurations, then the glued laws differ on every
bounded continuous test function by at most `2‖f‖` times the exterior mass of `A`. -/
lemma abs_integral_reconMeasure_sub_le {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {α β : B.Exterior → B.BoundaryPartition} (hα : Measurable α) (hβ : Measurable β)
    (ν : Measure B.Exterior) [IsFiniteMeasure ν]
    {A : Set B.Exterior} (hA : MeasurableSet A)
    (hagree : ∀ᵐ η ∂(ν.restrict Aᶜ), α η = β η)
    (f : BoundedContinuousFunction (Configuration E) ℝ) :
    |∫ ω, f ω ∂(reconMeasure B hq hp α hα ν) -
        ∫ ω, f ω ∂(reconMeasure B hq hp β hβ ν)| ≤ 2 * ‖f‖ * ν.real A := by
  have hsplit : ν = ν.restrict A + ν.restrict Aᶜ :=
    (Measure.restrict_add_restrict_compl hA).symm
  have hcongr : reconMeasure B hq hp α hα (ν.restrict Aᶜ) =
      reconMeasure B hq hp β hβ (ν.restrict Aᶜ) :=
    reconMeasure_restrict_congr B hq hp hα hβ ν hagree
  have hαsplit : reconMeasure B hq hp α hα ν =
      reconMeasure B hq hp α hα (ν.restrict A) +
        reconMeasure B hq hp α hα (ν.restrict Aᶜ) := by
    conv_lhs => rw [hsplit]
    exact reconMeasure_add B hq hp α hα (ν.restrict A) (ν.restrict Aᶜ)
  have hβsplit : reconMeasure B hq hp β hβ ν =
      reconMeasure B hq hp β hβ (ν.restrict A) +
        reconMeasure B hq hp β hβ (ν.restrict Aᶜ) := by
    conv_lhs => rw [hsplit]
    exact reconMeasure_add B hq hp β hβ (ν.restrict A) (ν.restrict Aᶜ)
  have hintαA : Integrable f (reconMeasure B hq hp α hα (ν.restrict A)) :=
    BoundedContinuousFunction.integrable _ f
  have hintαAc : Integrable f (reconMeasure B hq hp α hα (ν.restrict Aᶜ)) :=
    BoundedContinuousFunction.integrable _ f
  have hintβA : Integrable f (reconMeasure B hq hp β hβ (ν.restrict A)) :=
    BoundedContinuousFunction.integrable _ f
  have hintβAc : Integrable f (reconMeasure B hq hp β hβ (ν.restrict Aᶜ)) :=
    BoundedContinuousFunction.integrable _ f
  have hintα : ∫ ω, f ω ∂(reconMeasure B hq hp α hα ν) =
      ∫ ω, f ω ∂(reconMeasure B hq hp α hα (ν.restrict A)) +
        ∫ ω, f ω ∂(reconMeasure B hq hp α hα (ν.restrict Aᶜ)) := by
    rw [hαsplit, integral_add_measure hintαA hintαAc]
  have hintβ : ∫ ω, f ω ∂(reconMeasure B hq hp β hβ ν) =
      ∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict A)) +
        ∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict Aᶜ)) := by
    rw [hβsplit, integral_add_measure hintβA hintβAc]
  have hmassα : (reconMeasure B hq hp α hα (ν.restrict A)).real Set.univ = ν.real A := by
    rw [reconMeasure_real_univ, Measure.real_def, Measure.real_def,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hmassβ : (reconMeasure B hq hp β hβ (ν.restrict A)).real Set.univ = ν.real A := by
    rw [reconMeasure_real_univ, Measure.real_def, Measure.real_def,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hnorm : ∀ (γ : B.Exterior → B.BoundaryPartition) (hγ : Measurable γ)
      (m : Measure (Configuration E)) [IsFiniteMeasure m],
      |∫ ω, f ω ∂m| ≤ ‖f‖ * m.real Set.univ := by
    intro γ hγ m _
    have := norm_integral_le_of_norm_le_const
      (μ := m) (f := fun ω => f ω) (C := ‖f‖)
      (Eventually.of_forall fun ω => BoundedContinuousFunction.norm_coe_le_norm f ω)
    rwa [Real.norm_eq_abs] at this
  have hαA := hnorm α hα (reconMeasure B hq hp α hα (ν.restrict A))
  have hβA := hnorm β hβ (reconMeasure B hq hp β hβ (ν.restrict A))
  rw [hintα, hintβ, hcongr]
  calc |(∫ ω, f ω ∂(reconMeasure B hq hp α hα (ν.restrict A)) +
          ∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict Aᶜ))) -
        (∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict A)) +
          ∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict Aᶜ)))|
      = |∫ ω, f ω ∂(reconMeasure B hq hp α hα (ν.restrict A)) -
          ∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict A))| := by ring_nf
    _ ≤ |∫ ω, f ω ∂(reconMeasure B hq hp α hα (ν.restrict A))| +
          |∫ ω, f ω ∂(reconMeasure B hq hp β hβ (ν.restrict A))| := abs_sub _ _
    _ ≤ ‖f‖ * (reconMeasure B hq hp α hα (ν.restrict A)).real Set.univ +
          ‖f‖ * (reconMeasure B hq hp β hβ (ν.restrict A)).real Set.univ := by
        gcongr
    _ = 2 * ‖f‖ * ν.real A := by rw [hmassα, hmassβ]; ring

end FiniteBox

namespace FiniteBox

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- The glued law of a probability exterior measure, as a probability measure. -/
noncomputable def reconPM {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (ν : ProbabilityMeasure B.Exterior) : ProbabilityMeasure (Configuration E) :=
  ⟨reconMeasure B hq hp β hβ (ν : Measure B.Exterior),
    (Measure.isProbabilityMeasure_map_iff B.splitEquiv.symm.measurable.aemeasurable).2
      inferInstance⟩

lemma reconPM_val {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (ν : ProbabilityMeasure B.Exterior) :
    (reconPM B hq hp β hβ ν : Measure (Configuration E)) =
      reconMeasure B hq hp β hβ (ν : Measure B.Exterior) := rfl

/-- The repository's `reconstruct` is the glued law of the exterior marginal. -/
lemma reconstruct_val_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (μ : ProbabilityMeasure (Configuration E)) :
    ((FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.reconstruct B hq hp β hβ μ :
        ProbabilityMeasure (Configuration E)) : Measure (Configuration E)) =
      reconMeasure B hq hp β hβ (B.exteriorMeasure μ : Measure B.Exterior) := rfl

lemma reconPM_exteriorMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (μ : ProbabilityMeasure (Configuration E)) :
    reconPM B hq hp β hβ (B.exteriorMeasure μ) =
      FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.reconstruct B hq hp β hβ μ := by
  apply Subtype.ext
  exact (reconstruct_val_eq B hq hp β hβ μ).symm

/-- Weak continuity of reconstruction for a continuous conditional specification. -/
lemma tendsto_reconPM {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (hβc : Continuous (B.conditionalLaw hq hp β))
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun i => reconPM B hq hp β hβ (B.exteriorMeasure (μs i))) l
      (𝓝 (reconPM B hq hp β hβ (B.exteriorMeasure μ))) := by
  have hrecon := FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.tendsto_reconstruct
    B hq hp β hβ hβc hμ
  refine hrecon.congr' ?_
  filter_upwards [] with i
  exact reconPM_exteriorMeasure B hq hp β hβ (μs i)

/-- Test integrals against the glued law of an almost-everywhere identical
specification coincide. -/
lemma integral_reconMeasure_eq_of_ae {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {α β : B.Exterior → B.BoundaryPartition} (hα : Measurable α) (hβ : Measurable β)
    (ν : Measure B.Exterior) [IsFiniteMeasure ν]
    (hagree : ∀ᵐ η ∂ν, α η = β η)
    (f : BoundedContinuousFunction (Configuration E) ℝ) :
    ∫ ω, f ω ∂(reconMeasure B hq hp α hα ν) =
      ∫ ω, f ω ∂(reconMeasure B hq hp β hβ ν) := by
  classical
  set S : Set B.Exterior := {η | α η ≠ β η} with hSdef
  have hT : MeasurableSet {η : B.Exterior | α η = β η} := by
    haveI : MeasurableSingletonClass B.BoundaryPartition := inferInstance
    have h : {η : B.Exterior | α η = β η}
        = ⋃ π : B.BoundaryPartition, (α ⁻¹' {π} ∩ β ⁻¹' {π}) := by
      ext η
      constructor
      · intro hη
        exact Set.mem_iUnion.mpr ⟨α η, rfl, hη.symm⟩
      · intro hη
        obtain ⟨π, h1, h2⟩ := Set.mem_iUnion.mp hη
        exact h1.trans h2.symm
    rw [h]
    exact MeasurableSet.iUnion fun π =>
      (hα (measurableSet_singleton π)).inter (hβ (measurableSet_singleton π))
  have hS : MeasurableSet S := by
    have hcomp : S = {η : B.Exterior | α η = β η}ᶜ := by
      ext η
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hcomp]
    exact hT.compl
  have hSnull : ν S = 0 := by
    have h := MeasureTheory.ae_iff.mp hagree
    simpa [hSdef, eq_comm] using h
  have hreal : ν.real S = 0 := by
    rw [Measure.real_def, hSnull]
    simp
  have hres : ∀ᵐ η ∂(ν.restrict Sᶜ), α η = β η :=
    Filter.Eventually.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_le_self (s := Sᶜ))) hagree
  have hbound := abs_integral_reconMeasure_sub_le B hq hp hα hβ ν hS hres f
  rw [hreal, mul_zero] at hbound
  have habs : |∫ ω, f ω ∂(reconMeasure B hq hp α hα ν) -
      ∫ ω, f ω ∂(reconMeasure B hq hp β hβ ν)| = 0 :=
    le_antisymm hbound (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

end FiniteBox


namespace FiniteBox

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- **Weak closedness of the DLR class for asymptotically locally constant
specifications.**  A weak limit of laws which are DLR at the box for varying
measurable specifications is DLR for the fixed specification `β`, provided the
varying specifications agree with `β` almost everywhere for the corresponding
exterior marginals and `β`'s conditional law is weakly continuous. -/
theorem isDLR_of_tendsto_of_tendstoMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (hβc : Continuous (B.conditionalLaw hq hp β))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {α : ι → B.Exterior → B.BoundaryPartition} (hα : ∀ i, Measurable (α i))
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp (α i) (hα i) (μs i))
    (hagree : ∀ᶠ i in l,
      ∀ᵐ η ∂((B.exteriorMeasure (μs i)) : Measure B.Exterior), α i η = β η) :
    B.IsDLR hq hp β hβ μ := by
  refine (isDLR_iff_recon B hq hp β hβ μ).mpr ?_
  have key : ∀ f : BoundedContinuousFunction (Configuration E) ℝ,
      ∫ ω, f ω ∂(μ : Measure (Configuration E)) =
        ∫ ω, f ω ∂(reconMeasure B hq hp β hβ
          (B.exteriorMeasure μ : Measure B.Exterior)) := by
    intro f
    have hL : Tendsto (fun i => ∫ ω, f ω ∂(μs i : Measure (Configuration E))) l
        (𝓝 (∫ ω, f ω ∂(μ : Measure (Configuration E)))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
    have hR : Tendsto (fun i => ∫ ω, f ω ∂(reconMeasure B hq hp β hβ
          (B.exteriorMeasure (μs i) : Measure B.Exterior))) l
        (𝓝 (∫ ω, f ω ∂(reconMeasure B hq hp β hβ
          (B.exteriorMeasure μ : Measure B.Exterior)))) := by
      have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
        (tendsto_reconPM B hq hp β hβ hβc hμ)) f
      simpa only [reconPM_val] using h
    have heq : ∀ᶠ i in l,
        ∫ ω, f ω ∂(μs i : Measure (Configuration E)) =
          ∫ ω, f ω ∂(reconMeasure B hq hp β hβ
            (B.exteriorMeasure (μs i) : Measure B.Exterior)) := by
      filter_upwards [hDLR, hagree] with i hD hE
      rw [(isDLR_iff_recon B hq hp (α i) (hα i) (μs i)).mp hD]
      exact integral_reconMeasure_eq_of_ae B hq hp (hα i) hβ _ hE f
    exact tendsto_nhds_unique hL (hR.congr' (heq.mono fun i hi => hi.symm))
  have hν : Tendsto (fun _ : Unit =>
      reconPM B hq hp β hβ (B.exteriorMeasure μ)) (𝓝 ()) (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [] with i
    rw [reconPM_val]
    exact key f
  have hEqPM : μ = reconPM B hq hp β hβ (B.exteriorMeasure μ) :=
    (tendsto_nhds_unique tendsto_const_nhds hν).symm
  have hval := congrArg (fun x : ProbabilityMeasure (Configuration E) =>
    (x : Measure (Configuration E))) hEqPM
  simpa only [reconPM_val] using hval

end FiniteBox



namespace FiniteBox

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- Locally constant specifications need no separate continuity hypothesis. -/
theorem isDLR_of_tendsto_of_tendstoMeasure_of_isLocallyConstant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    (hlocal : IsLocallyConstant β)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {α : ι → B.Exterior → B.BoundaryPartition} (hα : ∀ i, Measurable (α i))
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp (α i) (hα i) (μs i))
    (hagree : ∀ᶠ i in l,
      ∀ᵐ η ∂((B.exteriorMeasure (μs i)) : Measure B.Exterior), α i η = β η) :
    B.IsDLR hq hp β hβ μ :=
  isDLR_of_tendsto_of_tendstoMeasure B hq hp β hβ
    (FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.continuous_conditionalLaw_of_isLocallyConstant
      B hq hp hlocal) hα hμ hDLR hagree

end FiniteBox

/-- **Exhaustion-level weak closedness.**  If every member of the sequence is DLR
for the boundary assignment `Φ`, and for every box the assignment `Φ` agrees
almost everywhere with the locally constant assignment `Φ'`, then the weak limit
is DLR for `Φ'`. -/
theorem mem_dlrMeasures_of_tendsto_of_tendstoMeasure {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ Φ' : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hlocal : ∀ n, IsLocallyConstant (Φ'.partition n))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp)
    (hagree : ∀ n, ∀ᶠ i in l,
      ∀ᵐ η ∂((exh.box n).exteriorMeasure (μs i) : Measure (exh.box n).Exterior),
        Φ.partition n η = Φ'.partition n η) :
    μ ∈ DLRMeasures exh Φ' hq hp := by
  intro n
  exact FiniteBox.isDLR_of_tendsto_of_tendstoMeasure_of_isLocallyConstant
    (exh.box n) hq hp (Φ'.partition n) (Φ'.measurable_partition n) (hlocal n)
    (fun i => Φ.measurable_partition n) hμ
    (hDLR.mono fun i hi => hi n) (hagree n)


local instance boundaryPartitionMeasurableSpaceCounter (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

open FK.Finite FK.Finite.LabelledMultigraph

def oneEdgeBox : FK.InfiniteVolume.FiniteBox ℕ where
  Vertex := Bool
  edges := {0}
  source := fun _ => false
  target := fun _ => true

abbrev oneEdgeGraph : LabelledMultigraph := oneEdgeBox.graph

def oneEdgeLabel : oneEdgeBox.edges := ⟨0, by simp [oneEdgeBox]⟩

/-- The all-open exterior configuration of the one-edge box. -/
def extAllTrue : oneEdgeBox.Exterior := fun _ => true

/-- The exterior configuration which is all open except at the `n`-th exterior label. -/
def extPerturb (n : ℕ) : oneEdgeBox.Exterior :=
  fun e => if (e : ℕ) = n + 1 then false else true

lemma extPerturb_ne (n : ℕ) : extPerturb n ≠ extAllTrue := by
  intro h
  have h' : extPerturb n ⟨n + 1, by simp [oneEdgeBox]⟩ = extAllTrue ⟨n + 1, by simp [oneEdgeBox]⟩ := by
    rw [h]
  simp [extPerturb, extAllTrue] at h'

lemma measurableSet_extAllTrue :
    MeasurableSet {η : oneEdgeBox.Exterior | η = extAllTrue} := by
  have h : {η : oneEdgeBox.Exterior | η = extAllTrue}
      = ⋂ e : {e : ℕ // e ∉ oneEdgeBox.edges}, {η : oneEdgeBox.Exterior | η e = true} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter, extAllTrue]
    exact ⟨fun h e => by rw [h]; rfl, fun h => funext h⟩
  rw [h]
  refine MeasurableSet.iInter fun e => ?_
  have hmeas : Measurable (fun η : oneEdgeBox.Exterior => η e) := measurable_pi_apply e
  have hset : MeasurableSet {true} := measurableSet_singleton true
  exact hmeas hset

/-- A measurable boundary specification which is wired exactly at the all-open
exterior configuration. -/
noncomputable def flipPartition (η : oneEdgeBox.Exterior) : oneEdgeBox.BoundaryPartition :=
  if η = extAllTrue then ⊤ else ⊥

lemma flipPartition_of_ne {η : oneEdgeBox.Exterior} (h : η ≠ extAllTrue) :
    flipPartition η = ⊥ := by
  unfold flipPartition
  rw [if_neg h]

lemma flipPartition_allTrue : flipPartition extAllTrue = ⊤ := by
  unfold flipPartition
  rw [if_pos rfl]

lemma measurable_flipPartition : Measurable flipPartition := by
  intro s hs
  by_cases htop : (⊤ : Setoid Bool) ∈ s
  · by_cases hbot : (⊥ : Setoid Bool) ∈ s
    · have h : flipPartition ⁻¹' s = Set.univ := by
        ext η
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        by_cases hη : η = extAllTrue
        · rw [hη, flipPartition_allTrue]; exact htop
        · rw [flipPartition_of_ne hη]; exact hbot
      rw [h]; exact MeasurableSet.univ
    · have h : flipPartition ⁻¹' s = {η : oneEdgeBox.Exterior | η = extAllTrue} := by
        ext η
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · intro hmem
          by_contra hη
          rw [flipPartition_of_ne hη] at hmem
          exact hbot hmem
        · intro hη
          rw [hη, flipPartition_allTrue]
          exact htop
      rw [h]; exact measurableSet_extAllTrue
  · by_cases hbot : (⊥ : Setoid Bool) ∈ s
    · have h : flipPartition ⁻¹' s = {η : oneEdgeBox.Exterior | η = extAllTrue}ᶜ := by
        ext η
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq]
        constructor
        · intro hmem hη
          rw [hη, flipPartition_allTrue] at hmem
          exact htop hmem
        · intro hη
          rw [flipPartition_of_ne hη]
          exact hbot
      rw [h]; exact measurableSet_extAllTrue.compl
    · have h : flipPartition ⁻¹' s = ∅ := by
        ext η
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        by_cases hη : η = extAllTrue
        · rw [hη, flipPartition_allTrue]; exact htop
        · rw [flipPartition_of_ne hη]; exact hbot
      rw [h]; exact MeasurableSet.empty

lemma tendsto_extPerturb : Tendsto extPerturb atTop (𝓝 extAllTrue) := by
  rw [tendsto_pi_nhds]
  intro e
  have h_eventually : ∀ᶠ n in atTop, (e : ℕ) ≠ n + 1 := by
    apply eventually_atTop.mpr
    exact ⟨(e : ℕ) + 1, fun n hn => by omega⟩
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h_eventually] with n hn
  simp [extPerturb, hn, extAllTrue]


open scoped Classical

/-- The product of an exterior Dirac mass with the FK kernel. -/
lemma dirac_compProd_fkKernel {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : oneEdgeBox.Exterior → oneEdgeBox.BoundaryPartition) (hβ : Measurable β)
    (η : oneEdgeBox.Exterior) :
    Measure.dirac η ⊗ₘ oneEdgeBox.fkKernel hq hp β hβ =
      Measure.map (fun ξ : oneEdgeBox.Interior => (η, ξ))
        (oneEdgeBox.graph.fkMeasure hq hp (β η)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply measurable_prodMk_left hs,
    MeasureTheory.lintegral_dirac, FK.InfiniteVolume.FiniteBox.fkKernel_apply]

/-- The glued law of an exterior Dirac mass is the box law glued at that exterior
configuration. -/
lemma reconMeasure_dirac {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : oneEdgeBox.Exterior → oneEdgeBox.BoundaryPartition) (hβ : Measurable β)
    (η : oneEdgeBox.Exterior) :
    FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure oneEdgeBox hq hp β hβ
        (Measure.dirac η) =
      Measure.map (fun ξ : oneEdgeBox.Interior => oneEdgeBox.glue (η, ξ))
        (oneEdgeBox.graph.fkMeasure hq hp (β η)) := by
  rw [FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure_def, dirac_compProd_fkKernel,
    Measure.map_map (FK.InfiniteVolume.LimitClosure.FiniteBox.measurable_glue oneEdgeBox)
      (measurable_prodMk_left (x := η))]
  rfl

/-- Test integrals against the glued law of an exterior Dirac mass. -/
lemma integral_reconMeasure_dirac {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : oneEdgeBox.Exterior → oneEdgeBox.BoundaryPartition) (hβ : Measurable β)
    (η : oneEdgeBox.Exterior)
    (f : BoundedContinuousFunction (FK.InfiniteVolume.Configuration ℕ) ℝ) :
    ∫ ω, f ω ∂(FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure oneEdgeBox hq hp β hβ
        (Measure.dirac η)) =
      ∫ ξ : oneEdgeBox.Interior, f (oneEdgeBox.glue (η, ξ))
        ∂(oneEdgeBox.graph.fkMeasure hq hp (β η)) := by
  have hmeas : Measurable (fun ξ : oneEdgeBox.Interior => oneEdgeBox.glue (η, ξ)) :=
    (FK.InfiniteVolume.LimitClosure.FiniteBox.measurable_glue oneEdgeBox).comp
      (measurable_const.prodMk measurable_id)
  rw [reconMeasure_dirac, integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]

/-- The exterior marginal of a glued law is the exterior measure it was built from. -/
lemma exteriorMeasure_reconPM {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : oneEdgeBox.Exterior → oneEdgeBox.BoundaryPartition) (hβ : Measurable β)
    (ν : ProbabilityMeasure oneEdgeBox.Exterior) :
    oneEdgeBox.exteriorMeasure
      (FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox hq hp β hβ ν) = ν := by
  apply Subtype.ext
  show Measure.map (fun ω : FK.InfiniteVolume.Configuration ℕ => (oneEdgeBox.splitEquiv ω).1)
      (FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure oneEdgeBox hq hp β hβ (ν : Measure _))
    = (ν : Measure oneEdgeBox.Exterior)
  rw [FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure_def,
    Measure.map_map (g := fun ω : FK.InfiniteVolume.Configuration ℕ =>
        (oneEdgeBox.splitEquiv ω).1) (f := oneEdgeBox.glue)
      (measurable_fst.comp oneEdgeBox.splitEquiv.measurable)
      (FK.InfiniteVolume.LimitClosure.FiniteBox.measurable_glue oneEdgeBox)]
  have hcomp : (fun ω : FK.InfiniteVolume.Configuration ℕ => (oneEdgeBox.splitEquiv ω).1) ∘
      oneEdgeBox.glue = Prod.fst := by
    funext z
    exact congrArg Prod.fst (oneEdgeBox.split_glue z)
  rw [hcomp]
  exact Measure.fst_compProd (ν : Measure oneEdgeBox.Exterior) (oneEdgeBox.fkKernel hq hp β hβ)

/-- Every glued law of an exterior Dirac mass is DLR for its own specification. -/
lemma isDLR_reconPM_dirac {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : oneEdgeBox.Exterior → oneEdgeBox.BoundaryPartition) (hβ : Measurable β)
    (η : oneEdgeBox.Exterior) :
    oneEdgeBox.IsDLR hq hp β hβ
      (FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox hq hp β hβ
        (MeasureTheory.diracProba η)) := by
  rw [FK.InfiniteVolume.LimitClosure.FiniteBox.isDLR_iff_recon, exteriorMeasure_reconPM]
  rfl



instance uniqueOneEdgeGraphEdge : Unique oneEdgeGraph.Edge where
  default := oneEdgeLabel
  uniq e := Subtype.ext (by
    have h : (e : ℕ) ∈ ({0} : Finset ℕ) := e.2
    simp only [Finset.mem_singleton] at h
    simp [oneEdgeLabel, h])

instance nonemptyOneEdgeGraphVertex : Nonempty oneEdgeGraph.Vertex := ⟨false⟩

lemma oneEdge_componentCount_free_allOpen :
    oneEdgeGraph.componentCount oneEdgeGraph.freeBoundary oneEdgeGraph.allOpen = 1 := by
  apply componentCount_eq_one_of_preconnected _ _ _ false
  intro x y
  cases x <;> cases y
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    refine ⟨(fun h => Bool.noConfusion h), Or.inr ⟨oneEdgeLabel, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  · apply SimpleGraph.Adj.reachable
    refine ⟨(fun h => Bool.noConfusion h), Or.inr ⟨oneEdgeLabel, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  · exact SimpleGraph.Reachable.refl _

lemma oneEdge_componentCount_free_allClosed :
    oneEdgeGraph.componentCount oneEdgeGraph.freeBoundary oneEdgeGraph.allClosed = 2 := by
  rw [componentCount_free_allClosed]
  change Nat.card Bool = 2
  simp

lemma oneHalf_sub_oneHalf : (1 - 1 / 2 : NNReal) = 1 / 2 := by
  apply NNReal.eq
  norm_num [NNReal.coe_sub (show (1 / 2 : NNReal) ≤ 1 by norm_num)]

lemma oneEdge_free_weight_allOpen :
    oneEdgeGraph.fkWeight 2 (1 / 2 : NNReal) oneEdgeGraph.freeBoundary
      oneEdgeGraph.allOpen = 1 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    oneEdge_componentCount_free_allOpen, LabelledMultigraph.allOpen]

lemma oneEdge_free_weight_allClosed :
    oneEdgeGraph.fkWeight 2 (1 / 2 : NNReal) oneEdgeGraph.freeBoundary
      oneEdgeGraph.allClosed = 2 := by
  have hcc := oneEdge_componentCount_free_allClosed
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    hcc, LabelledMultigraph.allClosed, oneHalf_sub_oneHalf]

lemma oneEdge_wired_weight_allOpen :
    oneEdgeGraph.fkWeight 2 (1 / 2 : NNReal) oneEdgeGraph.wiredBoundary
      oneEdgeGraph.allOpen = 1 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    LabelledMultigraph.allOpen, componentCount_wired]

lemma oneEdge_wired_weight_allClosed :
    oneEdgeGraph.fkWeight 2 (1 / 2 : NNReal) oneEdgeGraph.wiredBoundary
      oneEdgeGraph.allClosed = 1 := by
  norm_num [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    LabelledMultigraph.allClosed, componentCount_wired, oneHalf_sub_oneHalf]

noncomputable local instance oneEdgeConfigurationFintype : Fintype oneEdgeGraph.Configuration :=
  oneEdgeGraph.instFintypeConfiguration

lemma sum_oneEdgeConfiguration {M : Type*} [AddCommMonoid M]
    (f : oneEdgeGraph.Configuration → M) :
    (∑ ω, f ω) = f oneEdgeGraph.allOpen + f oneEdgeGraph.allClosed := by
  rw [← Equiv.sum_comp (Equiv.funUnique oneEdgeGraph.Edge Bool).symm f, Fintype.sum_bool]
  rfl

lemma oneEdge_free_partitionFunction :
    oneEdgeGraph.partitionFunction 2 (1 / 2 : NNReal) oneEdgeGraph.freeBoundary = 3 := by
  let f : oneEdgeGraph.Configuration → NNReal := fun ω =>
    oneEdgeGraph.fkWeight 2 (1 / 2 : NNReal) oneEdgeGraph.freeBoundary ω
  have hsum : (∑ ω, f ω) = f oneEdgeGraph.allOpen + f oneEdgeGraph.allClosed :=
    sum_oneEdgeConfiguration f
  unfold LabelledMultigraph.partitionFunction
  exact hsum.trans (by
    dsimp [f]
    rw [oneEdge_free_weight_allOpen, oneEdge_free_weight_allClosed]
    norm_num)

lemma oneEdge_wired_partitionFunction :
    oneEdgeGraph.partitionFunction 2 (1 / 2 : NNReal) oneEdgeGraph.wiredBoundary = 2 := by
  let f : oneEdgeGraph.Configuration → NNReal := fun ω =>
    oneEdgeGraph.fkWeight 2 (1 / 2 : NNReal) oneEdgeGraph.wiredBoundary ω
  have hsum : (∑ ω, f ω) = f oneEdgeGraph.allOpen + f oneEdgeGraph.allClosed :=
    sum_oneEdgeConfiguration f
  unfold LabelledMultigraph.partitionFunction
  exact hsum.trans (by
    dsimp [f]
    rw [oneEdge_wired_weight_allOpen, oneEdge_wired_weight_allClosed]
    norm_num)

lemma oneEdge_free_allOpen_mass :
    oneEdgeGraph.fkPMF (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeGraph.freeBoundary
        oneEdgeGraph.allOpen = (1 / 3 : NNReal) := by
  rw [LabelledMultigraph.fkPMF_apply, oneEdge_free_weight_allOpen,
    oneEdge_free_partitionFunction]

lemma oneEdge_wired_allOpen_mass :
    oneEdgeGraph.fkPMF (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeGraph.wiredBoundary
        oneEdgeGraph.allOpen = (1 / 2 : NNReal) := by
  rw [LabelledMultigraph.fkPMF_apply, oneEdge_wired_weight_allOpen,
    oneEdge_wired_partitionFunction]

lemma oneEdge_free_fkMeasure_ne_wired :
    oneEdgeGraph.fkMeasure (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeGraph.freeBoundary ≠
    oneEdgeGraph.fkMeasure (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) oneEdgeGraph.wiredBoundary := by
  intro h
  have hm := congrArg (fun ν : Measure oneEdgeGraph.Configuration =>
    ν {oneEdgeGraph.allOpen}) h
  simp only [LabelledMultigraph.fkMeasure,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    oneEdge_free_allOpen_mass, oneEdge_wired_allOpen_mass] at hm
  norm_num at hm



lemma oneEdge_freeBoundary_eq_bot : oneEdgeGraph.freeBoundary = (⊥ : Setoid Bool) := rfl

lemma oneEdge_wiredBoundary_eq_top : oneEdgeGraph.wiredBoundary = (⊤ : Setoid Bool) := by
  ext u v
  exact Iff.rfl

/-- The indicator of the open box edge, as a bounded continuous function. -/
def openEdgeIndicator : BoundedContinuousFunction (FK.InfiniteVolume.Configuration ℕ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun ω => if ω 0 then 1 else 0, by
      have hfun : (fun ω : FK.InfiniteVolume.Configuration ℕ => if ω 0 then (1:ℝ) else 0)
          = (fun b : Bool => if b then (1:ℝ) else 0) ∘ (fun ω => ω 0) := rfl
      rw [hfun]
      exact (continuous_of_discreteTopology (f := fun b : Bool => if b then (1:ℝ) else 0)).comp
        (continuous_apply 0)⟩

lemma openEdgeIndicator_glue (η : oneEdgeBox.Exterior) (ξ : oneEdgeBox.Interior) :
    openEdgeIndicator (oneEdgeBox.glue (η, ξ)) = if ξ oneEdgeLabel then 1 else 0 := by
  have h : (oneEdgeBox.glue (η, ξ)) 0 = ξ oneEdgeLabel := by
    simp [FK.InfiniteVolume.FiniteBox.glue, oneEdgeLabel, oneEdgeBox]
  have hunf : openEdgeIndicator (oneEdgeBox.glue (η, ξ)) =
      if (oneEdgeBox.glue (η, ξ)) 0 then (1:ℝ) else 0 := rfl
  rw [hunf, h]

/-- The integral of the open-edge indicator against a box law is the mass of the
all-open configuration. -/
lemma integral_openEdgeIndicator_fkMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (π : oneEdgeBox.graph.BoundaryPartition) (η : oneEdgeBox.Exterior) :
    ∫ ξ : oneEdgeBox.Interior, openEdgeIndicator (oneEdgeBox.glue (η, ξ))
        ∂(oneEdgeBox.graph.fkMeasure hq hp π) =
      (oneEdgeBox.graph.fkPMF hq hp π oneEdgeGraph.allOpen).toReal := by
  have hset : MeasurableSet {ξ : oneEdgeBox.Interior | ξ oneEdgeLabel = true} := by
    have hmeas : Measurable (fun ξ : oneEdgeBox.Interior => ξ oneEdgeLabel) :=
      measurable_pi_apply oneEdgeLabel
    have hsing : MeasurableSet {true} := measurableSet_singleton true
    exact hmeas hsing
  have hpt : ∀ ξ : oneEdgeBox.Interior, openEdgeIndicator (oneEdgeBox.glue (η, ξ)) =
      Set.indicator {ξ' : oneEdgeBox.Interior | ξ' oneEdgeLabel = true} (fun _ => (1:ℝ)) ξ := by
    intro ξ
    rw [openEdgeIndicator_glue]
    by_cases h : ξ oneEdgeLabel = true
    · simp [h]
    · have h' : ξ oneEdgeLabel = false := by
        cases hh : ξ oneEdgeLabel <;> simp_all
      simp [h']
  simp only [hpt]
  rw [show ∫ ξ : oneEdgeBox.Interior,
      Set.indicator {ξ' : oneEdgeBox.Interior | ξ' oneEdgeLabel = true} (fun _ => (1:ℝ)) ξ
        ∂(oneEdgeBox.graph.fkMeasure hq hp π) =
      (oneEdgeBox.graph.fkMeasure hq hp π).real
        {ξ : oneEdgeBox.Interior | ξ oneEdgeLabel = true} from
    integral_indicator_one hset]
  have hsingle : {ξ : oneEdgeBox.Interior | ξ oneEdgeLabel = true} = {oneEdgeGraph.allOpen} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      funext a
      rw [Subsingleton.elim a oneEdgeLabel]
      simpa [FK.Finite.LabelledMultigraph.allOpen] using h
    · intro h
      rw [h]
      rfl
  rw [hsingle, Measure.real_def, FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]

lemma oneEdge_bot_eq_free : (⊥ : oneEdgeBox.graph.BoundaryPartition) = oneEdgeGraph.freeBoundary :=
  rfl

lemma oneEdge_top_eq_wired : (⊤ : oneEdgeBox.graph.BoundaryPartition) = oneEdgeGraph.wiredBoundary :=
  rfl

lemma oneEdge_free_mass_real :
    (oneEdgeGraph.fkPMF (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      (⊥ : oneEdgeBox.graph.BoundaryPartition) oneEdgeGraph.allOpen).toReal = (1 / 3 : ℝ) := by
  rw [oneEdge_bot_eq_free, oneEdge_free_allOpen_mass]
  norm_num

lemma oneEdge_wired_mass_real :
    (oneEdgeGraph.fkPMF (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      (⊤ : oneEdgeBox.graph.BoundaryPartition) oneEdgeGraph.allOpen).toReal = (1 / 2 : ℝ) := by
  rw [oneEdge_top_eq_wired, oneEdge_wired_allOpen_mass]
  norm_num

lemma diracProba_val (η : oneEdgeBox.Exterior) :
    (MeasureTheory.diracProba η : Measure oneEdgeBox.Exterior) = Measure.dirac η := rfl

/-- **Measurability alone does not make the FK DLR class weakly closed.**  There is
a measurable boundary specification of the one-edge box whose DLR class has a weak
limit point outside the class: the specification `flipPartition` differs only at a
single exterior configuration, which measurability cannot see. -/
theorem exists_weakLimit_not_isDLR_of_measurable :
    ∃ (φ : ℕ → ℕ) (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration ℕ)),
      StrictMono φ ∧
      Tendsto (fun n => FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox
        (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition
        (MeasureTheory.diracProba (extPerturb (φ n)))) atTop (𝓝 μ) ∧
      ¬ oneEdgeBox.IsDLR (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition μ := by
  obtain ⟨μ, φ, hφ, hμ⟩ := CompactSpace.tendsto_subseq
    (fun n => FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox
      (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      flipPartition measurable_flipPartition (MeasureTheory.diracProba (extPerturb n)))
  have hμ' : Tendsto (fun n => FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox
      (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      flipPartition measurable_flipPartition
      (MeasureTheory.diracProba (extPerturb (φ n)))) atTop (𝓝 μ) :=
    hμ
  refine ⟨φ, μ, hφ, hμ', ?_⟩
  intro hDLR
  -- The exterior marginal of any weak limit is the Dirac mass at the all-open
  -- exterior configuration.
  have hη : oneEdgeBox.exteriorMeasure μ = MeasureTheory.diracProba extAllTrue := by
    have hconv := FK.InfiniteVolume.InteriorWeakLimit.FiniteBox.tendsto_exteriorMeasure
      oneEdgeBox hμ'
    have hlim : Tendsto (fun n => MeasureTheory.diracProba (extPerturb (φ n))) atTop
        (𝓝 (MeasureTheory.diracProba extAllTrue)) :=
      MeasureTheory.continuous_diracProba.tendsto extAllTrue |>.comp
        (tendsto_extPerturb.comp hφ.tendsto_atTop)
    refine tendsto_nhds_unique ?_ hlim
    refine hconv.congr' ?_
    filter_upwards [] with n
    exact exteriorMeasure_reconPM (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num) flipPartition measurable_flipPartition
      (MeasureTheory.diracProba (extPerturb (φ n)))
  -- Along the sequence every test integral equals `1/3`.
  have hseq : ∀ n, ∫ ω, openEdgeIndicator ω ∂
      ((FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox
        (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition
        (MeasureTheory.diracProba (extPerturb (φ n)))) : Measure _) = (1 / 3 : ℝ) := by
    intro n
    have hne : extPerturb (φ n) ≠ extAllTrue := extPerturb_ne (φ n)
    show ∫ ω, openEdgeIndicator ω ∂
      (FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure oneEdgeBox
        (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition (Measure.dirac (extPerturb (φ n)))) = (1 / 3 : ℝ)
    rw [integral_reconMeasure_dirac, flipPartition_of_ne hne,
      integral_openEdgeIndicator_fkMeasure, oneEdge_free_mass_real]
  have hconvint := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ') openEdgeIndicator
  have hlimval : ∫ ω, openEdgeIndicator ω ∂(μ : Measure _) = (1 / 3 : ℝ) := by
    have h1 : Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop
        (𝓝 (∫ ω, openEdgeIndicator ω ∂(μ : Measure _))) :=
      hconvint.congr' (Filter.Eventually.of_forall hseq)
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- A DLR law would give the value `1/2`.
  have hdlrval : ∫ ω, openEdgeIndicator ω ∂(μ : Measure _) = (1 / 2 : ℝ) := by
    have hμeq : (μ : Measure (FK.InfiniteVolume.Configuration ℕ)) =
        FK.InfiniteVolume.LimitClosure.FiniteBox.reconMeasure oneEdgeBox
          (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
          flipPartition measurable_flipPartition
          (oneEdgeBox.exteriorMeasure μ : Measure oneEdgeBox.Exterior) :=
      (FK.InfiniteVolume.LimitClosure.FiniteBox.isDLR_iff_recon oneEdgeBox
        (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition μ).mp hDLR
    rw [hμeq, hη, diracProba_val, integral_reconMeasure_dirac, flipPartition_allTrue,
      integral_openEdgeIndicator_fkMeasure, oneEdge_wired_mass_real]
  rw [hdlrval] at hlimval
  norm_num at hlimval

/-- Subsequential FK limits along a fixed genuine exhaustion. -/
def IsSubseqFKLimit {E : Type*} [Countable E] (exh : BoxExhaustion E) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (α : ∀ n, (exh.box n).BoundaryPartition)
    (ν : ProbabilityMeasure (Configuration E)) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun n => (exh.box (φ n)).finiteVolumeLaw hq hp (α (φ n))) atTop (𝓝 ν)

/-- **Subsequential existence of infinite-volume FK limits is unconditional.**  For
every genuine box exhaustion and every choice of boundary setoids, some subsequence
of finite-volume laws has a weak limit.  No monotonicity or coherent nesting is
needed; only compactness of the space of probability measures on the Boolean
product. -/
theorem exists_isSubseqFKLimit {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition) :
    ∃ ν, IsSubseqFKLimit exh hq hp α ν := by
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq
    (fun n => (exh.box n).finiteVolumeLaw hq hp (α n))
  exact ⟨ν, φ, hφ, hν⟩

/-- A subsequential limit along a coarsening is an FK limit for that coarsening:
the reindexed boxes are again a genuine exhaustion. -/
theorem isFKLimit_of_isSubseqFKLimit {E : Type*} [Countable E] {exh : BoxExhaustion E}
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    {α : ∀ n, (exh.box n).BoundaryPartition}
    {ν : ProbabilityMeasure (Configuration E)} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h : Tendsto (fun n => (exh.box (φ n)).finiteVolumeLaw hq hp (α (φ n))) atTop (𝓝 ν)) :
    IsFKLimit ⟨fun n => exh.box (φ n), fun a b hab => exh.monotone (hφ.monotone hab),
      fun e => by
        obtain ⟨n, hn⟩ := exh.covers e
        obtain ⟨m, hm⟩ := hφ.tendsto_atTop.eventually (eventually_ge_atTop n) |>.exists
        exact ⟨m, exh.monotone hm hn⟩⟩ hq hp (fun n => α (φ n)) ν :=
  h


/-- **The DLR class of a measurable specification is not sequentially closed.**
There is a sequence of genuine DLR laws of the one-edge box (at `q = 2`, `p = 1/2`)
whose weak limit along a subsequence fails to be DLR.  Thus weak closedness
genuinely needs more than measurability of the boundary specification. -/
theorem dlrClass_flipPartition_not_seqClosed :
    ∃ (φ : ℕ → ℕ) (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration ℕ)),
      StrictMono φ ∧
      (∀ n, oneEdgeBox.IsDLR (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition
        (FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox
          (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
          flipPartition measurable_flipPartition
          (MeasureTheory.diracProba (extPerturb (φ n))))) ∧
      Tendsto (fun n => FK.InfiniteVolume.LimitClosure.FiniteBox.reconPM oneEdgeBox
        (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition
        (MeasureTheory.diracProba (extPerturb (φ n)))) atTop (𝓝 μ) ∧
      ¬ oneEdgeBox.IsDLR (q := 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        flipPartition measurable_flipPartition μ := by
  obtain ⟨φ, μ, hφ, hμ, hnot⟩ := exists_weakLimit_not_isDLR_of_measurable
  exact ⟨φ, μ, hφ, fun n => isDLR_reconPM_dirac (q := 2) (p := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) flipPartition measurable_flipPartition (extPerturb (φ n)),
    hμ, hnot⟩


end

end FK.InfiniteVolume.LimitClosure
