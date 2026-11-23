import FK.ReverseMartingale
import FK.NonlocalGeometry

/-!
# Cylinder weak-limit closure for nonlocal FK specifications

The analytic input is local constancy along almost every exterior fibre, not
global local constancy.  Finite-valued lower integrals of locally constant
random indices pass through weak convergence: each fibre's frontier is null,
so the ordinary null-frontier portmanteau theorem applies.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.NonlocalInterior

open CurvatureVariance.Infra.Percolation
open ConventionGeometry
open ConventionTransport

noncomputable section

local instance nonlocalBoundaryPartitionMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

local instance nonlocalFiniteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- If a set belongs to the neighbourhood filter at `x`, then `x` is not in
the closure of its complement. -/
lemma not_mem_closure_compl_of_mem_nhds {X : Type*} [TopologicalSpace X]
    {A : Set X} {x : X} (h : A ∈ 𝓝 x) : x ∉ closure Aᶜ := by
  intro hx
  obtain ⟨U, hUA, hU, hxU⟩ := mem_nhds_iff.mp h
  obtain ⟨y, hyU, hy⟩ := (mem_closure_iff.mp hx) U hU hxU
  exact hy (hUA hyU)

/-- Fibres of an almost-everywhere locally constant measurable index have
null frontier. -/
lemma measure_frontier_preimage_singleton_eq_zero
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : ProbabilityMeasure X) (α : X → ι)
    (hlocal : ∀ᵐ x ∂(μ : Measure X), ∀ᶠ y in 𝓝 x, α y = α x) (a : ι) :
    (μ : Measure X) (frontier (α ⁻¹' {a})) = 0 := by
  have hbad : (μ : Measure X) {x | ¬ ∀ᶠ y in 𝓝 x, α y = α x} = 0 := by
    simpa only [ae_iff] using hlocal
  apply measure_mono_null (show frontier (α ⁻¹' {a}) ⊆
    {x | ¬ ∀ᶠ y in 𝓝 x, α y = α x} from ?_) hbad
  intro x hx
  simp only [Set.mem_ofPred_eq]
  intro hlocalx
  rw [frontier_eq_closure_inter_closure] at hx
  by_cases hxa : α x = a
  · have hmem : α ⁻¹' {a} ∈ 𝓝 x := by
      filter_upwards [hlocalx] with y hy
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, hxa] using hy
    exact not_mem_closure_compl_of_mem_nhds hmem hx.2
  · have hmem : (α ⁻¹' {a})ᶜ ∈ 𝓝 x := by
      filter_upwards [hlocalx] with y hy
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact fun hya => hxa (hy.symm.trans hya)
    have hnot := not_mem_closure_compl_of_mem_nhds hmem
    rw [compl_compl] at hnot
    exact hnot hx.1

/-- General simple-function map underlying a finite random index. -/
noncomputable def indexedSimpleFunc {X ι : Type*} [MeasurableSpace X]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Finite ι]
    (α : X → ι) (hα : Measurable α) : SimpleFunc X ι where
  toFun := α
  measurableSet_fiber' a := hα (measurableSet_singleton a)
  finite_range' := Set.toFinite _

@[simp] lemma indexedSimpleFunc_apply {X ι : Type*} [MeasurableSpace X]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Finite ι]
    (α : X → ι) (hα : Measurable α) (x : X) :
    indexedSimpleFunc α hα x = α x := rfl

/-- Lower integrals of a finite-valued statistic converge along weakly
convergent probability measures when its random index is locally constant
almost everywhere under the limiting exterior law. -/
theorem tendsto_lintegral_indexed_of_tendsto
    {X ι J : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Finite ι]
    {l : Filter J} {μs : J → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) (α : X → ι) (hα : Measurable α)
    (hlocal : ∀ᵐ x ∂(μ : Measure X), ∀ᶠ y in 𝓝 x, α y = α x)
    (g : ι → ℝ≥0∞) (hg : ∀ a, g a ≠ ∞) :
    Tendsto (fun j => ∫⁻ x, g (α x) ∂(μs j : Measure X)) l
      (𝓝 (∫⁻ x, g (α x) ∂(μ : Measure X))) := by
  let sα := indexedSimpleFunc α hα
  have hfibre (a : ι) : Tendsto
      (fun j => (μs j : Measure X) (α ⁻¹' {a})) l
      (𝓝 ((μ : Measure X) (α ⁻¹' {a}))) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (measure_frontier_preimage_singleton_eq_zero μ α hlocal a)
  have hformula (ν : ProbabilityMeasure X) :
      (∫⁻ x, g (α x) ∂(ν : Measure X)) =
        ∑ a ∈ sα.range, g a * (ν : Measure X) (α ⁻¹' {a}) := by
    change (∫⁻ x, (sα.map g) x ∂(ν : Measure X)) = _
    rw [SimpleFunc.lintegral_eq_lintegral]
    exact SimpleFunc.map_lintegral g sα
  simp_rw [hformula]
  exact tendsto_finsetSum sα.range fun a _ =>
    ENNReal.Tendsto.const_mul (hfibre a) (Or.inr (hg a))

/-- The finite exterior coordinates needed by an event supported on `T`. -/
def exteriorSupport {E : Type*} (B : FiniteBox E) (T : Finset E) :
    Finset {e : E // e ∉ B.edges} := T.subtype _

/-- Complete a configuration on finitely many exterior coordinates by closing
all remaining exterior coordinates. -/
def extendExterior {E : Type*} (B : FiniteBox E) {T : Finset E}
    (z : exteriorSupport B T → Bool) : B.Exterior :=
  fun e => if he : e ∈ exteriorSupport B T then z ⟨e, he⟩ else false

lemma conditionalLaw_apply_eq_of_agree {E : Type*} (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η ζ : B.Exterior)
    {A : Set (Configuration E)} {T : Finset E}
    (hA : FKLimit.DependsOnCoordinates A T)
    (hη : ∀ e : {e : E // e ∉ B.edges}, e.1 ∈ T → η e = ζ e) :
    (B.conditionalLaw hq hp α η : Measure (Configuration E)) A =
      (B.conditionalLaw hq hp (fun _ => α η) ζ : Measure (Configuration E)) A := by
  have hfiber : (fun ξ : B.Interior => B.glue (η, ξ)) ⁻¹' A =
      (fun ξ : B.Interior => B.glue (ζ, ξ)) ⁻¹' A := by
    ext ξ
    apply hA
    intro e heI
    by_cases he : e ∈ B.edges
    · simp only [FiniteBox.glue, he, dite_true]
    · simp only [FiniteBox.glue, he, dite_false]
      exact hη ⟨e, he⟩ heI
  change (Measure.map (fun ξ : B.Interior => B.glue (η, ξ))
      (B.graph.fkMeasure hq hp (α η))) A =
    (Measure.map (fun ξ : B.Interior => B.glue (ζ, ξ))
      (B.graph.fkMeasure hq hp (α η))) A
  rw [Measure.map_apply (B.measurable_glue_const_left η) hA.measurableSet,
    Measure.map_apply (B.measurable_glue_const_left ζ) hA.measurableSet, hfiber]

/-- Interior-reconstruction masses write as lower integrals of the actual
conditional global FK laws. -/
lemma apply_reconstruct {E : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    (InteriorWeakLimit.FiniteBox.reconstruct B hq hp α hα μ :
      Measure (Configuration E)) A =
      ∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
        ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
  change (Measure.map B.glue ((B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ
    B.fkKernel hq hp α hα)) A = _
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  rw [Measure.map_apply hg hA, Measure.compProd_apply (hg hA)]
  apply lintegral_congr
  intro η
  symm
  exact Measure.map_apply (B.measurable_glue_const_left η) hA

/-- Conditional masses of a fixed finitely supported event converge in lower
integral whenever the boundary partition is locally constant almost surely
under the limiting exterior law. -/
theorem tendsto_lintegral_conditionalLaw_apply_of_tendsto
    {E : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {A : Set (Configuration E)} {T : Finset E}
    (hA : FKLimit.DependsOnCoordinates A T)
    {J : Type*} {l : Filter J} {μs : J → ProbabilityMeasure B.Exterior}
    {μ : ProbabilityMeasure B.Exterior} (hμ : Tendsto μs l (𝓝 μ))
    (hlocal : ∀ᵐ η ∂(μ : Measure B.Exterior), ∀ᶠ ζ in 𝓝 η, α ζ = α η) :
    Tendsto (fun j => ∫⁻ η,
      (B.conditionalLaw hq hp α η : Measure (Configuration E)) A ∂(μs j : Measure B.Exterior)) l
      (𝓝 (∫⁻ η, (B.conditionalLaw hq hp α η : Measure (Configuration E)) A
        ∂(μ : Measure B.Exterior))) := by
  let idx : B.Exterior → B.BoundaryPartition × (exteriorSupport B T → Bool) :=
    fun η => (α η, fun e => η e)
  let g : B.BoundaryPartition × (exteriorSupport B T → Bool) → ℝ≥0∞ := fun z =>
    (B.conditionalLaw hq hp (fun _ => z.1) (extendExterior B z.2) :
      Measure (Configuration E)) A
  have hmeas : Measurable idx := by
    apply Measurable.prodMk hα
    exact Measurable.of_eval fun e => measurable_pi_apply e.1
  have hloc : ∀ᵐ η ∂(μ : Measure B.Exterior), ∀ᶠ ζ in 𝓝 η, idx ζ = idx η := by
    filter_upwards [hlocal] with η hη
    have hU : (↑(exteriorSupport B T) : Set {e : E // e ∉ B.edges}).pi
        (fun e => {η e}) ∈ 𝓝 η :=
      set_pi_mem_nhds (exteriorSupport B T).finite_toSet fun _ _ => by simp
    filter_upwards [hη, hU] with ζ hζα hζ
    apply Prod.ext hζα
    funext e
    exact hζ e.1 e.2
  have hfun : (fun η => (B.conditionalLaw hq hp α η : Measure (Configuration E)) A) =
      fun η => g (idx η) := by
    funext η
    apply conditionalLaw_apply_eq_of_agree B hq hp α η
      (extendExterior B (fun e => η e)) (hA := hA)
    intro e he
    simp only [extendExterior]
    split_ifs with hes
    · rfl
    · exact (hes (Finset.mem_subtype.mpr he)).elim
  simp_rw [hfun]
  exact tendsto_lintegral_indexed_of_tendsto hμ idx hmeas hloc g
    (fun _ => measure_ne_top _ _)

/-- Weak closure of DLR laws using only almost-everywhere local constancy of
the nonlocal boundary specification at the limiting exterior law. -/
theorem isDLR_of_tendsto_of_ae_eventually_eq {E : Type*} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp α hα (μs i))
    (hlocal : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      ∀ᶠ ζ in 𝓝 η, α ζ = α η) :
    B.IsDLR hq hp α hα μ := by
  apply InteriorWeakLimit.FiniteBox.isDLR_of_eq_reconstruct B hq hp α hα μ
  apply ProbabilityMeasure.toMeasure_injective
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro T S
  let A : Set (Configuration E) := cylinder T S
  have hA : FKLimit.DependsOnCoordinates A T := dependsOnCoordinates_cylinder T S
  have hleft : Tendsto (fun i => (μs i : Measure (Configuration E)) A) l
      (𝓝 ((μ : Measure (Configuration E)) A)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (by simp [hA.isClopen])
  have hright : Tendsto
      (fun i => (InteriorWeakLimit.FiniteBox.reconstruct B hq hp α hα (μs i) :
        Measure (Configuration E)) A) l
      (𝓝 ((InteriorWeakLimit.FiniteBox.reconstruct B hq hp α hα μ :
        Measure (Configuration E)) A)) := by
    simp_rw [apply_reconstruct B hq hp α hα _ hA.measurableSet]
    exact tendsto_lintegral_conditionalLaw_apply_of_tendsto B hq hp α hα hA
      (InteriorWeakLimit.FiniteBox.tendsto_exteriorMeasure B hμ) hlocal
  apply tendsto_nhds_unique (l := l) (f := fun i => (μs i : Measure (Configuration E)) A)
    (a := (μ : Measure (Configuration E)) A)
    (b := (InteriorWeakLimit.FiniteBox.reconstruct B hq hp α hα μ :
      Measure (Configuration E)) A)
  · exact hleft
  · apply hright.congr'
    filter_upwards [hDLR] with i hi
    exact congrArg (fun ν : ProbabilityMeasure (Configuration E) =>
      (ν : Measure (Configuration E)) A)
      (InteriorWeakLimit.FiniteBox.eq_reconstruct_of_isDLR B hq hp α hα (μs i) hi).symm


/-- Full-exhaustion form of almost-everywhere locally constant weak closure. -/
theorem mem_dlrMeasures_of_tendsto_of_ae_eventually_eq {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp)
    (hlocal : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, Φ.partition n ζ = Φ.partition n η) :
    μ ∈ DLRMeasures exh Φ hq hp := by
  intro n
  exact isDLR_of_tendsto_of_ae_eventually_eq (exh.box n) hq hp
    (Φ.partition n) (Φ.measurable_partition n) hμ
    (hDLR.mono fun _ hi => hi n) (hlocal n)


end

end FK.InfiniteVolume.NonlocalInterior
