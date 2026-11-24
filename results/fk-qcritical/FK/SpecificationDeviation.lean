/-
# Theorem 5.1 infrastructure I: finitely supported events determine a law
-/
import FK.ExteriorIdentification
import FK.GibbsOrder

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

local instance m5BoundaryPartitionMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

local instance m5FiniteSetoidOfFinite (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FK.InfiniteVolume

variable {E : Type*}

/-- The family of all events depending on finitely many coordinates. -/
def cylinderEvents (E : Type*) : Set (Set (Configuration E)) :=
  {A | ∃ S : Finset E, FKLimit.DependsOnCoordinates A S}

lemma exists_support_inter {A B : Set (Configuration E)} {S T : Finset E}
    (hA : FKLimit.DependsOnCoordinates A S) (hB : FKLimit.DependsOnCoordinates B T) :
    ∃ U : Finset E, FKLimit.DependsOnCoordinates (A ∩ B) U := by
  classical
  refine ⟨S ∪ T, ?_⟩
  intro ω η h
  have hA' : ω ∈ A ↔ η ∈ A :=
    hA ω η (fun e he => h e (Finset.mem_union_left T he))
  have hB' : ω ∈ B ↔ η ∈ B :=
    hB ω η (fun e he => h e (Finset.mem_union_right S he))
  simp only [Set.mem_inter_iff, hA', hB']

lemma isPiSystem_cylinderEvents : IsPiSystem (cylinderEvents E) := by
  rintro A ⟨S, hS⟩ B ⟨T, hT⟩ -
  obtain ⟨U, hU⟩ := exists_support_inter hS hT
  exact ⟨U, hU⟩

lemma measurableCylinders_subset_cylinderEvents :
    MeasureTheory.measurableCylinders (fun _ : E => Bool) ⊆ cylinderEvents E := by
  intro A hA
  obtain ⟨s, T, -, rfl⟩ := (MeasureTheory.mem_measurableCylinders A).mp hA
  refine ⟨s, ?_⟩
  intro ω η h
  have hres : (s.restrict (π := fun _ : E => Bool)) ω =
      (s.restrict (π := fun _ : E => Bool)) η := by
    funext e
    exact h e.1 e.2
  simp only [MeasureTheory.mem_cylinder, hres]

lemma generateFrom_cylinderEvents_le :
    MeasurableSpace.generateFrom (cylinderEvents E) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) := by
  classical
  rw [MeasurableSpace.generateFrom_le_iff]
  rintro A ⟨S, hS⟩
  exact FKLimit.DependsOnCoordinates.measurableSet hS

lemma pi_le_generateFrom_cylinderEvents :
    (MeasurableSpace.pi : MeasurableSpace (Configuration E)) ≤
      MeasurableSpace.generateFrom (cylinderEvents E) := by
  rw [← MeasureTheory.generateFrom_measurableCylinders (ι := E) (α := fun _ : E => Bool)]
  exact MeasurableSpace.generateFrom_mono measurableCylinders_subset_cylinderEvents

lemma generateFrom_cylinderEvents :
    (MeasurableSpace.pi : MeasurableSpace (Configuration E)) =
      MeasurableSpace.generateFrom (cylinderEvents E) :=
  le_antisymm pi_le_generateFrom_cylinderEvents generateFrom_cylinderEvents_le

/-- Two probability measures agreeing on every finitely supported event coincide. -/
theorem measure_eq_of_forall_dependsOn {μ ν : Measure (Configuration E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ (S : Finset E) (A : Set (Configuration E)),
      FKLimit.DependsOnCoordinates A S → μ A = ν A) : μ = ν := by
  classical
  refine MeasureTheory.ext_of_generate_finite (cylinderEvents E)
    generateFrom_cylinderEvents isPiSystem_cylinderEvents ?_ ?_
  · rintro A ⟨S, hS⟩
    exact h S A hS
  · rw [measure_univ, measure_univ]

end FK.InfiniteVolume

/-! ## The common-integrand identity

For a DLR law, the conditional probability of a fixed finitely supported event,
conditioned on the whole exterior of a box, is the value of the *same*
specification function for every law with that specification.  Averaging over
the law gives the event mass as the integral of that common function. -/

namespace FK.InfiniteVolume

variable {E : Type*}


theorem apply_eq_integral_conditionalLaw_real
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    MeasureTheory.Measure.real (μ : Measure (Configuration E)) A =
      ∫ ω, MeasureTheory.Measure.real
        (B.conditionalLaw hq hp α (FKLimit.exteriorRestriction B.edges ω) :
          Measure (Configuration E)) A ∂(μ : Measure (Configuration E)) := by
  classical
  have hm : FKLimit.outsideSigma B.edges ≤ (inferInstance : MeasurableSpace (Configuration E)) :=
    FKLimit.outsideSigma_le B.edges
  have hAmeas : MeasurableSet A := FKLimit.DependsOnCoordinates.measurableSet hA
  have hcond := B.condExp_of_dependsOn_edges_of_isDLR hq hp α hα μ hμ hA
  have hInt : Integrable (A.indicator (fun _ => (1 : ℝ))) (μ : Measure (Configuration E)) :=
    (integrable_indicator_iff hAmeas).mpr (integrable_const _)
  have h := MeasureTheory.integral_condExp (μ := (μ : Measure (Configuration E)))
    (m := FKLimit.outsideSigma B.edges) (m₀ := (inferInstance : MeasurableSpace (Configuration E)))
    (f := A.indicator (fun _ => (1 : ℝ))) hm
  have hleft : ∫ ω, (μ : Measure (Configuration E))[A.indicator (fun _ => (1:ℝ)) |
        FKLimit.outsideSigma B.edges] ω ∂(μ : Measure (Configuration E)) =
      ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂(μ : Measure (Configuration E)) := h
  have hright : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂(μ : Measure (Configuration E)) =
      MeasureTheory.Measure.real (μ : Measure (Configuration E)) A := by
    rw [MeasureTheory.integral_indicator_const (μ := (μ : Measure (Configuration E))) (1 : ℝ) hAmeas]
    simp
  have hcongr : ∫ ω, (μ : Measure (Configuration E))[A.indicator (fun _ => (1:ℝ)) |
        FKLimit.outsideSigma B.edges] ω ∂(μ : Measure (Configuration E)) =
      ∫ ω, MeasureTheory.Measure.real
        (B.conditionalLaw hq hp α (FKLimit.exteriorRestriction B.edges ω) :
          Measure (Configuration E)) A ∂(μ : Measure (Configuration E)) := by
    refine integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    exact hω
  rw [← hright, ← hleft]
  exact hcongr

end FK.InfiniteVolume

/-! ## Constant boundary conventions fix the law on a box

If the boundary partition assigned to a box does not depend on the exterior
configuration, the DLR equation at that box determines the mass of every event
supported in the box.  This is the exact special case of Theorem 5.1 in which
the boundary condition is a fixed convention rather than a configuration-
dependent one; it is also the "reference value" used by the reduction below. -/

namespace FK.InfiniteVolume

variable {E : Type*}

theorem apply_eq_of_const_partition
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (α₀ : B.BoundaryPartition) (hconst : ∀ η, α η = α₀)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    MeasureTheory.Measure.real (μ : Measure (Configuration E)) A =
      MeasureTheory.Measure.real (B.graph.fkMeasure hq hp α₀)
        (B.interiorRestriction '' A) := by
  classical
  rw [apply_eq_integral_conditionalLaw_real B hq hp α hα μ hμ hA]
  have hconstfun : ∀ ω : Configuration E,
      MeasureTheory.Measure.real
        (B.conditionalLaw hq hp α (FKLimit.exteriorRestriction B.edges ω) :
          Measure (Configuration E)) A =
      MeasureTheory.Measure.real (B.graph.fkMeasure hq hp α₀)
        (B.interiorRestriction '' A) := by
    intro ω
    conv_lhs => rw [B.eq_preimage_interiorRestriction_image hA]
    rw [B.conditionalLaw_real_interior_preimage hq hp α (FKLimit.exteriorRestriction B.edges ω)
      MeasurableSet.of_discrete, hconst]
  simp only [hconstfun]
  rw [integral_const]
  simp [MeasureTheory.Measure.real_def]

end FK.InfiniteVolume

/-! ## Deviation of the specification from its reference value -/

namespace FK.InfiniteVolume

variable {E : Type*}

/-- The specification value at the observed exterior. -/
noncomputable def specValue (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (ω : Configuration E)
    (A : Set (Configuration E)) : ℝ :=
  MeasureTheory.Measure.real
    (B.conditionalLaw hq hp α (FKLimit.exteriorRestriction B.edges ω) :
      Measure (Configuration E)) A

/-- The reference (closed-exterior) specification value of the same box. -/
noncomputable def refValue (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (A : Set (Configuration E)) : ℝ :=
  MeasureTheory.Measure.real (B.graph.fkMeasure hq hp (α B.closedExterior))
    (B.interiorRestriction '' A)

lemma specValue_eq_fkMeasure (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (ω : Configuration E)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    specValue B hq hp α ω A =
      MeasureTheory.Measure.real
        (B.graph.fkMeasure hq hp (α (FKLimit.exteriorRestriction B.edges ω)))
        (B.interiorRestriction '' A) := by
  rw [specValue]
  conv_lhs => rw [B.eq_preimage_interiorRestriction_image hA]
  rw [B.conditionalLaw_real_interior_preimage hq hp α (FKLimit.exteriorRestriction B.edges ω)
    MeasurableSet.of_discrete]

lemma real_le_one_of_probability {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (C : Set α) :
    MeasureTheory.Measure.real ν C ≤ 1 := by
  have h := MeasureTheory.measureReal_mono (μ := ν) (s₁ := C) (s₂ := Set.univ)
    (Set.subset_univ C)
  have h2 : MeasureTheory.Measure.real ν (Set.univ : Set α) = 1 := by
    simp [MeasureTheory.Measure.real_def]
  linarith

lemma measurable_specValue (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    Measurable (fun ω : Configuration E => specValue B hq hp α ω A) := by
  classical
  have hfun : (fun ω : Configuration E => specValue B hq hp α ω A) =
      fun ω => MeasureTheory.Measure.real
        (B.graph.fkMeasure hq hp (α (FKLimit.exteriorRestriction B.edges ω)))
        (B.interiorRestriction '' A) := by
    funext ω
    exact specValue_eq_fkMeasure B hq hp α ω hA
  rw [hfun]
  have hfin : Measurable (fun P : B.BoundaryPartition =>
      MeasureTheory.Measure.real (B.graph.fkMeasure hq hp P) (B.interiorRestriction '' A)) :=
    measurable_of_finite _
  exact hfin.comp (hα.comp (FKLimit.measurable_exteriorRestriction B.edges))

theorem abs_apply_sub_refValue_le
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        refValue B hq hp α A| ≤
      ∫ ω, |specValue B hq hp α ω A - refValue B hq hp α A|
        ∂(μ : Measure (Configuration E)) := by
  classical
  have hrefprob : IsProbabilityMeasure
      (B.graph.fkMeasure hq hp (α B.closedExterior)) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp
      (α B.closedExterior)
  have hmain : MeasureTheory.Measure.real (μ : Measure (Configuration E)) A =
      ∫ ω, specValue B hq hp α ω A ∂(μ : Measure (Configuration E)) :=
    apply_eq_integral_conditionalLaw_real B hq hp α hα μ hμ hA
  have hconst : ∫ _ω, refValue B hq hp α A ∂(μ : Measure (Configuration E)) =
      refValue B hq hp α A := by
    rw [integral_const]
    simp [MeasureTheory.Measure.real_def]
  have hbound : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ‖specValue B hq hp α ω A - refValue B hq hp α A‖ ≤ 1 := by
    filter_upwards with ω
    have h1 : MeasureTheory.Measure.real
        (B.conditionalLaw hq hp α (FKLimit.exteriorRestriction B.edges ω) :
          Measure (Configuration E)) A ≤ 1 :=
      real_le_one_of_probability _ A
    have h1' : 0 ≤ MeasureTheory.Measure.real
        (B.conditionalLaw hq hp α (FKLimit.exteriorRestriction B.edges ω) :
          Measure (Configuration E)) A := MeasureTheory.measureReal_nonneg
    have h2 : refValue B hq hp α A ≤ 1 :=
      real_le_one_of_probability _ _
    have h2' : 0 ≤ refValue B hq hp α A := MeasureTheory.measureReal_nonneg
    rw [specValue, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hint : Integrable (fun ω : Configuration E =>
      specValue B hq hp α ω A - refValue B hq hp α A) (μ : Measure (Configuration E)) := by
    refine Integrable.of_bound ?_ 1 hbound
    exact ((measurable_specValue B hq hp α hα hA).sub measurable_const).aestronglyMeasurable
  have hsub : MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
      refValue B hq hp α A =
      ∫ ω, (specValue B hq hp α ω A - refValue B hq hp α A)
        ∂(μ : Measure (Configuration E)) := by
    have hintf : Integrable (fun ω : Configuration E => specValue B hq hp α ω A)
        (μ : Measure (Configuration E)) :=
      (hint.add (integrable_const (refValue B hq hp α A))).congr
        (Filter.Eventually.of_forall (fun ω => by simp))
    rw [hmain]
    conv_lhs => rw [← hconst]
    exact (integral_sub hintf (integrable_const (refValue B hq hp α A))).symm
  rw [hsub]
  exact MeasureTheory.abs_integral_le_integral_abs

end FK.InfiniteVolume

/-! ## From real masses back to measures, and the two uniqueness theorems -/

namespace FK.InfiniteVolume

variable {E : Type*}

theorem measure_eq_of_forall_real_dependsOn {μ ν : Measure (Configuration E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ (S : Finset E) (A : Set (Configuration E)),
      FKLimit.DependsOnCoordinates A S →
      MeasureTheory.Measure.real μ A = MeasureTheory.Measure.real ν A) : μ = ν := by
  refine measure_eq_of_forall_dependsOn (fun S A hA => ?_)
  have hreal := h S A hA
  rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- **Theorem 5.1, constant-convention case.** -/
theorem probabilityMeasure_eq_of_const_partition
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (hconst : ∀ n, ∃ α₀ : (exh.box n).BoundaryPartition, ∀ η, Φ.partition n η = α₀)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp) : μ = ν := by
  classical
  refine ProbabilityMeasure.toMeasure_injective
    (measure_eq_of_forall_real_dependsOn (fun S A hA => ?_))
  have hμ' : ∀ n, (exh.box n).IsDLR hq hp (Φ.partition n) (Φ.measurable_partition n) μ := hμ
  have hν' : ∀ n, (exh.box n).IsDLR hq hp (Φ.partition n) (Φ.measurable_partition n) ν := hν
  obtain ⟨n, hn⟩ := (exh.eventually_subset S).exists
  obtain ⟨α₀, hα₀⟩ := hconst n
  have hA' : FKLimit.DependsOnCoordinates A (exh.box n).edges := hA.mono hn
  rw [apply_eq_of_const_partition (exh.box n) hq hp (Φ.partition n) (Φ.measurable_partition n)
      α₀ hα₀ μ (hμ' n) hA',
    apply_eq_of_const_partition (exh.box n) hq hp (Φ.partition n) (Φ.measurable_partition n)
      α₀ hα₀ ν (hν' n) hA']

end FK.InfiniteVolume

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Theorem 5.1, mean-insensitivity form.** -/
theorem probabilityMeasure_apply_eq_of_tendsto_deviation
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    {A : Set (Configuration E)} {S : Finset E} (hA : FKLimit.DependsOnCoordinates A S)
    (hdevμ : Tendsto (fun n => ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(μ : Measure (Configuration E))) atTop (𝓝 0))
    (hdevν : Tendsto (fun n => ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(ν : Measure (Configuration E))) atTop (𝓝 0)) :
    MeasureTheory.Measure.real (μ : Measure (Configuration E)) A =
      MeasureTheory.Measure.real (ν : Measure (Configuration E)) A := by
  classical
  have hμ' : ∀ n, (exh.box n).IsDLR hq hp (Φ.partition n) (Φ.measurable_partition n) μ := hμ
  have hν' : ∀ n, (exh.box n).IsDLR hq hp (Φ.partition n) (Φ.measurable_partition n) ν := hν
  have key : ∀ ε : ℝ, 0 < ε →
      |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| ≤ ε := by
    intro ε hε
    have hev1 : ∀ᶠ n in atTop, S ⊆ (exh.box n).edges := exh.eventually_subset S
    have hev2 : ∀ᶠ n in atTop, ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(μ : Measure (Configuration E)) < ε / 2 :=
      (tendsto_order.mp hdevμ).2 (ε / 2) (by linarith)
    have hev3 : ∀ᶠ n in atTop, ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(ν : Measure (Configuration E)) < ε / 2 :=
      (tendsto_order.mp hdevν).2 (ε / 2) (by linarith)
    obtain ⟨n, hn1, hn2, hn3⟩ := (hev1.and (hev2.and hev3)).exists
    have hA' : FKLimit.DependsOnCoordinates A (exh.box n).edges := hA.mono hn1
    have hb1 := abs_apply_sub_refValue_le (exh.box n) hq hp (Φ.partition n)
      (Φ.measurable_partition n) μ (hμ' n) hA'
    have hb2 := abs_apply_sub_refValue_le (exh.box n) hq hp (Φ.partition n)
      (Φ.measurable_partition n) ν (hν' n) hA'
    have htri : |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| ≤
        |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
          refValue (exh.box n) hq hp (Φ.partition n) A| +
        |MeasureTheory.Measure.real (ν : Measure (Configuration E)) A -
          refValue (exh.box n) hq hp (Φ.partition n) A| := by
      have h := abs_sub_le (MeasureTheory.Measure.real (μ : Measure (Configuration E)) A)
        (refValue (exh.box n) hq hp (Φ.partition n) A)
        (MeasureTheory.Measure.real (ν : Measure (Configuration E)) A)
      rw [abs_sub_comm (refValue (exh.box n) hq hp (Φ.partition n) A)] at h
      exact h
    linarith [htri, neg_abs_le (MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
      refValue (exh.box n) hq hp (Φ.partition n) A)]
  have hzero : |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
      MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| = 0 := by
    by_contra h
    have hpos : 0 < |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)
    have hhalf := key (|MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| / 2) (by linarith)
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

end FK.InfiniteVolume

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Theorem 5.1 assembled from mean insensitivity.**  If for every finitely
supported event the specification's mean deviation from its closed-exterior
reference value vanishes along the exhaustion, under both laws, then the two DLR
laws coincide. -/
theorem probabilityMeasure_eq_of_tendsto_deviation
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hdev : ∀ (A : Set (Configuration E)) (S : Finset E),
      FKLimit.DependsOnCoordinates A S →
      (Tendsto (fun n => ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(μ : Measure (Configuration E))) atTop (𝓝 0) ∧
       Tendsto (fun n => ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(ν : Measure (Configuration E))) atTop (𝓝 0))) : μ = ν := by
  refine ProbabilityMeasure.toMeasure_injective
    (measure_eq_of_forall_real_dependsOn (fun S A hA => ?_))
  exact probabilityMeasure_apply_eq_of_tendsto_deviation exh Φ hq hp hμ hν hA
    (hdev A S hA).1 (hdev A S hA).2

/-- **A sufficient pointwise form.**  If for every box of the exhaustion and every
event supported in it, the specification value at *every* exterior configuration
already equals the closed-exterior reference value, then the DLR class is a
singleton.  This covers every convention whose boundary partition at the boxes of
the exhaustion is the reference partition. -/
theorem probabilityMeasure_eq_of_specValue_eq_refValue
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hpoint : ∀ (n : ℕ) (A : Set (Configuration E)),
      FKLimit.DependsOnCoordinates A (exh.box n).edges →
      ∀ ω : Configuration E,
        specValue (exh.box n) hq hp (Φ.partition n) ω A =
          refValue (exh.box n) hq hp (Φ.partition n) A) : μ = ν := by
  classical
  refine probabilityMeasure_eq_of_tendsto_deviation exh Φ hq hp hμ hν (fun A S hA => ?_)
  have hzeroμ : ∀ᶠ n in atTop, ∫ ω,
      |specValue (exh.box n) hq hp (Φ.partition n) ω A -
        refValue (exh.box n) hq hp (Φ.partition n) A|
      ∂(μ : Measure (Configuration E)) = 0 := by
    filter_upwards [exh.eventually_subset S] with n hn
    have hA' : FKLimit.DependsOnCoordinates A (exh.box n).edges := hA.mono hn
    have hfun : (fun ω : Configuration E =>
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|) = fun _ => 0 := by
      funext ω
      simp [hpoint n A hA' ω]
    rw [hfun, integral_zero]
  have hzeroν : ∀ᶠ n in atTop, ∫ ω,
      |specValue (exh.box n) hq hp (Φ.partition n) ω A -
        refValue (exh.box n) hq hp (Φ.partition n) A|
      ∂(ν : Measure (Configuration E)) = 0 := by
    filter_upwards [exh.eventually_subset S] with n hn
    have hA' : FKLimit.DependsOnCoordinates A (exh.box n).edges := hA.mono hn
    have hfun : (fun ω : Configuration E =>
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|) = fun _ => 0 := by
      funext ω
      simp [hpoint n A hA' ω]
    rw [hfun, integral_zero]
  exact ⟨tendsto_const_nhds.congr' (hzeroμ.mono (fun n hn => hn.symm)),
    tendsto_const_nhds.congr' (hzeroν.mono (fun n hn => hn.symm))⟩

end FK.InfiniteVolume

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Quantitative two-law comparison.**  For a common box, the difference of the
two laws' masses of a box-supported event is bounded by the sum of the two mean
deviations of the specification from its closed-exterior reference value.  This is
the quantitative form of the Theorem 5.1 comparison and it holds for *every* box
at once. -/
theorem abs_apply_sub_apply_le_deviation
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) (hν : B.IsDLR hq hp α hα ν)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| ≤
      (∫ ω, |specValue B hq hp α ω A - refValue B hq hp α A|
          ∂(μ : Measure (Configuration E))) +
        ∫ ω, |specValue B hq hp α ω A - refValue B hq hp α A|
          ∂(ν : Measure (Configuration E)) := by
  have hbμ := abs_apply_sub_refValue_le B hq hp α hα μ hμ hA
  have hbν := abs_apply_sub_refValue_le B hq hp α hα ν hν hA
  have htri : |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
      MeasureTheory.Measure.real (ν : Measure (Configuration E)) A| ≤
      |MeasureTheory.Measure.real (μ : Measure (Configuration E)) A -
        refValue B hq hp α A| +
      |MeasureTheory.Measure.real (ν : Measure (Configuration E)) A -
        refValue B hq hp α A| := by
    have h := abs_sub_le (MeasureTheory.Measure.real (μ : Measure (Configuration E)) A)
      (refValue B hq hp α A) (MeasureTheory.Measure.real (ν : Measure (Configuration E)) A)
    rw [abs_sub_comm (refValue B hq hp α A)] at h
    exact h
  linarith [htri, hbμ, hbν]

/-- A configuration-level sufficient condition for the reference value: whenever the
convention assigns to the box the same boundary partition as to the closed exterior,
the specification value is the reference value. -/
theorem specValue_eq_refValue_of_partition_eq
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (ω : Configuration E)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges)
    (hpart : α (FKLimit.exteriorRestriction B.edges ω) = α B.closedExterior) :
    specValue B hq hp α ω A = refValue B hq hp α A := by
  rw [specValue_eq_fkMeasure B hq hp α ω hA, refValue, hpart]

end FK.InfiniteVolume

/-! ## Axiom audit -/

#print axioms FK.InfiniteVolume.measure_eq_of_forall_dependsOn
#print axioms FK.InfiniteVolume.apply_eq_integral_conditionalLaw_real
#print axioms FK.InfiniteVolume.apply_eq_of_const_partition
#print axioms FK.InfiniteVolume.probabilityMeasure_eq_of_const_partition
#print axioms FK.InfiniteVolume.abs_apply_sub_refValue_le
#print axioms FK.InfiniteVolume.abs_apply_sub_apply_le_deviation
#print axioms FK.InfiniteVolume.probabilityMeasure_apply_eq_of_tendsto_deviation
#print axioms FK.InfiniteVolume.probabilityMeasure_eq_of_tendsto_deviation
#print axioms FK.InfiniteVolume.probabilityMeasure_eq_of_specValue_eq_refValue
#print axioms FK.InfiniteVolume.specValue_eq_refValue_of_partition_eq

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Closed-exterior transfer along an ordered coupling.**  Suppose a convention
only assigns its reference partition to extreiors that are closed on a fixed finite
set `S` of edges.  If `ξ ≤ η` pointwise and `η` is closed on `S`, then `ξ` is closed
on `S` as well, so the specification value at `ξ` is already the reference value.
This is the deterministic content of the source's step "ω_i ≤ ω_3 and
ω_3|_{∂S} = 0 imply that the interior conditional law is the reference one": it is
where the ordered coupling is actually used, and it needs no probability. -/
theorem specValue_eq_refValue_of_closed_exterior
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (S : Finset E)
    (hα : ∀ ξ : Configuration E, (∀ e ∈ S, ξ e = false) →
      α (FKLimit.exteriorRestriction B.edges ξ) = α B.closedExterior)
    {ξ η : Configuration E} (hle : ∀ e, ξ e ≤ η e) (hclosed : ∀ e ∈ S, η e = false)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    specValue B hq hp α ξ A = refValue B hq hp α A := by
  refine specValue_eq_refValue_of_partition_eq B hq hp α ξ hA (hα ξ ?_)
  intro e he
  have h1 : ξ e ≤ η e := hle e
  rw [hclosed e he] at h1
  cases hξ : ξ e
  · rfl
  · rw [hξ] at h1
    exact absurd h1 (by simp)

end FK.InfiniteVolume

#print axioms FK.InfiniteVolume.specValue_eq_refValue_of_closed_exterior

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Free-boundary convention: at most one DLR law.**  If a convention assigns the
free (discrete) boundary partition to every box of an exhaustion, independently of
the exterior configuration, then its DLR class is a singleton.  This is an
unconditional instance of the constant-convention theorem above, and the exact
abstract counterpart of "a fixed boundary condition determines the weak limit". -/
theorem probabilityMeasure_eq_of_free_convention
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (hfree : ∀ (n : ℕ) (η : (exh.box n).Exterior), Φ.partition n η = ⊥)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp) : μ = ν :=
  probabilityMeasure_eq_of_const_partition exh Φ hq hp
    (fun n => ⟨⊥, fun η => hfree n η⟩) hμ hν

end FK.InfiniteVolume

#print axioms FK.InfiniteVolume.probabilityMeasure_eq_of_free_convention

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Cylinder separation.**  Two distinct probability measures on configurations
differ on a finitely supported event.  This is the contrapositive of the cylinder
determination theorem and is the precise form of the source's last step, "they
agree on cylindrical events and are thus equal". -/
theorem exists_dependsOn_real_ne {μ ν : Measure (Configuration E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ ≠ ν) :
    ∃ (S : Finset E) (A : Set (Configuration E)),
      FKLimit.DependsOnCoordinates A S ∧
        MeasureTheory.Measure.real μ A ≠ MeasureTheory.Measure.real ν A := by
  by_contra hcon
  push Not at hcon
  exact h (measure_eq_of_forall_real_dependsOn hcon)

/-- **Non-uniqueness forces boundary sensitivity.**  If two DLR laws of the same
convention differ, then the mean deviation of the specification from its
closed-exterior reference value cannot tend to zero under both laws for every
finitely supported event.  Equivalently: any completed proof of Theorem 5.1 must
establish mean insensitivity of the specification for at least one of the two laws.
This is the contrapositive of the reduction and records exactly where the
probabilistic work sits. -/
theorem not_tendsto_deviation_of_ne
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hne : μ ≠ ν) :
    ¬ (∀ (A : Set (Configuration E)) (S : Finset E),
        FKLimit.DependsOnCoordinates A S →
        (Tendsto (fun n => ∫ ω,
          |specValue (exh.box n) hq hp (Φ.partition n) ω A -
            refValue (exh.box n) hq hp (Φ.partition n) A|
          ∂(μ : Measure (Configuration E))) atTop (𝓝 0) ∧
         Tendsto (fun n => ∫ ω,
          |specValue (exh.box n) hq hp (Φ.partition n) ω A -
            refValue (exh.box n) hq hp (Φ.partition n) A|
          ∂(ν : Measure (Configuration E))) atTop (𝓝 0))) := by
  intro hdev
  exact hne (probabilityMeasure_eq_of_tendsto_deviation exh Φ hq hp hμ hν hdev)

end FK.InfiniteVolume

#print axioms FK.InfiniteVolume.exists_dependsOn_real_ne
#print axioms FK.InfiniteVolume.not_tendsto_deviation_of_ne

namespace FK.InfiniteVolume

variable {E : Type*}

/-- **Free/wired bounds for the specification value.**  At `q ≥ 1` and interior
`p`, the measure-level wiring monotonicity of the repo (`fkMeasure_sandwich`)
sandwiches the specification value of an *increasing* box event between the free
and the wired finite-box values, uniformly in the exterior configuration.  Hence,
for increasing events, the mean deviation of the specification is bounded by the
mean free/wired gap, which is a purely deterministic finite-volume quantity. -/
theorem real_bounds_of_free_wired_sandwich (B : FiniteBox E) {q p : NNReal}
    [DecidableEq B.graph.Vertex] [DecidableEq B.graph.Edge]
    (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {C : Set B.Interior} (hC : IsUpperSet C) :
    MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le
          B.graph.freeBoundary) C ≤
      MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (α η)) C ∧
    MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (α η)) C ≤
      MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le
          B.graph.wiredBoundary) C := by
  haveI i1 : IsProbabilityMeasure
      (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le B.graph.freeBoundary) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph _ hp1.le _
  haveI i2 : IsProbabilityMeasure
      (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (α η)) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph _ hp1.le _
  haveI i3 : IsProbabilityMeasure
      (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le B.graph.wiredBoundary) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph _ hp1.le _
  obtain ⟨h1, h2⟩ := B.graph.fkMeasure_sandwich hq hp0 hp1 (α η) hC
  exact ⟨ENNReal.toReal_mono (measure_ne_top _ _) h1,
    ENNReal.toReal_mono (measure_ne_top _ _) h2⟩

/-- The corresponding two-sided bound on the deviation of any specification value
from the *free* value, for increasing events. -/
theorem abs_specValue_sub_free_le_gap (B : FiniteBox E) {q p : NNReal}
    [DecidableEq B.graph.Vertex] [DecidableEq B.graph.Edge]
    (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {C : Set B.Interior} (hC : IsUpperSet C) :
    |MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (α η)) C -
      MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le
          B.graph.freeBoundary) C| ≤
    |MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le
          B.graph.wiredBoundary) C -
      MeasureTheory.Measure.real
        (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le
          B.graph.freeBoundary) C| := by
  obtain ⟨h1, h2⟩ := real_bounds_of_free_wired_sandwich B hq hp0 hp1 α η hC
  set f := MeasureTheory.Measure.real
    (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le B.graph.freeBoundary) C
  set s := MeasureTheory.Measure.real
    (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (α η)) C
  set w := MeasureTheory.Measure.real
    (B.graph.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le B.graph.wiredBoundary) C
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - f),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ w - f)]
  linarith

end FK.InfiniteVolume

#print axioms FK.InfiniteVolume.real_bounds_of_free_wired_sandwich
#print axioms FK.InfiniteVolume.abs_specValue_sub_free_le_gap

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace FK.InfiniteVolume

variable {E : Type*} [Countable E]

/-- **Cylinder masses from upper-corner masses only.**  Variant of
`cylinder_eq_of_upT_eq` in which the hypothesis is equality of the masses of the
finitely supported *upper corners* `upT S W` (these are increasing events), rather
than domination on all increasing measurable events. -/
theorem cylinder_eq_of_upT_mass_eq (S : Finset E) (μ ν : ProbabilityMeasure (Configuration E))
    (hup : ∀ W : Finset ↥S,
      (μ : Measure (Configuration E)) (upT S W) = (ν : Measure (Configuration E)) (upT S W))
    (T : Finset ↥S) :
    (μ : Measure (Configuration E)) (cyT S T) = (ν : Measure (Configuration E)) (cyT S T) := by
  classical
  have key : ∀ k : ℕ, ∀ W : Finset ↥S, (Finset.univ \ W).card = k →
      (μ : Measure (Configuration E)) (cyT S W) =
        (ν : Measure (Configuration E)) (cyT S W) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro W hk
      have hdecomp : Finset.univ.filter (fun U : Finset ↥S => W ⊆ U) =
          insert W (Finset.univ.filter (fun U : Finset ↥S => W ⊂ U)) := by
        ext U
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hWU
          by_cases h : U = W
          · exact Or.inl h
          · exact Or.inr ⟨hWU, fun hUW => h (Finset.Subset.antisymm hUW hWU)⟩
        · rintro (rfl | ⟨hWU, -⟩)
          · exact le_refl _
          · exact hWU
      have hnotmem : W ∉ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        exact h.2 (le_refl W)
      have hsum : ∀ ζ : ProbabilityMeasure (Configuration E),
          (ζ : Measure (Configuration E)) (upT S W) =
            (ζ : Measure (Configuration E)) (cyT S W) +
              ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
                (ζ : Measure (Configuration E)) (cyT S U) := by
        intro ζ
        rw [upT_eq_biUnion,
          measure_biUnion_finset (pairwiseDisjoint_cyT S W) (fun U _ => measurableSet_cyT S U),
          hdecomp, Finset.sum_insert hnotmem]
      have hupper : (μ : Measure (Configuration E)) (upT S W) =
          (ν : Measure (Configuration E)) (upT S W) := hup W
      have hIH : ∀ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
          (μ : Measure (Configuration E)) (cyT S U) =
            (ν : Measure (Configuration E)) (cyT S U) := by
        intro U hU
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
        refine ih ((Finset.univ \ U).card) ?_ U rfl
        have hlt : (Finset.univ \ U).card < (Finset.univ \ W).card := by
          rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ]
          exact Nat.sub_lt_sub_left
            (lt_of_lt_of_le (Finset.card_lt_card hU) (Finset.card_le_univ U))
            (Finset.card_lt_card hU)
        rwa [hk] at hlt
      have hsumEq : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (μ : Measure (Configuration E)) (cyT S U)) =
          ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (ν : Measure (Configuration E)) (cyT S U) :=
        Finset.sum_congr rfl hIH
      have hsumνtop : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
          (ν : Measure (Configuration E)) (cyT S U)) ≠ ⊤ := by
        have hle : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (ν : Measure (Configuration E)) (cyT S U)) ≤
            (ν : Measure (Configuration E)) (upT S W) := by
          rw [hsum ν]
          exact le_add_left le_rfl
        exact ne_top_of_le_ne_top (measure_ne_top _ _) hle
      have hfinal : (μ : Measure (Configuration E)) (cyT S W) +
          (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (ν : Measure (Configuration E)) (cyT S U)) =
          (ν : Measure (Configuration E)) (cyT S W) +
          (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (ν : Measure (Configuration E)) (cyT S U)) := by
        calc (μ : Measure (Configuration E)) (cyT S W) +
              (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
                (ν : Measure (Configuration E)) (cyT S U))
            = (μ : Measure (Configuration E)) (cyT S W) +
              (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
                (μ : Measure (Configuration E)) (cyT S U)) := by rw [hsumEq]
          _ = (μ : Measure (Configuration E)) (upT S W) := (hsum μ).symm
          _ = (ν : Measure (Configuration E)) (upT S W) := hupper
          _ = (ν : Measure (Configuration E)) (cyT S W) +
              (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
                (ν : Measure (Configuration E)) (cyT S U)) := hsum ν
      exact (ENNReal.add_left_inj hsumνtop).mp hfinal
  exact key ((Finset.univ \ T).card) T rfl

end FK.InfiniteVolume

namespace FK.InfiniteVolume

variable {E : Type*} [Countable E]

/-- Distinct true-set cylinders on a finite coordinate set are disjoint. -/
lemma cyT_disjoint {S : Finset E} {T U : Finset ↥S} (hTU : T ≠ U) :
    Disjoint (cyT S T) (cyT S U) := by
  refine Set.disjoint_left.mpr ?_
  intro ω hωT hωU
  apply hTU
  ext e
  exact (hωT e).symm.trans (hωU e)

/-- A finitely supported event is the finite disjoint union of the cylinders of the
true-set patterns it contains. -/
lemma eq_biUnion_cyT (S : Finset E) {A : Set (Configuration E)}
    [DecidablePred (fun T : Finset ↥S => cyT S T ⊆ A)]
    (hA : FKLimit.DependsOnCoordinates A S) :
    A = ⋃ T ∈ (Finset.univ.filter (fun T : Finset ↥S => cyT S T ⊆ A)), cyT S T := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hω
    refine ⟨Finset.univ.filter (fun e : ↥S => ω e.1 = true), ?_, ?_⟩
    · intro η hη
      exact (hA η ω (fun e he => by simpa using hη ⟨e, he⟩)).mpr hω
    · intro e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rintro ⟨T, hTA, hω⟩
    exact hTA hω

/-- If two probability measures agree on every true-set cylinder of a finite
coordinate set, they agree on every event supported there. -/
theorem measure_eq_of_cyT_eq (S : Finset E) (μ ν : ProbabilityMeasure (Configuration E))
    (hcell : ∀ T : Finset ↥S,
      (μ : Measure (Configuration E)) (cyT S T) = (ν : Measure (Configuration E)) (cyT S T))
    {A : Set (Configuration E)} [DecidablePred (fun T : Finset ↥S => cyT S T ⊆ A)]
    (hA : FKLimit.DependsOnCoordinates A S) :
    (μ : Measure (Configuration E)) A = (ν : Measure (Configuration E)) A := by
  classical
  have hdisj : ((Finset.univ.filter (fun T : Finset ↥S => cyT S T ⊆ A)) :
      Set (Finset ↥S)).PairwiseDisjoint (cyT S) := by
    intro T _ U _ hTU
    exact cyT_disjoint hTU
  have hmeas : ∀ T ∈ Finset.univ.filter (fun T : Finset ↥S => cyT S T ⊆ A),
      MeasurableSet (cyT S T) := fun T _ => measurableSet_cyT S T
  rw [eq_biUnion_cyT S hA,
    measure_biUnion_finset hdisj hmeas, measure_biUnion_finset hdisj hmeas]
  exact Finset.sum_congr rfl (fun T _ => hcell T)

end FK.InfiniteVolume

namespace FK.InfiniteVolume

variable {E : Type*} [Countable E]

/-- **Theorem 5.1 from mean insensitivity of increasing events.**  It is enough to
control the mean deviation of the specification on *increasing* finitely supported
events: the true-set cylinders of a finite coordinate set determine the law, and the
upper corners `upT S W` are exactly the increasing events used in the induction of
`cylinder_eq_of_upT_eq`.  Combined with `real_bounds_of_free_wired_sandwich`, this
means that at `q ≥ 1` the remaining input is the classical finite-volume free/wired
gap for increasing events. -/
theorem probabilityMeasure_eq_of_tendsto_deviation_increasing
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hdev : ∀ (A : Set (Configuration E)) (S : Finset E),
      FKLimit.DependsOnCoordinates A S → IsUpperSet A →
      (Tendsto (fun n => ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(μ : Measure (Configuration E))) atTop (𝓝 0) ∧
       Tendsto (fun n => ∫ ω,
        |specValue (exh.box n) hq hp (Φ.partition n) ω A -
          refValue (exh.box n) hq hp (Φ.partition n) A|
        ∂(ν : Measure (Configuration E))) atTop (𝓝 0))) : μ = ν := by
  classical
  refine ProbabilityMeasure.toMeasure_injective
    (measure_eq_of_forall_dependsOn (fun S A hA => ?_))
  have hup : ∀ W : Finset ↥S,
      (μ : Measure (Configuration E)) (upT S W) = (ν : Measure (Configuration E)) (upT S W) := by
    intro W
    have hdep : FKLimit.DependsOnCoordinates (upT S W) S := dependsOn_upT S W
    have hup' : IsUpperSet (upT S W) := isUpperSet_upT S W
    have hreal : MeasureTheory.Measure.real (μ : Measure (Configuration E)) (upT S W) =
        MeasureTheory.Measure.real (ν : Measure (Configuration E)) (upT S W) :=
      probabilityMeasure_apply_eq_of_tendsto_deviation exh Φ hq hp hμ hν hdep
        (hdev _ S hdep hup').1 (hdev _ S hdep hup').2
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def] at hreal
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
  exact measure_eq_of_cyT_eq S μ ν (fun W => cylinder_eq_of_upT_mass_eq S μ ν hup W) hA

end FK.InfiniteVolume

#print axioms FK.InfiniteVolume.cylinder_eq_of_upT_mass_eq
#print axioms FK.InfiniteVolume.measure_eq_of_cyT_eq
#print axioms FK.InfiniteVolume.probabilityMeasure_eq_of_tendsto_deviation_increasing
