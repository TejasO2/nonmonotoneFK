import FK.BackwardConditional

/-!
# Exterior conditional probabilities for actual FK-DLR laws

The DLR equation is a disintegration across the exterior/interior splitting.
We identify the corresponding elementary conditional expectation with the
actual finite FK measure.  The exterior configuration is not normalized away,
and the boundary setoid remains arbitrary and exterior-dependent.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace FK.InfiniteVolume.FiniteBox

open FK

variable {E : Type*}

local instance fkExteriorBoundaryMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

local instance fkExteriorFiniteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- The mass of an interior cylinder under a conditional global FK law is the
mass under its actual finite FK interior marginal. -/
theorem conditionalLaw_real_interior_preimage
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {C : Set B.Interior} (hC : MeasurableSet C) :
    (B.conditionalLaw hq hp α η : Measure (Configuration E)).real
        (B.interiorRestriction ⁻¹' C) =
      (B.graph.fkMeasure hq hp (α η)).real C := by
  rw [Measure.real, Measure.real, ← B.map_interiorRestriction_conditionalLaw hq hp α η,
    Measure.map_apply B.measurable_interiorRestriction hC]

/-- **Exact exterior conditioning of an FK-DLR law.**  For every measurable
interior event `C`, the ordinary conditional probability of its global lift,
given all edges outside the box, is the probability of `C` under the actual
finite FK law with boundary partition `α` evaluated at the observed exterior.

No positivity, extremality, product exterior law, or particular boundary
convention is assumed. -/
theorem condExp_interior_of_isDLR
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    {C : Set B.Interior} (hC : MeasurableSet C) :
    (μ : Measure (Configuration E))⟦B.interiorRestriction ⁻¹' C |
        FKLimit.outsideSigma B.edges⟧ =ᵐ[(μ : Measure (Configuration E))]
      fun ω ↦ (B.graph.fkMeasure hq hp
        (α (FKLimit.exteriorRestriction B.edges ω))).real C := by
  let X : Configuration E → B.Exterior := FKLimit.exteriorRestriction B.edges
  let Y : Configuration E → B.Interior := B.interiorRestriction
  have hX : Measurable X := FKLimit.measurable_exteriorRestriction B.edges
  have hY : Measurable Y := B.measurable_interiorRestriction
  have hsplit : Measure.map (fun ω ↦ (X ω, Y ω)) (μ : Measure (Configuration E)) =
      Measure.map X (μ : Measure (Configuration E)) ⊗ₘ B.fkKernel hq hp α hα := by
    change Measure.map B.splitEquiv (μ : Measure (Configuration E)) =
      (B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ B.fkKernel hq hp α hα
    exact hμ
  have hdist : (fun η ↦ condDistrib Y X (μ : Measure (Configuration E)) η) =ᵐ[
      Measure.map X (μ : Measure (Configuration E))]
      (fun η ↦ B.fkKernel hq hp α hα η) :=
    condDistrib_ae_eq_of_measure_eq_compProd hX.aemeasurable hY.aemeasurable hsplit
  have hdist_comp : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      condDistrib Y X (μ : Measure (Configuration E)) (X ω) =
        B.fkKernel hq hp α hα (X ω) :=
    (Measure.tendsto_ae_map hX.aemeasurable).eventually hdist
  have hcond := condDistrib_ae_eq_condExp
    (μ := (μ : Measure (Configuration E))) hX hY hC
  filter_upwards [hcond, hdist_comp] with ω hω hdistω
  change ((μ : Measure (Configuration E))⟦Y ⁻¹' C |
    MeasurableSpace.comap X MeasurableSpace.pi⟧) ω = _
  rw [← hω, hdistω, B.fkKernel_apply]

/-- The same exterior conditional probability, evaluated as the mass of the
original global event under `FiniteBox.conditionalLaw`. -/
theorem condExp_interior_eq_conditionalLaw_of_isDLR
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    {C : Set B.Interior} (hC : MeasurableSet C) :
    (μ : Measure (Configuration E))⟦B.interiorRestriction ⁻¹' C |
        FKLimit.outsideSigma B.edges⟧ =ᵐ[(μ : Measure (Configuration E))]
      fun ω ↦ (B.conditionalLaw hq hp α
        (FKLimit.exteriorRestriction B.edges ω) : Measure (Configuration E)).real
        (B.interiorRestriction ⁻¹' C) := by
  filter_upwards [B.condExp_interior_of_isDLR hq hp α hα μ hμ hC] with ω hω
  rw [hω, B.conditionalLaw_real_interior_preimage hq hp α _ hC]

/-- A global event depending only on the box coordinates is the preimage of
its interior image. -/
theorem eq_preimage_interiorRestriction_image
    (B : FiniteBox E) {A : Set (Configuration E)}
    (hA : FKLimit.DependsOnCoordinates A B.edges) :
    A = B.interiorRestriction ⁻¹' (B.interiorRestriction '' A) := by
  exact FKLimit.eq_preimage_restrict_image hA

/-- Exterior conditional probability of an arbitrary event supported on the
box's coordinates.  This is the finite-cylinder form needed in Proposition
1.8(1), with the actual global `conditionalLaw` on the right. -/
theorem condExp_of_dependsOn_edges_of_isDLR
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    (μ : Measure (Configuration E))⟦A | FKLimit.outsideSigma B.edges⟧
      =ᵐ[(μ : Measure (Configuration E))]
      fun ω ↦ (B.conditionalLaw hq hp α
        (FKLimit.exteriorRestriction B.edges ω) : Measure (Configuration E)).real A := by
  rw [B.eq_preimage_interiorRestriction_image hA]
  exact B.condExp_interior_eq_conditionalLaw_of_isDLR hq hp α hα μ hμ
    MeasurableSet.of_discrete

end FK.InfiniteVolume.FiniteBox

namespace FK.InfiniteVolume

open FK

universe u v

/-- For an extremal DLR law, the actual exterior finite-FK probabilities of a
fixed finitely supported event converge in `L¹` to its unconditional mass
along every box exhaustion.

This uses the exact DLR exterior identification, reverse conditional
expectation convergence, and extremal tail triviality.  It is deliberately an
`L¹` statement: no almost-everywhere full-sequence convergence is claimed. -/
theorem tendsto_eLpNorm_one_exteriorConditionalLaw_of_extremal_dlr
    {E : Type u} (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)))
    {A : Set (Configuration E)}
    (hA : ∀ᶠ n in atTop, FKLimit.DependsOnCoordinates A (exh.box n).edges) :
    Tendsto (fun n ↦ eLpNorm
      ((fun ω ↦ ((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real A) -
        fun _ ↦ (μ : Measure (Configuration E)).real A)
      1 (μ : Measure (Configuration E))) atTop (𝓝 0) := by
  have hAmeas : MeasurableSet A := by
    obtain ⟨n, hn⟩ := hA.exists
    exact hn.measurableSet
  have htail : FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (Configuration E)) :=
    zeroOneOn_tailSigma_of_extremal_dlr exh Φ hq hp μ hμ hext
  have htailcond : (μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧
      =ᵐ[(μ : Measure (Configuration E))] fun _ ↦ (μ : Measure (Configuration E)).real A :=
    FKLimit.condExp_indicator_of_zeroOneOn_tailSigma (μ : Measure (Configuration E))
      htail hAmeas
  let S : ℕ → Finset E := fun n ↦ (exh.box n).edges
  have hcof : ∀ T : Finset E, ∃ n, T ⊆ S n := by
    intro T
    exact (exh.eventually_subset T).exists
  have hback := FKLimit.tendsto_eLpNorm_one_condExp_indicator_outside_to_tail
    (μ := (μ : Measure (Configuration E))) S exh.monotone hcof hAmeas
  apply hback.congr'
  filter_upwards [hA] with n hn
  apply eLpNorm_congr_ae
  have hid := (exh.box n).condExp_of_dependsOn_edges_of_isDLR hq hp
    (Φ.partition n) (Φ.measurable_partition n) μ (hμ n) hn
  filter_upwards [hid, htailcond] with ω hω hωtail
  change ((μ : Measure (Configuration E))⟦A |
      FKLimit.outsideSigma (exh.box n).edges⟧ -
    (μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) ω = _
  simp only [Pi.sub_apply, hω, hωtail]

end FK.InfiniteVolume

namespace FK.InfiniteVolume

open FK

universe u v

/-- Finite-support form of
`tendsto_eLpNorm_one_exteriorConditionalLaw_of_extremal_dlr`.  The exhaustion
itself supplies eventual containment of the support, so no separate eventual
support hypothesis remains. -/
theorem tendsto_eLpNorm_one_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
    {E : Type u} (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)))
    {A : Set (Configuration E)} {T : Finset E}
    (hAT : FKLimit.DependsOnCoordinates A T) :
    Tendsto (fun n ↦ eLpNorm
      ((fun ω ↦ ((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real A) -
        fun _ ↦ (μ : Measure (Configuration E)).real A)
      1 (μ : Measure (Configuration E))) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_one_exteriorConditionalLaw_of_extremal_dlr
    exh Φ hq hp μ hμ hext
  filter_upwards [exh.eventually_subset T] with n hn
  exact hAT.mono hn

end FK.InfiniteVolume
