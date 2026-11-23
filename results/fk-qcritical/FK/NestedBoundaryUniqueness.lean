import FK.TailConditionalTriviality

/-!
# Nested-boundary coupling errors and DLR uniqueness

This module supplies the DLR/tail part of a nested-boundary strong-uniqueness
assembly.  It compares the actual finite-FK exterior conditional laws along a
single box exhaustion and boundary assignment.  A finite coupling only needs
to bound their finite-cylinder discrepancy on a common auxiliary space by an
error tending to zero pointwise almost everywhere.

The first theorem identifies two extremal DLR laws from this condition.  The
second uses the completed tail Choquet decomposition to identify arbitrary
members of the same DLR class when every pair of extremal laws admits such a
coupling.  The coupling condition is deliberately stated for the supplied
boundary assignment: no right-wired split-graph estimate is asserted to hold
for arbitrary boundaries.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FK.InfiniteVolume

universe u v

/-- A common auxiliary representation of two global laws, together with a
vanishing bound for the discrepancy of their actual FK exterior conditional
probabilities on every finite-base cylinder.

The maps `X` and `Y` are used only to transport almost-everywhere statements
from the two configuration measures to the common auxiliary space. -/

def HasVanishingExteriorCouplingError {E : Type u}
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E)) : Prop :=
  ∃ (Θ : Type u) (_ : MeasurableSpace Θ) (ρ : Measure Θ)
    (_ : IsProbabilityMeasure ρ) (X Y : Θ → Configuration E) (err : ℕ → Θ → ℝ),
    Measurable X ∧ Measurable Y ∧
    Measure.map X ρ = (μ : Measure (Configuration E)) ∧
    Measure.map Y ρ = (ν : Measure (Configuration E)) ∧
    (∀ᵐ z ∂ρ, Tendsto (fun n ↦ err n z) atTop (𝓝 0)) ∧
    ∀ (I : Finset E) (S : Set (I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      |(((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges (X z)) :
          Measure (Configuration E)).real (MeasureTheory.cylinder I S)) -
        (((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges (Y z)) :
          Measure (Configuration E)).real (MeasureTheory.cylinder I S))| ≤ err n z

/-- Extremal DLR uniqueness from a vanishing nested-boundary coupling error.
The reverse-martingale and tail-triviality inputs are supplied by the existing
DLR theory, rather than assumed again here. -/
theorem eq_of_extremal_dlr_of_hasVanishingExteriorCouplingError
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hextμ : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)))
    (hextν : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (ν : Measure (Configuration E)))
    (hcouple : HasVanishingExteriorCouplingError exh Φ hq hp μ ν) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S
  rw [← ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (μ : Measure (Configuration E)) _)
    (measure_ne_top (ν : Measure (Configuration E)) _)]
  rcases hcouple with ⟨Θ, mΘ, ρ, hρ, X, Y, err,
    hX, hY, hXμ, hYν, herr, hbound⟩
  let _ : MeasurableSpace Θ := mΘ
  let _ : IsProbabilityMeasure ρ := hρ
  let A : Set (Configuration E) := MeasureTheory.cylinder I S
  let F : ProbabilityMeasure (Configuration E) → ℕ → Configuration E → ℝ :=
    fun ξ n ω ↦ ((exh.box n).conditionalLaw hq hp (Φ.partition n)
      (FKLimit.exteriorRestriction (exh.box n).edges ω) :
      Measure (Configuration E)).real A
  have hμlim : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ F μ n ω) atTop
        (𝓝 ((μ : Measure (Configuration E)).real A)) :=
    tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
      exh Φ hq hp μ hμ hextμ (dependsOnCoordinates_cylinder I S)
  have hνlim : ∀ᵐ ω ∂(ν : Measure (Configuration E)),
      Tendsto (fun n ↦ F ν n ω) atTop
        (𝓝 ((ν : Measure (Configuration E)).real A)) :=
    tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
      exh Φ hq hp ν hν hextν (dependsOnCoordinates_cylinder I S)
  have hμρ : ∀ᵐ z ∂ρ, Tendsto (fun n ↦ F μ n (X z)) atTop
      (𝓝 ((μ : Measure (Configuration E)).real A)) := by
    exact (Measure.tendsto_ae_map (μ := ρ) hX.aemeasurable).eventually (by
      rwa [hXμ])
  have hνρ : ∀ᵐ z ∂ρ, Tendsto (fun n ↦ F ν n (Y z)) atTop
      (𝓝 ((ν : Measure (Configuration E)).real A)) := by
    exact (Measure.tendsto_ae_map (μ := ρ) hY.aemeasurable).eventually (by
      rwa [hYν])
  have hbound' : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      |F μ n (X z) - F ν n (Y z)| ≤ err n z := by
    simpa only [F, A] using hbound I S
  have heq : ∀ᵐ z ∂ρ, (μ : Measure (Configuration E)).real A =
      (ν : Measure (Configuration E)).real A := by
    filter_upwards [hμρ, hνρ, herr, hbound'] with z hμz hνz herrz hboundz
    have hdiff : Tendsto (fun n ↦ F μ n (X z) - F ν n (Y z)) atTop
        (𝓝 ((μ : Measure (Configuration E)).real A -
          (ν : Measure (Configuration E)).real A)) := hμz.sub hνz
    have hzero : Tendsto (fun n ↦ F μ n (X z) - F ν n (Y z)) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (by simpa using herrz.neg) herrz
      · filter_upwards [hboundz] with n hn
        exact (abs_le.mp hn).1
      · filter_upwards [hboundz] with n hn
        exact (abs_le.mp hn).2
    exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)
  simpa only [A, Measure.real] using heq.exists.choose_spec

/-- Membership in the DLR class is part of extremality in its measure image. -/
lemma mem_dlrMeasures_of_extremal_dlr
    {E : Type u} (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E))) : μ ∈ DLRMeasures exh Φ hq hp := by
  rcases hext.1 with ⟨ν, hν, hνμ⟩
  have h : ν = μ := ProbabilityMeasure.toMeasure_injective hνμ
  simpa only [h] using hν

/-- Full DLR uniqueness from pairwise vanishing nested-boundary coupling errors
on extremal laws.  A reference extremal law is obtained from an actual tail
fibre, and both arbitrary DLR laws are then identified by the existing tail
Choquet decomposition. -/
theorem eq_dlr_of_pairwise_hasVanishingExteriorCouplingError
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hpair : ∀ κ ξ : ProbabilityMeasure (Configuration E),
      FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (κ : Measure (Configuration E)) →
      FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (ξ : Measure (Configuration E)) →
      HasVanishingExteriorCouplingError exh Φ hq hp κ ξ) : μ = ν := by
  have hgood := (ae_mem_dlrMeasures_tailConditionalLaw exh Φ hq hp μ hμ).and
    (ae_isExtremalIn_dlr_tailConditionalLaw exh Φ hq hp μ hμ)
  obtain ⟨ω, hκ, hextκ⟩ := hgood.exists
  let κ : ProbabilityMeasure (Configuration E) := tailConditionalLaw μ ω
  change κ ∈ DLRMeasures exh Φ hq hp at hκ
  change FK.IsExtremalIn
    ((fun η : ProbabilityMeasure (Configuration E) ↦
      (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
    (κ : Measure (Configuration E)) at hextκ
  have heq (ξ : ProbabilityMeasure (Configuration E))
      (hξ : ξ ∈ DLRMeasures exh Φ hq hp)
      (hextξ : FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (ξ : Measure (Configuration E))) : ξ = κ :=
    eq_of_extremal_dlr_of_hasVanishingExteriorCouplingError
      exh Φ hq hp ξ κ hξ hκ hextξ hextκ (hpair ξ κ hextξ hextκ)
  have hμκ : μ = κ := by
    apply eq_dlr_of_extremal_unique exh Φ hq hp μ κ hμ
    intro ξ hextξ
    exact heq ξ (mem_dlrMeasures_of_extremal_dlr exh Φ hq hp ξ hextξ) hextξ
  have hνκ : ν = κ := by
    apply eq_dlr_of_extremal_unique exh Φ hq hp ν κ hν
    intro ξ hextξ
    exact heq ξ (mem_dlrMeasures_of_extremal_dlr exh Φ hq hp ξ hextξ) hextξ
  exact hμκ.trans hνκ.symm

end FK.InfiniteVolume
