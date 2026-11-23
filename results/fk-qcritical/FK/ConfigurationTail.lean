import FK.TailTriviality
import FK.Proposition42

/-!
# Exterior and tail sigma-algebras on edge configurations

The exterior filtration is given by restriction to all edges outside a finite
set.  Its infimum is the tail sigma-algebra used in the strong-uniqueness
argument.  This file proves only the measurable-space facts and specializes
the tail-triviality theorem; it does not define a Gibbs specification.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

namespace FKLimit

/-- Restriction of an edge configuration to the edges outside `S`. -/
def exteriorRestriction {E : Type*} (S : Finset E)
    (ω : Configuration E) : {e : E // e ∉ S} → Bool :=
  fun e ↦ ω e.1

lemma measurable_exteriorRestriction {E : Type*} (S : Finset E) :
    Measurable (exteriorRestriction S) := by
  exact Measurable.of_eval (fun (e : {e : E // e ∉ S}) ↦ measurable_pi_apply e.1)

/-- Events depending only on edges outside the finite set `S`. -/
@[instance_reducible] def outsideSigma {E : Type*} (S : Finset E) : MeasurableSpace (Configuration E) :=
  MeasurableSpace.comap (exteriorRestriction S) MeasurableSpace.pi

lemma outsideSigma_le {E : Type*} (S : Finset E) :
    outsideSigma S ≤ (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
  (measurable_exteriorRestriction S).comap_le

/-- The tail sigma-algebra: events outside every finite edge set. -/
@[instance_reducible] def tailSigma {E : Type*} : MeasurableSpace (Configuration E) :=
  ⨅ S : Finset E, outsideSigma S

lemma tailSigma_le_outsideSigma {E : Type*} (S : Finset E) :
    tailSigma (E := E) ≤ outsideSigma S :=
  iInf_le (fun T : Finset E ↦ outsideSigma T) S

lemma tailSigma_le {E : Type*} :
    tailSigma (E := E) ≤ (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
  (tailSigma_le_outsideSigma (∅ : Finset E)).trans (outsideSigma_le ∅)

/-- Increasing the excluded finite set shrinks the exterior sigma-algebra. -/
lemma outsideSigma_anti {E : Type*} {S T : Finset E} (hST : S ⊆ T) :
    outsideSigma T ≤ outsideSigma S := by
  let inclusion : {e : E // e ∉ T} → {e : E // e ∉ S} :=
    fun e ↦ ⟨e.1, fun heS ↦ e.2 (hST heS)⟩
  let forget : ({e : E // e ∉ S} → Bool) → ({e : E // e ∉ T} → Bool) :=
    fun ω e ↦ ω (inclusion e)
  have hforget : Measurable forget := by
    exact Measurable.of_eval (fun (e : {e : E // e ∉ T}) ↦
      measurable_pi_apply (inclusion e))
  change MeasurableSpace.comap (exteriorRestriction T) MeasurableSpace.pi ≤
    MeasurableSpace.comap (exteriorRestriction S) MeasurableSpace.pi
  have heq : exteriorRestriction T = forget ∘ exteriorRestriction S := by
    funext ω e
    rfl
  rw [heq, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hforget.comap_le

/-- Configuration-space form of the tail-triviality step: conditional
probability given the exact exterior tail is the unconditional mass. -/
theorem condExp_indicator_of_zeroOneOn_tailSigma {E : Type*}
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    (htail : FK.ZeroOneOn (tailSigma (E := E)) μ)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    μ⟦A | tailSigma (E := E)⟧ =ᵐ[μ] fun _ ↦ μ.real A := by
  exact FK.condExp_indicator_of_zeroOneOn (m₀ := MeasurableSpace.pi)
    (mTail := tailSigma (E := E)) tailSigma_le htail hA

end FKLimit
