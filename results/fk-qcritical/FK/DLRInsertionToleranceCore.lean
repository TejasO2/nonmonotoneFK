import FK.PatchLifting
import FK.ConventionTransport

/-!
# Finite-pattern insertion tolerance from the actual FK DLR equation

At interior parameters every finite FK configuration has positive mass.  The
comp-product form of `FiniteBox.IsDLR` therefore propagates positive mass of an
exterior event to the event with any prescribed finite Boolean pattern.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical

local instance setoidMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FK.InsertionTolerance

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.BurtonKeane
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u v

/-- Replacing interior coordinates on a finite patch contained in a finite box
is the same as applying `Function.updateFinset` after gluing. -/
lemma glue_forceInterior {E : Type u} (B : FiniteBox.{u, v} E)
    (j : PatchIndex E) (hj : j.1 ⊆ B.edges) (η : B.Exterior) (ξ : B.Interior) :
    let ξ' : B.Interior := fun e =>
      if he : (e : E) ∈ j.1 then j.2 ⟨(e : E), he⟩ else ξ e
    B.glue (η, ξ') = Function.updateFinset (B.glue (η, ξ)) j.1 j.2 := by
  classical
  dsimp only
  funext e
  by_cases he : e ∈ j.1
  · have hbe : e ∈ B.edges := hj he
    simp [FiniteBox.glue, Function.updateFinset, he, hbe]
  · by_cases hbe : e ∈ B.edges
    · simp [FiniteBox.glue, Function.updateFinset, he, hbe]
    · simp [FiniteBox.glue, Function.updateFinset, he, hbe]

/-- The result of prescribing a finite pattern belongs to its cylinder. -/
lemma updateFinset_mem_forcedPattern {E : Type u}
    (j : PatchIndex E) (ω : E → Bool) :
    Function.updateFinset ω j.1 j.2 ∈ forcedPattern j := by
  change j.1.restrict (Function.updateFinset ω j.1 j.2) = j.2
  exact Function.restrict_updateFinset ω j.2

/-- **Fixed-box finite energy.**  A genuine FK-DLR law retains positive mass
when an arbitrary finite Boolean pattern contained in the box is prescribed on
an event depending only on the other coordinates. -/
theorem measure_pos_inter_forcedPattern_of_isDLR {E : Type u}
    (B : FiniteBox.{u, v} E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp₁.le α hα μ)
    (j : PatchIndex E) (hj : j.1 ⊆ B.edges)
    (A : Set (Configuration E)) (hA : MeasurableSet A)
    (hAdep : DependsOn (· ∈ A) (j.1 : Set E)ᶜ) (hApos : 0 < (μ : Measure _) A) :
    0 < (μ : Measure (Configuration E)) (A ∩ forcedPattern j) := by
  classical
  apply pos_iff_ne_zero.mpr
  intro hz
  have hnull : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ω ∉ A ∩ forcedPattern j := measure_eq_zero_iff_ae_notMem.mp hz
  have hAvoid : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      ∀ ξ, B.glue (η, ξ) ∉ A ∩ forcedPattern j :=
    ae_forall_interior_of_ae_glue B hq hp₁.le α hα μ hμ
      (fun η ξ => fkMeasure_singleton_pos B hq hp₀ hp₁ α η ξ)
      (P := fun ω => ω ∉ A ∩ forcedPattern j)
      (hA.inter (measurable_forcedPattern j)).compl hnull
  have hcondzero : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      (B.conditionalLaw hq hp₁.le α η : Measure (Configuration E)) A = 0 := by
    filter_upwards [hAvoid] with η hη
    change (Measure.map (fun ξ : B.Interior => B.glue (η, ξ))
      (B.graph.fkMeasure hq hp₁.le (α η))) A = 0
    rw [Measure.map_apply (B.measurable_glue_const_left η) hA]
    have hempty : (fun ξ : B.Interior => B.glue (η, ξ)) ⁻¹' A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hξ
      let ξ' : B.Interior := fun e =>
        if he : (e : E) ∈ j.1 then j.2 ⟨(e : E), he⟩ else ξ e
      have hglue : B.glue (η, ξ') =
          Function.updateFinset (B.glue (η, ξ)) j.1 j.2 :=
        glue_forceInterior B j hj η ξ
      have hupdA : Function.updateFinset (B.glue (η, ξ)) j.1 j.2 ∈ A := by
        have heq : (B.glue (η, ξ) ∈ A) =
            (Function.updateFinset (B.glue (η, ξ)) j.1 j.2 ∈ A) :=
          hAdep (fun e he => by
            have he' : e ∉ j.1 := he
            simp [Function.updateFinset, he'])
        rw [← heq]
        exact hξ
      have hforced : Function.updateFinset (B.glue (η, ξ)) j.1 j.2 ∈
          forcedPattern j := updateFinset_mem_forcedPattern j _
      exact hη ξ' (hglue ▸ ⟨hupdA, hforced⟩)
    rw [hempty, measure_empty]
  have hmuA : (μ : Measure (Configuration E)) A = 0 := by
    rw [B.apply_of_isDLR hq hp₁.le α hα μ hμ hA]
    calc
      (∫⁻ η, (B.conditionalLaw hq hp₁.le α η : Measure (Configuration E)) A
          ∂(B.exteriorMeasure μ : Measure B.Exterior)) = ∫⁻ _η, 0
          ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
        apply lintegral_congr_ae
        filter_upwards [hcondzero] with η hη
        rw [hη]
      _ = 0 := by simp
  exact (ne_of_gt hApos) hmuA

/-- Every law satisfying the actual FK DLR equation on a finite-box
exhaustion has finite-pattern insertion tolerance at interior parameters. -/
theorem finitePatternInsertionTolerance_of_dlrMeasures {E : Type u}
    (exh : BoxExhaustion.{u, v} E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment exh.box)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp₁.le) :
    FinitePatternInsertionTolerance (μ : Measure (Configuration E)) := by
  intro j A hA hAdep hApos
  obtain ⟨n, hn⟩ := (exh.eventually_subset j.1).exists
  exact measure_pos_inter_forcedPattern_of_isDLR (exh.box n) hq hp₀ hp₁
    (Φ.partition n) (Φ.measurable_partition n) μ (hμ n) j hn A hA hAdep hApos

/-- Coherent-convention Gibbs form of
`finitePatternInsertionTolerance_of_dlrMeasures`. -/
theorem finitePatternInsertionTolerance_of_gibbsMeasures {E : Type u}
    (exh : BoxExhaustion.{u, v} E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ GibbsMeasures exh Φ) :
    FinitePatternInsertionTolerance (μ : Measure (Configuration E)) := by
  exact finitePatternInsertionTolerance_of_dlrMeasures exh hq hp₀ hp₁
    Φ.toBoundaryAssignment μ hμ

end

end FK.InsertionTolerance
