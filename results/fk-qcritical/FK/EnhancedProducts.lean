import FK.CanonicalDynamics
import FK.EssentialWindow

/-! Exact Boolean measure adapters and coordinatewise monotonicity for the
finite enhanced products used in the path comparisons. -/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal unitInterval Classical BigOperators
open OpenPath

noncomputable section

/-- The real-mass Boolean Bernoulli law is the same measure as
`bernoulliMeasure true false`. -/
lemma boolLaw_toPMF_toMeasure {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (Glauber.FKBridge.boolLaw r hr).toPMF.toMeasure =
      bernoulliMeasure true false ⟨r, hr.1, hr.2⟩ := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (by simp)]
  cases b <;>
    simp [bernoulliMeasure_def, OpenPath.FinProb.toPMF_apply,
      Glauber.FKBridge.boolLaw, unitInterval.coe_symm_eq,
      ENNReal.ofReal_sub _ hr.1]
  · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hr.1,
      ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr hr.2)]
    rfl
  · rw [ENNReal.ofReal_eq_coe_nnreal hr.1]
    rfl

/-- The Bit-to-Bool path product is exactly the finite Bernoulli product used
by the DLR box transport. -/
theorem productLaw_map_configToBool_toMeasure {E : Type*} [Fintype E] [DecidableEq E]
    (r : E → ℝ) (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1) :
    (((productLaw r hr).map configToBool).toPMF.toMeasure) =
      FKEnhancement.bernoulliProduct (FKLimit.unitParameters r
        (fun e => (hr e).1) (fun e => (hr e).2)) := by
  change (((FinProb.pi (fun e => bitLaw (r e) (hr e))).map
    (fun x i => bitToBool (x i))).toPMF.toMeasure) = _
  rw [FinProb.pi_map]
  have hbit : (fun e => (bitLaw (r e) (hr e)).map bitToBool) =
      (fun e => Glauber.FKBridge.boolLaw (r e) (hr e)) := by
    funext e
    exact LowerPathCoupling.bitLaw_map_bitToBool (hr e)
  rw [hbit]
  calc
    (FinProb.pi (fun e => Glauber.FKBridge.boolLaw (r e) (hr e))).toPMF.toMeasure =
        Measure.pi (fun e => (Glauber.FKBridge.boolLaw (r e) (hr e)).toPMF.toMeasure) :=
      FinProb.toPMF_pi_toMeasure _
    _ = FKEnhancement.bernoulliProduct (FKLimit.unitParameters r
        (fun e => (hr e).1) (fun e => (hr e).2)) := by
      unfold FKEnhancement.bernoulliProduct
      congr 1
      funext e
      exact boolLaw_toPMF_toMeasure (hr e)

/-- Exact Boolean-measure form of the lower open-path product. -/
theorem lowerProductPMF_map_configToBool_toMeasure
    {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (h : p' ≤ p) (Γ : E → Set (Finset E)) :
    ((lowerProductPMF enhanced hp1 hp' h Γ).map configToBool).toMeasure =
      FKEnhancement.bernoulliProduct (FKLimit.unitParameters
        (lowerProductParameters enhanced p p' hp' Γ)
        (fun e => (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ e).1)
        (fun e => (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ e).2)) := by
  rw [lowerProductPMF, lowerProductLaw, ← FinProb.toPMF_map]
  exact productLaw_map_configToBool_toMeasure _ _

/-- Exact Boolean-measure form of the upper open-path product. -/
theorem upperProductPMF_map_configToBool_toMeasure
    {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (Γ : E → Set (Finset E)) :
    ((upperProductPMF enhanced hp hp'1 h Γ).map configToBool).toMeasure =
      FKEnhancement.bernoulliProduct (FKLimit.unitParameters
        (upperProductParameters enhanced p p' hp Γ)
        (fun e => (upperProductParameters_mem_Icc enhanced hp hp'1 h Γ e).1)
        (fun e => (upperProductParameters_mem_Icc enhanced hp hp'1 h Γ e).2)) := by
  rw [upperProductPMF, upperProductLaw, ← FinProb.toPMF_map]
  exact productLaw_map_configToBool_toMeasure _ _

/-- Larger finite Boolean Bernoulli parameters give the larger product law on
all increasing events. -/
theorem finite_bernoulliProduct_mono {E : Type*} [Fintype E]
    {r s : E → unitInterval} (hrs : r ≤ s) :
    FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct r) (FKEnhancement.bernoulliProduct s) := by
  intro A _ hA
  have h' := FK.EssentialWindow.measure_le_of_stochasticallyDominates
    (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hrs)
    (A := A) (MeasurableSet.of_discrete : MeasurableSet A) hA
  have heq : ∀ t : E → unitInterval,
      (FKLimit.bernoulliProduct t : Measure (E → Bool)) =
        FKEnhancement.bernoulliProduct t := by
    intro t
    change Measure.infinitePi (fun e => bernoulliMeasure true false (t e)) =
      Measure.pi (fun e => bernoulliMeasure true false (t e))
    rw [Measure.infinitePi_eq_pi]
  rw [heq r, heq s] at h'
  exact h'

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.boolLaw_toPMF_toMeasure
#print axioms FK.EnhancedTransport.productLaw_map_configToBool_toMeasure
#print axioms FK.EnhancedTransport.finite_bernoulliProduct_mono
#print axioms FK.EnhancedTransport.lowerProductPMF_map_configToBool_toMeasure
#print axioms FK.EnhancedTransport.upperProductPMF_map_configToBool_toMeasure
