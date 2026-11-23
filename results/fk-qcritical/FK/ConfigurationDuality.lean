import Mathlib

/-!
# Complementation duality and stochastic domination

The main theorem is measure-theoretic and does not require finiteness: pushing
probability measures forward by a measurable order-anti-isomorphism reverses
stochastic domination.  We then specialize to open/closed dual configurations
on `E → Bool`, with an arbitrary primal/dual edge bijection.
-/

namespace FK.Configuration

open MeasureTheory Set

/-- An event is increasing when it is closed upwards in the pointwise order. -/
def IsIncreasing {Ω : Type*} [LE Ω] (A : Set Ω) : Prop :=
  ∀ ⦃ω η : Ω⦄, ω ≤ η → ω ∈ A → η ∈ A

/-- Stochastic domination, using exactly the increasing-event formulation in
Section 1 of the paper. -/
def StochDom {Ω : Type*} [LE Ω] [MeasurableSpace Ω]
    (μ ν : Measure Ω) : Prop :=
  ∀ A : Set Ω, MeasurableSet A → IsIncreasing A → μ A ≤ ν A

/-- If `d` reverses the order, the complement of the pullback of an increasing
event is increasing. -/
lemma isIncreasing_compl_preimage {Ω Ω' : Type*} [LE Ω] [LE Ω']
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (d : Ω ≃ᵐ Ω') (hd : ∀ ω η, d ω ≤ d η ↔ η ≤ ω)
    (A : Set Ω') (hA : IsIncreasing A) :
    IsIncreasing (d ⁻¹' A)ᶜ := by
  intro ω η hωη hω
  simp only [mem_compl_iff, mem_preimage] at hω ⊢
  intro hη
  exact hω (hA ((hd η ω).2 hωη) hη)

/-- Pushforward by a measurable order anti-isomorphism reverses stochastic
domination.  In the application, `μ ≼ ν` on the primal graph becomes
`dual ν ≼ dual μ` on the dual graph. -/
lemma stochDom_map_reverse {Ω Ω' : Type*} [LE Ω] [LE Ω']
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (d : Ω ≃ᵐ Ω') (hd : ∀ ω η, d ω ≤ d η ↔ η ≤ ω)
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : StochDom μ ν) :
    StochDom (Measure.map d ν) (Measure.map d μ) := by
  intro A hAmeas hAinc
  have hD : MeasurableSet (d ⁻¹' A) := d.measurable hAmeas
  have hB : MeasurableSet (d ⁻¹' A)ᶜ := hD.compl
  have hBinc : IsIncreasing (d ⁻¹' A)ᶜ :=
    isIncreasing_compl_preimage d hd A hAinc
  have hcomp : μ (d ⁻¹' A)ᶜ ≤ ν (d ⁻¹' A)ᶜ := h _ hB hBinc
  have hμcompl : μ (d ⁻¹' A)ᶜ = 1 - μ (d ⁻¹' A) := by
    rw [measure_compl hD (measure_ne_top μ _), IsProbabilityMeasure.measure_univ]
  have hνcompl : ν (d ⁻¹' A)ᶜ = 1 - ν (d ⁻¹' A) := by
    rw [measure_compl hD (measure_ne_top ν _), IsProbabilityMeasure.measure_univ]
  have hμle : μ (d ⁻¹' A) ≤ 1 := by
    calc
      μ (d ⁻¹' A) ≤ μ univ := measure_mono (subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ
  have hνle : ν (d ⁻¹' A) ≤ 1 := by
    calc
      ν (d ⁻¹' A) ≤ ν univ := measure_mono (subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ
  rw [d.map_apply, d.map_apply]
  calc
    ν (d ⁻¹' A) = 1 - (1 - ν (d ⁻¹' A)) := (ENNReal.sub_sub_cancel (by simp) hνle).symm
    _ = 1 - ν (d ⁻¹' A)ᶜ := by rw [hνcompl]
    _ ≤ 1 - μ (d ⁻¹' A)ᶜ := tsub_le_tsub_left hcomp 1
    _ = 1 - (1 - μ (d ⁻¹' A)) := by rw [hμcompl]
    _ = μ (d ⁻¹' A) := ENNReal.sub_sub_cancel (by simp) hμle

/-- Open dual edges are precisely closed primal edges, transported along the
canonical edge bijection. -/
def dualConfig {E E' : Type*} (e : E ≃ E') (ω : E → Bool) : E' → Bool :=
  fun f => !(ω (e.symm f))

/-- The plain equivalence underlying dual configurations. -/
def dualEquiv {E E' : Type*} (e : E ≃ E') : (E → Bool) ≃ (E' → Bool) where
  toFun := dualConfig e
  invFun := dualConfig e.symm
  left_inv ω := by
    funext x
    simp [dualConfig]
  right_inv ω := by
    funext x
    simp [dualConfig]

/-- Dualization is measurable for the product Borel spaces, including infinite
edge sets. -/
def dualMeasurableEquiv {E E' : Type*} (e : E ≃ E') :
    (E → Bool) ≃ᵐ (E' → Bool) where
  toEquiv := dualEquiv e
  measurable_toFun := by
    change Measurable (dualConfig e)
    apply measurable_pi_lambda
    intro f
    change Measurable (fun ω : E → Bool => !(ω (e.symm f)))
    fun_prop
  measurable_invFun := by
    change Measurable (dualConfig e.symm)
    apply measurable_pi_lambda
    intro x
    change Measurable (fun ω : E' → Bool => !(ω (e x)))
    fun_prop

@[simp] lemma dualMeasurableEquiv_apply {E E' : Type*} (e : E ≃ E')
    (ω : E → Bool) : dualMeasurableEquiv e ω = dualConfig e ω := rfl

@[simp] lemma dualConfig_dualConfig {E E' : Type*} (e : E ≃ E')
    (ω : E → Bool) : dualConfig e.symm (dualConfig e ω) = ω := by
  funext x
  simp [dualConfig]

lemma bool_not_le_not_iff (a b : Bool) : (Bool.not a ≤ Bool.not b) ↔ b ≤ a := by
  cases a <;> cases b <;> decide

/-- Dualization exactly reverses the pointwise open-edge order. -/
lemma dual_le_dual_iff {E E' : Type*} (e : E ≃ E') (ω η : E → Bool) :
    dualConfig e ω ≤ dualConfig e η ↔ η ≤ ω := by
  constructor
  · intro h
    apply Pi.le_def.mpr
    intro x
    have hx := (Pi.le_def.mp h) (e x)
    have hx' := (bool_not_le_not_iff _ _).1 hx
    simpa [dualConfig] using hx'
  · intro h
    rw [Pi.le_def] at h ⊢
    intro f
    apply (bool_not_le_not_iff _ _).2
    exact h (e.symm f)

/-- The Section 5.2 reversal of stochastic domination for complemented
open-edge configurations. -/
theorem stochDom_dual {E E' : Type*} (e : E ≃ E')
    (μ ν : Measure (E → Bool)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : StochDom μ ν) :
    StochDom (Measure.map (dualMeasurableEquiv e) ν)
      (Measure.map (dualMeasurableEquiv e) μ) := by
  apply stochDom_map_reverse (dualMeasurableEquiv e) _ μ ν h
  intro ω η
  exact dual_le_dual_iff e ω η

end FK.Configuration
