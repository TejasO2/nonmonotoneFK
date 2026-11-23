import FK.AGDifferential
import CurvatureVariance.Infra.Percolation.Critical

/-!
# Infinite-volume limits for finite-arm comparisons

This file isolates two limit statements used after the finite one-edge AG
calculation.  First, a finite-volume inequality passes to any specified
pointwise limits; no derivative limit is implied.  Second, on a connected,
locally finite graph the actual nested arm probabilities converge to the
actual percolation probability, by continuity from above.

The OR-enhanced joint product and its exact Bernoulli marginal are constructed
below without any finiteness assumption on the edge set.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology unitInterval

namespace FK.AGGadget

open CurvatureVariance.Infra.Percolation
open FK.Finite.Comparison FK.AGPeeling

universe u v

/-- A proved finite-arm comparison survives passage to arbitrary pointwise
limits.  The two limits are hypotheses, rather than an asserted interchange
of differentiation and infinite-volume limits. -/
theorem le_of_finite_arm_comparison
    {α : Type u} {τ : ℕ → α → ℝ} {θ : α → ℝ}
    (hlim : ∀ x, Tendsto (fun n => τ n x) atTop (𝓝 (θ x)))
    {a b : α} (hab : ∀ n, τ n a ≤ τ n b) : θ a ≤ θ b := by
  exact le_of_tendsto_of_tendsto (hlim a) (hlim b)
    (Filter.Eventually.of_forall hab)

/-- The arm probabilities of any probability law converge to the mass of the
actual infinite-cluster event. -/
theorem tendsto_measure_armEvent
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (o : V) (μ : Measure (G.edgeSet → Bool))
    [IsProbabilityMeasure μ] :
    Tendsto (fun n => μ (armEvent G o n)) atTop
      (𝓝 (μ {ω | {x | OpenConnected G ω Set.univ o x}.Infinite})) := by
  rw [setOf_infinite_eq_iInter_armEvent hG o]
  exact tendsto_measure_iInter_atTop
    (fun n => (measurableSet_armEvent o n).nullMeasurableSet)
    (armEvent_antitone o) ⟨0, measure_ne_top _ _⟩

/-- Continuity from above identifies the limit of the vendored normalized
Bernoulli arm probabilities with the vendored percolation probability. -/
theorem tendsto_armProb_percolationProb
    {V : Type u} (G : SimpleGraph V) [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (o : V) (p : unitInterval) :
    Tendsto (fun n => armProb G o p n) atTop
      (𝓝 (percolationProb G o p)) := by
  rw [percolationProb_eq]
  simp_rw [armProb_eq]
  exact tendsto_measure_armEvent hG o (percolation G p)

/-- The effective rate of `bond OR activation`, including both endpoints. -/
def orUnit (p s : unitInterval) : unitInterval :=
  ⟨orRate (p : ℝ) (s : ℝ), orRate_mem_Icc p.property s.property⟩

@[simp] lemma coe_orUnit (p s : unitInterval) :
    (orUnit p s : ℝ) = orRate (p : ℝ) (s : ℝ) := rfl

lemma measurable_jointPairedEquiv {E : Type u} :
    Measurable (jointPairedEquiv (E := E)) := by
  apply measurable_pi_iff.2
  intro e
  exact (measurable_pi_apply (Sum.inl e)).prodMk (measurable_pi_apply (Sum.inr e))

lemma measurable_jointPairedEquiv_symm {E : Type u} :
    Measurable (jointPairedEquiv (E := E)).symm := by
  apply measurable_pi_iff.2
  intro x
  cases x with
  | inl e => exact measurable_fst.comp (measurable_pi_apply e)
  | inr e => exact measurable_snd.comp (measurable_pi_apply e)

lemma measurable_enhancedConfig {E : Type u} :
    Measurable (enhancedConfig (E := E)) := by
  apply measurable_pi_iff.2
  intro e
  change Measurable (fun χ : JointConfig E E => χ (Sum.inl e) || χ (Sum.inr e))
  fun_prop

/-- Independent bond/activation pairs on an arbitrary edge index type. -/
noncomputable def infinitePairedLaw {E : Type u}
    (p s : unitInterval) : Measure (E → Bool × Bool) :=
  Measure.infinitePi fun _ : E =>
    (bernoulliMeasure true false p).prod (bernoulliMeasure true false s)

instance {E : Type u} (p s : unitInterval) :
    IsProbabilityMeasure (infinitePairedLaw (E := E) p s) := by
  unfold infinitePairedLaw
  infer_instance

/-- The independent joint bond/activation product on the same configuration
space as `AGDifferential`, now without a finite-edge hypothesis. -/
noncomputable def infiniteJointLaw {E : Type u}
    (p s : unitInterval) : Measure (JointConfig E E) :=
  (infinitePairedLaw p s).map (jointPairedEquiv (E := E)).symm

instance {E : Type u} (p s : unitInterval) :
    IsProbabilityMeasure (infiniteJointLaw (E := E) p s) where
  measure_univ := by
    rw [infiniteJointLaw, Measure.map_apply measurable_jointPairedEquiv_symm
      MeasurableSet.univ]
    simp

/-- One OR coordinate has exactly the normalized effective-rate Bernoulli
law. -/
theorem prod_bernoulliMeasure_map_or (p s : unitInterval) :
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false s)).map
      (fun x : Bool × Bool => x.1 || x.2) =
        bernoulliMeasure true false (orUnit p s) := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)]
  cases b with
  | false =>
      have hpre : (fun x : Bool × Bool => x.1 || x.2) ⁻¹' {false} =
          {false} ×ˢ {false} := by
        ext x
        rcases x with ⟨a, b⟩
        cases a <;> cases b <;> simp
      rw [hpre, Measure.prod_prod, bernoulliMeasure_false,
        bernoulliMeasure_false, bernoulliMeasure_false]
      simp only [coe_orUnit, orRate]
      rw [← ENNReal.ofReal_mul (sub_nonneg.mpr p.property.2)]
      congr 1
      ring
  | true =>
      have hpre : (fun x : Bool × Bool => x.1 || x.2) ⁻¹' {true} =
          ({true} ×ˢ Set.univ) ∪ ({false} ×ˢ {true}) := by
        ext x
        rcases x with ⟨a, b⟩
        cases a <;> cases b <;> simp
      have hdisj : Disjoint ({true} ×ˢ (Set.univ : Set Bool))
          ({false} ×ˢ {true}) := by
        simp [Set.disjoint_left]
      rw [hpre, measure_union hdisj (by measurability), Measure.prod_prod,
        Measure.prod_prod, bernoulliMeasure_true, bernoulliMeasure_false,
        bernoulliMeasure_true, bernoulliMeasure_true, measure_univ, mul_one]
      simp only [coe_orUnit, orRate]
      rw [ENNReal.ofReal_add p.property.1
        (mul_nonneg (sub_nonneg.mpr p.property.2) s.property.1),
        ENNReal.ofReal_mul (sub_nonneg.mpr p.property.2)]

/-- The enhanced marginal of the actual infinite independent joint law is
exactly Bernoulli percolation at `orUnit p s`. -/
theorem infiniteJointLaw_map_enhancedConfig {E : Type u}
    (p s : unitInterval) :
    (infiniteJointLaw (E := E) p s).map enhancedConfig =
      bernoulliProduct E (orUnit p s) := by
  rw [infiniteJointLaw, Measure.map_map measurable_enhancedConfig
    measurable_jointPairedEquiv_symm]
  change (infinitePairedLaw (E := E) p s).map
    (fun (ω : E → Bool × Bool) e => (ω e).1 || (ω e).2) = _
  unfold infinitePairedLaw
  refine (Measure.infinitePi_map_pi
    (fun _ : E => (bernoulliMeasure true false p).prod (bernoulliMeasure true false s))
    (f := fun _ (x : Bool × Bool) => x.1 || x.2) (fun _ => by fun_prop)).trans ?_
  unfold bernoulliProduct
  congr 1
  funext e
  exact prod_bernoulliMeasure_map_or p s

/-- Enhanced finite-arm probabilities are the original normalized Bernoulli
arm probabilities at the exact effective rate. -/
theorem infiniteJointLaw_enhancedArmEvent
    {V : Type u} (G : SimpleGraph V) [Countable V] (o : V) (n : ℕ)
    (p s : unitInterval) :
    infiniteJointLaw p s (enhancedArmEvent G o n) =
      armProb G o (orUnit p s) n := by
  rw [armProb_eq]
  change infiniteJointLaw p s (enhancedConfig ⁻¹' armEvent G o n) = _
  rw [← Measure.map_apply measurable_enhancedConfig (measurableSet_armEvent o n),
    infiniteJointLaw_map_enhancedConfig]

/-- The enhanced joint mass of the actual infinite-cluster event is exactly
the original percolation probability at the effective OR rate. -/
theorem infiniteJointLaw_enhancedPercolationEvent
    {V : Type u} (G : SimpleGraph V) [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (o : V) (p s : unitInterval) :
    infiniteJointLaw p s (enhancedConfig ⁻¹'
      {ω | {x | OpenConnected G ω Set.univ o x}.Infinite}) =
        percolationProb G o (orUnit p s) := by
  have hm : MeasurableSet {ω : G.edgeSet → Bool |
      {x | OpenConnected G ω Set.univ o x}.Infinite} := by
    rw [setOf_infinite_eq_iInter_armEvent hG o]
    exact MeasurableSet.iInter fun n => measurableSet_armEvent o n
  rw [percolationProb_eq, ← Measure.map_apply measurable_enhancedConfig hm,
    infiniteJointLaw_map_enhancedConfig]

/-- **Infinite-arm limit for the one-edge enhancement.**  No interchange of
derivatives with a limit is used: the actual nested enhanced arm probabilities
are identified exactly and continuity from above is applied to Bernoulli
percolation at `orUnit p s`. -/
theorem tendsto_enhancedArmEvent_percolationProb
    {V : Type u} (G : SimpleGraph V) [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (o : V) (p s : unitInterval) :
    Tendsto (fun n => infiniteJointLaw p s (enhancedArmEvent G o n)) atTop
      (𝓝 (percolationProb G o (orUnit p s))) := by
  simp_rw [infiniteJointLaw_enhancedArmEvent G o]
  exact tendsto_armProb_percolationProb G hG o (orUnit p s)

end FK.AGGadget
