import FK.MovingDominatedRate

/-! One-edge conditionals of an already-DLR law, with arbitrary exterior data. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace FK.InfiniteVolume.MovingClopenRate

noncomputable section


local instance boundaryPartitionMeasurableSpaceDLROnePoint (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

attribute [local instance] classicalDecEqInstance'

variable {E : Type*} [Countable E]

namespace FiniteBox

variable (B : FiniteBox E)

/-- Exterior/interior measurability of the open rate.  The finite off-edge
configuration is handled by a finite partition into singleton fibres. -/
lemma measurable_openRate_off {q p : NNReal}
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α) (e : B.edges) :
    Measurable (fun z : B.Exterior × Glauber.OffConfig Bool B.edges e =>
      Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α z.1) e z.2) := by
  classical
  let F : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ :=
    fun z => ∑ o : Glauber.OffConfig Bool B.edges e,
      {w | w.2 = o}.indicator
        (fun z => Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α z.1) e o) z
  have hF : Measurable F := by
    apply Finset.measurable_sum
    intro o _ho
    exact ((FK.InfiniteVolume.FiniteBox.measurable_openRate B α hα e o).comp measurable_fst).indicator
      ((measurableSet_singleton o).preimage measurable_snd)
  have hEq : (fun z : B.Exterior × Glauber.OffConfig Bool B.edges e =>
      Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α z.1) e z.2) = F := by
    funext z
    simp only [F]
    rw [Finset.sum_eq_single z.2]
    · simp
    · intro o _ho hoz
      have hz : z.2 ≠ o := Ne.symm hoz
      simp [Set.indicator, hz]
    · intro h
      simp at h
  rw [hEq]
  exact hF

/-- The conditional FK law has the exact one-point identities at every exterior
configuration, not only at the canonical closed exterior. -/
theorem conditionalLaw_hasOnePointConditionalsBif {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (α : B.Exterior → B.BoundaryPartition)
    (hα : Measurable α) (η₀ : B.Exterior) :
    B.HasOnePointConditionalsBif (q := q) (p := p) α
      (B.conditionalLaw hq hp₁.le α η₀) := by
  classical
  intro e g hg
  letI : DecidableEq B.edges := classicalDecEqInstance' _
  set ν : Measure B.Interior := B.graph.fkMeasure hq hp₁.le (α η₀) with hν
  haveI : IsProbabilityMeasure ν := by
    rw [hν]
    exact FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp₁.le (α η₀)
  have hglue : ∀ ξ : B.Interior, B.splitEquiv (B.glue (η₀, ξ)) = (η₀, ξ) := by
    intro ξ
    rw [FiniteBox.splitEquiv_apply]
    exact B.split_glue (η₀, ξ)
  have step : ∀ (H : Configuration E → ℝ≥0∞), Measurable H →
      ∫⁻ ω, H ω ∂((B.conditionalLaw hq hp₁.le α η₀) : Measure (Configuration E))
        = ∫⁻ ξ : B.Interior, H (B.glue (η₀, ξ)) ∂ν := by
    intro H hH
    rw [FiniteBox.conditionalLaw]
    exact MeasureTheory.lintegral_map hH (B.measurable_glue_const_left η₀)
  have hbit : ∀ ξ : B.Interior,
      B.splitBit e (B.glue (η₀, ξ)) = (Glauber.configSplit Bool e ξ).2 := by
    intro ξ
    rw [B.splitBit_apply, hglue]
  have hoff : ∀ ξ : B.Interior,
      B.splitOff e (B.glue (η₀, ξ)) = (η₀, (Glauber.configSplit Bool e ξ).1) := by
    intro ξ
    rw [B.splitOff_apply, hglue]
  have hmeas_if : Measurable (fun ω => (if B.splitBit e ω = true then g (B.splitOff e ω) else 0 :
      ℝ≥0∞)) :=
    Measurable.ite (B.measurable_splitBit e (measurableSet_singleton true))
      (hg.comp (B.measurable_splitOff e)) measurable_const
  have hmeas_rate : Measurable (fun ω => (ENNReal.ofReal (Glauber.FKBridge.openRate B.graph
      (q := q) (p := p) (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω) : ℝ≥0∞)) := by
    refine Measurable.mul ?_ (hg.comp (B.measurable_splitOff e))
    exact ENNReal.measurable_ofReal.comp
      ((measurable_openRate_off B α hα e).comp (B.measurable_splitOff e))
  have hleft : ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
      ∂((B.conditionalLaw hq hp₁.le α η₀) : Measure (Configuration E))
      = ∑ ξ : B.Interior,
          (if (Glauber.configSplit Bool e ξ).2 = true then g (η₀, (Glauber.configSplit Bool e ξ).1)
            else 0) * ν {ξ} := by
    rw [step _ hmeas_if, lintegral_fintype]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hbit, hoff]
  have hright : ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
      ∂((B.conditionalLaw hq hp₁.le α η₀) : Measure (Configuration E))
      = ∑ ξ : B.Interior,
          ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α η₀) e
            (Glauber.configSplit Bool e ξ).1) * g (η₀, (Glauber.configSplit Bool e ξ).1)
            * ν {ξ} := by
    rw [step _ hmeas_rate, lintegral_fintype]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hoff]
  rw [show ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
        ∂((B.conditionalLaw hq hp₁.le α η₀) : Measure (Configuration E))
      = ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
        ∂((B.conditionalLaw hq hp₁.le α η₀) : Measure (Configuration E)) from
    lintegral_congr fun ω => (FK.InfiniteVolume.FiniteBox.ite_bool_eq_bif _ _ _).symm]
  rw [hleft, hright]
  conv_lhs => rw [B.sum_interior_eq_sum_off e (F := fun ξ =>
      (if (Glauber.configSplit Bool e ξ).2 = true then g (η₀, (Glauber.configSplit Bool e ξ).1)
        else 0) * ν {ξ})]
  conv_rhs => rw [B.sum_interior_eq_sum_off e (F := fun ξ =>
      ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α η₀) e
        (Glauber.configSplit Bool e ξ).1) * g (η₀, (Glauber.configSplit Bool e ξ).1)
        * ν {ξ})]
  simp only [FK.InfiniteVolume.FiniteBox.configSplit_fibreConfig]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, zero_mul, add_zero]
  have h := B.fkMeasure_singleton_true_eq (q := q) (p := p) hq hp₁.le (α η₀) e o
  calc g (η₀, o) * ν {B.fibreConfig e o true}
      = g (η₀, o) * (ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (α η₀) e o) *
          (ν {B.fibreConfig e o true} + ν {B.fibreConfig e o false})) := by
        conv_lhs => rw [h]
    _ = ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α η₀) e o) *
          g (η₀, o) * (ν {B.fibreConfig e o true} + ν {B.fibreConfig e o false}) := by
        ring
    _ = ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α η₀) e o) *
          g (η₀, o) * ν {B.fibreConfig e o true} +
        ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) (α η₀) e o) *
          g (η₀, o) * ν {B.fibreConfig e o false} := by
        ring

/-- Every measurable global test integrates against the actual exterior/FK
fibre decomposition of a DLR law. -/
lemma lintegral_of_isDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    {H : Configuration E → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ ω, H ω ∂(μ : Measure (Configuration E))) =
      ∫⁻ η, ∫⁻ ξ : B.Interior, H (B.glue (η, ξ))
        ∂(B.graph.fkMeasure hq hp (α η)) ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  rw [B.measure_eq_map_glue_compProd hq hp α hα μ hμ,
    MeasureTheory.lintegral_map hH hg]
  exact Measure.lintegral_compProd (f := H ∘ B.glue) (hH.comp hg)

/-- A DLR law has the exact one-edge identities of its own specification. -/
theorem hasOnePointConditionalsBif_of_isDLR {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (α : B.Exterior → B.BoundaryPartition)
    (hα : Measurable α) (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp₁.le α hα μ) :
    B.HasOnePointConditionalsBif (q := q) (p := p) α μ := by
  intro e g hg
  have h1 := lintegral_of_isDLR B hq hp₁.le α hα μ hμ
    (H := fun ω => (bif B.splitBit e ω then g (B.splitOff e ω) else 0)) (by
      have hm : Measurable (fun ω => (if B.splitBit e ω = true then
          g (B.splitOff e ω) else 0 : ℝ≥0∞)) :=
        Measurable.ite (B.measurable_splitBit e (measurableSet_singleton true))
          (hg.comp (B.measurable_splitOff e)) measurable_const
      rw [show (fun ω => bif B.splitBit e ω then g (B.splitOff e ω) else 0) =
        (fun ω => if B.splitBit e ω = true then g (B.splitOff e ω) else 0) from
        funext fun ω => (FK.InfiniteVolume.FiniteBox.ite_bool_eq_bif _ _ _).symm]
      exact hm)
  have hrate : Measurable (fun ω => Glauber.FKBridge.openRate B.graph (q := q) (p := p)
      (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) :=
    (measurable_openRate_off B α hα e).comp (B.measurable_splitOff e)
  have h2 := lintegral_of_isDLR B hq hp₁.le α hα μ hμ
    (H := fun ω => ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)) (by
      exact (ENNReal.measurable_ofReal.comp hrate).mul (hg.comp (B.measurable_splitOff e)))
  rw [h1, h2]
  apply lintegral_congr
  intro η
  have h := conditionalLaw_hasOnePointConditionalsBif B hq hp₀ hp₁ α hα η e g hg
  have hm1 : Measurable (fun ω => (bif B.splitBit e ω then g (B.splitOff e ω) else 0 :
      ℝ≥0∞)) := by
    have hm : Measurable (fun ω => (if B.splitBit e ω = true then
        g (B.splitOff e ω) else 0 : ℝ≥0∞)) :=
      Measurable.ite (B.measurable_splitBit e (measurableSet_singleton true))
        (hg.comp (B.measurable_splitOff e)) measurable_const
    rw [show (fun ω => bif B.splitBit e ω then g (B.splitOff e ω) else 0) =
      (fun ω => if B.splitBit e ω = true then g (B.splitOff e ω) else 0) from
      funext fun ω => (FK.InfiniteVolume.FiniteBox.ite_bool_eq_bif _ _ _).symm]
    exact hm
  have hm2 : Measurable (fun ω => (ENNReal.ofReal (Glauber.FKBridge.openRate B.graph
      (q := q) (p := p) (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) *
        g (B.splitOff e ω) : ℝ≥0∞)) := by
    exact (ENNReal.measurable_ofReal.comp
      ((measurable_openRate_off B α hα e).comp (B.measurable_splitOff e))).mul
        (hg.comp (B.measurable_splitOff e))
  have hleft := MeasureTheory.lintegral_map (μ := B.graph.fkMeasure hq hp₁.le (α η)) hm1 (B.measurable_glue_const_left η)
  have hright := MeasureTheory.lintegral_map (μ := B.graph.fkMeasure hq hp₁.le (α η)) hm2 (B.measurable_glue_const_left η)
  rw [← hleft, ← hright]
  exact h

end FiniteBox

end

end FK.InfiniteVolume.MovingClopenRate

namespace FK.InfiniteVolume.MovingClopenRate.FiniteBox

local instance boundaryPartitionMeasurableSpaceDLRCorollary (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- Library (non-`bif`) form of the one-edge identities of a DLR law. -/
theorem hasOnePointConditionals_of_isDLR {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (α : B.Exterior → B.BoundaryPartition)
    (hα : Measurable α) (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp₁.le α hα μ) :
    B.HasOnePointConditionals (q := q) (p := p) α μ :=
  (B.hasOnePointConditionals_iff_bif α μ).mpr
    (hasOnePointConditionalsBif_of_isDLR B hq hp₀ hp₁ α hα μ hμ)

end FK.InfiniteVolume.MovingClopenRate.FiniteBox


namespace FK.InfiniteVolume.MovingClopenRate.FiniteBox

attribute [local instance] classicalDecEqInstance'

local instance boundaryPartitionMeasurableSpaceDLRTwoValued (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- The global off-edge event on which the specification's one-edge rate is the
connected rate. -/
def specificationConnectionEvent (α : B.Exterior → B.BoundaryPartition)
    (e : B.edges) : Set (Configuration E) :=
  {ω | FK.Finite.Conditional.endpointsConnectedWithout B.graph
    (α ((B.splitOff e ω).1)) e
    (Glauber.FKBridge.offConfiguration B.graph (α ((B.splitOff e ω).1)) e
      ((B.splitOff e ω).2))}

/-- Exact two-valued finite-stage identity of a DLR law. -/
theorem onePoint_twoValuedRate_of_isDLR {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (α : B.Exterior → B.BoundaryPartition)
    (hα : Measurable α) (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp₁.le α hα μ) (e : B.edges)
    (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
        ∂(μ : Measure (Configuration E)) =
      ∫⁻ ω, ENNReal.ofReal (OneEdgeNoEscape.twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
        (specificationConnectionEvent B α e) ω) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) := by
  have h := hasOnePointConditionalsBif_of_isDLR B hq hp₀ hp₁ α hα μ hμ e g hg
  have hrate : (fun ω : Configuration E => Glauber.FKBridge.openRate B.graph (q := q) (p := p)
      (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) =
      OneEdgeNoEscape.twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
        (specificationConnectionEvent B α e) := by
    simpa only [specificationConnectionEvent] using
      OneEdgeNoEscape.openRate_eq_twoValuedRate B e α
  have hpoint : ∀ ω, Glauber.FKBridge.openRate B.graph (q := q) (p := p)
      (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2) =
      OneEdgeNoEscape.twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
        (specificationConnectionEvent B α e) ω := congrFun hrate
  simp_rw [hpoint] at h
  exact h

end FK.InfiniteVolume.MovingClopenRate.FiniteBox
