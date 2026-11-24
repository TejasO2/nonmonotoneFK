import FK.FibreAssembly

/-!
# One-edge one-point conditionals through an infinite-volume weak limit

This file develops the fixed/finite-edge limiting step of the one-point
determination route to `FiniteBox.HasOnePointConditionals` (residual step 1 of
`docs/ONE-POINT-DETERMINATION.md`).

Contents:

* `finiteVolumeLaw_hasOnePointConditionals` : the finite-volume law of a box
  itself satisfies the box one-point conditional identity with its own constant
  boundary setoid.  This is the finite input at every stage of an exhaustion.
* `onePoint_le_of_antitone_rates` : the one-sided limit inequality.  If the
  finite laws satisfy the one-point identity with continuous rates `ρ k`
  decreasing pointwise to `ρ`, then the limit law satisfies the one-point
  *inequality* with rate `ρ`.
* `onePoint_of_scalar` : the exact scalar criterion.  Under the same hypotheses,
  the limit law satisfies the one-point *identity* with rate `ρ` as soon as the
  single scalar mass identity `μ(e open) = ∫ ρ dμ` holds.
* `hasOnePointConditionals_of_scalar` : the resulting
  `FiniteBox.HasOnePointConditionals`, hence `IsDLR` of the limit at that box.
* `le_liminf_measure_of_monotone_clopen` : only the automatic liminf half of
  the scalar mass identity follows from weak convergence.  The other limsup half
  — uniform no mass escape through increasingly distant connection events — and
  the geometric identification of the limiting rate remain genuine inputs.

Everything here is measure-theoretic; the intended applications are
`IsFKLimit` sequences of `finiteVolumeLaw`s.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

local instance (priority := 10000) classicalDecEqInstance' (α : Type*) : DecidableEq α :=
  Classical.decEq α

attribute [local instance] Classical.decEq

namespace FK.InfiniteVolume

local instance boundaryPartitionMeasurableSpaceOneEdge (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

namespace FiniteBox

variable {E : Type*} [Countable E]

/-! ## `bif`-normal form of the one-point conditionals -/

/-- `if b = true then x else 0` and `bif b then x else 0` agree for a Boolean
test.  This instance-robust rewriting avoids dependent `Decidable` mismatch. -/
lemma ite_bool_eq_bif {α : Type*} (b : Bool) (x z : α) [d : Decidable (b = true)] :
    (if b = true then x else z) = (bif b then x else z) := by
  cases d with
  | isTrue h =>
    rw [if_pos h, h]
    simp
  | isFalse h =>
    rw [if_neg h]
    cases b with
    | false => simp
    | true => exact absurd rfl h

variable (B : FiniteBox E)

/-- The `bif`-normal form of `B.HasOnePointConditionals`. -/
def HasOnePointConditionalsBif {q p : NNReal} (α : B.Exterior → B.BoundaryPartition)
    (μ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∀ (e : B.edges) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
    ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
        ∂(μ : Measure (Configuration E))
      = ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
            (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E))

/-- The `bif` form is the same condition as `HasOnePointConditionals`. -/
theorem hasOnePointConditionals_iff_bif {q p : NNReal}
    (α : B.Exterior → B.BoundaryPartition) (μ : ProbabilityMeasure (Configuration E)) :
    B.HasOnePointConditionals (q := q) (p := p) α μ ↔
      B.HasOnePointConditionalsBif (q := q) (p := p) α μ := by
  unfold HasOnePointConditionals HasOnePointConditionalsBif
  refine forall_congr' fun e => forall_congr' fun g => ?_
  constructor <;> intro h
  · intro hg
    have h' := h hg
    rw [← h']
    refine lintegral_congr fun ω => ?_
    exact (ite_bool_eq_bif _ _ _).symm
  · intro hg
    have h' := h hg
    rw [← h']
    refine lintegral_congr fun ω => ?_
    exact ite_bool_eq_bif _ _ _

/-! ## Part 1: the finite-volume law satisfies its own one-point conditionals -/

section FiniteVolumeLaw

/-- Regrouping a finite sum over interior configurations along the off-edge
split at one edge. -/
lemma sum_interior_eq_sum_off {M : Type*} [AddCommMonoid M] (e : B.edges)
    (F : B.Interior → M) :
    ∑ ξ : B.Interior, F ξ
      = ∑ o : Glauber.OffConfig Bool B.edges e, ∑ b : Bool, F (B.fibreConfig e o b) := by
  rw [← Equiv.sum_comp (Glauber.configSplit Bool e).symm F, Fintype.sum_prod_type]
  simp only [FiniteBox.fibreConfig]

/-- The equation-(2) two-valued per-off-edge mass identity of the finite
random-cluster law. -/
lemma fkMeasure_singleton_true_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.BoundaryPartition) (e : B.edges) (o : Glauber.OffConfig Bool B.edges e) :
    B.graph.fkMeasure hq hp β {B.fibreConfig e o true}
      = ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e o) *
        (B.graph.fkMeasure hq hp β {B.fibreConfig e o true} +
          B.graph.fkMeasure hq hp β {B.fibreConfig e o false}) := by
  have h := FKF.fkMeasure_singleton_odds (G := B.graph) (q := q) (p := p) hq hp β e o
  simpa only [FiniteBox.fibreConfig] using h

/-- **Finite stage.**  The finite-volume law of a box has the box's own
equation-(2) one-point conditional probabilities for its constant boundary
setoid (in `bif` normal form). -/
theorem finiteVolumeLaw_hasOnePointConditionalsBif {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (β : B.BoundaryPartition) :
    B.HasOnePointConditionalsBif (q := q) (p := p) (fun _ => β)
      (B.finiteVolumeLaw hq hp₁.le β) := by
  classical
  intro e g hg
  set η₀ : B.Exterior := B.closedExterior with hη
  set ν : Measure B.Interior := B.graph.fkMeasure hq hp₁.le β with hν
  haveI : IsProbabilityMeasure ν := by
    rw [hν]
    exact FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp₁.le β
  have hglue : ∀ ξ : B.Interior, B.splitEquiv (B.glue (η₀, ξ)) = (η₀, ξ) := by
    intro ξ
    rw [FiniteBox.splitEquiv_apply]
    exact B.split_glue (η₀, ξ)
  have step : ∀ (H : Configuration E → ℝ≥0∞), Measurable H →
      ∫⁻ ω, H ω ∂((B.finiteVolumeLaw hq hp₁.le β) : Measure (Configuration E))
        = ∫⁻ ξ : B.Interior, H (B.glue (η₀, ξ)) ∂ν := by
    intro H hH
    rw [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw]
    exact MeasureTheory.lintegral_map hH (B.measurable_glue_const_left η₀)
  have hbit : ∀ ξ : B.Interior,
      B.splitBit e (B.glue (η₀, ξ)) = (Glauber.configSplit Bool e ξ).2 := by
    intro ξ
    rw [B.splitBit_apply, hglue]
  have hoff : ∀ ξ : B.Interior,
      B.splitOff e (B.glue (η₀, ξ)) = (η₀, (Glauber.configSplit Bool e ξ).1) := by
    intro ξ
    rw [B.splitOff_apply, hglue]
  -- the two global integrands, pushed to the finite interior
  have hmeas_if : Measurable (fun ω => (if B.splitBit e ω = true then g (B.splitOff e ω) else 0 :
      ℝ≥0∞)) :=
    Measurable.ite (B.measurable_splitBit e (measurableSet_singleton true))
      (hg.comp (B.measurable_splitOff e)) measurable_const
  have hmeas_rate : Measurable (fun ω => (ENNReal.ofReal (Glauber.FKBridge.openRate B.graph
      (q := q) (p := p) (β) e ((B.splitOff e ω).2)) * g (B.splitOff e ω) : ℝ≥0∞)) := by
    refine Measurable.mul ?_ (hg.comp (B.measurable_splitOff e))
    exact ENNReal.measurable_ofReal.comp
      ((FKF.measurable_of_fintype_domain
        (fun o : Glauber.OffConfig Bool B.edges e =>
          Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e o)).comp
        (measurable_snd.comp (B.measurable_splitOff e)))
  have hleft : ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
      ∂((B.finiteVolumeLaw hq hp₁.le β) : Measure (Configuration E))
      = ∑ ξ : B.Interior,
          (if (Glauber.configSplit Bool e ξ).2 = true then g (η₀, (Glauber.configSplit Bool e ξ).1)
            else 0) * ν {ξ} := by
    rw [step _ hmeas_if, lintegral_fintype]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hbit, hoff]
  have hright : ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (β) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
      ∂((B.finiteVolumeLaw hq hp₁.le β) : Measure (Configuration E))
      = ∑ ξ : B.Interior,
          ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e
            (Glauber.configSplit Bool e ξ).1) * g (η₀, (Glauber.configSplit Bool e ξ).1)
            * ν {ξ} := by
    rw [step _ hmeas_rate, lintegral_fintype]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hoff]
  rw [show ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
        ∂((B.finiteVolumeLaw hq hp₁.le β) : Measure (Configuration E))
      = ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
        ∂((B.finiteVolumeLaw hq hp₁.le β) : Measure (Configuration E)) from
    lintegral_congr fun ω => (ite_bool_eq_bif _ _ _).symm]
  rw [hleft, hright]
  -- regroup both finite sums along the off-edge split
  rw [B.sum_interior_eq_sum_off e (F := fun ξ =>
      (if (Glauber.configSplit Bool e ξ).2 = true then g (η₀, (Glauber.configSplit Bool e ξ).1)
        else 0) * ν {ξ}),
    B.sum_interior_eq_sum_off e (F := fun ξ =>
      ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e
        (Glauber.configSplit Bool e ξ).1) * g (η₀, (Glauber.configSplit Bool e ξ).1)
        * ν {ξ})]
  simp only [configSplit_fibreConfig]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, zero_mul, add_zero]
  have h := B.fkMeasure_singleton_true_eq (q := q) (p := p) hq hp₁.le β e o
  calc g (η₀, o) * ν {B.fibreConfig e o true}
      = g (η₀, o) * (ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e o) *
          (ν {B.fibreConfig e o true} + ν {B.fibreConfig e o false})) := by
        conv_lhs => rw [h]
    _ = ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e o) *
          g (η₀, o) * (ν {B.fibreConfig e o true} + ν {B.fibreConfig e o false}) := by
        ring
    _ = ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e o) *
          g (η₀, o) * ν {B.fibreConfig e o true} +
        ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p) β e o) *
          g (η₀, o) * ν {B.fibreConfig e o false} := by
        ring

/-- **Finite stage**, library form. -/
theorem finiteVolumeLaw_hasOnePointConditionals {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (β : B.BoundaryPartition) :
    B.HasOnePointConditionals (q := q) (p := p) (fun _ => β)
      (B.finiteVolumeLaw hq hp₁.le β) :=
  (B.hasOnePointConditionals_iff_bif (fun _ => β) _).mpr
    (B.finiteVolumeLaw_hasOnePointConditionalsBif hq hp₀ hp₁ β)

end FiniteVolumeLaw

/-! ## Part 2: continuous test functions of the off-edge box data -/

section Transfer

variable (B : FiniteBox E) (e : B.edges)

lemma continuous_split' : Continuous B.split := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun a => continuous_apply a.1
  · exact continuous_pi fun f => continuous_apply f.1

lemma continuous_splitEquiv : Continuous (B.splitEquiv : Configuration E → B.Exterior × B.Interior) := by
  have h : (B.splitEquiv : Configuration E → B.Exterior × B.Interior) = B.split := by
    funext ω
    exact B.splitEquiv_apply ω
  rw [h]
  exact continuous_split' B

lemma continuous_splitBit : Continuous (B.splitBit e) := by
  have h1 : Continuous fun ω : Configuration E => (B.splitEquiv ω).2 :=
    continuous_snd.comp (continuous_splitEquiv B)
  have h2 : Continuous fun ξ : B.Interior => (Glauber.configSplit Bool e ξ).2 := by
    simpa only [Glauber.configSplit_apply_snd] using
      (continuous_apply e : Continuous fun ξ : B.Interior => ξ e)
  exact h2.comp h1

lemma continuous_splitOff : Continuous (B.splitOff e) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_fst.comp (continuous_splitEquiv B)
  · have h2 : Continuous fun ξ : B.Interior => (Glauber.configSplit Bool e ξ).1 := by
      refine continuous_pi fun f => ?_
      simpa only [Glauber.configSplit_apply_fst] using
        (continuous_apply f.1 : Continuous fun ξ : B.Interior => ξ f.1)
    exact h2.comp (continuous_snd.comp (continuous_splitEquiv B))

/-- A bounded continuous real function of the off-edge box data, read as a
function of the global configuration. -/
def offTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (ω : Configuration E) : ℝ :=
  φ (B.splitOff e ω)

lemma continuous_offTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) :
    Continuous (offTest B e φ) :=
  φ.continuous.comp (continuous_splitOff B e)

lemma measurable_offTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) :
    Measurable (offTest B e φ) :=
  (continuous_offTest B e φ).measurable

lemma norm_offTest_le (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (ω : Configuration E) :
    ‖offTest B e φ ω‖ ≤ ‖φ‖ :=
  φ.norm_coe_le_norm (B.splitOff e ω)

lemma offTest_le_norm (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (hφ : ∀ y, 0 ≤ φ y)
    (ω : Configuration E) : offTest B e φ ω ≤ ‖φ‖ := by
  have h := norm_offTest_le B e φ ω
  rw [Real.norm_eq_abs] at h
  exact le_trans (le_abs_self _) h


/-- The indicator of the open bit at `e`, as a real-valued test function. -/
def openBitTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (ω : Configuration E) : ℝ :=
  if B.splitBit e ω = true then offTest B e φ ω else 0

lemma openBitTest_eq_mul (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) :
    openBitTest B e φ =
      fun ω => (if B.splitBit e ω = true then (1 : ℝ) else 0) * offTest B e φ ω := by
  funext ω
  by_cases h : B.splitBit e ω = true
  · rw [openBitTest, if_pos h, if_pos h, one_mul]
  · rw [openBitTest, if_neg h, if_neg h, zero_mul]

lemma continuous_openBitFactor :
    Continuous fun ω : Configuration E => (if B.splitBit e ω = true then (1 : ℝ) else 0) := by
  show Continuous ((fun b : Bool => if b = true then (1 : ℝ) else 0) ∘ B.splitBit e)
  exact continuous_of_discreteTopology.comp (continuous_splitBit B e)

lemma continuous_openBitTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) :
    Continuous (openBitTest B e φ) := by
  rw [openBitTest_eq_mul]
  exact (continuous_openBitFactor B e).mul (continuous_offTest B e φ)

lemma measurable_openBitTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) :
    Measurable (openBitTest B e φ) :=
  (continuous_openBitTest B e φ).measurable

lemma norm_openBitTest_le (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (ω : Configuration E) :
    ‖openBitTest B e φ ω‖ ≤ ‖φ‖ := by
  by_cases h : B.splitBit e ω = true
  · rw [openBitTest, if_pos h]; exact norm_offTest_le B e φ ω
  · rw [openBitTest, if_neg h, norm_zero]; positivity

lemma integrable_openBitTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (ν : Measure (Configuration E)) [IsFiniteMeasure ν] :
    Integrable (openBitTest B e φ) ν :=
  Integrable.of_bound (measurable_openBitTest B e φ).aestronglyMeasurable ‖φ‖
    (Filter.Eventually.of_forall (norm_openBitTest_le B e φ))

lemma integrable_offTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (ν : Measure (Configuration E)) [IsFiniteMeasure ν] :
    Integrable (offTest B e φ) ν :=
  Integrable.of_bound (measurable_offTest B e φ).aestronglyMeasurable ‖φ‖
    (Filter.Eventually.of_forall (norm_offTest_le B e φ))

/-- The rate-weighted off-edge test is integrable against any finite measure when
the rate takes values in `[0,1]`. -/
lemma integrable_rate_mul (c : Configuration E → ℝ) (hc0 : ∀ ω, 0 ≤ c ω)
    (hc1 : ∀ ω, c ω ≤ 1) (hcmeas : Measurable c)
    (φ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (hφ : ∀ y, 0 ≤ φ y) (ν : Measure (Configuration E)) [IsFiniteMeasure ν] :
    Integrable (fun ω => c ω * offTest B e φ ω) ν := by
  refine Integrable.of_bound (hcmeas.mul (measurable_offTest B e φ)).aestronglyMeasurable ‖φ‖ ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ c ω * offTest B e φ ω from mul_nonneg (hc0 ω) (hφ _))]
  calc c ω * offTest B e φ ω ≤ 1 * ‖φ‖ :=
        mul_le_mul (hc1 ω) (offTest_le_norm B e φ hφ ω) (hφ _) zero_le_one
    _ = ‖φ‖ := one_mul _

/-! ## Part 3: from the finite stages to the limit -/

section LimitTransfer

variable (B : FiniteBox E) (e : B.edges)

/-- `ofReal` of the finite-stage open-bit integral is the corresponding
Lebesgue integral (with the `if`-form indicator). -/
lemma ofReal_integral_openBitTest (φ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (hφ : ∀ y, 0 ≤ φ y)
    (ν : Measure (Configuration E)) [IsFiniteMeasure ν] :
    ENNReal.ofReal (∫ ω, openBitTest B e φ ω ∂ν)
      = ∫⁻ ω, (if B.splitBit e ω = true then ENNReal.ofReal (φ (B.splitOff e ω)) else 0) ∂ν := by
  haveI := ‹IsFiniteMeasure ν›
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_openBitTest B e φ ν)
    (Filter.Eventually.of_forall fun ω => ?_)]
  · refine lintegral_congr fun ω => ?_
    by_cases h : B.splitBit e ω = true
    · rw [openBitTest, if_pos h, if_pos h]
      rfl
    · rw [openBitTest, if_neg h, if_neg h]
      rw [ENNReal.ofReal_zero]
  · by_cases h : B.splitBit e ω = true
    · rw [openBitTest, if_pos h]; exact hφ _
    · rw [openBitTest, if_neg h]; exact le_refl 0

/-- `ofReal` of the rate-weighted finite-stage integral is the corresponding
Lebesgue integral. -/
lemma ofReal_integral_rate_mul (ρ : Configuration E → ℝ) (hρ0 : ∀ ω, 0 ≤ ρ ω)
    (hρ1 : ∀ ω, ρ ω ≤ 1) (hρmeas : Measurable ρ)
    (φ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ)
    (hφ : ∀ y, 0 ≤ φ y) (ν : Measure (Configuration E)) [IsFiniteMeasure ν] :
    ENNReal.ofReal (∫ ω, ρ ω * offTest B e φ ω ∂ν)
      = ∫⁻ ω, ENNReal.ofReal (ρ ω) * ENNReal.ofReal (φ (B.splitOff e ω)) ∂ν := by
  have hnn : ∀ ω, 0 ≤ ρ ω * offTest B e φ ω := fun ω =>
    mul_nonneg (hρ0 ω) (hφ (B.splitOff e ω))
  have hmeas : Measurable fun ω => ρ ω * offTest B e φ ω :=
    hρmeas.mul (measurable_offTest B e φ)
  have hint : Integrable (fun ω => ρ ω * offTest B e φ ω) ν := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable ‖φ‖ ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω)]
    calc ρ ω * offTest B e φ ω ≤ 1 * ‖φ‖ :=
          mul_le_mul (hρ1 ω) (offTest_le_norm B e φ hφ ω) (hφ _) zero_le_one
      _ = ‖φ‖ := one_mul _
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_mul (hρ0 ω)]
  rfl

/-- **Finite stage in real form.** -/
theorem finiteStage_real
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (ρs : ℕ → Configuration E → ℝ)
    (hcont : ∀ k, Continuous (ρs k))
    (hρ0 : ∀ k ω, 0 ≤ ρs k ω) (hρ1 : ∀ k ω, ρs k ω ≤ 1)
    (hfin : ∀ k (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (k : ℕ) (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (hφ : ∀ y, 0 ≤ φ y) :
    ∫ ω, openBitTest B e φ ω ∂(μs k : Measure (Configuration E))
      = ∫ ω, ρs k ω * offTest B e φ ω ∂(μs k : Measure (Configuration E)) := by
  classical
  haveI : IsFiniteMeasure (μs k : Measure (Configuration E)) := inferInstance
  have hgmeas : Measurable fun z : B.Exterior × Glauber.OffConfig Bool B.edges e =>
      ENNReal.ofReal (φ z) :=
    ENNReal.measurable_ofReal.comp φ.continuous.measurable
  have h := hfin k (fun z => ENNReal.ofReal (φ z)) hgmeas
  -- convert the `bif` indicator into the `if`-form
  have hif : ∫⁻ ω, (if B.splitBit e ω = true then ENNReal.ofReal (φ (B.splitOff e ω)) else 0)
        ∂(μs k : Measure (Configuration E))
      = ∫⁻ ω, ENNReal.ofReal (ρs k ω) * ENNReal.ofReal (φ (B.splitOff e ω))
        ∂(μs k : Measure (Configuration E)) := by
    rw [← h]
    exact lintegral_congr fun ω => ite_bool_eq_bif (B.splitBit e ω) _ 0
  have key : ENNReal.ofReal (∫ ω, openBitTest B e φ ω ∂(μs k : Measure (Configuration E)))
      = ENNReal.ofReal (∫ ω, ρs k ω * offTest B e φ ω ∂(μs k : Measure (Configuration E))) := by
    rw [ofReal_integral_openBitTest (B := B) (e := e) φ hφ (μs k : Measure _),
      ofReal_integral_rate_mul (B := B) (e := e) (ρs k) (hρ0 k) (hρ1 k) (hcont k).measurable
        φ hφ (μs k : Measure _), hif]
  have h1 : 0 ≤ ∫ ω, openBitTest B e φ ω ∂(μs k : Measure (Configuration E)) := by
    refine integral_nonneg fun ω => ?_
    by_cases hb : B.splitBit e ω = true
    · rw [openBitTest, if_pos hb]; exact hφ _
    · rw [openBitTest, if_neg hb]; exact le_refl 0
  have h2 : 0 ≤ ∫ ω, ρs k ω * offTest B e φ ω ∂(μs k : Measure (Configuration E)) :=
    integral_nonneg fun ω => mul_nonneg (hρ0 k ω) (hφ _)
  exact (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp key

/-- **One-sided limit passage.**  If the finite-volume laws `μs k` satisfy the
one-point identity with the rates `ρs k`, the rates are continuous, lie in
`[0,1]` and decrease pointwise to `ρ`, and `μs k ⇀ μ`, then the limit law
satisfies the one-point *inequality* with rate `ρ`. -/
theorem onePoint_le_of_antitone_rates
    (μs : ℕ → ProbabilityMeasure (Configuration E)) (μ : ProbabilityMeasure (Configuration E))
    (ρs : ℕ → Configuration E → ℝ) (ρ : Configuration E → ℝ)
    (hcont : ∀ k, Continuous (ρs k))
    (hρ0 : ∀ k ω, 0 ≤ ρs k ω) (hρ1 : ∀ k ω, ρs k ω ≤ 1)
    (hmono : ∀ k ω, ρs (k+1) ω ≤ ρs k ω)
    (hlim : ∀ ω, Tendsto (fun k => ρs k ω) atTop (𝓝 (ρ ω)))
    (hfin : ∀ k (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (hφ : ∀ y, 0 ≤ φ y) :
    ∫ ω, openBitTest B e φ ω ∂(μ : Measure (Configuration E))
      ≤ ∫ ω, ρ ω * offTest B e φ ω ∂(μ : Measure (Configuration E)) := by
  classical
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  have hstage : ∀ k, ∫ ω, openBitTest B e φ ω ∂(μs k : Measure (Configuration E))
      = ∫ ω, ρs k ω * offTest B e φ ω ∂(μs k : Measure (Configuration E)) :=
    fun k => finiteStage_real B e μs ρs hcont hρ0 hρ1 hfin k φ hφ
  have hL : Tendsto (fun k => ∫ ω, openBitTest B e φ ω ∂(μs k : Measure (Configuration E)))
      atTop (𝓝 (∫ ω, openBitTest B e φ ω ∂(μ : Measure (Configuration E)))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ)
      (BoundedContinuousFunction.mkOfCompact
        ⟨openBitTest B e φ, continuous_openBitTest B e φ⟩)
  have hM : ∀ m, Tendsto (fun k => ∫ ω, ρs m ω * offTest B e φ ω
        ∂(μs k : Measure (Configuration E))) atTop
      (𝓝 (∫ ω, ρs m ω * offTest B e φ ω ∂(μ : Measure (Configuration E)))) := by
    intro m
    refine (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ)
      (BoundedContinuousFunction.mkOfCompact
        ⟨fun ω => ρs m ω * offTest B e φ ω, (hcont m).mul (continuous_offTest B e φ)⟩)
  have hcmp : ∀ m, ∀ᶠ k in atTop, ∫ ω, ρs k ω * offTest B e φ ω
        ∂(μs k : Measure (Configuration E))
      ≤ ∫ ω, ρs m ω * offTest B e φ ω ∂(μs k : Measure (Configuration E)) := by
    intro m
    filter_upwards [eventually_ge_atTop m] with k hk
    haveI : IsFiniteMeasure (μs k : Measure (Configuration E)) := inferInstance
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_)
      (integrable_rate_mul B e (ρs m) (hρ0 m) (hρ1 m) (hcont m).measurable φ hφ
        (μs k : Measure _))
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact mul_nonneg (hρ0 k ω) (hφ _)
    · have hle : ρs k ω ≤ ρs m ω :=
        antitone_nat_of_succ_le (f := fun i => ρs i ω) (fun i => hmono i ω) hk
      exact mul_le_mul_of_nonneg_right hle (hφ _)
  have h1 : ∀ m, ∫ ω, openBitTest B e φ ω ∂(μ : Measure (Configuration E))
      ≤ ∫ ω, ρs m ω * offTest B e φ ω ∂(μ : Measure (Configuration E)) := by
    intro m
    exact le_of_tendsto_of_tendsto (hL.congr' (Filter.Eventually.of_forall fun k => hstage k))
      (hM m) (hcmp m)
  have hlim_int : Tendsto (fun m => ∫ ω, ρs m ω * offTest B e φ ω
        ∂(μ : Measure (Configuration E))) atTop
      (𝓝 (∫ ω, ρ ω * offTest B e φ ω ∂(μ : Measure (Configuration E)))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖) ?_ ?_ ?_ ?_
    · intro m
      exact ((hcont m).measurable.mul (measurable_offTest B e φ)).aestronglyMeasurable
    · exact integrable_const ‖φ‖
    · intro m
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (show 0 ≤ ρs m ω * offTest B e φ ω from
        mul_nonneg (hρ0 m ω) (hφ _))]
      calc ρs m ω * offTest B e φ ω ≤ 1 * ‖φ‖ :=
            mul_le_mul (hρ1 m ω) (offTest_le_norm B e φ hφ ω) (hφ _) zero_le_one
        _ = ‖φ‖ := one_mul _
    · filter_upwards with ω
      exact (hlim ω).mul_const (offTest B e φ ω)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim_int (Filter.Eventually.of_forall fun m => h1 m)

/-- The integral of an indicator-constant test. -/
lemma integral_openBitFactor_mul (c : ℝ) (ν : Measure (Configuration E)) [IsFiniteMeasure ν] :
    ∫ ω, (if B.splitBit e ω = true then c else 0) ∂ν
      = c * ((ν {ω | B.splitBit e ω = true}).toReal) := by
  have hmeas : MeasurableSet {ω : Configuration E | B.splitBit e ω = true} :=
    (measurableSet_singleton true).preimage (B.measurable_splitBit e)
  have hfun : (fun ω => if B.splitBit e ω = true then c else 0)
      = {ω : Configuration E | B.splitBit e ω = true}.indicator (fun _ => c) := by
    funext ω
    by_cases h : B.splitBit e ω = true
    · rw [if_pos h, Set.indicator_of_mem (by exact h)]
    · rw [if_neg h, Set.indicator_of_notMem (by exact h)]
  rw [hfun, MeasureTheory.integral_indicator hmeas, MeasureTheory.setIntegral_const]
  simp only [MeasureTheory.Measure.real, smul_eq_mul]
  ring

/-- **Two-sided continuous-test identity, nonnegative tests.**  Under the scalar
mass identity, the one-point identity holds for every bounded continuous
nonnegative real test function of the off-edge box data. -/
theorem onePoint_eq_of_scalar_continuous
    (μs : ℕ → ProbabilityMeasure (Configuration E)) (μ : ProbabilityMeasure (Configuration E))
    (ρs : ℕ → Configuration E → ℝ) (ρ : Configuration E → ℝ)
    (hcont : ∀ k, Continuous (ρs k))
    (hρ0 : ∀ k ω, 0 ≤ ρs k ω) (hρ1 : ∀ k ω, ρs k ω ≤ 1)
    (hmono : ∀ k ω, ρs (k+1) ω ≤ ρs k ω)
    (hlim : ∀ ω, Tendsto (fun k => ρs k ω) atTop (𝓝 (ρ ω)))
    (hfin : ∀ k (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hρmeas : Measurable ρ)
    (hρ0' : ∀ ω, 0 ≤ ρ ω)
    (hscalar : ∫⁻ ω, ENNReal.ofReal (ρ ω) ∂(μ : Measure (Configuration E))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
    (φ : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ) (hφ : ∀ y, 0 ≤ φ y) :
    ∫ ω, openBitTest B e φ ω ∂(μ : Measure (Configuration E))
      = ∫ ω, ρ ω * offTest B e φ ω ∂(μ : Measure (Configuration E)) := by
  classical
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  have hAmeas : MeasurableSet {ω : Configuration E | B.splitBit e ω = true} :=
    (measurableSet_singleton true).preimage (B.measurable_splitBit e)
  -- the scalar identity in real form
  have hρint : ∫ ω, ρ ω ∂(μ : Measure (Configuration E))
      = ((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal := by
    have h1 : ∫ ω, (ENNReal.ofReal (ρ ω)).toReal ∂(μ : Measure (Configuration E))
        = (∫⁻ ω, ENNReal.ofReal (ρ ω) ∂(μ : Measure (Configuration E))).toReal :=
      MeasureTheory.integral_toReal (ENNReal.measurable_ofReal.comp hρmeas).aemeasurable
        (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)
    rw [hscalar] at h1
    rw [← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (ENNReal.toReal_ofReal (hρ0' ω)).symm)
  have hρ1' : ∀ ω, ρ ω ≤ 1 := by
    intro ω
    exact le_of_tendsto (hlim ω) (Filter.Eventually.of_forall fun k => hρ1 k ω)
  -- the complementary nonnegative test
  have hcont' : Continuous fun y : B.Exterior × Glauber.OffConfig Bool B.edges e => ‖φ‖ - φ y :=
    continuous_const.sub φ.continuous
  set φ' : BoundedContinuousFunction
      (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y => ‖φ‖ - φ y, hcont'⟩ with hφ'def
  have hφ'coe : ∀ y, φ' y = ‖φ‖ - φ y := fun y => rfl
  have hφ' : ∀ y, 0 ≤ φ' y := by
    intro y
    have h1 : φ y ≤ ‖φ‖ := by
      have h2 := φ.norm_coe_le_norm y
      rw [Real.norm_eq_abs] at h2
      exact le_trans (le_abs_self _) h2
    rw [hφ'coe]
    linarith
  have h1 := onePoint_le_of_antitone_rates B e μs μ ρs ρ hcont hρ0 hρ1 hmono hlim hfin hμ φ hφ
  have h2 := onePoint_le_of_antitone_rates B e μs μ ρs ρ hcont hρ0 hρ1 hmono hlim hfin hμ φ' hφ'
  -- the sum of the two open-bit integrals
  have hsum1 : ∫ ω, openBitTest B e φ ω ∂(μ : Measure (Configuration E))
      + ∫ ω, openBitTest B e φ' ω ∂(μ : Measure (Configuration E))
      = ‖φ‖ * ((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal := by
    have hpt : ∀ ω : Configuration E,
        openBitTest B e φ ω + openBitTest B e φ' ω
          = (if B.splitBit e ω = true then ‖φ‖ else 0) := by
      intro ω
      by_cases h : B.splitBit e ω = true
      · simp only [openBitTest, offTest, hφ'coe, if_pos h]
        ring
      · simp only [openBitTest, offTest, hφ'coe, if_neg h]
        ring
    rw [← MeasureTheory.integral_add (integrable_openBitTest B e φ _)
      (integrable_openBitTest B e φ' _)]
    rw [show ∫ ω, (openBitTest B e φ ω + openBitTest B e φ' ω)
        ∂(μ : Measure (Configuration E))
        = ∫ ω, (if B.splitBit e ω = true then ‖φ‖ else 0) ∂(μ : Measure (Configuration E)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => hpt ω)]
    exact integral_openBitFactor_mul B e ‖φ‖ _
  have hsum2 : ∫ ω, ρ ω * offTest B e φ ω ∂(μ : Measure (Configuration E))
      + ∫ ω, ρ ω * offTest B e φ' ω ∂(μ : Measure (Configuration E))
      = ‖φ‖ * ((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal := by
    have hpt : ∀ ω : Configuration E,
        ρ ω * offTest B e φ ω + ρ ω * offTest B e φ' ω = ρ ω * ‖φ‖ := by
      intro ω
      simp only [offTest, hφ'coe]
      ring
    rw [← MeasureTheory.integral_add (integrable_rate_mul B e ρ hρ0' hρ1' hρmeas φ hφ _)
      (integrable_rate_mul B e ρ hρ0' hρ1' hρmeas φ' hφ' _)]
    rw [show ∫ ω, (ρ ω * offTest B e φ ω + ρ ω * offTest B e φ' ω)
        ∂(μ : Measure (Configuration E))
        = ∫ ω, ρ ω * ‖φ‖ ∂(μ : Measure (Configuration E)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => hpt ω)]
    rw [MeasureTheory.integral_mul_const, hρint]
    ring
  linarith


lemma coe_measurable_test (ψ : BoundedContinuousFunction
    (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ≥0) :
    Measurable fun y => (ψ y : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp ψ.continuous.measurable

/-- The `splitOff`-pushforward of the open-bit part, tested against `ψ`, is the
real integral of the indicator test. -/
theorem lintegral_pushforward_restrict (μ : ProbabilityMeasure (Configuration E))
    (ψ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ≥0) :
    ∫⁻ y, (ψ y : ℝ≥0∞) ∂(((μ : Measure (Configuration E)).restrict
        {ω | B.splitBit e ω = true}).map (B.splitOff e))
      = ∫⁻ ω in {ω : Configuration E | B.splitBit e ω = true},
          (ψ (B.splitOff e ω) : ℝ≥0∞) ∂(μ : Measure (Configuration E)) := by
  rw [MeasureTheory.lintegral_map (coe_measurable_test B e ψ) (B.measurable_splitOff e)]

/-- The same lintegral as `ofReal` of the real open-bit test integral. -/
theorem lintegral_pushforward_restrict_eq (μ : ProbabilityMeasure (Configuration E))
    (ψ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ≥0) :
    ∫⁻ y, (ψ y : ℝ≥0∞) ∂(((μ : Measure (Configuration E)).restrict
        {ω | B.splitBit e ω = true}).map (B.splitOff e))
      = ENNReal.ofReal (∫ ω, openBitTest B e
          (BoundedContinuousFunction.mkOfCompact ⟨fun y => (ψ y : ℝ), NNReal.continuous_coe.comp ψ.continuous⟩) ω
          ∂(μ : Measure (Configuration E))) := by
  set ψr : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y => (ψ y : ℝ), NNReal.continuous_coe.comp ψ.continuous⟩
    with hψr
  have hcoe : ∀ y, ψr y = (ψ y : ℝ) := fun y => rfl
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  have hAmeas : MeasurableSet {ω : Configuration E | B.splitBit e ω = true} :=
    (measurableSet_singleton true).preimage (B.measurable_splitBit e)
  rw [lintegral_pushforward_restrict B e μ ψ]
  -- now: ∫⁻ ω in A, ↑(ψ (splitOff ω)) = ofReal (∫ openBitTest ψr)
  conv_lhs => rw [← MeasureTheory.lintegral_indicator (μ := (μ : Measure (Configuration E)))
    hAmeas (f := fun ω => (ψ (B.splitOff e ω) : ℝ≥0∞))]
  have hstep : (∫⁻ ω, {ω : Configuration E | B.splitBit e ω = true}.indicator
        (fun ω => (ψ (B.splitOff e ω) : ℝ≥0∞)) ω ∂(μ : Measure (Configuration E)))
      = ∫⁻ ω, ENNReal.ofReal (openBitTest B e ψr ω) ∂(μ : Measure (Configuration E)) := by
    refine lintegral_congr fun ω => ?_
    by_cases h : B.splitBit e ω = true
    · rw [Set.indicator_of_mem (by exact h), openBitTest, if_pos h, offTest, hcoe,
        ENNReal.ofReal_coe_nnreal]
    · rw [Set.indicator_of_notMem (by exact h), openBitTest, if_neg h, ENNReal.ofReal_zero]
  rw [hstep, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_openBitTest B e ψr _)
    (Filter.Eventually.of_forall fun ω => by
      by_cases h : B.splitBit e ω = true
      · rw [openBitTest, if_pos h, offTest, hcoe]
        exact (ψ (B.splitOff e ω)).coe_nonneg
      · rw [openBitTest, if_neg h]; exact le_refl 0)]

/-- The `splitOff`-pushforward of the `ρ`-weighted part, tested against `ψ`, is
`ofReal` of the real rate-weighted integral. -/
theorem lintegral_pushforward_withDensity (μ : ProbabilityMeasure (Configuration E))
    (ρ : Configuration E → ℝ) (hρmeas : Measurable ρ) (hρ0' : ∀ ω, 0 ≤ ρ ω)
    (hρ1' : ∀ ω, ρ ω ≤ 1)
    (ψ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ≥0) :
    ∫⁻ y, (ψ y : ℝ≥0∞) ∂(((μ : Measure (Configuration E)).withDensity
        (fun ω => ENNReal.ofReal (ρ ω))).map (B.splitOff e))
      = ENNReal.ofReal (∫ ω, ρ ω * offTest B e
          (BoundedContinuousFunction.mkOfCompact ⟨fun y => (ψ y : ℝ), NNReal.continuous_coe.comp ψ.continuous⟩) ω
          ∂(μ : Measure (Configuration E))) := by
  set ψr : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y => (ψ y : ℝ), NNReal.continuous_coe.comp ψ.continuous⟩
    with hψr
  have hcoe : ∀ y, ψr y = (ψ y : ℝ) := fun y => rfl
  have hψr0 : ∀ y, 0 ≤ ψr y := fun y => by rw [hcoe]; exact (ψ y).coe_nonneg
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  haveI hfin : IsFiniteMeasure ((μ : Measure (Configuration E)).withDensity
      (fun ω => ENNReal.ofReal (ρ ω))) := by
    constructor
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ ω, ENNReal.ofReal (ρ ω) ∂(μ : Measure (Configuration E))
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(μ : Measure (Configuration E)) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_one.mpr (hρ1' ω)
      _ = 1 := by simp
      _ < ∞ := by simp
  rw [MeasureTheory.lintegral_map (coe_measurable_test B e ψ) (B.measurable_splitOff e)]
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul (μ : Measure (Configuration E))
    (f := fun ω => ENNReal.ofReal (ρ ω)) (ENNReal.measurable_ofReal.comp hρmeas)
    (g := fun a => (ψ (B.splitOff e a) : ℝ≥0∞)) (by
      exact (coe_measurable_test B e ψ).comp (B.measurable_splitOff e))]
  have hstep : (∫⁻ ω, ((fun ω => ENNReal.ofReal (ρ ω)) *
        fun a => (ψ (B.splitOff e a) : ℝ≥0∞)) ω ∂(μ : Measure (Configuration E)))
      = ∫⁻ ω, ENNReal.ofReal (ρ ω * offTest B e ψr ω) ∂(μ : Measure (Configuration E)) := by
    refine lintegral_congr fun ω => ?_
    rw [Pi.mul_apply, offTest, hcoe]
    rw [show ((ψ (B.splitOff e ω) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal ((ψ (B.splitOff e ω) : ℝ≥0) : ℝ) from
      (ENNReal.ofReal_coe_nnreal (p := ψ (B.splitOff e ω))).symm]
    rw [← ENNReal.ofReal_mul (hρ0' ω)]
  rw [hstep, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_rate_mul B e ρ hρ0' hρ1' hρmeas ψr hψr0 _)
    (Filter.Eventually.of_forall fun ω => mul_nonneg (hρ0' ω) (hψr0 _))]

/-- **Pushforward equality.**  The continuous-test one-point identity forces the
two `splitOff`-pushforwards of the open-bit part and of the `ρ`-weighted part to
coincide. -/
theorem map_splitOff_restrict_eq_withDensity (μ : ProbabilityMeasure (Configuration E))
    (ρ : Configuration E → ℝ) (hρmeas : Measurable ρ) (hρ0' : ∀ ω, 0 ≤ ρ ω)
    (hρ1' : ∀ ω, ρ ω ≤ 1)
    (hcontId : ∀ (φ : BoundedContinuousFunction
        (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ), (∀ y, 0 ≤ φ y) →
      ∫ ω, openBitTest B e φ ω ∂(μ : Measure (Configuration E))
        = ∫ ω, ρ ω * offTest B e φ ω ∂(μ : Measure (Configuration E))) :
    ((μ : Measure (Configuration E)).restrict {ω | B.splitBit e ω = true}).map (B.splitOff e)
      = ((μ : Measure (Configuration E)).withDensity (fun ω => ENNReal.ofReal (ρ ω))).map
          (B.splitOff e) := by
  classical
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  haveI hfin : IsFiniteMeasure ((μ : Measure (Configuration E)).withDensity
      (fun ω => ENNReal.ofReal (ρ ω))) := by
    constructor
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ ω, ENNReal.ofReal (ρ ω) ∂(μ : Measure (Configuration E))
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(μ : Measure (Configuration E)) :=
          lintegral_mono fun ω => ENNReal.ofReal_le_one.mpr (hρ1' ω)
      _ = 1 := by simp
      _ < ∞ := by simp
  haveI : IsFiniteMeasure (((μ : Measure (Configuration E)).restrict
      {ω | B.splitBit e ω = true}).map (B.splitOff e)) :=
    MeasureTheory.Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure (((μ : Measure (Configuration E)).withDensity
      (fun ω => ENNReal.ofReal (ρ ω))).map (B.splitOff e)) :=
    MeasureTheory.Measure.isFiniteMeasure_map _ _
  refine MeasureTheory.ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun ψ => ?_
  rw [lintegral_pushforward_restrict_eq B e μ ψ,
    lintegral_pushforward_withDensity B e μ ρ hρmeas hρ0' hρ1' ψ]
  set ψr : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun y => (ψ y : ℝ), NNReal.continuous_coe.comp ψ.continuous⟩
  have hψr0 : ∀ y, 0 ≤ ψr y := fun y => (ψ y).coe_nonneg
  rw [hcontId ψr hψr0]

/-- **Per-edge one-point conditionals of the limit law.**  Under the finite-stage
identities, the monotone continuous rates, the scalar mass identity and the
identification of the limiting rate with the box specification's open rate, the
limit law has the box specification's one-point conditional probability at the
fixed edge `e`, tested against every measurable function of the off-edge data. -/
theorem onePoint_edge_of_scalar (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    (ρs : ℕ → Configuration E → ℝ) (ρ : Configuration E → ℝ)
    (hcont : ∀ k, Continuous (ρs k))
    (hρ0 : ∀ k ω, 0 ≤ ρs k ω) (hρ1 : ∀ k ω, ρs k ω ≤ 1)
    (hmono : ∀ k ω, ρs (k+1) ω ≤ ρs k ω)
    (hlim : ∀ ω, Tendsto (fun k => ρs k ω) atTop (𝓝 (ρ ω)))
    (hfin : ∀ k (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hρmeas : Measurable ρ) (hρ0' : ∀ ω, 0 ≤ ρ ω) (hρ1' : ∀ ω, ρ ω ≤ 1)
    (hscalar : ∫⁻ ω, ENNReal.ofReal (ρ ω) ∂(μ : Measure (Configuration E))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
    (α : B.Exterior → B.BoundaryPartition)
    (hrate : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ρ ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) :
    ∀ (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μ : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
              (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
          ∂(μ : Measure (Configuration E)) := by
  classical
  have hcontId := onePoint_eq_of_scalar_continuous B e μs μ ρs ρ hcont hρ0 hρ1 hmono hlim hfin
    hμ hρmeas hρ0' hscalar
  have hν := map_splitOff_restrict_eq_withDensity B e μ ρ hρmeas hρ0' hρ1' hcontId
  intro g hg
  haveI : IsFiniteMeasure (μ : Measure (Configuration E)) := inferInstance
  have hAmeas : MeasurableSet {ω : Configuration E | B.splitBit e ω = true} :=
    (measurableSet_singleton true).preimage (B.measurable_splitBit e)
  calc ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
        ∂(μ : Measure (Configuration E))
      = ∫⁻ y, g y ∂(((μ : Measure (Configuration E)).restrict
          {ω | B.splitBit e ω = true}).map (B.splitOff e)) := by
        rw [MeasureTheory.lintegral_map hg (B.measurable_splitOff e)]
        rw [show ∫⁻ ω in {ω : Configuration E | B.splitBit e ω = true},
              g (B.splitOff e ω) ∂(μ : Measure (Configuration E))
            = ∫⁻ ω, {ω : Configuration E | B.splitBit e ω = true}.indicator
                (fun ω => g (B.splitOff e ω)) ω ∂(μ : Measure (Configuration E)) from
          (MeasureTheory.lintegral_indicator (μ := (μ : Measure (Configuration E)))
            hAmeas (fun ω => g (B.splitOff e ω))).symm]
        refine lintegral_congr fun ω => ?_
        by_cases h : B.splitBit e ω = true
        · rw [Set.indicator_of_mem (by exact h)]
          rw [show (bif B.splitBit e ω then g (B.splitOff e ω) else 0) = g (B.splitOff e ω)
            from by rw [h]; rfl]
        · rw [Set.indicator_of_notMem (by exact h)]
          have hf : B.splitBit e ω = false := by rwa [Bool.not_eq_true] at h
          rw [show (bif B.splitBit e ω then g (B.splitOff e ω) else 0) = 0
            from by rw [hf]; rfl]
    _ = ∫⁻ y, g y ∂(((μ : Measure (Configuration E)).withDensity
          (fun ω => ENNReal.ofReal (ρ ω))).map (B.splitOff e)) := by rw [hν]
    _ = ∫⁻ ω, ENNReal.ofReal (ρ ω) * g (B.splitOff e ω) ∂(μ : Measure (Configuration E)) := by
        rw [MeasureTheory.lintegral_map hg (B.measurable_splitOff e)]
        exact MeasureTheory.lintegral_withDensity_eq_lintegral_mul (μ : Measure (Configuration E))
          (f := fun ω => ENNReal.ofReal (ρ ω)) (ENNReal.measurable_ofReal.comp hρmeas)
          (g := fun a => g (B.splitOff e a)) (hg.comp (B.measurable_splitOff e))
    _ = ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
              (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
          ∂(μ : Measure (Configuration E)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrate] with ω hω
        rw [hω]


/-- **Box-level one-point conditionals from per-edge two-valued data.**  If for
every box edge the per-edge limit theorem `onePoint_edge_of_scalar` applies with
the same specification `α`, then the limit law satisfies the box's
`HasOnePointConditionalsBif` in the specification `α`. -/
theorem hasOnePointConditionalsBif_of_edge_scalar
    {q p : NNReal}
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (ρs : (e : B.edges) → ℕ → Configuration E → ℝ)
    (ρ : (e : B.edges) → Configuration E → ℝ)
    (hcont : ∀ e k, Continuous (ρs e k))
    (hρ0 : ∀ e k ω, 0 ≤ ρs e k ω) (hρ1 : ∀ e k ω, ρs e k ω ≤ 1)
    (hmono : ∀ e k ω, ρs e (k+1) ω ≤ ρs e k ω)
    (hlim : ∀ e ω, Tendsto (fun k => ρs e k ω) atTop (𝓝 (ρ e ω)))
    (hfin : ∀ (e : B.edges) k (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs e k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hρmeas : ∀ e, Measurable (ρ e))
    (hρ0' : ∀ e ω, 0 ≤ ρ e ω) (hρ1' : ∀ e ω, ρ e ω ≤ 1)
    (hscalar : ∀ e, ∫⁻ ω, ENNReal.ofReal (ρ e ω) ∂(μ : Measure (Configuration E))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
    (α : B.Exterior → B.BoundaryPartition)
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ρ e ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) :
    B.HasOnePointConditionalsBif (q := q) (p := p) α μ :=
  fun e g hg => onePoint_edge_of_scalar B e μs μ (ρs e) (ρ e) (hcont e) (hρ0 e) (hρ1 e)
    (hmono e) (hlim e) (hfin e) hμ (hρmeas e) (hρ0' e) (hρ1' e) (hscalar e) α (hrate e) g hg

/-- **DLR of the limit at one box.**  The box-level one-point conditionals of the
limit law give its actual Dixon--Vere-Jones DLR identity at that box, through
`FiniteBox.isDLR_of_hasOnePointConditionals`. -/
theorem isDLR_of_edge_scalar
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (ρs : (e : B.edges) → ℕ → Configuration E → ℝ)
    (ρ : (e : B.edges) → Configuration E → ℝ)
    (hcont : ∀ e k, Continuous (ρs e k))
    (hρ0 : ∀ e k ω, 0 ≤ ρs e k ω) (hρ1 : ∀ e k ω, ρs e k ω ≤ 1)
    (hmono : ∀ e k ω, ρs e (k+1) ω ≤ ρs e k ω)
    (hlim : ∀ e ω, Tendsto (fun k => ρs e k ω) atTop (𝓝 (ρ e ω)))
    (hfin : ∀ (e : B.edges) k (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs e k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hρmeas : ∀ e, Measurable (ρ e))
    (hρ0' : ∀ e ω, 0 ≤ ρ e ω) (hρ1' : ∀ e ω, ρ e ω ≤ 1)
    (hscalar : ∀ e, ∫⁻ ω, ENNReal.ofReal (ρ e ω) ∂(μ : Measure (Configuration E))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (hrate : ∀ (e : B.edges), ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ρ e ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) :
    B.IsDLR hq hp₁.le α hα μ :=
  B.isDLR_of_hasOnePointConditionals hq hp₀ hp₁ α hα μ
    ((B.hasOnePointConditionals_iff_bif α μ).mpr
      (hasOnePointConditionalsBif_of_edge_scalar B μs μ hμ ρs ρ hcont hρ0 hρ1 hmono hlim
        hfin hρmeas hρ0' hρ1' hscalar α hrate))

end LimitTransfer

/-! ## Part 4: the automatic half of the scalar mass identity -/

section TwoValued

/-- **Increasing clopen families are asymptotically seen.**  If the clopen sets
`C k` increase to `C∞` and `μs k ⇀ μ`, then `μ C∞ ≤ liminf_k μs k (C k)`.

This is the automatic half of the scalar mass identity
`μs k (C k) → μ C∞` that `onePoint_eq_of_scalar_continuous` needs in the
two-valued connectivity shape: the other half (`limsup ≤`) is exactly the
uniform-in-volume *no-mass-escape* input for the connection events, and it does
not follow from weak convergence alone (mass can leave along the exhaustion). -/
theorem le_liminf_measure_of_monotone_clopen {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    {μs : ℕ → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) {C : ℕ → Set X} {Cinf : Set X}
    (hmono : Monotone C) (hclopen : ∀ k, IsClopen (C k))
    (hUnion : ∀ x, (∃ k, x ∈ C k) ↔ x ∈ Cinf) :
    ((μ : Measure X) Cinf)
      ≤ Filter.liminf (fun k => (μs k : Measure X) (C k)) atTop := by
  classical
  have hunion : Cinf = ⋃ k, C k := by
    ext x
    rw [Set.mem_iUnion]
    exact (hUnion x).symm
  have hcmp : ∀ m, ∀ᶠ k in atTop, (μs k : Measure X) (C m) ≤ (μs k : Measure X) (C k) := by
    intro m
    filter_upwards [eventually_ge_atTop m] with k hk
    exact measure_mono (hmono hk)
  have hfrontier : ∀ m, (μ : Measure X) (frontier (C m)) = 0 := by
    intro m
    rw [isClopen_iff_frontier_eq_empty.mp (hclopen m)]
    simp
  have htendC : ∀ m, Tendsto (fun k => (μs k : Measure X) (C m)) atTop
      (𝓝 ((μ : Measure X) (C m))) := fun m =>
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (hfrontier m)
  have hlower : ∀ m, (μ : Measure X) (C m)
      ≤ Filter.liminf (fun k => (μs k : Measure X) (C k)) atTop := by
    intro m
    rw [← (htendC m).liminf_eq]
    exact Filter.liminf_le_liminf (hcmp m)
  rw [hunion, hmono.measure_iUnion]
  exact iSup_le hlower

end TwoValued
