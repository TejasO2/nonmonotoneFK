import FK.CouplingSealCounterexample
import FK.RandomExhaustion

/-!
# An exact obstruction to the last random-frontier averaging step

The two marginal laws below are the same fair Bernoulli law.  The upper law is
Bernoulli(3/4), coupled to the fair law by the explicit ordered coupling from
`CouplingSealCounterexample`.  On the upper-open stratum we use the full finite
region; on the upper-closed stratum we use the empty region with its edge
closed.  Both stages satisfy the fixed-region conditional identification used
by `RandomExhaustion`.  Their common value is respectively `1/2` and `0`, so its
upper average is `3/8`, whereas the fair marginal's open mass is `1/2`.

Thus the fixed-region fibre identifications and the ordered triple do not imply
that the integral of a fibrewise conditional expectation is the unconditional
mass.  This is an obstruction to that fixed-stage inference, not a counterexample
to DLR uniqueness (the two displayed candidate marginals are equal).  The region
map is a finite diagnostic, not a cofinal exhaustion; no claim about a separate
cofinal reverse-martingale limit is made.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

noncomputable section

namespace FKLimit.AdaptiveMarginalObstruction

open FKLimit.CouplingSealCounterexample

abbrev Cfg := Configuration Unit

/-- The one-coordinate configuration determined by a Boolean. -/
def config (b : Bool) : Cfg := fun _ => b

/-- The unique coordinate of a configuration. -/
def bit (ω : Cfg) : Bool := ω ()

@[simp] lemma bit_config (b : Bool) : bit (config b) = b := rfl

lemma config_bit (ω : Cfg) : config (bit ω) = ω := by
  funext u
  cases u
  rfl

/-- The fair candidate marginal, transported from the ordered Bool coupling. -/
noncomputable def fair : PMF Cfg := law.map (fun z => config z.1)

/-- The noncandidate upper marginal, with open probability `3/4`. -/
noncomputable def upper : PMF Cfg := law.map (fun z => config z.2)

/-- An ordered triple with both candidate coordinates equal to the lower law. -/
noncomputable def triple : PMF (Cfg × Cfg × Cfg) :=
  law.map (fun z => (config z.1, config z.1, config z.2))

/-- The cylinder whose unique coordinate is open. -/
def openEvent : Set Cfg := {ω | bit ω = true}

lemma measurableSet_openEvent : MeasurableSet openEvent := MeasurableSet.of_discrete

@[simp] lemma triple_map_first :
    Measure.map (fun p : Cfg × Cfg × Cfg => p.1) triple.toMeasure = fair.toMeasure := by
  rw [triple, fair, PMF.toMeasure_map _ _ (measurable_of_finite _), PMF.map_comp]
  rfl

@[simp] lemma triple_map_second :
    Measure.map (fun p : Cfg × Cfg × Cfg => p.2.1) triple.toMeasure = fair.toMeasure := by
  rw [triple, fair, PMF.toMeasure_map _ _ (measurable_of_finite _), PMF.map_comp]
  rfl

@[simp] lemma triple_map_upper :
    Measure.map (fun p : Cfg × Cfg × Cfg => p.2.2) triple.toMeasure = upper.toMeasure := by
  rw [triple, upper, PMF.toMeasure_map _ _ (measurable_of_finite _), PMF.map_comp]
  rfl

lemma fair_openEvent : fair.toMeasure openEvent = 1 / 2 := by
  rw [fair, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    Measure.map_apply (measurable_of_finite _) measurableSet_openEvent]
  change law.toMeasure {z | z.1 = true} = 1 / 2
  exact open_lower

lemma upper_openEvent : upper.toMeasure openEvent = 3 / 4 := by
  rw [upper, ← PMF.toMeasure_map _ _ (measurable_of_finite _),
    Measure.map_apply (measurable_of_finite _) measurableSet_openEvent]
  change law.toMeasure {z | z.2 = true} = 3 / 4
  exact open_upper

lemma fair_real_openEvent : fair.toMeasure.real openEvent = 1 / 2 := by
  rw [Measure.real, fair_openEvent]
  norm_num [ENNReal.toReal_div]

lemma upper_real_openEvent : upper.toMeasure.real openEvent = 3 / 4 := by
  rw [Measure.real, upper_openEvent]
  norm_num [ENNReal.toReal_div]

/-- The full region at an open upper bit, and the empty region at a closed one. -/
def region (η : Cfg) : Finset Unit := if bit η = true then Finset.univ else ∅

/-- A closed frontier forces the unique bit to be closed precisely when the
region is empty; the full region has empty frontier. -/
def frontier (S : Finset Unit) : Finset Unit := if S = ∅ then Finset.univ else ∅

/-- Common fixed-region value: zero on the sealed empty region, otherwise the
unconditional fair open probability. -/
def stageValue (S : Finset Unit) : ℝ := if S = ∅ then 0 else 1 / 2

lemma finset_unit_eq_empty_or_univ (S : Finset Unit) : S = ∅ ∨ S = Finset.univ := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    apply Finset.eq_univ_iff_forall.mpr
    intro u
    cases u
    cases x
    exact hx

/-- Exterior restriction to the empty excluded set is a measurable equivalence. -/
def emptyExteriorEquiv :
    Cfg ≃ᵐ ({e : Unit // e ∉ (∅ : Finset Unit)} → Bool) where
  toFun := exteriorRestriction ∅
  invFun := fun ξ _ => ξ ⟨(), by simp⟩
  left_inv := by
    intro ω
    funext u
    cases u
    rfl
  right_inv := by
    intro ξ
    funext e
    rcases e with ⟨u, hu⟩
    cases u
    rfl
  measurable_toFun := measurable_exteriorRestriction ∅
  measurable_invFun := measurable_of_finite _

lemma outsideSigma_empty :
    outsideSigma (∅ : Finset Unit) = (inferInstance : MeasurableSpace Cfg) := by
  exact emptyExteriorEquiv.measurableEmbedding.comap_eq

lemma outsideSigma_univ :
    outsideSigma (Finset.univ : Finset Unit) = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  by_cases hmem : exteriorRestriction (Finset.univ : Finset Unit) (config false) ∈ t
  · have heq : exteriorRestriction (Finset.univ : Finset Unit) ⁻¹' t = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      have hfun : exteriorRestriction (Finset.univ : Finset Unit) ω =
          exteriorRestriction (Finset.univ : Finset Unit) (config false) := by
        funext e
        exact False.elim (e.2 (Finset.mem_univ e.1))
      rw [Set.mem_preimage, hfun]
      exact hmem
    rw [heq]
    exact MeasurableSet.univ
  · have heq : exteriorRestriction (Finset.univ : Finset Unit) ⁻¹' t = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro ω hω
      apply hmem
      have hfun : exteriorRestriction (Finset.univ : Finset Unit) ω =
          exteriorRestriction (Finset.univ : Finset Unit) (config false) := by
        funext e
        exact False.elim (e.2 (Finset.mem_univ e.1))
      rw [← hfun]
      exact hω
    rw [heq]
    exact @MeasurableSet.empty Cfg ⊥

lemma integral_indicator_openEvent (μ : Measure Cfg) [IsFiniteMeasure μ] :
    (∫ ω, openEvent.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real openEvent := by
  rw [integral_indicator measurableSet_openEvent]
  simp [Measure.real, Measure.restrict_apply MeasurableSet.univ]

lemma fair_integral_indicator_openEvent :
    (∫ ω, openEvent.indicator (fun _ => (1 : ℝ)) ω ∂fair.toMeasure) = 1 / 2 := by
  rw [integral_indicator_openEvent, fair_real_openEvent]

/-- At the empty region, conditioning on the full exterior returns the event
indicator.  At the full region, it returns the constant fair mass. -/
lemma condExp_openEvent_empty (ω : Cfg) :
    fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
      outsideSigma (∅ : Finset Unit)] ω = openEvent.indicator (fun _ => (1 : ℝ)) ω := by
  rw [outsideSigma_empty]
  have hmeas : StronglyMeasurable (openEvent.indicator (fun _ => (1 : ℝ))) :=
    (measurable_of_finite _).stronglyMeasurable
  rw [condExp_of_stronglyMeasurable le_rfl hmeas Integrable.of_finite]

lemma condExp_openEvent_univ (ω : Cfg) :
    fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
      outsideSigma (Finset.univ : Finset Unit)] ω = 1 / 2 := by
  rw [outsideSigma_univ, condExp_bot]
  exact fair_integral_indicator_openEvent

/-- The exact fixed-region input of `RandomExhaustion`, proved for both finite
subsets of the one-coordinate type. -/
lemma fixed_region_identification (S : Finset Unit) :
    ∀ᵐ ω ∂fair.toMeasure, closedFrontier frontier S ω →
      fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) | outsideSigma S] ω =
        stageValue S := by
  apply Eventually.of_forall
  intro ω hfront
  rcases finset_unit_eq_empty_or_univ S with rfl | rfl
  · rw [condExp_openEvent_empty]
    have hbit : bit ω = false := by
      exact hfront () (by simp [frontier])
    simp [openEvent, stageValue, hbit]
  · rw [condExp_openEvent_univ]
    simp [stageValue]

/-- At every upper configuration the selected region has closed frontier. -/
lemma upper_closed_frontier (η : Cfg) (_n : ℕ) :
    ∀ e ∈ frontier (region η), η e = false := by
  intro e he
  cases e
  by_cases h : bit η = true
  · simp [region, frontier, h] at he
  · have hb : bit η = false := Bool.eq_false_of_not_eq_true h
    exact hb

/-- The explicit ordered Bool coupling gives almost-sure order in both candidate
coordinates of the transported triple. -/
lemma ordered_candidates :
    (∀ᵐ p ∂triple.toMeasure, p.1 ≤ p.2.2) ∧
      (∀ᵐ p ∂triple.toMeasure, p.2.1 ≤ p.2.2) := by
  have hz : ∀ᵐ z ∂law.toMeasure, z.1 ≤ z.2 := by
    have hbad : ∀ᵐ z ∂law.toMeasure, ¬(z.1 = true ∧ z.2 = false) := by
      rw [ae_iff]
      simpa only [not_not] using order_violation
    filter_upwards [hbad] with z hz
    rcases z with ⟨a, b⟩
    cases a <;> cases b <;> simp_all
  have hm : Measurable (fun z : Bool × Bool => (config z.1, config z.1, config z.2)) :=
    measurable_of_finite _
  have hmapped : ∀ᵐ p ∂(Measure.map (fun z : Bool × Bool =>
      (config z.1, config z.1, config z.2)) law.toMeasure),
      (p.1 ≤ p.2.2 ∧ p.2.1 ≤ p.2.2) := by
    rw [ae_map_iff hm.aemeasurable MeasurableSet.of_discrete]
    filter_upwards [hz] with z hz
    constructor <;> intro u <;> cases u <;> exact hz
  have hboth : ∀ᵐ p ∂triple.toMeasure, (p.1 ≤ p.2.2 ∧ p.2.1 ≤ p.2.2) := by
    rw [triple, ← PMF.toMeasure_map _ _ hm]
    exact hmapped
  exact ⟨hboth.mono (fun _ h => h.1), hboth.mono (fun _ h => h.2)⟩

lemma measurable_stageValue_region (_n : ℕ) :
    Measurable (fun η : Cfg => stageValue (region η)) := measurable_of_finite _

lemma stageValue_region_eq (η : Cfg) :
    stageValue (region η) = (1 / 2 : ℝ) * openEvent.indicator (fun _ => (1 : ℝ)) η := by
  by_cases h : bit η = true
  · simp [stageValue, region, openEvent, h]
  · simp [stageValue, region, openEvent, h]

/-- The common random-stage average is exactly `3/8`. -/
lemma upper_integral_stageValue :
    (∫ η, stageValue (region η) ∂upper.toMeasure) = 3 / 8 := by
  have hfun : (fun η => stageValue (region η)) = fun η =>
      (1 / 2 : ℝ) * openEvent.indicator (fun _ => (1 : ℝ)) η := by
    funext η
    exact stageValue_region_eq η
  rw [hfun, integral_const_mul, integral_indicator_openEvent, upper_real_openEvent]
  norm_num

/-- The accepted `RandomExhaustion` joint-stage theorem applies literally to
this ordered triple, with both original candidate conditionals equal to the
same stage value. -/
theorem ae_joint_conditional_stage :
    ∀ᵐ p ∂triple.toMeasure, ∀ _ : ℕ,
      fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
        outsideSigma (region p.2.2)] p.1 = stageValue (region p.2.2) ∧
      fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
        outsideSigma (region p.2.2)] p.2.1 = stageValue (region p.2.2) := by
  have h := ae_condExp_eq_of_dominated_coupling_frontier
    triple_map_first triple_map_second triple_map_upper
    (fun (_ : ℕ) (η : Cfg) => region η) (fun _ => measurable_of_finite _)
    frontier stageValue fixed_region_identification fixed_region_identification
    (Eventually.of_forall (fun η n => upper_closed_frontier η n))
    ordered_candidates.1 ordered_candidates.2
  exact h

/-- The accepted integral identity also applies.  Nevertheless, the common
integral of the two original marginal conditional expectations is `3/8`. -/
theorem triple_integral_first_conditional_stage (n : ℕ) :
    (∫ p, fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
      outsideSigma (region p.2.2)] p.1 ∂triple.toMeasure) = 3 / 8 := by
  have h := (integral_condExp_eq_of_dominated_coupling
    triple_map_first triple_map_second triple_map_upper
    (fun (_ : ℕ) (η : Cfg) => region η) (fun _ => measurable_of_finite _)
    (closedFrontier frontier) stageValue (measurableSet_closedFrontier frontier)
    fixed_region_identification fixed_region_identification
    (Eventually.of_forall (fun η _ => upper_closed_frontier η 0))
    (closedFrontier_mono frontier) ordered_candidates.1 ordered_candidates.2
    measurable_stageValue_region n).1
  simpa only [upper_integral_stageValue] using h

/-- The second candidate has the same common stage integral. -/
theorem triple_integral_second_conditional_stage (n : ℕ) :
    (∫ p, fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
      outsideSigma (region p.2.2)] p.2.1 ∂triple.toMeasure) = 3 / 8 := by
  have h := (integral_condExp_eq_of_dominated_coupling
    triple_map_first triple_map_second triple_map_upper
    (fun (_ : ℕ) (η : Cfg) => region η) (fun _ => measurable_of_finite _)
    (closedFrontier frontier) stageValue (measurableSet_closedFrontier frontier)
    fixed_region_identification fixed_region_identification
    (Eventually.of_forall (fun η _ => upper_closed_frontier η 0))
    (closedFrontier_mono frontier) ordered_candidates.1 ordered_candidates.2
    measurable_stageValue_region n).2
  simpa only [upper_integral_stageValue] using h

/-- **Exact obstruction.**  Even though both fixed-region identifications and
the joint-stage theorem hold, the first candidate's random-stage integral is
not its unconditional mass.  The defect is the correlation between the upper
region and the lower configuration in the ordered coupling. -/
theorem conditional_stage_integral_ne_unconditional (n : ℕ) :
    (∫ p, fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
      outsideSigma (region p.2.2)] p.1 ∂triple.toMeasure) ≠
      fair.toMeasure.real openEvent := by
  rw [triple_integral_first_conditional_stage n, fair_real_openEvent]
  norm_num

/-- Exact missing mass in the proposed averaging identity. -/
theorem conditional_stage_mass_defect (n : ℕ) :
    fair.toMeasure.real openEvent -
      (∫ p, fair.toMeasure[openEvent.indicator (fun _ => (1 : ℝ)) |
        outsideSigma (region p.2.2)] p.1 ∂triple.toMeasure) = 1 / 8 := by
  rw [triple_integral_first_conditional_stage n, fair_real_openEvent]
  norm_num

end FKLimit.AdaptiveMarginalObstruction

#print axioms FKLimit.AdaptiveMarginalObstruction.fixed_region_identification
#print axioms FKLimit.AdaptiveMarginalObstruction.ae_joint_conditional_stage
#print axioms FKLimit.AdaptiveMarginalObstruction.upper_integral_stageValue
#print axioms FKLimit.AdaptiveMarginalObstruction.triple_integral_first_conditional_stage
#print axioms FKLimit.AdaptiveMarginalObstruction.triple_integral_second_conditional_stage
#print axioms FKLimit.AdaptiveMarginalObstruction.conditional_stage_integral_ne_unconditional
#print axioms FKLimit.AdaptiveMarginalObstruction.conditional_stage_mass_defect

#check FKLimit.AdaptiveMarginalObstruction.fixed_region_identification
#check FKLimit.AdaptiveMarginalObstruction.ae_joint_conditional_stage
#check FKLimit.AdaptiveMarginalObstruction.upper_integral_stageValue
#check FKLimit.AdaptiveMarginalObstruction.triple_integral_first_conditional_stage
#check FKLimit.AdaptiveMarginalObstruction.triple_integral_second_conditional_stage
#check FKLimit.AdaptiveMarginalObstruction.conditional_stage_integral_ne_unconditional
#check FKLimit.AdaptiveMarginalObstruction.conditional_stage_mass_defect
