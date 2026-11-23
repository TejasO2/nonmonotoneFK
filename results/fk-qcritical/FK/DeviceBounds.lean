import FK.EnhancedProducts

/-! Quantitative enhancement bounds from finite device certificates. -/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal unitInterval Classical BigOperators
open OpenPath FKEnhancement

noncomputable section

/-- A permitted closed cutset gives an explicit lower bound for the closed
certificate probability under the `max(p,p')` product law. -/
theorem cutsetWeight_ge_closedCylinder
    {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E)
    (p p' : unitInterval) (e : E) (χ : Finset E)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e) :
    (1 - (max p p' : unitInterval) : ℝ) ^ χ.card ≤
      cutsetWeight K enhanced p p' e := by
  let M : unitInterval := max p p'
  have hsubset : closedCylinder χ ⊆ certificateEvent K enhanced e := by
    intro ω hω
    exact ⟨(χ : Set E), hχ, fun a ha => hω a (by exact_mod_cast ha)⟩
  have hfalse : bernoulliMeasure true false M ({false} : Set Bool) =
      unitInterval.toNNReal (σ M) := by simp
  have hcyl : ((bernoulliProduct (fun _ : E => M) (closedCylinder χ)).toReal) =
      (1 - (M : ℝ)) ^ χ.card := by
    rw [bernoulliProduct_closedCylinder]
    simp_rw [hfalse]
    rw [ENNReal.toReal_prod]
    simp [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  calc
    (1 - (max p p' : unitInterval) : ℝ) ^ χ.card =
        ((bernoulliProduct (fun _ : E => M) (closedCylinder χ)).toReal) := hcyl.symm
    _ ≤ (bernoulliProduct (fun _ : E => M) (certificateEvent K enhanced e)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ = cutsetWeight K enhanced p p' e := rfl

/-- The same bound with the real maximum, in the exact form used by the star
parameter. -/
theorem cutsetWeight_ge_pow
    {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E)
    (p p' : unitInterval) (e : E) (χ : Finset E)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e) :
    (1 - max (p : ℝ) (p' : ℝ)) ^ χ.card ≤ cutsetWeight K enhanced p p' e := by
  have hcoe : ((max p p' : unitInterval) : ℝ) = max (p : ℝ) (p' : ℝ) := by
    by_cases h : p ≤ p' <;> simp [max_def, h]
  rw [← hcoe]
  exact cutsetWeight_ge_closedCylinder K enhanced p p' e χ hχ

/-- The exact cutset epsilon minorizes the device-size power bound. -/
theorem cutsetEpsilon_ge_pow
    {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E)
    (p p' : unitInterval) (e : E) (χ : Finset E)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e) :
    |(p' : ℝ) - (p : ℝ)| * (1 - max (p : ℝ) (p' : ℝ)) ^ χ.card ≤
      cutsetEpsilon K enhanced p p' e := by
  unfold cutsetEpsilon closedCutsetEnhancement
  exact mul_le_mul_of_nonneg_left (cutsetWeight_ge_pow K enhanced p p' e χ hχ) (abs_nonneg _)

/-- Version of the device bound with a prescribed upper bound on the number of
auxiliary closed edges. -/
theorem cutsetEpsilon_ge_pow_of_card_le
    {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E)
    (p p' : unitInterval) (e : E) (χ : Finset E) (k : ℕ)
    (hχ : (χ : Set E) ∈ CutsetFamily K enhanced e) (hcard : χ.card ≤ k) :
    |(p' : ℝ) - (p : ℝ)| * (1 - max (p : ℝ) (p' : ℝ)) ^ k ≤
      cutsetEpsilon K enhanced p p' e := by
  have hbase0 : 0 ≤ 1 - max (p : ℝ) (p' : ℝ) := sub_nonneg.mpr (max_le p.2.2 p'.2.2)
  have hmax0 : 0 ≤ max (p : ℝ) (p' : ℝ) := p.2.1.trans (le_max_left _ _)
  have hbase1 : 1 - max (p : ℝ) (p' : ℝ) ≤ 1 := by linarith
  have hp := pow_le_pow_of_le_one hbase0 hbase1 hcard
  calc
    |(p' : ℝ) - (p : ℝ)| * (1 - max (p : ℝ) (p' : ℝ)) ^ k ≤
        |(p' : ℝ) - (p : ℝ)| * (1 - max (p : ℝ) (p' : ℝ)) ^ χ.card :=
      mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ ≤ cutsetEpsilon K enhanced p p' e := cutsetEpsilon_ge_pow K enhanced p p' e χ hχ

/-- Event monotonicity for real finite-probability masses. -/
lemma finProb_event_mono {α : Type*} [Fintype α] (μ : FinProb α)
    {A C : Set α} (hCA : C ⊆ A) : μ.event C ≤ μ.event A := by
  unfold FinProb.event
  apply Finset.sum_le_sum
  intro a _
  by_cases hC : a ∈ C
  · rw [if_pos hC, if_pos (hCA hC)]
  · rw [if_neg hC]
    split_ifs
    · exact μ.mass_nonneg a
    · exact le_rfl

/-- Cylinder requiring all edges in `γ` to be open. -/
def openCylinder {E : Type*} (γ : Finset E) : Set (E → Bool) :=
  ((γ : Set E).pi fun _ => {true})

@[simp] lemma mem_openCylinder {E : Type*} {γ : Finset E} {ω : E → Bool} :
    ω ∈ openCylinder γ ↔ ∀ a ∈ γ, ω a = true := by
  simp [openCylinder]

/-- Product formula for an open-edge cylinder. -/
theorem bernoulliProduct_openCylinder {E : Type*} [Fintype E]
    (rates : E → unitInterval) (γ : Finset E) :
    bernoulliProduct rates (openCylinder γ) =
      ∏ a ∈ γ, bernoulliMeasure true false (rates a) ({true} : Set Bool) := by
  simp [bernoulliProduct, openCylinder, Measure.pi_pi_finset]

/-- Exact probability normalization after converting a Bit event to Bool. -/
theorem productLaw_event_eq_toReal
    {E : Type*} [Fintype E] [DecidableEq E]
    (r : E → ℝ) (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1) (A : Set (Config E)) :
    (productLaw r hr).event A =
      (bernoulliProduct (FKLimit.unitParameters r (fun e => (hr e).1) (fun e => (hr e).2))
        (configToBool '' A)).toReal := by
  have hpre : configToBool ⁻¹' (configToBool '' A) = A := by
    exact Set.preimage_image_eq A (configBitBoolEquiv E).injective
  calc
    (productLaw r hr).event A = ((productLaw r hr).map configToBool).event
        (configToBool '' A) := by
      rw [← FinProb.event_preimage_map, hpre]
    _ = ((((productLaw r hr).map configToBool).toPMF.toMeasure)
        (configToBool '' A)).toReal := (FinProb.toPMF_event _ _).symm
    _ = (bernoulliProduct (FKLimit.unitParameters r (fun e => (hr e).1)
        (fun e => (hr e).2)) (configToBool '' A)).toReal := by
      rw [productLaw_map_configToBool_toMeasure]

/-- One admissible finite path gives an explicit power lower bound for the
open-path event probability. -/
theorem pathEventProbability_ge_pow_of_mem
    {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
    (Γ : Set (Finset E)) (γ : Finset E) (hγ : γ ∈ Γ) :
    r ^ γ.card ≤ pathEventProbability r hr Γ := by
  let μ : FinProb (Config E) := productLaw (fun _ : E => r) (fun _ => hr)
  have himage : configToBool '' {ω : Config E | OpenEdges γ ω} = openCylinder γ := by
    ext ω
    constructor
    · rintro ⟨η, hη, rfl⟩
      intro a ha
      change bitToBool (η a) = true
      rw [hη a ha, bitToBool_one]
    · intro hω
      refine ⟨configOfBool ω, ?_, (configBitBoolEquiv E).right_inv ω⟩
      intro a ha
      change boolToBit (ω a) = 1
      rw [hω a ha, boolToBit_true]
  have htrue : bernoulliMeasure true false (⟨r, hr.1, hr.2⟩ : unitInterval)
      ({true} : Set Bool) = unitInterval.toNNReal ⟨r, hr.1, hr.2⟩ := by simp
  have hcyl : μ.event {ω : Config E | OpenEdges γ ω} = r ^ γ.card := by
    dsimp only [μ]
    rw [productLaw_event_eq_toReal, himage, bernoulliProduct_openCylinder]
    change (∏ a ∈ γ, bernoulliMeasure true false (⟨r, hr.1, hr.2⟩ : unitInterval)
      ({true} : Set Bool)).toReal = _
    simp_rw [htrue]
    rw [ENNReal.toReal_prod]
    simp [unitInterval.coe_toNNReal]
  have hsub : {ω : Config E | OpenEdges γ ω} ⊆ {ω | SomePathOpen Γ ω} := by
    intro ω hω
    exact ⟨γ, hγ, hω⟩
  calc
    r ^ γ.card = μ.event {ω : Config E | OpenEdges γ ω} := hcyl.symm
    _ ≤ μ.event {ω | SomePathOpen Γ ω} := finProb_event_mono μ hsub
    _ = pathEventProbability r hr Γ := rfl

/-- Cardinality form of the path probability bound. -/
theorem pathEventProbability_ge_pow_of_card_le
    {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
    (Γ : Set (Finset E)) (γ : Finset E) (k : ℕ)
    (hγ : γ ∈ Γ) (hcard : γ.card ≤ k) :
    r ^ k ≤ pathEventProbability r hr Γ := by
  calc
    r ^ k ≤ r ^ γ.card := pow_le_pow_of_le_one hr.1 hr.2 hcard
    _ ≤ pathEventProbability r hr Γ := pathEventProbability_ge_pow_of_mem r hr Γ γ hγ

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.cutsetWeight_ge_closedCylinder
#print axioms FK.EnhancedTransport.cutsetWeight_ge_pow
#print axioms FK.EnhancedTransport.cutsetEpsilon_ge_pow
#print axioms FK.EnhancedTransport.cutsetEpsilon_ge_pow_of_card_le
#print axioms FK.EnhancedTransport.finProb_event_mono
#print axioms FK.EnhancedTransport.bernoulliProduct_openCylinder
#print axioms FK.EnhancedTransport.productLaw_event_eq_toReal
#print axioms FK.EnhancedTransport.pathEventProbability_ge_pow_of_mem
#print axioms FK.EnhancedTransport.pathEventProbability_ge_pow_of_card_le
