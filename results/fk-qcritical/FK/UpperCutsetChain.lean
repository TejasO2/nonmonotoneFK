import FK.LowerCutsetChain

/-!
# Exact upper closed-cutset stationary ingredients

This module proves the finite-product restriction identities needed for the
`p' ≤ p` closed-cutset chain.  In particular, its cutset probability depends
only on the auxiliary coordinates, so the enhanced rates can be replaced by
`max p p'` there without changing it.
-/

noncomputable section

local instance (priority := low) upperCutsetPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

open scoped BigOperators ENNReal unitInterval ProbabilityTheory
open Set MeasureTheory

namespace FKEnhancement

/-- Restriction of a Boolean configuration to a decidable set of coordinates. -/
def restrictConfiguration {E : Type*} (s : E → Prop) [DecidablePred s]
    (ω : Configuration E) : Configuration (Subtype s) :=
  fun a => ω a.1

lemma measurable_restrictConfiguration {E : Type*} (s : E → Prop)
    [DecidablePred s] : Measurable (restrictConfiguration s (E := E)) := by
  exact measurable_pi_lambda (fun a => measurable_pi_apply a.1)

/-- The restriction of a product measure is the product over the restricted
coordinates, with the same local Bernoulli laws. -/
theorem bernoulliProduct_map_restrictConfiguration {E : Type*} [Fintype E]
    (rates : E → I) (s : E → Prop) [DecidablePred s] :
    (bernoulliProduct rates).map (restrictConfiguration s) =
      Measure.pi (fun a : Subtype s => Ber(true, false, rates a.1)) := by
  let μ : E → Measure Bool := fun e => Ber(true, false, rates e)
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ s
  have hfst := measurePreserving_fst
    (μ := Measure.pi (fun a : Subtype s => μ a.1))
    (ν := Measure.pi (fun a : Subtype (fun e => ¬ s e) => μ a.1))
  have hcomp := hfst.comp hsplit
  have heq := hcomp.map_eq
  change (Measure.pi μ).map (fun ω (a : Subtype s) => ω a.1) =
    Measure.pi (fun a : Subtype s => μ a.1)
  simpa only [Function.comp_def, MeasurableEquiv.piEquivPiSubtypeProd_apply] using heq

/-- An event pulled back from a coordinate restriction has the same product
probability after changing rates away from those coordinates. -/
theorem bernoulliProduct_restrictConfiguration_preimage_eq
    {E : Type*} [Fintype E] (rates rates' : E → I)
    (s : E → Prop) [DecidablePred s]
    (h : ∀ a, s a → rates a = rates' a)
    (C : Set (Configuration (Subtype s))) :
    bernoulliProduct rates (restrictConfiguration s ⁻¹' C) =
      bernoulliProduct rates' (restrictConfiguration s ⁻¹' C) := by
  have hC : MeasurableSet C := (Set.toFinite C).measurableSet
  rw [← Measure.map_apply (measurable_restrictConfiguration s) hC,
    ← Measure.map_apply (measurable_restrictConfiguration s) hC,
    bernoulliProduct_map_restrictConfiguration,
    bernoulliProduct_map_restrictConfiguration]
  congr 2
  funext a
  rw [h a.1 a.2]

/-- The auxiliary coordinates for an enhanced edge: no enhanced edge and not
that edge itself.  This is exactly the index set in `IsAuxiliary`. -/
def auxiliaryCoordinate {E : Type*} (enhanced : Set E) (e a : E) : Prop :=
  a ∉ enhanced ∧ a ≠ e

/-- A closed-cutset event is the pullback of its restriction to the auxiliary
coordinates.  The proof uses only `IsAuxiliary`, not graph simplicity. -/
theorem restrictConfiguration_preimage_image_certificateEvent
    {E : Type*} (K : E → Configuration E → Prop) (enhanced : Set E) (e : E) :
    restrictConfiguration (auxiliaryCoordinate enhanced e) ⁻¹'
      (restrictConfiguration (auxiliaryCoordinate enhanced e) ''
        certificateEvent K enhanced e) = certificateEvent K enhanced e := by
  classical
  ext ω
  constructor
  · rintro ⟨η, ⟨χ, hχ, hclosed⟩, hηω⟩
    refine ⟨χ, hχ, ?_⟩
    intro a ha
    have ha' : auxiliaryCoordinate enhanced e a := hχ.1 ha
    have heval := congrFun hηω (⟨a, ha'⟩ : Subtype (auxiliaryCoordinate enhanced e))
    change η a = ω a at heval
    rw [← heval]
    exact hclosed a ha
  · intro hω
    exact ⟨ω, hω, rfl⟩

/-- Closed-cutset probabilities are unchanged by arbitrary rate changes away
from the auxiliary coordinates. -/
theorem certificateProbability_congr_auxiliary {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (rates rates' : E → I)
    (h : ∀ a, a ∉ enhanced → a ≠ e → rates a = rates' a) :
    certificateProbability K enhanced e rates =
      certificateProbability K enhanced e rates' := by
  classical
  unfold certificateProbability
  rw [← restrictConfiguration_preimage_image_certificateEvent K enhanced e,
    ← restrictConfiguration_preimage_image_certificateEvent K enhanced e]
  exact congrArg ENNReal.toReal
    (bernoulliProduct_restrictConfiguration_preimage_eq rates rates'
      (auxiliaryCoordinate enhanced e) (fun a ha => h a ha.1 ha.2) _)

end FKEnhancement


namespace FKEnhancement

open FK.Finite.Comparison

/-- Away from the enhanced set and the distinguished edge, the upper enhanced
rate is exactly `max p p' = p` in the `p' ≤ p` direction. -/
theorem upperEnhancedRates_eq_max_auxiliary {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (a : E) (ha : a ∉ enhanced) :
    upperEnhancedRates K enhanced hp a = max p p' := by
  apply Subtype.ext
  simp [upperEnhancedRates, upperEnhancedRate, ha, max_eq_left hp]

/-- The enhanced second marginal has the same closed-cutset probability as the
constant `max(p,p')` product, namely the exact cutset weight. -/
theorem upperEnhancedFinProb_event_certificateEvent {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) :
    (upperEnhancedFinProb K enhanced hp).event (certificateEvent K enhanced e) =
      cutsetWeight K enhanced p p' e := by
  rw [← OpenPath.FinProb.toPMF_event, upperEnhancedFinProb_toMeasure]
  change certificateProbability K enhanced e (upperEnhancedRates K enhanced hp) =
    certificateProbability K enhanced e (fun _ => max p p')
  apply certificateProbability_congr_auxiliary
  intro a ha _
  exact upperEnhancedRates_eq_max_auxiliary K enhanced hp a ha

/-- The same certificate probability read from the second coordinate of the
ordered ordinary/enhanced pair law. -/
theorem upperCutsetPairLaw_event_snd_certificateEvent {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) :
    (upperCutsetPairLaw K enhanced hp).event
      ((fun ω a => (ω a).2) ⁻¹' certificateEvent K enhanced e) =
        cutsetWeight K enhanced p p' e := by
  rw [OpenPath.FinProb.event_preimage_map, upperCutsetPairLaw_map_snd,
    upperEnhancedFinProb_event_certificateEvent]

end FKEnhancement


namespace OpenPath.FinProb

open MeasureTheory

/-- The PMF measure of an indexed finite product is exactly the product of the
coordinate PMF measures. -/
theorem toPMF_pi_toMeasure {E B : Type*} [Fintype E] [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : E → FinProb B) :
    (FinProb.pi ν).toPMF.toMeasure =
      Measure.pi (fun e => (ν e).toPMF.toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro ω
  rw [PMF.toMeasure_apply_singleton _ _ (by simp), Measure.pi_singleton]
  simp only [FinProb.pi_mass, FinProb.toPMF_apply]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro e _
    rw [PMF.toMeasure_apply_singleton _ _ (by simp), FinProb.toPMF_apply]
  · intro e _
    exact (ν e).mass_nonneg (ω e)

/-- Taking an indexed product and then restricting coordinates gives the
indexed product over precisely those coordinates. -/
theorem pi_map_restrict {E B : Type*} [Fintype E] [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (s : E → Prop) [DecidablePred s] (ν : E → FinProb B) :
    (FinProb.pi ν).map (fun ω (a : Subtype s) => ω a.1) =
      FinProb.pi (fun a : Subtype s => ν a.1) := by
  apply FinProb.toPMF_injective
  apply PMF.toMeasure_injective
  rw [FinProb.toPMF_map]
  have hm : Measurable (fun (ω : E → B) (a : Subtype s) => ω a.1) :=
    measurable_pi_lambda (fun a => measurable_pi_apply a.1)
  rw [← PMF.toMeasure_map _ _ hm, toPMF_pi_toMeasure ν]
  let μ : E → Measure B := fun e => (ν e).toPMF.toMeasure
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ s
  have hfst := measurePreserving_fst
    (μ := Measure.pi (fun a : Subtype s => μ a.1))
    (ν := Measure.pi (fun a : Subtype (fun e => ¬ s e) => μ a.1))
  have heq := (hfst.comp hsplit).map_eq
  have hmap : Measure.map (fun (ω : E → B) (a : Subtype s) => ω a.1)
      (Measure.pi μ) = Measure.pi (fun a : Subtype s => μ a.1) := by
    simpa only [Function.comp_def, MeasurableEquiv.piEquivPiSubtypeProd_apply] using heq
  exact hmap.trans (toPMF_pi_toMeasure (fun a : Subtype s => ν a.1)).symm

/-- Event form of `pi_map_restrict`. -/
theorem pi_event_restrict_preimage {E B : Type*} [Fintype E] [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (s : E → Prop) [DecidablePred s] (ν : E → FinProb B)
    (C : Set (Subtype s → B)) :
    (FinProb.pi ν).event ((fun ω (a : Subtype s) => ω a.1) ⁻¹' C) =
      (FinProb.pi (fun a : Subtype s => ν a.1)).event C := by
  rw [FinProb.event_preimage_map, pi_map_restrict]

end OpenPath.FinProb


namespace OpenPath.FinProb

/-- Reindex an indexed finite product along an equivalence of coordinates. -/
theorem pi_map_equiv {R S B : Type*} [Fintype R] [Fintype S] [Fintype B]
    [DecidableEq R] [DecidableEq S] (D : R ≃ S) (ν : R → FinProb B) :
    (FinProb.pi (fun j => ν (D.symm j))).map (fun ω i => ω (D i)) =
      FinProb.pi ν := by
  classical
  let F : (S → B) ≃ (R → B) :=
    { toFun := fun ω i => ω (D i)
      invFun := fun ω j => ω (D.symm j)
      left_inv := by intro ω; funext j; simp
      right_inv := by intro ω; funext i; simp }
  have hF : (fun ω i => ω (D i)) = F := rfl
  rw [hF]
  apply FinProb.ext
  intro ω
  rw [FinProb.mass_map_equiv F]
  change (∏ j, (ν (D.symm j)).mass (ω (D.symm j))) = _
  exact D.symm.prod_comp (fun i => (ν i).mass (ω i))

end OpenPath.FinProb

namespace FKEnhancement

/-- The finset form of the auxiliary-edge predicate (apart from removal of the
distinguished edge, which is already present in `AuxiliaryIndex`). -/
def auxiliaryEnhancedFinset {E : Type*} [Fintype E] (enhanced : Set E) : Finset E :=
  Finset.univ.filter (fun a => a ∉ enhanced)

/-- The nested auxiliary index used by `JointInvariance` is equivalent to the
flat auxiliary coordinate subtype used by `CutsetFamily`. -/
def auxiliaryIndexEquiv {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Set E) (e : E) :
    JointInvariance.AuxiliaryIndex E e (auxiliaryEnhancedFinset enhanced) ≃
      Subtype (auxiliaryCoordinate enhanced e) where
  toFun a := ⟨a.1.1, by
    refine ⟨?_, a.1.2⟩
    have ha := a.2
    simpa [auxiliaryEnhancedFinset] using ha⟩
  invFun a := ⟨⟨a.1, a.2.2⟩, by
    simpa [auxiliaryEnhancedFinset] using a.2.1⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl

end FKEnhancement


namespace FKEnhancement

open FK.Finite.Comparison

/-- The local factor of `upperCutsetPairLaw`: ordinary `p'` below the exact
upper enhanced rate. -/
def upperCutsetFactor {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (a : E) : OpenPath.FinProb (Bool × Bool) :=
  boolPair p' (upperEnhancedRate K enhanced p p' a) p'.2.1
    (upperEnhancedRate_ge_of_ge K enhanced hp a)
    (upperEnhancedRate_le_one K enhanced hp a)

lemma upperCutsetFactor_map_snd_of_not_mem {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) {a : E} (ha : a ∉ enhanced) :
    (upperCutsetFactor K enhanced hp a).map Prod.snd =
      FK.Finite.Comparison.boolLaw (p : ℝ) p.2 := by
  unfold upperCutsetFactor
  rw [boolPair_snd]
  congr 1
  simp [upperEnhancedRate, ha]

/-- The second configuration on the flat auxiliary subtype, obtained from the
nested indexed-block auxiliary configuration. -/
def auxiliarySecondConfiguration {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Set E) (e : E)
    (ω : JointInvariance.AuxiliaryIndex E e (auxiliaryEnhancedFinset enhanced) →
      Bool × Bool) : Configuration (Subtype (auxiliaryCoordinate enhanced e)) :=
  fun a => (ω ((auxiliaryIndexEquiv enhanced e).symm a)).2

/-- The closed-cutset event in the precise auxiliary block used by the
stationary invariance theorem. -/
def auxiliaryCutsetEvent {E : Type*} [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E) :
    Set (JointInvariance.AuxiliaryIndex E e (auxiliaryEnhancedFinset enhanced) →
      Bool × Bool) :=
  auxiliarySecondConfiguration enhanced e ⁻¹'
    (restrictConfiguration (auxiliaryCoordinate enhanced e) ''
      certificateEvent K enhanced e)

/-- Restricting the full ordinary/upper-enhanced product pair to its auxiliary
second coordinates gives exactly the constant `p` product. -/
theorem upperCutsetPairLaw_map_restrict_snd {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) :
    (upperCutsetPairLaw K enhanced hp).map
      (fun ω (a : Subtype (auxiliaryCoordinate enhanced e)) => (ω a.1).2) =
      boolProduct (fun _ : Subtype (auxiliaryCoordinate enhanced e) => (p : ℝ))
        (fun _ => p.2) := by
  classical
  let ν := upperCutsetFactor K enhanced hp
  let f : (Subtype (auxiliaryCoordinate enhanced e) → Bool × Bool) →
      Configuration (Subtype (auxiliaryCoordinate enhanced e)) :=
    fun ω a => (ω a).2
  have h := congrArg (fun L : OpenPath.FinProb
      (Subtype (auxiliaryCoordinate enhanced e) → Bool × Bool) => L.map f)
    (OpenPath.FinProb.pi_map_restrict (auxiliaryCoordinate enhanced e) ν)
  rw [GlauberCoupling.map_map, OpenPath.FinProb.pi_map] at h
  change ((OpenPath.FinProb.pi ν).map
    (fun ω (a : Subtype (auxiliaryCoordinate enhanced e)) => (ω a.1).2)) = _
  refine h.trans ?_
  unfold boolProduct
  congr 1
  funext a
  exact upperCutsetFactor_map_snd_of_not_mem K enhanced hp a.2.1

/-- The nested block auxiliary product has the same constant-`p` second law,
after transport along `auxiliaryIndexEquiv`. -/
theorem upperAuxiliaryPairLaw_map_snd {E : Type*} [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) :
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      (auxiliaryEnhancedFinset enhanced) => upperCutsetFactor K enhanced hp a.1.1)).map
      (auxiliarySecondConfiguration enhanced e) =
      boolProduct (fun _ : Subtype (auxiliaryCoordinate enhanced e) => (p : ℝ))
        (fun _ => p.2) := by
  let ν : Subtype (auxiliaryCoordinate enhanced e) →
      OpenPath.FinProb (Bool × Bool) :=
    fun a => upperCutsetFactor K enhanced hp a.1
  let f : (Subtype (auxiliaryCoordinate enhanced e) → Bool × Bool) →
      Configuration (Subtype (auxiliaryCoordinate enhanced e)) :=
    fun ω a => (ω a).2
  have hEq :
      (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
        (auxiliaryEnhancedFinset enhanced) => upperCutsetFactor K enhanced hp a.1.1)).map
        (fun ω a => ω ((auxiliaryIndexEquiv enhanced e).symm a)) =
        OpenPath.FinProb.pi ν := by
    exact OpenPath.FinProb.pi_map_equiv (auxiliaryIndexEquiv enhanced e).symm ν
  have h := congrArg (fun L : OpenPath.FinProb
      (Subtype (auxiliaryCoordinate enhanced e) → Bool × Bool) => L.map f) hEq
  rw [GlauberCoupling.map_map, OpenPath.FinProb.pi_map] at h
  change (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      (auxiliaryEnhancedFinset enhanced) => upperCutsetFactor K enhanced hp a.1.1)).map
      (auxiliarySecondConfiguration enhanced e) = _
  refine h.trans ?_
  unfold boolProduct
  congr 1
  funext a
  exact upperCutsetFactor_map_snd_of_not_mem K enhanced hp a.2.1

/-- The actual auxiliary-block certificate probability is the cutset weight. -/
theorem upperAuxiliaryCutsetEvent_probability {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) :
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      (auxiliaryEnhancedFinset enhanced) => upperCutsetFactor K enhanced hp a.1.1)).event
      (auxiliaryCutsetEvent K enhanced e) = cutsetWeight K enhanced p p' e := by
  have hpre :
      (fun (ω : E → Bool × Bool) (a : Subtype (auxiliaryCoordinate enhanced e)) =>
        (ω a.1).2) ⁻¹'
        (restrictConfiguration (auxiliaryCoordinate enhanced e) ''
          certificateEvent K enhanced e) =
      (fun (ω : E → Bool × Bool) a => (ω a).2) ⁻¹' certificateEvent K enhanced e := by
    ext ω
    change restrictConfiguration (auxiliaryCoordinate enhanced e)
      (fun a => (ω a).2) ∈ restrictConfiguration (auxiliaryCoordinate enhanced e) ''
        certificateEvent K enhanced e ↔ HasClosedCutset K enhanced e (fun a => (ω a).2)
    have hmem := Set.ext_iff.mp
      (restrictConfiguration_preimage_image_certificateEvent K enhanced e)
      (fun a => (ω a).2)
    exact hmem
  have hfull := upperCutsetPairLaw_event_snd_certificateEvent K enhanced hp e
  rw [← hpre, OpenPath.FinProb.event_preimage_map,
    upperCutsetPairLaw_map_restrict_snd] at hfull
  rw [auxiliaryCutsetEvent, OpenPath.FinProb.event_preimage_map,
    upperAuxiliaryPairLaw_map_snd]
  exact hfull

end FKEnhancement


namespace FKEnhancement

open FK.Finite.Comparison
open scoped unitInterval

/-- Full exact stationarity of the ordinary `p'` / upper-enhanced pair under
one enhanced cutset update followed by a complete auxiliary refresh. -/
theorem upperCutsetPairLaw_enhancedBlock_invariant {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) {e : E} (he : e ∈ enhanced) :
    (upperCutsetPairLaw K enhanced hp).bind
      (JointInvariance.transportedBlockKernel
        (JointInvariance.indexedBlockEquiv e (auxiliaryEnhancedFinset enhanced))
        (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
          (auxiliaryEnhancedFinset enhanced) => upperCutsetFactor K enhanced hp a.1.1))
        (fun a => if a ∈ auxiliaryCutsetEvent K enhanced e then
          boolPair p' p' p'.2.1 le_rfl p'.2.2
          else boolPair p' p p'.2.1 hp p.2.2)) = upperCutsetPairLaw K enhanced hp := by
  change (OpenPath.FinProb.pi (upperCutsetFactor K enhanced hp)).bind _ = _
  apply pi_upperBoolPair_invariant
  have hprob := upperAuxiliaryCutsetEvent_probability K enhanced hp e
  simp only [hprob]
  simp only [upperCutsetFactor, upperEnhancedRate, he, if_true, cutsetEpsilon]

end FKEnhancement


namespace FKEnhancement

open Set
open FK.Finite.Comparison
open scoped unitInterval

/-- Restriction to any indexed block of the upper local product has the
corresponding indexed product law. -/
lemma upperCutset_auxiliaryRestriction_map {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) (A : Finset E) :
    (OpenPath.FinProb.pi (upperCutsetFactor K enhanced hp)).map
      (fun w => ((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A) w).1.2) =
      OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
        upperCutsetFactor K enhanced hp a.1.1) := by
  let D := JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A
  let ν := upperCutsetFactor K enhanced hp
  have hdecomp := JointInvariance.map_pi_indexedBlockEquiv ν e A
  change (OpenPath.FinProb.pi ν).map D = JointInvariance.blockLaw (ν e)
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
    (OpenPath.FinProb.pi (fun r : JointInvariance.RemainingIndex E e A => ν r.1.1))
    at hdecomp
  change (OpenPath.FinProb.pi ν).map (fun w => (D w).1.2) = _
  rw [show (fun w => (D w).1.2) = (fun t => t.1.2) ∘ D from rfl,
    ← GlauberCoupling.map_map, hdecomp]
  change ((((ν e).prod (OpenPath.FinProb.pi
      (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))).prod
      (OpenPath.FinProb.pi (fun r : JointInvariance.RemainingIndex E e A => ν r.1.1))).map
      (fun t => t.1.2)) = _
  rw [show (fun t : ((Bool × Bool) ×
      (JointInvariance.AuxiliaryIndex E e A → Bool × Bool)) ×
      (JointInvariance.RemainingIndex E e A → Bool × Bool) => t.1.2) =
      Prod.snd ∘ Prod.fst from rfl, ← GlauberCoupling.map_map]
  simp
  rfl

/-- The actual certificate average of an upper enhanced block is its exact
cutset weight, for every valid auxiliary enumeration. -/
theorem upperCutset_auxCertificate_event {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) (auxiliary : List E)
    (hA : ∀ f, f ∈ auxiliary ↔ f ∉ enhanced) :
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      auxiliary.toFinset => upperCutsetFactor K enhanced hp a.1.1)).event
      {a | HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset a)} =
        cutsetWeight K enhanced p p' e := by
  let D := JointInvariance.indexedBlockEquiv (β := Bool × Bool) e auxiliary.toFinset
  let ν := upperCutsetFactor K enhanced hp
  let R := fun w : E → Bool × Bool => (D w).1.2
  let U := fun w : E → Bool × Bool => fun e => (w e).2
  let C : Set (JointInvariance.AuxiliaryIndex E e auxiliary.toFinset → Bool × Bool) :=
    {a | HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset a)}
  have haux : (OpenPath.FinProb.pi ν).map R =
      OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e auxiliary.toFinset =>
        ν a.1.1) := upperCutset_auxiliaryRestriction_map K enhanced hp e auxiliary.toFinset
  have hupper : (OpenPath.FinProb.pi ν).map U = upperEnhancedFinProb K enhanced hp := by
    have h := upperCutsetPairLaw_map_snd K enhanced hp
    exact h
  have hevent : R ⁻¹' C = U ⁻¹' certificateEvent K enhanced e := by
    ext w
    change HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset (R w)) ↔
      HasClosedCutset K enhanced e (U w)
    apply hasClosedCutset_congr_of_aux_eq
    intro a hae haee
    have haA : a ∈ auxiliary.toFinset := List.mem_toFinset.mpr ((hA a).mpr hae)
    rw [pairAuxiliaryUpper_apply e auxiliary.toFinset (R w) a haee haA]
    rfl
  change (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
    auxiliary.toFinset => ν a.1.1)).event C = cutsetWeight K enhanced p p' e
  calc
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      auxiliary.toFinset => ν a.1.1)).event C =
        ((OpenPath.FinProb.pi ν).map R).event C := by rw [haux]
    _ = (OpenPath.FinProb.pi ν).event (R ⁻¹' C) := by
      rw [OpenPath.FinProb.event_preimage_map]
    _ = (OpenPath.FinProb.pi ν).event (U ⁻¹' certificateEvent K enhanced e) := by
      rw [hevent]
    _ = ((OpenPath.FinProb.pi ν).map U).event (certificateEvent K enhanced e) := by
      rw [OpenPath.FinProb.event_preimage_map]
    _ = (upperEnhancedFinProb K enhanced hp).event
        (certificateEvent K enhanced e) := by rw [hupper]
    _ = cutsetWeight K enhanced p p' e :=
      upperEnhancedFinProb_event_certificateEvent K enhanced hp e

/-- Singleton conditionals for the actual upper ordered pair dynamics. -/
def upperCutsetPairConditionals {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) : Glauber.EdgeConditionals (Bool × Bool) E := by
  classical
  exact fun e off =>
    if e ∈ enhanced then
      cutsetOuterPairLaw K enhanced e p p' (pairUpperOff e off)
    else upperCutsetFactor K enhanced hp e

/-- The enhanced upper kernel expressed using only the transported auxiliary
configuration. -/
def upperCutsetAuxKernel {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) (A : Finset E)
    (a : JointInvariance.AuxiliaryIndex E e A → Bool × Bool) :
    OpenPath.FinProb (Bool × Bool) := by
  classical
  exact if HasClosedCutset K enhanced e (pairAuxiliaryUpper e A a) then
    boolPair p' p' p'.2.1 le_rfl p'.2.2
  else boolPair p' p p'.2.1 hp p.2.2

lemma upperCutsetPairConditionals_enhanced_aux {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) (he : e ∈ enhanced) (auxiliary : List E)
    (hA : ∀ f, f ∈ auxiliary ↔ f ∉ enhanced) (ω : E → Bool × Bool) :
    upperCutsetPairConditionals K enhanced hp e (fun a => ω a.1) =
      upperCutsetAuxKernel K enhanced hp e auxiliary.toFinset
        (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e
          auxiliary.toFinset) ω).1.2) := by
  simp only [upperCutsetPairConditionals, if_pos he]
  unfold cutsetOuterPairLaw upperCutsetAuxKernel
  have hc : HasClosedCutset K enhanced e (pairUpperOff e (fun a => ω a.1)) ↔
      HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset
        (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e
          auxiliary.toFinset) ω).1.2)) := by
    apply hasClosedCutset_congr_of_aux_eq
    intro a hae haee
    have haA : a ∈ auxiliary.toFinset := List.mem_toFinset.mpr ((hA a).mpr hae)
    rw [pairUpperOff_apply_aux e ω a haee,
      pairAuxiliaryUpper_apply e auxiliary.toFinset _ a haee haA]
    rfl
  split_ifs <;> simp_all [min_eq_right hp, max_eq_left hp]

lemma upperCutsetPairConditionals_not_enhanced {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) (he : e ∉ enhanced) (off) :
    upperCutsetPairConditionals K enhanced hp e off = upperCutsetFactor K enhanced hp e := by
  simp [upperCutsetPairConditionals, he]

lemma upperCutsetPairLaw_eq_pi {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) :
    upperCutsetPairLaw K enhanced hp =
      OpenPath.FinProb.pi (upperCutsetFactor K enhanced hp) := by
  unfold upperCutsetPairLaw
  congr 1

end FKEnhancement


namespace FKEnhancement

open Set
open FK.Finite.Comparison
open scoped unitInterval

/-- Invariance of the ordinary/upper-enhanced pair under an actual enhanced
sequential FK block update. -/
theorem upperCutsetPairLaw_enhancedBlockUpdate_invariant {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary)
    (e : E) (he : e ∈ enhanced) :
    Glauber.Invariant (upperCutsetPairLaw K enhanced hp)
      (Glauber.blockUpdate (upperCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e) := by
  let ν := upperCutsetFactor K enhanced hp
  let A := auxiliary.toFinset
  let C : Set (JointInvariance.AuxiliaryIndex E e A → Bool × Bool) :=
    {a | HasClosedCutset K enhanced e (pairAuxiliaryUpper e A a)}
  have hA : ∀ f, f ∈ auxiliary ↔ f ∉ enhanced := by
    intro f
    rw [haux.2 f]
    simp
  have he' : e ∈ enhanced.toFinset := Set.mem_toFinset.mpr he
  have heaux : e ∉ auxiliary := by
    intro h
    exact (hA e).mp h he
  have hC : (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
      ν a.1.1)).event C = cutsetWeight K enhanced p p' e := by
    exact upperCutset_auxCertificate_event K enhanced hp e auxiliary hA
  have hνe : ν e = boolPair p'
      ((p : ℝ) - closedCutsetEnhancement p p'
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event C)) p'.2.1
      (enhancedOpenRate_bounds_of_ge p.2.2 p'.2.1 hp
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).2).1
      (((enhancedOpenRate_bounds_of_ge p.2.2 p'.2.1 hp
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).2).2).trans p.2.2) := by
    change upperCutsetFactor K enhanced hp e = _
    apply OpenPath.FinProb.ext
    rintro ⟨i, j⟩
    cases i <;> cases j <;>
      simp [boolPair, upperCutsetFactor, upperEnhancedRate, he, cutsetEpsilon, hC]
  have hstat := pi_upperBoolPair_invariant ν e A C (p : ℝ) (p' : ℝ)
    p'.2.1 p.2.2 hp hνe
  have hc : ∀ f ∈ auxiliary, ∀ off,
      upperCutsetPairConditionals K enhanced hp f off = ν f := by
    intro f hf off
    exact upperCutsetPairConditionals_not_enhanced K enhanced hp f ((hA f).mp hf) off
  have hκ : ∀ ω : E → Bool × Bool,
      upperCutsetPairConditionals K enhanced hp e (fun a => ω a.1) =
        upperCutsetAuxKernel K enhanced hp e A
          (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A) ω).1.2) := by
    intro ω
    exact upperCutsetPairConditionals_enhanced_aux K enhanced hp e he auxiliary hA ω
  have hlift := Glauber.dirac_blockUpdate_eq_transportedBlockKernel
    (upperCutsetPairConditionals K enhanced hp) ν enhanced.toFinset e he' auxiliary
    haux.1 heaux hc (upperCutsetAuxKernel K enhanced hp e A) hκ
  unfold Glauber.Invariant
  rw [upperCutsetPairLaw_eq_pi]
  change (OpenPath.FinProb.pi ν).bind _ = OpenPath.FinProb.pi ν
  calc
    (OpenPath.FinProb.pi ν).bind
        (Glauber.blockUpdate (upperCutsetPairConditionals K enhanced hp)
          enhanced.toFinset auxiliary e) =
      (OpenPath.FinProb.pi ν).bind
        (JointInvariance.transportedBlockKernel
          (JointInvariance.indexedBlockEquiv e A)
          (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
          (upperCutsetAuxKernel K enhanced hp e A)) := by
      congr 1
      funext ω
      simpa using hlift ω
    _ = OpenPath.FinProb.pi ν := by
      change (OpenPath.FinProb.pi ν).bind
        (JointInvariance.transportedBlockKernel
          (JointInvariance.indexedBlockEquiv e A)
          (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
          (fun a => if HasClosedCutset K enhanced e (pairAuxiliaryUpper e A a) then
            boolPair p' p' p'.2.1 le_rfl p'.2.2
            else boolPair p' p p'.2.1 hp p.2.2)) = OpenPath.FinProb.pi ν
      simpa [C] using hstat

/-- The upper ordered product is invariant for every actual modified-block
clock update, including the ordinary nonenhanced clocks. -/
theorem upperCutsetPairLaw_blockUpdate_invariant {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) (e : E) :
    Glauber.Invariant (upperCutsetPairLaw K enhanced hp)
      (Glauber.blockUpdate (upperCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e) := by
  by_cases he : e ∈ enhanced
  · exact upperCutsetPairLaw_enhancedBlockUpdate_invariant K enhanced hp auxiliary haux e he
  · let ν := upperCutsetFactor K enhanced hp
    unfold Glauber.Invariant
    rw [upperCutsetPairLaw_eq_pi]
    change (OpenPath.FinProb.pi ν).bind _ = OpenPath.FinProb.pi ν
    have hblock : Glauber.blockUpdate (upperCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e =
        Glauber.edgeUpdate (upperCutsetPairConditionals K enhanced hp) e := by
      simp [Glauber.blockUpdate, Glauber.blockCoordinates, he, Glauber.sweep_singleton]
    rw [hblock, Glauber.pi_bind_edgeUpdate_const ν
      (upperCutsetPairConditionals K enhanced hp) e (ν e)
      (upperCutsetPairConditionals_not_enhanced K enhanced hp e he)]
    simp

/-- Exact stationary pair equation for the upper modified jump chain. -/
theorem upperCutsetPairLaw_modifiedJump_invariant {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) :
    Glauber.Invariant (upperCutsetPairLaw K enhanced hp)
      (Glauber.modifiedJump ρ (upperCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary) := by
  apply Glauber.mixture_invariant
  intro e
  exact upperCutsetPairLaw_blockUpdate_invariant K enhanced hp auxiliary haux e

end FKEnhancement
