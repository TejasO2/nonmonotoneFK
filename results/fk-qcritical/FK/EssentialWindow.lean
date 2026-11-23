import FK.Theorem14
import FK.Proposition42
import CurvatureVariance.Infra.Percolation.Critical
import PercLib.Probability.Coupling.Monotone

/-!
# From a strict enhanced critical point to a parameter window

This module uses the correct open-edge convention of `FKLimit.bernoulliProduct`:
`true` has probability `r e`.  It transports the existing `PercLib` ordered
coupling to Boolean configurations and uses it to extend subcriticality and
supercriticality from one inhomogeneous reference law to a whole window.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement

noncomputable section

/-- The open-set pushforward of the Boolean inhomogeneous product law is the
`PercLib` product law with the same parameters. -/
theorem map_openSet_bernoulliProduct {E : Type*} (r : E → unitInterval) :
    Measure.map openSet (FKLimit.bernoulliProduct r : Measure (E → Bool)) =
      PercLib.Probability.prodBernoulli r := by
  change Measure.map openSet (Measure.infinitePi fun e ↦ bernoulliMeasure true false (r e)) = _
  rw [PercLib.Probability.prodBernoulli_eq_map]
  have hf : Measurable (fun (ω : E → Bool) (e : E) ↦ ω e = true) :=
    measurable_pi_iff.2 fun e ↦
      (Measurable.of_discrete (f := fun b : Bool ↦ b = true)).comp (measurable_pi_apply e)
  have hcomp : (openSet : (E → Bool) → Set E) =
      MeasurableEquiv.setOfPred ∘ (fun ω e ↦ ω e = true) := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable hf]
  have hpi := Measure.infinitePi_map_pi
    (fun e : E ↦ bernoulliMeasure true false (r e))
    (f := fun _ (b : Bool) ↦ b = true) (fun _ ↦ Measurable.of_discrete)
  have hmaps : (fun e : E ↦ Measure.map (fun b : Bool ↦ b = true)
      (bernoulliMeasure true false (r e))) =
      (fun e : E ↦ bernoulliMeasure True False (r e)) := by
    funext e
    rw [map_bernoulliMeasure' _ _ Measurable.of_discrete]
    simp
  rw [hmaps] at hpi
  exact congrArg (Measure.map (MeasurableEquiv.setOfPred : (E → Prop) ≃ᵐ Set E)) hpi

/-- Pointwise order of Boolean configurations is inclusion of their open sets. -/
theorem config_le_of_openSet_subset {E : Type*} {ω η : E → Bool}
    (h : openSet ω ⊆ openSet η) : ω ≤ η := by
  intro e
  cases hω : ω e
  · exact bot_le
  · have he : e ∈ openSet η := h (by simp [openSet, hω])
    have hetrue : η e = true := by simpa [openSet] using he
    rw [hetrue]

/-- Evaluating the Boolean product law on `A` is evaluation of the set-product
law on the image of `A` under open sets. -/
theorem bernoulliProduct_apply_image {E : Type*} (r : E → unitInterval)
    (A : Set (E → Bool)) :
    (FKLimit.bernoulliProduct r : Measure (E → Bool)) A =
      PercLib.Probability.prodBernoulli r (openSet '' A) := by
  have hpre : openSet ⁻¹' (openSet '' A) = A := by
    ext ω
    constructor
    · rintro ⟨η, hη, heq⟩
      have hηω : η = ω := openSetEquiv.injective heq
      simpa [hηω] using hη
    · intro hω
      exact ⟨ω, hω, rfl⟩
  calc
    (FKLimit.bernoulliProduct r : Measure (E → Bool)) A =
        Measure.map openSet (FKLimit.bernoulliProduct r : Measure (E → Bool))
          (openSet '' A) := by
      have happly := openSetEquiv.map_apply
        (μ := (FKLimit.bernoulliProduct r : Measure (E → Bool))) (openSet '' A)
      change Measure.map openSet (FKLimit.bernoulliProduct r : Measure (E → Bool))
        (openSet '' A) = (FKLimit.bernoulliProduct r : Measure (E → Bool))
          (openSet ⁻¹' (openSet '' A)) at happly
      rw [hpre] at happly
      exact happly.symm
    _ = PercLib.Probability.prodBernoulli r (openSet '' A) := by
      rw [map_openSet_bernoulliProduct]

/-- Larger coordinate probabilities stochastically dominate smaller ones on
measurable increasing Boolean events. -/
theorem stochasticallyDominates_bernoulliProduct_of_le {E : Type*} [Countable E]
    {r s : E → unitInterval} (hrs : r ≤ s) :
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct s) (FKLimit.bernoulliProduct r) := by
  intro A hA hAup
  have hBmeas : MeasurableSet (openSet '' A) :=
    openSetEquiv.measurableSet_image.mpr hA
  have hBup : IsUpperSet (openSet '' A) := by
    rintro S T hST ⟨ω, hωA, rfl⟩
    let η : E → Bool := openSetEquiv.symm T
    have hη : openSet η = T := openSetEquiv.right_inv T
    have hωη : ω ≤ η := config_le_of_openSet_subset (by simpa [hη] using hST)
    exact ⟨η, hAup hωη hωA, hη⟩
  change ((FKLimit.bernoulliProduct r : Measure (E → Bool)) A).toNNReal ≤
    ((FKLimit.bernoulliProduct s : Measure (E → Bool)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [bernoulliProduct_apply_image, bernoulliProduct_apply_image]
  exact PercLib.Probability.prodBernoulli_mono_event r s hrs hBmeas hBup

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open Set MeasureTheory ProbabilityTheory CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- Stochastic domination in the `FKLimit` formulation, converted back to an
inequality between the underlying `ENNReal` measures. -/
theorem measure_le_of_stochasticallyDominates {E : Type*} {ν μ : ProbabilityMeasure (E → Bool)}
    (hdom : FKLimit.StochasticallyDominates ν μ) {A : Set (E → Bool)}
    (hmeas : MeasurableSet A) (hA : IsUpperSet A) :
    (μ : Measure (E → Bool)) A ≤ (ν : Measure (E → Bool)) A := by
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact hdom A hmeas hA

/-- A nonpercolating upper law forces every dominated law to assign zero to an
increasing event. -/
theorem measure_eq_zero_of_stochasticallyDominates {E : Type*} {ν μ : ProbabilityMeasure (E → Bool)}
    (hdom : FKLimit.StochasticallyDominates ν μ) {A : Set (E → Bool)}
    (hmeas : MeasurableSet A) (hA : IsUpperSet A)
    (hν : (ν : Measure (E → Bool)) A = 0) : (μ : Measure (E → Bool)) A = 0 := by
  apply le_antisymm _ bot_le
  simpa [hν] using measure_le_of_stochasticallyDominates hdom hmeas hA

/-- A supercritical lower law forces every law dominating it to assign one to an
increasing event. -/
theorem measure_eq_one_of_stochasticallyDominates {E : Type*} {ν μ : ProbabilityMeasure (E → Bool)}
    (hdom : FKLimit.StochasticallyDominates μ ν) {A : Set (E → Bool)}
    (hmeas : MeasurableSet A) (hA : IsUpperSet A)
    (hν : (ν : Measure (E → Bool)) A = 1) : (μ : Measure (E → Bool)) A = 1 := by
  apply le_antisymm prob_le_one
  simpa [hν] using measure_le_of_stochasticallyDominates hdom hmeas hA

/-- Base parameter `b`, decreased by `ε` exactly on `S`. -/
def decrementProfile {E : Type*} (S : Set E) (b ε : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hε0 : 0 ≤ ε) (hεb : ε ≤ b) : E → unitInterval :=
  fun e ↦ if e ∈ S then
    ⟨b - ε, sub_nonneg.mpr hεb, by linarith⟩ else ⟨b, hb0, hb1⟩

/-- Base parameter `a`, increased by `ε` exactly on `S`. -/
def incrementProfile {E : Type*} (S : Set E) (a ε : ℝ)
    (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε) (haε1 : a + ε ≤ 1) : E → unitInterval :=
  fun e ↦ if e ∈ S then
    ⟨a + ε, add_nonneg ha0 hε0, haε1⟩ else ⟨a, ha0, by linarith⟩

/-- The intended upper-window predicate, using the product law whose `true`
coordinate has probability `r e`. -/
def UpperWindow {E : Type*} (A : Set (E → Bool)) (pc : ℝ)
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) : Prop :=
  ∃ δ' > 0, ∀ p (hp : p ∈ Icc (0 : ℝ) 1),
    max p (fkPrime p q) < pc + δ' →
    (FKLimit.bernoulliProduct (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq) :
      Measure (E → Bool)) A = 0

/-- The intended lower-window predicate, using the product law whose `true`
coordinate has probability `r e`. -/
def LowerWindow {E : Type*} (A : Set (E → Bool)) (pc : ℝ)
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) : Prop :=
  ∃ δ > 0, ∀ p (hp : p ∈ Icc (0 : ℝ) 1),
    pc - δ < min p (fkPrime p q) →
    (FKLimit.bernoulliProduct (FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq) :
      Measure (E → Bool)) A = 1

/-- One subcritical decrement law and a uniform path-enhancement bound give the
full upper parameter window when `q < 1`. -/
theorem upperWindow_of_decrementProfile_q_lt_one {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 ≤ pc)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (b ε : ℝ) (K : Set ℝ) (hpcb : pc < b) (hb1 : b ≤ 1) (hε0 : 0 < ε) (hεb : ε ≤ b)
    (hcover : ∀ p (_hp : p ∈ Icc (0 : ℝ) 1), max p (fkPrime p q) < b →
      b - ε < fkPrime p q → p ∈ K)
    (href : (FKLimit.bernoulliProduct
      (decrementProfile Ee b ε (hpc0.trans hpcb.le) hb1 hε0.le hεb) :
        Measure (E → Bool)) A = 0)
    (henh : ∀ p ∈ K, ε ≤ pathEnhancement p q m) :
    UpperWindow A pc Eb Ee n m q hq := by
  have hb0 : 0 ≤ b := hpc0.trans hpcb.le
  refine ⟨b - pc, sub_pos.mpr hpcb, ?_⟩
  intro p hp hpwindow
  have hpwindow' : max p (fkPrime p q) < b := by linarith
  have hp'b : fkPrime p q < b :=
    (le_max_right p (fkPrime p q)).trans_lt hpwindow'
  have hple : p ≤ fkPrime p q := le_fkPrime_of_q_le_one hp.1 hp.2 hq hq1.le
  have hle : FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq ≤
      decrementProfile Ee b ε hb0 hb1 hε0.le hεb := by
    intro e
    change FK.Phases.upperWeightsReal Eb Ee n m p q e ≤
      ((decrementProfile Ee b ε hb0 hb1 hε0.le hεb e : unitInterval) : ℝ)
    rw [FK.Phases.upperWeightsReal_of_le hple]
    by_cases he : e ∈ Ee
    · simp only [decrementProfile, if_pos he]
      by_cases hbase : fkPrime p q ≤ b - ε
      · have heps0 := pathEnhancement_nonneg hp.1 hp.2 hq m
        linarith
      · have heps := henh p (hcover p hp hpwindow' (lt_of_not_ge hbase))
        linarith
    · simp only [decrementProfile, if_neg he, sub_zero]
      exact hp'b.le
  exact measure_eq_zero_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA href

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open Set MeasureTheory ProbabilityTheory CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- One subcritical decrement law and a uniform cutset-enhancement bound give
the full upper parameter window when `1 < q`. -/
theorem upperWindow_of_decrementProfile_one_lt_q {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q) (hpc0 : 0 ≤ pc)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (b ε : ℝ) (K : Set ℝ) (hpcb : pc < b) (hb1 : b ≤ 1) (hε0 : 0 < ε) (hεb : ε ≤ b)
    (hcover : ∀ p (_hp : p ∈ Icc (0 : ℝ) 1), max p (fkPrime p q) < b →
      b - ε < p → p ∈ K)
    (href : (FKLimit.bernoulliProduct
      (decrementProfile Eb b ε (hpc0.trans hpcb.le) hb1 hε0.le hεb) :
        Measure (E → Bool)) A = 0)
    (henh : ∀ p ∈ K, ε ≤ cutsetEnhancement p q n) :
    UpperWindow A pc Eb Ee n m q hq := by
  have hb0 : 0 ≤ b := hpc0.trans hpcb.le
  refine ⟨b - pc, sub_pos.mpr hpcb, ?_⟩
  intro p hp hpwindow
  have hpwindow' : max p (fkPrime p q) < b := by linarith
  have hle : FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq ≤
      decrementProfile Eb b ε hb0 hb1 hε0.le hεb := by
    by_cases hp0 : p = 0
    · subst p
      intro e
      change FK.Phases.upperWeightsReal Eb Ee n m 0 q e ≤
        ((decrementProfile Eb b ε hb0 hb1 hε0.le hεb e : unitInterval) : ℝ)
      rw [FK.Phases.upperWeightsReal_of_le (fkPrime_nonneg le_rfl zero_le_one hq)]
      simp [fkPrime, pathEnhancement, decrementProfile]
      split_ifs <;> linarith
    · by_cases hp1 : p = 1
      · subst p
        have hfk : fkPrime 1 q = 1 := by simp [fkPrime]
        rw [hfk] at hpwindow'
        have : (1 : ℝ) < b := (le_max_left 1 1).trans_lt hpwindow'
        linarith
      · have hp0pos : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
        have hp1lt : p < 1 := lt_of_le_of_ne hp.2 hp1
        have hplt : fkPrime p q < p := (fkPrime_lt_iff hp0pos hp1lt hq).2 hq1
        have hpb : p < b := (le_max_left p (fkPrime p q)).trans_lt hpwindow'
        intro e
        change FK.Phases.upperWeightsReal Eb Ee n m p q e ≤
          ((decrementProfile Eb b ε hb0 hb1 hε0.le hεb e : unitInterval) : ℝ)
        rw [FK.Phases.upperWeightsReal_of_ge hplt]
        by_cases he : e ∈ Eb
        · simp only [decrementProfile, if_pos he]
          by_cases hbase : p ≤ b - ε
          · have heps0 := cutsetEnhancement_nonneg hp.1 hp.2 hq n
            linarith
          · have heps := henh p (hcover p hp hpwindow' (lt_of_not_ge hbase))
            linarith
        · simp only [decrementProfile, if_neg he, sub_zero]
          exact hpb.le
  exact measure_eq_zero_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA href

/-- One supercritical increment law and a uniform cutset-enhancement bound give
the full lower parameter window when `q < 1`. -/
theorem lowerWindow_of_incrementProfile_q_lt_one {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (a ε : ℝ) (K : Set ℝ) (hapc : a < pc) (ha0 : 0 ≤ a) (hε0 : 0 < ε)
    (haε1 : a + ε ≤ 1)
    (hcover : ∀ p (_hp : p ∈ Icc (0 : ℝ) 1), a < min p (fkPrime p q) →
      p < a + ε → p ∈ K)
    (href : (FKLimit.bernoulliProduct
      (incrementProfile Eb a ε ha0 hε0.le haε1) : Measure (E → Bool)) A = 1)
    (henh : ∀ p ∈ K, ε ≤ cutsetEnhancement p q n) :
    LowerWindow A pc Eb Ee n m q hq := by
  refine ⟨pc - a, sub_pos.mpr hapc, ?_⟩
  intro p hp hpwindow
  have hpwindow' : a < min p (fkPrime p q) := by linarith
  have hpa : a < p := hpwindow'.trans_le (min_le_left _ _)
  have hple : p ≤ fkPrime p q := le_fkPrime_of_q_le_one hp.1 hp.2 hq hq1.le
  have hle : incrementProfile Eb a ε ha0 hε0.le haε1 ≤
      FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq := by
    intro e
    change ((incrementProfile Eb a ε ha0 hε0.le haε1 e : unitInterval) : ℝ) ≤
      FK.Phases.lowerWeightsReal Eb Ee n m p q e
    rw [FK.Phases.lowerWeightsReal_of_le hple]
    by_cases he : e ∈ Eb
    · simp only [incrementProfile, if_pos he]
      by_cases hbase : a + ε ≤ p
      · have heps0 := cutsetEnhancement_nonneg hp.1 hp.2 hq n
        linarith
      · have heps := henh p (hcover p hp hpwindow' (lt_of_not_ge hbase))
        linarith
    · simp only [incrementProfile, if_neg he, add_zero]
      exact hpa.le
  exact measure_eq_one_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA href

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open Set MeasureTheory ProbabilityTheory CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- One supercritical increment law and a uniform path-enhancement bound give
the full lower parameter window when `1 < q`. -/
theorem lowerWindow_of_incrementProfile_one_lt_q {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (a ε : ℝ) (K : Set ℝ) (hapc : a < pc) (ha0 : 0 ≤ a) (hε0 : 0 < ε)
    (haε1 : a + ε ≤ 1)
    (hcover : ∀ p (_hp : p ∈ Icc (0 : ℝ) 1), a < min p (fkPrime p q) →
      fkPrime p q < a + ε → p ∈ K)
    (href : (FKLimit.bernoulliProduct
      (incrementProfile Ee a ε ha0 hε0.le haε1) : Measure (E → Bool)) A = 1)
    (henh : ∀ p ∈ K, ε ≤ pathEnhancement p q m) :
    LowerWindow A pc Eb Ee n m q hq := by
  refine ⟨pc - a, sub_pos.mpr hapc, ?_⟩
  intro p hp hpwindow
  have hpwindow' : a < min p (fkPrime p q) := by linarith
  have hle : incrementProfile Ee a ε ha0 hε0.le haε1 ≤
      FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq := by
    by_cases hp0 : p = 0
    · subst p
      have ha_neg : a < 0 := by simpa [fkPrime] using hpwindow'
      linarith
    · by_cases hp1 : p = 1
      · subst p
        have hfk : fkPrime 1 q = 1 := by simp [fkPrime]
        intro e
        change ((incrementProfile Ee a ε ha0 hε0.le haε1 e : unitInterval) : ℝ) ≤
          FK.Phases.lowerWeightsReal Eb Ee n m 1 q e
        have hinc : ((incrementProfile Ee a ε ha0 hε0.le haε1 e : unitInterval) : ℝ) ≤ 1 := by
          by_cases hee : e ∈ Ee <;> simp [incrementProfile, hee] <;> linarith
        have hc : 0 ≤ if e ∈ Eb then cutsetEnhancement 1 q n else 0 := by
          split_ifs
          · exact cutsetEnhancement_nonneg zero_le_one le_rfl hq n
          · exact le_rfl
        rw [FK.Phases.lowerWeightsReal_of_le (le_of_eq hfk.symm)]
        exact hinc.trans (le_add_of_nonneg_right hc)
      · have hp0pos : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
        have hp1lt : p < 1 := lt_of_le_of_ne hp.2 hp1
        have hplt : fkPrime p q < p := (fkPrime_lt_iff hp0pos hp1lt hq).2 hq1
        have hp'a : a < fkPrime p q := hpwindow'.trans_le (min_le_right _ _)
        intro e
        change ((incrementProfile Ee a ε ha0 hε0.le haε1 e : unitInterval) : ℝ) ≤
          FK.Phases.lowerWeightsReal Eb Ee n m p q e
        rw [FK.Phases.lowerWeightsReal_of_ge hplt]
        by_cases he : e ∈ Ee
        · simp only [incrementProfile, if_pos he]
          by_cases hbase : a + ε ≤ fkPrime p q
          · have heps0 := pathEnhancement_nonneg hp.1 hp.2 hq m
            linarith
          · have heps := henh p (hcover p hp hpwindow' (lt_of_not_ge hbase))
            linarith
        · simp only [incrementProfile, if_neg he, add_zero]
          exact hp'a.le
  exact measure_eq_one_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA href

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open Set FK.Enhancement
open scoped unitInterval

/-- `fkPrime` is continuous on the whole closed parameter interval, including
both endpoints. -/
theorem continuousOn_fkPrime {q : ℝ} (hq : 0 < q) :
    ContinuousOn (fun p : ℝ ↦ fkPrime p q) (Icc 0 1) := by
  apply ContinuousOn.div continuousOn_id
    (continuousOn_id.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
  intro p hp
  exact (FK.Enhancement.denominator_pos (p := p) (q := q) (by simpa using hp.1)
    (by simpa using hp.2) hq).ne'

/-- A continuous positive function on a compact set has a positive uniform
lower bound.  The empty-set case is included separately. -/
theorem exists_pos_forall_le_of_isCompact {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ → ℝ} (hf : ContinuousOn f K) (hpos : ∀ p ∈ K, 0 < f p) :
    ∃ ε > 0, ∀ p ∈ K, ε ≤ f p := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x, hpos x hxK, fun _ hp ↦ hmin hp⟩
  · exact ⟨1, one_pos, fun _ hp ↦ (hne ⟨‹ℝ›, hp⟩).elim⟩

/-- Continuity of the closed-cutset enhancement on `[0,1]`. -/
theorem continuousOn_cutsetEnhancement {q : ℝ} (hq : 0 < q) (n : ℕ) :
    ContinuousOn (fun p : ℝ ↦ cutsetEnhancement p q n) (Icc 0 1) := by
  have hfk := continuousOn_fkPrime hq
  have hmax : ContinuousOn (fun p : ℝ ↦ max p (fkPrime p q)) (Icc 0 1) := by
    intro p hp
    exact continuousWithinAt_id.max (hfk p hp)
  exact ((hfk.sub continuousOn_id).abs).mul
    ((continuousOn_const.sub hmax).pow n)

/-- Continuity of the open-path enhancement on `[0,1]`. -/
theorem continuousOn_pathEnhancement {q : ℝ} (hq : 0 < q) (m : ℕ) :
    ContinuousOn (fun p : ℝ ↦ pathEnhancement p q m) (Icc 0 1) := by
  have hfk := continuousOn_fkPrime hq
  have hmin : ContinuousOn (fun p : ℝ ↦ min p (fkPrime p q)) (Icc 0 1) := by
    intro p hp
    exact continuousWithinAt_id.min (hfk p hp)
  exact ((hfk.sub continuousOn_id).abs).mul (hmin.pow m)

/-- Uniform positivity of the cutset enhancement on compact subsets of the
open parameter interval. -/
theorem exists_pos_cutsetEnhancement {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    {K : Set ℝ} (hK : IsCompact K) (hKopen : K ⊆ Ioo 0 1) (n : ℕ) :
    ∃ ε > 0, ∀ p ∈ K, ε ≤ cutsetEnhancement p q n := by
  apply exists_pos_forall_le_of_isCompact hK
    ((continuousOn_cutsetEnhancement hq n).mono (fun _ hp ↦
      ⟨(hKopen hp).1.le, (hKopen hp).2.le⟩ : K ⊆ Icc 0 1))
  intro p hp
  exact cutsetEnhancement_pos (hKopen hp).1 (hKopen hp).2 hq hq1 n

/-- Uniform positivity of the open-path enhancement on compact subsets of the
open parameter interval. -/
theorem exists_pos_pathEnhancement {q : ℝ} (hq : 0 < q) (hq1 : q ≠ 1)
    {K : Set ℝ} (hK : IsCompact K) (hKopen : K ⊆ Ioo 0 1) (m : ℕ) :
    ∃ ε > 0, ∀ p ∈ K, ε ≤ pathEnhancement p q m := by
  apply exists_pos_forall_le_of_isCompact hK
    ((continuousOn_pathEnhancement hq m).mono (fun _ hp ↦
      ⟨(hKopen hp).1.le, (hKopen hp).2.le⟩ : K ⊆ Icc 0 1))
  intro p hp
  exact pathEnhancement_pos (hKopen hp).1 (hKopen hp).2 hq hq1 m

end FK.EssentialWindow
