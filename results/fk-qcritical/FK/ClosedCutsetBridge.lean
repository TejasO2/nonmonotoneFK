import FK.Proposition32
import FK.FiniteComparison
import FK.JointProductInvariance
import FK.FiniteComponentCounts

/-!
# Finite-law bridges for the closed-cutset comparison

This module supplies the explicit `FinProb`/PMF/product-measure conversions used
by Proposition 3.1.  The sandwich theorem still takes finite-time coupled
marginals and their limits as inputs; it does not assert convergence of the
enhanced Markov chain.  The product-law identity is unconditional.
-/

namespace OpenPath.FinProb

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

variable {α : Type*} [Fintype α]

/- `toPMF` and its point-mass formulas are supplied by `FK.Proposition32`. -/

@[simp] lemma Glauber_ofPMF_toPMF (μ : FinProb α) :
    Glauber.ofPMF μ.toPMF = μ := by
  apply FinProb.ext
  intro a
  exact toPMF_apply_toReal μ a

@[simp] lemma toPMF_Glauber_ofPMF (μ : PMF α) :
    FinProb.toPMF (Glauber.ofPMF μ) = μ := by
  ext a
  simp [PMF.apply_ne_top]

section Measurable

variable [MeasurableSpace α] [MeasurableSingletonClass α]
  [DiscreteMeasurableSpace α] [Preorder α]

omit [Preorder α] in
/-- Real probabilities agree under `FinProb.toPMF`. -/
lemma toPMF_toMeasure_toReal (μ : FinProb α) (A : Set α) :
    (μ.toPMF.toMeasure A).toReal = μ.event A := by
  classical
  rw [FKEnhancement.pmf_toReal_toMeasure_eq_sum]
  unfold FinProb.event
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ A
  · simp only [Set.indicator_of_mem ha, ha, ↓reduceIte, toPMF_apply_toReal]
  · simp [ha]

/-- Finite real-mass stochastic domination is the same as stochastic
domination of the corresponding PMF measures on all increasing events. -/
lemma stochasticallyDominates_toPMF_of_stochLe {μ ν : FinProb α}
    (h : FinProb.StochLe μ ν) :
    FKEnhancement.StochasticallyDominates μ.toPMF.toMeasure ν.toPMF.toMeasure := by
  intro A _ hA
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  simpa only [toPMF_toMeasure_toReal] using
    h A (by
      intro a ha b hab
      exact hA hab ha)

end Measurable

section Sandwich

open scoped Topology

variable {α : Type*} [Fintype α] [Preorder α]

/-- Finite-time ordered triple marginals give both limiting stochastic
comparisons.  This is the `FinProb` counterpart of the existing PMF sandwich
lemma and avoids any conversion hypotheses in the enhanced dynamics. -/
theorem sandwich_stochLe_of_tendsto
    (lower fk upper : FinProb α) (lowerN fkN upperN : ℕ → FinProb α)
    (joint : ℕ → FinProb (α × α × α))
    (hlower : ∀ n, (joint n).map (fun t => t.1) = lowerN n)
    (hfk : ∀ n, (joint n).map (fun t => t.2.1) = fkN n)
    (hupper : ∀ n, (joint n).map (fun t => t.2.2) = upperN n)
    (horder : ∀ n t, (joint n).mass t ≠ 0 → t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)
    (hlowerLim : LawTendsto atTop lowerN lower)
    (hfkLim : LawTendsto atTop fkN fk)
    (hupperLim : LawTendsto atTop upperN upper) :
    StochLe lower fk ∧ StochLe fk upper := by
  let lowerPair : ℕ → FinProb (α × α) := fun n =>
    (joint n).map (fun t => (t.1, t.2.1))
  let upperPair : ℕ → FinProb (α × α) := fun n =>
    (joint n).map (fun t => (t.2.1, t.2.2))
  have lowerFst : ∀ n, (lowerPair n).map Prod.fst = lowerN n := by
    intro n
    simpa [lowerPair, GlauberCoupling.map_map, Function.comp_def] using hlower n
  have lowerSnd : ∀ n, (lowerPair n).map Prod.snd = fkN n := by
    intro n
    simpa [lowerPair, GlauberCoupling.map_map, Function.comp_def] using hfk n
  have upperFst : ∀ n, (upperPair n).map Prod.fst = fkN n := by
    intro n
    simpa [upperPair, GlauberCoupling.map_map, Function.comp_def] using hfk n
  have upperSnd : ∀ n, (upperPair n).map Prod.snd = upperN n := by
    intro n
    simpa [upperPair, GlauberCoupling.map_map, Function.comp_def] using hupper n
  have lowerOrder : ∀ n a, (lowerPair n).mass a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    obtain ⟨t, ht, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ha
    exact (horder n t ht).1
  have upperOrder : ∀ n a, (upperPair n).mass a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    obtain ⟨t, ht, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ha
    exact (horder n t ht).2
  have hdomLower : ∀ n, StochLe (lowerN n) (fkN n) := by
    intro n
    exact stochLe_of_orderedCoupling
      { law := lowerPair n, fst := lowerFst n, snd := lowerSnd n,
        ordered := lowerOrder n }
  have hdomUpper : ∀ n, StochLe (fkN n) (upperN n) := by
    intro n
    exact stochLe_of_orderedCoupling
      { law := upperPair n, fst := upperFst n, snd := upperSnd n,
        ordered := upperOrder n }
  exact ⟨stochLe_of_tendsto hdomLower hlowerLim hfkLim,
    stochLe_of_tendsto hdomUpper hfkLim hupperLim⟩

end Sandwich
end OpenPath.FinProb

namespace FKEnhancement

open MeasureTheory Set Filter
open scoped unitInterval ENNReal ProbabilityTheory BigOperators Topology
open FK.Finite.Comparison

variable {E : Type*} [Fintype E]

/-- The existing measure-valued inhomogeneous product is exactly the PMF
measure of the existing `Bool`-valued `FinProb` product. -/
theorem toPMF_boolProduct_toMeasure [DecidableEq E] (rates : E → I) :
    (OpenPath.FinProb.toPMF
      (boolProduct (fun e => (rates e : ℝ)) (fun e => (rates e).2))).toMeasure =
      bernoulliProduct rates := by
  classical
  apply MeasureTheory.Measure.ext_of_singleton
  intro ω
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ENNReal.ofReal ((boolProduct (fun e => (rates e : ℝ))
    (fun e => (rates e).2)).mass ω) = bernoulliProduct rates {ω}
  simp only [boolProduct, OpenPath.FinProb.pi_mass, bernoulliProduct,
    MeasureTheory.Measure.pi_singleton]
  have ofReal_toNNReal (x : I) : ENNReal.ofReal (x : ℝ) =
      (unitInterval.toNNReal x : ℝ≥0∞) := by
    change ENNReal.ofReal ((unitInterval.toNNReal x : NNReal) : ℝ) =
      ((unitInterval.toNNReal x : NNReal) : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  have ofReal_symm_toNNReal (x : I) : ENNReal.ofReal (1 - (x : ℝ)) =
      (unitInterval.toNNReal (σ x) : ℝ≥0∞) := by
    have hreal : ((unitInterval.toNNReal (σ x) : NNReal) : ℝ) = 1 - (x : ℝ) := by
      rw [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    rw [← hreal]
    exact ENNReal.ofReal_coe_nnreal
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro e _
    cases h : ω e <;>
      simp [FK.Finite.Comparison.boolLaw, ofReal_toNNReal, ofReal_symm_toNNReal]
  · intro e _
    exact FK.Finite.Comparison.boolLaw (rates e : ℝ) (rates e).2 |>.mass_nonneg (ω e)

end FKEnhancement


namespace OpenPath.FinProb

open scoped Topology
open Filter

variable {α : Type*} [Fintype α] [Preorder α]

/-- Pair form of the finite stochastic-limit argument. -/
theorem stochLe_of_tendsto_orderedCouplings
    (μ ν : FinProb α) (μn νn : ℕ → FinProb α)
    (joint : ℕ → FinProb (α × α))
    (hfst : ∀ n, (joint n).map Prod.fst = μn n)
    (hsnd : ∀ n, (joint n).map Prod.snd = νn n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2)
    (hμ : LawTendsto atTop μn μ) (hν : LawTendsto atTop νn ν) :
    StochLe μ ν := by
  apply stochLe_of_tendsto (μn := μn) (νn := νn) (l := atTop) _ hμ hν
  intro n
  exact stochLe_of_orderedCoupling
    { law := joint n, fst := hfst n, snd := hsnd n, ordered := horder n }

end OpenPath.FinProb

namespace FKEnhancement

open MeasureTheory Set Filter
open scoped Classical unitInterval ENNReal ProbabilityTheory BigOperators Topology
open FK.Finite.Comparison

/-- The lower enhanced law as a finite real-mass law on Bool configurations. -/
noncomputable def lowerEnhancedFinProb {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') : OpenPath.FinProb (Configuration E) :=
  boolProduct (fun e => (lowerEnhancedRates K enhanced hp e : ℝ))
    (fun e => (lowerEnhancedRates K enhanced hp e).2)

/-- The upper enhanced law as a finite real-mass law on Bool configurations. -/
noncomputable def upperEnhancedFinProb {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) : OpenPath.FinProb (Configuration E) :=
  boolProduct (fun e => (upperEnhancedRates K enhanced hp e : ℝ))
    (fun e => (upperEnhancedRates K enhanced hp e).2)

@[simp] theorem lowerEnhancedFinProb_toMeasure {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') :
    (lowerEnhancedFinProb K enhanced hp).toPMF.toMeasure = lowerEnhancedLaw K enhanced hp := by
  exact toPMF_boolProduct_toMeasure (lowerEnhancedRates K enhanced hp)

@[simp] theorem upperEnhancedFinProb_toMeasure {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) :
    (upperEnhancedFinProb K enhanced hp).toPMF.toMeasure = upperEnhancedLaw K enhanced hp := by
  exact toPMF_boolProduct_toMeasure (upperEnhancedRates K enhanced hp)

/-- Lower closed-cutset comparison of an actual finite FK PMF, with all
law-conversion assumptions removed.  The remaining inputs are precisely the
finite-time ordered coupled marginals and their weak limits. -/
theorem graph_lower_comparison_of_tendsto_dynamics
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr : r ≤ 1) (ξ : G.BoundaryPartition)
    (K : G.Edge → Configuration G.Edge → Prop) (enhanced : Set G.Edge)
    {p p' : I} (hp : p ≤ p')
    (lowerN fkN : ℕ → OpenPath.FinProb (Configuration G.Edge))
    (joint : ℕ → OpenPath.FinProb (Configuration G.Edge × Configuration G.Edge))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = fkN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2)
    (hlowerLim : OpenPath.FinProb.LawTendsto atTop lowerN
      (lowerEnhancedFinProb K enhanced hp))
    (hfkLim : OpenPath.FinProb.LawTendsto atTop fkN
      (Glauber.ofPMF (G.fkPMF hq hr ξ))) :
    StochasticallyDominates (lowerEnhancedLaw K enhanced hp) (G.fkMeasure hq hr ξ) := by
  have hdom := OpenPath.FinProb.stochLe_of_tendsto_orderedCouplings
    (lowerEnhancedFinProb K enhanced hp) (Glauber.ofPMF (G.fkPMF hq hr ξ))
    lowerN fkN joint hfst hsnd horder hlowerLim hfkLim
  have hmeasure := OpenPath.FinProb.stochasticallyDominates_toPMF_of_stochLe hdom
  simpa only [OpenPath.FinProb.toPMF_Glauber_ofPMF,
    lowerEnhancedFinProb_toMeasure, FK.Finite.LabelledMultigraph.fkMeasure] using hmeasure

/-- Upper closed-cutset comparison of an actual finite FK PMF, in the opposite
parameter direction and with the FK coordinate below the enhanced product. -/
theorem graph_upper_comparison_of_tendsto_dynamics
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr : r ≤ 1) (ξ : G.BoundaryPartition)
    (K : G.Edge → Configuration G.Edge → Prop) (enhanced : Set G.Edge)
    {p p' : I} (hp : p' ≤ p)
    (fkN upperN : ℕ → OpenPath.FinProb (Configuration G.Edge))
    (joint : ℕ → OpenPath.FinProb (Configuration G.Edge × Configuration G.Edge))
    (hfst : ∀ n, (joint n).map Prod.fst = fkN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2)
    (hfkLim : OpenPath.FinProb.LawTendsto atTop fkN
      (Glauber.ofPMF (G.fkPMF hq hr ξ)))
    (hupperLim : OpenPath.FinProb.LawTendsto atTop upperN
      (upperEnhancedFinProb K enhanced hp)) :
    StochasticallyDominates (G.fkMeasure hq hr ξ) (upperEnhancedLaw K enhanced hp) := by
  have hdom := OpenPath.FinProb.stochLe_of_tendsto_orderedCouplings
    (Glauber.ofPMF (G.fkPMF hq hr ξ)) (upperEnhancedFinProb K enhanced hp)
    fkN upperN joint hfst hsnd horder hfkLim hupperLim
  have hmeasure := OpenPath.FinProb.stochasticallyDominates_toPMF_of_stochLe hdom
  simpa only [OpenPath.FinProb.toPMF_Glauber_ofPMF,
    upperEnhancedFinProb_toMeasure, FK.Finite.LabelledMultigraph.fkMeasure] using hmeasure

end FKEnhancement

namespace FKEnhancement

open FK.Finite.Comparison
open FK.Finite.Conditional
open FK.FiniteFiber
open scoped Classical

/-- The FK singleton connection predicate, evaluated on the full finite
labelled-multigraph configuration. -/
def graphConnectionEvent (G : FK.Finite.LabelledMultigraph) (ξ : G.BoundaryPartition) :
    G.Edge → Configuration G.Edge → Prop := fun e ω =>
  endpointsConnectedWithout G ξ e ω

/-- The graph connection event cannot depend on the state of the distinguished
edge, since `endpointsConnectedWithout` closes that edge before exploring. -/
lemma graphConnectionEvent_update (G : FK.Finite.LabelledMultigraph)
    (ξ : G.BoundaryPartition) (e : G.Edge) (ω : Configuration G.Edge) (b : Bool) :
    graphConnectionEvent G ξ e (Function.update ω e b) ↔ graphConnectionEvent G ξ e ω := by
  exact endpointsConnectedWithout_congr G (withEdge_mem_offFiber e b ω)

/-- The abstract FK threshold used by the closed-cutset update is definitionally
the actual singleton FK conditional threshold for the labelled multigraph. -/
lemma graphConnectionEvent_fkRate (G : FK.Finite.LabelledMultigraph)
    (q p : NNReal) (ξ : G.BoundaryPartition) (e : G.Edge) (ω : Configuration G.Edge) :
    FKEnhancement.fkRate (graphConnectionEvent G ξ) e (p : ℝ)
        (FK.prime (q : ℝ) (p : ℝ)) ω =
      FK.Finite.Comparison.fkRate G q p ξ e ((Glauber.configSplit Bool e ω).1) := by
  have hfull : fullOff e ((Glauber.configSplit Bool e ω).1) = Function.update ω e false := by
    simpa [fullOff] using Glauber.configSplit_symm_update e ω false
  have hoff : fullOff e ((Glauber.configSplit Bool e ω).1) ∈ offFiber e ω := by
    rw [hfull]
    exact withEdge_mem_offFiber e false ω
  unfold FKEnhancement.fkRate FK.Finite.Comparison.fkRate graphConnectionEvent
  rw [endpointsConnectedWithout_congr G hoff]

end FKEnhancement


namespace FKEnhancement

open Set
open scoped Classical BigOperators unitInterval
open FK.Finite.Comparison

/-- Average the enhanced ordered Bool pair in the `p ≤ p'` direction. -/
noncomputable def averagedLowerBoolPair {α : Type*} [Fintype α]
    (μ : OpenPath.FinProb α) (C : Set α) (p p' : ℝ)
    (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    OpenPath.FinProb (Bool × Bool) :=
  μ.bind (fun a => if a ∈ C then
    boolPair p' p' (hp0.trans h) le_rfl hp'1 else boolPair p p' hp0 h hp'1)

/-- The averaged first marginal is exactly the closed-cutset enhancement
`p + (p'-p) * P(C)`, and the second marginal has reference rate `p'`. -/
lemma averagedLowerBoolPair_eq {α : Type*} [Fintype α]
    (μ : OpenPath.FinProb α) (C : Set α) (p p' : ℝ)
    (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    averagedLowerBoolPair μ C p p' hp0 hp'1 h =
      boolPair (p + closedCutsetEnhancement p p' (μ.event C)) p'
        (add_nonneg hp0 (mul_nonneg (abs_nonneg _) (μ.event_mem_Icc C).1))
        (enhancedOpenRate_le hp0 h (μ.event_mem_Icc C).1 (μ.event_mem_Icc C).2)
        hp'1 := by
  apply OpenPath.FinProb.ext
  rintro ⟨i, j⟩
  change (∑ a, μ.mass a * (if a ∈ C then
    boolPair p' p' (hp0.trans h) le_rfl hp'1 else
      boolPair p p' hp0 h hp'1).mass (i, j)) = _
  simp_rw [apply_ite (fun ν : OpenPath.FinProb (Bool × Bool) => ν.mass (i, j))]
  rw [OpenPath.FinProb.sum_mass_mul_ite]
  cases i <;> cases j <;> simp [boolPair, closedCutsetEnhancement_of_le h] <;> ring

/-- Average the enhanced ordered Bool pair in the `p' ≤ p` direction. -/
noncomputable def averagedUpperBoolPair {α : Type*} [Fintype α]
    (μ : OpenPath.FinProb α) (C : Set α) (p p' : ℝ)
    (hp'0 : 0 ≤ p') (hp1 : p ≤ 1) (h : p' ≤ p) :
    OpenPath.FinProb (Bool × Bool) :=
  μ.bind (fun a => if a ∈ C then
    boolPair p' p' hp'0 le_rfl (h.trans hp1) else boolPair p' p hp'0 h hp1)

/-- The averaged second marginal is exactly `p - (p-p') * P(C)`, with
first marginal at the ordinary reference rate `p'`. -/
lemma averagedUpperBoolPair_eq {α : Type*} [Fintype α]
    (μ : OpenPath.FinProb α) (C : Set α) (p p' : ℝ)
    (hp'0 : 0 ≤ p') (hp1 : p ≤ 1) (h : p' ≤ p) :
    averagedUpperBoolPair μ C p p' hp'0 hp1 h =
      boolPair p' (p - closedCutsetEnhancement p p' (μ.event C)) hp'0
        (enhancedOpenRate_bounds_of_ge hp1 hp'0 h
          (μ.event_mem_Icc C).1 (μ.event_mem_Icc C).2).1
        ((enhancedOpenRate_bounds_of_ge hp1 hp'0 h
          (μ.event_mem_Icc C).1 (μ.event_mem_Icc C).2).2.trans hp1) := by
  apply OpenPath.FinProb.ext
  rintro ⟨i, j⟩
  change (∑ a, μ.mass a * (if a ∈ C then
    boolPair p' p' hp'0 le_rfl (h.trans hp1) else
      boolPair p' p hp'0 h hp1).mass (i, j)) = _
  simp_rw [apply_ite (fun ν : OpenPath.FinProb (Bool × Bool) => ν.mass (i, j))]
  rw [OpenPath.FinProb.sum_mass_mul_ite]
  cases i <;> cases j <;> simp [boolPair, closedCutsetEnhancement_of_ge h] <;> ring

/-- Exact joint-product invariance after enhancement and complete auxiliary
refresh, for the Bool lower-enhancement pair. -/
theorem blockLaw_lowerBoolPair_invariant {α ρ : Type*}
    [Fintype α] [Fintype ρ]
    (μ : OpenPath.FinProb α) (ξ : OpenPath.FinProb ρ) (C : Set α)
    (p p' : ℝ) (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    let ν := boolPair (p + closedCutsetEnhancement p p' (μ.event C)) p'
      (add_nonneg hp0 (mul_nonneg (abs_nonneg _) (μ.event_mem_Icc C).1))
      (enhancedOpenRate_le hp0 h (μ.event_mem_Icc C).1 (μ.event_mem_Icc C).2) hp'1
    (JointInvariance.blockLaw ν μ ξ).bind
      (JointInvariance.blockKernel μ (fun a => if a ∈ C then
        boolPair p' p' (hp0.trans h) le_rfl hp'1 else boolPair p p' hp0 h hp'1)) =
      JointInvariance.blockLaw ν μ ξ := by
  dsimp only
  apply JointInvariance.blockLaw_invariant
  exact averagedLowerBoolPair_eq μ C p p' hp0 hp'1 h

end FKEnhancement


namespace FKEnhancement

open Set
open scoped Classical BigOperators unitInterval
open FK.Finite.Comparison

/-- Exact joint-product invariance for the upper-enhancement Bool pair. -/
theorem blockLaw_upperBoolPair_invariant {α ρ : Type*}
    [Fintype α] [Fintype ρ]
    (μ : OpenPath.FinProb α) (ξ : OpenPath.FinProb ρ) (C : Set α)
    (p p' : ℝ) (hp'0 : 0 ≤ p') (hp1 : p ≤ 1) (h : p' ≤ p) :
    let ν := boolPair p' (p - closedCutsetEnhancement p p' (μ.event C)) hp'0
      (enhancedOpenRate_bounds_of_ge hp1 hp'0 h
        (μ.event_mem_Icc C).1 (μ.event_mem_Icc C).2).1
      ((enhancedOpenRate_bounds_of_ge hp1 hp'0 h
        (μ.event_mem_Icc C).1 (μ.event_mem_Icc C).2).2.trans hp1)
    (JointInvariance.blockLaw ν μ ξ).bind
      (JointInvariance.blockKernel μ (fun a => if a ∈ C then
        boolPair p' p' hp'0 le_rfl (h.trans hp1) else boolPair p' p hp'0 h hp1)) =
      JointInvariance.blockLaw ν μ ξ := by
  dsimp only
  apply JointInvariance.blockLaw_invariant
  exact averagedUpperBoolPair_eq μ C p p' hp'0 hp1 h

/-- The ordinary lower endpoint is below the upper enhanced rate. -/
lemma upperEnhancedRate_ge_of_ge {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) (e : E) : (p' : ℝ) ≤ upperEnhancedRate K enhanced p p' e := by
  classical
  simp only [upperEnhancedRate]
  split_ifs
  · exact (enhancedOpenRate_bounds_of_ge p.2.2 p'.2.1 hp
      (cutsetWeight_nonneg K enhanced p p' e)
      (cutsetWeight_le_one K enhanced p p' e)).1
  · exact hp

/-- The ordered lower-enhanced/reference pair law, independently at each edge. -/
noncomputable def lowerCutsetPairLaw {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') : OpenPath.FinProb (E → Bool × Bool) :=
  OpenPath.FinProb.pi (fun e =>
    boolPair (lowerEnhancedRate K enhanced p p' e) (max p p' : I)
      (lowerEnhancedRate_nonneg K enhanced hp e)
      (by simpa [max_eq_right hp] using lowerEnhancedRate_le K enhanced hp e)
      (max p p' : I).2.2)

/-- Its first marginal is precisely the lower enhanced Bool product law. -/
theorem lowerCutsetPairLaw_map_fst {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') :
    (lowerCutsetPairLaw K enhanced hp).map (fun ω e => (ω e).1) =
      lowerEnhancedFinProb K enhanced hp := by
  unfold lowerCutsetPairLaw lowerEnhancedFinProb boolProduct
  rw [OpenPath.FinProb.pi_map]
  congr 1
  funext e
  exact boolPair_fst _ _ _ _ _

/-- Its second marginal is the ordinary `max(p,p')` reference product. -/
theorem lowerCutsetPairLaw_map_snd {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') :
    (lowerCutsetPairLaw K enhanced hp).map (fun ω e => (ω e).2) =
      boolProduct (fun _ : E => (max p p' : I)) (fun _ => (max p p' : I).2) := by
  unfold lowerCutsetPairLaw boolProduct
  rw [OpenPath.FinProb.pi_map]
  congr 1
  funext e
  exact boolPair_snd _ _ _ _ _

/-- Every positive-mass configuration of the lower pair law is ordered. -/
theorem lowerCutsetPairLaw_ordered {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    {hp : p ≤ p'} {ω : E → Bool × Bool}
    (hω : (lowerCutsetPairLaw K enhanced hp).mass ω ≠ 0) (e : E) :
    (ω e).1 ≤ (ω e).2 := by
  apply boolPair_ordered _ _ _ _ _
  have hfactor : (boolPair (lowerEnhancedRate K enhanced p p' e) (max p p' : I)
      (lowerEnhancedRate_nonneg K enhanced hp e)
      (by simpa [max_eq_right hp] using lowerEnhancedRate_le K enhanced hp e)
      (max p p' : I).2.2).mass (ω e) ≠ 0 := by
    intro hz
    apply hω
    change ∏ a, _ = 0
    exact Finset.prod_eq_zero (Finset.mem_univ e) hz
  exact hfactor

/-- The ordered ordinary/enhanced-upper pair law in the opposite direction. -/
noncomputable def upperCutsetPairLaw {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) : OpenPath.FinProb (E → Bool × Bool) :=
  OpenPath.FinProb.pi (fun e =>
    boolPair p' (upperEnhancedRate K enhanced p p' e) p'.2.1
      (upperEnhancedRate_ge_of_ge K enhanced hp e)
      (upperEnhancedRate_le_one K enhanced hp e))

/-- The first marginal in the `p' ≤ p` case is the ordinary lower reference. -/
theorem upperCutsetPairLaw_map_fst {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) :
    (upperCutsetPairLaw K enhanced hp).map (fun ω e => (ω e).1) =
      boolProduct (fun _ : E => p') (fun _ => p'.2) := by
  unfold upperCutsetPairLaw boolProduct
  rw [OpenPath.FinProb.pi_map]
  congr 1
  funext e
  exact boolPair_fst _ _ _ _ _

/-- The second marginal is precisely the upper enhanced Bool product law. -/
theorem upperCutsetPairLaw_map_snd {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p' ≤ p) :
    (upperCutsetPairLaw K enhanced hp).map (fun ω e => (ω e).2) =
      upperEnhancedFinProb K enhanced hp := by
  unfold upperCutsetPairLaw upperEnhancedFinProb boolProduct
  rw [OpenPath.FinProb.pi_map]
  congr 1
  funext e
  exact boolPair_snd _ _ _ _ _

/-- Every positive-mass configuration of the upper pair law is ordered. -/
theorem upperCutsetPairLaw_ordered {E : Type*} [Fintype E]
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    {hp : p' ≤ p} {ω : E → Bool × Bool}
    (hω : (upperCutsetPairLaw K enhanced hp).mass ω ≠ 0) (e : E) :
    (ω e).1 ≤ (ω e).2 := by
  apply boolPair_ordered _ _ _ _ _
  have hfactor : (boolPair p' (upperEnhancedRate K enhanced p p' e) p'.2.1
      (upperEnhancedRate_ge_of_ge K enhanced hp e)
      (upperEnhancedRate_le_one K enhanced hp e)).mass (ω e) ≠ 0 := by
    intro hz
    apply hω
    change ∏ a, _ = 0
    exact Finset.prod_eq_zero (Finset.mem_univ e) hz
  exact hfactor

end FKEnhancement


namespace FKEnhancement

open Set
open scoped Classical BigOperators
open FK.Finite.Comparison

variable {E : Type*} [Fintype E]

/-- One complete enhanced/auxiliary block, expressed on indexed Bool pairs,
leaves every product whose distinguished local pair has the exact enhanced
average invariant.  Other enhanced edges may have arbitrary local pair laws. -/
theorem pi_lowerBoolPair_invariant
    (ν : E → OpenPath.FinProb (Bool × Bool)) (e : E) (A : Finset E)
    (C : Set (JointInvariance.AuxiliaryIndex E e A → Bool × Bool))
    (p p' : ℝ) (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (hνe : ν e = boolPair
      (p + closedCutsetEnhancement p p'
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event C)) p'
      (add_nonneg hp0 (mul_nonneg (abs_nonneg _)
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1))
      (enhancedOpenRate_le hp0 h
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).2) hp'1) :
    (OpenPath.FinProb.pi ν).bind
      (JointInvariance.transportedBlockKernel (JointInvariance.indexedBlockEquiv e A)
        (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
        (fun a => if a ∈ C then boolPair p' p' (hp0.trans h) le_rfl hp'1
          else boolPair p p' hp0 h hp'1)) = OpenPath.FinProb.pi ν := by
  apply JointInvariance.pi_bind_transportedBlockKernel_invariant
  rw [hνe]
  exact averagedLowerBoolPair_eq _ C p p' hp0 hp'1 h

/-- The companion indexed Bool-pair invariance theorem in the `p' ≤ p`
direction; only the second local marginal receives the enhancement. -/
theorem pi_upperBoolPair_invariant
    (ν : E → OpenPath.FinProb (Bool × Bool)) (e : E) (A : Finset E)
    (C : Set (JointInvariance.AuxiliaryIndex E e A → Bool × Bool))
    (p p' : ℝ) (hp'0 : 0 ≤ p') (hp1 : p ≤ 1) (h : p' ≤ p)
    (hνe : ν e = boolPair p'
      (p - closedCutsetEnhancement p p'
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event C)) hp'0
      (enhancedOpenRate_bounds_of_ge hp1 hp'0 h
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).2).1
      ((enhancedOpenRate_bounds_of_ge hp1 hp'0 h
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).2).2.trans hp1)) :
    (OpenPath.FinProb.pi ν).bind
      (JointInvariance.transportedBlockKernel (JointInvariance.indexedBlockEquiv e A)
        (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
        (fun a => if a ∈ C then boolPair p' p' hp'0 le_rfl (h.trans hp1)
          else boolPair p' p hp'0 h hp1)) = OpenPath.FinProb.pi ν := by
  apply JointInvariance.pi_bind_transportedBlockKernel_invariant
  rw [hνe]
  exact averagedUpperBoolPair_eq _ C p p' hp'0 hp1 h

end FKEnhancement


namespace FKEnhancement

open FK.Finite.Comparison
open scoped BigOperators

/-- The common-uniform coupling of three ordered Bool laws.  The only states
with positive mass are `000`, `001`, `011`, and `111`. -/
def boolTriple (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) : OpenPath.FinProb (Bool × Bool × Bool) where
  mass
    | (false, false, false) => 1 - c
    | (false, false, true) => c - b
    | (false, true, false) => 0
    | (false, true, true) => b - a
    | (true, false, false) => 0
    | (true, false, true) => 0
    | (true, true, false) => 0
    | (true, true, true) => a
  mass_nonneg t := by
    rcases t with ⟨i, j, k⟩
    cases i <;> cases j <;> cases k <;>
      simp [h0, hab, hbc, hc, sub_nonneg]
  sum_mass := by
    simp only [Fintype.sum_prod_type]
    simp

@[simp] lemma boolTriple_mass_000 (a b c : ℝ) (h0 hab hbc hc) :
    (boolTriple a b c h0 hab hbc hc).mass (false, false, false) = 1 - c := rfl
@[simp] lemma boolTriple_mass_001 (a b c : ℝ) (h0 hab hbc hc) :
    (boolTriple a b c h0 hab hbc hc).mass (false, false, true) = c - b := rfl
@[simp] lemma boolTriple_mass_011 (a b c : ℝ) (h0 hab hbc hc) :
    (boolTriple a b c h0 hab hbc hc).mass (false, true, true) = b - a := rfl
@[simp] lemma boolTriple_mass_111 (a b c : ℝ) (h0 hab hbc hc) :
    (boolTriple a b c h0 hab hbc hc).mass (true, true, true) = a := rfl

/-- The first two coordinates have the ordinary ordered Bool-pair law. -/
lemma boolTriple_map_fst_snd (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    (boolTriple a b c h0 hab hbc hc).map (fun t => (t.1, t.2.1)) =
      boolPair a b h0 hab (hbc.trans hc) := by
  apply OpenPath.FinProb.ext
  rintro ⟨i, j⟩
  cases i <;> cases j <;>
    simp [OpenPath.FinProb.mass_map, boolTriple, boolPair, Fintype.sum_prod_type]

/-- The last two coordinates have the ordinary ordered Bool-pair law. -/
lemma boolTriple_map_snd_thd (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    (boolTriple a b c h0 hab hbc hc).map (fun t => (t.2.1, t.2.2)) =
      boolPair b c (h0.trans hab) hbc hc := by
  apply OpenPath.FinProb.ext
  rintro ⟨i, j⟩
  cases i <;> cases j <;>
    simp [OpenPath.FinProb.mass_map, boolTriple, boolPair, Fintype.sum_prod_type]

/-- The outside pair also has exactly the common-uniform ordered pair law. -/
lemma boolTriple_map_fst_thd (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    (boolTriple a b c h0 hab hbc hc).map (fun t => (t.1, t.2.2)) =
      boolPair a c h0 (hab.trans hbc) hc := by
  apply OpenPath.FinProb.ext
  rintro ⟨i, j⟩
  cases i <;> cases j <;>
    simp [OpenPath.FinProb.mass_map, boolTriple, boolPair, Fintype.sum_prod_type]

/-- The middle marginal is exactly the Bool law at the intermediate rate. -/
lemma boolTriple_map_snd (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    (boolTriple a b c h0 hab hbc hc).map (fun t => t.2.1) =
      boolLaw b ⟨h0.trans hab, hbc.trans hc⟩ := by
  apply OpenPath.FinProb.ext
  intro i
  cases i <;>
    simp [OpenPath.FinProb.mass_map, boolTriple, boolLaw, Fintype.sum_prod_type]

/-- Every positive-mass triple is ordered `lower ≤ FK ≤ upper`. -/
lemma boolTriple_ordered (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) {t : Bool × Bool × Bool}
    (ht : (boolTriple a b c h0 hab hbc hc).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  rcases t with ⟨i, j, k⟩
  cases i <;> cases j <;> cases k <;> simp_all [boolTriple]

end FKEnhancement


namespace FKEnhancement

open Set
open scoped Classical unitInterval BigOperators
open FK.Finite.Comparison

lemma fkRate_mem_Icc {E : Type*} (K : E → Configuration E → Prop)
    (e : E) (p p' : I) (ω : Configuration E) :
    FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) ω ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold FKEnhancement.fkRate
  split_ifs
  · exact p.2
  · exact p'.2

lemma fkRate_ge_min' {E : Type*} (K : E → Configuration E → Prop)
    (e : E) (p p' : I) (ω : Configuration E) :
    min (p : ℝ) (p' : ℝ) ≤ FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) ω := by
  classical
  unfold FKEnhancement.fkRate
  split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

lemma fkRate_le_max' {E : Type*} (K : E → Configuration E → Prop)
    (e : E) (p p' : I) (ω : Configuration E) :
    FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) ω ≤ max (p : ℝ) (p' : ℝ) := by
  classical
  unfold FKEnhancement.fkRate
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The exact outer lower/upper law at an enhanced edge. -/
noncomputable def cutsetOuterPairLaw {E : Type*}
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (z : Configuration E) : OpenPath.FinProb (Bool × Bool) := by
  classical
  exact if HasClosedCutset K enhanced e z then
    boolPair p' p' p'.2.1 le_rfl p'.2.2
  else
    boolPair (min (p : ℝ) (p' : ℝ)) (max (p : ℝ) (p' : ℝ))
      (le_min p.2.1 p'.2.1) min_le_max (max_le p.2.2 p'.2.2)

/-- On an ordered pair of old configurations, a certificate in the upper one
forces the FK singleton threshold to be `p'`. -/
lemma fkRate_eq_right_of_hasClosedCutset {E : Type*}
    {K : E → Configuration E → Prop} {enhanced : Set E} {e : E}
    {p p' : I} {x z : Configuration E} (hxz : x ≤ z)
    (hc : HasClosedCutset K enhanced e z) :
    FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x = (p' : ℝ) := by
  classical
  obtain ⟨χ, hχ, hclosed⟩ := hc.mono hxz
  have hK : ¬ K e x := hχ.2 x hclosed
  simp [FKEnhancement.fkRate, hK]

/-- A finite exact coupling of the lower, FK, and upper enhanced bits.  The
only old-state order used by the paper is the middle/upper inequality. -/
noncomputable def orderedCutsetBitLaw {E : Type*}
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (x z : Configuration E) (_hxz : x ≤ z) :
    OpenPath.FinProb (Bool × Bool × Bool) := by
  classical
  exact if HasClosedCutset K enhanced e z then
    boolTriple p' p' p' p'.2.1 le_rfl le_rfl p'.2.2
  else
    boolTriple (min (p : ℝ) (p' : ℝ))
      (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
      (max (p : ℝ) (p' : ℝ))
      (le_min p.2.1 p'.2.1)
      (fkRate_ge_min' K e p p' x) (fkRate_le_max' K e p p' x)
      (max_le p.2.2 p'.2.2)

/-- Projecting out the FK bit recovers the exact enhanced outer-pair kernel. -/
theorem orderedCutsetBitLaw_map_fst_thd {E : Type*}
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (x z : Configuration E) (hxz : x ≤ z) :
    (orderedCutsetBitLaw K enhanced e p p' x z hxz).map
      (fun t => (t.1, t.2.2)) = cutsetOuterPairLaw K enhanced e p p' z := by
  classical
  unfold orderedCutsetBitLaw cutsetOuterPairLaw
  split_ifs
  · exact boolTriple_map_fst_thd _ _ _ _ _ _ _
  · exact boolTriple_map_fst_thd _ _ _ _ _ _ _

/-- The middle marginal is exactly the FK singleton law. -/
theorem orderedCutsetBitLaw_map_snd {E : Type*}
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (x z : Configuration E) (hxz : x ≤ z) :
    (orderedCutsetBitLaw K enhanced e p p' x z hxz).map (fun t => t.2.1) =
      boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
        (fkRate_mem_Icc K e p p' x) := by
  classical
  unfold orderedCutsetBitLaw
  split_ifs with hc
  · have h := boolTriple_map_snd (p' : ℝ) (p' : ℝ) (p' : ℝ)
      p'.2.1 le_rfl le_rfl p'.2.2
    simpa only [fkRate_eq_right_of_hasClosedCutset hxz hc] using h
  · exact boolTriple_map_snd _ _ _ _ _ _ _

/-- Every supported enhanced triple has lower ≤ FK ≤ upper. -/
theorem orderedCutsetBitLaw_ordered {E : Type*}
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (x z : Configuration E) (hxz : x ≤ z)
    {t : Bool × Bool × Bool}
    (ht : (orderedCutsetBitLaw K enhanced e p p' x z hxz).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  classical
  unfold orderedCutsetBitLaw at ht
  split_ifs at ht <;> exact boolTriple_ordered _ _ _ _ _ _ _ ht

end FKEnhancement


namespace FKEnhancement

open Set
open scoped Classical unitInterval BigOperators
open FK.Finite.Comparison

/-- One enhanced-edge configuration update with exact lower/FK/upper joint
law.  Off-edge values are retained independently in each coordinate. -/
noncomputable def orderedCutsetUpdateLaw {E : Type*} [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (y x z : Configuration E) (hxz : x ≤ z) :
    OpenPath.FinProb (Configuration E × Configuration E × Configuration E) :=
  (orderedCutsetBitLaw K enhanced e p p' x z hxz).map (fun b =>
    (Function.update y e b.1, Function.update x e b.2.1,
      Function.update z e b.2.2))

/-- Its outer pair marginal is the cutset outer-pair update. -/
theorem orderedCutsetUpdateLaw_map_fst_thd {E : Type*} [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (y x z : Configuration E) (hxz : x ≤ z) :
    (orderedCutsetUpdateLaw K enhanced e p p' y x z hxz).map
      (fun t => (t.1, t.2.2)) =
    (cutsetOuterPairLaw K enhanced e p p' z).map (fun b =>
      (Function.update y e b.1, Function.update z e b.2)) := by
  unfold orderedCutsetUpdateLaw
  rw [GlauberCoupling.map_map]
  change (orderedCutsetBitLaw K enhanced e p p' x z hxz).map
    ((fun b : Bool × Bool => (Function.update y e b.1, Function.update z e b.2)) ∘
      (fun t : Bool × Bool × Bool => (t.1, t.2.2))) = _
  rw [← GlauberCoupling.map_map, orderedCutsetBitLaw_map_fst_thd]

/-- Its middle marginal is the exact FK heat-bath update for the abstract
connection predicate, after recombination with the off-edge configuration. -/
theorem orderedCutsetUpdateLaw_map_snd {E : Type*} [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (y x z : Configuration E) (hxz : x ≤ z) :
    (orderedCutsetUpdateLaw K enhanced e p p' y x z hxz).map (fun t => t.2.1) =
      (boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
        (fkRate_mem_Icc K e p p' x)).map (Function.update x e) := by
  unfold orderedCutsetUpdateLaw
  rw [GlauberCoupling.map_map]
  change (orderedCutsetBitLaw K enhanced e p p' x z hxz).map
    ((Function.update x e) ∘ (fun t : Bool × Bool × Bool => t.2.1)) = _
  rw [← GlauberCoupling.map_map, orderedCutsetBitLaw_map_snd]

/-- Order is preserved by the enhanced update, including both inequalities. -/
theorem orderedCutsetUpdateLaw_ordered {E : Type*} [Fintype E] [DecidableEq E]
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) {y x z : Configuration E} (hyx : y ≤ x) (hxz : x ≤ z)
    {t : Configuration E × Configuration E × Configuration E}
    (ht : (orderedCutsetUpdateLaw K enhanced e p p' y x z hxz).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  obtain ⟨b, hb, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ht
  have hb' := orderedCutsetBitLaw_ordered K enhanced e p p' x z hxz hb
  constructor <;> intro a <;> by_cases ha : a = e
  · subst a
    simpa using hb'.1
  · simp only [Function.update_of_ne ha]
    exact hyx a
  · subst a
    simpa using hb'.2
  · simp only [Function.update_of_ne ha]
    exact hxz a

end FKEnhancement


namespace FKEnhancement

open Set Filter
open scoped Classical unitInterval BigOperators Topology
open FK.Finite.Comparison

/-- Lower cutset comparison with the FK marginal generated by the actual
modified block Glauber dynamics.  Only the enhanced marginal limit remains an
analytic input; the FK limit is supplied by `fk_modifiedJump_tendsto`. -/
theorem graphConnectionEvent_lower_comparison_of_tendsto_lower_and_modifiedFK
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr : r ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) {p p' : I} (hp : p ≤ p')
    (μ : OpenPath.FinProb G.Configuration) (ρ : OpenPath.FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (auxiliary schedule : List G.Edge)
    (hschedule : ∀ e, e ∈ schedule)
    (lowerN : ℕ → OpenPath.FinProb (Configuration G.Edge))
    (joint : ℕ → OpenPath.FinProb (Configuration G.Edge × Configuration G.Edge))
    (hlowerLim : OpenPath.FinProb.LawTendsto atTop lowerN
      (lowerEnhancedFinProb (graphConnectionEvent G ξ) enhanced hp))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = μ.bind (Glauber.iterate
      (Glauber.modifiedJump ρ (Glauber.FKBridge.edgeConditionals G hq hr ξ)
        enhanced.toFinset auxiliary) n))
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    StochasticallyDominates
      (lowerEnhancedLaw (graphConnectionEvent G ξ) enhanced hp) (G.fkMeasure hq hr ξ) := by
  apply graph_lower_comparison_of_tendsto_dynamics G hq hr ξ
    (graphConnectionEvent G ξ) enhanced hp lowerN _ joint hfst hsnd horder hlowerLim
  exact Glauber.FKBridge.fk_modifiedJump_tendsto G hq hr hr0 hr1 μ ρ hρ ξ
    enhanced.toFinset auxiliary schedule hschedule

/-- Upper cutset comparison with convergence of the actual modified FK
marginal proved by the existing interior block-chain theorem. -/
theorem graphConnectionEvent_upper_comparison_of_tendsto_upper_and_modifiedFK
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr : r ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) {p p' : I} (hp : p' ≤ p)
    (μ : OpenPath.FinProb G.Configuration) (ρ : OpenPath.FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (auxiliary schedule : List G.Edge)
    (hschedule : ∀ e, e ∈ schedule)
    (upperN : ℕ → OpenPath.FinProb (Configuration G.Edge))
    (joint : ℕ → OpenPath.FinProb (Configuration G.Edge × Configuration G.Edge))
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (hfst : ∀ n, (joint n).map Prod.fst = μ.bind (Glauber.iterate
      (Glauber.modifiedJump ρ (Glauber.FKBridge.edgeConditionals G hq hr ξ)
        enhanced.toFinset auxiliary) n))
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2)
    (hupperLim : OpenPath.FinProb.LawTendsto atTop upperN
      (upperEnhancedFinProb (graphConnectionEvent G ξ) enhanced hp)) :
    StochasticallyDominates (G.fkMeasure hq hr ξ)
      (upperEnhancedLaw (graphConnectionEvent G ξ) enhanced hp) := by
  apply graph_upper_comparison_of_tendsto_dynamics G hq hr ξ
    (graphConnectionEvent G ξ) enhanced hp _ upperN joint hfst hsnd horder _ hupperLim
  exact Glauber.FKBridge.fk_modifiedJump_tendsto G hq hr hr0 hr1 μ ρ hρ ξ
    enhanced.toFinset auxiliary schedule hschedule

end FKEnhancement
