import FK.FKGlauber
import FK.Proposition31All
import FK.Coupling

/-!
# Open-path comparison against the actual finite FK PMF

This module supplies finite `FinProb`/`PMF` round trips, an order equivalence
between the open-path `Fin 2` convention and `FK.FiniteModel` Booleans, and the
limiting comparison in both stochastic directions.  The actual marginal is
`(G.fkPMF hq hp ξ).map configOfBool`, transported back to the original Boolean
FK PMF in the main statements.

These are coupled-dynamics reductions, **not an unconditional Proposition 3.2**.
The general forms take ordered joint laws and appropriate marginal limits.  The
modified-FK forms prove the FK limit with `fk_modifiedJump_tendsto`.  For the
lower direction, `pathProductKernel` also proves the enhanced-marginal limit
from interior rates and an explicit `Invariant` equation.  The remaining
obligations are therefore exactly that stationarity equation and the ordered
joint dynamics.  No such one-marginal reduction is asserted for the upper
direction: its path event is evaluated in the lower component of the coupled
pair, so the pair state must be retained.
-/

noncomputable section

open scoped Classical BigOperators ENNReal
open Set Filter
open OpenPath

namespace OpenPath.FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The probability mass function canonically associated to a finite real-mass law. -/
noncomputable def toPMF (μ : FinProb α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (μ.mass a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (fun a _ => μ.mass_nonneg a)]
    simp [μ.sum_mass])

@[simp] lemma toPMF_apply (μ : FinProb α) (a : α) :
    μ.toPMF a = ENNReal.ofReal (μ.mass a) := rfl

@[simp] lemma toPMF_apply_toReal (μ : FinProb α) (a : α) :
    (μ.toPMF a).toReal = μ.mass a := by
  simp [ENNReal.toReal_ofReal (μ.mass_nonneg a)]

lemma ofPMF_toPMF (μ : FinProb α) : Glauber.ofPMF μ.toPMF = μ := by
  apply FinProb.ext
  intro a
  change (ENNReal.ofReal (μ.mass a)).toReal = μ.mass a
  exact ENNReal.toReal_ofReal (μ.mass_nonneg a)

lemma toPMF_ofPMF (p : PMF α) : (Glauber.ofPMF p).toPMF = p := by
  apply PMF.ext
  intro a
  rw [toPMF_apply]
  simp [Glauber.ofPMF_mass, ENNReal.ofReal_toReal (p.apply_ne_top a)]

lemma toPMF_map (μ : FinProb α) (f : α → β) :
    (μ.map f).toPMF = μ.toPMF.map f := by
  classical
  apply PMF.ext
  intro b
  rw [toPMF_apply, PMF.map_apply, tsum_fintype]
  simp only [toPMF_apply, FinProb.mass_map]
  calc
    ENNReal.ofReal (∑ a, if f a = b then μ.mass a else 0) =
        ∑ a, ENNReal.ofReal (if f a = b then μ.mass a else 0) := by
      apply ENNReal.ofReal_sum_of_nonneg
      intro a _
      split_ifs
      · exact μ.mass_nonneg a
      · exact le_rfl
    _ = ∑ a, if b = f a then ENNReal.ofReal (μ.mass a) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : f a = b
      · rw [if_pos h, if_pos h.symm]
      · have h' : ¬ b = f a := fun hb => h hb.symm
        rw [if_neg h, if_neg h', ENNReal.ofReal_zero]

lemma toPMF_event [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : FinProb α) (A : Set α) :
    (μ.toPMF.toMeasure A).toReal = μ.event A := by
  rw [PMF.toMeasure_apply_fintype]
  simp only [FinProb.event]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ A <;>
      simp [ha, ENNReal.toReal_ofReal (μ.mass_nonneg a)]
  · intro a _
    by_cases ha : a ∈ A <;> simp [ha]


/-- Real-mass stochastic comparison is exactly the PMF comparison on finite types. -/
lemma stochLe_toPMF [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Preorder α] {μ ν : FinProb α} (h : StochLe μ ν) :
    PMF.StochLe μ.toPMF ν.toPMF := by
  intro A hA
  have hm : MeasurableSet A := MeasurableSet.of_discrete
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm,
    ← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm,
    ← ENNReal.toReal_le_toReal (MeasureTheory.measure_ne_top _ _)
      (MeasureTheory.measure_ne_top _ _)]
  simpa only [toPMF_event] using
    h A (fun a ha b hab => hA hab ha)

end OpenPath.FinProb


namespace OpenPath.FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

lemma toPMF_injective : Function.Injective (toPMF (α := α)) := by
  intro μ ν h
  rw [← ofPMF_toPMF μ, ← ofPMF_toPMF ν, h]

lemma ofPMF_map (p : PMF α) (f : α → β) :
    Glauber.ofPMF (p.map f) = (Glauber.ofPMF p).map f := by
  apply toPMF_injective
  rw [toPMF_ofPMF, toPMF_map, toPMF_ofPMF]

lemma stochasticallyDominates_toPMF [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Preorder α] {μ ν : FinProb α}
    (h : StochLe μ ν) :
    FKEnhancement.StochasticallyDominates μ.toPMF.toMeasure ν.toPMF.toMeasure := by
  intro A hmeas hupper
  have hs := stochLe_toPMF h A hupper
  simpa only [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hmeas] using hs

/-- Mapping each finite law by a fixed function commutes with mass convergence. -/
lemma LawTendsto.map {ι : Type*} {l : Filter ι} {μn : ι → FinProb α}
    {μ : FinProb α} (hμ : FinProb.LawTendsto l μn μ) (f : α → β) :
    FinProb.LawTendsto l (fun n => (μn n).map f) (μ.map f) := by
  classical
  intro b
  simp only [FinProb.mass_map]
  apply tendsto_finsetSum Finset.univ
  intro a _
  by_cases ha : f a = b
  · simpa [ha] using hμ a
  · simpa [ha] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (0 : ℝ)) l (nhds 0))

end OpenPath.FinProb

namespace OpenPath

/-- Convert an open-path bit to the Boolean state used by `FK.FiniteModel`. -/
def bitToBool (b : Bit) : Bool := decide (b = 1)

/-- Convert a Boolean FK state to an open-path bit. -/
def boolToBit (b : Bool) : Bit := if b then 1 else 0

@[simp] lemma bitToBool_zero : bitToBool 0 = false := by decide
@[simp] lemma bitToBool_one : bitToBool 1 = true := by decide
@[simp] lemma boolToBit_false : boolToBit false = 0 := rfl
@[simp] lemma boolToBit_true : boolToBit true = 1 := rfl

/-- The ordered two-point equivalence between the two configuration conventions. -/
def bitBoolEquiv : Bit ≃ Bool where
  toFun := bitToBool
  invFun := boolToBit
  left_inv b := by fin_cases b <;> rfl
  right_inv b := by cases b <;> rfl

@[simp] lemma bitBoolEquiv_apply (b : Bit) : bitBoolEquiv b = bitToBool b := rfl
@[simp] lemma bitBoolEquiv_symm_apply (b : Bool) : bitBoolEquiv.symm b = boolToBit b := rfl

lemma bitToBool_le_iff {a b : Bit} : bitToBool a ≤ bitToBool b ↔ a ≤ b := by
  fin_cases a <;> fin_cases b <;> simp [bitToBool]

lemma boolToBit_le_iff {a b : Bool} : boolToBit a ≤ boolToBit b ↔ a ≤ b := by
  cases a <;> cases b <;> simp [boolToBit]

/-- Coordinatewise conversion of a bit configuration to a Boolean FK configuration. -/
def configToBool {E : Type*} (ω : Config E) : E → Bool :=
  fun e => bitToBool (ω e)

/-- Coordinatewise conversion of a Boolean FK configuration to a bit configuration. -/
def configOfBool {E : Type*} (ω : E → Bool) : Config E :=
  fun e => boolToBit (ω e)

/-- The coordinatewise configuration equivalence. -/
def configBitBoolEquiv (E : Type*) : Config E ≃ (E → Bool) where
  toFun := configToBool
  invFun := configOfBool
  left_inv ω := by funext e; exact bitBoolEquiv.left_inv (ω e)
  right_inv ω := by funext e; exact bitBoolEquiv.right_inv (ω e)

lemma configToBool_le_iff {E : Type*} {ω ξ : Config E} :
    configToBool ω ≤ configToBool ξ ↔ ω ≤ ξ := by
  constructor
  · intro h e
    exact bitToBool_le_iff.mp (h e)
  · intro h e
    exact bitToBool_le_iff.mpr (h e)

lemma configOfBool_le_iff {E : Type*} {ω ξ : E → Bool} :
    configOfBool ω ≤ configOfBool ξ ↔ ω ≤ ξ := by
  constructor
  · intro h e
    exact boolToBit_le_iff.mp (h e)
  · intro h e
    exact boolToBit_le_iff.mpr (h e)

end OpenPath

namespace OpenPath.FinProb

end OpenPath.FinProb

namespace OpenPath

open FK.Finite

/-- The actual finite FK PMF transported to the open-path bit convention. -/
noncomputable def fkBitPMF (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) : PMF (Config G.Edge) :=
  (G.fkPMF hq hp ξ).map configOfBool

/-- The real-mass finite law underlying `fkBitPMF`. -/
noncomputable def fkBitFinProb (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) : FinProb (Config G.Edge) :=
  Glauber.ofPMF (fkBitPMF G hq hp ξ)

lemma fkBitFinProb_eq_map (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    fkBitFinProb G hq hp ξ = (Glauber.ofPMF (G.fkPMF hq hp ξ)).map configOfBool := by
  exact FinProb.ofPMF_map _ _

/-- Transporting the FK PMF to bits and back is the identity. -/
lemma fkBitPMF_map_configToBool (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    (fkBitPMF G hq hp ξ).map configToBool = G.fkPMF hq hp ξ := by
  rw [fkBitPMF, PMF.map_comp]
  have hfun : configToBool ∘ configOfBool = (id : (G.Edge → Bool) → (G.Edge → Bool)) := by
    funext ω e
    exact bitBoolEquiv.right_inv (ω e)
  change (G.fkPMF hq hp ξ).map (configToBool ∘ configOfBool) = G.fkPMF hq hp ξ
  rw [hfun, PMF.map_id]

/-- The exact lower inhomogeneous product law of Proposition 3.2(2). -/
noncomputable def lowerProductLaw {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (h : p' ≤ p) (Γ : E → Set (Finset E)) : FinProb (Config E) :=
  productLaw (lowerProductParameters enhanced p p' hp' Γ)
    (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ)

/-- The exact upper inhomogeneous product law of Proposition 3.2(1). -/
noncomputable def upperProductLaw {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (Γ : E → Set (Finset E)) : FinProb (Config E) :=
  productLaw (upperProductParameters enhanced p p' hp Γ)
    (upperProductParameters_mem_Icc enhanced hp hp'1 h Γ)

/-- PMF form of `lowerProductLaw`. -/
noncomputable def lowerProductPMF {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (h : p' ≤ p) (Γ : E → Set (Finset E)) : PMF (Config E) :=
  (lowerProductLaw enhanced hp1 hp' h Γ).toPMF

/-- PMF form of `upperProductLaw`. -/
noncomputable def upperProductPMF {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (Γ : E → Set (Finset E)) : PMF (Config E) :=
  (upperProductLaw enhanced hp hp'1 h Γ).toPMF

/-- Generic PMF domination, transported from outer measures to measures. -/
theorem stochasticallyDominates_of_pmfStochLe {α : Type*} [MeasurableSpace α]
    [LE α] {μ ν : PMF α} (h : PMF.StochLe μ ν) :
    FKEnhancement.StochasticallyDominates μ.toMeasure ν.toMeasure := by
  intro A hmeas hupper
  have hs := h A hupper
  simpa only [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hmeas] using hs

/-- Ordered configuration conversion transports PMF domination to the actual
Boolean FK configuration type. -/
theorem pmfStochLe_map_configToBool {E : Type*} {μ ν : PMF (Config E)}
    (h : PMF.StochLe μ ν) : PMF.StochLe (μ.map configToBool) (ν.map configToBool) := by
  intro A hA
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply h
  intro ω ξ hωξ hω
  exact hA (configToBool_le_iff.mpr hωξ) hω

/-- **Open-path lower comparison, coupled-dynamics form.**  The two marginal
limit hypotheses are explicit; no convergence or stationary law is asserted
for the supplied coupling sequence.  The middle limit is the actual finite FK
PMF transported to bits. -/
theorem lower_comparison_of_tendsto_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (lowerN fkN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hlowerLim : FinProb.LawTendsto atTop lowerN
      (lowerProductLaw enhanced (by exact_mod_cast hp) hp' h Γ))
    (hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hp ξ))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = fkN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FinProb.StochLe (lowerProductLaw enhanced (by exact_mod_cast hp) hp' h Γ)
      (fkBitFinProb G hq hp ξ) := by
  apply FinProb.stochLe_of_tendsto (l := atTop) (μn := lowerN) (νn := fkN)
  · intro n
    exact FinProb.stochLe_of_orderedCoupling
      { law := joint n, fst := hfst n, snd := hsnd n, ordered := horder n }
  · exact hlowerLim
  · exact hfkLim

/-- **Open-path upper comparison, coupled-dynamics form.** -/
theorem upper_comparison_of_tendsto_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (hpReal : (p : ℝ) ∈ Icc (0 : ℝ) 1)
    {p' : ℝ} (hp'1 : p' ≤ 1) (h : (p : ℝ) ≤ p')
    (Γ : G.Edge → Set (Finset G.Edge))
    (fkN upperN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hp ξ))
    (hupperLim : FinProb.LawTendsto atTop upperN
      (upperProductLaw enhanced hpReal hp'1 h Γ))
    (hfst : ∀ n, (joint n).map Prod.fst = fkN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FinProb.StochLe (fkBitFinProb G hq hp ξ)
      (upperProductLaw enhanced hpReal hp'1 h Γ) := by
  apply FinProb.stochLe_of_tendsto (l := atTop) (μn := fkN) (νn := upperN)
  · intro n
    exact FinProb.stochLe_of_orderedCoupling
      { law := joint n, fst := hfst n, snd := hsnd n, ordered := horder n }
  · exact hfkLim
  · exact hupperLim

end OpenPath

namespace OpenPath

open FK.Finite

/-- PMF form of the lower open-path comparison. -/
theorem lower_comparison_pmf_of_tendsto_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (lowerN fkN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hlowerLim : FinProb.LawTendsto atTop lowerN
      (lowerProductLaw enhanced (by exact_mod_cast hp) hp' h Γ))
    (hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hp ξ))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = fkN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    PMF.StochLe (lowerProductPMF enhanced (by exact_mod_cast hp) hp' h Γ)
      (fkBitPMF G hq hp ξ) := by
  letI : MeasurableSpace (Config G.Edge) := ⊤
  letI : DiscreteMeasurableSpace (Config G.Edge) := ⟨fun _ => trivial⟩
  have hdom := lower_comparison_of_tendsto_orderedDynamics G hq hp ξ enhanced hp' h Γ
    lowerN fkN joint hlowerLim hfkLim hfst hsnd horder
  have hpmf := FinProb.stochLe_toPMF hdom
  simpa only [lowerProductPMF, fkBitFinProb, FinProb.toPMF_ofPMF] using hpmf

/-- PMF form of the upper open-path comparison. -/
theorem upper_comparison_pmf_of_tendsto_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (hpReal : (p : ℝ) ∈ Icc (0 : ℝ) 1)
    {p' : ℝ} (hp'1 : p' ≤ 1) (h : (p : ℝ) ≤ p')
    (Γ : G.Edge → Set (Finset G.Edge))
    (fkN upperN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hp ξ))
    (hupperLim : FinProb.LawTendsto atTop upperN
      (upperProductLaw enhanced hpReal hp'1 h Γ))
    (hfst : ∀ n, (joint n).map Prod.fst = fkN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    PMF.StochLe (fkBitPMF G hq hp ξ)
      (upperProductPMF enhanced hpReal hp'1 h Γ) := by
  letI : MeasurableSpace (Config G.Edge) := ⊤
  letI : DiscreteMeasurableSpace (Config G.Edge) := ⟨fun _ => trivial⟩
  have hdom := upper_comparison_of_tendsto_orderedDynamics G hq hp ξ enhanced hpReal hp'1 h Γ
    fkN upperN joint hfkLim hupperLim hfst hsnd horder
  have hpmf := FinProb.stochLe_toPMF hdom
  simpa only [upperProductPMF, fkBitFinProb, FinProb.toPMF_ofPMF] using hpmf

/-- Lower comparison on the original Boolean finite FK configuration space.
The product law is transported from bits by the explicit order equivalence. -/
theorem lower_comparison_bool_of_tendsto_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (lowerN fkN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hlowerLim : FinProb.LawTendsto atTop lowerN
      (lowerProductLaw enhanced (by exact_mod_cast hp) hp' h Γ))
    (hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hp ξ))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = fkN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp) hp' h Γ).map configToBool).toMeasure
      (G.fkPMF hq hp ξ).toMeasure := by
  apply stochasticallyDominates_of_pmfStochLe
  have hmap := pmfStochLe_map_configToBool
    (lower_comparison_pmf_of_tendsto_orderedDynamics G hq hp ξ enhanced hp' h Γ
      lowerN fkN joint hlowerLim hfkLim hfst hsnd horder)
  rwa [fkBitPMF_map_configToBool] at hmap

/-- Upper comparison on the original Boolean finite FK configuration space. -/
theorem upper_comparison_bool_of_tendsto_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (hpReal : (p : ℝ) ∈ Icc (0 : ℝ) 1)
    {p' : ℝ} (hp'1 : p' ≤ 1) (h : (p : ℝ) ≤ p')
    (Γ : G.Edge → Set (Finset G.Edge))
    (fkN upperN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hp ξ))
    (hupperLim : FinProb.LawTendsto atTop upperN
      (upperProductLaw enhanced hpReal hp'1 h Γ))
    (hfst : ∀ n, (joint n).map Prod.fst = fkN n)
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates (G.fkPMF hq hp ξ).toMeasure
      ((upperProductPMF enhanced hpReal hp'1 h Γ).map configToBool).toMeasure := by
  apply stochasticallyDominates_of_pmfStochLe
  have hmap := pmfStochLe_map_configToBool
    (upper_comparison_pmf_of_tendsto_orderedDynamics G hq hp ξ enhanced hpReal hp'1 h Γ
      fkN upperN joint hfkLim hupperLim hfst hsnd horder)
  rwa [fkBitPMF_map_configToBool] at hmap

end OpenPath

namespace OpenPath

open FK.Finite Glauber

/-- Lower comparison with the FK marginal supplied by the actual modified block
Glauber dynamics.  Its convergence and stationarity are proved, not assumed. -/
theorem lower_comparison_of_tendsto_lower_and_modifiedFK
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ (p : ℝ))
    (Γ : G.Edge → Set (Finset G.Edge))
    (μ : FinProb (G.Edge → Bool)) (ρ : FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule)
    (lowerN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hlowerLim : FinProb.LawTendsto atTop lowerN
      (lowerProductLaw enhanced (by exact_mod_cast hp) hp' h Γ))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd =
      ((μ.bind (iterate (modifiedJump ρ
        (Glauber.FKBridge.edgeConditionals G hq hp ξ) enhanced auxiliary) n)).map
          configOfBool))
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp) hp' h Γ).map configToBool).toMeasure
      (G.fkPMF hq hp ξ).toMeasure := by
  apply lower_comparison_bool_of_tendsto_orderedDynamics G hq hp ξ enhanced hp' h Γ
    lowerN _ joint hlowerLim _ hfst hsnd horder
  have ht := Glauber.FKBridge.fk_modifiedJump_tendsto G hq hp hp0 hp1 μ ρ hρ ξ
    enhanced auxiliary schedule hschedule
  have hmap := FinProb.LawTendsto.map ht configOfBool
  simpa only [fkBitFinProb_eq_map] using hmap

/-- Upper comparison with convergence of the actual modified FK marginal proved
by the existing interior chain theorem. -/
theorem upper_comparison_of_tendsto_upper_and_modifiedFK
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (hpReal : (p : ℝ) ∈ Icc (0 : ℝ) 1)
    {p' : ℝ} (hp'1 : p' ≤ 1) (h : (p : ℝ) ≤ p')
    (Γ : G.Edge → Set (Finset G.Edge))
    (μ : FinProb (G.Edge → Bool)) (ρ : FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule)
    (upperN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hupperLim : FinProb.LawTendsto atTop upperN
      (upperProductLaw enhanced hpReal hp'1 h Γ))
    (hfst : ∀ n, (joint n).map Prod.fst =
      ((μ.bind (iterate (modifiedJump ρ
        (Glauber.FKBridge.edgeConditionals G hq hp ξ) enhanced auxiliary) n)).map
          configOfBool))
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates (G.fkPMF hq hp ξ).toMeasure
      ((upperProductPMF enhanced hpReal hp'1 h Γ).map configToBool).toMeasure := by
  apply upper_comparison_bool_of_tendsto_orderedDynamics G hq hp ξ enhanced hpReal hp'1 h Γ
    _ upperN joint _ hupperLim hfst hsnd horder
  have ht := Glauber.FKBridge.fk_modifiedJump_tendsto G hq hp hp0 hp1 μ ρ hρ ξ
    enhanced auxiliary schedule hschedule
  have hmap := FinProb.LawTendsto.map ht configOfBool
  simpa only [fkBitFinProb_eq_map] using hmap

end OpenPath

namespace OpenPath

open FK.Finite Glauber

/-- Equation-(2) specialization of the lower comparison: the disconnected
singleton rate is exactly `FK.prime q p`. -/
theorem prime_lower_comparison_of_tendsto_lower_and_modifiedFK
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hprime : FK.prime (q : ℝ) (p : ℝ) ≤ (p : ℝ))
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (μ : FinProb (G.Edge → Bool)) (ρ : FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule)
    (lowerN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hlowerLim : FinProb.LawTendsto atTop lowerN
      (lowerProductLaw enhanced (by exact_mod_cast hp)
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp))
        hprime Γ))
    (hfst : ∀ n, (joint n).map Prod.fst = lowerN n)
    (hsnd : ∀ n, (joint n).map Prod.snd =
      ((μ.bind (iterate (modifiedJump ρ
        (Glauber.FKBridge.edgeConditionals G hq hp ξ) enhanced auxiliary) n)).map
          configOfBool))
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp)
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp))
        hprime Γ).map configToBool).toMeasure
      (G.fkPMF hq hp ξ).toMeasure := by
  exact lower_comparison_of_tendsto_lower_and_modifiedFK G hq hp hp0 hp1 ξ enhanced
    (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp))
    hprime Γ μ ρ hρ auxiliary schedule hschedule lowerN joint hlowerLim hfst hsnd horder

/-- Equation-(2) specialization of the upper comparison. -/
theorem prime_upper_comparison_of_tendsto_upper_and_modifiedFK
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hprime : (p : ℝ) ≤ FK.prime (q : ℝ) (p : ℝ))
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (μ : FinProb (G.Edge → Bool)) (ρ : FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule)
    (upperN : ℕ → FinProb (Config G.Edge))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hupperLim : FinProb.LawTendsto atTop upperN
      (upperProductLaw enhanced
        ⟨by positivity, by exact_mod_cast hp⟩
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)).2
        hprime Γ))
    (hfst : ∀ n, (joint n).map Prod.fst =
      ((μ.bind (iterate (modifiedJump ρ
        (Glauber.FKBridge.edgeConditionals G hq hp ξ) enhanced auxiliary) n)).map
          configOfBool))
    (hsnd : ∀ n, (joint n).map Prod.snd = upperN n)
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates (G.fkPMF hq hp ξ).toMeasure
      ((upperProductPMF enhanced
        ⟨by positivity, by exact_mod_cast hp⟩
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)).2
        hprime Γ).map configToBool).toMeasure := by
  exact upper_comparison_of_tendsto_upper_and_modifiedFK G hq hp hp0 hp1 ξ enhanced
    ⟨by positivity, by exact_mod_cast hp⟩
    (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)).2
    hprime Γ μ ρ hρ auxiliary schedule hschedule upperN joint hupperLim hfst hsnd horder

end OpenPath

namespace Glauber

/-- Convergence of a modified block chain when stationarity is proved directly.
Unlike `modifiedJump_tendsto`, this does not require each enhanced substep to be
an ordinary conditional refresh: enhanced paths may be tested in the old state. -/
theorem tendsto_bind_iterate_of_invariant_of_positive
    {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]
    (μ π : OpenPath.FinProb (E → B)) (c : EdgeConditionals B E)
    (ρ : OpenPath.FinProb E) (hρ : ∀ e, 0 < ρ.mass e)
    (hbit : ∀ e off b, 0 < (c e off).mass b)
    (enhanced : Finset E) (auxiliary : List E)
    (hπ : Invariant π (modifiedJump ρ c enhanced auxiliary))
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    OpenPath.FinProb.LawTendsto Filter.atTop
      (fun n => μ.bind (iterate (modifiedJump ρ c enhanced auxiliary) n)) π := by
  obtain ⟨a, _⟩ := FinProb.exists_mass_pos μ
  letI : Nonempty (E → B) := ⟨a⟩
  obtain ⟨e₀, _⟩ := FinProb.exists_mass_pos ρ
  have hN : 0 < schedule.length := List.length_pos_of_mem (hschedule e₀)
  apply tendsto_bind_iterate_of_positive_power μ π
    (modifiedJump ρ c enhanced auxiliary) hπ hN
  intro ω η
  simpa only [FinProb.bind_dirac] using
    modifiedJump_iterate_pos c hbit ρ hρ enhanced auxiliary schedule hschedule ω η

end Glauber

namespace OpenPath

open Glauber

/-- Recombine an off-edge bit configuration with a closed distinguished edge. -/
noncomputable def pathOffConfiguration {E : Type*} [Fintype E] [DecidableEq E]
    (e : E) (off : OffConfig Bit E e) : Config E :=
  (configSplit Bit e).symm (off, 0)

/-- In the lower comparison, the enhanced edge has rate `p` on an open path
and `p'` otherwise; nonenhanced edges have rate `p'`.  The path is tested in the
lower configuration.  The upper comparison needs the ordered pair state and is
not represented by this one-marginal kernel. -/
noncomputable def pathProductRate {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (Γ : E → Set (Finset E))
    (e : E) (off : OffConfig Bit E e) : ℝ :=
  if e ∈ enhanced ∧ SomePathOpen (Γ e) (pathOffConfiguration e off) then p else p'

lemma pathProductRate_mem_Icc {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp' : p' ∈ Icc (0 : ℝ) 1) (Γ : E → Set (Finset E))
    (e : E) (off : OffConfig Bit E e) :
    pathProductRate enhanced p p' Γ e off ∈ Icc (0 : ℝ) 1 := by
  unfold pathProductRate
  split_ifs <;> assumption

/-- Exact finite conditional laws for the path-enhanced product marginal. -/
noncomputable def pathProductConditionals {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp' : p' ∈ Icc (0 : ℝ) 1) (Γ : E → Set (Finset E)) :
    EdgeConditionals Bit E := fun e off =>
  bitLaw (pathProductRate enhanced p p' Γ e off)
    (pathProductRate_mem_Icc enhanced hp hp' Γ e off)

lemma pathProductConditionals_pos {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hp'0 : 0 < p') (hp'1 : p' < 1)
    (Γ : E → Set (Finset E)) (e : E) (off : OffConfig Bit E e) (b : Bit) :
    0 < (pathProductConditionals enhanced
      ⟨hp0.le, hp1.le⟩ ⟨hp'0.le, hp'1.le⟩ Γ e off).mass b := by
  unfold pathProductConditionals bitLaw pathProductRate
  split_ifs <;> fin_cases b <;> simp_all

/-- The path-enhanced modified block kernel on one product marginal. -/
noncomputable def pathProductKernel {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : FinProb E) (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) (auxiliary : List E) :
    Config E → FinProb (Config E) :=
  modifiedJump ρ (pathProductConditionals enhanced hp hp' Γ) enhanced auxiliary

/-- Interior path-enhanced product dynamics converge to any law proved invariant
for the same kernel.  Stationarity is deliberately an explicit input, to be
discharged by exact joint-product invariance, not inferred from singleton
conditional factorization. -/
theorem pathProduct_tendsto_of_invariant {E : Type*} [Fintype E] [DecidableEq E]
    (μ π : FinProb (Config E)) (ρ : FinProb E)
    (hρ : ∀ e, 0 < ρ.mass e) (enhanced : Finset E) {p p' : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hp'0 : 0 < p') (hp'1 : p' < 1)
    (Γ : E → Set (Finset E)) (auxiliary : List E)
    (hπ : Invariant π (pathProductKernel ρ enhanced
      ⟨hp0.le, hp1.le⟩ ⟨hp'0.le, hp'1.le⟩ Γ auxiliary))
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    FinProb.LawTendsto atTop
      (fun n => μ.bind (iterate (pathProductKernel ρ enhanced
        ⟨hp0.le, hp1.le⟩ ⟨hp'0.le, hp'1.le⟩ Γ auxiliary) n)) π := by
  exact Glauber.tendsto_bind_iterate_of_invariant_of_positive μ π
    (pathProductConditionals enhanced ⟨hp0.le, hp1.le⟩ ⟨hp'0.le, hp'1.le⟩ Γ)
    ρ hρ (pathProductConditionals_pos enhanced hp0 hp1 hp'0 hp'1 Γ)
    enhanced auxiliary hπ schedule hschedule

end OpenPath

namespace OpenPath

open FK.Finite Glauber

/-- Lower comparison whose lower marginal is the exact path-product kernel.
Both marginal limits are proved; the remaining probabilistic inputs are the
stationarity equation and the ordered joint dynamics. -/
theorem lower_comparison_of_stationary_pathProduct_and_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (hp'0 : 0 < p') (hp'1 : p' < 1)
    (h : p' ≤ (p : ℝ)) (Γ : G.Edge → Set (Finset G.Edge))
    (μlower : FinProb (Config G.Edge)) (μfk : FinProb (G.Edge → Bool))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule)
    (hInvariant : Invariant (lowerProductLaw enhanced (by exact_mod_cast hp) hp' h Γ)
      (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
        ⟨by positivity, by exact_mod_cast hp⟩ hp' Γ auxiliary))
    (joint : ℕ → FinProb (Config G.Edge × Config G.Edge))
    (hfst : ∀ n, (joint n).map Prod.fst = μlower.bind
      (iterate (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
        ⟨by positivity, by exact_mod_cast hp⟩ hp' Γ auxiliary) n))
    (hsnd : ∀ n, (joint n).map Prod.snd =
      ((μfk.bind (iterate (modifiedJump ρ
        (Glauber.FKBridge.edgeConditionals G hq hp ξ) enhanced auxiliary) n)).map
          configOfBool))
    (horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp) hp' h Γ).map configToBool).toMeasure
      (G.fkPMF hq hp ξ).toMeasure := by
  apply lower_comparison_of_tendsto_lower_and_modifiedFK G hq hp hp0 hp1 ξ enhanced
    hp' h Γ μfk ρ hρ auxiliary schedule hschedule
    (fun n => μlower.bind (iterate (pathProductKernel (p := (p : ℝ)) (p' := p') ρ enhanced
      ⟨by positivity, by exact_mod_cast hp⟩ hp' Γ auxiliary) n)) joint _ hfst hsnd horder
  exact pathProduct_tendsto_of_invariant (p := (p : ℝ)) (p' := p') μlower _ ρ hρ enhanced
    (by exact_mod_cast hp0) (by exact_mod_cast hp1) hp'0 hp'1 Γ auxiliary
    hInvariant schedule hschedule

end OpenPath
