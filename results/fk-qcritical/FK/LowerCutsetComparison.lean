import FK.LowerCutsetChain
import FK.MultigraphEnhancement

/-!
# Unconditional lower closed-cutset comparison

The ordered outer pair starts in its stationary law.  The FK coordinate starts
at its upper marginal.  Consequently the enhanced lower marginal is constant
along the coupled chain, while the existing FK convergence theorem applies to
the arbitrary initial upper product.  No convergence theorem for the singular
ordered pair chain is needed.
-/

namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- Ordinary lower/FK/upper bits, without an enhanced-cutset test. -/
def ordinaryCutsetBitLaw (K : E → Configuration E → Prop) (e : E)
    (p p' : I) (x : Configuration E) : OpenPath.FinProb (Bool × Bool × Bool) :=
  boolTriple (min (p : ℝ) (p' : ℝ))
    (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x) (max (p : ℝ) (p' : ℝ))
    (le_min p.2.1 p'.2.1) (fkRate_ge_min' K e p p' x)
    (fkRate_le_max' K e p p' x) (max_le p.2.2 p'.2.2)

/-- One ordinary configuration update. -/
def ordinaryCutsetUpdateLaw (K : E → Configuration E → Prop) (e : E)
    (p p' : I) (y x z : Configuration E) :
    OpenPath.FinProb (Configuration E × Configuration E × Configuration E) :=
  (ordinaryCutsetBitLaw K e p p' x).map (fun b =>
    (Function.update y e b.1, Function.update x e b.2.1,
      Function.update z e b.2.2))

/-- Enhanced configuration update on every raw state.  Off the ordered region,
an independent coupling is used only to keep both marginals globally exact. -/
def enhancedCutsetUpdateLawTotal (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) (p p' : I)
    (y x z : Configuration E) :
    OpenPath.FinProb (Configuration E × Configuration E × Configuration E) := by
  classical
  exact if hxz : x ≤ z then
    orderedCutsetUpdateLaw K enhanced e p p' y x z hxz
  else
    ((cutsetOuterPairLaw K enhanced e p p' z).prod
      (boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
        (fkRate_mem_Icc K e p p' x))).map (fun b =>
      (Function.update y e b.1.1, Function.update x e b.2,
        Function.update z e b.1.2))

lemma ordinaryCutsetUpdateLaw_map_fst_thd (K : E → Configuration E → Prop)
    (e : E) (p p' : I) (y x z : Configuration E) :
    (ordinaryCutsetUpdateLaw K e p p' y x z).map (fun t => (t.1, t.2.2)) =
      (boolPair (min (p : ℝ) (p' : ℝ)) (max (p : ℝ) (p' : ℝ))
        (le_min p.2.1 p'.2.1) min_le_max (max_le p.2.2 p'.2.2)).map (fun b =>
          (Function.update y e b.1, Function.update z e b.2)) := by
  unfold ordinaryCutsetUpdateLaw
  rw [GlauberCoupling.map_map]
  change (ordinaryCutsetBitLaw K e p p' x).map
    ((fun b : Bool × Bool => (Function.update y e b.1, Function.update z e b.2)) ∘
      (fun t : Bool × Bool × Bool => (t.1, t.2.2))) = _
  unfold ordinaryCutsetBitLaw
  rw [← GlauberCoupling.map_map, boolTriple_map_fst_thd]

lemma ordinaryCutsetUpdateLaw_map_snd (K : E → Configuration E → Prop)
    (e : E) (p p' : I) (y x z : Configuration E) :
    (ordinaryCutsetUpdateLaw K e p p' y x z).map (fun t => t.2.1) =
      (boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
        (fkRate_mem_Icc K e p p' x)).map (Function.update x e) := by
  unfold ordinaryCutsetUpdateLaw
  rw [GlauberCoupling.map_map]
  change (ordinaryCutsetBitLaw K e p p' x).map
    ((Function.update x e) ∘ (fun t : Bool × Bool × Bool => t.2.1)) = _
  unfold ordinaryCutsetBitLaw
  rw [← GlauberCoupling.map_map, boolTriple_map_snd]

lemma ordinaryCutsetUpdateLaw_ordered (K : E → Configuration E → Prop)
    (e : E) (p p' : I) {y x z : Configuration E}
    (hyx : y ≤ x) (hxz : x ≤ z)
    {t : Configuration E × Configuration E × Configuration E}
    (ht : (ordinaryCutsetUpdateLaw K e p p' y x z).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  obtain ⟨b, hb, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ht
  have hb' : b.1 ≤ b.2.1 ∧ b.2.1 ≤ b.2.2 := by
    exact boolTriple_ordered _ _ _ _ _ _ _ hb
  constructor <;> intro a <;> by_cases ha : a = e
  · subst a
    simpa using hb'.1
  · simp only [Function.update_of_ne ha]
    exact hyx a
  · subst a
    simpa using hb'.2
  · simp only [Function.update_of_ne ha]
    exact hxz a

lemma enhancedCutsetUpdateLawTotal_map_fst_thd (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) (p p' : I) (y x z : Configuration E) :
    (enhancedCutsetUpdateLawTotal K enhanced e p p' y x z).map
      (fun t => (t.1, t.2.2)) =
    (cutsetOuterPairLaw K enhanced e p p' z).map (fun b =>
      (Function.update y e b.1, Function.update z e b.2)) := by
  classical
  unfold enhancedCutsetUpdateLawTotal
  split_ifs with hxz
  · exact orderedCutsetUpdateLaw_map_fst_thd K enhanced e p p' y x z hxz
  · rw [GlauberCoupling.map_map]
    change ((cutsetOuterPairLaw K enhanced e p p' z).prod _).map
      ((fun b : Bool × Bool => (Function.update y e b.1, Function.update z e b.2)) ∘
        Prod.fst) = _
    rw [← GlauberCoupling.map_map, OpenPath.FinProb.prod_map_fst]

lemma enhancedCutsetUpdateLawTotal_map_snd (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) (p p' : I) (y x z : Configuration E) :
    (enhancedCutsetUpdateLawTotal K enhanced e p p' y x z).map (fun t => t.2.1) =
      (boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
        (fkRate_mem_Icc K e p p' x)).map (Function.update x e) := by
  classical
  unfold enhancedCutsetUpdateLawTotal
  split_ifs with hxz
  · exact orderedCutsetUpdateLaw_map_snd K enhanced e p p' y x z hxz
  · rw [GlauberCoupling.map_map]
    change ((cutsetOuterPairLaw K enhanced e p p' z).prod _).map
      ((Function.update x e) ∘ Prod.snd) = _
    rw [← GlauberCoupling.map_map, OpenPath.FinProb.prod_map_snd]

lemma enhancedCutsetUpdateLawTotal_ordered (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) (p p' : I) {y x z : Configuration E}
    (hyx : y ≤ x) (hxz : x ≤ z)
    {t : Configuration E × Configuration E × Configuration E}
    (ht : (enhancedCutsetUpdateLawTotal K enhanced e p p' y x z).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  classical
  unfold enhancedCutsetUpdateLawTotal at ht
  simp only [dif_pos hxz] at ht
  exact orderedCutsetUpdateLaw_ordered K enhanced e p p' hyx hxz ht

end

end FKEnhancement


namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- Outer ordered pair and FK configuration forming one joint state. -/
abbrev LowerJointState (E : Type*) := (E → Bool × Bool) × Configuration E

/-- Lower coordinate of an indexed pair configuration. -/
def pairLower (ω : E → Bool × Bool) : Configuration E := fun e => (ω e).1

/-- Upper coordinate of an indexed pair configuration. -/
def pairUpper (ω : E → Bool × Bool) : Configuration E := fun e => (ω e).2

/-- Convert a pair of configurations to an indexed pair. -/
def configPair (yz : Configuration E × Configuration E) : E → Bool × Bool :=
  fun e => (yz.1 e, yz.2 e)

/-- Convert a triple of configurations to an indexed outer pair. -/
def triplePair (t : Configuration E × Configuration E × Configuration E) :
    E → Bool × Bool := fun e => (t.1 e, t.2.2 e)

/-- Convert a triple of configurations to a joint state. -/
def tripleJoint (t : Configuration E × Configuration E × Configuration E) :
    LowerJointState E := (triplePair t, t.2.1)

/-- The joint state is ordered in both slots. -/
def LowerJointOrdered (s : LowerJointState E) : Prop :=
  pairLower s.1 ≤ s.2 ∧ s.2 ≤ pairUpper s.1

/-- Abstract FK singleton conditionals on an off-edge recombination. -/
def abstractFKConditionals (K : E → Configuration E → Prop) (p p' : I) :
    Glauber.EdgeConditionals Bool E := fun e off =>
  boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) (fullOff e off))
    (fkRate_mem_Icc K e p p' (fullOff e off))

/-- Full update at one edge, with the ordinary rule off the enhanced set. -/
def lowerJointEdgeUpdate (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (e : E) (s : LowerJointState E) :
    OpenPath.FinProb (LowerJointState E) := by
  classical
  exact (if e ∈ enhanced then
    enhancedCutsetUpdateLawTotal K enhanced e p p' (pairLower s.1) s.2 (pairUpper s.1)
  else ordinaryCutsetUpdateLaw K e p p' (pairLower s.1) s.2 (pairUpper s.1)).map
    tripleJoint

/-- One coupled modified-block update on joint states. -/
def lowerJointBlockUpdate (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (auxiliary : List E) (e : E) :
    LowerJointState E → OpenPath.FinProb (LowerJointState E) :=
  Glauber.sweep ((Glauber.blockCoordinates enhanced.toFinset auxiliary e).map
    (lowerJointEdgeUpdate K enhanced hp))

/-- Shared-clock coupled modified jump. -/
def lowerJointJump (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E) :
    LowerJointState E → OpenPath.FinProb (LowerJointState E) :=
  Glauber.mixture ρ (lowerJointBlockUpdate K enhanced hp auxiliary)

/-- Initialize the outer pair in its stationary law and put FK on top. -/
def lowerJointInitial (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') : OpenPath.FinProb (LowerJointState E) :=
  (lowerCutsetPairLaw K enhanced hp).map (fun w => (w, pairUpper w))

/-- The finite-time coupled laws. -/
def lowerJointLaw (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E) :
    ℕ → OpenPath.FinProb (LowerJointState E) :=
  GlauberCoupling.iterateLaw (lowerJointInitial K enhanced hp)
    (lowerJointJump K enhanced hp ρ auxiliary)

lemma pairUpperOff_eq_update (e : E) (ω : E → Bool × Bool) :
    pairUpperOff e (fun f : {f : E // f ≠ e} => ω f.1) =
      Function.update (pairUpper ω) e false := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [pairUpperOff, pairUpper]
  · simp [pairUpperOff, pairUpper, hf]

lemma cutsetOuterPairLaw_update (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) (p p' : I) (z : Configuration E) (b : Bool) :
    cutsetOuterPairLaw K enhanced e p p' (Function.update z e b) =
      cutsetOuterPairLaw K enhanced e p p' z := by
  unfold cutsetOuterPairLaw
  rw [hasClosedCutset_update]

lemma configPair_update (y z : Configuration E) (e : E) (b : Bool × Bool) :
    configPair (Function.update y e b.1, Function.update z e b.2) =
      Function.update (configPair (y, z)) e b := by
  funext a
  by_cases ha : a = e
  · subst a
    simp [configPair]
  · simp [configPair, ha]

lemma configPair_lowerUpper (ω : E → Bool × Bool) :
    configPair (pairLower ω, pairUpper ω) = ω := rfl

lemma enhancedCutsetUpdateLawTotal_map_triplePair
    (K : E → Configuration E → Prop) (enhanced : Set E) (e : E)
    (p p' : I) (y x z : Configuration E) :
    (enhancedCutsetUpdateLawTotal K enhanced e p p' y x z).map triplePair =
      (cutsetOuterPairLaw K enhanced e p p' z).map
        (Function.update (configPair (y, z)) e) := by
  have h := congrArg (fun μ : OpenPath.FinProb (Configuration E × Configuration E) =>
    μ.map (fun yz => configPair (yz.1, yz.2)))
    (enhancedCutsetUpdateLawTotal_map_fst_thd K enhanced e p p' y x z)
  change (enhancedCutsetUpdateLawTotal K enhanced e p p' y x z).map
    (fun x => configPair (x.1, x.2.2)) = _
  simpa only [GlauberCoupling.map_map, Function.comp_def, configPair_update,
    triplePair, configPair] using h

lemma ordinaryCutsetUpdateLaw_map_triplePair
    (K : E → Configuration E → Prop) (e : E) (p p' : I)
    (y x z : Configuration E) :
    (ordinaryCutsetUpdateLaw K e p p' y x z).map triplePair =
      (boolPair (min (p : ℝ) (p' : ℝ)) (max (p : ℝ) (p' : ℝ))
        (le_min p.2.1 p'.2.1) min_le_max (max_le p.2.2 p'.2.2)).map
        (Function.update (configPair (y, z)) e) := by
  have h := congrArg (fun μ : OpenPath.FinProb (Configuration E × Configuration E) =>
    μ.map (fun yz => configPair (yz.1, yz.2)))
    (ordinaryCutsetUpdateLaw_map_fst_thd K e p p' y x z)
  change (ordinaryCutsetUpdateLaw K e p p' y x z).map
    (fun x => configPair (x.1, x.2.2)) = _
  simpa only [GlauberCoupling.map_map, Function.comp_def, configPair_update,
    triplePair, configPair] using h

/-- The outer marginal is the exact enhanced pair heat bath. -/
theorem lowerJointEdgeUpdate_map_fst (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (e : E) (s : LowerJointState E) :
    (lowerJointEdgeUpdate K enhanced hp e s).map Prod.fst =
      Glauber.edgeUpdate (lowerCutsetPairConditionals K enhanced hp) e s.1 := by
  classical
  unfold lowerJointEdgeUpdate
  rw [Glauber.edgeUpdate_eq_map]
  split_ifs with he
  · rw [GlauberCoupling.map_map]
    change (enhancedCutsetUpdateLawTotal K enhanced e p p'
      (pairLower s.1) s.2 (pairUpper s.1)).map triplePair = _
    rw [enhancedCutsetUpdateLawTotal_map_triplePair]
    simp only [lowerCutsetPairConditionals, if_pos he]
    rw [pairUpperOff_eq_update, cutsetOuterPairLaw_update]
    rfl
  · rw [GlauberCoupling.map_map]
    change (ordinaryCutsetUpdateLaw K e p p'
      (pairLower s.1) s.2 (pairUpper s.1)).map triplePair = _
    rw [ordinaryCutsetUpdateLaw_map_triplePair]
    simp only [lowerCutsetPairConditionals, if_neg he]
    have hpp' : (p : ℝ) ≤ (p' : ℝ) := hp
    have hb : boolPair (min (p : ℝ) (p' : ℝ)) (max (p : ℝ) (p' : ℝ))
        (le_min p.2.1 p'.2.1) min_le_max (max_le p.2.2 p'.2.2) =
        boolPair p p' p.2.1 hp p'.2.2 := by
      apply OpenPath.FinProb.ext
      rintro ⟨i, j⟩
      cases i <;> cases j <;> simp [boolPair, min_eq_left hpp', max_eq_right hpp']
    rw [hb, configPair_lowerUpper]

lemma abstractFKConditionals_apply (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (p p' : I) (e : E) (x : Configuration E) :
    abstractFKConditionals K p p' e ((Glauber.configSplit Bool e x).1) =
      boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x)
        (fkRate_mem_Icc K e p p' x) := by
  have hfull : fullOff e ((Glauber.configSplit Bool e x).1) =
      Function.update x e false := by
    simpa [fullOff] using Glauber.configSplit_symm_update e x false
  have hr : FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ)
      (fullOff e ((Glauber.configSplit Bool e x).1)) =
        FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) x := by
    rw [hfull]
    unfold FKEnhancement.fkRate
    rw [hK e x false]
  unfold abstractFKConditionals
  apply OpenPath.FinProb.ext
  intro b
  cases b <;> simp only [boolLaw_false, boolLaw_true, hr]

/-- The middle marginal is the exact FK heat bath. -/
theorem lowerJointEdgeUpdate_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (e : E) (s : LowerJointState E) :
    (lowerJointEdgeUpdate K enhanced hp e s).map Prod.snd =
      Glauber.edgeUpdate (abstractFKConditionals K p p') e s.2 := by
  classical
  unfold lowerJointEdgeUpdate
  rw [Glauber.edgeUpdate_eq_map]
  have hc : abstractFKConditionals K p p' e (fun f : {f : E // f ≠ e} => s.2 f.1) =
      boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) s.2)
        (fkRate_mem_Icc K e p p' s.2) := by
    simpa only [Glauber.configSplit_apply_fst] using
      abstractFKConditionals_apply K hK p p' e s.2
  rw [hc]
  split_ifs with he
  · rw [GlauberCoupling.map_map]
    exact enhancedCutsetUpdateLawTotal_map_snd K enhanced e p p'
      (pairLower s.1) s.2 (pairUpper s.1)
  · rw [GlauberCoupling.map_map]
    exact ordinaryCutsetUpdateLaw_map_snd K e p p'
      (pairLower s.1) s.2 (pairUpper s.1)

end

end FKEnhancement


namespace OpenPath.FinProb

variable {α : Type*} [Fintype α]

lemma map_id (μ : FinProb α) : μ.map (fun a => a) = μ := by
  classical
  apply FinProb.ext
  intro b
  rw [FinProb.mass_map]
  change (∑ a, if a = b then μ.mass a else 0) = μ.mass b
  simp

end OpenPath.FinProb

namespace Glauber

section KernelProjection

lemma map_dirac {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (s : α) :
    (FinProb.dirac s).map f = FinProb.dirac (f s) := by
  classical
  apply OpenPath.FinProb.ext
  intro b
  rw [OpenPath.FinProb.mass_map]
  simp only [FinProb.dirac]
  rw [Finset.sum_eq_single s]
  · by_cases h : f s = b
    · subst b
      simp
    · have h' : b ≠ f s := Ne.symm h
      simp [h, h']
  · intro a _ ha
    simp [ha]
  · simp

variable {α β ι : Type*} [Fintype α] [Fintype β]

/-- Projection through sequential kernels. -/
lemma map_sweep_kernel (f : α → β) (κ : ι → α → OpenPath.FinProb α)
    (κ' : ι → β → OpenPath.FinProb β)
    (h : ∀ i s, (κ i s).map f = κ' i (f s)) :
    ∀ (l : List ι) (s : α),
      ((sweep (l.map κ) s).map f) = sweep (l.map κ') (f s) := by
  intro l
  induction l with
  | nil =>
      intro s
      change (FinProb.dirac s).map f = FinProb.dirac (f s)
      exact map_dirac f s
  | cons i l ih =>
      intro s
      simp only [List.map_cons, sweep]
      unfold seq
      rw [OpenPath.FinProb.map_bind]
      simp_rw [ih]
      rw [← GlauberCoupling.bind_map, h i s]

lemma map_mixture [Fintype ι] (f : α → β) (ρ : OpenPath.FinProb ι)
    (κ : ι → α → OpenPath.FinProb α) (κ' : ι → β → OpenPath.FinProb β)
    (h : ∀ i s, (κ i s).map f = κ' i (f s)) (s : α) :
    ((mixture ρ κ s).map f) = mixture ρ κ' (f s) := by
  unfold mixture
  rw [OpenPath.FinProb.map_bind]
  simp_rw [h]

lemma map_iterateLaw (f : α → β) (K : α → OpenPath.FinProb α)
    (K' : β → OpenPath.FinProb β) (h : ∀ s, (K s).map f = K' (f s))
    (μ : OpenPath.FinProb α) (n : ℕ) :
    ((GlauberCoupling.iterateLaw μ K n).map f) =
      GlauberCoupling.iterateLaw (μ.map f) K' n := by
  induction n generalizing μ with
  | zero => rfl
  | succ n ih =>
      rw [GlauberCoupling.iterateLaw_succ, OpenPath.FinProb.map_bind]
      simp_rw [h]
      rw [← GlauberCoupling.bind_map, ih]
      rfl

end KernelProjection

end Glauber

namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- The sequential joint block projects to the pair block. -/
theorem lowerJointBlockUpdate_map_fst (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (auxiliary : List E)
    (e : E) (s : LowerJointState E) :
    (lowerJointBlockUpdate K enhanced hp auxiliary e s).map Prod.fst =
      Glauber.blockUpdate (lowerCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e s.1 := by
  unfold lowerJointBlockUpdate Glauber.blockUpdate
  exact Glauber.map_sweep_kernel Prod.fst _ _ (lowerJointEdgeUpdate_map_fst K enhanced hp)
    _ s

/-- The sequential joint block projects to the FK block. -/
theorem lowerJointBlockUpdate_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (auxiliary : List E)
    (e : E) (s : LowerJointState E) :
    (lowerJointBlockUpdate K enhanced hp auxiliary e s).map Prod.snd =
      Glauber.blockUpdate (abstractFKConditionals K p p')
        enhanced.toFinset auxiliary e s.2 := by
  unfold lowerJointBlockUpdate Glauber.blockUpdate
  exact Glauber.map_sweep_kernel Prod.snd _ _
    (lowerJointEdgeUpdate_map_snd K hK enhanced hp) _ s

/-- Outer marginal of a joint jump. -/
theorem lowerJointJump_map_fst (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E)
    (auxiliary : List E) (s : LowerJointState E) :
    (lowerJointJump K enhanced hp ρ auxiliary s).map Prod.fst =
      Glauber.modifiedJump ρ (lowerCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary s.1 := by
  unfold lowerJointJump Glauber.modifiedJump
  exact Glauber.map_mixture Prod.fst ρ _ _
    (lowerJointBlockUpdate_map_fst K enhanced hp auxiliary) s

/-- FK marginal of a joint jump. -/
theorem lowerJointJump_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E)
    (auxiliary : List E) (s : LowerJointState E) :
    (lowerJointJump K enhanced hp ρ auxiliary s).map Prod.snd =
      Glauber.modifiedJump ρ (abstractFKConditionals K p p')
        enhanced.toFinset auxiliary s.2 := by
  unfold lowerJointJump Glauber.modifiedJump
  exact Glauber.map_mixture Prod.snd ρ _ _
    (lowerJointBlockUpdate_map_snd K hK enhanced hp auxiliary) s

/-- The ordered pair marginal is stationary at every finite time. -/
theorem lowerJointLaw_map_fst (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) (n : ℕ) :
    (lowerJointLaw K enhanced hp ρ auxiliary n).map Prod.fst =
      lowerCutsetPairLaw K enhanced hp := by
  have hm := Glauber.map_iterateLaw Prod.fst
    (lowerJointJump K enhanced hp ρ auxiliary)
    (Glauber.modifiedJump ρ (lowerCutsetPairConditionals K enhanced hp)
      enhanced.toFinset auxiliary)
    (lowerJointJump_map_fst K enhanced hp ρ auxiliary)
    (lowerJointInitial K enhanced hp) n
  have hinit : (lowerJointInitial K enhanced hp).map Prod.fst =
      lowerCutsetPairLaw K enhanced hp := by
    unfold lowerJointInitial
    rw [GlauberCoupling.map_map]
    exact OpenPath.FinProb.map_id _
  rw [hinit] at hm
  change (lowerJointLaw K enhanced hp ρ auxiliary n).map Prod.fst = _ at hm
  rw [hm, GlauberCoupling.iterateLaw_eq_bind_iterate]
  exact Glauber.iterate_invariant
    (lowerCutsetPairLaw_modifiedJump_invariant K enhanced hp ρ auxiliary haux) n

/-- The lower product marginal is the target enhanced product at every time. -/
theorem lowerJointLaw_map_lower (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) (n : ℕ) :
    (lowerJointLaw K enhanced hp ρ auxiliary n).map (fun s => pairLower s.1) =
      lowerEnhancedFinProb K enhanced hp := by
  rw [show (fun s : LowerJointState E => pairLower s.1) = pairLower ∘ Prod.fst from rfl,
    ← GlauberCoupling.map_map, lowerJointLaw_map_fst K enhanced hp ρ auxiliary haux]
  exact lowerCutsetPairLaw_map_fst K enhanced hp

/-- Exact FK marginal at every finite time. -/
theorem lowerJointLaw_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E)
    (auxiliary : List E) (n : ℕ) :
    (lowerJointLaw K enhanced hp ρ auxiliary n).map Prod.snd =
      ((lowerCutsetPairLaw K enhanced hp).map pairUpper).bind
        (Glauber.iterate (Glauber.modifiedJump ρ (abstractFKConditionals K p p')
          enhanced.toFinset auxiliary) n) := by
  have hm := Glauber.map_iterateLaw Prod.snd
    (lowerJointJump K enhanced hp ρ auxiliary)
    (Glauber.modifiedJump ρ (abstractFKConditionals K p p')
      enhanced.toFinset auxiliary)
    (lowerJointJump_map_snd K hK enhanced hp ρ auxiliary)
    (lowerJointInitial K enhanced hp) n
  have hinit : (lowerJointInitial K enhanced hp).map Prod.snd =
      (lowerCutsetPairLaw K enhanced hp).map pairUpper := by
    unfold lowerJointInitial
    rw [GlauberCoupling.map_map]
    rfl
  rw [hinit] at hm
  change (lowerJointLaw K enhanced hp ρ auxiliary n).map Prod.snd =
    GlauberCoupling.iterateLaw ((lowerCutsetPairLaw K enhanced hp).map pairUpper)
      (Glauber.modifiedJump ρ (abstractFKConditionals K p p')
        enhanced.toFinset auxiliary) n at hm
  rw [GlauberCoupling.iterateLaw_eq_bind_iterate] at hm
  exact hm

/-- Order is preserved by one joint enhanced/ordinary edge update. -/
theorem lowerJointEdgeUpdate_ordered (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (e : E)
    {s : LowerJointState E} (hs : LowerJointOrdered s)
    {u : LowerJointState E} (hu : (lowerJointEdgeUpdate K enhanced hp e s).mass u ≠ 0) :
    LowerJointOrdered u := by
  classical
  obtain ⟨t, ht, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
  change t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2
  split_ifs at ht with he
  · exact enhancedCutsetUpdateLawTotal_ordered K enhanced e p p' hs.1 hs.2 ht
  · exact ordinaryCutsetUpdateLaw_ordered K e p p' hs.1 hs.2 ht

/-- Order propagation through one sequential block. -/
theorem lowerJointSweep_ordered (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') :
    ∀ (l : List E) {s : LowerJointState E}, LowerJointOrdered s →
      ∀ {u : LowerJointState E},
        (Glauber.sweep (l.map (lowerJointEdgeUpdate K enhanced hp)) s).mass u ≠ 0 →
        LowerJointOrdered u := by
  intro l
  induction l with
  | nil =>
      intro s hs u hu
      have hus : u = s := by
        by_contra hne
        simpa [Glauber.sweep, Glauber.FinProb.dirac, hne] using hu
      simpa [hus] using hs
  | cons e l ih =>
      intro s hs u hu
      simp only [List.map_cons, Glauber.sweep] at hu
      unfold Glauber.seq at hu
      obtain ⟨v, hv, hvu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact ih (lowerJointEdgeUpdate_ordered K enhanced hp e hs hv) hvu

/-- Order propagation through a joint clock jump. -/
theorem lowerJointJump_ordered (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E)
    {s : LowerJointState E} (hs : LowerJointOrdered s)
    {u : LowerJointState E} (hu : (lowerJointJump K enhanced hp ρ auxiliary s).mass u ≠ 0) :
    LowerJointOrdered u := by
  unfold lowerJointJump Glauber.mixture at hu
  obtain ⟨e, _, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
  exact lowerJointSweep_ordered K enhanced hp _ hs hu

/-- Every supported finite-time joint state is ordered. -/
theorem lowerJointLaw_ordered (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E) :
    ∀ n u, (lowerJointLaw K enhanced hp ρ auxiliary n).mass u ≠ 0 →
      LowerJointOrdered u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      change (lowerJointInitial K enhanced hp).mass u ≠ 0 at hu
      obtain ⟨w, hw, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
      exact ⟨lowerCutsetPairLaw_ordered K enhanced hw, le_rfl⟩
  | succ n ih =>
      intro u hu
      change ((lowerJointLaw K enhanced hp ρ auxiliary n).bind
        (lowerJointJump K enhanced hp ρ auxiliary)).mass u ≠ 0 at hu
      obtain ⟨s, hs, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact lowerJointJump_ordered K enhanced hp ρ auxiliary (ih s hs) hu

end

end FKEnhancement


namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology
open FK.Finite.Comparison

noncomputable section

/-- FK retention parameter packaged in the unit interval. -/
def actualLowerParameter (r : NNReal) (hr : r ≤ 1) : I :=
  ⟨(r : ℝ), r.coe_nonneg, by exact_mod_cast hr⟩

/-- FK off-connection parameter packaged in the unit interval. -/
def actualPrimeParameter {q r : NNReal} (hq : 0 < q) (hr : r ≤ 1) : I :=
  ⟨FK.prime (q : ℝ) (r : ℝ), FK.prime_mem_Icc
    (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hr)⟩

@[simp] lemma coe_actualLowerParameter (r : NNReal) (hr : r ≤ 1) :
    (actualLowerParameter r hr : ℝ) = (r : ℝ) := rfl

@[simp] lemma coe_actualPrimeParameter {q r : NNReal} (hq : 0 < q) (hr : r ≤ 1) :
    (actualPrimeParameter hq hr : ℝ) = FK.prime (q : ℝ) (r : ℝ) := rfl

/-- The `q < 1` orientation is exactly `p < p'` in the interior. -/
theorem actualLower_le_prime {q r : NNReal} (hq : 0 < q) (hr0 : 0 < r)
    (hr1 : r < 1) (hq1 : q < 1) :
    actualLowerParameter r hr1.le ≤ actualPrimeParameter hq hr1.le := by
  exact_mod_cast (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
    (by exact_mod_cast hq) (by exact_mod_cast hr0) (by exact_mod_cast hr1)
    (by exact_mod_cast hq1)).le

/-- The abstract FK conditionals at the actual pair of parameters are exactly
those of the labelled multigraph connection event. -/
lemma abstractFKConditionals_graphConnectionEvent
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr : r ≤ 1) (ξ : G.BoundaryPartition) :
    abstractFKConditionals (graphConnectionEvent G ξ)
      (actualLowerParameter r hr) (actualPrimeParameter hq hr) =
      Glauber.FKBridge.edgeConditionals G hq hr ξ := by
  funext e off
  apply OpenPath.FinProb.ext
  intro b
  have hrate := graphConnectionEvent_fkRate G q r ξ e (fullOff e off)
  cases b <;>
    simp [abstractFKConditionals, Glauber.FKBridge.edgeConditionals,
      Glauber.FKBridge.openRate, FK.Finite.Comparison.fkRate,
      Glauber.FKBridge.offConfiguration, fullOff, fullOff_apply,
      FKEnhancement.fkRate, graphConnectionEvent,
      Glauber.FKBridge.boolLaw, boolLaw, hrate] <;>
    split_ifs <;> rfl

/-- **Unconditional lower closed-cutset comparison for the actual finite FK
model.**  No finite-time coupling, stationarity equation, or enhanced-chain
convergence is assumed. -/
theorem graphConnectionEvent_lower_comparison
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1) (hq1 : q < 1)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    (ρ : OpenPath.FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    StochasticallyDominates
      (lowerEnhancedLaw (graphConnectionEvent G ξ) enhanced
        (actualLower_le_prime hq hr0 hr1 hq1))
      (G.fkMeasure hq hr1.le ξ) := by
  let p := actualLowerParameter r hr1.le
  let p' := actualPrimeParameter hq hr1.le
  let hp : p ≤ p' := actualLower_le_prime hq hr0 hr1 hq1
  let K := graphConnectionEvent G ξ
  let μ₀ := (lowerCutsetPairLaw K enhanced hp).map pairUpper
  let fkN : ℕ → OpenPath.FinProb G.Configuration := fun n => μ₀.bind
    (Glauber.iterate (Glauber.modifiedJump ρ
      (Glauber.FKBridge.edgeConditionals G hq hr1.le ξ)
      enhanced.toFinset auxiliary) n)
  let joint : ℕ → OpenPath.FinProb (G.Configuration × G.Configuration) := fun n =>
    (lowerJointLaw K enhanced hp ρ auxiliary n).map (fun s => (pairLower s.1, s.2))
  have hK : ∀ e (x : Configuration G.Edge) b,
      K e (Function.update x e b) ↔ K e x := graphConnectionEvent_update G ξ
  have hcond : abstractFKConditionals K p p' =
      Glauber.FKBridge.edgeConditionals G hq hr1.le ξ := by
    exact abstractFKConditionals_graphConnectionEvent G hq hr1.le ξ
  have hfst : ∀ n, (joint n).map Prod.fst = lowerEnhancedFinProb K enhanced hp := by
    intro n
    change ((lowerJointLaw K enhanced hp ρ auxiliary n).map
      (fun s => (pairLower s.1, s.2))).map Prod.fst = _
    rw [GlauberCoupling.map_map]
    exact lowerJointLaw_map_lower K enhanced hp ρ auxiliary haux n
  have hsnd : ∀ n, (joint n).map Prod.snd = fkN n := by
    intro n
    change ((lowerJointLaw K enhanced hp ρ auxiliary n).map
      (fun s => (pairLower s.1, s.2))).map Prod.snd = _
    rw [GlauberCoupling.map_map]
    change (lowerJointLaw K enhanced hp ρ auxiliary n).map Prod.snd = _
    simpa only [hcond] using lowerJointLaw_map_snd K hK enhanced hp ρ auxiliary n
  have horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    obtain ⟨s, hs, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ha
    exact (lowerJointLaw_ordered K enhanced hp ρ auxiliary n s hs).1
  have hlowerLim : OpenPath.FinProb.LawTendsto atTop
      (fun _ : ℕ => lowerEnhancedFinProb K enhanced hp) (lowerEnhancedFinProb K enhanced hp) := by
    intro a
    exact tendsto_const_nhds
  exact graphConnectionEvent_lower_comparison_of_tendsto_lower_and_modifiedFK
    G hq hr1.le hr0 hr1 ξ enhanced hp μ₀ ρ hρ auxiliary schedule hschedule
    (fun _ : ℕ => lowerEnhancedFinProb K enhanced hp) joint hlowerLim hfst hsnd horder

end

end FKEnhancement
