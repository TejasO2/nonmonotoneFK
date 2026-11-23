import FK.LowerPathStationarity
import FK.LowerCutsetComparison

/-!
# Stationary ordered pair for the upper open-path enhancement

The outer pair is started in its stationary ordered product law. Its lower
coordinate is the ordinary `p`-product and its upper coordinate is exactly
`upperProductLaw`. Enhanced blocks test the path in the lower coordinate and
refresh the ordered pair at `(p,p)` on a path and at `(p,p')` otherwise.
-/

noncomputable section

open scoped BigOperators Classical
open Set Filter

namespace OpenPath

open Glauber JointInvariance FK.Finite

variable {E : Type*} [Fintype E] [DecidableEq E]

lemma upperProductParameters_ge (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (h : p ≤ p') (Γ : E → Set (Finset E)) (e : E) :
    p ≤ upperProductParameters enhanced p p' hp Γ e := by
  by_cases he : e ∈ enhanced
  · rw [upperProductParameters, if_pos he]
    exact (enhancedUpper_mem_Icc hp.1 h
      (pathEventProbability_mem_Icc p hp (Γ e))).1
  · simpa [upperProductParameters, he] using h

/-- Local ordinary/upper-enhanced ordered pair law. -/
noncomputable def upperPathFactor (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) (e : E) : FinProb (Bit × Bit) :=
  coupledPair p (upperProductParameters enhanced p p' hp Γ e) hp.1
    (upperProductParameters_ge enhanced hp h Γ e)
    (upperProductParameters_mem_Icc enhanced hp hp'1 h Γ e).2

/-- Edgewise independent stationary ordered pair for the upper path chain. -/
noncomputable def upperPathPairLaw (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) : FinProb (E → Bit × Bit) :=
  FinProb.pi (upperPathFactor enhanced hp hp'1 h Γ)

theorem upperPathPairLaw_map_lower (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) :
    (upperPathPairLaw enhanced hp hp'1 h Γ).map (fun ω e => (ω e).1) =
      productLaw (fun _ : E => p) (fun _ => hp) := by
  unfold upperPathPairLaw productLaw
  rw [FinProb.pi_map]
  congr 1
  funext e
  exact coupledPair_fst _ _ _ _ _

/-- The upper marginal is exactly the target inhomogeneous product. -/
theorem upperPathPairLaw_map_upper (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) :
    (upperPathPairLaw enhanced hp hp'1 h Γ).map (fun ω e => (ω e).2) =
      upperProductLaw enhanced hp hp'1 h Γ := by
  unfold upperPathPairLaw upperProductLaw productLaw
  rw [FinProb.pi_map]
  congr 1
  funext e
  exact coupledPair_snd _ _ _ _ _

theorem upperPathPairLaw_ordered (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) {ω : E → Bit × Bit}
    (hω : (upperPathPairLaw enhanced hp hp'1 h Γ).mass ω ≠ 0) (e : E) :
    (ω e).1 ≤ (ω e).2 := by
  apply coupledPair_ordered _ _ _ _ _
  intro hz
  apply hω
  change ∏ a, _ = 0
  exact Finset.prod_eq_zero (Finset.mem_univ e) hz

/-- Lower off-edge configuration of an indexed pair, with `e` closed. -/
noncomputable def pairPathOffConfiguration (e : E)
    (off : OffConfig (Bit × Bit) E e) : Config E :=
  pathOffConfiguration e (fun f => (off f).1)

/-- Lower configuration on an auxiliary block, with every other edge closed. -/
noncomputable def auxOnlyPairConfiguration (e : E) (l : List E)
    (a : AuxiliaryIndex E e l.toFinset → Bit × Bit) : Config E :=
  auxOnlyConfiguration e l (fun x => (a x).1)

lemma somePathOpen_pairPathOff_iff_auxOnly (enhanced : Finset E) (e : E)
    (l : List E) (Γ : Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e Γ)
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) (off : OffConfig (Bit × Bit) E e) :
    SomePathOpen Γ (pairPathOffConfiguration e off) ↔
      SomePathOpen Γ (auxOnlyPairConfiguration e l
        (fun a : AuxiliaryIndex E e l.toFinset => off a.1)) := by
  apply somePathOpen_congr
  intro γ hγ f hf
  obtain ⟨hef, hauxPath⟩ := hΓ γ hγ
  have hne : f ≠ e := by
    intro hfe
    subst f
    exact hef hf
  have hfl : f ∈ l.toFinset := List.mem_toFinset.mpr ((hl f).mpr (hauxPath f hf))
  let x : AuxiliaryIndex E e l.toFinset := ⟨⟨f, hne⟩, hfl⟩
  change pathOffConfiguration e (fun g => (off g).1) f =
    auxOnlyConfiguration e l (fun a => (off a.1).1) f
  rw [pathOffConfiguration_apply_of_ne e f _ hne]
  exact (auxOnlyConfiguration_apply_aux e l (fun a => (off a.1).1) x).symm

/-- The lower-path event on an auxiliary pair block has exactly the homogeneous
ordinary `p`-product probability. -/
theorem upperPath_auxPair_event (enhanced : Finset E) (e : E) (l : List E)
    (Γ : Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e Γ)
    (Δ : E → Set (Finset E))
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    (FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
      upperPathFactor enhanced hp hp'1 h Δ a.1.1)).event
        {a | SomePathOpen Γ (auxOnlyPairConfiguration e l a)} =
      pathEventProbability p hp Γ := by
  let μ := FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
    upperPathFactor enhanced hp hp'1 h Δ a.1.1)
  let L : (AuxiliaryIndex E e l.toFinset → Bit × Bit) →
      (AuxiliaryIndex E e l.toFinset → Bit) := fun a x => (a x).1
  let C : Set (AuxiliaryIndex E e l.toFinset → Bit) :=
    {b | SomePathOpen Γ (auxOnlyConfiguration e l b)}
  have hmap : μ.map L = FinProb.pi (fun _ : AuxiliaryIndex E e l.toFinset =>
      bitLaw p hp) := by
    unfold μ L
    rw [FinProb.pi_map]
    congr 1
    funext a
    exact coupledPair_fst _ _ _ _ _
  change μ.event (L ⁻¹' C) = _
  rw [FinProb.event_preimage_map, hmap]
  have hbase := pathEventProbability_eq_aux_event enhanced e l Γ hΓ Δ hl hp p hp.2 le_rfl
  have hparams : (fun _ : AuxiliaryIndex E e l.toFinset => bitLaw p hp) =
      (fun a : AuxiliaryIndex E e l.toFinset =>
        bitLaw (lowerProductParameters enhanced p p hp Δ a.1.1)
          (lowerProductParameters_mem_Icc enhanced hp.2 hp le_rfl Δ a.1.1)) := by
    funext a
    have ha : (a.1.1 : E) ∉ enhanced :=
      (hl a.1.1).mp (List.mem_toFinset.mp a.2)
    simp [lowerProductParameters, ha]
  rw [hparams]
  exact hbase.symm

/-- One enhanced ordered-pair update based only on the old auxiliary block. -/
noncomputable def upperPathAuxKernel (enhanced : Finset E) (e : E) (l : List E)
    (Γ : Set (Finset E)) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') :
    (AuxiliaryIndex E e l.toFinset → Bit × Bit) → FinProb (Bit × Bit) :=
  fun a => if SomePathOpen Γ (auxOnlyPairConfiguration e l a) then
    coupledPair p p hp.1 le_rfl (h.trans hp'1)
  else coupledPair p p' hp.1 h hp'1

lemma upperPathAuxKernel_bind (enhanced : Finset E) (e : E) (l : List E)
    (Γ : E → Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e (Γ e))
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (heEnhanced : e ∈ enhanced) :
    (FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
      upperPathFactor enhanced hp hp'1 h Γ a.1.1)).bind
      (upperPathAuxKernel enhanced e l (Γ e) hp hp'1 h) =
        upperPathFactor enhanced hp hp'1 h Γ e := by
  let μ := FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
    upperPathFactor enhanced hp hp'1 h Γ a.1.1)
  let C : Set (AuxiliaryIndex E e l.toFinset → Bit × Bit) :=
    {a | SomePathOpen (Γ e) (auxOnlyPairConfiguration e l a)}
  have hμm : μ.bind (upperPathAuxKernel enhanced e l (Γ e) hp hp'1 h) =
      averagedUpperPair μ C p p' hp.1 hp'1 h := rfl
  rw [hμm, averagedUpperPair_eq]
  have hevent : μ.event C = pathEventProbability p hp (Γ e) :=
    upperPath_auxPair_event enhanced e l (Γ e) hΓ Γ hl hp hp'1 h
  simp [upperPathFactor, upperProductParameters, heEnhanced, hevent]

/-- Singleton conditionals of the actual upper ordered path-pair dynamics. -/
noncomputable def upperPathPairConditionals (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) : EdgeConditionals (Bit × Bit) E :=
  fun e off => if e ∈ enhanced then
    (if SomePathOpen (Γ e) (pairPathOffConfiguration e off) then
      coupledPair p p hp.1 le_rfl (h.trans hp'1)
    else coupledPair p p' hp.1 h hp'1)
  else upperPathFactor enhanced hp hp'1 h Γ e

/-- Exact stationarity of the upper ordered pair for sequential modified blocks. -/
theorem upperPathPairLaw_blockUpdate_invariant
    (enhanced : Finset E) (auxiliary : List E)
    (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) :
    Invariant (upperPathPairLaw enhanced hp hp'1 h Γ)
      (blockUpdate (upperPathPairConditionals enhanced hp hp'1 h Γ)
        enhanced auxiliary e) := by
  let ν : E → FinProb (Bit × Bit) := upperPathFactor enhanced hp hp'1 h Γ
  let c := upperPathPairConditionals enhanced hp hp'1 h Γ
  change (FinProb.pi ν).bind (blockUpdate c enhanced auxiliary e) = FinProb.pi ν
  by_cases he : e ∈ enhanced
  · let κ := upperPathAuxKernel enhanced e auxiliary (Γ e) hp hp'1 h
    have heAux : e ∉ auxiliary := by
      intro hea
      exact (haux.2 e).mp hea he
    have hcAux : ∀ f ∈ auxiliary, ∀ off, c f off = ν f := by
      intro f hf off
      have hf' : f ∉ enhanced := (haux.2 f).mp hf
      simp [c, ν, upperPathPairConditionals, hf']
    have hce : ∀ s : E → Bit × Bit, c e (fun f => s f.1) =
        κ (fun a : AuxiliaryIndex E e auxiliary.toFinset => s a.1.1) := by
      intro s
      unfold c κ upperPathPairConditionals upperPathAuxKernel
      simp only [he, if_pos]
      by_cases hpath : SomePathOpen (Γ e)
          (pathOffConfiguration e (fun f : {f : E // f ≠ e} => (s f.1).1))
      · have ha : SomePathOpen (Γ e) (auxOnlyPairConfiguration e auxiliary
            (fun a : AuxiliaryIndex E e auxiliary.toFinset => s a.1.1)) := by
          apply (somePathOpen_pairPathOff_iff_auxOnly enhanced e auxiliary (Γ e)
            (hΓ e he) haux.2 (fun f : {f : E // f ≠ e} => s f.1)).mp
          simpa [pairPathOffConfiguration] using hpath
        simp [pairPathOffConfiguration, hpath, ha]
      · have ha : ¬ SomePathOpen (Γ e) (auxOnlyPairConfiguration e auxiliary
            (fun a : AuxiliaryIndex E e auxiliary.toFinset => s a.1.1)) := by
          intro ha
          apply hpath
          have hp' := (somePathOpen_pairPathOff_iff_auxOnly enhanced e auxiliary
            (Γ e) (hΓ e he) haux.2 (fun f : {f : E // f ≠ e} => s f.1)).mpr ha
          simpa [pairPathOffConfiguration] using hp'
        simp [pairPathOffConfiguration, hpath, ha]
    have hκ : (FinProb.pi
        (fun a : AuxiliaryIndex E e auxiliary.toFinset => ν a.1.1)).bind κ = ν e := by
      exact upperPathAuxKernel_bind enhanced e auxiliary Γ (hΓ e he) haux.2
        hp hp'1 h he
    exact PathProduct.pi_bind_blockUpdate_invariant ν c auxiliary e κ enhanced he
      heAux haux.1 hcAux hce hκ
  · have hc : ∀ off, c e off = ν e := by
      intro off
      simp [c, ν, upperPathPairConditionals, he]
    have hk : blockUpdate c enhanced auxiliary e = edgeUpdate c e := by
      funext s
      simp [blockUpdate, blockCoordinates, he, sweep, Glauber.seq,
        Glauber.FinProb.bind_dirac_right]
    change (FinProb.pi ν).bind (blockUpdate c enhanced auxiliary e) = FinProb.pi ν
    rw [hk]
    exact PathProduct.pi_bind_edgeUpdate_invariant_of_constant ν c e hc

/-- The full shared-clock upper pair modified jump is stationary. -/
theorem upperPathPairLaw_modifiedJump_invariant
    (ρ : FinProb E) (enhanced : Finset E) (auxiliary : List E)
    (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    Invariant (upperPathPairLaw enhanced hp hp'1 h Γ)
      (modifiedJump ρ (upperPathPairConditionals enhanced hp hp'1 h Γ)
        enhanced auxiliary) := by
  apply mixture_invariant
  intro e
  exact upperPathPairLaw_blockUpdate_invariant enhanced auxiliary haux Γ hΓ
    hp hp'1 h e

end OpenPath


namespace OpenPath

open Glauber JointInvariance

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Closing the distinguished edge does not change an admissible path event. -/
lemma somePathOpen_pathOff_self (enhanced : Finset E) (e : E)
    (Γ : Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e Γ) (y : Config E) :
    SomePathOpen Γ (pathOffConfiguration e (fun f => y f.1)) ↔
      SomePathOpen Γ y := by
  apply somePathOpen_congr
  intro γ hγ f hf
  have hne : f ≠ e := by
    intro hfe
    subst f
    exact (hΓ γ hγ).1 hf
  exact pathOffConfiguration_apply_of_ne e f _ hne

/-- Closing the distinguished edge is recombination by `Function.update`. -/
lemma pathOffConfiguration_eq_update (e : E) (x : Config E) :
    pathOffConfiguration e (fun f => x f.1) = Function.update x e 0 := by
  exact Glauber.configSplit_symm_update e x 0

/-- Common-uniform coupling of three ordered bit laws. -/
def bitTriple (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) : FinProb (Bit × Bit × Bit) where
  mass t := if t = (1, 1, 1) then a else if t = (0, 1, 1) then b - a else
    if t = (0, 0, 1) then c - b else if t = (0, 0, 0) then 1 - c else 0
  mass_nonneg t := by
    split_ifs <;> linarith
  sum_mass := by
    simp only [Fintype.sum_prod_type]
    simp [Fin.sum_univ_two]

lemma bitTriple_map_fst_thd (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    (bitTriple a b c h0 hab hbc hc).map (fun t => (t.1, t.2.2)) =
      coupledPair a c h0 (hab.trans hbc) hc := by
  apply FinProb.ext
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [FinProb.mass_map, bitTriple, coupledPair, Fintype.sum_prod_type,
      Fin.sum_univ_two]

lemma bitTriple_map_snd (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) :
    (bitTriple a b c h0 hab hbc hc).map (fun t => t.2.1) =
      bitLaw b ⟨h0.trans hab, hbc.trans hc⟩ := by
  apply FinProb.ext
  intro i
  fin_cases i <;>
    simp [FinProb.mass_map, bitTriple, bitLaw, Fintype.sum_prod_type,
      Fin.sum_univ_two]

lemma bitTriple_ordered (a b c : ℝ) (h0 : 0 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hc : c ≤ 1) {t : Bit × Bit × Bit}
    (ht : (bitTriple a b c h0 hab hbc hc).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  rcases t with ⟨i, j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [bitTriple]

/-- Abstract FK threshold on bit configurations. -/
def pathFKRate (K : E → Config E → Prop) (e : E) (p p' : ℝ)
    (x : Config E) : ℝ := if K e x then p else p'

lemma pathFKRate_mem_Icc (K : E → Config E → Prop) (e : E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p') (x : Config E) :
    pathFKRate K e p p' x ∈ Icc (0 : ℝ) 1 := by
  unfold pathFKRate
  split_ifs
  · exact hp
  · exact ⟨hp.1.trans h, hp'1⟩

lemma pathFKRate_ge (K : E → Config E → Prop) (e : E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (h : p ≤ p') (x : Config E) :
    p ≤ pathFKRate K e p p' x := by
  unfold pathFKRate
  split_ifs
  · exact le_rfl
  · exact h

lemma pathFKRate_le (K : E → Config E → Prop) (e : E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (h : p ≤ p') (x : Config E) :
    pathFKRate K e p p' x ≤ p' := by
  unfold pathFKRate
  split_ifs
  · exact h
  · exact le_rfl

lemma pathFKRate_eq_of_path (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (Γ : E → Set (Finset E))
    (hΓK : ∀ e {y : Config E}, SomePathOpen (Γ e) y → K e y)
    (e : E) {p p' : ℝ} {y x : Config E} (hyx : y ≤ x)
    (hpath : SomePathOpen (Γ e) y) : pathFKRate K e p p' x = p := by
  rw [pathFKRate, if_pos (hK e hyx (hΓK e hpath))]

/-- Exact FK singleton conditionals in the bit convention. -/
noncomputable def abstractPathBitConditionals (K : E → Config E → Prop)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    EdgeConditionals Bit E := fun e off =>
  bitLaw (pathFKRate K e p p' (pathOffConfiguration e off))
    (pathFKRate_mem_Icc K e hp hp'1 h _)

/-- The outer law at an enhanced update, before inserting the FK coordinate. -/
noncomputable def upperPathOrderedOuterBitLaw (enhanced : Finset E)
    (Γ : E → Set (Finset E)) (e : E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y : Config E) : FinProb (Bit × Bit) :=
  if e ∈ enhanced ∧ SomePathOpen (Γ e) y then
    coupledPair p p hp.1 le_rfl (h.trans hp'1)
  else coupledPair p p' hp.1 h hp'1

/-- Exact common-uniform lower/FK/upper bit law on an ordered input. -/
noncomputable def upperPathOrderedBitLaw (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x : Config E) (_hyx : y ≤ x) : FinProb (Bit × Bit × Bit) :=
  if e ∈ enhanced ∧ SomePathOpen (Γ e) y then
    bitTriple p p p hp.1 le_rfl le_rfl (h.trans hp'1)
  else
    bitTriple p (pathFKRate K e p p' x) p' hp.1
      (pathFKRate_ge K e hp h x) (pathFKRate_le K e hp h x) hp'1

lemma upperPathOrderedBitLaw_map_fst_thd (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x : Config E) (hyx : y ≤ x) :
    (upperPathOrderedBitLaw K enhanced Γ e hp hp'1 h y x hyx).map
      (fun t => (t.1, t.2.2)) =
        upperPathOrderedOuterBitLaw enhanced Γ e hp hp'1 h y := by
  unfold upperPathOrderedBitLaw upperPathOrderedOuterBitLaw
  split_ifs <;> exact bitTriple_map_fst_thd _ _ _ _ _ _ _

lemma upperPathOrderedBitLaw_map_snd (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓK : ∀ e ∈ enhanced, ∀ {y : Config E}, SomePathOpen (Γ e) y → K e y)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x : Config E) (hyx : y ≤ x) :
    (upperPathOrderedBitLaw K enhanced Γ e hp hp'1 h y x hyx).map
      (fun t => t.2.1) = bitLaw (pathFKRate K e p p' x)
        (pathFKRate_mem_Icc K e hp hp'1 h x) := by
  classical
  unfold upperPathOrderedBitLaw
  split_ifs with he
  · have hr : pathFKRate K e p p' x = p := by
      rw [pathFKRate, if_pos (hK e hyx (hΓK e he.1 he.2))]
    have hm := bitTriple_map_snd p p p hp.1 le_rfl le_rfl (h.trans hp'1)
    simpa only [hr] using hm
  · exact bitTriple_map_snd _ _ _ _ _ _ _

lemma upperPathOrderedBitLaw_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x : Config E) (hyx : y ≤ x) {t : Bit × Bit × Bit}
    (ht : (upperPathOrderedBitLaw K enhanced Γ e hp hp'1 h y x hyx).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  classical
  unfold upperPathOrderedBitLaw at ht
  split_ifs at ht <;> exact bitTriple_ordered _ _ _ _ _ _ _ ht

/-- Configuration update attached to the ordered path bit law. -/
noncomputable def upperPathOrderedUpdateLaw (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x z : Config E) (hyx : y ≤ x) :
    FinProb (Config E × Config E × Config E) :=
  (upperPathOrderedBitLaw K enhanced Γ e hp hp'1 h y x hyx).map (fun b =>
    (Function.update y e b.1, Function.update x e b.2.1,
      Function.update z e b.2.2))

/-- Total enhanced path update. Off the ordered region an independent fallback
is used only to make both marginal identities valid on every raw state. -/
noncomputable def upperPathEnhancedUpdateLawTotal (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x z : Config E) : FinProb (Config E × Config E × Config E) := by
  classical
  exact if hyx : y ≤ x then
    upperPathOrderedUpdateLaw K enhanced Γ e hp hp'1 h y x z hyx
  else
    ((upperPathOrderedOuterBitLaw enhanced Γ e hp hp'1 h y).prod
      (bitLaw (pathFKRate K e p p' x) (pathFKRate_mem_Icc K e hp hp'1 h x))).map
      (fun b => (Function.update y e b.1.1, Function.update x e b.2,
        Function.update z e b.1.2))

/-- Ordinary update, also used away from enhanced edges. -/
noncomputable def upperPathOrdinaryUpdateLaw (K : E → Config E → Prop)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (y x z : Config E) :
    FinProb (Config E × Config E × Config E) :=
  (bitTriple p (pathFKRate K e p p' x) p' hp.1
    (pathFKRate_ge K e hp h x) (pathFKRate_le K e hp h x) hp'1).map (fun b =>
    (Function.update y e b.1, Function.update x e b.2.1,
      Function.update z e b.2.2))

end OpenPath


namespace OpenPath

open Glauber JointInvariance

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Lower coordinate of an indexed bit pair. -/
def pathPairLower (ω : E → Bit × Bit) : Config E := fun e => (ω e).1
/-- Upper coordinate of an indexed bit pair. -/
def pathPairUpper (ω : E → Bit × Bit) : Config E := fun e => (ω e).2
/-- Convert a pair of bit configurations to an indexed pair. -/
def pathConfigPair (yz : Config E × Config E) : E → Bit × Bit :=
  fun e => (yz.1 e, yz.2 e)
/-- Outer pair in a triple of bit configurations. -/
def pathTriplePair (t : Config E × Config E × Config E) : E → Bit × Bit :=
  fun e => (t.1 e, t.2.2 e)

/-- Outer path pair together with its middle FK configuration. -/
abbrev UpperPathJointState (E : Type*) := (E → Bit × Bit) × Config E

/-- Convert a configuration triple to the joint pair/FK state. -/
def pathTripleJoint (t : Config E × Config E × Config E) : UpperPathJointState E :=
  (pathTriplePair t, t.2.1)

/-- Both order inequalities in the upper joint chain. -/
def UpperPathJointOrdered (s : UpperPathJointState E) : Prop :=
  pathPairLower s.1 ≤ s.2 ∧ s.2 ≤ pathPairUpper s.1

lemma pathConfigPair_update (y z : Config E) (e : E) (b : Bit × Bit) :
    pathConfigPair (Function.update y e b.1, Function.update z e b.2) =
      Function.update (pathConfigPair (y, z)) e b := by
  funext a
  by_cases ha : a = e
  · subst a
    simp [pathConfigPair]
  · simp [pathConfigPair, ha]

lemma pathConfigPair_lowerUpper (ω : E → Bit × Bit) :
    pathConfigPair (pathPairLower ω, pathPairUpper ω) = ω := rfl

/-- Outer projection of the total enhanced path update. -/
lemma upperPathEnhancedUpdateLawTotal_map_outer (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x z : Config E) :
    (upperPathEnhancedUpdateLawTotal K enhanced Γ e hp hp'1 h y x z).map
      (fun t => (t.1, t.2.2)) =
    (upperPathOrderedOuterBitLaw enhanced Γ e hp hp'1 h y).map (fun b =>
      (Function.update y e b.1, Function.update z e b.2)) := by
  classical
  unfold upperPathEnhancedUpdateLawTotal
  split_ifs with hyx
  · unfold upperPathOrderedUpdateLaw
    rw [GlauberCoupling.map_map]
    change (upperPathOrderedBitLaw K enhanced Γ e hp hp'1 h y x hyx).map
      ((fun b : Bit × Bit => (Function.update y e b.1, Function.update z e b.2)) ∘
        (fun t : Bit × Bit × Bit => (t.1, t.2.2))) = _
    rw [← GlauberCoupling.map_map, upperPathOrderedBitLaw_map_fst_thd]
  · rw [GlauberCoupling.map_map]
    change ((upperPathOrderedOuterBitLaw enhanced Γ e hp hp'1 h y).prod _).map
      ((fun b : Bit × Bit => (Function.update y e b.1, Function.update z e b.2)) ∘
        Prod.fst) = _
    rw [← GlauberCoupling.map_map, FinProb.prod_map_fst]

/-- Middle projection of the total enhanced path update. -/
lemma upperPathEnhancedUpdateLawTotal_map_snd (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓK : ∀ e ∈ enhanced, ∀ {y : Config E}, SomePathOpen (Γ e) y → K e y)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x z : Config E) :
    (upperPathEnhancedUpdateLawTotal K enhanced Γ e hp hp'1 h y x z).map
      (fun t => t.2.1) =
    (bitLaw (pathFKRate K e p p' x) (pathFKRate_mem_Icc K e hp hp'1 h x)).map
      (Function.update x e) := by
  classical
  unfold upperPathEnhancedUpdateLawTotal
  split_ifs with hyx
  · unfold upperPathOrderedUpdateLaw
    rw [GlauberCoupling.map_map]
    change (upperPathOrderedBitLaw K enhanced Γ e hp hp'1 h y x hyx).map
      ((Function.update x e) ∘ (fun t : Bit × Bit × Bit => t.2.1)) = _
    rw [← GlauberCoupling.map_map,
      upperPathOrderedBitLaw_map_snd K hK enhanced Γ hΓK]
  · rw [GlauberCoupling.map_map]
    change ((_ : FinProb (Bit × Bit)).prod
      (bitLaw (pathFKRate K e p p' x) (pathFKRate_mem_Icc K e hp hp'1 h x))).map
      ((Function.update x e) ∘ Prod.snd) = _
    rw [← GlauberCoupling.map_map, FinProb.prod_map_snd]

lemma upperPathOrdinaryUpdateLaw_map_outer (K : E → Config E → Prop)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (y x z : Config E) :
    (upperPathOrdinaryUpdateLaw K e hp hp'1 h y x z).map
      (fun t => (t.1, t.2.2)) =
    (coupledPair p p' hp.1 h hp'1).map (fun b =>
      (Function.update y e b.1, Function.update z e b.2)) := by
  unfold upperPathOrdinaryUpdateLaw
  rw [GlauberCoupling.map_map]
  change (bitTriple p (pathFKRate K e p p' x) p' hp.1
    (pathFKRate_ge K e hp h x) (pathFKRate_le K e hp h x) hp'1).map
    ((fun b : Bit × Bit => (Function.update y e b.1, Function.update z e b.2)) ∘
      (fun t : Bit × Bit × Bit => (t.1, t.2.2))) = _
  rw [← GlauberCoupling.map_map, bitTriple_map_fst_thd]

lemma upperPathOrdinaryUpdateLaw_map_snd (K : E → Config E → Prop)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (y x z : Config E) :
    (upperPathOrdinaryUpdateLaw K e hp hp'1 h y x z).map
      (fun t => t.2.1) =
    (bitLaw (pathFKRate K e p p' x) (pathFKRate_mem_Icc K e hp hp'1 h x)).map
      (Function.update x e) := by
  unfold upperPathOrdinaryUpdateLaw
  rw [GlauberCoupling.map_map]
  change (bitTriple p (pathFKRate K e p p' x) p' hp.1
    (pathFKRate_ge K e hp h x) (pathFKRate_le K e hp h x) hp'1).map
    ((Function.update x e) ∘ (fun t : Bit × Bit × Bit => t.2.1)) = _
  rw [← GlauberCoupling.map_map, bitTriple_map_snd]

lemma upperPathEnhancedUpdateLawTotal_map_triplePair (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (y x z : Config E) :
    (upperPathEnhancedUpdateLawTotal K enhanced Γ e hp hp'1 h y x z).map
      pathTriplePair =
    (upperPathOrderedOuterBitLaw enhanced Γ e hp hp'1 h y).map
      (Function.update (pathConfigPair (y, z)) e) := by
  have hmap := congrArg (fun μ : FinProb (Config E × Config E) =>
    μ.map (fun yz => pathConfigPair (yz.1, yz.2)))
    (upperPathEnhancedUpdateLawTotal_map_outer K enhanced Γ e hp hp'1 h y x z)
  simp only [GlauberCoupling.map_map, Function.comp_def, pathConfigPair_update] at hmap
  have heq : (fun t : Config E × Config E × Config E =>
      pathConfigPair (t.1, t.2.2)) = pathTriplePair := by
    funext t e
    rfl
  rw [heq] at hmap
  exact hmap

lemma upperPathOrdinaryUpdateLaw_map_triplePair (K : E → Config E → Prop)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (y x z : Config E) :
    (upperPathOrdinaryUpdateLaw K e hp hp'1 h y x z).map pathTriplePair =
    (coupledPair p p' hp.1 h hp'1).map
      (Function.update (pathConfigPair (y, z)) e) := by
  have hmap := congrArg (fun μ : FinProb (Config E × Config E) =>
    μ.map (fun yz => pathConfigPair (yz.1, yz.2)))
    (upperPathOrdinaryUpdateLaw_map_outer K e hp hp'1 h y x z)
  simp only [GlauberCoupling.map_map, Function.comp_def, pathConfigPair_update] at hmap
  have heq : (fun t : Config E × Config E × Config E =>
      pathConfigPair (t.1, t.2.2)) = pathTriplePair := by
    funext t e
    rfl
  rw [heq] at hmap
  exact hmap

/-- The enhanced conditional law is the outer law evaluated on the full lower
configuration; admissibility makes the off-edge test equivalent. -/
lemma upperPathPairConditionals_eq_outer (enhanced : Finset E)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) (ω : E → Bit × Bit) :
    upperPathPairConditionals enhanced hp hp'1 h Γ e (fun f => ω f.1) =
      upperPathOrderedOuterBitLaw enhanced Γ e hp hp'1 h (pathPairLower ω) := by
  classical
  by_cases he : e ∈ enhanced
  · have hpoff : SomePathOpen (Γ e) (pairPathOffConfiguration e (fun f => ω f.1)) ↔
        SomePathOpen (Γ e) (pathPairLower ω) := by
      simpa [pairPathOffConfiguration, pathPairLower] using
        somePathOpen_pathOff_self enhanced e (Γ e) (hΓ e he) (pathPairLower ω)
    by_cases hfull : SomePathOpen (Γ e) (pathPairLower ω)
    · have hoff := hpoff.mpr hfull
      simp [upperPathPairConditionals, upperPathOrderedOuterBitLaw,
        he, hfull, hoff]
    · have hoff : ¬ SomePathOpen (Γ e)
          (pairPathOffConfiguration e (fun f => ω f.1)) := by
        intro hpath
        exact hfull (hpoff.mp hpath)
      simp [upperPathPairConditionals, upperPathOrderedOuterBitLaw,
        he, hfull, hoff]
  · simp [upperPathPairConditionals, upperPathOrderedOuterBitLaw,
      upperPathFactor, upperProductParameters, he]

/-- Full joint update at one edge. -/
noncomputable def upperPathJointEdgeUpdate (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) (s : UpperPathJointState E) : FinProb (UpperPathJointState E) := by
  classical
  exact (if e ∈ enhanced then
    upperPathEnhancedUpdateLawTotal K enhanced Γ e hp hp'1 h
      (pathPairLower s.1) s.2 (pathPairUpper s.1)
  else upperPathOrdinaryUpdateLaw K e hp hp'1 h
      (pathPairLower s.1) s.2 (pathPairUpper s.1)).map pathTripleJoint

/-- One shared upper joint modified block. -/
noncomputable def upperPathJointBlockUpdate (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (auxiliary : List E) (e : E) :
    UpperPathJointState E → FinProb (UpperPathJointState E) :=
  Glauber.sweep ((Glauber.blockCoordinates enhanced auxiliary e).map
    (upperPathJointEdgeUpdate K enhanced Γ hp hp'1 h))

/-- Shared-clock coupled modified jump. -/
noncomputable def upperPathJointJump (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) :
    UpperPathJointState E → FinProb (UpperPathJointState E) :=
  Glauber.mixture ρ (upperPathJointBlockUpdate K enhanced Γ hp hp'1 h auxiliary)

/-- Stationary outer pair, with FK initialized at its ordinary lower marginal. -/
noncomputable def upperPathJointInitial (enhanced : Finset E) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (Γ : E → Set (Finset E)) : FinProb (UpperPathJointState E) :=
  (upperPathPairLaw enhanced hp hp'1 h Γ).map (fun w => (w, pathPairLower w))

/-- Finite-time upper joint laws. -/
noncomputable def upperPathJointLaw (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) : ℕ → FinProb (UpperPathJointState E) :=
  GlauberCoupling.iterateLaw (upperPathJointInitial enhanced hp hp'1 h Γ)
    (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary)

/-- The one-edge outer projection is exactly the stationary pair heat bath. -/
theorem upperPathJointEdgeUpdate_map_fst (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) (s : UpperPathJointState E) :
    (upperPathJointEdgeUpdate K enhanced Γ hp hp'1 h e s).map Prod.fst =
      Glauber.edgeUpdate (upperPathPairConditionals enhanced hp hp'1 h Γ) e s.1 := by
  classical
  unfold upperPathJointEdgeUpdate
  rw [Glauber.edgeUpdate_eq_map, upperPathPairConditionals_eq_outer enhanced Γ hΓ]
  split_ifs with he
  · rw [GlauberCoupling.map_map]
    change (upperPathEnhancedUpdateLawTotal K enhanced Γ e hp hp'1 h
      (pathPairLower s.1) s.2 (pathPairUpper s.1)).map pathTriplePair = _
    rw [upperPathEnhancedUpdateLawTotal_map_triplePair,
      pathConfigPair_lowerUpper]
  · rw [GlauberCoupling.map_map]
    change (upperPathOrdinaryUpdateLaw K e hp hp'1 h
      (pathPairLower s.1) s.2 (pathPairUpper s.1)).map pathTriplePair = _
    rw [upperPathOrdinaryUpdateLaw_map_triplePair, pathConfigPair_lowerUpper]
    simp [upperPathOrderedOuterBitLaw, he]

/-- Recombination makes the abstract bit conditional independent of the value
at the distinguished edge, as required for the exact middle projection. -/
lemma abstractPathBitConditionals_apply (K : E → Config E → Prop)
    (hKupdate : ∀ e (x : Config E) b, K e (Function.update x e b) ↔ K e x)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) (x : Config E) :
    abstractPathBitConditionals K hp hp'1 h e (fun f => x f.1) =
      bitLaw (pathFKRate K e p p' x) (pathFKRate_mem_Icc K e hp hp'1 h x) := by
  have hr : pathFKRate K e p p' (pathOffConfiguration e (fun f => x f.1)) =
      pathFKRate K e p p' x := by
    rw [pathOffConfiguration_eq_update]
    unfold pathFKRate
    rw [hKupdate e x 0]
  simp only [abstractPathBitConditionals, hr]

/-- The middle marginal is exactly the FK heat bath in the bit convention. -/
theorem upperPathJointEdgeUpdate_map_snd (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (hKupdate : ∀ e (x : Config E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓK : ∀ e ∈ enhanced, ∀ {y : Config E}, SomePathOpen (Γ e) y → K e y)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) (s : UpperPathJointState E) :
    (upperPathJointEdgeUpdate K enhanced Γ hp hp'1 h e s).map Prod.snd =
      Glauber.edgeUpdate (abstractPathBitConditionals K hp hp'1 h) e s.2 := by
  classical
  unfold upperPathJointEdgeUpdate
  rw [Glauber.edgeUpdate_eq_map, abstractPathBitConditionals_apply K hKupdate]
  split_ifs with he
  · rw [GlauberCoupling.map_map]
    exact upperPathEnhancedUpdateLawTotal_map_snd K hK enhanced Γ hΓK e
      hp hp'1 h _ _ _
  · rw [GlauberCoupling.map_map]
    exact upperPathOrdinaryUpdateLaw_map_snd K e hp hp'1 h _ _ _

end OpenPath


namespace OpenPath

open Glauber JointInvariance

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Sequential joint blocks project to the ordered-pair blocks. -/
theorem upperPathJointBlockUpdate_map_fst (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (auxiliary : List E) (e : E) (s : UpperPathJointState E) :
    (upperPathJointBlockUpdate K enhanced Γ hp hp'1 h auxiliary e s).map Prod.fst =
      Glauber.blockUpdate (upperPathPairConditionals enhanced hp hp'1 h Γ)
        enhanced auxiliary e s.1 := by
  unfold upperPathJointBlockUpdate Glauber.blockUpdate
  exact Glauber.map_sweep_kernel Prod.fst _ _
    (upperPathJointEdgeUpdate_map_fst K enhanced Γ hΓ hp hp'1 h) _ s

/-- Sequential joint blocks project to the exact FK blocks. -/
theorem upperPathJointBlockUpdate_map_snd (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (hKupdate : ∀ e (x : Config E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓK : ∀ e ∈ enhanced, ∀ {y : Config E}, SomePathOpen (Γ e) y → K e y)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (auxiliary : List E) (e : E) (s : UpperPathJointState E) :
    (upperPathJointBlockUpdate K enhanced Γ hp hp'1 h auxiliary e s).map Prod.snd =
      Glauber.blockUpdate (abstractPathBitConditionals K hp hp'1 h)
        enhanced auxiliary e s.2 := by
  unfold upperPathJointBlockUpdate Glauber.blockUpdate
  exact Glauber.map_sweep_kernel Prod.snd _ _
    (upperPathJointEdgeUpdate_map_snd K hK hKupdate enhanced Γ hΓK hp hp'1 h) _ s

/-- Outer marginal of a joint jump. -/
theorem upperPathJointJump_map_fst (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) (s : UpperPathJointState E) :
    (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary s).map Prod.fst =
      Glauber.modifiedJump ρ (upperPathPairConditionals enhanced hp hp'1 h Γ)
        enhanced auxiliary s.1 := by
  unfold upperPathJointJump Glauber.modifiedJump
  exact Glauber.map_mixture Prod.fst ρ _ _
    (upperPathJointBlockUpdate_map_fst K enhanced Γ hΓ hp hp'1 h auxiliary) s

/-- FK marginal of a joint jump. -/
theorem upperPathJointJump_map_snd (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (hKupdate : ∀ e (x : Config E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓK : ∀ e ∈ enhanced, ∀ {y : Config E}, SomePathOpen (Γ e) y → K e y)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) (s : UpperPathJointState E) :
    (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary s).map Prod.snd =
      Glauber.modifiedJump ρ (abstractPathBitConditionals K hp hp'1 h)
        enhanced auxiliary s.2 := by
  unfold upperPathJointJump Glauber.modifiedJump
  exact Glauber.map_mixture Prod.snd ρ _ _
    (upperPathJointBlockUpdate_map_snd K hK hKupdate enhanced Γ hΓK
      hp hp'1 h auxiliary) s

/-- The ordered upper pair marginal is stationary at every finite time. -/
theorem upperPathJointLaw_map_fst (K : E → Config E → Prop)
    (enhanced : Finset E) (auxiliary : List E)
    (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (n : ℕ) :
    (upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).map Prod.fst =
      upperPathPairLaw enhanced hp hp'1 h Γ := by
  have hm := Glauber.map_iterateLaw Prod.fst
    (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary)
    (Glauber.modifiedJump ρ (upperPathPairConditionals enhanced hp hp'1 h Γ)
      enhanced auxiliary)
    (upperPathJointJump_map_fst K enhanced Γ hΓ hp hp'1 h ρ auxiliary)
    (upperPathJointInitial enhanced hp hp'1 h Γ) n
  have hinit : (upperPathJointInitial enhanced hp hp'1 h Γ).map Prod.fst =
      upperPathPairLaw enhanced hp hp'1 h Γ := by
    unfold upperPathJointInitial
    rw [GlauberCoupling.map_map]
    exact OpenPath.FinProb.map_id _
  rw [hinit] at hm
  change (upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).map Prod.fst = _ at hm
  rw [hm, GlauberCoupling.iterateLaw_eq_bind_iterate]
  exact Glauber.iterate_invariant
    (upperPathPairLaw_modifiedJump_invariant ρ enhanced auxiliary haux Γ hΓ
      hp hp'1 h) n

/-- The enhanced upper marginal is constant and exact at every finite time. -/
theorem upperPathJointLaw_map_upper (K : E → Config E → Prop)
    (enhanced : Finset E) (auxiliary : List E)
    (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (n : ℕ) :
    (upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).map
      (fun s => pathPairUpper s.1) = upperProductLaw enhanced hp hp'1 h Γ := by
  rw [show (fun s : UpperPathJointState E => pathPairUpper s.1) =
      pathPairUpper ∘ Prod.fst from rfl,
    ← GlauberCoupling.map_map,
    upperPathJointLaw_map_fst K enhanced auxiliary haux Γ hΓ hp hp'1 h ρ]
  exact upperPathPairLaw_map_upper enhanced hp hp'1 h Γ

/-- Exact bit FK marginal at every finite time, initialized at the ordinary
lower marginal of the stationary pair. -/
theorem upperPathJointLaw_map_snd (K : E → Config E → Prop)
    (hK : ∀ e {y x : Config E}, y ≤ x → K e y → K e x)
    (hKupdate : ∀ e (x : Config E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    (hΓK : ∀ e ∈ enhanced, ∀ {y : Config E}, SomePathOpen (Γ e) y → K e y)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) (n : ℕ) :
    (upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).map Prod.snd =
      ((upperPathPairLaw enhanced hp hp'1 h Γ).map pathPairLower).bind
        (Glauber.iterate (Glauber.modifiedJump ρ
          (abstractPathBitConditionals K hp hp'1 h) enhanced auxiliary) n) := by
  have hm := Glauber.map_iterateLaw Prod.snd
    (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary)
    (Glauber.modifiedJump ρ (abstractPathBitConditionals K hp hp'1 h)
      enhanced auxiliary)
    (upperPathJointJump_map_snd K hK hKupdate enhanced Γ hΓK hp hp'1 h ρ auxiliary)
    (upperPathJointInitial enhanced hp hp'1 h Γ) n
  have hinit : (upperPathJointInitial enhanced hp hp'1 h Γ).map Prod.snd =
      (upperPathPairLaw enhanced hp hp'1 h Γ).map pathPairLower := by
    unfold upperPathJointInitial
    rw [GlauberCoupling.map_map]
    rfl
  rw [hinit] at hm
  change (upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).map Prod.snd =
    GlauberCoupling.iterateLaw ((upperPathPairLaw enhanced hp hp'1 h Γ).map pathPairLower)
      (Glauber.modifiedJump ρ (abstractPathBitConditionals K hp hp'1 h)
        enhanced auxiliary) n at hm
  rw [GlauberCoupling.iterateLaw_eq_bind_iterate] at hm
  exact hm

/-- Order preservation for an ordered configuration update. -/
lemma upperPathOrderedUpdateLaw_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    {y x z : Config E} (hyx : y ≤ x) (hxz : x ≤ z)
    {t : Config E × Config E × Config E}
    (ht : (upperPathOrderedUpdateLaw K enhanced Γ e hp hp'1 h y x z hyx).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  obtain ⟨b, hb, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ht
  have hb' := upperPathOrderedBitLaw_ordered K enhanced Γ e hp hp'1 h y x hyx hb
  constructor <;> intro a <;> by_cases ha : a = e
  · subst a
    simpa using hb'.1
  · simp only [Function.update_of_ne ha]
    exact hyx a
  · subst a
    simpa using hb'.2
  · simp only [Function.update_of_ne ha]
    exact hxz a

lemma upperPathEnhancedUpdateLawTotal_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E)) (e : E)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    {y x z : Config E} (hyx : y ≤ x) (hxz : x ≤ z)
    {t : Config E × Config E × Config E}
    (ht : (upperPathEnhancedUpdateLawTotal K enhanced Γ e hp hp'1 h y x z).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  classical
  unfold upperPathEnhancedUpdateLawTotal at ht
  simp only [dif_pos hyx] at ht
  exact upperPathOrderedUpdateLaw_ordered K enhanced Γ e hp hp'1 h hyx hxz ht

lemma upperPathOrdinaryUpdateLaw_ordered (K : E → Config E → Prop)
    (e : E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') {y x z : Config E}
    (hyx : y ≤ x) (hxz : x ≤ z) {t : Config E × Config E × Config E}
    (ht : (upperPathOrdinaryUpdateLaw K e hp hp'1 h y x z).mass t ≠ 0) :
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 := by
  obtain ⟨b, hb, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ht
  have hb' := bitTriple_ordered _ _ _ _ _ _ _ hb
  constructor <;> intro a <;> by_cases ha : a = e
  · subst a
    simpa using hb'.1
  · simp only [Function.update_of_ne ha]
    exact hyx a
  · subst a
    simpa using hb'.2
  · simp only [Function.update_of_ne ha]
    exact hxz a

/-- Order is preserved by one joint path update. -/
theorem upperPathJointEdgeUpdate_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (e : E) {s : UpperPathJointState E} (hs : UpperPathJointOrdered s)
    {u : UpperPathJointState E}
    (hu : (upperPathJointEdgeUpdate K enhanced Γ hp hp'1 h e s).mass u ≠ 0) :
    UpperPathJointOrdered u := by
  classical
  obtain ⟨t, ht, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
  change t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2
  split_ifs at ht with he
  · exact upperPathEnhancedUpdateLawTotal_ordered K enhanced Γ e hp hp'1 h
      hs.1 hs.2 ht
  · exact upperPathOrdinaryUpdateLaw_ordered K e hp hp'1 h hs.1 hs.2 ht

/-- Order propagation through one sequential joint block. -/
theorem upperPathJointSweep_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    ∀ (l : List E) {s : UpperPathJointState E}, UpperPathJointOrdered s →
      ∀ {u : UpperPathJointState E},
        (Glauber.sweep (l.map (upperPathJointEdgeUpdate K enhanced Γ hp hp'1 h)) s).mass u ≠ 0 →
        UpperPathJointOrdered u := by
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
      exact ih (upperPathJointEdgeUpdate_ordered K enhanced Γ hp hp'1 h e hs hv) hvu

/-- Order propagation through a shared-clock joint jump. -/
theorem upperPathJointJump_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) {s : UpperPathJointState E}
    (hs : UpperPathJointOrdered s) {u : UpperPathJointState E}
    (hu : (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary s).mass u ≠ 0) :
    UpperPathJointOrdered u := by
  unfold upperPathJointJump Glauber.mixture at hu
  obtain ⟨e, _, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
  exact upperPathJointSweep_ordered K enhanced Γ hp hp'1 h _ hs hu

/-- Every supported finite-time joint state has lower ≤ FK ≤ upper. -/
theorem upperPathJointLaw_ordered (K : E → Config E → Prop)
    (enhanced : Finset E) (Γ : E → Set (Finset E))
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (ρ : FinProb E) (auxiliary : List E) :
    ∀ n u, (upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).mass u ≠ 0 →
      UpperPathJointOrdered u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      change (upperPathJointInitial enhanced hp hp'1 h Γ).mass u ≠ 0 at hu
      obtain ⟨w, hw, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
      exact ⟨le_rfl, upperPathPairLaw_ordered enhanced hp hp'1 h Γ hw⟩
  | succ n ih =>
      intro u hu
      change ((upperPathJointLaw K enhanced Γ hp hp'1 h ρ auxiliary n).bind
        (upperPathJointJump K enhanced Γ hp hp'1 h ρ auxiliary)).mass u ≠ 0 at hu
      obtain ⟨s, hs, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact upperPathJointJump_ordered K enhanced Γ hp hp'1 h ρ auxiliary (ih s hs) hu

end OpenPath


namespace OpenPath

open Glauber

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Transport Boolean singleton conditionals to bits. -/
noncomputable def bitTransportConditionals (c : EdgeConditionals Bool E) :
    EdgeConditionals Bit E := fun e off =>
  (c e (fun f => bitToBool (off f))).map boolToBit

@[simp] lemma configOfBool_update (ω : E → Bool) (e : E) (b : Bool) :
    configOfBool (Function.update ω e b) =
      Function.update (configOfBool ω) e (boolToBit b) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [configOfBool]
  · simp [configOfBool, hf]

/-- The Boolean-to-bit equivalence commutes with an edge heat-bath update. -/
lemma edgeUpdate_map_configOfBool (c : EdgeConditionals Bool E) (e : E)
    (ω : E → Bool) :
    (edgeUpdate c e ω).map configOfBool =
      edgeUpdate (bitTransportConditionals c) e (configOfBool ω) := by
  have hoff : (fun f : {f : E // f ≠ e} => bitToBool ((configOfBool ω) f.1)) =
      (fun f : {f : E // f ≠ e} => ω f.1) := by
    funext f
    exact bitBoolEquiv.right_inv (ω f.1)
  have hfun : configOfBool ∘ Function.update ω e =
      Function.update (configOfBool ω) e ∘ boolToBit := by
    funext b
    exact configOfBool_update ω e b
  rw [edgeUpdate_eq_map, edgeUpdate_eq_map]
  simp only [GlauberCoupling.map_map, bitTransportConditionals, hoff, hfun]

/-- The equivalence commutes with sequential modified blocks. -/
lemma blockUpdate_map_configOfBool (c : EdgeConditionals Bool E)
    (enhanced : Finset E) (auxiliary : List E) (e : E) (ω : E → Bool) :
    (blockUpdate c enhanced auxiliary e ω).map configOfBool =
      blockUpdate (bitTransportConditionals c) enhanced auxiliary e (configOfBool ω) := by
  unfold blockUpdate
  exact Glauber.map_sweep_kernel configOfBool _ _
    (edgeUpdate_map_configOfBool c) _ ω

/-- The equivalence commutes with a shared-clock modified jump. -/
lemma modifiedJump_map_configOfBool (c : EdgeConditionals Bool E) (ρ : FinProb E)
    (enhanced : Finset E) (auxiliary : List E) (ω : E → Bool) :
    (modifiedJump ρ c enhanced auxiliary ω).map configOfBool =
      modifiedJump ρ (bitTransportConditionals c) enhanced auxiliary (configOfBool ω) := by
  unfold modifiedJump
  exact Glauber.map_mixture configOfBool ρ _ _
    (blockUpdate_map_configOfBool c enhanced auxiliary) ω

/-- The equivalence commutes with every finite-time FK marginal. -/
lemma bind_iterate_map_configOfBool (μ : FinProb (E → Bool)) (ρ : FinProb E)
    (c : EdgeConditionals Bool E) (enhanced : Finset E) (auxiliary : List E) (n : ℕ) :
    (μ.bind (iterate (modifiedJump ρ c enhanced auxiliary) n)).map configOfBool =
      (μ.map configOfBool).bind
        (iterate (modifiedJump ρ (bitTransportConditionals c) enhanced auxiliary) n) := by
  have hm := Glauber.map_iterateLaw configOfBool
    (modifiedJump ρ c enhanced auxiliary)
    (modifiedJump ρ (bitTransportConditionals c) enhanced auxiliary)
    (modifiedJump_map_configOfBool c ρ enhanced auxiliary) μ n
  simpa only [GlauberCoupling.iterateLaw_eq_bind_iterate] using hm

namespace FKEnhancement

open FK.Finite

/-- The actual FK conditionals transported to open-path bits. -/
noncomputable def fkBitConditionals (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) : EdgeConditionals Bit G.Edge :=
  OpenPath.bitTransportConditionals (Glauber.FKBridge.edgeConditionals G hq hp ξ)

/-- Interior convergence of the bit FK chain, transported from the established
Boolean theorem rather than assumed for a new joint chain. -/
theorem fkBit_modifiedJump_tendsto (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (μ : FinProb (G.Edge → Bool))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (enhanced : Finset G.Edge) (auxiliary schedule : List G.Edge)
    (hschedule : ∀ e, e ∈ schedule) :
    OpenPath.FinProb.LawTendsto atTop
      (fun n => (μ.map OpenPath.configOfBool).bind
        (Glauber.iterate (Glauber.modifiedJump ρ (fkBitConditionals G hq hp ξ)
          enhanced auxiliary) n))
      (OpenPath.fkBitFinProb G hq hp ξ) := by
  have ht := Glauber.FKBridge.fk_modifiedJump_tendsto G hq hp hp0 hp1 μ ρ hρ ξ
    enhanced auxiliary schedule hschedule
  have hmap := OpenPath.FinProb.LawTendsto.map ht OpenPath.configOfBool
  simpa only [OpenPath.fkBitFinProb_eq_map, OpenPath.bind_iterate_map_configOfBool,
    fkBitConditionals] using hmap

end FKEnhancement

end OpenPath


namespace FKEnhancement

open OpenPath Glauber
open FK.Finite

/-- The actual multigraph connection event on open-path bit configurations. -/
def bitGraphConnectionEvent (G : LabelledMultigraph) (ξ : G.BoundaryPartition) :
    G.Edge → Config G.Edge → Prop := fun e ω =>
  graphConnectionEvent G ξ e (configToBool ω)

@[simp] lemma configToBool_update_bit {E : Type*} [DecidableEq E]
    (x : Config E) (e : E) (b : Bit) :
    configToBool (Function.update x e b) =
      Function.update (configToBool x) e (bitToBool b) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [configToBool]
  · simp [configToBool, hf]

/-- Bit off-edge recombination is exactly the actual Boolean FK off-edge
configuration after transport. -/
lemma configToBool_pathOffConfiguration (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (e : G.Edge) (off : OffConfig Bit G.Edge e) :
    configToBool (pathOffConfiguration e off) =
      Glauber.FKBridge.offConfiguration G ξ e (fun f => bitToBool (off f)) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [pathOffConfiguration, Glauber.configSplit, Equiv.funSplitAt_symm_apply,
      configToBool, Glauber.FKBridge.offConfiguration, bitToBool, boolToBit]
  · change bitToBool (pathOffConfiguration e off f) = _
    rw [pathOffConfiguration_apply_of_ne e f off hf]
    simp [configToBool, Glauber.FKBridge.offConfiguration, Glauber.configSplit,
      Equiv.funSplitAt_symm_apply, hf]

/-- The actual graph event is monotone in the bit order. -/
lemma bitGraphConnectionEvent_mono (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (e : G.Edge) {y x : Config G.Edge}
    (hyx : y ≤ x) (hconn : bitGraphConnectionEvent G ξ e y) :
    bitGraphConnectionEvent G ξ e x := by
  exact FK.Finite.WiredEnhancement.endpointsConnectedWithout_configToBool_mono
    G ξ e hyx hconn

/-- The actual graph event is independent of the distinguished bit. -/
lemma bitGraphConnectionEvent_update (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (e : G.Edge) (x : Config G.Edge) (b : Bit) :
    bitGraphConnectionEvent G ξ e (Function.update x e b) ↔
      bitGraphConnectionEvent G ξ e x := by
  rw [bitGraphConnectionEvent, configToBool_update_bit]
  exact graphConnectionEvent_update G ξ e (configToBool x) (bitToBool b)

/-- The abstract bit singleton conditional used by the coupled path chain is
exactly the actual FK conditional transported from Booleans. -/
theorem abstractPathBitConditionals_graph (G : LabelledMultigraph)
    {q r : NNReal} (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1)
    (h : (r : ℝ) ≤ FK.prime (q : ℝ) (r : ℝ)) (ξ : G.BoundaryPartition) :
    abstractPathBitConditionals (bitGraphConnectionEvent G ξ)
      ⟨r.coe_nonneg, by exact_mod_cast hr1.le⟩
      (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity)
        (by exact_mod_cast hr1.le)).2 h =
      OpenPath.FKEnhancement.fkBitConditionals G hq hr1.le ξ := by
  funext e off
  apply OpenPath.FinProb.ext
  intro b
  fin_cases b <;>
    simp [abstractPathBitConditionals, OpenPath.FKEnhancement.fkBitConditionals,
      bitTransportConditionals, OpenPath.FinProb.mass_map, Fintype.sum_bool,
      Glauber.FKBridge.edgeConditionals, Glauber.FKBridge.boolLaw,
      Glauber.FKBridge.openRate, bitGraphConnectionEvent, graphConnectionEvent,
      pathFKRate, configToBool_pathOffConfiguration, boolToBit, bitToBool] <;> rfl

end FKEnhancement


namespace FKEnhancement

open OpenPath Glauber
open FK.Finite
open Filter

/-- **Unconditional upper open-path comparison at the actual FK prime
parameter.** The stationary ordered outer pair and the exact FK middle dynamics
are constructed internally. There is no joint-limit, ordered-coupling,
stationarity, or enhanced-convergence hypothesis. -/
theorem graphConnectionEvent_upper_path_comparison_of_le
    (G : LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1)
    (h : (r : ℝ) ≤ FK.prime (q : ℝ) (r : ℝ))
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    (hΓK : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → graphConnectionEvent G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge) (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    StochasticallyDominates (G.fkPMF hq hr1.le ξ).toMeasure
      ((upperProductPMF enhanced
        ⟨r.coe_nonneg, by exact_mod_cast hr1.le⟩
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity)
          (by exact_mod_cast hr1.le)).2 h Γ).map configToBool).toMeasure := by
  let hp : (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨r.coe_nonneg, by exact_mod_cast hr1.le⟩
  let hpP : FK.prime (q : ℝ) (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hr1.le)
  let K : G.Edge → Config G.Edge → Prop := bitGraphConnectionEvent G ξ
  let cbit : EdgeConditionals Bit G.Edge :=
    abstractPathBitConditionals K hp hpP.2 h
  let μ₀ : FinProb (Config G.Edge) :=
    (upperPathPairLaw enhanced hp hpP.2 h Γ).map pathPairLower
  let μbool : FinProb (G.Edge → Bool) := μ₀.map configToBool
  let fkN : ℕ → FinProb (Config G.Edge) := fun n => μ₀.bind
    (Glauber.iterate (Glauber.modifiedJump ρ cbit enhanced auxiliary) n)
  let joint : ℕ → FinProb (Config G.Edge × Config G.Edge) := fun n =>
    (upperPathJointLaw K enhanced Γ hp hpP.2 h ρ auxiliary n).map
      (fun s => (s.2, pathPairUpper s.1))
  have hK : ∀ e {y x : Config G.Edge}, y ≤ x → K e y → K e x := by
    intro e y x hyx hconn
    exact bitGraphConnectionEvent_mono G ξ e hyx hconn
  have hKupdate : ∀ e (x : Config G.Edge) b,
      K e (Function.update x e b) ↔ K e x := by
    intro e x b
    exact bitGraphConnectionEvent_update G ξ e x b
  have hΓbit : ∀ e ∈ enhanced, ∀ {y : Config G.Edge},
      SomePathOpen (Γ e) y → K e y := by
    intro e he y hpath
    exact hΓK e he hpath
  have hcond : cbit = OpenPath.FKEnhancement.fkBitConditionals G hq hr1.le ξ := by
    exact abstractPathBitConditionals_graph G hq hr0 hr1 h ξ
  have hinit : μbool.map configOfBool = μ₀ := by
    unfold μbool
    rw [GlauberCoupling.map_map]
    have heq : configOfBool ∘ configToBool = (id : Config G.Edge → Config G.Edge) := by
      funext ω
      exact (configBitBoolEquiv G.Edge).left_inv ω
    rw [heq]
    exact OpenPath.FinProb.map_id _
  have hfkLim : FinProb.LawTendsto atTop fkN (fkBitFinProb G hq hr1.le ξ) := by
    have ht := OpenPath.FKEnhancement.fkBit_modifiedJump_tendsto G hq hr1.le hr0 hr1
      ξ μbool ρ hρ enhanced auxiliary schedule hschedule
    rw [hinit, ← hcond] at ht
    exact ht
  have hfst : ∀ n, (joint n).map Prod.fst = fkN n := by
    intro n
    change ((upperPathJointLaw K enhanced Γ hp hpP.2 h ρ auxiliary n).map
      (fun s => (s.2, pathPairUpper s.1))).map Prod.fst = _
    rw [GlauberCoupling.map_map]
    exact upperPathJointLaw_map_snd K hK hKupdate enhanced Γ hΓbit
      hp hpP.2 h ρ auxiliary n
  have hsnd : ∀ n, (joint n).map Prod.snd =
      upperProductLaw enhanced hp hpP.2 h Γ := by
    intro n
    change ((upperPathJointLaw K enhanced Γ hp hpP.2 h ρ auxiliary n).map
      (fun s => (s.2, pathPairUpper s.1))).map Prod.snd = _
    rw [GlauberCoupling.map_map]
    exact upperPathJointLaw_map_upper K enhanced auxiliary haux Γ hΓ
      hp hpP.2 h ρ n
  have horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    obtain ⟨s, hs, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ha
    exact (upperPathJointLaw_ordered K enhanced Γ hp hpP.2 h ρ auxiliary n s hs).2
  have hupperLim : FinProb.LawTendsto atTop
      (fun _ : ℕ => upperProductLaw enhanced hp hpP.2 h Γ)
      (upperProductLaw enhanced hp hpP.2 h Γ) := by
    intro a
    exact tendsto_const_nhds
  exact OpenPath.upper_comparison_bool_of_tendsto_orderedDynamics
    G hq hr1.le ξ enhanced hp hpP.2 h Γ fkN
      (fun _ : ℕ => upperProductLaw enhanced hp hpP.2 h Γ) joint
      hfkLim hupperLim hfst hsnd horder

/-- The `q < 1` instance of the actual upper open-path comparison. -/
theorem graphConnectionEvent_upper_path_comparison
    (G : LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1) (hq1 : q < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    (hΓK : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → graphConnectionEvent G ξ e (configToBool ω))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge) (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    StochasticallyDominates (G.fkPMF hq hr1.le ξ).toMeasure
      ((upperProductPMF enhanced
        ⟨r.coe_nonneg, by exact_mod_cast hr1.le⟩
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity)
          (by exact_mod_cast hr1.le)).2
        (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
          (by exact_mod_cast hq) (by exact_mod_cast hr0)
          (by exact_mod_cast hr1) (by exact_mod_cast hq1)).le Γ).map
            configToBool).toMeasure := by
  exact graphConnectionEvent_upper_path_comparison_of_le G hq hr0 hr1
    (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
      (by exact_mod_cast hq) (by exact_mod_cast hr0)
      (by exact_mod_cast hr1) (by exact_mod_cast hq1)).le
    ξ enhanced Γ hΓ hΓK ρ hρ auxiliary haux schedule hschedule

end FKEnhancement
