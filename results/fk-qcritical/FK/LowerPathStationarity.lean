import FK.PathProductInvariance

noncomputable section

open scoped BigOperators Classical
open Set Filter

namespace OpenPath

open Glauber JointInvariance FK.Finite FK.Finite

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Embed an auxiliary configuration, setting every other coordinate closed. -/
noncomputable def auxOnlyConfiguration (e : E) (l : List E)
    (a : AuxiliaryIndex E e l.toFinset → Bit) : Config E :=
  (indexedBlockEquiv e l.toFinset).symm ⟨⟨0, a⟩, fun _ => 0⟩

@[simp] lemma auxOnlyConfiguration_apply_aux (e : E) (l : List E)
    (a : AuxiliaryIndex E e l.toFinset → Bit)
    (x : AuxiliaryIndex E e l.toFinset) :
    auxOnlyConfiguration e l a x.1.1 = a x := by
  exact PathProduct.indexedBlockEquiv_symm_apply_aux e l.toFinset 0 a _ x

lemma somePathOpen_congr {Γ : Set (Finset E)} {s t : Config E}
    (h : ∀ γ ∈ Γ, ∀ f ∈ γ, s f = t f) :
    SomePathOpen Γ s ↔ SomePathOpen Γ t := by
  constructor <;> rintro ⟨γ, hγ, hopen⟩
  · refine ⟨γ, hγ, ?_⟩
    intro f hf
    rw [← h γ hγ f hf]
    exact hopen f hf
  · refine ⟨γ, hγ, ?_⟩
    intro f hf
    rw [h γ hγ f hf]
    exact hopen f hf

/-- An admissible path event sees exactly the old auxiliary restriction. -/
lemma somePathOpen_iff_auxOnly (enhanced : Finset E) (e : E) (l : List E)
    (Γ : Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e Γ)
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) (s : Config E) :
    SomePathOpen Γ s ↔
      SomePathOpen Γ (auxOnlyConfiguration e l
        (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1)) := by
  apply somePathOpen_congr
  intro γ hγ f hf
  obtain ⟨hef, hauxPath⟩ := hΓ γ hγ
  have hne : f ≠ e := by
    intro hfe
    subst f
    exact hef hf
  have hfl : f ∈ l.toFinset := List.mem_toFinset.mpr ((hl f).mpr (hauxPath f hf))
  let x : AuxiliaryIndex E e l.toFinset := ⟨⟨f, hne⟩, hfl⟩
  exact (auxOnlyConfiguration_apply_aux e l
    (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1) x).symm

lemma pathOffConfiguration_apply_of_ne (e f : E) (off : OffConfig Bit E e)
    (hf : f ≠ e) : pathOffConfiguration e off f = off ⟨f, hf⟩ := by
  simp [pathOffConfiguration, configSplit, Equiv.funSplitAt_symm_apply, hf]

lemma somePathOpen_pathOff_iff_auxOnly (enhanced : Finset E) (e : E) (l : List E)
    (Γ : Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e Γ)
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) (s : Config E) :
    SomePathOpen Γ (pathOffConfiguration e (fun f => s f.1)) ↔
      SomePathOpen Γ (auxOnlyConfiguration e l
        (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1)) := by
  apply somePathOpen_congr
  intro γ hγ f hf
  obtain ⟨hef, hauxPath⟩ := hΓ γ hγ
  have hne : f ≠ e := by
    intro hfe
    subst f
    exact hef hf
  rw [pathOffConfiguration_apply_of_ne e f _ hne]
  have hfl : f ∈ l.toFinset := List.mem_toFinset.mpr ((hl f).mpr (hauxPath f hf))
  let x : AuxiliaryIndex E e l.toFinset := ⟨⟨f, hne⟩, hfl⟩
  exact (auxOnlyConfiguration_apply_aux e l
    (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1) x).symm

variable {ε α ρ : Type*} [Fintype ε] [Fintype α] [Fintype ρ]

lemma blockLaw_map_aux (ν : FinProb ε) (μ : FinProb α) (ξ : FinProb ρ) :
    (blockLaw ν μ ξ).map (fun s => s.1.2) = μ := by
  unfold blockLaw
  change ((ν.prod μ).prod ξ).map (Prod.snd ∘ Prod.fst) = μ
  rw [← GlauberCoupling.map_map, FinProb.prod_map_fst, FinProb.prod_map_snd]

/-- The homogeneous path probability equals the probability on the auxiliary
block of the lower inhomogeneous product. -/
lemma pathEventProbability_eq_aux_event (enhanced : Finset E) (e : E)
    (l : List E) (Γ : Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e Γ)
    (Δ : E → Set (Finset E))
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1)
    (p : ℝ) (hp1 : p ≤ 1) (h : p' ≤ p) :
    pathEventProbability p' hp' Γ =
      (FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
        bitLaw (lowerProductParameters enhanced p p' hp' Δ a.1.1)
          (lowerProductParameters_mem_Icc enhanced hp1 hp' h Δ a.1.1))).event
        {a | SomePathOpen Γ (auxOnlyConfiguration e l a)} := by
  let μ : FinProb (Config E) := FinProb.pi (fun _ : E => bitLaw p' hp')
  let D := indexedBlockEquiv e l.toFinset (β := Bit)
  let C : Set (((Bit × (AuxiliaryIndex E e l.toFinset → Bit)) ×
      (RemainingIndex E e l.toFinset → Bit))) :=
    {s | SomePathOpen Γ (auxOnlyConfiguration e l s.1.2)}
  have hD : D = indexedBlockEquiv e l.toFinset (β := Bit) := rfl
  have hpre : D ⁻¹' C = {s | SomePathOpen Γ s} := by
    ext s
    change SomePathOpen Γ (auxOnlyConfiguration e l (D s).1.2) ↔ SomePathOpen Γ s
    have ha : (D s).1.2 = (fun a : AuxiliaryIndex E e l.toFinset => s a.1.1) := by
      funext a
      exact PathProduct.indexedBlockEquiv_apply_aux e l.toFinset s a
    rw [ha]
    exact (somePathOpen_iff_auxOnly enhanced e l Γ hΓ hl s).symm
  let Caux : Set (AuxiliaryIndex E e l.toFinset → Bit) :=
    {a | SomePathOpen Γ (auxOnlyConfiguration e l a)}
  have hC : C = (fun s => s.1.2) ⁻¹' Caux := rfl
  have hμ : pathEventProbability p' hp' Γ = μ.event {s | SomePathOpen Γ s} := rfl
  rw [hμ, ← hpre, FinProb.event_preimage_map]
  change ((μ.map D).event C) = _
  dsimp [μ, D, C, Caux]
  rw [map_pi_indexedBlockEquiv]
  have haux : (FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset => bitLaw p' hp')) =
      (FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
        bitLaw (lowerProductParameters enhanced p p' hp' Δ a.1.1)
          (lowerProductParameters_mem_Icc enhanced hp1 hp' h Δ a.1.1))) := by
    apply congrArg FinProb.pi
    funext a
    have ha : (a.1.1 : E) ∉ enhanced :=
      (hl a.1.1).mp (List.mem_toFinset.mp a.2)
    simp [lowerProductParameters, ha]
  change (indexedBlockLaw (fun _ : E => bitLaw p' hp') e l.toFinset).event
      ((fun s => s.1.2) ⁻¹' {a | SomePathOpen Γ (auxOnlyConfiguration e l a)}) = _
  unfold indexedBlockLaw
  rw [FinProb.event_preimage_map, blockLaw_map_aux, haux]

/-- Average an enhanced Bernoulli update over the old auxiliary law. -/
noncomputable def averagedLowerBitLaw {α : Type*} [Fintype α]
    (μ : FinProb α) (C : Set α) (p p' : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ p) :
    FinProb Bit :=
  μ.bind (fun a => if a ∈ C then bitLaw p ⟨hp0, hp1⟩ else bitLaw p' hp')

lemma averagedLowerBitLaw_eq {α : Type*} [Fintype α]
    (μ : FinProb α) (C : Set α) (p p' : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ p) :
    averagedLowerBitLaw μ C p p' hp0 hp1 hp' h =
      bitLaw (enhancedLower p p' (μ.event C))
        (enhancedLower_mem_unit hp1 hp'.1 h (μ.event_mem_Icc C)) := by
  apply FinProb.ext
  intro b
  change (∑ a, μ.mass a * (if a ∈ C then bitLaw p ⟨hp0, hp1⟩ else
    bitLaw p' hp').mass b) = _
  simp_rw [apply_ite (fun q : FinProb Bit => q.mass b)]
  rw [FinProb.sum_mass_mul_ite]
  fin_cases b <;> simp [bitLaw, enhancedLower] <;> ring

/-- Enhanced update based only on the old auxiliary path configuration. -/
noncomputable def lowerPathAuxKernel (enhanced : Finset E) (e : E) (l : List E)
    (Γ : Set (Finset E)) {p p' : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1) :
    (AuxiliaryIndex E e l.toFinset → Bit) → FinProb Bit :=
  fun a => if SomePathOpen Γ (auxOnlyConfiguration e l a) then
    bitLaw p ⟨hp0, hp1⟩ else bitLaw p' hp'

/-- The exact enhanced marginal is stationary for the auxiliary-path update. -/
lemma lowerPathAuxKernel_bind (enhanced : Finset E) (e : E)
    (l : List E) (Γ : E → Set (Finset E)) (hΓ : AuxiliaryPaths enhanced e (Γ e))
    (hl : ∀ f, f ∈ l ↔ f ∉ enhanced) {p p' : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (h : p' ≤ p) (heEnhanced : e ∈ enhanced) :
    (FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
      bitLaw (lowerProductParameters enhanced p p' hp' Γ a.1.1)
        (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ a.1.1))).bind
      (lowerPathAuxKernel enhanced e l (Γ e) hp0 hp1 hp') =
        bitLaw (lowerProductParameters enhanced p p' hp' Γ e)
          (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ e) := by
  let μ := FinProb.pi (fun a : AuxiliaryIndex E e l.toFinset =>
    bitLaw (lowerProductParameters enhanced p p' hp' Γ a.1.1)
      (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ a.1.1))
  let C : Set (AuxiliaryIndex E e l.toFinset → Bit) :=
    {a | SomePathOpen (Γ e) (auxOnlyConfiguration e l a)}
  have hμm : μ.bind (lowerPathAuxKernel enhanced e l (Γ e) hp0 hp1 hp') =
      averagedLowerBitLaw μ C p p' hp0 hp1 hp' h := rfl
  rw [hμm, averagedLowerBitLaw_eq]
  have hevent : μ.event C = pathEventProbability p' hp' (Γ e) :=
    (pathEventProbability_eq_aux_event enhanced e l (Γ e) hΓ Γ hl hp' p hp1 h).symm
  simp [hevent, lowerProductParameters, heEnhanced]

/-- Stationarity of the actual lower path-product law for the sequential
modified jump kernel. No stationarity equation is assumed. -/
theorem lowerProductLaw_invariant_pathProductKernel
    (ρ : FinProb E) (enhanced : Finset E) (auxiliary : List E)
    (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ p) :
    Invariant (lowerProductLaw enhanced hp1 hp' h Γ)
      (pathProductKernel ρ enhanced ⟨hp0, hp1⟩ hp' Γ auxiliary) := by
  let ν : E → FinProb Bit := fun e =>
    bitLaw (lowerProductParameters enhanced p p' hp' Γ e)
      (lowerProductParameters_mem_Icc enhanced hp1 hp' h Γ e)
  let c := pathProductConditionals enhanced ⟨hp0, hp1⟩ hp' Γ
  change (FinProb.pi ν).bind (modifiedJump ρ c enhanced auxiliary) = FinProb.pi ν
  apply mixture_invariant
  intro e
  by_cases he : e ∈ enhanced
  · let κ := lowerPathAuxKernel enhanced e auxiliary (Γ e) hp0 hp1 hp'
    have heAux : e ∉ auxiliary := by
      intro hea
      exact (haux.2 e).mp hea he
    have hcAux : ∀ f ∈ auxiliary, ∀ off, c f off = ν f := by
      intro f hf off
      have hf' : f ∉ enhanced := (haux.2 f).mp hf
      simp [c, ν, pathProductConditionals, pathProductRate, lowerProductParameters, hf']
    have hce : ∀ s : E → Bit, c e (fun f => s f.1) =
        κ (fun a : AuxiliaryIndex E e auxiliary.toFinset => s a.1.1) := by
      intro s
      unfold c κ pathProductConditionals pathProductRate lowerPathAuxKernel
      simp only [he, true_and]
      by_cases hpath : SomePathOpen (Γ e) (pathOffConfiguration e (fun f => s f.1))
      · have ha : SomePathOpen (Γ e) (auxOnlyConfiguration e auxiliary
            (fun a : AuxiliaryIndex E e auxiliary.toFinset => s a.1.1)) :=
          (somePathOpen_pathOff_iff_auxOnly enhanced e auxiliary (Γ e)
            (hΓ e he) haux.2 s).mp hpath
        simp [hpath, ha]
      · have ha : ¬ SomePathOpen (Γ e) (auxOnlyConfiguration e auxiliary
            (fun a : AuxiliaryIndex E e auxiliary.toFinset => s a.1.1)) := by
          intro ha
          exact hpath ((somePathOpen_pathOff_iff_auxOnly enhanced e auxiliary (Γ e)
            (hΓ e he) haux.2 s).mpr ha)
        simp [hpath, ha]
    have hκ : (FinProb.pi
        (fun a : AuxiliaryIndex E e auxiliary.toFinset => ν a.1.1)).bind κ = ν e := by
      exact lowerPathAuxKernel_bind enhanced e auxiliary Γ (hΓ e he) haux.2
        hp0 hp1 hp' h he
    exact PathProduct.pi_bind_blockUpdate_invariant ν c auxiliary e κ enhanced he
      heAux haux.1 hcAux hce hκ
  · have hc : ∀ off, c e off = ν e := by
      intro off
      simp [c, ν, pathProductConditionals, pathProductRate, lowerProductParameters, he]
    have hk : blockUpdate c enhanced auxiliary e = edgeUpdate c e := by
      funext s
      simp [blockUpdate, blockCoordinates, he, sweep, Glauber.seq,
        Glauber.FinProb.bind_dirac_right]
    change (FinProb.pi ν).bind (blockUpdate c enhanced auxiliary e) = FinProb.pi ν
    rw [hk]
    exact PathProduct.pi_bind_edgeUpdate_invariant_of_constant ν c e hc

/-- Interior convergence to the lower product law, without a separately
assumed invariance equation. -/
theorem pathProduct_tendsto_lowerProductLaw
    (μ : FinProb (Config E)) (ρ : FinProb E)
    (hρ : ∀ e, 0 < ρ.mass e) (enhanced : Finset E) (auxiliary : List E)
    (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (Γ : E → Set (Finset E))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    {p p' : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hp'0 : 0 < p') (hp'1 : p' < 1) (h : p' ≤ p)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    FinProb.LawTendsto atTop
      (fun n => μ.bind (iterate (pathProductKernel ρ enhanced
        ⟨hp0.le, hp1.le⟩ ⟨hp'0.le, hp'1.le⟩ Γ auxiliary) n))
      (lowerProductLaw enhanced hp1.le ⟨hp'0.le, hp'1.le⟩ h Γ) := by
  apply pathProduct_tendsto_of_invariant μ _ ρ hρ enhanced hp0 hp1 hp'0 hp'1 Γ auxiliary
    (lowerProductLaw_invariant_pathProductKernel ρ enhanced auxiliary haux Γ hΓ
      hp0.le hp1.le ⟨hp'0.le, hp'1.le⟩ h)
  exact hschedule

/-- Lower comparison with both marginal limits supplied by the proved
stationary block dynamics. The remaining coupling inputs are the ordered joint
finite-time laws, not an unproved stationarity assertion. -/
theorem lower_comparison_of_auxiliary_paths_and_orderedDynamics
    (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    {p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (hp'0 : 0 < p') (hp'1 : p' < 1)
    (h : p' ≤ (p : ℝ)) (Γ : G.Edge → Set (Finset G.Edge))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    (μlower : FinProb (Config G.Edge)) (μfk : FinProb (G.Edge → Bool))
    (ρ : FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge) (haux : IsAuxiliaryEnumeration enhanced auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule)
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
  apply lower_comparison_of_stationary_pathProduct_and_orderedDynamics G hq hp hp0 hp1 ξ
    enhanced hp' hp'0 hp'1 h Γ μlower μfk ρ hρ auxiliary schedule hschedule
    (lowerProductLaw_invariant_pathProductKernel ρ enhanced auxiliary haux Γ hΓ
      (by positivity) (by exact_mod_cast hp) hp' h) joint hfst hsnd horder

end OpenPath
