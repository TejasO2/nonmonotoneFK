import FK.FKGlauber

/-!
# Full support is essential in the one-point determination theorem

`Glauber.FinProb.eq_of_shared_edgeConditionals` needs both laws to have full
support: the mass-ratio argument divides by `ν.mass ω`.  This file records that
the hypothesis is not cosmetic.  On two Boolean coordinates there are two
*distinct* laws with the *same* off-coordinate conditional family, the shared
family being the Dirac mass at the value of the other coordinate.

Concretely, `μ = δ_{00}` and `ν = (δ_{00} + δ_{11})/2` have the same one-point
conditional law at both coordinates: the fibre on which they differ is the one
obtained by flipping *both* coordinates at once, and a single-coordinate
conditional cannot see it.  So "positive specification" is a real hypothesis in
the cited `[15] Theorem 1.33` step of the source, not bookkeeping.
-/

noncomputable section

open scoped BigOperators

namespace Glauber.FinProb

open OpenPath

/-! ### Two Boolean coordinates -/

/-- The unique coordinate different from `e` in the two-point index type. -/
def otherCoord (e : Bool) : {f : Bool // f ≠ e} := ⟨!e, by cases e <;> simp⟩

/-- Any coordinate different from `e` is `otherCoord e`. -/
lemma eq_otherCoord_of_ne {e f : Bool} (h : f ≠ e) : f = (otherCoord e).1 := by
  cases e <;> cases f <;> simp_all [otherCoord]

/-- The conditional family shared by the two laws: the bit at the other
coordinate. -/
def otherFamily : EdgeConditionals Bool Bool :=
  fun e off => Glauber.FinProb.dirac (off (otherCoord e))

/-- The all-closed configuration. -/
def confFF : Bool → Bool := fun _ => false

/-- The all-open configuration. -/
def confTT : Bool → Bool := fun _ => true

lemma confFF_ne_confTT : confFF ≠ confTT := by
  intro h
  have := congrFun h false
  simp [confFF, confTT] at this

/-- The one-point law at the all-closed configuration. -/
def muEx : FinProb (Bool → Bool) := Glauber.FinProb.dirac confFF

/-- The half-half mixture of the two constant configurations. -/
def nuEx : FinProb (Bool → Bool) :=
  (Glauber.FKBridge.boolLaw (1 / 2) (by norm_num)).bind
    fun b => Glauber.FinProb.dirac (if b then confTT else confFF)

/-! ### Splitting a two-coordinate configuration -/

/-- Reassemble a configuration from an off-coordinate family. -/
def glueOff (e : Bool) (off : {f : Bool // f ≠ e} → Bool) : Bool → Bool :=
  fun f => if h : f = e then false else off ⟨f, h⟩

lemma configSplit_glueOff_fst (e : Bool) (off : {f : Bool // f ≠ e} → Bool) :
    (configSplit Bool e (glueOff e off)).1 = off := by
  funext g
  simp only [configSplit_apply_fst, glueOff, g.2, dite_false]

/-- Splitting and recombining an off-coordinate family is a single-coordinate
update of its canonical representative. -/
lemma configSplit_symm_eq_update_glueOff (e : Bool)
    (off : {f : Bool // f ≠ e} → Bool) (y : Bool) :
    (configSplit Bool e).symm (off, y) = Function.update (glueOff e off) e y := by
  have h := configSplit_symm_update (B := Bool) e (glueOff e off) y
  rwa [configSplit_glueOff_fst e off] at h

/-- Which single-coordinate updates of the canonical representative give the
all-closed configuration. -/
lemma update_glueOff_eq_confFF_iff (e : Bool) (off : {f : Bool // f ≠ e} → Bool)
    (y : Bool) :
    Function.update (glueOff e off) e y = confFF ↔
      (y = false ∧ off (otherCoord e) = false) := by
  constructor
  · intro h
    have h1 : Function.update (glueOff e off) e y e = y := Function.update_self e y (glueOff e off)
    have h2 : y = confFF e := by rw [← h1, h]
    refine ⟨?_, ?_⟩
    · simpa [confFF] using h2
    · have h3 : Function.update (glueOff e off) e y (otherCoord e).1 =
          glueOff e off (otherCoord e).1 :=
        Function.update_of_ne (otherCoord e).2 y (glueOff e off)
      have h4 : Function.update (glueOff e off) e y (otherCoord e).1 =
          confFF (otherCoord e).1 := congrFun h _
      calc off (otherCoord e) = glueOff e off (otherCoord e).1 := by
            simp only [glueOff, (otherCoord e).2, dite_false]
        _ = Function.update (glueOff e off) e y (otherCoord e).1 := h3.symm
        _ = confFF (otherCoord e).1 := h4
        _ = false := rfl
  · rintro ⟨rfl, hoff⟩
    funext f
    by_cases hf : f = e
    · subst hf
      simp [Function.update, confFF]
    · have hfe : f = (otherCoord e).1 := eq_otherCoord_of_ne hf
      simp [Function.update, glueOff, confFF, hf, hfe, hoff]

/-- Which single-coordinate updates of the canonical representative give the
all-open configuration. -/
lemma update_glueOff_eq_confTT_iff (e : Bool) (off : {f : Bool // f ≠ e} → Bool)
    (y : Bool) :
    Function.update (glueOff e off) e y = confTT ↔
      (y = true ∧ off (otherCoord e) = true) := by
  constructor
  · intro h
    have h1 : Function.update (glueOff e off) e y e = y := Function.update_self e y (glueOff e off)
    have h2 : y = confTT e := by rw [← h1, h]
    refine ⟨?_, ?_⟩
    · simpa [confTT] using h2
    · have h3 : Function.update (glueOff e off) e y (otherCoord e).1 =
          glueOff e off (otherCoord e).1 :=
        Function.update_of_ne (otherCoord e).2 y (glueOff e off)
      have h4 : Function.update (glueOff e off) e y (otherCoord e).1 =
          confTT (otherCoord e).1 := congrFun h _
      calc off (otherCoord e) = glueOff e off (otherCoord e).1 := by
            simp only [glueOff, (otherCoord e).2, dite_false]
        _ = Function.update (glueOff e off) e y (otherCoord e).1 := h3.symm
        _ = confTT (otherCoord e).1 := h4
        _ = true := rfl
  · rintro ⟨rfl, hoff⟩
    funext f
    by_cases hf : f = e
    · subst hf
      simp [Function.update, confTT]
    · have hfe : f = (otherCoord e).1 := eq_otherCoord_of_ne hf
      simp [Function.update, glueOff, confTT, hf, hfe, hoff]

/-! ### The shared one-point part -/

lemma dirac_mass_eq (a ω : Bool → Bool) :
    (Glauber.FinProb.dirac a).mass ω = if ω = a then 1 else 0 := by
  simp [Glauber.FinProb.dirac]

lemma nuEx_mass (ω : Bool → Bool) :
    nuEx.mass ω = (if ω = confFF then 1 / 2 else 0) + (if ω = confTT then 1 / 2 else 0) := by
  rw [nuEx, OpenPath.FinProb.mass_bind, Fintype.sum_bool]
  by_cases h1 : ω = confFF <;> by_cases h2 : ω = confTT <;>
    simp [Glauber.FKBridge.boolLaw, Glauber.FinProb.dirac, h1, h2, confFF_ne_confTT,
      add_comm] <;> norm_num

/-- The shared conditional of the point mass at the all-closed configuration. -/
theorem hasEdgeConditional_muEx : ∀ e, HasEdgeConditional muEx otherFamily e := by
  intro e off y
  cases y
  · rw [configSplit_symm_eq_update_glueOff]
    rw [show outsideMassConj (configSplit Bool e) muEx off =
        ∑ y' : Bool, (if Function.update (glueOff e off) e y' = confFF then 1 else 0) from by
      rw [Glauber.outsideMassConj]
      exact Finset.sum_congr rfl fun y' _ => by
        rw [configSplit_symm_eq_update_glueOff]
        exact dirac_mass_eq confFF _]
    simp only [muEx, otherFamily, Fintype.sum_bool, Glauber.FinProb.dirac,
      update_glueOff_eq_confFF_iff, update_glueOff_eq_confTT_iff]
    by_cases ho : off (otherCoord e) = false <;> simp [ho, eq_comm] <;> norm_num
  · rw [configSplit_symm_eq_update_glueOff]
    rw [show outsideMassConj (configSplit Bool e) muEx off =
        ∑ y' : Bool, (if Function.update (glueOff e off) e y' = confFF then 1 else 0) from by
      rw [Glauber.outsideMassConj]
      exact Finset.sum_congr rfl fun y' _ => by
        rw [configSplit_symm_eq_update_glueOff]
        exact dirac_mass_eq confFF _]
    simp only [muEx, otherFamily, Fintype.sum_bool, Glauber.FinProb.dirac,
      update_glueOff_eq_confFF_iff, update_glueOff_eq_confTT_iff]
    by_cases ho : off (otherCoord e) = false <;> simp [ho, eq_comm] <;> norm_num

/-- The shared conditional of the half-half mixture. -/
theorem hasEdgeConditional_nuEx : ∀ e, HasEdgeConditional nuEx otherFamily e := by
  intro e off y
  cases y
  · rw [configSplit_symm_eq_update_glueOff]
    rw [show outsideMassConj (configSplit Bool e) nuEx off =
        ∑ y' : Bool, ((if Function.update (glueOff e off) e y' = confFF then 1 / 2 else 0) +
          (if Function.update (glueOff e off) e y' = confTT then 1 / 2 else 0)) from by
      rw [Glauber.outsideMassConj]
      exact Finset.sum_congr rfl fun y' _ => by
        rw [configSplit_symm_eq_update_glueOff]
        exact nuEx_mass _]
    simp only [nuEx_mass, otherFamily, Fintype.sum_bool, Glauber.FinProb.dirac,
      update_glueOff_eq_confFF_iff, update_glueOff_eq_confTT_iff]
    by_cases ho : off (otherCoord e) = false <;> simp [ho, eq_comm] <;> norm_num
  · rw [configSplit_symm_eq_update_glueOff]
    rw [show outsideMassConj (configSplit Bool e) nuEx off =
        ∑ y' : Bool, ((if Function.update (glueOff e off) e y' = confFF then 1 / 2 else 0) +
          (if Function.update (glueOff e off) e y' = confTT then 1 / 2 else 0)) from by
      rw [Glauber.outsideMassConj]
      exact Finset.sum_congr rfl fun y' _ => by
        rw [configSplit_symm_eq_update_glueOff]
        exact nuEx_mass _]
    simp only [nuEx_mass, otherFamily, Fintype.sum_bool, Glauber.FinProb.dirac,
      update_glueOff_eq_confFF_iff, update_glueOff_eq_confTT_iff]
    by_cases ho : off (otherCoord e) = false <;> simp [ho, eq_comm] <;> norm_num

/-- The two laws are distinct. -/
theorem muEx_ne_nuEx : muEx ≠ nuEx := by
  intro h
  have hm := congrArg (fun μ : FinProb (Bool → Bool) => μ.mass confTT) h
  have hne : confTT ≠ confFF := fun h => confFF_ne_confTT h.symm
  have hmu : muEx.mass confTT = 0 := by
    rw [muEx, dirac_mass_eq]
    simp [hne]
  have hnu : nuEx.mass confTT = 1 / 2 := by
    rw [nuEx_mass]
    simp [hne]
  rw [hmu, hnu] at hm
  norm_num at hm

/-- **The one-point part does not determine the law without full support.** -/
theorem onePoint_determination_needs_fullSupport :
    ∃ (μ ν : FinProb (Bool → Bool)) (c : EdgeConditionals Bool Bool),
      (∀ e, HasEdgeConditional μ c e) ∧ (∀ e, HasEdgeConditional ν c e) ∧ μ ≠ ν :=
  ⟨muEx, nuEx, otherFamily, hasEdgeConditional_muEx, hasEdgeConditional_nuEx, muEx_ne_nuEx⟩

end Glauber.FinProb

#print axioms Glauber.FinProb.hasEdgeConditional_muEx
#print axioms Glauber.FinProb.hasEdgeConditional_nuEx
#print axioms Glauber.FinProb.muEx_ne_nuEx
#print axioms Glauber.FinProb.onePoint_determination_needs_fullSupport
