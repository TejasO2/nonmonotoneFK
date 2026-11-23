import FK.PlanarActual

/-!
# Exact exterior-fiber conditioning for finite FK measures

`PlanarActual.conditionedPMF_actual_fkPMF` identifies the normalized weights
on an exterior fiber.  This file proves the remaining probabilistic point:
that law is the actual `PMF.filter` of the ambient normalized FK law, not
merely a separately defined law with the same informal conditioning
interpretation.
-/

namespace FK.FinitePlane

open scoped ENNReal BigOperators Classical
open FK.Configuration

/-- Configurations with a prescribed restriction to the exterior edge
labels. -/
def exteriorFiber {I O : Type*} (ξ : O → Bool) : Set (I ⊕ O → Bool) :=
  {ρ | ∀ o, ρ (Sum.inr o) = ξ o}

lemma glue_mem_exteriorFiber {I O : Type*} (ω : I → Bool) (ξ : O → Bool) :
    glue ω ξ ∈ exteriorFiber ξ := by
  intro o
  rfl

lemma eq_glue_of_mem_exteriorFiber {I O : Type*} {ξ : O → Bool}
    {ρ : I ⊕ O → Bool} (hρ : ρ ∈ exteriorFiber ξ) :
    ρ = glue (ρ ∘ Sum.inl) ξ := by
  funext a
  cases a with
  | inl i => rfl
  | inr o => exact hρ o

lemma glue_left_injective {I O : Type*} (ξ : O → Bool) :
    Function.Injective (fun ω : I → Bool => glue ω ξ) := by
  intro ω η h
  funext i
  exact congrFun h (Sum.inl i)

/-- Canonical identification of an exterior fiber with its interior
configurations. -/
def glueFiberEquiv {I O : Type*} (ξ : O → Bool) :
    (I → Bool) ≃ exteriorFiber (I := I) ξ where
  toFun ω := ⟨glue ω ξ, glue_mem_exteriorFiber ω ξ⟩
  invFun ρ := ρ.1 ∘ Sum.inl
  left_inv _ := by rfl
  right_inv ρ := by
    apply Subtype.ext
    exact (eq_glue_of_mem_exteriorFiber ρ.2).symm

lemma normalizedPMF_mem_support_of_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → NNReal) (hw : ∀ a, 0 < w a) (a : Ω) :
    a ∈ (normalizedPMF w hw).support := by
  rw [PMF.mem_support_iff, normalizedPMF_apply]
  apply mul_ne_zero
  · exact ENNReal.coe_ne_zero.mpr (hw a).ne'
  · exact ENNReal.inv_ne_zero.mpr (tsum_coe_ne_top w)

lemma exteriorFiber_support {I O : Type*} [Fintype I] [Fintype O]
    (w : (I ⊕ O → Bool) → NNReal) (hw : ∀ ρ, 0 < w ρ) (ξ : O → Bool) :
    ∃ ρ ∈ exteriorFiber ξ, ρ ∈ (normalizedPMF w hw).support := by
  refine ⟨glue (fun _ => false) ξ, glue_mem_exteriorFiber _ _,
    normalizedPMF_mem_support_of_pos w hw _⟩

/-- Normalizing a positive finite weight on the full configurations and then
filtering to an exterior fiber is the same pushforward as first normalizing
on that fiber. -/
theorem map_glue_conditionedPMF {I O : Type*} [Fintype I] [Fintype O]
    (w : (I ⊕ O → Bool) → NNReal) (hw : ∀ ρ, 0 < w ρ) (ξ : O → Bool) :
    PMF.map (fun ω : I → Bool => glue ω ξ) (conditionedPMF w hw ξ) =
      (normalizedPMF w hw).filter (exteriorFiber ξ)
        (exteriorFiber_support w hw ξ) := by
  classical
  let h := exteriorFiber_support w hw ξ
  have hZ0 : (∑' ρ, (w ρ : ℝ≥0∞)) ≠ 0 := tsum_coe_ne_zero_of_pos w hw
  have hZtop : (∑' ρ, (w ρ : ℝ≥0∞)) ≠ ∞ := tsum_coe_ne_top w
  let ZI : ℝ≥0∞ := ∑' ω : I → Bool, (w (glue ω ξ) : ℝ≥0∞)
  have hZI0 : ZI ≠ 0 := by
    exact tsum_coe_ne_zero_of_pos (fun ω => w (glue ω ξ)) (fun ω => hw _)
  have hZItop : ZI ≠ ∞ := by
    exact tsum_coe_ne_top (fun ω => w (glue ω ξ))
  have hdenom :
      (∑' ρ, (exteriorFiber ξ).indicator (normalizedPMF w hw) ρ) =
        ZI * (∑' ρ, (w ρ : ℝ≥0∞))⁻¹ := by
    calc
      (∑' ρ, (exteriorFiber ξ).indicator (normalizedPMF w hw) ρ) =
          ∑' ρ : exteriorFiber ξ, normalizedPMF w hw ρ.1 := by
        exact (tsum_subtype (exteriorFiber ξ) (normalizedPMF w hw)).symm
      _ = ∑' ω : I → Bool, normalizedPMF w hw (glue ω ξ) := by
        exact ((glueFiberEquiv ξ).tsum_eq
          (fun ρ : exteriorFiber ξ => normalizedPMF w hw ρ.1)).symm
      _ = ∑' ω : I → Bool,
          (w (glue ω ξ) : ℝ≥0∞) * (∑' ρ, (w ρ : ℝ≥0∞))⁻¹ := by
        congr 1
      _ = ZI * (∑' ρ, (w ρ : ℝ≥0∞))⁻¹ := by
        exact ENNReal.tsum_mul_right
  apply PMF.ext
  intro ρ
  by_cases hρ : ρ ∈ exteriorFiber ξ
  · let ω : I → Bool := ρ ∘ Sum.inl
    have hρeq : ρ = glue ω ξ := eq_glue_of_mem_exteriorFiber hρ
    rw [hρeq]
    have hmap : (PMF.map (fun η : I → Bool => glue η ξ)
        (conditionedPMF w hw ξ)) (glue ω ξ) = conditionedPMF w hw ξ ω := by
      rw [PMF.map_apply, tsum_fintype]
      have hiff : ∀ η : I → Bool, (glue ω ξ = glue η ξ) ↔ η = ω := by
        intro η
        constructor
        · intro heq
          exact (glue_left_injective ξ heq).symm
        · intro heq
          subst η
          rfl
      simp only [hiff]
      simp
    rw [hmap, PMF.filter_apply, Set.indicator_of_mem (glue_mem_exteriorFiber ω ξ),
      hdenom]
    change (w (glue ω ξ) : ℝ≥0∞) * ZI⁻¹ =
      ((w (glue ω ξ) : ℝ≥0∞) * (∑' ρ, (w ρ : ℝ≥0∞))⁻¹) *
        (ZI * (∑' ρ, (w ρ : ℝ≥0∞))⁻¹)⁻¹
    rw [ENNReal.mul_inv (Or.inl hZI0) (Or.inl hZItop), inv_inv]
    have hinv0 : (∑' ρ, (w ρ : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hZtop
    have hinvtop : (∑' ρ, (w ρ : ℝ≥0∞))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hZ0
    calc
      (w (glue ω ξ) : ℝ≥0∞) * ZI⁻¹ =
          ((w (glue ω ξ) : ℝ≥0∞) * ZI⁻¹) *
            ((∑' ρ, (w ρ : ℝ≥0∞))⁻¹ * ∑' ρ, (w ρ : ℝ≥0∞)) := by
        rw [ENNReal.inv_mul_cancel hZ0 hZtop, mul_one]
      _ = ((w (glue ω ξ) : ℝ≥0∞) * (∑' ρ, (w ρ : ℝ≥0∞))⁻¹) *
          (ZI⁻¹ * ∑' ρ, (w ρ : ℝ≥0∞)) := by ac_rfl
  · rw [PMF.filter_apply_eq_zero_of_notMem h hρ]
    symm
    rw [PMF.map_apply]
    symm
    rw [ENNReal.tsum_eq_zero]
    intro ω
    by_cases heq : ρ = glue ω ξ
    · subst ρ
      exact (hρ (glue_mem_exteriorFiber ω ξ)).elim
    · simp [heq]

/-- Exact actual-FK form of exterior-fiber conditioning.  On the fiber the
ambient configuration is recovered by gluing, and its filtered law is the
pushforward of the interior FK measure with exterior components wired. -/
theorem filter_actual_fkPMF_eq_map_glue {V I O : Type*} [Fintype V]
    [Fintype I] [Fintype O] (s t : I ⊕ O → V) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    PMF.map (fun ω : I → Bool => glue ω ξ)
        ((interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ)) =
      (normalizedPMF
        (FK.FinitePlane.fkWeight q p ((ambientOfSum s t).componentCount
          (ambientOfSum s t).freeBoundary))
        (fun ρ => fkWeight_pos hq hp₀ hp₁ _ ρ)).filter (exteriorFiber ξ)
          (exteriorFiber_support _ (fun ρ => fkWeight_pos hq hp₀ hp₁ _ ρ) ξ) := by
  rw [← conditionedPMF_actual_fkPMF s t hq hp₀ hp₁ ξ]
  exact map_glue_conditionedPMF _ _ ξ

lemma exteriorFiber_support_actual {V I O : Type*} [Fintype V]
    [Fintype I] [Fintype O] (s t : I ⊕ O → V) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    ∃ ρ ∈ exteriorFiber ξ,
      ρ ∈ ((ambientOfSum s t).fkPMF hq hp₁.le
        (ambientOfSum s t).freeBoundary).support := by
  rw [← normalizedPMF_eq_actual_fkPMF (ambientOfSum s t)
    (ambientOfSum s t).freeBoundary hq hp₀ hp₁]
  exact exteriorFiber_support _ (fun ρ => fkWeight_pos hq hp₀ hp₁ _ ρ) ξ

/-- The actual ambient FK law filtered to an exterior configuration is the
actual interior FK law with induced wiring, glued with that same exterior. -/
theorem filter_ambient_fkPMF_eq_map_glue {V I O : Type*} [Fintype V]
    [Fintype I] [Fintype O] (s t : I ⊕ O → V) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    PMF.map (fun ω : I → Bool => glue ω ξ)
        ((interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ)) =
      ((ambientOfSum s t).fkPMF hq hp₁.le (ambientOfSum s t).freeBoundary).filter
        (exteriorFiber ξ) (exteriorFiber_support_actual s t hq hp₀ hp₁ ξ) := by
  simpa only [normalizedPMF_eq_actual_fkPMF (ambientOfSum s t)
    (ambientOfSum s t).freeBoundary hq hp₀ hp₁] using
      filter_actual_fkPMF_eq_map_glue s t hq hp₀ hp₁ ξ

/-- If no open exterior edge is incident with `U`, every exterior-open path
starting in `U` is trivial.  The induced boundary relation is therefore free
on `U`, although it may have arbitrary open-connected blocks outside `U`. -/
theorem exteriorBoundary_related_iff_of_no_open_incident {V I O : Type*}
    [Fintype V] [Fintype I] [Fintype O] (s t : I ⊕ O → V)
    (ξ : O → Bool) (U : Set V)
    (hsep : ∀ o, ξ o = true → s (Sum.inr o) ∉ U ∧ t (Sum.inr o) ∉ U)
    {u v : V} (hu : u ∈ U) :
    (exteriorBoundary s t ξ).r u v ↔ u = v := by
  have hadj : ∀ {x y : V}, x ∈ U → ¬ (exteriorGraph s t ξ).Adj x y := by
    intro x y hx hxy
    rcases hxy.2 with hfree | ⟨a, ha, hjoin⟩
    · exact hxy.1 hfree
    · cases a with
      | inl i => simp [glue] at ha
      | inr o =>
          obtain ⟨hs, ht⟩ := hsep o ha
          change (s (Sum.inr o) = x ∧ t (Sum.inr o) = y) ∨
            (s (Sum.inr o) = y ∧ t (Sum.inr o) = x) at hjoin
          rcases hjoin with h | h
          · exact hs (h.1.symm ▸ hx)
          · exact ht (h.2.symm ▸ hx)
  constructor
  · intro huv
    change (exteriorGraph s t ξ).Reachable u v at huv
    rw [SimpleGraph.reachable_iff_reflTransGen] at huv
    induction huv with
    | refl => rfl
    | tail hxy hyz ih =>
        rw [← ih] at hyz
        exact (hadj hu hyz).elim
  · intro huv
    subst v
    exact SimpleGraph.Reachable.refl u

end FK.FinitePlane
