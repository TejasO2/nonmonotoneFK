import FK.Theorem12Less
import FK.Theorem12Greater

/-!
# Source-fidelity interfaces for the finite enhanced comparisons

These lemmas expose the ordinary real-valued enhancement profiles used in
Theorem 1.2 of arXiv:2512.16486v1.  They are deliberately not called paper
theorems: the stochastic comparisons and graph certificates are supplied by
`Theorem12Less` and `Theorem12Greater`, while this file only makes the
normalization, unit-interval bounds, and non-identically-zero witnesses
simultaneously visible.
-/

namespace FK.EnhancedComparisons.Fidelity

open Set
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.WiredEnhancement
open OpenPath FKEnhancement
open scoped unitInterval

noncomputable section

/-- The lower closed-cutset profile is `p + ε`, with `ε ∈ [0,1]` and the
requested strict witness.  This adds no hypothesis about a stochastic
comparison and proves none. -/
theorem normalized_lower_cutset_profile
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    {p p' : I} (hp : p ≤ p')
    (hpos : ∃ e, 0 < extendedCutsetEpsilon G ξ enhanced p p' e) :
    ∃ ε : G.Edge → ℝ,
      (∀ e, ε e ∈ Icc (0 : ℝ) 1) ∧ (∃ e, 0 < ε e) ∧
      ∀ e, ((lowerEnhancedRates (graphConnectionEvent G ξ) enhanced hp e : I) : ℝ) =
        (p : ℝ) + ε e := by
  refine ⟨extendedCutsetEpsilon G ξ enhanced p p',
    extendedCutsetEpsilon_mem_Icc G ξ enhanced p p', hpos, ?_⟩
  intro e
  exact lowerEnhancedRate_eq_add_extended G ξ enhanced hp e

/-- The upper closed-cutset profile is `p - ε`, again with an explicit strict
witness and unit-interval bounds. -/
theorem normalized_upper_cutset_profile
    (G : LabelledMultigraph) (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    {p p' : I} (hp : p' ≤ p)
    (hpos : ∃ e, 0 < extendedCutsetEpsilon G ξ enhanced p p' e) :
    ∃ ε : G.Edge → ℝ,
      (∀ e, ε e ∈ Icc (0 : ℝ) 1) ∧ (∃ e, 0 < ε e) ∧
      ∀ e, ((upperEnhancedRates (graphConnectionEvent G ξ) enhanced hp e : I) : ℝ) =
        (p : ℝ) - ε e := by
  refine ⟨extendedCutsetEpsilon G ξ enhanced p p',
    extendedCutsetEpsilon_mem_Icc G ξ enhanced p p', hpos, ?_⟩
  intro e
  exact upperEnhancedRate_eq_sub_extended G ξ enhanced hp e

/-- For `p < p'`, the open-path product has exactly the paper's upper profile
`p' - ε`; `HasEnhancingPaths` supplies both auxiliary-edge semantics and a
nonempty certificate, hence non-identical vanishing is strict. -/
theorem normalized_upper_path_profile {E : Type*} [Fintype E] [DecidableEq E]
    {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ) (henh : enhanced.Nonempty)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hp'1 : p' ≤ 1) (h : p < p') :
    ∃ ε : E → ℝ,
      (∀ e, ε e ∈ Icc (0 : ℝ) 1) ∧ (∃ e, 0 < ε e) ∧
      upperProductParameters enhanced p p' hp Γ = fun e => p' - ε e := by
  let ε := upperEpsilon enhanced p p' hp Γ
  have hpos : ∃ e, 0 < ε e := by
    obtain ⟨e, he⟩ := henh
    exact ⟨e, upperEpsilon_pos hΓ hp hp0 hp1 h he⟩
  exact ⟨ε, upperEpsilon_mem_Icc enhanced hp hp'1 h.le Γ, hpos,
    upperProductParameters_eq E enhanced p p' hp Γ⟩

/-- For `p' < p`, the open-path product has exactly the paper's lower profile
`p' + ε`. -/
theorem normalized_lower_path_profile {E : Type*} [Fintype E] [DecidableEq E]
    {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ) (henh : enhanced.Nonempty)
    {p p' : ℝ} (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (hp'0 : 0 < p') (hp'1 : p' < 1) (h : p' < p) :
    ∃ ε : E → ℝ,
      (∀ e, ε e ∈ Icc (0 : ℝ) 1) ∧ (∃ e, 0 < ε e) ∧
      lowerProductParameters enhanced p p' hp' Γ = fun e => p' + ε e := by
  let ε := lowerEpsilon enhanced p p' hp' Γ
  have hpos : ∃ e, 0 < ε e := by
    obtain ⟨e, he⟩ := henh
    exact ⟨e, lowerEpsilon_pos hΓ hp' hp'0 hp'1 h he⟩
  exact ⟨ε, lowerEpsilon_mem_Icc enhanced hp1 hp' h.le Γ, hpos,
    lowerProductParameters_eq E enhanced p p' hp' Γ⟩

end

end FK.EnhancedComparisons.Fidelity
