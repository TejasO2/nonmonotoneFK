import FK.FinitePlanarDuality

/-!
# Conditioning finite planar FK duality on matching exterior configurations

This file formalizes the finite-volume conditioning step used for equation (12).
An ambient edge type is split as `I ⊕ O`, the edges inside and outside the
finite region. Conditioning on an exterior configuration normalizes the
ambient FK weights with that configuration fixed. Complementation respects
this operation, so ambient no-boundary duality restricts to matching exterior
configurations.

The geometric Euler/component relation is still supplied explicitly. No
embedding or component-count theorem is asserted here.
-/

namespace FK.FinitePlane

open scoped ENNReal BigOperators
open FK.Configuration

/-- Glue an interior and an exterior configuration along a sum decomposition
of the ambient edge type. -/
def glue {I O : Type*} (ω : I → Bool) (ξ : O → Bool) : I ⊕ O → Bool
  | Sum.inl i => ω i
  | Sum.inr o => ξ o

@[simp] lemma glue_inl {I O : Type*} (ω : I → Bool) (ξ : O → Bool) (i : I) :
    glue ω ξ (Sum.inl i) = ω i := rfl

@[simp] lemma glue_inr {I O : Type*} (ω : I → Bool) (ξ : O → Bool) (o : O) :
    glue ω ξ (Sum.inr o) = ξ o := rfl

/-- The law obtained by conditioning an ambient positive-weight PMF on the
outside coordinates being `ξ`. Since every full configuration has positive
weight, normalization of the restricted weights is exactly this conditional
law; it also makes sense without defining a general conditional-PMF operator. -/
noncomputable def conditionedPMF {I O : Type*} [Fintype I]
    (w : (I ⊕ O → Bool) → NNReal) (hw : ∀ ρ, 0 < w ρ) (ξ : O → Bool) :
    PMF (I → Bool) := by
  classical
  exact normalizedPMF (fun ω => w (glue ω ξ)) (fun ω => hw (glue ω ξ))

@[simp] lemma conditionedPMF_apply {I O : Type*} [Fintype I]
    (w : (I ⊕ O → Bool) → NNReal) (hw : ∀ ρ, 0 < w ρ)
    (ξ : O → Bool) (ω : I → Bool) :
    conditionedPMF w hw ξ ω =
      (w (glue ω ξ) : ℝ≥0∞) *
        (∑' η : I → Bool, (w (glue η ξ) : ℝ≥0∞))⁻¹ := by
  classical
  rw [conditionedPMF]
  apply normalizedPMF_apply

/-- Dualization commutes with gluing when the primal/dual edge bijection
respects the inside/outside decomposition. -/
lemma dualConfig_glue {I O I' O' : Type*} (eI : I ≃ I') (eO : O ≃ O')
    (ω : I → Bool) (ξ : O → Bool) :
    dualConfig (eI.sumCongr eO) (glue ω ξ) =
      glue (dualConfig eI ω) (dualConfig eO ξ) := by
  funext x
  cases x <;> rfl

/-- Ambient proportional dual weights restrict to proportional weights after
conditioning on matching exterior configurations. -/
lemma conditioned_fkWeight_proportional {V I O I' O' : Type*} [Fintype V]
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    (eI : I ≃ I') (eO : O ≃ O') (q p ps : NNReal)
    (K : (I ⊕ O → Bool) → ℕ) (KDual : (I' ⊕ O' → Bool) → ℕ)
    (hp₁ : p < 1) (hq : 0 < q)
    (hcross : q * (1 - p) * (1 - ps) = p * ps)
    (heuler : ∀ ρ, KDual (dualConfig (eI.sumCongr eO) ρ) + Fintype.card V =
      K ρ + 1 + openCard ρ)
    (ξ : O → Bool) (ω : I → Bool) :
    fkWeight q ps KDual
        (glue (dualConfig eI ω) (dualConfig eO ξ)) =
      (ps ^ Fintype.card (I ⊕ O) * q /
        ((1 - p) ^ Fintype.card (I ⊕ O) * q ^ Fintype.card V)) *
        fkWeight q p K (glue ω ξ) := by
  rw [← dualConfig_glue]
  exact dual_fkWeight_proportional (eI.sumCongr eO) q p ps K KDual hp₁ hq
    hcross heuler (glue ω ξ)

/-- General finite conditioning lemma: dualization commutes with restriction
of a normalized positive-weight PMF to matching exterior coordinates. -/
theorem map_conditionedPMF {I O I' O' : Type*} [Fintype I] [Fintype O]
    [Fintype I'] [Fintype O']
    (eI : I ≃ I') (eO : O ≃ O')
    (w : (I ⊕ O → Bool) → NNReal) (wDual : (I' ⊕ O' → Bool) → NNReal)
    (c : NNReal) (hc : 0 < c) (hw : ∀ ρ, 0 < w ρ) (hwDual : ∀ ρ, 0 < wDual ρ)
    (hprop : ∀ ρ, wDual (dualConfig (eI.sumCongr eO) ρ) = c * w ρ)
    (ξ : O → Bool) :
    PMF.map (dualEquiv eI) (conditionedPMF w hw ξ) =
      conditionedPMF wDual hwDual (dualConfig eO ξ) := by
  classical
  apply normalizedPMF_map_eq_of_proportional (dualEquiv eI) _ _ c hc
  intro ω
  change wDual (glue (dualConfig eI ω) (dualConfig eO ξ)) = c * w (glue ω ξ)
  rw [← dualConfig_glue]
  exact hprop (glue ω ξ)

/-- Finite no-boundary FK duality, conditioned on an arbitrary exterior primal
configuration and its complementary dual configuration. This is the exact
finite mechanism behind the deduction of equation (12) in Section 5.2. -/
theorem map_conditioned_fkPMF {V I O I' O' : Type*} [Fintype V]
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    (eI : I ≃ I') (eO : O ≃ O') (q p : NNReal)
    (K : (I ⊕ O → Bool) → ℕ) (KDual : (I' ⊕ O' → Bool) → ℕ)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ, KDual (dualConfig (eI.sumCongr eO) ρ) + Fintype.card V =
      K ρ + 1 + openCard ρ) (ξ : O → Bool) :
    PMF.map (dualEquiv eI)
      (conditionedPMF (fkWeight q p K)
        (fun ρ => fkWeight_pos hq hp₀ hp₁ K ρ) ξ) =
      conditionedPMF (fkWeight q (dualParameter q p) KDual)
        (fun ρ => fkWeight_pos hq (dualParameter_pos hq hp₀ hp₁)
          (dualParameter_lt_one hq hp₀ hp₁.le) KDual ρ)
        (dualConfig eO ξ) := by
  apply map_conditionedPMF eI eO _ _
    ((dualParameter q p) ^ Fintype.card (I ⊕ O) * q /
      ((1 - p) ^ Fintype.card (I ⊕ O) * q ^ Fintype.card V))
  · apply div_pos
    · exact mul_pos (pow_pos (dualParameter_pos hq hp₀ hp₁) _) hq
    · exact mul_pos (pow_pos (tsub_pos_of_lt hp₁) _) (pow_pos hq _)
  · intro ρ
    exact dual_fkWeight_proportional (eI.sumCongr eO) q p (dualParameter q p)
      K KDual hp₁ hq (dualParameter_odds_cross hq hp₁.le) heuler ρ

/-- Pointwise form of conditioned finite FK duality, matching equation (12):
the probability of an interior configuration equals the probability of its
complementary dual, with the exterior configurations complemented as well. -/
theorem equation_twelve_conditioned {V I O I' O' : Type*} [Fintype V]
    [Fintype I] [Fintype O] [Fintype I'] [Fintype O']
    (eI : I ≃ I') (eO : O ≃ O') (q p : NNReal)
    (K : (I ⊕ O → Bool) → ℕ) (KDual : (I' ⊕ O' → Bool) → ℕ)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ, KDual (dualConfig (eI.sumCongr eO) ρ) + Fintype.card V =
      K ρ + 1 + openCard ρ) (ξ : O → Bool) (ω : I → Bool) :
    conditionedPMF (fkWeight q p K)
        (fun ρ => fkWeight_pos hq hp₀ hp₁ K ρ) ξ ω =
      conditionedPMF (fkWeight q (dualParameter q p) KDual)
        (fun ρ => fkWeight_pos hq (dualParameter_pos hq hp₀ hp₁)
          (dualParameter_lt_one hq hp₀ hp₁.le) KDual ρ)
        (dualConfig eO ξ) (dualConfig eI ω) := by
  classical
  have h := congrArg (fun P : PMF (I' → Bool) => P (dualConfig eI ω))
    (map_conditioned_fkPMF eI eO q p K KDual hq hp₀ hp₁ heuler ξ)
  rw [pmf_map_equiv_apply] at h
  simpa [dualEquiv] using h

end FK.FinitePlane
