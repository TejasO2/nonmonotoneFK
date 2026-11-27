import FK.NestedProductRegion
import FK.NestedTransportGeneral

/-! # Synchronized nested FK / independently-extended-FK / Bernoulli coupling -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling FK.FinitePlane FK.RegionSeal

variable {V : Type*} [Fintype V] {G D O : LabelledMultigraph} {eV : V ≃ G.Vertex}
  (e : D.Edge ⊕ O.Edge ≃ G.Edge)

/-- The big graph transported to the nested edge split. -/
abbrev nestedBig := G.transport eV e

/-- Nested coordinate law: the transported big FK law, the independently
extended small FK law, and the transported upper Bernoulli product. -/
noncomputable def nestedSideLaw (τ : D.BoundaryPartition) (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    Side → PMF (D.Edge ⊕ O.Edge → Bool)
  | .left => (nestedBig (eV := eV) e).fkPMF hq hp₁.le ξ
  | .right => productJoinLaw (D.fkPMF hq hp₁.le τ)
      (O.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
  | .upper => (nestedBig (eV := eV) e).bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le

lemma nestedSideLaw_pos (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ∀ s ω, nestedSideLaw e τ ξ hq hp₀ hp₁ s ω ≠ 0 := by
  intro s
  cases s with
  | left => exact fun ω => fkPMF_ne_zero (nestedBig (eV := eV) e) hq hp₀ hp₁ ξ ω
  | right =>
      exact productJoinLaw_ne_zero (fun ω => fkPMF_ne_zero D hq hp₀ hp₁ τ ω)
        (bernoulliProductPMF_ne_zero O ξO (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁))
  | upper =>
      exact bernoulliProductPMF_ne_zero (nestedBig (eV := eV) e) ξ (upperRateNN_pos hp₀)
        (upperRateNN_lt_one hq hp₀ hp₁)

/-- The synchronized one-bit step of the nested laws. -/
noncomputable def nestedTripleStep (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (h₁ h₂ k : Assignment (D.Edge ⊕ O.Edge)) (a : D.Edge ⊕ O.Edge) :
    PMF (Bool × Bool × Bool) :=
  if hh : h₁ a = none ∧ h₂ a = none ∧ k a = none then
    (PMF.OrderedCoupling.glue
      (boolOrderedCouplingOfLe
        (bit ((nestedBig (eV := eV) e).fkPMF hq hp₁.le ξ)
          (fun ω => fkPMF_ne_zero (nestedBig (eV := eV) e) hq hp₀ hp₁ ξ ω) h₁ a)
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
        (fk_bit_true_toReal_le (nestedBig (eV := eV) e) ξ hq hp₀ hp₁ hh.1))
      (boolOrderedCouplingOfLe
        (bit (productJoinLaw (D.fkPMF hq hp₁.le τ)
          (O.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
          (productJoinLaw_ne_zero
            (fun ω => fkPMF_ne_zero D hq hp₀ hp₁ τ ω)
            (bernoulliProductPMF_ne_zero O ξO (upperRateNN_pos hp₀)
              (upperRateNN_lt_one hq hp₀ hp₁))) h₂ a)
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
        (productJoinLaw_fk_bernoulli_bit_le τ ξO hq hp₀ hp₁ hh.2.1))).dist
  else
    (productTriple
      (bit ((nestedBig (eV := eV) e).fkPMF hq hp₁.le ξ)
        (fun ω => fkPMF_ne_zero (nestedBig (eV := eV) e) hq hp₀ hp₁ ξ ω) h₁ a)
      (bit (productJoinLaw (D.fkPMF hq hp₁.le τ)
        (O.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
        (productJoinLaw_ne_zero
          (fun ω => fkPMF_ne_zero D hq hp₀ hp₁ τ ω)
          (bernoulliProductPMF_ne_zero O ξO (upperRateNN_pos hp₀)
            (upperRateNN_lt_one hq hp₀ hp₁))) h₂ a)
      (bit ((nestedBig (eV := eV) e).bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
        (bernoulliProductPMF_ne_zero (nestedBig (eV := eV) e) ξ (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁)) k a)).dist

lemma nestedTripleStep_map_side (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (s : Side) (h₁ h₂ k : Assignment (D.Edge ⊕ O.Edge)) {a : D.Edge ⊕ O.Edge}
    (ha : pick s h₁ h₂ k a = none) :
    (nestedTripleStep e τ ξO ξ hq hp₀ hp₁ h₁ h₂ k a).map (project s) =
      bit (nestedSideLaw e τ ξ hq hp₀ hp₁ s) (nestedSideLaw_pos e τ ξO ξ hq hp₀ hp₁ s)
        (pick s h₁ h₂ k) a := by
  by_cases hh : h₁ a = none ∧ h₂ a = none ∧ k a = none
  · cases s with
    | left =>
        rw [nestedTripleStep, dif_pos hh]
        exact (PMF.OrderedCoupling.glue _ _).map_fst
    | right =>
        rw [nestedTripleStep, dif_pos hh]
        exact (PMF.OrderedCoupling.glue _ _).map_snd
    | upper =>
        rw [nestedTripleStep, dif_pos hh]
        exact (PMF.OrderedCoupling.glue _ _).map_thd.trans
          (bit_bernoulliProductPMF (nestedBig (eV := eV) e) ξ (upperRateNN_pos hp₀)
            (upperRateNN_lt_one hq hp₀ hp₁) hh.2.2).symm
  · cases s with
    | left =>
        rw [nestedTripleStep, dif_neg hh]
        exact (productTriple _ _ _).map_fst
    | right =>
        rw [nestedTripleStep, dif_neg hh]
        exact (productTriple _ _ _).map_snd
    | upper =>
        rw [nestedTripleStep, dif_neg hh]
        exact (productTriple _ _ _).map_thd

lemma nestedTripleStep_ordered (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (h₁ h₂ k : Assignment (D.Edge ⊕ O.Edge)) {a : D.Edge ⊕ O.Edge}
    (hh₁ : h₁ a = none) (hh₂ : h₂ a = none) (hhk : k a = none)
    {z : Bool × Bool × Bool}
    (hz : z ∈ (nestedTripleStep e τ ξO ξ hq hp₀ hp₁ h₁ h₂ k a).support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  have hh : h₁ a = none ∧ h₂ a = none ∧ k a = none := ⟨hh₁, hh₂, hhk⟩
  rw [nestedTripleStep, dif_pos hh] at hz
  exact ⟨(PMF.OrderedCoupling.glue _ _).rel_fst z hz,
    (PMF.OrderedCoupling.glue _ _).rel_snd z hz⟩

/-- Full synchronized nested coupling on the transported big configuration
space. -/
noncomputable def nestedAdaptiveTriple (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    PMF.OrderedTripleCoupling
      ((nestedBig (eV := eV) e).fkPMF hq hp₁.le ξ)
      (productJoinLaw (D.fkPMF hq hp₁.le τ)
        (O.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
      ((nestedBig (eV := eV) e).bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le) where
  dist := (runTriple (nestedTripleStep e τ ξO ξ hq hp₀ hp₁) (frontierNext (G := nestedBig (eV := eV) e) B e₀)
    blank blank blank (Fintype.card (D.Edge ⊕ O.Edge))).map (fun z =>
      (decodeOption z.1, decodeOption z.2.1, decodeOption z.2.2))
  map_fst := by
    rw [PMF.map_comp]
    change (runTriple (nestedTripleStep e τ ξO ξ hq hp₀ hp₁) (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      blank blank blank (Fintype.card (D.Edge ⊕ O.Edge))).map (fun z => decodeOption z.1) = _
    have hcond := runTriple_map_side (μ := nestedSideLaw e τ ξ hq hp₀ hp₁)
      (hμ := nestedSideLaw_pos e τ ξO ξ hq hp₀ hp₁) (nestedTripleStep e τ ξO ξ hq hp₀ hp₁)
      (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      (fun s h₁ h₂ k a ha => nestedTripleStep_map_side e τ ξO ξ hq hp₀ hp₁ s h₁ h₂ k ha)
      (fun k hk => frontierNext_unrevealed (G := nestedBig (eV := eV) e) B e₀ (k := k) hk) Side.left
      blank blank blank (by simp) (by simp) (Fintype.card (D.Edge ⊕ O.Edge)) (by simp)
    simpa only [pick, nestedSideLaw] using hcond.trans (cond_blank _ _)
  map_snd := by
    rw [PMF.map_comp]
    change (runTriple (nestedTripleStep e τ ξO ξ hq hp₀ hp₁) (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      blank blank blank (Fintype.card (D.Edge ⊕ O.Edge))).map (fun z => decodeOption z.2.1) = _
    have hcond := runTriple_map_side (μ := nestedSideLaw e τ ξ hq hp₀ hp₁)
      (hμ := nestedSideLaw_pos e τ ξO ξ hq hp₀ hp₁) (nestedTripleStep e τ ξO ξ hq hp₀ hp₁)
      (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      (fun s h₁ h₂ k a ha => nestedTripleStep_map_side e τ ξO ξ hq hp₀ hp₁ s h₁ h₂ k ha)
      (fun k hk => frontierNext_unrevealed (G := nestedBig (eV := eV) e) B e₀ (k := k) hk) Side.right
      blank blank blank (by simp) (by simp) (Fintype.card (D.Edge ⊕ O.Edge)) (by simp)
    simpa only [pick, nestedSideLaw] using hcond.trans (cond_blank _ _)
  map_thd := by
    rw [PMF.map_comp]
    change (runTriple (nestedTripleStep e τ ξO ξ hq hp₀ hp₁) (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      blank blank blank (Fintype.card (D.Edge ⊕ O.Edge))).map (fun z => decodeOption z.2.2) = _
    have hcond := runTriple_map_side (μ := nestedSideLaw e τ ξ hq hp₀ hp₁)
      (hμ := nestedSideLaw_pos e τ ξO ξ hq hp₀ hp₁) (nestedTripleStep e τ ξO ξ hq hp₀ hp₁)
      (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      (fun s h₁ h₂ k a ha => nestedTripleStep_map_side e τ ξO ξ hq hp₀ hp₁ s h₁ h₂ k ha)
      (fun k hk => frontierNext_unrevealed (G := nestedBig (eV := eV) e) B e₀ (k := k) hk) Side.upper
      blank blank blank (by simp) (by simp) (Fintype.card (D.Edge ⊕ O.Edge)) (by simp)
    simpa only [pick, nestedSideLaw] using hcond.trans (cond_blank _ _)
  rel_fst := by
    letI : Fintype (D.Edge ⊕ O.Edge) := (nestedBig (eV := eV) e).fintypeEdge
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (runTriple_ordered (nestedTripleStep e τ ξO ξ hq hp₀ hp₁) (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      (fun h₁ h₂ k a hh₁ hh₂ hhk z hz => nestedTripleStep_ordered e τ ξO ξ hq hp₀ hp₁
        h₁ h₂ k hh₁ hh₂ hhk hz)
      (fun k hk => frontierNext_unrevealed (G := nestedBig (eV := eV) e) B e₀ (k := k) hk)
      blank blank blank (by simp) (by simp) (by simp [decodeOption, blank])
      (by simp [decodeOption, blank]) (Fintype.card (D.Edge ⊕ O.Edge))
      (by
        with_unfolding_all simp [unrevealed, blank]
        exact Finset.card_univ) hw).1
  rel_snd := by
    letI : Fintype (D.Edge ⊕ O.Edge) := (nestedBig (eV := eV) e).fintypeEdge
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (runTriple_ordered (nestedTripleStep e τ ξO ξ hq hp₀ hp₁) (frontierNext (G := nestedBig (eV := eV) e) B e₀)
      (fun h₁ h₂ k a hh₁ hh₂ hhk z hz => nestedTripleStep_ordered e τ ξO ξ hq hp₀ hp₁
        h₁ h₂ k hh₁ hh₂ hhk hz)
      (fun k hk => frontierNext_unrevealed (G := nestedBig (eV := eV) e) B e₀ (k := k) hk)
      blank blank blank (by simp) (by simp) (by simp [decodeOption, blank])
      (by simp [decodeOption, blank]) (Fintype.card (D.Edge ⊕ O.Edge))
      (by
        with_unfolding_all simp [unrevealed, blank]
        exact Finset.card_univ) hw).2

end FK.Adaptive
