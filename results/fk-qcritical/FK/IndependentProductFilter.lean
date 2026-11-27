import FK.IndependentProductConditional

/-! # Partial-history conditioning factors through an independent product -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Finite.MarkovFactorization FK.Exploration.FKCoupling FK.FinitePlane
open FK.Exploration.StoppedInterior

lemma sumConfigEquiv_symm_apply {A B : Type*} (z : (A → Bool) × (B → Bool)) :
    (sumConfigEquiv (A := A) (B := B)).symm z = joinSum z.1 z.2 := rfl

/-- Read the left part of a summed assignment. -/
def leftPartial {A B : Type*} (h : Assignment (A ⊕ B)) : Assignment A :=
  fun a => h (Sum.inl a)

/-- Read the right part of a summed assignment. -/
def rightPartial {A B : Type*} (h : Assignment (A ⊕ B)) : Assignment B :=
  fun b => h (Sum.inr b)

lemma fiber_joinSum_iff {A B : Type*} [DecidableEq A] [DecidableEq B]
    {h : Assignment (A ⊕ B)} {ω : A → Bool} {η : B → Bool} :
    joinSum ω η ∈ Fiber h ↔ ω ∈ Fiber (leftPartial h) ∧ η ∈ Fiber (rightPartial h) := by
  constructor
  · intro H
    constructor <;> intro e b hb
    · exact H (Sum.inl e) b hb
    · exact H (Sum.inr e) b hb
  · rintro ⟨Hω, Hη⟩ e b hb
    cases e with
    | inl a => exact Hω a b hb
    | inr c => exact Hη c b hb

/-- The pair-space event corresponding to a summed history fibre. -/
def productFiber {A B : Type*} (h : Assignment (A ⊕ B)) : Set ((A → Bool) × (B → Bool)) :=
  {z | z.1 ∈ Fiber (leftPartial h) ∧ z.2 ∈ Fiber (rightPartial h)}

lemma sumConfigEquiv_symm_preimage_fiber {A B : Type*} [DecidableEq A] [DecidableEq B]
    (h : Assignment (A ⊕ B)) :
    (sumConfigEquiv (A := A) (B := B)).symm ⁻¹' Fiber h = productFiber h := by
  ext ⟨ω, η⟩
  exact fiber_joinSum_iff

lemma product_support_of_positive {A B : Type*} [Fintype A] [Fintype B]
    (μ : PMF (A → Bool)) (ν : PMF (B → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (hν : ∀ η, ν η ≠ 0) (h : Assignment (A ⊕ B)) :
    ∃ z ∈ productFiber h, z ∈ (independentProd μ ν).support := by
  refine ⟨(decodeOption (leftPartial h), decodeOption (rightPartial h)),
    ⟨decodeOption_mem_fiber _, decodeOption_mem_fiber _⟩, ?_⟩
  exact (PMF.mem_support_iff _ _).2 (mul_ne_zero (hμ _) (hν _))

lemma independentProd_filter_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : PMF (A → Bool)) (ν : PMF (B → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) (hν : ∀ η, ν η ≠ 0) (h : Assignment (A ⊕ B)) :
    (independentProd μ ν).filter (productFiber h) (product_support_of_positive μ ν hμ hν h) =
      independentProd
        (μ.filter (Fiber (leftPartial h)) (fiber_support_of_positive μ hμ _))
        (ν.filter (Fiber (rightPartial h)) (fiber_support_of_positive ν hν _)) := by
  let A' := Fiber (leftPartial h)
  let B' := Fiber (rightPartial h)
  let MA := mass μ (leftPartial h)
  let MB := mass ν (rightPartial h)
  have hdenom : (∑' z, (productFiber h).indicator (independentProd μ ν) z) = MA * MB := by
    rw [tsum_fintype]
    calc
      _ = ∑ a, ∑ b, A'.indicator (⇑μ) a * B'.indicator (⇑ν) b := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        by_cases ha : a ∈ A' <;> by_cases hb : b ∈ B' <;>
          simp [Set.indicator, A', B', productFiber, ha, hb]
      _ = _ := by
        rw [← Fintype.sum_mul_sum]
        simp only [MA, MB, mass, tsum_fintype]
        rfl
  have hMA0 : MA ≠ 0 := ne_of_gt (mass_pos_of_positive μ hμ _)
  have hMB0 : MB ≠ 0 := ne_of_gt (mass_pos_of_positive ν hν _)
  have hMAt : MA ≠ ∞ := mass_ne_top μ _
  have hMBt : MB ≠ ∞ := mass_ne_top ν _
  apply PMF.ext
  intro z
  by_cases hz : z ∈ productFiber h
  · rw [PMF.filter_apply, Set.indicator_of_mem hz, hdenom, independentProd_apply,
      independentProd_apply, PMF.filter_apply, PMF.filter_apply,
      Set.indicator_of_mem hz.1, Set.indicator_of_mem hz.2]
    change (μ z.1 * ν z.2) * (MA * MB)⁻¹ =
      (μ z.1 * MA⁻¹) * (ν z.2 * MB⁻¹)
    rw [ENNReal.mul_inv (Or.inl hMA0) (Or.inl hMAt)]
    ac_rfl
  · rw [PMF.filter_apply_eq_zero_of_notMem _ hz]
    have hnot : z.1 ∉ A' ∨ z.2 ∉ B' := by
      by_contra hn
      push_neg at hn
      exact hz ⟨hn.1, hn.2⟩
    rcases hnot with ha | hb
    · rw [independentProd_apply, PMF.filter_apply_eq_zero_of_notMem _ ha]
      simp
    · rw [independentProd_apply, PMF.filter_apply_eq_zero_of_notMem _ hb]
      simp

/-- Conditioning an independent joined law on a summed partial history factors
into independent joined conditional laws on the two partial histories. -/
theorem filter_productJoinLaw_fiber {G H : LabelledMultigraph}
    {μ : PMF G.Configuration} {ν : PMF H.Configuration}
    (hμ : ∀ ω, μ ω ≠ 0) (hν : ∀ η, ν η ≠ 0) (h : Assignment (G.Edge ⊕ H.Edge)) :
    (productJoinLaw μ ν).filter (Fiber h)
      (by
        refine ⟨(sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm
          (decodeOption (leftPartial h), decodeOption (rightPartial h)), ?_, ?_⟩
        · exact fiber_joinSum_iff.2 ⟨decodeOption_mem_fiber _, decodeOption_mem_fiber _⟩
        · exact (PMF.mem_support_iff _ _).2 (productJoinLaw_ne_zero hμ hν _)) =
      productJoinLaw
        (μ.filter (Fiber (leftPartial h)) (fiber_support_of_positive μ hμ _))
        (ν.filter (Fiber (rightPartial h)) (fiber_support_of_positive ν hν _)) := by
  let e := (sumConfigEquiv (A := G.Edge) (B := H.Edge)).symm
  let P := independentProd μ ν
  have hA : ∃ z ∈ e ⁻¹' Fiber h, z ∈ P.support := by
    rw [sumConfigEquiv_symm_preimage_fiber]
    exact product_support_of_positive μ ν hμ hν h
  have hB : ∃ ω ∈ Fiber h, ω ∈ (P.map e).support := by
    refine ⟨e (decodeOption (leftPartial h), decodeOption (rightPartial h)), ?_, ?_⟩
    · rw [sumConfigEquiv_symm_apply]
      exact fiber_joinSum_iff.2 ⟨decodeOption_mem_fiber _, decodeOption_mem_fiber _⟩
    · exact (PMF.mem_support_iff _ _).2 (productJoinLaw_ne_zero hμ hν _)
  have hfilter := map_filter_equiv e P (Fiber h) hA hB
  change (P.map e).filter (Fiber h) _ = _
  rw [← hfilter]
  have hset : P.filter (e ⁻¹' Fiber h) hA =
      P.filter (productFiber h) (product_support_of_positive μ ν hμ hν h) :=
    filter_congr_set P (sumConfigEquiv_symm_preimage_fiber h) hA
      (product_support_of_positive μ ν hμ hν h)
  rw [hset, independentProd_filter_product μ ν hμ hν h]
  rfl

/-- Forgetting the right coordinates of a joined independent product recovers
its left marginal exactly. -/
lemma productJoinLaw_map_left {G H : LabelledMultigraph}
    (μ : PMF G.Configuration) (ν : PMF H.Configuration) :
    (productJoinLaw μ ν).map (fun ω => ω ∘ Sum.inl) = μ := by
  apply PMF.ext
  intro ω
  rw [PMF.map_apply, tsum_fintype]
  let e := sumConfigEquiv (A := G.Edge) (B := H.Edge)
  calc
    _ = ∑ z : G.Configuration × H.Configuration,
        if ω = z.1 then independentProd μ ν z else 0 := by
      rw [← e.symm.sum_comp]
      apply Finset.sum_congr rfl
      intro z _
      have hproj : (e.symm z) ∘ Sum.inl = z.1 := by
        exact sumConfigEquiv_symm_apply z ▸ rfl
      have heval : productJoinLaw μ ν (e.symm z) = independentProd μ ν z := by
        rw [productJoinLaw]
        have hm := pmf_map_equiv_apply (d := e.symm) (independentProd μ ν) (e.symm z)
        exact hm.trans (by simp)
      by_cases heq : ω = z.1
      · subst ω
        simp [heval, hproj]
      · simp [heval, hproj, heq]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have hu := ν.tsum_coe
      rw [tsum_fintype] at hu
      calc
        _ = ∑ a, if ω = a then μ a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : ω = a
          · subst a
            simp only [Prod.fst, independentProd_apply, if_true]
            rw [← Finset.mul_sum, hu, mul_one]
          · simp [ha]
        _ = μ ω := by simp

/-- After conditioning a joined product, forgetting the right coordinates
recovers the left conditional on the corresponding partial history. -/
theorem cond_productJoinLaw_map_left {G H : LabelledMultigraph}
    {μ : PMF G.Configuration} {ν : PMF H.Configuration}
    (hμ : ∀ ω, μ ω ≠ 0) (hν : ∀ η, ν η ≠ 0) (h : Assignment (G.Edge ⊕ H.Edge)) :
    (cond (productJoinLaw μ ν) (productJoinLaw_ne_zero hμ hν) h).map
      (fun ω => ω ∘ Sum.inl) = cond μ hμ (leftPartial h) := by
  unfold cond
  rw [filter_productJoinLaw_fiber hμ hν h, productJoinLaw_map_left]

end FK.Adaptive
