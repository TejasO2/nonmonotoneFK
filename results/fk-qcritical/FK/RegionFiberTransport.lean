import FK.AdaptiveStopping
import FK.RegionSeal
import FK.StoppedInterior

/-! # Transport of exterior-fibre conditioning to an arbitrary vertex region -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling
open FK.RegionSeal FK.FinitePlane

variable {G : LabelledMultigraph} (U : Set G.Vertex) [DecidablePred (· ∈ U)]

/-- The canonical equivalence between configurations and configurations on the
sum of the internal and external label types. -/
noncomputable def splitSumEquiv : G.Configuration ≃
    (RegionSeal.Internal G U ⊕ RegionSeal.External G U → Bool) where
  toFun ω := Sum.elim (fun i => ω i.1) (fun o => ω o.1)
  invFun z e := if h : IsInternal G U e then z (Sum.inl ⟨e, h⟩) else z (Sum.inr ⟨e, h⟩)
  left_inv ω := by
    funext e
    by_cases h : IsInternal G U e <;> simp [h]
  right_inv z := by
    funext a
    cases a with
    | inl i =>
        change (if h : IsInternal G U i.1 then z (Sum.inl ⟨i.1, h⟩) else
          z (Sum.inr ⟨i.1, h⟩)) = z (Sum.inl i)
        rw [dif_pos i.2]
    | inr o =>
        change (if h : IsInternal G U o.1 then z (Sum.inl ⟨o.1, h⟩) else
          z (Sum.inr ⟨o.1, h⟩)) = z (Sum.inr o)
        rw [dif_neg o.2]

lemma splitSumEquiv_symm_glue (ω : RegionSeal.Internal G U → Bool)
    (ζ : RegionSeal.External G U → Bool) :
    (splitSumEquiv (G := G) U).symm (glue ω ζ) = glueExt G U ω ζ := by
  funext e
  by_cases h : IsInternal G U e
  · change (if h' : IsInternal G U e then ω ⟨e, h'⟩ else ζ ⟨e, h'⟩) = _
    rw [dif_pos h]
    exact (glueExt_of_internal G U ω ζ e h).symm
  · change (if h' : IsInternal G U e then ω ⟨e, h'⟩ else ζ ⟨e, h'⟩) = _
    rw [dif_neg h]
    exact (glueExt_of_external G U ω ζ e h).symm

lemma restrictO_splitSumEquiv_symm (z : RegionSeal.Internal G U ⊕
    RegionSeal.External G U → Bool) :
    restrictO G U ((splitSumEquiv (G := G) U).symm z) = z ∘ Sum.inr := by
  funext o
  change (if h : IsInternal G U o.1 then z (Sum.inl ⟨o.1, h⟩) else
    z (Sum.inr ⟨o.1, h⟩)) = z (Sum.inr o)
  rw [dif_neg o.2]

lemma splitSumEquiv_symm_preimage_extFiber (ζ : RegionSeal.External G U → Bool) :
    (splitSumEquiv (G := G) U).symm ⁻¹' extFiber G U ζ = exteriorFiber ζ := by
  ext z
  constructor
  · intro hz o
    change restrictO G U ((splitSumEquiv (G := G) U).symm z) = ζ at hz
    rw [restrictO_splitSumEquiv_symm] at hz
    exact congrFun hz o
  · intro hz
    change restrictO G U ((splitSumEquiv (G := G) U).symm z) = ζ
    rw [restrictO_splitSumEquiv_symm]
    funext o
    exact hz o

lemma restrictI_splitSumEquiv_symm (z : RegionSeal.Internal G U ⊕
    RegionSeal.External G U → Bool) :
    restrictI G U ((splitSumEquiv (G := G) U).symm z) = z ∘ Sum.inl := by
  funext i
  change (if h : IsInternal G U i.1 then z (Sum.inl ⟨i.1, h⟩) else
    z (Sum.inr ⟨i.1, h⟩)) = z (Sum.inl i)
  rw [dif_pos i.2]

lemma filter_congr_set {A : Type*} [Fintype A] (μ : PMF A)
    {s t : Set A} (h : s = t) (hs : ∃ a ∈ s, a ∈ μ.support)
    (ht : ∃ a ∈ t, a ∈ μ.support) : μ.filter s hs = μ.filter t ht := by
  subst t
  rfl

/-- The actual FK law filtered to a full region-exterior fibre and restricted
to its interior is exactly `RegionSeal.fiberPMF`. -/
theorem map_restrictI_filter_fkPMF (α : G.BoundaryPartition)
    (ζ : RegionSeal.External G U → Bool) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ((G.fkPMF hq hp₁.le α).filter (extFiber G U ζ)
      (by
        refine ⟨glueExt G U (fun _ => false) ζ, glueExt_mem_extFiber G U _ ζ, ?_⟩
        exact (PMF.mem_support_iff _ _).2 (fkPMF_ne_zero G hq hp₀ hp₁ α _))).map
        (restrictI G U) = fiberPMF G U α ζ hq hp₀ hp₁ := by
  let e : (RegionSeal.Internal G U ⊕ RegionSeal.External G U → Bool) ≃ G.Configuration :=
    (splitSumEquiv (G := G) U).symm
  let w : (RegionSeal.Internal G U ⊕ RegionSeal.External G U → Bool) → NNReal :=
    fun z => FK.FinitePlane.fkWeight q p (G.componentCount α) (e z)
  have hw : ∀ z, 0 < w z := fun z => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _
  have hnorm : (normalizedPMF w hw).map e = G.fkPMF hq hp₁.le α := by
    apply normalizedPMF_map_eq_of_proportional e w
      (fun ω => FK.FinitePlane.fkWeight q p (G.componentCount α) ω) 1 zero_lt_one hw
      (fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ ω)
    intro z
    simp [w]
  have hcond : conditionedPMF w hw ζ = fiberPMF G U α ζ hq hp₀ hp₁ := by
    unfold conditionedPMF fiberPMF
    congr 1
  have hmap := map_glue_conditionedPMF w hw ζ
  rw [hcond] at hmap
  have hA : ∃ a ∈ e ⁻¹' extFiber G U ζ, a ∈ (normalizedPMF w hw).support := by
    rw [show e ⁻¹' extFiber G U ζ = exteriorFiber ζ from
      splitSumEquiv_symm_preimage_extFiber U ζ]
    exact exteriorFiber_support w hw ζ
  have hB : ∃ b ∈ extFiber G U ζ, b ∈ ((normalizedPMF w hw).map e).support := by
    rw [hnorm]
    refine ⟨glueExt G U (fun _ => false) ζ, glueExt_mem_extFiber G U _ ζ, ?_⟩
    exact (PMF.mem_support_iff _ _).2 (fkPMF_ne_zero G hq hp₀ hp₁ α _)
  have hfilter := FK.Exploration.StoppedInterior.map_filter_equiv e
    (normalizedPMF w hw) (extFiber G U ζ) hA hB
  have hpre : e ⁻¹' extFiber G U ζ = exteriorFiber ζ :=
    splitSumEquiv_symm_preimage_extFiber U ζ
  simp only [hpre, hnorm] at hfilter
  let hs := exteriorFiber_support w hw ζ
  have hset : (normalizedPMF w hw).filter (exteriorFiber ζ) hs =
      (normalizedPMF w hw).filter (e ⁻¹' extFiber G U ζ) hA :=
    filter_congr_set (normalizedPMF w hw) hpre.symm hs hA
  have hB' : ∃ b ∈ extFiber G U ζ, b ∈ (G.fkPMF hq hp₁.le α).support := by
    refine ⟨glueExt G U (fun _ => false) ζ, glueExt_mem_extFiber G U _ ζ, ?_⟩
    exact (PMF.mem_support_iff _ _).2 (fkPMF_ne_zero G hq hp₀ hp₁ α _)
  have hfilterStd : ((normalizedPMF w hw).filter (exteriorFiber ζ) hs).map e =
      (G.fkPMF hq hp₁.le α).filter (extFiber G U ζ) hB' := by
    with_unfolding_all exact hfilter
  rw [← hfilterStd, PMF.map_comp]
  have hlift := congrArg (PMF.map ((restrictI G U) ∘ e)) hmap.symm
  rw [PMF.map_comp] at hlift
  have hid : ((restrictI G U ∘ e) ∘
      (fun ω : RegionSeal.Internal G U → Bool => glue ω ζ)) = id := by
    funext ω
    change restrictI G U (glueExt G U ω ζ) = ω
    exact restrictI_glueExt G U ω ζ
  rw [hid, PMF.map_id] at hlift
  with_unfolding_all exact hlift

end FK.Adaptive
