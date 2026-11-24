/-
# The conditional region law is not stratum-independent without separation

`ConfinedStrata.stratum_conditional_region_eq_region` proves that on any
pointwise separated exterior stratum the conditional region law of the ambient
confined FK law is `regionGraph.fkPMF theta`.  On the explicit geometry of
`ConfinedStrataObstruction` (one interior edge `0 -- 1` and one exterior label
parallel to it, free boundaries, so confinement holds but separation fails) that
conclusion is *false*:

  `((ambientFK).filter (exterior open)).map (region projection) != regionFK`

The proof assembles `mass_eq_of_map_filter_eq` (the necessary direction of
`map_filter_eq_of_mass_factorization`), `fkPMF_mass_eq`, the exact weights
`oAmb_w_open`, `oAmb_w_closed`, `oRegionW_open`, `oRegionW_closed`, and the
four-configuration sum `sum_amb`.
-/
import FK.ConfinedStrataObstruction

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement.ConfinedStrata

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

section StratumLaw

/-- The ambient FK law at `q = p = 1/2` on the explicit geometry. -/
noncomputable abbrev oAmbFK : PMF (Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool) :=
  oAmb.fkPMF (q := 1 / 2) (p := 1 / 2)
    (by norm_num : (0 : NNReal) < 1 / 2) (by norm_num : (1 / 2 : NNReal) ≤ 1) oBd

/-- The region FK law at `q = p = 1/2` on the explicit geometry. -/
noncomputable abbrev oRegFK : PMF (Fin 1 → Bool) :=
  (regionGraph oSi oTi).fkPMF (q := 1 / 2) (p := 1 / 2)
    (by norm_num : (0 : NNReal) < 1 / 2) (by norm_num : (1 / 2 : NNReal) ≤ 1) oTh

/-- The exterior-open stratum has positive mass. -/
theorem oSupp : ∃ ρ ∈ extMask (I := Fin 1) oE, ρ ∈ oAmbFK.support :=
  extMask_support oSi oTi oSo oXo oAo oBo oBd
    (q := 1 / 2) (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    oE ⟨fun _ => true, rfl⟩

/-- Region FK point masses are the region weights over the region partition
function. -/
theorem oRegFK_apply (ω : Fin 1 → Bool) :
    (oRegFK ω : ℝ≥0∞) =
      (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞) *
        (∑' ω : Fin 1 → Bool, (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞))⁻¹ :=
  FK.FinitePlane.normalizedPMF_apply (regionWeight oSi oTi oTh (1 / 2) (1 / 2))
    (fun a => regionWeight_pos (by norm_num) (by norm_num) (by norm_num) a) ω

theorem oRegionSum_ne_zero :
    (∑' ω : Fin 1 → Bool, (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞)) ≠ 0 :=
  FK.FinitePlane.tsum_coe_ne_zero_of_pos (regionWeight oSi oTi oTh (1 / 2) (1 / 2))
    (fun ω => regionWeight_pos (by norm_num) (by norm_num) (by norm_num) ω)

theorem oRegionSum_ne_top :
    (∑' ω : Fin 1 → Bool, (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞)) ≠ ∞ :=
  FK.FinitePlane.tsum_coe_ne_top (regionWeight oSi oTi oTh (1 / 2) (1 / 2))

theorem oAmbSum_ne_zero :
    (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
      (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) ≠ 0 :=
  FK.FinitePlane.tsum_coe_ne_zero_of_pos (fun ρ => oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ)
    (fun ρ => oAmb.fkWeight_pos (by norm_num) (by norm_num) (by norm_num) oBd ρ)

theorem oAmbSum_ne_top :
    (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
      (oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞)) ≠ ∞ :=
  FK.FinitePlane.tsum_coe_ne_top (fun ρ => oAmb.fkWeight (1 / 2) (1 / 2) oBd ρ)


/-- **The conditional region law is not the region FK law on the unseparated
stratum.**  Conditioning the ambient confined FK law (at `q = p = 1/2`) on the
stratum "the exterior label is open" and reading off the region configuration
does *not* give `regionGraph.fkPMF theta`, although every other hypothesis of
`stratum_conditional_region_eq_region` holds.

The stratum mass identity would force
`(1/4)*(1/4) = (1/8)*(3/8)`, i.e. `1/16 = 3/64`. -/
theorem conditional_region_ne_region :
    ((oAmbFK).filter (extMask (I := Fin 1) oE) oSupp).map (fun ρ => ρ ∘ Sum.inl) ≠ oRegFK := by
  intro hcontra
  set R : ℝ≥0∞ := ∑' ω : Fin 1 → Bool, oA.indicator (fun ω => (oRegFK ω : ℝ≥0∞)) ω with hR
  set M : ℝ≥0∞ := ∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
    (extMask (I := Fin 1) oE).indicator (fun ρ => (oAmbFK ρ : ℝ≥0∞)) ρ with hM
  set AE : ℝ≥0∞ := ∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
    (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
      (fun ρ => (oAmbFK ρ : ℝ≥0∞)) ρ with hAE
  set ZrE : ℝ≥0∞ := ∑' ω : Fin 1 → Bool,
    (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞) with hZrE
  set Zw : ℝ≥0∞ := ∑' ρ : (ambientOfSum (splitSource oSi (bigSo oSo oAo))
      (splitTarget oTi (bigXo oXo oBo))).Configuration,
      ((ambientOfSum (splitSource oSi (bigSo oSo oAo))
        (splitTarget oTi (bigXo oXo oBo))).fkWeight (1 / 2) (1 / 2) oBd ρ : ℝ≥0∞) with hZw
  -- (i) the necessary mass identity coming from the conditional law
  have hmass : R * M = AE := by
    have h := mass_eq_of_map_filter_eq (P := oAmbFK) (f := fun ρ => ρ ∘ Sum.inl)
      (T := extMask (I := Fin 1) oE) oSupp oRegFK hcontra oA
    rw [show ((fun ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool => ρ ∘ Sum.inl) ⁻¹' oA) =
        regionMask (I := Fin 1) oA from rfl] at h
    exact h
  -- (ii) region mass: R * ZrE = 1/4
  have hRZR : R * ZrE = ((1 / 4 : NNReal) : ℝ≥0∞) := by
    have h : R = (∑' ω : Fin 1 → Bool, oA.indicator
          (fun ω => (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞)) ω) * ZrE⁻¹ := by
      rw [hR, hZrE]
      rw [show (∑' ω : Fin 1 → Bool, oA.indicator (fun ω => (oRegFK ω : ℝ≥0∞)) ω) =
          ∑' ω : Fin 1 → Bool, oA.indicator
              (fun ω => (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞)) ω *
            (∑' ω : Fin 1 → Bool,
              (regionWeight oSi oTi oTh (1 / 2) (1 / 2) ω : ℝ≥0∞))⁻¹ from by
        refine tsum_congr (fun ω => ?_)
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hω : ω ∈ oA
        · rw [ite_eq_left hω, ite_eq_left hω, oRegFK_apply]
        · rw [ite_eq_right hω, ite_eq_right hω, zero_mul]]
      rw [ENNReal.tsum_mul_right]
    rw [h, oRegionASum, hZrE, oRegionSum, mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr (by norm_num : (3 / 8 : NNReal) ≠ 0))
        ENNReal.coe_ne_top, mul_one]
  -- (iii) stratum mass: M * Zw = 1/4
  have hMZW : M * Zw = ((1 / 4 : NNReal) : ℝ≥0∞) := by
    have h := FK.RegionConfinement.PrefixContinuation.fkPMF_mass_eq oSi oTi oSo oXo oAo oBo
      oBd (q := 1 / 2) (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (extMask (I := Fin 1) oE)
    rw [hM]
    rw [show (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
        (extMask (I := Fin 1) oE).indicator (fun ρ => (oAmbFK ρ : ℝ≥0∞)) ρ) =
      (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
        (extMask (I := Fin 1) oE).indicator (fun ρ =>
          (((ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkPMF (q := 1 / 2) (p := 1 / 2)
              (by norm_num) (by norm_num) oBd) ρ : ℝ≥0∞)) ρ) from rfl]
    rw [h, oAmbSum_ext, hZw, mul_assoc,
      ENNReal.inv_mul_cancel
        (FK.FinitePlane.tsum_coe_ne_zero_of_pos
          (fun ρ => ((ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkWeight (1 / 2) (1 / 2) oBd ρ))
          (fun ρ => (ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkWeight_pos (by norm_num) (by norm_num)
              (by norm_num) oBd ρ))
        (FK.FinitePlane.tsum_coe_ne_top
          (fun ρ => ((ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkWeight (1 / 2) (1 / 2) oBd ρ))),
      mul_one]
  -- (iv) joint mass: AE * Zw = 1/8
  have hAEZ : AE * Zw = ((1 / 8 : NNReal) : ℝ≥0∞) := by
    have h := FK.RegionConfinement.PrefixContinuation.fkPMF_mass_eq oSi oTi oSo oXo oAo oBo
      oBd (q := 1 / 2) (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE)
    rw [hAE]
    rw [show (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
        (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator
          (fun ρ => (oAmbFK ρ : ℝ≥0∞)) ρ) =
      (∑' ρ : Fin 1 ⊕ (Fin 1 ⊕ Fin 0) → Bool,
        (regionMask (I := Fin 1) oA ∩ extMask (I := Fin 1) oE).indicator (fun ρ =>
          (((ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkPMF (q := 1 / 2) (p := 1 / 2)
              (by norm_num) (by norm_num) oBd) ρ : ℝ≥0∞)) ρ) from rfl]
    rw [h, oAmbSum_AE, hZw, mul_assoc,
      ENNReal.inv_mul_cancel
        (FK.FinitePlane.tsum_coe_ne_zero_of_pos
          (fun ρ => ((ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkWeight (1 / 2) (1 / 2) oBd ρ))
          (fun ρ => (ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkWeight_pos (by norm_num) (by norm_num)
              (by norm_num) oBd ρ))
        (FK.FinitePlane.tsum_coe_ne_top
          (fun ρ => ((ambientOfSum (splitSource oSi (bigSo oSo oAo))
            (splitTarget oTi (bigXo oXo oBo))).fkWeight (1 / 2) (1 / 2) oBd ρ))),
      mul_one]
  -- (v) the numerical contradiction
  have key : ((1 / 4 : NNReal) : ℝ≥0∞) * ((1 / 4 : NNReal) : ℝ≥0∞) =
      ((1 / 8 : NNReal) : ℝ≥0∞) * ((3 / 8 : NNReal) : ℝ≥0∞) := by
    have h : R * ZrE * (M * Zw) = AE * Zw * ZrE := by
      rw [show R * ZrE * (M * Zw) = R * M * (ZrE * Zw) from by ac_rfl, hmass]
      ac_rfl
    rw [hRZR, hMZW, hAEZ, hZrE, oRegionSum] at h
    exact h
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ENNReal.coe_inj] at key
  norm_num at key

end StratumLaw

end FK.RegionConfinement.ConfinedStrata
