import FK.ForestGeometry

/-! # One-endpoint attachment of a straight segment -/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval
open FK.PlaneTopology.Continuous.Segment

/-- **One-endpoint straight-segment attachment.**  The old compact carrier
meets the new segment exactly at its source endpoint.  Its complement has the
same path-connectedness property as before the attachment. -/
theorem isPathConnected_compl_union_segment_of_attached
    {K : Set Plane} (hKcompact : IsCompact K) {a b : Plane} (hab : a ≠ b)
    (hinter : K ∩ [a -[ℝ] b] = {a})
    (hconn : IsPathConnected Kᶜ) :
    IsPathConnected (K ∪ [a -[ℝ] b])ᶜ := by
  have hKopen : IsOpen Kᶜ := hKcompact.isClosed.isOpen_compl
  have haK : a ∈ K := by
    have ha : a ∈ K ∩ [a -[ℝ] b] := by
      rw [hinter]
      exact mem_singleton a
    exact ha.1
  have hbS : b ∈ [a -[ℝ] b] := right_mem_segment ℝ a b
  have hbU : b ∈ Kᶜ := by
    intro hbK
    have hb : b ∈ K ∩ [a -[ℝ] b] := ⟨hbK, hbS⟩
    rw [hinter, mem_singleton_iff] at hb
    exact hab hb.symm
  obtain ⟨q, hq, hbc⟩ := exists_scaledBase_segment_subset hKopen hbU
  have hcU : scaledBase a b q ∈ Kᶜ := hbc (right_mem_segment ℝ _ _)
  have hcS : scaledBase a b q ∈ ([a -[ℝ] b] : Set Plane)ᶜ :=
    scaledBase_mem_compl_segment hab hq
  have hlink : ∀ z ∈ Kᶜ ∩ [a -[ℝ] b], ∃ N ∈ 𝓝 z,
      ∀ x ∈ N, x ∈ Kᶜ \ [a -[ℝ] b] →
        JoinedIn (Kᶜ \ [a -[ℝ] b]) x (scaledBase a b q) := by
    intro z hz
    have hza : z ≠ a := by
      intro hza
      subst z
      exact hz.1 haK
    have hTU : [z -[ℝ] scaledBase a b q] ⊆ Kᶜ :=
      segment_scaledBase_subset_compl_of_attached hab hq hinter hz.2 hza hbc
    obtain ⟨δ, hδ, hWU⟩ := IsCompact.exists_thickening_subset_open
      (isCompact_straightSegment z (scaledBase a b q)) hKopen hTU
    let W := thickening δ [z -[ℝ] scaledBase a b q]
    have hWopen : IsOpen W := Metric.isOpen_thickening
    have hWconv : Convex ℝ W := (convex_segment z (scaledBase a b q)).thickening δ
    have hTW : [z -[ℝ] scaledBase a b q] ⊆ W :=
      Metric.self_subset_thickening hδ _
    have hzW : z ∈ W := hTW (left_mem_segment ℝ _ _)
    have hcW : scaledBase a b q ∈ W := hTW (right_mem_segment ℝ _ _)
    let r := δ / (2 * (‖normal a b‖ + 1))
    have hrdden : 0 < 2 * (‖normal a b‖ + 1) := by positivity
    have hr : 0 < r := div_pos hδ hrdden
    have hrn : ‖r • normal a b‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      have hid : r * (‖normal a b‖ + 1) = δ / 2 := by
        dsimp [r]
        field_simp [hrdden.ne'] <;> ring
      have hle : r * ‖normal a b‖ ≤ r * (‖normal a b‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (normal a b)]) hr.le
      nlinarith
    have hzrW : z + r • normal a b ∈ W := by
      apply (Metric.ball_subset_thickening (show z ∈ [z -[ℝ] scaledBase a b q] from
        left_mem_segment ℝ _ _) δ)
      rw [mem_ball']
      simpa [dist_eq_norm] using hrn
    have hcrW : scaledBase a b q + r • normal a b ∈ W := by
      apply (Metric.ball_subset_thickening (show scaledBase a b q ∈
        [z -[ℝ] scaledBase a b q] from right_mem_segment ℝ _ _) δ)
      rw [mem_ball']
      simpa [dist_eq_norm] using hrn
    let offFar : Plane → Plane := fun x => scaledBase a b q +
      (side a b x / dirNormSq a b) • normal a b
    let onPoint : Plane → Plane := fun x => x + r • normal a b
    have hoffCont : Continuous offFar := by
      dsimp [offFar]
      unfold side
      fun_prop
    have honCont : Continuous onPoint := by
      dsimp [onPoint]
      fun_prop
    let N := (W ∩ offFar ⁻¹' W) ∩ onPoint ⁻¹' W
    have hoffz : offFar z ∈ W := by
      have hs0 := (segment_coordinates hab hz.2).1
      have heq : offFar z = scaledBase a b q := by simp [offFar, hs0]
      rw [heq]
      exact hcW
    have hzN : z ∈ N := ⟨⟨hzW, hoffz⟩, hzrW⟩
    have hNopen : IsOpen N :=
      (hWopen.inter (hWopen.preimage hoffCont)).inter (hWopen.preimage honCont)
    refine ⟨N, hNopen.mem_nhds hzN, ?_⟩
    intro x hxN hxF
    by_cases hs : side a b x = 0
    · apply joinedIn_scaledDetour_of_convex_subset hWconv hWU hab hr.ne' hq hxF hxN.1.1
      · rw [scaledSide_eq_add_of_side_eq_zero hs]
        exact hxN.2
      · rw [scaledFar_eq_add_of_side_eq_zero hab hs]
        exact hcrW
      · exact hcW
    · apply joinedIn_scaledDetour_of_convex_subset hWconv hWU hab hr.ne' hq hxF hxN.1.1
      · rw [scaledSide_eq_self_of_side_ne hs]
        exact hxN.1.1
      · rw [scaledFar_eq_offline q x hs]
        exact hxN.1.2
      · exact hcW
  have hresult := isPathConnected_diff_of_localLink hKopen
    (isCompact_straightSegment a b).isClosed hconn.isConnected.isPreconnected
    ⟨b, hbU, hbS⟩ ⟨hcU, hcS⟩ hlink
  simpa only [Set.diff_eq, compl_union, compl_compl] using hresult


end
end FK.PlaneTopology.Continuous.Forest
