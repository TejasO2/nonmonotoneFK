import FK.ScaledDetour

/-!
# Geometric attachment lemma for straight segment forests

The old carrier meets the new segment exactly at its source endpoint.  The
complement of the new carrier is proved path connected using the abstract
common-local-link theorem and scaled explicit detours.
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval
open FK.PlaneTopology.Continuous.Segment

lemma scaledBase_eq_lineMap (a b : Plane) (q : ℝ) :
    scaledBase a b q = AffineMap.lineMap a b q := by
  simp [scaledBase, AffineMap.lineMap_apply, add_comm]

lemma lineMap_lineMap_segment (a b : Plane) (s t v : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) v =
      AffineMap.lineMap a b ((1 - v) * s + v * t) := by
  simp only [AffineMap.lineMap_apply_module]
  module

lemma lineMap_mem_segment_of_le {a b : Plane} {s t u : ℝ}
    (hsu : s ≤ u) (hut : u ≤ t) :
    AffineMap.lineMap a b u ∈
      [AffineMap.lineMap a b s -[ℝ] AffineMap.lineMap a b t] := by
  by_cases hst : s = t
  · subst t
    have hu : u = s := le_antisymm hut hsu
    subst u
    exact left_mem_segment ℝ _ _
  · have hstle : s < t := lt_of_le_of_ne (hsu.trans hut) hst
    let v := (u - s) / (t - s)
    have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr hsu) (sub_nonneg.mpr hstle.le)
    have hv1 : v ≤ 1 := by
      change (u - s) / (t - s) ≤ 1
      rw [div_le_one (sub_pos.mpr hstle)]
      linarith
    rw [segment_eq_image_lineMap]
    refine ⟨v, ⟨hv0, hv1⟩, ?_⟩
    rw [lineMap_lineMap_segment]
    congr 1
    dsimp [v]
    field_simp [sub_ne_zero.mpr hst]
    ring

lemma isCompact_straightSegment (a b : Plane) : IsCompact [a -[ℝ] b] := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- The tube from a non-attachment segment point to an extension beyond the
free endpoint stays in the old complement. -/
lemma segment_scaledBase_subset_compl_of_attached
    {K : Set Plane} {a b z : Plane} {q : ℝ}
    (hab : a ≠ b) (hq : 1 < q) (hinter : K ∩ [a -[ℝ] b] = {a})
    (hzab : z ∈ [a -[ℝ] b]) (hza : z ≠ a)
    (hbc : [b -[ℝ] scaledBase a b q] ⊆ Kᶜ) :
    [z -[ℝ] scaledBase a b q] ⊆ Kᶜ := by
  rw [segment_eq_image_lineMap] at hzab
  obtain ⟨tz, htz, rfl⟩ := hzab
  have htzne : tz ≠ 0 := by
    intro hz
    apply hza
    calc
      AffineMap.lineMap a b tz = AffineMap.lineMap a b (0 : ℝ) := congrArg _ hz
      _ = a := AffineMap.lineMap_apply_zero _ _
  have htzpos : 0 < tz := lt_of_le_of_ne htz.1 (Ne.symm htzne)
  intro x hx
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [scaledBase_eq_lineMap, lineMap_lineMap_segment]
  let s := (1 - t) * tz + t * q
  have hqtz : tz ≤ q := htz.2.trans hq.le
  have hslo : tz ≤ s := by
    dsimp [s]
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hqtz)]
  have hshi : s ≤ q := by
    dsimp [s]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hqtz)]
  have hspos : 0 < s := htzpos.trans_le hslo
  intro hxK
  by_cases hs1 : s ≤ 1
  · have hxS : AffineMap.lineMap a b s ∈ [a -[ℝ] b] := by
      exact lineMap_mem_segment ℝ a b ⟨hspos.le, hs1⟩
    have hxmem : AffineMap.lineMap a b s ∈ K ∩ [a -[ℝ] b] := ⟨hxK, hxS⟩
    rw [hinter, mem_singleton_iff] at hxmem
    have heq0 : AffineMap.lineMap a b s = AffineMap.lineMap a b (0 : ℝ) := by
      exact hxmem.trans (AffineMap.lineMap_apply_zero _ _).symm
    have hs0 : s = 0 := (AffineMap.lineMap_injective ℝ hab) heq0
    linarith
  · have hs1' : 1 ≤ s := le_of_lt (lt_of_not_ge hs1)
    have hxbc : AffineMap.lineMap a b s ∈
        [AffineMap.lineMap a b (1 : ℝ) -[ℝ] AffineMap.lineMap a b q] :=
      lineMap_mem_segment_of_le hs1' hshi
    rw [AffineMap.lineMap_apply_one, ← scaledBase_eq_lineMap] at hxbc
    exact hbc hxbc hxK

/-- There is an arbitrarily short extension beyond a free endpoint which
stays in the old open complement. -/
lemma exists_scaledBase_segment_subset
    {K : Set Plane} {a b : Plane} (hKopen : IsOpen Kᶜ) (hb : b ∈ Kᶜ) :
    ∃ q : ℝ, 1 < q ∧ [b -[ℝ] scaledBase a b q] ⊆ Kᶜ := by
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hKopen) b hb
  let q := 1 + ε / (2 * (dist a b + 1))
  have hden : 0 < 2 * (dist a b + 1) := by positivity
  have heta : 0 < ε / (2 * (dist a b + 1)) := div_pos hε hden
  have hq : 1 < q := by dsimp [q]; linarith
  have hcball : scaledBase a b q ∈ ball b ε := by
    rw [mem_ball', dist_comm, scaledBase_eq_lineMap, dist_lineMap_right]
    have hq0 : 0 ≤ q - 1 := sub_nonneg.mpr hq.le
    have hnorm : ‖1 - q‖ = q - 1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : 1 - q ≤ 0)]
      ring
    rw [hnorm]
    have hbound : (q - 1) * dist a b < ε := by
      have hid : q - 1 = ε / (2 * (dist a b + 1)) := by dsimp [q]; ring
      rw [hid]
      have heq : ε / (2 * (dist a b + 1)) * dist a b =
          ε * dist a b / (2 * (dist a b + 1)) := by ring
      rw [heq, div_lt_iff₀ hden]
      nlinarith [dist_nonneg (x := a) (y := b)]
    exact hbound
  refine ⟨q, hq, fun x hx => hball ?_⟩
  exact (convex_ball b ε).segment_subset (mem_ball_self hε) hcball hx

/-- A scaled detour whose vertices lie in a convex subset of the old
complement stays in the new complement. -/
lemma joinedIn_scaledDetour_of_convex_subset
    {K W : Set Plane} {a b x : Plane} {q r : ℝ}
    (hWconv : Convex ℝ W) (hWU : W ⊆ Kᶜ)
    (hab : a ≠ b) (hr : r ≠ 0) (hq : 1 < q)
    (hx : x ∈ Kᶜ \ [a -[ℝ] b]) (hxW : x ∈ W)
    (hsideW : scaledSide a b x r ∈ W)
    (hfarW : scaledFar a b q x r ∈ W)
    (hbaseW : scaledBase a b q ∈ W) :
    JoinedIn (Kᶜ \ [a -[ℝ] b]) x (scaledBase a b q) := by
  have h1 : JoinedIn (Kᶜ \ [a -[ℝ] b]) x (scaledSide a b x r) := by
    apply JoinedIn.of_segment_subset
    intro y hy
    exact ⟨hWU (hWconv.segment_subset hxW hsideW hy),
      segment_scaledSide_subset_compl hab hr hx.2 hy⟩
  have h2 : JoinedIn (Kᶜ \ [a -[ℝ] b])
      (scaledSide a b x r) (scaledFar a b q x r) := by
    apply JoinedIn.of_segment_subset
    intro y hy
    exact ⟨hWU (hWconv.segment_subset hsideW hfarW hy),
      segment_scaledFar_subset_compl hab hr q x hy⟩
  have h3 : JoinedIn (Kᶜ \ [a -[ℝ] b])
      (scaledFar a b q x r) (scaledBase a b q) := by
    apply JoinedIn.of_segment_subset
    intro y hy
    exact ⟨hWU (hWconv.segment_subset hfarW hbaseW hy),
      segment_scaledBase_subset_compl hab hq x r hy⟩
  exact h1.trans (h2.trans h3)

end
end FK.PlaneTopology.Continuous.Forest
