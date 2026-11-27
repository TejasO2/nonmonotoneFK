import FK.ContinuousPlane

/-!
# The complement of a straight segment

This file proves an explicit finite polygonal separation theorem with no
Jordan-curve input: a nondegenerate straight segment in `ℝ × ℝ` never
disconnects the plane. The proof constructs a three-leg polygonal path from
an arbitrary off-segment point to a fixed point beyond the target endpoint.
-/

namespace FK.PlaneTopology.Continuous.Segment

noncomputable section

open Set
open scoped Classical Convex unitInterval

open FK.PlaneTopology.Continuous

/-- Squared Euclidean length of the direction vector. -/
def dirNormSq (a b : Plane) : ℝ := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

/-- A normal to the oriented segment. -/
def normal (a b : Plane) : Plane := (-(b.2 - a.2), b.1 - a.1)

/-- Signed cross-product coordinate relative to the segment's supporting line. -/
def side (a b x : Plane) : ℝ :=
  (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)

/-- Affine coordinate in the direction of the segment. -/
def progress (a b x : Plane) : ℝ :=
  ((x.1 - a.1) * (b.1 - a.1) + (x.2 - a.2) * (b.2 - a.2)) / dirNormSq a b

lemma dirNormSq_pos {a b : Plane} (hab : a ≠ b) : 0 < dirNormSq a b := by
  have hfast : b.1 - a.1 ≠ 0 ∨ b.2 - a.2 ≠ 0 := by
    by_contra! h
    apply hab
    apply Prod.ext
    · linarith [h.1]
    · linarith [h.2]
  rcases hfast with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)

@[simp] lemma side_affine (a b : Plane) (t : ℝ) :
    side a b (a + t • (b - a)) = 0 := by
  simp [side]
  ring

@[simp] lemma progress_affine {a b : Plane} (hab : a ≠ b) (t : ℝ) :
    progress a b (a + t • (b - a)) = t := by
  have h := (dirNormSq_pos hab).ne'
  simp [progress]
  field_simp [h]
  unfold dirNormSq
  ring

lemma side_add_normal (a b x : Plane) (r : ℝ) :
    side a b (x + r • normal a b) = side a b x + r * dirNormSq a b := by
  simp [side, normal, dirNormSq]
  ring

lemma progress_add_normal {a b : Plane} (hab : a ≠ b) (x : Plane) (r : ℝ) :
    progress a b (x + r • normal a b) = progress a b x := by
  have h := (dirNormSq_pos hab).ne'
  simp [progress, normal]
  field_simp [h]
  ring

lemma side_lineMap (a b x y : Plane) (t : ℝ) :
    side a b (AffineMap.lineMap x y t) =
      (1 - t) * side a b x + t * side a b y := by
  simp [side, AffineMap.lineMap_apply]
  ring

lemma progress_lineMap (a b x y : Plane) (t : ℝ) :
    progress a b (AffineMap.lineMap x y t) =
      (1 - t) * progress a b x + t * progress a b y := by
  simp [progress, AffineMap.lineMap_apply]
  ring

/-- Every point of the segment has zero side coordinate and progress in `[0,1]`. -/
lemma segment_coordinates {a b x : Plane} (hab : a ≠ b)
    (hx : x ∈ [a -[ℝ] b]) :
    side a b x = 0 ∧ 0 ≤ progress a b x ∧ progress a b x ≤ 1 := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hdiff : (AffineMap.lineMap a b (t : ℝ)) = a + t • (b - a) := by
    simp [AffineMap.lineMap_apply]
    abel
  rw [hdiff, side_affine, progress_affine hab]
  exact ⟨rfl, ht.1, ht.2⟩

/-- The normal displacement used when a point is on the supporting line. -/
def offset (a b x : Plane) : ℝ := if side a b x = 0 then 1 else 0

/-- First detour vertex, off the supporting line. -/
def detourSide (a b x : Plane) : Plane := x + offset a b x • normal a b

/-- The common endpoint coordinate beyond which every detour finishes. -/
def detourParam (_a _b _x : Plane) : ℝ := 2

/-- Common endpoint of all detours, beyond `b` on its supporting line. -/
def detourBase (a b x : Plane) : Plane := a + detourParam a b x • (b - a)

/-- Last off-line detour vertex, with the same side coordinate as `detourSide`. -/
def detourFar (a b x : Plane) : Plane :=
  detourBase a b x +
    (side a b (detourSide a b x) / dirNormSq a b) • normal a b

lemma side_detourSide_ne {a b : Plane} (hab : a ≠ b) (x : Plane) :
    side a b (detourSide a b x) ≠ 0 := by
  unfold detourSide offset
  rw [side_add_normal]
  by_cases hx : side a b x = 0
  · simp [hx, (dirNormSq_pos hab).ne']
  · simp [hx]

lemma progress_detourSide {a b : Plane} (hab : a ≠ b) (x : Plane) :
    progress a b (detourSide a b x) = progress a b x := by
  exact progress_add_normal hab _ _

lemma detourParam_gt_one (a b x : Plane) : 1 < detourParam a b x := by
  norm_num [detourParam]

lemma side_detourBase (a b x : Plane) : side a b (detourBase a b x) = 0 := by
  exact side_affine _ _ _

lemma progress_detourBase {a b : Plane} (hab : a ≠ b) (x : Plane) :
    progress a b (detourBase a b x) = detourParam a b x := by
  exact progress_affine hab _

lemma side_detourFar {a b : Plane} (hab : a ≠ b) (x : Plane) :
    side a b (detourFar a b x) = side a b (detourSide a b x) := by
  rw [detourFar, side_add_normal, side_detourBase]
  field_simp [(dirNormSq_pos hab).ne']
  simp

lemma progress_detourFar {a b : Plane} (hab : a ≠ b) (x : Plane) :
    progress a b (detourFar a b x) = detourParam a b x := by
  rw [detourFar, progress_add_normal hab, progress_detourBase hab]

/-- The first leg leaves the supporting line without meeting the segment. -/
lemma segment_detourSide_subset_compl {a b : Plane} (hab : a ≠ b) {x : Plane}
    (hx : x ∈ ([a -[ℝ] b] : Set Plane)ᶜ) :
    [x -[ℝ] detourSide a b x] ⊆ ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro z hz hzab
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hs := (segment_coordinates hab hzab).1
  by_cases hxside : side a b x = 0
  · have hsd : side a b (detourSide a b x) = dirNormSq a b := by
      rw [detourSide, side_add_normal, offset, if_pos hxside, hxside]
      ring
    rw [side_lineMap, hsd, hxside] at hs
    have hprod : t * dirNormSq a b = 0 := by
      nlinarith
    have ht0 : t = 0 := (mul_eq_zero.mp hprod).resolve_right (dirNormSq_pos hab).ne'
    apply hx
    simpa [ht0] using hzab
  · have hsd : side a b (detourSide a b x) = side a b x := by
      simp [detourSide, offset, hxside]
    rw [side_lineMap, hsd] at hs
    apply hxside
    nlinarith

/-- The parallel middle leg has a fixed nonzero side coordinate. -/
lemma segment_detourFar_subset_compl {a b : Plane} (hab : a ≠ b) (x : Plane) :
    [detourSide a b x -[ℝ] detourFar a b x] ⊆ ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro z hz hzab
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  have hs := (segment_coordinates hab hzab).1
  rw [side_lineMap, side_detourFar hab] at hs
  exact side_detourSide_ne hab x (by nlinarith)

/-- The final leg returns to the supporting line beyond the target endpoint. -/
lemma segment_detourBase_subset_compl {a b : Plane} (hab : a ≠ b) (x : Plane) :
    [detourFar a b x -[ℝ] detourBase a b x] ⊆ ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro z hz hzab
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  have hp := (segment_coordinates hab hzab).2.2
  rw [progress_lineMap, progress_detourFar hab, progress_detourBase hab] at hp
  have h := detourParam_gt_one a b x
  nlinarith

lemma detourBase_mem_compl {a b : Plane} (hab : a ≠ b) (x : Plane) :
    detourBase a b x ∈ ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro hzab
  have hp := (segment_coordinates hab hzab).2.2
  rw [progress_detourBase hab] at hp
  linarith [detourParam_gt_one a b x]

/-- The explicit three-leg detour avoids the original segment throughout. -/
theorem joinedIn_detour {a b : Plane} (hab : a ≠ b) {x : Plane}
    (hx : x ∈ ([a -[ℝ] b] : Set Plane)ᶜ) :
    JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ x (detourBase a b x) := by
  have h1 : JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ x (detourSide a b x) :=
    JoinedIn.of_segment_subset (segment_detourSide_subset_compl hab hx)
  have h2 : JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ
      (detourSide a b x) (detourFar a b x) :=
    JoinedIn.of_segment_subset (segment_detourFar_subset_compl hab x)
  have h3 : JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ
      (detourFar a b x) (detourBase a b x) :=
    JoinedIn.of_segment_subset (segment_detourBase_subset_compl hab x)
  exact h1.trans (h2.trans h3)

/-- **A straight segment never disconnects the plane.** The path-connectedness
witness and all three path legs are explicit in the preceding definitions. -/
theorem isPathConnected_compl_segment {a b : Plane} (hab : a ≠ b) :
    IsPathConnected ([a -[ℝ] b] : Set Plane)ᶜ := by
  refine ⟨detourBase a b a, detourBase_mem_compl hab a, fun y hy => ?_⟩
  simpa only [detourBase, detourParam] using (joinedIn_detour hab hy).symm

/-- Consequently the complement has exactly one connected-component face. -/
theorem subsingleton_connectedComponents_compl_segment {a b : Plane} (hab : a ≠ b) :
    Subsingleton (ConnectedComponents {z // z ∈ ([a -[ℝ] b] : Set Plane)ᶜ}) := by
  letI : PathConnectedSpace {z // z ∈ ([a -[ℝ] b] : Set Plane)ᶜ} :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_segment hab)
  infer_instance

/-- In particular, the complementary face type is nonempty. -/
theorem nonempty_connectedComponents_compl_segment {a b : Plane} (hab : a ≠ b) :
    Nonempty (ConnectedComponents {z // z ∈ ([a -[ℝ] b] : Set Plane)ᶜ}) := by
  letI : PathConnectedSpace {z // z ∈ ([a -[ℝ] b] : Set Plane)ᶜ} :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_segment hab)
  infer_instance

end
end FK.PlaneTopology.Continuous.Segment
