import FK.ForestAttachment

/-!
# Scaled three-leg detours around a straight segment

This is the parameter-dependent form of `PolygonalSegment.joinedIn_detour`.
The final point can be arbitrarily close to the free endpoint, and the normal
step used for a point on the supporting line can be arbitrarily short.
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval
open FK.PlaneTopology.Continuous.Segment

/-- The normal displacement used only on the supporting line. -/
def scaledOffset (a b x : Plane) (r : ℝ) : ℝ := if side a b x = 0 then r else 0

/-- First detour vertex. -/
def scaledSide (a b x : Plane) (r : ℝ) : Plane :=
  x + scaledOffset a b x r • normal a b

/-- Point with parameter `q` on the supporting line. -/
def scaledBase (a b : Plane) (q : ℝ) : Plane := a + q • (b - a)

/-- Last off-line vertex, with the same side coordinate as `scaledSide`. -/
def scaledFar (a b : Plane) (q : ℝ) (x : Plane) (r : ℝ) : Plane :=
  scaledBase a b q + (side a b (scaledSide a b x r) / dirNormSq a b) • normal a b

lemma scaledOffset_eq_zero_of_side_ne {a b x : Plane} {r : ℝ}
    (hx : side a b x ≠ 0) : scaledOffset a b x r = 0 := by
  simp [scaledOffset, hx]

lemma scaledSide_eq_self_of_side_ne {a b x : Plane} {r : ℝ}
    (hx : side a b x ≠ 0) : scaledSide a b x r = x := by
  simp [scaledSide, scaledOffset_eq_zero_of_side_ne hx]

lemma scaledSide_eq_add_of_side_eq_zero {a b x : Plane} {r : ℝ}
    (hx : side a b x = 0) : scaledSide a b x r = x + r • normal a b := by
  simp [scaledSide, scaledOffset, hx]

lemma side_scaledSide (a b x : Plane) (r : ℝ) :
    side a b (scaledSide a b x r) = side a b x + scaledOffset a b x r * dirNormSq a b := by
  rw [scaledSide, side_add_normal]

lemma side_scaledSide_ne {a b : Plane} (hab : a ≠ b) (x : Plane) {r : ℝ}
    (hr : r ≠ 0) : side a b (scaledSide a b x r) ≠ 0 := by
  rw [side_scaledSide]
  by_cases hx : side a b x = 0
  · simp [scaledOffset, hx, hr, (dirNormSq_pos hab).ne']
  · simp [scaledOffset, hx]

lemma progress_scaledSide {a b : Plane} (hab : a ≠ b) (x : Plane) (r : ℝ) :
    progress a b (scaledSide a b x r) = progress a b x := by
  exact progress_add_normal hab _ _

@[simp] lemma side_scaledBase (a b : Plane) (q : ℝ) :
    side a b (scaledBase a b q) = 0 := by
  exact side_affine _ _ _

@[simp] lemma progress_scaledBase {a b : Plane} (hab : a ≠ b) (q : ℝ) :
    progress a b (scaledBase a b q) = q := by
  exact progress_affine hab _

lemma side_scaledFar {a b : Plane} (hab : a ≠ b) (q : ℝ) (x : Plane) (r : ℝ) :
    side a b (scaledFar a b q x r) = side a b (scaledSide a b x r) := by
  rw [scaledFar, side_add_normal, side_scaledBase]
  field_simp [(dirNormSq_pos hab).ne']
  simp

lemma progress_scaledFar {a b : Plane} (hab : a ≠ b) (q : ℝ) (x : Plane) (r : ℝ) :
    progress a b (scaledFar a b q x r) = q := by
  rw [scaledFar, progress_add_normal hab, progress_scaledBase hab]

lemma scaledFar_eq_add_of_side_eq_zero {a b : Plane} (hab : a ≠ b)
    {q r : ℝ} {x : Plane} (hx : side a b x = 0) :
    scaledFar a b q x r = scaledBase a b q + r • normal a b := by
  rw [scaledFar, scaledSide_eq_add_of_side_eq_zero hx, side_add_normal, hx]
  have hn := (dirNormSq_pos hab).ne'
  have heq : r * dirNormSq a b / dirNormSq a b = r := by
    field_simp [hn]
  simp only [zero_add]
  rw [heq]

lemma scaledFar_eq_offline {a b : Plane} (q : ℝ) (x : Plane) {r : ℝ}
    (hx : side a b x ≠ 0) :
    scaledFar a b q x r = scaledBase a b q +
      (side a b x / dirNormSq a b) • normal a b := by
  simp [scaledFar, scaledSide_eq_self_of_side_ne hx]

lemma scaledBase_mem_compl_segment {a b : Plane} (hab : a ≠ b) {q : ℝ}
    (hq : 1 < q) : scaledBase a b q ∈ ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro hz
  have hp := (segment_coordinates hab hz).2.2
  rw [progress_scaledBase hab] at hp
  linarith

/-- First leg of the scaled detour avoids the original segment. -/
lemma segment_scaledSide_subset_compl {a b : Plane} (hab : a ≠ b) {r : ℝ}
    (hr : r ≠ 0) {x : Plane} (hx : x ∈ ([a -[ℝ] b] : Set Plane)ᶜ) :
    [x -[ℝ] scaledSide a b x r] ⊆ ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro z hz hzab
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hs := (segment_coordinates hab hzab).1
  by_cases hxside : side a b x = 0
  · have hsd : side a b (scaledSide a b x r) = r * dirNormSq a b := by
      rw [scaledSide_eq_add_of_side_eq_zero hxside, side_add_normal, hxside, zero_add]
    rw [side_lineMap, hsd, hxside] at hs
    have hprod : t * (r * dirNormSq a b) = 0 := by nlinarith
    have ht0 : t = 0 := (mul_eq_zero.mp hprod).resolve_right
      (mul_ne_zero hr (dirNormSq_pos hab).ne')
    apply hx
    simpa [ht0] using hzab
  · have hsd : side a b (scaledSide a b x r) = side a b x := by
      rw [scaledSide_eq_self_of_side_ne hxside]
    rw [side_lineMap, hsd] at hs
    apply hxside
    nlinarith

/-- Parallel middle leg of the scaled detour avoids the original segment. -/
lemma segment_scaledFar_subset_compl {a b : Plane} (hab : a ≠ b) {r : ℝ}
    (hr : r ≠ 0) (q : ℝ) (x : Plane) :
    [scaledSide a b x r -[ℝ] scaledFar a b q x r] ⊆
      ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro z hz hzab
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  have hs := (segment_coordinates hab hzab).1
  rw [side_lineMap, side_scaledFar hab] at hs
  exact side_scaledSide_ne hab x hr (by nlinarith)

/-- Final leg of the scaled detour returns beyond the free endpoint. -/
lemma segment_scaledBase_subset_compl {a b : Plane} (hab : a ≠ b) {q : ℝ}
    (hq : 1 < q) (x : Plane) (r : ℝ) :
    [scaledFar a b q x r -[ℝ] scaledBase a b q] ⊆
      ([a -[ℝ] b] : Set Plane)ᶜ := by
  intro z hz hzab
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _ht, rfl⟩ := hz
  have hp := (segment_coordinates hab hzab).2.2
  rw [progress_lineMap, progress_scaledFar hab, progress_scaledBase hab] at hp
  nlinarith

/-- The explicit scaled three-leg detour avoids the original segment. -/
theorem joinedIn_scaledDetour {a b : Plane} (hab : a ≠ b) {r : ℝ}
    (hr : r ≠ 0) {q : ℝ} (hq : 1 < q) {x : Plane}
    (hx : x ∈ ([a -[ℝ] b] : Set Plane)ᶜ) :
    JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ x (scaledBase a b q) := by
  have h1 : JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ x (scaledSide a b x r) :=
    JoinedIn.of_segment_subset (segment_scaledSide_subset_compl hab hr hx)
  have h2 : JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ
      (scaledSide a b x r) (scaledFar a b q x r) :=
    JoinedIn.of_segment_subset (segment_scaledFar_subset_compl hab hr q x)
  have h3 : JoinedIn ([a -[ℝ] b] : Set Plane)ᶜ
      (scaledFar a b q x r) (scaledBase a b q) :=
    JoinedIn.of_segment_subset (segment_scaledBase_subset_compl hab hq x r)
  exact h1.trans (h2.trans h3)

end
end FK.PlaneTopology.Continuous.Forest
