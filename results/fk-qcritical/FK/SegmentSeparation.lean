import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Straight dual arcs crossing a metric circle

This file strengthens the radial-arc calculation in the inherited
`CircleSeparation.lean`.  A straight arc may start at any point of the open
ball, not just at its centre.  It crosses the sphere exactly once on its way
to any exterior point.  Before that parameter the arc is strictly inside;
after it, and until the exterior endpoint, it is strictly outside.

The proof uses only convexity of distance and the intermediate value theorem.
No Jordan-curve, rotation-system, or matroid-duality hypothesis occurs.
-/

namespace FK.PlaneTopology

open Set Metric unitInterval
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard straight arc, with parameter in the real affine line. -/
def segmentArc (x y : E) : ℝ → E := AffineMap.lineMap x y

@[simp] lemma segmentArc_zero (x y : E) : segmentArc x y 0 = x := by
  simp [segmentArc]

@[simp] lemma segmentArc_one (x y : E) : segmentArc x y 1 = y := by
  simp [segmentArc]

lemma segmentArc_apply (x y : E) (t : ℝ) :
    segmentArc x y t = x + t • (y - x) := by
  rw [segmentArc, AffineMap.lineMap_apply_module']
  abel

lemma continuous_segmentArc (x y : E) : Continuous (segmentArc x y) := by
  exact AffineMap.lineMap_continuous

/-- A nontrivial convex combination of an interior point and a point of the
closed ball is still in the open ball, provided the interior point has
positive weight. -/
lemma dist_lineMap_lt_of_inside_of_mem_closedBall {c x z : E} {r t : ℝ}
    (hx : dist x c < r) (hz : z ∈ closedBall c r)
    (ht0 : 0 < t) (ht1 : t < 1) :
    dist (AffineMap.lineMap x z t) c < r := by
  have ht0' : 0 ≤ t := ht0.le
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
  have hconv :
      dist ((1 - t) • x + t • z) c ≤ (1 - t) * dist x c + t * dist z c := by
    simpa only [smul_eq_mul] using
      (convexOn_univ_dist c).2 (Set.mem_univ x) (Set.mem_univ z)
        h1t ht0' (by ring)
  rw [AffineMap.lineMap_apply_module]
  calc
    dist ((1 - t) • x + t • z) c ≤ (1 - t) * dist x c + t * dist z c := hconv
    _ < (1 - t) * r + t * r := by
      apply add_lt_add_of_lt_of_le
      · exact mul_lt_mul_of_pos_left hx (sub_pos.mpr ht1)
      · exact mul_le_mul_of_nonneg_left hz ht0'
    _ = r := by ring

/-- An earlier parameter on a segment from an interior point to a boundary
point is strictly inside.  There is no nondegeneracy or strict-convexity
assumption on the norm. -/
lemma dist_segmentArc_lt_of_inside_of_lt {c x y : E} {r s t : ℝ}
    (hx : x ∈ ball c r) (hs0 : 0 < s) (hst : s < t)
    (ht : segmentArc x y t ∈ sphere c r) :
    dist (segmentArc x y s) c < r := by
  have ht0 : 0 < t := hs0.trans hst
  have hst0 : 0 < s / t := div_pos hs0 ht0
  have hst1 : s / t < 1 := (div_lt_one ht0).mpr hst
  have hclosed : segmentArc x y t ∈ closedBall c r := mem_closedBall.mpr ht.le
  have hlt := dist_lineMap_lt_of_inside_of_mem_closedBall hx hclosed hst0 hst1
  change dist (AffineMap.lineMap x (AffineMap.lineMap x y t) (s / t)) c < r at hlt
  rw [AffineMap.lineMap_lineMap_right, div_mul_cancel₀ s ht0.ne'] at hlt
  exact hlt

/-- Existence and uniqueness of the crossing parameter for an arbitrary
straight inside-to-outside arc. -/
theorem segmentArc_existsUnique_crossing {c x y : E} {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    ∃! t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ segmentArc x y t ∈ sphere c r := by
  let f : ℝ → ℝ := fun t => dist (segmentArc x y t) c
  have hf : Continuous f := by
    exact (continuous_segmentArc x y).dist continuous_const
  have hrmem : r ∈ Icc (f 0) (f 1) := by
    constructor
    · simpa [f] using hx.le
    · simpa [f] using hy.le
  obtain ⟨t, htI, ht⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hrmem
  have htcross : segmentArc x y t ∈ sphere c r := ht
  refine ⟨t, ⟨htI, htcross⟩, ?_⟩
  intro s hs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hs0 : 0 < s := by
      rcases hs.1.1.eq_or_lt with hs0 | hs0
      · exfalso
        have : x ∈ sphere c r := by simpa [← hs0] using hs.2
        exact (ne_of_lt hx) this
      · exact hs0
    have hlt := dist_segmentArc_lt_of_inside_of_lt hx hs0 hst htcross
    exact (ne_of_lt hlt) hs.2
  · have ht0 : 0 < t := by
      rcases htI.1.eq_or_lt with ht0 | ht0
      · exfalso
        have : x ∈ sphere c r := by simpa [← ht0] using htcross
        exact (ne_of_lt hx) this
      · exact ht0
    have hlt := dist_segmentArc_lt_of_inside_of_lt hx ht0 hts hs.2
    exact (ne_of_lt hlt) htcross

/-- The crossing parameters form a singleton; unlike the radial special case,
the parameter need not have a closed radial formula. -/
theorem segmentArc_crossing_parameters {c x y : E} {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    ∃ t₀ : ℝ, {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ segmentArc x y t ∈ sphere c r} =
      {t₀} := by
  obtain ⟨t₀, ht₀, hu⟩ := segmentArc_existsUnique_crossing hx hy
  refine ⟨t₀, ?_⟩
  ext t
  simp only [Set.mem_ofPred_eq, mem_singleton_iff]
  exact ⟨hu t, fun h => h ▸ ht₀⟩

/-- Every straight dual arc from an arbitrary inside face representative to an
outside representative has geometric crossing number one with the circle. -/
theorem segmentArc_crossing_card (c x y : E) {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ segmentArc x y t ∈ sphere c r}.ncard = 1 := by
  obtain ⟨t₀, ht₀⟩ := segmentArc_crossing_parameters hx hy
  rw [ht₀]
  exact Set.ncard_singleton _

/-- The unique crossing is interior to the parameter interval. -/
theorem segmentArc_crossing_mem_Ioo {c x y : E} {r t : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r)
    (htI : t ∈ Icc (0 : ℝ) 1) (ht : segmentArc x y t ∈ sphere c r) :
    t ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · rcases htI.1.eq_or_lt with h0 | h0
    · have hxs : x ∈ sphere c r := by simpa [← h0] using ht
      exact ((ne_of_lt hx) hxs).elim
    · exact h0
  · rcases htI.2.eq_or_lt with h1 | h1
    · have hys : y ∈ sphere c r := by simpa [h1] using ht
      exact ((ne_of_gt hy) hys).elim
    · exact h1

/-- Before the unique crossing, every point of the arc is in the inside face. -/
theorem segmentArc_inside_before_crossing {c x y : E} {r s t : ℝ}
    (hx : x ∈ ball c r)
    (hsI : s ∈ Icc (0 : ℝ) 1) (hst : s < t)
    (ht : segmentArc x y t ∈ sphere c r) :
    segmentArc x y s ∈ ball c r := by
  by_cases hs0 : s = 0
  · simpa [hs0] using hx
  · exact dist_segmentArc_lt_of_inside_of_lt hx (lt_of_le_of_ne hsI.1 (Ne.symm hs0)) hst ht

/-- After a crossing, every point of the straight arc is outside the sphere.
In particular, the arc cannot re-enter the closed ball. -/
theorem segmentArc_outside_after_crossing {c x y : E} {r s t : ℝ}
    (hx : x ∈ ball c r) (ht0 : 0 < t) (hts : t < s)
    (ht : segmentArc x y t ∈ sphere c r) :
    segmentArc x y s ∈ (fun z : E => dist z c) ⁻¹' Ioi r := by
  change r < dist (segmentArc x y s) c
  by_contra hnot
  have hs : segmentArc x y s ∈ closedBall c r := mem_closedBall.mpr (not_lt.mp hnot)
  have hs0 : 0 < s := ht0.trans hts
  have hts0 : 0 < t / s := div_pos ht0 hs0
  have hts1 : t / s < 1 := (div_lt_one hs0).mpr hts
  have hlt := dist_lineMap_lt_of_inside_of_mem_closedBall hx hs hts0 hts1
  change dist (AffineMap.lineMap x (AffineMap.lineMap x y s) (t / s)) c < r at hlt
  rw [AffineMap.lineMap_lineMap_right, div_mul_cancel₀ t hs0.ne'] at hlt
  exact (ne_of_lt hlt) ht

/-- Exact three-part behaviour at the crossing supplied by
`segmentArc_existsUnique_crossing`: inside before, on the circle at the
crossing, and outside after. -/
theorem segmentArc_exists_crossing_faces {c x y : E} {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    ∃ t₀ ∈ Ioo (0 : ℝ) 1,
      segmentArc x y t₀ ∈ sphere c r ∧
      (∀ s ∈ Icc (0 : ℝ) 1, s < t₀ → segmentArc x y s ∈ ball c r) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, t₀ < s →
        segmentArc x y s ∈ (fun z : E => dist z c) ⁻¹' Ioi r) := by
  obtain ⟨t₀, ⟨htI, ht⟩, _⟩ := segmentArc_existsUnique_crossing hx hy
  have ht₀ : t₀ ∈ Ioo (0 : ℝ) 1 := segmentArc_crossing_mem_Ioo hx hy htI ht
  refine ⟨t₀, ht₀, ht, ?_, ?_⟩
  · intro s hsI hst
    exact segmentArc_inside_before_crossing hx hsI hst ht
  · intro s _hsI hts
    exact segmentArc_outside_after_crossing hx ht₀.1 hts ht

end FK.PlaneTopology
