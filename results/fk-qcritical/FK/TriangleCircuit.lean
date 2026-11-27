import FK.OneSegmentWindow
import FK.SeparatorCircuits
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Jordan separation for a nondegenerate triangular polygonal circuit

This file treats an arbitrary affine basis with three vertices in the plane.
Its three straight sides are proved to be the frontier of its convex hull.
No general simple-polygon Jordan theorem is assumed or claimed.
-/

namespace FK.PlaneTopology.Continuous.Triangle

noncomputable section

open Set Metric
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology.Continuous
open FK.PlaneTopology.Continuous.OneSegment

/-- The nondegenerate triangle determined by an affine basis of `ℝ × ℝ`. -/
def simplex (b : AffineBasis (Fin 3) ℝ Plane) : Affine.Triangle ℝ Plane :=
  ⟨b, b.ind⟩

/-- The solid triangle, with no topological face assumption built in. -/
def solid (b : AffineBasis (Fin 3) ℝ Plane) : Set Plane :=
  convexHull ℝ (Set.range b)

/-- The three closed sides of the triangle. -/
def boundary (b : AffineBasis (Fin 3) ℝ Plane) : Set Plane :=
  [b 0 -[ℝ] b 1] ∪ [b 1 -[ℝ] b 2] ∪ [b 2 -[ℝ] b 0]

/-- The bounded complementary region. -/
def inside (b : AffineBasis (Fin 3) ℝ Plane) : Set Plane := interior (solid b)

/-- The complementary region outside the closed solid triangle. -/
def outside (b : AffineBasis (Fin 3) ℝ Plane) : Set Plane := (closure (solid b))ᶜ

lemma convex_solid (b : AffineBasis (Fin 3) ℝ Plane) : Convex ℝ (solid b) :=
  convex_convexHull _ _

lemma isCompact_solid (b : AffineBasis (Fin 3) ℝ Plane) : IsCompact (solid b) := by
  exact (Set.finite_range b).isCompact_convexHull ℝ

lemma isClosed_solid (b : AffineBasis (Fin 3) ℝ Plane) : IsClosed (solid b) :=
  (isCompact_solid b).isClosed

lemma closure_solid (b : AffineBasis (Fin 3) ℝ Plane) : closure (solid b) = solid b :=
  (isClosed_solid b).closure_eq

/-- The barycentric characterization of the topological interior. -/
lemma mem_inside_iff (b : AffineBasis (Fin 3) ℝ Plane) (x : Plane) :
    x ∈ inside b ↔ ∀ i, 0 < b.coord i x := by
  change x ∈ interior (convexHull ℝ (Set.range b)) ↔ _
  rw [AffineBasis.interior_convexHull]
  rfl

/-- The simplex interior coincides with the actual topological interior. -/
lemma simplexInterior_eq_inside (b : AffineBasis (Fin 3) ℝ Plane) :
    (simplex b).interior = inside b := by
  ext x
  constructor
  · rintro ⟨w, hw, hw01, rfl⟩
    rw [mem_inside_iff]
    intro i
    change 0 < b.coord i (Finset.univ.affineCombination ℝ b w)
    rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) hw]
    exact (hw01 i).1
  · intro hx
    refine ⟨fun i => b.coord i x, b.sum_coord_apply_eq_one x, ?_, ?_⟩
    · intro i
      have hsum := b.sum_coord_apply_eq_one x
      have hpos := (mem_inside_iff b x).1 hx
      have hnonneg (j : Fin 3) : 0 ≤ b.coord j x := (hpos j).le
      constructor
      · exact hpos i
      · have hle : b.coord i x ≤ 1 := by
          rw [← hsum]
          exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
        rcases hle.eq_or_lt with heq | hlt
        · exfalso
          have hothers : ∀ j ∈ Finset.univ.erase i, b.coord j x = 0 := by
            have hsplit : (∑ j ∈ Finset.univ.erase i, b.coord j x) + b.coord i x =
                ∑ j, b.coord j x :=
              Finset.sum_erase_add _ _ (Finset.mem_univ i)
            have hz : ∑ j ∈ Finset.univ.erase i, b.coord j x = 0 := by
              rw [hsum, heq] at hsplit
              linarith
            exact (Finset.sum_eq_zero_iff_of_nonneg
              (fun j hj => hnonneg j)).1 hz
          have hzero : b.coord (i + 1) x = 0 := by
            apply hothers
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            fin_cases i <;> decide
          linarith [hpos (i + 1)]
        · exact hlt
    · exact b.affineCombination_coord_eq_self x

/-- Each opposite simplex face is exactly the corresponding straight side. -/
lemma faceOpposite_zero (b : AffineBasis (Fin 3) ℝ Plane) :
    ((simplex b).faceOpposite 0).closedInterior = [b 1 -[ℝ] b 2] := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior,
    Affine.Simplex.range_faceOpposite_points]
  change convexHull ℝ (b '' ({0}ᶜ : Set (Fin 3))) = _
  have hset : b '' ({0}ᶜ : Set (Fin 3)) = {b 1, b 2} := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨1, by simp, rfl⟩
      · subst x
        exact ⟨2, by simp, rfl⟩
  rw [hset, convexHull_pair]

lemma faceOpposite_one (b : AffineBasis (Fin 3) ℝ Plane) :
    ((simplex b).faceOpposite 1).closedInterior = [b 0 -[ℝ] b 2] := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior,
    Affine.Simplex.range_faceOpposite_points]
  change convexHull ℝ (b '' ({1}ᶜ : Set (Fin 3))) = _
  have hset : b '' ({1}ᶜ : Set (Fin 3)) = {b 0, b 2} := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨0, by simp, rfl⟩
      · subst x
        exact ⟨2, by simp, rfl⟩
  rw [hset, convexHull_pair]

lemma faceOpposite_two (b : AffineBasis (Fin 3) ℝ Plane) :
    ((simplex b).faceOpposite 2).closedInterior = [b 0 -[ℝ] b 1] := by
  rw [← Affine.Simplex.convexHull_eq_closedInterior,
    Affine.Simplex.range_faceOpposite_points]
  change convexHull ℝ (b '' ({2}ᶜ : Set (Fin 3))) = _
  have hset : b '' ({2}ᶜ : Set (Fin 3)) = {b 0, b 1} := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨0, by simp, rfl⟩
      · subst x
        exact ⟨1, by simp, rfl⟩
  rw [hset, convexHull_pair]

/-- The solid triangle is closed and its simplex surface is its exact frontier. -/
lemma frontier_solid (b : AffineBasis (Fin 3) ℝ Plane) :
    frontier (solid b) = boundary b := by
  rw [frontier, closure_solid]
  change solid b \ inside b = boundary b
  rw [← simplexInterior_eq_inside]
  change convexHull ℝ (Set.range (simplex b).points) \ (simplex b).interior = boundary b
  rw [Affine.Simplex.convexHull_eq_closedInterior]
  change (simplex b).closedInterior \ (simplex b).interior = boundary b
  rw [(simplex b).closedInterior_sdiff_interior]
  have hu : (⋃ i : Fin 3, ((simplex b).faceOpposite i).closedInterior) =
      ((simplex b).faceOpposite 0).closedInterior ∪
        ((simplex b).faceOpposite 1).closedInterior ∪
          ((simplex b).faceOpposite 2).closedInterior := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · intro hx
      rcases hx with (h0 | h1) | h2
      · exact Set.mem_iUnion.mpr ⟨0, h0⟩
      · exact Set.mem_iUnion.mpr ⟨1, h1⟩
      · exact Set.mem_iUnion.mpr ⟨2, h2⟩
  rw [hu, faceOpposite_zero, faceOpposite_one, faceOpposite_two]
  change [b 1 -[ℝ] b 2] ∪ [b 0 -[ℝ] b 2] ∪ [b 0 -[ℝ] b 1] = _
  rw [segment_symm ℝ (b 0) (b 2)]
  unfold boundary
  ac_rfl

/-- The complement of the three sides is precisely the inside/outside union. -/
lemma compl_boundary (b : AffineBasis (Fin 3) ℝ Plane) :
    (boundary b)ᶜ = inside b ∪ outside b := by
  rw [← frontier_solid]
  exact FK.PlaneTopology.compl_frontier_eq_interior_union_compl_closure (solid b)

/-- A path from a topological interior to the exterior of the closure meets
its frontier.  This general connectedness fact uses no convexity assumption. -/
lemma not_joinedIn_compl_frontier {X : Type*} [TopologicalSpace X] {s : Set X}
    {x y : X} (hx : x ∈ interior s) (hy : y ∈ (closure s)ᶜ) :
    ¬ JoinedIn (frontier s)ᶜ x y := by
  rintro ⟨γ, hγ⟩
  let F : Set X := Set.range γ
  have hFconn : IsPreconnected F := isPreconnected_range γ.continuous
  have hFsub : F ⊆ interior s ∪ (closure s)ᶜ := by
    rintro z ⟨t, rfl⟩
    exact (Set.ext_iff.1
      (FK.PlaneTopology.compl_frontier_eq_interior_union_compl_closure s) (γ t)).1 (hγ t)
  have hdisj : Disjoint (interior s) (closure s)ᶜ := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz' (interior_subset_closure hz)
  rcases hFconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
      hdisj hFsub with hin | hout
  · have hyin : y ∈ interior s := hin ⟨1, by simp⟩
    exact hy (interior_subset_closure hyin)
  · have hxout : x ∈ (closure s)ᶜ := hout ⟨0, by simp⟩
    exact hxout (interior_subset_closure hx)

/-- Inside and outside cannot be joined by a path avoiding the three sides. -/
lemma not_joinedIn_inside_outside {b : AffineBasis (Fin 3) ℝ Plane} {x y : Plane}
    (hx : x ∈ inside b) (hy : y ∈ outside b) :
    ¬ JoinedIn (boundary b)ᶜ x y := by
  rw [← frontier_solid]
  exact not_joinedIn_compl_frontier hx hy

/-- Points on a ray starting at a convex set and continuing beyond an exterior
point stay outside the set. -/
lemma notMem_of_one_le_lineMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {o x : E} {c : ℝ} (hconv : Convex ℝ s) (ho : o ∈ s)
    (hx : x ∉ s) (hc : 1 ≤ c) : AffineMap.lineMap o x c ∉ s := by
  intro hy
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hxseg : x ∈ [o -[ℝ] AffineMap.lineMap o x c] := by
    rw [segment_eq_image_lineMap]
    refine ⟨c⁻¹, ⟨inv_nonneg.mpr hc0.le, inv_le_one_of_one_le₀ hc⟩, ?_⟩
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hc0.ne',
      AffineMap.lineMap_apply_one]
  exact hx (hconv.segment_subset ho hy hxseg)

/-- Normalize an exterior point radially onto a sphere around `o`. -/
def radialProject {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (o : E) (R : ℝ) (x : E) : E := o + (R * ‖x - o‖⁻¹) • (x - o)

lemma radialProject_eq_lineMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (o : E) (R : ℝ) (x : E) :
    radialProject o R x = AffineMap.lineMap o x (R * ‖x - o‖⁻¹) := by
  simp only [radialProject, AffineMap.lineMap_apply_module']
  abel

lemma radialProject_mem_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {o x : E} {R : ℝ} (hR : 0 ≤ R) (hxo : x ≠ o) :
    radialProject o R x ∈ sphere o R := by
  have hnorm : ‖x - o‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxo)
  simp [radialProject, mem_sphere_iff_norm, norm_smul, abs_of_nonneg hR,
    mul_assoc, inv_mul_cancel₀ hnorm]

/-- The entire radial segment remains exterior when the target sphere is at
least as far from `o` as the starting point. -/
lemma segment_radialProject_subset_compl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {o x : E} {R : ℝ} (hconv : Convex ℝ s) (ho : o ∈ s)
    (hx : x ∉ s) (hR : ‖x - o‖ ≤ R) :
    [x -[ℝ] radialProject o R x] ⊆ sᶜ := by
  have hxo : x ≠ o := by
    intro h
    subst x
    exact hx ho
  have hnorm : 0 < ‖x - o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxo)
  have hc : 1 ≤ R * ‖x - o‖⁻¹ := by
    apply (le_mul_inv_iff₀ hnorm).2
    simpa using hR
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let c : ℝ := (1 - (t : ℝ)) + (t : ℝ) * (R * ‖x - o‖⁻¹)
  have hline : AffineMap.lineMap x (radialProject o R x) (t : ℝ) =
      AffineMap.lineMap o x c := by
    simp only [radialProject, AffineMap.lineMap_apply_module', c]
    module
  rw [hline]
  apply notMem_of_one_le_lineMap hconv ho hx
  dsimp only [c]
  nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hc)]

/-- In rank greater than one, the exterior of a bounded convex set is path
connected.  Each pair of points is joined through a sufficiently distant
sphere, with the radius chosen after the two points. -/
lemma isPathConnected_compl_closure_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {o : E} (hconv : Convex ℝ s) (ho : o ∈ s)
    (hb : Bornology.IsBounded s) (hrank : 1 < Module.rank ℝ E) :
    IsPathConnected (closure s)ᶜ := by
  let _ : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  obtain ⟨R, hRball⟩ := hb.closure.subset_ball o
  have hRpos : 0 < R := by
    have h := hRball (subset_closure ho)
    simpa [Metric.mem_ball] using h
  rw [isPathConnected_iff]
  constructor
  · by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    have hs : closure s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      have hx' : x ∈ (closure s)ᶜ := hx
      rw [hn] at hx'
      exact hx'
    exact NormedSpace.unbounded_univ ℝ E (hs ▸ hb.closure)
  · intro x hx y hy
    let S : ℝ := max R (max ‖x - o‖ ‖y - o‖) + 1
    have hRS : R < S := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    have hxS : ‖x - o‖ < S :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (lt_add_one _)
    have hyS : ‖y - o‖ < S :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) (lt_add_one _)
    have hS0 : 0 ≤ S := (hRpos.trans hRS).le
    have hxo : x ≠ o := by
      intro h
      subst x
      exact hx (subset_closure ho)
    have hyo : y ≠ o := by
      intro h
      subst y
      exact hy (subset_closure ho)
    have hradx : [x -[ℝ] radialProject o S x] ⊆ (closure s)ᶜ :=
      segment_radialProject_subset_compl hconv.closure (subset_closure ho) hx hxS.le
    have hrady : [y -[ℝ] radialProject o S y] ⊆ (closure s)ᶜ :=
      segment_radialProject_subset_compl hconv.closure (subset_closure ho) hy hyS.le
    have hsphere : sphere o S ⊆ (closure s)ᶜ := by
      intro z hz hzc
      have hzb := hRball hzc
      rw [mem_sphere] at hz
      rw [Metric.mem_ball] at hzb
      linarith
    have hjoinx : JoinedIn (closure s)ᶜ x (radialProject o S x) :=
      JoinedIn.of_segment_subset hradx
    have hjoiny : JoinedIn (closure s)ᶜ y (radialProject o S y) :=
      JoinedIn.of_segment_subset hrady
    have hmid : JoinedIn (closure s)ᶜ (radialProject o S x) (radialProject o S y) :=
      ((isPathConnected_sphere hrank o hS0).joinedIn
        (radialProject o S x) (radialProject_mem_sphere hS0 hxo)
        (radialProject o S y) (radialProject_mem_sphere hS0 hyo)).mono hsphere
    exact hjoinx.trans (hmid.trans hjoiny.symm)

/-- The exterior of a bounded set in a nontrivial real normed space is
unbounded. -/
lemma not_isBounded_compl_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {s : Set E} (hb : Bornology.IsBounded s) :
    ¬ Bornology.IsBounded (closure s)ᶜ := by
  intro hc
  have hu : Bornology.IsBounded (closure s ∪ (closure s)ᶜ) := hb.closure.union hc
  rw [Set.union_compl_self] at hu
  exact NormedSpace.unbounded_univ ℝ E hu

lemma rank_plane : 1 < Module.rank ℝ Plane := by
  apply Module.one_lt_rank_of_one_lt_finrank
  simp [Module.finrank_prod]

/-- The inside of the triangle is path connected. -/
lemma isPathConnected_inside (b : AffineBasis (Fin 3) ℝ Plane) :
    IsPathConnected (inside b) := by
  apply (convex_solid b).interior.isPathConnected
  exact ⟨Finset.univ.centroid ℝ b, b.centroid_mem_interior_convexHull⟩

/-- The unbounded outside of the triangle is path connected, by explicit
radial paths and paths on a distant sphere. -/
lemma isPathConnected_outside (b : AffineBasis (Fin 3) ℝ Plane) :
    IsPathConnected (outside b) := by
  exact isPathConnected_compl_closure_of_bounded (convex_solid b)
    (interior_subset b.centroid_mem_interior_convexHull)
    (isCompact_solid b).isBounded rank_plane

/-- The inside is bounded. -/
lemma isBounded_inside (b : AffineBasis (Fin 3) ℝ Plane) :
    Bornology.IsBounded (inside b) :=
  (isCompact_solid b).isBounded.subset interior_subset

/-- The outside is unbounded. -/
lemma not_isBounded_outside (b : AffineBasis (Fin 3) ℝ Plane) :
    ¬ Bornology.IsBounded (outside b) := by
  exact not_isBounded_compl_closure (isCompact_solid b).isBounded

end
end FK.PlaneTopology.Continuous.Triangle
