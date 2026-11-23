import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Euclidean circle and open-annulus separation

No Jordan-curve hypothesis is used.  Radial preimages of path-connected sets
in the positive reals are proved path-connected by the polar parametrization.
The intermediate value theorem gives exact inside/outside path components of
the complement of a metric circle in a real normed space of dimension at
least two.  Isolated vertices, loops, and graph labels play no role here.
-/

namespace FK.PlaneTopology

open Set Metric unitInterval
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The positive-radial part of space is the continuous image of the product
    of radii and the unit sphere. -/
lemma preimage_dist_eq_polar_image (c : E) (s : Set ℝ)
    (hs : ∀ ρ ∈ s, 0 < ρ) :
    (fun x : E => dist x c) ⁻¹' s =
      (fun p : ℝ × E => c + p.1 • p.2) '' (s ×ˢ sphere (0 : E) 1) := by
  ext x
  constructor
  · intro hx
    let ρ : ℝ := dist x c
    have hρ : 0 < ρ := hs ρ hx
    refine ⟨(ρ, ρ⁻¹ • (x - c)), ⟨hx, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hρ]
      simpa [ρ, dist_eq_norm] using (inv_mul_cancel₀ hρ.ne')
    · simp only [smul_smul]
      rw [mul_inv_cancel₀ hρ.ne']
      simp
  · rintro ⟨⟨ρ, v⟩, ⟨hρs, hv⟩, rfl⟩
    have hρ : 0 < ρ := hs ρ hρs
    rw [mem_sphere_zero_iff_norm] at hv
    have hdist : dist (c + ρ • v) c = ρ := by
      simp [dist_eq_norm, norm_smul, abs_of_pos hρ, hv]
    change dist (c + ρ • v) c ∈ s
    rwa [hdist]

/-- Every path-connected set of positive radii has a path-connected radial
    preimage.  This gives annuli, exteriors, and punctured spaces uniformly. -/
theorem isPathConnected_preimage_dist (hrank : 1 < Module.rank ℝ E)
    (c : E) {s : Set ℝ} (hpath : IsPathConnected s) (hs : ∀ ρ ∈ s, 0 < ρ) :
    IsPathConnected ((fun x : E => dist x c) ⁻¹' s) := by
  rw [preimage_dist_eq_polar_image c s hs]
  exact (hpath.prod (isPathConnected_sphere hrank (0 : E) zero_le_one)).image
    (by fun_prop)

/-- An open metric annulus is path-connected in dimension at least two. -/
theorem isPathConnected_openAnnulus (hrank : 1 < Module.rank ℝ E)
    (c : E) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsPathConnected {x : E | r < dist x c ∧ dist x c < R} := by
  have hp : IsPathConnected (Ioo r R) :=
    (convex_Ioo r R).isPathConnected (nonempty_Ioo.mpr hrR)
  exact isPathConnected_preimage_dist hrank c hp (fun _ h => hr.trans_lt h.1)

/-- The exterior of a closed metric ball is path-connected in dimension at
    least two.  The radius is only required to be nonnegative. -/
theorem isPathConnected_outsideClosedBall (hrank : 1 < Module.rank ℝ E)
    (c : E) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected ((fun x : E => dist x c) ⁻¹' Ioi r) := by
  have hp : IsPathConnected (Ioi r) := (convex_Ioi r).isPathConnected nonempty_Ioi
  exact isPathConnected_preimage_dist hrank c hp (fun _ h => hr.trans_lt h)

/-- The complement of a metric sphere is exactly the union of its open inside
    and its open outside. -/
theorem compl_sphere_eq_ball_union_outside (c : E) (r : ℝ) :
    (sphere c r)ᶜ = ball c r ∪ ((fun x : E => dist x c) ⁻¹' Ioi r) := by
  ext x
  simpa only [mem_compl_iff, mem_sphere, mem_ball, mem_union, mem_preimage,
    mem_Ioi] using (ne_iff_lt_or_gt : dist x c ≠ r ↔ dist x c < r ∨ r < dist x c)

/-- Intermediate value is exactly the circle-separation argument: a path from
    the inside to the outside has a point at distance `r` from the centre. -/
theorem not_joinedIn_compl_sphere_of_inside_outside {c x y : E} {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    ¬ JoinedIn (sphere c r)ᶜ x y := by
  intro hxy
  let γ : Path x y := hxy.somePath
  let f : I → ℝ := fun t => dist (γ t) c
  have hf : Continuous f := by
    exact γ.continuous.dist continuous_const
  have h0 : f 0 = dist x c := by simp [f, γ]
  have h1 : f 1 = dist y c := by simp [f, γ]
  have hrmem : r ∈ Icc (f 0) (f 1) := by
    constructor
    · rw [h0]
      exact hx.le
    · rw [h1]
      exact hy.le
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) (1 : I) hf hrmem
  apply hxy.somePath_mem t
  change dist (γ t) c = r
  change f t = r at ht
  exact ht

/-- The inside of a circle is exactly the path component of every one of its
    points in the complement of the circle. -/
theorem pathComponentIn_compl_sphere_of_inside (c : E) {r : ℝ} (hr : 0 < r)
    {x : E} (hx : x ∈ ball c r) :
    pathComponentIn (sphere c r)ᶜ x = ball c r := by
  ext y
  constructor
  · intro hxy
    have hycompl : y ∈ (sphere c r)ᶜ := hxy.target_mem
    rw [compl_sphere_eq_ball_union_outside] at hycompl
    rcases hycompl with hy | hy
    · exact hy
    · exact (not_joinedIn_compl_sphere_of_inside_outside hx hy hxy).elim
  · intro hy
    change JoinedIn (sphere c r)ᶜ x y
    apply ((isPathConnected_ball hr).joinedIn x hx y hy).mono
    rw [compl_sphere_eq_ball_union_outside]
    exact subset_union_left

/-- The outside of a circle is exactly the path component of every one of its
    points in the complement of the circle. -/
theorem pathComponentIn_compl_sphere_of_outside (hrank : 1 < Module.rank ℝ E)
    (c : E) {r : ℝ} (hr : 0 < r) {x : E}
    (hx : x ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    pathComponentIn (sphere c r)ᶜ x = (fun z : E => dist z c) ⁻¹' Ioi r := by
  ext y
  constructor
  · intro hxy
    have hycompl : y ∈ (sphere c r)ᶜ := hxy.target_mem
    rw [compl_sphere_eq_ball_union_outside] at hycompl
    rcases hycompl with hy | hy
    · exact (not_joinedIn_compl_sphere_of_inside_outside hy hx hxy.symm).elim
    · exact hy
  · intro hy
    change JoinedIn (sphere c r)ᶜ x y
    apply ((isPathConnected_outsideClosedBall hrank c hr.le).joinedIn x hx y hy).mono
    rw [compl_sphere_eq_ball_union_outside]
    exact subset_union_right

/-- The explicit radial arc from `c` to `y`. -/
def radialArc (c y : E) (t : ℝ) : E := c + t • (y - c)

@[simp] lemma radialArc_zero (c y : E) : radialArc c y 0 = c := by
  simp [radialArc]

@[simp] lemma radialArc_one (c y : E) : radialArc c y 1 = y := by
  simp [radialArc]

lemma continuous_radialArc (c y : E) : Continuous (radialArc c y) := by
  unfold radialArc
  fun_prop

lemma dist_radialArc (c y : E) (t : ℝ) :
    dist (radialArc c y t) c = |t| * dist y c := by
  simp [radialArc, dist_eq_norm, norm_smul, mul_comm]

/-- A radial dual arc from the centre to an exterior point crosses its circle
    at exactly one parameter, explicitly `r / dist y c`. -/
theorem radialArc_existsUnique_crossing {c y : E} {r : ℝ} (hr : 0 < r)
    (hy : r < dist y c) :
    ∃! t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ radialArc c y t ∈ sphere c r := by
  have hd : 0 < dist y c := hr.trans hy
  let t₀ : ℝ := r / dist y c
  have ht₀ : 0 < t₀ := div_pos hr hd
  have ht₀1 : t₀ < 1 := (div_lt_one hd).mpr hy
  refine ⟨t₀, ⟨⟨ht₀.le, ht₀1.le⟩, ?_⟩, ?_⟩
  · change dist (radialArc c y t₀) c = r
    rw [dist_radialArc, abs_of_pos ht₀]
    dsimp [t₀]
    exact div_mul_cancel₀ r hd.ne'
  · intro t ht
    have ht0 : 0 ≤ t := ht.1.1
    have hdist : dist (radialArc c y t) c = r := ht.2
    rw [dist_radialArc, abs_of_nonneg ht0] at hdist
    exact (eq_div_iff hd.ne').2 hdist

/-- The transverse parameters of the radial arc and circle form exactly a
    singleton, so their crossing number is one (in particular odd). -/
theorem radialArc_crossing_parameters {c y : E} {r : ℝ} (hr : 0 < r)
    (hy : r < dist y c) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ radialArc c y t ∈ sphere c r} =
      {r / dist y c} := by
  have hd : 0 < dist y c := hr.trans hy
  let t₀ : ℝ := r / dist y c
  have ht₀ : 0 < t₀ := div_pos hr hd
  have ht₀1 : t₀ < 1 := (div_lt_one hd).mpr hy
  have ht₀cross : t₀ ∈ Icc (0 : ℝ) 1 ∧ radialArc c y t₀ ∈ sphere c r := by
    refine ⟨⟨ht₀.le, ht₀1.le⟩, ?_⟩
    change dist (radialArc c y t₀) c = r
    rw [dist_radialArc, abs_of_pos ht₀]
    dsimp [t₀]
    exact div_mul_cancel₀ r hd.ne'
  have hu := radialArc_existsUnique_crossing hr hy
  have heq : hu.choose = t₀ := (hu.choose_spec.2 t₀ ht₀cross).symm
  ext t
  change (t ∈ {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ radialArc c y t ∈ sphere c r} ↔
    t ∈ ({t₀} : Set ℝ))
  rw [← heq]
  simp only [mem_setOf_eq, mem_singleton_iff]
  exact ⟨hu.choose_spec.2 t, fun ht => ht ▸ hu.choose_spec.1⟩

theorem radialArc_crossing_card (c y : E) {r : ℝ} (hr : 0 < r)
    (hy : r < dist y c) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ radialArc c y t ∈ sphere c r}.ncard = 1 := by
  rw [radialArc_crossing_parameters hr hy]
  exact Set.ncard_singleton _

end FK.PlaneTopology
