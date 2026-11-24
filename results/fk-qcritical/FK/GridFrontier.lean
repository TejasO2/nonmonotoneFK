import FK.SeparatorCircuits
import FK.JordanUnicyclicEnclosure

/-!
# The square lattice: exact convex-frontier crossing control

This module supplies the plane-geometry step that `FK.SeparatorCircuits` leaves
explicit: an actual **grid-like graph** with a straight-segment realization, an
actual **convex frontier** (the `ℓ¹`/diamond sphere), and the **exact** set of
graph edges whose arcs meet that frontier.
-/

namespace FK.PlaneTopology.GridFrontier

open Set Metric unitInterval
open scoped Classical Topology Pointwise
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionGeometry
open FK.InfiniteVolume.ConventionTransport
open FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon (straightPath)

/-! ## The square lattice and its straight-line realization -/

/-- Vertices of the square lattice. -/
abbrev GridV := ℤ × ℤ

/-- The lattice vertex as an actual point of the plane. -/
def gridVertex : GridV → ℝ × ℝ := fun p => ((p.1 : ℝ), (p.2 : ℝ))

/-- Unit-step adjacency of the square lattice. -/
def gridAdj (p q : GridV) : Prop :=
  (p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)) ∨
    (p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1))

theorem gridAdj_symm {p q : GridV} (h : gridAdj p q) : gridAdj q p := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

theorem gridAdj_irrefl (p : GridV) : ¬ gridAdj p p := by
  rintro (⟨-, h | h⟩ | ⟨-, h | h⟩) <;> omega

/-- The square lattice as a simple graph. -/
def gridGraph : SimpleGraph GridV where
  Adj := gridAdj
  symm := ⟨fun a b h => gridAdj_symm (p := a) (q := b) h⟩
  loopless := ⟨gridAdj_irrefl⟩

theorem gridVertex_injective : Function.Injective gridVertex := by
  intro p q h
  have h1 : (p.1 : ℝ) = (q.1 : ℝ) := congrArg Prod.fst h
  have h2 : (p.2 : ℝ) = (q.2 : ℝ) := congrArg Prod.snd h
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- The straight-segment realization of the square lattice. -/
noncomputable def gridRealization : OpenPathRealization gridGraph gridVertex where
  arc {x y} _ := straightPath (gridVertex x) (gridVertex y)

/-! ## The diamond norm and the level function -/

/-- The `ℓ¹` ("diamond") norm of a point of the plane. -/
def l1 (z : ℝ × ℝ) : ℝ := |z.1| + |z.2|

/-- The integer diamond level of a lattice vertex. -/
def lvl (p : GridV) : ℕ := p.1.natAbs + p.2.natAbs

theorem continuous_l1 : Continuous l1 := by
  unfold l1
  fun_prop

theorem abs_int_cast (a : ℤ) : |((a : ℝ))| = ((a.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  push_cast
  norm_num

theorem lvl_cast (p : GridV) : l1 (gridVertex p) = ((lvl p : ℕ) : ℝ) := by
  simp only [l1, gridVertex, lvl, abs_int_cast, Nat.cast_add]

/-! ## Affineness of the diamond norm along unit steps -/

/-- The coordinates of a straight path in the plane. -/
theorem straightPath_apply (x y : ℝ × ℝ) (t : I) :
    straightPath x y t =
      (x.1 + (t : ℝ) * (y.1 - x.1), x.2 + (t : ℝ) * (y.2 - x.2)) := by
  have h : straightPath x y t = AffineMap.lineMap x y (t : ℝ) := by
    simp [straightPath, FK.PlaneTopology.segmentArc]
  rw [h, AffineMap.lineMap_apply_module]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem abs_int_add_I (m : ℤ) (t : I) :
    |(m : ℝ) + (t : ℝ)| =
      (1 - (t : ℝ)) * |(m : ℝ)| + (t : ℝ) * |(((m + 1 : ℤ)) : ℝ)| := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases le_or_gt 0 m with hm | hm
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm1 : (0 : ℝ) ≤ (((m + 1 : ℤ)) : ℝ) := by push_cast; linarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hm0, abs_of_nonneg hm1]
    push_cast
    ring
  · have hm0 : (m : ℝ) ≤ 0 := by exact_mod_cast hm.le
    have hmle : m ≤ -1 := by omega
    have hmr : (m : ℝ) ≤ -1 := by exact_mod_cast hmle
    have hm1 : (((m + 1 : ℤ)) : ℝ) ≤ 0 := by
      push_cast
      linarith
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hm0, abs_of_nonpos hm1]
    push_cast
    ring

theorem abs_int_sub_I (m : ℤ) (t : I) :
    |(m : ℝ) - (t : ℝ)| =
      (1 - (t : ℝ)) * |(m : ℝ)| + (t : ℝ) * |(((m - 1 : ℤ)) : ℝ)| := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases lt_or_ge 0 m with hm | hm
  · have hm1 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.le
    have hmge : (1 : ℤ) ≤ m := by omega
    have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge
    have hm0 : (0 : ℝ) ≤ (((m - 1 : ℤ)) : ℝ) := by
      push_cast
      linarith
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hm1, abs_of_nonneg hm0]
    push_cast
    ring
  · have hm0 : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    have hm1 : (((m - 1 : ℤ)) : ℝ) ≤ 0 := by push_cast; linarith
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hm0, abs_of_nonpos hm1]
    push_cast
    ring

theorem l1_step_fst_add (m n : ℤ) (t : I) :
    l1 (straightPath (gridVertex (m, n)) (gridVertex (m + 1, n)) t) =
      (1 - (t : ℝ)) * l1 (gridVertex (m, n)) +
        (t : ℝ) * l1 (gridVertex (m + 1, n)) := by
  have hfst : (straightPath (gridVertex (m, n)) (gridVertex (m + 1, n)) t).1 =
      (m : ℝ) + (t : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; push_cast; ring
  have hsnd : (straightPath (gridVertex (m, n)) (gridVertex (m + 1, n)) t).2 = (n : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; ring
  rw [show straightPath (gridVertex (m, n)) (gridVertex (m + 1, n)) t =
      ((m : ℝ) + (t : ℝ), (n : ℝ)) from Prod.ext hfst hsnd]
  simp only [l1, gridVertex, abs_int_add_I m t]
  push_cast
  ring

theorem l1_step_fst_sub (m n : ℤ) (t : I) :
    l1 (straightPath (gridVertex (m, n)) (gridVertex (m - 1, n)) t) =
      (1 - (t : ℝ)) * l1 (gridVertex (m, n)) +
        (t : ℝ) * l1 (gridVertex (m - 1, n)) := by
  have hfst : (straightPath (gridVertex (m, n)) (gridVertex (m - 1, n)) t).1 =
      (m : ℝ) - (t : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; push_cast; ring
  have hsnd : (straightPath (gridVertex (m, n)) (gridVertex (m - 1, n)) t).2 = (n : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; ring
  rw [show straightPath (gridVertex (m, n)) (gridVertex (m - 1, n)) t =
      ((m : ℝ) - (t : ℝ), (n : ℝ)) from Prod.ext hfst hsnd]
  simp only [l1, gridVertex, abs_int_sub_I m t]
  push_cast
  ring

theorem l1_step_snd_add (m n : ℤ) (t : I) :
    l1 (straightPath (gridVertex (m, n)) (gridVertex (m, n + 1)) t) =
      (1 - (t : ℝ)) * l1 (gridVertex (m, n)) +
        (t : ℝ) * l1 (gridVertex (m, n + 1)) := by
  have hfst : (straightPath (gridVertex (m, n)) (gridVertex (m, n + 1)) t).1 = (m : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; ring
  have hsnd : (straightPath (gridVertex (m, n)) (gridVertex (m, n + 1)) t).2 =
      (n : ℝ) + (t : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; push_cast; ring
  rw [show straightPath (gridVertex (m, n)) (gridVertex (m, n + 1)) t =
      ((m : ℝ), (n : ℝ) + (t : ℝ)) from Prod.ext hfst hsnd]
  simp only [l1, gridVertex, abs_int_add_I n t]
  push_cast
  ring

theorem l1_step_snd_sub (m n : ℤ) (t : I) :
    l1 (straightPath (gridVertex (m, n)) (gridVertex (m, n - 1)) t) =
      (1 - (t : ℝ)) * l1 (gridVertex (m, n)) +
        (t : ℝ) * l1 (gridVertex (m, n - 1)) := by
  have hfst : (straightPath (gridVertex (m, n)) (gridVertex (m, n - 1)) t).1 = (m : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; ring
  have hsnd : (straightPath (gridVertex (m, n)) (gridVertex (m, n - 1)) t).2 =
      (n : ℝ) - (t : ℝ) := by
    rw [straightPath_apply]; simp only [gridVertex]; push_cast; ring
  rw [show straightPath (gridVertex (m, n)) (gridVertex (m, n - 1)) t =
      ((m : ℝ), (n : ℝ) - (t : ℝ)) from Prod.ext hfst hsnd]
  simp only [l1, gridVertex, abs_int_sub_I n t]
  push_cast
  ring

/-- **Affineness along a lattice step.**  The diamond norm is affine on the
straight segment joining two adjacent lattice vertices. -/
theorem l1_affine_step {p q : GridV} (h : gridAdj p q) (t : I) :
    l1 (straightPath (gridVertex p) (gridVertex q) t) =
      (1 - (t : ℝ)) * l1 (gridVertex p) + (t : ℝ) * l1 (gridVertex q) := by
  rcases p with ⟨m, n⟩
  rcases q with ⟨m', n'⟩
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hm : m' = m := h1.symm
    have hn : n' = n - 1 := by omega
    rw [hm, hn]
    exact l1_step_snd_sub m n t
  · have hm : m' = m := h1.symm
    have hn : n' = n + 1 := by omega
    rw [hm, hn]
    exact l1_step_snd_add m n t
  · have hn : n' = n := h1.symm
    have hm : m' = m - 1 := by omega
    rw [hm, hn]
    exact l1_step_fst_sub m n t
  · have hn : n' = n := h1.symm
    have hm : m' = m + 1 := by omega
    rw [hm, hn]
    exact l1_step_fst_add m n t

/-! ## Levels of adjacent vertices -/

theorem int_abs_succ (a : ℤ) : |a + 1| = |a| + 1 ∨ |a| = |a + 1| + 1 := by
  rcases lt_or_ge a 0 with ha | ha
  · right
    rw [abs_of_nonpos (by omega : a + 1 ≤ 0), abs_of_nonpos (by omega : a ≤ 0)]
    omega
  · left
    rw [abs_of_nonneg (by omega : 0 ≤ a + 1), abs_of_nonneg ha]

theorem int_abs_pred (a : ℤ) : |a - 1| = |a| + 1 ∨ |a| = |a - 1| + 1 := by
  rcases lt_or_ge a 1 with ha | ha
  · left
    rw [abs_of_nonpos (by omega : a - 1 ≤ 0), abs_of_nonpos (by omega : a ≤ 0)]
    omega
  · right
    rw [abs_of_nonneg (by omega : 0 ≤ a - 1), abs_of_nonneg (by omega : 0 ≤ a)]
    omega

/-- Casting a real level equality back to integer levels. -/
theorem lvl_of_l1 {p q : GridV} (h : l1 (gridVertex q) = l1 (gridVertex p) + 1) :
    lvl q = lvl p + 1 := by
  have hcast : ((lvl q : ℕ) : ℝ) = ((lvl p : ℕ) : ℝ) + 1 := by
    rw [← lvl_cast q, ← lvl_cast p]
    exact h
  exact_mod_cast hcast

theorem lvl_of_l1' {p q : GridV} (h : l1 (gridVertex p) = l1 (gridVertex q) + 1) :
    lvl p = lvl q + 1 := by
  have hcast : ((lvl p : ℕ) : ℝ) = ((lvl q : ℕ) : ℝ) + 1 := by
    rw [← lvl_cast p, ← lvl_cast q]
    exact h
  exact_mod_cast hcast

theorem real_abs_succ (a : ℤ) :
    |(((a + 1 : ℤ)) : ℝ)| = |((a : ℤ) : ℝ)| + 1 ∨
      |((a : ℤ) : ℝ)| = |(((a + 1 : ℤ)) : ℝ)| + 1 := by
  rcases int_abs_succ a with h | h
  · left
    have h' : ((|a + 1| : ℤ) : ℝ) = ((|a| : ℤ) : ℝ) + 1 := by exact_mod_cast h
    rw [Int.cast_abs, Int.cast_abs] at h'
    push_cast at h' ⊢
    exact h'
  · right
    have h' : ((|a| : ℤ) : ℝ) = ((|a + 1| : ℤ) : ℝ) + 1 := by exact_mod_cast h
    rw [Int.cast_abs, Int.cast_abs] at h'
    push_cast at h' ⊢
    exact h'

theorem real_abs_pred (a : ℤ) :
    |(((a - 1 : ℤ)) : ℝ)| = |((a : ℤ) : ℝ)| + 1 ∨
      |((a : ℤ) : ℝ)| = |(((a - 1 : ℤ)) : ℝ)| + 1 := by
  rcases int_abs_pred a with h | h
  · left
    have h' : ((|a - 1| : ℤ) : ℝ) = ((|a| : ℤ) : ℝ) + 1 := by exact_mod_cast h
    rw [Int.cast_abs, Int.cast_abs] at h'
    push_cast at h' ⊢
    exact h'
  · right
    have h' : ((|a| : ℤ) : ℝ) = ((|a - 1| : ℤ) : ℝ) + 1 := by exact_mod_cast h
    rw [Int.cast_abs, Int.cast_abs] at h'
    push_cast at h' ⊢
    exact h'

/-- Adjacent lattice vertices have diamond levels differing by one. -/
theorem lvl_adj {p q : GridV} (h : gridAdj p q) :
    lvl q = lvl p + 1 ∨ lvl p = lvl q + 1 := by
  rcases p with ⟨m, n⟩
  rcases q with ⟨m', n'⟩
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hm' : m' = m := h1.symm
    have hn' : n' = n - 1 := by omega
    rw [hm', hn']
    rcases real_abs_pred n with hn | hn
    · left
      apply lvl_of_l1
      simp only [l1, gridVertex]
      rw [hn]
      ring
    · right
      apply lvl_of_l1'
      simp only [l1, gridVertex]
      rw [hn]
      ring
  · have hm' : m' = m := h1.symm
    have hn' : n' = n + 1 := by omega
    rw [hm', hn']
    rcases real_abs_succ n with hn | hn
    · left
      apply lvl_of_l1
      simp only [l1, gridVertex]
      rw [hn]
      ring
    · right
      apply lvl_of_l1'
      simp only [l1, gridVertex]
      rw [hn]
      ring
  · have hn' : n' = n := h1.symm
    have hm' : m' = m - 1 := by omega
    rw [hm', hn']
    rcases real_abs_pred m with hm | hm
    · left
      apply lvl_of_l1
      simp only [l1, gridVertex]
      rw [hm]
      ring
    · right
      apply lvl_of_l1'
      simp only [l1, gridVertex]
      rw [hm]
      ring
  · have hn' : n' = n := h1.symm
    have hm' : m' = m + 1 := by omega
    rw [hm', hn']
    rcases real_abs_succ m with hm | hm
    · left
      apply lvl_of_l1
      simp only [l1, gridVertex]
      rw [hm]
      ring
    · right
      apply lvl_of_l1'
      simp only [l1, gridVertex]
      rw [hm]
      ring

/-! ## The diamond frontier as a two-sided separator -/

/-- The diamond sphere of half-integer radius `k + 1/2`. -/
def diamondBarrier (k : ℕ) : Set (ℝ × ℝ) := {z | l1 z = (k : ℝ) + 1 / 2}

/-- The open diamond of radius `k + 1/2`. -/
def diamondInside (k : ℕ) : Set (ℝ × ℝ) := {z | l1 z < (k : ℝ) + 1 / 2}

/-- The exterior of the diamond of radius `k + 1/2`. -/
def diamondOutside (k : ℕ) : Set (ℝ × ℝ) := {z | (k : ℝ) + 1 / 2 < l1 z}

/-- **The diamond frontier separates the plane**, purely by the intermediate value
theorem for the continuous diamond norm.  No Jordan curve theorem is used. -/
noncomputable def diamondSep (k : ℕ) : TwoSidedSeparation (ℝ × ℝ) where
  K := diamondBarrier k
  inside := diamondInside k
  outside := diamondOutside k
  cover := by
    intro z hz
    rcases lt_trichotomy (l1 z) ((k : ℝ) + 1 / 2) with h | h | h
    · exact Or.inl h
    · exact absurd h hz
    · exact Or.inr h
  separated := by
    intro x y hx hy
    exact not_joinedIn_compl_levelSet_of_lt continuous_l1 hx hy

/-- Every lattice vertex avoids every half-integral diamond sphere. -/
theorem gridVertex_off_diamond {k : ℕ} (p : GridV) :
    gridVertex p ∈ (diamondBarrier k)ᶜ := by
  intro hcontr
  simp only [diamondBarrier, Set.mem_ofPred_eq, lvl_cast] at hcontr
  have h2 : ((2 * lvl p : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h3 : 2 * lvl p = 2 * k + 1 := by exact_mod_cast h2
  omega

/-! ## The crossing-edge label set -/

/-- The edges whose arcs meet the diamond sphere of radius `k + 1/2`: exactly the
edges joining level `k` to level `k + 1`. -/
def diamondCut (k : ℕ) : Set gridGraph.edgeSet :=
  {e | ∃ (p q : GridV) (h : gridAdj p q), e = ⟨s(p, q), h⟩ ∧
    ((lvl p = k ∧ lvl q = k + 1) ∨ (lvl q = k ∧ lvl p = k + 1))}

theorem mem_diamondCut_of_levels {k : ℕ} {p q : GridV} (h : gridAdj p q)
    (hlev : (lvl p = k ∧ lvl q = k + 1) ∨ (lvl q = k ∧ lvl p = k + 1)) :
    (⟨s(p, q), h⟩ : gridGraph.edgeSet) ∈ diamondCut k :=
  ⟨p, q, h, rfl, hlev⟩

/-- **Exact crossing characterisation.**  A straight lattice edge meets the
half-integral diamond sphere exactly when its endpoints straddle that level. -/
theorem crosses_diamondBarrier_iff {p q : GridV} (h : gridAdj p q) (k : ℕ) :
    (∃ t : I, straightPath (gridVertex p) (gridVertex q) t ∈ diamondBarrier k) ↔
      ((lvl p = k ∧ lvl q = k + 1) ∨ (lvl q = k ∧ lvl p = k + 1)) := by
  have key : ∀ a b : ℕ, (b = a + 1 ∨ a = b + 1) →
      ∀ t : I, (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) = (k : ℝ) + 1 / 2 →
      ((a = k ∧ b = k + 1) ∨ (b = k ∧ a = k + 1)) := by
    intro a b hab t ht
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    rcases hab with hb | hb
    · left
      have ht' : (a : ℝ) + (t : ℝ) = (k : ℝ) + 1 / 2 := by
        rw [hb] at ht; push_cast at ht; nlinarith [ht]
      have e1 : (a : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have i1 : a < k + 1 := by exact_mod_cast e1
      have e2 : (k : ℝ) < ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
      have i2 : k < a + 1 := by exact_mod_cast e2
      have ha : a = k := by omega
      refine ⟨ha, ?_⟩
      rw [ha] at hb
      omega
    · right
      have ht' : (b : ℝ) + 1 - (t : ℝ) = (k : ℝ) + 1 / 2 := by
        rw [hb] at ht; push_cast at ht; nlinarith [ht]
      have e1 : (b : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      have i1 : b < k + 1 := by exact_mod_cast e1
      have e2 : (k : ℝ) < ((b + 1 : ℕ) : ℝ) := by push_cast; linarith
      have i2 : k < b + 1 := by exact_mod_cast e2
      have hb' : b = k := by omega
      refine ⟨hb', ?_⟩
      rw [hb'] at hb
      omega
  constructor
  · rintro ⟨t, ht⟩
    simp only [diamondBarrier, Set.mem_ofPred_eq] at ht
    rw [l1_affine_step h t, lvl_cast p, lvl_cast q] at ht
    exact key (lvl p) (lvl q) (lvl_adj h) t ht
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨⟨1 / 2, by norm_num⟩, ?_⟩
      simp only [diamondBarrier, Set.mem_ofPred_eq]
      rw [l1_affine_step h ⟨1 / 2, by norm_num⟩, lvl_cast p, lvl_cast q, h1, h2]
      push_cast
      ring
    · refine ⟨⟨1 / 2, by norm_num⟩, ?_⟩
      simp only [diamondBarrier, Set.mem_ofPred_eq]
      rw [l1_affine_step h ⟨1 / 2, by norm_num⟩, lvl_cast p, lvl_cast q, h1, h2]
      push_cast
      ring

/-- The straight realization crosses the diamond frontier only along the diamond
cut labels. -/
theorem gridRealization_crossing_diamond (k : ℕ) :
    gridRealization.CrossingControlledBy (diamondBarrier k) (diamondCut k) := by
  intro u v huv hmeet
  exact mem_diamondCut_of_levels huv ((crosses_diamondBarrier_iff huv k).1 hmeet)

/-! ## Finiteness of the interior vertex set -/

theorem le_self_natAbs (a : ℤ) : a ≤ (a.natAbs : ℤ) := by
  have h := le_abs_self a
  rwa [Int.abs_eq_natAbs] at h

theorem neg_natAbs_le (a : ℤ) : -((a.natAbs : ℤ)) ≤ a := by
  have h := neg_abs_le a
  rwa [Int.abs_eq_natAbs] at h

theorem natAbs_le_iff (a : ℤ) (k : ℕ) : a.natAbs ≤ k ↔ -(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) := by
  constructor
  · intro h
    have h' : (a.natAbs : ℤ) ≤ (k : ℤ) := by exact_mod_cast h
    exact ⟨by have := neg_natAbs_le a; linarith, by have := le_self_natAbs a; linarith⟩
  · rintro ⟨h1, h2⟩
    rcases le_or_gt a 0 with ha | ha
    · have h0 : (a.natAbs : ℤ) = -a := by
        rw [← Int.natAbs_neg a]
        exact Int.natAbs_of_nonneg (by linarith)
      have : (a.natAbs : ℤ) ≤ (k : ℤ) := by linarith
      exact_mod_cast this
    · have h0 : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha.le
      have : (a.natAbs : ℤ) ≤ (k : ℤ) := by linarith
      exact_mod_cast this

theorem finite_natAbs_le (k : ℕ) : {a : ℤ | a.natAbs ≤ k}.Finite := by
  have h : {a : ℤ | a.natAbs ≤ k} = Set.Icc (-(k : ℤ)) (k : ℤ) := by
    ext a
    rw [Set.mem_ofPred_eq, Set.mem_Icc, natAbs_le_iff]
  rw [h]
  exact Set.finite_Icc _ _

/-- A vertex inside the diamond of radius `k + 1/2` has level at most `k`. -/
theorem lvl_le_of_mem_inside {k : ℕ} {p : GridV} (h : gridVertex p ∈ diamondInside k) :
    lvl p ≤ k := by
  simp only [diamondInside, Set.mem_ofPred_eq, lvl_cast] at h
  have h2 : ((lvl p : ℕ) : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h3 : lvl p < k + 1 := by exact_mod_cast h2
  omega

theorem finite_gridVertex_preimage_inside (k : ℕ) :
    (gridVertex ⁻¹' diamondInside k).Finite := by
  have hfin : ({p : GridV | lvl p ≤ k}).Finite := by
    apply Set.Finite.subset ((finite_natAbs_le k).prod (finite_natAbs_le k))
    intro p hp
    have h1 : p.1.natAbs ≤ k := by
      have h : p.1.natAbs + p.2.natAbs ≤ k := hp
      omega
    have h2 : p.2.natAbs ≤ k := by
      have h : p.1.natAbs + p.2.natAbs ≤ k := hp
      omega
    exact ⟨h1, h2⟩
  exact hfin.subset fun p hp => lvl_le_of_mem_inside hp

/-! ## Directional level lemmas -/

theorem natAbs_add_one_of_nonneg {m : ℤ} (hm : 0 ≤ m) : (m + 1).natAbs = m.natAbs + 1 := by
  have h1 : ((m + 1).natAbs : ℤ) = m + 1 := Int.natAbs_of_nonneg (by linarith)
  have h2 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
  have h3 : ((m + 1).natAbs : ℤ) = (m.natAbs : ℤ) + 1 := by rw [h1, h2]
  omega

theorem natAbs_sub_one_of_nonpos {m : ℤ} (hm : m ≤ 0) : (m - 1).natAbs = m.natAbs + 1 := by
  have h1 : ((m - 1).natAbs : ℤ) = -(m - 1) := by
    rw [← Int.natAbs_neg (m - 1)]
    exact Int.natAbs_of_nonneg (by linarith)
  have h2 : (m.natAbs : ℤ) = -m := by
    rw [← Int.natAbs_neg m]
    exact Int.natAbs_of_nonneg (by linarith)
  have h3 : ((m - 1).natAbs : ℤ) = (m.natAbs : ℤ) + 1 := by rw [h1, h2]; ring
  omega

theorem lvl_fst_add_of_nonneg {m n : ℤ} (hm : 0 ≤ m) :
    lvl (m + 1, n) = lvl (m, n) + 1 := by
  simp only [lvl, natAbs_add_one_of_nonneg hm]
  omega

theorem lvl_fst_sub_of_nonpos {m n : ℤ} (hm : m ≤ 0) :
    lvl (m - 1, n) = lvl (m, n) + 1 := by
  simp only [lvl, natAbs_sub_one_of_nonpos hm]
  omega

theorem lvl_snd_add_of_nonneg {m n : ℤ} (hn : 0 ≤ n) :
    lvl (m, n + 1) = lvl (m, n) + 1 := by
  simp only [lvl, natAbs_add_one_of_nonneg hn]
  omega

theorem lvl_snd_sub_of_nonpos {m n : ℤ} (hn : n ≤ 0) :
    lvl (m, n - 1) = lvl (m, n) + 1 := by
  simp only [lvl, natAbs_sub_one_of_nonpos hn]
  omega

/-! ## One crossing step -/

theorem openConnected_single {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) {p q : GridV} (h : gridAdj p q)
    (hlev : (lvl p = k ∧ lvl q = k + 1) ∨ (lvl q = k ∧ lvl p = k + 1)) :
    OpenConnected gridGraph ω (LabelCarrier (diamondCut k)) p q :=
  OpenConnected.of_adj h ⟨⟨s(p, q), h⟩, mem_diamondCut_of_levels h hlev, rfl⟩
    (hopen _ (mem_diamondCut_of_levels h hlev))

/-- A vertex incident to a diamond cut label has level `k` or `k + 1`. -/
theorem level_of_vertexOnLabels {k : ℕ} {u : GridV}
    (hu : VertexOnLabels (diamondCut k) u) : lvl u = k ∨ lvl u = k + 1 := by
  obtain ⟨v, h, he⟩ := hu
  obtain ⟨p, q, hadj, heq, hlev⟩ := he
  have hsym : s(u, v) = s(p, q) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    rcases hlev with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl e1
    · exact Or.inr e2
  · rw [h1]
    rcases hlev with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr e2
    · exact Or.inl e1

/-! ## The four unit adjacencies -/

theorem gridAdj_fst_add (m n : ℤ) : gridAdj (m, n) (m + 1, n) :=
  Or.inr ⟨rfl, Or.inr rfl⟩

theorem gridAdj_fst_sub (m n : ℤ) : gridAdj (m, n) (m - 1, n) :=
  Or.inr ⟨rfl, Or.inl (by ring)⟩

theorem gridAdj_snd_add (m n : ℤ) : gridAdj (m, n) (m, n + 1) :=
  Or.inl ⟨rfl, Or.inr rfl⟩

theorem gridAdj_snd_sub (m n : ℤ) : gridAdj (m, n) (m, n - 1) :=
  Or.inl ⟨rfl, Or.inl (by ring)⟩

/-! ## Neighbours one level inward -/

/-- A vertex at level `k + 1` has a neighbour at level `k`. -/
theorem exists_inner_neighbour {p : GridV} {k : ℕ} (h : lvl p = k + 1) :
    ∃ q : GridV, gridAdj p q ∧ lvl q = k := by
  rcases p with ⟨m, n⟩
  rcases lt_or_ge m 0 with hm | hm
  · -- m ≤ -1: step east
    refine ⟨(m + 1, n), gridAdj_fst_add m n, ?_⟩
    have hstep : lvl ((m + 1) - 1, n) = lvl (m + 1, n) + 1 :=
      lvl_fst_sub_of_nonpos (by linarith)
    rw [show m + 1 - 1 = m by ring] at hstep
    omega
  · rcases lt_or_ge m 1 with hm1 | hm1
    · -- m = 0: step in the second coordinate
      have hmz : m = 0 := by omega
      subst hmz
      have hzero : lvl ((0 : ℤ), n) = n.natAbs := by simp [lvl]
      have hnne : n ≠ 0 := by
        intro hnz
        rw [hnz] at h
        simp [lvl] at h
      rcases lt_or_ge n 0 with hn | hn
      · refine ⟨(0, n + 1), gridAdj_snd_add 0 n, ?_⟩
        have hstep : lvl ((0 : ℤ), (n + 1) - 1) = lvl ((0 : ℤ), n + 1) + 1 :=
          lvl_snd_sub_of_nonpos (by omega)
        rw [show n + 1 - 1 = n by ring] at hstep
        omega
      · refine ⟨(0, n - 1), gridAdj_snd_sub 0 n, ?_⟩
        have hstep : lvl ((0 : ℤ), (n - 1) + 1) = lvl ((0 : ℤ), n - 1) + 1 :=
          lvl_snd_add_of_nonneg (by omega)
        rw [show n - 1 + 1 = n by ring] at hstep
        omega
    · -- m ≥ 1: step west
      refine ⟨(m - 1, n), gridAdj_fst_sub m n, ?_⟩
      have hstep : lvl ((m - 1) + 1, n) = lvl (m - 1, n) + 1 :=
        lvl_fst_add_of_nonneg (by linarith)
      rw [show m - 1 + 1 = m by ring] at hstep
      omega

/-! ## The four staircases -/

/-- North-east staircase: a level-`k` vertex in the closed first quadrant reaches
`(k, 0)` through crossing edges only. -/
theorem conn_NE {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) :
    ∀ (n : ℕ) (m : ℤ), 0 ≤ m → lvl (m, (n : ℤ)) = k →
      OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (m, (n : ℤ)) ((k : ℤ), 0) := by
  intro n
  induction n with
  | zero =>
    intro m hm hlv
    have hzero : lvl (m, (((0 : ℕ)) : ℤ)) = m.natAbs := by simp [lvl]
    rw [hzero] at hlv
    have h2 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
    have hmk : m = (k : ℤ) := by omega
    subst hmk
    exact OpenConnected.refl ω (LabelCarrier (diamondCut k)) _
  | succ n ih =>
    intro m hm hlv
    have hcast : (((n : ℕ) + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hlv ⊢
    have hA : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (m, (n : ℤ) + 1) (m + 1, (n : ℤ) + 1) := by
      refine openConnected_single hopen (gridAdj_fst_add m ((n : ℤ) + 1)) (Or.inl ⟨hlv, ?_⟩)
      rw [lvl_fst_add_of_nonneg hm]
      omega
    have hplev : lvl (m + 1, (n : ℤ) + 1) = k + 1 := by
      rw [lvl_fst_add_of_nonneg hm]
      omega
    have hlevB : lvl (m + 1, (n : ℤ)) = k := by
      have h1 : lvl (m + 1, (n : ℤ) + 1) = lvl (m + 1, (n : ℤ)) + 1 :=
        lvl_snd_add_of_nonneg (Int.natCast_nonneg n)
      omega
    have hB : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (m + 1, (n : ℤ) + 1) (m + 1, (n : ℤ)) := by
      have hadj : gridAdj (m + 1, (n : ℤ) + 1) (m + 1, (n : ℤ)) := by
        have h := gridAdj_snd_sub (m + 1) ((n : ℤ) + 1)
        rwa [show (n : ℤ) + 1 - 1 = (n : ℤ) by ring] at h
      exact openConnected_single hopen hadj (Or.inr ⟨hlevB, hplev⟩)
    exact hA.trans (hB.trans (ih (m + 1) (by linarith) hlevB))

/-- North-west staircase: north, then east. -/
theorem conn_NW {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) :
    ∀ (j : ℕ) (n : ℤ), 0 ≤ n → lvl (-(j : ℤ), n) = k →
      OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (-(j : ℤ), n) ((0 : ℤ), (k : ℤ)) := by
  intro j
  induction j with
  | zero =>
    intro n hn hlv
    have hz : -((((0 : ℕ)) : ℤ)) = (0 : ℤ) := by norm_num
    rw [hz] at hlv ⊢
    have hzero : lvl ((0 : ℤ), n) = n.natAbs := by simp [lvl]
    rw [hzero] at hlv
    have h2 : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn
    have hnk : n = (k : ℤ) := by omega
    subst hnk
    exact OpenConnected.refl ω (LabelCarrier (diamondCut k)) _
  | succ j ih =>
    intro n hn hlv
    have hcast : (-(((j : ℕ) + 1 : ℕ) : ℤ)) = -(j : ℤ) - 1 := by push_cast; ring
    rw [hcast] at hlv ⊢
    have hA : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (-(j : ℤ) - 1, n) (-(j : ℤ) - 1, n + 1) := by
      refine openConnected_single hopen (gridAdj_snd_add (-(j : ℤ) - 1) n) (Or.inl ⟨hlv, ?_⟩)
      rw [lvl_snd_add_of_nonneg hn]
      omega
    have hplev : lvl (-(j : ℤ) - 1, n + 1) = k + 1 := by
      rw [lvl_snd_add_of_nonneg hn]
      omega
    have hlevB : lvl (-(j : ℤ), n + 1) = k := by
      have h1 : lvl (-(j : ℤ) - 1, n + 1) = lvl (-(j : ℤ), n + 1) + 1 :=
        lvl_fst_sub_of_nonpos (m := -(j : ℤ)) (n := n + 1) (by linarith)
      omega
    have hB : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (-(j : ℤ) - 1, n + 1) (-(j : ℤ), n + 1) := by
      have hadj : gridAdj (-(j : ℤ) - 1, n + 1) (-(j : ℤ), n + 1) := by
        have h := gridAdj_fst_add (-(j : ℤ) - 1) (n + 1)
        rwa [show -(j : ℤ) - 1 + 1 = -(j : ℤ) by ring] at h
      exact openConnected_single hopen hadj (Or.inr ⟨hlevB, hplev⟩)
    exact hA.trans (hB.trans (ih (n + 1) (by linarith) hlevB))

/-- South-west staircase: west, then north. -/
theorem conn_SW {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) :
    ∀ (j : ℕ) (m : ℤ), m ≤ 0 → lvl (m, -(j : ℤ)) = k →
      OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (m, -(j : ℤ)) ((-(k : ℤ)), 0) := by
  intro j
  induction j with
  | zero =>
    intro m hm hlv
    have hz : -((((0 : ℕ)) : ℤ)) = (0 : ℤ) := by norm_num
    rw [hz] at hlv ⊢
    have hzero : lvl (m, (0 : ℤ)) = m.natAbs := by simp [lvl]
    rw [hzero] at hlv
    have h2 : (m.natAbs : ℤ) = -m := by
      rw [← Int.natAbs_neg m]
      exact Int.natAbs_of_nonneg (by linarith)
    have hmk : m = -(k : ℤ) := by omega
    subst hmk
    exact OpenConnected.refl ω (LabelCarrier (diamondCut k)) _
  | succ j ih =>
    intro m hm hlv
    have hcast : (-(((j : ℕ) + 1 : ℕ) : ℤ)) = -(j : ℤ) - 1 := by push_cast; ring
    rw [hcast] at hlv ⊢
    have hA : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (m, -(j : ℤ) - 1) (m - 1, -(j : ℤ) - 1) := by
      refine openConnected_single hopen (gridAdj_fst_sub m (-(j : ℤ) - 1)) (Or.inl ⟨hlv, ?_⟩)
      rw [lvl_fst_sub_of_nonpos hm]
      omega
    have hplev : lvl (m - 1, -(j : ℤ) - 1) = k + 1 := by
      rw [lvl_fst_sub_of_nonpos hm]
      omega
    have hlevB : lvl (m - 1, -(j : ℤ)) = k := by
      have h1 : lvl (m - 1, -(j : ℤ) - 1) = lvl (m - 1, -(j : ℤ)) + 1 :=
        lvl_snd_sub_of_nonpos (m := m - 1) (n := -(j : ℤ)) (by linarith)
      omega
    have hB : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        (m - 1, -(j : ℤ) - 1) (m - 1, -(j : ℤ)) := by
      have hadj : gridAdj (m - 1, -(j : ℤ) - 1) (m - 1, -(j : ℤ)) := by
        have h := gridAdj_snd_add (m - 1) (-(j : ℤ) - 1)
        rwa [show -(j : ℤ) - 1 + 1 = -(j : ℤ) by ring] at h
      exact openConnected_single hopen hadj (Or.inr ⟨hlevB, hplev⟩)
    exact hA.trans (hB.trans (ih (m - 1) (by linarith) hlevB))

/-- South-east staircase: south, then west. -/
theorem conn_SE {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) :
    ∀ (i : ℕ) (n : ℤ), n ≤ 0 → lvl ((i : ℤ), n) = k →
      OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        ((i : ℤ), n) ((0 : ℤ), -(k : ℤ)) := by
  intro i
  induction i with
  | zero =>
    intro n hn hlv
    have hzero : lvl (((((0 : ℕ)) : ℤ)), n) = n.natAbs := by simp [lvl]
    rw [hzero] at hlv
    have h2 : (n.natAbs : ℤ) = -n := by
      rw [← Int.natAbs_neg n]
      exact Int.natAbs_of_nonneg (by linarith)
    have hnk : n = -(k : ℤ) := by omega
    subst hnk
    exact OpenConnected.refl ω (LabelCarrier (diamondCut k)) _
  | succ i ih =>
    intro n hn hlv
    have hcast : (((i : ℕ) + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast] at hlv ⊢
    have hA : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        ((i : ℤ) + 1, n) ((i : ℤ) + 1, n - 1) := by
      refine openConnected_single hopen (gridAdj_snd_sub ((i : ℤ) + 1) n) (Or.inl ⟨hlv, ?_⟩)
      rw [lvl_snd_sub_of_nonpos hn]
      omega
    have hplev : lvl ((i : ℤ) + 1, n - 1) = k + 1 := by
      rw [lvl_snd_sub_of_nonpos hn]
      omega
    have hlevB : lvl ((i : ℤ), n - 1) = k := by
      have h1 : lvl ((i : ℤ) + 1, n - 1) = lvl ((i : ℤ), n - 1) + 1 :=
        lvl_fst_add_of_nonneg (m := (i : ℤ)) (n := n - 1) (Int.natCast_nonneg i)
      omega
    have hB : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
        ((i : ℤ) + 1, n - 1) ((i : ℤ), n - 1) := by
      have hadj : gridAdj ((i : ℤ) + 1, n - 1) ((i : ℤ), n - 1) := by
        have h := gridAdj_fst_sub ((i : ℤ) + 1) (n - 1)
        rwa [show (i : ℤ) + 1 - 1 = (i : ℤ) by ring] at h
      exact openConnected_single hopen hadj (Or.inr ⟨hlevB, hplev⟩)
    exact hA.trans (hB.trans (ih (n - 1) (by linarith) hlevB))

/-- **Every level-`k` lattice vertex reaches the hub `(k, 0)`** through crossing
edges of the diamond frontier only. -/
theorem connected_to_hub_of_level {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) {u : GridV} (hlvl : lvl u = k) :
    OpenConnected gridGraph ω (LabelCarrier (diamondCut k)) u ((k : ℤ), 0) := by
  have hubNE : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
      ((0 : ℤ), (k : ℤ)) ((k : ℤ), 0) := by
    have h := conn_NE hopen k 0 (by linarith) (by simp [lvl])
    simpa using h
  have hubNW : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
      ((-(k : ℤ)), (0 : ℤ)) ((0 : ℤ), (k : ℤ)) := conn_NW hopen k 0 (by linarith) (by simp [lvl])
  have hubSW : OpenConnected gridGraph ω (LabelCarrier (diamondCut k))
      ((0 : ℤ), (-(k : ℤ))) ((-(k : ℤ)), (0 : ℤ)) := by
    have h := conn_SW hopen k 0 (by linarith) (by simp [lvl])
    simpa using h
  rcases u with ⟨m, n⟩
  rcases le_or_gt (0 : ℤ) m with hm | hm <;> rcases le_or_gt (0 : ℤ) n with hn | hn
  · obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = (n' : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    exact conn_NE hopen n' m hm hlvl
  · obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = (m' : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) :=
      ⟨(-n).toNat, by
        have h1 : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by linarith)
        linarith⟩
    exact (conn_SE hopen m' (-(j : ℤ)) hn.le hlvl).trans (hubSW.trans (hubNW.trans hubNE))
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j : ℤ) :=
      ⟨(-m).toNat, by
        have h1 : ((((-m).toNat : ℕ)) : ℤ) = -m := Int.toNat_of_nonneg (by linarith)
        linarith⟩
    obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = (n' : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    exact (conn_NW hopen j n' hn hlvl).trans hubNE
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -(j : ℤ) :=
      ⟨(-m).toNat, by
        have h1 : ((((-m).toNat : ℕ)) : ℤ) = -m := Int.toNat_of_nonneg (by linarith)
        linarith⟩
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = -(i : ℤ) :=
      ⟨(-n).toNat, by
        have h1 : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by linarith)
        linarith⟩
    exact (conn_SW hopen i (-(j : ℤ)) hm.le hlvl).trans (hubNW.trans hubNE)

/-- Every vertex incident to a diamond cut label reaches the hub `(k, 0)`. -/
theorem connected_to_hub {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) {u : GridV}
    (hu : VertexOnLabels (diamondCut k) u) :
    OpenConnected gridGraph ω (LabelCarrier (diamondCut k)) u ((k : ℤ), 0) := by
  rcases level_of_vertexOnLabels hu with hk | hk
  · exact connected_to_hub_of_level hopen hk
  · obtain ⟨q, hadj, hq⟩ := exists_inner_neighbour hk
    exact (openConnected_single hopen hadj (Or.inr ⟨hq, hk⟩)).trans
      (connected_to_hub_of_level hopen hq)

/-- **The diamond cut labels are open-connected**: every vertex incident to a
crossing edge is joined to every other one through crossing edges alone. -/
theorem diamondCut_openLabelConnected (k : ℕ) {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) :
    OpenLabelConnected gridGraph ω (diamondCut k) := by
  intro u v hu hv
  exact (connected_to_hub hopen hu).trans (openConnected_symm (connected_to_hub hopen hv))

/-! ## A genuine separator open circuit on every diamond shell -/

/-- The all-open configuration carries a genuine `SeparatorOpenCircuit` on the
diamond frontier: every vertex avoids the barrier, only crossing labels meet it,
those labels are open, and they are connected through one another. -/
theorem separatorOpenCircuit_diamond (k : ℕ) :
    SeparatorOpenCircuit gridRealization (fun _ => true) (diamondCut k) (diamondSep k) where
  vertex_off v := gridVertex_off_diamond v
  crossing := gridRealization_crossing_diamond k
  label_open _ _ := rfl
  openConnected := diamondCut_openLabelConnected k (fun _ _ => rfl)

/-- The sup-norm ball of radius `ρ` about the origin lies inside the diamond of
radius `⌈2ρ⌉₊ + 1/2`. -/
theorem ball_subset_diamondInside (ρ : ℝ) :
    ball ((0 : ℝ), (0 : ℝ)) ρ ⊆ diamondInside (⌈2 * ρ⌉₊ + 1) := by
  intro z hz
  have hd : dist z ((0 : ℝ), (0 : ℝ)) < ρ := hz
  rw [Prod.dist_eq] at hd
  simp only [Real.dist_eq, sub_zero] at hd
  have h1 : |z.1| < ρ := lt_of_le_of_lt (le_max_left _ _) hd
  have h2 : |z.2| < ρ := lt_of_le_of_lt (le_max_right _ _) hd
  simp only [diamondInside, Set.mem_ofPred_eq]
  have h3 : |z.1| + |z.2| < 2 * ρ := by linarith
  have h4 : 2 * ρ ≤ ((⌈2 * ρ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h5 : ((⌈2 * ρ⌉₊ : ℕ) : ℝ) ≤ ((⌈2 * ρ⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  simp only [l1]
  push_cast
  linarith

/-- **Cofinal separator circuit exhaustion** for the square lattice: for every
radius the diamond frontier encloses the ball, carries only finitely many
vertices, and its crossing labels form a connected open circuit. -/
theorem hasSeparatorCircuitExhaustion_allOpen :
    HasSeparatorCircuitExhaustion gridRealization (fun _ => true) ((0 : ℝ), (0 : ℝ)) := by
  intro ρ
  exact ⟨diamondCut (⌈2 * ρ⌉₊ + 1), diamondSep (⌈2 * ρ⌉₊ + 1), ball_subset_diamondInside ρ,
    finite_gridVertex_preimage_inside _, separatorOpenCircuit_diamond _⟩

/-- At most one infinite open cluster for the all-open square lattice, obtained
through the separator machinery from the diamond circuits. -/
theorem globalAtMostOne_allOpen : GlobalAtMostOne gridGraph (fun _ => true) :=
  globalAtMostOne_of_separatorCircuitExhaustion gridRealization _ _
    hasSeparatorCircuitExhaustion_allOpen

/-! ## Exactness of the crossing control is sharp

The diamond crossing sets are *not* a proper subfamily of the edges: they
partition the whole edge set.  Hence a configuration whose every diamond shell is
crossed only by open labels is necessarily the all-open configuration; the
convex diamond frontier cannot supply a non-trivial cofinal exhaustion on the
square lattice. -/

theorem mem_diamondCut_of_adj {p q : GridV} (h : gridAdj p q) :
    ∃ k : ℕ, (⟨s(p, q), h⟩ : gridGraph.edgeSet) ∈ diamondCut k := by
  rcases lvl_adj h with hstep | hstep
  · exact ⟨lvl p, mem_diamondCut_of_levels h (Or.inl ⟨rfl, hstep⟩)⟩
  · exact ⟨lvl q, mem_diamondCut_of_levels h (Or.inr ⟨rfl, hstep⟩)⟩

/-- Every edge of the square lattice lies in some diamond crossing set. -/
theorem exists_mem_diamondCut (e : gridGraph.edgeSet) : ∃ k : ℕ, e ∈ diamondCut k := by
  have hout : e.1 = s(e.1.out.1, e.1.out.2) := (Quot.out_eq e.1).symm
  have hadj : gridGraph.Adj e.1.out.1 e.1.out.2 := by
    have h2 : s(e.1.out.1, e.1.out.2) ∈ gridGraph.edgeSet := hout ▸ e.2
    rwa [SimpleGraph.mem_edgeSet] at h2
  obtain ⟨k, hk⟩ := mem_diamondCut_of_adj hadj
  have hee : e = (⟨s(e.1.out.1, e.1.out.2), hadj⟩ : gridGraph.edgeSet) := by
    refine Subtype.ext ?_
    exact hout
  rw [hee]
  exact ⟨k, hk⟩

/-- If every diamond crossing set consists of open labels, the configuration is
all-open. -/
theorem allOpen_of_diamondCuts_open {ω : gridGraph.edgeSet → Bool}
    (h : ∀ k : ℕ, ∀ e ∈ diamondCut k, ω e = true) : ∀ e, ω e = true := by
  intro e
  obtain ⟨k, hk⟩ := exists_mem_diamondCut e
  exact h k e hk

/-! ## The dual direction: a closed diamond cut traps the open cluster

The same exact crossing control gives the *non-vacuous* percolation statement:
if every edge crossing a diamond shell is closed, no open path can leave the
diamond, so the open component of any interior vertex is finite. -/

/-- **Trapping by a closed diamond cut.**  If all crossing labels of the diamond
shell of radius `k + 1/2` are closed, the open cluster of every interior vertex
stays inside the diamond. -/
theorem openComponent_finite_of_diamondCut_closed (k : ℕ) {ω : gridGraph.edgeSet → Bool}
    (hclosed : ∀ e ∈ diamondCut k, ω e = false) {x : GridV}
    (hx : gridVertex x ∈ diamondInside k) :
    {y : GridV | OpenConnected gridGraph ω Set.univ x y}.Finite := by
  refine (finite_gridVertex_preimage_inside k).subset ?_
  intro y hy
  exact mem_inside_of_openConnected_of_closed gridRealization
    (gridRealization_crossing_diamond k) hclosed (diamondSep k).cover (diamondSep k).separated
    hx hy

/-- Consequently an interior vertex of a closed diamond cut is not in an
infinite open cluster. -/
theorem not_exteriorInfiniteCluster_of_diamondCut_closed (k : ℕ)
    {ω : gridGraph.edgeSet → Bool} (hclosed : ∀ e ∈ diamondCut k, ω e = false)
    {x : GridV} (hx : gridVertex x ∈ diamondInside k) :
    ¬ ExteriorInfiniteCluster gridGraph ω Set.univ x := by
  intro hxinf
  exact hxinf (openComponent_finite_of_diamondCut_closed k hclosed hx)

/-- The diamond crossing set is finite: its edges have both endpoints at level
`k` or `k + 1`, hence lie in a bounded box of lattice points. -/
theorem finite_diamondCut (k : ℕ) : (diamondCut k).Finite := by
  have hS : ({p : GridV | p.1.natAbs ≤ k + 1 ∧ p.2.natAbs ≤ k + 1}).Finite :=
    (finite_natAbs_le (k + 1)).prod (finite_natAbs_le (k + 1))
  have hbox : ∀ p : GridV, lvl p = k ∨ lvl p = k + 1 →
      p.1.natAbs ≤ k + 1 ∧ p.2.natAbs ≤ k + 1 := by
    intro p hp
    have h1 : p.1.natAbs ≤ lvl p := by simp only [lvl]; omega
    have h2 : p.2.natAbs ≤ lvl p := by simp only [lvl]; omega
    omega
  have himg : ((fun z : GridV × GridV => s(z.1, z.2)) ''
      (({p : GridV | p.1.natAbs ≤ k + 1 ∧ p.2.natAbs ≤ k + 1} :
        Set GridV) ×ˢ {p : GridV | p.1.natAbs ≤ k + 1 ∧ p.2.natAbs ≤ k + 1})).Finite :=
    (hS.prod hS).image _
  refine Set.Finite.of_finite_image (s := diamondCut k) (f := fun e : gridGraph.edgeSet => e.1)
    ?_ ?_
  · refine himg.subset ?_
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨p, q, hadj, rfl, hlev⟩ := he
    have hp : lvl p = k ∨ lvl p = k + 1 := by
      rcases hlev with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
    have hq : lvl q = k ∨ lvl q = k + 1 := by
      rcases hlev with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr h2
      · exact Or.inl h1
    exact ⟨(p, q), ⟨hbox p hp, hbox q hq⟩, rfl⟩
  · intro e _ f _ h
    exact Subtype.ext h

/-! ## The square (`ℓ^∞`) box cut is *not* open-connected

The diamond frontier gives a connected crossing cycle; the square frontier does
not.  The reason is purely combinatorial: the crossing labels of the `ℓ^∞` box
shell are the edges joining sup-norm level `k` to level `k+1`, and in the square
lattice those labels have isolated edges.  This is the precise obstruction that
prevents a solid square shell from serving as an open circuit; a closed square
cut still traps clusters (`openComponent_finite_of_diamondCut_closed` with the
diamond replaced by the box). -/

/-- The `ℓ^∞` (sup) level of a lattice vertex. -/
def lvlInf (p : GridV) : ℕ := max p.1.natAbs p.2.natAbs

theorem lvlInf_natCast (a b : ℕ) : lvlInf (((a : ℤ)), ((b : ℤ))) = max a b := by
  simp [lvlInf]

/-- The box cut at level `k`: edges joining sup-norm level `k` to level `k+1`. -/
def boxCut (k : ℕ) : Set gridGraph.edgeSet :=
  {e | ∃ (p q : GridV) (h : gridAdj p q), e = ⟨s(p, q), h⟩ ∧
    ((lvlInf p = k ∧ lvlInf q = k + 1) ∨ (lvlInf q = k ∧ lvlInf p = k + 1))}

theorem mem_boxCut_of_levels {k : ℕ} {p q : GridV} (h : gridAdj p q)
    (hlev : (lvlInf p = k ∧ lvlInf q = k + 1) ∨ (lvlInf q = k ∧ lvlInf p = k + 1)) :
    (⟨s(p, q), h⟩ : gridGraph.edgeSet) ∈ boxCut k :=
  ⟨p, q, h, rfl, hlev⟩

/-- Compute the sup-norm level of `((k + c), b)`. -/
theorem lvlInf_of_nat_add (k c : ℕ) (b : ℤ) :
    lvlInf (((k : ℤ) + (c : ℤ)), b) = max (k + c) b.natAbs := by
  have ha : (((k : ℤ) + (c : ℤ)).natAbs) = k + c := by
    have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) + (c : ℤ) by positivity)
    omega
  simp only [lvlInf, ha]

/-- The two levels of a box-cut edge are `k` and `k+1`, in some order. -/
theorem boxCut_levels {k : ℕ} {p q : GridV} (h : gridAdj p q)
    (hmem : (⟨s(p, q), h⟩ : gridGraph.edgeSet) ∈ boxCut k) :
    (lvlInf p = k ∧ lvlInf q = k + 1) ∨ (lvlInf p = k + 1 ∧ lvlInf q = k) := by
  obtain ⟨p', q', h', he, hlev⟩ := hmem
  have hsym : s(p, q) = s(p', q') := congrArg Subtype.val he
  rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    rcases hlev with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e2, e1⟩
  · rw [h1, h2]
    rcases hlev with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr ⟨e2, e1⟩
    · exact Or.inl ⟨e1, e2⟩

theorem natAbs_int_add_one (k : ℕ) : (((k : ℤ) + 1).natAbs) = k + 1 := by
  have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) + 1 by positivity)
  omega

theorem natAbs_int_zero : ((0 : ℤ)).natAbs = 0 := by norm_num

theorem natAbs_int_one : ((1 : ℤ)).natAbs = 1 := by norm_num

theorem natAbs_int_neg_one : ((-1 : ℤ)).natAbs = 1 := by norm_num

/-- The east corner `(k+1, 0)` has exactly one box-cut neighbour: `(k, 0)`. -/
theorem boxCut_corner_neighbours (k : ℕ) {x : GridV}
    (h : gridAdj (((k + 1 : ℕ) : ℤ), (0 : ℤ)) x)
    (hmem : (⟨s((((k + 1 : ℕ) : ℤ), (0 : ℤ)), x), h⟩ : gridGraph.edgeSet) ∈ boxCut k) :
    x = (((k : ℕ) : ℤ), (0 : ℤ)) := by
  have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hlv : lvlInf ((((k + 1 : ℕ) : ℤ)), (0 : ℤ)) = k + 1 := by
    rw [hcast]; simp only [lvlInf, natAbs_int_add_one k, natAbs_int_zero]
    exact max_eq_left (by omega)
  obtain ⟨e1, e2⟩ | ⟨e1, e2⟩ := boxCut_levels h hmem
  · omega
  · rcases x with ⟨a, b⟩
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · obtain rfl : a = (k : ℤ) + 1 := by
        rw [hcast] at h1; exact h1.symm
      obtain rfl : b = -1 := by omega
      have hx : lvlInf ((k : ℤ) + 1, (-1 : ℤ)) = k + 1 := by
        simp only [lvlInf, natAbs_int_add_one k, natAbs_int_neg_one]
        exact Nat.max_eq_left (by omega)
      rw [hx] at e2
      omega
    · obtain rfl : a = (k : ℤ) + 1 := by
        rw [hcast] at h1; exact h1.symm
      obtain rfl : b = 1 := by omega
      have hx : lvlInf ((k : ℤ) + 1, (1 : ℤ)) = k + 1 := by
        simp only [lvlInf, natAbs_int_add_one k, natAbs_int_one]
        exact Nat.max_eq_left (by omega)
      rw [hx] at e2
      omega
    · obtain rfl : b = (0 : ℤ) := h1.symm
      obtain rfl : a = ((k : ℕ) : ℤ) := by omega
      rfl
    · obtain rfl : b = (0 : ℤ) := h1.symm
      obtain rfl : a = (k : ℤ) + 2 := by omega
      have ha : (((k : ℤ) + 2).natAbs) = k + 2 := by
        have h2' := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) + 2 by positivity)
        omega
      have hx : lvlInf ((k : ℤ) + 2, (0 : ℤ)) = k + 2 := by
        simp only [lvlInf, ha, natAbs_int_zero]
        exact max_eq_left (by omega)
      rw [hx] at e2
      omega

/-- The axis point `(k, 0)` has exactly one box-cut neighbour: `(k+1, 0)`. -/
theorem boxCut_axis_neighbours (k : ℕ) (hk : 1 ≤ k) {x : GridV}
    (h : gridAdj (((k : ℕ) : ℤ), (0 : ℤ)) x)
    (hmem : (⟨s((((k : ℕ) : ℤ), (0 : ℤ)), x), h⟩ : gridGraph.edgeSet) ∈ boxCut k) :
    x = (((k + 1 : ℕ) : ℤ), (0 : ℤ)) := by
  have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hlv : lvlInf ((((k : ℕ) : ℤ)), (0 : ℤ)) = k := by
    simp only [lvlInf, natAbs_int_zero]
    exact max_eq_left (by omega)
  obtain ⟨e1, e2⟩ | ⟨e1, e2⟩ := boxCut_levels h hmem
  · rcases x with ⟨a, b⟩
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
    · -- a = k, b = -1
      obtain rfl : a = ((k : ℕ) : ℤ) := h1.symm
      obtain rfl : b = -1 := by omega
      have hx : lvlInf (((k : ℕ) : ℤ), (-1 : ℤ)) = k := by
        simp only [lvlInf, natAbs_int_neg_one]
        exact Nat.max_eq_left hk
      rw [hx] at e2
      omega
    · -- a = k, b = 1
      obtain rfl : a = ((k : ℕ) : ℤ) := h1.symm
      obtain rfl : b = 1 := by omega
      have hx : lvlInf (((k : ℕ) : ℤ), (1 : ℤ)) = k := by
        simp only [lvlInf, natAbs_int_one]
        exact Nat.max_eq_left hk
      rw [hx] at e2
      omega
    · -- b = 0, a = k - 1
      obtain rfl : b = (0 : ℤ) := h1.symm
      obtain rfl : a = ((k : ℕ) : ℤ) - 1 := by omega
      have ha : ((((k : ℕ) : ℤ) - 1).natAbs) = k - 1 := by
        have h2' : ((k : ℤ) - 1) = (((k - 1 : ℕ)) : ℤ) := by
          push_cast [hk]; omega
        rw [h2']
        have h3 := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ (((k - 1 : ℕ)) : ℤ) by positivity)
        omega
      have hx : lvlInf ((((k : ℕ) : ℤ) - 1), (0 : ℤ)) = k - 1 := by
        simp only [lvlInf, ha, natAbs_int_zero]
        exact max_eq_left (by omega)
      rw [hx] at e2
      omega
    · -- b = 0, a = k + 1
      obtain rfl : b = (0 : ℤ) := h1.symm
      obtain rfl : a = (k : ℤ) + 1 := by omega
      rw [← hcast]
  · omega

/-- **The box cut is not open-connected.**  For `k ≥ 1` the two isolated box-cut
edges through `(k,0)` and `(0,k)` lie in different components, so the box-cut
labels can never be the connected open circuit that `SeparatorOpenCircuit`
demands. -/
theorem boxCut_not_openLabelConnected (k : ℕ) (hk : 1 ≤ k)
    (ω : gridGraph.edgeSet → Bool) :
    ¬ OpenLabelConnected gridGraph ω (boxCut k) := by
  have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  have hlv1 : lvlInf ((((k + 1 : ℕ) : ℤ)), (0 : ℤ)) = k + 1 := by
    rw [hcast]; simp only [lvlInf, natAbs_int_add_one k, natAbs_int_zero]
    exact max_eq_left (by omega)
  have hlv0 : lvlInf ((((k : ℕ) : ℤ)), (0 : ℤ)) = k := by
    simp only [lvlInf, natAbs_int_zero]
    exact max_eq_left (by omega)
  have hlv1' : lvlInf ((0 : ℤ), (((k + 1 : ℕ) : ℤ))) = k + 1 := by
    rw [hcast]; simp only [lvlInf, natAbs_int_add_one k, natAbs_int_zero]
    exact max_eq_right (by omega)
  have hlv0' : lvlInf ((0 : ℤ), (((k : ℕ) : ℤ))) = k := by
    simp only [lvlInf, natAbs_int_zero]
    exact max_eq_right (by omega)
  have hadj1 : gridAdj ((((k + 1 : ℕ) : ℤ)), (0 : ℤ)) (((k : ℕ) : ℤ), (0 : ℤ)) := by
    have h := gridAdj_fst_sub ((((k + 1 : ℕ) : ℤ))) 0
    rwa [show ((((k + 1 : ℕ) : ℤ)) - 1) = ((k : ℕ) : ℤ) by rw [hcast]; ring] at h
  have hadj2 : gridAdj ((0 : ℤ), (((k + 1 : ℕ) : ℤ))) ((0 : ℤ), (((k : ℕ) : ℤ))) := by
    have h := gridAdj_snd_sub (0 : ℤ) ((((k + 1 : ℕ) : ℤ)))
    rwa [show ((((k + 1 : ℕ) : ℤ)) - 1) = ((k : ℕ) : ℤ) by rw [hcast]; ring] at h
  intro hconn
  have hu : VertexOnLabels (boxCut k) (((k + 1 : ℕ) : ℤ), (0 : ℤ)) :=
    ⟨(((k : ℕ) : ℤ), (0 : ℤ)), hadj1,
      mem_boxCut_of_levels hadj1 (Or.inr ⟨hlv0, hlv1⟩)⟩
  have hv : VertexOnLabels (boxCut k) ((0 : ℤ), (((k + 1 : ℕ) : ℤ))) :=
    ⟨((0 : ℤ), (((k : ℕ) : ℤ))), hadj2,
      mem_boxCut_of_levels hadj2 (Or.inr ⟨hlv0', hlv1'⟩)⟩
  obtain ⟨p, hp⟩ := hconn hu hv
  have key : ∀ {a x : GridV} (w : gridGraph.Walk a x),
      (a = (((k + 1 : ℕ) : ℤ), (0 : ℤ)) ∨ a = (((k : ℕ) : ℤ), (0 : ℤ))) →
      IsOpenIn ω (LabelCarrier (boxCut k)) w →
      (x = (((k + 1 : ℕ) : ℤ), (0 : ℤ)) ∨ x = (((k : ℕ) : ℤ), (0 : ℤ))) := by
    intro a x w
    induction w with
    | nil => intro ha _; exact ha
    | @cons a b c hab w ih =>
      intro ha hw
      obtain ⟨⟨hA, -⟩, hrest⟩ := isOpenIn_cons.mp hw
      obtain ⟨e, he, hee⟩ := hA
      have hedge : (⟨s(a, b), hab⟩ : gridGraph.edgeSet) ∈ boxCut k := by
        have h1 : e.1 = s(a, b) := hee
        have h2 : e = ⟨s(a, b), hab⟩ := Subtype.ext h1
        rwa [h2] at he
      rcases ha with ha | ha
      · subst ha
        exact ih (Or.inr (boxCut_corner_neighbours k hab hedge)) hrest
      · subst ha
        exact ih (Or.inl (boxCut_axis_neighbours k hk hab hedge)) hrest
  have hend := key p (Or.inl rfl) hp
  rcases hend with h1 | h1
  · have : (((k + 1 : ℕ) : ℤ)) = (0 : ℤ) := (congrArg Prod.fst h1).symm
    omega
  · have : ((k : ℕ) : ℤ) = (0 : ℤ) := (congrArg Prod.fst h1).symm
    omega

end FK.PlaneTopology.GridFrontier
