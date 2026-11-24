import FK.PlanarTarget
import FK.WeakOpenCut

/-!
# The staircase configuration: a positive instance beyond the finite class

`PlanarTarget.exists_dualNonpercolating_noOpenDiamondCut` exhibits a
configuration with no infinite dual-open cluster on which no diamond shell is
all-open, so the fixed `ℓ¹` level-set cut argument cannot reach it.  This file
shows that the *conclusion* of the planar target nevertheless holds for that
configuration, so the obstruction concerns the method and not the truth of the
target:

* the closed staircase edges form an infinite set, so the finite-closed-edge
  instance `dualNonpercolation_imp_atMostOne_of_finite_closedEdges` does not
  apply;
* the open graph is connected, hence there is exactly one infinite open cluster.

The connectivity is proved by explicit lattice walks: every vertex reaches the
origin along an open row and an open column.

## Main results

* `FK.PlaneTopology.StaircaseConnected.horiz_open`, `vert_open`
* `FK.PlaneTopology.StaircaseConnected.staircase_connected`
* `FK.PlaneTopology.StaircaseConnected.staircase_globalAtMostOne`
* `FK.PlaneTopology.StaircaseConnected.staircase_infinite_closed`
* `FK.PlaneTopology.StaircaseConnected.staircase_witness`
-/

namespace FK.PlaneTopology.StaircaseConnected

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridOpenCuts
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PlanarTarget

/-! ## Which staircase edges are open -/

/-- A horizontal lattice edge off the positive `x`-axis is open. -/
lemma horiz_open {m n : ℤ} (h : n ≠ 0 ∨ m < 0) :
    staircaseConfig (⟨s((m, n), (m + 1, n)), gridAdj_fst_add m n⟩ :
      gridGraph.edgeSet) = true := by
  by_contra hc
  have hfalse : staircaseConfig (⟨s((m, n), (m + 1, n)), gridAdj_fst_add m n⟩ :
      gridGraph.edgeSet) = false := by simpa using hc
  obtain ⟨k, hk⟩ := (staircaseConfig_closed_iff _).mp hfalse
  have hval : s((m, n), (m + 1, n)) = s(((k : ℤ), 0), ((k : ℤ) + 1, 0)) := by
    have := congrArg Subtype.val hk
    simpa [staircaseEdge] using this
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Prod.mk.injEq] at h1 h2 <;> omega

/-- Every vertical lattice edge is open. -/
lemma vert_open (m n : ℤ) :
    staircaseConfig (⟨s((m, n), (m, n + 1)), gridAdj_snd_add m n⟩ :
      gridGraph.edgeSet) = true := by
  by_contra hc
  have hfalse : staircaseConfig (⟨s((m, n), (m, n + 1)), gridAdj_snd_add m n⟩ :
      gridGraph.edgeSet) = false := by simpa using hc
  obtain ⟨k, hk⟩ := (staircaseConfig_closed_iff _).mp hfalse
  have hval : s((m, n), (m, n + 1)) = s(((k : ℤ), 0), ((k : ℤ) + 1, 0)) := by
    have := congrArg Subtype.val hk
    simpa [staircaseEdge] using this
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Prod.mk.injEq] at h1 h2 <;> omega

/-! ## Open walks along a row and along a column -/

/-- An open walk along a row, to the right, as long as the row stays below the
bound `c` where the edges are known open. -/
lemma row_open_of_le {n : ℤ} {ω : gridGraph.edgeSet → Bool} {c : ℤ}
    (hopen : ∀ m : ℤ, m < c → ω (⟨s((m, n), (m + 1, n)), gridAdj_fst_add m n⟩ :
      gridGraph.edgeSet) = true) :
    ∀ a b : ℤ, a ≤ b → b ≤ c →
      OpenConnected gridGraph ω Set.univ ((a, n) : GridV) ((b, n) : GridV) := by
  intro a b hab hbc
  obtain ⟨d, hd⟩ : ∃ d : ℕ, b = a + (d : ℤ) := ⟨(b - a).toNat, by omega⟩
  have key : ∀ d : ℕ, ∀ a : ℤ, a + (d : ℤ) ≤ c →
      OpenConnected gridGraph ω Set.univ ((a, n) : GridV) ((a + (d : ℤ), n) : GridV) := by
    intro d
    induction d with
    | zero =>
        intro a _
        simpa using OpenConnected.refl (G := gridGraph) ω Set.univ ((a, n) : GridV)
    | succ d ih =>
        intro a ha
        have hstep : OpenConnected gridGraph ω Set.univ
            (((a + (d : ℤ)), n) : GridV) ((((a + (d : ℤ)) + 1), n) : GridV) :=
          OpenConnected.of_adj (gridAdj_fst_add (a + (d : ℤ)) n) (Set.mem_univ _)
            (hopen (a + (d : ℤ)) (by omega))
        have := (ih a (by omega)).trans hstep
        push_cast at this ⊢
        simpa [add_assoc] using this
  rw [hd]
  exact key d a (by omega)

/-- An open walk along a row, in either direction. -/
lemma row_open {n : ℤ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ m : ℤ, ω (⟨s((m, n), (m + 1, n)), gridAdj_fst_add m n⟩ :
      gridGraph.edgeSet) = true) (a b : ℤ) :
    OpenConnected gridGraph ω Set.univ ((a, n) : GridV) ((b, n) : GridV) := by
  rcases le_or_gt a b with h | h
  · exact row_open_of_le (c := b) (fun m _ => hopen m) a b h le_rfl
  · exact openConnected_symm (row_open_of_le (c := a) (fun m _ => hopen m) b a h.le le_rfl)

/-- An open walk along a column, upwards, below the bound `c`. -/
lemma col_open_of_le {m : ℤ} {ω : gridGraph.edgeSet → Bool} {c : ℤ}
    (hopen : ∀ n : ℤ, n < c → ω (⟨s((m, n), (m, n + 1)), gridAdj_snd_add m n⟩ :
      gridGraph.edgeSet) = true) :
    ∀ a b : ℤ, a ≤ b → b ≤ c →
      OpenConnected gridGraph ω Set.univ ((m, a) : GridV) ((m, b) : GridV) := by
  intro a b hab hbc
  obtain ⟨d, hd⟩ : ∃ d : ℕ, b = a + (d : ℤ) := ⟨(b - a).toNat, by omega⟩
  have key : ∀ d : ℕ, ∀ a : ℤ, a + (d : ℤ) ≤ c →
      OpenConnected gridGraph ω Set.univ ((m, a) : GridV) ((m, a + (d : ℤ)) : GridV) := by
    intro d
    induction d with
    | zero =>
        intro a _
        simpa using OpenConnected.refl (G := gridGraph) ω Set.univ ((m, a) : GridV)
    | succ d ih =>
        intro a ha
        have hstep : OpenConnected gridGraph ω Set.univ
            ((m, (a + (d : ℤ))) : GridV) ((m, ((a + (d : ℤ)) + 1)) : GridV) :=
          OpenConnected.of_adj (gridAdj_snd_add m (a + (d : ℤ))) (Set.mem_univ _)
            (hopen (a + (d : ℤ)) (by omega))
        have := (ih a (by omega)).trans hstep
        push_cast at this ⊢
        simpa [add_assoc] using this
  rw [hd]
  exact key d a (by omega)

/-- An open walk along a column, in either direction. -/
lemma col_open {m : ℤ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ n : ℤ, ω (⟨s((m, n), (m, n + 1)), gridAdj_snd_add m n⟩ :
      gridGraph.edgeSet) = true) (a b : ℤ) :
    OpenConnected gridGraph ω Set.univ ((m, a) : GridV) ((m, b) : GridV) := by
  rcases le_or_gt a b with h | h
  · exact col_open_of_le (c := b) (fun n _ => hopen n) a b h le_rfl
  · exact openConnected_symm (col_open_of_le (c := a) (fun n _ => hopen n) b a h.le le_rfl)

/-! ## Every vertex reaches the origin -/

/-- Horizontal edges at a fixed nonzero row are open in the staircase
configuration. -/
lemma row_hopen_of_ne {n : ℤ} (hn : n ≠ 0) :
    ∀ m : ℤ, staircaseConfig (⟨s((m, n), (m + 1, n)), gridAdj_fst_add m n⟩ :
      gridGraph.edgeSet) = true :=
  fun m => horiz_open (Or.inl hn)

/-- Vertical edges in the staircase configuration are open. -/
lemma col_hopen (m : ℤ) :
    ∀ n : ℤ, staircaseConfig (⟨s((m, n), (m, n + 1)), gridAdj_snd_add m n⟩ :
      gridGraph.edgeSet) = true :=
  fun n => vert_open m n

/-- Every lattice vertex is open-connected to the origin. -/
theorem staircase_connected (x : GridV) :
    OpenConnected gridGraph staircaseConfig Set.univ x ((0, 0) : GridV) := by
  obtain ⟨m, n⟩ := x
  by_cases hn : n = 0
  · subst hn
    by_cases hm : 0 < m
    · -- over the top of the axis: up, along row one, and back down
      have hup : OpenConnected gridGraph staircaseConfig Set.univ ((m, 0) : GridV) ((m, 1) : GridV) :=
        OpenConnected.of_adj (gridAdj_snd_add m 0) (Set.mem_univ _) (vert_open m 0)
      have hrow : OpenConnected gridGraph staircaseConfig Set.univ ((m, 1) : GridV) ((0, 1) : GridV) :=
        row_open (row_hopen_of_ne (by norm_num : (1 : ℤ) ≠ 0)) m 0
      have hdown : OpenConnected gridGraph staircaseConfig Set.univ ((0, 1) : GridV) ((0, 0) : GridV) :=
        col_open (col_hopen 0) 1 0
      exact hup.trans (hrow.trans hdown)
    · -- along the nonpositive part of the `x`-axis
      have hrow : OpenConnected gridGraph staircaseConfig Set.univ ((m, 0) : GridV) ((0, 0) : GridV) :=
        row_open_of_le (n := 0) (c := 0) (fun j hj => horiz_open (Or.inr hj)) m 0
          (by omega) le_rfl
      exact hrow
  · -- off the axis: along the row to the `y`-axis, then along the axis
    have hrow : OpenConnected gridGraph staircaseConfig Set.univ ((m, n) : GridV) ((0, n) : GridV) :=
      row_open (row_hopen_of_ne hn) m 0
    have hcol : OpenConnected gridGraph staircaseConfig Set.univ ((0, n) : GridV) ((0, 0) : GridV) :=
      col_open (col_hopen 0) n 0
    exact hrow.trans hcol

/-- **The staircase configuration has at most one infinite open cluster.** -/
theorem staircase_globalAtMostOne : GlobalAtMostOne gridGraph staircaseConfig := by
  intro x y _ _
  exact (staircase_connected x).trans (openConnected_symm (staircase_connected y))

/-! ## The closed set is infinite -/

lemma staircaseEdge_injective : Function.Injective staircaseEdge := by
  intro j k hjk
  have hval : s(((j : ℤ), 0), ((j : ℤ) + 1, 0)) = s(((k : ℤ), 0), ((k : ℤ) + 1, 0)) := by
    have := congrArg Subtype.val hjk
    simpa [staircaseEdge] using this
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Prod.mk.injEq] at h1 h2 <;> omega

/-- The staircase configuration closes infinitely many edges. -/
theorem staircase_infinite_closed :
    ¬ ({e : gridGraph.edgeSet | staircaseConfig e = false}).Finite := by
  intro hfin
  have hrange : (Set.range staircaseEdge).Finite :=
    hfin.subset (by
      rintro e ⟨k, rfl⟩
      exact (staircaseConfig_closed_iff _).mpr ⟨k, rfl⟩)
  exact Set.infinite_range_of_injective staircaseEdge_injective hrange

/-! ## The complete witness -/

/-- **The staircase configuration is a positive instance of the planar target's
conclusion which the fixed `ℓ¹` shell method cannot reach.**  It has no infinite
dual-open cluster, infinitely many closed edges, a closed edge in every diamond
shell, and at most one infinite primal-open cluster. -/
theorem staircase_witness :
    FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv staircaseConfig) ∧
      GlobalAtMostOne gridGraph staircaseConfig ∧
      ¬ ({e : gridGraph.edgeSet | staircaseConfig e = false}).Finite ∧
      (∀ k : ℕ, ∃ e ∈ diamondCut k, staircaseConfig e = false) :=
  ⟨staircase_dual_nonpercolation, staircase_globalAtMostOne, staircase_infinite_closed,
    exists_closed_mem_diamondCut⟩

end FK.PlaneTopology.StaircaseConnected

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.StaircaseConnected.horiz_open
#print axioms FK.PlaneTopology.StaircaseConnected.vert_open
#print axioms FK.PlaneTopology.StaircaseConnected.staircase_connected
#print axioms FK.PlaneTopology.StaircaseConnected.staircase_globalAtMostOne
#print axioms FK.PlaneTopology.StaircaseConnected.staircase_infinite_closed
#print axioms FK.PlaneTopology.StaircaseConnected.staircase_witness
