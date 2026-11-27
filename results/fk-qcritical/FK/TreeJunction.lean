import FK.ClusterCover
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Three-way junctions in trees

This file proves the graph-theoretic ingredient of the Burton--Keane
encounter-point construction.  Any three vertices in a tree have a junction
and three internally vertex-disjoint paths to them.  Repeated terminals are
allowed; the corresponding branches are then empty.
-/

open scoped Classical

namespace SimpleGraph

universe u

variable {V : Type u} {T : SimpleGraph V}

/-- **Three-way junctions in a tree.**  The three returned paths have only
`y` in common, pairwise.  No distinctness assumption on `a`, `b`, and `c` is
needed. -/
theorem IsTree.exists_three_way_junction (hT : T.IsTree) (a b c : V) :
    ∃ y : V, ∃ pa : T.Walk y a, ∃ pb : T.Walk y b, ∃ pc : T.Walk y c,
      pa.IsPath ∧ pb.IsPath ∧ pc.IsPath ∧
      (∀ z ∈ pa.support, z ∈ pb.support → z = y) ∧
      (∀ z ∈ pa.support, z ∈ pc.support → z = y) ∧
      (∀ z ∈ pb.support, z ∈ pc.support → z = y) := by
  classical
  let p : T.Walk a b := (hT.existsUnique_path a b).choose
  let q : T.Walk a c := (hT.existsUnique_path a c).choose
  have hp : p.IsPath := (hT.existsUnique_path a b).choose_spec.1
  have hq : q.IsPath := (hT.existsUnique_path a c).choose_spec.1
  let P : ℕ → Prop := fun n => p.getVert n ∈ q.support
  have hP0 : P 0 := by
    change p.getVert 0 ∈ q.support
    rw [show p.getVert 0 = a from p.getVert_zero]
    exact q.start_mem_support
  let n := Nat.findGreatest P p.length
  have hn : n ≤ p.length := Nat.findGreatest_le p.length
  have hnP : P n := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hP0
  let y := p.getVert n
  have hyq : y ∈ q.support := hnP
  let pa' := p.take n
  let pb := p.drop n
  let qc' := q.takeUntil y hyq
  let pc := q.dropUntil y hyq
  have hpa' : pa'.IsPath := hp.take n
  have hpb : pb.IsPath := hp.drop n
  have hqc' : qc'.IsPath := hq.takeUntil hyq
  have hpc : pc.IsPath := hq.dropUntil hyq
  have hpre : pa' = qc' := by
    exact (hT.existsUnique_path a y).unique hpa' hqc'
  have hpappend : (pa'.append pb).IsPath := by
    rw [show pa'.append pb = p from p.append_take_drop_eq n]
    exact hp
  have hqappend : (qc'.append pc).IsPath := by
    rw [show qc'.append pc = q from q.take_spec hyq]
    exact hq
  have sep_pre_pb : ∀ z ∈ pa'.support, z ∈ pb.support → z = y := by
    intro z hza hzb
    by_contra hz
    exact (hpappend.ne_of_mem_support_of_append hz hza hzb) rfl
  have sep_pre_pc : ∀ z ∈ pa'.support, z ∈ pc.support → z = y := by
    intro z hza hzc
    rw [hpre] at hza
    by_contra hz
    exact (hqappend.ne_of_mem_support_of_append hz hza hzc) rfl
  have sep_pb_pc : ∀ z ∈ pb.support, z ∈ pc.support → z = y := by
    intro z hzb hzc
    obtain ⟨k, hk, hklen⟩ := Walk.mem_support_iff_exists_getVert.mp hzb
    rw [Walk.drop_getVert] at hk
    have hzq : z ∈ q.support :=
      q.support_dropUntil_subset_support hyq hzc
    have hkle : k ≤ p.length - n := by
      simpa [pb, Walk.drop_length] using hklen
    by_cases hk0 : k = 0
    · subst k
      simpa [y] using hk.symm
    · have hlt : n < n + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk0)
      have hle : n + k ≤ p.length := by omega
      have hnot : ¬ P (n + k) := Nat.findGreatest_is_greatest hlt hle
      exact (hnot (by simpa [P, hk] using hzq)).elim
  refine ⟨y, pa'.reverse, pb, pc, hpa'.reverse, hpb, hpc, ?_, ?_, sep_pb_pc⟩
  · intro z hza hzb
    rw [Walk.support_reverse, List.mem_reverse] at hza
    exact sep_pre_pb z hza hzb
  · intro z hza hzc
    rw [Walk.support_reverse, List.mem_reverse] at hza
    exact sep_pre_pc z hza hzc
