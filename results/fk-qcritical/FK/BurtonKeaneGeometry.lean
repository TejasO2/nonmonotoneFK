import FK.TreeJunction

/-!
# Finite-scale three-way arms and splicing

Deterministic graph geometry for the Burton--Keane encounter-point argument.
The paths produced here are open in a prescribed percolation configuration and
remain open after pruning with `Walk.toPath`.
-/

open scoped Classical
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane

universe u

variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- Pruning preserves openness of a walk. -/
theorem isOpenIn_toPath [DecidableEq V] {A : Set (Sym2 V)} {x z : V}
    (p : G.Walk x z) (hp : IsOpenIn ω A p) :
    IsOpenIn ω A (p.toPath : G.Walk x z) := by
  intro d hd
  exact hp d (p.darts_toPath_subset_darts hd)

/-- Three open simple paths from `y`, pairwise meeting only at `y`, with
endpoints at distance at least `n`. -/
def ThreeWayArms (G : SimpleGraph V) (ω : G.edgeSet → Bool) (y : V) (n : ℕ) :
    Prop :=
  ∃ a b c : V, ∃ pa : G.Walk y a, ∃ pb : G.Walk y b, ∃ pc : G.Walk y c,
    n ≤ G.dist y a ∧ n ≤ G.dist y b ∧ n ≤ G.dist y c ∧
    pa.IsPath ∧ pb.IsPath ∧ pc.IsPath ∧
    IsOpenIn ω Set.univ pa ∧ IsOpenIn ω Set.univ pb ∧ IsOpenIn ω Set.univ pc ∧
    (∀ z ∈ pa.support, z ∈ pb.support → z = y) ∧
    (∀ z ∈ pa.support, z ∈ pc.support → z = y) ∧
    (∀ z ∈ pb.support, z ∈ pc.support → z = y)

/-- Splice three junction branches to paths in three separated exterior
regions.  The hypotheses forbid all cross intersections: two junction paths
may meet only at `y`, a junction path and another exterior path may not meet,
and two exterior paths may not meet. -/
theorem threeWayArms_splice [DecidableEq V] (y : V) (n : ℕ)
    {a b c a' b' c' : V}
    (pa : G.Walk y a) (pb : G.Walk y b) (pc : G.Walk y c)
    (qa : G.Walk a a') (qb : G.Walk b b') (qc : G.Walk c c')
    (hpa : IsOpenIn ω Set.univ pa) (hpb : IsOpenIn ω Set.univ pb)
    (hpc : IsOpenIn ω Set.univ pc)
    (hqa : IsOpenIn ω Set.univ qa) (hqb : IsOpenIn ω Set.univ qb)
    (hqc : IsOpenIn ω Set.univ qc)
    (hab : ∀ z ∈ pa.support, z ∈ pb.support → z = y)
    (hac : ∀ z ∈ pa.support, z ∈ pc.support → z = y)
    (hbc : ∀ z ∈ pb.support, z ∈ pc.support → z = y)
    (ha_b : ∀ z ∈ pa.support, z ∈ qb.support → False)
    (ha_c : ∀ z ∈ pa.support, z ∈ qc.support → False)
    (hb_a : ∀ z ∈ pb.support, z ∈ qa.support → False)
    (hb_c : ∀ z ∈ pb.support, z ∈ qc.support → False)
    (hc_a : ∀ z ∈ pc.support, z ∈ qa.support → False)
    (hc_b : ∀ z ∈ pc.support, z ∈ qb.support → False)
    (hAB : ∀ z ∈ qa.support, z ∈ qb.support → False)
    (hAC : ∀ z ∈ qa.support, z ∈ qc.support → False)
    (hBC : ∀ z ∈ qb.support, z ∈ qc.support → False)
    (hna : n ≤ G.dist y a') (hnb : n ≤ G.dist y b') (hnc : n ≤ G.dist y c') :
    ThreeWayArms G ω y n := by
  let ra : G.Walk y a' := (pa.append qa).toPath
  let rb : G.Walk y b' := (pb.append qb).toPath
  let rc : G.Walk y c' := (pc.append qc).toPath
  have hra : IsOpenIn ω Set.univ ra :=
    isOpenIn_toPath _ (isOpenIn_append.mpr ⟨hpa, hqa⟩)
  have hrb : IsOpenIn ω Set.univ rb :=
    isOpenIn_toPath _ (isOpenIn_append.mpr ⟨hpb, hqb⟩)
  have hrc : IsOpenIn ω Set.univ rc :=
    isOpenIn_toPath _ (isOpenIn_append.mpr ⟨hpc, hqc⟩)
  have mem_ra : ∀ z ∈ ra.support, z ∈ pa.support ∨ z ∈ qa.support := by
    intro z hz
    have hz' := SimpleGraph.Walk.support_toPath_subset_support (pa.append qa) hz
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hz'
    rcases hz' with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr (List.mem_of_mem_tail hz')
  have mem_rb : ∀ z ∈ rb.support, z ∈ pb.support ∨ z ∈ qb.support := by
    intro z hz
    have hz' := SimpleGraph.Walk.support_toPath_subset_support (pb.append qb) hz
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hz'
    rcases hz' with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr (List.mem_of_mem_tail hz')
  have mem_rc : ∀ z ∈ rc.support, z ∈ pc.support ∨ z ∈ qc.support := by
    intro z hz
    have hz' := SimpleGraph.Walk.support_toPath_subset_support (pc.append qc) hz
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hz'
    rcases hz' with hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr (List.mem_of_mem_tail hz')
  have sAB : ∀ z ∈ ra.support, z ∈ rb.support → z = y := by
    intro z hza hzb
    rcases mem_ra z hza with hpa' | hqa'
    · rcases mem_rb z hzb with hpb' | hqb'
      · exact hab z hpa' hpb'
      · exact (ha_b z hpa' hqb').elim
    · rcases mem_rb z hzb with hpb' | hqb'
      · exact (hb_a z hpb' hqa').elim
      · exact (hAB z hqa' hqb').elim
  have sAC : ∀ z ∈ ra.support, z ∈ rc.support → z = y := by
    intro z hza hzc
    rcases mem_ra z hza with hpa' | hqa'
    · rcases mem_rc z hzc with hpc' | hqc'
      · exact hac z hpa' hpc'
      · exact (ha_c z hpa' hqc').elim
    · rcases mem_rc z hzc with hpc' | hqc'
      · exact (hc_a z hpc' hqa').elim
      · exact (hAC z hqa' hqc').elim
  have sBC : ∀ z ∈ rb.support, z ∈ rc.support → z = y := by
    intro z hzb hzc
    rcases mem_rb z hzb with hpb' | hqb'
    · rcases mem_rc z hzc with hpc' | hqc'
      · exact hbc z hpb' hpc'
      · exact (hb_c z hpb' hqc').elim
    · rcases mem_rc z hzc with hpc' | hqc'
      · exact (hc_b z hpc' hqb').elim
      · exact (hBC z hqb' hqc').elim
  exact ⟨a', b', c', ra, rb, rc, hna, hnb, hnc,
    (pa.append qa).toPath.isPath, (pb.append qb).toPath.isPath,
    (pc.append qc).toPath.isPath, hra, hrb, hrc, sAB, sAC, sBC⟩
