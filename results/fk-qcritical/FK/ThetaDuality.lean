import FK.PlanarMatroid

/-!
# Exact graphic duals of labelled cycles and parallel-edge graphs

This file constructs combinatorial plane-dual pairs without assuming a matroid
identity.  A connected labelled cycle has as its independent edge sets exactly
its proper subsets.  Its two-face dual has two vertices and the same labelled
edges in parallel; its independent edge sets are exactly the sets of cardinal
at most one.  Matroid duality follows from complementary bases.
-/

namespace FK.Finite.PlaneMatroid

universe u v

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

namespace LabelledDualPair

/-- A labelled cycle and its explicit two-face parallel-edge dual. -/
def cyclePair (G : LabelledMultigraph.{u,v}) : LabelledDualPair where
  Vertex := G.Vertex
  Face := Bool
  Edge := G.Edge
  source := G.source
  target := G.target
  dualSource _ := false
  dualTarget _ := true

@[simp] lemma cyclePair_primal (G : LabelledMultigraph.{u,v}) :
    (cyclePair G).primal = G := by
  cases G
  rfl

@[simp] lemma cyclePair_faceDual (G : LabelledMultigraph.{u,v}) :
    (cyclePair G).faceDual = cycleDual G := rfl

/-- In a connected labelled cycle, independent sets are precisely proper sets
of labels.  Loops and two-vertex/two-edge cycles are included. -/
lemma cycle_indep_iff (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle)
    (A : Set G.Edge) : G.cycleMatroid.Indep A ↔ A ≠ Set.univ := by
  rw [G.cycleMatroid_indep]
  constructor
  · intro hA hAU
    subst A
    rw [G.setConfig_univ] at hA
    have hcomp : G.componentCount G.freeBoundary G.allOpen = 1 :=
      componentCount_eq_one_of_preconnected G G.freeBoundary G.allOpen
        hG.nonemptyVertex.some hG.preconnected
    have heuler := G.componentCount_add_openCard_of_free_isOpenForest G.allOpen hA
    rw [hcomp, openCard_allOpen, hG.card_edges] at heuler
    omega
  · intro hA
    apply hG.isOpenForest_of_ne_allOpen
    intro hconfig
    apply hA
    have hset := congrArg G.openEdgeSet hconfig
    simpa using hset

/-- In the two-vertex parallel dual, independent sets have at most one
label.  This proof uses the actual component counts, not a simple-graph
quotient of the labels. -/
lemma cycleDual_indep_iff (G : LabelledMultigraph.{u,v}) (A : Set (cycleDual G).Edge) :
    (cycleDual G).cycleMatroid.Indep A ↔ A.ncard ≤ 1 := by
  simp only [cycleMatroid_indep, isOpenForest_setConfig_iff]
  by_cases hA : A = ∅
  · subst A
    rw [(cycleDual G).setConfig_empty, cycleDual_componentCount_allClosed]
    norm_num [cycleDual]
    change 2 = Fintype.card Bool
    norm_num
  · obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hA
    have heopen : (cycleDual G).setConfig A e = true := by
      simp [setConfig, he]
    rw [cycleDual_componentCount_eq_one G _ e heopen]
    have hcardpos : 0 < A.ncard := (Set.ncard_pos (s := A)).mpr ⟨e, he⟩
    change 1 + A.ncard = 2 ↔ A.ncard ≤ 1
    constructor <;> omega

lemma cycle_nonempty_edge (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle) :
    Nonempty G.Edge := by
  apply Fintype.card_pos_iff.mp
  rw [hG.card_edges]
  exact Fintype.card_pos_iff.mpr hG.nonemptyVertex

/-- A basis of a labelled cycle is the whole cycle minus one labelled edge. -/
lemma cycle_isBase_iff (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle)
    (B : Set G.Edge) : G.cycleMatroid.IsBase B ↔ ∃ e, B = Set.univ \ {e} := by
  constructor
  · intro hB
    have hBI : B ≠ Set.univ := (cycle_indep_iff G hG B).mp hB.indep
    obtain ⟨e, he⟩ := (Set.ne_univ_iff_exists_notMem B).mp hBI
    refine ⟨e, ?_⟩
    have hdep := (hB.insert_dep ⟨Set.mem_univ e, he⟩).not_indep
    have hins : insert e B = Set.univ := by
      by_contra hne
      exact hdep ((cycle_indep_iff G hG _).mpr hne)
    ext f
    by_cases hfe : f = e
    · subst f
      simp [he]
    · have hfins : f ∈ insert e B := hins.symm ▸ Set.mem_univ f
      have hfB : f ∈ B := (Set.mem_insert_iff.mp hfins).resolve_left hfe
      simp [hfe, hfB]
  · rintro ⟨e, rfl⟩
    have hBI : Set.univ \ {e} ≠ (Set.univ : Set G.Edge) := by
      intro h
      have he' : e ∈ Set.univ \ ({e} : Set G.Edge) := by
        rw [h]
        exact Set.mem_univ e
      simp at he'
    apply ((cycle_indep_iff G hG _).mpr hBI).isBase_of_maximal
    intro J hJ hsub
    apply hsub.antisymm
    intro f hf
    by_cases hfe : f = e
    · subst e
      have hins : insert f (Set.univ \ {f}) = (Set.univ : Set G.Edge) := by
        ext a
        by_cases haf : a = f <;> simp [haf]
      have huniv : (Set.univ : Set G.Edge) ⊆ J := by
        rw [← hins]
        exact Set.insert_subset hf hsub
      have hJuniv : J = Set.univ := Set.eq_univ_of_univ_subset huniv
      exact ((cycle_indep_iff G hG J).mp hJ hJuniv).elim
    · simp [hfe]


/-- Bases of the two-face parallel graph are singletons.  Nonemptiness of
`G.Edge` is necessary: the rank-one assertion is false on an empty edge type. -/
lemma cycleDual_isBase_iff (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle)
    (B : Set (cycleDual G).Edge) :
    (cycleDual G).cycleMatroid.IsBase B ↔ ∃ e, B = {e} := by
  constructor
  · intro hB
    have hcardle : B.ncard ≤ 1 := (cycleDual_indep_iff G B).mp hB.indep
    obtain ⟨e⟩ := cycle_nonempty_edge G hG
    have hne : B.Nonempty := by
      obtain ⟨e₀⟩ := cycle_nonempty_edge G hG
      let e : (cycleDual G).Edge := e₀
      have hi : (cycleDual G).cycleMatroid.Indep ({e} : Set (cycleDual G).Edge) :=
        (cycleDual_indep_iff G _).mpr (by rw [Set.ncard_singleton])
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty] at hn
      have hBE : B = {e} := hB.eq_of_subset_indep hi (by
        rw [hn]
        exact Set.empty_subset _)
      have heB : e ∈ B := by
        rw [hBE]
        exact Set.mem_singleton e
      rw [hn] at heB
      exact (Set.notMem_empty e heB).elim
    have hcardpos : 0 < B.ncard := (Set.ncard_pos (s := B)).mpr hne
    exact Set.ncard_eq_one.mp (by omega)
  · rintro ⟨e, rfl⟩
    apply ((cycleDual_indep_iff G _).mpr (by simp)).isBase_of_maximal
    intro J hJ hsub
    apply hsub.antisymm
    intro f hf
    have hsmall : J.Subsingleton :=
      Set.ncard_le_one_iff_subsingleton.mp ((cycleDual_indep_iff G J).mp hJ)
    have heJ : e ∈ J := hsub (Set.mem_singleton e)
    have hfe : f = e := hsmall hf heJ
    simp [hfe]

/-- **Actual matroid duality for a connected labelled cycle.**  No cycle-matroid
identity is assumed: both sides were computed above from the open forests. -/
theorem cycle_dual_cycleMatroid (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle) :
    (G.cycleMatroid)✶ = (cycleDual G).cycleMatroid := by
  apply Matroid.ext_isBase (by
    change (Set.univ : Set G.Edge) = Set.univ
    rfl)
  intro B hB
  rw [Matroid.dual_isBase_iff]
  change G.cycleMatroid.IsBase (Set.univ \ B) ↔
    (cycleDual G).cycleMatroid.IsBase B
  rw [cycle_isBase_iff G hG]
  constructor
  · rintro ⟨e, he⟩
    apply (cycleDual_isBase_iff G hG B).mpr
    refine ⟨e, ?_⟩
    calc
      B = Set.univ \ (Set.univ \ B) := by ext; simp
      _ = Set.univ \ (Set.univ \ {e}) := congrArg (fun S : Set G.Edge => Set.univ \ S) he
      _ = {e} := by ext; simp
  · intro hright
    obtain ⟨e, rfl⟩ := (cycleDual_isBase_iff G hG B).mp hright
    exact ⟨e, rfl⟩

/-- Every all-open parallel graph with at least one edge is preconnected. -/
lemma cycleDual_allOpen_preconnected (G : LabelledMultigraph.{u,v}) (e : G.Edge) :
    ((cycleDual G).connectionGraph (cycleDual G).freeBoundary
      (cycleDual G).allOpen).Preconnected := by
  have hadj : ((cycleDual G).connectionGraph (cycleDual G).freeBoundary
      (cycleDual G).allOpen).Adj false true := by
    refine ⟨Bool.false_ne_true, Or.inr ⟨e, by simp [allOpen], ?_⟩⟩
    simp [cycleDual, Joins]
  intro u v
  change Bool at u v
  cases u <;> cases v
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

/-- An explicit `GraphicDualCertificate` for every connected labelled cycle. -/
theorem graphicDualCertificate_cycle (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle) :
    (cyclePair G).GraphicDualCertificate where
  dual_cycleMatroid := by
    change (G.cycleMatroid)✶ = (cycleDual G).cycleMatroid
    exact cycle_dual_cycleMatroid G hG
  nonemptyFace := ⟨false⟩
  allOpen_preconnected := by
    obtain ⟨e⟩ := cycle_nonempty_edge G hG
    exact cycleDual_allOpen_preconnected G e

/-- The same labelled edge type with the primal and facial endpoints exchanged. -/
def parallelPair (G : LabelledMultigraph.{u,v}) : LabelledDualPair where
  Vertex := Bool
  Face := G.Vertex
  Edge := G.Edge
  source _ := false
  target _ := true
  dualSource := G.source
  dualTarget := G.target

@[simp] lemma parallelPair_primal (G : LabelledMultigraph.{u,v}) :
    (parallelPair G).primal = cycleDual G := rfl

@[simp] lemma parallelPair_faceDual (G : LabelledMultigraph.{u,v}) :
    (parallelPair G).faceDual = G := by
  cases G
  rfl

/-- The reverse orientation: an arbitrary nonempty parallel-edge graph has its
original connected labelled cycle as an exact graphic dual. -/
theorem graphicDualCertificate_parallel (G : LabelledMultigraph.{u,v}) (hG : G.IsLabelledCycle) :
    (parallelPair G).GraphicDualCertificate where
  dual_cycleMatroid := by
    change ((cycleDual G).cycleMatroid)✶ = G.cycleMatroid
    have hd := congrArg Matroid.dual (cycle_dual_cycleMatroid G hG)
    rw [Matroid.dual_dual] at hd
    exact hd.symm
  nonemptyFace := hG.nonemptyVertex
  allOpen_preconnected := hG.preconnected


/-- The one-vertex, one-labelled-edge loop is the smallest labelled cycle.
Its explicit plane dual has two face vertices joined by one labelled edge. -/
def oneEdgeLoopCycle : LabelledMultigraph where
  Vertex := PUnit
  Edge := PUnit
  source _ := PUnit.unit
  target _ := PUnit.unit

lemma isLabelledCycle_oneEdgeLoopCycle : oneEdgeLoopCycle.IsLabelledCycle := by
  refine ⟨⟨PUnit.unit⟩, rfl, ?_, ?_⟩
  · intro u v
    cases u
    cases v
    exact SimpleGraph.Reachable.refl _
  · intro ω hω e he
    obtain ⟨f, hf⟩ := oneEdgeLoopCycle.exists_closed_of_ne_allOpen hω
    have hfe : f = e := by cases f; cases e; rfl
    subst f
    rw [hf] at he
    contradiction

/-- A fully explicit certificate for the one-edge loop and its two-face dual. -/
theorem graphicDualCertificate_oneEdgeLoopCycle :
    (cyclePair oneEdgeLoopCycle).GraphicDualCertificate :=
  graphicDualCertificate_cycle oneEdgeLoopCycle isLabelledCycle_oneEdgeLoopCycle

/-- A fully explicit certificate for the smallest non-simple cycle with two
parallel labelled edges. -/
theorem graphicDualCertificate_twoEdgeCycle :
    (cyclePair twoEdgeCycle).GraphicDualCertificate :=
  graphicDualCertificate_cycle twoEdgeCycle isLabelledCycle_twoEdgeCycle

end LabelledDualPair
end FK.Finite.PlaneMatroid
