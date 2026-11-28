import FK.BurtonKeaneGeometry
import FK.ForestMarkedCount

/-!
# An obstruction to naïve multi-centre encounter-forest pruning

The six-vertex graph below is a triangle with one pendant vertex at each
triangle vertex. Its three triangle vertices have genuine open
`ThreeWayArms` at scale one, using their three incident edges. Nevertheless,
no subgraph in which all three have degree at least three is acyclic: degree
three forces every edge incident to each centre, and in particular forces the
triangle. Thus arbitrary union-and-cycle-deletion cannot feed the hypotheses
of `markedCount_le_of_encounterForest` from the present `ThreeWayArms` data.

This is a finite, fixed-scale obstruction to that proposed construction only.
It is not a counterexample to Burton--Keane uniqueness, and it does not use or
produce a Følner sequence, an invariant law, or a global percolation theorem.
-/

open scoped Classical BigOperators
open Finset
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane.MultiCentreObstruction

/-- Directed representatives of three triangle edges and three pendant edges.
`SimpleGraph.fromRel` supplies their reverses and removes diagonal loops. -/
def lollipopRelation (v w : Fin 6) : Prop :=
  (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 0) ∨
  (v = 0 ∧ w = 3) ∨ (v = 1 ∧ w = 4) ∨ (v = 2 ∧ w = 5)

/-- A triangle on `0,1,2`, with pendant vertices `3,4,5` respectively. -/
def lollipopGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel lollipopRelation

instance : DecidableRel lollipopGraph.Adj := by
  unfold lollipopGraph lollipopRelation
  infer_instance

/-- Three adjacent endpoints that are pairwise distinct and distinct from the
centre give one-edge `ThreeWayArms` at scale one in the all-open configuration. -/
lemma threeWayArms_one_of_adj {V : Type*} {G : SimpleGraph V} {y a b c : V}
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ThreeWayArms G (fun _ => true) y 1 := by
  refine ⟨a, b, c, hya.toWalk, hyb.toWalk, hyc.toWalk, ?_, ?_, ?_,
    hya.isPath_toWalk, hyb.isPath_toWalk, hyc.isPath_toWalk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G.dist_eq_one_iff_adj.mpr hya]
  · rw [G.dist_eq_one_iff_adj.mpr hyb]
  · rw [G.dist_eq_one_iff_adj.mpr hyc]
  · intro d hd
    exact ⟨Set.mem_univ _, rfl⟩
  · intro d hd
    exact ⟨Set.mem_univ _, rfl⟩
  · intro d hd
    exact ⟨Set.mem_univ _, rfl⟩
  · intro z hza hzb
    have hza' : z = y ∨ z = a := by simpa using hza
    have hzb' : z = y ∨ z = b := by simpa using hzb
    rcases hza' with hzy | hza
    · exact hzy
    · rcases hzb' with hzy | hzb
      · exact hzy
      · exact (hab (hza.symm.trans hzb)).elim
  · intro z hza hzc
    have hza' : z = y ∨ z = a := by simpa using hza
    have hzc' : z = y ∨ z = c := by simpa using hzc
    rcases hza' with hzy | hza
    · exact hzy
    · rcases hzc' with hzy | hzc
      · exact hzy
      · exact (hac (hza.symm.trans hzc)).elim
  · intro z hzb hzc
    have hzb' : z = y ∨ z = b := by simpa using hzb
    have hzc' : z = y ∨ z = c := by simpa using hzc
    rcases hzb' with hzy | hzb
    · exact hzy
    · rcases hzc' with hzy | hzc
      · exact hzy
      · exact (hbc (hzb.symm.trans hzc)).elim

/-- Centre `0` has three actual open arms, with endpoints `1`, `2`, and `3`. -/
theorem threeWayArms_zero :
    ThreeWayArms lollipopGraph (fun _ => true) 0 1 := by
  apply threeWayArms_one_of_adj (a := 1) (b := 2) (c := 3) <;>
    decide

/-- Centre `1` has three actual open arms, with endpoints `0`, `2`, and `4`. -/
theorem threeWayArms_one :
    ThreeWayArms lollipopGraph (fun _ => true) 1 1 := by
  apply threeWayArms_one_of_adj (a := 0) (b := 2) (c := 4) <;>
    decide

/-- Centre `2` has three actual open arms, with endpoints `0`, `1`, and `5`. -/
theorem threeWayArms_two :
    ThreeWayArms lollipopGraph (fun _ => true) 2 1 := by
  apply threeWayArms_one_of_adj (a := 0) (b := 1) (c := 5) <;>
    decide

/-- If a subgraph has at least the ambient degree at `v`, all ambient
neighbours of `v` are retained. -/
lemma neighborFinset_eq_of_le_of_degree_le {V : Type*} [Fintype V]
    {T G : SimpleGraph V} [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hTG : T ≤ G) {v : V} (hdegree : G.degree v ≤ T.degree v) :
    T.neighborFinset v = G.neighborFinset v := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hTG hw
  · exact hdegree

lemma degree_zero : lollipopGraph.degree 0 = 3 := by decide
lemma degree_one : lollipopGraph.degree 1 = 3 := by decide
lemma degree_two : lollipopGraph.degree 2 = 3 := by decide

/-- The three centre-degree requirements force the whole triangle, so no such
subgraph is acyclic. Pendant edges are forced as well, although the displayed
cycle already gives the contradiction. -/
theorem not_isAcyclic_of_degree_three (T : SimpleGraph (Fin 6))
    [DecidableRel T.Adj] (hTG : T ≤ lollipopGraph)
    (h0 : 3 ≤ T.degree 0) (h1 : 3 ≤ T.degree 1) (h2 : 3 ≤ T.degree 2) :
    ¬ T.IsAcyclic := by
  classical
  have hN0 : T.neighborFinset 0 = lollipopGraph.neighborFinset 0 :=
    neighborFinset_eq_of_le_of_degree_le hTG (degree_zero ▸ h0)
  have hN1 : T.neighborFinset 1 = lollipopGraph.neighborFinset 1 :=
    neighborFinset_eq_of_le_of_degree_le hTG (degree_one ▸ h1)
  have hN2 : T.neighborFinset 2 = lollipopGraph.neighborFinset 2 :=
    neighborFinset_eq_of_le_of_degree_le hTG (degree_two ▸ h2)
  have h01 : T.Adj 0 1 := by
    rw [← SimpleGraph.mem_neighborFinset, hN0]
    decide
  have h12 : T.Adj 1 2 := by
    rw [← SimpleGraph.mem_neighborFinset, hN1]
    decide
  have h20 : T.Adj 2 0 := by
    rw [← SimpleGraph.mem_neighborFinset, hN2]
    decide
  let c : T.Walk 0 0 := SimpleGraph.Walk.cons h01
    (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))
  have hc : c.IsCycle := by
    simp [c, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  exact fun hacyclic => hacyclic c hc

/-- Packaged obstruction: the all-open six-vertex configuration has the three
per-centre arm witnesses, yet admits no acyclic spanning subgraph satisfying
the simultaneous branch-degree requirement. -/
theorem arms_and_no_encounter_forest :
    (ThreeWayArms lollipopGraph (fun _ => true) 0 1 ∧
      ThreeWayArms lollipopGraph (fun _ => true) 1 1 ∧
      ThreeWayArms lollipopGraph (fun _ => true) 2 1) ∧
    ∀ (T : SimpleGraph (Fin 6)) [DecidableRel T.Adj], T ≤ lollipopGraph →
      3 ≤ T.degree 0 → 3 ≤ T.degree 1 → 3 ≤ T.degree 2 → ¬ T.IsAcyclic := by
  exact ⟨⟨threeWayArms_zero, threeWayArms_one, threeWayArms_two⟩,
    not_isAcyclic_of_degree_three⟩

end FK.BurtonKeane.MultiCentreObstruction

#print axioms FK.BurtonKeane.MultiCentreObstruction.threeWayArms_one_of_adj
#print axioms FK.BurtonKeane.MultiCentreObstruction.threeWayArms_zero
#print axioms FK.BurtonKeane.MultiCentreObstruction.threeWayArms_one
#print axioms FK.BurtonKeane.MultiCentreObstruction.threeWayArms_two
#print axioms FK.BurtonKeane.MultiCentreObstruction.neighborFinset_eq_of_le_of_degree_le
#print axioms FK.BurtonKeane.MultiCentreObstruction.not_isAcyclic_of_degree_three
#print axioms FK.BurtonKeane.MultiCentreObstruction.arms_and_no_encounter_forest
