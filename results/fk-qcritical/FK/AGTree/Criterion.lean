import FK.AGTree.Model

/-!
# Percolation and nonpercolation criteria on the two-class tree
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal unitInterval Topology

/-- Number of letters of each class. -/
def dcount : Fin 2 → ℕ := ![3, 2]

lemma dcount_zero : dcount 0 = 3 := rfl
lemma dcount_one : dcount 1 = 2 := rfl

lemma card_class (j : Fin 2) : ((Finset.univ : Finset A).filter (fun a => acls a = j)).card =
    dcount j := by
  fin_cases j
  · decide
  · decide

lemma card_class_add (j : Fin 2) (x : A) :
    (((Finset.univ : Finset A).filter (fun a => acls a = j)).erase x).card =
      dcount j - (if acls x = j then 1 else 0) := by
  by_cases hx : acls x = j
  · have hmem : x ∈ (Finset.univ : Finset A).filter (fun a => acls a = j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
    rw [if_pos hx, Finset.card_erase_of_mem hmem, card_class]
  · have hmem : x ∉ (Finset.univ : Finset A).filter (fun a => acls a = j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
    rw [if_neg hx, Finset.erase_eq_of_notMem hmem, card_class]
    simp

/-- Exact count of valid letters of a given class. -/
lemma card_valid_class {v : V} (hv : v.w ≠ []) (j : Fin 2) :
    ((Finset.univ : Finset A).filter (fun a => v.Valid a ∧ acls a = j)).card =
      dcount j - (if acls (v.w.getLast hv) = j then 1 else 0) := by
  have hset : (Finset.univ.filter (fun a => v.Valid a ∧ acls a = j)) =
      ((Finset.univ.filter (fun a => acls a = j)).erase (v.w.getLast hv)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hval, hcl⟩
      refine ⟨?_, hcl⟩
      rw [V.Valid] at hval
      rcases hval with h | h
      · exact absurd h hv
      · intro he
        exact h (by rw [he, List.getLast?_eq_some_getLast hv])
    · rintro ⟨hne, hcl⟩
      refine ⟨?_, hcl⟩
      rw [V.Valid]
      refine Or.inr ?_
      rw [List.getLast?_eq_some_getLast hv]
      exact fun he => hne (by simpa using he.symm)
  rw [hset, card_class_add]

lemma card_valid_root (j : Fin 2) :
    ((Finset.univ : Finset A).filter (fun a => V.root.Valid a ∧ acls a = j)).card = dcount j := by
  fin_cases j <;> decide

/-- Monotonicity of the event probability. -/
lemma pr_mono (r : Fin 2 → unitInterval) {A B : Set (G.edgeSet → Bool)} (h : A ⊆ B) :
    pr r A ≤ pr r B := by
  rw [pr, pr]; exact measureReal_mono h (by simp)

lemma pr_fwd_zero (r : Fin 2 → unitInterval) (u : V) : pr r {ω | Fwd ω u 0} = 1 := by
  have h : {ω : G.edgeSet → Bool | Fwd ω u 0} = Set.univ := by
    ext ω; simp [fwd_zero]
  rw [h, pr_univ]

lemma pr_cluster_tendsto (r : Fin 2 → unitInterval) (u : V) :
    Tendsto (fun n => pr r {ω : G.edgeSet → Bool | Fwd ω u n}) atTop
      (𝓝 (pr r {ω | Cluster ω u})) := by
  have h1 := tendsto_measure_iInter_atTop (μ := law r)
    (s := fun n => {ω : G.edgeSet → Bool | Fwd ω u n})
    (fun n => (measurableSet_fwd u n).nullMeasurableSet) (cluster_anti u) ⟨0, by simp⟩
  have h2 : Tendsto (fun n => ((law r) {ω : G.edgeSet → Bool | Fwd ω u n}).toReal) atTop
      (𝓝 (((law r) (⋂ n, {ω : G.edgeSet → Bool | Fwd ω u n})).toReal)) :=
    ENNReal.tendsto_toReal (by simp) |>.comp h1
  have h3 : pr r {ω : G.edgeSet → Bool | Cluster ω u} =
      ((law r) (⋂ n, {ω : G.edgeSet → Bool | Fwd ω u n})).toReal := by
    rw [← cluster_eq_iInter]
    rfl
  rw [h3]
  exact h2

end Ultra
