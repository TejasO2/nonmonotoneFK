import FK.BurtonKeaneGeometry

/-!
# All-scales arms do not imply that arbitrary unions can be pruned

A triangle carries one infinite simple ray at each vertex. At each triangle
vertex and at every scale, the three arms go along its own ray and through the
other two triangle vertices to their rays. The arms are genuine simple paths,
pairwise disjoint away from their centre, and their endpoints are arbitrarily
far away. The triangle nevertheless remains a degree-three obstruction to
naïve union-and-prune constructions. This file checks both the arm
construction and the no-forest statement for locally finite spanning subgraphs.
A smaller six-vertex finite version is in `MultiCentreForestObstruction.lean`.
-/

open scoped Classical
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane.MultiCentreObstruction.AllScale

abbrev Vertex := Fin 3 ⊕ (Fin 3 × ℕ)
abbrev Graph := SimpleGraph Vertex

abbrev core (i : Fin 3) : Vertex := .inl i
abbrev ray (i : Fin 3) (n : ℕ) : Vertex := .inr (i, n)

/-- The complete graph on the three core vertices, with a private copy of the
natural-number ray attached at `ray i 0` to core `i`. -/
def triangleWithRays : Graph where
  Adj
    | .inl i, .inl j => i ≠ j
    | .inl i, .inr (j, n) => i = j ∧ n = 0
    | .inr (i, n), .inl j => i = j ∧ n = 0
    | .inr (i, n), .inr (j, m) => i = j ∧ (m = n + 1 ∨ n = m + 1)
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all <;> omega⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

@[simp] lemma core_adj_core {i j : Fin 3} :
    triangleWithRays.Adj (core i) (core j) ↔ i ≠ j := Iff.rfl
@[simp] lemma core_adj_ray {i j : Fin 3} {n : ℕ} :
    triangleWithRays.Adj (core i) (ray j n) ↔ i = j ∧ n = 0 := Iff.rfl
@[simp] lemma ray_adj_core {i j : Fin 3} {n : ℕ} :
    triangleWithRays.Adj (ray i n) (core j) ↔ i = j ∧ n = 0 := Iff.rfl
@[simp] lemma ray_adj_ray {i j : Fin 3} {n m : ℕ} :
    triangleWithRays.Adj (ray i n) (ray j m) ↔
      i = j ∧ (m = n + 1 ∨ n = m + 1) := Iff.rfl

/-- The short prefix from core `i` to the start of ray `j`: direct if `i=j`,
and through core `j` otherwise. -/
def initialArm (i j : Fin 3) : triangleWithRays.Walk (core i) (ray j 0) :=
  if h : i = j then
    (show triangleWithRays.Adj (core i) (ray j 0) by simp [h]).toWalk
  else
    SimpleGraph.Walk.cons
      (show triangleWithRays.Adj (core i) (core j) by simpa using h)
      (show triangleWithRays.Adj (core j) (ray j 0) by simp).toWalk

/-- Go to the start of ray `j` and then follow it to index `n`. -/
def armWalk (i j : Fin 3) : (n : ℕ) → triangleWithRays.Walk (core i) (ray j n)
  | 0 => initialArm i j
  | n + 1 => (armWalk i j n).concat (by simp)

/-- Exact support membership. The optional other core appears only on a
non-own arm, and the only ray vertices are on the selected ray up to `n`. -/
lemma mem_support_armWalk {i j : Fin 3} {z : Vertex} :
    ∀ {n : ℕ}, z ∈ (armWalk i j n).support ↔
      z = core i ∨ (i ≠ j ∧ z = core j) ∨ ∃ k, k ≤ n ∧ z = ray j k := by
  intro n
  induction n with
  | zero =>
      by_cases h : i = j
      · subst j
        simp [armWalk, initialArm]
      · simp [armWalk, initialArm, h]
  | succ n ih =>
      rw [armWalk, SimpleGraph.Walk.support_concat, List.mem_append, ih]
      simp only [List.mem_singleton]
      constructor
      · intro hz
        rcases hz with hz | hz
        · rcases hz with hz | hz | ⟨k, hk, hz⟩
          · exact Or.inl hz
          · exact Or.inr (Or.inl hz)
          · exact Or.inr (Or.inr ⟨k, Nat.le.step hk, hz⟩)
        · exact Or.inr (Or.inr ⟨n + 1, le_rfl, hz⟩)
      · intro hz
        rcases hz with hz | hz | ⟨k, hk, hz⟩
        · exact Or.inl (Or.inl hz)
        · exact Or.inl (Or.inr (Or.inl hz))
        · by_cases hkn : k ≤ n
          · exact Or.inl (Or.inr (Or.inr ⟨k, hkn, hz⟩))
          · have hk' : k = n + 1 := by omega
            subst k
            exact Or.inr hz

lemma isPath_initialArm (i j : Fin 3) : (initialArm i j).IsPath := by
  by_cases h : i = j
  · subst j
    simp [initialArm, SimpleGraph.Walk.isPath_def]
  · simp [initialArm, h, SimpleGraph.Walk.isPath_def]

lemma isPath_armWalk (i j : Fin 3) : ∀ n, (armWalk i j n).IsPath := by
  intro n
  induction n with
  | zero => exact isPath_initialArm i j
  | succ n ih =>
      rw [armWalk, SimpleGraph.Walk.isPath_concat]
      refine ⟨ih, ?_⟩
      intro hz
      rcases mem_support_armWalk.mp hz with hz | hz | ⟨k, hk, hz⟩
      · simp at hz
      · simp at hz
      · have hnk : n + 1 = k := by
          simpa using congrArg (fun x => match x with | .inr (_, m) => m | _ => 0) hz
        omega

/-- Supports of arms to two different rays meet only at their common centre.
No hypothesis of global path disjointness is used. -/
lemma eq_core_of_mem_armWalk_of_mem_armWalk {i j k : Fin 3}
    {n m : ℕ} {z : Vertex} (hjk : j ≠ k)
    (hzj : z ∈ (armWalk i j n).support)
    (hzk : z ∈ (armWalk i k m).support) : z = core i := by
  rcases mem_support_armWalk.mp hzj with hz | hz | ⟨a, ha, hz⟩
  · exact hz
  · rcases mem_support_armWalk.mp hzk with hz' | hz' | ⟨b, hb, hz'⟩
    · exact hz'
    · exfalso
      apply hjk
      have hcore : core j = core k := hz.2.symm.trans hz'.2
      exact Sum.inl.inj hcore
    · have hbad : core j = ray k b := hz.2.symm.trans hz'
      simp at hbad
  · rcases mem_support_armWalk.mp hzk with hz' | hz' | ⟨b, hb, hz'⟩
    · exact hz'
    · have hbad : ray j a = core k := hz.symm.trans hz'.2
      simp at hbad
    · exfalso
      apply hjk
      have hray : ray j a = ray k b := hz.symm.trans hz'
      exact congrArg (fun x => match x with | .inr (r, _) => r | _ => j) hray

/-- Every edge increases the ray level by at most one. -/
def level : Vertex → ℕ
  | .inl _ => 0
  | .inr (_, n) => n + 1

lemma level_le_of_adj {u v : Vertex} (h : triangleWithRays.Adj u v) :
    level v ≤ level u + 1 := by
  cases u with
  | inl i =>
      cases v with
      | inl j => simp [level]
      | inr val =>
          obtain ⟨j, n⟩ := val
          simp_all [level]
  | inr val =>
      obtain ⟨i, n⟩ := val
      cases v with
      | inl j => simp_all [level]
      | inr val' =>
          obtain ⟨j, m⟩ := val'
          simp_all [level]
          omega

lemma level_le_length {u v : Vertex} (p : triangleWithRays.Walk u v) :
    level v ≤ level u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
      have hstep := level_le_of_adj h
      simp only [SimpleGraph.Walk.length_cons]
      omega

lemma dist_core_ray_lower (i j : Fin 3) (n : ℕ) :
    n + 1 ≤ triangleWithRays.dist (core i) (ray j n) := by
  obtain ⟨p, hp⟩ := (armWalk i j n).reachable.exists_walk_length_eq_dist
  have h := level_le_length p
  change n + 1 ≤ 0 + p.length at h
  omega

/-- Three arms at core `i`, using the three distinct rays `i`, `j`, `k`, at
any prescribed scale. Their paths need not be disjoint from arms at other
centres. -/
theorem threeWayArms_triangle (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    ThreeWayArms triangleWithRays (fun _ => true) (core i) n := by
  refine ⟨ray i n, ray j n, ray k n, armWalk i i n, armWalk i j n,
    armWalk i k n, ?_, ?_, ?_, isPath_armWalk i i n, isPath_armWalk i j n,
    isPath_armWalk i k n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := dist_core_ray_lower i i n
    omega
  · have h := dist_core_ray_lower i j n
    omega
  · have h := dist_core_ray_lower i k n
    omega
  · intro d hd
    exact ⟨Set.mem_univ _, rfl⟩
  · intro d hd
    exact ⟨Set.mem_univ _, rfl⟩
  · intro d hd
    exact ⟨Set.mem_univ _, rfl⟩
  · exact fun z hz hz' => eq_core_of_mem_armWalk_of_mem_armWalk hij hz hz'
  · exact fun z hz hz' => eq_core_of_mem_armWalk_of_mem_armWalk hik hz hz'
  · exact fun z hz hz' => eq_core_of_mem_armWalk_of_mem_armWalk hjk hz hz'

/-- All three core vertices are encounter centres at every scale in the same
all-open configuration. -/
theorem allScalesAtAllCentres (i : Fin 3) (n : ℕ) :
    ThreeWayArms triangleWithRays (fun _ => true) (core i) n := by
  fin_cases i
  · exact threeWayArms_triangle 0 1 2 (by decide) (by decide) (by decide) n
  · exact threeWayArms_triangle 1 2 0 (by decide) (by decide) (by decide) n
  · exact threeWayArms_triangle 2 0 1 (by decide) (by decide) (by decide) n

/-- The original triangle remains a cycle. Any pruning operation retaining its
three edges therefore fails to produce a forest. -/
theorem triangle_cycle (h01 : triangleWithRays.Adj (core 0) (core 1))
    (h12 : triangleWithRays.Adj (core 1) (core 2))
    (h20 : triangleWithRays.Adj (core 2) (core 0)) :
    ¬ triangleWithRays.IsAcyclic := by
  let c : triangleWithRays.Walk (core 0) (core 0) := SimpleGraph.Walk.cons h01
    (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))
  have hc : c.IsCycle := by
    simp [c, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  exact fun hacyclic => hacyclic c hc

-- Every vertex has only finitely many neighbours. The finite suprema below
-- avoid any computation of the ambient infinite vertex type.
noncomputable instance locallyFinite_triangleWithRays : triangleWithRays.LocallyFinite := by
  intro v
  apply Set.Finite.fintype
  cases v with
  | inl i =>
      apply Set.Finite.subset ((Set.finite_range core).union (Set.finite_singleton (ray i 0)))
      intro z hz
      cases z with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr val =>
          obtain ⟨j, n⟩ := val
          change i = j ∧ n = 0 at hz
          rcases hz with ⟨rfl, rfl⟩
          exact Or.inr (Set.mem_singleton _)
  | inr val =>
      obtain ⟨i, n⟩ := val
      apply Set.Finite.subset ((Set.finite_range core).union
        ((Set.finite_singleton (ray i (n - 1))).insert (ray i (n + 1))))
      intro z hz
      cases z with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr val =>
          obtain ⟨j, m⟩ := val
          change i = j ∧ (m = n + 1 ∨ n = m + 1) at hz
          rcases hz with ⟨rfl, hm | hm⟩
          · subst m
            exact Or.inr (by simp)
          · have hmn : m = n - 1 := by omega
            exact Or.inr (by simp [hmn])

lemma core_zero_neighborFinset :
    triangleWithRays.neighborFinset (core 0) = {core 1, core 2, ray 0 0} := by
  ext z
  cases z with
  | inl j => fin_cases j <;> simp
  | inr val =>
      obtain ⟨j, n⟩ := val
      fin_cases j <;> simp [eq_comm]

lemma core_one_neighborFinset :
    triangleWithRays.neighborFinset (core 1) = {core 0, core 2, ray 1 0} := by
  ext z
  cases z with
  | inl j => fin_cases j <;> simp
  | inr val =>
      obtain ⟨j, n⟩ := val
      fin_cases j <;> simp [eq_comm]

lemma core_two_neighborFinset :
    triangleWithRays.neighborFinset (core 2) = {core 0, core 1, ray 2 0} := by
  ext z
  cases z with
  | inl j => fin_cases j <;> simp
  | inr val =>
      obtain ⟨j, n⟩ := val
      fin_cases j <;> simp [eq_comm]

lemma core_zero_degree : triangleWithRays.degree (core 0) = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, core_zero_neighborFinset]
  decide
lemma core_one_degree : triangleWithRays.degree (core 1) = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, core_one_neighborFinset]
  decide
lemma core_two_degree : triangleWithRays.degree (core 2) = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, core_two_neighborFinset]
  decide

/-- Local-neighbour version of the degree forcing argument. -/
lemma neighborFinset_eq_of_le_of_degree_le_local {V : Type*} {v : V}
    {T G : SimpleGraph V} [Fintype (T.neighborSet v)] [Fintype (G.neighborSet v)]
    (hTG : T ≤ G) (hdegree : G.degree v ≤ T.degree v) :
    T.neighborFinset v = G.neighborFinset v := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hTG hw
  · exact hdegree

/-- Even with all-scales arms at every centre, no locally finite spanning
subgraph can retain degree three at all three cores and be acyclic. -/
theorem not_isAcyclic_of_core_degree_three (T : Graph) [T.LocallyFinite]
    (hTG : T ≤ triangleWithRays)
    (h0 : 3 ≤ T.degree (core 0)) (h1 : 3 ≤ T.degree (core 1))
    (h2 : 3 ≤ T.degree (core 2)) : ¬ T.IsAcyclic := by
  classical
  have hN0 := neighborFinset_eq_of_le_of_degree_le_local hTG
    (show triangleWithRays.degree (core 0) ≤ T.degree (core 0) by
      rw [core_zero_degree]
      exact h0)
  have hN1 := neighborFinset_eq_of_le_of_degree_le_local hTG
    (show triangleWithRays.degree (core 1) ≤ T.degree (core 1) by
      rw [core_one_degree]
      exact h1)
  have hN2 := neighborFinset_eq_of_le_of_degree_le_local hTG
    (show triangleWithRays.degree (core 2) ≤ T.degree (core 2) by
      rw [core_two_degree]
      exact h2)
  have h01 : T.Adj (core 0) (core 1) := by
    rw [← SimpleGraph.mem_neighborFinset, hN0, core_zero_neighborFinset]
    simp
  have h12 : T.Adj (core 1) (core 2) := by
    rw [← SimpleGraph.mem_neighborFinset, hN1, core_one_neighborFinset]
    simp
  have h20 : T.Adj (core 2) (core 0) := by
    rw [← SimpleGraph.mem_neighborFinset, hN2, core_two_neighborFinset]
    simp
  let c : T.Walk (core 0) (core 0) := SimpleGraph.Walk.cons h01
    (SimpleGraph.Walk.cons h12 (SimpleGraph.Walk.cons h20 SimpleGraph.Walk.nil))
  have hc : c.IsCycle := by
    simp [c, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
  exact fun hacyclic => hacyclic c hc

/-- The packaged all-scales obstruction to this degree-preserving pruning
proposal. This makes no assertion about a true Burton--Keane trifurcation,
whose exterior separation condition is strictly stronger. -/
theorem allScales_and_no_degree_preserving_forest :
    (∀ i n, ThreeWayArms triangleWithRays (fun _ => true) (core i) n) ∧
    ∀ (T : Graph) [T.LocallyFinite], T ≤ triangleWithRays →
      3 ≤ T.degree (core 0) → 3 ≤ T.degree (core 1) →
      3 ≤ T.degree (core 2) → ¬ T.IsAcyclic := by
  exact ⟨allScalesAtAllCentres, not_isAcyclic_of_core_degree_three⟩

end FK.BurtonKeane.MultiCentreObstruction.AllScale

#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.mem_support_armWalk
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.isPath_armWalk
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.eq_core_of_mem_armWalk_of_mem_armWalk
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.dist_core_ray_lower
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.threeWayArms_triangle
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.allScalesAtAllCentres
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.triangle_cycle
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.neighborFinset_eq_of_le_of_degree_le_local
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.not_isAcyclic_of_core_degree_three
#print axioms FK.BurtonKeane.MultiCentreObstruction.AllScale.allScales_and_no_degree_preserving_forest
