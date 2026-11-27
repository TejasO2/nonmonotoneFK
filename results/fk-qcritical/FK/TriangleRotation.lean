import FK.TriangleEmbedding

/-!
# The exact spherical rotation system of a triangle

Three disjoint swaps give the local rotations.  Face traversal has one cycle
on forward darts and one on reverse darts, hence exactly two faces.
-/

namespace FK.PlaneTopology.Continuous.Triangle

noncomputable section

open Set Metric Function
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology.Continuous

/-- A dart constructor with `Fin 3` made explicit for kernel reduction. -/
def dt (e : Fin 3) (b : Bool) : Dart graph := (e, b)

/-- At every vertex, exchange its incoming and outgoing darts.  The two
three-entry tables form one involution. -/
def dartMap : Dart graph → Dart graph := fun d =>
  cond d.2
    ((![dt 1 false, dt 2 false, dt 0 false] : Fin 3 → Dart graph) d.1)
    ((![dt 2 true, dt 0 true, dt 1 true] : Fin 3 → Dart graph) d.1)

lemma dartMap_dartMap (d : Dart graph) : dartMap (dartMap d) = d := by
  rcases d with ⟨e, b⟩
  change Fin 3 at e
  fin_cases e <;> cases b <;> rfl

/-- The local rotation as an explicitly involutive permutation. -/
def dartRotation : Equiv.Perm (Dart graph) where
  toFun := dartMap
  invFun := dartMap
  left_inv := dartMap_dartMap
  right_inv := dartMap_dartMap

@[simp] lemma dartRotation_apply (e : Fin 3) (b : Bool) :
    vertex graph (dartRotation (dt e b)) = vertex graph (dt e b) := by
  change vertex graph (dartMap (dt e b)) = vertex graph (dt e b)
  fin_cases e <;> cases b <;> rfl

lemma dart_eq_or_rotation_eq {d d' : Dart graph}
    (hd : vertex graph d = vertex graph d') : d = d' ∨ dartRotation d = d' := by
  rcases d with ⟨e, b⟩
  rcases d' with ⟨e', b'⟩
  fin_cases e <;> cases b <;> fin_cases e' <;> cases b' <;>
    simp [vertex, graph, vertexSource, vertexTarget] at hd <;>
    simp [dartRotation, dartMap, dt]

/-- The three-cycle equipped with its exact local rotation. -/
def rotationSystem : RotationSystem graph where
  rotation := dartRotation
  vertex_rotation := by
    rintro ⟨e, b⟩
    exact dartRotation_apply e b
  sameCycle_rotation := by
    intro d d' hd
    rcases dart_eq_or_rotation_eq hd with rfl | h
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simpa using h⟩

@[simp] lemma facePerm_zero_false :
    rotationSystem.facePerm (dt 0 false) = dt 1 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_one_false :
    rotationSystem.facePerm (dt 1 false) = dt 2 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_two_false :
    rotationSystem.facePerm (dt 2 false) = dt 0 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_zero_true :
    rotationSystem.facePerm (dt 0 true) = dt 2 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_one_true :
    rotationSystem.facePerm (dt 1 true) = dt 0 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_two_true :
    rotationSystem.facePerm (dt 2 true) = dt 1 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_snd (d : Dart graph) :
    (rotationSystem.facePerm d).2 = d.2 := by
  rcases d with ⟨e, b⟩
  fin_cases e <;> cases b <;>
    simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

lemma facePerm_pow_snd (d : Dart graph) (n : ℕ) :
    ((rotationSystem.facePerm ^ n) d).2 = d.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, facePerm_snd]
      exact ih

/-- Every dart is in the face orbit of the dart on edge zero with the same
orientation. -/
lemma faceOf_base (e : Fin 3) (b : Bool) :
    rotationSystem.faceOf (dt e b) = rotationSystem.faceOf (dt 0 b) := by
  fin_cases e <;> cases b
  · rfl
  · rfl
  · apply (rotationSystem.faceOf_eq_iff).2
    have h₁ : rotationSystem.facePerm.SameCycle (dt 1 false) (dt 2 false) :=
      ⟨1, by simp⟩
    have h₂ : rotationSystem.facePerm.SameCycle (dt 2 false) (dt 0 false) :=
      ⟨1, by simp⟩
    exact h₁.trans h₂
  · apply (rotationSystem.faceOf_eq_iff).2
    exact ⟨1, by simp⟩
  · apply (rotationSystem.faceOf_eq_iff).2
    exact ⟨1, by simp⟩
  · apply (rotationSystem.faceOf_eq_iff).2
    have h₁ : rotationSystem.facePerm.SameCycle (dt 2 true) (dt 1 true) :=
      ⟨1, by simp⟩
    have h₂ : rotationSystem.facePerm.SameCycle (dt 1 true) (dt 0 true) :=
      ⟨1, by simp⟩
    exact h₁.trans h₂

/-- Combinatorial face equality is exactly equality of dart orientation. -/
lemma faceOf_eq_iff_snd {d d' : Dart graph} :
    rotationSystem.faceOf d = rotationSystem.faceOf d' ↔ d.2 = d'.2 := by
  constructor
  · intro heq
    obtain ⟨n, hn⟩ := ((rotationSystem.faceOf_eq_iff).1 heq).exists_nat_pow_eq
    have hn' := congrArg Prod.snd hn
    rwa [facePerm_pow_snd] at hn'
  · rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    change Fin 3 at e e'
    intro hb
    cases hb
    change rotationSystem.faceOf (dt e b) = rotationSystem.faceOf (dt e' b)
    rw [faceOf_base e b, faceOf_base e' b]

/-- Face traversal has exactly the two orientation classes. -/
noncomputable def combFaceEquivBool : rotationSystem.Face ≃ Bool where
  toFun f := Quotient.liftOn f (fun d : Dart graph => d.2) (fun d d' h => by
    apply (faceOf_eq_iff_snd).1
    exact (rotationSystem.faceOf_eq_iff).2 h)
  invFun b := rotationSystem.faceOf (dt 0 b)
  left_inv f := by
    refine Quotient.inductionOn f ?_
    rintro ⟨e, b⟩
    change Fin 3 at e
    change rotationSystem.faceOf (dt 0 b) = rotationSystem.faceOf (dt e b)
    exact (faceOf_base e b).symm
  right_inv b := rfl

noncomputable instance fintypeFace : Fintype rotationSystem.Face :=
  rotationSystem.dualPair.fintypeFace

/-- The combinatorial triangle has two faces. -/
theorem card_face : Fintype.card rotationSystem.Face = 2 := by
  rw [Fintype.card_congr combFaceEquivBool]
  decide

lemma adj_zero_one : (graph.connectionGraph graph.freeBoundary graph.allOpen).Adj
    (0 : Fin 3) (1 : Fin 3) := by
  refine ⟨?_, Or.inr ⟨(0 : Fin 3), ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
  · change (0 : Fin 3) ≠ (1 : Fin 3)
    decide
  · rfl

lemma adj_one_two : (graph.connectionGraph graph.freeBoundary graph.allOpen).Adj
    (1 : Fin 3) (2 : Fin 3) := by
  refine ⟨?_, Or.inr ⟨(1 : Fin 3), ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
  · change (1 : Fin 3) ≠ (2 : Fin 3)
    decide
  · rfl

lemma adj_two_zero : (graph.connectionGraph graph.freeBoundary graph.allOpen).Adj
    (2 : Fin 3) (0 : Fin 3) := by
  refine ⟨?_, Or.inr ⟨(2 : Fin 3), ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
  · change (2 : Fin 3) ≠ (0 : Fin 3)
    decide
  · rfl

/-- The primal three-cycle is connected. -/
theorem graph_preconnected :
    (graph.connectionGraph graph.freeBoundary graph.allOpen).Preconnected := by
  have h01 := SimpleGraph.Adj.reachable adj_zero_one
  have h12 := SimpleGraph.Adj.reachable adj_one_two
  have h20 := SimpleGraph.Adj.reachable adj_two_zero
  intro u v
  change Fin 3 at u v
  fin_cases u <;> fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact h01
  · exact h01.trans h12
  · exact h01.symm
  · exact SimpleGraph.Reachable.refl _
  · exact h12
  · exact (h01.trans h12).symm
  · exact h12.symm
  · exact SimpleGraph.Reachable.refl _

/-- The exact six-dart spherical rotation system. -/
def sphere : RotationSphere graph where
  toRotationSystem := rotationSystem
  nonemptyVertex := ⟨(0 : Fin 3)⟩
  nonemptyDart := ⟨dt 0 false⟩
  primal_preconnected := graph_preconnected
  euler := by
    change Fintype.card rotationSystem.Face + Fintype.card (Fin 3) =
      Fintype.card (Fin 3) + 2
    rw [card_face]
    decide

/-- Exact geometric/combinatorial face incidence.  The two independently
constructed face types are identified through their labels. -/
noncomputable def faceEquiv (b : AffineBasis (Fin 3) ℝ Plane) :
    sphere.toRotationSystem.Face ≃ (embedding b).Face :=
  combFaceEquivBool.trans (faceEquivBool b).symm

end
end FK.PlaneTopology.Continuous.Triangle
