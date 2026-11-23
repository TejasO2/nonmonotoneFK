import FK.FiniteModel

/-!
# Connected components after adding one graph connection

Adding an adjacency between two previously disconnected vertices merges exactly
two connected components.  We prove an explicit equivalence between the new
components and `Option` of the old components other than the two merged ones.
-/

namespace FK.Finite.ComponentUpdate

open scoped BigOperators

/-- Equality of components, possibly after identifying the two marked
components `a` and `b`. -/
def JoinClasses {α : Type*} (a b x y : α) : Prop :=
  x = y ∨ (x = a ∧ b = y) ∨ (x = b ∧ a = y)

lemma JoinClasses.trans {α : Type*} {a b x y z : α}
    (hxy : JoinClasses a b x y) (hyz : JoinClasses a b y z) :
    JoinClasses a b x z := by
  unfold JoinClasses at *
  aesop

lemma JoinClasses.symm {α : Type*} {a b x y : α}
    (h : JoinClasses a b x y) : JoinClasses a b y x := by
  unfold JoinClasses at *
  aesop

namespace SimpleGraph

variable {V : Type*} (H K : _root_.SimpleGraph V) (s t : V)

/-- Reachability in a supergraph whose only additional adjacency is between
`s` and `t` is exactly equality after merging their old components. -/
lemma reachable_iff_joinClasses (hle : H ≤ K) (hst : K.Reachable s t)
    (honly : ∀ {u v : V}, K.Adj u v →
      H.Adj u v ∨ (u = s ∧ v = t) ∨ (u = t ∧ v = s)) (u v : V) :
    K.Reachable u v ↔
      JoinClasses (H.connectedComponentMk s) (H.connectedComponentMk t)
        (H.connectedComponentMk u) (H.connectedComponentMk v) := by
  constructor
  · intro huv
    rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at huv
    induction huv with
    | refl => exact Or.inl rfl
    | tail hxy hyz ih =>
        apply JoinClasses.trans ih
        rcases honly hyz with h | h | h
        · exact Or.inl (_root_.SimpleGraph.ConnectedComponent.sound h.reachable)
        · rcases h with ⟨rfl, rfl⟩
          exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · rcases h with ⟨rfl, rfl⟩
          exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro h
    have hjoin : K.Reachable s t := hst
    have hold : ∀ {x y : V}, H.Reachable x y → K.Reachable x y :=
      fun {_ _} hxy => hxy.mono hle
    rcases h with h | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hold (_root_.SimpleGraph.ConnectedComponent.exact h)
    · have hus : K.Reachable u s :=
        hold (_root_.SimpleGraph.ConnectedComponent.exact hu)
      have htv : K.Reachable t v :=
        hold (_root_.SimpleGraph.ConnectedComponent.exact hv)
      exact hus.trans (hjoin.trans htv)
    · have hut : K.Reachable u t :=
        hold (_root_.SimpleGraph.ConnectedComponent.exact hu)
      have hsv : K.Reachable s v :=
        hold (_root_.SimpleGraph.ConnectedComponent.exact hv)
      exact hut.trans (hjoin.symm.trans hsv)

section Fibers

variable {H K} {s t}

/-- Fibres of the old-to-new component map are singletons except for the two
components merged by the new connection. -/
lemma map_eq_iff_joinClasses (hle : H ≤ K) (hst : K.Reachable s t)
    (honly : ∀ {u v : V}, K.Adj u v →
      H.Adj u v ∨ (u = s ∧ v = t) ∨ (u = t ∧ v = s))
    (a b : H.ConnectedComponent) :
    a.map (_root_.SimpleGraph.Hom.ofLE hle) = b.map (_root_.SimpleGraph.Hom.ofLE hle) ↔
      JoinClasses (H.connectedComponentMk s) (H.connectedComponentMk t) a b := by
  induction a, b using _root_.SimpleGraph.ConnectedComponent.ind₂ with
  | h u v =>
      change K.connectedComponentMk u = K.connectedComponentMk v ↔ _
      rw [_root_.SimpleGraph.ConnectedComponent.eq, reachable_iff_joinClasses H K s t hle hst honly]

/-- The new components are in bijection with `Option` of the old components
outside the two marked ones.  The `none` point is the merged component. -/
noncomputable def joinedComponentsEquiv (hle : H ≤ K) (hst : K.Reachable s t)
    (honly : ∀ {u v : V}, K.Adj u v →
      H.Adj u v ∨ (u = s ∧ v = t) ∨ (u = t ∧ v = s)) :
    Option {C : H.ConnectedComponent //
      C ≠ H.connectedComponentMk s ∧ C ≠ H.connectedComponentMk t} ≃
      K.ConnectedComponent := by
  let f : Option {C : H.ConnectedComponent //
      C ≠ H.connectedComponentMk s ∧ C ≠ H.connectedComponentMk t} →
      K.ConnectedComponent
    | none => K.connectedComponentMk s
    | some C => C.1.map (_root_.SimpleGraph.Hom.ofLE hle)
  have hmap := map_eq_iff_joinClasses (H := H) (K := K) (s := s) (t := t) hle hst honly
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    have hnome : ∀ (C : {C : H.ConnectedComponent //
        C ≠ H.connectedComponentMk s ∧ C ≠ H.connectedComponentMk t}),
        f none ≠ f (some C) := by
      intro C hC
      have hj := (hmap (H.connectedComponentMk s) C.1).mp hC
      rcases hj with hj | ⟨_, hj⟩ | ⟨_, hj⟩
      · exact C.2.1 hj.symm
      · exact C.2.2 hj.symm
      · exact C.2.1 hj.symm
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some C => exact (hnome C hxy).elim
    | some C =>
        cases y with
        | none => exact (hnome C hxy.symm).elim
        | some D =>
            have hj := (hmap C.1 D.1).mp hxy
            rcases hj with hj | ⟨hCs, htD⟩ | ⟨hCt, hsD⟩
            · exact congrArg some (Subtype.ext hj)
            · exact (C.2.1 hCs).elim
            · exact (C.2.2 hCt).elim
  · intro D
    obtain ⟨C, rfl⟩ := _root_.SimpleGraph.ConnectedComponent.surjective_map_ofLE hle D
    by_cases hC : C = H.connectedComponentMk s ∨ C = H.connectedComponentMk t
    · refine ⟨none, ?_⟩
      apply (hmap (H.connectedComponentMk s) C).mpr
      rcases hC with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · have hCs : C ≠ H.connectedComponentMk s := fun h => hC (Or.inl h)
      have hCt : C ≠ H.connectedComponentMk t := fun h => hC (Or.inr h)
      exact ⟨some ⟨C, hCs, hCt⟩, rfl⟩

/-- If the two marked old components are distinct, adding their connection
lowers the finite component count by exactly one. -/
theorem card_joinedComponents [Fintype H.ConnectedComponent]
    [Fintype K.ConnectedComponent] (hle : H ≤ K) (hst : K.Reachable s t)
    (honly : ∀ {u v : V}, K.Adj u v →
      H.Adj u v ∨ (u = s ∧ v = t) ∨ (u = t ∧ v = s))
    (hne : H.connectedComponentMk s ≠ H.connectedComponentMk t) :
    Fintype.card K.ConnectedComponent + 1 = Fintype.card H.ConnectedComponent := by
  classical
  have hcard := Fintype.card_congr (joinedComponentsEquiv hle hst honly)
  simp only [Fintype.card_option] at hcard
  have hfilter :
      (Finset.univ.filter fun C : H.ConnectedComponent =>
        C ≠ H.connectedComponentMk s ∧ C ≠ H.connectedComponentMk t) =
      (Finset.univ.erase (H.connectedComponentMk s)).erase
        (H.connectedComponentMk t) := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    aesop
  have hc : Fintype.card {C : H.ConnectedComponent //
      C ≠ H.connectedComponentMk s ∧ C ≠ H.connectedComponentMk t} =
      Fintype.card H.ConnectedComponent - 2 := by
    rw [Fintype.card_subtype, hfilter,
      Finset.card_erase_of_mem (by simp [Ne.symm hne]),
      Finset.card_erase_of_mem (by simp), Finset.card_univ]
    omega
  rw [hc] at hcard
  let _ : Nontrivial H.ConnectedComponent :=
    ⟨⟨H.connectedComponentMk s, H.connectedComponentMk t, hne⟩⟩
  have hn : 1 < Fintype.card H.ConnectedComponent := Fintype.one_lt_card
  omega

end Fibers

end SimpleGraph
end FK.Finite.ComponentUpdate
