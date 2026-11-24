import FK.AGTree.Transitive

/-!
# Exact regularity of the two-class tree

Every vertex of `Ultra.G` has exactly five neighbours.  Since the automorphism
group is vertex transitive by `Ultra.vertex_transitive`, it suffices to count
the neighbours of the root, which are exactly the five appended letters.
-/

namespace Ultra

open V

noncomputable section

/-- The neighbour of the root obtained by appending `c`. -/
def rootNbr (c : A) : G.neighborSet V.root :=
  ⟨V.root.snoc c (Or.inl rfl), by
    rw [SimpleGraph.mem_neighborSet]
    exact adj_snoc (Or.inl rfl)⟩

lemma rootNbr_injective : Function.Injective rootNbr := by
  intro c c' h
  have hw : (V.root.snoc c (Or.inl rfl)).w = (V.root.snoc c' (Or.inl rfl)).w :=
    congrArg (fun z : G.neighborSet V.root => (z : V).w) h
  simpa [V.snoc_w] using hw

lemma rootNbr_surjective : Function.Surjective rootNbr := by
  rintro ⟨w, hw⟩
  rw [SimpleGraph.mem_neighborSet] at hw
  rcases (adj_iff (v := V.root) (w := w)).1 hw with ⟨a, hv, rfl⟩ | ⟨h, rfl⟩
  · refine ⟨a, ?_⟩
    apply Subtype.ext
    apply V.ext
    rfl
  · exact absurd rfl h

/-- The root has five neighbours. -/
theorem card_neighborSet_root : Fintype.card (G.neighborSet V.root) = 5 := by
  rw [← Fintype.card_congr (Equiv.ofBijective rootNbr ⟨rootNbr_injective, rootNbr_surjective⟩)]
  simp [A]

/-- The root has degree five. -/
theorem degree_root : G.degree V.root = 5 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact card_neighborSet_root

/-- **Exact boundedness**: the two-class tree is regular of degree five. -/
theorem degree_eq_five (v : V) : G.degree v = 5 := by
  obtain ⟨φ, hφ⟩ := vertex_transitive v V.root
  rw [← φ.degree_eq, hφ]
  exact degree_root

/-- The uniform degree bound in the form used by the device packing results. -/
theorem degree_le_five (v : V) : G.degree v ≤ 5 := (degree_eq_five v).le

end

end Ultra
