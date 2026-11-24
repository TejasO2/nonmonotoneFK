import FK.GibbsOrder

/-!
# The boundary-only wired convention versus the all-vertex top setoid

The paper's wired boundary condition wires the *boundary* vertices of a finite
box and leaves the interior vertices free.  The vacuous alternative — the top
setoid on *all* vertices — is a different, strictly coarser convention.  This
file records the honest boundary-only setoid, proves it lies between the free
and the all-vertex-top setoids, so the `q ≥ 1` wiring order (`FK.GibbsOrder`)
gives the corresponding sandwich of FK measures, and records the two endpoint
identifications.  Nothing here is specific to the paper's geometry: the boundary
set is an explicit parameter, as in the source's `∂Λ`.
-/

open scoped Classical BigOperators ENNReal NNReal
open FK.Finite

namespace FK.NestedMixture

namespace BoundaryOnly

variable (G : LabelledMultigraph)

/-- **The boundary-only wired boundary condition**: two vertices are equivalent
when they are equal or both lie on the prescribed boundary set.  Interior
vertices stay in singleton classes. -/
@[instance_reducible] def boundaryWired (bnd : Set G.Vertex) : G.BoundaryPartition where
  r x y := x = y ∨ (x ∈ bnd ∧ y ∈ bnd)
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · rintro x y (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ⟨h.2, h.1⟩
    · rintro x y z (h | h) (h' | h')
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨h ▸ h'.1, h'.2⟩
      · exact Or.inr ⟨h.1, h' ▸ h.2⟩
      · exact Or.inr ⟨h.1, h'.2⟩

lemma freeBoundary_le_boundaryWired (bnd : Set G.Vertex) :
    G.freeBoundary ≤ boundaryWired G bnd := by
  intro x y hxy
  exact Or.inl hxy

lemma boundaryWired_le_wiredBoundary (bnd : Set G.Vertex) :
    boundaryWired G bnd ≤ G.wiredBoundary := by
  intro x y _
  exact trivial

@[simp] lemma boundaryWired_empty : boundaryWired G ∅ = G.freeBoundary := by
  refine Setoid.ext ?_
  intro a b
  show (a = b ∨ (a ∈ (∅ : Set G.Vertex) ∧ b ∈ (∅ : Set G.Vertex))) ↔ a = b
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (Set.notMem_empty a)
  · exact fun h => Or.inl h

@[simp] lemma boundaryWired_univ : boundaryWired G Set.univ = G.wiredBoundary := by
  refine Setoid.ext ?_
  intro a b
  show (a = b ∨ (a ∈ (Set.univ : Set G.Vertex) ∧ b ∈ Set.univ)) ↔ True
  constructor
  · intro _; trivial
  · intro _
    exact Or.inr ⟨Set.mem_univ a, Set.mem_univ b⟩

/-- The boundary-only convention sits in the `q ≥ 1` wiring order between the
free law and the all-vertex-top law on every increasing event. -/
theorem fkMeasure_boundaryWired_sandwich {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) (bnd : Set G.Vertex) {A : Set G.Configuration} (hA : IsUpperSet A) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le G.freeBoundary A
        ≤ G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (boundaryWired G bnd) A
      ∧ G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le (boundaryWired G bnd) A
        ≤ G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le G.wiredBoundary A :=
  ⟨FK.Finite.LabelledMultigraph.fkMeasure_mono_wiring (G := G) hq hp0 hp1 (freeBoundary_le_boundaryWired G bnd) hA,
    FK.Finite.LabelledMultigraph.fkMeasure_mono_wiring (G := G) hq hp0 hp1 (boundaryWired_le_wiredBoundary G bnd) hA⟩

end BoundaryOnly

end FK.NestedMixture

#print axioms FK.NestedMixture.BoundaryOnly.fkMeasure_boundaryWired_sandwich
#print axioms FK.NestedMixture.BoundaryOnly.boundaryWired_univ
