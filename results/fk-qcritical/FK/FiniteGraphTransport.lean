import FK.PlanarActual

/-!
# Isomorphism invariance of the actual finite FK model

Vertices and labelled edges may be reindexed simultaneously.  Loops and
parallel labels are preserved.  The free connection graphs are isomorphic,
and the pushforward of the actual finite FK PMF along the induced
configuration equivalence is the original FK PMF.
-/

namespace FK.Finite.LabelledMultigraph

open scoped ENNReal BigOperators Classical
open FK.FinitePlane

variable (G : LabelledMultigraph) {V E : Type*} [Fintype V] [Fintype E]

/-- Simultaneous vertex and edge transport of a finite labelled multigraph. -/
def transport (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge) : LabelledMultigraph where
  Vertex := V
  Edge := E
  source a := eV.symm (G.source (eE a))
  target a := eV.symm (G.target (eE a))

/-- The configuration equivalence induced by an edge equivalence. -/
def transportConfig (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge) :
    (G.transport eV eE).Configuration ≃ G.Configuration where
  toFun ω := ω ∘ eE.symm
  invFun ω := ω ∘ eE
  left_inv ω := by
    funext a
    exact congrArg ω (eE.symm_apply_apply a)
  right_inv ω := by
    funext a
    change ω (eE (eE.symm a)) = ω a
    exact congrArg ω (eE.apply_symm_apply a)

@[simp] lemma transport_source (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge) (a : E) :
    eV ((G.transport eV eE).source a) = G.source (eE a) := by
  change eV (eV.symm (G.source (eE a))) = G.source (eE a)
  exact eV.apply_symm_apply _

@[simp] lemma transport_target (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge) (a : E) :
    eV ((G.transport eV eE).target a) = G.target (eE a) := by
  change eV (eV.symm (G.target (eE a))) = G.target (eE a)
  exact eV.apply_symm_apply _

/-- Transport preserves the free open connection graph, up to `eV`. -/
noncomputable def freeConnectionIso (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).connectionGraph (G.transport eV eE).freeBoundary ω ≃g
      G.connectionGraph G.freeBoundary (G.transportConfig eV eE ω) where
  toEquiv := eV
  map_rel_iff' := by
    intro u v
    change V at u v
    change (E → Bool) at ω
    constructor
    · intro huv
      refine ⟨?_, ?_⟩
      · intro heq
        exact huv.1 (congrArg eV heq)
      · rcases huv.2 with hfree | ⟨e, he, hjoin⟩
        · exact Or.inl (eV.injective hfree)
        · refine Or.inr ⟨eE.symm e, by
            change ω (eE.symm e) = true at he
            exact he, ?_⟩
          rcases hjoin with h | h
          · apply Or.inl
            constructor
            · apply eV.injective
              rw [G.transport_source]
              exact (congrArg G.source (eE.apply_symm_apply e)).trans h.1
            · apply eV.injective
              rw [G.transport_target]
              exact (congrArg G.target (eE.apply_symm_apply e)).trans h.2
          · apply Or.inr
            constructor
            · apply eV.injective
              rw [G.transport_source]
              exact (congrArg G.source (eE.apply_symm_apply e)).trans h.1
            · apply eV.injective
              rw [G.transport_target]
              exact (congrArg G.target (eE.apply_symm_apply e)).trans h.2
    · intro huv
      refine ⟨?_, ?_⟩
      · intro heq
        exact huv.1 (eV.injective heq)
      · rcases huv.2 with hfree | ⟨a, ha, hjoin⟩
        · exact Or.inl (congrArg eV hfree)
        · change E at a
          refine Or.inr ⟨eE a, by
            change ω (eE.symm (eE a)) = true
            rw [eE.symm_apply_apply]
            exact ha, ?_⟩
          rcases hjoin with h | h
          · apply Or.inl
            constructor
            · have hu := congrArg eV h.1
              rw [G.transport_source] at hu
              exact hu
            · have hv := congrArg eV h.2
              rw [G.transport_target] at hv
              exact hv
          · apply Or.inr
            constructor
            · have hv := congrArg eV h.1
              rw [G.transport_source] at hv
              exact hv
            · have hu := congrArg eV h.2
              rw [G.transport_target] at hu
              exact hu

lemma componentCount_free_transport (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).componentCount (G.transport eV eE).freeBoundary ω =
      G.componentCount G.freeBoundary (G.transportConfig eV eE ω) := by
  unfold componentCount
  exact Nat.card_congr (G.freeConnectionIso eV eE ω).connectedComponentEquiv

lemma edgeWeight_transport (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge) (p : NNReal)
    (ω : (G.transport eV eE).Configuration) :
    G.edgeWeight p (G.transportConfig eV eE ω) = (G.transport eV eE).edgeWeight p ω := by
  unfold edgeWeight transportConfig
  change (∏ e, if ω (eE.symm e) then p else 1 - p) = ∏ a, if ω a then p else 1 - p
  rw [← eE.prod_comp]
  apply Finset.prod_congr rfl
  intro a _
  simp

lemma fkWeight_free_transport (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (q p : NNReal) (ω : (G.transport eV eE).Configuration) :
    G.fkWeight q p G.freeBoundary (G.transportConfig eV eE ω) =
      (G.transport eV eE).fkWeight q p (G.transport eV eE).freeBoundary ω := by
  unfold fkWeight
  rw [G.componentCount_free_transport eV eE, G.edgeWeight_transport eV eE]

/-- The actual FK PMF is invariant under simultaneous vertex and labelled
edge transport. -/
theorem map_transport_fkPMF_free (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (G.transportConfig eV eE)
        ((G.transport eV eE).fkPMF hq hp₁.le (G.transport eV eE).freeBoundary) =
      G.fkPMF hq hp₁.le G.freeBoundary := by
  rw [← normalizedPMF_eq_actual_fkPMF (G.transport eV eE)
      (G.transport eV eE).freeBoundary hq hp₀ hp₁,
    ← normalizedPMF_eq_actual_fkPMF G G.freeBoundary hq hp₀ hp₁]
  exact normalizedPMF_map_eq_of_proportional (G.transportConfig eV eE) _ _ 1 zero_lt_one
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (by
      intro ω
      rw [one_mul]
      exact G.fkWeight_free_transport eV eE q p ω)

end FK.Finite.LabelledMultigraph
