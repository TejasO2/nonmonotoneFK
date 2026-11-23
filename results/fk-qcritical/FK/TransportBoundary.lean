import FK.WiredRightInterior

/-!
# Transport of arbitrary finite FK boundary setoids

The established free-boundary graph transport is extended to the pullback of
an arbitrary boundary setoid.  This keeps the exterior-first sequential laws
aligned with the original sum-labelled FK model under right-supported wiring.
-/

namespace FK.Finite.LabelledMultigraph

open scoped ENNReal BigOperators Classical
open FK.FinitePlane

variable (G : LabelledMultigraph) {V E : Type*} [Fintype V] [Fintype E]

/-- Pull back a boundary setoid along the vertex equivalence. -/
@[instance_reducible] def transportBoundary (eV : V ≃ G.Vertex)
    (ξ : G.BoundaryPartition) : (G.transport eV (Equiv.refl G.Edge)).BoundaryPartition :=
  Setoid.comap eV ξ

/-- Pull back a boundary setoid along both parts of a graph transport.  The
edge equivalence plays no role in the setoid itself. -/
@[instance_reducible] def transportBoundaryOf (eV : V ≃ G.Vertex) {eE : E ≃ G.Edge}
    (ξ : G.BoundaryPartition) : (G.transport eV eE).BoundaryPartition :=
  Setoid.comap eV ξ

/-- Transport preserves every wired open graph, not only the free graph. -/
noncomputable def connectionIso (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (ξ : G.BoundaryPartition) (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).connectionGraph (G.transportBoundaryOf eV ξ) ω ≃g
      G.connectionGraph ξ (G.transportConfig eV eE ω) where
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
      · rcases huv.2 with hwire | ⟨e, he, hjoin⟩
        · exact Or.inl hwire
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
      · rcases huv.2 with hwire | ⟨a, ha, hjoin⟩
        · exact Or.inl hwire
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

/-- Component counts are unchanged by arbitrary-boundary transport. -/
lemma componentCount_transport (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (ξ : G.BoundaryPartition) (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).componentCount (G.transportBoundaryOf eV ξ) ω =
      G.componentCount ξ (G.transportConfig eV eE ω) := by
  unfold componentCount
  exact Nat.card_congr (G.connectionIso eV eE ξ ω).connectedComponentEquiv

/-- FK weights are unchanged by arbitrary-boundary transport. -/
lemma fkWeight_transport (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (ξ : G.BoundaryPartition) (q p : NNReal) (ω : (G.transport eV eE).Configuration) :
    G.fkWeight q p ξ (G.transportConfig eV eE ω) =
      (G.transport eV eE).fkWeight q p (G.transportBoundaryOf eV ξ) ω := by
  unfold fkWeight
  rw [G.componentCount_transport eV eE ξ ω, G.edgeWeight_transport eV eE]

/-- The actual finite FK PMF transports with every boundary setoid. -/
theorem map_transport_fkPMF (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)
    (ξ : G.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (G.transportConfig eV eE)
        ((G.transport eV eE).fkPMF hq hp₁.le (G.transportBoundaryOf eV ξ)) =
      G.fkPMF hq hp₁.le ξ := by
  rw [← normalizedPMF_eq_actual_fkPMF (G.transport eV eE)
      (G.transportBoundaryOf eV ξ) hq hp₀ hp₁,
    ← normalizedPMF_eq_actual_fkPMF G ξ hq hp₀ hp₁]
  exact normalizedPMF_map_eq_of_proportional (G.transportConfig eV eE) _ _ 1 zero_lt_one
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (by
      intro ω
      rw [one_mul]
      exact G.fkWeight_transport eV eE ξ q p ω)

end FK.Finite.LabelledMultigraph
