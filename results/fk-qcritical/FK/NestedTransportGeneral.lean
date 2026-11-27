import FK.NestedMixture.Mixture
import FK.NestedMixture.Transport

/-! Arbitrary-boundary invariance of the finite FK model under reindexing. -/

open scoped ENNReal BigOperators Classical
open FK.Finite

namespace FK.NestedFinDLR

open FK.Finite.LabelledMultigraph

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The boundary partition transported to the reindexed vertex type. -/
noncomputable def transportBoundary {G : LabelledMultigraph} (eV : V ≃ G.Vertex)
    (eE : E ≃ G.Edge) (ξ : G.BoundaryPartition) :
    (G.transport eV eE).BoundaryPartition :=
  Setoid.comap eV ξ

section
variable (G : LabelledMultigraph) (eV : V ≃ G.Vertex) (eE : E ≃ G.Edge)

/-- Transport preserves the connection graph for every boundary partition. -/
noncomputable def connectionIso (ξ : G.BoundaryPartition)
    (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).connectionGraph (transportBoundary eV eE ξ) ω ≃g
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
        · refine Or.inr ⟨eE.symm e, ?_, ?_⟩
          · change ω (eE.symm e) = true at he
            exact he
          · rcases hjoin with h | h
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
          refine Or.inr ⟨eE a, ?_, ?_⟩
          · change ω (eE.symm (eE a)) = true
            rw [eE.symm_apply_apply]
            exact ha
          · rcases hjoin with h | h
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
              · have hu := congrArg eV h.1
                rw [G.transport_source] at hu
                exact hu
              · have hv := congrArg eV h.2
                rw [G.transport_target] at hv
                exact hv

lemma componentCount_transport (ξ : G.BoundaryPartition)
    (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).componentCount (transportBoundary eV eE ξ) ω =
      G.componentCount ξ (G.transportConfig eV eE ω) := by
  unfold LabelledMultigraph.componentCount
  exact Nat.card_congr (connectionIso G eV eE ξ ω).connectedComponentEquiv

lemma fkWeight_transport (ξ : G.BoundaryPartition) (q p : NNReal)
    (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).fkWeight q p (transportBoundary eV eE ξ) ω =
      G.fkWeight q p ξ (G.transportConfig eV eE ω) := by
  unfold LabelledMultigraph.fkWeight
  rw [componentCount_transport G eV eE ξ, G.edgeWeight_transport eV eE]

lemma partitionFunction_transport (ξ : G.BoundaryPartition) (q p : NNReal) :
    (G.transport eV eE).partitionFunction q p (transportBoundary eV eE ξ) =
      G.partitionFunction q p ξ := by
  classical
  unfold LabelledMultigraph.partitionFunction
  rw [← Equiv.sum_comp (G.transportConfig eV eE)
    (fun ω => G.fkWeight q p ξ ω)]
  exact Finset.sum_congr rfl (fun ω _ => fkWeight_transport G eV eE ξ q p ω)

/-- Pointwise FK masses are invariant under transport, for every boundary setoid. -/
theorem fkPMF_transport (ξ : G.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ω : (G.transport eV eE).Configuration) :
    (G.transport eV eE).fkPMF hq hp (transportBoundary eV eE ξ) ω =
      G.fkPMF hq hp ξ (G.transportConfig eV eE ω) := by
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.fkPMF_apply,
    fkWeight_transport G eV eE ξ q p, partitionFunction_transport G eV eE]

/-- The reindexed FK measure pushes forward to the original FK measure. -/
theorem map_transport_fkPMF (ξ : G.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) :
    PMF.map (G.transportConfig eV eE)
      ((G.transport eV eE).fkPMF hq hp (transportBoundary eV eE ξ)) =
      G.fkPMF hq hp ξ := by
  apply PMF.ext
  intro ω
  rw [PMF.map_apply]
  let z := (G.transportConfig eV eE).symm ω
  rw [tsum_eq_single z]
  · simp only [show ω = G.transportConfig eV eE z by simp [z], if_pos]
    rw [fkPMF_transport G eV eE ξ hq hp z]
  · intro z' hz'
    have hne : ω ≠ G.transportConfig eV eE z' := by
      intro h
      apply hz'
      apply (G.transportConfig eV eE).injective
      simpa [z] using h.symm
    simp [hne]

end

end FK.NestedFinDLR
