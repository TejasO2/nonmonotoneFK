import FK.ComponentUpdate
import FK.FiniteFiber

/-!
# One-edge component identities for finite FK graphs

These are the exact graph facts behind the two cases of equation (2).  Loops
are handled by reflexivity of reachability, and parallel edges and arbitrary
boundary wiring need no special cases.
-/

namespace FK.Finite.Conditional

noncomputable section
open scoped Classical

open FK.FiniteFiber
open FK.Finite.LabelledMultigraph
open FK.Finite.ComponentUpdate

variable (G : LabelledMultigraph)

/-- Whether the endpoints of `e` are connected without using `e`. -/
def endpointsConnectedWithout (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) : Prop :=
  (G.connectionGraph ξ (withEdge e false ω)).Reachable (G.source e) (G.target e)

lemma connectionGraph_withEdge_congr {ξ : G.BoundaryPartition} {e : G.Edge}
    {ω η : FiniteFiber.Config G.Edge} (h : ∀ a, a ≠ e → ω a = η a) (b : Bool) :
    G.connectionGraph ξ (withEdge e b ω) = G.connectionGraph ξ (withEdge e b η) := by
  have hcfg : withEdge e b ω = withEdge e b η := by
    funext a
    by_cases ha : a = e
    · subst a
      simp only [withEdge_edge]
    · rw [withEdge_off ha, withEdge_off ha]
      exact h a ha
  rw [hcfg]

lemma endpointsConnectedWithout_congr {ξ : G.BoundaryPartition} {e : G.Edge}
    {ω η : FiniteFiber.Config G.Edge} (h : η ∈ offFiber e ω) :
    endpointsConnectedWithout G ξ e η ↔ endpointsConnectedWithout G ξ e ω := by
  unfold endpointsConnectedWithout
  rw [connectionGraph_withEdge_congr G (fun a ha => (h a ha).symm) false]

lemma connectionGraph_closed_le_open (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) :
    G.connectionGraph ξ (withEdge e false ω) ≤
      G.connectionGraph ξ (withEdge e true ω) := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hwire | ⟨a, ha, hjoin⟩
  · exact Or.inl hwire
  · refine Or.inr ⟨a, ?_, hjoin⟩
    by_cases hae : a = e
    · subst a
      simp at ha
    · have hoff : withEdge e true ω a = withEdge e false ω a := by
        simp only [withEdge_off hae]
      rw [hoff]
      exact ha

lemma connectionGraph_open_adj (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) {u v : G.Vertex}
    (huv : (G.connectionGraph ξ (withEdge e true ω)).Adj u v) :
    (G.connectionGraph ξ (withEdge e false ω)).Adj u v ∨
      (u = G.source e ∧ v = G.target e) ∨
      (u = G.target e ∧ v = G.source e) := by
  rcases huv.2 with hwire | ⟨a, ha, hjoin⟩
  · exact Or.inl ⟨huv.1, Or.inl hwire⟩
  · by_cases hae : a = e
    · subst a
      rcases hjoin with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact Or.inr (Or.inl ⟨hs.symm, ht.symm⟩)
      · exact Or.inr (Or.inr ⟨hs.symm, ht.symm⟩)
    · have hoff : withEdge e true ω a = withEdge e false ω a := by
        simp only [withEdge_off hae]
      refine Or.inl ⟨huv.1, Or.inr ⟨a, ?_, hjoin⟩⟩
      rw [← hoff]
      exact ha

lemma connectionGraph_open_adj_endpoints (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge) (hne : G.source e ≠ G.target e) :
    (G.connectionGraph ξ (withEdge e true ω)).Adj (G.source e) (G.target e) := by
  exact ⟨hne, Or.inr ⟨e, by simp, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Opening an already connected edge does not change wired components. -/
noncomputable def componentsEquivOfConnected (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge)
    (hconn : endpointsConnectedWithout G ξ e ω) :
    (G.connectionGraph ξ (withEdge e false ω)).ConnectedComponent ≃
      (G.connectionGraph ξ (withEdge e true ω)).ConnectedComponent := by
  let H := G.connectionGraph ξ (withEdge e false ω)
  let K := G.connectionGraph ξ (withEdge e true ω)
  have hle : H ≤ K := connectionGraph_closed_le_open G ξ e ω
  have hclass : H.connectedComponentMk (G.source e) =
      H.connectedComponentMk (G.target e) :=
    SimpleGraph.ConnectedComponent.sound hconn
  have hclosed : ∀ {u v : G.Vertex}, K.Reachable u v → H.Reachable u v := by
    intro u v huv
    rw [FK.Finite.ComponentUpdate.SimpleGraph.reachable_iff_joinClasses
      H K (G.source e) (G.target e)
      hle (hconn.mono hle) (by
          intro x y hxy
          exact connectionGraph_open_adj G ξ e ω hxy)] at huv
    apply SimpleGraph.ConnectedComponent.exact
    rcases huv with huv | ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact huv
    · exact hu.trans (hclass.trans hv)
    · exact hu.trans (hclass.symm.trans hv)
  apply Equiv.ofBijective
    (fun C : H.ConnectedComponent => C.map (SimpleGraph.Hom.ofLE hle))
  constructor
  · intro C D hCD
    induction C, D using SimpleGraph.ConnectedComponent.ind₂ with
    | h u v =>
        apply SimpleGraph.ConnectedComponent.sound
        apply hclosed
        exact SimpleGraph.ConnectedComponent.exact hCD
  · exact SimpleGraph.ConnectedComponent.surjective_map_ofLE hle

lemma componentCount_open_eq_of_connected (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge)
    (hconn : endpointsConnectedWithout G ξ e ω) :
    G.componentCount ξ (withEdge e true ω) =
      G.componentCount ξ (withEdge e false ω) := by
  classical
  unfold LabelledMultigraph.componentCount
  exact (Nat.card_congr (componentsEquivOfConnected G ξ e ω hconn)).symm

lemma source_ne_target_of_not_connected (ξ : G.BoundaryPartition) (e : G.Edge)
    (ω : FiniteFiber.Config G.Edge)
    (hconn : ¬ endpointsConnectedWithout G ξ e ω) : G.source e ≠ G.target e := by
  intro hst
  apply hconn
  unfold endpointsConnectedWithout
  rw [hst]

/-- Opening a non-bridge (in `ω` without `e`) merges exactly two wired
components and therefore lowers their number by one. -/
lemma componentCount_open_add_one_of_not_connected (ξ : G.BoundaryPartition)
    (e : G.Edge) (ω : FiniteFiber.Config G.Edge)
    (hconn : ¬ endpointsConnectedWithout G ξ e ω) :
    G.componentCount ξ (withEdge e true ω) + 1 =
      G.componentCount ξ (withEdge e false ω) := by
  classical
  unfold LabelledMultigraph.componentCount
  have hc : Fintype.card (G.connectionGraph ξ (withEdge e true ω)).ConnectedComponent + 1 =
      Fintype.card (G.connectionGraph ξ (withEdge e false ω)).ConnectedComponent := by
    apply FK.Finite.ComponentUpdate.SimpleGraph.card_joinedComponents
      (connectionGraph_closed_le_open G ξ e ω)
      (connectionGraph_open_adj_endpoints G ξ e ω
        (source_ne_target_of_not_connected G ξ e ω hconn)).reachable
      (by
        intro u v huv
        exact connectionGraph_open_adj G ξ e ω huv)
    intro hst
    exact hconn (SimpleGraph.ConnectedComponent.exact hst)
  simpa only [Nat.card_eq_fintype_card] using hc

end
end FK.Finite.Conditional
