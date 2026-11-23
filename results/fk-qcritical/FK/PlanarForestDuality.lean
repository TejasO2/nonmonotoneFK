import FK.PlanarActual
import FK.LabelledForestEuler

/-!
# Actual planar FK duality for finite labelled forests and cycles

A finite plane forest has one face; its dual has one vertex and one loop for
every primal labelled edge. A finite plane cycle has two faces; its dual has
two vertices and parallel labelled edges. This file proves the resulting
component-form Euler identities and uses them to remove the geometric
`heuler` hypothesis from the actual FK duality theorems for these graph
classes. A conditioned forest version is included. Labelled edges and isolated
primal vertices are retained; no simple-graph collapse is used.
-/

namespace FK.Finite.LabelledMultigraph

open FK.Configuration
open FK.Finite.Conditional
open FK.FiniteFiber

/-- The dual of a finite plane forest: one face/vertex and one dual loop for
each primal labelled edge. The edge type is definitionally unchanged. -/
def loopDual (G : LabelledMultigraph) : LabelledMultigraph where
  Vertex := PUnit
  Edge := G.Edge
  source _ := PUnit.unit
  target _ := PUnit.unit

instance (G : LabelledMultigraph) : Subsingleton (loopDual G).Vertex := by
  change Subsingleton PUnit
  infer_instance

instance (G : LabelledMultigraph) : Nonempty (loopDual G).Vertex := by
  change Nonempty PUnit
  infer_instance

/-- Acyclicity of a labelled multigraph, expressed without collapsing loops or
parallel edges: every edge is a bridge in the all-open configuration. -/
def IsLabelledForest (G : LabelledMultigraph) : Prop :=
  G.IsOpenForest G.freeBoundary G.allOpen

/-- Every subconfiguration of a labelled forest is an open forest. -/
lemma isOpenForest_of_isLabelledForest (G : LabelledMultigraph)
    (hG : G.IsLabelledForest) (ω : G.Configuration) :
    G.IsOpenForest G.freeBoundary ω := by
  classical
  intro e he hconn
  apply hG e (by simp [allOpen])
  unfold endpointsConnectedWithout at hconn ⊢
  apply hconn.mono
  apply G.connectionGraph_mono
  intro a
  by_cases hae : a = e
  · subst a
    simp
  · simp [withEdge_off hae, allOpen]

/-- On a one-vertex graph the free and wired boundary partitions coincide. -/
lemma loopDual_freeBoundary_eq_wired (G : LabelledMultigraph) :
    (loopDual G).freeBoundary = (loopDual G).wiredBoundary := by
  apply Setoid.ext
  intro u v
  change u = v ↔ True
  simp only [iff_true]
  exact Subsingleton.elim u v

/-- Every configuration on the one-face loop dual has exactly one free
component, irrespective of which loops are open. -/
lemma loopDual_componentCount (G : LabelledMultigraph)
    (η : (loopDual G).Configuration) :
    (loopDual G).componentCount (loopDual G).freeBoundary η = 1 := by
  rw [loopDual_freeBoundary_eq_wired]
  exact (loopDual G).componentCount_wired η

/-- The planar dual of a labelled cycle: its two faces are the two vertices,
and all dual labelled edges join those vertices in parallel. -/
def cycleDual (G : LabelledMultigraph) : LabelledMultigraph where
  Vertex := Bool
  Edge := G.Edge
  source _ := false
  target _ := true

/-- A graph-theoretic certificate for a connected labelled cycle.  The last
field excludes both extra bridges and additional cycles, while the cardinal
and connectivity fields exclude degenerate vacuous cases. -/
structure IsLabelledCycle (G : LabelledMultigraph) : Prop where
  nonemptyVertex : Nonempty G.Vertex
  card_edges : Fintype.card G.Edge = Fintype.card G.Vertex
  preconnected : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected
  isOpenForest_of_ne_allOpen : ∀ {ω : G.Configuration}, ω ≠ G.allOpen →
    G.IsOpenForest G.freeBoundary ω

/-- The two-vertex graph with two labelled parallel edges: the smallest
non-simple cycle in the present labelled-edge convention. -/
def twoEdgeCycle : LabelledMultigraph where
  Vertex := Bool
  Edge := Bool
  source _ := false
  target _ := true

/-- The cycle certificate is inhabited, explicitly for `twoEdgeCycle`. -/
lemma isLabelledCycle_twoEdgeCycle : twoEdgeCycle.IsLabelledCycle := by
  classical
  refine ⟨⟨false⟩, by rfl, ?_, ?_⟩
  · have hadj : (twoEdgeCycle.connectionGraph twoEdgeCycle.freeBoundary
        twoEdgeCycle.allOpen).Adj false true := by
      refine ⟨Bool.false_ne_true, Or.inr ⟨false, by rfl, ?_⟩⟩
      simp [twoEdgeCycle, Joins]
    intro u v
    change Bool at u v
    cases u <;> cases v
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _
  · intro ω hω e he hconn
    obtain ⟨f, hf⟩ := twoEdgeCycle.exists_closed_of_ne_allOpen hω
    have hfe : f ≠ e := by
      intro hfe
      subst f
      rw [hf] at he
      contradiction
    have hclosed : withEdge e false ω = twoEdgeCycle.allClosed := by
      funext a
      by_cases hae : a = e
      · subst a
        simp [allClosed]
      · rw [withEdge_off hae]
        change ω a = false
        have haf : a = f := by
          have hbool : ∀ a e f : Bool, a ≠ e → f ≠ e → a = f := by decide
          exact hbool a e f hae hfe
        rw [haf, hf]
    unfold endpointsConnectedWithout at hconn
    rw [hclosed, connectionGraph_free_allClosed] at hconn
    have h := SimpleGraph.reachable_bot.mp hconn
    simp [twoEdgeCycle] at h

/-- A preconnected actual connection graph on a finite vertex type has one
component.  The explicit vertex witness avoids any noncomputable global
choice of a component. -/
lemma componentCount_eq_one_of_preconnected (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (ω : G.Configuration) (v : G.Vertex)
    (h : (G.connectionGraph ξ ω).Preconnected) :
    G.componentCount ξ ω = 1 := by
  change Nat.card (G.connectionGraph ξ ω).ConnectedComponent = 1
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨h.subsingleton_connectedComponent,
      ⟨(G.connectionGraph ξ ω).connectedComponentMk v⟩⟩

/-- With no open dual edges, the two faces are distinct free components. -/
lemma cycleDual_componentCount_allClosed (G : LabelledMultigraph) :
    (cycleDual G).componentCount (cycleDual G).freeBoundary
      (cycleDual G).allClosed = 2 := by
  rw [componentCount_free_allClosed]
  change Nat.card Bool = 2
  simp

/-- Any open labelled edge connects the two face vertices of `cycleDual`. -/
lemma cycleDual_componentCount_eq_one (G : LabelledMultigraph)
    (η : (cycleDual G).Configuration) (e : (cycleDual G).Edge)
    (he : η e = true) :
    (cycleDual G).componentCount (cycleDual G).freeBoundary η = 1 := by
  have hadj : (cycleDual G).connectionGraph (cycleDual G).freeBoundary η |>.Adj
      false true := by
    refine ⟨Bool.false_ne_true, Or.inr ⟨e, he, ?_⟩⟩
    simp [cycleDual, Joins]
  have hpre : ((cycleDual G).connectionGraph
      (cycleDual G).freeBoundary η).Preconnected := by
    intro u v
    change Bool at u v
    cases u <;> cases v
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _
  exact componentCount_eq_one_of_preconnected (cycleDual G)
    (cycleDual G).freeBoundary η false hpre

lemma openCard_allOpen (G : LabelledMultigraph) :
    FK.FinitePlane.openCard G.allOpen = Fintype.card G.Edge := by
  simp [FK.FinitePlane.openCard, allOpen]

end FK.Finite.LabelledMultigraph

namespace FK.FinitePlane

open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph

/-- Component-form planar Euler identity for a finite labelled forest and its
one-face loop dual.  Any identification of the primal and dual labelled edge
types may be used, since every dual configuration has one component. -/
lemma loopDual_componentCount_add_card_of_equiv (G : LabelledMultigraph)
    (hG : G.IsLabelledForest) (e : G.Edge ≃ (loopDual G).Edge)
    (ω : G.Configuration) :
    (loopDual G).componentCount (loopDual G).freeBoundary (dualConfig e ω) +
        Fintype.card G.Vertex =
      G.componentCount G.freeBoundary ω + 1 + openCard ω := by
  rw [loopDual_componentCount]
  have h := G.componentCount_add_openCard_of_free_isOpenForest ω
    (G.isOpenForest_of_isLabelledForest hG ω)
  omega

/-- The identity-equivalence form of `loopDual_componentCount_add_card_of_equiv`. -/
lemma loopDual_componentCount_add_card (G : LabelledMultigraph)
    (hG : G.IsLabelledForest) (ω : G.Configuration) :
    (loopDual G).componentCount (loopDual G).freeBoundary
        (dualConfig (Equiv.refl G.Edge : G.Edge ≃ (loopDual G).Edge) ω) +
        Fintype.card G.Vertex =
      G.componentCount G.freeBoundary ω + 1 + openCard ω :=
  loopDual_componentCount_add_card_of_equiv G hG
    (Equiv.refl G.Edge : G.Edge ≃ (loopDual G).Edge) ω

/-- Unconditional actual FK planar duality for a finite labelled forest. This
is `actual_fkPMF_duality` with its geometric Euler obligation proved. -/
theorem actual_fkPMF_forest_loopDual_duality (G : LabelledMultigraph)
    (hG : G.IsLabelledForest) (q p : NNReal)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (dualEquiv (Equiv.refl G.Edge))
        (G.fkPMF hq hp₁.le G.freeBoundary) =
      (loopDual G).fkPMF hq (dualParameter_le_one hq hp₁.le)
        (loopDual G).freeBoundary := by
  apply actual_fkPMF_duality G (loopDual G) (Equiv.refl G.Edge) q p hq hp₀ hp₁
  exact loopDual_componentCount_add_card G hG

/-- Conditioned actual FK duality for a finite plane forest, with the matching
exterior primal and dual configurations.  This discharges the ambient Euler
hypothesis in `actual_conditioned_fkPMF_duality`; the induced exterior boundary
partitions are exactly those of the original theorem. -/
theorem actual_conditioned_fkPMF_forest_loopDual_duality
    {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) (hG : (ambientOfSum s t).IsLabelledForest)
    (q p : NNReal) (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : O → Bool) :
    PMF.map (dualEquiv (Equiv.refl I))
        ((interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ)) =
      (interiorOfSum (fun _ : I ⊕ O => PUnit.unit)
        (fun _ : I ⊕ O => PUnit.unit)).fkPMF hq
        (dualParameter_le_one hq hp₁.le)
        (exteriorBoundary (fun _ : I ⊕ O => PUnit.unit)
          (fun _ : I ⊕ O => PUnit.unit) (dualConfig (Equiv.refl O) ξ)) := by
  refine actual_conditioned_fkPMF_duality s t
    (fun _ : I ⊕ O => PUnit.unit) (fun _ : I ⊕ O => PUnit.unit)
    (Equiv.refl I) (Equiv.refl O) q p hq hp₀ hp₁ ?_ ξ
  intro ρ
  exact loopDual_componentCount_add_card_of_equiv (ambientOfSum s t) hG
    (((Equiv.refl I).sumCongr (Equiv.refl O)) :
      (I ⊕ O) ≃ (loopDual (ambientOfSum s t)).Edge) ρ

/-- Component-form planar Euler identity for a labelled cycle.  If all primal
edges are open, the dual is all closed and has two components.  Otherwise an
open dual parallel edge joins the two faces and the primal configuration is a
forest. -/
lemma cycleDual_componentCount_add_card (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) (ω : G.Configuration) :
    (cycleDual G).componentCount (cycleDual G).freeBoundary
        (dualConfig (Equiv.refl G.Edge : G.Edge ≃ (cycleDual G).Edge) ω) +
        Fintype.card G.Vertex =
      G.componentCount G.freeBoundary ω + 1 + openCard ω := by
  classical
  by_cases hω : ω = G.allOpen
  · subst ω
    have hd : dualConfig (Equiv.refl G.Edge : G.Edge ≃ (cycleDual G).Edge)
        G.allOpen = (cycleDual G).allClosed := by
      funext f
      simp [dualConfig, allOpen, allClosed]
    have hkd : (cycleDual G).componentCount (cycleDual G).freeBoundary
        (dualConfig (Equiv.refl G.Edge : G.Edge ≃ (cycleDual G).Edge)
          G.allOpen) = 2 := by
      calc
        _ = (cycleDual G).componentCount (cycleDual G).freeBoundary
            (cycleDual G).allClosed :=
          congrArg (fun η : (cycleDual G).Configuration =>
            (cycleDual G).componentCount (cycleDual G).freeBoundary η) hd
        _ = 2 := cycleDual_componentCount_allClosed G
    have hk : G.componentCount G.freeBoundary G.allOpen = 1 :=
      componentCount_eq_one_of_preconnected G G.freeBoundary G.allOpen
        hG.nonemptyVertex.some hG.preconnected
    rw [hkd, hk, openCard_allOpen]
    have hc := hG.card_edges
    omega
  · obtain ⟨f, hf⟩ := G.exists_closed_of_ne_allOpen hω
    have hd : dualConfig (Equiv.refl G.Edge) ω f = true := by
      simp [dualConfig, hf]
    have hkd := cycleDual_componentCount_eq_one G
      (dualConfig (Equiv.refl G.Edge) ω) f hd
    have hk := G.componentCount_add_openCard_of_free_isOpenForest ω
      (hG.isOpenForest_of_ne_allOpen hω)
    rw [hkd]
    omega

/-- Unconditional actual FK planar duality for a finite labelled cycle and its
two-face parallel-edge dual. -/
theorem actual_fkPMF_cycleDual_duality (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) (q p : NNReal)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (dualEquiv (Equiv.refl G.Edge))
        (G.fkPMF hq hp₁.le G.freeBoundary) =
      (cycleDual G).fkPMF hq (dualParameter_le_one hq hp₁.le)
        (cycleDual G).freeBoundary := by
  apply actual_fkPMF_duality G (cycleDual G) (Equiv.refl G.Edge) q p hq hp₀ hp₁
  exact cycleDual_componentCount_add_card G hG

end FK.FinitePlane
