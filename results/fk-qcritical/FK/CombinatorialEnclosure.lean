import FK.GlobalPrimalCompatibility
import FK.DualFiniteEnclosure
import FK.RotationSystemDuality

/-!
# Combinatorial enclosure by a primal circuit

On a finite cellular sphere, a primal circuit has a dual `F2` potential.  Its
two potential classes are therefore genuine dual regions whose common cut is
the circuit.  If the circuit is chosen in the boundary of an ambient-connected
dual box, one of those regions contains the whole box.  This is the Jordan-side
selection step in combinatorial form: no spherical locus or separately supplied
exterior component is used.
-/

namespace FK.Finite.PlaneMatroid.Cellular

open scoped BigOperators Classical
open Matroid
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.LabelledDualPair
open FK.Configuration

variable (P : LabelledDualPair)

/-- Exchanging primal and dual preserves a cellular sphere.  The nontrivial
boundary identity in the reversed direction was already derived from the
original one by adjointness in `RotationSystemDuality`. -/
theorem CellularSphere.swap (hS : CellularSphere P) : CellularSphere P.swap where
  nonemptyVertex := hS.nonemptyFace
  nonemptyFace := hS.nonemptyVertex
  primal_preconnected := hS.dual_preconnected
  dual_preconnected := hS.primal_preconnected
  euler := by
    unfold LabelledDualPair.swap
    dsimp only
    rw [Nat.add_comm (Fintype.card P.Vertex) (Fintype.card P.Face)]
    exact hS.euler
  boundary_boundary := by
    intro q
    exact LabelledDualPair.boundary_faceDual_coboundary_primal P hS q

/-- A primal circuit is supported by an `F2` cycle, and that cycle is the
coboundary of a potential on dual faces.  We retain the support formulation:
it identifies exactly the edges whose dual endpoints receive different values. -/
theorem exists_facePotential_of_primalCircuit (hS : CellularSphere P)
    {C : Set P.Edge} (hC : P.primal.cycleMatroid.IsCircuit C) :
    ∃ q : P.Face → F2, ∀ e : P.Edge,
      (coboundary P.faceDual q e ≠ 0 ↔ e ∈ C) := by
  have hdep : ¬ F2Independent P.primal C := by
    intro hF
    apply hC.not_indep
    exact (cycleMatroid_indep_iff_f2Independent P.primal C).mpr hF
  unfold F2Independent at hdep
  push Not at hdep
  obtain ⟨x, hxC, hxzero, hxne⟩ := hdep
  let D : Set P.Edge := {e | x e ≠ 0}
  have hDC : D ⊆ C := by
    intro e he
    exact hxC e he
  have hDdep : ¬ P.primal.cycleMatroid.Indep D := by
    intro hDI
    have hDF : F2Independent P.primal D :=
      (cycleMatroid_indep_iff_f2Independent P.primal D).mp hDI
    apply hxne
    exact hDF x (fun _ he => he) hxzero
  have hDeq : D = C := hC.eq_of_not_indep_subset hDdep hDC
  have hxker : x ∈ LinearMap.ker (boundary P.primal) := hxzero
  have hrange := LabelledDualPair.range_coboundary_primal_eq_ker_boundary_faceDual
    P.swap hS.swap
  change LinearMap.range (coboundary P.faceDual) =
    LinearMap.ker (boundary P.primal) at hrange
  rw [← hrange] at hxker
  obtain ⟨q, hq⟩ := hxker
  refine ⟨q, fun e => ?_⟩
  have hqe : coboundary P.faceDual q e = x e := congrFun hq e
  rw [hqe]
  change (e ∈ D ↔ e ∈ C)
  rw [hDeq]

/-- Every element of the two-element field is zero or one. -/
private lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  have h : ∀ z : F2, z = 0 ∨ z = 1 := by decide
  exact h a

/-- The cut of a potential class consists precisely of the edges with nonzero
coboundary. -/
theorem vertexCut_potentialClass (q : P.Face → F2) (a : F2) :
    P.faceDual.vertexCut {z | q z = a} =
      {e | coboundary P.faceDual q e ≠ 0} := by
  ext e
  change P.Edge at e
  simp only [vertexCut, Set.mem_ofPred_eq]
  change ((q (P.faceDual.source e) = a ∧ ¬q (P.faceDual.target e) = a) ∨
    (¬q (P.faceDual.source e) = a ∧ q (P.faceDual.target e) = a)) ↔
      coboundary P.faceDual q e ≠ 0
  rw [coboundary_apply P.faceDual q e]
  rcases f2_cases a with rfl | rfl <;>
    rcases f2_cases (q (P.faceDual.source e)) with hs | hs <;>
    rcases f2_cases (q (P.faceDual.target e)) with ht | ht <;>
    simp [hs, ht, CharTwo.add_self_eq_zero]

/-- Along an ambient dual walk lying in `S`, a potential whose nonzero
coboundary is contained in the cut of `S` stays constant. -/
theorem potential_eq_of_induced_walk (q : P.Face → F2) {S : Set P.Face}
    {C : Set P.Edge} (hpot : ∀ e : P.Edge,
      coboundary P.faceDual q e ≠ 0 ↔ e ∈ C)
    (hC : C ⊆ P.faceDual.vertexCut S)
    {u v : S} (w : (P.faceDual.simpleGraph.induce S).Walk u v) :
    q u.1 = q v.1 := by
  induction w with
  | nil => rfl
  | @cons u v z huv w ih =>
      have hstep : q u.1 = q v.1 := by
        change P.faceDual.simpleGraph.Adj u.1 v.1 at huv
        obtain ⟨-, e, hjoin⟩ := (P.faceDual.simpleGraph_adj_iff).mp huv
        change P.Edge at e
        apply CharTwo.add_eq_zero.mp
        by_contra hx
        rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · have hx' : coboundary P.faceDual q e ≠ 0 := by
            rw [coboundary_apply P.faceDual q e, hs, ht]
            exact hx
          have hecut : e ∈ P.faceDual.vertexCut S := hC ((hpot e).mp hx')
          have huS : P.faceDual.source e ∈ S := hs.symm ▸ u.2
          have hvS : P.faceDual.target e ∈ S := ht.symm ▸ v.2
          exact (P.faceDual.notMem_vertexCut_of_mem_of_mem huS hvS) hecut
        · have hx' : coboundary P.faceDual q e ≠ 0 := by
            rw [coboundary_apply P.faceDual q e, hs, ht, add_comm]
            exact hx
          have hecut : e ∈ P.faceDual.vertexCut S := hC ((hpot e).mp hx')
          have huS : P.faceDual.source e ∈ S := hs.symm ▸ v.2
          have hvS : P.faceDual.target e ∈ S := ht.symm ▸ u.2
          exact (P.faceDual.notMem_vertexCut_of_mem_of_mem huS hvS) hecut
      exact hstep.trans ih

/-- **Combinatorial Jordan enclosure.**  A circuit selected in the boundary of
an ambient-connected dual box encloses that entire box.  The second region is
proper, and the circuit is its complete edge cut, not merely a cycle somewhere
in the original boundary. -/
theorem exists_primalCircuit_enclosing_dualBox (hS : CellularSphere P)
    {S : Set P.Face} (hSne : S.Nonempty)
    (hSconn : (P.faceDual.simpleGraph.induce S).Preconnected)
    {e : P.Edge} (he : e ∈ P.faceDual.vertexCut S) :
    ∃ (C : Set P.Edge) (T : Set P.Face),
      C ⊆ P.faceDual.vertexCut S ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCircuit C ∧ S ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = P.faceDual.vertexCut T := by
  obtain ⟨C, hCcut, heC, hCco⟩ := P.swap.exists_isCocircuit_subset_vertexCut he
  have hcert : P.GraphicDualCertificate :=
    LabelledDualPair.graphicDualCertificate_of_cellularSphere P hS
  have hC : P.primal.cycleMatroid.IsCircuit C :=
    P.isCircuit_primal_of_isCocircuit_faceDual hcert hCco
  obtain ⟨q, hpot⟩ := exists_facePotential_of_primalCircuit P hS hC
  obtain ⟨x, hx⟩ := hSne
  let T : Set P.Face := {z | q z = q x}
  have hqconst : ∀ y ∈ S, q y = q x := by
    intro y hy
    obtain ⟨w⟩ := hSconn ⟨x, hx⟩ ⟨y, hy⟩
    exact (potential_eq_of_induced_walk P q hpot hCcut w).symm
  have hST : S ⊆ T := by
    intro y hy
    exact hqconst y hy
  have hCeq : C = P.faceDual.vertexCut T := by
    change C = P.faceDual.vertexCut {z | q z = q x}
    rw [vertexCut_potentialClass P q (q x)]
    ext f
    exact (hpot f).symm
  refine ⟨C, T, hCcut, heC, hC, hST, Set.toFinite T, ?_, hCeq⟩
  have heT : e ∈ P.faceDual.vertexCut T := by rwa [← hCeq]
  rcases heT with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨P.faceDual.target e, ht⟩
  · exact ⟨P.faceDual.source e, hs⟩

/-- Open-boundary form of combinatorial enclosure.  The carrier is also
open-connected, by the finite circuit theorem, and the enclosing region has a
nonempty exterior. -/
theorem exists_primalOpenCircuit_enclosing_dualBox (hS : CellularSphere P)
    (ω : P.primal.Configuration) {S : Set P.Face} (hSne : S.Nonempty)
    (hSconn : (P.faceDual.simpleGraph.induce S).Preconnected)
    (hSsat : P.faceDual.OpenComponentSaturated
      (dualConfig (Equiv.refl P.Edge) ω) S)
    {e : P.Edge} (he : e ∈ P.faceDual.vertexCut S) :
    ∃ (C : Set P.Edge) (T : Set P.Face),
      C ⊆ P.faceDual.vertexCut S ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCircuit C ∧ S ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = P.faceDual.vertexCut T ∧ C ⊆ P.primal.openEdgeSet ω ∧
      ∀ {u v : P.Vertex}, P.primal.VertexOnLabels C u →
        P.primal.VertexOnLabels C v →
        (P.primal.connectionGraph P.primal.freeBoundary ω).Reachable u v := by
  obtain ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq⟩ :=
    exists_primalCircuit_enclosing_dualBox P hS hSne hSconn he
  have hCopen : C ⊆ P.primal.openEdgeSet ω := by
    intro f hf
    have hd := P.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
      hSsat (hCcut hf)
    change (!ω f) = false at hd
    change ω f = true
    cases h : ω f <;> simp [h] at hd ⊢
  refine ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq, hCopen, ?_⟩
  intro u v hu hv
  have hreach := P.primal.reachable_of_cycleMatroid_isCircuit hC hu hv
  have hle : P.primal.connectionGraph P.primal.freeBoundary (P.primal.setConfig C) ≤
      P.primal.connectionGraph P.primal.freeBoundary
        (P.primal.setConfig (P.primal.openEdgeSet ω)) :=
    P.primal.connectionGraph_mono (ξ := P.primal.freeBoundary)
      (P.primal.setConfig_mono hCopen)
  rw [P.primal.setConfig_openEdgeSet] at hle
  exact hreach.mono hle

end FK.Finite.PlaneMatroid.Cellular



namespace FK.Finite.PlaneMatroid.Cellular.Rotation

open scoped Classical
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Configuration

variable {G : LabelledMultigraph} (R : RotationSphere G)

/-- Rotation-system specialization: graphic duality is constructed from the
rotation and Euler data, so no `GraphicDualCertificate` occurs as an input. -/
theorem exists_primalOpenCircuit_enclosing_dualBox_of_rotationSphere
    (ω : G.Configuration) {S : Set R.Face} (hSne : S.Nonempty)
    (hSconn : (R.dualPair.faceDual.simpleGraph.induce S).Preconnected)
    (hSsat : R.dualPair.faceDual.OpenComponentSaturated
      (dualConfig (Equiv.refl G.Edge) ω) S)
    {e : G.Edge} (he : e ∈ R.dualPair.faceDual.vertexCut S) :
    ∃ (C : Set G.Edge) (T : Set R.Face),
      C ⊆ R.dualPair.faceDual.vertexCut S ∧ e ∈ C ∧
      R.dualPair.primal.cycleMatroid.IsCircuit C ∧ S ⊆ T ∧ T.Finite ∧
      Tᶜ.Nonempty ∧ C = R.dualPair.faceDual.vertexCut T ∧
      C ⊆ R.dualPair.primal.openEdgeSet ω ∧
      ∀ {u v : G.Vertex}, R.dualPair.primal.VertexOnLabels C u →
        R.dualPair.primal.VertexOnLabels C v →
        (R.dualPair.primal.connectionGraph R.dualPair.primal.freeBoundary ω).Reachable u v := by
  exact Cellular.exists_primalOpenCircuit_enclosing_dualBox
    R.toRotationSystem.dualPair R.cellularSphere ω hSne hSconn hSsat he

end FK.Finite.PlaneMatroid.Cellular.Rotation


namespace FK.PlaneTopology

open scoped Classical
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular
open CurvatureVariance.Infra.Percolation

namespace LabelledDualPairEmbedding

variable {V F : Type*} {P : LabelledDualPair} {G : SimpleGraph V}
variable {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
variable (B : LabelledDualPairEmbedding P G GD edge)

/-- Compatible-global-window form of combinatorial enclosure.  The region and
its complete cut remain in the finite labelled window; openness and connected
carrier are transported to the actual global configuration and edge labels. -/
theorem exists_globalOpenCircuit_enclosing_dualBox
    (hS : CellularSphere P) (ω : G.edgeSet → Bool)
    {S : Set P.Face} (hSne : S.Nonempty)
    (hSconn : (P.faceDual.simpleGraph.induce S).Preconnected)
    (hSsat : P.faceDual.OpenComponentSaturated (B.dualRestriction ω) S)
    {e : P.Edge} (he : e ∈ P.faceDual.vertexCut S) :
    ∃ (C : Set P.Edge) (T : Set P.Face),
      C ⊆ P.faceDual.vertexCut S ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCircuit C ∧ S ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = P.faceDual.vertexCut T ∧
      (∀ ε ∈ B.primal.globalLabels C, ω ε = true) ∧
      OpenLabelConnected G ω (B.primal.globalLabels C) := by
  obtain ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq, hCopen, -⟩ :=
    Cellular.exists_primalOpenCircuit_enclosing_dualBox P hS
      (B.primalRestriction ω) hSne hSconn hSsat he
  refine ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq,
    B.primal.globalLabels_open hCopen, ?_⟩
  exact B.primal.openLabelConnected_global_of_cycleMatroid_isCircuit hCopen hC

end LabelledDualPairEmbedding
end FK.PlaneTopology



namespace FK.Finite.PlaneMatroid.Cellular

open scoped BigOperators Classical
open Matroid
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.LabelledDualPair

variable (P : LabelledDualPair)

/-- If a vertex cut is empty, all-open reachability preserves membership in
its defining region. -/
theorem mem_of_allOpen_reachable_of_vertexCut_eq_empty (G : LabelledMultigraph)
    {S : Set G.Vertex} (hcut : G.vertexCut S = ∅) {u v : G.Vertex}
    (huv : (G.connectionGraph G.freeBoundary G.allOpen).Reachable u v)
    (hu : u ∈ S) : v ∈ S := by
  obtain ⟨w⟩ := huv
  have heq : G.setConfig (Set.univ \ G.vertexCut S) = G.allOpen := by
    simp [hcut]
  rw [← heq] at w
  exact G.target_mem_of_walk_compl_vertexCut w hu

/-- A cut contained in a primal circuit is the entire circuit, provided the
region and its complement are nonempty.  This is the matroid-minimality form of
a bond having no proper nonempty cut underneath it. -/
theorem vertexCut_eq_of_subset_primalCircuit (hS : CellularSphere P)
    {C : Set P.Edge} (hC : P.primal.cycleMatroid.IsCircuit C)
    {U : Set P.Face} (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hsub : P.faceDual.vertexCut U ⊆ C) :
    P.faceDual.vertexCut U = C := by
  let q : P.Face → F2 := fun z => if z ∈ U then 1 else 0
  have hclass : {z | q z = 1} = U := by
    ext z
    simp [q]
  have hcut : P.faceDual.vertexCut U = {e | coboundary P.faceDual q e ≠ 0} := by
    rw [← hclass]
    exact vertexCut_potentialClass P q 1
  let x : P.Edge → F2 := coboundary P.faceDual q
  have hxzero : boundary P.primal x = 0 := by
    change boundary P.primal (coboundary P.faceDual q) = 0
    exact hS.boundary_boundary q
  have hdep : ¬ P.primal.cycleMatroid.Indep (P.faceDual.vertexCut U) := by
    intro hI
    have hF : F2Independent P.primal (P.faceDual.vertexCut U) :=
      (cycleMatroid_indep_iff_f2Independent P.primal _).mp hI
    have hx0 : x = 0 := hF x (fun e he => by
      rw [hcut]
      exact he) hxzero
    have hemempty : P.faceDual.vertexCut U = ∅ := by
      rw [hcut]
      ext e
      simp only [Set.mem_ofPred_eq, Set.notMem_empty, iff_false]
      intro he
      apply he
      change x e = 0
      have h0 := congrFun hx0 e
      change x e = 0 at h0
      exact h0
    obtain ⟨u, hu⟩ := hU
    obtain ⟨v, hv⟩ := hUc
    have huv : (P.faceDual.connectionGraph P.faceDual.freeBoundary
        P.faceDual.allOpen).Reachable u v := hS.dual_preconnected u v
    exact hv (mem_of_allOpen_reachable_of_vertexCut_eq_empty
      P.faceDual hemempty huv hu)
  exact hC.eq_of_not_indep_subset hdep hsub

/-- A proper region whose complete cut is a primal circuit is connected in
the ambient dual simple graph.  Two different induced components would give
two distinct cuts strictly below the circuit, contradicting the bond lemma. -/
theorem preconnected_region_of_primalCircuit_vertexCut (hS : CellularSphere P)
    {C : Set P.Edge} (hC : P.primal.cycleMatroid.IsCircuit C)
    {T : Set P.Face} (hCeq : C = P.faceDual.vertexCut T) :
    (P.faceDual.simpleGraph.induce T).Preconnected := by
  let G := P.faceDual.simpleGraph
  intro x y
  change (G.induce T).Reachable x y
  by_contra hxy
  let U : Set P.Face := {z | ∃ hz : z ∈ T, (G.induce T).Reachable x ⟨z, hz⟩}
  have hUT : U ⊆ T := by
    rintro z ⟨hz, -⟩
    exact hz
  have hxU : x.1 ∈ U := ⟨x.2, SimpleGraph.Reachable.refl x⟩
  have hyU : y.1 ∉ U := by
    rintro ⟨hy, hreach⟩
    exact hxy hreach
  have hprop : ∀ {z w : P.Face}, z ∈ U → w ∈ T → G.Adj z w → w ∈ U := by
    intro z w hz hw hadj
    obtain ⟨hzT, hxz⟩ := hz
    refine ⟨hw, hxz.trans (SimpleGraph.Adj.reachable ?_)⟩
    exact hadj
  let V : Set P.Face := T \ U
  have hyV : y.1 ∈ V := ⟨y.2, hyU⟩
  have hxV : x.1 ∉ V := by
    simp [V, hxU]
  have hsubU : P.faceDual.vertexCut U ⊆ C := by
    intro e he
    rw [hCeq]
    have hne : P.faceDual.source e ≠ P.faceDual.target e :=
      P.faceDual.source_ne_target_of_mem_vertexCut he
    have hadj : G.Adj (P.faceDual.source e) (P.faceDual.target e) :=
      (P.faceDual.simpleGraph_adj_iff).2 ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
    rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hsT := hUT hs
      have htT : P.faceDual.target e ∉ T := by
        intro htT
        exact ht (hprop hs htT hadj)
      exact Or.inl ⟨hsT, htT⟩
    · have htT := hUT ht
      have hsT : P.faceDual.source e ∉ T := by
        intro hsT
        exact hs (hprop ht hsT hadj.symm)
      exact Or.inr ⟨hsT, htT⟩
  have hsubV : P.faceDual.vertexCut V ⊆ C := by
    intro e he
    rw [hCeq]
    have hne : P.faceDual.source e ≠ P.faceDual.target e :=
      P.faceDual.source_ne_target_of_mem_vertexCut he
    have hadj : G.Adj (P.faceDual.source e) (P.faceDual.target e) :=
      (P.faceDual.simpleGraph_adj_iff).2 ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
    rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hsT := hs.1
      have htT : P.faceDual.target e ∉ T := by
        intro htT
        have htU : P.faceDual.target e ∈ U := by
          by_contra htUn
          exact ht ⟨htT, htUn⟩
        exact hs.2 (hprop htU hsT hadj.symm)
      exact Or.inl ⟨hsT, htT⟩
    · have htT := ht.1
      have hsT : P.faceDual.source e ∉ T := by
        intro hsT
        have hsU : P.faceDual.source e ∈ U := by
          by_contra hsUn
          exact hs ⟨hsT, hsUn⟩
        exact ht.2 (hprop hsU htT hadj)
      exact Or.inr ⟨hsT, htT⟩
  have hcutU : P.faceDual.vertexCut U = C :=
    vertexCut_eq_of_subset_primalCircuit P hS hC ⟨x.1, hxU⟩ ⟨y.1, hyU⟩ hsubU
  have hcutV : P.faceDual.vertexCut V = C :=
    vertexCut_eq_of_subset_primalCircuit P hS hC ⟨y.1, hyV⟩ ⟨x.1, hxV⟩ hsubV
  obtain ⟨e, heC⟩ := hC.nonempty
  have heT : e ∈ P.faceDual.vertexCut T := by rwa [← hCeq]
  have heU : e ∈ P.faceDual.vertexCut U := by rwa [hcutU]
  have heV : e ∈ P.faceDual.vertexCut V := by rwa [hcutV]
  rcases heT with ⟨hsT, htT⟩ | ⟨hsT, htT⟩
  · have hsU : P.faceDual.source e ∈ U := by
      rcases heU with ⟨hs, -⟩ | ⟨-, ht⟩
      · exact hs
      · exact (htT (hUT ht)).elim
    have hsV : P.faceDual.source e ∈ V := by
      rcases heV with ⟨hs, -⟩ | ⟨-, ht⟩
      · exact hs
      · exact (htT ht.1).elim
    exact hsV.2 hsU
  · have htU : P.faceDual.target e ∈ U := by
      rcases heU with ⟨hs, -⟩ | ⟨-, ht⟩
      · exact (hsT (hUT hs)).elim
      · exact ht
    have htV : P.faceDual.target e ∈ V := by
      rcases heV with ⟨hs, -⟩ | ⟨-, ht⟩
      · exact (hsT hs.1).elim
      · exact ht
    exact htV.2 htU

end FK.Finite.PlaneMatroid.Cellular



namespace FK.Finite.PlaneMatroid.Cellular

open scoped Classical
open Matroid
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.LabelledDualPair

variable (P : LabelledDualPair)

/-- Complementing a region preserves its unoriented labelled vertex cut. -/
theorem vertexCut_compl (G : LabelledMultigraph) (S : Set G.Vertex) :
    G.vertexCut Sᶜ = G.vertexCut S := by
  ext e
  simp only [vertexCut, Set.mem_compl_iff, Set.mem_ofPred_eq]
  aesop

/-- Full two-sided enclosure: both the inside containing the original box and
its complementary outside are ambient-preconnected. -/
theorem exists_primalCircuit_enclosing_connected_dualBox (hS : CellularSphere P)
    {S : Set P.Face} (hSne : S.Nonempty)
    (hSconn : (P.faceDual.simpleGraph.induce S).Preconnected)
    {e : P.Edge} (he : e ∈ P.faceDual.vertexCut S) :
    ∃ (C : Set P.Edge) (T : Set P.Face),
      C ⊆ P.faceDual.vertexCut S ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCircuit C ∧ S ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = P.faceDual.vertexCut T ∧
      (P.faceDual.simpleGraph.induce T).Preconnected ∧
      (P.faceDual.simpleGraph.induce Tᶜ).Preconnected := by
  obtain ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq⟩ :=
    exists_primalCircuit_enclosing_dualBox P hS hSne hSconn he
  have hTconn : (P.faceDual.simpleGraph.induce T).Preconnected :=
    preconnected_region_of_primalCircuit_vertexCut P hS hC hCeq
  have hCeqCompl : C = P.faceDual.vertexCut Tᶜ := by
    change Set P.faceDual.Vertex at T
    rw [hCeq]
    exact (vertexCut_compl P.faceDual T).symm
  have hTcconn : (P.faceDual.simpleGraph.induce Tᶜ).Preconnected := by
    apply preconnected_region_of_primalCircuit_vertexCut P hS hC hCeqCompl
  exact ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq, hTconn, hTcconn⟩

end FK.Finite.PlaneMatroid.Cellular



namespace FK.Finite.PlaneMatroid.Cellular

open scoped Classical
open Matroid
open FK
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.LabelledDualPair
open FK.Configuration

variable (P : LabelledDualPair)

/-- The closed-boundary property on the actual labelled open connection graph
implies saturation by its open components. -/
theorem openComponentSaturated_of_closedBoundary (G : LabelledMultigraph)
    {ω : G.Configuration} {S : Set G.Vertex}
    (h : ClosedBoundary G.simpleGraph (G.connectionGraph G.freeBoundary ω) S) :
    G.OpenComponentSaturated ω S := by
  intro e he
  by_cases hst : G.source e = G.target e
  · simp only [hst]
  have hG : G.simpleGraph.Adj (G.source e) (G.target e) :=
    (G.simpleGraph_adj_iff).2 ⟨hst, e, Or.inl ⟨rfl, rfl⟩⟩
  have hH : (G.connectionGraph G.freeBoundary ω).Adj (G.source e) (G.target e) :=
    ⟨hst, Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩
  constructor
  · intro hs
    by_contra ht
    exact h hs ht hG hH
  · intro ht
    by_contra hs
    exact h ht hs hG.symm hH.symm

/-- A nonempty proper region in a preconnected labelled graph has nonempty
vertex cut. -/
theorem nonempty_vertexCut_of_preconnected (G : LabelledMultigraph)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    {S : Set G.Vertex} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    (G.vertexCut S).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hcut
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hSc
  exact hv (mem_of_allOpen_reachable_of_vertexCut_eq_empty G hcut (hconn u v) hu)

/-- The complete finite planar package: an open-connected primal circuit, a
connected finite inside containing the prescribed dual box, a connected proper
outside, and exact incidence as the cut separating those two regions. -/
theorem exists_primalOpenCircuit_enclosing_connected_dualBox
    (hS : CellularSphere P) (ω : P.primal.Configuration)
    {S : Set P.Face} (hSne : S.Nonempty)
    (hSconn : (P.faceDual.simpleGraph.induce S).Preconnected)
    (hSsat : P.faceDual.OpenComponentSaturated
      (dualConfig (Equiv.refl P.Edge) ω) S)
    {e : P.Edge} (he : e ∈ P.faceDual.vertexCut S) :
    ∃ (C : Set P.Edge) (T : Set P.Face),
      C ⊆ P.faceDual.vertexCut S ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCircuit C ∧ S ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = P.faceDual.vertexCut T ∧
      (P.faceDual.simpleGraph.induce T).Preconnected ∧
      (P.faceDual.simpleGraph.induce Tᶜ).Preconnected ∧
      C ⊆ P.primal.openEdgeSet ω ∧
      ∀ {u v : P.Vertex}, P.primal.VertexOnLabels C u →
        P.primal.VertexOnLabels C v →
        (P.primal.connectionGraph P.primal.freeBoundary ω).Reachable u v := by
  obtain ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq, hTconn, hTcconn⟩ :=
    exists_primalCircuit_enclosing_connected_dualBox P hS hSne hSconn he
  have hCopen : C ⊆ P.primal.openEdgeSet ω := by
    intro f hf
    have hd := P.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
      hSsat (hCcut hf)
    change (!ω f) = false at hd
    change ω f = true
    cases h : ω f <;> simp [h] at hd ⊢
  refine ⟨C, T, hCcut, heC, hC, hST, hTfin, hTproper, hCeq,
    hTconn, hTcconn, hCopen, ?_⟩
  intro u v hu hv
  have hreach := P.primal.reachable_of_cycleMatroid_isCircuit hC hu hv
  have hle : P.primal.connectionGraph P.primal.freeBoundary (P.primal.setConfig C) ≤
      P.primal.connectionGraph P.primal.freeBoundary
        (P.primal.setConfig (P.primal.openEdgeSet ω)) :=
    P.primal.connectionGraph_mono (ξ := P.primal.freeBoundary)
      (P.primal.setConfig_mono hCopen)
  rw [P.primal.setConfig_openEdgeSet] at hle
  exact hreach.mono hle

/-- Direct adapter for the finite regions of a labelled closed-boundary
exhaustion.  Its connectedness and saturation inputs are proved from `E`. -/
theorem exists_primalOpenCircuit_enclosing_closedBoundaryRegion
    (hS : CellularSphere P) (ω : P.primal.Configuration)
    (E : ClosedBoundaryExhaustion P.faceDual.simpleGraph
      (P.faceDual.connectionGraph P.faceDual.freeBoundary
        (dualConfig (Equiv.refl P.Edge) ω))) (n : ℕ)
    {e : P.Edge} (he : e ∈ P.faceDual.vertexCut (E.region n)) :
    ∃ (C : Set P.Edge) (T : Set P.Face),
      C ⊆ P.faceDual.vertexCut (E.region n) ∧ e ∈ C ∧
      P.primal.cycleMatroid.IsCircuit C ∧ E.region n ⊆ T ∧ T.Finite ∧
      Tᶜ.Nonempty ∧ C = P.faceDual.vertexCut T ∧
      (P.faceDual.simpleGraph.induce T).Preconnected ∧
      (P.faceDual.simpleGraph.induce Tᶜ).Preconnected ∧
      C ⊆ P.primal.openEdgeSet ω ∧
      ∀ {u v : P.Vertex}, P.primal.VertexOnLabels C u →
        P.primal.VertexOnLabels C v →
        (P.primal.connectionGraph P.primal.freeBoundary ω).Reachable u v := by
  have hSne : (E.region n).Nonempty := by
    obtain ⟨x⟩ := (E.connected n).nonempty
    exact ⟨x.1, x.2⟩
  have hSsat : P.faceDual.OpenComponentSaturated
      (dualConfig (Equiv.refl P.Edge) ω) (E.region n) := by
    apply openComponentSaturated_of_closedBoundary
    exact E.closed n
  exact exists_primalOpenCircuit_enclosing_connected_dualBox P hS ω
    hSne (E.connected n).preconnected hSsat he

end FK.Finite.PlaneMatroid.Cellular



namespace FK.Finite.PlaneMatroid.Cellular.Rotation

open scoped Classical
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Configuration
open Equiv.Perm

variable {G : LabelledMultigraph} (R : RotationSystem G)

/-- Reversing a dart of an allowed label is an allowed dual reachability step. -/
theorem reachable_faceOf_reverse_of_mem (A : Set G.Edge) {d : Dart G}
    (hd : d.1 ∈ A) :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      (R.dualPair.faceDual.setConfig A)).Reachable
      (R.faceOf d) (R.faceOf (reverse G d)) := by
  by_cases h : R.faceOf d = R.faceOf (reverse G d)
  · rw [h]
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    refine ⟨h, Or.inr ⟨d.1, ?_, ?_⟩⟩
    · simp only [LabelledMultigraph.setConfig, decide_eq_true_eq]
      exact hd
    · rcases d with ⟨e, b⟩
      cases b
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩

/-- Rotation gives an allowed face-dual step whenever the old dart's label is
allowed. -/
theorem reachable_faceOf_rotation_of_mem (A : Set G.Edge) {d : Dart G}
    (hd : d.1 ∈ A) :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      (R.dualPair.faceDual.setConfig A)).Reachable
      (R.faceOf d) (R.faceOf (R.rotation d)) := by
  rw [← R.faceOf_reverse_eq_faceOf_rotation]
  exact reachable_faceOf_reverse_of_mem R A hd

/-- Vertex labels are unchanged by powers of the rotation. -/
theorem vertex_rotation_pow (d : Dart G) (n : ℕ) :
    vertex G ((R.rotation ^ n) d) = vertex G d := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, R.vertex_rotation]
      exact ih

/-- A local rotation cycle lifts to a dual path on any label set containing
all darts at the vertex. -/
theorem reachable_faceOf_sameCycle_of_mem (A : Set G.Edge) {u : G.Vertex}
    (hu : ∀ d : Dart G, vertex G d = u → d.1 ∈ A)
    {d d' : Dart G} (hd : vertex G d = u)
    (h : R.rotation.SameCycle d d') :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      (R.dualPair.faceDual.setConfig A)).Reachable (R.faceOf d) (R.faceOf d') := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      apply ih.trans
      apply reachable_faceOf_rotation_of_mem R
      apply hu
      rw [vertex_rotation_pow R]
      exact hd

/-- A clear primal adjacency lifts to a dual path on the same allowed labels
between arbitrary darts at its endpoints. -/
theorem reachable_faceOf_of_adj_of_mem {A : Set G.Edge} {u v : G.Vertex}
    (w : (G.connectionGraph G.freeBoundary (G.setConfig A)).Adj u v)
    (hu : ∀ d : Dart G, vertex G d = u → d.1 ∈ A)
    (hv : ∀ d : Dart G, vertex G d = v → d.1 ∈ A)
    {d d' : Dart G} (hd : vertex G d = u) (hd' : vertex G d' = v) :
    (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
      (R.dualPair.faceDual.setConfig A)).Reachable (R.faceOf d) (R.faceOf d') := by
  rcases w.2 with hfree | ⟨e, he, hjoin⟩
  · exact (w.1 hfree).elim
  · rcases hjoin with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · have hdu : vertex G d = vertex G (e, false) := by
        rw [hd]
        exact hs.symm
      have hda := reachable_faceOf_sameCycle_of_mem R A hu hd
        (R.sameCycle_rotation d (e, false) hdu)
      have hab : (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
          (R.dualPair.faceDual.setConfig A)).Reachable
          (R.faceOf (e, false)) (R.faceOf (e, true)) := by
        simpa [reverse] using reachable_faceOf_reverse_of_mem R A (d := (e, false))
          (hu (e, false) hs)
      have hbd := reachable_faceOf_sameCycle_of_mem R A hv (d := (e, true)) (d' := d')
        ht
        (R.sameCycle_rotation (e, true) d' (ht.trans hd'.symm))
      exact (hda.trans hab).trans hbd
    · have hdu : vertex G d = vertex G (e, true) := by
        rw [hd]
        exact hs.symm
      have hda := reachable_faceOf_sameCycle_of_mem R A hu hd
        (R.sameCycle_rotation d (e, true) hdu)
      have hab : (R.dualPair.faceDual.connectionGraph R.dualPair.faceDual.freeBoundary
          (R.dualPair.faceDual.setConfig A)).Reachable
          (R.faceOf (e, true)) (R.faceOf (e, false)) := by
        simpa [reverse] using reachable_faceOf_reverse_of_mem R A (d := (e, true))
          (hu (e, true) hs)
      have hbd := reachable_faceOf_sameCycle_of_mem R A hv (d := (e, false)) (d' := d')
        ht
        (R.sameCycle_rotation (e, false) d' (ht.trans hd'.symm))
      exact (hda.trans hab).trans hbd

end FK.Finite.PlaneMatroid.Cellular.Rotation

namespace FK.Finite.PlaneMatroid.Cellular

open scoped Classical
open Matroid
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.LabelledDualPair
open FK.Configuration

variable (P : LabelledDualPair)

/-- A dual face potential is constant along every dual path avoiding its
nonzero-coboundary labels. -/
theorem potential_eq_of_reachable_compl (q : P.Face → F2) {C : Set P.Edge}
    (hpot : ∀ e : P.Edge, coboundary P.faceDual q e ≠ 0 ↔ e ∈ C)
    {f g : P.Face}
    (hfg : (P.faceDual.connectionGraph P.faceDual.freeBoundary
      (P.faceDual.setConfig Cᶜ)).Reachable f g) : q f = q g := by
  change Set P.faceDual.Edge at C
  obtain ⟨w⟩ := hfg
  induction w with
  | nil => rfl
  | @cons a b c hab w ih =>
      have hstep : q a = q b := by
        rcases hab.2 with hfree | ⟨e, he, hjoin⟩
        · exact (hab.1 hfree).elim
        · have heC : e ∉ C := by
            simpa [LabelledMultigraph.setConfig] using he
          have hz : coboundary P.faceDual q e = 0 := by
            by_contra hn
            exact heC ((hpot e).mp hn)
          rw [coboundary_apply P.faceDual q e] at hz
          have hq : q (P.faceDual.source e) = q (P.faceDual.target e) :=
            CharTwo.add_eq_zero.mp hz
          rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
          · rw [hs, ht] at hq
            exact hq
          · rw [hs, ht] at hq
            exact hq.symm
      exact hstep.trans ih

end FK.Finite.PlaneMatroid.Cellular

namespace FK.Finite.PlaneMatroid.Cellular.Rotation

open scoped Classical
open Matroid
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular
open FK.Configuration

variable {G : LabelledMultigraph} (R : RotationSystem G)

/-- All faces incident to a primal vertex have the prescribed potential value. -/
def FaceInterior (q : R.Face → F2) (a : F2) (v : G.Vertex) : Prop :=
  ∀ d : Dart G, vertex G d = v → q (R.faceOf d) = a

/-- Every dart at a clear vertex avoids the circuit. -/
def ClearVertex (C : Set G.Edge) (v : G.Vertex) : Prop :=
  ∀ d : Dart G, vertex G d = v → d.1 ∈ Cᶜ

/-- A non-clear dart supplies the required circuit incidence. -/
theorem vertexOnLabels_of_not_clearVertex {C : Set G.Edge} {v : G.Vertex}
    (h : ¬ ClearVertex C v) : G.VertexOnLabels C v := by
  unfold ClearVertex at h
  push Not at h
  obtain ⟨d, hd, hdC⟩ := h
  have heC : d.1 ∈ C := by simpa using hdC
  rcases d with ⟨e, b⟩
  cases b
  · exact ⟨e, heC, Or.inl hd.symm⟩
  · exact ⟨e, heC, Or.inr hd.symm⟩

/-- A clear adjacency outside `C` transports the all-incident-faces interior. -/
theorem faceInterior_of_adj_compl {C : Set G.Edge}
    (q : R.Face → F2) (a : F2)
    (hpot : ∀ e : G.Edge, coboundary R.dualPair.faceDual q e ≠ 0 ↔ e ∈ C)
    {u v : G.Vertex}
    (w : (G.connectionGraph G.freeBoundary (G.setConfig Cᶜ)).Adj u v)
    (huClear : ClearVertex C u) (hvClear : ClearVertex C v)
    (hu : FaceInterior R q a u) : FaceInterior R q a v := by
  intro d' hd'
  rcases w.2 with hfree | ⟨e, he, hjoin⟩
  · exact (w.1 hfree).elim
  · rcases hjoin with ⟨hs, ht⟩ | ⟨ht, hs⟩
    · have hd : vertex G (e, false) = u := hs
      have hr := reachable_faceOf_of_adj_of_mem R w huClear hvClear hd hd'
      have hq := potential_eq_of_reachable_compl R.dualPair q hpot hr
      rw [← hq]
      exact hu (e, false) hd
    · have hd : vertex G (e, true) = u := hs
      have hr := reachable_faceOf_of_adj_of_mem R w huClear hvClear hd hd'
      have hq := potential_eq_of_reachable_compl R.dualPair q hpot hr
      rw [← hq]
      exact hu (e, true) hd

/-- **Sealed combinatorial path exit.**  An open primal walk from the
all-incident-faces interior to a vertex outside that class reaches a vertex
incident with the circuit.  The returned vertex is connected to the source by
the already traversed open prefix. -/
theorem exists_vertexOnLabels_of_reachable_not_faceInterior
    {C : Set G.Edge} (q : R.Face → F2) (α : F2)
    (hpot : ∀ e : G.Edge, coboundary R.dualPair.faceDual q e ≠ 0 ↔ e ∈ C)
    {ω : G.Configuration} {u v : G.Vertex}
    (huv : (G.connectionGraph G.freeBoundary ω).Reachable u v)
    (hu : FaceInterior R q α u) (hv : ¬ FaceInterior R q α v) :
    ∃ z : G.Vertex, G.VertexOnLabels C z ∧
      (G.connectionGraph G.freeBoundary ω).Reachable u z := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact (hv hu).elim
  | @cons a b c hab w ih =>
      by_cases haClear : ClearVertex C a
      · by_cases hbClear : ClearVertex C b
        · have hab' : (G.connectionGraph G.freeBoundary
              (G.setConfig Cᶜ)).Adj a b := by
            rcases hab.2 with hfree | ⟨e, he, hjoin⟩
            · exact (hab.1 hfree).elim
            · have heC : e ∈ Cᶜ := by
                rcases hjoin with ⟨hs, -⟩ | ⟨-, ht⟩
                · exact haClear (e, false) hs
                · exact haClear (e, true) ht
              refine ⟨hab.1, Or.inr ⟨e, ?_, hjoin⟩⟩
              simp [LabelledMultigraph.setConfig, heC]
          have hbi := faceInterior_of_adj_compl R q α hpot hab' haClear hbClear hu
          obtain ⟨z, hz, hzb⟩ := ih hbi hv
          exact ⟨z, hz, (SimpleGraph.Adj.reachable hab).trans hzb⟩
        · exact ⟨b, vertexOnLabels_of_not_clearVertex hbClear,
            SimpleGraph.Adj.reachable hab⟩
      · exact ⟨a, vertexOnLabels_of_not_clearVertex haClear,
          SimpleGraph.Reachable.refl _⟩

end FK.Finite.PlaneMatroid.Cellular.Rotation
