import FK.GraphConnectionTransport

/-! Nested stage connections in the outer finite graph. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture

universe u v

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- Close one labelled global edge while retaining all others. -/
noncomputable def closeGlobalEdge (e : G.edgeSet) (ω : G.edgeSet → Bool) : G.edgeSet → Bool :=
  fun f => if f = e then false else ω f

@[simp] lemma closeGlobalEdge_self (e : G.edgeSet) (ω : G.edgeSet → Bool) :
    closeGlobalEdge e ω e = false := by
  simp [closeGlobalEdge]

@[simp] lemma closeGlobalEdge_of_ne (e f : G.edgeSet) (ω : G.edgeSet → Bool) (h : f ≠ e) :
    closeGlobalEdge e ω f = ω f := by
  simp [closeGlobalEdge, h]

lemma offConfiguration_eq_closeGlobalEdge {E : Type*} (B : FiniteBox E)
    (α : B.BoundaryPartition) (e : B.edges) (ω : Configuration E) :
    Glauber.FKBridge.offConfiguration B.graph α e ((B.splitOff e ω).2) =
      (fun f => if f = e then false else ω f.1) := by
  funext f
  by_cases h : f = e
  · subst f
    simp [Glauber.FKBridge.offConfiguration, Glauber.configSplit]
  · simp [Glauber.FKBridge.offConfiguration, Glauber.configSplit, h]
    rfl

lemma withEdge_offConfiguration {E : Type*} (B : FiniteBox E)
    (α : B.BoundaryPartition) (e : B.edges) (o : Glauber.OffConfig Bool B.edges e) :
    FiniteFiber.withEdge e false (Glauber.FKBridge.offConfiguration B.graph α e o) =
      Glauber.FKBridge.offConfiguration B.graph α e o := by
  funext j
  by_cases hj : j = e
  · subst j
    simp [Glauber.FKBridge.offConfiguration, Glauber.configSplit, FiniteFiber.withEdge]
  · simp [Glauber.FKBridge.offConfiguration, Glauber.configSplit, FiniteFiber.withEdge, hj]

section Stage

variable {B C : FiniteBox G.edgeSet} (N : NestedBox B C)
variable (data : SimpleGraphBoxData G (fun _ : ℕ => C))
variable (hinj : Function.Injective (data.vertex 0))

lemma stage_specificationConnectionEvent_iff_outer
    (a : C.BoundaryPartition) (e : B.edges) (ω : G.edgeSet → Bool) :
    MovingClopenRate.FiniteBox.specificationConnectionEvent B (inducedBoundary N a) e
        ((closeGlobalEdge (e.1 : G.edgeSet) ω)) ↔
      (C.graph.connectionGraph a
        (fun f => (closeGlobalEdge (e.1 : G.edgeSet) ω) f.1)).Reachable
          (N.vert (B.source e)) (N.vert (B.target e)) := by
  letI : DecidableEq B.edges := Classical.decEq _
  let ec : C.edges := ⟨e.1, N.edge_sub e.1 e.2⟩
  let Ω : C.graph.Configuration := fun f =>
    (closeGlobalEdge ec ω) f.1
  have hAB : FK.Finite.SpecificationNesting.fixedGraph N.ide a Ω ≤
      C.graph.connectionGraph a Ω :=
    C.graph.connectionGraph_mono (FK.Finite.SpecificationNesting.interiorClosed_le N.ide Ω)
  have hR : ∀ u v, (C.graph.connectionGraph a Ω).Adj u v →
      (FK.Finite.SpecificationNesting.fixedGraph N.ide a Ω).Adj u v ∨
        (u ∈ N.dom ∧ v ∈ N.dom) := by
    intro u v huv
    obtain ⟨hne, hwire | ⟨f, hf, hjoin⟩⟩ := huv
    · exact Or.inl ⟨hne, Or.inl hwire⟩
    · by_cases hfI : f ∈ N.ide
      · refine Or.inr ⟨?_, ?_⟩
        · rcases hjoin with h1 | h1
          · exact h1.1 ▸ (N.hdom ⟨f, hfI⟩).1
          · exact h1.2 ▸ (N.hdom ⟨f, hfI⟩).2
        · rcases hjoin with h1 | h1
          · exact h1.2 ▸ (N.hdom ⟨f, hfI⟩).2
          · exact h1.1 ▸ (N.hdom ⟨f, hfI⟩).1
      · exact Or.inl ⟨hne, Or.inr ⟨f, by
          simp [FK.Finite.SpecificationNesting.interiorClosed, hfI, hf], hjoin⟩⟩
  have hsub := FK.Finite.SpecificationNesting.regionGraph_reachable_iff_subBox
    (dom := N.dom) (I := N.ide) (hdom := N.hdom) a Ω
  have hreg := FK.Finite.SpecificationNesting.regionGraph_reachable_iff hAB hR
  let offB : B.graph.Configuration := Glauber.FKBridge.offConfiguration B.graph
    (inducedBoundary N a
      ((B.splitOff e ((closeGlobalEdge (e.1 : G.edgeSet) ω))).1)) e
    ((B.splitOff e ((closeGlobalEdge (e.1 : G.edgeSet) ω))).2)
  let Ω : C.graph.Configuration := fun f =>
    (closeGlobalEdge (e.1 : G.edgeSet) ω) f.1
  have hcfg : (B.graph.transportConfig N.vertEquiv N.edgeEquiv).symm offB =
      FK.Finite.SpecificationNesting.restrictI N.ide Ω := by
    funext f
    by_cases hf : f.1 = e.1
    · have hfe : N.edgeEquiv f = e := by
        apply Subtype.ext
        exact hf
      change offB (N.edgeEquiv f) = Ω f.1
      dsimp only [offB]
      rw [offConfiguration_eq_closeGlobalEdge B
        (inducedBoundary N a
          ((B.splitOff e ((closeGlobalEdge (e.1 : G.edgeSet) ω))).1)) e
        ((closeGlobalEdge (e.1 : G.edgeSet) ω))]
      simp_all [offB, FK.Finite.SpecificationNesting.restrictI, ec, closeGlobalEdge, Ω, hfe]
    · have hfe : N.edgeEquiv f ≠ e := by
        intro heq
        apply hf
        exact congrArg (fun z : B.edges => z.1) heq
      have hmem : (N.edgeEquiv f).1 ∈ C.edges := N.edge_sub _ (N.edgeEquiv f).2
      change offB (N.edgeEquiv f) = Ω f.1
      dsimp only [offB]
      rw [offConfiguration_eq_closeGlobalEdge B
        (inducedBoundary N a
          ((B.splitOff e ((closeGlobalEdge (e.1 : G.edgeSet) ω))).1)) e
        ((closeGlobalEdge (e.1 : G.edgeSet) ω))]
      simp_all [offB, FK.Finite.SpecificationNesting.restrictI, ec, closeGlobalEdge, hfe, Ω,
        closeOutside, hmem]
      rfl
  have hcomb : FK.Finite.SpecificationNesting.combine N.ide
      ((B.graph.transportConfig N.vertEquiv N.edgeEquiv).symm offB)
      (annulusOfExterior N
        (FKLimit.exteriorRestriction B.edges
          ((closeGlobalEdge (e.1 : G.edgeSet) ω)))) = Ω := by
    funext f
    by_cases hf : f ∈ N.ide
    · simp only [FK.Finite.SpecificationNesting.combine, hf, dite_true]
      exact congrFun hcfg ⟨f, hf⟩
    · simp only [FK.Finite.SpecificationNesting.combine, hf, dite_false]
      rfl
  have hpart : transportBoundary N.vertEquiv N.edgeEquiv
      (inducedBoundary N a
        (FKLimit.exteriorRestriction B.edges
          ((closeGlobalEdge (e.1 : G.edgeSet) ω)))) =
      FK.Finite.SpecificationNesting.inducedPartition N.dom N.ide a Ω := by
    rw [transportBoundary_inducedBoundary]
    have h := NestedMixture.inducedPartition_eq_exteriorPartition
      (dom := N.dom) (I := N.ide) (α := a)
      ((B.graph.transportConfig N.vertEquiv N.edgeEquiv).symm offB)
      (annulusOfExterior N (FKLimit.exteriorRestriction B.edges
        ((closeGlobalEdge (e.1 : G.edgeSet) ω))))
    rw [hcomb] at h
    exact h.symm
  have hsub := FK.Finite.SpecificationNesting.regionGraph_reachable_iff_subBox
    (dom := N.dom) (I := N.ide) (hdom := N.hdom) a Ω
  have hreg := FK.Finite.SpecificationNesting.regionGraph_reachable_iff hAB hR
  simp only [MovingClopenRate.FiniteBox.specificationConnectionEvent, Set.mem_setOf_eq,
    FK.Finite.Conditional.endpointsConnectedWithout, withEdge_offConfiguration,
    Equiv.apply_symm_apply]
  have hoff : FiniteFiber.withEdge e false offB = offB := by
    funext j
    by_cases hj : j = e
    · subst j
      simp [offB, FiniteFiber.withEdge, Glauber.FKBridge.offConfiguration,
        offConfiguration_eq_closeGlobalEdge]
    · simp [offB, FiniteFiber.withEdge, hj, Glauber.FKBridge.offConfiguration]
  simp only [offB] at hoff ⊢
  have hnorm : (B.graph.connectionGraph
      (inducedBoundary N a
        ((B.splitOff e ((closeGlobalEdge (e.1 : G.edgeSet) ω))).1))
      (FiniteFiber.withEdge e false offB)).Reachable (B.source e) (B.target e) ↔
    (B.graph.connectionGraph
      (inducedBoundary N a
        ((B.splitOff e ((closeGlobalEdge (e.1 : G.edgeSet) ω))).1)) offB).Reachable
      (B.source e) (B.target e) := by
    rw [hoff]
  let Φ := connectionIso B.graph N.vertEquiv N.edgeEquiv
    (inducedBoundary N a
      (FKLimit.exteriorRestriction B.edges
        ((closeGlobalEdge (e.1 : G.edgeSet) ω))))
    ((B.graph.transportConfig N.vertEquiv N.edgeEquiv).symm offB)
  have hΦ := Φ.reachable_iff (u := N.vertEquiv.symm (B.source e)) (v := N.vertEquiv.symm (B.target e))
  simp only [Equiv.apply_symm_apply] at hΦ
  apply Iff.trans hnorm
  have hs : Φ (N.vertEquiv.symm (B.source e)) = B.source e := by
    change N.vertEquiv (N.vertEquiv.symm (B.source e)) = B.source e
    exact N.vertEquiv.apply_symm_apply _
  have ht : Φ (N.vertEquiv.symm (B.target e)) = B.target e := by
    change N.vertEquiv (N.vertEquiv.symm (B.target e)) = B.target e
    exact N.vertEquiv.apply_symm_apply _
  rw [hs, ht] at hΦ
  simp only [← N.subBox_eq_transport, hpart, hcfg, ← hsub, hreg] at hΦ
  apply Iff.trans hΦ
  have hfinal : ((FK.Finite.SpecificationNesting.subBox N.dom N.ide N.hdom).connectionGraph
      (FK.Finite.SpecificationNesting.inducedPartition N.dom N.ide a Ω)
      (FK.Finite.SpecificationNesting.restrictI N.ide Ω)).Reachable
        (N.vertEquiv.symm (B.source e)) (N.vertEquiv.symm (B.target e)) ↔
      (C.graph.connectionGraph a Ω).Reachable
        (N.vert (B.source e)) (N.vert (B.target e)) := by
    exact (hsub (N.vertEquiv.symm (B.source e)) (N.vertEquiv.symm (B.target e))).symm.trans
      (hreg (N.vertEquiv.symm (B.source e)) (N.vertEquiv.symm (B.target e)))
  have hsource : (B.graph.transport N.vertEquiv N.edgeEquiv).source =
      (FK.Finite.SpecificationNesting.subBox N.dom N.ide N.hdom).source :=
    N.transport_source_eq
  have htarget : (B.graph.transport N.vertEquiv N.edgeEquiv).target =
      (FK.Finite.SpecificationNesting.subBox N.dom N.ide N.hdom).target :=
    N.transport_target_eq
  let P : Setoid N.dom := FK.Finite.SpecificationNesting.inducedPartition N.dom N.ide a Ω
  let R : N.ide → Bool := FK.Finite.SpecificationNesting.restrictI N.ide Ω
  have hgraph : (B.graph.transport N.vertEquiv N.edgeEquiv).connectionGraph P R =
      (FK.Finite.SpecificationNesting.subBox N.dom N.ide N.hdom).connectionGraph P R := by
    ext u v
    simp only [FK.Finite.LabelledMultigraph.connectionGraph,
      FK.Finite.LabelledMultigraph.Joins, hsource, htarget]
    rfl
  dsimp only [P, R] at hgraph
  rw [hgraph]
  exact hfinal


end Stage

end FK.NestedFinDLR
