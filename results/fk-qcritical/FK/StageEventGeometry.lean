import FK.StageEscapeGeometry

/-! Finite stage/lower connection events and their exact specification forms. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ClusterEscape
open FK.NestedMixture

universe u v

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- Restrict global box embeddings to one constant finite box. -/
noncomputable def constantBoxData {box : ℕ → FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G box) (n : ℕ) :
    SimpleGraphBoxData G (fun _ : ℕ => box n) where
  vertex _ := data.vertex n
  endpoint _ := data.endpoint n

@[simp] lemma constantBoxData_vertex {box : ℕ → FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G box) (n : ℕ) (x : (box n).Vertex) :
    (constantBoxData data n).vertex 0 x = data.vertex n x := rfl

/-- Closing a box edge does not change its exterior/off-edge split. -/
lemma splitOff_closeGlobalEdge (B : FiniteBox G.edgeSet)
    (e : B.edges) (ω : Configuration G.edgeSet) :
    B.splitOff e (closeGlobalEdge (e.1 : G.edgeSet) ω) = B.splitOff e ω := by
  apply Prod.ext
  · funext f
    change closeGlobalEdge (e.1 : G.edgeSet) ω f.1 = ω f.1
    apply closeGlobalEdge_of_ne
    intro h
    exact f.2 (h.symm ▸ e.2)
  · funext j
    change closeGlobalEdge (e.1 : G.edgeSet) ω j.1.1 = ω j.1.1
    apply closeGlobalEdge_of_ne
    intro h
    exact j.2 (Subtype.ext h)

/-- The specification connection event is unchanged by explicitly closing its
labelled edge first. -/
lemma specificationConnectionEvent_closeGlobalEdge (B : FiniteBox G.edgeSet)
    (α : B.Exterior → B.BoundaryPartition) (e : B.edges) (ω : Configuration G.edgeSet) :
    MovingClopenRate.FiniteBox.specificationConnectionEvent B α e
        (closeGlobalEdge (e.1 : G.edgeSet) ω) ↔
      MovingClopenRate.FiniteBox.specificationConnectionEvent B α e ω := by
  change FK.Finite.Conditional.endpointsConnectedWithout B.graph
      (α ((B.splitOff e (closeGlobalEdge (e.1 : G.edgeSet) ω)).1)) e
      (Glauber.FKBridge.offConfiguration B.graph
        (α ((B.splitOff e (closeGlobalEdge (e.1 : G.edgeSet) ω)).1)) e
        ((B.splitOff e (closeGlobalEdge (e.1 : G.edgeSet) ω)).2)) ↔
    FK.Finite.Conditional.endpointsConnectedWithout B.graph
      (α ((B.splitOff e ω).1)) e
      (Glauber.FKBridge.offConfiguration B.graph
        (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
  rw [splitOff_closeGlobalEdge]

section OuterStage

variable {B C : FiniteBox G.edgeSet} (N : NestedBox B C)

/-- The nested stage connection event, expressed directly in the outer box. -/
def outerStageConnectionEvent (a : C.BoundaryPartition) (e : B.edges) :
    Set (G.edgeSet → Bool) :=
  {ω | (C.graph.connectionGraph a
    (fun f => closeGlobalEdge (e.1 : G.edgeSet) ω f.1)).Reachable
      (N.vert (B.source e)) (N.vert (B.target e))}

/-- The outer-graph event is exactly the induced-specification event. -/
lemma outerStageConnectionEvent_eq_specification (a : C.BoundaryPartition) (e : B.edges)
    (ω : G.edgeSet → Bool) :
    ω ∈ outerStageConnectionEvent N a e ↔
      MovingClopenRate.FiniteBox.specificationConnectionEvent B (inducedBoundary N a) e ω := by
  change (C.graph.connectionGraph a
    (fun f => closeGlobalEdge (e.1 : G.edgeSet) ω f.1)).Reachable
      (N.vert (B.source e)) (N.vert (B.target e)) ↔ _
  rw [← stage_specificationConnectionEvent_iff_outer N a e ω]
  exact specificationConnectionEvent_closeGlobalEdge B (inducedBoundary N a) e ω

/-- Outer stage events are finite-coordinate, hence clopen. -/
lemma isClopen_outerStageConnectionEvent (a : C.BoundaryPartition) (e : B.edges) :
    IsClopen (outerStageConnectionEvent N a e) := by
  apply FKLimit.DependsOnCoordinates.isClopen (S := C.edges)
  intro ω η hωη
  have hcfg : (fun f : C.edges => closeGlobalEdge (e.1 : G.edgeSet) ω f.1) =
      (fun f : C.edges => closeGlobalEdge (e.1 : G.edgeSet) η f.1) := by
    funext f
    by_cases hf : f.1 = (e.1 : G.edgeSet)
    · simp [closeGlobalEdge, hf]
    · simp [closeGlobalEdge_of_ne, hf, hωη f.1 f.2]
  change (C.graph.connectionGraph a
    (fun f => closeGlobalEdge (e.1 : G.edgeSet) ω f.1)).Reachable
      (N.vert (B.source e)) (N.vert (B.target e)) ↔
    (C.graph.connectionGraph a
    (fun f => closeGlobalEdge (e.1 : G.edgeSet) η f.1)).Reachable
      (N.vert (B.source e)) (N.vert (B.target e))
  rw [hcfg]

end OuterStage

/-- Open connection inside a finite vertex set after closing one labelled edge. -/
def offEdgeConnectionInside (e : G.edgeSet) (K : Finset V) (x y : V) :
    Set (G.edgeSet → Bool) :=
  {ω | OpenConnected G (closeGlobalEdge e ω) (innerEdges K) x y}

/-- These lower events depend only on the finite set of edges inside `K`. -/
lemma isClopen_offEdgeConnectionInside (e : G.edgeSet) (K : Finset V) (x y : V)
    (S : Finset G.edgeSet) (hS : ∀ f : G.edgeSet, f.1 ∈ innerEdges K → f ∈ S) :
    IsClopen (offEdgeConnectionInside e K x y) := by
  apply FKLimit.DependsOnCoordinates.isClopen (S := S)
  intro ω η hωη
  have hcfg : ∀ f : G.edgeSet, f.1 ∈ innerEdges K →
      closeGlobalEdge e ω f = closeGlobalEdge e η f := by
    intro f hf
    by_cases hfe : f = e
    · simp [closeGlobalEdge, hfe]
    · simp [closeGlobalEdge_of_ne, hfe, hωη f (hS f hf)]
  constructor
  · intro h
    exact h.congr hcfg
  · intro h
    exact h.congr (fun f hf => (hcfg f hf).symm)

/-- Monotonicity of the lower events in the finite vertex exhaustion. -/
lemma offEdgeConnectionInside_mono (e : G.edgeSet) {K : ℕ → Finset V}
    (hK : Monotone K) (x y : V) : Monotone (fun m => offEdgeConnectionInside e (K m) x y) := by
  intro m n hmn ω hω
  apply OpenConnected.mono_edges hω
  intro f hf
  obtain ⟨u, hu, v, hv, rfl⟩ := hf
  exact ⟨u, hK hmn hu, v, hK hmn hv, rfl⟩

end FK.NestedFinDLR


namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ClusterEscape
open CurvatureVariance.Infra.Percolation

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V]

/-- An ordinary walk supported in `K` is open for `innerEdges K` whenever it is
open globally. -/
lemma openConnected_innerEdges_of_walk {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {x y : V} (p : G.Walk x y) (hp : IsOpenIn ω Set.univ p) (K : Finset V)
    (hsupp : ∀ w ∈ p.support, w ∈ K) : OpenConnected G ω (innerEdges K) x y := by
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons u v w hadj p ih =>
      rw [isOpenIn_cons] at hp
      have hvK : v ∈ K := hsupp v (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem u p.start_mem_support)
      have huK : u ∈ K := hsupp u (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_self)
      have hstep : OpenConnected G ω (innerEdges K) u v :=
        OpenConnected.of_adj hadj (mem_innerEdges_iff.mpr ⟨huK, hvK⟩) hp.1.2
      exact hstep.trans (ih hp.2 (fun z hz => hsupp z (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem u hz)))

/-- Finite inner-path events exhaust global off-edge connection along a nested
cofinal family of finite vertex sets. -/
lemma exists_offEdgeConnectionInside_iff {G : SimpleGraph V} (e : G.edgeSet)
    {K : ℕ → Finset V} (hK : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N)
    (x y : V) (ω : G.edgeSet → Bool) :
    (∃ m, ω ∈ offEdgeConnectionInside e (K m) x y) ↔
      OpenConnected G (closeGlobalEdge e ω) Set.univ x y := by
  constructor
  · rintro ⟨m, hm⟩
    exact OpenConnected.mono_edges hm (Set.subset_univ _)
  · intro h
    rcases h with ⟨p, hp⟩
    obtain ⟨m, hm⟩ := exists_finset_subset hK hcov p.support.toFinset
    refine ⟨m, openConnected_innerEdges_of_walk p hp (K m) ?_⟩
    intro w hw
    exact hm (by simpa using hw)

/-- The canonical free specification event is global open connection after
closing the selected labelled edge. -/
lemma free_specificationConnectionEvent_iff_openConnected {G : SimpleGraph V}
    {B : FiniteBox G.edgeSet} (data : SimpleGraphBoxData G (fun _ : ℕ => B)) (hinj : Function.Injective (data.vertex 0))
    (e : B.edges) (ω : G.edgeSet → Bool) :
    ω ∈ MovingClopenRate.FiniteBox.specificationConnectionEvent B (data.free.partition 0) e ↔
      OpenConnected G (closeGlobalEdge (e.1 : G.edgeSet) ω) Set.univ
        (data.vertex 0 (B.source e)) (data.vertex 0 (B.target e)) := by
  letI : DecidableEq B.edges := fun a b => Classical.propDecidable (a = b)
  let η : B.Exterior := FKLimit.exteriorRestriction B.edges ω
  have hsplit := splitOff_closeGlobalEdge B e ω
  have hext : FKLimit.exteriorRestriction B.edges (closeGlobalEdge (e.1 : G.edgeSet) ω) = η :=
    congrArg Prod.fst hsplit
  simp only [MovingClopenRate.FiniteBox.specificationConnectionEvent, Set.mem_setOf_eq,
    FK.Finite.Conditional.endpointsConnectedWithout]
  let offB : B.edges → Bool := Glauber.FKBridge.offConfiguration B.graph
    (data.free.partition 0 ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)
  change (B.graph.connectionGraph (data.free.partition 0 ((B.splitOff e ω).1))
    (FiniteFiber.withEdge e false offB)).Reachable (B.source e) (B.target e) ↔ _
  have hoff : FiniteFiber.withEdge e false offB =
      (fun f : B.edges => closeGlobalEdge (e.1 : G.edgeSet) ω f.1) := by
    dsimp only [offB]
    funext f
    by_cases hf : f = e
    · subst f
      simp [FiniteFiber.withEdge, closeGlobalEdge]
    · have hf' : (f.1 : G.edgeSet) ≠ (e.1 : G.edgeSet) := by
        intro h
        exact hf (Subtype.ext h)
      simp [FiniteFiber.withEdge, Glauber.FKBridge.offConfiguration,
        Glauber.configSplit, closeGlobalEdge, hf, hf']
      rfl
  have hnorm : (B.graph.connectionGraph (data.free.partition 0 ((B.splitOff e ω).1))
      (FiniteFiber.withEdge e false offB)).Reachable (B.source e) (B.target e) ↔
    (B.graph.connectionGraph (data.free.partition 0 ((B.splitOff e ω).1))
      (fun f : B.edges => closeGlobalEdge (e.1 : G.edgeSet) ω f.1)).Reachable
        (B.source e) (B.target e) := by
    rw [hoff]
  apply Iff.trans hnorm
  change (B.graph.connectionGraph (data.free.partition 0 η)
      (fun f : B.edges => closeGlobalEdge (e.1 : G.edgeSet) ω f.1)).Reachable
        (B.source e) (B.target e) ↔ _
  rw [← hext]
  exact (openConnected_iff_freeComponents data hinj
    (closeGlobalEdge (e.1 : G.edgeSet) ω) (B.source e) (B.target e)).symm

end FK.NestedFinDLR
