import FK.StageEventGeometry

/-! Containment and escape bounds for the outer stage events. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ClusterEscape
open FK.NestedMixture

universe u

variable {V : Type u} [Countable V] {G : SimpleGraph V}

section OneStage

variable {B C : FiniteBox G.edgeSet} (N : NestedBox B C)
variable (data : SimpleGraphBoxData G (fun _ : ℕ => C))

/-- Global wired form of the outer stage connection event. -/
lemma outerStageConnectionEvent_iff_globalWired (hinj : Function.Injective (data.vertex 0))
    (a : C.BoundaryPartition)
    (e : B.edges) (ω : G.edgeSet → Bool) :
    ω ∈ outerStageConnectionEvent N a e ↔
      (wiredGraph G (globalBoundary data hinj a)
        (closeOutside C (closeGlobalEdge (e.1 : G.edgeSet) ω))).Reachable
          (data.vertex 0 (N.vert (B.source e)))
          (data.vertex 0 (N.vert (B.target e))) := by
  exact (reachable_wiredGraph_closeOutside_iff data hinj a
    (closeGlobalEdge (e.1 : G.edgeSet) ω) (N.vert (B.source e)) (N.vert (B.target e))).symm

/-- Every inner open path whose edge support is contained in the outer box is a
stage connection. -/
lemma outerStage_mem_of_offEdgeConnectionInside (hinj : Function.Injective (data.vertex 0))
    (a : C.BoundaryPartition) (e : B.edges)
    (K : Finset V) (S : Finset G.edgeSet)
    (hKS : ∀ f : G.edgeSet, f.1 ∈ innerEdges K → f ∈ S) (hSC : S ⊆ C.edges)
    (ω : G.edgeSet → Bool)
    (h : ω ∈ offEdgeConnectionInside (e.1 : G.edgeSet) K
      (data.vertex 0 (N.vert (B.source e))) (data.vertex 0 (N.vert (B.target e)))) :
    ω ∈ outerStageConnectionEvent N a e := by
  have hc : OpenConnected G (closeOutside C (closeGlobalEdge (e.1 : G.edgeSet) ω))
      (innerEdges K) (data.vertex 0 (N.vert (B.source e)))
      (data.vertex 0 (N.vert (B.target e))) := by
    apply OpenConnected.congr h
    intro f hf
    exact (closeOutside_apply_of_mem C (closeGlobalEdge (e.1 : G.edgeSet) ω)
      (hSC (hKS f hf))).symm
  have hw := reachable_wiredGraph_of_openConnected
    (γ := globalBoundary data hinj a) hc
  exact (outerStageConnectionEvent_iff_globalWired N data hinj a e ω).mpr hw

/-- If the outer boundary has no nonreflexive relation incident to `K`, a stage
connection not explained by an inner path forces the source cluster to leave
`K`, even after returning to the original (unclosed) configuration. -/
lemma clusterMeetsOutside_of_outerStage_diff (hinj : Function.Injective (data.vertex 0))
    (a : C.BoundaryPartition) (e : B.edges)
    (K : Finset V)
    (hKx : data.vertex 0 (N.vert (B.source e)) ∈ K)
    (hKy : data.vertex 0 (N.vert (B.target e)) ∈ K)
    (hγ : ∀ u v : C.Vertex, u ≠ v → a.r u v →
      data.vertex 0 u ∉ K ∧ data.vertex 0 v ∉ K)
    (ω : G.edgeSet → Bool) (hstage : ω ∈ outerStageConnectionEvent N a e)
    (hnot : ω ∉ offEdgeConnectionInside (e.1 : G.edgeSet) K
      (data.vertex 0 (N.vert (B.source e))) (data.vertex 0 (N.vert (B.target e)))) :
    ClusterMeetsOutside G ω (data.vertex 0 (N.vert (B.source e))) K := by
  let x := data.vertex 0 (N.vert (B.source e))
  let y := data.vertex 0 (N.vert (B.target e))
  let e0 : G.edgeSet := e.1
  let η0 : G.edgeSet → Bool := closeGlobalEdge e0 ω
  have hγ' : ∀ u v : V, u ≠ v → (globalBoundary data hinj a).r u v → u ∉ K ∧ v ∉ K := by
    intro u v huv hrel
    rcases hrel with ⟨c, d, huc, hvd, hcd⟩ | heq
    · subst u
      subst v
      have hne : c ≠ d := by
        intro h
        subst d
        exact huv rfl
      exact hγ c d hne hcd
    · exact (huv heq).elim
  have hconn : (wiredGraph G (globalBoundary data hinj a) (closeOutside C η0)).Reachable x y :=
    (outerStageConnectionEvent_iff_globalWired N data hinj a e ω).mp hstage
  have hnotin : ¬ OpenConnected G (closeOutside C η0) (innerEdges K) x y := by
    intro hc
    apply hnot
    exact OpenConnected.mono_config hc (closeOutside_le η0)
  have hpair := escape_pair_of_wiredConn_ne hγ' hKx hKy hconn hnotin
  obtain ⟨z, hzK, hxz⟩ := hpair.1
  refine ⟨z, hzK, ?_⟩
  exact OpenConnected.mono_config hxz
    ((closeOutside_le η0).trans (closeGlobalEdge_le e0 ω))

end OneStage

end FK.NestedFinDLR
