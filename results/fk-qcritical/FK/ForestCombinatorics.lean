import FK.ForestHistory
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Labelled forest combinatorics for straight embeddings
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FiniteFiber

/-- Loops are excluded by the labelled forest bridge condition. -/
lemma source_ne_target_of_isLabelledForest {G : LabelledMultigraph}
    (hG : G.IsLabelledForest) (e : G.Edge) : G.source e ≠ G.target e := by
  intro he
  apply hG e (by simp [allOpen])
  unfold endpointsConnectedWithout
  rw [he]

/-- Two labels joining the same unordered pair of vertices must agree. -/
lemma edge_unique_of_joins_of_isLabelledForest {G : LabelledMultigraph}
    (hG : G.IsLabelledForest) {e f : G.Edge} {u v : G.Vertex}
    (he : G.Joins e u v) (hf : G.Joins f u v) : e = f := by
  by_contra hef
  have huv : u ≠ v := by
    have hloop := source_ne_target_of_isLabelledForest hG e
    rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simpa [hs, ht] using hloop
    · exact Ne.symm (by simpa [hs, ht] using hloop)
  have hopen : withEdge e false G.allOpen f = true := by
    rw [withEdge_off (Ne.symm hef)]
    simp [allOpen]
  have hadj : (G.connectionGraph G.freeBoundary (withEdge e false G.allOpen)).Adj u v :=
    ⟨huv, Or.inr ⟨f, hopen, hf⟩⟩
  apply hG e (by simp [allOpen])
  unfold endpointsConnectedWithout
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simpa [hs, ht] using hadj.reachable
  · simpa [hs, ht] using hadj.symm.reachable

/-- The unordered endpoints of a labelled adjacency. -/
lemma sym2_eq_endpoints_of_joins {G : LabelledMultigraph}
    {e : G.Edge} {x y : G.Vertex} (h : G.Joins e x y) :
    s(x, y) = s(G.source e, G.target e) := by
  rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs, ht]
  · rw [hs, ht, Sym2.eq_swap]

/-- The underlying simple graph of a labelled forest is acyclic. -/
lemma isAcyclic_simpleGraph_of_isLabelledForest {G : LabelledMultigraph}
    (hG : G.IsLabelledForest) : G.simpleGraph.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [SimpleGraph.isBridge_iff]
  intro hr
  obtain ⟨e, heuv⟩ := ((G.simpleGraph_adj_iff).mp huv).2
  let adjLabel : ∀ {x y : G.Vertex}, G.simpleGraph.Adj x y → G.Edge :=
    fun h => Classical.choose ((G.simpleGraph_adj_iff).mp h).2
  have adjLabel_joins : ∀ {x y : G.Vertex} (h : G.simpleGraph.Adj x y),
      G.Joins (adjLabel h) x y := by
    intro x y h
    exact Classical.choose_spec ((G.simpleGraph_adj_iff).mp h).2
  let φ : (G.simpleGraph.deleteEdges {s(u, v)}) →g
      G.connectionGraph G.freeBoundary (withEdge e false G.allOpen) := {
    toFun := id
    map_rel' {x y} hxy := by
      have hdel : s(x, y) ∉ {s(u, v)} := (SimpleGraph.deleteEdges_adj.mp hxy).2
      have hlabel : adjLabel hxy.1 ≠ e := by
        intro he
        apply hdel
        have hj := adjLabel_joins hxy.1
        rw [he] at hj
        rw [mem_singleton_iff]
        exact (sym2_eq_endpoints_of_joins hj).trans
          (sym2_eq_endpoints_of_joins heuv).symm
      refine ⟨hxy.1.1, Or.inr ⟨adjLabel hxy.1, ?_, adjLabel_joins hxy.1⟩⟩
      rw [withEdge_off hlabel]
      simp [allOpen] }
  have hr' : (G.connectionGraph G.freeBoundary
      (withEdge e false G.allOpen)).Reachable u v := SimpleGraph.Reachable.map φ hr
  apply hG e (by simp [allOpen])
  unfold endpointsConnectedWithout
  rcases heuv with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simpa [hs, ht] using hr'
  · simpa [hs, ht] using hr'.symm

/-- Every nonempty labelled forest has a labelled edge with a degree-one
incidence.  Parallel labels and loops are excluded by the same forest input. -/
lemma exists_labelledLeaf_of_isLabelledForest {G : LabelledMultigraph}
    (hG : G.IsLabelledForest) (e₀ : G.Edge) :
    ∃ (v w : G.Vertex) (e : G.Edge), G.Joins e v w ∧
      ∀ f : G.Edge, G.source f = v ∨ G.target f = v → f = e := by
  have hjoin : G.Joins e₀ (G.source e₀) (G.target e₀) := Or.inl ⟨rfl, rfl⟩
  have hadj₀ : G.simpleGraph.Adj (G.source e₀) (G.target e₀) :=
    (G.simpleGraph_adj_iff).2 ⟨source_ne_target_of_isLabelledForest hG e₀,
      e₀, hjoin⟩
  let C := G.simpleGraph.connectedComponentMk (G.source e₀)
  have hsC : G.source e₀ ∈ C.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have htC : G.target e₀ ∈ C.supp := C.mem_supp_of_adj_mem_supp hsC hadj₀
  letI : Nontrivial C := ⟨⟨G.source e₀, hsC⟩, ⟨G.target e₀, htC⟩, by
    intro heq
    exact (source_ne_target_of_isLabelledForest hG e₀) (congrArg Subtype.val heq)⟩
  let hT := (isAcyclic_simpleGraph_of_isLabelledForest hG).isTree_connectedComponent C
  obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hneighbors : G.simpleGraph.neighborSet v.1 ⊆ C.supp := by
    intro z hz
    exact C.mem_supp_of_adj_mem_supp v.2 hz
  have hdegree : G.simpleGraph.degree v.1 = 1 := by
    rw [← SimpleGraph.degree_induce_of_neighborSet_subset hneighbors]
    exact hv
  obtain ⟨w, hvw, hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree
  let e := Classical.choose ((G.simpleGraph_adj_iff).mp hvw).2
  have hejoin : G.Joins e v.1 w :=
    Classical.choose_spec ((G.simpleGraph_adj_iff).mp hvw).2
  refine ⟨v.1, w, e, hejoin, ?_⟩
  intro f hf
  have hfjoins : ∃ z, G.Joins f v.1 z ∧ G.simpleGraph.Adj v.1 z := by
    rcases hf with hs | ht
    · have hj : G.Joins f v.1 (G.target f) := Or.inl ⟨hs, rfl⟩
      have hne : v.1 ≠ G.target f := by
        have hloop := source_ne_target_of_isLabelledForest hG f
        simpa [hs] using hloop
      exact ⟨G.target f, hj, (G.simpleGraph_adj_iff).2 ⟨hne, f, hj⟩⟩
    · have hj : G.Joins f v.1 (G.source f) := Or.inr ⟨rfl, ht⟩
      have hne : v.1 ≠ G.source f := by
        have hloop := source_ne_target_of_isLabelledForest hG f
        exact Ne.symm (by simpa [ht] using hloop)
      exact ⟨G.source f, hj, (G.simpleGraph_adj_iff).2 ⟨hne, f, hj⟩⟩
  obtain ⟨z, hj, hz⟩ := hfjoins
  have hzw : z = w := hunique z hz
  subst z
  exact (edge_unique_of_joins_of_isLabelledForest hG hejoin hj).symm

end
end FK.PlaneTopology.Continuous.Forest
