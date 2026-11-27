import FK.ForestCombinatorics

/-!
# Straight finite-arc embeddings and labelled leaf deletion
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FiniteFiber

/-- A finite-arc embedding whose arcs have exactly the expected straight
segment ranges.  Endpoints of edges in a labelled forest are proved distinct
from the bridge condition, so no separate nondegeneracy premise is needed. -/
structure StraightFiniteArcEmbedding (G : LabelledMultigraph)
    extends FiniteArcEmbedding G where
  range_segment : ∀ e, Set.range (arc e) =
    [point (G.source e) -[ℝ] point (G.target e)]

/-- A labelled edge incident to a vertex with no other incident edge. -/
structure LabelledLeaf (G : LabelledMultigraph) where
  edge : G.Edge
  leaf : G.Vertex
  other : G.Vertex
  joins : G.Joins edge leaf other
  unique : ∀ f : G.Edge, G.source f = leaf ∨ G.target f = leaf → f = edge

namespace LabelledLeaf

variable {G : LabelledMultigraph} (d : LabelledLeaf G)

/-- The graph obtained by deleting the leaf vertex and its unique incident
labelled edge. -/
noncomputable def graph : LabelledMultigraph := by
  classical
  exact {
    Vertex := {v : G.Vertex // v ≠ d.leaf}
    Edge := {e : G.Edge // e ≠ d.edge}
    source := fun e => ⟨G.source e.1, by
      intro he
      exact e.2 (d.unique e.1 (Or.inl he))⟩
    target := fun e => ⟨G.target e.1, by
      intro he
      exact e.2 (d.unique e.1 (Or.inr he))⟩ }

@[simp] lemma graph_source_val (e : d.graph.Edge) :
    (d.graph.source e).1 = G.source e.1 := rfl

@[simp] lemma graph_target_val (e : d.graph.Edge) :
    (d.graph.target e).1 = G.target e.1 := rfl

/-- Deleting a labelled leaf preserves the labelled forest bridge condition. -/
lemma isLabelledForest_graph (hG : G.IsLabelledForest) :
    d.graph.IsLabelledForest := by
  intro e he hconn
  apply hG e.1 (by simp [allOpen])
  unfold endpointsConnectedWithout at hconn ⊢
  let φ : d.graph.connectionGraph d.graph.freeBoundary
      (withEdge e false d.graph.allOpen) →g
      G.connectionGraph G.freeBoundary (withEdge e.1 false G.allOpen) := {
    toFun := Subtype.val
    map_rel' {u v} huv := by
      refine ⟨fun heq => huv.1 (Subtype.ext heq), ?_⟩
      rcases huv.2 with hfree | ⟨f, hf, hjoin⟩
      · exact (huv.1 hfree).elim
      · have hfe : f ≠ e := by
          intro hfe
          subst f
          simp at hf
        have hfe' : f.1 ≠ e.1 := by
          intro h
          exact hfe (Subtype.ext h)
        refine Or.inr ⟨f.1, ?_, ?_⟩
        · rw [withEdge_off hfe']
          simp [allOpen]
        · rcases hjoin with ⟨hs, ht⟩ | ⟨hs, ht⟩
          · exact Or.inl ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩
          · exact Or.inr ⟨congrArg Subtype.val hs, congrArg Subtype.val ht⟩ }
  exact SimpleGraph.Reachable.map φ hconn

/-- Restrict a genuine straight embedding to the leaf-deleted graph. -/
def embedding (E : StraightFiniteArcEmbedding G) : FiniteArcEmbedding d.graph where
  point v := E.point v.1
  arc e := E.arc e.1
  point_injective := by
    intro u v huv
    exact Subtype.ext (E.point_injective huv)
  source e := E.source e.1
  target e := E.target e.1
  vertex_intersection := by
    intro v e t h
    rcases E.vertex_intersection v.1 e.1 t h with ⟨ht, hs⟩ | ⟨ht, hs⟩
    · exact Or.inl ⟨ht, Subtype.ext hs⟩
    · exact Or.inr ⟨ht, Subtype.ext hs⟩
  intersection := by
    intro e f hef s t hst
    have hef' : e.1 ≠ f.1 := by
      intro heq
      exact hef (Subtype.ext heq)
    obtain ⟨v, hp, he, hf⟩ := E.intersection hef' s t hst
    have hv : v ≠ d.leaf := by
      intro hv
      subst v
      apply e.2
      apply d.unique e.1
      rcases he with ⟨_, hs⟩ | ⟨_, ht⟩
      · exact Or.inl hs
      · exact Or.inr ht
    refine ⟨⟨v, hv⟩, hp, ?_, ?_⟩
    · rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨hs, Subtype.ext ht⟩
      · exact Or.inr ⟨hs, Subtype.ext ht⟩
    · rcases hf with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨hs, Subtype.ext ht⟩
      · exact Or.inr ⟨hs, Subtype.ext ht⟩

/-- Restrict the straightness and nondegeneracy fields as well. -/
def straightEmbedding (E : StraightFiniteArcEmbedding G) :
    StraightFiniteArcEmbedding d.graph where
  toFiniteArcEmbedding := d.embedding E
  range_segment e := E.range_segment e.1

/-- The leaf and attachment vertices are distinct in a labelled forest. -/
lemma leaf_ne_other (hG : G.IsLabelledForest) : d.leaf ≠ d.other := by
  have hloop := source_ne_target_of_isLabelledForest hG d.edge
  rcases d.joins with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simpa [hs, ht] using hloop
  · exact Ne.symm (by simpa [hs, ht] using hloop)

/-- The deleted segment uses the free leaf as its final endpoint. -/
lemma range_arc_segment (E : StraightFiniteArcEmbedding G) :
    Set.range (E.arc d.edge) = [E.point d.other -[ℝ] E.point d.leaf] := by
  rcases d.joins with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · calc
      Set.range (E.arc d.edge) =
          [E.point (G.source d.edge) -[ℝ] E.point (G.target d.edge)] :=
        E.range_segment d.edge
      _ = [E.point d.leaf -[ℝ] E.point d.other] := by rw [hs, ht]
      _ = [E.point d.other -[ℝ] E.point d.leaf] := segment_symm ℝ _ _
  · calc
      Set.range (E.arc d.edge) =
          [E.point (G.source d.edge) -[ℝ] E.point (G.target d.edge)] :=
        E.range_segment d.edge
      _ = [E.point d.other -[ℝ] E.point d.leaf] := by rw [hs, ht]

/-- Deleting a labelled leaf removes precisely its vertex-and-arc carrier. -/
lemma carrier_eq_restricted_union_segment (E : StraightFiniteArcEmbedding G) :
    E.carrier = (d.embedding E).carrier ∪ [E.point d.other -[ℝ] E.point d.leaf] := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨v, rfl⟩ | hx
    · by_cases hv : v = d.leaf
      · subst v
        exact Or.inr (right_mem_segment ℝ _ _)
      · exact Or.inl (Or.inl ⟨⟨v, hv⟩, rfl⟩)
    · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, rfl⟩ := hf
      by_cases hfe : f = d.edge
      · subst f
        apply Or.inr
        rw [← d.range_arc_segment E]
        exact ⟨t, rfl⟩
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨f, hfe⟩, ⟨t, rfl⟩⟩))
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨v, rfl⟩ | hx
      · exact Or.inl ⟨v.1, rfl⟩
      · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
        obtain ⟨t, rfl⟩ := hf
        exact Or.inr (Set.mem_iUnion.mpr ⟨f.1, ⟨t, rfl⟩⟩)
    · have hr : x ∈ Set.range (E.arc d.edge) := by
        rw [d.range_arc_segment E]
        exact hx
      obtain ⟨t, rfl⟩ := hr
      exact Or.inr (Set.mem_iUnion.mpr ⟨d.edge, ⟨t, rfl⟩⟩)

/-- An endpoint of the deleted edge which is not the leaf is the attachment
vertex. -/
lemma eq_other_of_endpoint_ne_leaf {v : G.Vertex} (hv : v ≠ d.leaf)
    (hend : G.source d.edge = v ∨ G.target d.edge = v) : v = d.other := by
  rcases d.joins with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rcases hend with he | he
    · exact (hv (he.symm.trans hs)).elim
    · exact he.symm.trans ht
  · rcases hend with he | he
    · exact he.symm.trans hs
    · exact (hv (he.symm.trans ht)).elim

/-- The restricted carrier meets the deleted segment only at the attachment
vertex. -/
lemma restricted_inter_segment (hG : G.IsLabelledForest)
    (E : StraightFiniteArcEmbedding G) :
    (d.embedding E).carrier ∩ [E.point d.other -[ℝ] E.point d.leaf] =
      {E.point d.other} := by
  ext x
  constructor
  · intro hx
    rw [mem_singleton_iff]
    rw [← d.range_arc_segment E] at hx
    obtain ⟨t, rfl⟩ := hx.2
    rcases hx.1 with ⟨v, hvpoint⟩ | hxold
    · rcases E.vertex_intersection v.1 d.edge t hvpoint with ⟨ht, hs⟩ | ⟨ht, hs⟩
      · have hvo := d.eq_other_of_endpoint_ne_leaf v.2 (Or.inl hs)
        rw [ht, E.source, hs, hvo]
      · have hvo := d.eq_other_of_endpoint_ne_leaf v.2 (Or.inr hs)
        rw [ht, E.target, hs, hvo]
    · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hxold
      obtain ⟨s, hs⟩ := hf
      have hef : d.edge ≠ f.1 := Ne.symm f.2
      obtain ⟨v, hp, he, hfcommon⟩ := E.intersection hef t s hs.symm
      have hv : v ≠ d.leaf := by
        intro hv
        subst v
        apply f.2
        apply d.unique f.1
        rcases hfcommon with ⟨_, hs'⟩ | ⟨_, ht'⟩
        · exact Or.inl hs'
        · exact Or.inr ht'
      have hvo : v = d.other := by
        apply d.eq_other_of_endpoint_ne_leaf hv
        rcases he with ⟨_, hs'⟩ | ⟨_, ht'⟩
        · exact Or.inl hs'
        · exact Or.inr ht'
      rw [hp, hvo]
  · intro hx
    rw [mem_singleton_iff] at hx
    subst x
    refine ⟨?_, left_mem_segment ℝ _ _⟩
    apply Or.inl
    exact ⟨⟨d.other, Ne.symm (d.leaf_ne_other hG)⟩, rfl⟩

end LabelledLeaf

/-- Attach the existence form to the packaged leaf data. -/
lemma exists_labelledLeaf {G : LabelledMultigraph}
    (hG : G.IsLabelledForest) (e : G.Edge) : Nonempty (LabelledLeaf G) := by
  obtain ⟨v, w, e', hj, hu⟩ := exists_labelledLeaf_of_isLabelledForest hG e
  exact ⟨⟨e', v, w, hj, hu⟩⟩

/-- **Finite straight labelled forests do not disconnect the plane.**  The
proof is induction on the number of labelled edges by deleting a genuine
labelled leaf.  Multiple components and isolated vertices are included. -/
theorem isPathConnected_compl_carrier_of_isLabelledForest
    {G : LabelledMultigraph} (hG : G.IsLabelledForest)
    (E : StraightFiniteArcEmbedding G) : IsPathConnected E.carrierᶜ := by
  classical
  induction hn : Fintype.card G.Edge using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hempty : IsEmpty G.Edge
      · have hc : E.carrier = Set.range E.point := by
          apply Set.Subset.antisymm
          · intro x hx
            rcases hx with hx | hx
            · exact hx
            · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
              exact isEmptyElim e
          · intro x hx
            exact Or.inl hx
        rw [hc]
        have hrank : 1 < Module.rank ℝ Plane := by
          simp
          norm_num
        exact (Set.finite_range E.point).countable.isPathConnected_compl_of_one_lt_rank hrank
      · letI : Nonempty G.Edge := not_isEmpty_iff.mp hempty
        let d : LabelledLeaf G := (exists_labelledLeaf hG (Classical.arbitrary G.Edge)).some
        have hcard : Fintype.card d.graph.Edge = Fintype.card G.Edge - 1 := by
          change Fintype.card {e : G.Edge // e ≠ d.edge} = Fintype.card G.Edge - 1
          rw [Fintype.card_subtype_compl (fun e => e = d.edge), Fintype.card_subtype_eq]
        have hpos : 0 < Fintype.card G.Edge := Fintype.card_pos_iff.mpr inferInstance
        have hlt : Fintype.card d.graph.Edge < n := by omega
        have hi := ih _ hlt (G := d.graph) (d.isLabelledForest_graph hG)
          (d.straightEmbedding E) rfl
        have hab : E.point d.other ≠ E.point d.leaf :=
          (E.point_injective.ne (d.leaf_ne_other hG)).symm
        have hattached := isPathConnected_compl_union_segment_of_attached
          (d.embedding E).isCompact_carrier hab (d.restricted_inter_segment hG E) hi
        rw [← d.carrier_eq_restricted_union_segment E] at hattached
        exact hattached

/-- A finite straight labelled forest has exactly one actual complementary
face. -/
theorem face_subsingleton_of_isLabelledForest
    {G : LabelledMultigraph} (hG : G.IsLabelledForest)
    (E : StraightFiniteArcEmbedding G) : Subsingleton E.Face := by
  letI : PathConnectedSpace E.FacePoints := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_compl_carrier_of_isLabelledForest hG E)
  infer_instance

/-- The unique actual face of a nonempty-vertex straight labelled forest is
nonempty; in fact, it is nonempty without any vertex nonemptiness assumption,
since the entire plane is allowed as the complement. -/
theorem face_nonempty_of_isLabelledForest
    {G : LabelledMultigraph} (hG : G.IsLabelledForest)
    (E : StraightFiniteArcEmbedding G) : Nonempty E.Face := by
  letI : PathConnectedSpace E.FacePoints := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_compl_carrier_of_isLabelledForest hG E)
  infer_instance

end
end FK.PlaneTopology.Continuous.Forest
