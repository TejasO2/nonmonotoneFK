import FK.PolygonalSegment

/-!
# An exact continuous one-edge spherical window

The nondegenerate straight segment is realized by a two-vertex, one-edge
labelled graph. We construct its spherical rotation system directly and prove
that the unique combinatorial face is equivalent to the actual face of the
continuous plane embedding, using the explicit detour theorem.
-/

namespace FK.PlaneTopology.Continuous.OneSegment

noncomputable section

open Set
open scoped Classical Convex unitInterval BigOperators
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology.Continuous
open FK.PlaneTopology.Continuous.Segment

/-- The labelled multigraph with vertices `false`, `true` and one unit edge. -/
def graph : LabelledMultigraph where
  Vertex := Bool
  Edge := Unit
  source _ := false
  target _ := true

/-- Identity vertex rotation: each endpoint has exactly one incident dart. -/
def rotation : RotationSystem graph where
  rotation := Equiv.refl _
  vertex_rotation _ := rfl
  sameCycle_rotation := by
    intro d d' hd
    have hdd : d = d' := by
      rcases d with ⟨⟨⟩, b⟩
      rcases d' with ⟨⟨⟩, b'⟩
      cases b <;> cases b' <;> simp [vertex, graph] at hd ⊢
    exact hdd.sameCycle _

/-- The primal one-edge graph is connected. -/
theorem graph_preconnected :
    (graph.connectionGraph graph.freeBoundary graph.allOpen).Preconnected := by
  intro u v
  cases u <;> cases v
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    refine ⟨fun h => Bool.noConfusion h, Or.inr ⟨(), ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
    rfl
  · apply SimpleGraph.Adj.reachable
    refine ⟨fun h => Bool.noConfusion h, Or.inr ⟨(), ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
    rfl
  · exact SimpleGraph.Reachable.refl _

/-- Both darts lie in the same face cycle. -/
theorem face_subsingleton : Subsingleton rotation.Face := by
  constructor
  intro f g
  refine Quotient.inductionOn f (fun d => Quotient.inductionOn g (fun d' => ?_))
  apply (rotation.faceOf_eq_iff).2
  rcases d with ⟨⟨⟩, b⟩
  rcases d' with ⟨⟨⟩, b'⟩
  cases b <;> cases b'
  · exact Equiv.Perm.SameCycle.rfl
  · refine ⟨1, ?_⟩
    simp [RotationSystem.facePerm, rotation, reverse]
  · refine ⟨-1, ?_⟩
    simp [RotationSystem.facePerm, rotation, reverse]
  · exact Equiv.Perm.SameCycle.rfl

noncomputable instance fintypeFace : Fintype rotation.Face := rotation.dualPair.fintypeFace

/-- The rotation system has exactly one face. -/
theorem card_face : Fintype.card rotation.Face = 1 := by
  letI : Subsingleton rotation.Face := face_subsingleton
  exact Fintype.card_eq_one_iff.mpr
    ⟨rotation.faceOf ((), false), fun f => Subsingleton.elim _ _⟩

/-- A genuine spherical rotation system for one embedded segment. -/
def sphere : RotationSphere graph where
  toRotationSystem := rotation
  nonemptyVertex := ⟨false⟩
  nonemptyDart := ⟨((), false)⟩
  primal_preconnected := graph_preconnected
  euler := by
    change Fintype.card rotation.Face + Fintype.card Bool = Fintype.card Unit + 2
    rw [card_face]
    decide

/-- The continuous Jordan arc parametrized by a straight segment. -/
def straightArc {a b : Plane} (hab : a ≠ b) : JordanArc Plane where
  toMap := (Path.segment a b).toContinuousMap
  injective := Path.segment_injective_of_ne hab

@[simp] theorem straightArc_zero {a b : Plane} (hab : a ≠ b) :
    straightArc hab 0 = a := by
  simp [straightArc]

@[simp] theorem straightArc_one {a b : Plane} (hab : a ≠ b) :
    straightArc hab 1 = b := by
  simp [straightArc]

theorem range_straightArc {a b : Plane} (hab : a ≠ b) :
    Set.range (straightArc hab) = [a -[ℝ] b] := by
  exact Path.range_segment a b

/-- The straight segment is a source-faithful continuous embedding of `graph`. -/
def embedding {a b : Plane} (hab : a ≠ b) : FiniteArcEmbedding graph where
  point v := cond v b a
  arc _ := straightArc hab
  point_injective := by
    intro u v huv
    cases u <;> cases v
    · rfl
    · change a = b at huv
      exact (hab huv).elim
    · change b = a at huv
      exact (hab huv.symm).elim
    · rfl
  source e := by
    cases e
    simp [straightArc, graph]
  target e := by
    cases e
    simp [straightArc, graph]
  vertex_intersection := by
    intro v e t h
    obtain ⟨⟩ := e
    cases v
    · left
      have heq : (straightArc hab) 0 = (straightArc hab) t := by
        calc
          (straightArc hab) 0 = a := straightArc_zero hab
          _ = (straightArc hab) t := h
      exact ⟨(straightArc hab).injective heq.symm, rfl⟩
    · right
      have heq : (straightArc hab) 1 = (straightArc hab) t := by
        calc
          (straightArc hab) 1 = b := straightArc_one hab
          _ = (straightArc hab) t := h
      exact ⟨(straightArc hab).injective heq.symm, rfl⟩
  intersection := by
    intro e f hef
    cases e
    cases f
    exact (hef rfl).elim

/-- The continuous carrier is exactly the supplied segment, with no extra
points or parts of arcs. -/
theorem carrier_embedding {a b : Plane} (hab : a ≠ b) :
    (embedding hab).carrier = [a -[ℝ] b] := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with ⟨v, rfl⟩ | hz
    · cases v
      · change a ∈ [a -[ℝ] b]
        exact left_mem_segment ℝ a b
      · change b ∈ [a -[ℝ] b]
        exact right_mem_segment ℝ a b
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, rfl⟩ := he
      obtain ⟨⟩ := e
      exact range_straightArc hab ▸ ⟨t, rfl⟩
  · intro z hz
    have hr : z ∈ Set.range (straightArc hab) := by
      rw [range_straightArc hab]
      exact hz
    obtain ⟨t, rfl⟩ := hr
    exact Or.inr (Set.mem_iUnion.mpr ⟨(), ⟨t, rfl⟩⟩)

/-- The actual continuous complement has a unique face. -/
theorem face_embedding_subsingleton {a b : Plane} (hab : a ≠ b) :
    Subsingleton (embedding hab).Face := by
  change Subsingleton (ConnectedComponents {z // z ∈ (embedding hab).carrierᶜ})
  rw [carrier_embedding hab]
  exact subsingleton_connectedComponents_compl_segment hab

/-- The actual continuous complement has a face. -/
theorem face_embedding_nonempty {a b : Plane} (hab : a ≠ b) :
    Nonempty (embedding hab).Face := by
  change Nonempty (ConnectedComponents {z // z ∈ (embedding hab).carrierᶜ})
  rw [carrier_embedding hab]
  exact nonempty_connectedComponents_compl_segment hab

/-- **Exact geometric/combinatorial incidence for the one-edge window.** The
face computed by face traversal of the spherical rotation system is identified
with the connected component of the actual plane complement. -/
def faceEquiv {a b : Plane} (hab : a ≠ b) : rotation.Face ≃ (embedding hab).Face := by
  letI : Subsingleton rotation.Face := face_subsingleton
  letI : Subsingleton (embedding hab).Face := face_embedding_subsingleton hab
  exact equivOfSubsingletonOfSubsingleton
    (fun _ => (face_embedding_nonempty hab).some)
    (fun _ => rotation.faceOf ((), false))

/-- The unique nonloop edge in the ambient simple graph `SimpleGraph.edge a b`. -/
def globalEdge {a b : Plane} (hab : a ≠ b) : (SimpleGraph.edge a b).edgeSet := by
  refine ⟨s(a, b), ?_⟩
  change (SimpleGraph.edge a b).Adj a b
  rw [SimpleGraph.edge_adj]
  exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩

/-- Exact labelled primal incidence in the ambient simple graph with precisely
the drawn segment as its edge. -/
def primalEmbedding {a b : Plane} (hab : a ≠ b) :
    FK.PlaneTopology.LabelledSimpleGraphEmbedding graph (SimpleGraph.edge a b) where
  vertex := (embedding hab).point
  label _ := globalEdge hab
  endpoint e := by
    cases e
    change s(a, b) = s(a, b)
    rfl

open FK.PlaneTopology.CellularSealed

/-- The sealed-cut strict-interior edge-coverage condition is proved for the
continuous one-edge window, uniformly in the prescribed face region. -/
theorem interiorEdgeCoverage {a b : Plane} (hab : a ≠ b) (T : Set rotation.Face) :
    LabelledSimpleGraphEmbedding.InteriorEdgeCoverage (primalEmbedding hab) rotation T := by
  intro u _hu z hadj
  cases u
  · change (SimpleGraph.edge a b).Adj a z at hadj
    rw [SimpleGraph.edge_adj] at hadj
    have hz : z = b := by
      rcases hadj.1 with h | h
      · exact h.2
      · exact (hab h.1).elim
    refine ⟨(), true, Or.inl ⟨rfl, rfl⟩, ?_, hz.symm⟩
    apply Subtype.ext
    change s(a, b) = s(a, z)
    rw [hz]
  · change (SimpleGraph.edge a b).Adj b z at hadj
    rw [SimpleGraph.edge_adj] at hadj
    have hz : z = a := by
      rcases hadj.1 with h | h
      · exact (hab h.1.symm).elim
      · exact h.2
    refine ⟨(), false, Or.inr ⟨rfl, rfl⟩, ?_, hz.symm⟩
    apply Subtype.ext
    change s(a, b) = s(b, z)
    rw [hz]
    exact Sym2.eq_swap

end
end FK.PlaneTopology.Continuous.OneSegment
