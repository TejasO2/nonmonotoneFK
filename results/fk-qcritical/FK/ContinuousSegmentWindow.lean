import FK.OneSegmentWindow

/-!
# Continuous parametrizations of a straight-segment window

The existing one-segment window uses the affine parametrization.  Here we
allow an arbitrary continuous injective parametrization whose range is
contained in the same nondegenerate straight segment.  The intermediate value
theorem shows that its range is the whole segment; no polygonality or affine
parametrization is assumed.
-/

namespace FK.PlaneTopology.Continuous.SegmentArc

noncomputable section

open Set
open scoped Classical Convex unitInterval BigOperators
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology.Continuous
open FK.PlaneTopology.Continuous.Segment

variable {a b : Plane}

lemma progress_left (hab : a ≠ b) : progress a b a = 0 := by
  have h := progress_affine (a := a) (b := b) hab 0
  simpa using h

lemma progress_right (hab : a ≠ b) : progress a b b = 1 := by
  have h := progress_affine (a := a) (b := b) hab 1
  simpa using h

/-- A point of a segment is the affine-line point at its progress coordinate. -/
lemma eq_lineMap_progress (hab : a ≠ b) {x : Plane}
    (hx : x ∈ [a -[ℝ] b]) :
    x = AffineMap.lineMap a b (progress a b x) := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  have hdiff : AffineMap.lineMap a b r = a + r • (b - a) := by
    simp [AffineMap.lineMap_apply]
    abel
  rw [hdiff, progress_affine hab]
  exact hdiff.symm

/-- Every continuous Jordan arc from `a` to `b` inside their straight segment
has exactly that segment as its range.  Injectivity is not needed for this
surjectivity lemma; it is needed later for the source-faithful embedding. -/
theorem range_eq_segment_of_continuous
    (γ : JordanArc Plane) (hzero : γ 0 = a) (hone : γ 1 = b)
    (hsub : Set.range γ ⊆ [a -[ℝ] b]) (hab : a ≠ b) :
    Set.range γ = [a -[ℝ] b] := by
  apply Set.Subset.antisymm hsub
  intro x hx
  let f : I → ℝ := fun t => progress a b (γ t)
  have hf : Continuous f := by
    unfold f progress
    fun_prop (disch := exact (dirNormSq_pos hab).ne')
  have hfzero : f 0 = 0 := by
    simp only [f, hzero]
    exact progress_left hab
  have hfone : f 1 = 1 := by
    simp only [f, hone]
    exact progress_right hab
  have hxprog : progress a b x ∈ Set.Icc (f 0) (f 1) := by
    rw [hfzero, hfone]
    exact ⟨(segment_coordinates hab hx).2.1, (segment_coordinates hab hx).2.2⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) (1 : I) hf hxprog
  refine ⟨t, ?_⟩
  rw [eq_lineMap_progress hab (hsub ⟨t, rfl⟩), eq_lineMap_progress hab hx]
  exact congrArg (AffineMap.lineMap a b) ht

/-- A single arbitrary Jordan arc with distinct declared endpoints is a
source-faithful embedding of the one-edge graph. -/
def embedding (γ : JordanArc Plane) (hzero : γ 0 = a) (hone : γ 1 = b)
    (hab : a ≠ b) : FiniteArcEmbedding OneSegment.graph where
  point v := cond v b a
  arc _ := γ
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
    exact hzero
  target e := by
    cases e
    exact hone
  vertex_intersection := by
    intro v e t h
    obtain ⟨⟩ := e
    cases v
    · left
      have heq : γ 0 = γ t := by
        calc
          γ 0 = a := hzero
          _ = γ t := h
      exact ⟨γ.injective heq.symm, rfl⟩
    · right
      have heq : γ 1 = γ t := by
        calc
          γ 1 = b := hone
          _ = γ t := h
      exact ⟨γ.injective heq.symm, rfl⟩
  intersection := by
    intro e f hef
    cases e
    cases f
    exact (hef rfl).elim

/-- When the arc lies in the segment joining its endpoints, the carrier is
exactly that segment, independently of its parametrization. -/
theorem carrier_embedding (γ : JordanArc Plane) (hzero : γ 0 = a)
    (hone : γ 1 = b) (hsub : Set.range γ ⊆ [a -[ℝ] b]) (hab : a ≠ b) :
    (embedding γ hzero hone hab).carrier = [a -[ℝ] b] := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with ⟨v, rfl⟩ | hz
    · cases v
      · exact left_mem_segment ℝ a b
      · exact right_mem_segment ℝ a b
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
      obtain ⟨t, rfl⟩ := he
      obtain ⟨⟩ := e
      exact hsub ⟨t, rfl⟩
  · intro z hz
    rw [← range_eq_segment_of_continuous γ hzero hone hsub hab] at hz
    obtain ⟨t, rfl⟩ := hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨(), ⟨t, rfl⟩⟩)

/-- The actual continuous complement has exactly one face for every such
parametrization. -/
theorem face_embedding_subsingleton (γ : JordanArc Plane) (hzero : γ 0 = a)
    (hone : γ 1 = b) (hsub : Set.range γ ⊆ [a -[ℝ] b]) (hab : a ≠ b) :
    Subsingleton (embedding γ hzero hone hab).Face := by
  change Subsingleton
    (ConnectedComponents {z // z ∈ (embedding γ hzero hone hab).carrierᶜ})
  rw [carrier_embedding γ hzero hone hsub hab]
  exact subsingleton_connectedComponents_compl_segment hab

/-- The complementary face type is nonempty. -/
theorem face_embedding_nonempty (γ : JordanArc Plane) (hzero : γ 0 = a)
    (hone : γ 1 = b) (hsub : Set.range γ ⊆ [a -[ℝ] b]) (hab : a ≠ b) :
    Nonempty (embedding γ hzero hone hab).Face := by
  change Nonempty
    (ConnectedComponents {z // z ∈ (embedding γ hzero hone hab).carrierᶜ})
  rw [carrier_embedding γ hzero hone hsub hab]
  exact nonempty_connectedComponents_compl_segment hab

/-- Exact combinatorial-to-continuous face incidence for an arbitrary
parametrization of a straight segment. -/
def faceEquiv (γ : JordanArc Plane) (hzero : γ 0 = a) (hone : γ 1 = b)
    (hsub : Set.range γ ⊆ [a -[ℝ] b]) (hab : a ≠ b) :
    OneSegment.rotation.Face ≃ (embedding γ hzero hone hab).Face := by
  letI : Subsingleton OneSegment.rotation.Face := OneSegment.face_subsingleton
  letI : Subsingleton (embedding γ hzero hone hab).Face :=
    face_embedding_subsingleton γ hzero hone hsub hab
  exact equivOfSubsingletonOfSubsingleton
    (fun _ => (face_embedding_nonempty γ hzero hone hsub hab).some)
    (fun _ => OneSegment.rotation.faceOf ((), false))

/-- Exact labelled primal incidence for the arbitrary continuous arc. -/
def primalEmbedding (γ : JordanArc Plane) (hzero : γ 0 = a)
    (hone : γ 1 = b) (hab : a ≠ b) :
    FK.PlaneTopology.LabelledSimpleGraphEmbedding OneSegment.graph
      (SimpleGraph.edge a b) where
  vertex := (embedding γ hzero hone hab).point
  label _ := OneSegment.globalEdge hab
  endpoint e := by
    cases e
    rfl

/-- The strict-interior coverage input used by `CellularSealedCuts` holds for
the arbitrary-parametrization window, uniformly in the face region. -/
theorem interiorEdgeCoverage (γ : JordanArc Plane) (hzero : γ 0 = a)
    (hone : γ 1 = b) (hab : a ≠ b) (T : Set OneSegment.rotation.Face) :
    FK.PlaneTopology.CellularSealed.LabelledSimpleGraphEmbedding.InteriorEdgeCoverage
      (primalEmbedding γ hzero hone hab) OneSegment.rotation T := by
  exact OneSegment.interiorEdgeCoverage hab T

end
end FK.PlaneTopology.Continuous.SegmentArc
