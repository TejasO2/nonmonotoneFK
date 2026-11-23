import FK.ThetaDuality
import FK.CircleSeparation
import FK.SegmentSeparation

/-!
# Circular plane loops with non-radial straight dual arcs

The inherited `CircularLoopCertificate.lean` treats only the radial arc from
the centre.  This file uses an arbitrary interior representative.  The two
Boolean dual vertices are identified with the actual inside and outside path
components, and the straight dual arc has exactly one primal-circle crossing.

The matroid equality is not assumed: it is the already checked one-edge cycle
certificate from `FK.ThetaDuality`.  The new work is the embedded separation
and crossing data.
-/

namespace FK.PlaneTopology

open Set Metric
open FK.Finite FK.FinitePlane FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.LabelledDualPair

/-- A concrete embedded circular loop, with one representative of each face.
The primal vertex lies on the circle; the interior representative need not be
its centre. -/
structure CircularSegmentPlane where
  centre : ℝ × ℝ
  radius : ℝ
  radius_pos : 0 < radius
  vertex : ℝ × ℝ
  vertex_on_circle : vertex ∈ sphere centre radius
  interior : ℝ × ℝ
  interior_inside : interior ∈ ball centre radius
  exterior : ℝ × ℝ
  exterior_outside : exterior ∈ (fun z : ℝ × ℝ => dist z centre) ⁻¹' Ioi radius

namespace CircularSegmentPlane

/-- The one-vertex, one-labelled-loop primal multigraph. -/
def primal : LabelledMultigraph where
  Vertex := Unit
  Edge := Unit
  source _ := Unit.unit
  target _ := Unit.unit

/-- Repaired version of the inherited one-loop cycle proof: the cardinality
field is closed by the definitional equality that the old file leaves behind. -/
lemma isLabelledCycle_primal : primal.IsLabelledCycle := by
  refine ⟨⟨Unit.unit⟩, ?_, ?_, ?_⟩
  · change Fintype.card Unit = Fintype.card Unit
    rfl
  · intro u v
    change Unit at u v
    cases u
    cases v
    exact SimpleGraph.Reachable.refl _
  · intro ω hω
    obtain ⟨e, he⟩ := primal.exists_closed_of_ne_allOpen hω
    have hclosed : ω = primal.allClosed := by
      funext a
      change Unit at a e
      cases a
      cases e
      exact he
    rw [hclosed]
    exact primal.isOpenForest_allClosed primal.freeBoundary

/-- The labelled pair of the one-edge loop and its two-face parallel dual. -/
def pair (_ : CircularSegmentPlane) : LabelledDualPair := cyclePair primal

lemma graphicDualCertificate_pair (C : CircularSegmentPlane) : C.pair.GraphicDualCertificate :=
  graphicDualCertificate_cycle primal isLabelledCycle_primal

/-- Geometric image of the unique primal vertex. -/
def embeddedVertex (C : CircularSegmentPlane) (_ : C.pair.Vertex) : ℝ × ℝ := C.vertex

/-- Geometric locus of the unique labelled primal edge. -/
def embeddedEdge (C : CircularSegmentPlane) (_ : C.pair.Edge) : Set (ℝ × ℝ) :=
  sphere C.centre C.radius

/-- The two actual complementary face regions. -/
def faceRegion (C : CircularSegmentPlane) : C.pair.Face → Set (ℝ × ℝ)
  | false => ball C.centre C.radius
  | true => (fun z : ℝ × ℝ => dist z C.centre) ⁻¹' Ioi C.radius

/-- The supplied point in each actual face. -/
def faceRepresentative (C : CircularSegmentPlane) : C.pair.Face → ℝ × ℝ
  | false => C.interior
  | true => C.exterior

lemma faceRepresentative_mem (C : CircularSegmentPlane) (f : C.pair.Face) :
    C.faceRepresentative f ∈ C.faceRegion f := by
  change Bool at f
  cases f
  · exact C.interior_inside
  · exact C.exterior_outside

lemma vertex_mem_embeddedEdge (C : CircularSegmentPlane) (v : C.pair.Vertex) :
    C.embeddedVertex v ∈ C.embeddedEdge Unit.unit := C.vertex_on_circle

@[simp] lemma embeddedEdge_eq_circle (C : CircularSegmentPlane) (e : C.pair.Edge) :
    C.embeddedEdge e = sphere C.centre C.radius := rfl

/-- The circle complement is precisely the union of the two specified faces. -/
theorem compl_embeddedEdge (C : CircularSegmentPlane) (e : C.pair.Edge) :
    (C.embeddedEdge e)ᶜ = C.faceRegion false ∪ C.faceRegion true :=
  compl_sphere_eq_ball_union_outside C.centre C.radius

private lemma one_lt_rank_plane : 1 < Module.rank ℝ (ℝ × ℝ) := by
  simp
  norm_num

/-- The Boolean indices denote the actual path-connected faces, for the
arbitrary interior representative as well as the exterior representative. -/
theorem pathComponentIn_faceRepresentative (C : CircularSegmentPlane)
    (f : C.pair.Face) (e : C.pair.Edge) :
    pathComponentIn (C.embeddedEdge e)ᶜ (C.faceRepresentative f) = C.faceRegion f := by
  change Bool at f
  cases f
  · change pathComponentIn (sphere C.centre C.radius)ᶜ C.interior = ball C.centre C.radius
    exact pathComponentIn_compl_sphere_of_inside C.centre C.radius_pos C.interior_inside
  · change pathComponentIn (sphere C.centre C.radius)ᶜ C.exterior =
      (fun z : ℝ × ℝ => dist z C.centre) ⁻¹' Ioi C.radius
    exact pathComponentIn_compl_sphere_of_outside one_lt_rank_plane C.centre
      C.radius_pos C.exterior_outside

/-- The generally non-radial straight dual arc between the two face points. -/
noncomputable def dualArc (C : CircularSegmentPlane) : ℝ → ℝ × ℝ :=
  segmentArc C.interior C.exterior

@[simp] lemma dualArc_zero (C : CircularSegmentPlane) :
    C.dualArc 0 = C.faceRepresentative false := by
  simp [dualArc, faceRepresentative]

@[simp] lemma dualArc_one (C : CircularSegmentPlane) :
    C.dualArc 1 = C.faceRepresentative true := by
  simp [dualArc, faceRepresentative]

lemma continuous_dualArc (C : CircularSegmentPlane) : Continuous C.dualArc := by
  exact continuous_segmentArc C.interior C.exterior

/-- The primal/dual crossing parameters form a singleton. -/
theorem dualArc_crossing_parameters (C : CircularSegmentPlane) (e : C.pair.Edge) :
    ∃ t₀ : ℝ, {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ C.dualArc t ∈ C.embeddedEdge e} = {t₀} := by
  exact segmentArc_crossing_parameters C.interior_inside C.exterior_outside

/-- The geometric primal/dual crossing number is exactly one. -/
theorem dualArc_crossing_card (C : CircularSegmentPlane) (e : C.pair.Edge) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ C.dualArc t ∈ C.embeddedEdge e}.ncard = 1 := by
  exact segmentArc_crossing_card C.centre C.interior C.exterior
    C.interior_inside C.exterior_outside

/-- The crossing divides the dual arc into an inside prefix and an outside
suffix; in particular the dual arc does not re-enter the circular face. -/
theorem dualArc_crossing_faces (C : CircularSegmentPlane) (e : C.pair.Edge) :
    ∃ t₀ ∈ Ioo (0 : ℝ) 1,
      C.dualArc t₀ ∈ C.embeddedEdge e ∧
      (∀ s ∈ Icc (0 : ℝ) 1, s < t₀ → C.dualArc s ∈ C.faceRegion false) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, t₀ < s → C.dualArc s ∈ C.faceRegion true) := by
  exact segmentArc_exists_crossing_faces C.interior_inside C.exterior_outside

/-- All geometric conclusions together with the exact graphic-dual equality. -/
structure Certificate (C : CircularSegmentPlane) : Prop where
  graphicDual : C.pair.GraphicDualCertificate
  inside_face : pathComponentIn (C.embeddedEdge Unit.unit)ᶜ C.interior = C.faceRegion false
  outside_face : pathComponentIn (C.embeddedEdge Unit.unit)ᶜ C.exterior = C.faceRegion true
  crossing_card : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
    C.dualArc t ∈ C.embeddedEdge Unit.unit}.ncard = 1
  crossing_faces : ∃ t₀ ∈ Ioo (0 : ℝ) 1,
    C.dualArc t₀ ∈ C.embeddedEdge Unit.unit ∧
    (∀ s ∈ Icc (0 : ℝ) 1, s < t₀ → C.dualArc s ∈ C.faceRegion false) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, t₀ < s → C.dualArc s ∈ C.faceRegion true)

/-- Unconditional certificate of the explicit circular plane embedding and its
arbitrary straight inside-to-outside dual arc. -/
theorem certificate (C : CircularSegmentPlane) : C.Certificate where
  graphicDual := graphicDualCertificate_pair C
  inside_face := C.pathComponentIn_faceRepresentative false Unit.unit
  outside_face := C.pathComponentIn_faceRepresentative true Unit.unit
  crossing_card := C.dualArc_crossing_card Unit.unit
  crossing_faces := C.dualArc_crossing_faces Unit.unit

end CircularSegmentPlane
end FK.PlaneTopology
