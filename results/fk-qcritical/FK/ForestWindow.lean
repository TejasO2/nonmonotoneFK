import FK.ForestRotation

/-!
# Geometric/combinatorial face equivalence for straight forests
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FiniteFiber
open FK.Finite.PlaneMatroid.Cellular.Rotation

/-- For a connected straight labelled forest with a dart, the canonical
spherical incidence rotation and the actual continuous plane embedding have
the same one-face quotient. -/
def faceEquiv {G : LabelledMultigraph} (hG : G.IsLabelledForest)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (hdart : Nonempty (Dart G)) (E : StraightFiniteArcEmbedding G) :
    (incidenceRotationSphere hG hconn hdart).Face ≃ E.Face := by
  let R := incidenceRotationSphere hG hconn hdart
  letI : Subsingleton R.Face :=
    face_subsingleton_rotation_of_isLabelledForest hG hconn R.toRotationSystem
  letI : Nonempty R.Face := ⟨R.faceOf hdart.some⟩
  letI : Subsingleton E.Face := face_subsingleton_of_isLabelledForest hG E
  letI : Nonempty E.Face := face_nonempty_of_isLabelledForest hG E
  exact equivOfSubsingletonOfSubsingleton
    (fun _ => (face_nonempty_of_isLabelledForest hG E).some)
    (fun _ => R.faceOf hdart.some)

/-- Both sides of the face equivalence are singletons. -/
lemma card_combinatorial_face {G : LabelledMultigraph}
    (hG : G.IsLabelledForest)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (hdart : Nonempty (Dart G)) :
    @Fintype.card (incidenceRotationSphere hG hconn hdart).Face
      (incidenceRotationSphere hG hconn hdart).dualPair.fintypeFace = 1 := by
  let R := incidenceRotationSphere hG hconn hdart
  letI : Fintype R.Face := R.dualPair.fintypeFace
  letI : Subsingleton R.Face :=
    face_subsingleton_rotation_of_isLabelledForest hG hconn R.toRotationSystem
  exact Fintype.card_eq_one_iff.mpr ⟨R.faceOf hdart.some, fun _ => Subsingleton.elim _ _⟩

end
end FK.PlaneTopology.Continuous.Forest
