import FK.CellularSealedCuts
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Continuous plane-arc windows

A source-faithful finite plane window is made of injective continuous arcs,
with prescribed graph endpoints and intersections only at common endpoints.
No combinatorial rotation or Jordan-separation statement is built into the
embedding structure.

For every such finite window the drawn carrier is compact. Its complementary
faces are open and their connected components agree with path components.
These facts use only continuity and local path-connectedness of the plane.
-/

namespace FK.PlaneTopology.Continuous

open Set
open scoped Classical unitInterval
open FK.Finite
open FK.Finite.LabelledMultigraph

abbrev Plane := ℝ × ℝ

/-- An embedded Jordan arc: a continuous injective parametrization of the
unit interval. No polygonality is assumed. -/
structure JordanArc (X : Type*) [TopologicalSpace X] where
  toMap : C(I, X)
  injective : Function.Injective toMap

namespace JordanArc

variable {X : Type*} [TopologicalSpace X]

/-- The underlying continuous map of a Jordan arc. -/
instance : CoeFun (JordanArc X) (fun _ => I → X) where
  coe a := a.toMap

@[simp] theorem toMap_apply (a : JordanArc X) (t : I) : a.toMap t = a t := rfl

theorem continuous (a : JordanArc X) : Continuous a := a.toMap.continuous

/-- The range of an arc is compact. -/
theorem isCompact_range (a : JordanArc X) : IsCompact (Set.range a) := by
  have h : IsCompact ((a : I → X) '' Set.univ) :=
    isCompact_univ.image a.continuous
  simpa only [Set.image_univ] using h

/-- In a Hausdorff plane the range of an arc is closed. -/
theorem isClosed_range [T2Space X] (a : JordanArc X) : IsClosed (Set.range a) :=
  a.isCompact_range.isClosed

end JordanArc

/-- A finite labelled graph drawn by continuous Jordan arcs in the plane.
The last two fields are exactly the non-crossing conditions: a vertex cannot
lie in the interior of an arc, and every common point of two distinct arcs is
a common endpoint. Vertex injectivity excludes collapsed vertices. -/
structure FiniteArcEmbedding (L : LabelledMultigraph) where
  point : L.Vertex → Plane
  arc : L.Edge → JordanArc Plane
  point_injective : Function.Injective point
  source : ∀ e, arc e 0 = point (L.source e)
  target : ∀ e, arc e 1 = point (L.target e)
  vertex_intersection : ∀ v e t, point v = arc e t →
    (t = 0 ∧ L.source e = v) ∨ (t = 1 ∧ L.target e = v)
  intersection : ∀ {e f}, e ≠ f → ∀ s t, arc e s = arc f t →
    ∃ v : L.Vertex, arc e s = point v ∧
      ((s = 0 ∧ L.source e = v) ∨ (s = 1 ∧ L.target e = v)) ∧
      ((t = 0 ∧ L.source f = v) ∨ (t = 1 ∧ L.target f = v))

namespace FiniteArcEmbedding

variable {L : LabelledMultigraph} (E : FiniteArcEmbedding L)

/-- All points drawn by vertices or edge arcs. -/
def carrier : Set Plane :=
  Set.range E.point ∪ ⋃ e, Set.range (E.arc e)

/-- Finite arc windows have compact drawn carriers. -/
theorem isCompact_carrier : IsCompact E.carrier := by
  apply IsCompact.union
  · exact (Set.finite_range E.point).isCompact
  · exact isCompact_iUnion fun e => (E.arc e).isCompact_range

/-- The carrier is closed, hence the face carrier is open. -/
theorem isClosed_carrier : IsClosed E.carrier := E.isCompact_carrier.isClosed

theorem isOpen_compl_carrier : IsOpen E.carrierᶜ := E.isClosed_carrier.isOpen_compl

/-- The actual subtype of complementary plane points. -/
abbrev FacePoints := E.carrierᶜ

/-- Faces are connected components of the complement, as in §5.2 of the
source. This is a quotient of the complement subtype, not a separately
postulated collection of dual vertices. -/
abbrev Face := ConnectedComponents E.FacePoints

/-- Complement path-components inherit a locally path-connected topology. -/
noncomputable instance locallyPathConnectedFacePoints :
    LocallyPathConnectedSpace E.FacePoints :=
  E.isOpen_compl_carrier.locallyPathConnectedSpace

/-- Two complementary points determine the same source face exactly when
they are joined by a path avoiding every vertex and edge arc. -/
theorem face_eq_iff_joined (x y : E.FacePoints) :
    ConnectedComponents.mk x = ConnectedComponents.mk y ↔ Joined x y := by
  rw [ConnectedComponents.coe_eq_coe, connectedComponent_eq_iff_joined]

/-- Every source face is an open subset of the complement. -/
theorem isOpen_face (x : E.FacePoints) : IsOpen (connectedComponent x) :=
  isOpen_connectedComponent

/-- Restriction to the complement itself, in ambient-set notation. -/
theorem face_eq_iff_joinedIn (x y : Plane) (hx : x ∈ E.carrierᶜ)
    (hy : y ∈ E.carrierᶜ) :
    ConnectedComponents.mk (⟨x, hx⟩ : E.FacePoints) =
      ConnectedComponents.mk (⟨y, hy⟩ : E.FacePoints) ↔
      JoinedIn E.carrierᶜ x y := by
  rw [E.face_eq_iff_joined]
  exact (joinedIn_iff_joined hx hy).symm

end FiniteArcEmbedding

end FK.PlaneTopology.Continuous
