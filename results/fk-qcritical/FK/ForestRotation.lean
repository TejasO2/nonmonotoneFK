import FK.StraightForest
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.End
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A canonical rotation for a labelled forest

A finite incidence-fiber rotation is constructed without geometric input.
Connectedness and the labelled-forest bridge condition force its face quotient
to be a singleton by a binary coboundary-rank argument.
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FiniteFiber
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.Finite.PlaneMatroid.Cellular
open Equiv.Perm

/-- Every pair of points belongs to one `finRotate` cycle, including the empty
and singleton cases. -/
lemma sameCycle_finRotate_total {n : ℕ} (x y : Fin n) :
    (finRotate n).SameCycle x y := by
  by_cases hn0 : n = 0
  · subst n
    exact Fin.elim0 x
  by_cases hn1 : n = 1
  · subst n
    exact (Subsingleton.elim x y).sameCycle _
  have hn : 2 ≤ n := by omega
  apply (isCycle_finRotate_of_le hn).sameCycle
  · rw [← Equiv.Perm.mem_support, support_finRotate_of_le hn]
    exact Finset.mem_univ _
  · rw [← Equiv.Perm.mem_support, support_finRotate_of_le hn]
    exact Finset.mem_univ _

/-- Same-cycle witnesses are transported by conjugation. -/
lemma sameCycle_permCongr {α β : Type*} (e : α ≃ β) (f : Equiv.Perm α)
    {x y : α} (h : f.SameCycle x y) :
    (e.permCongr f).SameCycle (e x) (e y) := by
  let conj : Equiv.Perm α ≃* Equiv.Perm β := {
    e.permCongr with
    map_mul' := by
      intro a b
      exact (e.permCongr_trans b a).symm }
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hp : e.permCongr (f ^ n) = (e.permCongr f) ^ n := by
    change conj (f ^ n) = (conj f) ^ n
    exact map_zpow conj f n
  rw [← hp]
  simp [hn]

/-- Darts incident to a prescribed vertex. -/
abbrev IncidentDart (G : LabelledMultigraph) (v : G.Vertex) :=
  {d : Dart G // vertex G d = v}

/-- Darts are the disjoint sum of their incidence fibers. -/
def incidentSigmaEquiv (G : LabelledMultigraph) :
    (Σ v, IncidentDart G v) ≃ Dart G where
  toFun x := x.2.1
  invFun d := ⟨vertex G d, ⟨d, rfl⟩⟩
  left_inv x := by rcases x with ⟨v, ⟨d, hd⟩⟩; cases hd; rfl
  right_inv d := rfl

/-- Rotate the incidences at one vertex by enumerating them finitely. -/
def localCycle (G : LabelledMultigraph) (v : G.Vertex) :
    Equiv.Perm (IncidentDart G v) :=
  (Fintype.equivFin (IncidentDart G v)).symm.permCongr
    (finRotate (Fintype.card (IncidentDart G v)))

lemma sameCycle_localCycle (G : LabelledMultigraph) (v : G.Vertex)
    (x y : IncidentDart G v) : (localCycle G v).SameCycle x y := by
  let e := Fintype.equivFin (IncidentDart G v)
  have h := sameCycle_permCongr e.symm (finRotate (Fintype.card (IncidentDart G v)))
    (sameCycle_finRotate_total (e x) (e y))
  simpa [localCycle, e] using h

/-- Fiberwise same-cycle witnesses lift to the disjoint sum. -/
lemma sameCycle_sigma_fibers {ι : Type*} {β : ι → Type*}
    (F : ∀ i, Equiv.Perm (β i)) {i : ι} {x y : β i}
    (h : (F i).SameCycle x y) :
    (Equiv.Perm.sigmaCongrRightHom β F).SameCycle (⟨i, x⟩) (⟨i, y⟩) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have hp := map_zpow (Equiv.Perm.sigmaCongrRightHom β) F n
  rw [← hp]
  change (⟨i, ((F i) ^ n) x⟩ : Σ i, β i) = ⟨i, y⟩
  rw [hn]

/-- The constructed fiberwise rotation on all darts. -/
def rotationPerm (G : LabelledMultigraph) : Equiv.Perm (Dart G) :=
  (incidentSigmaEquiv G).permCongr (Equiv.Perm.sigmaCongrRightHom _ (localCycle G))

lemma vertex_rotationPerm (G : LabelledMultigraph) (d : Dart G) :
    vertex G (rotationPerm G d) = vertex G d := by
  let x := (incidentSigmaEquiv G).symm d
  have hd : incidentSigmaEquiv G x = d := (incidentSigmaEquiv G).apply_symm_apply d
  rw [← hd]
  rcases x with ⟨v, d⟩
  unfold rotationPerm
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact (((Equiv.Perm.sigmaCongrRightHom _ (localCycle G)) ⟨v, d⟩).2.2).trans d.2.symm

lemma sameCycle_rotationPerm (G : LabelledMultigraph) {d d' : Dart G}
    (hd : vertex G d = vertex G d') : (rotationPerm G).SameCycle d d' := by
  let x := (incidentSigmaEquiv G).symm d
  let y := (incidentSigmaEquiv G).symm d'
  have hsigma : (Equiv.Perm.sigmaCongrRightHom _ (localCycle G)).SameCycle x y := by
    rcases hx : x with ⟨v, x⟩
    rcases hy : y with ⟨w, y⟩
    have hxd : incidentSigmaEquiv G ⟨v, x⟩ = d := by
      rw [← hx]
      exact (incidentSigmaEquiv G).apply_symm_apply d
    have hyd : incidentSigmaEquiv G ⟨w, y⟩ = d' := by
      rw [← hy]
      exact (incidentSigmaEquiv G).apply_symm_apply d'
    have hvw : v = w := x.2.symm.trans ((congrArg (vertex G) hxd).trans
      (hd.trans ((congrArg (vertex G) hyd).symm.trans y.2)))
    subst w
    exact sameCycle_sigma_fibers (localCycle G) (sameCycle_localCycle G v x y)
  have h := sameCycle_permCongr (incidentSigmaEquiv G)
    (Equiv.Perm.sigmaCongrRightHom _ (localCycle G)) hsigma
  simpa [rotationPerm, x, y] using h

/-- A genuine local cyclic rotation on any finite labelled multigraph. -/
def incidenceRotation (G : LabelledMultigraph) : RotationSystem G where
  rotation := rotationPerm G
  vertex_rotation := vertex_rotationPerm G
  sameCycle_rotation := by
    intro d d' hd
    exact sameCycle_rotationPerm G hd

/-- A connected labelled forest with a dart has at most one face in any
rotation system.  Rotation compatibility puts the dual coboundary in the
primal cycle space, which has dimension zero for a forest. -/
lemma card_face_le_one_rotation_of_isLabelledForest
    {G : LabelledMultigraph} (hG : G.IsLabelledForest)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (R : RotationSystem G) (d : Dart G) :
    @Fintype.card R.Face R.dualPair.fintypeFace ≤ 1 := by
  classical
  letI : Nonempty G.Vertex := ⟨G.source d.1⟩
  letI : Fintype R.Face := R.dualPair.fintypeFace
  letI : Nonempty R.dualPair.faceDual.Vertex := ⟨R.faceOf d⟩
  have hc : G.componentCount G.freeBoundary G.allOpen = 1 :=
    componentCount_eq_one_of_preconnected G G.freeBoundary G.allOpen
      (Classical.arbitrary G.Vertex) hconn
  have hcount := G.componentCount_add_openCard_of_free_isOpenForest G.allOpen hG
  rw [hc, openCard_allOpen] at hcount
  have hrP := incidence_rank_add_one G hconn
  change Module.finrank F2 (LinearMap.range (boundary G)) + 1 =
    Fintype.card G.Vertex at hrP
  have hdconn := R.allOpen_preconnected hconn
  have hrD := finrank_range_coboundary_add_one R.dualPair.faceDual hdconn
  change Module.finrank F2 (LinearMap.range (coboundary R.dualPair.faceDual)) + 1 =
    Fintype.card R.Face at hrD
  have hnull := (boundary G).finrank_range_add_finrank_ker
  rw [Module.finrank_pi F2] at hnull
  have hsub : LinearMap.range (coboundary R.dualPair.faceDual) ≤
      LinearMap.ker (boundary R.dualPair.primal) := by
    intro x hx
    obtain ⟨q, rfl⟩ := hx
    exact R.boundary_faceDual_coboundary q
  have hle := Submodule.finrank_mono hsub
  change Module.finrank F2 (LinearMap.range (coboundary R.dualPair.faceDual)) ≤
    Module.finrank F2 (LinearMap.ker (boundary G)) at hle
  omega

/-- Every rotation of a connected labelled forest has exactly one face. -/
lemma face_subsingleton_rotation_of_isLabelledForest
    {G : LabelledMultigraph} (hG : G.IsLabelledForest)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (R : RotationSystem G) : Subsingleton R.Face := by
  by_cases hd : Nonempty (Dart G)
  · letI : Fintype R.Face := R.dualPair.fintypeFace
    have hle := card_face_le_one_rotation_of_isLabelledForest hG hconn R hd.some
    have hpos : 0 < Fintype.card R.Face := Fintype.card_pos_iff.mpr ⟨R.faceOf hd.some⟩
    have hone : Fintype.card R.Face = 1 := by omega
    obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp hone
    exact ⟨fun f g => (hz f).trans (hz g).symm⟩
  · letI : IsEmpty (Dart G) := not_nonempty_iff.mp hd
    constructor
    intro f g
    exact isEmptyElim f.out

/-- The constructed incidence rotation is spherical on every connected
labelled forest with an edge. -/
def incidenceRotationSphere {G : LabelledMultigraph}
    (hG : G.IsLabelledForest)
    (hconn : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected)
    (hdart : Nonempty (Dart G)) : RotationSphere G where
  toRotationSystem := incidenceRotation G
  nonemptyVertex := ⟨G.source hdart.some.1⟩
  nonemptyDart := hdart
  primal_preconnected := hconn
  euler := by
    letI : Nonempty G.Vertex := ⟨G.source hdart.some.1⟩
    letI : Subsingleton (incidenceRotation G).Face :=
      face_subsingleton_rotation_of_isLabelledForest hG hconn (incidenceRotation G)
    letI : Fintype (incidenceRotation G).Face := (incidenceRotation G).dualPair.fintypeFace
    have hf : Fintype.card (incidenceRotation G).Face = 1 :=
      Fintype.card_eq_one_iff.mpr
        ⟨(incidenceRotation G).faceOf hdart.some, fun _ => Subsingleton.elim _ _⟩
    rw [hf]
    have hc : G.componentCount G.freeBoundary G.allOpen = 1 :=
      componentCount_eq_one_of_preconnected G G.freeBoundary G.allOpen
        (Classical.arbitrary G.Vertex) hconn
    have hcount := G.componentCount_add_openCard_of_free_isOpenForest G.allOpen hG
    rw [hc, openCard_allOpen] at hcount
    omega

end
end FK.PlaneTopology.Continuous.Forest
