import FK.ContinuousSegmentWindow
import FK.TriangleRotation

/-!
# Arbitrary range-preserving reparametrizations of continuous plane windows

A finite continuous embedding may be reparametrized on every labelled edge by
an arbitrary Jordan arc with the same endpoints and range.  The original
noncrossing proofs and carrier then transport without any polygonality or
affine-parametrization assumption.  We apply this to every nondegenerate
triangle, obtaining its exact spherical rotation/actual-face window with
arbitrary continuous parametrizations of the three straight sides.
-/

namespace FK.PlaneTopology.Continuous

noncomputable section

open Set
open scoped Classical Convex unitInterval BigOperators
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation

variable {L : LabelledMultigraph}

/-- New Jordan parametrizations of all arcs of a finite embedding, with the
same endpoints and the same geometric ranges. -/
structure ArcReparametrization (E : FiniteArcEmbedding L) where
  arc : L.Edge → JordanArc Plane
  zero : ∀ e, arc e 0 = E.arc e 0
  one : ∀ e, arc e 1 = E.arc e 1
  range : ∀ e, Set.range (arc e) = Set.range (E.arc e)

namespace ArcReparametrization

variable {E : FiniteArcEmbedding L} (ρ : ArcReparametrization E)

lemma source_of_eq_old_zero {e : L.Edge} {t s : I}
    (h : ρ.arc e t = E.arc e s) (hs : s = 0) : t = 0 := by
  apply (ρ.arc e).injective
  calc
    ρ.arc e t = E.arc e s := h
    _ = E.arc e 0 := by rw [hs]
    _ = ρ.arc e 0 := (ρ.zero e).symm

lemma target_of_eq_old_one {e : L.Edge} {t s : I}
    (h : ρ.arc e t = E.arc e s) (hs : s = 1) : t = 1 := by
  apply (ρ.arc e).injective
  calc
    ρ.arc e t = E.arc e s := h
    _ = E.arc e 1 := by rw [hs]
    _ = ρ.arc e 1 := (ρ.one e).symm

lemma exists_old_parameter {e : L.Edge} (t : I) :
    ∃ s : I, E.arc e s = ρ.arc e t := by
  have ht : ρ.arc e t ∈ Set.range (E.arc e) := by
    rw [← ρ.range e]
    exact ⟨t, rfl⟩
  exact ht

end ArcReparametrization

namespace FiniteArcEmbedding

/-- Transport a source-faithful finite plane embedding along arbitrary
range-preserving Jordan-arc reparametrizations. -/
def reparametrize (E : FiniteArcEmbedding L)
    (ρ : ArcReparametrization E) : FiniteArcEmbedding L where
  point := E.point
  arc := ρ.arc
  point_injective := E.point_injective
  source e := (ρ.zero e).trans (E.source e)
  target e := (ρ.one e).trans (E.target e)
  vertex_intersection := by
    intro v e t h
    obtain ⟨s, hs⟩ := ρ.exists_old_parameter (e := e) t
    have hv : E.point v = E.arc e s := h.trans hs.symm
    rcases E.vertex_intersection v e s hv with hzero | hone
    · exact Or.inl ⟨ρ.source_of_eq_old_zero hs.symm hzero.1, hzero.2⟩
    · exact Or.inr ⟨ρ.target_of_eq_old_one hs.symm hone.1, hone.2⟩
  intersection := by
    intro e f hef s t hst
    obtain ⟨s', hs'⟩ := ρ.exists_old_parameter (e := e) s
    obtain ⟨t', ht'⟩ := ρ.exists_old_parameter (e := f) t
    have hold : E.arc e s' = E.arc f t' := hs'.trans (hst.trans ht'.symm)
    obtain ⟨v, hv, he, hf⟩ := E.intersection hef s' t' hold
    refine ⟨v, hs'.symm.trans hv, ?_, ?_⟩
    · rcases he with hzero | hone
      · exact Or.inl ⟨ρ.source_of_eq_old_zero hs'.symm hzero.1, hzero.2⟩
      · exact Or.inr ⟨ρ.target_of_eq_old_one hs'.symm hone.1, hone.2⟩
    · rcases hf with hzero | hone
      · exact Or.inl ⟨ρ.source_of_eq_old_zero ht'.symm hzero.1, hzero.2⟩
      · exact Or.inr ⟨ρ.target_of_eq_old_one ht'.symm hone.1, hone.2⟩

/-- Reparametrization leaves the entire compact geometric carrier unchanged. -/
theorem carrier_reparametrize (E : FiniteArcEmbedding L)
    (ρ : ArcReparametrization E) :
    (E.reparametrize ρ).carrier = E.carrier := by
  change Set.range E.point ∪ (⋃ e, Set.range (ρ.arc e)) =
    Set.range E.point ∪ (⋃ e, Set.range (E.arc e))
  simp_rw [ρ.range]

/-- The actual connected-component faces depend only on the carrier, so they
transport along arbitrary reparametrizations. -/
def faceEquivReparametrize (E : FiniteArcEmbedding L)
    (ρ : ArcReparametrization E) : E.Face ≃ (E.reparametrize ρ).Face := by
  change ConnectedComponents {x // x ∈ E.carrierᶜ} ≃
    ConnectedComponents {x // x ∈ (E.reparametrize ρ).carrierᶜ}
  rw [carrier_reparametrize]

end FiniteArcEmbedding

namespace Triangle

/-- Arbitrary continuous Jordan parametrizations of the three sides of an
affine-basis triangle.  Their ranges are required to lie in the corresponding
straight segments; the segment theorem proves that this inclusion is equality. -/
structure SideArcs (b : AffineBasis (Fin 3) ℝ Plane) where
  arc : Fin 3 → JordanArc Plane
  zero : ∀ e, arc e 0 = b (graph.source e)
  one : ∀ e, arc e 1 = b (graph.target e)
  range_subset : ∀ e, Set.range (arc e) ⊆
    [b (graph.source e) -[ℝ] b (graph.target e)]

/-- Package arbitrary side parametrizations as a reparametrization of the
existing straight triangle embedding. -/
def arcReparametrization (b : AffineBasis (Fin 3) ℝ Plane)
    (γ : SideArcs b) : ArcReparametrization (embedding b) where
  arc := γ.arc
  zero e := (γ.zero e).trans (arc_zero b e).symm
  one e := (γ.one e).trans (arc_one b e).symm
  range e := by
    calc
      Set.range (γ.arc e) = [b (graph.source e) -[ℝ] b (graph.target e)] :=
        SegmentArc.range_eq_segment_of_continuous (γ.arc e)
          (γ.zero e) (γ.one e) (γ.range_subset e) (endpoint_ne b e)
      _ = Set.range (arc b e) := (range_arc b e).symm

/-- The nondegenerate triangle with arbitrary continuous parametrizations of
its three straight sides. -/
def continuousEmbedding (b : AffineBasis (Fin 3) ℝ Plane) (γ : SideArcs b) :
    FiniteArcEmbedding graph :=
  (embedding b).reparametrize (arcReparametrization b γ)

/-- Its compact carrier is exactly the triangular boundary. -/
theorem carrier_continuousEmbedding (b : AffineBasis (Fin 3) ℝ Plane)
    (γ : SideArcs b) : (continuousEmbedding b γ).carrier = boundary b := by
  exact (FiniteArcEmbedding.carrier_reparametrize (embedding b)
    (arcReparametrization b γ)).trans (carrier_embedding b)

/-- Exact six-dart spherical-rotation/actual-face incidence for every choice of
continuous side parametrizations. -/
def continuousFaceEquiv (b : AffineBasis (Fin 3) ℝ Plane) (γ : SideArcs b) :
    rotationSystem.Face ≃ (continuousEmbedding b γ).Face :=
  (faceEquiv b).trans
    (FiniteArcEmbedding.faceEquivReparametrize (embedding b)
      (arcReparametrization b γ))

end Triangle
end
end FK.PlaneTopology.Continuous
