import FK.OpenCutSeparation
import FK.GridOpenCuts

/-!
# The cut criterion with a partially closed cut

`FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts` asks that
*every* edge of the finite cut be open.  The proof only ever traverses an edge
that an infinite open cluster actually crosses, and an open cluster can only
cross an *open* edge.  This file states and proves the sharpened criterion: it
is enough that the vertices incident with the **open** edges of the oriented cut
are mutually open-connected.  The published criterion is recovered as the
special case where the whole cut is open.

This is the form which survives the planar obstruction recorded in
`PlanarTarget.exists_dualNonpercolating_noOpenDiamondCut`, where every shell
carries at least one closed edge, so the strong criterion is never applicable.

## Main results

* `FK.PlaneTopology.WeakOpenCut.exists_open_orientedCut_vertex_of_walk`
* `FK.PlaneTopology.WeakOpenCut.globalAtMostOne_of_finite_openCut_on_openVertices`
* `FK.PlaneTopology.WeakOpenCut.globalAtMostOne_of_finite_openCuts` (recovered)
-/

namespace FK.PlaneTopology.WeakOpenCut

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.CutSeparation

variable {V : Type*}

/-- A vertex is **incident with an open edge of the oriented cut** of `A`. -/
def OpenCutIncident (G : SimpleGraph V) (ω : G.edgeSet → Bool) (A : Set V) (u : V) : Prop :=
  ∃ e ∈ orientedCut G A, ω e = true ∧ ∃ w : V, e.1 = s(u, w)

/-- **Crossing lemma, open-edge form.**  An open walk from inside `A` to outside
`A` traverses an *open* edge of the oriented cut, and the vertex of that edge on
the `A`-side is open-connected to the walk's source. -/
theorem exists_open_orientedCut_vertex_of_walk {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} {A : Set V} {x z : V} (p : G.Walk x z)
    (hp : IsOpenIn ω Set.univ p) (hxA : x ∈ A) (hzA : z ∉ A) :
    ∃ u : V, OpenCutIncident G ω A u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact (hzA hxA).elim
  | @cons a b c hab q ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      by_cases hbA : b ∈ A
      · obtain ⟨u, hu, hbu⟩ := ih hrest hbA hzA
        exact ⟨u, hu, (OpenConnected.of_adj hab (Set.mem_univ _) hopen).trans hbu⟩
      · refine ⟨a, ⟨⟨s(a, b), hab⟩, ?_, hopen, b, rfl⟩, OpenConnected.refl _ _ _⟩
        rw [mem_orientedCut_iff]
        exact ⟨a, hxA, b, hbA, hab, rfl⟩

/-- **The sharpened finite open cut criterion.**  A finite cut containing both
vertices whose *open* part has open-connected incident vertices joins every two
infinite open clusters. -/
theorem globalAtMostOne_of_finite_openCut_on_openVertices {G : SimpleGraph V}
    {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ExteriorInfiniteCluster G ω Set.univ x →
      ExteriorInfiniteCluster G ω Set.univ y →
      ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
        (∀ u v : V, OpenCutIncident G ω A u → OpenCutIncident G ω A v →
          OpenConnected G ω Set.univ u v)) :
    GlobalAtMostOne G ω := by
  intro x y hx hy
  obtain ⟨A, hAfin, hxA, hyA, hconn⟩ := h x y hx hy
  have hex : ∃ z : V, OpenConnected G ω Set.univ x z ∧ z ∉ A := by
    by_contra hc
    push_neg at hc
    exact hx (hAfin.subset fun z hz => hc z hz)
  obtain ⟨z, hxz, hzA⟩ := hex
  obtain ⟨p, hp⟩ := hxz
  obtain ⟨u, hu, hxu⟩ := exists_open_orientedCut_vertex_of_walk p hp hxA hzA
  have hey : ∃ z : V, OpenConnected G ω Set.univ y z ∧ z ∉ A := by
    by_contra hc
    push_neg at hc
    exact hy (hAfin.subset fun z hz => hc z hz)
  obtain ⟨w, hyw, hwA⟩ := hey
  obtain ⟨q, hq⟩ := hyw
  obtain ⟨v, hv, hyv⟩ := exists_open_orientedCut_vertex_of_walk q hq hyA hwA
  exact hxu.trans ((hconn u v hu hv).trans (openConnected_symm hyv))

/-- **The published criterion is the special case of a fully open cut.** -/
theorem globalAtMostOne_of_finite_openCuts {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ e ∈ orientedCut G A, ω e = true) ∧
      (∀ u v : V, VertexOnLabels (orientedCut G A) u →
        VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v)) :
    GlobalAtMostOne G ω := by
  apply globalAtMostOne_of_finite_openCut_on_openVertices
  intro x y _ _
  obtain ⟨A, hAfin, hxA, hyA, hopen, hconn⟩ := h x y
  have aux : ∀ {u : V}, OpenCutIncident G ω A u → VertexOnLabels (orientedCut G A) u := by
    rintro u ⟨e, he, -, w, hw⟩
    have hadj : G.Adj u w := by
      have hmem : s(u, w) ∈ G.edgeSet := hw ▸ e.2
      rwa [SimpleGraph.mem_edgeSet] at hmem
    refine ⟨w, hadj, ?_⟩
    have heq : e = (⟨s(u, w), hadj⟩ : G.edgeSet) := Subtype.ext hw
    rw [← heq]
    exact he
  refine ⟨A, hAfin, hxA, hyA, ?_⟩
  intro u v hu hv
  exact hconn u v (aux hu) (aux hv)

end FK.PlaneTopology.WeakOpenCut

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.WeakOpenCut.exists_open_orientedCut_vertex_of_walk
#print axioms FK.PlaneTopology.WeakOpenCut.globalAtMostOne_of_finite_openCut_on_openVertices
#print axioms FK.PlaneTopology.WeakOpenCut.globalAtMostOne_of_finite_openCuts
