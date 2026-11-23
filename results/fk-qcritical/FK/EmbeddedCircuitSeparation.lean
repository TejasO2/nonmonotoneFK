import FK.PlaneClusterTarget
import FK.PlaneCutCircuit
import FK.RotationSystemDuality
import FK.CircleSeparation

/-!
# Embedded separating labels and open paths

This module supplies the topological step that finite matroid duality does not
provide.  An edge realization assigns an actual continuous arc to every edge.
For a specified locus `K`, a set of labels controls crossings when every arc
meeting `K` has its label in that set.  If all those labels are closed, an open
walk cannot cross `K`.

The realization hypotheses are deliberately explicit.  In particular, no
matroid circuit is asserted to be a Jordan curve.  For metric spheres we use
the proved inside/outside separation theorem from `FK.CircleSeparation`, and
also obtain a finite-component conclusion when only finitely many embedded
vertices lie in the ball.
-/

namespace FK.PlaneTopology

open Set Metric unitInterval
open scoped Topology
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

section SimpleGraph

variable {V X : Type*} [TopologicalSpace X]

/-- Continuous arcs joining the embedded endpoints of a simple graph.  This is
only path realization data: injectivity and planarity are separate questions. -/
structure OpenPathRealization (G : SimpleGraph V) (vertex : V → X) where
  arc : ∀ {u v : V}, G.Adj u v → Path (vertex u) (vertex v)

namespace OpenPathRealization

variable {G : SimpleGraph V} {vertex : V → X}

/-- `C` accounts for every realized edge arc that meets `K`.  Using the actual
edge subtype retains the proof that the crossing edge belongs to `G`. -/
def CrossingControlledBy (R : OpenPathRealization G vertex)
    (K : Set X) (C : Set G.edgeSet) : Prop :=
  ∀ {u v : V} (h : G.Adj u v),
    (∃ t : I, R.arc h t ∈ K) → (⟨s(u, v), h⟩ : G.edgeSet) ∈ C

/-- One open edge has a path in the complement of the geometric locus when
all labels controlling its crossings are closed. -/
lemma joinedIn_compl_adj (R : OpenPathRealization G vertex)
    {K : Set X} {C : Set G.edgeSet} {ω : G.edgeSet → Bool}
    (hcross : R.CrossingControlledBy K C)
    (hclosed : ∀ e ∈ C, ω e = false)
    {u v : V} (huv : G.Adj u v) (hopen : ω ⟨s(u, v), huv⟩ = true) :
    JoinedIn Kᶜ (vertex u) (vertex v) := by
  refine ⟨R.arc huv, fun t => ?_⟩
  change R.arc huv t ∉ K
  intro ht
  have hmem : (⟨s(u, v), huv⟩ : G.edgeSet) ∈ C := hcross huv ⟨t, ht⟩
  have hfalse := hclosed _ hmem
  simp [hopen] at hfalse

/-- Concatenation of realized edges: an entire open walk stays off `K`. -/
lemma joinedIn_compl_openConnected (R : OpenPathRealization G vertex)
    {K : Set X} {C : Set G.edgeSet} {ω : G.edgeSet → Bool}
    (hcross : R.CrossingControlledBy K C)
    (hvertices : ∀ v, vertex v ∈ Kᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    {u v : V} (huv : OpenConnected G ω Set.univ u v) :
    JoinedIn Kᶜ (vertex u) (vertex v) := by
  obtain ⟨p, hp⟩ := huv
  induction p with
  | nil => exact JoinedIn.refl (hvertices _)
  | @cons u v w huv p ih =>
      have hparts := isOpenIn_cons.mp hp
      exact (R.joinedIn_compl_adj hcross hclosed huv hparts.1.2).trans
        (ih hparts.2)

end OpenPathRealization
end SimpleGraph

section SimpleGraphSphere

variable {V X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- A closed crossing-controlling label set blocks every open connection from
the inside of a metric sphere to its outside. -/
theorem not_openConnected_sphere_of_inside_outside
    (R : OpenPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.edgeSet} {ω : G.edgeSet → Bool}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    {x y : V} (hx : vertex x ∈ ball c r)
    (hy : vertex y ∈ (fun z : X => dist z c) ⁻¹' Ioi r) :
    ¬ OpenConnected G ω Set.univ x y := by
  intro hxy
  exact not_joinedIn_compl_sphere_of_inside_outside hx hy
    (R.joinedIn_compl_openConnected hcross hvertices hclosed hxy)

/-- The same obstruction says that an open component starting inside a sphere
cannot contain a vertex outside it. -/
theorem mem_ball_of_openConnected_sphere
    (R : OpenPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.edgeSet} {ω : G.edgeSet → Bool}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    {x y : V} (hx : vertex x ∈ ball c r)
    (hxy : OpenConnected G ω Set.univ x y) :
    vertex y ∈ ball c r := by
  have hy := hvertices y
  rw [compl_sphere_eq_ball_union_outside] at hy
  rcases hy with hy | hy
  · exact hy
  · exact (not_openConnected_sphere_of_inside_outside R hcross hvertices hclosed
      hx hy hxy).elim

/-- A proper-on-balls vertex realization turns the sphere obstruction into an
actual finite-cluster statement. -/
theorem finite_openComponent_sphere
    (R : OpenPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.edgeSet} {ω : G.edgeSet → Bool}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    (hproper : (vertex ⁻¹' ball c r).Finite)
    {x : V} (hx : vertex x ∈ ball c r) :
    {y | OpenConnected G ω Set.univ x y}.Finite := by
  apply hproper.subset
  intro y hxy
  exact mem_ball_of_openConnected_sphere R hcross hvertices hclosed hx hxy

/-- In the repository's global percolation language, such a vertex does not
belong to an infinite open cluster. -/
theorem not_exteriorInfiniteCluster_sphere
    (R : OpenPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.edgeSet} {ω : G.edgeSet → Bool}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    (hproper : (vertex ⁻¹' ball c r).Finite)
    {x : V} (hx : vertex x ∈ ball c r) :
    ¬ ExteriorInfiniteCluster G ω Set.univ x := by
  intro hxinf
  exact hxinf (finite_openComponent_sphere R hcross hvertices hclosed hproper hx)

end SimpleGraphSphere

section LabelledMultigraph

open FK.Finite
open FK.Finite.LabelledMultigraph

variable {X : Type*} [TopologicalSpace X]

/-- A continuous realization of every labelled edge, preserving its source and
target.  Parallel labels remain distinct. -/
structure LabelledPathRealization (G : LabelledMultigraph) (vertex : G.Vertex → X) where
  arc : ∀ e : G.Edge, Path (vertex (G.source e)) (vertex (G.target e))

namespace LabelledPathRealization

variable {G : LabelledMultigraph} {vertex : G.Vertex → X}

def CrossingControlledBy (R : LabelledPathRealization G vertex)
    (K : Set X) (C : Set G.Edge) : Prop :=
  ∀ e : G.Edge, (∃ t : I, R.arc e t ∈ K) → e ∈ C

lemma joinedIn_compl_label (R : LabelledPathRealization G vertex)
    {K : Set X} {C : Set G.Edge} {ω : G.Configuration}
    (hcross : R.CrossingControlledBy K C)
    (hclosed : ∀ e ∈ C, ω e = false)
    {e : G.Edge} (he : ω e = true) :
    JoinedIn Kᶜ (vertex (G.source e)) (vertex (G.target e)) := by
  refine ⟨R.arc e, fun t => ?_⟩
  change R.arc e t ∉ K
  intro ht
  have hfalse := hclosed e (hcross e ⟨t, ht⟩)
  simp [he] at hfalse

/-- Every adjacency of the actual open connection graph is realized in the
complement of `K`.  The free-boundary alternative is impossible by irreflexivity. -/
lemma joinedIn_compl_adj (R : LabelledPathRealization G vertex)
    {K : Set X} {C : Set G.Edge} {ω : G.Configuration}
    (hcross : R.CrossingControlledBy K C)
    (hclosed : ∀ e ∈ C, ω e = false)
    {u v : G.Vertex} (huv : (G.connectionGraph G.freeBoundary ω).Adj u v) :
    JoinedIn Kᶜ (vertex u) (vertex v) := by
  rcases huv with ⟨hne, hfree | ⟨e, he, hjoin⟩⟩
  · exact (hne hfree).elim
  · rcases hjoin with ⟨hes, het⟩ | ⟨het, hes⟩
    · rw [← hes, ← het]
      exact R.joinedIn_compl_label hcross hclosed he
    · rw [← hes, ← het]
      exact (R.joinedIn_compl_label hcross hclosed he).symm

/-- Labelled version of walk concatenation over the actual open connection graph. -/
lemma joinedIn_compl_reachable (R : LabelledPathRealization G vertex)
    {K : Set X} {C : Set G.Edge} {ω : G.Configuration}
    (hcross : R.CrossingControlledBy K C)
    (hvertices : ∀ v, vertex v ∈ Kᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    {u v : G.Vertex} (huv : (G.connectionGraph G.freeBoundary ω).Reachable u v) :
    JoinedIn Kᶜ (vertex u) (vertex v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact JoinedIn.refl (hvertices _)
  | @cons u v w huv p ih =>
      exact (R.joinedIn_compl_adj hcross hclosed huv).trans ih

end LabelledPathRealization
end LabelledMultigraph

section LabelledSphere

open FK.Finite
open FK.Finite.LabelledMultigraph

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : LabelledMultigraph} {vertex : G.Vertex → X}

theorem not_reachable_sphere_of_inside_outside
    (R : LabelledPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.Edge} {ω : G.Configuration}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    {x y : G.Vertex} (hx : vertex x ∈ ball c r)
    (hy : vertex y ∈ (fun z : X => dist z c) ⁻¹' Ioi r) :
    ¬ (G.connectionGraph G.freeBoundary ω).Reachable x y := by
  intro hxy
  exact not_joinedIn_compl_sphere_of_inside_outside hx hy
    (R.joinedIn_compl_reachable hcross hvertices hclosed hxy)

theorem mem_ball_of_reachable_sphere
    (R : LabelledPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.Edge} {ω : G.Configuration}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    {x y : G.Vertex} (hx : vertex x ∈ ball c r)
    (hxy : (G.connectionGraph G.freeBoundary ω).Reachable x y) :
    vertex y ∈ ball c r := by
  have hy := hvertices y
  rw [compl_sphere_eq_ball_union_outside] at hy
  rcases hy with hy | hy
  · exact hy
  · exact (not_reachable_sphere_of_inside_outside R hcross hvertices hclosed
      hx hy hxy).elim

theorem finite_openVertexComponent_sphere
    (R : LabelledPathRealization G vertex) {c : X} {r : ℝ}
    {C : Set G.Edge} {ω : G.Configuration}
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hclosed : ∀ e ∈ C, ω e = false)
    (hproper : (vertex ⁻¹' ball c r).Finite)
    {x : G.Vertex} (hx : vertex x ∈ ball c r) :
    (G.openVertexComponent ω x).Finite := by
  apply hproper.subset
  intro y hxy
  exact mem_ball_of_reachable_sphere R hcross hvertices hclosed hx hxy

end LabelledSphere

end FK.PlaneTopology


namespace FK.PlaneTopology

open Set Metric
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid

section FiniteDualCircuit

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Geometric data that an actual embedding must supply for dual circuits.
This structure is not constructed from a `GraphicDualCertificate`: its fields
are the independent Jordan/crossing input.  In particular, `crossing` says
that a primal edge arc meeting the sphere belongs to that circuit's label set. -/
structure SphericalDualCircuitGeometry (P : LabelledDualPair)
    {vertex : P.Vertex → X} (R : LabelledPathRealization P.primal vertex) where
  centre : Set P.Edge → X
  radius : Set P.Edge → ℝ
  radius_pos : ∀ C, P.faceDual.cycleMatroid.IsCircuit C → 0 < radius C
  vertex_off : ∀ C, P.faceDual.cycleMatroid.IsCircuit C →
    ∀ v, vertex v ∈ (sphere (centre C) (radius C))ᶜ
  crossing : ∀ C, P.faceDual.cycleMatroid.IsCircuit C →
    R.CrossingControlledBy (sphere (centre C) (radius C)) C

/-- For every boundary label of an actual finite primal open component, the
proved cut/circuit theorem supplies a dual-open circuit.  If the supplied
spherical geometry places the component's root inside that circuit and only
finitely many vertices lie in its ball, the whole component is finite.

The alternative that the root is not inside the produced circuit remains a
geometric/exhaustion obligation; it is not hidden in the statement. -/
theorem exists_dualOpen_circuit_boundary_openComponent_finite_of_spherical
    {P : LabelledDualPair} {vertex : P.Vertex → X}
    (R : LabelledPathRealization P.primal vertex)
    (S : SphericalDualCircuitGeometry P R)
    (hP : P.GraphicDualCertificate) (ω : P.primal.Configuration) (x : P.Vertex)
    {e : P.Edge} (he : e ∈ P.primal.vertexCut (P.primal.openVertexComponent ω x))
    (hproper : ∀ C, P.faceDual.cycleMatroid.IsCircuit C →
      (vertex ⁻¹' ball (S.centre C) (S.radius C)).Finite) :
    ∃ C, C ⊆ P.primal.vertexCut (P.primal.openVertexComponent ω x) ∧
      e ∈ C ∧ P.faceDual.cycleMatroid.IsCircuit C ∧
      C ⊆ P.faceDual.openEdgeSet (dualConfig (Equiv.refl P.Edge) ω) ∧
      0 < S.radius C ∧
      (vertex x ∈ ball (S.centre C) (S.radius C) →
        (P.primal.openVertexComponent ω x).Finite) := by
  obtain ⟨C, hCcut, heC, hC, hCopen, _⟩ :=
    P.exists_dualOpen_circuit_boundary_openComponent hP ω x he
  refine ⟨C, hCcut, heC, hC, hCopen, S.radius_pos C hC, fun hx => ?_⟩
  apply finite_openVertexComponent_sphere R (S.crossing C hC) (S.vertex_off C hC)
    _ (hproper C hC) hx
  intro f hf
  exact P.primal.closed_of_mem_vertexCut_of_openComponentSaturated
    (P.primal.openComponentSaturated_openVertexComponent ω x) (hCcut hf)

end FiniteDualCircuit
end FK.PlaneTopology


namespace FK.PlaneTopology

open Set Metric
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular.Rotation

section RotationSphere

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Rotation-system specialization: graphic duality comes from the actual
spherical rotation system.  The independent continuous circuit geometry is
still required and is not inferred from the combinatorial Euler hypothesis. -/
theorem rotationSphere_exists_dualOpen_circuit_boundary_openComponent_finite
    {G : LabelledMultigraph} (W : RotationSphere G)
    {vertex : G.Vertex → X} (R : LabelledPathRealization G vertex)
    (S : SphericalDualCircuitGeometry (RotationSystem.dualPair W.toRotationSystem) R)
    (ω : G.Configuration) (x : G.Vertex) {e : G.Edge}
    (he : e ∈ G.vertexCut (G.openVertexComponent ω x))
    (hproper : ∀ C,
      (RotationSystem.dualPair W.toRotationSystem).faceDual.cycleMatroid.IsCircuit C →
      (vertex ⁻¹' ball (S.centre C) (S.radius C)).Finite) :
    ∃ C, C ⊆ G.vertexCut (G.openVertexComponent ω x) ∧ e ∈ C ∧
      (RotationSystem.dualPair W.toRotationSystem).faceDual.cycleMatroid.IsCircuit C ∧
      C ⊆ (RotationSystem.dualPair W.toRotationSystem).faceDual.openEdgeSet
        (dualConfig (Equiv.refl G.Edge) ω) ∧ 0 < S.radius C ∧
      (vertex x ∈ ball (S.centre C) (S.radius C) →
        (G.openVertexComponent ω x).Finite) := by
  exact exists_dualOpen_circuit_boundary_openComponent_finite_of_spherical
    (P := RotationSystem.dualPair W.toRotationSystem)
    R S W.graphicDualCertificate_of_rotationSphere ω x he hproper

end RotationSphere
end FK.PlaneTopology
