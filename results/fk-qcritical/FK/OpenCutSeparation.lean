import FK.PrimalOpenBoundary

/-!
# At most one infinite open cluster from finite open vertex cuts

The published uniqueness chain (`FK/InfiniteOpenCircuitUniqueness.lean`) proves
`GlobalAtMostOne` from a cofinal family of *metric-spherical* primal-open
circuits, using the intermediate value theorem for the distance to a centre.
This module isolates the two properties of that argument which are actually
used, and none of them mentions the ambient geometry:

* the cut `orientedCut G A` of a **finite** vertex set `A` is entirely open;
* all vertices incident to the cut are mutually open-connected.

Given such a cut through any two prescribed vertices `x`, `y`, two infinite
open clusters rooted at `x` and `y` must both leave `A` (finite), hence both
cross an open cut edge, hence both meet the cut's vertex set, hence are equal.
No planarity, no Jordan curve, no properness and no metric sphere is used.

The second half of the file proves that an actual `SphericalOpenCircuit`
supplies such a cut, so the existing spherical exhaustion theorem is recovered
as a corollary: the geometric content of the published argument is exactly the
statement "every edge leaving the finite set of vertices in the ball belongs to
one open-connected circuit".

## Main results

* `FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts`
* `FK.PlaneTopology.CutSeparation.finite_openCut_of_sphericalOpenCircuit`
* `FK.PlaneTopology.CutSeparation.globalAtMostOne_of_openCircuitExhaustion_cut`
  (the existing theorem, re-derived through the cut form)
* `FK.PlaneTopology.CutSeparation.dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction`
-/

namespace FK.PlaneTopology.CutSeparation

open Set Metric
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology

variable {V : Type*}

/-- The **oriented edge cut** of a vertex set `A`: every edge of `G` with one
endpoint in `A` and the other outside, represented from its `A`-endpoint.
This is the edge set `FK.PlaneTopology.DualExhaustion.edgeCut`, restated here
so that this module does not depend on the dual-enclosure file. -/
def orientedCut (G : SimpleGraph V) (A : Set V) : Set G.edgeSet :=
  {e | ∃ u : V, u ∈ A ∧ ∃ v : V, v ∉ A ∧ ∃ h : G.Adj u v, e = ⟨s(u, v), h⟩}

lemma mem_orientedCut_iff {G : SimpleGraph V} {A : Set V} {e : G.edgeSet} :
    e ∈ orientedCut G A ↔
      ∃ u : V, u ∈ A ∧ ∃ v : V, v ∉ A ∧ ∃ h : G.Adj u v, e = ⟨s(u, v), h⟩ :=
  Iff.rfl

/-- **Crossing lemma.**  An open walk from a vertex inside `A` to a vertex
outside `A` traverses an edge of the oriented cut, and the endpoint of that
cut edge on the `A`-side is open-connected to the walk's source by the open
prefix of the walk. -/
theorem exists_orientedCut_vertex_of_walk {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} {x z : V} (p : G.Walk x z) (hp : IsOpenIn ω Set.univ p)
    (hxA : x ∈ A) (hzA : z ∉ A) :
    ∃ u : V, VertexOnLabels (orientedCut G A) u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact (hzA hxA).elim
  | @cons a b c hab p ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      by_cases hbA : b ∈ A
      · obtain ⟨u, hu, hbu⟩ := ih hrest hbA hzA
        exact ⟨u, hu, (OpenConnected.of_adj hab (Set.mem_univ _) hopen).trans hbu⟩
      · refine ⟨a, ⟨b, hab, ?_⟩, OpenConnected.refl _ _ _⟩
        rw [mem_orientedCut_iff]
        exact ⟨a, hxA, b, hbA, hab, rfl⟩

/-- **Geometry-free uniqueness criterion, sharp form.**  It is enough that the
finite open cut with connected cut-vertices exists for every pair of vertices
that actually carries two infinite open clusters.  Then `ω` has at most one
infinite open cluster.

No planarity, embedding, properness or metric sphere enters this statement;
the two cut hypotheses are the complete combinatorial content of the
spherical open-circuit argument. -/
theorem globalAtMostOne_of_finite_openCuts_on_infinite
    {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ExteriorInfiniteCluster G ω Set.univ x →
      ExteriorInfiniteCluster G ω Set.univ y →
      ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
        (∀ e ∈ orientedCut G A, ω e = true) ∧
        (∀ u v : V, VertexOnLabels (orientedCut G A) u →
          VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v)) :
    GlobalAtMostOne G ω := by
  intro x y hx hy
  obtain ⟨A, hAfin, hxA, hyA, hopen, hconn⟩ := h x y hx hy
  have hex : ∃ z : V, OpenConnected G ω Set.univ x z ∧ z ∉ A := by
    by_contra hc
    push_neg at hc
    exact hx (hAfin.subset fun z hz => hc z hz)
  obtain ⟨z, hxz, hzA⟩ := hex
  obtain ⟨p, hp⟩ := hxz
  obtain ⟨u, hu, hxu⟩ := exists_orientedCut_vertex_of_walk p hp hxA hzA
  have hey : ∃ z : V, OpenConnected G ω Set.univ y z ∧ z ∉ A := by
    by_contra hc
    push_neg at hc
    exact hy (hAfin.subset fun z hz => hc z hz)
  obtain ⟨w, hyw, hwA⟩ := hey
  obtain ⟨q, hq⟩ := hyw
  obtain ⟨v, hv, hyv⟩ := exists_orientedCut_vertex_of_walk q hq hyA hwA
  exact hxu.trans ((hconn u v hu hv).trans (openConnected_symm hyv))

/-- Criterion with the cut hypothesis required for every pair of vertices. -/
theorem globalAtMostOne_of_finite_openCuts {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ e ∈ orientedCut G A, ω e = true) ∧
      (∀ u v : V, VertexOnLabels (orientedCut G A) u →
        VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v)) :
    GlobalAtMostOne G ω :=
  globalAtMostOne_of_finite_openCuts_on_infinite fun x y _ _ => h x y

/-- **Crossing edge lemma.**  An open walk from inside `A` to outside `A`
traverses an open edge of the oriented cut. -/
theorem exists_orientedCut_edge_of_walk {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} {x z : V} (p : G.Walk x z) (hp : IsOpenIn ω Set.univ p)
    (hxA : x ∈ A) (hzA : z ∉ A) :
    ∃ e ∈ orientedCut G A, ω e = true := by
  induction p with
  | nil => exact (hzA hxA).elim
  | @cons a b c hab ptail ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      by_cases hbA : b ∈ A
      · exact ih hrest hbA hzA
      · refine ⟨⟨s(a, b), hab⟩, ?_, hopen⟩
        rw [mem_orientedCut_iff]
        exact ⟨a, hxA, b, hbA, hab, rfl⟩

/-- **Exterior exclusion, cut form.**  If every edge leaving a finite vertex set
`A` is closed, the open cluster of any vertex of `A` is contained in `A`, hence
finite.  This is the companion of `globalAtMostOne_of_finite_openCuts`: a
finite closed cut traps finite clusters, a finite open cut with connected
cut-vertices joins all infinite ones.  Neither statement needs geometry. -/
theorem openCluster_subset_of_closed_cut {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} {x : V} (hxA : x ∈ A)
    (hclosed : ∀ e ∈ orientedCut G A, ω e = false) :
    {y : V | OpenConnected G ω Set.univ x y} ⊆ A := by
  intro y hy
  by_contra hyA
  obtain ⟨p, hp⟩ := hy
  obtain ⟨e, he, hopen⟩ := exists_orientedCut_edge_of_walk p hp hxA hyA
  exact absurd hopen (by rw [hclosed e he]; exact Bool.false_ne_true)

/-- A finite closed cut through every vertex forbids any infinite open cluster:
the classical combinatorial form of "no percolation". -/
theorem noInfiniteOpenCluster_of_forall_finite_closedCut {G : SimpleGraph V}
    {ω : G.edgeSet → Bool}
    (h : ∀ x : V, ∃ A : Set V, A.Finite ∧ x ∈ A ∧
      (∀ e ∈ orientedCut G A, ω e = false)) :
    ∀ x : V, {y : V | OpenConnected G ω Set.univ x y}.Finite := by
  intro x
  obtain ⟨A, hAfin, hxA, hclosed⟩ := h x
  exact hAfin.subset (openCluster_subset_of_closed_cut hxA hclosed)

/-- **Cut criterion via an open-connected label set.**  It suffices that some
open-connected label set `C` contains every edge of the oriented cut: all
vertices incident to the cut are then `VertexOnLabels C`, and
`OpenLabelConnected` connects them inside `C`.  This is the shape of the
conclusion produced by the finite planar boundary theorems
(`FK.Finite.LabelledMultigraph.openLabelConnected_simple_of_cycleMatroid_isCircuit`
and `FK.PlaneTopology.exists_primalOpen_circuit_boundary_dualOpenComponent`). -/
theorem globalAtMostOne_of_finite_openCuts_through_labelSet
    {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ∃ (A : Set V) (C : Set G.edgeSet), A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      orientedCut G A ⊆ C ∧ (∀ e ∈ C, ω e = true) ∧ OpenLabelConnected G ω C) :
    GlobalAtMostOne G ω := by
  apply globalAtMostOne_of_finite_openCuts
  intro x y
  obtain ⟨A, C, hAfin, hxA, hyA, hsub, hopen, hconn⟩ := h x y
  refine ⟨A, hAfin, hxA, hyA, fun e he => hopen e (hsub he), ?_⟩
  intro u v hu hv
  have hu' : VertexOnLabels C u := by
    obtain ⟨w, h, he⟩ := hu
    exact ⟨w, h, hsub he⟩
  have hv' : VertexOnLabels C v := by
    obtain ⟨w, h, he⟩ := hv
    exact ⟨w, h, hsub he⟩
  exact (hconn hu' hv').mono_edges (Set.subset_univ _)

/-! ## Spherical circuits supply finite open cuts

The next two lemmas show that the published spherical hypothesis is only used
to produce the cut hypotheses above.  The intermediate value theorem is applied
once, to the distance to the centre along an edge arc. -/

section Spherical

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- A path from inside a metric ball to a point outside the ball but off its
sphere meets the sphere.  This is the intermediate value theorem for the
distance to the centre. -/
theorem exists_mem_sphere_of_mem_ball_not_mem_ball {c : X} {r : ℝ} {x y : X}
    (γ : Path x y) (hx : x ∈ ball c r) (hy : y ∉ ball c r)
    (hy' : y ∉ sphere c r) : ∃ t, γ t ∈ sphere c r := by
  by_contra h
  push_neg at h
  have hlt : r < dist y c := by
    rcases lt_or_ge (dist y c) r with h' | h'
    · exact absurd (mem_ball.mpr h') hy
    · exact lt_of_le_of_ne h' (Ne.symm (by simpa [dist_eq_norm] using hy'))
  let f : unitInterval → ℝ := fun t => dist (γ t) c
  have hf : Continuous f := γ.continuous.dist continuous_const
  have h0 : f 0 = dist x c := by simp [f]
  have h1 : f 1 = dist y c := by simp [f]
  have hrmem : r ∈ Icc (f 0) (f 1) := by
    rw [h0, h1]
    exact ⟨hx.le, hlt.le⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hf hrmem
  have : γ t ∈ sphere c r := ht
  exact h t this

/-- Every edge leaving the finite vertex set inside a metric ball belongs to a
spherical open circuit controlling that ball. -/
theorem orientedCut_subset_of_sphericalOpenCircuit
    (R : OpenPathRealization G vertex) {ω : G.edgeSet → Bool} {C : Set G.edgeSet}
    {c : X} {r : ℝ} (S : SphericalOpenCircuit R ω C c r) :
    orientedCut G (vertex ⁻¹' ball c r) ⊆ C := by
  rintro e ⟨u, hu, v, hv, h, rfl⟩
  apply S.crossing h
  exact exists_mem_sphere_of_mem_ball_not_mem_ball (R.arc h) hu hv (S.vertex_off v)

/-- **A spherical open circuit yields a finite open cut through any two
vertices of its ball.**  The cut is the oriented cut of the finite set of
vertices lying in the ball; properness makes it finite, the crossing lemma puts
every cut edge into the circuit, and circuit-connectivity connects the cut's
vertices. -/
theorem finite_openCut_of_sphericalOpenCircuit
    (R : OpenPathRealization G vertex) {ω : G.edgeSet → Bool} {C : Set G.edgeSet}
    {c : X} {r : ℝ} (S : SphericalOpenCircuit R ω C c r)
    (hproper : (vertex ⁻¹' ball c r).Finite) {x y : V}
    (hx : vertex x ∈ ball c r) (hy : vertex y ∈ ball c r) :
    ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ e ∈ orientedCut G A, ω e = true) ∧
      (∀ u v : V, VertexOnLabels (orientedCut G A) u →
        VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v) := by
  refine ⟨vertex ⁻¹' ball c r, hproper, hx, hy, ?_, ?_⟩
  · intro e he
    exact S.label_open e (orientedCut_subset_of_sphericalOpenCircuit R S he)
  · intro u v hu hv
    have hconn := S.openConnected
      (by obtain ⟨w, h, he⟩ := hu
          exact ⟨w, h, orientedCut_subset_of_sphericalOpenCircuit R S he⟩)
      (by obtain ⟨w, h, he⟩ := hv
          exact ⟨w, h, orientedCut_subset_of_sphericalOpenCircuit R S he⟩)
    exact hconn.mono_edges (Set.subset_univ _)

/-- **The published spherical exhaustion theorem, re-derived from the
geometry-free cut criterion.**  This shows the cut form is a genuine
generalisation rather than a restatement: only the two cut properties are
consumed. -/
theorem globalAtMostOne_of_openCircuitExhaustion_cut
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (hexhaust : HasOpenCircuitExhaustion R ω c) : GlobalAtMostOne G ω := by
  apply globalAtMostOne_of_finite_openCuts
  intro x y
  obtain ⟨C, r, hr, S⟩ := hexhaust (max (dist (vertex x) c) (dist (vertex y) c))
  exact finite_openCut_of_sphericalOpenCircuit R S (hproper r)
    (lt_of_le_of_lt (le_max_left _ _) hr) (lt_of_le_of_lt (le_max_right _ _) hr)

end Spherical

/-! ## Source-facing residual

`FK.PlaneClusterTarget.DualNonpercolationForcesPrimalAtMostOne` asks that dual
nonpercolation force at most one primal infinite cluster.  The following
theorem records exactly what a geometric proof must deliver: a finite open cut
through any two prescribed vertices.  It is deliberately *not* derived from
dual nonpercolation here. -/

/-- A construction of finite open cuts through any two vertices gives the
planar cluster-count implication. -/
theorem dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction
    {F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F}
    (edge : G.edgeSet ≃ GD.edgeSet)
    (hconstruct : ∀ ω : G.edgeSet → Bool,
      FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω) →
        ∀ x y : V, ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
          (∀ e ∈ orientedCut G A, ω e = true) ∧
          (∀ u v : V, VertexOnLabels (orientedCut G A) u →
            VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v)) :
    FK.Planar.DualNonpercolationForcesPrimalAtMostOne G GD edge := by
  intro ω hdual
  exact globalAtMostOne_of_finite_openCuts (hconstruct ω hdual)

end FK.PlaneTopology.CutSeparation

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.CutSeparation.exists_orientedCut_vertex_of_walk
#print axioms FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts_on_infinite
#print axioms FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts
#print axioms FK.PlaneTopology.CutSeparation.exists_orientedCut_edge_of_walk
#print axioms FK.PlaneTopology.CutSeparation.openCluster_subset_of_closed_cut
#print axioms FK.PlaneTopology.CutSeparation.noInfiniteOpenCluster_of_forall_finite_closedCut
#print axioms FK.PlaneTopology.CutSeparation.orientedCut_subset_of_sphericalOpenCircuit
#print axioms FK.PlaneTopology.CutSeparation.finite_openCut_of_sphericalOpenCircuit
#print axioms FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts_through_labelSet
#print axioms FK.PlaneTopology.CutSeparation.globalAtMostOne_of_openCircuitExhaustion_cut
#print axioms FK.PlaneTopology.CutSeparation.dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction
