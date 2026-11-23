import FK.EmbeddedCircuitSeparation
import FK.PlaneClusterTarget

/-!
# Infinite uniqueness from enclosing open circuits

This is the open-circuit counterpart of the closed-circuit obstruction in
`EmbeddedCircuitSeparation`. If a realized open walk escapes a sphere, then
some crossing-controlled label occurs on a prefix of the walk. Consequently,
if all incident vertices of that label set belong to one open component, every
infinite open component through an inside vertex meets that component.

A cofinal family of such open spherical circuits therefore joins any two
infinite open components. The last theorem packages the remaining planar
input explicitly: dual nonpercolation must be used to construct the enclosing
primal-open circuit exhaustion. No such construction is asserted here.
-/

namespace FK.PlaneTopology

open Set Metric unitInterval
open scoped Topology
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

variable {V X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- A vertex incident to an oriented representative of a label in `C`.
Orientation is irrelevant to the associated edge, but exposing the chosen
source makes walk-prefix arguments economical. -/
def VertexOnLabels (C : Set G.edgeSet) (u : V) : Prop :=
  ∃ v : V, ∃ h : G.Adj u v, (⟨s(u, v), h⟩ : G.edgeSet) ∈ C

/-- Underlying unoriented edges of a label set. -/
def LabelCarrier (C : Set G.edgeSet) : Set (Sym2 V) := Subtype.val '' C

/-- All vertices incident to `C` are connected by open paths using only
labels of `C`, not by an arbitrary ambient open path. -/
def OpenLabelConnected (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (C : Set G.edgeSet) : Prop :=
  ∀ {u v : V}, VertexOnLabels C u → VertexOnLabels C v →
    OpenConnected G ω (LabelCarrier C) u v

namespace OpenPathRealization

variable {ω : G.edgeSet → Bool} {c : X} {r : ℝ} {C : Set G.edgeSet}

/-- Walk induction form of the open-crossing lemma. Until a controlled
crossing label is encountered, every endpoint remains inside the sphere. The
returned vertex is connected to the walk's source by the already traversed
open prefix, not merely by an arbitrary ambient path. -/
lemma mem_ball_or_exists_vertexOnLabels_of_walk
    (R : OpenPathRealization G vertex)
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    {x y : V} (p : G.Walk x y) (hp : IsOpenIn ω Set.univ p)
    (hx : vertex x ∈ ball c r) :
    vertex y ∈ ball c r ∨
      ∃ u : V, VertexOnLabels C u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact Or.inl hx
  | @cons a b y hab p ih =>
      have hparts := isOpenIn_cons.mp hp
      by_cases hc : ∃ t : I, R.arc hab t ∈ sphere c r
      · right
        refine ⟨a, ⟨b, hab, hcross hab hc⟩, ?_⟩
        exact OpenConnected.refl ω Set.univ a
      · have hjoined : JoinedIn (sphere c r)ᶜ (vertex a) (vertex b) := by
          refine ⟨R.arc hab, fun t => ?_⟩
          change R.arc hab t ∉ sphere c r
          intro ht
          exact hc ⟨t, ht⟩
        have hb : vertex b ∈ ball c r := by
          have hb' := hvertices b
          rw [compl_sphere_eq_ball_union_outside] at hb'
          rcases hb' with hb' | hb'
          · exact hb'
          · exact (not_joinedIn_compl_sphere_of_inside_outside hx hb' hjoined).elim
        rcases ih hparts.2 hb with hy | ⟨u, hu, hbu⟩
        · exact Or.inl hy
        · right
          refine ⟨u, hu, ?_⟩
          exact (OpenConnected.of_adj hab (Set.mem_univ _) hparts.1.2).trans hbu

/-- An open walk from inside to outside a sphere meets a crossing-controlled
label. Its source-side endpoint is connected to the original source by an
open prefix of the same walk. -/
theorem exists_vertexOnLabels_of_openConnected_inside_outside
    (R : OpenPathRealization G vertex)
    (hcross : R.CrossingControlledBy (sphere c r) C)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    {x y : V} (hxy : OpenConnected G ω Set.univ x y)
    (hx : vertex x ∈ ball c r)
    (hy : vertex y ∈ (fun z : X => dist z c) ⁻¹' Ioi r) :
    ∃ u : V, VertexOnLabels C u ∧ OpenConnected G ω Set.univ x u := by
  obtain ⟨p, hp⟩ := hxy
  rcases R.mem_ball_or_exists_vertexOnLabels_of_walk hcross hvertices p hp hx with hy' | h
  · change r < dist (vertex y) c at hy
    change dist (vertex y) c < r at hy'
    exact ((not_lt_of_ge hy.le) hy').elim
  · exact h

end OpenPathRealization

/-- A spherical circuit whose labels are genuinely open and whose incident
vertices are genuinely open-connected. The geometry is still explicit:
`crossing` is not inferred from planarity or matroid duality. -/
structure SphericalOpenCircuit (R : OpenPathRealization G vertex)
    (ω : G.edgeSet → Bool) (C : Set G.edgeSet) (c : X) (r : ℝ) : Prop where
  radius_pos : 0 < r
  crossing : R.CrossingControlledBy (sphere c r) C
  vertex_off : ∀ v, vertex v ∈ (sphere c r)ᶜ
  label_open : ∀ e ∈ C, ω e = true
  openConnected : OpenLabelConnected G ω C

/-- Cofinally many concentric spherical open circuits. The quantifier over
all real radii, rather than an arbitrary unbounded sequence, makes enclosure
of any prescribed finite collection of embedded points immediate. -/
def HasOpenCircuitExhaustion (R : OpenPathRealization G vertex)
    (ω : G.edgeSet → Bool) (c : X) : Prop :=
  ∀ ρ : ℝ, ∃ C : Set G.edgeSet, ∃ r : ℝ, ρ < r ∧ SphericalOpenCircuit R ω C c r

/-- Two infinite components with inside roots meet every fixed connected open
circuit. Finite properness of the vertex realization supplies an outside
vertex in each component. -/
theorem openConnected_of_two_infinite_of_sphericalOpenCircuit
    (R : OpenPathRealization G vertex) {ω : G.edgeSet → Bool}
    {C : Set G.edgeSet} {c : X} {r : ℝ}
    (S : SphericalOpenCircuit R ω C c r)
    (hproper : (vertex ⁻¹' ball c r).Finite)
    {x y : V} (hx : vertex x ∈ ball c r) (hy : vertex y ∈ ball c r)
    (hxinf : ExteriorInfiniteCluster G ω Set.univ x)
    (hyinf : ExteriorInfiniteCluster G ω Set.univ y) :
    OpenConnected G ω Set.univ x y := by
  have hxout : ∃ z, OpenConnected G ω Set.univ x z ∧ vertex z ∉ ball c r := by
    by_contra! h
    exact hxinf (hproper.subset h)
  have hyout : ∃ z, OpenConnected G ω Set.univ y z ∧ vertex z ∉ ball c r := by
    by_contra! h
    exact hyinf (hproper.subset h)
  obtain ⟨z, hxz, hz⟩ := hxout
  obtain ⟨w, hyw, hw⟩ := hyout
  have hzout : vertex z ∈ (fun q : X => dist q c) ⁻¹' Ioi r := by
    have hz' := S.vertex_off z
    rw [compl_sphere_eq_ball_union_outside] at hz'
    rcases hz' with hz' | hz'
    · exact (hz hz').elim
    · exact hz'
  have hwout : vertex w ∈ (fun q : X => dist q c) ⁻¹' Ioi r := by
    have hw' := S.vertex_off w
    rw [compl_sphere_eq_ball_union_outside] at hw'
    rcases hw' with hw' | hw'
    · exact (hw hw').elim
    · exact hw'
  obtain ⟨u, hu, hxu⟩ := R.exists_vertexOnLabels_of_openConnected_inside_outside
    S.crossing S.vertex_off hxz hx hzout
  obtain ⟨v, hv, hyv⟩ := R.exists_vertexOnLabels_of_openConnected_inside_outside
    S.crossing S.vertex_off hyw hy hwout
  have huv : OpenConnected G ω Set.univ u v :=
    (S.openConnected hu hv).mono_edges (Set.subset_univ _)
  exact hxu.trans (huv.trans (openConnected_symm hyv))

/-- **Infinite geometric uniqueness step.** A cofinal enclosing family of
connected primal-open circuits joins any two infinite primal components. -/
theorem globalAtMostOne_of_openCircuitExhaustion
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (hexhaust : HasOpenCircuitExhaustion R ω c) :
    GlobalAtMostOne G ω := by
  intro x y hxinf hyinf
  obtain ⟨C, r, hr, S⟩ := hexhaust (max (dist (vertex x) c) (dist (vertex y) c))
  apply openConnected_of_two_infinite_of_sphericalOpenCircuit R S (hproper r)
    _ _ hxinf hyinf
  · exact lt_of_le_of_lt (le_max_left _ _) hr
  · exact lt_of_le_of_lt (le_max_right _ _) hr

/-- Source-facing residual for `DualNonpercolationForcesPrimalAtMostOne`:
construct a primal-open enclosing circuit exhaustion from finite dual-open
components. This theorem proves only the subsequent uniqueness assembly; the
construction hypothesis is not disguised as a consequence of nonpercolation. -/
theorem dualNonpercolationForcesPrimalAtMostOne_of_circuitConstruction
    {F : Type*} {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
    (R : OpenPathRealization G vertex) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (hconstruct : ∀ ω : G.edgeSet → Bool,
      FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω) →
        HasOpenCircuitExhaustion R ω c) :
    FK.Planar.DualNonpercolationForcesPrimalAtMostOne G GD edge := by
  intro ω hdual
  exact globalAtMostOne_of_openCircuitExhaustion R ω c hproper (hconstruct ω hdual)

end FK.PlaneTopology
