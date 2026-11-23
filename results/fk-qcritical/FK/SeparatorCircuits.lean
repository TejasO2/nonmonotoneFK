import FK.EmbeddedCircuitSeparation
import FK.PrimalOpenBoundary
import FK.InfiniteOpenCircuitUniqueness
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Order.IntermediateValue

/-!
# Two-sided separators: level sets, convex bodies, and graph-dual cuts

`FK.EmbeddedCircuitSeparation` and `FK.InfiniteOpenCircuitUniqueness` obtain the
geometric inside/outside specification for an open primal circuit from a single
round metric sphere: the circuit's carrier is placed on `sphere c r`, every
vertex stays off it, and (in `HasOpenCircuitExhaustion`) the whole cofinal family
must be *concentric* spheres about one fixed centre `c`.  A general plane
embedding supplies no such family: the boundary of a face of a rectangular grid,
for example, is not a round circle.

This module isolates the actual Jordan-type content in a two-sided separation
datum `TwoSidedSeparation` (a barrier `K`, an inside and an outside, and the
statement that no path in `Kᶜ` joins them), and proves:

* every level set of a continuous real-valued function is such a barrier (the
  abstract form of the intermediate-value separation already used for spheres);
* every **convex body** is such a barrier: the frontier of an arbitrary convex
  set that is a neighbourhood of the origin separates its interior from its
  exterior.  This is genuine non-round geometry, supplied by the Minkowski
  functional (`gauge`);
* the spherical open-circuit chain of `FK.InfiniteOpenCircuitUniqueness` is
  *unchanged* by replacing spheres with separators, so every spherical result is
  an instance;
* a cofinal exhaustion can be produced from **one** fixed convex shape by
  scaling, instead of from concentric spheres about a fixed centre;
* on the labelled side, an arbitrary separator-controlled dual circuit still
  gives finiteness of a primal open component whose root lies inside it, which is
  the cut/circuit step used for graphic-dual certificates.

Nothing here asserts a continuous plane embedding of an arbitrary planar graph;
the residual geometric input is stated exactly as the crossing-control and
vertex-avoidance fields of `SeparatorCircuitGeometry`.
-/

namespace FK.PlaneTopology

set_option linter.unusedSectionVars false

open Set Metric unitInterval
open scoped Topology Pointwise

/-! ## Level-set separation

The intermediate-value argument used for metric spheres only needs that the
sphere is the zero set of a continuous function taking opposite signs at the two
endpoints.  This is the general statement; no Jordan curve theorem is used or
needed. -/

variable {X : Type*} [TopologicalSpace X]

/-- **A level set separates.**  If a continuous real-valued function equals `a`
on the set `f ⁻¹' {a}`, then no path can join a point where `f < a` to a point
where `a < f` while avoiding that level set. -/
theorem not_joinedIn_compl_levelSet_of_lt {f : X → ℝ} (hf : Continuous f) {a : ℝ}
    {x y : X} (hx : f x < a) (hy : a < f y) :
    ¬ JoinedIn (f ⁻¹' {a})ᶜ x y := by
  intro h
  have hcont : Continuous fun t : I => f (h.somePath t) := hf.comp h.somePath.continuous
  have h0 : f (h.somePath 0) = f x := by rw [h.somePath.source]
  have h1 : f (h.somePath 1) = f y := by rw [h.somePath.target]
  have hmem : a ∈ Icc (f (h.somePath 0)) (f (h.somePath 1)) := by
    rw [h0, h1]
    exact ⟨hx.le, hy.le⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (0 : I) (1 : I) hcont hmem
  have hout := h.somePath_mem t
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff] at hout
  exact hout ht

/-- The complement of a frontier is the union of the interior and the exterior. -/
theorem compl_frontier_eq_interior_union_compl_closure (s : Set X) :
    (frontier s)ᶜ = interior s ∪ (closure s)ᶜ := by
  rw [compl_frontier_eq_union_interior, interior_compl]

/-! ## Two-sided separation data

This is the exact Jordan-type input the open-circuit argument consumes.  For a
metric sphere it is *proved* below; for the frontier of a convex body it is
proved from the Minkowski functional. -/

/-- A barrier `K` together with an inside and an outside region that no path
avoiding `K` can join. -/
structure TwoSidedSeparation (X : Type*) [TopologicalSpace X] where
  /-- The separating locus. -/
  K : Set X
  /-- The inside region. -/
  inside : Set X
  /-- The outside region. -/
  outside : Set X
  /-- Every point off the barrier is inside or outside. -/
  cover : Kᶜ ⊆ inside ∪ outside
  /-- No path off the barrier joins the inside to the outside. -/
  separated : ∀ ⦃x y : X⦄, x ∈ inside → y ∈ outside → ¬ JoinedIn Kᶜ x y

namespace TwoSidedSeparation

/-- Inside and outside are disjoint, since the barrier-avoiding constant path at
a common point would join them. -/
theorem disjoint (S : TwoSidedSeparation X) (hK : ∀ x ∈ S.inside, x ∈ S.Kᶜ) :
    Disjoint S.inside S.outside := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact S.separated hx hx' (JoinedIn.refl (hK x hx))

end TwoSidedSeparation


/-! ### Separators are exactly unions of path components

The two-sided separation datum has no genuine extra structure: an inside region
is admissible precisely when it is a union of path components of the complement
of the barrier.  This is the abstract Jordan-type principle behind both the
metric-sphere and the convex-body instances, and it is the exact check a
continuous plane embedding has to perform to produce a separator. -/

/-- **Admissible insides are unions of path components.**  A set closed under
path components of the complement of the barrier defines a two-sided separation
whose outside is the remaining complement. -/
def twoSidedSeparationOfPathComponents (K : Set X) (inside : Set X)
    (hcomp : ∀ x ∈ inside, pathComponentIn Kᶜ x ⊆ inside) : TwoSidedSeparation X where
  K := K
  inside := inside
  outside := Kᶜ \ inside
  cover := by
    intro z hz
    by_cases h : z ∈ inside
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  separated := by
    intro x y hx hy hjoin
    exact hy.2 (hcomp x hx hjoin)

/-- **Conversely**, the inside region of any two-sided separation is a union of
path components of the complement of its barrier: every point path-joined to an
inside point avoiding the barrier is again inside. -/
theorem pathComponentIn_subset_inside_of_mem (S : TwoSidedSeparation X)
    {x : X} (hx : x ∈ S.inside) :
    pathComponentIn S.Kᶜ x ⊆ S.inside := by
  intro y hy
  by_contra hout
  exact S.separated hx (S.cover (pathComponentIn_subset hy) |>.resolve_left hout) hy

section ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Frontier separation for convex bodies.**  A path from an interior point to
a point outside the closure must cross the frontier. -/
theorem not_joinedIn_compl_convexFrontier_of_interior_notMem_closure {s : Set E}
    (hconv : Convex ℝ s) (hnhds : s ∈ 𝓝 (0 : E)) {x y : E}
    (hx : x ∈ interior s) (hy : y ∉ closure s) :
    ¬ JoinedIn (frontier s)ᶜ x y := by
  have hcont : Continuous (gauge s) := continuous_gauge hconv hnhds
  have hlt : gauge s x < 1 := (gauge_lt_one_iff_mem_interior hconv hnhds).2 hx
  have hgt : 1 < gauge s y := by
    have hnot : ¬ gauge s y ≤ 1 := fun hle =>
      hy ((gauge_le_one_iff_mem_closure hconv hnhds).1 hle)
    exact lt_of_not_ge hnot
  have hset : gauge s ⁻¹' ({1} : Set ℝ) = frontier s := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    exact gauge_eq_one_iff_mem_frontier hconv hnhds
  rw [← hset]
  exact not_joinedIn_compl_levelSet_of_lt hcont hlt hgt


/-- **Inner segments are automatically safe.**  The segment between two interior
points of a convex body stays in the interior, hence avoids the frontier.  This
is the elementary step that discharges `crossing` for every edge of a
straight-line drawing whose endpoints both lie inside the body; only the edges
crossing the frontier have to be listed in the circuit. -/
theorem convex_segment_subset_interior {s : Set E} (hconv : Convex ℝ s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ interior s) : segment ℝ x y ⊆ interior s := by
  rw [segment_eq_image_lineMap]
  rintro p ⟨t, ht, rfl⟩
  rw [AffineMap.lineMap_apply_module]
  rcases eq_or_lt_of_le ht.1 with h0 | ht0
  · rw [← h0]
    simpa using hx
  · rcases eq_or_lt_of_le ht.2 with h1 | ht1
    · rw [h1]
      simpa using hy
    · have h1t : 0 < 1 - t := by linarith
      have hmem : (1 - t) • x + t • y ∈ (1 - t) • interior s + t • s :=
        Set.add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set (interior_subset hy))
      exact hconv.combo_interior_self_subset_interior h1t ht.1 (by ring) hmem

/-- A point of a segment between two interior points of a convex body is not on
its frontier. -/
theorem segment_notMem_convexFrontier {s : Set E} (hconv : Convex ℝ s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ interior s) {p : E} (hp : p ∈ segment ℝ x y) :
    p ∉ frontier s := by
  intro hp'
  exact Set.disjoint_left.1 (disjoint_interior_frontier (s := s))
    (convex_segment_subset_interior hconv hx hy hp) hp'

/-- The metric-sphere separation theorem as a level-set instance. -/
theorem not_joinedIn_compl_sphere_of_inside_outside_separator {c x y : E} {r : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ (fun z : E => dist z c) ⁻¹' Ioi r) :
    ¬ JoinedIn (sphere c r)ᶜ x y := by
  have hcont : Continuous fun z : E => dist z c := continuous_id.dist continuous_const
  have hset : (fun z : E => dist z c) ⁻¹' ({r} : Set ℝ) = sphere c r := rfl
  rw [← hset]
  exact not_joinedIn_compl_levelSet_of_lt hcont hx hy

/-- The two-sided separation carried by a metric sphere. -/
def sphericalSeparation (c : E) (r : ℝ) : TwoSidedSeparation E where
  K := sphere c r
  inside := ball c r
  outside := (fun z : E => dist z c) ⁻¹' Ioi r
  cover := fun _ hz => compl_sphere_eq_ball_union_outside c r ▸ hz
  separated := by
    intro x y hx hy
    exact not_joinedIn_compl_sphere_of_inside_outside_separator hx hy

/-- The two-sided separation carried by the frontier of a convex body that is a
neighbourhood of the origin.  `inside` is the interior and `outside` the
complement of the closure. -/
def convexSeparation {s : Set E} (hconv : Convex ℝ s) (hnhds : s ∈ 𝓝 (0 : E)) :
    TwoSidedSeparation E where
  K := frontier s
  inside := interior s
  outside := (closure s)ᶜ
  cover := fun _ hz => (compl_frontier_eq_interior_union_compl_closure s).le hz
  separated := by
    intro x y hx hy
    exact not_joinedIn_compl_convexFrontier_of_interior_notMem_closure hconv hnhds hx hy

end ConvexBody


end FK.PlaneTopology


namespace FK.PlaneTopology

open Set Metric unitInterval
open scoped Topology Pointwise
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

/-! ## Separator open circuits on a simple graph

This section is the exact separator analogue of the spherical development in
`FK.InfiniteOpenCircuitUniqueness`.  The geometry enters only through a
`TwoSidedSeparation` and the crossing-control field; the proofs are those of the
spherical case with the sphere replaced by an arbitrary barrier. -/

section SimpleGraphTop

variable {V X : Type*} [TopologicalSpace X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- A primal circuit carrier placed on a two-sided separator: every vertex is off
the barrier, the only arcs meeting the barrier carry labels of `C`, those labels
are open, and their incident vertices are open-connected using only them. -/
structure SeparatorOpenCircuit (R : OpenPathRealization G vertex)
    (ω : G.edgeSet → Bool) (C : Set G.edgeSet) (S : TwoSidedSeparation X) : Prop where
  /-- All embedded vertices avoid the barrier. -/
  vertex_off : ∀ v, vertex v ∈ S.Kᶜ
  /-- An arc meeting the barrier carries a label of `C`. -/
  crossing : R.CrossingControlledBy S.K C
  /-- The circuit labels are open. -/
  label_open : ∀ e ∈ C, ω e = true
  /-- The vertices incident to `C` are open-connected through `C` alone. -/
  openConnected : OpenLabelConnected G ω C

variable {ω : G.edgeSet → Bool} {C : Set G.edgeSet} {S : TwoSidedSeparation X}

/-- Walk induction: until an open walk leaves the inside of a separator, either it
stays inside or it meets a vertex incident to `C`. -/
lemma mem_inside_or_exists_vertexOnLabels_of_walk
    (R : OpenPathRealization G vertex)
    (hcross : R.CrossingControlledBy S.K C)
    (hcover : S.Kᶜ ⊆ S.inside ∪ S.outside)
    (hsep : ∀ ⦃x y : X⦄, x ∈ S.inside → y ∈ S.outside → ¬ JoinedIn S.Kᶜ x y)
    {x y : V} (p : G.Walk x y) (hp : IsOpenIn ω Set.univ p)
    (hx : vertex x ∈ S.inside) :
    vertex y ∈ S.inside ∨
      ∃ u : V, VertexOnLabels C u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact Or.inl hx
  | @cons a b y hab p ih =>
      have hparts := isOpenIn_cons.mp hp
      by_cases hc : ∃ t : I, R.arc hab t ∈ S.K
      · right
        exact ⟨a, ⟨b, hab, hcross hab hc⟩, OpenConnected.refl ω Set.univ a⟩
      · have hjoined : JoinedIn S.Kᶜ (vertex a) (vertex b) := by
          refine ⟨R.arc hab, fun t => ?_⟩
          change R.arc hab t ∉ S.K
          intro ht
          exact hc ⟨t, ht⟩
        have hb : vertex b ∈ S.inside := by
          rcases hcover hjoined.target_mem with h | h
          · exact h
          · exact absurd hjoined (hsep hx h)
        rcases ih hparts.2 hb with hy | ⟨u, hu, hbu⟩
        · exact Or.inl hy
        · exact Or.inr ⟨u, hu,
            (OpenConnected.of_adj hab (Set.mem_univ _) hparts.1.2).trans hbu⟩

/-- An open walk that leaves the inside of a separator must pass through a vertex
incident to the circuit's labels, and that vertex is reached by an open prefix of
the same walk. -/
theorem exists_vertexOnLabels_of_openConnected_inside_outside
    (R : OpenPathRealization G vertex)
    (hcross : R.CrossingControlledBy S.K C)
    (hcover : S.Kᶜ ⊆ S.inside ∪ S.outside)
    (hsep : ∀ ⦃x y : X⦄, x ∈ S.inside → y ∈ S.outside → ¬ JoinedIn S.Kᶜ x y)
    (hvertices : ∀ v, vertex v ∈ S.Kᶜ)
    {x y : V} (hxy : OpenConnected G ω Set.univ x y)
    (hx : vertex x ∈ S.inside) (hy : vertex y ∈ S.outside) :
    ∃ u : V, VertexOnLabels C u ∧ OpenConnected G ω Set.univ x u := by
  obtain ⟨p, hp⟩ := hxy
  rcases mem_inside_or_exists_vertexOnLabels_of_walk R hcross hcover hsep p hp hx
    with hin | h
  · exact (hsep hin hy (JoinedIn.refl (hvertices y))).elim
  · exact h


/-- Walk induction for a **closed** circuit label set: an open walk that starts
inside a separator never leaves it.  This is the separator form of
`mem_ball_of_openConnected_sphere`. -/
lemma mem_inside_of_walk_of_closed
    (R : OpenPathRealization G vertex)
    (hcross : R.CrossingControlledBy S.K C)
    (hclosed : ∀ e ∈ C, ω e = false)
    (hcover : S.Kᶜ ⊆ S.inside ∪ S.outside)
    (hsep : ∀ ⦃x y : X⦄, x ∈ S.inside → y ∈ S.outside → ¬ JoinedIn S.Kᶜ x y)
    {x y : V} (p : G.Walk x y) (hp : IsOpenIn ω Set.univ p)
    (hx : vertex x ∈ S.inside) : vertex y ∈ S.inside := by
  induction p with
  | nil => exact hx
  | @cons a b y hab p ih =>
      have hparts := isOpenIn_cons.mp hp
      have hjoined := R.joinedIn_compl_adj hcross hclosed hab hparts.1.2
      have hb : vertex b ∈ S.inside := by
        rcases hcover hjoined.target_mem with h | h
        · exact h
        · exact absurd hjoined (hsep hx h)
      exact ih hparts.2 hb

/-- A whole open connection stays inside a separator when its crossing labels are
closed. -/
theorem mem_inside_of_openConnected_of_closed
    (R : OpenPathRealization G vertex)
    (hcross : R.CrossingControlledBy S.K C)
    (hclosed : ∀ e ∈ C, ω e = false)
    (hcover : S.Kᶜ ⊆ S.inside ∪ S.outside)
    (hsep : ∀ ⦃x y : X⦄, x ∈ S.inside → y ∈ S.outside → ¬ JoinedIn S.Kᶜ x y)
    {x y : V} (hx : vertex x ∈ S.inside) (hxy : OpenConnected G ω Set.univ x y) :
    vertex y ∈ S.inside := by
  obtain ⟨p, hp⟩ := hxy
  exact mem_inside_of_walk_of_closed R hcross hclosed hcover hsep p hp hx

end SimpleGraphTop

section SimpleGraphNormed

variable {V X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : SimpleGraph V} {vertex : V → X}
variable {ω : G.edgeSet → Bool} {C : Set G.edgeSet} {S : TwoSidedSeparation X}

omit [NormedSpace ℝ X] in
/-- Two infinite open components meeting the inside of a separator are connected
through the circuit carrier, provided only finitely many vertices lie inside. -/
theorem openConnected_of_two_infinite_of_separatorOpenCircuit
    (R : OpenPathRealization G vertex) {ω : G.edgeSet → Bool}
    {C : Set G.edgeSet} {S : TwoSidedSeparation X}
    (hcirc : SeparatorOpenCircuit R ω C S)
    (hfinite : (vertex ⁻¹' S.inside).Finite)
    {x y : V} (hx : vertex x ∈ S.inside) (hy : vertex y ∈ S.inside)
    (hxinf : ExteriorInfiniteCluster G ω Set.univ x)
    (hyinf : ExteriorInfiniteCluster G ω Set.univ y) :
    OpenConnected G ω Set.univ x y := by
  have hxout : ∃ z, OpenConnected G ω Set.univ x z ∧ vertex z ∉ S.inside := by
    by_contra! h
    exact hxinf (hfinite.subset h)
  have hyout : ∃ z, OpenConnected G ω Set.univ y z ∧ vertex z ∉ S.inside := by
    by_contra! h
    exact hyinf (hfinite.subset h)
  obtain ⟨z, hxz, hz⟩ := hxout
  obtain ⟨w, hyw, hw⟩ := hyout
  have hzout : vertex z ∈ S.outside := by
    rcases S.cover (hcirc.vertex_off z) with h | h
    · exact (hz h).elim
    · exact h
  have hwout : vertex w ∈ S.outside := by
    rcases S.cover (hcirc.vertex_off w) with h | h
    · exact (hw h).elim
    · exact h
  obtain ⟨u, hu, hxu⟩ := exists_vertexOnLabels_of_openConnected_inside_outside R
    hcirc.crossing S.cover S.separated hcirc.vertex_off hxz hx hzout
  obtain ⟨v, hv, hyv⟩ := exists_vertexOnLabels_of_openConnected_inside_outside R
    hcirc.crossing S.cover S.separated hcirc.vertex_off hyw hy hwout
  have huv : OpenConnected G ω Set.univ u v :=
    (hcirc.openConnected hu hv).mono_edges (Set.subset_univ _)
  exact hxu.trans (huv.trans (openConnected_symm hyv))

/-- Cofinal separator circuits: for every radius there is a circuit whose inside
contains the whole ball and carries only finitely many vertices. -/
def HasSeparatorCircuitExhaustion (R : OpenPathRealization G vertex)
    (ω : G.edgeSet → Bool) (c : X) : Prop :=
  ∀ ρ : ℝ, ∃ (C : Set G.edgeSet) (S : TwoSidedSeparation X),
    ball c ρ ⊆ S.inside ∧ (vertex ⁻¹' S.inside).Finite ∧
      SeparatorOpenCircuit R ω C S

omit [NormedSpace ℝ X] in
/-- **Infinite geometric uniqueness step for arbitrary separators.**  A cofinal
family of connected open circuits carried by two-sided separators joins any two
infinite open components. -/
theorem globalAtMostOne_of_separatorCircuitExhaustion
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hexhaust : HasSeparatorCircuitExhaustion R ω c) :
    GlobalAtMostOne G ω := by
  intro x y hxinf hyinf
  obtain ⟨C, S, hball, hfinite, hcirc⟩ :=
    hexhaust (max (dist (vertex x) c) (dist (vertex y) c) + 1)
  refine openConnected_of_two_infinite_of_separatorOpenCircuit R hcirc hfinite ?_ ?_
    hxinf hyinf
  · exact hball (by
      rw [mem_ball]
      exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _))
  · exact hball (by
      rw [mem_ball]
      exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _))

/-! ### Conservativity: spheres are separators -/

/-- A spherical open circuit is a separator open circuit for the sphere's own
two-sided separation. -/
theorem separatorOpenCircuit_of_sphericalOpenCircuit {c : X} {r : ℝ}
    (h : SphericalOpenCircuit R ω C c r) :
    SeparatorOpenCircuit R ω C (sphericalSeparation c r) :=
  { vertex_off := h.vertex_off
    crossing := h.crossing
    label_open := h.label_open
    openConnected := h.openConnected }

/-- A concentric spherical exhaustion is a separator exhaustion. -/
theorem hasSeparatorCircuitExhaustion_of_hasOpenCircuitExhaustion
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (h : HasOpenCircuitExhaustion R ω c) : HasSeparatorCircuitExhaustion R ω c := by
  intro ρ
  obtain ⟨C, r, hr, hS⟩ := h ρ
  exact ⟨C, sphericalSeparation c r, fun z hz => ball_subset_ball hr.le hz, hproper r,
    separatorOpenCircuit_of_sphericalOpenCircuit hS⟩

/-- The published spherical uniqueness theorem, recovered as the special case of
the separator theorem.  This checks that the generalization is conservative. -/
theorem globalAtMostOne_of_openCircuitExhaustion_via_separator
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (hexhaust : HasOpenCircuitExhaustion R ω c) :
    GlobalAtMostOne G ω :=
  globalAtMostOne_of_separatorCircuitExhaustion R ω c
    (hasSeparatorCircuitExhaustion_of_hasOpenCircuitExhaustion R ω c hproper hexhaust)

end SimpleGraphNormed

/-! ### Cofinality from one fixed convex shape

The spherical exhaustion demands concentric spheres about a fixed centre.  For
the frontier of a fixed convex body, scaling alone makes the inside regions
cofinal, so a single crossing-control family has to be produced once and then
transported along the scaling. -/

section ConvexExhaustion

variable {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : SimpleGraph W} {vertex : W → E}

/-- A positive rescaling of a neighbourhood of the origin is again one. -/
theorem smul_mem_nhds_zero_of_mem_nhds {s : Set E} (hnhds : s ∈ 𝓝 (0 : E)) {t : ℝ}
    (ht : 0 < t) : t • s ∈ 𝓝 (0 : E) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.1 hnhds
  have hsm : t • ball (0 : E) ε = ball (0 : E) (t * ε) := by
    rw [smul_ball (ne_of_gt ht) (0 : E) ε]
    simp [Real.norm_of_nonneg ht.le]
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (mul_pos ht hεpos)) ?_
  rw [← hsm]
  exact Set.smul_set_mono hε

/-- Scaling a fixed convex neighbourhood of the origin makes its interior contain
any prescribed ball about the origin.  This is what replaces the concentric
family `ball c r` of the spherical interface. -/
theorem exists_smul_ball_subset_interior {s : Set E} (hnhds : s ∈ 𝓝 (0 : E)) (ρ : ℝ) :
    ∃ t : ℝ, 0 < t ∧ ball (0 : E) ρ ⊆ interior (t • s) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨max (ρ / ε) 0 + 1, by positivity, fun z hz => ?_⟩
  have ht : 0 < max (ρ / ε) 0 + 1 := by positivity
  have hte : ρ < (max (ρ / ε) 0 + 1) * ε := by
    have hlt : ρ / ε < max (ρ / ε) 0 + 1 := by
      have hle : ρ / ε ≤ max (ρ / ε) 0 := le_max_left _ _
      linarith
    have hmul := mul_lt_mul_of_pos_right hlt hεpos
    rwa [div_mul_cancel₀ ρ hεpos.ne'] at hmul
  have hzn : ‖z‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hz
  have hsm : (max (ρ / ε) 0 + 1) • ball (0 : E) ε =
      ball (0 : E) ((max (ρ / ε) 0 + 1) * ε) := by
    rw [smul_ball (ne_of_gt ht) (0 : E) ε]
    simp [Real.norm_of_nonneg ht.le]
  have hsub : ball (0 : E) ((max (ρ / ε) 0 + 1) * ε) ⊆ (max (ρ / ε) 0 + 1) • s := by
    rw [← hsm]
    exact Set.smul_set_mono hε
  exact interior_maximal hsub Metric.isOpen_ball (by
    rw [mem_ball, dist_eq_norm]
    simpa using lt_trans hzn hte)

/-- **Cofinal exhausted circuits from one convex shape.**  If every positive
rescaling of a fixed convex neighbourhood of the origin carries an
`SeparatorOpenCircuit` on its frontier, then the scaled family is a genuine
cofinal separator exhaustion.  No concentric spheres and no single centre are
required. -/
theorem hasSeparatorCircuitExhaustion_of_scaled_convexBody
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool)
    {s : Set E} (hconv : Convex ℝ s) (hnhds : s ∈ 𝓝 (0 : E))
    (hcirc : ∀ (t : ℝ) (ht : 0 < t), ∃ C : Set G.edgeSet,
      SeparatorOpenCircuit R ω C
        (convexSeparation (hconv.smul t) (smul_mem_nhds_zero_of_mem_nhds hnhds ht)))
    (hfinite : ∀ (t : ℝ) (ht : 0 < t),
      (vertex ⁻¹' (convexSeparation (hconv.smul t)
        (smul_mem_nhds_zero_of_mem_nhds hnhds ht)).inside).Finite) :
    HasSeparatorCircuitExhaustion R ω (0 : E) := by
  intro ρ
  obtain ⟨t, ht, hball⟩ := exists_smul_ball_subset_interior hnhds ρ
  obtain ⟨C, hC⟩ := hcirc t ht
  exact ⟨C, convexSeparation (hconv.smul t)
      (smul_mem_nhds_zero_of_mem_nhds hnhds ht), hball, hfinite t ht, hC⟩

/-- The uniqueness conclusion of the separator chain, specialised to a scaled
convex-body family. -/
theorem globalAtMostOne_of_scaled_convexBody
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool)
    {s : Set E} (hconv : Convex ℝ s) (hnhds : s ∈ 𝓝 (0 : E))
    (hcirc : ∀ (t : ℝ) (ht : 0 < t), ∃ C : Set G.edgeSet,
      SeparatorOpenCircuit R ω C
        (convexSeparation (hconv.smul t) (smul_mem_nhds_zero_of_mem_nhds hnhds ht)))
    (hfinite : ∀ (t : ℝ) (ht : 0 < t),
      (vertex ⁻¹' (convexSeparation (hconv.smul t)
        (smul_mem_nhds_zero_of_mem_nhds hnhds ht)).inside).Finite) :
    GlobalAtMostOne G ω :=
  globalAtMostOne_of_separatorCircuitExhaustion R ω 0
    (hasSeparatorCircuitExhaustion_of_scaled_convexBody R ω hconv hnhds hcirc hfinite)

end ConvexExhaustion

/-! ### The separator class is strictly larger than the spherical one

A half-space is a two-sided separator: the level set of the continuous linear
functional `Complex.re` at `1`.  It is not a metric sphere, since spheres are
bounded and the vertical line at real part `1` is not.  So `TwoSidedSeparation`
covers cuts that no round sphere can express. -/

section HalfSpace

/-- The vertical line at real part `1`, as a two-sided separator: `inside` is the
open half-plane to its left and `outside` the open half-plane to its right. -/
def halfSpaceSeparation : TwoSidedSeparation ℂ where
  K := {z : ℂ | z.re = 1}
  inside := {z : ℂ | z.re < 1}
  outside := {z : ℂ | 1 < z.re}
  cover := by
    intro z hz
    simp only [mem_compl_iff, mem_ofPred_eq] at hz
    simp only [mem_union, mem_ofPred_eq]
    exact lt_or_gt_of_ne hz
  separated := by
    intro x y hx hy
    exact not_joinedIn_compl_levelSet_of_lt Complex.continuous_re hx hy

/-- **Strictness.**  No metric sphere in `ℂ` is the half-space barrier, so the
separator interface strictly contains the spherical interface used by
`SphericalOpenCircuit`. -/
theorem halfSpaceSeparation_not_sphere (c : ℂ) (r : ℝ) :
    sphere c r ≠ halfSpaceSeparation.K := by
  intro h
  have hbdd : Bornology.IsBounded (halfSpaceSeparation.K : Set ℂ) :=
    h ▸ Metric.isBounded_sphere
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hbdd
  have hK1 : (1 : ℂ) ∈ halfSpaceSeparation.K := by simp [halfSpaceSeparation]
  have hRge : 1 ≤ R := by
    have := hR hK1
    simpa using this
  have hmem : ((1 : ℝ) + ((R + 1 : ℝ) : ℂ) * Complex.I : ℂ) ∈ halfSpaceSeparation.K := by
    simp [halfSpaceSeparation]
  have hdist := hR hmem
  simp only [mem_closedBall, dist_eq_norm, sub_zero] at hdist
  have habs := Complex.abs_im_le_norm ((1 : ℝ) + ((R + 1 : ℝ) : ℂ) * Complex.I : ℂ)
  have him : (((1 : ℝ) + ((R + 1 : ℝ) : ℂ) * Complex.I : ℂ)).im = R + 1 := by simp
  rw [him, abs_of_nonneg (by linarith)] at habs
  linarith

end HalfSpace

/-! ### Separator geometry for dual circuits of a graphic-dual pair

The spherical version `SphericalDualCircuitGeometry` places each dual circuit on
a metric sphere about a centre that is itself indexed by the circuit.  The
separator version below keeps the same three geometric obligations — the
vertices avoid the barrier, only circuit arcs meet it, and only finitely many
vertices lie inside — but for an arbitrary barrier. -/

section LabelledDual

open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid

variable {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Geometric data for dual circuits of a labelled dual pair, expressed with
two-sided separators. -/
structure SeparatorDualCircuitGeometry (P : LabelledDualPair)
    {vertex : P.Vertex → E} (R : LabelledPathRealization P.primal vertex) where
  /-- The separator attached to each set of labels. -/
  sep : Set P.Edge → TwoSidedSeparation E
  /-- Every embedded vertex avoids the barrier of a dual circuit. -/
  vertex_off : ∀ C, P.faceDual.cycleMatroid.IsCircuit C → ∀ v, vertex v ∈ (sep C).Kᶜ
  /-- An arc meeting the barrier carries a label of that dual circuit. -/
  crossing : ∀ C, P.faceDual.cycleMatroid.IsCircuit C →
    R.CrossingControlledBy (sep C).K C
  /-- Only finitely many vertices lie inside a dual circuit's barrier. -/
  finite_inside : ∀ C, P.faceDual.cycleMatroid.IsCircuit C →
    (vertex ⁻¹' (sep C).inside).Finite

omit [NormedSpace ℝ E] in
/-- The spherical dual-circuit geometry is a separator dual-circuit geometry for
the spheres it supplies, once the (independent) vertex properness of those
spheres is supplied.  This checks that the labelled port is conservative. -/
def separatorDualCircuitGeometry_of_sphericalDualCircuitGeometry
    {P : LabelledDualPair} {vertex : P.Vertex → E}
    {R : LabelledPathRealization P.primal vertex}
    (S : SphericalDualCircuitGeometry P R)
    (hproper : ∀ C, P.faceDual.cycleMatroid.IsCircuit C →
      (vertex ⁻¹' ball (S.centre C) (S.radius C)).Finite) :
    SeparatorDualCircuitGeometry P R where
  sep C := sphericalSeparation (S.centre C) (S.radius C)
  vertex_off C hC := S.vertex_off C hC
  crossing C hC := S.crossing C hC
  finite_inside C hC := hproper C hC

omit [NormedSpace ℝ E] in
/-- A primal open component whose boundary labels are closed and crossing
controlled by a separator is finite as soon as its root vertex lies inside. -/
theorem openVertexComponent_finite_of_separator
    {P : LabelledDualPair} {vertex : P.Vertex → E}
    (R : LabelledPathRealization P.primal vertex) (S : TwoSidedSeparation E)
    {C : Set P.Edge} {ω : P.primal.Configuration}
    (hcross : R.CrossingControlledBy S.K C)
    (hclosed : ∀ e ∈ C, ω e = false)
    (hfinite : (vertex ⁻¹' S.inside).Finite)
    {x : P.Vertex} (hx : vertex x ∈ S.inside) :
    (P.primal.openVertexComponent ω x).Finite := by
  have hstep : ∀ {a b : P.Vertex}, vertex a ∈ S.inside →
      (P.primal.connectionGraph P.primal.freeBoundary ω).Adj a b →
      vertex b ∈ S.inside := by
    intro a b ha hab
    have hjoin := R.joinedIn_compl_adj (K := S.K) (C := C) (ω := ω) hcross hclosed hab
    rcases S.cover hjoin.target_mem with h | h
    · exact h
    · exact absurd hjoin (S.separated ha h)
  have hreach : ∀ {b : P.Vertex},
      (P.primal.connectionGraph P.primal.freeBoundary ω).Reachable x b →
      vertex b ∈ S.inside := by
    intro b hb
    obtain ⟨p⟩ := hb
    induction p with
    | nil => exact hx
    | @cons a b c hab p ih => exact ih (hstep ‹vertex a ∈ S.inside› hab)
  refine hfinite.subset ?_
  intro y hy
  exact hreach hy

omit [NormedSpace ℝ E] in
/-- **Separator-controlled dual boundary.**  Every boundary label of an actual
primal open component lies on a dual-open circuit whose separator barrier
encloses the component's root.  If the root is inside the barrier and its inside
carries finitely many vertices, the component is finite. -/
theorem exists_dualOpen_circuit_boundary_openComponent_finite_of_separator
    {P : LabelledDualPair} {vertex : P.Vertex → E}
    (R : LabelledPathRealization P.primal vertex)
    (S : SeparatorDualCircuitGeometry P R)
    (hP : P.GraphicDualCertificate) (ω : P.primal.Configuration) (x : P.Vertex)
    {e : P.Edge} (he : e ∈ P.primal.vertexCut (P.primal.openVertexComponent ω x)) :
    ∃ C, C ⊆ P.primal.vertexCut (P.primal.openVertexComponent ω x) ∧
      e ∈ C ∧ P.faceDual.cycleMatroid.IsCircuit C ∧
      C ⊆ P.faceDual.openEdgeSet (dualConfig (Equiv.refl P.Edge) ω) ∧
      (vertex x ∈ (S.sep C).inside → (P.primal.openVertexComponent ω x).Finite) := by
  obtain ⟨C, hCcut, heC, hC, hCopen, _⟩ :=
    P.exists_dualOpen_circuit_boundary_openComponent hP ω x he
  refine ⟨C, hCcut, heC, hC, hCopen, fun hx => ?_⟩
  exact openVertexComponent_finite_of_separator R (S.sep C) (S.crossing C hC)
    (fun f hf =>
      P.primal.closed_of_mem_vertexCut_of_openComponentSaturated
        (P.primal.openComponentSaturated_openVertexComponent ω x) (hCcut hf))
    (S.finite_inside C hC) hx


/-! ### Cofinal dual boundaries with separator control

`FK.PrimalOpenBoundary` converts primal circuits contained in the boundary of a
finite dual-open component into `SphericalOpenCircuit`s, but its cofinality
hypothesis forces every circuit to be a sphere about one common centre
(`c = S.centre C`).  The separator version below replaces that by the honest
condition that the barrier's inside contains the ball of radius `ρ` about `c`. -/

section LabelledPrimal

open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid

variable {W E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Separator geometry for primal circuit labels on the simple graph underlying a
labelled multigraph.  This is the separator replacement for
`SphericalPrimalCircuitGeometry`. -/
structure SeparatorPrimalCircuitGeometry (P : LabelledDualPair)
    (hloop : ∀ e, P.primal.source e ≠ P.primal.target e)
    {vertex : P.Vertex → E} (R : OpenPathRealization P.primal.simpleGraph vertex) where
  /-- The separator attached to each set of labels. -/
  sep : Set P.Edge → TwoSidedSeparation E
  /-- Every embedded vertex avoids a primal circuit's barrier. -/
  vertex_off : ∀ C, P.primal.cycleMatroid.IsCircuit C → ∀ v, vertex v ∈ (sep C).Kᶜ
  /-- An arc meeting the barrier carries a label of that circuit. -/
  crossing : ∀ C, P.primal.cycleMatroid.IsCircuit C →
    R.CrossingControlledBy (sep C).K (P.primal.simpleLabels hloop C)
  /-- Only finitely many vertices lie inside a circuit's barrier. -/
  finite_inside : ∀ C, P.primal.cycleMatroid.IsCircuit C →
    (vertex ⁻¹' (sep C).inside).Finite

omit [NormedSpace ℝ E] in
/-- A primal circuit contained in the boundary of a finite dual-open component is
a separator open circuit, with open and open-connected carrier. -/
theorem separatorOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → E} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SeparatorPrimalCircuitGeometry P hloop R)
    (ω : P.primal.Configuration) (x : P.Face) {C : Set P.Edge}
    (hCcut : C ⊆ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x))
    (hC : P.primal.cycleMatroid.IsCircuit C) :
    SeparatorOpenCircuit R (P.primal.simpleConfig hloop ω)
      (P.primal.simpleLabels hloop C) (S.sep C) := by
  have hCopen : C ⊆ P.primal.openEdgeSet ω := by
    intro f hf
    have hd := P.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
      (P.faceDual.openComponentSaturated_openVertexComponent
        (dualConfig (Equiv.refl P.Edge) ω) x) (hCcut hf)
    change (dualConfig (Equiv.refl P.Edge) ω f) = false at hd
    change (!ω f) = false at hd
    change ω f = true
    cases h : ω f <;> simp [h] at hd ⊢
  exact
    { vertex_off := S.vertex_off C hC
      crossing := S.crossing C hC
      label_open := by
        intro ε hε
        obtain ⟨e, heC, rfl⟩ := hε
        exact P.primal.simpleConfig_simpleEdge_of_mem_openEdgeSet hloop hCopen heC
      openConnected :=
        P.primal.openLabelConnected_simple_of_cycleMatroid_isCircuit hloop hCopen hC }

omit [NormedSpace ℝ E] in
/-- **Cofinal dual boundaries with separator control.**  If for every radius some
primal circuit sits on the boundary of a finite dual-open component and has its
barrier-inside containing the ball of that radius, then the separator exhaustion
of the primal simple graph follows. -/
theorem hasSeparatorCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → E} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SeparatorPrimalCircuitGeometry P hloop R)
    (ω : P.primal.Configuration) (c : E)
    (hcofinal : ∀ ρ : ℝ, ∃ (x : P.Face) (C : Set P.Edge),
      C ⊆ P.faceDual.vertexCut
        (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x) ∧
      P.primal.cycleMatroid.IsCircuit C ∧ ball c ρ ⊆ (S.sep C).inside) :
    HasSeparatorCircuitExhaustion R (P.primal.simpleConfig hloop ω) c := by
  intro ρ
  obtain ⟨x, C, hCcut, hC, hball⟩ := hcofinal ρ
  exact ⟨P.primal.simpleLabels hloop C, S.sep C, hball, S.finite_inside C hC,
    separatorOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary
      S ω x hCcut hC⟩

omit [NormedSpace ℝ E] in
/-- Composition check: cofinal separator-controlled dual boundaries give actual
`GlobalAtMostOne` for the primal simple graph. -/
theorem globalAtMostOne_of_cofinal_dualOpenComponentBoundaries_separator
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → E} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SeparatorPrimalCircuitGeometry P hloop R)
    (ω : P.primal.Configuration) (c : E)
    (hcofinal : ∀ ρ : ℝ, ∃ (x : P.Face) (C : Set P.Edge),
      C ⊆ P.faceDual.vertexCut
        (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x) ∧
      P.primal.cycleMatroid.IsCircuit C ∧ ball c ρ ⊆ (S.sep C).inside) :
    GlobalAtMostOne P.primal.simpleGraph (P.primal.simpleConfig hloop ω) :=
  globalAtMostOne_of_separatorCircuitExhaustion R _ c
    (hasSeparatorCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries S ω c hcofinal)

end LabelledPrimal

end LabelledDual

section SquareNotSphere

/-- The closed unit square in `ℂ`. -/
def closedSquare : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc (-1 : ℝ) 1 ∧ z.im ∈ Set.Icc (-1 : ℝ) 1}

/-- Membership in the frontier from square membership and failure of interior
membership. -/
lemma mem_frontier_of_notMem_interior {z : ℂ} (hz : z ∈ closedSquare)
    (hni : z ∉ interior closedSquare) : z ∈ frontier closedSquare :=
  (mem_frontier_iff_notMem_interior hz).2 hni

lemma mem_closedSquare_of_re_one {z : ℂ} (hz : z.re = 1) (h : z.im ∈ Set.Icc (-1 : ℝ) 1) :
    z ∈ closedSquare :=
  ⟨⟨by simp [hz], by simp [hz]⟩, h⟩

lemma mem_closedSquare_of_im_one {z : ℂ} (hz : z.im = 1) (h : z.re ∈ Set.Icc (-1 : ℝ) 1) :
    z ∈ closedSquare :=
  ⟨h, ⟨by simp [hz], by simp [hz]⟩⟩

/-- A point with real part `1` is never interior to the closed square: moving to
the right by `ε / 2` stays in every ball of radius `ε` and leaves the square. -/
lemma re_eq_one_notMem_interior {z : ℂ} (hz : z.re = 1) : z ∉ interior closedSquare := by
  intro hzint
  obtain ⟨ε, hεpos, hball⟩ :=
    Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzint)
  have hpt : z + ((ε / 2 : ℝ) : ℂ) ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm]
    have hsub : z + ((ε / 2 : ℝ) : ℂ) - z = ((ε / 2 : ℝ) : ℂ) := by ring
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hin : z + ((ε / 2 : ℝ) : ℂ) ∈ closedSquare := interior_subset (hball hpt)
  have hre : (z + ((ε / 2 : ℝ) : ℂ)).re = 1 + ε / 2 := by simp [hz]
  have hle := hin.1.2
  linarith

/-- The imaginary-part analogue. -/
lemma im_eq_one_notMem_interior {z : ℂ} (hz : z.im = 1) : z ∉ interior closedSquare := by
  intro hzint
  obtain ⟨ε, hεpos, hball⟩ :=
    Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzint)
  have hpt : z + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm]
    have hsub : z + ((ε / 2 : ℝ) : ℂ) * Complex.I - z = ((ε / 2 : ℝ) : ℂ) * Complex.I := by
      ring
    rw [hsub, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hin : z + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ closedSquare := interior_subset (hball hpt)
  have him : (z + ((ε / 2 : ℝ) : ℂ) * Complex.I).im = 1 + ε / 2 := by simp [hz]
  have hle := hin.2.2
  linarith

/-- **The unit square's frontier is not a metric sphere.**  So a convex body that
is admissible for the separator exhaustion need not be a ball, and no
reparametrization of the spherical interface `SphericalOpenCircuit` can express
this barrier. -/
theorem closedSquare_frontier_not_sphere (c : ℂ) (r : ℝ) :
    sphere c r ≠ frontier closedSquare := by
  intro hcr
  have hmem : ∀ z ∈ frontier closedSquare, ‖z - c‖ = r := by
    intro z hz
    have hz' : z ∈ sphere c r := hcr ▸ hz
    simpa [mem_sphere, dist_eq_norm] using hz'
  have hA := hmem (1 + Complex.I) (mem_frontier_of_notMem_interior
    (mem_closedSquare_of_re_one (by simp) (by simp))
    (re_eq_one_notMem_interior (by simp)))
  have hB := hmem (1 - Complex.I) (mem_frontier_of_notMem_interior
    (mem_closedSquare_of_re_one (by simp) (by simp))
    (re_eq_one_notMem_interior (by simp)))
  have hC := hmem (-1 + Complex.I) (mem_frontier_of_notMem_interior
    (mem_closedSquare_of_im_one (by simp) (by simp))
    (im_eq_one_notMem_interior (by simp)))
  have hD := hmem (1 : ℂ) (mem_frontier_of_notMem_interior
    (mem_closedSquare_of_re_one (by simp) (by simp))
    (re_eq_one_notMem_interior (by simp)))
  have sq : ∀ z : ℂ, ‖z - c‖ = r → (z - c).re ^ 2 + (z - c).im ^ 2 = r ^ 2 := by
    intro z hz
    have h2 : ‖z - c‖ ^ 2 = r ^ 2 := by rw [hz]
    rw [Complex.sq_norm, Complex.normSq_apply] at h2
    nlinarith [h2]
  have sA := sq (1 + Complex.I) hA
  have sB := sq (1 - Complex.I) hB
  have sC := sq (-1 + Complex.I) hC
  have sD := sq (1 : ℂ) hD
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im] at sA sB sC sD
  nlinarith

end SquareNotSphere

end FK.PlaneTopology
