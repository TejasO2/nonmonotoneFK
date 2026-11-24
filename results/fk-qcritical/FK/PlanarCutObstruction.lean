import FK.PlaneClusterTarget
import FK.PlanarTarget
import FK.StaircaseConnected
import FK.OpenCutSeparation

/-!
# What a finite open cut really is, and why the planar cut interface cannot be met

The planar uniqueness chain of `FK/OpenCutSeparation.lean` proves at most one
infinite primal-open cluster from a supply of *finite all-open cuts*

`A` finite, `x, y ∈ A`, every edge of `orientedCut G A` open, and all vertices
incident to the cut mutually open-connected.

This file establishes four things about that interface and about the residual
planar obligation it was meant to discharge.

* **Exact algebra.**  All edges of `orientedCut G A` are open **iff** `A` does
  not split a single closed edge, i.e. `A` is a union of connected components of
  the graph of closed edges.  Consequently a finite all-open cut through `x`
  exists only if the whole closed-edge component of `x` is finite, and no
  version of the strict criterion can hold unless *every* closed component is
  finite.

* **The interface is not producible on the square lattice.**  The concrete
  configuration `staircaseConfig` of `FK/PlanarTarget.lean` (closed edges
  exactly the ray `(k,0)-(k+1,0)`, `k : ℕ`) has **no infinite dual-open
  cluster**, yet the origin has an infinite closed-edge component, so *no*
  finite all-open cut through the origin exists, although the origin does carry
  an infinite open cluster.  Hence the cut-construction hypothesis consumed by
  `FK.PlaneTopology.CutSeparation.dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction`
  is false for the square lattice as a whole, in all three forms in which
  `FK/OpenCutSeparation.lean` states it.  It is strictly stronger than the
  planar target and cannot be the route to it.

* **The existing open-incident criterion, algebraically repackaged.**  Replacing
  "all cut edges are open" by "the vertices incident to *open* cut edges are
  open-connected" is the already public theorem `WeakOpenCut`.  This file records
  that criterion's equivalence to open connectivity of the pair, its strict
  special case, and the staircase singleton example.  It does not derive this
  criterion from dual nonpercolation.  A closed-separating-cut formulation of
  the same connectivity target is also included, without a planar construction.

* **Sharpness on both sides.**  `strip_dualPercolation_not_atMostOne` records the
  complementary configuration on the square lattice: closing the vertical strip
  `{(a,0),(a,1)}` produces an infinite dual-open cluster *and* two infinite
  primal-open clusters, so neither hypothesis of the planar target can be
  dropped.

## Main results

* `FK.PlaneTopology.CutObstruction.orientedCut_open_iff`
* `FK.PlaneTopology.CutObstruction.closedReach_subset_of_openCut`
* `FK.PlaneTopology.CutObstruction.finite_closedComponent_of_finite_openCut`
* `FK.PlaneTopology.CutObstruction.finite_closedComponent_of_strict_criterion`
* `FK.PlaneTopology.CutObstruction.openConnected_or_exists_closed_cut`
* `FK.PlaneTopology.CutObstruction.staircase_closedReach`
* `FK.PlaneTopology.CutObstruction.staircase_closedComponent_infinite`
* `FK.PlaneTopology.CutObstruction.no_finite_openCut_at_origin`
* `FK.PlaneTopology.CutObstruction.staircase_exteriorInfinite_origin`
* `FK.PlaneTopology.CutObstruction.cutConstruction_hypothesis_false_square`
* `FK.PlaneTopology.CutObstruction.cutConstruction_hypothesis_false_square_onInfinite`
* `FK.PlaneTopology.CutObstruction.cutConstruction_hypothesis_false_square_throughLabelSet`
* `FK.PlaneTopology.CutObstruction.exists_openCut_vertex_of_walk`
* `FK.PlaneTopology.CutObstruction.openConnected_of_openCutConnected`
* `FK.PlaneTopology.CutObstruction.globalAtMostOne_of_openCutConnected`
* `FK.PlaneTopology.CutObstruction.openCutConnected_of_strict`
* `FK.PlaneTopology.CutObstruction.openCutVertex_connected_of_pair`
* `FK.PlaneTopology.CutObstruction.exists_openCut_of_openConnected`
* `FK.PlaneTopology.CutObstruction.exists_openCut_iff_openConnected`
* `FK.PlaneTopology.CutObstruction.staircase_relaxed_cut_origin`
* `FK.PlaneTopology.CutObstruction.globalAtMostOne_of_no_separating_closedCut`
* `FK.PlaneTopology.CutObstruction.strip_dualPercolation_not_atMostOne`
-/

namespace FK.PlaneTopology.CutObstruction

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.CutSeparation
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PlanarTarget

variable {V : Type*}

/-! ## The algebra of all-open cuts -/

/-- `u` and `v` are the endpoints of a **closed** edge. -/
def ClosedAdj (G : SimpleGraph V) (ω : G.edgeSet → Bool) (u v : V) : Prop :=
  ∃ h : G.Adj u v, ω (⟨s(u, v), h⟩ : G.edgeSet) = false

/-- The relation "reachable using closed edges only". -/
inductive ClosedReach (G : SimpleGraph V) (ω : G.edgeSet → Bool) : V → V → Prop where
  | refl (x : V) : ClosedReach G ω x x
  | step {x y z : V} : ClosedReach G ω x y → ClosedAdj G ω y z → ClosedReach G ω x z

/-- **Exact characterization.**  Every edge of the oriented cut of `A` is open
if and only if `A` contains both endpoints or neither endpoint of every closed
edge. -/
theorem orientedCut_open_iff {G : SimpleGraph V} {ω : G.edgeSet → Bool} {A : Set V} :
    (∀ e ∈ orientedCut G A, ω e = true) ↔
      ∀ u v : V, ClosedAdj G ω u v → (u ∈ A ↔ v ∈ A) := by
  constructor
  · intro hopen u v hcl
    obtain ⟨hadj, hclosed⟩ := hcl
    have hnot : ¬ (u ∈ A ∧ v ∉ A) := by
      rintro ⟨hu, hv⟩
      have hmem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ orientedCut G A := by
        rw [mem_orientedCut_iff]
        exact ⟨u, hu, v, hv, hadj, rfl⟩
      have hval := hopen _ hmem
      rw [hclosed] at hval
      exact Bool.false_ne_true hval
    have hnot' : ¬ (v ∈ A ∧ u ∉ A) := by
      rintro ⟨hv, hu⟩
      have hmem : (⟨s(u, v), hadj⟩ : G.edgeSet) ∈ orientedCut G A := by
        rw [mem_orientedCut_iff]
        exact ⟨v, hv, u, hu, hadj.symm, Subtype.ext Sym2.eq_swap⟩
      have hval := hopen _ hmem
      rw [hclosed] at hval
      exact Bool.false_ne_true hval
    exact ⟨fun hu => by
        by_contra hv
        exact hnot ⟨hu, hv⟩,
      fun hv => by
        by_contra hu
        exact hnot' ⟨hv, hu⟩⟩
  · intro hcross e he
    rw [mem_orientedCut_iff] at he
    obtain ⟨u, hu, v, hv, hadj, rfl⟩ := he
    by_contra hne
    have hclosed : ω (⟨s(u, v), hadj⟩ : G.edgeSet) = false := by
      cases h : ω (⟨s(u, v), hadj⟩ : G.edgeSet) with
      | false => rfl
      | true => exact absurd h hne
    exact hv ((hcross u v ⟨hadj, hclosed⟩).mp hu)

/-- The vertices reachable from `x` by closed edges stay inside any finite
all-open cut through `x`. -/
theorem closedReach_subset_of_openCut {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} (hopen : ∀ e ∈ orientedCut G A, ω e = true) {x : V} (hx : x ∈ A) :
    {y : V | ClosedReach G ω x y} ⊆ A := by
  intro y hy
  induction hy with
  | refl => exact hx
  | step _ hstep ih => exact (orientedCut_open_iff.mp hopen _ _ hstep).mp ih

/-- **A finite all-open cut forces the closed component of its vertex to be
finite.** -/
theorem finite_closedComponent_of_finite_openCut {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} {x : V} (hA : A.Finite) (hx : x ∈ A)
    (hopen : ∀ e ∈ orientedCut G A, ω e = true) :
    {y : V | ClosedReach G ω x y}.Finite :=
  hA.subset (closedReach_subset_of_openCut hopen hx)

/-! ## Separation by closed cuts, in general -/

/-- **Closed-cut duality in a graph.**  Two vertices are either open-connected,
or the closed edges leave the open component of one of them: the oriented cut of
the open component of `x` consists of closed edges and separates `x` from `y`.

This is an algebraic disconnectedness dichotomy only. No construction of a dual
connected boundary from the closed cut is proved here. -/
theorem openConnected_or_exists_closed_cut {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (x : V) :
    ∀ y : V, OpenConnected G ω Set.univ x y ∨
      ∃ A : Set V, x ∈ A ∧ y ∉ A ∧ ∀ e ∈ orientedCut G A, ω e = false := by
  intro y
  by_cases h : OpenConnected G ω Set.univ x y
  · exact Or.inl h
  · right
    refine ⟨{z : V | OpenConnected G ω Set.univ x z},
      OpenConnected.refl ω Set.univ x, h, ?_⟩
    intro e he
    rw [mem_orientedCut_iff] at he
    obtain ⟨u, hu, v, hv, hadj, rfl⟩ := he
    by_contra hne
    have hopen : ω (⟨s(u, v), hadj⟩ : G.edgeSet) = true := by
      cases hh : ω (⟨s(u, v), hadj⟩ : G.edgeSet) with
      | false => exact absurd hh hne
      | true => rfl
    exact hv (hu.trans (OpenConnected.of_adj hadj (Set.mem_univ _) hopen))

/-! ## The staircase obstruction on the square lattice -/

/-- The `k`-th closed step of the staircase configuration at the origin. -/
theorem staircase_step_closed (k : ℕ) :
    ClosedAdj gridGraph staircaseConfig (((k : ℤ)), 0) ((((k : ℤ)) + 1), 0) :=
  ⟨gridAdj_fst_add (k : ℤ) 0, (staircaseConfig_closed_iff _).mpr ⟨k, rfl⟩⟩

/-- The whole ray `(k,0)` is closed-reachable from the origin. -/
theorem staircase_closedReach : ∀ k : ℕ,
    ClosedReach gridGraph staircaseConfig ((0 : ℤ), 0) (((k : ℕ) : ℤ), 0)
  | 0 => ClosedReach.refl _
  | (n + 1) => by
      have hstep : ClosedAdj gridGraph staircaseConfig (((n : ℕ) : ℤ), 0)
          ((((n : ℕ) : ℤ) + 1), 0) := staircase_step_closed n
      have h := ClosedReach.step (staircase_closedReach n) hstep
      have hcast : (((n : ℕ) : ℤ) + 1) = (((n + 1 : ℕ) : ℤ)) := by push_cast; ring
      have hpair : ((((n : ℕ) : ℤ) + 1), (0 : ℤ)) = ((((n + 1 : ℕ) : ℤ)), (0 : ℤ)) := by
        rw [hcast]
      rw [hpair] at h
      exact h

/-- **The origin has an infinite closed component** in the staircase
configuration. -/
theorem staircase_closedComponent_infinite :
    {y : GridV | ClosedReach gridGraph staircaseConfig ((0 : ℤ), 0) y}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (((k : ℤ)), (0 : ℤ))) ?_ ?_
  · rintro a b hab
    have h1 : ((a : ℤ)) = ((b : ℤ)) := by
      have := congrArg Prod.fst hab
      simpa using this
    exact_mod_cast h1
  · intro k
    exact staircase_closedReach k

/-- **No finite all-open cut passes through the origin** of the staircase
configuration, whatever its shape: the closed ray forces every such cut to
contain infinitely many vertices.  Compare
`FK.PlaneTopology.PlanarTarget.exists_dualNonpercolating_noOpenDiamondCut`,
which only excludes the fixed `ℓ¹` level sets. -/
theorem no_finite_openCut_at_origin :
    ¬ ∃ A : Set GridV, A.Finite ∧ ((0 : ℤ), 0) ∈ A ∧
      ∀ e ∈ orientedCut gridGraph A, staircaseConfig e = true := by
  rintro ⟨A, hA, hx, hopen⟩
  exact staircase_closedComponent_infinite
    (finite_closedComponent_of_finite_openCut hA hx hopen)

/-- **The cut-construction hypothesis of the planar uniqueness chain is false on
the square lattice.**  There is no way to produce the finite all-open cut
demanded by
`FK.PlaneTopology.CutSeparation.dualNonpercolationForcesPrimalAtMostOne_of_cutConstruction`
from dual nonpercolation: the staircase configuration has no infinite dual-open
cluster but no finite all-open cut through the origin exists. -/
theorem cutConstruction_hypothesis_false_square :
    ¬ (∀ (ω : gridGraph.edgeSet → Bool),
        FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) →
        ∀ x y : GridV, ∃ A : Set GridV, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
          (∀ e ∈ orientedCut gridGraph A, ω e = true) ∧
          (∀ u v : GridV, VertexOnLabels (orientedCut gridGraph A) u →
            VertexOnLabels (orientedCut gridGraph A) v →
              OpenConnected gridGraph ω Set.univ u v)) := by
  intro hcon
  obtain ⟨A, hA, hx, -, hopen, -⟩ :=
    hcon staircaseConfig staircase_dual_nonpercolation ((0 : ℤ), 0) ((0 : ℤ), 0)
  exact no_finite_openCut_at_origin ⟨A, hA, hx, hopen⟩

/-- **The origin already carries an infinite open cluster** in the staircase
configuration (`StaircaseConnected.staircase_connected`), so the obstruction
above applies to the "infinite clusters only" form of the cut criterion too. -/
theorem staircase_exteriorInfinite_origin :
    ExteriorInfiniteCluster gridGraph staircaseConfig Set.univ ((0 : ℤ), 0) := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((0 : ℤ), ((n : ℕ) : ℤ)))) ?_ ?_
  · rintro a b hab
    have h := congrArg Prod.snd hab
    simpa using h
  · intro n
    exact openConnected_symm
      (FK.PlaneTopology.StaircaseConnected.staircase_connected ((0 : ℤ), ((n : ℕ) : ℤ)))

/-- **The weaker, infinite-cluster-only form of the cut interface is also
unproducible on the square lattice.** -/
theorem cutConstruction_hypothesis_false_square_onInfinite :
    ¬ (∀ (ω : gridGraph.edgeSet → Bool),
        FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) →
        ∀ x y : GridV, ExteriorInfiniteCluster gridGraph ω Set.univ x →
          ExteriorInfiniteCluster gridGraph ω Set.univ y →
          ∃ A : Set GridV, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
            (∀ e ∈ orientedCut gridGraph A, ω e = true) ∧
            (∀ u v : GridV, VertexOnLabels (orientedCut gridGraph A) u →
              VertexOnLabels (orientedCut gridGraph A) v →
                OpenConnected gridGraph ω Set.univ u v)) := by
  intro hcon
  obtain ⟨A, hA, hx, -, hopen, -⟩ :=
    hcon staircaseConfig staircase_dual_nonpercolation ((0 : ℤ), 0) ((0 : ℤ), 0)
      staircase_exteriorInfinite_origin staircase_exteriorInfinite_origin
  exact no_finite_openCut_at_origin ⟨A, hA, hx, hopen⟩

/-! ## Repackaging the existing open-incident criterion -/

/-- A vertex incident to an **open** edge of the oriented cut of `A`. -/
def OpenCutVertex (G : SimpleGraph V) (ω : G.edgeSet → Bool) (A : Set V) (u : V) : Prop :=
  ∃ e ∈ orientedCut G A, ω e = true ∧ VertexOnLabels ({e} : Set G.edgeSet) u

/-- Crossing lemma, with the open cut edge recorded. -/
theorem exists_openCut_vertex_of_walk {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} {x z : V} (p : G.Walk x z) (hp : IsOpenIn ω Set.univ p)
    (hxA : x ∈ A) (hzA : z ∉ A) :
    ∃ (u : V) (e : G.edgeSet), e ∈ orientedCut G A ∧ ω e = true ∧
      VertexOnLabels ({e} : Set G.edgeSet) u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact (hzA hxA).elim
  | @cons a b c hab q ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      by_cases hbA : b ∈ A
      · obtain ⟨u, e, he, hoe, hlab, hbu⟩ := ih hrest hbA hzA
        exact ⟨u, e, he, hoe, hlab,
          (OpenConnected.of_adj hab (Set.mem_univ _) hopen).trans hbu⟩
      · refine ⟨a, ⟨s(a, b), hab⟩, ?_, hopen, ⟨b, hab, by simp⟩,
          OpenConnected.refl ω Set.univ a⟩
        rw [mem_orientedCut_iff]
        exact ⟨a, hxA, b, hbA, hab, rfl⟩

/-- **The crossing argument of the defect-tolerant criterion.**  A finite set
through two vertices with infinite clusters, whose open cut vertices are
mutually open-connected, forces the two vertices to be open-connected. -/
theorem openConnected_of_openCutConnected {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set V} {x y : V} (hAfin : A.Finite) (hxA : x ∈ A) (hyA : y ∈ A)
    (hx : ExteriorInfiniteCluster G ω Set.univ x)
    (hy : ExteriorInfiniteCluster G ω Set.univ y)
    (hconn : ∀ u v : V, OpenCutVertex G ω A u → OpenCutVertex G ω A v →
      OpenConnected G ω Set.univ u v) :
    OpenConnected G ω Set.univ x y := by
  have hex : ∃ z : V, OpenConnected G ω Set.univ x z ∧ z ∉ A := by
    by_contra hc
    exact hx (hAfin.subset fun z hz => by
      by_contra hzA
      exact hc ⟨z, hz, hzA⟩)
  obtain ⟨z, hxz, hzA⟩ := hex
  obtain ⟨p, hp⟩ := hxz
  obtain ⟨u, e, he, hoe, hlab, hxu⟩ := exists_openCut_vertex_of_walk p hp hxA hzA
  have hey : ∃ z : V, OpenConnected G ω Set.univ y z ∧ z ∉ A := by
    by_contra hc
    exact hy (hAfin.subset fun z hz => by
      by_contra hzA
      exact hc ⟨z, hz, hzA⟩)
  obtain ⟨w, hyw, hwA⟩ := hey
  obtain ⟨q, hq⟩ := hyw
  obtain ⟨v, f, hf, hof, hflab, hyv⟩ := exists_openCut_vertex_of_walk q hq hyA hwA
  exact hxu.trans
    ((hconn u v ⟨e, he, hoe, hlab⟩ ⟨f, hf, hof, hflab⟩).trans (openConnected_symm hyv))

/-- **The defect-tolerant cut criterion.**  At most one infinite open cluster
follows if for every pair of vertices carrying infinite clusters there is a
finite set `A` containing both whose *open* cut vertices are mutually
open-connected.  Closed cut edges are irrelevant: only the open crossing edges
are used in the argument. -/
theorem globalAtMostOne_of_openCutConnected {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ExteriorInfiniteCluster G ω Set.univ x →
      ExteriorInfiniteCluster G ω Set.univ y →
      ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
        (∀ u v : V, OpenCutVertex G ω A u → OpenCutVertex G ω A v →
          OpenConnected G ω Set.univ u v)) :
    GlobalAtMostOne G ω := by
  intro x y hx hy
  obtain ⟨A, hAfin, hxA, hyA, hconn⟩ := h x y hx hy
  exact openConnected_of_openCutConnected hAfin hxA hyA hx hy hconn

/-- The converse of the crossing argument: for an open-connected pair the
two-point set `{x, y}` has connected open cut vertices, because every open cut
edge is incident to `x` or to `y`. -/
theorem openCutVertex_connected_of_pair {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {x y : V} (hxy : OpenConnected G ω Set.univ x y)
    {u : V} (hu : OpenCutVertex G ω ({x, y} : Set V) u) :
    OpenConnected G ω Set.univ u x := by
  obtain ⟨e, he, hoe, hlab⟩ := hu
  rw [mem_orientedCut_iff] at he
  obtain ⟨p, hp, q, hq, hadj, rfl⟩ := he
  obtain ⟨w, hw, hmem⟩ := hlab
  have hedge : (⟨s(u, w), hw⟩ : G.edgeSet) = (⟨s(p, q), hadj⟩ : G.edgeSet) := by
    simpa using hmem
  have hsym : s(u, w) = s(p, q) := congrArg Subtype.val hedge
  rcases Sym2.eq_iff.mp hsym with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]
    rcases (by simpa using hp : p = x ∨ p = y) with hpx | hpy
    · rw [hpx]; exact OpenConnected.refl ω Set.univ x
    · rw [hpy]; exact openConnected_symm hxy
  · rw [h1]
    have hpq : OpenConnected G ω Set.univ q p :=
      openConnected_symm (OpenConnected.of_adj hadj (Set.mem_univ _) hoe)
    rcases (by simpa using hp : p = x ∨ p = y) with hpx | hpy
    · rw [hpx] at hpq
      exact hpq
    · rw [hpy] at hpq
      exact hpq.trans (openConnected_symm hxy)

/-- **An open-connected pair admits a defect-tolerant cut.** -/
theorem exists_openCut_of_openConnected {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {x y : V} (hxy : OpenConnected G ω Set.univ x y) :
    ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ u v : V, OpenCutVertex G ω A u → OpenCutVertex G ω A v →
        OpenConnected G ω Set.univ u v) := by
  refine ⟨{x, y}, (Set.finite_singleton y).insert x, by simp, by simp, ?_⟩
  intro u v hu hv
  exact (openCutVertex_connected_of_pair hxy hu).trans
    (openConnected_symm (openCutVertex_connected_of_pair hxy hv))

/-- Every vertex incident to an open edge of the cut of the origin in the
staircase configuration is open-connected to the origin. -/
theorem staircase_cutVertex_connected {u : GridV}
    (hu : OpenCutVertex gridGraph staircaseConfig ({((0 : ℤ), (0 : ℤ))} : Set GridV) u) :
    OpenConnected gridGraph staircaseConfig Set.univ u ((0 : ℤ), 0) := by
  obtain ⟨e, he, hoe, hlab⟩ := hu
  rw [mem_orientedCut_iff] at he
  obtain ⟨p, hp, q, hq, hadj, rfl⟩ := he
  have hp' : p = ((0 : ℤ), (0 : ℤ)) := by simpa using hp
  subst hp'
  obtain ⟨w, hw, hmem⟩ := hlab
  have hedge : (⟨s(u, w), hw⟩ : gridGraph.edgeSet) =
      (⟨s(((0 : ℤ), (0 : ℤ)), q), hadj⟩ : gridGraph.edgeSet) := by
    simpa using hmem
  have hsym : s(u, w) = s(((0 : ℤ), (0 : ℤ)), q) := congrArg Subtype.val hedge
  rcases Sym2.eq_iff.mp hsym with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]
    exact OpenConnected.refl staircaseConfig Set.univ _
  · rw [h1]
    exact openConnected_symm (OpenConnected.of_adj hadj (Set.mem_univ _) hoe)

/-- **The repaired hypothesis holds exactly where the strict one fails.**  For
the pair `(origin, origin)` of the staircase configuration — the pair on which
`no_finite_openCut_at_origin` shows that *no* finite all-open cut exists — the
singleton `{(0,0)}` satisfies the defect-tolerant hypothesis. -/
theorem staircase_relaxed_cut_origin :
    ∀ u v : GridV,
      OpenCutVertex gridGraph staircaseConfig ({((0 : ℤ), (0 : ℤ))} : Set GridV) u →
      OpenCutVertex gridGraph staircaseConfig ({((0 : ℤ), (0 : ℤ))} : Set GridV) v →
      OpenConnected gridGraph staircaseConfig Set.univ u v := by
  intro u v hu hv
  exact (staircase_cutVertex_connected hu).trans
    (openConnected_symm (staircase_cutVertex_connected hv))

/-! ## The strict criterion implies the open-incident criterion -/

/-- If every cut edge is open, the vertices incident to open cut edges are
exactly the vertices incident to cut edges; hence the strict cut hypothesis
implies the defect-tolerant one. -/
theorem openCutVertex_iff_of_all_open {G : SimpleGraph V} {ω : G.edgeSet → Bool} {A : Set V}
    (hopen : ∀ e ∈ orientedCut G A, ω e = true) {u : V} :
    OpenCutVertex G ω A u ↔ VertexOnLabels (orientedCut G A) u := by
  constructor
  · rintro ⟨e, he, -, hlab⟩
    obtain ⟨v, hadj, hmem⟩ := hlab
    refine ⟨v, hadj, ?_⟩
    rw [Set.mem_singleton_iff] at hmem
    rwa [hmem]
  · rintro ⟨v, hadj, hmem⟩
    exact ⟨⟨s(u, v), hadj⟩, hmem, hopen _ hmem, ⟨v, hadj, rfl⟩⟩

/-- The strict cut hypothesis of `FK.PlaneTopology.CutSeparation` implies the
defect-tolerant hypothesis, so `globalAtMostOne_of_openCutConnected` is a
strict generalisation. -/
theorem openCutConnected_of_strict {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ e ∈ orientedCut G A, ω e = true) ∧
      (∀ u v : V, VertexOnLabels (orientedCut G A) u →
        VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v)) :
    ∀ x y : V, Exists fun A : Set V => A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ u v : V, OpenCutVertex G ω A u → OpenCutVertex G ω A v →
        OpenConnected G ω Set.univ u v) := by
  intro x y
  obtain ⟨A, hA, hx, hy, hopen, hconn⟩ := h x y
  refine ⟨A, hA, hx, hy, ?_⟩
  intro u v hu hv
  exact hconn u v ((openCutVertex_iff_of_all_open hopen).mp hu)
    ((openCutVertex_iff_of_all_open hopen).mp hv)

/-! ## The complementary regime: dual percolation with two infinite primal clusters -/

/-- The closed vertical edge `(a,0)-(a,1)`. -/
def stripEdge (a : ℤ) : gridGraph.edgeSet :=
  ⟨s(((a : ℤ), (0 : ℤ)), ((a : ℤ), (1 : ℤ))), gridAdj_snd_add (a : ℤ) 0⟩

/-- The configuration closing exactly the vertical strip between the rows `0`
and `1`. -/
noncomputable def stripConfig : gridGraph.edgeSet → Bool :=
  fun e => if ∃ a : ℤ, e = stripEdge a then false else true

lemma stripConfig_closed_iff (e : gridGraph.edgeSet) :
    stripConfig e = false ↔ ∃ a : ℤ, e = stripEdge a := by
  unfold stripConfig
  by_cases h : ∃ a : ℤ, e = stripEdge a <;> simp [h]

lemma stripConfig_open_iff (e : gridGraph.edgeSet) :
    stripConfig e = true ↔ ∀ a : ℤ, e ≠ stripEdge a := by
  constructor
  · intro h a ha
    have hclosed : stripConfig e = false := (stripConfig_closed_iff e).mpr ⟨a, ha⟩
    rw [hclosed] at h
    exact Bool.false_ne_true h
  · intro h
    by_contra hc
    have hclosed : stripConfig e = false := by
      cases he : stripConfig e with
      | false => rfl
      | true => exact absurd he hc
    obtain ⟨a, ha⟩ := (stripConfig_closed_iff e).mp hclosed
    exact h a ha

/-- No horizontal edge of the lattice is a strip edge. -/
lemma strip_horiz_open (m n : ℤ) :
    stripConfig (⟨s((m, n), (m + 1, n)), gridAdj_fst_add m n⟩ : gridGraph.edgeSet) = true := by
  rw [stripConfig_open_iff]
  intro a hEq
  have hval : s((m, n), (m + 1, n)) = s(((a : ℤ), (0 : ℤ)), ((a : ℤ), (1 : ℤ))) := by
    have := congrArg Subtype.val hEq
    simpa [stripEdge] using this
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Prod.mk.injEq] at h1 h2 <;> omega

/-- A vertical edge off the row `0` is open. -/
lemma strip_vert_open {m n : ℤ} (hn : n ≠ 0) :
    stripConfig (⟨s((m, n), (m, n + 1)), gridAdj_snd_add m n⟩ : gridGraph.edgeSet) = true := by
  rw [stripConfig_open_iff]
  intro a hEq
  have hval : s((m, n), (m, n + 1)) = s(((a : ℤ), (0 : ℤ)), ((a : ℤ), (1 : ℤ))) := by
    have := congrArg Subtype.val hEq
    simpa [stripEdge] using this
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [Prod.mk.injEq] at h1 h2 <;> omega

/-- The row `y = 0` is open-connected, so `(0,0)` carries an infinite cluster. -/
theorem strip_lower_infinite :
    ExteriorInfiniteCluster gridGraph stripConfig Set.univ ((0 : ℤ), 0) := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n : ℕ) : ℤ), (0 : ℤ))) ?_ ?_
  · rintro a b hab
    have h := congrArg Prod.fst hab
    simpa using h
  · intro n
    exact FK.PlaneTopology.StaircaseConnected.row_open (n := 0) (ω := stripConfig)
      (fun m => strip_horiz_open m 0) 0 ((n : ℕ) : ℤ)

/-- The row `y = 1` is open-connected, so `(0,1)` carries an infinite cluster. -/
theorem strip_upper_infinite :
    ExteriorInfiniteCluster gridGraph stripConfig Set.univ ((0 : ℤ), 1) := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n : ℕ) : ℤ), (1 : ℤ))) ?_ ?_
  · rintro a b hab
    have h := congrArg Prod.fst hab
    simpa using h
  · intro n
    exact FK.PlaneTopology.StaircaseConnected.row_open (n := 1) (ω := stripConfig)
      (fun m => strip_horiz_open m 1) 0 ((n : ℕ) : ℤ)

/-- No open edge crosses the strip from above. -/
lemma strip_open_step {u v : GridV} (h : gridAdj u v)
    (hopen : stripConfig (⟨s(u, v), h⟩ : gridGraph.edgeSet) = true) (hu : 1 ≤ u.2) : 1 ≤ v.2 := by
  by_contra hv
  have hv' : v.2 ≤ 0 := by omega
  have h' : gridAdj u v := h
  rcases h' with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hu2 : u.2 = 1 := by omega
    have hv2 : v.2 = 0 := by omega
    have hEq : (⟨s(u, v), h⟩ : gridGraph.edgeSet) = stripEdge (v.1) := by
      refine Subtype.ext ?_
      show s(u, v) = s(((v.1 : ℤ), (0 : ℤ)), ((v.1 : ℤ), (1 : ℤ)))
      rw [show u = (v.1, (1 : ℤ)) from Prod.ext h1 hu2,
        show v = (v.1, (0 : ℤ)) from Prod.ext rfl hv2]
      exact Sym2.eq_swap
    have hclosed : stripConfig (stripEdge (v.1)) = false := (stripConfig_closed_iff _).mpr ⟨v.1, rfl⟩
    rw [hEq, hclosed] at hopen
    exact Bool.false_ne_true hopen
  · omega
  · omega
  · omega

/-- Any open walk starting on or above the row `1` stays there. -/
theorem strip_openWalk_upper {x z : GridV} (p : gridGraph.Walk x z)
    (hp : IsOpenIn stripConfig Set.univ p) (hx : 1 ≤ x.2) : 1 ≤ z.2 := by
  induction p with
  | nil => exact hx
  | @cons a b c hab q ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      exact ih hrest (strip_open_step hab hopen hx)

theorem strip_not_openConnected :
    ¬ OpenConnected gridGraph stripConfig Set.univ ((0 : ℤ), 1) ((0 : ℤ), 0) := by
  rintro ⟨p, hp⟩
  have h := strip_openWalk_upper p hp (by norm_num : (1 : ℤ) ≤ ((0 : ℤ), (1 : ℤ)).2)
  norm_num at h

/-- The strip configuration is not at most one: two infinite open clusters. -/
theorem strip_not_globalAtMostOne : ¬ GlobalAtMostOne gridGraph stripConfig := by
  intro h
  exact strip_not_openConnected (h _ _ strip_upper_infinite strip_lower_infinite)

lemma gridAdj_fst_sub_add (a : ℤ) : gridAdj (((a - 1 : ℤ), (0 : ℤ)) : GridV) ((a : ℤ), (0 : ℤ)) := by
  have h : (a - 1) + 1 = a := by ring
  simpa [h] using gridAdj_fst_add (a - 1) (0 : ℤ)

/-- The primal edge whose dual is the horizontal edge `(a,0)-(a+1,0)`. -/
lemma crossEdge_stripEdge (a : ℤ) :
    crossEdge (stripEdge a) =
      (⟨s(((a - 1 : ℤ), (0 : ℤ)), ((a : ℤ), (0 : ℤ))), gridAdj_fst_sub_add a⟩ :
        gridGraph.edgeSet) := by
  unfold stripEdge
  rw [crossEdge_apply_mk]
  refine Subtype.ext ?_
  simp only [crossPair]
  rw [dualLo_vert (p := ((a : ℤ), (0 : ℤ))) (q := ((a : ℤ), (1 : ℤ))) rfl (Or.inr rfl),
    dualHi_vert (p := ((a : ℤ), (0 : ℤ))) (q := ((a : ℤ), (1 : ℤ))) rfl (Or.inr rfl)]
  simp

/-- The duals of the strip edges form an open horizontal row in the dual
configuration. -/
lemma dualStrip_row_open (m : ℤ) :
    dualConfig gridCrossEquiv stripConfig
      (⟨s(((m : ℤ), (0 : ℤ)), (((m : ℤ) + 1), (0 : ℤ))), gridAdj_fst_add m 0⟩ :
        gridGraph.edgeSet) = true := by
  unfold dualConfig
  have hsym : gridCrossEquiv.symm
      (⟨s(((m : ℤ), (0 : ℤ)), (((m : ℤ) + 1), (0 : ℤ))), gridAdj_fst_add m 0⟩ :
        gridGraph.edgeSet) = stripEdge (m + 1) := by
    rw [Equiv.symm_apply_eq]
    change (⟨s(((m : ℤ), (0 : ℤ)), (((m : ℤ) + 1), (0 : ℤ))), gridAdj_fst_add m 0⟩ :
      gridGraph.edgeSet) = crossEdge (stripEdge (m + 1))
    rw [crossEdge_stripEdge (m + 1)]
    refine Subtype.ext ?_
    have hk : ((m + 1) - 1 : ℤ) = m := by ring
    simp [hk]
  rw [hsym]
  have hclosed : stripConfig (stripEdge (m + 1)) = false :=
    (stripConfig_closed_iff _).mpr ⟨m + 1, rfl⟩
  rw [hclosed]
  rfl

/-- The dual configuration percolates. -/
theorem strip_dual_infinite :
    ExteriorInfiniteCluster gridDual (dualConfig gridCrossEquiv stripConfig) Set.univ ((0 : ℤ), 0) := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n : ℕ) : ℤ), (0 : ℤ))) ?_ ?_
  · rintro a b hab
    have h := congrArg Prod.fst hab
    simpa using h
  · intro n
    exact FK.PlaneTopology.StaircaseConnected.row_open (n := 0)
      (ω := dualConfig gridCrossEquiv stripConfig) (fun m => dualStrip_row_open m) 0 ((n : ℕ) : ℤ)

/-- **Both hypotheses of the planar target are essential.**  The strip
configuration has an infinite dual-open cluster and two infinite primal-open
clusters, so neither `DualNonpercolationForcesPrimalAtMostOne` nor an
unconditional `GlobalAtMostOne` can be strengthened. -/
theorem strip_dualPercolation_not_atMostOne :
    ¬ FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv stripConfig) ∧
      ¬ GlobalAtMostOne gridGraph stripConfig :=
  ⟨fun h => strip_dual_infinite (h ((0 : ℤ), 0)), strip_not_globalAtMostOne⟩

/-! ## Algebraic cut equivalences -/

/-- **The relaxed criterion is exact, not merely sufficient.**  Two vertices that
already carry infinite open clusters have a finite set `A` through them with
connected open cut vertices **iff** they are open-connected.  The forward
direction is the crossing argument of the cut criterion; the converse takes
`A = {x, y}`.

Consequently the strict "all cut edges open" hypothesis is stronger than the
requested open-connectedness conclusion for a pair, and its construction from dual
nonpercolation is impossible on the square lattice by
`cutConstruction_hypothesis_false_square`.  The open-incident hypothesis is itself
equivalent to that pair's conclusion; this equivalence does not construct it. -/
theorem exists_openCut_iff_openConnected {G : SimpleGraph V} {ω : G.edgeSet → Bool} {x y : V}
    (hx : ExteriorInfiniteCluster G ω Set.univ x) (hy : ExteriorInfiniteCluster G ω Set.univ y) :
    (∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ u v : V, OpenCutVertex G ω A u → OpenCutVertex G ω A v →
        OpenConnected G ω Set.univ u v)) ↔ OpenConnected G ω Set.univ x y := by
  constructor
  · rintro ⟨A, hAfin, hxA, hyA, hconn⟩
    exact openConnected_of_openCutConnected hAfin hxA hyA hx hy hconn
  · exact exists_openCut_of_openConnected

/-- A sufficient closed-separating-cut formulation, not a construction from dual
nonpercolation. If every oriented cut separating two vertices with infinite open
clusters contains an open edge, those vertices are open-connected; otherwise the
open component of the first vertex supplies a closed separating cut. Since the
hypothesis quantifies over all such sets, this retains the original connectivity
obligation rather than providing a planar proof of it. -/

theorem globalAtMostOne_of_no_separating_closedCut {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ (A : Set V) (x y : V), ExteriorInfiniteCluster G ω Set.univ x →
      ExteriorInfiniteCluster G ω Set.univ y → x ∈ A → y ∉ A →
      ∃ e ∈ orientedCut G A, ω e = true) :
    GlobalAtMostOne G ω := by
  intro x y hx hy
  by_contra hconn
  obtain ⟨A, hxA, hyA, hclosed⟩ :=
    (openConnected_or_exists_closed_cut (ω := ω) x y).resolve_left hconn
  obtain ⟨e, he, hopen⟩ := h A x y hx hy hxA hyA
  rw [hclosed e he] at hopen
  exact Bool.false_ne_true hopen

/-- **No version of the strict cut criterion can hold on a configuration with an
infinite closed component.**  This is the general form of the obstruction: any
`A` with an all-open cut is a union of closed-edge components, so every closed
component through a vertex that the criterion must serve has to be finite. -/
theorem finite_closedComponent_of_strict_criterion {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    (h : ∀ x y : V, ∃ A : Set V, A.Finite ∧ x ∈ A ∧ y ∈ A ∧
      (∀ e ∈ orientedCut G A, ω e = true) ∧
      (∀ u v : V, VertexOnLabels (orientedCut G A) u →
        VertexOnLabels (orientedCut G A) v → OpenConnected G ω Set.univ u v)) :
    ∀ x : V, {y : V | ClosedReach G ω x y}.Finite := by
  intro x
  obtain ⟨A, hA, hx, -, hopen, -⟩ := h x x
  exact finite_closedComponent_of_finite_openCut hA hx hopen

/-- **The label-set form of the cut interface is unproducible too.**  Any `C`
containing the oriented cut and consisting of open edges makes the cut all-open,
so the obstruction of `no_finite_openCut_at_origin` applies to
`globalAtMostOne_of_finite_openCuts_through_labelSet` as well. -/
theorem cutConstruction_hypothesis_false_square_throughLabelSet :
    ¬ (∀ (ω : gridGraph.edgeSet → Bool),
        FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) →
        ∀ x y : GridV, ∃ (A : Set GridV) (C : Set gridGraph.edgeSet),
          A.Finite ∧ x ∈ A ∧ y ∈ A ∧ orientedCut gridGraph A ⊆ C ∧
          (∀ e ∈ C, ω e = true) ∧ OpenLabelConnected gridGraph ω C) := by
  intro hcon
  obtain ⟨A, C, hA, hx, -, hsub, hopen, -⟩ :=
    hcon staircaseConfig staircase_dual_nonpercolation ((0 : ℤ), 0) ((0 : ℤ), 0)
  exact no_finite_openCut_at_origin ⟨A, hA, hx, fun e he => hopen e (hsub he)⟩

end FK.PlaneTopology.CutObstruction

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.CutObstruction.orientedCut_open_iff
#print axioms FK.PlaneTopology.CutObstruction.closedReach_subset_of_openCut
#print axioms FK.PlaneTopology.CutObstruction.finite_closedComponent_of_finite_openCut
#print axioms FK.PlaneTopology.CutObstruction.openConnected_or_exists_closed_cut
#print axioms FK.PlaneTopology.CutObstruction.staircase_step_closed
#print axioms FK.PlaneTopology.CutObstruction.staircase_closedReach
#print axioms FK.PlaneTopology.CutObstruction.staircase_closedComponent_infinite
#print axioms FK.PlaneTopology.CutObstruction.no_finite_openCut_at_origin
#print axioms FK.PlaneTopology.CutObstruction.staircase_exteriorInfinite_origin
#print axioms FK.PlaneTopology.CutObstruction.cutConstruction_hypothesis_false_square
#print axioms FK.PlaneTopology.CutObstruction.cutConstruction_hypothesis_false_square_onInfinite
#print axioms FK.PlaneTopology.CutObstruction.finite_closedComponent_of_strict_criterion
#print axioms FK.PlaneTopology.CutObstruction.cutConstruction_hypothesis_false_square_throughLabelSet
#print axioms FK.PlaneTopology.CutObstruction.openCutVertex_iff_of_all_open
#print axioms FK.PlaneTopology.CutObstruction.openCutConnected_of_strict
#print axioms FK.PlaneTopology.CutObstruction.exists_openCut_vertex_of_walk
#print axioms FK.PlaneTopology.CutObstruction.openConnected_of_openCutConnected
#print axioms FK.PlaneTopology.CutObstruction.openCutVertex_connected_of_pair
#print axioms FK.PlaneTopology.CutObstruction.exists_openCut_of_openConnected
#print axioms FK.PlaneTopology.CutObstruction.exists_openCut_iff_openConnected
#print axioms FK.PlaneTopology.CutObstruction.globalAtMostOne_of_openCutConnected
#print axioms FK.PlaneTopology.CutObstruction.staircase_cutVertex_connected
#print axioms FK.PlaneTopology.CutObstruction.staircase_relaxed_cut_origin
#print axioms FK.PlaneTopology.CutObstruction.globalAtMostOne_of_no_separating_closedCut
#print axioms FK.PlaneTopology.CutObstruction.stripConfig_closed_iff
#print axioms FK.PlaneTopology.CutObstruction.strip_horiz_open
#print axioms FK.PlaneTopology.CutObstruction.strip_vert_open
#print axioms FK.PlaneTopology.CutObstruction.strip_lower_infinite
#print axioms FK.PlaneTopology.CutObstruction.strip_upper_infinite
#print axioms FK.PlaneTopology.CutObstruction.strip_open_step
#print axioms FK.PlaneTopology.CutObstruction.strip_openWalk_upper
#print axioms FK.PlaneTopology.CutObstruction.strip_not_openConnected
#print axioms FK.PlaneTopology.CutObstruction.strip_not_globalAtMostOne
#print axioms FK.PlaneTopology.CutObstruction.gridAdj_fst_sub_add
#print axioms FK.PlaneTopology.CutObstruction.crossEdge_stripEdge
#print axioms FK.PlaneTopology.CutObstruction.dualStrip_row_open
#print axioms FK.PlaneTopology.CutObstruction.strip_dual_infinite
#print axioms FK.PlaneTopology.CutObstruction.strip_dualPercolation_not_atMostOne
