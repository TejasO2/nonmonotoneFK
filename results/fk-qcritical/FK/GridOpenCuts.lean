import FK.GridFrontier
import FK.OpenCutSeparation
import FK.PlaneClusterTarget

/-!
# Non-degenerate open cuts on the square lattice

`FK/GridFrontier.lean` proves that the `ℓ¹` diamond shells of the square lattice
carry *connected* crossing label sets (`diamondCut_openLabelConnected`), that the
all-open configuration has a genuine cofinal separator--circuit exhaustion, and
that the diamond crossing sets partition the edge set, so a cofinal family of
all-open diamond shells forces the configuration to be all-open
(`allOpen_of_diamondCuts_open`).

This file closes the step that this obstruction leaves open: a diamond shell
which happens to be open is a genuine **finite open cut** in the sense of
`FK.PlaneTopology.CutSeparation.globalAtMostOne_of_finite_openCuts_through_labelSet`,
so *cofinally many* open diamond shells already give at most one infinite open
cluster.  Specialising, a configuration of the square lattice whose **closed
edge set is finite** has at most one infinite open cluster.  This is a genuine
non-all-open instance: the cut criterion, the `ℓ¹` crossing control and the
level-set separation are all consumed at once, and the configuration is allowed
to carry arbitrarily many closed edges.

The companion file `GridDualIncidence.lean` builds the actual face--dual pair of
the square lattice, which turns the finite-closed-edge hypothesis into genuine
absence of an infinite dual-open cluster.

## Main results

* `FK.PlaneTopology.GridOpenCuts.diamondBall`, `mem_diamondBall_iff`
* `FK.PlaneTopology.GridOpenCuts.orientedCut_diamondBall_subset_diamondCut`
* `FK.PlaneTopology.GridOpenCuts.globalAtMostOne_of_cofinal_diamondCuts`
* `FK.PlaneTopology.GridOpenCuts.globalAtMostOne_of_eventually_open_diamondCuts`
* `FK.PlaneTopology.GridOpenCuts.globalAtMostOne_of_finite_closedEdges`
-/

namespace FK.PlaneTopology.GridOpenCuts

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.CutSeparation
open FK.PlaneTopology.GridFrontier

/-- The set of lattice vertices enclosed by the diamond shell of level `k + 1/2`,
i.e. the lattice vertices of `ℓ¹` level at most `k`. -/
def diamondBall (k : ℕ) : Set GridV := {p | lvl p ≤ k}

lemma mem_diamondBall_iff {k : ℕ} {p : GridV} :
    p ∈ diamondBall k ↔ gridVertex p ∈ diamondInside k := by
  constructor
  · intro h
    have hc : ((lvl p : ℕ) : ℝ) < (k : ℝ) + 1 / 2 := by
      have h' : (lvl p : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      linarith
    rw [diamondInside, Set.mem_ofPred_eq, lvl_cast]
    exact hc
  · intro h
    exact lvl_le_of_mem_inside h

lemma finite_diamondBall (k : ℕ) : (diamondBall k).Finite := by
  refine Set.Finite.subset (finite_gridVertex_preimage_inside k) ?_
  intro p hp
  show gridVertex p ∈ diamondInside k
  rw [diamondInside, Set.mem_ofPred_eq, lvl_cast]
  have h' : (lvl p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp
  linarith

/-- **The oriented cut of a diamond ball is a diamond crossing set.**  Every edge
leaving the `ℓ¹` ball of level `k` joins level `k` to level `k + 1`. -/
theorem orientedCut_diamondBall_subset_diamondCut (k : ℕ) :
    CutSeparation.orientedCut gridGraph (diamondBall k) ⊆ diamondCut k := by
  intro e he
  obtain ⟨u, hu, v, hv, h, rfl⟩ := he
  have hu' : lvl u ≤ k := hu
  have hv' : k < lvl v := by
    have hnk : ¬ lvl v ≤ k := hv
    omega
  rcases lvl_adj h with hstep | hstep
  · have huk : lvl u = k := by omega
    exact mem_diamondCut_of_levels h (Or.inl ⟨huk, by omega⟩)
  · omega

/-- **Cofinally many open diamond shells give the finite open cut separation.**
If for any two prescribed vertices there is a diamond shell of level at least
both levels which is entirely open, then the two vertices are open-connected.
This is the cut form of the `ℓ¹` separator argument, and it is exactly the
hypothesis consumed by `OpenCutSeparation`. -/
theorem globalAtMostOne_of_cofinal_diamondCuts
    {ω : gridGraph.edgeSet → Bool}
    (h : ∀ x y : GridV, ∃ k : ℕ, lvl x ≤ k ∧ lvl y ≤ k ∧
      ∀ e ∈ diamondCut k, ω e = true) :
    GlobalAtMostOne gridGraph ω := by
  apply CutSeparation.globalAtMostOne_of_finite_openCuts_through_labelSet
  intro x y
  obtain ⟨k, hx, hy, hopen⟩ := h x y
  exact ⟨diamondBall k, diamondCut k, finite_diamondBall k, hx, hy,
    orientedCut_diamondBall_subset_diamondCut k, hopen,
    diamondCut_openLabelConnected k hopen⟩

/-- **An eventually open diamond shell suffices**, in the form in which the
finite-closed-edge computation produces it. -/
theorem globalAtMostOne_of_eventually_open_diamondCuts
    {ω : gridGraph.edgeSet → Bool}
    (h : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ e ∈ diamondCut k, ω e = true) :
    GlobalAtMostOne gridGraph ω := by
  obtain ⟨K, hK⟩ := h
  apply globalAtMostOne_of_cofinal_diamondCuts
  intro x y
  refine ⟨max K (max (lvl x) (lvl y)), ?_, ?_, ?_⟩
  · refine le_trans (le_max_left (lvl x) (lvl y)) (le_max_right K (max (lvl x) (lvl y)))
  · refine le_trans (le_max_right (lvl x) (lvl y)) (le_max_right K (max (lvl x) (lvl y)))
  · refine hK _ (le_max_left K (max (lvl x) (lvl y)))

/-- The first vertex of a canonical representative of a lattice edge. -/
noncomputable def edgeFst (e : gridGraph.edgeSet) : GridV := e.1.out.1

/-- The second vertex of a canonical representative of a lattice edge. -/
noncomputable def edgeSnd (e : gridGraph.edgeSet) : GridV := e.1.out.2

lemma edgeFst_adj_edgeSnd (e : gridGraph.edgeSet) : gridAdj (edgeFst e) (edgeSnd e) := by
  have hout : e.1 = s(edgeFst e, edgeSnd e) := (Quot.out_eq e.1).symm
  have h2 : s(edgeFst e, edgeSnd e) ∈ gridGraph.edgeSet := hout ▸ e.2
  rw [SimpleGraph.mem_edgeSet] at h2
  exact h2

lemma edge_eq_mk (e : gridGraph.edgeSet) :
    e = (⟨s(edgeFst e, edgeSnd e), edgeFst_adj_edgeSnd e⟩ : gridGraph.edgeSet) := by
  refine Subtype.ext ?_
  exact (Quot.out_eq e.1).symm

/-- A finite closed edge set is contained in a diamond ball. -/
theorem exists_level_bound_of_finite_closedEdges
    {ω : gridGraph.edgeSet → Bool}
    (hfin : ({e : gridGraph.edgeSet | ω e = false}).Finite) :
    ∃ K : ℕ, ∀ e : gridGraph.edgeSet, ω e = false →
      lvl (edgeFst e) < K ∧ lvl (edgeSnd e) < K := by
  classical
  obtain ⟨t, ht⟩ := hfin.exists_finset_coe
  refine ⟨t.sup (fun e => max (lvl (edgeFst e)) (lvl (edgeSnd e))) + 1, ?_⟩
  intro e he
  have het : e ∈ t := by
    rw [← Finset.mem_coe, ht]
    exact he
  have h1 : lvl (edgeFst e) ≤
      t.sup (fun e => max (lvl (edgeFst e)) (lvl (edgeSnd e))) :=
    le_trans (le_max_left _ _) (Finset.le_sup (f := fun e => max (lvl (edgeFst e)) (lvl (edgeSnd e))) het)
  have h2 : lvl (edgeSnd e) ≤
      t.sup (fun e => max (lvl (edgeFst e)) (lvl (edgeSnd e))) :=
    le_trans (le_max_right _ _) (Finset.le_sup (f := fun e => max (lvl (edgeFst e)) (lvl (edgeSnd e))) het)
  omega

/-- Membership in a crossing set forces the canonical endpoint levels `k` and
`k + 1`. -/
theorem levels_of_mem_diamondCut {k : ℕ} {e : gridGraph.edgeSet}
    (he : e ∈ diamondCut k) :
    (lvl (edgeFst e) = k ∧ lvl (edgeSnd e) = k + 1) ∨
      (lvl (edgeFst e) = k + 1 ∧ lvl (edgeSnd e) = k) := by
  obtain ⟨p, q, hpq, heq, hlev⟩ := he
  have hval' : e.1 = s(p, q) := by simpa using congrArg Subtype.val heq
  have hval : s(edgeFst e, edgeSnd e) = s(p, q) := by
    rw [← hval']
    exact Quot.out_eq e.1
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    rcases hlev with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨b, a⟩
  · rw [h1, h2]
    rcases hlev with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨b, a⟩
    · exact Or.inl ⟨a, b⟩

/-- **Finite closed edge set gives a genuine non-all-open open cut family.**
Only finitely many edges are closed, so every sufficiently large diamond shell
consists of open edges; the cut criterion then joins every pair of vertices. -/
theorem globalAtMostOne_of_finite_closedEdges
    {ω : gridGraph.edgeSet → Bool}
    (hfin : ({e : gridGraph.edgeSet | ω e = false}).Finite) :
    GlobalAtMostOne gridGraph ω := by
  obtain ⟨K, hK⟩ := exists_level_bound_of_finite_closedEdges hfin
  apply globalAtMostOne_of_eventually_open_diamondCuts
  refine ⟨K, fun k hk e he => ?_⟩
  by_contra hc
  have hcfalse : ω e = false := by simpa using hc
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := levels_of_mem_diamondCut he
  · have hb := (hK e hcfalse).1
    omega
  · have hb := (hK e hcfalse).2
    omega


/-! ## Instantiating the geometric separator interface

The geometric interface `FK.PlaneTopology.SeparatorOpenCircuit` /
`HasSeparatorCircuitExhaustion` is stated for an arbitrary two-sided separator.
The next two theorems instantiate it in a **non-all-open** class: a diamond shell
which happens to be open is a separator open circuit, and cofinally many such
shells form a separator circuit exhaustion. -/

/-- A diamond shell consisting of open edges is a `SeparatorOpenCircuit` for the
two-sided `ℓ¹` separation. -/
theorem separatorOpenCircuit_diamond_of_open {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ diamondCut k, ω e = true) :
    SeparatorOpenCircuit gridRealization ω (diamondCut k) (diamondSep k) where
  vertex_off := gridVertex_off_diamond
  crossing := gridRealization_crossing_diamond k
  label_open := hopen
  openConnected := diamondCut_openLabelConnected k hopen

/-- **A genuine non-all-open separator circuit exhaustion.**  If every diamond
shell is open then the diamond shells realize the full geometric exhaustion
interface.  Compared with `hasSeparatorCircuitExhaustion_allOpen` the
configuration is not assumed all-open: only the shells themselves matter. -/
theorem hasSeparatorCircuitExhaustion_of_open_diamondCuts
    {ω : gridGraph.edgeSet → Bool}
    (h : ∀ ρ : ℝ, ∀ e ∈ diamondCut (⌈2 * ρ⌉₊ + 1), ω e = true) :
    HasSeparatorCircuitExhaustion gridRealization ω ((0 : ℝ), (0 : ℝ)) := by
  intro ρ
  exact ⟨diamondCut (⌈2 * ρ⌉₊ + 1), diamondSep (⌈2 * ρ⌉₊ + 1),
    ball_subset_diamondInside ρ, finite_gridVertex_preimage_inside _,
    separatorOpenCircuit_diamond_of_open (h ρ)⟩

end FK.PlaneTopology.GridOpenCuts

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.GridOpenCuts.mem_diamondBall_iff
#print axioms FK.PlaneTopology.GridOpenCuts.orientedCut_diamondBall_subset_diamondCut
#print axioms FK.PlaneTopology.GridOpenCuts.globalAtMostOne_of_cofinal_diamondCuts
#print axioms FK.PlaneTopology.GridOpenCuts.globalAtMostOne_of_eventually_open_diamondCuts
#print axioms FK.PlaneTopology.GridOpenCuts.globalAtMostOne_of_finite_closedEdges
#print axioms FK.PlaneTopology.GridOpenCuts.separatorOpenCircuit_diamond_of_open
#print axioms FK.PlaneTopology.GridOpenCuts.hasSeparatorCircuitExhaustion_of_open_diamondCuts
