import FK.GridDualIncidence
import FK.FiniteOpenEdges
import FK.OpenCutSeparation

/-!
# The planar target on the square lattice: verified instances and an obstruction

`FK.PlaneClusterTarget` records the unproved deterministic target

`FK.Planar.DualNonpercolationForcesPrimalAtMostOne G GD edge`:
absence of an infinite dual-open cluster forces at most one infinite primal-open
cluster.  This file connects the two halves built in `GridOpenCuts` and
`GridDualIncidence`:

* the dual-open edges of the square lattice are exactly the images of the
  primal-closed edges under the exact face--dual edge equivalence, so a
  configuration with finitely many closed edges satisfies the dual
  nonpercolation hypothesis;
* for such configurations at most one infinite primal-open cluster follows from
  the `ℓ¹` diamond open cuts, giving a genuine non-all-open instance of the
  target;
* **obstruction.**  There is a configuration with no infinite dual-open cluster
  whose *every* diamond shell carries a closed edge.  Hence dual nonpercolation
  does not imply the cofinal-all-open-diamond-cut hypothesis, and the fixed
  `ℓ¹` level-set geometry cannot prove the general target: the separating
  circuit has to be configuration-dependent.

## Main results

* `FK.PlaneTopology.PlanarTarget.dual_openSet_eq_image_closed`
* `FK.PlaneTopology.PlanarTarget.noInfiniteOpenCluster_dual_of_finite_closedEdges`
* `FK.PlaneTopology.PlanarTarget.dualNonpercolation_imp_atMostOne_of_finite_closedEdges`
* `FK.PlaneTopology.PlanarTarget.dualNonpercolationForcesPrimalAtMostOne_of_finite_closedEdges`
* `FK.PlaneTopology.PlanarTarget.exists_dualNonpercolating_noOpenDiamondCut`
-/

namespace FK.PlaneTopology.PlanarTarget

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridOpenCuts
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.FiniteOpenEdges

/-! ## The dual-open set is the image of the primal-closed set -/

/-- **Exact complementarity.**  Under the face--dual edge equivalence, the
dual-open edges are precisely the images of the primal-closed edges. -/
theorem dual_openSet_eq_image_closed (ω : gridGraph.edgeSet → Bool) :
    {f : gridDual.edgeSet | dualConfig gridCrossEquiv ω f = true}
      = gridCrossEquiv '' {e : gridGraph.edgeSet | ω e = false} := by
  ext f
  constructor
  · intro hf
    refine ⟨gridCrossEquiv.symm f, ?_, gridCrossEquiv.apply_symm_apply f⟩
    have h : !(ω (gridCrossEquiv.symm f)) = true := hf
    simpa using h
  · rintro ⟨e, he, rfl⟩
    have h : !(ω (gridCrossEquiv.symm (gridCrossEquiv e))) = true := by
      rw [Equiv.symm_apply_apply, he]
      rfl
    simpa [dualConfig] using h

/-- **Dual nonpercolation from a finite closed edge set.** -/
theorem noInfiniteOpenCluster_dual_of_finite_closedEdges
    {ω : gridGraph.edgeSet → Bool}
    (hfin : ({e : gridGraph.edgeSet | ω e = false}).Finite) :
    FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) := by
  intro x
  refine noInfiniteOpenCluster_of_finite_openEdges ?_ x
  rw [dual_openSet_eq_image_closed]
  exact hfin.image _

/-- **The verified non-all-open instance of the planar target.**  A square
lattice configuration with finitely many closed edges has no infinite dual-open
cluster and at most one infinite primal-open cluster. -/
theorem dualNonpercolation_imp_atMostOne_of_finite_closedEdges
    {ω : gridGraph.edgeSet → Bool}
    (hfin : ({e : gridGraph.edgeSet | ω e = false}).Finite) :
    FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) ∧
      GlobalAtMostOne gridGraph ω :=
  ⟨noInfiniteOpenCluster_dual_of_finite_closedEdges hfin,
    globalAtMostOne_of_finite_closedEdges hfin⟩

/-- The implication form of the previous instance, matching the shape of the
recorded target `FK.Planar.DualNonpercolationForcesPrimalAtMostOne`. -/
theorem dualNonpercolationForcesPrimalAtMostOne_of_finite_closedEdges
    (ω : gridGraph.edgeSet → Bool)
    (hfin : ({e : gridGraph.edgeSet | ω e = false}).Finite) :
    FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) →
      GlobalAtMostOne gridGraph ω :=
  fun _ => globalAtMostOne_of_finite_closedEdges hfin

/-! ## Components of a configuration with unique incident open edges

The obstruction below has a dual-open set which is a matching: no two of its
edges share a face.  The next combinatorial lemma turns that into finiteness of
all open components. -/

/-- **A configuration whose open edges are uniquely incident is subcritical.**
If any two open edges sharing a vertex coincide, then in a locally finite graph
every open component is finite: an open walk can use at most one edge at each of
its vertices, so it cannot travel. -/
theorem finite_openComponent_of_unique_incident {V : Type*} {G : SimpleGraph V}
    {ω : G.edgeSet → Bool}
    (hun : ∀ (v : V) (e f : G.edgeSet), (∃ w, e.1 = s(v, w)) →
      (∃ w, f.1 = s(v, w)) → ω e = true → ω f = true → e = f)
    (hfin : ∀ v : V, (G.neighborSet v).Finite) (x : V) :
    {y : V | OpenConnected G ω Set.univ x y}.Finite := by
  classical
  have key : ∀ {a b : V}, (q : G.Walk a b) → IsOpenIn ω Set.univ q →
      b = a ∨ (G.Adj a b ∧ ∃ h : G.Adj a b, ω ⟨s(a, b), h⟩ = true) := by
    intro a b q
    induction q with
    | nil => intro _; exact Or.inl rfl
    | @cons a m c ham r ih =>
        intro hq
        obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hq
        obtain ⟨hhead, hopenhead⟩ : ∃ h : G.Adj a m,
            ω (⟨s(a, m), h⟩ : G.edgeSet) = true := ⟨ham, hopen⟩
        rcases ih hrest with hc | ⟨hmc, h', hopen'⟩
        · -- c = m : the head edge is the required edge at `a`
          subst hc
          exact Or.inr ⟨ham, ⟨ham, hopenhead⟩⟩
        · -- two open edges at `m` coincide, so the walk folds back
          have heq : (⟨s(a, m), ham⟩ : G.edgeSet) = ⟨s(m, c), hmc⟩ :=
            hun m _ _ ⟨a, Sym2.eq_swap⟩ ⟨c, rfl⟩ hopenhead hopen'
          have hval : s(a, m) = s(m, c) := congrArg Subtype.val heq
          rcases Sym2.eq_iff.mp hval with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact absurd h1 ham.ne
          · exact Or.inl h1.symm
  have hsub : {y : V | OpenConnected G ω Set.univ x y} ⊆ insert x (G.neighborSet x) := by
    intro y hy
    obtain ⟨p, hp⟩ := hy
    rcases key p hp with h | ⟨hadj, -⟩
    · exact Or.inl h
    · exact Or.inr hadj
  exact (hfin x).insert x |>.subset hsub

/-! ## The obstruction: dual nonpercolation without open diamond shells -/

/-- The `k`-th horizontal lattice edge on the positive `x`-axis. -/
def staircaseEdge (k : ℕ) : gridGraph.edgeSet :=
  ⟨s(((k : ℤ), 0), ((k : ℤ) + 1, 0)), gridAdj_fst_add (k : ℤ) 0⟩

/-- The face--dual edge crossing the `k`-th staircase edge: a single edge in the
face lattice around the face `(k, -1)`. -/
def dualStaircaseEdge (k : ℕ) : gridGraph.edgeSet :=
  ⟨s(((k : ℤ), -1), ((k : ℤ), 0)),
    Or.inl ⟨rfl, Or.inr (by simp)⟩⟩

/-- The configuration closing exactly the staircase edges. -/
noncomputable def staircaseConfig : gridGraph.edgeSet → Bool :=
  fun e => if ∃ k : ℕ, e = staircaseEdge k then false else true

lemma staircaseConfig_closed_iff (e : gridGraph.edgeSet) :
    staircaseConfig e = false ↔ ∃ k : ℕ, e = staircaseEdge k := by
  unfold staircaseConfig
  by_cases h : ∃ k : ℕ, e = staircaseEdge k
  · simp [h]
  · simp [h]

lemma lvl_staircase_lo (k : ℕ) : lvl (((k : ℤ), (0 : ℤ)) : GridV) = k := by
  simp [lvl, Int.natAbs_natCast]

lemma lvl_staircase_hi (k : ℕ) : lvl ((((k : ℤ) + 1), (0 : ℤ)) : GridV) = k + 1 := by
  simp only [lvl, natAbs_add_one_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) by positivity),
    Int.natAbs_natCast, Int.natAbs_zero]


lemma staircaseEdge_mem_diamondCut (k : ℕ) : staircaseEdge k ∈ diamondCut k := by
  unfold staircaseEdge
  exact mem_diamondCut_of_levels (gridAdj_fst_add (k : ℤ) 0)
    (Or.inl ⟨lvl_staircase_lo k, lvl_staircase_hi k⟩)

/-- Every diamond shell carries a closed edge of the staircase configuration. -/
theorem exists_closed_mem_diamondCut (k : ℕ) :
    ∃ e ∈ diamondCut k, staircaseConfig e = false :=
  ⟨staircaseEdge k, staircaseEdge_mem_diamondCut k,
    (staircaseConfig_closed_iff _).mpr ⟨k, rfl⟩⟩

/-- The face--dual edge crossing a staircase edge. -/
lemma crossEdge_staircaseEdge (k : ℕ) :
    crossEdge (staircaseEdge k) = dualStaircaseEdge k := by
  unfold staircaseEdge dualStaircaseEdge
  rw [crossEdge_apply_mk]
  refine Subtype.ext ?_
  simp only [crossPair]
  rw [dualLo_horiz (p := ((k : ℤ), (0 : ℤ))) (q := ((k : ℤ) + 1, (0 : ℤ)))
      rfl (Or.inr (by simp)),
    dualHi_horiz (p := ((k : ℤ), (0 : ℤ))) (q := ((k : ℤ) + 1, (0 : ℤ)))
      rfl (Or.inr (by simp))]
  have hm : min ((k : ℤ)) ((k : ℤ) + 1) = (k : ℤ) := by omega
  rw [hm, show ((0 : ℤ) - 1) = -1 by norm_num]

/-- The dual-open edges of the staircase configuration share no face: distinct
staircase edges have disjoint sets of face endpoints. -/
lemma dualStaircaseEdge_no_shared_face {j k : ℕ} {v : GridV}
    (hv : v = ((k : ℤ), -1) ∨ v = ((k : ℤ), 0))
    (hw : v = ((j : ℤ), -1) ∨ v = ((j : ℤ), 0)) : j = k := by
  rcases hv with rfl | rfl <;> rcases hw with h | h <;>
    simp only [Prod.mk.injEq] at h <;> omega

/-- **Uniqueness of the incident dual-open edge** for the staircase
configuration. -/
theorem staircase_unique_incident (v : GridV) (e f : gridDual.edgeSet)
    (he : ∃ w, e.1 = s(v, w)) (hf : ∃ w, f.1 = s(v, w))
    (hoe : dualConfig gridCrossEquiv staircaseConfig e = true)
    (hof : dualConfig gridCrossEquiv staircaseConfig f = true) : e = f := by
  -- read `e` and `f` as dual images of closed staircase edges
  have key : ∀ (g : gridDual.edgeSet),
      dualConfig gridCrossEquiv staircaseConfig g = true →
      ∃ j : ℕ, g = dualStaircaseEdge j := by
    intro g hg
    have hclosed : ∃ k : ℕ, gridCrossEquiv.symm g = staircaseEdge k := by
      refine (staircaseConfig_closed_iff _).mp ?_
      have h : !(staircaseConfig (gridCrossEquiv.symm g)) = true := hg
      simpa using h
    obtain ⟨k, hk⟩ := hclosed
    refine ⟨k, ?_⟩
    have hg' : gridCrossEquiv (staircaseEdge k) = g := by
      rw [← hk]
      exact Equiv.apply_symm_apply gridCrossEquiv g |>.symm ▸ rfl
    rw [← hg']
    exact crossEdge_staircaseEdge k
  obtain ⟨j, rfl⟩ := key e hoe
  obtain ⟨k, rfl⟩ := key f hof
  -- both edges contain `v`
  obtain ⟨w₁, hw₁⟩ := he
  obtain ⟨w₂, hw₂⟩ := hf
  have hvj : v = ((j : ℤ), -1) ∨ v = ((j : ℤ), 0) := by
    simp only [dualStaircaseEdge] at hw₁
    rcases Sym2.eq_iff.mp hw₁ with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  have hvk : v = ((k : ℤ), -1) ∨ v = ((k : ℤ), 0) := by
    simp only [dualStaircaseEdge] at hw₂
    rcases Sym2.eq_iff.mp hw₂ with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  have hjk := dualStaircaseEdge_no_shared_face hvj hvk
  subst hjk
  rfl

/-- **The staircase configuration has no infinite dual-open cluster.** -/
theorem staircase_dual_nonpercolation :
    FK.Planar.NoInfiniteOpenCluster gridDual
      (dualConfig gridCrossEquiv staircaseConfig) := by
  intro x
  exact finite_openComponent_of_unique_incident
    (fun v e f he hf hoe hof => staircase_unique_incident v e f he hf hoe hof)
    (fun v => finite_neighborSet v) x

/-- **The obstruction.**  There is a square lattice configuration with no
infinite dual-open cluster on which every `ℓ¹` diamond shell carries a closed
edge.  Consequently dual nonpercolation does not imply the cofinal
all-open-diamond-cut hypothesis: the separating circuit in the general planar
argument cannot be a fixed level set of the `ℓ¹` norm. -/
theorem exists_dualNonpercolating_noOpenDiamondCut :
    ∃ ω : gridGraph.edgeSet → Bool,
      FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) ∧
        ∀ k : ℕ, ∃ e ∈ diamondCut k, ω e = false :=
  ⟨staircaseConfig, staircase_dual_nonpercolation, exists_closed_mem_diamondCut⟩

end FK.PlaneTopology.PlanarTarget

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.PlanarTarget.dual_openSet_eq_image_closed
#print axioms FK.PlaneTopology.PlanarTarget.noInfiniteOpenCluster_dual_of_finite_closedEdges
#print axioms FK.PlaneTopology.PlanarTarget.dualNonpercolation_imp_atMostOne_of_finite_closedEdges
#print axioms FK.PlaneTopology.PlanarTarget.dualNonpercolationForcesPrimalAtMostOne_of_finite_closedEdges
#print axioms FK.PlaneTopology.PlanarTarget.finite_openComponent_of_unique_incident
#print axioms FK.PlaneTopology.PlanarTarget.staircase_dual_nonpercolation
#print axioms FK.PlaneTopology.PlanarTarget.exists_dualNonpercolating_noOpenDiamondCut
