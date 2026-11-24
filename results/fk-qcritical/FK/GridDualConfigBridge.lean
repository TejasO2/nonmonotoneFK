import FK.GridDualCofinal
import FK.ConfigurationDuality
import FK.PlaneClusterTarget

/-!
# The closed-cell graph is the dual configuration of `gridCrossEquiv`

`FK.PlaneTopology.GridBoxCrossing` and `FK.PlaneTopology.GridCofinalCrossing`
work with closed *primal* bonds on the lattice of cells.  This file identifies
that graph with the ordinary dual configuration `dualConfig gridCrossEquiv ω` of
`FK.ConfigurationDuality` on the genuine face lattice `gridDual`: two adjacent
cells are joined by a closed step exactly when the dual edge crossing their
common side is open.

Consequently "every component of the closed-cell graph is finite" is exactly
non-percolation of the dual configuration, and the cofinal-crossing theorem of
`FK.PlaneTopology.GridCofinalCrossing` can be phrased in the repository's
percolation language.
-/

namespace FK.PlaneTopology.GridDualConfigBridge

open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PrimalClosedDuality
open FK.PlaneTopology.GridCofinalCrossing
open FK.PlaneTopology.BoxSeamBridge
open FK.Configuration
open CurvatureVariance.Infra.Percolation

attribute [local instance] Classical.propDecidable

variable {ω : gridGraph.edgeSet → Bool}

lemma uncrossLo_lt_uncrossHi {f g : GridV} (h : gridAdj f g) :
    bondClosed ω (uncrossLo f g) (uncrossHi f g) ↔
      CellClosedAdj ω f g := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · -- same column, `g` strictly below `f`
    have hl : uncrossLo f g = (min f.1 g.1, min f.2 g.2 + 1) := uncrossLo_vert h1 (Or.inl h2)
    have hh : uncrossHi f g = (min f.1 g.1 + 1, min f.2 g.2 + 1) :=
      uncrossHi_vert h1 (Or.inl h2)
    have hm1 : min f.1 g.1 = g.1 := by omega
    have hm2 : min f.2 g.2 = g.2 := by omega
    rw [hl, hh, hm1, hm2]
    constructor
    · intro hb
      exact Or.inr ⟨h1.symm, Or.inr (by omega), by convert hb using 2 <;> omega⟩
    · rintro (⟨-, hc, -⟩ | ⟨-, hc, hb⟩)
      · omega
      · convert hb using 2 <;> omega
  · -- same column, `f` strictly below `g`
    have hl : uncrossLo f g = (min f.1 g.1, min f.2 g.2 + 1) := uncrossLo_vert h1 (Or.inr h2)
    have hh : uncrossHi f g = (min f.1 g.1 + 1, min f.2 g.2 + 1) :=
      uncrossHi_vert h1 (Or.inr h2)
    have hm1 : min f.1 g.1 = f.1 := by omega
    have hm2 : min f.2 g.2 = f.2 := by omega
    rw [hl, hh, hm1, hm2]
    constructor
    · intro hb
      exact Or.inr ⟨h1.symm, Or.inl (by omega), by convert hb using 2 <;> omega⟩
    · rintro (⟨-, hc, -⟩ | ⟨-, hc, hb⟩)
      · omega
      · convert hb using 2 <;> omega
  · -- same row, `g` strictly left of `f`
    have hl : uncrossLo f g = (min f.1 g.1 + 1, min f.2 g.2) := uncrossLo_horiz h1 (Or.inl h2)
    have hh : uncrossHi f g = (min f.1 g.1 + 1, min f.2 g.2 + 1) :=
      uncrossHi_horiz h1 (Or.inl h2)
    have hm1 : min f.1 g.1 = g.1 := by omega
    have hm2 : min f.2 g.2 = g.2 := by omega
    rw [hl, hh, hm1, hm2]
    constructor
    · intro hb
      exact Or.inl ⟨h1.symm, Or.inr (by omega), by convert hb using 2 <;> omega⟩
    · rintro (⟨-, hc, hb⟩ | ⟨-, hc, -⟩)
      · convert hb using 2 <;> omega
      · omega
  · -- same row, `f` strictly left of `g`
    have hl : uncrossLo f g = (min f.1 g.1 + 1, min f.2 g.2) := uncrossLo_horiz h1 (Or.inr h2)
    have hh : uncrossHi f g = (min f.1 g.1 + 1, min f.2 g.2 + 1) :=
      uncrossHi_horiz h1 (Or.inr h2)
    have hm1 : min f.1 g.1 = f.1 := by omega
    have hm2 : min f.2 g.2 = f.2 := by omega
    rw [hl, hh, hm1, hm2]
    constructor
    · intro hb
      exact Or.inl ⟨h1.symm, Or.inl (by omega), by convert hb using 2 <;> omega⟩
    · rintro (⟨-, hc, hb⟩ | ⟨-, hc, -⟩)
      · convert hb using 2 <;> omega
      · omega

/-- **Pointwise bridge.**  Two adjacent cells of the lattice are joined by a
closed cell step exactly when the dual edge crossing their common side is open
in the dual configuration `dualConfig gridCrossEquiv ω`. -/
theorem cellClosedAdj_iff_dualConfig {f g : GridV} (h : gridAdj f g) :
    CellClosedAdj ω f g ↔
      (dualConfig gridCrossEquiv ω (⟨s(f, g), h⟩ : gridDual.edgeSet) = true) := by
  have hb := uncrossLo_lt_uncrossHi (ω := ω) h
  have he : gridCrossEquiv.symm (⟨s(f, g), h⟩ : gridDual.edgeSet) =
      (⟨s(uncrossLo f g, uncrossHi f g), (show gridGraph.Adj (uncrossLo f g) (uncrossHi f g) from gridAdj_uncross h)⟩ :
        gridGraph.edgeSet) := rfl
  rw [← hb, dualConfig, he]
  cases hv : ω (⟨s(uncrossLo f g, uncrossHi f g), (show gridGraph.Adj (uncrossLo f g) (uncrossHi f g) from gridAdj_uncross h)⟩ :
      gridGraph.edgeSet) with
  | true => simp [bondClosed_iff (gridAdj_uncross h), hv]
  | false => simp [bondClosed_iff (gridAdj_uncross h), hv]

/-! ## Component-level identification with the dual configuration -/

/-- A closed cell step is a lattice step of the face lattice. -/
lemma gridAdj_of_cellClosedAdj {f g : GridV} (h : CellClosedAdj ω f g) : gridAdj f g := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩

/-- The closed cell graph of the lattice as a subgraph of the face lattice. -/
def cellClosedGraph_hom : cellClosedGraph ω →g gridDual where
  toFun := id
  map_rel' := fun h => gridAdj_of_cellClosedAdj h

lemma isOpenIn_map_cellClosed {f g : GridV} (w : (cellClosedGraph ω).Walk f g) :
    IsOpenIn (dualConfig gridCrossEquiv ω) Set.univ
      (w.map (cellClosedGraph_hom (ω := ω))) := by
  induction w with
  | nil => exact isOpenIn_nil
  | @cons a b c hstep rest ih =>
    rw [SimpleGraph.Walk.map_cons]
    refine isOpenIn_cons.mpr ⟨⟨Set.mem_univ _, ?_⟩, ih⟩
    have hbridge := (cellClosedAdj_iff_dualConfig (ω := ω) (gridAdj_of_cellClosedAdj hstep)).mp hstep
    exact hbridge

/-- Closed cell reachability implies openness in the dual configuration. -/
theorem openConnected_of_cellReach {f g : GridV}
    (h : (cellClosedGraph ω).Reachable f g) :
    OpenConnected gridDual (dualConfig gridCrossEquiv ω) Set.univ f g := by
  obtain ⟨w⟩ := h
  exact ⟨w.map (cellClosedGraph_hom (ω := ω)), isOpenIn_map_cellClosed w⟩

/-- An open dual walk is a closed cell walk. -/
lemma cellReach_of_isOpenIn {f g : GridV} (p : gridDual.Walk f g)
    (hp : IsOpenIn (dualConfig gridCrossEquiv ω) Set.univ p) :
    (cellClosedGraph ω).Reachable f g := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons a b c hstep rest ih =>
    rw [isOpenIn_cons] at hp
    have hedge : CellClosedAdj ω a b :=
      (cellClosedAdj_iff_dualConfig (ω := ω) hstep).mpr hp.1.2
    obtain ⟨w'⟩ := ih hp.2
    exact ⟨SimpleGraph.Walk.cons hedge w'⟩

/-- Openness in the dual configuration implies closed cell reachability. -/
theorem cellReach_of_openConnected {f g : GridV}
    (h : OpenConnected gridDual (dualConfig gridCrossEquiv ω) Set.univ f g) :
    (cellClosedGraph ω).Reachable f g := by
  obtain ⟨p, hp⟩ := h
  exact cellReach_of_isOpenIn p hp

/-- **Component-level identification.**  Closed cell reachability in the lattice
of cells is exactly connection in the dual configuration of the primal
configuration under `gridCrossEquiv`. -/
theorem cellReach_iff_openConnected {f g : GridV} :
    (cellClosedGraph ω).Reachable f g ↔
      OpenConnected gridDual (dualConfig gridCrossEquiv ω) Set.univ f g :=
  ⟨openConnected_of_cellReach, cellReach_of_openConnected⟩

/-- Every connected component of the closed cell graph is finite exactly when the
dual configuration does not percolate. -/
theorem noInfiniteOpenCluster_iff_cellClosed :
    FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω) ↔
      ∀ f : GridV, {g | (cellClosedGraph ω).Reachable f g}.Finite := by
  constructor
  · intro h f
    refine Set.Finite.subset (h f) ?_
    intro g hg
    exact cellReach_iff_openConnected.mp hg
  · intro h x
    refine Set.Finite.subset (h x) ?_
    intro g hg
    exact cellReach_iff_openConnected.mpr hg

/-- **Cofinal open primal crossings from dual non-percolation**, in the
repository's percolation language: if the dual configuration
`dualConfig gridCrossEquiv ω` has no infinite open cluster, then for every fixed
width `k` and all sufficiently large heights `n` the primal configuration has an
open left-right crossing of the vertex box `[0,k+1] × [0,n]`. -/
theorem primalOpenCrossing_cofinally_of_noInfiniteOpenCluster
    (h : FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω)) (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → PrimalOpenCrossing ω k n :=
  primalOpenCrossing_cofinally (fun f => noInfiniteOpenCluster_iff_cellClosed.mp h f) k

end FK.PlaneTopology.GridDualConfigBridge

#print axioms FK.PlaneTopology.GridDualConfigBridge.uncrossLo_lt_uncrossHi
#print axioms FK.PlaneTopology.GridDualConfigBridge.cellClosedAdj_iff_dualConfig
#print axioms FK.PlaneTopology.GridDualConfigBridge.cellReach_iff_openConnected
#print axioms FK.PlaneTopology.GridDualConfigBridge.noInfiniteOpenCluster_iff_cellClosed
#print axioms FK.PlaneTopology.GridDualConfigBridge.primalOpenCrossing_cofinally_of_noInfiniteOpenCluster
