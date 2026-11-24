import FK.GridBoxCrossing

/-!
# From non-percolation of the closed cell graph to cofinal primal crossings

`FK.PlaneTopology.GridBoxCrossing` proves the un-collapsed finite box duality:
an open primal left-right crossing of the vertex box `[0,k+1] × [0,n]` exists
exactly when the genuine cell box has no closed cell walk from the exterior row
`j = -1` to the exterior row `j = n`.

Here the cell box is glued into the *global* closed-cell graph on all cells
`ℤ × ℤ` (two cells are adjacent when their common side is a closed primal
bond).  The main result is a genuine compactness/pigeonhole step:

* `row_zero_of_walk` — a closed cell walk from row `-1` up to row `n ≥ 0` passes
  through a cell of row `0` (discrete intermediate value property).
* `infinite_component_of_forall_dualBoxCrossing` — if for a fixed width `k` the
  cell box has a closed crossing at *every* height `n`, then the global
  closed-cell graph has an infinite connected component.
* `primalOpenCrossing_cofinally` — consequently, if every connected component of
  the global closed-cell graph is finite, then for every fixed width `k` and all
  sufficiently large heights `n` the primal configuration has an open
  left-right crossing of `[0,k+1] × [0,n]`.

This is the deterministic input the planar uniqueness argument needs in order to
produce cofinally many open primal crossings out of dual non-percolation.  It is
not `GlobalAtMostOne`, Theorem 1.11, or any probabilistic statement.
-/

namespace FK.PlaneTopology.GridCofinalCrossing

open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PrimalClosedDuality
open FK.PlaneTopology.BoxSeamBridge
open FK.PlaneTopology.GridBoxCrossing

attribute [local instance] Classical.propDecidable

variable {k n : ℕ} {ω : gridGraph.edgeSet → Bool}

/-! ## 1. The global closed-cell graph -/

/-- Two cells of the lattice are joined by a **closed step** when their common
side is a closed primal bond. -/
def CellClosedAdj (ω : gridGraph.edgeSet → Bool) (f g : GridV) : Prop :=
  CellClosed ω f.1 f.2 g.1 g.2

lemma CellClosedAdj_comm {f g : GridV} (h : CellClosedAdj ω f g) : CellClosedAdj ω g f :=
  CellClosed_comm h

lemma CellClosedAdj_irrefl (f : GridV) : ¬ CellClosedAdj ω f f := by
  rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> omega

/-- The closed-bond dual graph on the whole lattice of cells. -/
noncomputable def cellClosedGraph (ω : gridGraph.edgeSet → Bool) : SimpleGraph GridV where
  Adj := CellClosedAdj ω
  symm := ⟨fun _ _ h => CellClosedAdj_comm h⟩
  loopless := ⟨fun f h => CellClosedAdj_irrefl f h⟩

/-- The closed cell graph restricted to a box is contained in the global one. -/
lemma DCellStep_cellClosedAdj {f g : DCell k n} (h : DCellStep ω k n f g) :
    CellClosedAdj ω f.1 g.1 := by
  rcases h with ⟨h1, h2, -, -, h5⟩ | ⟨h1, h2, -, -, h5⟩
  · exact Or.inl ⟨h1, h2, h5⟩
  · exact Or.inr ⟨h1, h2, h5⟩

/-- Row displacements of a closed cell step. -/
lemma DCellStep_row_bounds {f g : DCell k n} (h : DCellStep ω k n f g) :
    g.1.2 ≤ f.1.2 + 1 ∧ f.1.2 ≤ g.1.2 + 1 := by
  rcases h with ⟨h1, -, -, -, -⟩ | ⟨-, h2, -, -, -⟩
  · omega
  · omega

/-! ## 2. Discrete intermediate value along a cell walk -/

/-- Rows along a closed cell walk cover every intermediate value: the discrete
intermediate value property. -/
theorem exists_row_of_walk {f g : DCell k n} (w : (dCellGraph ω k n).Walk f g)
    {m : ℤ} (hm1 : f.1.2 ≤ m) (hm2 : m ≤ g.1.2) :
    ∃ u : DCell k n, (dCellGraph ω k n).Reachable f u ∧ u.1.2 = m := by
  induction w with
  | nil =>
    exact ⟨_, ⟨SimpleGraph.Walk.nil⟩, by omega⟩
  | @cons a b c hstep rest ih =>
    have hrow := DCellStep_row_bounds hstep
    by_cases hcase : m ≤ b.1.2
    · rcases eq_or_lt_of_le hcase with heq | hlt
      · exact ⟨b, ⟨SimpleGraph.Walk.cons hstep
          (SimpleGraph.Walk.nil : (dCellGraph ω k n).Walk b b)⟩, heq.symm⟩
      · exact ⟨a, ⟨(SimpleGraph.Walk.nil : (dCellGraph ω k n).Walk a a)⟩, by omega⟩
    · obtain ⟨u, hu, hu0⟩ := ih (by omega) (by omega)
      obtain ⟨w'⟩ := hu
      exact ⟨u, ⟨SimpleGraph.Walk.cons hstep w'⟩, hu0⟩

/-- A closed cell walk from the exterior row `-1` to a cell of row `≥ 0` passes
through a cell of row `0` which is reachable from its starting cell. -/
theorem row_zero_of_walk {f g : DCell k n}
    (w : (dCellGraph ω k n).Walk f g) (hf : f.1.2 = -1) (hg : 0 ≤ g.1.2) :
    ∃ u : DCell k n, (dCellGraph ω k n).Reachable f u ∧ u.1.2 = 0 := by
  exact exists_row_of_walk w (by omega) (by omega)

/-! ## 3. Bounded components cannot carry crossings at all heights -/

/-- The cell box embedded in the global closed-cell graph. -/
noncomputable def DCellHomGlobal : dCellGraph ω k n →g cellClosedGraph ω where
  toFun := fun f => f.1
  map_rel' := fun h => DCellStep_cellClosedAdj h

/-- The cell of row zero in column `i`. -/
def rowZeroCell (i : Fin (k + 1)) : GridV := (((i : ℕ) : ℤ), 0)

/-- Enlarging the box in the vertical direction embeds its vertex set. -/
def castBox {n n' : ℕ} (h : n ≤ n') (v : BVert k n) : BVert k n' :=
  ⟨v.1, by
    have hv := v.2
    simp only [inBox] at hv ⊢
    omega⟩

lemma castBox_fst {n n' : ℕ} (h : n ≤ n') (v : BVert k n) :
    (castBox (k := k) h v).1 = v.1 := rfl

/-- The primal open graph of the smaller box is a subgraph of the larger one. -/
def primalGraph_castBox {n n' : ℕ} (h : n ≤ n') :
    primalGraph ω k n →g primalGraph ω k n' where
  toFun := castBox (k := k) h
  map_rel' := fun {_ _} hab => hab

/-- Open left-right crossings are monotone in the height of the box. -/
theorem primalOpenCrossing_mono {m m' : ℕ} (h : m ≤ m')
    (hp : PrimalOpenCrossing ω k m) : PrimalOpenCrossing ω k m' := by
  obtain ⟨u, v, hu, hv, ⟨w⟩⟩ := hp
  refine ⟨castBox (k := k) h u, castBox (k := k) h v, ?_, ?_, ?_⟩
  · show (castBox (k := k) h u).1.1 = 0
    rw [castBox_fst]; exact hu
  · show (castBox (k := k) h v).1.1 = (k : ℤ) + 1
    rw [castBox_fst]; exact hv
  · exact ⟨w.map (primalGraph_castBox (ω := ω) h)⟩

/-- **Pigeonhole step.**  If for a fixed width `k` the closed cell box has a
crossing from row `-1` to row `n` for *every* positive height `n`, then the
global closed-cell graph has an infinite connected component.  Otherwise the
finitely many components of the row-zero cells would have a bounded height,
contradicting the row-zero intermediate value property of a crossing of larger
height. -/
theorem infinite_component_of_forall_dualBoxCrossing
    (h : ∀ n : ℕ, 0 < n → DualBoxCrossing ω k n) :
    ∃ f : GridV, {g | (cellClosedGraph ω).Reachable f g}.Infinite := by
  by_contra hcon
  push Not at hcon
  have hcomp : ∀ i : Fin (k + 1),
      {g : GridV | (cellClosedGraph ω).Reachable (rowZeroCell i) g}.Finite :=
    fun i => hcon (rowZeroCell i)
  have hne : ∀ i : Fin (k + 1), (hcomp i).toFinset.Nonempty := by
    intro i
    exact ⟨rowZeroCell i, (Set.Finite.mem_toFinset (hcomp i)).mpr (SimpleGraph.Reachable.refl _)⟩
  let ρ : Fin (k + 1) → ℤ := fun i =>
    (hcomp i).toFinset.sup' (hne i) (fun g => g.2)
  have hρle : ∀ (i : Fin (k + 1)) {g : GridV},
      (cellClosedGraph ω).Reachable (rowZeroCell i) g → g.2 ≤ ρ i := by
    intro i g hg
    exact Finset.le_sup' (s := (hcomp i).toFinset) (fun g => g.2)
      ((Set.Finite.mem_toFinset (hcomp i)).mpr hg)
  let N : ℤ := Finset.univ.sup' Finset.univ_nonempty ρ
  have hNle : ∀ i : Fin (k + 1), ρ i ≤ N := by
    intro i
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin (k + 1)))) (f := ρ) (Finset.mem_univ i)
  -- a height exceeding every component of a row-zero cell
  have hmax : N ≤ max N 0 := le_max_left _ _
  have hMnn : (0 : ℤ) ≤ max N 0 := le_max_right _ _
  have hM : (((max N 0).toNat : ℕ) : ℤ) = max N 0 := Int.toNat_of_nonneg hMnn
  have hcastN : (((((max N 0).toNat + 1 : ℕ)) : ℤ)) = max N 0 + 1 := by
    rw [Nat.cast_add, Nat.cast_one, hM]
  obtain ⟨f, g, hf, hg, hreach⟩ := h ((max N 0).toNat + 1) (Nat.succ_pos _)
  obtain ⟨w⟩ := hreach
  have hg0 : (0 : ℤ) ≤ g.1.2 := by rw [hg]; exact Int.natCast_nonneg _
  obtain ⟨u, hu, hu0⟩ := row_zero_of_walk w hf hg0
  have hglob_u : (cellClosedGraph ω).Reachable f.1 u.1 := by
    obtain ⟨wu⟩ := hu
    exact ⟨wu.map (DCellHomGlobal (ω := ω))⟩
  have hglob_g : (cellClosedGraph ω).Reachable f.1 g.1 := ⟨w.map (DCellHomGlobal (ω := ω))⟩
  have hug : (cellClosedGraph ω).Reachable u.1 g.1 :=
    (SimpleGraph.Reachable.symm hglob_u).trans hglob_g
  have hcol : u.1.1 = ((u.1.1.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg u.fst_nonneg).symm
  have hlt : u.1.1.toNat < k + 1 := u.fst_toNat_lt
  set i : Fin (k + 1) := ⟨u.1.1.toNat, hlt⟩ with hi
  have hu1 : u.1 = rowZeroCell i := by
    refine Prod.ext ?_ ?_
    · show u.1.1 = ((u.1.1.toNat : ℕ) : ℤ)
      exact hcol
    · show u.1.2 = 0
      exact hu0
  rw [hu1] at hug
  have h1 : g.1.2 ≤ ρ i := hρle i hug
  have h2 : ρ i ≤ N := hNle i
  have hg' : g.1.2 = ((((max N 0).toNat + 1 : ℕ)) : ℤ) := hg
  omega

/-- **Cofinal primal open crossings from dual non-percolation.**  If every
connected component of the global closed-cell graph is finite, then for every
fixed width `k` and all sufficiently large heights `n`, the primal
configuration has an open left-right crossing of the vertex box
`[0,k+1] × [0,n]`. -/
theorem primalOpenCrossing_cofinally
    (hfin : ∀ f : GridV, {g | (cellClosedGraph ω).Reachable f g}.Finite) (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → PrimalOpenCrossing ω k n := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ m : ℕ, ¬ PrimalOpenCrossing ω k m := by
    intro m hpm
    obtain ⟨n, hmn, hn⟩ := hcon m
    exact hn (primalOpenCrossing_mono hmn hpm)
  have hcross : ∀ n : ℕ, 0 < n → DualBoxCrossing ω k n := by
    intro n hn
    by_contra hd
    exact hall n ((primalOpenCrossing_iff_no_dualBoxCrossing (k := k) (n := n) hn).mpr hd)
  obtain ⟨f, hf⟩ := infinite_component_of_forall_dualBoxCrossing hcross
  exact hf (hfin f)

end FK.PlaneTopology.GridCofinalCrossing

/-! ## 4. Principal declarations and trust -/

#print axioms FK.PlaneTopology.GridCofinalCrossing.row_zero_of_walk
#print axioms FK.PlaneTopology.GridCofinalCrossing.infinite_component_of_forall_dualBoxCrossing
#print axioms FK.PlaneTopology.GridCofinalCrossing.primalOpenCrossing_mono
#print axioms FK.PlaneTopology.GridCofinalCrossing.primalOpenCrossing_cofinally
