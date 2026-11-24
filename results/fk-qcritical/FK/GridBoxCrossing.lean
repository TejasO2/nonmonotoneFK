import FK.FiniteBoxDuality
import FK.GridDualIncidence

/-!
# Un-collapsed finite-box crossing duality on the square lattice

`FK.PlaneTopology.BoxSeamBridge` proves the finite box duality

`PrimalOpenCrossing ω k n ↔ ¬ (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)`

for the vertex box `[0,k+1] × [0,n]`.  The two dual *exterior rows* are
represented there by the two extra vertices `Sum.inr 0` ("below") and
`Sum.inr 1` ("above"): every cell of the bottom resp. top row of the box is
adjacent to that single vertex across its bottom resp. top bond.

This file removes that collapse.  The dual side is re-stated on genuine cells
`(i,j) ∈ ℤ × ℤ`, i.e. on genuine vertices of the *same* `GridV` that carries
the primal lattice and of the genuine face lattice `gridDual`:

* `inCellBox`, `DCell` — the cell box `0 ≤ i ≤ k`, `-1 ≤ j ≤ n`, including the
  two exterior cell rows `j = -1` and `j = n`;
* `DCellStep` — two cells of that box whose common side is a *closed* primal
  bond of the box (the two exterior rows are only allowed to communicate with
  the box through genuine box bonds);
* `DualBoxCrossing` — a closed-cell walk from the exterior row `j = -1` to the
  exterior row `j = n` staying inside the cell box;
* `toD`, `dCellStep_toD` — the graph homomorphism collapsing the exterior rows,
  and `lift_walk`, the converse path lifting;
* `dualBoxCrossing_iff_closedReachable`, and the resulting genuine-lattice
  statement `primalOpenCrossing_iff_no_dualBoxCrossing`.

The result is a finite-box duality whose dual crossing is a genuine walk of the
face lattice on genuine cells; no artificial exterior vertex is used in the
final statement.  It is a *finite* statement: no infinite-volume, compactness,
`GlobalAtMostOne` or Theorem 1.11 claim is made here.
-/

namespace FK.PlaneTopology.GridBoxCrossing

open FK.PlaneTopology.CutCrossing
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PrimalClosedDuality
open FK.PlaneTopology.BoxSeam
open FK.PlaneTopology.BoxSeamBridge

attribute [local instance] Classical.propDecidable

variable {k n : ℕ} {ω : gridGraph.edgeSet → Bool}

/-! ## 1. The cell box with its two exterior rows -/

/-- The cells of the box cylinder: columns `0,…,k`, rows `-1,…,n`.  Row `-1`
resp. row `n` is the exterior row below resp. above the vertex box
`[0,k+1] × [0,n]`. -/
def inCellBox (k n : ℕ) (f : GridV) : Prop :=
  0 ≤ f.1 ∧ f.1 ≤ (k : ℤ) ∧ -1 ≤ f.2 ∧ f.2 ≤ (n : ℤ)

/-- The cells of the un-collapsed dual box. -/
abbrev DCell (k n : ℕ) : Type := {f : GridV // inCellBox k n f}

lemma DCell.fst_nonneg (f : DCell k n) : 0 ≤ f.1.1 := by
  have h := f.2; simp only [inCellBox] at h; exact h.1

lemma DCell.fst_le (f : DCell k n) : f.1.1 ≤ (k : ℤ) := by
  have h := f.2; simp only [inCellBox] at h; exact h.2.1

lemma DCell.snd_ge (f : DCell k n) : -1 ≤ f.1.2 := by
  have h := f.2; simp only [inCellBox] at h; exact h.2.2.1

lemma DCell.snd_le (f : DCell k n) : f.1.2 ≤ (n : ℤ) := by
  have h := f.2; simp only [inCellBox] at h; exact h.2.2.2

lemma DCell.fst_toNat_lt (f : DCell k n) : f.1.1.toNat < k + 1 := by
  have h1 := f.fst_nonneg
  have h2 := f.fst_le
  have := Int.toNat_lt h1 |>.mpr (by omega : f.1.1 < ((k + 1 : ℕ) : ℤ))
  simpa using this

lemma DCell.snd_toNat_lt (hn : 0 < n) (f : DCell k n) (hbot : f.1.2 ≠ -1)
    (htop : f.1.2 ≠ (n : ℤ)) : f.1.2.toNat < n := by
  have hge := f.snd_ge
  have hle := f.snd_le
  have hlt : (-1 : ℤ) < f.1.2 := lt_of_le_of_ne hge (Ne.symm hbot)
  have hpos : (0 : ℤ) ≤ f.1.2 := by omega
  have hlt2 : f.1.2 < (n : ℤ) := lt_of_le_of_ne hle htop
  exact Int.toNat_lt hpos |>.mpr hlt2

/-- The cells of the vertex box proper (`0 ≤ j ≤ n-1`), i.e. the image of the
`Sum.inl` cells of `DVert`. -/
noncomputable def cellOf (c : Fin (k + 1) × Fin n) : DCell k n :=
  ⟨(((c.1 : ℕ) : ℤ), ((c.2 : ℕ) : ℤ)), by
    have h1 := c.1.isLt
    have h2 := c.2.isLt
    simp only [inCellBox]
    omega⟩

@[simp] lemma cellOf_fst (c : Fin (k + 1) × Fin n) : (cellOf c).1.1 = ((c.1 : ℕ) : ℤ) := rfl
@[simp] lemma cellOf_snd (c : Fin (k + 1) × Fin n) : (cellOf c).1.2 = ((c.2 : ℕ) : ℤ) := rfl

/-! ## 2. Closed cell steps inside the box -/

/-- Two cells of the cell box are joined by a **closed** step when they share a
side which is a closed primal bond *of the vertex box*.  Concretely this is
`CellClosed` together with the requirement that the crossed bond lies inside the
vertex box `[0,k+1] × [0,n]`.  Both horizontal moves inside an exterior row and
moves leaving the cell box are thereby excluded. -/
def DCellStep (ω : gridGraph.edgeSet → Bool) (k n : ℕ) (f g : DCell k n) : Prop :=
  (g.1.2 = f.1.2 ∧ (g.1.1 = f.1.1 + 1 ∨ f.1.1 = g.1.1 + 1) ∧
      (0 : ℤ) ≤ f.1.2 ∧ f.1.2 + 1 ≤ (n : ℤ) ∧
      bondClosed ω (min f.1.1 g.1.1 + 1, f.1.2) (min f.1.1 g.1.1 + 1, f.1.2 + 1)) ∨
    (g.1.1 = f.1.1 ∧ (g.1.2 = f.1.2 + 1 ∨ f.1.2 = g.1.2 + 1) ∧
      (0 : ℤ) ≤ min f.1.2 g.1.2 + 1 ∧ min f.1.2 g.1.2 + 1 ≤ (n : ℤ) ∧
      bondClosed ω (f.1.1, min f.1.2 g.1.2 + 1) (f.1.1 + 1, min f.1.2 g.1.2 + 1))

lemma DCellStep_comm {f g : DCell k n} (h : DCellStep ω k n f g) :
    DCellStep ω k n g f := by
  unfold DCellStep at *
  rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · refine Or.inl ⟨h1.symm, h2.symm, ?_, ?_, ?_⟩
    · rw [h1]; exact h3
    · rw [h1]; exact h4
    · rw [h1, min_comm]; exact h5
  · refine Or.inr ⟨h1.symm, h2.symm, ?_, ?_, ?_⟩
    · rw [min_comm]; exact h3
    · rw [min_comm]; exact h4
    · rw [h1, min_comm]; exact h5

lemma DCellStep_irrefl (f : DCell k n) : ¬ DCellStep ω k n f f := by
  rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> omega

/-- The closed-cell graph of the un-collapsed box. -/
noncomputable def dCellGraph (ω : gridGraph.edgeSet → Bool) (k n : ℕ) :
    SimpleGraph (DCell k n) where
  Adj := DCellStep ω k n
  symm := ⟨fun _ _ h => DCellStep_comm h⟩
  loopless := ⟨fun f h => DCellStep_irrefl f h⟩

/-- A closed-bond dual crossing of the box, from the exterior row `j = -1` to
the exterior row `j = n`, inside the cell box. -/
def DualBoxCrossing (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : Prop :=
  ∃ f g : DCell k n, f.1.2 = -1 ∧ g.1.2 = (n : ℤ) ∧ (dCellGraph ω k n).Reachable f g

/-! ## 3. The collapse map to `DVert` -/

/-- Collapse the two exterior rows `j = -1` and `j = n` to the two exterior
vertices `Sum.inr 0` and `Sum.inr 1`; interior cells keep their coordinates. -/
noncomputable def toD (hn : 0 < n) (f : DCell k n) : DVert k n :=
  if h1 : f.1.2 = -1 then Sum.inr 0
  else if h2 : f.1.2 = (n : ℤ) then Sum.inr 1
  else Sum.inl
    (⟨⟨f.1.1.toNat, f.fst_toNat_lt⟩, ⟨f.1.2.toNat, f.snd_toNat_lt hn h1 h2⟩⟩)

lemma toD_bot (hn : 0 < n) (f : DCell k n) (h : f.1.2 = -1) : toD hn f = Sum.inr 0 := by
  unfold toD
  rw [dif_pos h]

lemma toD_top (hn : 0 < n) (f : DCell k n) (h : f.1.2 = (n : ℤ)) : toD hn f = Sum.inr 1 := by
  unfold toD
  rw [dif_neg (by omega), dif_pos h]

lemma toD_interior (hn : 0 < n) (f : DCell k n) (h1 : f.1.2 ≠ -1) (h2 : f.1.2 ≠ (n : ℤ)) :
    toD hn f = Sum.inl
        (⟨⟨f.1.1.toNat, f.fst_toNat_lt⟩, ⟨f.1.2.toNat, f.snd_toNat_lt hn h1 h2⟩⟩) := by
  unfold toD
  rw [dif_neg h1, dif_neg h2]

lemma toD_eq_inr_zero (hn : 0 < n) {f : DCell k n} (h : toD hn f = Sum.inr 0) :
    f.1.2 = -1 := by
  by_contra hc
  by_cases htop : f.1.2 = (n : ℤ)
  · rw [toD_top hn f htop] at h
    exact absurd h (by simp)
  · rw [toD_interior hn f hc htop] at h
    exact absurd h (by simp)

lemma toD_eq_inr_one (hn : 0 < n) {f : DCell k n} (h : toD hn f = Sum.inr 1) :
    f.1.2 = (n : ℤ) := by
  by_contra hc
  by_cases hbot : f.1.2 = -1
  · rw [toD_bot hn f hbot] at h
    exact absurd h (by simp)
  · rw [toD_interior hn f hbot hc] at h
    exact absurd h (by simp)

lemma toD_eq_inl (hn : 0 < n) {f : DCell k n} {c : Fin (k + 1) × Fin n}
    (h : toD hn f = Sum.inl c) :
    ((c.1 : ℕ) : ℤ) = f.1.1 ∧ ((c.2 : ℕ) : ℤ) = f.1.2 := by
  have hbot : f.1.2 ≠ -1 := by
    intro hc
    rw [toD_bot hn f hc] at h
    exact absurd h (by simp)
  have htop : f.1.2 ≠ (n : ℤ) := by
    intro hc
    rw [toD_top hn f hc] at h
    exact absurd h (by simp)
  rw [toD_interior hn f hbot htop] at h
  have hc : (⟨⟨f.1.1.toNat, f.fst_toNat_lt⟩,
      ⟨f.1.2.toNat, f.snd_toNat_lt hn hbot htop⟩⟩ : Fin (k + 1) × Fin n) = c := by
    simpa using h
  rw [← hc]
  exact ⟨Int.toNat_of_nonneg f.fst_nonneg,
    Int.toNat_of_nonneg (by have := f.snd_ge; omega)⟩

lemma toD_cellOf (hn : 0 < n) (c : Fin (k + 1) × Fin n) : toD hn (cellOf c) = Sum.inl c := by
  have h1 : (cellOf c).1.2 ≠ -1 := by
    rw [cellOf_snd]; have := c.2.isLt; omega
  have h2 : (cellOf c).1.2 ≠ (n : ℤ) := by
    rw [cellOf_snd]; have := c.2.isLt; omega
  rw [toD_interior hn _ h1 h2]
  have hkey : (⟨⟨(cellOf c).1.1.toNat, (cellOf c).fst_toNat_lt⟩,
      ⟨(cellOf c).1.2.toNat, (cellOf c).snd_toNat_lt hn h1 h2⟩⟩ :
      Fin (k + 1) × Fin n) = c := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [cellOf]
  rw [hkey]

/-! ## 4. Interior steps, and the two exterior steps -/

/-- A `CellClosed` step between two cells of the vertex box is a closed step of
the cell box: the crossed bond automatically lies inside the vertex box. -/
lemma DCellStep_of_cellClosed_interior {f g : DCell k n}
    (h : CellClosed ω f.1.1 f.1.2 g.1.1 g.1.2)
    (hf : 0 ≤ f.1.2) (hf' : f.1.2 < (n : ℤ))
    (hg : 0 ≤ g.1.2) (hg' : g.1.2 < (n : ℤ)) :
    DCellStep ω k n f g := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, hf, by omega, h3⟩
  · exact Or.inr ⟨h1, h2, by omega, by omega, h3⟩

/-- Vertical closed step whose crossed bond is one row above both cells. -/
lemma DCellStep_up {f g : DCell k n} (hcol : f.1.1 = g.1.1) (hrow : g.1.2 = f.1.2 + 1)
    (hmin : min f.1.2 g.1.2 = f.1.2)
    (h0 : (0 : ℤ) ≤ f.1.2 + 1) (hn' : f.1.2 + 1 ≤ (n : ℤ))
    (hb : bondClosed ω (f.1.1, f.1.2 + 1) (f.1.1 + 1, f.1.2 + 1)) :
    DCellStep ω k n f g := by
  refine Or.inr ⟨hcol.symm, Or.inl hrow, ?_, ?_, ?_⟩
  · rw [hmin]; exact h0
  · rw [hmin]; exact hn'
  · rw [hmin]; exact hb

/-- The exterior cell directly below the cell `(i,0)`. -/
noncomputable def botCell (i : Fin (k + 1)) : DCell k n :=
  ⟨(((i : ℕ) : ℤ), -1), by
    have hi := i.isLt
    simp only [inCellBox]; omega⟩

/-- The exterior cell directly above the cell `(i,n-1)`. -/
noncomputable def topCell (i : Fin (k + 1)) : DCell k n :=
  ⟨(((i : ℕ) : ℤ), (n : ℤ)), by
    have hi := i.isLt
    simp only [inCellBox]; omega⟩

lemma botCell_fst (i : Fin (k + 1)) : (botCell (n := n) i).1.1 = ((i : ℕ) : ℤ) := rfl
lemma botCell_snd (i : Fin (k + 1)) : (botCell (n := n) i).1.2 = -1 := rfl
lemma topCell_fst (i : Fin (k + 1)) : (topCell (k := k) (n := n) i).1.1 = ((i : ℕ) : ℤ) := rfl
lemma topCell_snd (i : Fin (k + 1)) : (topCell (k := k) (n := n) i).1.2 = (n : ℤ) := rfl

/-- The cell `(i,0)`, as a cell of the vertex box. -/
noncomputable def zeroCell (hn : 0 < n) (i : Fin (k + 1)) : DCell k n :=
  cellOf (i, ⟨0, hn⟩)

lemma zeroCell_fst (hn : 0 < n) (i : Fin (k + 1)) : (zeroCell hn i).1.1 = ((i : ℕ) : ℤ) := by
  rw [zeroCell, cellOf_fst]

lemma zeroCell_snd (hn : 0 < n) (i : Fin (k + 1)) : (zeroCell hn i).1.2 = 0 := by
  rw [zeroCell, cellOf_snd]
  rfl

/-- The cell `(i,n-1)`, as a cell of the vertex box. -/
noncomputable def lastCell (hn : 0 < n) (i : Fin (k + 1)) : DCell k n :=
  cellOf (i, ⟨n - 1, by omega⟩)

lemma lastCell_fst (hn : 0 < n) (i : Fin (k + 1)) : (lastCell hn i).1.1 = ((i : ℕ) : ℤ) := by
  rw [lastCell, cellOf_fst]

lemma lastCell_snd (hn : 0 < n) (i : Fin (k + 1)) : (lastCell hn i).1.2 = (n : ℤ) - 1 := by
  rw [lastCell, cellOf_snd]
  have hcast : (((⟨n - 1, by omega⟩ : Fin n) : ℕ) : ℤ) = ((n - 1 : ℕ) : ℤ) := rfl
  rw [hcast]
  have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [this]

/-- Entry step: the cell `(i,0)` is reached from the exterior cell `(i,-1)`
across the closed bottom bond. -/
lemma DCellStep_enter (hn : 0 < n) (i : Fin (k + 1))
    (h : bondClosed ω (((i : ℕ) : ℤ), 0) (((i : ℕ) : ℤ) + 1, 0)) :
    DCellStep ω k n (botCell i) (zeroCell hn i) := by
  have hbf : (botCell (n := n) i).1.1 = ((i : ℕ) : ℤ) := botCell_fst i
  have hbs : (botCell (n := n) i).1.2 = -1 := botCell_snd i
  have hzf : (zeroCell hn i).1.1 = ((i : ℕ) : ℤ) := zeroCell_fst hn i
  have hzs : (zeroCell hn i).1.2 = 0 := zeroCell_snd hn i
  refine DCellStep_up (f := botCell i) (g := zeroCell hn i) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hbf, hzf]
  · rw [hbs, hzs]; norm_num
  · rw [hbs, hzs]; norm_num
  · omega
  · omega
  · rw [hbf, hbs]
    norm_num
    exact h

/-- Exit step: the exterior cell `(i,n)` is reached from `(i,n-1)` across the
closed top bond. -/
lemma DCellStep_exit (hn : 0 < n) (i : Fin (k + 1))
    (h : bondClosed ω (((i : ℕ) : ℤ), (n : ℤ)) (((i : ℕ) : ℤ) + 1, (n : ℤ))) :
    DCellStep ω k n (lastCell hn i) (topCell i) := by
  have hlf : (lastCell hn i).1.1 = ((i : ℕ) : ℤ) := lastCell_fst hn i
  have hls : (lastCell hn i).1.2 = (n : ℤ) - 1 := lastCell_snd hn i
  have htf : (topCell (k := k) (n := n) i).1.1 = ((i : ℕ) : ℤ) := topCell_fst i
  have hts : (topCell (k := k) (n := n) i).1.2 = (n : ℤ) := topCell_snd i
  refine DCellStep_up (f := lastCell hn i) (g := topCell (k := k) (n := n) i) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hlf, htf]
  · rw [hls, hts]; ring
  · rw [hls, hts]; omega
  · omega
  · omega
  · rw [hlf, hls]
    norm_num
    exact h

/-- A downward vertical closed step, crossing the bond one row above the lower
cell. -/
lemma DCellStep_down {f g : DCell k n} (hcol : f.1.1 = g.1.1) (hrow : f.1.2 = g.1.2 + 1)
    (hmin : min f.1.2 g.1.2 = g.1.2)
    (h0 : (0 : ℤ) ≤ g.1.2 + 1) (hn' : g.1.2 + 1 ≤ (n : ℤ))
    (hb : bondClosed ω (f.1.1, g.1.2 + 1) (f.1.1 + 1, g.1.2 + 1)) :
    DCellStep ω k n f g := by
  refine Or.inr ⟨hcol.symm, Or.inr hrow, ?_, ?_, ?_⟩
  · rw [hmin]; exact h0
  · rw [hmin]; exact hn'
  · rw [hmin]; exact hb

/-! ## 5. Lifting closed steps into the cell box -/

/-- **Interior step lifting.**  A closed step of the collapsed dual graph out of
an interior box cell is a closed step of the un-collapsed cell graph. -/
lemma exists_step_of_DClosed (hn : 0 < n) {f : DCell k n} {c : Fin (k + 1) × Fin n}
    (hf : toD hn f = Sum.inl c) {u : DVert k n}
    (h : DClosed ω k n (Sum.inl c) u) :
    ∃ g : DCell k n, toD hn g = u ∧ DCellStep ω k n f g := by
  obtain ⟨hcf, hcs⟩ := toD_eq_inl hn hf
  have hcf' : ((c.1 : ℕ) : ℤ) = f.1.1 := hcf
  have hcs' : ((c.2 : ℕ) : ℤ) = f.1.2 := hcs
  have hf0 : (0 : ℤ) ≤ f.1.2 := by rw [← hcs']; exact Int.natCast_nonneg _
  have hf1 : f.1.2 < (n : ℤ) := by
    rw [← hcs']
    have := c.2.isLt
    omega
  rcases u with d | s
  · -- interior step
    have hcc : CellClosed ω f.1.1 f.1.2 ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := by
      have h' : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := h
      rwa [hcf', hcs'] at h'
    have hd0 : (0 : ℤ) ≤ ((d.2 : ℕ) : ℤ) := Int.natCast_nonneg _
    have hd1 : ((d.2 : ℕ) : ℤ) < (n : ℤ) := by
      have := d.2.isLt; omega
    refine ⟨cellOf d, toD_cellOf hn d, ?_⟩
    exact DCellStep_of_cellClosed_interior hcc hf0 hf1 hd0 hd1
  · -- exterior step
    rcases h with ⟨hs, hc0, hbond⟩ | ⟨hs, hc0, hbond⟩
    · -- below: `s = 0`
      subst hs
      have hrow : f.1.2 = 0 := by rw [← hcs']; exact hc0
      have hcol : f.1.1 = (botCell (n := n) c.1).1.1 := by rw [botCell_fst]; exact hcf'.symm
      have hmin : min f.1.2 (botCell (n := n) (k := k) c.1).1.2
          = (botCell (n := n) (k := k) c.1).1.2 := by
        rw [botCell_snd, hrow]; norm_num
      have hbs : (botCell (n := n) (k := k) c.1).1.2 = -1 := botCell_snd _
      have hb : bondClosed ω (f.1.1, (botCell (n := n) (k := k) c.1).1.2 + 1)
          (f.1.1 + 1, (botCell (n := n) (k := k) c.1).1.2 + 1) := by
        rw [hbs, ← hcf']
        norm_num
        exact hbond
      refine ⟨botCell (n := n) c.1, toD_bot (n := n) (k := k) hn _ (botCell_snd c.1), ?_⟩
      exact DCellStep_down hcol hrow hmin (by omega) (by omega) hb
    · -- above: `s = 1`
      subst hs
      have hrow : f.1.2 = (n : ℤ) - 1 := by rw [← hcs']; exact hc0
      have hcol : f.1.1 = (topCell (k := k) (n := n) c.1).1.1 := by
        rw [topCell_fst]; exact hcf'.symm
      have hmin : min f.1.2 (topCell (k := k) (n := n) c.1).1.2 = f.1.2 := by
        rw [topCell_snd, hrow]; norm_num
      have hb : bondClosed ω (f.1.1, f.1.2 + 1) (f.1.1 + 1, f.1.2 + 1) := by
        rw [hrow, ← hcf']
        have h1 : ((n : ℤ) - 1 + 1) = (n : ℤ) := by ring
        rw [h1]
        exact hbond
      refine ⟨topCell (k := k) (n := n) c.1,
        toD_top (n := n) (k := k) hn _ (topCell_snd c.1), ?_⟩
      exact DCellStep_up hcol (by rw [topCell_snd, hrow]; ring) hmin
        (by omega) (by omega) hb

/-! ## 6. Honest reachability, and the collapse of a closed dual crossing -/

/-- Cells of the box reachable from the exterior row `j = -1` by a closed cell
walk of the box. -/
def HonestReach (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : Set (DCell k n) :=
  {g | ∃ f₀ : DCell k n, f₀.1.2 = -1 ∧ (dCellGraph ω k n).Reachable f₀ g}

/-- An honest crossing has occurred: some honest cell sits in the top exterior
row `j = n`. -/
def TopDone (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : Prop :=
  ∃ g : DCell k n, HonestReach ω k n g ∧ g.1.2 = (n : ℤ)

lemma honestReach_step {f g : DCell k n} (hf : HonestReach ω k n f)
    (h : DCellStep ω k n f g) : HonestReach ω k n g := by
  obtain ⟨f₀, hf₀, ⟨w⟩⟩ := hf
  exact ⟨f₀, hf₀, ⟨w.append (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)⟩⟩

lemma honestReach_zeroCell (hn : 0 < n) (i : Fin (k + 1))
    (h : bondClosed ω (((i : ℕ) : ℤ), 0) (((i : ℕ) : ℤ) + 1, 0)) :
    HonestReach ω k n (zeroCell hn i) :=
  ⟨botCell i, botCell_snd i,
    ⟨SimpleGraph.Walk.cons (DCellStep_enter hn i h) SimpleGraph.Walk.nil⟩⟩

lemma cellOf_eq_zeroCell (hn : 0 < n) {c : Fin (k + 1) × Fin n}
    (hc : ((c.2 : ℕ) : ℤ) = 0) : cellOf c = zeroCell hn c.1 := by
  have h2 : c.2 = (⟨0, hn⟩ : Fin n) := by
    apply Fin.ext
    show (c.2 : ℕ) = 0
    have hcast : ((c.2 : ℕ) : ℤ) = 0 := by simpa using hc
    omega
  have hceq : c = (c.1, (⟨0, hn⟩ : Fin n)) := Prod.ext rfl h2
  rw [hceq, zeroCell]

lemma eq_cellOf_of_toD_eq_inl (hn : 0 < n) {g : DCell k n} {d : Fin (k + 1) × Fin n}
    (h : toD hn g = Sum.inl d) : g = cellOf d := by
  obtain ⟨h1, h2⟩ := toD_eq_inl hn h
  refine Subtype.ext (Prod.ext ?_ ?_)
  · rw [cellOf_fst]; exact h1.symm
  · rw [cellOf_snd]; exact h2.symm

/-- The state invariant along a collapsed closed walk starting below the box. -/
def Inv (ω : gridGraph.edgeSet → Bool) (k n : ℕ) (hn : 0 < n) (v : DVert k n) : Prop :=
  TopDone ω k n ∨ ((v = Sum.inr 1 → TopDone ω k n) ∧
    ∀ c : Fin (k + 1) × Fin n, v = Sum.inl c → HonestReach ω k n (cellOf c))

lemma inv_zero : Inv ω k n hn (Sum.inr 0) :=
  Or.inr ⟨by intro hc; exact absurd hc (by simp),
    by intro c hc; exact absurd hc (by simp)⟩

lemma inv_step {a b : DVert k n} (hn : 0 < n) (h : DClosed ω k n a b)
    (ha : Inv ω k n hn a) : Inv ω k n hn b := by
  rcases ha with hdone | ⟨htop, hcell⟩
  · exact Or.inl hdone
  rcases a with c | s
  · -- the walk is at an interior cell
    have hc : HonestReach ω k n (cellOf c) := hcell c rfl
    obtain ⟨g, hg, hstepg⟩ := exists_step_of_DClosed hn (toD_cellOf hn c) h
    have hg' : HonestReach ω k n g := honestReach_step hc hstepg
    rcases b with d | t
    · refine Or.inr ⟨?_, ?_⟩
      · intro hb; exact absurd hb (by simp)
      · intro e he
        have hed : e = d := by simpa using he.symm
        rw [hed]
        rw [← eq_cellOf_of_toD_eq_inl hn hg]
        exact hg'
    · refine Or.inr ⟨?_, ?_⟩
      · intro hb
        have ht : t = 1 := by simpa using hb
        subst ht
        exact ⟨g, hg', toD_eq_inr_one hn hg⟩
      · intro e he; exact absurd he (by simp)
  · -- the walk is on an exterior vertex
    rcases b with d | t
    · rcases h with ⟨hs, hc0, hbond⟩ | ⟨hs, hc0, hbond⟩
      · -- `s = 0`: the step enters the bottom row of the box
        subst hs
        refine Or.inr ⟨?_, ?_⟩
        · intro hb; exact absurd hb (by simp)
        · intro e he
          have hed : e = d := by simpa using he.symm
          rw [hed]
          have hce : ((d.2 : ℕ) : ℤ) = 0 := hc0
          rw [cellOf_eq_zeroCell hn hce]
          exact honestReach_zeroCell hn d.1 hbond
      · -- `s = 1`: the invariant was already inherited from the interior step
        subst hs
        exact Or.inl (htop rfl)
    · exact h.elim

lemma inv_of_walk (hn : 0 < n) {a b : DVert k n} (p : (closedGraph ω k n).Walk a b)
    (ha : Inv ω k n hn a) : Inv ω k n hn b := by
  induction p with
  | nil => exact ha
  | cons h q ih => exact ih (inv_step hn h ha)

/-- **From a collapsed closed crossing to an honest one.**  A closed-bond dual
crossing of the collapsed box graph produces a closed cell walk in the genuine
cell box from the exterior row `-1` to the exterior row `n`. -/
theorem dualBoxCrossing_of_closedReachable (hn : 0 < n)
    (h : (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)) :
    DualBoxCrossing ω k n := by
  obtain ⟨p⟩ := h
  rcases inv_of_walk hn p inv_zero with hdone | ⟨htop, -⟩
  · obtain ⟨g, ⟨f₀, hf₀, hreach⟩, hg⟩ := hdone
    exact ⟨f₀, g, hf₀, hg, hreach⟩
  · obtain ⟨g, ⟨f₀, hf₀, hreach⟩, hg⟩ := htop rfl
    exact ⟨f₀, g, hf₀, hg, hreach⟩

/-! ## 7. A closed cell step collapses to a closed dual step -/

/-- The four exterior adjacencies of the collapsed box graph, in the exact form
used by `DClosed`. -/
lemma DClosed_inr_zero_inl {c : Fin (k + 1) × Fin n} (hc : ((c.2 : ℕ) : ℤ) = 0)
    (hb : bondClosed ω (((c.1 : ℕ) : ℤ), 0) (((c.1 : ℕ) : ℤ) + 1, 0)) :
    DClosed ω k n (Sum.inr 0) (Sum.inl c) :=
  Or.inl ⟨rfl, hc, hb⟩

lemma DClosed_inl_inr_zero {c : Fin (k + 1) × Fin n} (hc : ((c.2 : ℕ) : ℤ) = 0)
    (hb : bondClosed ω (((c.1 : ℕ) : ℤ), 0) (((c.1 : ℕ) : ℤ) + 1, 0)) :
    DClosed ω k n (Sum.inl c) (Sum.inr 0) :=
  Or.inl ⟨rfl, hc, hb⟩

lemma DClosed_inr_one_inl {c : Fin (k + 1) × Fin n} (hc : ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1)
    (hb : bondClosed ω (((c.1 : ℕ) : ℤ), (n : ℤ)) (((c.1 : ℕ) : ℤ) + 1, (n : ℤ))) :
    DClosed ω k n (Sum.inr 1) (Sum.inl c) :=
  Or.inr ⟨rfl, hc, hb⟩

lemma DClosed_inl_inr_one {c : Fin (k + 1) × Fin n} (hc : ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1)
    (hb : bondClosed ω (((c.1 : ℕ) : ℤ), (n : ℤ)) (((c.1 : ℕ) : ℤ) + 1, (n : ℤ))) :
    DClosed ω k n (Sum.inl c) (Sum.inr 1) :=
  Or.inr ⟨rfl, hc, hb⟩

lemma DClosed_inl_inl {c d : Fin (k + 1) × Fin n}
    (h : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ)) :
    DClosed ω k n (Sum.inl c) (Sum.inl d) := h

lemma toNat_row {f : DCell k n} (h0 : (0 : ℤ) ≤ f.1.2) :
    ((f.1.2.toNat : ℕ) : ℤ) = f.1.2 := Int.toNat_of_nonneg h0

lemma toNat_col (f : DCell k n) : ((f.1.1.toNat : ℕ) : ℤ) = f.1.1 :=
  Int.toNat_of_nonneg f.fst_nonneg

lemma DCell.snd_pos {f : DCell k n} (h : f.1.2 ≠ -1) : (0 : ℤ) ≤ f.1.2 := by
  have hge := f.snd_ge
  have hlt : (-1 : ℤ) < f.1.2 := lt_of_le_of_ne hge (Ne.symm h)
  omega

lemma DCell.snd_lt_top_of_ne {f : DCell k n} (h : f.1.2 ≠ (n : ℤ)) : f.1.2 < (n : ℤ) :=
  lt_of_le_of_ne f.snd_le h

lemma min_row_up {f g : DCell k n} (h : g.1.2 = f.1.2 + 1) :
    min f.1.2 g.1.2 = f.1.2 := by
  rw [min_eq_left]; omega

lemma min_row_down {f g : DCell k n} (h : f.1.2 = g.1.2 + 1) :
    min f.1.2 g.1.2 = g.1.2 := by
  rw [min_eq_right]; omega

lemma toD_interior_fst (hn : 0 < n) {f : DCell k n} (hfb : f.1.2 ≠ -1) (hft : f.1.2 ≠ (n : ℤ)) :
    ((toD hn f).elim (fun c => ((c.1 : ℕ) : ℤ)) (fun _ => 0)) = f.1.1 := by
  rw [toD_interior hn f hfb hft]
  exact toNat_col f

lemma DCellStep_toD_same_row (hn : 0 < n) {f g : DCell k n}
    (hrow : g.1.2 = f.1.2) (hcolrel : g.1.1 = f.1.1 + 1 ∨ f.1.1 = g.1.1 + 1)
    (h0 : (0 : ℤ) ≤ f.1.2) (hn1 : f.1.2 + 1 ≤ (n : ℤ))
    (hb : bondClosed ω (min f.1.1 g.1.1 + 1, f.1.2) (min f.1.1 g.1.1 + 1, f.1.2 + 1)) :
    DClosed ω k n (toD hn f) (toD hn g) := by
  have hfbot : f.1.2 ≠ -1 := by omega
  have hftop : f.1.2 ≠ (n : ℤ) := by omega
  have hgbot : g.1.2 ≠ -1 := by omega
  have hgtop : g.1.2 ≠ (n : ℤ) := by omega
  have hcf := toNat_col f
  have hcg := toNat_col g
  have hrf := toNat_row h0
  have hrg : ((g.1.2.toNat : ℕ) : ℤ) = g.1.2 := by rw [hrow]; exact hrf
  rw [toD_interior hn f hfbot hftop, toD_interior hn g hgbot hgtop]
  refine DClosed_inl_inl ?_
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hrg, hrf]; exact hrow
  · rw [hcg, hcf]; exact hcolrel
  · rw [hcg, hcf, hrf]; exact hb

lemma DCellStep_toD_up (hn : 0 < n) {f g : DCell k n}
    (hcol : g.1.1 = f.1.1) (hrow : g.1.2 = f.1.2 + 1)
    (h0 : (0 : ℤ) ≤ min f.1.2 g.1.2 + 1) (hn1 : min f.1.2 g.1.2 + 1 ≤ (n : ℤ))
    (hb : bondClosed ω (f.1.1, min f.1.2 g.1.2 + 1) (f.1.1 + 1, min f.1.2 g.1.2 + 1)) :
    DClosed ω k n (toD hn f) (toD hn g) := by
  by_cases hfb : f.1.2 = -1
  · -- `f` is the bottom exterior cell, `g` has row `0`
    have hg0 : g.1.2 = 0 := by omega
    have hgbot : g.1.2 ≠ -1 := by omega
    have hgtop : g.1.2 ≠ (n : ℤ) := by omega
    have hcg := toNat_col g
    have hrg : ((g.1.2.toNat : ℕ) : ℤ) = g.1.2 := toNat_row (by omega)
    have hmin : min f.1.2 g.1.2 + 1 = 0 := by
      have hle : f.1.2 ≤ g.1.2 := by omega
      rw [min_eq_left hle]; omega
    rw [toD_bot hn f hfb, toD_interior hn g hgbot hgtop]
    refine DClosed_inr_zero_inl ?_ ?_
    · rw [hrg, hg0]
    · rw [hmin] at hb
      rw [← hcol] at hb
      rw [hcg]
      exact hb
  · by_cases hgt : g.1.2 = (n : ℤ)
    · -- `g` is the top exterior cell, `f` has row `n-1`
      have hf : f.1.2 = (n : ℤ) - 1 := by omega
      have hftop : f.1.2 ≠ (n : ℤ) := by omega
      have hcf := toNat_col f
      have hrf : ((f.1.2.toNat : ℕ) : ℤ) = f.1.2 := toNat_row (f.snd_pos hfb)
      have hmin : min f.1.2 g.1.2 + 1 = (n : ℤ) := by
        have hle : f.1.2 ≤ g.1.2 := by omega
        rw [min_eq_left hle]; omega
      rw [toD_interior hn f hfb hftop, toD_top hn g hgt]
      refine DClosed_inl_inr_one ?_ ?_
      · rw [hrf, hf]
      · rw [hmin] at hb
        rw [hcf]
        exact hb
    · -- both interior
      have hgbot : g.1.2 ≠ -1 := by
        intro hc
        have hge := f.snd_ge
        omega
      have hcf := toNat_col f
      have hcg := toNat_col g
      have hrf : ((f.1.2.toNat : ℕ) : ℤ) = f.1.2 := toNat_row (f.snd_pos hfb)
      have hrg : ((g.1.2.toNat : ℕ) : ℤ) = g.1.2 := toNat_row (g.snd_pos hgbot)
      have hftop : f.1.2 ≠ (n : ℤ) := by omega
      rw [toD_interior hn f hfb hftop, toD_interior hn g hgbot hgt]
      refine DClosed_inl_inl ?_
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [hcg, hcf]; exact hcol
      · rw [hrg, hrf]; exact Or.inl hrow
      · rw [hcf, hrf, hrg]; exact hb

lemma DCellStep_toD_down (hn : 0 < n) {f g : DCell k n}
    (hcol : g.1.1 = f.1.1) (hrow : f.1.2 = g.1.2 + 1)
    (h0 : (0 : ℤ) ≤ min f.1.2 g.1.2 + 1) (hn1 : min f.1.2 g.1.2 + 1 ≤ (n : ℤ))
    (hb : bondClosed ω (f.1.1, min f.1.2 g.1.2 + 1) (f.1.1 + 1, min f.1.2 g.1.2 + 1)) :
    DClosed ω k n (toD hn f) (toD hn g) := by
  by_cases hft : f.1.2 = (n : ℤ)
  · -- `f` is the top exterior cell, `g` has row `n-1`
    have hg : g.1.2 = (n : ℤ) - 1 := by omega
    have hgbot : g.1.2 ≠ -1 := by omega
    have hgtop : g.1.2 ≠ (n : ℤ) := by omega
    have hcg := toNat_col g
    have hcf := toNat_col f
    have hrg : ((g.1.2.toNat : ℕ) : ℤ) = g.1.2 := toNat_row (by omega)
    have hmin : min f.1.2 g.1.2 + 1 = (n : ℤ) := by
      have hle : g.1.2 ≤ f.1.2 := by omega
      rw [min_eq_right hle]; omega
    rw [toD_top hn f hft, toD_interior hn g hgbot hgtop]
    refine DClosed_inr_one_inl ?_ ?_
    · rw [hrg, hg]
    · rw [hmin] at hb
      rw [← hcol] at hb
      rw [hcg]
      exact hb
  · by_cases hgb : g.1.2 = -1
    · -- `g` is the bottom exterior cell, `f` has row `0`
      have hf : f.1.2 = 0 := by omega
      have hfbot : f.1.2 ≠ -1 := by omega
      have hftop : f.1.2 ≠ (n : ℤ) := by omega
      have hcf := toNat_col f
      have hrf : ((f.1.2.toNat : ℕ) : ℤ) = f.1.2 := toNat_row (by omega)
      have hmin : min f.1.2 g.1.2 + 1 = 0 := by
        have hle : g.1.2 ≤ f.1.2 := by omega
        rw [min_eq_right hle]; omega
      rw [toD_interior hn f hfbot hftop, toD_bot hn g hgb]
      refine DClosed_inl_inr_zero ?_ ?_
      · rw [hrf, hf]
      · rw [hmin] at hb
        rw [hcf]
        exact hb
    · -- both interior
      have hcf := toNat_col f
      have hcg := toNat_col g
      have hg0 : (0 : ℤ) ≤ g.1.2 := g.snd_pos hgb
      have hfnb : f.1.2 ≠ -1 := by omega
      have hrf : ((f.1.2.toNat : ℕ) : ℤ) = f.1.2 := toNat_row (by omega)
      have hrg : ((g.1.2.toNat : ℕ) : ℤ) = g.1.2 := toNat_row hg0
      rw [toD_interior hn f hfnb hft, toD_interior hn g hgb (by omega)]
      refine DClosed_inl_inl ?_
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [hcg, hcf]; exact hcol
      · rw [hrg, hrf]; exact Or.inr hrow
      · rw [hcf, hrf, hrg]; exact hb

lemma DCellStep_toD (hn : 0 < n) {f g : DCell k n} (h : DCellStep ω k n f g) :
    DClosed ω k n (toD hn f) (toD hn g) := by
  rcases h with ⟨hrow, hcolrel, h0, hn1, hb⟩ | ⟨hcol, hrowrel, h0, hn1, hb⟩
  · exact DCellStep_toD_same_row hn hrow hcolrel h0 hn1 hb
  · rcases hrowrel with hup | hdown
    · exact DCellStep_toD_up hn hcol hup h0 hn1 hb
    · exact DCellStep_toD_down hn hcol hdown h0 hn1 hb

/-! ## 8. The un-collapsed finite box duality -/

/-- Collapsing the two exterior rows is a graph homomorphism into the collapsed
closed-bond graph. -/
noncomputable def dCellHom (hn : 0 < n) :
    dCellGraph ω k n →g closedGraph ω k n where
  toFun := toD hn
  map_rel' := fun h => DCellStep_toD hn h

/-- A closed cell crossing of the box is a closed dual crossing of the collapsed
box graph. -/
theorem closedReachable_of_dualBoxCrossing (hn : 0 < n) (h : DualBoxCrossing ω k n) :
    (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1) := by
  obtain ⟨f, g, hf, hg, ⟨w⟩⟩ := h
  have hw := w.map (dCellHom (ω := ω) hn)
  have h1 : (dCellHom (ω := ω) hn) f = Sum.inr 0 := toD_bot hn f hf
  have h2 : (dCellHom (ω := ω) hn) g = Sum.inr 1 := toD_top hn g hg
  exact ⟨hw.copy h1 h2⟩

/-- **Un-collapsed finite box duality.**  An open primal left-right crossing of
the vertex box `[0,k+1] × [0,n]` exists exactly when the genuine cell box
`0 ≤ i ≤ k`, `-1 ≤ j ≤ n` has **no** closed cell walk from the exterior row
`j = -1` to the exterior row `j = n`.  Both sides are stated with genuine
lattice cells and genuine closed primal bonds; no exterior vertex of the
collapsed box graph occurs in the statement. -/
theorem primalOpenCrossing_iff_no_dualBoxCrossing (hn : 0 < n) :
    PrimalOpenCrossing ω k n ↔ ¬ DualBoxCrossing ω k n := by
  constructor
  · intro hp hd
    exact no_primal_crossing_of_closed_reachable hn
      (closedReachable_of_dualBoxCrossing hn hd) hp
  · intro hd
    refine exists_primal_open_walk_of_no_closed_dual hn ?_
    intro hc
    exact hd (dualBoxCrossing_of_closedReachable hn hc)

/-- The XOR dichotomy in un-collapsed form. -/
theorem dualBoxCrossing_xor_primalOpen (hn : 0 < n) :
    (PrimalOpenCrossing ω k n ∧ ¬ DualBoxCrossing ω k n) ∨
      (DualBoxCrossing ω k n ∧ ¬ PrimalOpenCrossing ω k n) := by
  by_cases h : DualBoxCrossing ω k n
  · exact Or.inr ⟨h, fun hp =>
      (primalOpenCrossing_iff_no_dualBoxCrossing hn).mp hp h⟩
  · exact Or.inl ⟨(primalOpenCrossing_iff_no_dualBoxCrossing hn).mpr h, h⟩

/-- Non-vacuity, closed side: the all-closed configuration has a closed cell
crossing of the box. -/
theorem allClosed_dualBoxCrossing (hn : 0 < n) :
    DualBoxCrossing (fun _ : gridGraph.edgeSet => false) k n :=
  dualBoxCrossing_of_closedReachable hn (allClosed_closed_crossing hn)

/-- Non-vacuity, open side: the all-open configuration has no closed cell
crossing. -/
theorem allOpen_not_dualBoxCrossing (hn : 0 < n) :
    ¬ DualBoxCrossing (fun _ : gridGraph.edgeSet => true) k n :=
  fun h => no_primal_crossing_of_closed_reachable hn
    (closedReachable_of_dualBoxCrossing hn h) (allOpen_primal_crossing hn)

end FK.PlaneTopology.GridBoxCrossing

/-! ## 9. Principal declarations and trust -/

#print axioms FK.PlaneTopology.GridBoxCrossing.DCellStep_toD
#print axioms FK.PlaneTopology.GridBoxCrossing.dualBoxCrossing_of_closedReachable
#print axioms FK.PlaneTopology.GridBoxCrossing.closedReachable_of_dualBoxCrossing
#print axioms FK.PlaneTopology.GridBoxCrossing.primalOpenCrossing_iff_no_dualBoxCrossing
#print axioms FK.PlaneTopology.GridBoxCrossing.dualBoxCrossing_xor_primalOpen
#print axioms FK.PlaneTopology.GridBoxCrossing.allClosed_dualBoxCrossing
#print axioms FK.PlaneTopology.GridBoxCrossing.allOpen_not_dualBoxCrossing
