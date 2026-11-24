import FK.PrimalClosedDuality
import FK.BoxSeamSeparation

/-!
# The finite-box bridge: a closed dual crossing blocks every open primal crossing

`FK.PlaneTopology.PrimalClosedDuality` proves the easy direction of finite
planar duality on the box: if the closed-bond graph has no below-to-above path,
the primal configuration has an open left-to-right crossing
(`exists_primal_open_walk_of_no_closed_dual`).  The converse — a closed dual
crossing blocks every open primal crossing — is the planar direction.

`FK.BoxSeamSeparation` proves `closed_chain_blocks` in namespace
`FK.PlaneTopology.BoxSeam`: a simple chain of cells from the bottom row to the
top row, all of whose crossed bonds are closed, blocks open left-right box paths.

This file formalises the missing bridge rather than restating it:

* `chainOfPath` — a `closedGraph` walk from `Sum.inr 0` to `Sum.inr 1` becomes a
  `CellChain`, using `SimpleGraph.Walk.toPath`: the interior vertices of the
  simple path are the cells, consecutivity is `DClosed`, injectivity is
  simplicity of the path (so the two outer vertices are stripped and play no
  further role).
* `chain_closedH`, `chain_closedV`, `chain_closedBot`, `chain_closedTop` — every
  bond crossed or touched by that chain is a *closed* primal bond of `ω`, read
  off the `DClosed` steps; `min_cast_add_one_eq_max_cast` is the `min`/`max`
  bookkeeping of `CellClosed` against `bondH`/`bondV`.
* `chainSeam_mh_closed`, `chainSeam_mv_closed` — the seam support of the chain
  consists of closed bonds.
* `toBox`, `boxAdj_of_primal_adj` — the coordinate bijection
  `BVert k n → Fin (k+2) × Fin (n+1)` (`0 ≤ i ≤ k+1`, `0 ≤ j ≤ n` versus
  `i < k+2`, `j < n+1`), and the fact that an open primal bond is a seam-free
  bond of `boxGraph (openSeam openH openV)`.
* `no_primal_crossing_of_closed_reachable` — the missing implication;
  `primal_open_crossing_iff_no_closed_dual`, `closed_reachable_xor_primal_open`
  — the equivalence and the XOR dichotomy on the same `k n ω`.

No `sorry`, `admit`, new axioms, `unsafe`, `native_decide`, `maxHeartbeats`
override; no uncollapsing, infinite-volume, compactness, `GlobalAtMostOne` or
Theorem 1.11 claim.
-/

namespace FK.PlaneTopology.BoxSeamBridge

open FK.PlaneTopology.CutCrossing
open FK.PlaneTopology.PrimalClosedDuality
open FK.PlaneTopology.BoxSeam
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence

attribute [local instance] Classical.propDecidable

variable {k n : ℕ} {ω : gridGraph.edgeSet → Bool}

/-! ## 1. The `min`/`max` bookkeeping of `CellClosed` against `bondH`/`bondV` -/

/-- Rows (or columns) one apart: the `min` of `CellClosed` plus one is the `max`
of `bondH`/`bondV`. -/
lemma min_cast_add_one_eq_max_cast {a b : ℕ} (h : a + 1 = b ∨ b + 1 = a) :
    min ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) + 1 = ((max a b : ℕ) : ℤ) := by
  rcases h with h | h
  · have hle : ((a : ℕ) : ℤ) ≤ ((b : ℕ) : ℤ) := by omega
    rw [min_eq_left hle]
    have hmax : max a b = b := by omega
    rw [hmax]
    omega
  · have hle : ((b : ℕ) : ℤ) ≤ ((a : ℕ) : ℤ) := by omega
    rw [min_eq_right hle]
    have hmax : max a b = a := by omega
    rw [hmax]
    omega

lemma bondClosed_congr {p q p' q' : GridV} (hp : p = p') (hq : q = q')
    (h : bondClosed ω p q) : bondClosed ω p' q' := by
  subst hp
  subst hq
  exact h

/-! ## 2. From a closed-graph path to a chain of cells -/

/-- The two outer vertices are not adjacent in the closed-bond graph. -/
lemma DClosed_inr_inr (s t : Fin 2) : ¬ DClosed ω k n (Sum.inr s) (Sum.inr t) :=
  fun h => h

/-- The below vertex forces the cell's row to be `0`. -/
lemma DClosed_inr_zero_row {c : Fin (k + 1) × Fin n}
    (h : DClosed ω k n (Sum.inr (0 : Fin 2)) (Sum.inl c)) : (c.2 : ℕ) = 0 := by
  rcases h with ⟨-, hrow, -⟩ | ⟨h1, -⟩
  · have h' : ((c.2 : ℕ) : ℤ) = 0 := hrow
    omega
  · exact absurd h1 (by decide)

/-- The above vertex forces the cell's row to be `n - 1`. -/
lemma DClosed_top_row (hn : 0 < n) {c : Fin (k + 1) × Fin n}
    (h : DClosed ω k n (Sum.inl c) (Sum.inr (1 : Fin 2))) : (c.2 : ℕ) = n - 1 := by
  rcases h with ⟨h1, -⟩ | ⟨-, hrow, -⟩
  · exact absurd h1 (by decide)
  · have h' : ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 := hrow
    omega

/-- `DClosed` between two cells is the cell adjacency of the seam module. -/
lemma CellAdj_of_DClosed {c d : Fin (k + 1) × Fin n}
    (h : DClosed ω k n (Sum.inl c) (Sum.inl d)) : CellAdj c d := by
  have h' : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := h
  unfold CellClosed at h'
  rcases h' with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · refine Or.inl ⟨Fin.ext (by omega), ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · refine Or.inr ⟨Fin.ext (by omega), ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- A step across a horizontal bond (equal columns) has rows one apart. -/
lemma cellAdj_vert_row {c d : Fin (k + 1) × Fin n} (hadj : CellAdj c d)
    (hcol : c.1 = d.1) :
    (c.2 : ℕ) + 1 = (d.2 : ℕ) ∨ (d.2 : ℕ) + 1 = (c.2 : ℕ) := by
  rcases hadj with ⟨-, h | h⟩ | ⟨-, h⟩
  · exfalso
    have hv : (c.1 : ℕ) = (d.1 : ℕ) := by rw [hcol]
    omega
  · exfalso
    have hv : (c.1 : ℕ) = (d.1 : ℕ) := by rw [hcol]
    omega
  · exact h

/-- A step across a vertical bond (different columns) has rows equal. -/
lemma cellAdj_horiz {c d : Fin (k + 1) × Fin n} (hadj : CellAdj c d) (hne : c.1 ≠ d.1) :
    c.2 = d.2 ∧ ((c.1 : ℕ) + 1 = (d.1 : ℕ) ∨ (d.1 : ℕ) + 1 = (c.1 : ℕ)) := by
  rcases hadj with h | ⟨h1, -⟩
  · exact h
  · exact absurd h1 hne

/-- A vertical step of a cell chain crosses a closed horizontal bond. -/
lemma bondClosed_of_cellClosed_vert {c d : Fin (k + 1) × Fin n}
    (h : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ))
    (_hcol : c.1 = d.1)
    (hrow : (c.2 : ℕ) + 1 = (d.2 : ℕ) ∨ (d.2 : ℕ) + 1 = (c.2 : ℕ)) :
    bondClosed ω (((c.1 : ℕ) : ℤ), ((max (c.2 : ℕ) (d.2 : ℕ) : ℕ) : ℤ))
      (((c.1 : ℕ) : ℤ) + 1, ((max (c.2 : ℕ) (d.2 : ℕ) : ℕ) : ℤ)) := by
  unfold CellClosed at h
  rcases h with ⟨h1, -, -⟩ | ⟨-, -, h3⟩
  · exfalso
    have h21 : ((c.2 : ℕ) : ℤ) = ((d.2 : ℕ) : ℤ) := h1.symm
    omega
  · have h3' := h3
    rw [show min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1
        = ((max (c.2 : ℕ) (d.2 : ℕ) : ℕ) : ℤ) from min_cast_add_one_eq_max_cast hrow] at h3'
    exact h3'

/-- A horizontal step of a cell chain crosses a closed vertical bond. -/
lemma bondClosed_of_cellClosed_horiz {c d : Fin (k + 1) × Fin n}
    (h : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ))
    (_hrow : c.2 = d.2)
    (hcol : (c.1 : ℕ) + 1 = (d.1 : ℕ) ∨ (d.1 : ℕ) + 1 = (c.1 : ℕ)) :
    bondClosed ω (((max (c.1 : ℕ) (d.1 : ℕ) : ℕ) : ℤ), ((c.2 : ℕ) : ℤ))
      (((max (c.1 : ℕ) (d.1 : ℕ) : ℕ) : ℤ), ((c.2 : ℕ) : ℤ) + 1) := by
  unfold CellClosed at h
  rcases h with ⟨-, -, h3⟩ | ⟨h1, -, -⟩
  · have h3' := h3
    rw [show min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) + 1
        = ((max (c.1 : ℕ) (d.1 : ℕ) : ℕ) : ℤ) from min_cast_add_one_eq_max_cast hcol] at h3'
    exact h3'
  · exfalso
    have h11 : ((c.1 : ℕ) : ℤ) = ((d.1 : ℕ) : ℤ) := h1.symm
    omega

/-- A walk from below to above in the closed-bond graph has length at least two. -/
lemma two_le_length {p : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1)}
    (_hp : p.IsPath) : 2 ≤ p.length := by
  rcases Nat.lt_or_ge p.length 2 with h2 | h2
  · have hcases : p.length = 0 ∨ p.length = 1 := by omega
    rcases hcases with h0 | h1
    · have he : (Sum.inr 0 : DVert k n) = Sum.inr 1 := SimpleGraph.Walk.eq_of_length_eq_zero h0
      exact absurd he (by simp)
    · have ha : (closedGraph ω k n).Adj (Sum.inr 0) (Sum.inr 1) :=
        SimpleGraph.Walk.adj_of_length_eq_one h1
      exact absurd ha (DClosed_inr_inr (ω := ω) (k := k) (n := n) 0 1)
  · exact h2

/-- An interior vertex of a simple path from below to above is a cell. -/
lemma exists_cell {p : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1)}
    (hp : p.IsPath) {t : ℕ} (h1 : 0 < t) (h2 : t < p.length) :
    ∃ c : Fin (k + 1) × Fin n, p.getVert t = Sum.inl c := by
  cases h : p.getVert t with
  | inl c => exact ⟨c, rfl⟩
  | inr s =>
    exfalso
    fin_cases s
    · have hz : p.getVert t = p.getVert 0 := by
        rw [h, SimpleGraph.Walk.getVert_zero]; simp
      have := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hz
      omega
    · have hl : p.getVert t = p.getVert p.length := by
        rw [h, SimpleGraph.Walk.getVert_length]; simp
      have := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hl
      omega

/-- The cell at interior position `t` of a simple path from below to above. -/
noncomputable def cellAt (p : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1))
    (hp : p.IsPath) (t : ℕ) (h1 : 0 < t) (h2 : t < p.length) : Fin (k + 1) × Fin n :=
  Classical.choose (exists_cell hp h1 h2)

lemma cellAt_spec (p : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1))
    (hp : p.IsPath) (t : ℕ) (h1 : 0 < t) (h2 : t < p.length) :
    p.getVert t = Sum.inl (cellAt p hp t h1 h2) :=
  Classical.choose_spec (exists_cell hp h1 h2)

/-- The cell chain of a simple closed-graph path from below to above: the two
outer vertices are stripped and the interior cells form the chain. -/
noncomputable def chainOfPath (hn : 0 < n)
    {p : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1)} (hp : p.IsPath) :
    CellChain k n := by
  classical
  have hL2 : 2 ≤ p.length := two_le_length hp
  let cell : Fin (p.length - 2 + 1) → Fin (k + 1) × Fin n :=
    fun t => cellAt p hp (t.val + 1) (by omega) (by omega)
  have hcell : ∀ t : Fin (p.length - 2 + 1), p.getVert (t.val + 1) = Sum.inl (cell t) :=
    fun t => cellAt_spec p hp (t.val + 1) (by omega) (by omega)
  refine ⟨p.length - 2, cell, ?_, ?_, ?_, ?_⟩
  · intro t
    have h0 : (closedGraph ω k n).Adj (p.getVert (t.val + 1))
        (p.getVert (t.val + 1 + 1)) :=
      SimpleGraph.Walk.adj_getVert_succ p (by omega)
    have hc1 : p.getVert (t.val + 1) = Sum.inl (cell t.castSucc) := hcell t.castSucc
    have hc2 : p.getVert (t.val + 1 + 1) = Sum.inl (cell t.succ) := hcell t.succ
    rw [hc1, hc2] at h0
    exact CellAdj_of_DClosed h0
  · intro a b hab
    have hv : p.getVert (a.val + 1) = p.getVert (b.val + 1) := by
      rw [hcell a, hcell b, hab]
    have hEq := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hv
    exact Fin.ext (by omega)
  · have h0 : (closedGraph ω k n).Adj (p.getVert 0) (p.getVert (0 + 1)) :=
      SimpleGraph.Walk.adj_getVert_succ p (by omega)
    have hc0 : p.getVert (0 + 1) = Sum.inl (cell (0 : Fin (p.length - 2 + 1))) :=
      hcell (0 : Fin (p.length - 2 + 1))
    rw [SimpleGraph.Walk.getVert_zero, hc0] at h0
    exact DClosed_inr_zero_row h0
  · have h0 : (closedGraph ω k n).Adj (p.getVert ((Fin.last (p.length - 2)).val + 1))
        (p.getVert ((Fin.last (p.length - 2)).val + 1 + 1)) :=
      SimpleGraph.Walk.adj_getVert_succ p (by simp only [Fin.val_last]; omega)
    have hc1 : p.getVert ((Fin.last (p.length - 2)).val + 1) =
        Sum.inl (cell (Fin.last (p.length - 2))) := hcell (Fin.last (p.length - 2))
    rw [hc1] at h0
    rw [show (Fin.last (p.length - 2)).val + 1 + 1 = p.length by
      simp only [Fin.val_last]; omega, SimpleGraph.Walk.getVert_length] at h0
    exact DClosed_top_row hn h0

/-! ## 3. Every bond of that chain is closed -/

variable {p : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1)}

/-- The `DClosed` step of the chain at position `t`. -/
lemma chainOfPath_step (hn : 0 < n) (hp : p.IsPath) {t : Fin (chainOfPath hn hp).len} :
    DClosed ω k n (Sum.inl ((chainOfPath hn hp).cell t.castSucc))
      (Sum.inl ((chainOfPath hn hp).cell t.succ)) := by
  have hL2 : 2 ≤ p.length := two_le_length hp
  have hlen : (chainOfPath hn hp).len = p.length - 2 := rfl
  have h0 : (closedGraph ω k n).Adj (p.getVert (t.val + 1))
      (p.getVert (t.val + 1 + 1)) :=
    SimpleGraph.Walk.adj_getVert_succ p (by have := t.isLt; omega)
  have hc1 : p.getVert (t.val + 1) = Sum.inl ((chainOfPath hn hp).cell t.castSucc) :=
    cellAt_spec p hp (t.val + 1) (by omega) (by have := t.isLt; omega)
  have hc2 : p.getVert (t.val + 1 + 1) = Sum.inl ((chainOfPath hn hp).cell t.succ) :=
    cellAt_spec p hp (t.val + 1 + 1) (by omega) (by have := t.isLt; omega)
  rw [hc1, hc2] at h0
  exact h0

/-- The horizontal bond crossed by a vertical step of the chain is closed. -/
lemma chain_closedH (hn : 0 < n) (hp : p.IsPath) {t : Fin (chainOfPath hn hp).len}
    (h : stepUp (chainOfPath hn hp) t) :
    bondClosed ω ((((bondH (chainOfPath hn hp) t).1 : ℕ) : ℤ),
        (((bondH (chainOfPath hn hp) t).2 : ℕ) : ℤ))
      ((((bondH (chainOfPath hn hp) t).1 : ℕ) : ℤ) + 1,
        (((bondH (chainOfPath hn hp) t).2 : ℕ) : ℤ)) := by
  have h0 := chainOfPath_step (p := p) hn hp (t := t)
  have hadj : CellAdj ((chainOfPath hn hp).cell t.castSucc) ((chainOfPath hn hp).cell t.succ) :=
    CellAdj_of_DClosed h0
  have hrow := cellAdj_vert_row hadj h
  exact bondClosed_of_cellClosed_vert h0 h hrow

/-- The vertical bond crossed by a horizontal step of the chain is closed. -/
lemma chain_closedV (hn : 0 < n) (hp : p.IsPath) {t : Fin (chainOfPath hn hp).len}
    (h : ¬ stepUp (chainOfPath hn hp) t) :
    bondClosed ω ((((bondV (chainOfPath hn hp) t).1 : ℕ) : ℤ),
        (((bondV (chainOfPath hn hp) t).2 : ℕ) : ℤ))
      ((((bondV (chainOfPath hn hp) t).1 : ℕ) : ℤ),
        (((bondV (chainOfPath hn hp) t).2 : ℕ) : ℤ) + 1) := by
  have h0 := chainOfPath_step (p := p) hn hp (t := t)
  have hadj : CellAdj ((chainOfPath hn hp).cell t.castSucc) ((chainOfPath hn hp).cell t.succ) :=
    CellAdj_of_DClosed h0
  have hne : ((chainOfPath hn hp).cell t.castSucc).1 ≠ ((chainOfPath hn hp).cell t.succ).1 := h
  obtain ⟨hrow, hcol⟩ := cellAdj_horiz hadj hne
  exact bondClosed_of_cellClosed_horiz h0 hrow hcol

/-- The bottom bond of the first cell is closed. -/
lemma chain_closedBot (hn : 0 < n) (hp : p.IsPath) :
    bondClosed ω (((((chainOfPath hn hp).cell 0).1 : ℕ) : ℤ), 0)
      (((((chainOfPath hn hp).cell 0).1 : ℕ) : ℤ) + 1, 0) := by
  have hL2 : 2 ≤ p.length := two_le_length hp
  have h0 : (closedGraph ω k n).Adj (p.getVert 0) (p.getVert (0 + 1)) :=
    SimpleGraph.Walk.adj_getVert_succ p (by omega)
  have hc1 : p.getVert (0 + 1) = Sum.inl ((chainOfPath hn hp).cell 0) :=
    cellAt_spec p hp (0 + 1) (by omega) (by omega)
  rw [SimpleGraph.Walk.getVert_zero, hc1] at h0
  rcases h0 with ⟨-, -, hb⟩ | ⟨h1, -⟩
  · exact hb
  · exact absurd h1 (by decide)

/-- The top bond of the last cell is closed. -/
lemma chain_closedTop (hn : 0 < n) (hp : p.IsPath) :
    bondClosed ω
      (((((chainOfPath hn hp).cell (Fin.last (chainOfPath hn hp).len)).1 : ℕ) : ℤ), (n : ℤ))
      (((((chainOfPath hn hp).cell (Fin.last (chainOfPath hn hp).len)).1 : ℕ) : ℤ) + 1,
        (n : ℤ)) := by
  have hL2 : 2 ≤ p.length := two_le_length hp
  have hlen : (chainOfPath hn hp).len = p.length - 2 := rfl
  have h0 : (closedGraph ω k n).Adj
      (p.getVert ((Fin.last (chainOfPath hn hp).len).val + 1))
      (p.getVert ((Fin.last (chainOfPath hn hp).len).val + 1 + 1)) :=
    SimpleGraph.Walk.adj_getVert_succ p (by simp only [Fin.val_last]; omega)
  have hc1 : p.getVert ((Fin.last (chainOfPath hn hp).len).val + 1) =
      Sum.inl ((chainOfPath hn hp).cell (Fin.last (chainOfPath hn hp).len)) :=
    cellAt_spec p hp _ (by omega) (by simp only [Fin.val_last]; omega)
  rw [hc1] at h0
  rw [show (Fin.last (chainOfPath hn hp).len).val + 1 + 1 = p.length by
    simp only [Fin.val_last]; omega, SimpleGraph.Walk.getVert_length] at h0
  rcases h0 with ⟨h1, -⟩ | ⟨-, -, hb⟩
  · exact absurd h1 (by decide)
  · exact hb

/-! ## 4. The seam support of the chain consists of closed bonds -/

/-- Every horizontal bond of the chain seam of the extracted chain is closed. -/
lemma chainSeam_mh_closed (hn : 0 < n) (hp : p.IsPath) {i j : ℕ}
    (h : (chainSeam (chainOfPath hn hp)).mh i j ≠ 0) :
    bondClosed ω ((i : ℤ), (j : ℤ)) ((i : ℤ) + 1, (j : ℤ)) := by
  set C : CellChain k n := chainOfPath hn hp with hC
  have hmh : (chainSeam C).mh i j = ind (j = 0 ∧ (C.cell 0).1.val = i)
      + ind (j = n ∧ (C.cell (Fin.last C.len)).1.val = i)
      + ∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j)) := rfl
  rw [hmh] at h
  by_cases hbot : j = 0 ∧ (C.cell 0).1.val = i
  · obtain ⟨hj, hi⟩ := hbot
    rw [← hi, hj]
    exact chain_closedBot hn hp
  · by_cases htop : j = n ∧ (C.cell (Fin.last C.len)).1.val = i
    · obtain ⟨hj, hi⟩ := htop
      rw [← hi, hj]
      exact chain_closedTop hn hp
    · rw [ind_neg hbot, ind_neg htop, zero_add, zero_add] at h
      have hex : ∃ t : Fin C.len, stepUp C t ∧ bondH C t = (i, j) := by
        by_contra hcon
        push Not at hcon
        exact h (Finset.sum_eq_zero fun t _ => ind_neg (fun hh => hcon t hh.1 hh.2))
      obtain ⟨t, ht⟩ := hex
      obtain ⟨hstep, hbond⟩ := ht
      have h1 : (bondH C t).1 = i := by rw [hbond]
      have h2 : (bondH C t).2 = j := by rw [hbond]
      rw [← h1, ← h2]
      exact chain_closedH hn hp hstep

/-- Every vertical bond of the chain seam of the extracted chain is closed. -/
lemma chainSeam_mv_closed (hn : 0 < n) (hp : p.IsPath) {i j : ℕ}
    (h : (chainSeam (chainOfPath hn hp)).mv i j ≠ 0) :
    bondClosed ω ((i : ℤ), (j : ℤ)) ((i : ℤ), (j : ℤ) + 1) := by
  set C : CellChain k n := chainOfPath hn hp with hC
  have hmv : (chainSeam C).mv i j
      = ∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j)) := rfl
  rw [hmv] at h
  have hex : ∃ t : Fin C.len, ¬ stepUp C t ∧ bondV C t = (i, j) := by
    by_contra hcon
    push Not at hcon
    exact h (Finset.sum_eq_zero fun t _ => ind_neg (fun hh => hcon t hh.1 hh.2))
  obtain ⟨t, ht⟩ := hex
  obtain ⟨hstep, hbond⟩ := ht
  have h1 : (bondV C t).1 = i := by rw [hbond]
  have h2 : (bondV C t).2 = j := by rw [hbond]
  rw [← h1, ← h2]
  exact chain_closedV hn hp hstep

/-! ## 5. The open-bond indicators of the box and the seam of open bonds -/

/-- The horizontal box bond `(i,j)--(i+1,j)` is open. -/
noncomputable def openH (ω : gridGraph.edgeSet → Bool) (i j : ℕ) : Bool :=
  if bondOpen ω ((i : ℤ), (j : ℤ)) ((i : ℤ) + 1, (j : ℤ)) then true else false

/-- The vertical box bond `(i,j)--(i,j+1)` is open. -/
noncomputable def openV (ω : gridGraph.edgeSet → Bool) (i j : ℕ) : Bool :=
  if bondOpen ω ((i : ℤ), (j : ℤ)) ((i : ℤ), (j : ℤ) + 1) then true else false

lemma openH_eq_true {i j : ℕ} :
    openH ω i j = true ↔ bondOpen ω ((i : ℤ), (j : ℤ)) ((i : ℤ) + 1, (j : ℤ)) := by
  unfold openH
  by_cases h : bondOpen ω ((i : ℤ), (j : ℤ)) ((i : ℤ) + 1, (j : ℤ))
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

lemma openV_eq_true {i j : ℕ} :
    openV ω i j = true ↔ bondOpen ω ((i : ℤ), (j : ℤ)) ((i : ℤ), (j : ℤ) + 1) := by
  unfold openV
  by_cases h : bondOpen ω ((i : ℤ), (j : ℤ)) ((i : ℤ), (j : ℤ) + 1)
  · rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]
    exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h⟩

/-- The seam of the open bonds of the box has a seam bond exactly on the closed
bonds. -/
lemma openSeam_mh_eq_zero {openH openV : ℕ → ℕ → Bool} {i j : ℕ} :
    (openSeam openH openV).mh i j = 0 ↔ openH i j = true := by
  unfold openSeam
  by_cases h : openH i j = true
  · simp [h]
  · simp [h]

lemma openSeam_mv_eq_zero {openH openV : ℕ → ℕ → Bool} {i j : ℕ} :
    (openSeam openH openV).mv i j = 0 ↔ openV i j = true := by
  unfold openSeam
  by_cases h : openV i j = true
  · simp [h]
  · simp [h]

/-! ## 6. The coordinate map `BVert k n → Fin (k+2) × Fin (n+1)` and open steps -/

/-- The box vertex `(i,j)` with `0 ≤ i ≤ k+1`, `0 ≤ j ≤ n` as the coordinate
pair `(i,j)` with `i < k+2`, `j < n+1` used by the seam module. -/
noncomputable def toBox (v : BVert k n) : Fin (k + 2) × Fin (n + 1) :=
  (⟨v.1.1.toNat, by
      have h : inBox k n v.1 := v.2
      simp only [inBox] at h
      have hc : ((v.1.1.toNat : ℕ) : ℤ) = v.1.1 := Int.toNat_of_nonneg h.1
      omega⟩,
    ⟨v.1.2.toNat, by
      have h : inBox k n v.1 := v.2
      simp only [inBox] at h
      have hc : ((v.1.2.toNat : ℕ) : ℤ) = v.1.2 := Int.toNat_of_nonneg h.2.2.1
      omega⟩)

lemma toBox_fst (v : BVert k n) : (((toBox v).1 : ℕ) : ℤ) = v.1.1 := by
  have h : inBox k n v.1 := v.2
  simp only [inBox] at h
  exact Int.toNat_of_nonneg h.1

lemma toBox_snd (v : BVert k n) : (((toBox v).2 : ℕ) : ℤ) = v.1.2 := by
  have h : inBox k n v.1 := v.2
  simp only [inBox] at h
  exact Int.toNat_of_nonneg h.2.2.1

lemma toBox_fst_lt (v : BVert k n) : v.1.1.toNat < k + 2 := by
  have h : inBox k n v.1 := v.2
  simp only [inBox] at h
  have hc : ((v.1.1.toNat : ℕ) : ℤ) = v.1.1 := Int.toNat_of_nonneg h.1
  omega

lemma toBox_snd_lt (v : BVert k n) : v.1.2.toNat < n + 1 := by
  have h : inBox k n v.1 := v.2
  simp only [inBox] at h
  have hc : ((v.1.2.toNat : ℕ) : ℤ) = v.1.2 := Int.toNat_of_nonneg h.2.2.1
  omega

lemma toBox_fst_lt_succ {u v : BVert k n} (h : v.1.1 = u.1.1 + 1) :
    u.1.1.toNat < k + 1 := by
  have h1 : inBox k n u.1 := u.2
  simp only [inBox] at h1
  have h2 : inBox k n v.1 := v.2
  simp only [inBox] at h2
  have hc : ((u.1.1.toNat : ℕ) : ℤ) = u.1.1 := Int.toNat_of_nonneg h1.1
  omega

lemma toBox_snd_lt_of_succ {u v : BVert k n} (h : v.1.2 = u.1.2 + 1) :
    u.1.2.toNat < n := by
  have h1 : inBox k n u.1 := u.2
  simp only [inBox] at h1
  have h2 : inBox k n v.1 := v.2
  simp only [inBox] at h2
  have hc : ((u.1.2.toNat : ℕ) : ℤ) = u.1.2 := Int.toNat_of_nonneg h1.2.2.1
  omega

/-- An open vertical primal bond is a seam-free vertical bond of the box graph. -/
lemma boxAdj_vert_step {u v : BVert k n} (hcol : u.1.1 = v.1.1)
    (hrow : v.1.2 = u.1.2 + 1) (hbo : bondOpen ω u.1 v.1) :
    boxAdj (openSeam (openH ω) (openV ω)) (toBox u) (toBox v) := by
  have hk : u.1.1.toNat < k + 2 := toBox_fst_lt u
  have hj : u.1.2.toNat < n := toBox_snd_lt_of_succ hrow
  have hu1 : (0 : ℤ) ≤ u.1.1 := by
    have h := u.2; simp only [inBox] at h; exact h.1
  have hu2 : (0 : ℤ) ≤ u.1.2 := by
    have h := u.2; simp only [inBox] at h; exact h.2.2.1
  refine Or.inr ⟨⟨u.1.1.toNat, hk⟩, ⟨u.1.2.toNat, hj⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
  · refine (openSeam_mv_eq_zero (openH := openH ω) (openV := openV ω) (i := u.1.1.toNat)
      (j := u.1.2.toNat)).mpr (openV_eq_true.mpr ?_)
    have h1 : (((⟨u.1.1.toNat, hk⟩ : Fin (k + 2)).val : ℕ) : ℤ) = u.1.1 := toBox_fst u
    have h2 : (((⟨u.1.2.toNat, hj⟩ : Fin n).val : ℕ) : ℤ) = u.1.2 := toBox_snd u
    rw [h1, h2]
    have h' : bondOpen ω ((u.1.1), (u.1.2)) ((v.1.1), (v.1.2)) := hbo
    rw [← hcol, hrow] at h'
    exact h'
  · exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  · refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show v.1.1.toNat = u.1.1.toNat
      omega
    · show v.1.2.toNat = u.1.2.toNat + 1
      omega

/-- An open horizontal primal bond is a seam-free horizontal bond of the box
graph. -/
lemma boxAdj_horiz_step {u v : BVert k n} (hrow : u.1.2 = v.1.2)
    (hcol : v.1.1 = u.1.1 + 1) (hbo : bondOpen ω u.1 v.1) :
    boxAdj (openSeam (openH ω) (openV ω)) (toBox u) (toBox v) := by
  have hk : u.1.1.toNat < k + 1 := toBox_fst_lt_succ hcol
  have hj : u.1.2.toNat < n + 1 := toBox_snd_lt u
  have hu1 : (0 : ℤ) ≤ u.1.1 := by
    have h := u.2; simp only [inBox] at h; exact h.1
  have hu2 : (0 : ℤ) ≤ u.1.2 := by
    have h := u.2; simp only [inBox] at h; exact h.2.2.1
  refine Or.inl ⟨⟨u.1.1.toNat, hk⟩, ⟨u.1.2.toNat, hj⟩, ?_, Or.inl ⟨?_, ?_⟩⟩
  · refine (openSeam_mh_eq_zero (openH := openH ω) (openV := openV ω) (i := u.1.1.toNat)
      (j := u.1.2.toNat)).mpr (openH_eq_true.mpr ?_)
    have h1 : (((⟨u.1.1.toNat, hk⟩ : Fin (k + 1)).val : ℕ) : ℤ) = u.1.1 := toBox_fst u
    have h2 : (((⟨u.1.2.toNat, hj⟩ : Fin (n + 1)).val : ℕ) : ℤ) = u.1.2 := toBox_snd u
    rw [h1, h2]
    have h' : bondOpen ω ((u.1.1), (u.1.2)) ((v.1.1), (v.1.2)) := hbo
    rw [hcol, ← hrow] at h'
    exact h'
  · exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  · refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show v.1.1.toNat = u.1.1.toNat + 1
      omega
    · show v.1.2.toNat = u.1.2.toNat
      omega

/-- Every open primal bond of the box is a seam-free bond of the box graph of
the open-bond seam.  This is the graph homomorphism used for the primal walk. -/
lemma boxAdj_of_primal_adj {u v : BVert k n} (h : (primalGraph ω k n).Adj u v) :
    boxAdj (openSeam (openH ω) (openV ω)) (toBox u) (toBox v) := by
  have hbo' : bondOpen ω ((u.1.1), (u.1.2)) ((v.1.1), (v.1.2)) := h
  obtain ⟨hg, -⟩ := h
  rcases hg with ⟨hcol, hrow | hrow⟩ | ⟨hrow, hcol | hcol⟩
  · exact boxAdj_symm (boxAdj_vert_step (u := v) (v := u) hcol.symm hrow (bondOpen_comm hbo'))
  · exact boxAdj_vert_step hcol hrow hbo'
  · exact boxAdj_symm (boxAdj_horiz_step (u := v) (v := u) hrow.symm hcol (bondOpen_comm hbo'))
  · exact boxAdj_horiz_step hrow hcol hbo'

/-! ## 7. The bridge: a closed dual crossing blocks open primal crossings -/

/-- A primal open crossing of the box: an open primal walk from the left wall to
the right wall inside the box. -/
def PrimalOpenCrossing (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : Prop :=
  ∃ u v : BVert k n, u ∈ leftWall k n ∧ v ∈ rightWall k n ∧ (primalGraph ω k n).Reachable u v

/-- **The missing implication.**  A closed-bond path of the box from below to
above blocks every open primal left-right crossing. -/
theorem no_primal_crossing_of_closed_reachable (hn : 0 < n)
    (hclosed : (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)) :
    ¬ PrimalOpenCrossing ω k n := by
  obtain ⟨p⟩ := hclosed
  have hpq : ((p.toPath : (closedGraph ω k n).Walk (Sum.inr 0) (Sum.inr 1))).IsPath :=
    p.toPath.property
  rintro ⟨u, v, hu, hv, hwalk⟩
  have hH : ∀ i j : ℕ, openH ω i j = true →
      (chainSeam (chainOfPath hn hpq)).mh i j = 0 := by
    intro i j ho
    by_contra hne
    exact chainSeam_mh_closed hn hpq hne (openH_eq_true.mp ho)
  have hV : ∀ i j : ℕ, openV ω i j = true →
      (chainSeam (chainOfPath hn hpq)).mv i j = 0 := by
    intro i j ho
    by_contra hne
    exact chainSeam_mv_closed hn hpq hne (openV_eq_true.mp ho)
  have hfu : (toBox u).1 = 0 := by
    apply Fin.ext
    have h1 := toBox_fst u
    have h2 : u.1.1 = 0 := hu
    show ((toBox u).1).val = 0
    omega
  have hfv : (toBox v).1 = Fin.last (k + 1) := by
    apply Fin.ext
    have h1 := toBox_fst v
    have h2 : v.1.1 = (k : ℤ) + 1 := hv
    show ((toBox v).1).val = k + 1
    omega
  obtain ⟨w⟩ := hwalk
  let f : primalGraph ω k n →g boxGraph (openSeam (openH ω) (openV ω)) :=
    { toFun := toBox, map_rel' := fun {a b} h => boxAdj_of_primal_adj h }
  exact closed_chain_blocks (k := k) (n := n) (chainOfPath hn hpq) (openH ω) (openV ω)
    hH hV hfu hfv (w.map f)

/-- **Finite box duality on the very same `k n ω`.**  An open primal left-right
crossing of the box exists exactly when the closed-bond graph has no path from
below to above. -/
theorem primal_open_crossing_iff_no_closed_dual (hn : 0 < n) :
    PrimalOpenCrossing ω k n ↔ ¬ (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1) :=
  ⟨fun hp hc => no_primal_crossing_of_closed_reachable hn hc hp,
    fun hno => exists_primal_open_walk_of_no_closed_dual hn hno⟩

/-- **The XOR dichotomy.**  Exactly one of the two crossings exists. -/
theorem closed_reachable_xor_primal_open (hn : 0 < n) :
    (PrimalOpenCrossing ω k n ∧ ¬ (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)) ∨
      ((closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1) ∧ ¬ PrimalOpenCrossing ω k n) := by
  by_cases h : (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)
  · exact Or.inr ⟨h, no_primal_crossing_of_closed_reachable hn h⟩
  · exact Or.inl ⟨exists_primal_open_walk_of_no_closed_dual hn h, h⟩

/-! ## 8. Non-vacuity of both sides -/

/-- The all-closed configuration: the closed crossing exists (as produced in
`FK.PlaneTopology.PrimalClosedDuality`), so the theorem applies non-vacuously and
yields the absence of a primal crossing. -/
theorem allClosed_no_primal_crossing (hn : 0 < n) :
    ¬ PrimalOpenCrossing (fun _ : gridGraph.edgeSet => false) k n :=
  no_primal_crossing_of_closed_reachable hn (allClosed_closed_crossing hn)

/-- The all-open configuration: no closed crossing, and the primal crossing
exists.  Both sides of the equivalence are inhabited for `0 < n`. -/
theorem allOpen_primal_crossing (hn : 0 < n) :
    PrimalOpenCrossing (fun _ : gridGraph.edgeSet => true) k n :=
  (primal_open_crossing_iff_no_closed_dual (k := k) (n := n) hn).mpr
    (allOpen_no_closed_crossing (k := k) (n := n))

end FK.PlaneTopology.BoxSeamBridge

/-! ## 9. Principal declarations and trust -/

#print axioms FK.PlaneTopology.BoxSeamBridge.min_cast_add_one_eq_max_cast
#print axioms FK.PlaneTopology.BoxSeamBridge.DClosed_inr_zero_row
#print axioms FK.PlaneTopology.BoxSeamBridge.DClosed_top_row
#print axioms FK.PlaneTopology.BoxSeamBridge.CellAdj_of_DClosed
#print axioms FK.PlaneTopology.BoxSeamBridge.two_le_length
#print axioms FK.PlaneTopology.BoxSeamBridge.exists_cell
#print axioms FK.PlaneTopology.BoxSeamBridge.chainOfPath
#print axioms FK.PlaneTopology.BoxSeamBridge.chain_closedH
#print axioms FK.PlaneTopology.BoxSeamBridge.chain_closedV
#print axioms FK.PlaneTopology.BoxSeamBridge.chain_closedBot
#print axioms FK.PlaneTopology.BoxSeamBridge.chain_closedTop
#print axioms FK.PlaneTopology.BoxSeamBridge.chainSeam_mh_closed
#print axioms FK.PlaneTopology.BoxSeamBridge.chainSeam_mv_closed
#print axioms FK.PlaneTopology.BoxSeamBridge.openH_eq_true
#print axioms FK.PlaneTopology.BoxSeamBridge.openV_eq_true
#print axioms FK.PlaneTopology.BoxSeamBridge.toBox_fst
#print axioms FK.PlaneTopology.BoxSeamBridge.toBox_snd
#print axioms FK.PlaneTopology.BoxSeamBridge.boxAdj_vert_step
#print axioms FK.PlaneTopology.BoxSeamBridge.boxAdj_horiz_step
#print axioms FK.PlaneTopology.BoxSeamBridge.boxAdj_of_primal_adj
#print axioms FK.PlaneTopology.BoxSeamBridge.no_primal_crossing_of_closed_reachable
#print axioms FK.PlaneTopology.BoxSeamBridge.primal_open_crossing_iff_no_closed_dual
#print axioms FK.PlaneTopology.BoxSeamBridge.closed_reachable_xor_primal_open
#print axioms FK.PlaneTopology.BoxSeamBridge.allClosed_no_primal_crossing
#print axioms FK.PlaneTopology.BoxSeamBridge.allOpen_primal_crossing
