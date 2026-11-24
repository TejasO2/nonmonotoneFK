import FK.CutCrossingDuality

/-!
# Seam separation for the square-lattice box: the closed dual barrier direction

`FK.CutCrossingDuality` proves that a vertex labelling `a` of `ℤ × ℤ` whose left
wall lies in `a` and whose right wall lies outside `a` has a *cut* graph path
from below the box to above it.  That is the "no primal crossing, then a dual
crossing" direction of finite planar duality.

This module supplies the other, genuinely planar direction: **a closed dual
barrier blocks open primal crossings**.  The proof is an explicit parity
potential, not a Jordan curve theorem.

## Sealed barriers

The three hypotheses on a seam are the finite *sealed barrier* conditions: no
seam bond on the left or right wall (the barrier is sealed against the side
walls, so it can only enter through the bottom wall and leave through the top
wall), an even number of seam bonds around every cell (the barrier is a bond
chain, not a Primal crossing), and an odd number of seam bonds on the bottom row
(one entry).  The theorem below converts exactly these conditions into the
non-existence of an open primal left-right crossing.

## The potential

A `Seam` records, for every bond of the square lattice, the *parity* of the
number of seam bonds carried by that bond (`mh i j` for the horizontal bond
`(i,j)--(i+1,j)`, `mv i j` for the vertical bond `(i,j)--(i,j+1)`).  The parity
potential of a seam is

`Φ(x,y) = Σ_{i<x} mh i 0 + Σ_{j<y} mv x j`   (values in `ZMod 2`).

Its coboundary is the seam: `Φ_vert` and `Φ_horiz` show that `Φ` changes across a
bond exactly by that bond's seam parity, the horizontal case using the even-cell
condition and a telescoping sum.  Hence `Φ` is constant across every bond of
seam parity zero.

## Main results

* `Seam.Phi_vert`, `Seam.Phi_horiz` — the coboundary of the potential.
* `no_path` — **seam separation**: if no seam bond lies on the left or right
  wall, every cell of the box carries an even number of seam bonds, and the
  bottom row carries an odd number, then no box path from the left wall to the
  right wall runs only through zero-parity bonds.
* `cutSeam`, `cutBonds_separate` — the cut bonds of any labelling with the left
  wall inside and the right wall outside form such a seam, so they separate the
  two walls.  (The hypotheses are exactly the ones of `exists_cut_crossing`.)
* `CellChain`, `chainSeam`, `chainSeam_evenAround`, `chainSeam_oddBottom`,
  `chainSeam_wallLeft`, `chainSeam_wallRight` — a simple chain of box cells from
  the bottom row to the top row, together with the bonds it crosses and its
  bottom and top bonds, satisfies the three seam conditions: each cell is
  visited by an even number of chain bonds, the bottom row carries exactly the
  one entry-bond parity, and no chain bond lies on the left or right wall.
* `closed_chain_blocks` — **closed dual barrier**: for any bond configuration,
  if such a chain exists all of whose bonds are closed, then there is no open
  box path from the left wall to the right wall.
* `single_row_closed_barrier` — a non-vacuous one-row instance.
* `two_crossing_clusters_no_barrier` — a **precise finite obstruction**: the
  two-row configuration has two distinct open left-right crossing clusters while
  no bond of the bottom row is closed, so no closed dual chain enters the box.
  Hence "no closed dual crossing ⇒ at most one crossing cluster" is false in a
  finite box: the finite barrier controls existence, not uniqueness, of a
  crossing cluster.

Nothing here uses `sorry`, `admit`, custom axioms, `unsafe`, `native_decide` or
any heartbeat/trust override; the trust check is at the end of the file.
-/

namespace FK.PlaneTopology.BoxSeam

open Finset
open FK.PlaneTopology.CutCrossing

attribute [local instance] Classical.propDecidable

variable {k n : ℕ}

/-! ## Bonds, seams and the parity potential -/


/-- Bond parities of a seam on the lattice. -/
structure Seam where
  /-- parity of the seam bonds on the horizontal bond `(i,j)--(i+1,j)` -/
  mh : ℕ → ℕ → ZMod 2
  /-- parity of the seam bonds on the vertical bond `(i,j)--(i,j+1)` -/
  mv : ℕ → ℕ → ZMod 2

/-- Partial sums of a `ZMod 2`-valued sequence. -/
noncomputable def psum (f : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | (m+1) => psum f m + f m

lemma psum_add (f g : ℕ → ZMod 2) (m : ℕ) :
    psum (fun j => f j + g j) m = psum f m + psum g m := by
  induction m with
  | zero => simp [psum]
  | succ m ih => simp only [psum, ih]; abel

lemma psum_congr {f g : ℕ → ZMod 2} (m : ℕ) (h : ∀ j < m, f j = g j) :
    psum f m = psum g m := by
  induction m with
  | zero => simp [psum]
  | succ m ih => simp only [psum, ih (fun j hj => h j (by omega)), h m (by omega)]

lemma psum_telescope (f : ℕ → ZMod 2) (m : ℕ) :
    psum (fun j => f j + f (j+1)) m = f 0 + f m := by
  induction m with
  | zero => exact (CharTwo.add_self_eq_zero (f 0)).symm
  | succ m ih =>
      simp only [psum, ih]
      calc f 0 + f m + (f m + f (m+1))
          = f 0 + (f m + f m) + f (m+1) := by abel
        _ = f 0 + f (m+1) := by rw [CharTwo.add_self_eq_zero]; abel

lemma psum_eq_zero {f : ℕ → ZMod 2} (m : ℕ) (h : ∀ j < m, f j = 0) : psum f m = 0 := by
  induction m with
  | zero => simp [psum]
  | succ m ih => simp only [psum, ih (fun j hj => h j (by omega)), h m (by omega)]; abel

lemma psum_eq_finset_sum (f : ℕ → ZMod 2) (m : ℕ) :
    psum f m = ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp [psum]
  | succ m ih => rw [psum, ih, Finset.sum_range_succ]

lemma zmod2_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  calc x = x + 0 := by abel
    _ = x + (y + y) := by rw [CharTwo.add_self_eq_zero]
    _ = (x + y) + y := by abel
    _ = 0 + y := by rw [h]
    _ = y := by abel

lemma zmod2_one_of_odd {m : ℕ} (h : Odd m) : ((m : ℕ) : ZMod 2) = 1 := by
  obtain ⟨r, hr⟩ := h
  rw [hr]
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2]
  ring

namespace Seam

variable (S : Seam)

/-- No seam bond on the left wall. -/
def WallLeft : Prop := ∀ j : ℕ, S.mv 0 j = 0

/-- No seam bond on the right wall. -/
def WallRight (k : ℕ) : Prop := ∀ j : ℕ, S.mv (k+1) j = 0

/-- Each cell of the box carries an even number of seam bonds. -/
def EvenAround (k n : ℕ) : Prop := ∀ i j : ℕ, i < k+1 → j < n →
  (S.mv (i+1) j + S.mv i j) + (S.mh i j + S.mh i (j+1)) = 0

end Seam

/-- The parity potential `Φ(x,y) = Σ_{i<x} mh i 0 + Σ_{j<y} mv x j`. -/
noncomputable def Seam.Phi (S : Seam) (z : Fin (k+2) × Fin (n+1)) : ZMod 2 :=
  psum (fun i => S.mh i 0) z.1.val + psum (fun j => S.mv z.1.val j) z.2.val

/-- The vertical coboundary. -/
lemma Seam.Phi_vert (S : Seam) (i : Fin (k+2)) (j : Fin n) :
    S.Phi (i, j.succ) + S.Phi (i, j.castSucc) = S.mv i.val j.val := by
  unfold Seam.Phi
  simp only [Fin.val_succ, Fin.val_castSucc, psum]
  generalize psum (fun j => S.mv i.val j) j.val = B
  generalize psum (fun i_1 => S.mh i_1 0) i.val = A
  have hA : A + A = 0 := CharTwo.add_self_eq_zero A
  have hB : B + B = 0 := CharTwo.add_self_eq_zero B
  calc A + (B + S.mv i.val j.val) + (A + B)
      = (A + A) + (B + B) + S.mv i.val j.val := by abel
    _ = S.mv i.val j.val := by rw [hA, hB]; abel

/-- The horizontal coboundary, from the even-cell condition. -/
lemma Seam.Phi_horiz (S : Seam) (hE : S.EvenAround k n) (i : Fin (k+1)) (y : Fin (n+1)) :
    S.Phi (i.succ, y) + S.Phi (i.castSucc, y) = S.mh i.val y.val := by
  unfold Seam.Phi
  simp only [Fin.val_succ, Fin.val_castSucc, psum]
  have hcol : ∀ j < y.val,
      S.mv (i.val+1) j + S.mv i.val j = S.mh i.val j + S.mh i.val (j+1) := by
    intro j hj
    exact zmod2_eq_of_add_eq_zero (hE i.val j i.isLt (by omega))
  set P1 := psum (fun i_1 => S.mh i_1 0) i.val
  set Q1 := psum (fun j => S.mv i.val j) y.val
  set Q2 := psum (fun j => S.mv (i.val+1) j) y.val
  have hkey : Q2 + Q1 = S.mh i.val 0 + S.mh i.val y.val := by
    rw [← psum_add, psum_congr (f := fun j => S.mv (i.val+1) j + S.mv i.val j)
      (g := fun j => S.mh i.val j + S.mh i.val (j+1)) _ hcol, psum_telescope]
  have hP : P1 + P1 = 0 := CharTwo.add_self_eq_zero P1
  calc P1 + S.mh i.val 0 + Q2 + (P1 + Q1)
      = (P1 + P1) + S.mh i.val 0 + (Q2 + Q1) := by abel
    _ = 0 + S.mh i.val 0 + (Q2 + Q1) := by rw [hP]
    _ = S.mh i.val 0 + (Q2 + Q1) := by abel
    _ = S.mh i.val 0 + (S.mh i.val 0 + S.mh i.val y.val) := by rw [hkey]
    _ = S.mh i.val y.val := by
        have h : S.mh i.val 0 + S.mh i.val 0 = 0 := CharTwo.add_self_eq_zero _
        calc S.mh i.val 0 + (S.mh i.val 0 + S.mh i.val y.val)
            = (S.mh i.val 0 + S.mh i.val 0) + S.mh i.val y.val := by abel
          _ = S.mh i.val y.val := by rw [h]; abel

/-- Left-wall value of the potential. -/
lemma Seam.Phi_left (S : Seam) (hL : S.WallLeft) (y : Fin (n+1)) :
    S.Phi ((0 : Fin (k+2)), y) = 0 := by
  unfold Seam.Phi
  have h0 : (0 : Fin (k+2)).val = 0 := rfl
  rw [h0]
  have hv : psum (fun j => S.mv 0 j) y.val = 0 := by
    apply psum_eq_zero
    intro j _
    exact hL j
  rw [hv]
  simp [psum]

/-- Right-wall value of the potential: the bottom-row parity. -/
lemma Seam.Phi_right (S : Seam) (hR : S.WallRight k) (y : Fin (n+1))
    (hO : psum (fun i => S.mh i 0) (k+1) = 1) :
    S.Phi ((Fin.last (k+1)), y) = 1 := by
  unfold Seam.Phi
  have hval : (Fin.last (k+1) : Fin (k+2)).val = k+1 := Fin.val_last (k+1)
  rw [hval, hO]
  have hv : psum (fun j => S.mv (k+1) j) y.val = 0 := by
    apply psum_eq_zero
    intro j _
    exact hR j
  rw [hv, add_zero]

/-! ## The box graph with seam bonds removed, and the separation theorem -/

/-- Adjacency of box vertices across a bond that carries no seam bond. -/
def boxAdj (S : Seam) (u v : Fin (k+2) × Fin (n+1)) : Prop :=
  (∃ (i : Fin (k+1)) (j : Fin (n+1)), S.mh i.val j.val = 0 ∧
      ((u = (i.castSucc, j) ∧ v = (i.succ, j)) ∨
       (v = (i.castSucc, j) ∧ u = (i.succ, j)))) ∨
  (∃ (i : Fin (k+2)) (j : Fin n), S.mv i.val j.val = 0 ∧
      ((u = (i, j.castSucc) ∧ v = (i, j.succ)) ∨
       (v = (i, j.castSucc) ∧ u = (i, j.succ))))

lemma boxAdj_symm {S : Seam} {u v : Fin (k+2) × Fin (n+1)} (h : boxAdj S u v) :
    boxAdj S v u := by
  rcases h with ⟨i, j, hm, h | h⟩ | ⟨i, j, hm, h | h⟩
  · exact Or.inl ⟨i, j, hm, Or.inr h⟩
  · exact Or.inl ⟨i, j, hm, Or.inl h⟩
  · exact Or.inr ⟨i, j, hm, Or.inr h⟩
  · exact Or.inr ⟨i, j, hm, Or.inl h⟩

lemma boxAdj_irrefl {S : Seam} {u : Fin (k+2) × Fin (n+1)} : ¬ boxAdj S u u := by
  rintro (⟨i, j, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨i, j, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩)
  · have := congrArg (fun z : Fin (k+2) × Fin (n+1) => z.1.val) (h1.symm.trans h2)
    simp at this
  · have := congrArg (fun z : Fin (k+2) × Fin (n+1) => z.1.val) (h1.symm.trans h2)
    simp at this
  · have := congrArg (fun z : Fin (k+2) × Fin (n+1) => z.2.val) (h1.symm.trans h2)
    simp at this
  · have := congrArg (fun z : Fin (k+2) × Fin (n+1) => z.2.val) (h1.symm.trans h2)
    simp at this

/-- The box's primal graph with the seam bonds removed. -/
def boxGraph (S : Seam) : SimpleGraph (Fin (k+2) × Fin (n+1)) where
  Adj := boxAdj S
  symm := ⟨fun _ _ h => boxAdj_symm h⟩
  loopless := ⟨fun _ h => boxAdj_irrefl h⟩

/-- The potential is constant across every seam-free bond. -/
lemma Phi_const_of_adj (S : Seam) (hE : S.EvenAround k n) {u v : Fin (k+2) × Fin (n+1)}
    (h : boxAdj S u v) : S.Phi u = S.Phi v := by
  rcases h with ⟨i, j, hm, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, j, hm, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · have hh := S.Phi_horiz hE i j
    rw [hm] at hh
    exact (zmod2_eq_of_add_eq_zero hh).symm
  · have hh := S.Phi_horiz hE i j
    rw [hm] at hh
    exact zmod2_eq_of_add_eq_zero hh
  · have hh := S.Phi_vert i j
    rw [hm] at hh
    exact (zmod2_eq_of_add_eq_zero hh).symm
  · have hh := S.Phi_vert i j
    rw [hm] at hh
    exact zmod2_eq_of_add_eq_zero hh

/-- **Seam separation.**  In the box, no vertex of the left wall is connected to a
vertex of the right wall by a path whose bonds all carry zero seam parity. -/
theorem no_path (S : Seam) (hL : S.WallLeft) (hR : S.WallRight k) (hE : S.EvenAround k n)
    (hO : psum (fun i => S.mh i 0) (k+1) = 1)
    {u v : Fin (k+2) × Fin (n+1)} (hu : u.1 = 0) (hv : v.1 = Fin.last (k+1))
    (p : (boxGraph S).Walk u v) : False := by
  have hconst_all : ∀ {u v : Fin (k+2) × Fin (n+1)} (p : (boxGraph S).Walk u v),
      S.Phi u = S.Phi v := by
    intro u v p
    induction p with
    | nil => rfl
    | cons h p ih => exact (Phi_const_of_adj S hE h).trans ih
  have hconst : S.Phi u = S.Phi v := hconst_all p
  have hu0 : S.Phi u = 0 := by
    have h : u = ((0 : Fin (k+2)), u.2) := Prod.ext hu rfl
    rw [h]
    exact S.Phi_left hL u.2
  have hv1 : S.Phi v = 1 := by
    have h : v = ((Fin.last (k+1) : Fin (k+2)), v.2) := Prod.ext hv rfl
    rw [h]
    exact S.Phi_right hR v.2 hO
  rw [hu0, hv1] at hconst
  exact zero_ne_one hconst

/-! ## The cut-bond seam of a vertex labelling -/

/-- The seam of cut bonds of a labelling `a`. -/
noncomputable def cutSeam (a : ℤ → ℤ → Bool) : Seam where
  mh i j := if hCut a (i:ℤ) (j:ℤ) then 1 else 0
  mv i j := if vCut a (i:ℤ) (j:ℤ) then 1 else 0

/-- The four-bond parity of a boolean square. -/
lemma bool_parity (p q r s : Bool) :
    ((if (q != s) then (1:ZMod 2) else 0) + (if (p != r) then (1:ZMod 2) else 0))
      + ((if (p != q) then (1:ZMod 2) else 0) + (if (r != s) then (1:ZMod 2) else 0)) = 0 := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

lemma cutSeam_evenAround (a : ℤ → ℤ → Bool) : (cutSeam a).EvenAround k n := by
  intro i j _ _
  have hi : ((i+1 : ℕ) : ℤ) = (i:ℤ) + 1 := by push_cast; ring
  have hj : ((j+1 : ℕ) : ℤ) = (j:ℤ) + 1 := by push_cast; ring
  simp only [cutSeam, hCut, vCut, hi, hj]
  exact bool_parity _ _ _ _

lemma cutSeam_wallLeft (a : ℤ → ℤ → Bool) (h : ∀ j : ℤ, a 0 j = true) :
    (cutSeam a).WallLeft := by
  intro j
  show (if vCut a ((0:ℕ):ℤ) (j:ℤ) then (1:ZMod 2) else 0) = 0
  rw [show ((0:ℕ):ℤ) = 0 from rfl, vCut_zero_col h (j:ℤ)]
  rfl

lemma cutSeam_wallRight (a : ℤ → ℤ → Bool) (k : ℕ)
    (h : ∀ j : ℤ, a ((k:ℤ)+1) j = false) : (cutSeam a).WallRight k := by
  intro j
  have hcast : ((k+1 : ℕ) : ℤ) = (k:ℤ)+1 := by push_cast; ring
  show (if vCut a ((k+1:ℕ):ℤ) (j:ℤ) then (1:ZMod 2) else 0) = 0
  rw [hcast, vCut_last_col h (j:ℤ)]
  rfl

lemma cutSeam_oddBottom (a : ℤ → ℤ → Bool) (k : ℕ)
    (h0 : a 0 0 = true) (h1 : a ((k:ℤ)+1) 0 = false) :
    psum (fun i => (cutSeam a).mh i 0) (k+1) = 1 := by
  have hodd : (((Finset.range (k+1)).filter
      (fun i : ℕ => hCut a (i:ℤ) 0 = true)).card : ZMod 2) = 1 :=
    zmod2_one_of_odd (odd_changes a 0 h0 h1)
  have hsummand : ∀ i : ℕ, (cutSeam a).mh i 0
      = (if hCut a (i:ℤ) 0 = true then (1:ZMod 2) else 0) := by
    intro i; rfl
  calc psum (fun i => (cutSeam a).mh i 0) (k+1)
      = ∑ i ∈ Finset.range (k+1), (cutSeam a).mh i 0 := psum_eq_finset_sum _ _
    _ = ∑ i ∈ Finset.range (k+1), (if hCut a (i:ℤ) 0 = true then (1:ZMod 2) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsummand i
    _ = (((Finset.range (k+1)).filter (fun i : ℕ => hCut a (i:ℤ) 0 = true)).card : ZMod 2) :=
        Finset.sum_boole _ _
    _ = 1 := hodd

/-- **The cut bonds of a labelling separate the box.**  If the left wall of the
box lies in `a` and the right wall outside `a`, no box path from the left wall
to the right wall avoids the cut bonds of `a`. -/
theorem cutBonds_separate (a : ℤ → ℤ → Bool) {k n : ℕ}
    (hleft : ∀ j : ℤ, a 0 j = true) (hright : ∀ j : ℤ, a ((k:ℤ)+1) j = false)
    {u v : Fin (k+2) × Fin (n+1)} (hu : u.1 = 0) (hv : v.1 = Fin.last (k+1))
    (p : (boxGraph (cutSeam a)).Walk u v) : False :=
  no_path (cutSeam a) (cutSeam_wallLeft a hleft) (cutSeam_wallRight a k hright)
    (cutSeam_evenAround a) (cutSeam_oddBottom a k (hleft 0) (hright 0)) hu hv p



/-!
# Closed dual chains seal the primal box
-/


/-- An indicator as an element of `ZMod 2`. -/
noncomputable def ind (P : Prop) : ZMod 2 := if P then 1 else 0

lemma ind_pos {P : Prop} (h : P) : ind P = 1 := ite_eq_left h

lemma ind_neg {P : Prop} (h : ¬P) : ind P = 0 := ite_eq_right h

lemma ind_split (P Q : Prop) : ind (Q ∧ P) + ind (¬Q ∧ P) = ind P := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ind, hP, hQ]

lemma ind_and_neg (P Q : Prop) : ind (P ∧ ¬Q) + ind (P ∧ Q) = ind P := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ind, hP, hQ]

/-- Two cells sharing a side. -/
def CellAdj (c d : Fin (k+1) × Fin n) : Prop :=
  (c.2 = d.2 ∧ (c.1.val + 1 = d.1.val ∨ d.1.val + 1 = c.1.val)) ∨
  (c.1 = d.1 ∧ (c.2.val + 1 = d.2.val ∨ d.2.val + 1 = c.2.val))

/-- A simple chain of box cells from the bottom row to the top row. -/
structure CellChain (k n : ℕ) where
  len : ℕ
  cell : Fin (len+1) → Fin (k+1) × Fin n
  adj : ∀ t : Fin len, CellAdj (cell t.castSucc) (cell t.succ)
  inj : Function.Injective cell
  start_row : (cell 0).2.val = 0
  end_row : (cell (Fin.last len)).2.val = n - 1

variable (C : CellChain k n)

lemma CellChain.n_pos (C : CellChain k n) : 0 < n := by
  have h := (C.cell (Fin.last C.len)).2.isLt
  rw [C.end_row] at h
  omega

/-- The step stays in one column (so it crosses a horizontal bond). -/
def stepUp (t : Fin C.len) : Prop := (C.cell t.castSucc).1 = (C.cell t.succ).1

/-- Index of the horizontal bond crossed by a vertical step. -/
def bondH (t : Fin C.len) : ℕ × ℕ :=
  ((C.cell t.castSucc).1.val, max (C.cell t.castSucc).2.val (C.cell t.succ).2.val)

/-- Index of the vertical bond crossed by a horizontal step. -/
def bondV (t : Fin C.len) : ℕ × ℕ :=
  (max (C.cell t.castSucc).1.val (C.cell t.succ).1.val, (C.cell t.castSucc).2.val)

lemma rows_of_stepUp {t : Fin C.len} (h : stepUp C t) :
    (C.cell t.castSucc).2.val + 1 = (C.cell t.succ).2.val ∨
      (C.cell t.succ).2.val + 1 = (C.cell t.castSucc).2.val := by
  rcases C.adj t with ⟨hr, _⟩ | ⟨-, hr⟩
  · exfalso
    have hce : C.cell t.castSucc = C.cell t.succ := Prod.ext h hr
    have hfin : t.castSucc = t.succ := C.inj hce
    have := congrArg Fin.val hfin
    simp at this
  · exact hr

lemma cols_of_not_stepUp {t : Fin C.len} (h : ¬ stepUp C t) :
    (C.cell t.castSucc).1.val + 1 = (C.cell t.succ).1.val ∨
      (C.cell t.succ).1.val + 1 = (C.cell t.castSucc).1.val := by
  rcases C.adj t with ⟨-, hc⟩ | ⟨hc, _⟩
  · exact hc
  · exfalso
    exact h hc


/-- Arithmetic core for a vertical step. -/
lemma arith_up (col rA rB i j : ℕ) (hr : rA + 1 = rB ∨ rB + 1 = rA) :
    ind ((col, max rA rB) = (i, j)) + ind ((col, max rA rB) = (i, j+1))
      = ind (i = col ∧ j = rA) + ind (i = col ∧ j = rB) := by
  rcases hr with hr | hr
  · have hmax : max rA rB = rB := by omega
    rw [hmax]
    have e1 : ((col, rB) = (i, j)) ↔ (i = col ∧ j = rB) := by
      simp only [Prod.ext_iff]
      constructor <;> intro h <;> exact ⟨h.1.symm, h.2.symm⟩
    have e2 : ((col, rB) = (i, j+1)) ↔ (i = col ∧ j = rA) := by
      simp only [Prod.ext_iff]; omega
    simp only [e1, e2]
    exact add_comm _ _
  · have hmax : max rA rB = rA := by omega
    rw [hmax]
    have e1 : ((col, rA) = (i, j)) ↔ (i = col ∧ j = rA) := by
      simp only [Prod.ext_iff]
      constructor <;> intro h <;> exact ⟨h.1.symm, h.2.symm⟩
    have e2 : ((col, rA) = (i, j+1)) ↔ (i = col ∧ j = rB) := by
      simp only [Prod.ext_iff]; omega
    simp only [e1, e2]

/-- Arithmetic core for a horizontal step. -/
lemma arith_left (row cA cB i j : ℕ) (hc : cA + 1 = cB ∨ cB + 1 = cA) :
    ind ((max cA cB, row) = (i, j)) + ind ((max cA cB, row) = (i+1, j))
      = ind (i = cA ∧ j = row) + ind (i = cB ∧ j = row) := by
  rcases hc with hc | hc
  · have hmax : max cA cB = cB := by omega
    rw [hmax]
    have e1 : ((cB, row) = (i, j)) ↔ (i = cB ∧ j = row) := by
      simp only [Prod.ext_iff]
      constructor <;> intro h <;> exact ⟨h.1.symm, h.2.symm⟩
    have e2 : ((cB, row) = (i+1, j)) ↔ (i = cA ∧ j = row) := by
      simp only [Prod.ext_iff]; omega
    simp only [e1, e2]
    exact add_comm _ _
  · have hmax : max cA cB = cA := by omega
    rw [hmax]
    have e1 : ((cA, row) = (i, j)) ↔ (i = cA ∧ j = row) := by
      simp only [Prod.ext_iff]
      constructor <;> intro h <;> exact ⟨h.1.symm, h.2.symm⟩
    have e2 : ((cA, row) = (i+1, j)) ↔ (i = cB ∧ j = row) := by
      simp only [Prod.ext_iff]; omega
    simp only [e1, e2]


/-- A cardinality is a sum of indicators mod 2. -/
lemma card_eq_sum_ind {m : ℕ} {p : Fin m → Prop} :
    ((Finset.univ.filter p).card : ZMod 2) = ∑ t : Fin m, ind (p t) := by
  rw [← Finset.sum_boole (fun t => p t) Finset.univ]
  apply Finset.sum_congr rfl
  intro t _
  rfl


lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by
  by_cases hP : P
  · have hQ : Q := h.mp hP
    simp [ind, hP, hQ]
  · have hQ : ¬Q := fun hq => hP (h.mpr hq)
    simp [ind, hP, hQ]

lemma ind_of_and_left {P Q : Prop} (h : P) : ind (P ∧ Q) = ind Q :=
  ind_congr (by simp [h])

lemma ind_zero_of_and_left {P Q : Prop} (h : ¬P) : ind (P ∧ Q) = 0 :=
  ind_neg (by simp [h])

lemma ind_of_and_left_neg {P Q : Prop} (h : ¬P) : ind (¬P ∧ Q) = ind Q :=
  ind_congr (by simp [h])

lemma ind_zero_of_and_left_neg {P Q : Prop} (h : P) : ind (¬P ∧ Q) = 0 :=
  ind_neg (by simp [h])

/-- Per-step count for a vertical step. -/
lemma stepH_count (t : Fin C.len) (h : stepUp C t) (c : Fin (k+1) × Fin n) :
    ind (bondH C t = (c.1.val, c.2.val)) + ind (bondH C t = (c.1.val, c.2.val + 1))
      = ind (c = C.cell t.castSucc) + ind (c = C.cell t.succ) := by
  have hcol : (C.cell t.castSucc).1.val = (C.cell t.succ).1.val := congrArg Fin.val h
  have hr := rows_of_stepUp C h
  have key := arith_up (C.cell t.castSucc).1.val (C.cell t.castSucc).2.val
    (C.cell t.succ).2.val c.1.val c.2.val hr
  simp only [bondH] at key ⊢
  rw [key]
  have e1 : ind (c.1.val = (C.cell t.castSucc).1.val ∧ c.2.val = (C.cell t.castSucc).2.val)
      = ind (c = C.cell t.castSucc) := by
    apply ind_congr; simp [Prod.ext_iff, Fin.ext_iff]
  have e2 : ind (c.1.val = (C.cell t.castSucc).1.val ∧ c.2.val = (C.cell t.succ).2.val)
      = ind (c = C.cell t.succ) := by
    apply ind_congr; simp [Prod.ext_iff, Fin.ext_iff, hcol]
  rw [e1, e2]

/-- Per-step count for a horizontal step. -/
lemma stepV_count (t : Fin C.len) (h : ¬ stepUp C t) (c : Fin (k+1) × Fin n) :
    ind (bondV C t = (c.1.val, c.2.val)) + ind (bondV C t = (c.1.val + 1, c.2.val))
      = ind (c = C.cell t.castSucc) + ind (c = C.cell t.succ) := by
  have hrow : (C.cell t.castSucc).2.val = (C.cell t.succ).2.val := by
    rcases C.adj t with ⟨hr, -⟩ | ⟨hc, -⟩
    · exact congrArg Fin.val hr
    · exact absurd hc h
  have hc := cols_of_not_stepUp C h
  have key := arith_left (C.cell t.castSucc).2.val (C.cell t.castSucc).1.val
    (C.cell t.succ).1.val c.1.val c.2.val hc
  simp only [bondV] at key ⊢
  rw [key]
  have e1 : ind (c.1.val = (C.cell t.castSucc).1.val ∧ c.2.val = (C.cell t.castSucc).2.val)
      = ind (c = C.cell t.castSucc) := by
    apply ind_congr; simp [Prod.ext_iff, Fin.ext_iff]
  have e2 : ind (c.1.val = (C.cell t.succ).1.val ∧ c.2.val = (C.cell t.castSucc).2.val)
      = ind (c = C.cell t.succ) := by
    apply ind_congr; simp [Prod.ext_iff, Fin.ext_iff, hrow]
  rw [e1, e2]

/-- The total per-step contribution. -/
lemma step_total (t : Fin C.len) (c : Fin (k+1) × Fin n) :
    ind (stepUp C t ∧ bondH C t = (c.1.val, c.2.val))
    + ind (stepUp C t ∧ bondH C t = (c.1.val, c.2.val + 1))
    + ind (¬ stepUp C t ∧ bondV C t = (c.1.val, c.2.val))
    + ind (¬ stepUp C t ∧ bondV C t = (c.1.val + 1, c.2.val))
    = ind (c = C.cell t.castSucc) + ind (c = C.cell t.succ) := by
  by_cases h : stepUp C t
  · rw [ind_of_and_left h, ind_of_and_left h, ind_zero_of_and_left_neg h,
      ind_zero_of_and_left_neg h, add_zero, add_zero, stepH_count C t h c]
  · rw [ind_zero_of_and_left h, ind_zero_of_and_left h, ind_of_and_left_neg h,
      ind_of_and_left_neg h, zero_add, zero_add, stepV_count C t h c]

/-- The seam of a cell chain: the crossed bonds together with the bottom and top bonds. -/
noncomputable def chainSeam (C : CellChain k n) : Seam where
  mh i j := ind (j = 0 ∧ (C.cell 0).1.val = i)
    + ind (j = n ∧ (C.cell (Fin.last C.len)).1.val = i)
    + ∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j))
  mv i j := ∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j))

/-- **Even-cell parity of a chain seam.** -/
lemma chainSeam_evenAround (C : CellChain k n) : (chainSeam C).EvenAround k n := by
  intro i j hi hj
  set c : Fin (k+1) × Fin n := (⟨i, hi⟩, ⟨j, hj⟩) with hcdef
  have hc1 : c.1.val = i := rfl
  have hc2 : c.2.val = j := rfl
  have e_bot : ind (j = 0 ∧ (C.cell 0).1.val = i) = ind (c = C.cell 0) := by
    apply ind_congr
    constructor
    · rintro ⟨h0, hcol⟩
      have hrow : c.2.val = (C.cell 0).2.val := by rw [hc2, h0, C.start_row]
      exact Prod.ext (Fin.ext (by rw [hc1, hcol]) ) (Fin.ext hrow)
    · intro h
      refine ⟨?_, ?_⟩
      · have := congrArg (fun z => z.2.val) h
        rw [hc2] at this
        rw [this, C.start_row]
      · have := congrArg (fun z => z.1.val) h
        rw [hc1] at this
        exact this.symm
  have e_top : ind (j+1 = n ∧ (C.cell (Fin.last C.len)).1.val = i)
      = ind (c = C.cell (Fin.last C.len)) := by
    apply ind_congr
    constructor
    · rintro ⟨hlast, hcol⟩
      have hrow : c.2.val = (C.cell (Fin.last C.len)).2.val := by
        rw [hc2, C.end_row]; omega
      exact Prod.ext (Fin.ext (by rw [hc1, hcol])) (Fin.ext hrow)
    · intro h
      refine ⟨?_, ?_⟩
      · have := congrArg (fun z => z.2.val) h
        rw [hc2, C.end_row] at this
        omega
      · have := congrArg (fun z => z.1.val) h
        rw [hc1] at this
        exact this.symm
  have e_bot' : ind (j+1 = 0 ∧ (C.cell 0).1.val = i) = 0 := ind_neg (by omega)
  have e_top' : ind (j = n ∧ (C.cell (Fin.last C.len)).1.val = i) = 0 := ind_neg (by omega)
  have hsum : (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j)))
      + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j+1)))
      + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j)))
      + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i+1, j)))
      = (∑ t : Fin C.len, ind (c = C.cell t.castSucc))
        + (∑ t : Fin C.len, ind (c = C.cell t.succ)) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← hc1, ← hc2]
    exact step_total C t c
  have hvisits : (∑ t : Fin C.len, ind (c = C.cell t.castSucc))
      + (∑ t : Fin C.len, ind (c = C.cell t.succ))
      + ind (c = C.cell (Fin.last C.len)) + ind (c = C.cell 0) = 0 := by
    set F : Fin (C.len+1) → ZMod 2 := fun u => ind (c = C.cell u) with hF
    have h1 : (∑ u, F u) = (∑ t : Fin C.len, F t.castSucc) + F (Fin.last C.len) :=
      Fin.sum_univ_castSucc F
    have h2 : (∑ u, F u) = F 0 + (∑ t : Fin C.len, F t.succ) := Fin.sum_univ_succ F
    have h4 : (∑ t : Fin C.len, F t.castSucc) + F (Fin.last C.len)
        = F 0 + (∑ t : Fin C.len, F t.succ) := by rw [← h1, ← h2]
    have hF2 : F (Fin.last C.len) + F (Fin.last C.len) = 0 := CharTwo.add_self_eq_zero _
    have key : (∑ t : Fin C.len, F t.castSucc) + (∑ t : Fin C.len, F t.succ)
        = F 0 + F (Fin.last C.len) := by
      calc (∑ t : Fin C.len, F t.castSucc) + (∑ t : Fin C.len, F t.succ)
          = ((∑ t : Fin C.len, F t.castSucc) + F (Fin.last C.len))
              + ((∑ t : Fin C.len, F t.succ) + F (Fin.last C.len)) := by
            rw [show ((∑ t : Fin C.len, F t.castSucc) + F (Fin.last C.len))
                  + ((∑ t : Fin C.len, F t.succ) + F (Fin.last C.len))
                = ((∑ t : Fin C.len, F t.castSucc) + (∑ t : Fin C.len, F t.succ))
                  + (F (Fin.last C.len) + F (Fin.last C.len)) from by abel, hF2, add_zero]
        _ = (F 0 + (∑ t : Fin C.len, F t.succ))
              + ((∑ t : Fin C.len, F t.succ) + F (Fin.last C.len)) := by rw [h4]
        _ = F 0 + F (Fin.last C.len) := by
            rw [show F 0 + (∑ t : Fin C.len, F t.succ)
                  + ((∑ t : Fin C.len, F t.succ) + F (Fin.last C.len))
                = (F 0 + F (Fin.last C.len))
                  + ((∑ t : Fin C.len, F t.succ) + (∑ t : Fin C.len, F t.succ)) from by abel,
              CharTwo.add_self_eq_zero, add_zero]
    have hgoal : (∑ t : Fin C.len, F t.castSucc) + (∑ t : Fin C.len, F t.succ)
        + F (Fin.last C.len) + F 0 = 0 := by
      rw [key]
      rw [show F 0 + F (Fin.last C.len) + F (Fin.last C.len) + F 0
          = (F 0 + F 0) + (F (Fin.last C.len) + F (Fin.last C.len)) from by abel,
        CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    exact hgoal
  have expand : (chainSeam C).mv (i+1) j + (chainSeam C).mv i j
      + ((chainSeam C).mh i j + (chainSeam C).mh i (j+1))
      = (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i+1, j)))
        + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j)))
        + ((ind (c = C.cell 0)
            + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j))))
          + (ind (c = C.cell (Fin.last C.len))
            + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j+1))))) := by
    simp only [chainSeam, e_bot, e_top, e_bot', e_top', zero_add]
    abel
  rw [expand]
  have finish : (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i+1, j)))
        + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j)))
        + ((ind (c = C.cell 0)
            + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j))))
          + (ind (c = C.cell (Fin.last C.len))
            + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j+1))))) = 0 := by
    have e : (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i+1, j)))
          + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j)))
          + ((ind (c = C.cell 0)
              + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j))))
            + (ind (c = C.cell (Fin.last C.len))
              + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j+1)))))
        = ((∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j)))
            + (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, j+1)))
            + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i, j)))
            + (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (i+1, j))))
          + (ind (c = C.cell 0) + ind (c = C.cell (Fin.last C.len))) := by abel
    rw [e, hsum]
    rw [show (∑ t : Fin C.len, ind (c = C.cell t.castSucc))
          + (∑ t : Fin C.len, ind (c = C.cell t.succ))
          + (ind (c = C.cell 0) + ind (c = C.cell (Fin.last C.len)))
        = (∑ t : Fin C.len, ind (c = C.cell t.castSucc))
          + (∑ t : Fin C.len, ind (c = C.cell t.succ))
          + ind (c = C.cell (Fin.last C.len)) + ind (c = C.cell 0) from by abel]
    exact hvisits
  exact finish

/-- A chain seam carries no bond on the left wall. -/
lemma chainSeam_wallLeft (C : CellChain k n) : (chainSeam C).WallLeft := by
  intro j
  show (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (0, j))) = 0
  apply Finset.sum_eq_zero
  intro t _
  apply ind_neg
  rintro ⟨h, hb⟩
  have hc := cols_of_not_stepUp C h
  have hmax : max (C.cell t.castSucc).1.val (C.cell t.succ).1.val = 0 := by
    have := congrArg Prod.fst hb
    simpa [bondV] using this
  omega

/-- A chain seam carries no bond on the right wall. -/
lemma chainSeam_wallRight (C : CellChain k n) : (chainSeam C).WallRight k := by
  intro j
  show (∑ t : Fin C.len, ind (¬ stepUp C t ∧ bondV C t = (k+1, j))) = 0
  apply Finset.sum_eq_zero
  intro t _
  apply ind_neg
  rintro ⟨h, hb⟩
  have hc := cols_of_not_stepUp C h
  have h1 : (C.cell t.castSucc).1.val ≤ k := by have := (C.cell t.castSucc).1.isLt; omega
  have h2 : (C.cell t.succ).1.val ≤ k := by have := (C.cell t.succ).1.isLt; omega
  have hmax : max (C.cell t.castSucc).1.val (C.cell t.succ).1.val = k+1 := by
    have := congrArg Prod.fst hb
    simpa [bondV] using this
  omega

/-- The bottom row of a chain seam is odd. -/
lemma chainSeam_oddBottom (C : CellChain k n) :
    psum (fun i => (chainSeam C).mh i 0) (k+1) = 1 := by
  have hpt : ∀ i : ℕ, (chainSeam C).mh i 0 = ind ((C.cell 0).1.val = i) := by
    intro i
    have hstep : (∑ t : Fin C.len, ind (stepUp C t ∧ bondH C t = (i, 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      apply ind_neg
      rintro ⟨hu, hb⟩
      have hr := rows_of_stepUp C hu
      have hmax : max (C.cell t.castSucc).2.val (C.cell t.succ).2.val = 0 := by
        have := congrArg Prod.snd hb
        simpa [bondH] using this
      omega
    have htop : ind (0 = n ∧ (C.cell (Fin.last C.len)).1.val = i) = 0 := by
      apply ind_neg
      have := C.n_pos
      omega
    have hbot : ind (True ∧ (C.cell 0).1.val = i) = ind ((C.cell 0).1.val = i) :=
      ind_congr (by simp)
    simp only [chainSeam, hbot, htop, hstep, add_zero]
  rw [psum_eq_finset_sum]
  simp only [hpt]
  have hmem : (C.cell 0).1.val < k+1 := (C.cell 0).1.isLt
  rw [Finset.sum_eq_single (C.cell 0).1.val]
  · rw [ind_pos rfl]
  · intro i _ hi
    exact ind_neg (fun h => hi h.symm)
  · intro h
    exact absurd (Finset.mem_range.mpr hmem) h

/-- The seam of an open-bond configuration: a bond is free exactly when open. -/
noncomputable def openSeam (openH openV : ℕ → ℕ → Bool) : Seam where
  mh i j := if openH i j then 0 else 1
  mv i j := if openV i j then 0 else 1

/-- **A closed dual chain blocks every open primal left-right path.**

`openH`/`openV` are the open-bond indicators of a bond configuration.  The two
hypotheses say that every open bond carries no seam bond of the chain, i.e. that
every bond crossed by the chain is closed. -/
theorem closed_chain_blocks (C : CellChain k n) (openH openV : ℕ → ℕ → Bool)
    (hH : ∀ i j, openH i j = true → (chainSeam C).mh i j = 0)
    (hV : ∀ i j, openV i j = true → (chainSeam C).mv i j = 0)
    {u v : Fin (k+2) × Fin (n+1)} (hu : u.1 = 0) (hv : v.1 = Fin.last (k+1))
    (p : (boxGraph (k := k) (n := n) (openSeam openH openV)).Walk u v) : False := by
  have hH' : ∀ i j, (openSeam openH openV).mh i j = 0 → (chainSeam C).mh i j = 0 := by
    intro i j hm
    by_cases hh : openH i j = true
    · exact hH i j hh
    · exfalso
      have h1 : (openSeam openH openV).mh i j = 1 := by
        simp only [openSeam]
        rw [ite_eq_right hh]
      exact one_ne_zero (h1 ▸ hm)
  have hV' : ∀ i j, (openSeam openH openV).mv i j = 0 → (chainSeam C).mv i j = 0 := by
    intro i j hm
    by_cases hh : openV i j = true
    · exact hV i j hh
    · exfalso
      have h1 : (openSeam openH openV).mv i j = 1 := by
        simp only [openSeam]
        rw [ite_eq_right hh]
      exact one_ne_zero (h1 ▸ hm)
  have hle : ∀ x y : Fin (k+2) × Fin (n+1),
      boxAdj (openSeam openH openV) x y → boxAdj (chainSeam C) x y := by
    rintro x y (⟨i, j, hm, h⟩ | ⟨i, j, hm, h⟩)
    · exact Or.inl ⟨i, j, hH' i j hm, h⟩
    · exact Or.inr ⟨i, j, hV' i j hm, h⟩
  let f : boxGraph (openSeam openH openV) →g boxGraph (chainSeam C) :=
    { toFun := id, map_rel' := fun h => hle _ _ h }
  exact no_path (k := k) (n := n) (chainSeam C) (chainSeam_wallLeft C) (chainSeam_wallRight C)
    (chainSeam_evenAround C) (chainSeam_oddBottom C) hu hv (p.map f)

/-! ## A non-vacuous instance: a one-row box and a single-cell chain -/

/-- In a one-row box, a single cell is a chain from the bottom to the top row. -/
def singleChain (c : Fin (k+1)) (hn : n = 1) : CellChain k n where
  len := 0
  cell := fun _ => (c, ⟨0, by omega⟩)
  adj := fun t => absurd t.isLt (by omega)
  inj := fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)
  start_row := rfl
  end_row := by
    change 0 = n - 1
    omega

/-- The single-cell seam is supported exactly on the bottom and top bonds of the cell. -/
lemma singleChain_mh (c : Fin (k+1)) (hn : n = 1) (i j : ℕ) :
    (chainSeam (singleChain c hn)).mh i j
      = ind (j = 0 ∧ c.val = i) + ind (j = n ∧ c.val = i) := by
  have hempty : (∑ t : Fin (singleChain c hn).len,
      ind (stepUp (singleChain c hn) t ∧ bondH (singleChain c hn) t = (i, j))) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact absurd t.isLt (by simp [singleChain])
  have hcell0 : (singleChain c hn).cell 0 = (c, ⟨0, by omega⟩) := rfl
  have hcellL : (singleChain c hn).cell (Fin.last (singleChain c hn).len)
      = (c, ⟨0, by omega⟩) := rfl
  simp only [chainSeam, hcell0, hcellL, hempty, add_zero]

/-- **Concrete obstruction.**  In a box with a single row of cells, if the bottom
and top bonds of one cell are closed, then no open path joins the left wall to
the right wall. -/
theorem single_row_closed_barrier (c : Fin (k+1)) (hn : n = 1)
    (openH openV : ℕ → ℕ → Bool)
    (hbot : openH c.val 0 = false) (htop : openH c.val n = false) :
    ∀ {u v : Fin (k+2) × Fin (n+1)}, u.1 = 0 → v.1 = Fin.last (k+1) →
      ¬ Nonempty ((boxGraph (k := k) (n := n) (openSeam openH openV)).Walk u v) := by
  intro u v hu hv ⟨p⟩
  refine closed_chain_blocks (singleChain c hn) openH openV ?_ ?_ hu hv p
  · intro i j hoj
    rw [singleChain_mh c hn]
    by_cases h1 : j = 0 ∧ c.val = i
    · exfalso
      obtain ⟨rfl, rfl⟩ := h1
      rw [hbot] at hoj
      exact Bool.false_eq_true.mp hoj
    · by_cases h2 : j = n ∧ c.val = i
      · exfalso
        obtain ⟨rfl, rfl⟩ := h2
        rw [htop] at hoj
        exact Bool.false_eq_true.mp hoj
      · rw [ind_neg h1, ind_neg h2, add_zero]
  · intro i j _
    simp only [chainSeam]
    apply Finset.sum_eq_zero
    intro t _
    exact absurd t.isLt (by simp [singleChain])




/-! ## A precise finite obstruction: two crossing clusters without a dual barrier

The barrier theorem gives "closed dual crossing ⇒ no open crossing".  The
converse implication "no closed dual crossing ⇒ at most one open crossing
cluster" is *false* in a finite box.  In the configuration where only the bottom
row and the top row of horizontal bonds are open, both rows are left-right
crossings (two distinct clusters) and yet every bond of the bottom row is open,
so no closed bond of the bottom row exists and no closed dual chain can enter the
box from below.

This pins the exact input the global at-most-one argument needs: a finite closed
dual crossing controls *existence* of a crossing, not *uniqueness* of the
crossing cluster; uniqueness has to come from a cofinal/sealed family of
separators, not from one box.
-/

/-- The two-row configuration: only the bottom and top rows of horizontal bonds
are open. -/
def rowOpenH (n : ℕ) (_i j : ℕ) : Bool := j = 0 ∨ j = n

/-- The two-row configuration has no open vertical bonds. -/
def rowOpenV (_n _i _j : ℕ) : Bool := false

lemma openSeam_mh_zero {openH openV : ℕ → ℕ → Bool} {i j : ℕ} (h : openH i j = true) :
    (openSeam openH openV).mh i j = 0 := by
  simp [openSeam, h]

lemma openSeam_mv_one {openH openV : ℕ → ℕ → Bool} {i j : ℕ} (h : openV i j = false) :
    (openSeam openH openV).mv i j = 1 := by
  simp [openSeam, h]

/-- Row labels separate the two rows in the two-row configuration: an open step
never changes whether the row index is zero. -/
lemma row_label_constant {n : ℕ} {x y : Fin (k+2) × Fin (n+1)}
    (h : boxAdj (openSeam (rowOpenH n) (rowOpenV n)) x y) :
    (x.2.val = 0) = (y.2.val = 0) := by
  rcases h with ⟨i, j, hm, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, j, hm, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · rfl
  · rfl
  · rw [openSeam_mv_one (openV := rowOpenV n) rfl] at hm
    exact absurd hm one_ne_zero
  · rw [openSeam_mv_one (openV := rowOpenV n) rfl] at hm
    exact absurd hm one_ne_zero

/-- No open walk changes whether the row index is `0`. -/
lemma row_label_walk {n : ℕ} {x y : Fin (k+2) × Fin (n+1)}
    (p : (boxGraph (k := k) (n := n) (openSeam (rowOpenH n) (rowOpenV n))).Walk x y) :
    (x.2.val = 0) = (y.2.val = 0) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact (row_label_constant h).trans ih

/-- In the two-row configuration, the two rows are not open-connected. -/
theorem row_zero_not_row_n {n : ℕ} (hn : 0 < n) :
    ¬ ((boxGraph (k := k) (n := n) (openSeam (rowOpenH n) (rowOpenV n))).Reachable
        ((0 : Fin (k+2)), (0 : Fin (n+1))) ((0 : Fin (k+2)), ⟨n, by omega⟩)) := by
  intro hreach
  obtain ⟨p⟩ := hreach
  have hlab := row_label_walk p
  simp at hlab
  omega

/-- Open walks along a fixed row of the two-row configuration. -/
lemma row_walk {n j m : ℕ} (hj : j = 0 ∨ j = n) (hm : m ≤ k+1) :
    (boxGraph (k := k) (n := n) (openSeam (rowOpenH n) (rowOpenV n))).Reachable
      ((0 : Fin (k+2)), ⟨j, by omega⟩) (⟨m, by omega⟩, ⟨j, by omega⟩) := by
  induction m with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
      have hm' : m ≤ k+1 := by omega
      have hbond : rowOpenH n m j = true := by
        simp only [rowOpenH]
        simpa using hj
      have hstep : (boxGraph (k := k) (n := n)
          (openSeam (rowOpenH n) (rowOpenV n))).Adj
          (⟨m, by omega⟩, ⟨j, by omega⟩) (⟨m+1, by omega⟩, ⟨j, by omega⟩) :=
        Or.inl ⟨⟨m, by omega⟩, ⟨j, by omega⟩, openSeam_mh_zero hbond, Or.inl ⟨rfl, rfl⟩⟩
      exact (ih hm').trans (SimpleGraph.Adj.reachable hstep)

/-- **Obstruction.**  In a box with at least two rows, the two-row configuration
has two distinct open left-right crossing clusters, while every bond of the
bottom row is open — so no closed dual chain enters the box and the barrier
theorem is silent.  Hence "no closed dual crossing ⇒ at most one crossing
cluster" fails already in a finite box. -/
theorem two_crossing_clusters_no_barrier {n : ℕ} (hn : 2 ≤ n) :
    (boxGraph (k := k) (n := n) (openSeam (rowOpenH n) (rowOpenV n))).Reachable
        ((0 : Fin (k+2)), (0 : Fin (n+1)))
        ((Fin.last (k+1)), (0 : Fin (n+1)))
      ∧ (boxGraph (k := k) (n := n) (openSeam (rowOpenH n) (rowOpenV n))).Reachable
        ((0 : Fin (k+2)), ⟨n, by omega⟩)
        ((Fin.last (k+1)), ⟨n, by omega⟩)
      ∧ ¬ (boxGraph (k := k) (n := n) (openSeam (rowOpenH n) (rowOpenV n))).Reachable
        ((0 : Fin (k+2)), (0 : Fin (n+1))) ((0 : Fin (k+2)), ⟨n, by omega⟩)
      ∧ (∀ i : ℕ, (openSeam (rowOpenH n) (rowOpenV n)).mh i 0 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := row_walk (k := k) (n := n) (j := 0) (m := k+1) (Or.inl rfl) (by omega)
    have hlast : ((⟨k+1, by omega⟩ : Fin (k+2))) = Fin.last (k+1) := Fin.ext rfl
    rw [hlast] at h
    exact h
  · have h := row_walk (k := k) (n := n) (j := n) (m := k+1) (Or.inr rfl) (by omega)
    have hlast : ((⟨k+1, by omega⟩ : Fin (k+2))) = Fin.last (k+1) := Fin.ext rfl
    rw [hlast] at h
    exact h
  · exact row_zero_not_row_n (k := k) (by omega)
  · intro i
    exact openSeam_mh_zero (by simp [rowOpenH])

/-! ## Statement summary -/

#check @FK.PlaneTopology.BoxSeam.Seam
#check @FK.PlaneTopology.BoxSeam.Seam.Phi
#check @FK.PlaneTopology.BoxSeam.Seam.Phi_vert
#check @FK.PlaneTopology.BoxSeam.Seam.Phi_horiz
#check @FK.PlaneTopology.BoxSeam.no_path
#check @FK.PlaneTopology.BoxSeam.cutBonds_separate
#check @FK.PlaneTopology.BoxSeam.CellChain
#check @FK.PlaneTopology.BoxSeam.chainSeam
#check @FK.PlaneTopology.BoxSeam.chainSeam_evenAround
#check @FK.PlaneTopology.BoxSeam.chainSeam_oddBottom
#check @FK.PlaneTopology.BoxSeam.closed_chain_blocks
#check @FK.PlaneTopology.BoxSeam.single_row_closed_barrier
#check @FK.PlaneTopology.BoxSeam.two_crossing_clusters_no_barrier

/-! ## Trust check -/

#print axioms FK.PlaneTopology.BoxSeam.Seam.Phi_vert
#print axioms FK.PlaneTopology.BoxSeam.Seam.Phi_horiz
#print axioms FK.PlaneTopology.BoxSeam.no_path
#print axioms FK.PlaneTopology.BoxSeam.cutBonds_separate
#print axioms FK.PlaneTopology.BoxSeam.chainSeam_evenAround
#print axioms FK.PlaneTopology.BoxSeam.chainSeam_oddBottom
#print axioms FK.PlaneTopology.BoxSeam.chainSeam_wallLeft
#print axioms FK.PlaneTopology.BoxSeam.chainSeam_wallRight
#print axioms FK.PlaneTopology.BoxSeam.closed_chain_blocks
#print axioms FK.PlaneTopology.BoxSeam.single_row_closed_barrier
#print axioms FK.PlaneTopology.BoxSeam.two_crossing_clusters_no_barrier
