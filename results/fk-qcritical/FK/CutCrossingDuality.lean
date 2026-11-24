import FK.GridDualIncidence

/-!
# Cut parity on the square lattice: exact face incidence, cell degrees, and the
finite dual crossing

The finite planar-duality input behind "dual nonpercolation forces at most one
infinite primal cluster", on the concrete square lattice and **without** any
Jordan curve theorem.

Setting: `a : ℤ → ℤ → Bool` is the membership function of a vertex set `A` of
`ℤ × ℤ` (intended: the vertices reachable by primal-open paths from the left wall
of a box).  A bond is a **cut bond** when exactly one endpoint lies in `A`; the
*cut graph* `cutGraph a k n` has as vertices the `(k+1)·n` unit cells of the box
`[0,k+1] × [0,n]`, plus one vertex `below` and one vertex `above` the box, with
two faces adjacent when they share a cut bond.

## Main results (all with default heartbeats, no `sorry`/`axiom`/`unsafe`)

* `reachable_of_odd_degree` — handshake step: in a finite simple graph, two
  odd-degree vertices are connected once every other vertex has even degree.
* `sideBond_parity` — **face parity**: around each unit cell the number of cut
  bonds is even.
* `odd_changes` — **row parity**: along a vertex row the number of cut bonds is
  odd exactly when the two wall vertices differ in membership.
* `adj_inl_iff` — **exact face incidence**: the neighbours of a cell in the cut
  graph are exactly the neighbours across its four cut sides, wall columns
  included (no extra and no missing edges); `sideNbr_injOn_cutSides` says the
  four side neighbours are distinct when the sides are cut.
* `degree_inl_eq`, `even_degree_inl` — a cell's degree is the number of its cut
  sides, hence **every cell has even degree**.
* `degree_inr_zero`, `degree_inr_one` — the two outer vertices have as degree the
  number of cut bonds of the bottom resp. top row, so by `odd_changes` they have
  **odd** degree whenever the left wall lies in `A` and the right wall outside.
* `exists_cut_crossing` — **finite dual crossing**: if the left wall of the box
  lies in `A` and the right wall lies outside `A`, then `below` and `above` are
  connected in `cutGraph a k n`, i.e. the cut bonds of `A` contain a dual curve
  crossing the box from below to above.

The intended use is with `A` the set of vertices reachable from the left wall by
primal-open paths inside the box: every cut bond of `A` is then closed, so this
is the finite "no dual crossing, then an open primal left-right path" step.  The
passage from an arbitrary membership function `a` to a primal configuration is
not part of this file; neither is any statement about `GlobalAtMostOne` or about
Theorem 1.11 of the source paper.
-/

namespace FK.PlaneTopology.CutCrossing

open Finset

attribute [local instance] Classical.propDecidable

/-! ## 1. The handshake step

In a finite simple graph, two odd-degree vertices are connected as soon as all
other vertices have even degree. -/

/-- **Handshake step.** -/
theorem reachable_of_odd_degree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}
    (_hu : Odd (G.degree u)) (hv : Odd (G.degree v))
    (hpar : ∀ w, w ≠ u → w ≠ v → Even (G.degree w)) :
    G.Reachable u v := by
  classical
  by_contra hcon
  set S : Set V := {w | G.Reachable u w} with hSdef
  have huS : u ∈ S := SimpleGraph.Reachable.refl u
  have hvS : v ∉ S := fun h => hcon h
  have hclosed : ∀ w ∈ S, G.neighborSet w ⊆ S := by
    intro w hw z hz
    exact hw.trans ⟨SimpleGraph.Walk.cons hz SimpleGraph.Walk.nil⟩
  have hdeg : ∀ w : S, (G.induce S).degree w = G.degree (w : V) := by
    intro w
    exact SimpleGraph.degree_induce_of_neighborSet_subset (hclosed w w.2)
  have hodd : Odd ((G.induce S).degree ⟨u, huS⟩) := by
    rw [hdeg ⟨u, huS⟩]
    exact ‹Odd (G.degree u)›
  have hcount := SimpleGraph.odd_card_odd_degree_vertices_ne (G := G.induce S) ⟨u, huS⟩ hodd
  have hno : ∀ x : S, ¬ (x ≠ ⟨u, huS⟩ ∧ Odd ((G.induce S).degree x)) := by
    intro x hx
    obtain ⟨hxu, hxodd⟩ := hx
    have hxu' : (x : V) ≠ u := fun h => hxu (Subtype.ext h)
    have hxv : (x : V) ≠ v := fun h => hvS (h ▸ x.2)
    exact Nat.not_odd_iff_even.2 (hpar (x : V) hxu' hxv) (by rw [← hdeg x]; exact hxodd)
  have hzero' :
      (Finset.univ.filter (fun w : S => w ≠ ⟨u, huS⟩ ∧ Odd ((G.induce S).degree w))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun x _ hx => hno x hx
  rw [hzero'] at hcount
  exact Nat.not_odd_iff_even.2 (by decide) hcount

/-! ## 2. Cut bonds of the square lattice -/

/-- The horizontal bond through `(i,j)` and `(i+1,j)`. -/
def hCut (a : ℤ → ℤ → Bool) (i j : ℤ) : Bool := a i j != a (i + 1) j

/-- The vertical bond through `(i,j)` and `(i,j+1)`. -/
def vCut (a : ℤ → ℤ → Bool) (i j : ℤ) : Bool := a i j != a i (j + 1)

/-- The four sides of a unit cell, as `Fin 4`: `0` left, `1` right, `2` bottom,
`3` top, together with the information whether the bond on that side is a cut
bond. -/
def sideBond (a : ℤ → ℤ → Bool) {k n : ℕ} (c : Fin (k + 1) × Fin n) (s : Fin 4) : Bool :=
  if s = 0 then vCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ)
  else if s = 1 then vCut a (((c.1 : ℕ) : ℤ) + 1) ((c.2 : ℕ) : ℤ)
  else if s = 2 then hCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ)
  else hCut a ((c.1 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) + 1)

@[simp] lemma sideBond_zero (a : ℤ → ℤ → Bool) {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideBond a c 0 = vCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) := rfl
@[simp] lemma sideBond_one (a : ℤ → ℤ → Bool) {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideBond a c 1 = vCut a (((c.1 : ℕ) : ℤ) + 1) ((c.2 : ℕ) : ℤ) := by
  simp only [sideBond]; norm_num
@[simp] lemma sideBond_two (a : ℤ → ℤ → Bool) {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideBond a c 2 = hCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) := by
  simp only [sideBond]; norm_num
@[simp] lemma sideBond_three (a : ℤ → ℤ → Bool) {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideBond a c 3 = hCut a ((c.1 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) + 1) := by
  simp only [sideBond]; norm_num

/-- **Four-cycle parity.**  A unit cell has an even number of cut bonds: the
number of membership changes around a four-cycle is even. -/
theorem sideBond_parity (a : ℤ → ℤ → Bool) {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    Even ((sideBond a c 0).toNat + (sideBond a c 1).toNat +
      (sideBond a c 2).toNat + (sideBond a c 3).toNat) := by
  simp only [sideBond_zero, sideBond_one, sideBond_two, sideBond_three, hCut, vCut]
  generalize a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) = p
  generalize a (((c.1 : ℕ) : ℤ) + 1) ((c.2 : ℕ) : ℤ) = q
  generalize a ((c.1 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) + 1) = r
  generalize a (((c.1 : ℕ) : ℤ) + 1) (((c.2 : ℕ) : ℤ) + 1) = s
  cases p <;> cases q <;> cases r <;> cases s <;> decide

/-- The number of sign changes of a Boolean sequence `f 0, …, f m`, modulo `2`,
records whether the two endpoints differ. -/
theorem changes_mod_two (f : ℕ → Bool) (m : ℕ) :
    ((Finset.range m).filter (fun i => f i != f (i + 1))).card % 2
      = if f 0 = f m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hb : f m = f (m + 1)
      · have hb' : (f m != f (m + 1)) = false := by simp [hb]
        rw [if_neg (by rw [hb']; decide), ih, ← hb]
      · have hb' : (f m != f (m + 1)) = true := by simp [hb]
        rw [if_pos (by rw [hb']), Finset.card_insert_of_notMem (by simp)]
        rw [Nat.add_mod, ih]
        by_cases h2 : f 0 = f m
        · have h3 : f 0 ≠ f (m + 1) := fun h => hb (h2.symm.trans h)
          rw [if_pos h2, if_neg h3]
        · have h3 : f 0 = f (m + 1) := by
            revert h2 hb
            cases f 0 <;> cases f m <;> cases f (m + 1) <;> simp
          rw [if_neg h2, if_pos h3]

/-- **Row parity.**  Along the vertex row of height `j`, the number of cut bonds
of the box is odd exactly when the two end vertices differ in membership. -/
theorem odd_changes (a : ℤ → ℤ → Bool) {k : ℕ} (j : ℤ) (h0 : a 0 j = true)
    (h1 : a ((k : ℤ) + 1) j = false) :
    Odd ((Finset.range (k + 1)).filter (fun i : ℕ => hCut a (i : ℤ) j = true)).card := by
  let f : ℕ → Bool := fun m => a (m : ℤ) j
  have hcm := changes_mod_two f (k + 1)
  have hcard : ((Finset.range (k + 1)).filter (fun i : ℕ => hCut a (i : ℤ) j = true)).card
      = ((Finset.range (k + 1)).filter (fun i : ℕ => f i != f (i + 1))).card := by
    congr 1
  rw [hcard, Nat.odd_iff, hcm]
  have hlast : a ((k + 1 : ℕ) : ℤ) j = false := by
    rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
    exact h1
  have hf0 : f 0 = true := h0
  have hfk : f (k + 1) = false := hlast
  rw [hf0, hfk]
  decide

/-! ## 3. The augmented dual graph of the box -/

/-- Vertices: the unit cells of the box, a vertex `below` below the box and a
vertex `above` above it. -/
abbrev DVert (k n : ℕ) := (Fin (k + 1) × Fin n) ⊕ Fin 2

/-- The cell cut relation: two cells sharing a cut bond. -/
def CellCut (a : ℤ → ℤ → Bool) (i j i' j' : ℤ) : Prop :=
  (j' = j ∧ (i' = i + 1 ∨ i = i' + 1) ∧ vCut a (min i i' + 1) j = true) ∨
  (i' = i ∧ (j' = j + 1 ∨ j = j' + 1) ∧ hCut a i (min j j' + 1) = true)

lemma CellCut_comm {a : ℤ → ℤ → Bool} {i j i' j' : ℤ} (h : CellCut a i j i' j') :
    CellCut a i' j' i j := by
  unfold CellCut at *
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl ⟨h1.symm, h2.symm, ?_⟩
    subst h1; rw [min_comm]; exact h3
  · refine Or.inr ⟨h1.symm, h2.symm, ?_⟩
    subst h1; rw [min_comm]; exact h3

/-- Adjacency of the augmented dual graph. -/
def DAdj (a : ℤ → ℤ → Bool) (k n : ℕ) : DVert k n → DVert k n → Prop
  | Sum.inl c, Sum.inl d =>
      CellCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ)
  | Sum.inl c, Sum.inr s =>
      (s = 0 ∧ ((c.2 : ℕ) : ℤ) = 0 ∧ hCut a ((c.1 : ℕ) : ℤ) 0 = true) ∨
      (s = 1 ∧ ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧ hCut a ((c.1 : ℕ) : ℤ) (n : ℤ) = true)
  | Sum.inr s, Sum.inl c =>
      (s = 0 ∧ ((c.2 : ℕ) : ℤ) = 0 ∧ hCut a ((c.1 : ℕ) : ℤ) 0 = true) ∨
      (s = 1 ∧ ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧ hCut a ((c.1 : ℕ) : ℤ) (n : ℤ) = true)
  | Sum.inr _, Sum.inr _ => False

/-- Decidability of the cut relation (classical, so that degrees exist). -/
noncomputable instance instDecidableDAdj (a : ℤ → ℤ → Bool) (k n : ℕ) :
    DecidableRel (DAdj a k n) :=
  fun _ _ => Classical.dec _

lemma DAdj_symm {a : ℤ → ℤ → Bool} {k n : ℕ} {x y : DVert k n}
    (h : DAdj a k n x y) : DAdj a k n y x := by
  obtain (c | s) := x <;> obtain (d | t) := y <;> simp only [DAdj] at *
  all_goals first | exact CellCut_comm h | exact h

lemma DAdj_irrefl {a : ℤ → ℤ → Bool} {k n : ℕ} {x : DVert k n} :
    ¬ DAdj a k n x x := by
  obtain (c | s) := x
  · simp only [DAdj, CellCut]
    rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> omega
  · simp [DAdj]

/-- The dual graph of the cut bonds of the box. -/
def cutGraph (a : ℤ → ℤ → Bool) (k n : ℕ) : SimpleGraph (DVert k n) where
  Adj := DAdj a k n
  symm := ⟨fun _ _ h => DAdj_symm h⟩
  loopless := ⟨fun _ h => DAdj_irrefl h⟩

/-- Decidability of the adjacency of the cut graph (classical, so that degrees exist). -/
noncomputable instance instDecidableCutGraph (a : ℤ → ℤ → Bool) (k n : ℕ) :
    DecidableRel (cutGraph a k n).Adj :=
  fun _ _ => Classical.dec _

end FK.PlaneTopology.CutCrossing



namespace FK.PlaneTopology.CutCrossing

/-- The left boundary column carries no cut bonds. -/
theorem vCut_zero_col {a : ℤ → ℤ → Bool} (hv : ∀ j : ℤ, a 0 j = true) (j : ℤ) :
    vCut a 0 j = false := by
  simp [vCut, hv j, hv (j + 1)]

/-- The right boundary column carries no cut bonds. -/
theorem vCut_last_col {k : ℕ} {a : ℤ → ℤ → Bool} (hv : ∀ j : ℤ, a ((k : ℤ) + 1) j = false)
    (j : ℤ) : vCut a ((k : ℤ) + 1) j = false := by
  simp [vCut, hv j, hv (j + 1)]

/-- **Cut sides of a cell.**  Two cells share a cut bond exactly when they are
the two cells of that bond; the four sides of a cell are the four primal bonds
around it. -/
theorem sideBond_eq_false_of_boundary_left {k n : ℕ} {a : ℤ → ℤ → Bool}
    (hvL : ∀ j : ℤ, vCut a 0 j = false) (c : Fin (k + 1) × Fin n)
    (h0 : (c.1 : ℕ) = 0) : sideBond a c 0 = false := by
  rw [sideBond_zero, show ((c.1 : ℕ) : ℤ) = 0 by omega]
  exact hvL _

theorem sideBond_eq_false_of_boundary_right {k n : ℕ} {a : ℤ → ℤ → Bool}
    (hvR : ∀ j : ℤ, vCut a ((k : ℤ) + 1) j = false) (c : Fin (k + 1) × Fin n)
    (h0 : (c.1 : ℕ) + 1 = k + 1) : sideBond a c 1 = false := by
  rw [sideBond_one, show ((c.1 : ℕ) : ℤ) + 1 = (k : ℤ) + 1 by omega]
  exact hvR _

/-! ## 4. Sides, side neighbours, and the degree of a cell -/

/-- The four elements of `Fin 4`, listed. -/
lemma fin4_cases (s : Fin 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
  fin_cases s <;> simp

/-- The neighbour of a cell across side `s`: `0` left, `1` right, `2` bottom,
`3` top.  When the side lies on the wall of the box the value is a junk value
(the cell itself); such a side is never a cut bond by
`sideBond_eq_false_of_boundary_left/right`. -/
def sideNbr {k n : ℕ} (c : Fin (k + 1) × Fin n) (s : Fin 4) : DVert k n :=
  if s = 0 then (if (c.1 : ℕ) = 0 then Sum.inl c
      else Sum.inl ⟨⟨(c.1 : ℕ) - 1, by omega⟩, c.2⟩)
  else if s = 1 then (if h : (c.1 : ℕ) + 1 < k + 1 then
      Sum.inl ⟨⟨(c.1 : ℕ) + 1, h⟩, c.2⟩ else Sum.inl c)
  else if s = 2 then (if (c.2 : ℕ) = 0 then Sum.inr 0
      else Sum.inl ⟨c.1, ⟨(c.2 : ℕ) - 1, by omega⟩⟩)
  else (if h : (c.2 : ℕ) + 1 < n then Sum.inl ⟨c.1, ⟨(c.2 : ℕ) + 1, h⟩⟩
      else Sum.inr 1)

@[simp] lemma sideNbr_zero {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideNbr c 0 = (if (c.1 : ℕ) = 0 then Sum.inl c
      else Sum.inl ⟨⟨(c.1 : ℕ) - 1, by omega⟩, c.2⟩) := rfl
@[simp] lemma sideNbr_one {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideNbr c 1 = (if h : (c.1 : ℕ) + 1 < k + 1 then
      Sum.inl ⟨⟨(c.1 : ℕ) + 1, h⟩, c.2⟩ else Sum.inl c) := by
  simp only [sideNbr]; norm_num
@[simp] lemma sideNbr_two {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideNbr c 2 = (if (c.2 : ℕ) = 0 then Sum.inr 0
      else Sum.inl ⟨c.1, ⟨(c.2 : ℕ) - 1, by omega⟩⟩) := by
  simp only [sideNbr]; norm_num
@[simp] lemma sideNbr_three {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    sideNbr c 3 = (if h : (c.2 : ℕ) + 1 < n then Sum.inl ⟨c.1, ⟨(c.2 : ℕ) + 1, h⟩⟩
      else Sum.inr 1) := by
  simp only [sideNbr]; norm_num


lemma fst_pair_cast {k n : ℕ} (y : Fin (k+1)) (c : Fin n) :
    (((y, c) : Fin (k+1) × Fin n).1 : ℤ) = ((y : ℕ) : ℤ) := rfl
lemma snd_pair_cast {k n : ℕ} (y : Fin (k+1)) (c : Fin n) :
    (((y, c) : Fin (k+1) × Fin n).2 : ℤ) = ((c : ℕ) : ℤ) := rfl
lemma fin_mk_cast_sub {k : ℕ} (i : Fin (k+1)) (h : 1 ≤ (i:ℕ)) :
    (((⟨(i:ℕ) - 1, by omega⟩ : Fin (k+1)) : ℕ) : ℤ) = ((i:ℕ):ℤ) - 1 := by
  push_cast [Nat.cast_sub h]; ring
lemma fin_mk_cast_add {k : ℕ} (i : Fin (k+1)) (h : (i:ℕ) + 1 < k+1) :
    (((⟨(i:ℕ) + 1, h⟩ : Fin (k+1)) : ℕ) : ℤ) = ((i:ℕ):ℤ) + 1 := by
  push_cast; ring
lemma fin_mk_cast_sub' {m : ℕ} (i : Fin m) (h : 1 ≤ (i:ℕ)) :
    (((⟨(i:ℕ) - 1, by omega⟩ : Fin m) : ℕ) : ℤ) = ((i:ℕ):ℤ) - 1 := by
  push_cast [Nat.cast_sub h]; ring
lemma fin_mk_cast_add' {m : ℕ} (i : Fin m) (h : (i:ℕ) + 1 < m) :
    (((⟨(i:ℕ) + 1, h⟩ : Fin m) : ℕ) : ℤ) = ((i:ℕ):ℤ) + 1 := by
  push_cast; ring

/-- **Neighbours of a cell.**  In the cut graph, the neighbours of a cell are
exactly the neighbours across its four cut sides.  This is the exact face
incidence of the square lattice, including both wall columns. -/
theorem adj_inl_iff {k n : ℕ} {a : ℤ → ℤ → Bool} (hvL : ∀ j : ℤ, vCut a 0 j = false)
    (hvR : ∀ j : ℤ, vCut a ((k : ℤ) + 1) j = false) (c : Fin (k + 1) × Fin n)
    (y : DVert k n) :
    DAdj a k n (Sum.inl c) y ↔ ∃ s : Fin 4, sideBond a c s = true ∧ sideNbr c s = y := by
  obtain (d | t) := y
  · constructor
    · intro h
      simp only [DAdj, CellCut] at h
      obtain ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ := h
      · rcases h2 with h2 | h2
        · have hbond : vCut a (((c.1 : ℕ) : ℤ) + 1) ((c.2 : ℕ) : ℤ) = true := by
            rw [show min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) + 1 = ((c.1 : ℕ) : ℤ) + 1 by omega] at h3
            exact h3
          refine ⟨1, by rw [sideBond_one]; exact hbond, ?_⟩
          have hb : (c.1 : ℕ) + 1 < k + 1 := by have := d.1.2; omega
          simp only [sideNbr_one, dif_pos hb]
          congr 1
          exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
        · have hbond : vCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) = true := by
            rw [show min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) + 1 = ((c.1 : ℕ) : ℤ) by omega] at h3
            exact h3
          have hc0 : (c.1 : ℕ) ≠ 0 := by have := d.1.2; omega
          refine ⟨0, by rw [sideBond_zero]; exact hbond, ?_⟩
          simp only [sideNbr_zero, if_neg hc0]
          congr 1
          exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
      · rcases h2 with h2 | h2
        · have hbond : hCut a ((c.1 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) + 1) = true := by
            rw [show min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1 = ((c.2 : ℕ) : ℤ) + 1 by omega] at h3
            exact h3
          have hb : (c.2 : ℕ) + 1 < n := by have := d.2.2; omega
          refine ⟨3, by rw [sideBond_three]; exact hbond, ?_⟩
          simp only [sideNbr_three, dif_pos hb]
          congr 1
          exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
        · have hbond : hCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) = true := by
            rw [show min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1 = ((c.2 : ℕ) : ℤ) by omega] at h3
            exact h3
          have hc0 : (c.2 : ℕ) ≠ 0 := by have := d.2.2; omega
          refine ⟨2, by rw [sideBond_two]; exact hbond, ?_⟩
          simp only [sideNbr_two, if_neg hc0]
          congr 1
          exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
    · intro hex
      obtain ⟨s, hs, hN⟩ := hex
      rw [← hN]
      rcases fin4_cases s with h0 | h1 | h2 | h3
      · subst h0
        simp only [sideBond_zero, sideNbr_zero] at hs ⊢
        by_cases hc0 : (c.1 : ℕ) = 0
        · rw [if_pos hc0]
          rw [show ((c.1 : ℕ) : ℤ) = 0 by omega] at hs
          rw [hvL] at hs
          simp at hs
        · rw [if_neg hc0]
          unfold DAdj CellCut
          have hpos : 1 ≤ (c.1 : ℕ) := Nat.one_le_iff_ne_zero.mpr hc0
          refine Or.inl ⟨rfl, Or.inr ?_, ?_⟩
          · rw [fst_pair_cast (k := k) (n := n), fin_mk_cast_sub (k := k) (i := c.1) hpos]
            omega
          · rw [fst_pair_cast (k := k) (n := n), fin_mk_cast_sub (k := k) (i := c.1) hpos]
            rw [show min ((c.1 : ℕ) : ℤ) (((c.1 : ℕ) : ℤ) - 1) + 1 = ((c.1 : ℕ) : ℤ) by omega]
            exact hs
      · subst h1
        simp only [sideBond_one, sideNbr_one] at hs ⊢
        by_cases hc1 : (c.1 : ℕ) + 1 < k + 1
        · rw [dif_pos hc1]
          unfold DAdj CellCut
          refine Or.inl ⟨rfl, Or.inl ?_, ?_⟩
          · rw [fst_pair_cast (k := k) (n := n), fin_mk_cast_add (k := k) (i := c.1) hc1]
          · rw [fst_pair_cast (k := k) (n := n), fin_mk_cast_add (k := k) (i := c.1) hc1]
            rw [show min ((c.1 : ℕ) : ℤ) (((c.1 : ℕ) : ℤ) + 1) + 1 = ((c.1 : ℕ) : ℤ) + 1 by omega]
            exact hs
        · rw [dif_neg hc1]
          rw [show ((c.1 : ℕ) : ℤ) + 1 = (k : ℤ) + 1 by omega] at hs
          rw [hvR] at hs
          simp at hs
      · subst h2
        simp only [sideBond_two, sideNbr_two] at hs ⊢
        by_cases hc2 : (c.2 : ℕ) = 0
        · rw [if_pos hc2]
          unfold DAdj
          refine Or.inl ⟨rfl, ?_, ?_⟩
          · show ((c.2 : ℕ) : ℤ) = 0
            omega
          · show hCut a ((c.1 : ℕ) : ℤ) 0 = true
            rw [show (0 : ℤ) = ((c.2 : ℕ) : ℤ) by omega]
            exact hs
        · rw [if_neg hc2]
          unfold DAdj CellCut
          have hpos : 1 ≤ (c.2 : ℕ) := Nat.one_le_iff_ne_zero.mpr hc2
          refine Or.inr ⟨rfl, Or.inr ?_, ?_⟩
          · rw [snd_pair_cast (k := k) (n := n), fin_mk_cast_sub' (m := n) (i := c.2) hpos]
            omega
          · rw [snd_pair_cast (k := k) (n := n), fin_mk_cast_sub' (m := n) (i := c.2) hpos]
            rw [show min ((c.2 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) - 1) + 1 = ((c.2 : ℕ) : ℤ) by omega]
            exact hs
      · subst h3
        simp only [sideBond_three, sideNbr_three] at hs ⊢
        by_cases hc2 : (c.2 : ℕ) + 1 < n
        · rw [dif_pos hc2]
          unfold DAdj CellCut
          refine Or.inr ⟨rfl, Or.inl ?_, ?_⟩
          · rw [snd_pair_cast (k := k) (n := n), fin_mk_cast_add' (m := n) (i := c.2) hc2]
          · rw [snd_pair_cast (k := k) (n := n), fin_mk_cast_add' (m := n) (i := c.2) hc2]
            rw [show min ((c.2 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) + 1) + 1 = ((c.2 : ℕ) : ℤ) + 1 by omega]
            exact hs
        · rw [dif_neg hc2]
          unfold DAdj
          refine Or.inr ⟨rfl, ?_, ?_⟩
          · show ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1
            omega
          · show hCut a ((c.1 : ℕ) : ℤ) (n : ℤ) = true
            rw [show (n : ℤ) = ((c.2 : ℕ) : ℤ) + 1 by omega]
            exact hs
  · constructor
    · intro h
      simp only [DAdj] at h
      obtain ⟨rfl, hj, hb⟩ | ⟨rfl, hj, hb⟩ := h
      · refine ⟨2, ?_, ?_⟩
        · rw [sideBond_two]
          show hCut a ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) = true
          rw [show ((c.2 : ℕ) : ℤ) = 0 by omega]
          exact hb
        · rw [sideNbr_two, if_pos (by omega)]
      · refine ⟨3, ?_, ?_⟩
        · rw [sideBond_three]
          show hCut a ((c.1 : ℕ) : ℤ) (((c.2 : ℕ) : ℤ) + 1) = true
          rw [show ((c.2 : ℕ) : ℤ) + 1 = (n : ℤ) by omega]
          exact hb
        · rw [sideNbr_three, dif_neg]
          show ¬ ((c.2 : ℕ) + 1 < n)
          omega
    · intro hex
      obtain ⟨s, hs, hN⟩ := hex
      rw [← hN]
      rcases fin4_cases s with h0 | h1 | h2 | h3
      · subst h0
        simp only [sideBond_zero, sideNbr_zero] at hs hN ⊢
        by_cases hc0 : (c.1 : ℕ) = 0
        · rw [if_pos hc0] at hN
          simp at hN
        · rw [if_neg hc0] at hN
          simp at hN
      · subst h1
        simp only [sideBond_one, sideNbr_one] at hs hN ⊢
        by_cases hc1 : (c.1 : ℕ) + 1 < k + 1
        · rw [dif_pos hc1] at hN
          simp at hN
        · rw [dif_neg hc1] at hN
          simp at hN
      · subst h2
        simp only [sideBond_two, sideNbr_two] at hs hN ⊢
        by_cases hc2 : (c.2 : ℕ) = 0
        · rw [if_pos hc2] at hN
          have ht : t = 0 := by simpa using hN.symm
          subst ht
          rw [if_pos hc2]
          unfold DAdj
          refine Or.inl ⟨rfl, by omega, ?_⟩
          rw [show (0 : ℤ) = ((c.2 : ℕ) : ℤ) by omega]
          exact hs
        · rw [if_neg hc2] at hN
          simp at hN
      · subst h3
        simp only [sideBond_three, sideNbr_three] at hs hN ⊢
        by_cases hc2 : (c.2 : ℕ) + 1 < n
        · rw [dif_pos hc2] at hN
          simp at hN
        · rw [dif_neg hc2] at hN
          have ht : t = 1 := by simpa using hN.symm
          subst ht
          rw [dif_neg hc2]
          unfold DAdj
          refine Or.inr ⟨rfl, by omega, ?_⟩
          rw [show (n : ℤ) = ((c.2 : ℕ) : ℤ) + 1 by omega]
          exact hs


/-- **Distinct cut sides lead to distinct neighbours.**  This is what turns the
side count of a cell into its graph degree. -/
theorem sideNbr_injOn_cutSides {k n : ℕ} {a : ℤ → ℤ → Bool}
    (hvL : ∀ j : ℤ, vCut a 0 j = false) (hvR : ∀ j : ℤ, vCut a ((k : ℤ) + 1) j = false)
    {s s' : Fin 4} (c : Fin (k + 1) × Fin n)
    (hs : sideBond a c s = true) (hs' : sideBond a c s' = true)
    (heq : sideNbr c s = sideNbr c s') : s = s' := by
  rcases fin4_cases s with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases s' with rfl | rfl | rfl | rfl <;>
    simp only [sideBond_zero, sideBond_one, sideBond_two, sideBond_three,
      sideNbr_zero, sideNbr_one, sideNbr_two, sideNbr_three] at hs hs' heq
  all_goals
    first
    | rfl
    | (exfalso
       have hL := hvL ((c.2 : ℕ) : ℤ)
       have hR := hvR ((c.2 : ℕ) : ℤ)
       split_ifs at heq
       all_goals
         first
         | (simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq,
             Fin.ext_iff] at heq
            omega)
         | (first
            | (rw [show ((c.1 : ℕ) : ℤ) = 0 by omega, hL] at hs; simp at hs)
            | (rw [show ((c.1 : ℕ) : ℤ) + 1 = (k : ℤ) + 1 by omega, hR] at hs; simp at hs)
            | (rw [show ((c.1 : ℕ) : ℤ) = 0 by omega, hL] at hs'; simp at hs')
            | (rw [show ((c.1 : ℕ) : ℤ) + 1 = (k : ℤ) + 1 by omega, hR] at hs'; simp at hs')
            | (simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq,
                 Fin.ext_iff] at heq
               first | omega | (cases heq) | (simp_all only [Bool.false_eq_true]))))


/-- **Degree of a cell.**  A cell of the cut graph has exactly as many neighbours
as it has cut sides: the four side neighbours are distinct by
`sideNbr_injOn_cutSides`, and `adj_inl_iff` says there are no others. -/
theorem degree_inl_eq {k n : ℕ} {a : ℤ → ℤ → Bool} (hvL : ∀ j : ℤ, vCut a 0 j = false)
    (hvR : ∀ j : ℤ, vCut a ((k : ℤ) + 1) j = false) (c : Fin (k + 1) × Fin n) :
    (cutGraph a k n).degree (Sum.inl c)
      = (sideBond a c 0).toNat + (sideBond a c 1).toNat
        + (sideBond a c 2).toNat + (sideBond a c 3).toNat := by
  classical
  set S : Finset (Fin 4) := Finset.univ.filter (fun s : Fin 4 => sideBond a c s = true) with hS
  have himg : (Finset.univ.filter (DAdj a k n (Sum.inl c)))
      = S.image (sideNbr (k := k) (n := n) c) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hS]
    exact adj_inl_iff hvL hvR c y
  have hinj : Set.InjOn (sideNbr (k := k) (n := n) c) ↑S := by
    intro s hs s' hs' heq
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs hs'
    exact sideNbr_injOn_cutSides hvL hvR c hs hs' heq
  have hcard : (S.image (sideNbr (k := k) (n := n) c)).card
      = (sideBond a c 0).toNat + (sideBond a c 1).toNat
        + (sideBond a c 2).toNat + (sideBond a c 3).toNat := by
    rw [Finset.card_image_of_injOn hinj, hS, Finset.card_filter, Fin.sum_univ_four]
    rcases h0 : sideBond a c 0 with _ | _ <;>
      rcases h1 : sideBond a c 1 with _ | _ <;>
      rcases h2 : sideBond a c 2 with _ | _ <;>
      rcases h3 : sideBond a c 3 with _ | _ <;>
      simp [h0, h1, h2, h3]
  have hdeg : (cutGraph a k n).degree (Sum.inl c)
      = (Finset.univ.filter (DAdj a k n (Sum.inl c))).card := by
    have h1 : (cutGraph a k n).degree (Sum.inl c)
        = ((cutGraph a k n).neighborFinset (Sum.inl c)).card := rfl
    rw [h1]
    congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [hdeg, himg, hcard]


/-- Even-degree cells: the parity of the four cut sides. -/
theorem even_degree_inl {k n : ℕ} {a : ℤ → ℤ → Bool} (hvL : ∀ j : ℤ, vCut a 0 j = false)
    (hvR : ∀ j : ℤ, vCut a ((k : ℤ) + 1) j = false) (c : Fin (k + 1) × Fin n) :
    Even ((cutGraph a k n).degree (Sum.inl c)) := by
  rw [degree_inl_eq hvL hvR c]
  exact sideBond_parity a c


/-! ## 6. Prop-valued cut predicates, the two boundary degrees, and the crossing -/

/-- Propositional form of the horizontal cut bond.  Stating the row counts with
this (rather than with the `Bool` indicator) avoids rewriting inside `BEq`. -/
def hCutP (a : ℤ → ℤ → Bool) (i j : ℤ) : Prop := a i j ≠ a (i + 1) j

/-- Propositional form of the vertical cut bond. -/
def vCutP (a : ℤ → ℤ → Bool) (i j : ℤ) : Prop := a i j ≠ a i (j + 1)

lemma hCutP_iff (a : ℤ → ℤ → Bool) (i j : ℤ) : hCutP a i j ↔ hCut a i j = true := by
  simp only [hCutP, hCut]
  cases a i j <;> cases a (i + 1) j <;> simp

lemma vCutP_iff (a : ℤ → ℤ → Bool) (i j : ℤ) : vCutP a i j ↔ vCut a i j = true := by
  simp only [vCutP, vCut]
  cases a i j <;> cases a i (j + 1) <;> simp

/-- Decidability of the row predicates (classical). -/
noncomputable instance decidablePred_hCutP_row (a : ℤ → ℤ → Bool) (j : ℤ) :
    DecidablePred (fun i : ℕ => hCutP a (i : ℤ) j) :=
  fun i => Classical.dec _

/-- **Degree of the vertex below the box.**  Its neighbours are exactly the cells
of the bottom row whose bottom bond is a cut bond, indexed by the columns. -/
theorem degree_inr_zero {k n : ℕ} {a : ℤ → ℤ → Bool} (hn : 0 < n) :
    (cutGraph a k n).degree (Sum.inr 0)
      = ((Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) 0)).card := by
  classical
  have hdeg : (cutGraph a k n).degree (Sum.inr 0)
      = (Finset.univ.filter (DAdj a k n (Sum.inr 0))).card := by
    have h1 : (cutGraph a k n).degree (Sum.inr 0)
        = ((cutGraph a k n).neighborFinset (Sum.inr 0)).card := rfl
    rw [h1]
    congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hmain : ((Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) 0)).card
      = (Finset.univ.filter (DAdj a k n (Sum.inr 0))).card := by
    refine Finset.card_bij
      (fun (i : ℕ) (hi : i ∈ (Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) 0)) =>
        (Sum.inl ((⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩ : Fin (k + 1)),
          (⟨0, hn⟩ : Fin n)) : DVert k n)) ?_ ?_ ?_
    · intro i hi
      obtain ⟨hir, hib⟩ := Finset.mem_filter.mp hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold DAdj
      exact Or.inl ⟨rfl, by simp, (hCutP_iff a (i : ℤ) 0).mp hib⟩
    · intro i hi i' hi' heq
      simpa using heq
    · intro y hy
      obtain (d | t) := y
      · rw [Finset.mem_filter] at hy
        obtain ⟨-, hyd⟩ := hy
        unfold DAdj at hyd
        rcases hyd with ⟨-, hj, hb⟩ | ⟨h1, -⟩
        · refine ⟨(d.1 : ℕ), ?_, ?_⟩
          · rw [Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr d.1.2, (hCutP_iff a ((d.1 : ℕ) : ℤ) 0).mpr hb⟩
          · congr 1
            exact Prod.ext rfl (Fin.ext (by simp at hj ⊢; omega))
        · omega
      · rw [Finset.mem_filter] at hy
        exact absurd hy.2 (by simp [DAdj])
  rw [hdeg]
  exact hmain.symm

/-- **Degree of the vertex above the box.**  Its neighbours are exactly the cells
of the top row whose top bond is a cut bond. -/
theorem degree_inr_one {k n : ℕ} {a : ℤ → ℤ → Bool} (hn : 0 < n) :
    (cutGraph a k n).degree (Sum.inr 1)
      = ((Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) (n : ℤ))).card := by
  classical
  have hdeg : (cutGraph a k n).degree (Sum.inr 1)
      = (Finset.univ.filter (DAdj a k n (Sum.inr 1))).card := by
    have h1 : (cutGraph a k n).degree (Sum.inr 1)
        = ((cutGraph a k n).neighborFinset (Sum.inr 1)).card := rfl
    rw [h1]
    congr 1
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hmain : ((Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) (n : ℤ))).card
      = (Finset.univ.filter (DAdj a k n (Sum.inr 1))).card := by
    refine Finset.card_bij
      (fun (i : ℕ) (hi : i ∈ (Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) (n : ℤ))) =>
        (Sum.inl ((⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩ : Fin (k + 1)),
          (⟨n - 1, by omega⟩ : Fin n)) : DVert k n)) ?_ ?_ ?_
    · intro i hi
      obtain ⟨hir, hib⟩ := Finset.mem_filter.mp hi
      have hcast : (((⟨n - 1, by omega⟩ : Fin n) : ℕ) : ℤ) = (n : ℤ) - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
        ring
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold DAdj
      exact Or.inr ⟨rfl, hcast, (hCutP_iff a (i : ℤ) (n : ℤ)).mp hib⟩
    · intro i hi i' hi' heq
      simpa using heq
    · intro y hy
      obtain (d | t) := y
      · rw [Finset.mem_filter] at hy
        obtain ⟨-, hyd⟩ := hy
        unfold DAdj at hyd
        rcases hyd with ⟨h1, -⟩ | ⟨-, hj, hb⟩
        · omega
        · refine ⟨(d.1 : ℕ), ?_, ?_⟩
          · rw [Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr d.1.2, (hCutP_iff a ((d.1 : ℕ) : ℤ) (n : ℤ)).mpr hb⟩
          · congr 1
            exact Prod.ext rfl (Fin.ext (by simp at hj ⊢; omega))
      · rw [Finset.mem_filter] at hy
        exact absurd hy.2 (by simp [DAdj])
  rw [hdeg]
  exact hmain.symm

/-- **Finite dual crossing from a separating vertex set.**  If the whole left wall
of the box lies in `A` and the whole right wall lies outside `A`, then the cut
bonds of `A` contain a dual curve joining the region below the box to the region
above it.  Cells have even degree (`even_degree_inl`), the two outer vertices
have odd degree (the row parity `odd_changes` through `degree_inr_zero/one`), so
the handshake lemma `reachable_of_odd_degree` applies. -/
theorem exists_cut_crossing {k n : ℕ} {a : ℤ → ℤ → Bool} (hn : 0 < n)
    (hleft : ∀ j : ℤ, a 0 j = true) (hright : ∀ j : ℤ, a ((k : ℤ) + 1) j = false) :
    (cutGraph a k n).Reachable (Sum.inr 0) (Sum.inr 1) := by
  classical
  have hvL : ∀ j : ℤ, vCut a 0 j = false := vCut_zero_col hleft
  have hvR : ∀ j : ℤ, vCut a ((k : ℤ) + 1) j = false := vCut_last_col hright
  have hrow_zero : Odd ((Finset.range (k + 1)).filter
      (fun i : ℕ => hCutP a (i : ℤ) 0)).card := by
    have h := odd_changes a 0 (hleft 0) (hright 0)
    have hcard : ((Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) 0)).card
        = ((Finset.range (k + 1)).filter (fun i : ℕ => hCut a (i : ℤ) 0 = true)).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, (hCutP_iff a (i : ℤ) 0).mp h.2⟩,
        fun h => ⟨h.1, (hCutP_iff a (i : ℤ) 0).mpr h.2⟩⟩
    rw [hcard]
    exact h
  have hrow_top : Odd ((Finset.range (k + 1)).filter
      (fun i : ℕ => hCutP a (i : ℤ) (n : ℤ))).card := by
    have h := odd_changes a (n : ℤ) (hleft n) (hright n)
    have hcard : ((Finset.range (k + 1)).filter (fun i : ℕ => hCutP a (i : ℤ) (n : ℤ))).card
        = ((Finset.range (k + 1)).filter
            (fun i : ℕ => hCut a (i : ℤ) (n : ℤ) = true)).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, (hCutP_iff a (i : ℤ) (n : ℤ)).mp h.2⟩,
        fun h => ⟨h.1, (hCutP_iff a (i : ℤ) (n : ℤ)).mpr h.2⟩⟩
    rw [hcard]
    exact h
  refine reachable_of_odd_degree ?_ ?_ ?_
  · rw [degree_inr_zero (k := k) (n := n) (a := a) hn]
    exact hrow_zero
  · rw [degree_inr_one (k := k) (n := n) (a := a) hn]
    exact hrow_top
  · intro w h1 h2
    obtain (c | t) := w
    · exact even_degree_inl hvL hvR c
    · fin_cases t
      · exact absurd rfl h1
      · exact absurd rfl h2


/-- **Transfer of the crossing to any supergraph.**  If every cut bond of the box
is an edge of another graph `G'` on the same vertices, then `G'` also connects
`below` to `above`.  Instantiate `G'` with the graph of primal-**closed** bonds
to read `exists_cut_crossing` as a dual path of closed bonds. -/
theorem reachable_of_cut_le {k n : ℕ} {a : ℤ → ℤ → Bool} (hn : 0 < n)
    (hleft : ∀ j : ℤ, a 0 j = true) (hright : ∀ j : ℤ, a ((k : ℤ) + 1) j = false)
    (G' : SimpleGraph (DVert k n)) (hle : ∀ x y, DAdj a k n x y → G'.Adj x y) :
    G'.Reachable (Sum.inr 0) (Sum.inr 1) := by
  let f : cutGraph a k n →g G' :=
    { toFun := id
      map_rel' := fun {x y} => hle x y }
  rw [show (Sum.inr 0 : DVert k n) = f (Sum.inr 0) by rfl,
    show (Sum.inr 1 : DVert k n) = f (Sum.inr 1) by rfl]
  exact SimpleGraph.Reachable.map f (exists_cut_crossing hn hleft hright)

/-! ## 7. Principal declarations and trust -/


#print axioms FK.PlaneTopology.CutCrossing.reachable_of_odd_degree
#print axioms FK.PlaneTopology.CutCrossing.sideBond_parity
#print axioms FK.PlaneTopology.CutCrossing.changes_mod_two
#print axioms FK.PlaneTopology.CutCrossing.odd_changes
#print axioms FK.PlaneTopology.CutCrossing.sideBond_eq_false_of_boundary_left
#print axioms FK.PlaneTopology.CutCrossing.sideBond_eq_false_of_boundary_right
#print axioms FK.PlaneTopology.CutCrossing.adj_inl_iff
#print axioms FK.PlaneTopology.CutCrossing.sideNbr_injOn_cutSides
#print axioms FK.PlaneTopology.CutCrossing.degree_inl_eq
#print axioms FK.PlaneTopology.CutCrossing.even_degree_inl
#print axioms FK.PlaneTopology.CutCrossing.fin4_cases
#print axioms FK.PlaneTopology.CutCrossing.hCutP_iff
#print axioms FK.PlaneTopology.CutCrossing.degree_inr_zero
#print axioms FK.PlaneTopology.CutCrossing.degree_inr_one
#print axioms FK.PlaneTopology.CutCrossing.exists_cut_crossing
#print axioms FK.PlaneTopology.CutCrossing.reachable_of_cut_le
#print axioms FK.PlaneTopology.CutCrossing.vCut_zero_col
#print axioms FK.PlaneTopology.CutCrossing.vCut_last_col
#print axioms FK.PlaneTopology.CutCrossing.DAdj_symm
#print axioms FK.PlaneTopology.CutCrossing.DAdj_irrefl
