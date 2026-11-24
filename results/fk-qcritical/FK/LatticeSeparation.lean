/-
# Mod-2 Jordan separation for finite lattice circuits

This file proves, for a finite set `C` of edges of the square lattice `ℤ × ℤ` in
which every vertex has even `C`-degree (a finite union of closed lattice curves),
the separation statement needed to turn an *open circuit* into a statement about
open paths:

* `Circuit.cellPar` is the mod-2 crossing parity of the eastward ray from a cell.
* `Circuit.cellPar_succ` and `Circuit.handshake` are the two local relations:
  crossing a lattice edge flips the parity of exactly the cells on its two sides.
* `Circuit.chain_vertexPar` : a lattice walk that never visits a vertex incident
  with `C` has constant cell parity along the walk.
* `Circuit.exists_incident_of_walk` : a walk from a vertex of parity `1` to one
  of parity `0` must visit a vertex incident with `C`.
* `Circuit.openConnected_of_enclosed` and
  `Circuit.openConnected_of_cofinal_circuits` : the primal
  at-most-one-infinite-cluster step, from a cofinal family of open enclosing
  lattice circuits.

The parity relations are established by a finite degree count, so nothing here
depends on a Jordan curve theorem: `Mathlib` has none, and metric spheres are
not the loci that dual-percolation arguments produce.
-/
import Mathlib

namespace FK.LatticeSep

open scoped Classical

noncomputable section

/-- A finite set of edges of the square lattice: vertical edges are indexed by
their lower endpoint, horizontal edges by their left endpoint. -/
structure Circuit where
  vert : Finset (ℤ × ℤ)
  horiz : Finset (ℤ × ℤ)

namespace Circuit

variable (C : Circuit)

/-- The vertical edge from `(x,y)` to `(x,y+1)` belongs to `C`. -/
def HasV (x y : ℤ) : Prop := (x, y) ∈ C.vert

/-- The horizontal edge from `(x,y)` to `(x+1,y)` belongs to `C`. -/
def HasH (x y : ℤ) : Prop := (x, y) ∈ C.horiz

/-- The vertex `(a,b)` is incident with an edge of `C`. -/
def Incident (a b : ℤ) : Prop :=
  C.HasV a b ∨ C.HasV a (b - 1) ∨ C.HasH a b ∨ C.HasH (a - 1) b

/-- The parity of the number of `C`-edges incident with the vertex `(a,b)`. -/
def degParity (a b : ℤ) : ZMod 2 :=
  (if C.HasV a b then 1 else 0) + (if C.HasV a (b - 1) then 1 else 0) +
    (if C.HasH a b then 1 else 0) + (if C.HasH (a - 1) b then 1 else 0)

/-- Every vertex has even `C`-degree, i.e. `C` is a union of closed lattice
curves. -/
def EvenDeg : Prop := ∀ a b, C.degParity a b = 0

/-- `x`-coordinates of the vertical `C`-edges at height `y`. -/
def Lv (y : ℤ) : Finset ℤ := (C.vert.filter (fun p => p.2 = y)).image Prod.fst

/-- `x`-coordinates of the horizontal `C`-edges at level `y`. -/
def Lh (y : ℤ) : Finset ℤ := (C.horiz.filter (fun p => p.2 = y)).image Prod.fst

lemma mem_Lv {a y : ℤ} : a ∈ C.Lv y ↔ C.HasV a y := by
  simp [Lv, HasV, Finset.mem_image, Finset.mem_filter, eq_comm]

lemma mem_Lh {a y : ℤ} : a ∈ C.Lh y ↔ C.HasH a y := by
  simp [Lh, HasH, Finset.mem_image, Finset.mem_filter, eq_comm]

/-- Crossing parity of the eastward ray starting in the cell with lower-left
corner `(x,y)`, i.e. from the point `(x+1/2, y+1/2)`. -/
def cellPar (x y : ℤ) : ZMod 2 := (((C.Lv y).filter (fun a => x < a)).card : ZMod 2)

/-- Moving one cell to the east flips the parity exactly across a vertical
`C`-edge. -/
theorem cellPar_succ (x y : ℤ) :
    C.cellPar (x + 1) y + C.cellPar x y = (if C.HasV (x + 1) y then 1 else 0) := by
  have hsplit :
      (C.Lv y).filter (fun a => x < a) =
        (C.Lv y).filter (fun a => x + 1 < a) ∪ (C.Lv y).filter (fun a => a = x + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨ha, hlt⟩
      by_cases h : x + 1 < a
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨ha, by omega⟩
    · rintro (⟨ha, h⟩ | ⟨ha, h⟩)
      · exact ⟨ha, by omega⟩
      · exact ⟨ha, by omega⟩
  have hdisj : Disjoint ((C.Lv y).filter (fun a => x + 1 < a))
      ((C.Lv y).filter (fun a => a = x + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter] at ha ha'
    omega
  have hcard : ((C.Lv y).filter (fun a => a = x + 1)).card
      = if C.HasV (x + 1) y then 1 else 0 := by
    by_cases h : C.HasV (x + 1) y
    · have hone : (C.Lv y).filter (fun a => a = x + 1) = {x + 1} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · rintro rfl
          exact ⟨(mem_Lv (C := C)).mpr h, rfl⟩
      rw [hone, Finset.card_singleton, if_pos h]
    · have hnone : (C.Lv y).filter (fun a => a = x + 1) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro a ha
        simp only [Finset.mem_filter] at ha
        exact h (ha.2 ▸ (mem_Lv (C := C)).mp ha.1)
      rw [hnone, Finset.card_empty, if_neg h]
  simp only [cellPar, hsplit, Finset.card_union_of_disjoint hdisj, hcard]
  push_cast
  rw [← add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul, zero_add]

end Circuit

end

namespace Circuit

variable (C : Circuit)

/-- Sum of a masked indicator over a finset of integers. -/
lemma sum_masked_eq_card {T B : Finset ℤ} (hB : B ⊆ T) (x : ℤ) :
    (∑ a ∈ T, (if x < a then (if a ∈ B then (1 : ZMod 2) else 0) else 0))
      = ((B.filter (fun a => x < a)).card : ZMod 2) := by
  have hterm : ∀ a : ℤ,
      (if x < a then (if a ∈ B then (1 : ZMod 2) else 0) else 0)
        = (if a ∈ B.filter (fun a => x < a) then 1 else 0) := by
    intro a
    by_cases hxa : x < a
    · by_cases haB : a ∈ B
      · rw [if_pos hxa, if_pos haB, if_pos (Finset.mem_filter.mpr ⟨haB, hxa⟩)]
      · rw [if_pos hxa, if_neg haB, if_neg (fun h => haB (Finset.mem_filter.mp h).1)]
    · rw [if_neg hxa, if_neg (fun h => hxa (Finset.mem_filter.mp h).2)]
  simp only [hterm, Finset.sum_boole]
  have hTeq : T.filter (fun a => a ∈ B.filter (fun a => x < a)) = B.filter (fun a => x < a) := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, ha⟩; exact ha
    · intro ha; exact ⟨hB ha.1, ha⟩
  rw [hTeq]

end Circuit

namespace Circuit

variable (C : Circuit)

/-- **Handshake.** Moving one cell north flips the parity exactly across the
horizontal `C`-edge at the level between them. Proved by summing the even-degree
condition over all vertices strictly to the right of the cell. -/
theorem handshake (h : C.EvenDeg) (x y : ℤ) :
    C.cellPar x y + C.cellPar x (y + 1) = (if C.HasH x (y + 1) then 1 else 0) := by
  set A0 := C.Lv y with hA0
  set A1 := C.Lv (y + 1) with hA1
  set C1 := C.Lh (y + 1) with hC1
  set T := A0 ∪ A1 ∪ C1 ∪ C1.image (fun a => a + 1) with hT
  have hA0T : A0 ⊆ T := fun a ha => by rw [hT]; simp [ha]
  have hA1T : A1 ⊆ T := fun a ha => by rw [hT]; simp [ha]
  have hC1T : C1 ⊆ T := fun a ha => by rw [hT]; simp [ha]
  have hImgT : C1.image (fun c => c + 1) ⊆ T := fun a ha => by
    rw [hT]; exact Finset.mem_union_right _ ha
  have hpoint : ∀ a : ℤ, (if a ∈ A1 then (1 : ZMod 2) else 0) + (if a ∈ A0 then 1 else 0) +
      (if a ∈ C1 then 1 else 0) + (if a - 1 ∈ C1 then 1 else 0) = 0 := by
    intro a
    have key := h a (y + 1)
    simp only [degParity, HasV, HasH, add_sub_cancel_right] at key
    have h1 : (a ∈ A1) ↔ ((a, y + 1) ∈ C.vert) := by
      rw [hA1]; exact mem_Lv (C := C)
    have h2 : (a ∈ A0) ↔ ((a, y) ∈ C.vert) := by
      rw [hA0]; exact mem_Lv (C := C)
    have h3 : (a ∈ C1) ↔ ((a, y + 1) ∈ C.horiz) := by
      rw [hC1]; exact mem_Lh (C := C)
    have h4 : (a - 1 ∈ C1) ↔ ((a - 1, y + 1) ∈ C.horiz) := by
      rw [hC1]; exact mem_Lh (C := C)
    by_cases hc1 : a ∈ A1 <;> by_cases hc2 : a ∈ A0 <;>
      by_cases hc3 : a ∈ C1 <;> by_cases hc4 : a - 1 ∈ C1 <;>
      (simp only [← h1, ← h2, ← h3, ← h4, hc1, hc2, hc3, hc4, if_true, if_false] at key ⊢
       exact key)
  have hsum : (∑ a ∈ T, ((if x < a then (if a ∈ A1 then (1 : ZMod 2) else 0) else 0)
      + (if x < a then (if a ∈ A0 then 1 else 0) else 0)
      + (if x < a then (if a ∈ C1 then 1 else 0) else 0)
      + (if x < a then (if a - 1 ∈ C1 then 1 else 0) else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases hxa : x < a
    · simp only [hxa, if_true]
      exact hpoint a
    · simp [hxa]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have e1 : (∑ a ∈ T, (if x < a then (if a ∈ A1 then (1 : ZMod 2) else 0) else 0))
      = C.cellPar x (y + 1) := by
    rw [sum_masked_eq_card (B := A1) (T := T) hA1T x]
    rfl
  have e2 : (∑ a ∈ T, (if x < a then (if a ∈ A0 then (1 : ZMod 2) else 0) else 0))
      = C.cellPar x y := by
    rw [sum_masked_eq_card (B := A0) (T := T) hA0T x]
    rfl
  have e3 : (∑ a ∈ T, (if x < a then (if a ∈ C1 then (1 : ZMod 2) else 0) else 0))
      = ((C1.filter (fun a => x < a)).card : ZMod 2) :=
    sum_masked_eq_card (B := C1) (T := T) hC1T x
  have e4 : (∑ a ∈ T, (if x < a then (if a - 1 ∈ C1 then (1 : ZMod 2) else 0) else 0))
      = ((C1.filter (fun a => x - 1 < a)).card : ZMod 2) := by
    have hstep : ∀ a : ℤ, (if x < a then (if a - 1 ∈ C1 then (1 : ZMod 2) else 0) else 0)
        = (if x < a then (if a ∈ C1.image (fun c => c + 1) then 1 else 0) else 0) := by
      intro a
      have hiff : (a - 1 ∈ C1) ↔ (a ∈ C1.image (fun c => c + 1)) := by
        rw [Finset.mem_image]
        constructor
        · intro hh
          exact ⟨a - 1, hh, by omega⟩
        · rintro ⟨c, hc, hca⟩
          have hca' : a - 1 = c := by omega
          rw [hca']
          exact hc
      by_cases hxa : x < a
      · rw [if_pos hxa, if_pos hxa]
        by_cases hc : a - 1 ∈ C1
        · rw [if_pos hc, if_pos (hiff.mp hc)]
        · rw [if_neg hc, if_neg (fun hh => hc (hiff.mpr hh))]
      · rw [if_neg hxa, if_neg hxa]
    rw [Finset.sum_congr rfl (fun a _ => hstep a)]
    rw [sum_masked_eq_card (T := T) (B := C1.image (fun c => c + 1)) hImgT x]
    have hsets : (C1.filter (fun c => x < c + 1))
        = C1.filter (fun a => x - 1 < a) := by
      ext c
      simp only [Finset.mem_filter]
      constructor <;> intro hh <;> refine ⟨hh.1, ?_⟩ <;> omega
    have himg : (C1.image (fun c => c + 1)).filter (fun a => x < a)
        = (C1.filter (fun c => x < c + 1)).image (fun c => c + 1) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨c, hc, rfl⟩, hlt⟩
        exact ⟨c, ⟨hc, hlt⟩, rfl⟩
      · rintro ⟨c, ⟨hc, hlt⟩, rfl⟩
        exact ⟨⟨c, hc, rfl⟩, hlt⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b hab => by omega), hsets]
  rw [e1, e2, e3, e4] at hsum
  have hsplit : (C1.filter (fun a => x - 1 < a))
      = (C1.filter (fun a => x < a)) ∪ (C1.filter (fun a => a = x)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨ha, hlt⟩
      by_cases hxa : x < a
      · exact Or.inl ⟨ha, hxa⟩
      · exact Or.inr ⟨ha, by omega⟩
    · rintro (⟨ha, h⟩ | ⟨ha, h⟩)
      · exact ⟨ha, by omega⟩
      · exact ⟨ha, by omega⟩
  have hdisj : Disjoint (C1.filter (fun a => x < a)) (C1.filter (fun a => a = x)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_filter] at ha ha'
    omega
  have hcardx : ((C1.filter (fun a => a = x)).card : ZMod 2)
      = (if C.HasH x (y + 1) then 1 else 0) := by
    by_cases hx : x ∈ C1
    · have hone : C1.filter (fun a => a = x) = {x} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · rintro rfl; exact ⟨hx, rfl⟩
      rw [hone, Finset.card_singleton, if_pos ((mem_Lh (C := C)).mp (hC1 ▸ hx))]
      simp
    · have hnone : C1.filter (fun a => a = x) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro a ha
        simp only [Finset.mem_filter] at ha
        exact hx (ha.2 ▸ ha.1)
      rw [hnone, Finset.card_empty,
        if_neg (fun hh => hx (hC1.symm ▸ (mem_Lh (C := C)).mpr hh))]
      simp
  have hcard' : ((C1.filter (fun a => x - 1 < a)).card : ZMod 2)
      = ((C1.filter (fun a => x < a)).card : ZMod 2)
        + (if C.HasH x (y + 1) then 1 else 0) := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    push_cast
    rw [hcardx]
  rw [hcard'] at hsum
  have hzero : ∀ t : ZMod 2, t + t = 0 := by decide
  have hrearr : (((C.cellPar x (y + 1) + C.cellPar x y)
        + ((C1.filter (fun a => x < a)).card : ZMod 2))
      + (((C1.filter (fun a => x < a)).card : ZMod 2)
        + (if C.HasH x (y + 1) then 1 else 0)))
      = ((C.cellPar x (y + 1) + C.cellPar x y) + (if C.HasH x (y + 1) then 1 else 0))
        + (((C1.filter (fun a => x < a)).card : ZMod 2)
          + ((C1.filter (fun a => x < a)).card : ZMod 2)) := by
    ring
  rw [hrearr, hzero, add_zero] at hsum
  exact (show ∀ a b d : ZMod 2, a + b + d = 0 → b + a = d from by decide) _ _ _ hsum

end Circuit





open Classical

/-- Lattice adjacency of vertices of `ℤ × ℤ`, in a form convenient for case
analysis (the four unit steps). -/
def Adjacent (u v : ℤ × ℤ) : Prop :=
  (u.1 = v.1 ∧ (u.2 = v.2 + 1 ∨ u.2 + 1 = v.2)) ∨
    (u.2 = v.2 ∧ (u.1 = v.1 + 1 ∨ u.1 + 1 = v.1))

/-- A walk in the lattice: a list of successive vertices. -/
def WalkFrom : ℤ × ℤ → List (ℤ × ℤ) → Prop
  | _, [] => True
  | u, v :: rest => Adjacent u v ∧ WalkFrom v rest

namespace Circuit

variable (C : Circuit)

/-- The parity of the cell at the north-east of a vertex. -/
def vertexPar (u : ℤ × ℤ) : ZMod 2 := C.cellPar u.1 u.2

lemma not_incident_iff (a b : ℤ) : ¬ C.Incident a b ↔
    ¬ C.HasV a b ∧ ¬ C.HasV a (b - 1) ∧ ¬ C.HasH a b ∧ ¬ C.HasH (a - 1) b := by
  simp only [Incident, not_or]

/-- Adjacent vertices, both not incident with `C`, have the same vertex parity. -/
theorem vertexPar_step (h : C.EvenDeg) {u v : ℤ × ℤ} (huv : Adjacent u v)
    (hu : ¬ C.Incident u.1 u.2) (hv : ¬ C.Incident v.1 v.2) :
    C.vertexPar u = C.vertexPar v := by
  have hu' := (not_incident_iff C u.1 u.2).mp hu
  have hv' := (not_incident_iff C v.1 v.2).mp hv
  have key1 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have key2 : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  rcases huv with ⟨he1, he2 | he2⟩ | ⟨he2, he1 | he1⟩
  · -- v = (u.1, u.2 - 1)
    have hEq : (u.2 - 1) + 1 = u.2 := by ring
    have hs := C.handshake h u.1 (u.2 - 1)
    rw [hEq, if_neg hu'.2.2.1] at hs
    simp only [vertexPar]
    rw [show v.1 = u.1 from he1.symm, show v.2 = u.2 - 1 from by omega]
    exact key2 _ _ hs
  · -- v = (u.1, u.2 + 1)
    have hH : ¬ C.HasH u.1 (u.2 + 1) := by
      rw [show v.1 = u.1 from he1.symm, show v.2 = u.2 + 1 from he2.symm] at hv'
      exact hv'.2.2.1
    have hs := C.handshake h u.1 u.2
    rw [if_neg hH] at hs
    simp only [vertexPar]
    rw [show v.1 = u.1 from he1.symm, show v.2 = u.2 + 1 from he2.symm]
    exact key1 _ _ hs
  · -- v = (u.1 - 1, u.2) : u.1 = v.1 + 1
    have hV : ¬ C.HasV (v.1 + 1) v.2 := by
      rw [show u.1 = v.1 + 1 from he1, show u.2 = v.2 from he2] at hu'
      exact hu'.1
    have hs := C.cellPar_succ v.1 v.2
    rw [if_neg hV] at hs
    simp only [vertexPar]
    rw [show u.1 = v.1 + 1 from he1, show u.2 = v.2 from he2]
    exact key1 _ _ hs
  · -- v = (u.1 + 1, u.2) : u.1 + 1 = v.1
    have hV : ¬ C.HasV (u.1 + 1) u.2 := by
      rw [show v.1 = u.1 + 1 from he1.symm, show v.2 = u.2 from he2.symm] at hv'
      exact hv'.1
    have hs := C.cellPar_succ u.1 u.2
    rw [if_neg hV] at hs
    simp only [vertexPar]
    rw [show v.1 = u.1 + 1 from he1.symm, show v.2 = u.2 from he2.symm]
    exact key2 _ _ hs

/-- Along a lattice walk all of whose vertices avoid `C`, the vertex parity is
constant. -/
theorem chain_vertexPar (h : C.EvenDeg) :
    ∀ (l : List (ℤ × ℤ)) (u : ℤ × ℤ), WalkFrom u l →
      (¬ C.Incident u.1 u.2) → (∀ v ∈ l, ¬ C.Incident v.1 v.2) →
      ∀ w ∈ l, C.vertexPar u = C.vertexPar w
  | [], u, _, _, _, w, hw => by simp at hw
  | v :: rest, u, hw, hu, hall, w, hwmem => by
      obtain ⟨huv, hrest⟩ := hw
      have hv : ¬ C.Incident v.1 v.2 := hall v (by simp)
      rcases List.mem_cons.mp hwmem with rfl | hwmem
      · exact C.vertexPar_step h huv hu hv
      · exact (C.vertexPar_step h huv hu hv).trans
          (chain_vertexPar h rest v hrest hv
            (fun x hx => hall x (by simp [hx])) w hwmem)

/-- Crossing parity of a cell far to the right of all edges of `C` vanishes. -/
theorem cellPar_of_bound {N y : ℤ} (hb : ∀ p ∈ C.vert, p.1 ≤ N) :
    C.cellPar N y = 0 := by
  have hempty : (C.Lv y).filter (fun a => N < a) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro a ha
    simp only [Finset.mem_filter] at ha
    have hx : a ≤ N := hb (a, y) ((mem_Lv (C := C)).mp ha.1)
    omega
  simp [cellPar, hempty]

/-- Some cell has parity `1` as soon as `C` is nonempty. -/
theorem exists_cellPar_one (hne : C.vert.Nonempty) : ∃ x y : ℤ, C.cellPar x y = 1 := by
  obtain ⟨⟨x, y⟩, hmem⟩ := hne
  have hV : C.HasV x y := hmem
  have hs := C.cellPar_succ (x - 1) y
  rw [show x - 1 + 1 = x from by ring, if_pos hV] at hs
  rcases (show ∀ a b : ZMod 2, a + b = 1 → a = 1 ∨ b = 1 from by decide)
    _ _ hs with h1 | h0
  · exact ⟨x, y, h1⟩
  · exact ⟨x - 1, y, h0⟩

/-- **Separation.** An open lattice walk from a vertex whose north-east cell has
parity `1` to a vertex whose north-east cell has parity `0` must visit a vertex
incident with `C`. -/
theorem exists_incident_of_walk (h : C.EvenDeg) {u w : ℤ × ℤ} {l : List (ℤ × ℤ)}
    (hw : WalkFrom u l) (hwl : w ∈ l) (h1 : C.vertexPar u = 1)
    (h0 : C.vertexPar w = 0) : ∃ x ∈ (u :: l), C.Incident x.1 x.2 := by
  by_contra hcon
  push_neg at hcon
  have hu : ¬ C.Incident u.1 u.2 := hcon u (by simp)
  have hall : ∀ v ∈ l, ¬ C.Incident v.1 v.2 := fun v hv => hcon v (by simp [hv])
  have heq := C.chain_vertexPar h l u hw hu hall w hwl
  rw [h1, h0] at heq
  exact absurd heq (by decide)

end Circuit





/-- Open/closed state of the edges of the square lattice. -/
structure Bonds where
  vertOpen : ℤ × ℤ → Bool
  horizOpen : ℤ × ℤ → Bool

/-- One step of the lattice from `u` to `v` using an open edge. -/
def OpenStep (B : Bonds) (u v : ℤ × ℤ) : Prop :=
  (u.1 = v.1 ∧ ((u.2 = v.2 + 1 ∧ B.vertOpen (v.1, v.2) = true) ∨
    (u.2 + 1 = v.2 ∧ B.vertOpen (u.1, u.2) = true))) ∨
  (u.2 = v.2 ∧ ((u.1 = v.1 + 1 ∧ B.horizOpen (v.1, v.2) = true) ∨
    (u.1 + 1 = v.1 ∧ B.horizOpen (u.1, u.2) = true)))

/-- Open connectivity of lattice vertices. -/
def OpenConnected (B : Bonds) (u v : ℤ × ℤ) : Prop :=
  Relation.ReflTransGen (OpenStep B) u v

lemma openStep_adjacent {B : Bonds} {u v : ℤ × ℤ} (h : OpenStep B u v) :
    Adjacent u v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h2 with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl ⟨h1, Or.inl he⟩
    · exact Or.inl ⟨h1, Or.inr he⟩
  · rcases h2 with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inr ⟨h1, Or.inl he⟩
    · exact Or.inr ⟨h1, Or.inr he⟩

lemma openStep_symm {B : Bonds} {u v : ℤ × ℤ} (h : OpenStep B u v) :
    OpenStep B v u := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases h2 with ⟨he, hb⟩ | ⟨he, hb⟩
    · exact Or.inl ⟨h1.symm, Or.inr ⟨by omega, hb⟩⟩
    · exact Or.inl ⟨h1.symm, Or.inl ⟨by omega, hb⟩⟩
  · rcases h2 with ⟨he, hb⟩ | ⟨he, hb⟩
    · exact Or.inr ⟨h1.symm, Or.inr ⟨by omega, hb⟩⟩
    · exact Or.inr ⟨h1.symm, Or.inl ⟨by omega, hb⟩⟩

lemma openConnected_symm {B : Bonds} {u v : ℤ × ℤ} (h : OpenConnected B u v) :
    OpenConnected B v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact (Relation.ReflTransGen.single (openStep_symm hbc)).trans ih

namespace Circuit

variable (C : Circuit)

/-- All edges of `C` are open in `B`. -/
def AllOpen (B : Bonds) : Prop :=
  (∀ x y, C.HasV x y → B.vertOpen (x, y) = true) ∧
    (∀ x y, C.HasH x y → B.horizOpen (x, y) = true)

/-- An open path from a vertex with crossing parity `1` to one with parity `0`
visits a vertex incident with `C`, and that vertex is open-connected to the
start. -/
theorem incident_of_openConnected (h : C.EvenDeg) {B : Bonds} {u v : ℤ × ℤ}
    (huv : OpenConnected B u v) (hu : C.vertexPar u = 1) (hv : C.vertexPar v = 0) :
    ∃ x : ℤ × ℤ, C.Incident x.1 x.2 ∧ OpenConnected B u x := by
  revert hu
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hu
      rw [hu] at hv
      exact absurd hv (by decide)
  | @head a c hac hcv ih =>
      intro hu
      by_cases hca : C.Incident a.1 a.2
      · exact ⟨a, hca, Relation.ReflTransGen.refl⟩
      · by_cases hcc : C.Incident c.1 c.2
        · exact ⟨c, hcc, Relation.ReflTransGen.single hac⟩
        · have hpar := C.vertexPar_step h (openStep_adjacent hac) hca hcc
          obtain ⟨x, hx, hcon⟩ := ih (hpar ▸ hu)
          exact ⟨x, hx, Relation.ReflTransGen.head hac hcon⟩

end Circuit



namespace Circuit

variable (C : Circuit)

/-- Crossing parity vanishes on every cell to the right of all edges of `C`. -/
theorem cellPar_eq_zero_of_le {x y N : ℤ} (hb : ∀ p ∈ C.vert, p.1 ≤ N) (hN : N ≤ x) :
    C.cellPar x y = 0 := by
  have hempty : (C.Lv y).filter (fun a => x < a) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro a ha
    simp only [Finset.mem_filter] at ha
    have hx : a ≤ N := hb (a, y) ((mem_Lv (C := C)).mp ha.1)
    omega
  simp [cellPar, hempty]

/-- **At most one infinite cluster from an enclosing open circuit.** If `u` and
`w` are enclosed by the same open circuit `C` (both north-east cells of parity
`1`), and both are joined by open paths to vertices far to the right of `C`,
then `u` and `w` are open connected. -/
theorem openConnected_of_enclosed (h : C.EvenDeg) {B : Bonds} {N : ℤ}
    (hbound : ∀ p ∈ C.vert, p.1 ≤ N)
    (hC : ∀ p q : ℤ × ℤ, C.Incident p.1 p.2 → C.Incident q.1 q.2 → OpenConnected B p q)
    {u w : ℤ × ℤ} (hu : C.vertexPar u = 1) (hw : C.vertexPar w = 1)
    (huinf : ∃ v : ℤ × ℤ, N ≤ v.1 ∧ OpenConnected B u v)
    (hwinf : ∃ v : ℤ × ℤ, N ≤ v.1 ∧ OpenConnected B w v) :
    OpenConnected B u w := by
  obtain ⟨v, hvN, huv⟩ := huinf
  obtain ⟨v', hv'N, hwv'⟩ := hwinf
  have hv0 : C.vertexPar v = 0 := C.cellPar_eq_zero_of_le hbound hvN
  have hv'0 : C.vertexPar v' = 0 := C.cellPar_eq_zero_of_le hbound hv'N
  obtain ⟨x, hx, hux⟩ := C.incident_of_openConnected h huv hu hv0
  obtain ⟨y, hy, hwy⟩ := C.incident_of_openConnected h hwv' hw hv'0
  exact hux.trans ((hC x y hx hy).trans (openConnected_symm hwy))

/-- **At most one infinite cluster.** If every finite set of lattice vertices is
enclosed by a closed lattice curve all of whose incident vertices lie in a single
open component, then any two vertices that are joined to vertices arbitrarily far
to the right are open connected. This is the primal at-most-one-cluster step with
the open circuit as an explicit geometric input. -/
theorem openConnected_of_cofinal_circuits (B : Bonds)
    (hcof : ∀ S : Finset (ℤ × ℤ), ∃ (C : Circuit) (N : ℤ),
      C.EvenDeg ∧ (∀ p ∈ C.vert, p.1 ≤ N) ∧
        (∀ s ∈ S, C.vertexPar s = 1) ∧
        (∀ p q : ℤ × ℤ, C.Incident p.1 p.2 → C.Incident q.1 q.2 →
          OpenConnected B p q))
    {u w : ℤ × ℤ}
    (hu : ∀ N : ℤ, ∃ v : ℤ × ℤ, N ≤ v.1 ∧ OpenConnected B u v)
    (hw : ∀ N : ℤ, ∃ v : ℤ × ℤ, N ≤ v.1 ∧ OpenConnected B w v) :
    OpenConnected B u w := by
  obtain ⟨C, N, hdeg, hbound, henc, hC⟩ := hcof {u, w}
  exact C.openConnected_of_enclosed hdeg hbound hC
    (henc u (by simp)) (henc w (by simp)) (hu N) (hw N)

end Circuit

namespace Circuit

/-! ## Non-vacuity: the unit square -/

/-- The unit square (a genuine closed lattice curve) has even degree everywhere. -/
theorem unitSquare_evenDeg : (⟨{(0, 0), (1, 0)}, {(0, 0), (0, 1)}⟩ : Circuit).EvenDeg := by
  intro a b
  simp only [degParity, HasV, HasH, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  by_cases ha0 : a = 0 <;> by_cases ha1 : a = 1 <;> by_cases hb0 : b = 0 <;>
    by_cases hb1 : b = 1 <;> by_cases hbm : b - 1 = 0 <;> by_cases ham : a - 1 = 0 <;>
    simp_all <;> (first | decide | omega)

/-- The fully open lattice: a sanity check that `OpenConnected` has the intended
content. -/
def allOpen : Bonds := ⟨fun _ => true, fun _ => true⟩

theorem allOpen_step_h : OpenStep allOpen (0, 0) (1, 0) := by
  simp [OpenStep, allOpen]

theorem allOpen_step_v : OpenStep allOpen (1, 0) (1, 1) := by
  simp [OpenStep, allOpen]

theorem allOpen_openConnected : OpenConnected allOpen (0, 0) (1, 1) :=
  Relation.ReflTransGen.head allOpen_step_h
    (Relation.ReflTransGen.single allOpen_step_v)

/-- The crossing parity detects the interior of the unit square: the cell inside
has parity `1`, cells outside have parity `0`. -/
theorem unitSquare_cellPar :
    (⟨{(0, 0), (1, 0)}, {(0, 0), (0, 1)}⟩ : Circuit).cellPar 0 0 = 1 ∧
      (⟨{(0, 0), (1, 0)}, {(0, 0), (0, 1)}⟩ : Circuit).cellPar 1 0 = 0 ∧
      (⟨{(0, 0), (1, 0)}, {(0, 0), (0, 1)}⟩ : Circuit).cellPar (-1) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The side-two square: parity `1` strictly inside, `0` outside. -/
theorem square2_cellPar :
    (⟨{(0, 0), (0, 1), (2, 0), (2, 1)}, {(0, 0), (1, 0), (0, 2), (1, 2)}⟩ : Circuit).cellPar 1 1 = 1 ∧
      (⟨{(0, 0), (0, 1), (2, 0), (2, 1)}, {(0, 0), (1, 0), (0, 2), (1, 2)}⟩ : Circuit).cellPar 3 1 = 0 := by
  refine ⟨?_, ?_⟩ <;> decide

end Circuit

end FK.LatticeSep

/-! ## Axiom audit -/

#print axioms FK.LatticeSep.Circuit.cellPar_succ
#print axioms FK.LatticeSep.Circuit.handshake
#print axioms FK.LatticeSep.Circuit.vertexPar_step
#print axioms FK.LatticeSep.Circuit.chain_vertexPar
#print axioms FK.LatticeSep.Circuit.exists_cellPar_one
#print axioms FK.LatticeSep.Circuit.exists_incident_of_walk
#print axioms FK.LatticeSep.openStep_adjacent
#print axioms FK.LatticeSep.openStep_symm
#print axioms FK.LatticeSep.openConnected_symm
#print axioms FK.LatticeSep.Circuit.incident_of_openConnected
#print axioms FK.LatticeSep.Circuit.openConnected_of_enclosed
#print axioms FK.LatticeSep.Circuit.openConnected_of_cofinal_circuits
#print axioms FK.LatticeSep.Circuit.allOpen_openConnected
#print axioms FK.LatticeSep.Circuit.unitSquare_evenDeg
#print axioms FK.LatticeSep.Circuit.unitSquare_cellPar
#print axioms FK.LatticeSep.Circuit.square2_cellPar
