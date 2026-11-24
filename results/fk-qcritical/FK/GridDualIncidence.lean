import FK.GridFrontier
import FK.GridOpenCuts
import FK.ConfigurationDuality

/-!
# Exact face--dual incidence for the square lattice

The square lattice is self-dual: the *dual* lattice of unit-square centres is the
same graph shifted by `(1/2, 1/2)`.  This file makes the incidence exact.  Each
primal edge is crossed by exactly one dual edge and vice versa, and the
correspondence is packaged as an equivalence
`gridCrossEquiv : gridGraph.edgeSet ≃ gridDual.edgeSet` of edge types, so that
`FK.Configuration.dualConfig` turns a primal configuration into the genuine
complementary face--dual configuration.

`dualLo`/`dualHi` (resp. `uncrossLo`/`uncrossHi`) compute the two face centres
adjacent to a primal edge (resp. the two lattice vertices adjacent to a dual
edge).  All four are *symmetric* functions of the unordered pair, hence lift to
`Sym2`, which is what makes the well-definedness on unoriented edges automatic.

## Main results

* `FK.PlaneTopology.GridDualIncidence.gridCrossEquiv`
* `FK.PlaneTopology.GridDualIncidence.gridCrossEquiv_apply`
* `FK.PlaneTopology.GridDualIncidence.dual_open_iff`
-/

namespace FK.PlaneTopology.GridDualIncidence

open Set
open scoped Classical
open FK.PlaneTopology
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridOpenCuts

/-! ## The two faces of a primal edge -/

/-- The *lower* (for a horizontal edge) or *left* (for a vertical edge) unit
square adjacent to the lattice edge through `p` and `q`.  Off the adjacency
relation the value is a junk term `(0,0)`; only the symmetric shape matters. -/
def dualLo (p q : GridV) : GridV :=
  if p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1) then (min p.1 q.1, p.2 - 1)
  else if p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1) then
    (min p.1 q.1 - 1, min p.2 q.2)
  else (0, 0)

/-- The *upper* (for a horizontal edge) or *right* (for a vertical edge) unit
square adjacent to the lattice edge through `p` and `q`. -/
def dualHi (p q : GridV) : GridV :=
  if p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1) then (min p.1 q.1, p.2)
  else if p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1) then
    (min p.1 q.1, min p.2 q.2)
  else (1, 0)

lemma dualLo_comm (p q : GridV) : dualLo p q = dualLo q p := by
  unfold dualLo
  by_cases h1 : p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1)
  · have h1' : q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1) := ⟨h1.1.symm, h1.2.symm⟩
    rw [if_pos h1, if_pos h1']
    rw [min_comm q.1 p.1, h1.1]
  · have h1' : ¬ (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1)) := by
      rintro ⟨c, d⟩; exact h1 ⟨c.symm, d.symm⟩
    rw [if_neg h1, if_neg h1']
    by_cases h2 : p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)
    · have h2' : q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1) := ⟨h2.1.symm, h2.2.symm⟩
      rw [if_pos h2, if_pos h2', min_comm q.1 p.1, min_comm q.2 p.2]
    · have h2' : ¬ (q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) := by
        rintro ⟨c, d⟩; exact h2 ⟨c.symm, d.symm⟩
      rw [if_neg h2, if_neg h2']

lemma dualHi_comm (p q : GridV) : dualHi p q = dualHi q p := by
  unfold dualHi
  by_cases h1 : p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ q.1 = p.1 + 1)
  · have h1' : q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1) := ⟨h1.1.symm, h1.2.symm⟩
    rw [if_pos h1, if_pos h1']
    rw [min_comm q.1 p.1, h1.1]
  · have h1' : ¬ (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1)) := by
      rintro ⟨c, d⟩; exact h1 ⟨c.symm, d.symm⟩
    rw [if_neg h1, if_neg h1']
    by_cases h2 : p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)
    · have h2' : q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1) := ⟨h2.1.symm, h2.2.symm⟩
      rw [if_pos h2, if_pos h2', min_comm q.1 p.1, min_comm q.2 p.2]
    · have h2' : ¬ (q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) := by
        rintro ⟨c, d⟩; exact h2 ⟨c.symm, d.symm⟩
      rw [if_neg h2, if_neg h2']

/-- Value of `dualLo` on a horizontal lattice edge. -/
lemma dualLo_horiz {p q : GridV} (h1 : p.2 = q.2)
    (h2 : p.1 = q.1 + 1 ∨ q.1 = p.1 + 1) : dualLo p q = (min p.1 q.1, p.2 - 1) := by
  unfold dualLo
  rw [if_pos ⟨h1, h2⟩]

/-- Value of `dualHi` on a horizontal lattice edge. -/
lemma dualHi_horiz {p q : GridV} (h1 : p.2 = q.2)
    (h2 : p.1 = q.1 + 1 ∨ q.1 = p.1 + 1) : dualHi p q = (min p.1 q.1, p.2) := by
  unfold dualHi
  rw [if_pos ⟨h1, h2⟩]

/-- Value of `dualLo` on a vertical lattice edge. -/
lemma dualLo_vert {p q : GridV} (h1 : p.1 = q.1)
    (h2 : p.2 = q.2 + 1 ∨ q.2 = p.2 + 1) :
    dualLo p q = (min p.1 q.1 - 1, min p.2 q.2) := by
  unfold dualLo
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

/-- Value of `dualHi` on a vertical lattice edge. -/
lemma dualHi_vert {p q : GridV} (h1 : p.1 = q.1)
    (h2 : p.2 = q.2 + 1 ∨ q.2 = p.2 + 1) :
    dualHi p q = (min p.1 q.1, min p.2 q.2) := by
  unfold dualHi
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

/-- The two face centres adjacent to a lattice edge are adjacent in the face
lattice: the primal edge separates them. -/
lemma gridAdj_dualLo_dualHi {p q : GridV} (h : gridAdj p q) :
    gridAdj (dualLo p q) (dualHi p q) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · rw [dualLo_vert h1 (Or.inl h2), dualHi_vert h1 (Or.inl h2)]
    exact Or.inr ⟨rfl, Or.inr (by omega)⟩
  · rw [dualLo_vert h1 (Or.inr h2), dualHi_vert h1 (Or.inr h2)]
    exact Or.inr ⟨rfl, Or.inr (by omega)⟩
  · rw [dualLo_horiz h1 (Or.inl h2), dualHi_horiz h1 (Or.inl h2)]
    exact Or.inl ⟨rfl, Or.inr (by omega)⟩
  · rw [dualLo_horiz h1 (Or.inr h2), dualHi_horiz h1 (Or.inr h2)]
    exact Or.inl ⟨rfl, Or.inr (by omega)⟩

/-! ## The crossing map on unoriented edges -/

/-- The crossing map on unordered pairs of lattice vertices.  It is symmetric by
construction, so it descends to `Sym2`. -/
def crossPair (p q : GridV) : Sym2 GridV := s(dualLo p q, dualHi p q)

lemma crossPair_comm (p q : GridV) : crossPair p q = crossPair q p := by
  unfold crossPair
  rw [dualLo_comm, dualHi_comm]

/-- The face--dual edge crossed by a lattice edge. -/
def crossVal (z : Sym2 GridV) : Sym2 GridV :=
  Sym2.lift ⟨crossPair, crossPair_comm⟩ z

@[simp] lemma crossVal_mk (p q : GridV) : crossVal s(p, q) = crossPair p q :=
  Sym2.lift_mk ⟨crossPair, crossPair_comm⟩ p q

/-- The crossing map on lattice edges. -/
noncomputable def crossEdge (e : gridGraph.edgeSet) : gridGraph.edgeSet where
  val := crossVal e.1
  property := by
    obtain ⟨p, q, hpq, rfl⟩ : ∃ (p q : GridV) (h : gridAdj p q), e = ⟨s(p, q), h⟩ :=
      ⟨edgeFst e, edgeSnd e, edgeFst_adj_edgeSnd e, edge_eq_mk e⟩
    rw [crossVal_mk, crossPair]
    exact gridAdj_dualLo_dualHi hpq

lemma crossEdge_apply (p q : GridV) (h : gridAdj p q) :
    crossEdge (⟨s(p, q), h⟩ : gridGraph.edgeSet) = ⟨crossPair p q,
      by rw [crossPair]; exact gridAdj_dualLo_dualHi h⟩ := by
  refine Subtype.ext ?_
  simp [crossEdge]



/-! ## The inverse crossing map -/

/-- The lattice vertex below/left of the lattice edge crossed by the face edge
through `f` and `g`. -/
def uncrossLo (f g : GridV) : GridV :=
  if f.2 = g.2 ∧ (f.1 = g.1 + 1 ∨ g.1 = f.1 + 1) then (min f.1 g.1 + 1, min f.2 g.2)
  else if f.1 = g.1 ∧ (f.2 = g.2 + 1 ∨ g.2 = f.2 + 1) then (min f.1 g.1, min f.2 g.2 + 1)
  else (0, 1)

/-- The lattice vertex above/right of the lattice edge crossed by the face edge
through `f` and `g`. -/
def uncrossHi (f g : GridV) : GridV :=
  if f.2 = g.2 ∧ (f.1 = g.1 + 1 ∨ g.1 = f.1 + 1) then (min f.1 g.1 + 1, min f.2 g.2 + 1)
  else if f.1 = g.1 ∧ (f.2 = g.2 + 1 ∨ g.2 = f.2 + 1) then (min f.1 g.1 + 1, min f.2 g.2 + 1)
  else (1, 1)

lemma uncrossLo_comm (f g : GridV) : uncrossLo f g = uncrossLo g f := by
  unfold uncrossLo
  by_cases h1 : f.2 = g.2 ∧ (f.1 = g.1 + 1 ∨ g.1 = f.1 + 1)
  · have h1' : g.2 = f.2 ∧ (g.1 = f.1 + 1 ∨ f.1 = g.1 + 1) := ⟨h1.1.symm, h1.2.symm⟩
    rw [if_pos h1, if_pos h1', min_comm g.1 f.1, min_comm g.2 f.2]
  · have h1' : ¬ (g.2 = f.2 ∧ (g.1 = f.1 + 1 ∨ f.1 = g.1 + 1)) := by
      rintro ⟨c, d⟩; exact h1 ⟨c.symm, d.symm⟩
    rw [if_neg h1, if_neg h1']
    by_cases h2 : f.1 = g.1 ∧ (f.2 = g.2 + 1 ∨ g.2 = f.2 + 1)
    · have h2' : g.1 = f.1 ∧ (g.2 = f.2 + 1 ∨ f.2 = g.2 + 1) := ⟨h2.1.symm, h2.2.symm⟩
      rw [if_pos h2, if_pos h2', min_comm g.1 f.1, min_comm g.2 f.2]
    · have h2' : ¬ (g.1 = f.1 ∧ (g.2 = f.2 + 1 ∨ f.2 = g.2 + 1)) := by
        rintro ⟨c, d⟩; exact h2 ⟨c.symm, d.symm⟩
      rw [if_neg h2, if_neg h2']

lemma uncrossHi_comm (f g : GridV) : uncrossHi f g = uncrossHi g f := by
  unfold uncrossHi
  by_cases h1 : f.2 = g.2 ∧ (f.1 = g.1 + 1 ∨ g.1 = f.1 + 1)
  · have h1' : g.2 = f.2 ∧ (g.1 = f.1 + 1 ∨ f.1 = g.1 + 1) := ⟨h1.1.symm, h1.2.symm⟩
    rw [if_pos h1, if_pos h1', min_comm g.1 f.1, min_comm g.2 f.2]
  · have h1' : ¬ (g.2 = f.2 ∧ (g.1 = f.1 + 1 ∨ f.1 = g.1 + 1)) := by
      rintro ⟨c, d⟩; exact h1 ⟨c.symm, d.symm⟩
    rw [if_neg h1, if_neg h1']
    by_cases h2 : f.1 = g.1 ∧ (f.2 = g.2 + 1 ∨ g.2 = f.2 + 1)
    · have h2' : g.1 = f.1 ∧ (g.2 = f.2 + 1 ∨ f.2 = g.2 + 1) := ⟨h2.1.symm, h2.2.symm⟩
      rw [if_pos h2, if_pos h2', min_comm g.1 f.1, min_comm g.2 f.2]
    · have h2' : ¬ (g.1 = f.1 ∧ (g.2 = f.2 + 1 ∨ f.2 = g.2 + 1)) := by
        rintro ⟨c, d⟩; exact h2 ⟨c.symm, d.symm⟩
      rw [if_neg h2, if_neg h2']

lemma uncrossLo_horiz {f g : GridV} (h1 : f.2 = g.2)
    (h2 : f.1 = g.1 + 1 ∨ g.1 = f.1 + 1) :
    uncrossLo f g = (min f.1 g.1 + 1, min f.2 g.2) := by
  unfold uncrossLo
  rw [if_pos ⟨h1, h2⟩]

lemma uncrossHi_horiz {f g : GridV} (h1 : f.2 = g.2)
    (h2 : f.1 = g.1 + 1 ∨ g.1 = f.1 + 1) :
    uncrossHi f g = (min f.1 g.1 + 1, min f.2 g.2 + 1) := by
  unfold uncrossHi
  rw [if_pos ⟨h1, h2⟩]

lemma uncrossLo_vert {f g : GridV} (h1 : f.1 = g.1)
    (h2 : f.2 = g.2 + 1 ∨ g.2 = f.2 + 1) :
    uncrossLo f g = (min f.1 g.1, min f.2 g.2 + 1) := by
  unfold uncrossLo
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

lemma uncrossHi_vert {f g : GridV} (h1 : f.1 = g.1)
    (h2 : f.2 = g.2 + 1 ∨ g.2 = f.2 + 1) :
    uncrossHi f g = (min f.1 g.1 + 1, min f.2 g.2 + 1) := by
  unfold uncrossHi
  rw [if_neg (by omega), if_pos ⟨h1, h2⟩]

lemma gridAdj_uncross {f g : GridV} (h : gridAdj f g) :
    gridAdj (uncrossLo f g) (uncrossHi f g) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · rw [uncrossLo_vert h1 (Or.inl h2), uncrossHi_vert h1 (Or.inl h2)]
    exact Or.inr ⟨rfl, Or.inr (by omega)⟩
  · rw [uncrossLo_vert h1 (Or.inr h2), uncrossHi_vert h1 (Or.inr h2)]
    exact Or.inr ⟨rfl, Or.inr (by omega)⟩
  · rw [uncrossLo_horiz h1 (Or.inl h2), uncrossHi_horiz h1 (Or.inl h2)]
    exact Or.inl ⟨rfl, Or.inr (by omega)⟩
  · rw [uncrossLo_horiz h1 (Or.inr h2), uncrossHi_horiz h1 (Or.inr h2)]
    exact Or.inl ⟨rfl, Or.inr (by omega)⟩

/-- The inverse crossing map on unordered pairs of faces. -/
def uncrossPair (f g : GridV) : Sym2 GridV := s(uncrossLo f g, uncrossHi f g)

lemma uncrossPair_comm (f g : GridV) : uncrossPair f g = uncrossPair g f := by
  unfold uncrossPair
  rw [uncrossLo_comm, uncrossHi_comm]

/-- The lattice edge crossed by a face edge. -/
def uncrossVal (z : Sym2 GridV) : Sym2 GridV :=
  Sym2.lift ⟨uncrossPair, uncrossPair_comm⟩ z

@[simp] lemma uncrossVal_mk (f g : GridV) : uncrossVal s(f, g) = uncrossPair f g :=
  Sym2.lift_mk ⟨uncrossPair, uncrossPair_comm⟩ f g

/-- The inverse crossing map on lattice edges. -/
noncomputable def uncrossEdge (e : gridGraph.edgeSet) : gridGraph.edgeSet where
  val := uncrossVal e.1
  property := by
    obtain ⟨f, g, hfg, rfl⟩ : ∃ (f g : GridV) (h : gridAdj f g), e = ⟨s(f, g), h⟩ :=
      ⟨edgeFst e, edgeSnd e, edgeFst_adj_edgeSnd e, edge_eq_mk e⟩
    rw [uncrossVal_mk, uncrossPair]
    exact gridAdj_uncross hfg

lemma crossEdge_apply_mk (p q : GridV) (h : gridAdj p q) :
    crossEdge (⟨s(p, q), h⟩ : gridGraph.edgeSet) =
      (⟨crossPair p q, by rw [crossPair]; exact gridAdj_dualLo_dualHi h⟩ :
        gridGraph.edgeSet) := by
  refine Subtype.ext ?_
  simp [crossEdge]

lemma uncrossEdge_apply_mk (f g : GridV) (h : gridAdj f g) :
    uncrossEdge (⟨s(f, g), h⟩ : gridGraph.edgeSet) =
      (⟨uncrossPair f g, by rw [uncrossPair]; exact gridAdj_uncross h⟩ :
        gridGraph.edgeSet) := by
  refine Subtype.ext ?_
  simp [uncrossEdge]

/-! ## The two crossing maps are mutually inverse -/

/-- Closing tactic for the two round-trip computations: the goal is an
equality of unordered pairs of lattice vertices, i.e. a disjunction of two
coordinate equalities, on which `omega` decides. -/
macro "finish_pair" : tactic =>
  `(tactic|
    (rw [Sym2.eq_iff]
     first
       | (left; simp only [Prod.ext_iff, Prod.mk.injEq]; omega)
       | (right; simp only [Prod.ext_iff, Prod.mk.injEq]; omega)))

/-- Crossing a primal edge and then uncrossing recovers the primal edge. -/
theorem uncrossPair_dualLo_dualHi {p q : GridV} (h : gridAdj p q) :
    uncrossPair (dualLo p q) (dualHi p q) = s(p, q) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hm1 : min p.1 q.1 = q.1 := by omega
    have hm2 : min p.2 q.2 = q.2 := by omega
    have hl : dualLo p q = (q.1 - 1, q.2) := by
      rw [dualLo_vert h1 (Or.inl h2), hm1, hm2]
    have hh : dualHi p q = (q.1, q.2) := by
      rw [dualHi_vert h1 (Or.inl h2), hm1, hm2]
    simp only [uncrossPair, hl, hh,
      uncrossLo_horiz (f := (q.1 - 1, q.2)) (g := (q.1, q.2)) rfl (Or.inr (by omega)),
      uncrossHi_horiz (f := (q.1 - 1, q.2)) (g := (q.1, q.2)) rfl (Or.inr (by omega))]
    finish_pair
  · have hm1 : min p.1 q.1 = q.1 := by omega
    have hm2 : min p.2 q.2 = p.2 := by omega
    have hl : dualLo p q = (q.1 - 1, p.2) := by
      rw [dualLo_vert h1 (Or.inr h2), hm1, hm2]
    have hh : dualHi p q = (q.1, p.2) := by
      rw [dualHi_vert h1 (Or.inr h2), hm1, hm2]
    simp only [uncrossPair, hl, hh,
      uncrossLo_horiz (f := (q.1 - 1, p.2)) (g := (q.1, p.2)) rfl (Or.inr (by omega)),
      uncrossHi_horiz (f := (q.1 - 1, p.2)) (g := (q.1, p.2)) rfl (Or.inr (by omega))]
    finish_pair
  · have hm1 : min p.1 q.1 = q.1 := by omega
    have hl : dualLo p q = (q.1, p.2 - 1) := by
      rw [dualLo_horiz h1 (Or.inl h2), hm1]
    have hh : dualHi p q = (q.1, p.2) := by
      rw [dualHi_horiz h1 (Or.inl h2), hm1]
    simp only [uncrossPair, hl, hh,
      uncrossLo_vert (f := (q.1, p.2 - 1)) (g := (q.1, p.2)) rfl (Or.inr (by omega)),
      uncrossHi_vert (f := (q.1, p.2 - 1)) (g := (q.1, p.2)) rfl (Or.inr (by omega))]
    finish_pair
  · have hm1 : min p.1 q.1 = p.1 := by omega
    have hl : dualLo p q = (p.1, p.2 - 1) := by
      rw [dualLo_horiz h1 (Or.inr h2), hm1]
    have hh : dualHi p q = (p.1, p.2) := by
      rw [dualHi_horiz h1 (Or.inr h2), hm1]
    simp only [uncrossPair, hl, hh,
      uncrossLo_vert (f := (p.1, p.2 - 1)) (g := (p.1, p.2)) rfl (Or.inr (by omega)),
      uncrossHi_vert (f := (p.1, p.2 - 1)) (g := (p.1, p.2)) rfl (Or.inr (by omega))]
    finish_pair

/-- Uncrossing a dual edge and then crossing recovers the dual edge. -/
theorem crossPair_uncrossLo_uncrossHi {f g : GridV} (h : gridAdj f g) :
    crossPair (uncrossLo f g) (uncrossHi f g) = s(f, g) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hm1 : min f.1 g.1 = g.1 := by omega
    have hm2 : min f.2 g.2 = g.2 := by omega
    have hl : uncrossLo f g = (g.1, g.2 + 1) := by
      rw [uncrossLo_vert h1 (Or.inl h2), hm1, hm2]
    have hh : uncrossHi f g = (g.1 + 1, g.2 + 1) := by
      rw [uncrossHi_vert h1 (Or.inl h2), hm1, hm2]
    simp only [crossPair, hl, hh,
      dualLo_horiz (p := (g.1, g.2 + 1)) (q := (g.1 + 1, g.2 + 1)) rfl (Or.inr (by omega)),
      dualHi_horiz (p := (g.1, g.2 + 1)) (q := (g.1 + 1, g.2 + 1)) rfl (Or.inr (by omega))]
    finish_pair
  · have hm1 : min f.1 g.1 = g.1 := by omega
    have hm2 : min f.2 g.2 = f.2 := by omega
    have hl : uncrossLo f g = (g.1, f.2 + 1) := by
      rw [uncrossLo_vert h1 (Or.inr h2), hm1, hm2]
    have hh : uncrossHi f g = (g.1 + 1, f.2 + 1) := by
      rw [uncrossHi_vert h1 (Or.inr h2), hm1, hm2]
    simp only [crossPair, hl, hh,
      dualLo_horiz (p := (g.1, f.2 + 1)) (q := (g.1 + 1, f.2 + 1)) rfl (Or.inr (by omega)),
      dualHi_horiz (p := (g.1, f.2 + 1)) (q := (g.1 + 1, f.2 + 1)) rfl (Or.inr (by omega))]
    finish_pair
  · have hm1 : min f.1 g.1 = g.1 := by omega
    have hm2 : min f.2 g.2 = f.2 := by omega
    have hl : uncrossLo f g = (g.1 + 1, f.2) := by
      rw [uncrossLo_horiz h1 (Or.inl h2), hm1, hm2]
    have hh : uncrossHi f g = (g.1 + 1, f.2 + 1) := by
      rw [uncrossHi_horiz h1 (Or.inl h2), hm1, hm2]
    simp only [crossPair, hl, hh,
      dualLo_vert (p := (g.1 + 1, f.2)) (q := (g.1 + 1, f.2 + 1)) rfl (Or.inr (by omega)),
      dualHi_vert (p := (g.1 + 1, f.2)) (q := (g.1 + 1, f.2 + 1)) rfl (Or.inr (by omega))]
    finish_pair
  · have hm1 : min f.1 g.1 = f.1 := by omega
    have hm2 : min f.2 g.2 = f.2 := by omega
    have hl : uncrossLo f g = (f.1 + 1, f.2) := by
      rw [uncrossLo_horiz h1 (Or.inr h2), hm1, hm2]
    have hh : uncrossHi f g = (f.1 + 1, f.2 + 1) := by
      rw [uncrossHi_horiz h1 (Or.inr h2), hm1, hm2]
    simp only [crossPair, hl, hh,
      dualLo_vert (p := (f.1 + 1, f.2)) (q := (f.1 + 1, f.2 + 1)) rfl (Or.inr (by omega)),
      dualHi_vert (p := (f.1 + 1, f.2)) (q := (f.1 + 1, f.2 + 1)) rfl (Or.inr (by omega))]
    finish_pair

/-! ## The face--dual edge equivalence -/

/-- The face--dual graph: the unit-square centres with the induced adjacency.
It is the square lattice shifted by `(1/2, 1/2)`, hence literally the same
graph. -/
abbrev gridDual : SimpleGraph GridV := gridGraph

/-- **The exact primal/dual edge correspondence.** -/
noncomputable def gridCrossEquiv : gridGraph.edgeSet ≃ gridDual.edgeSet where
  toFun := crossEdge
  invFun := uncrossEdge
  left_inv := by
    intro e
    obtain ⟨p, q, hpq, rfl⟩ : ∃ (p q : GridV) (h : gridAdj p q), e = ⟨s(p, q), h⟩ :=
      ⟨edgeFst e, edgeSnd e, edgeFst_adj_edgeSnd e, edge_eq_mk e⟩
    rw [crossEdge_apply_mk]
    refine Subtype.ext ?_
    show uncrossVal (crossPair p q) = s(p, q)
    simp only [crossPair, uncrossVal_mk]
    exact uncrossPair_dualLo_dualHi hpq
  right_inv := by
    intro e
    obtain ⟨f, g, hfg, rfl⟩ : ∃ (f g : GridV) (h : gridAdj f g), e = ⟨s(f, g), h⟩ :=
      ⟨edgeFst e, edgeSnd e, edgeFst_adj_edgeSnd e, edge_eq_mk e⟩
    rw [uncrossEdge_apply_mk]
    refine Subtype.ext ?_
    show crossVal (uncrossPair f g) = s(f, g)
    simp only [uncrossPair, crossVal_mk]
    exact crossPair_uncrossLo_uncrossHi hfg

/-- The dual graph is locally finite: every vertex has a finite neighbour set. -/
theorem finite_neighborSet (p : GridV) : (gridDual.neighborSet p).Finite := by
  have hfin : (({p.1 - 1, p.1, p.1 + 1} : Set ℤ) ×ˢ
      ({p.2 - 1, p.2, p.2 + 1} : Set ℤ)).Finite :=
    (((Set.finite_singleton (p.1 + 1)).insert p.1).insert (p.1 - 1)).prod
      (((Set.finite_singleton (p.2 + 1)).insert p.2).insert (p.2 - 1))
  refine Set.Finite.subset hfin ?_
  intro q hq
  have hq' : gridAdj p q := hq
  simp only [Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hq' with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

end FK.PlaneTopology.GridDualIncidence
