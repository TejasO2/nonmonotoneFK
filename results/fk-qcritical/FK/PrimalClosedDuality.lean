import FK.CutCrossingDuality
import FK.GridDualIncidence

/-!
# Closed-bond dual graph and the finite primal left-reachable duality

This module supplies what `FK.CutCrossingDuality` explicitly leaves open: the
**primal** half of the finite square-lattice duality, on the very same
`DVert`/`DAdj` data.

## The primal side

`ω : gridGraph.edgeSet → Bool` is an open-bond configuration of the square
lattice (the honest FK bond variable, on the genuine `gridGraph` edge type used
by `gridCrossEquiv`).  The box is the vertex rectangle `[0,k+1] × [0,n]`;
`primalGraph ω k n` is its open subgraph, and `leftReach ω k n` is the vertex set
reachable from the left wall by *open* primal paths inside the box.  `boxMem`
turns that set into a membership function `ℤ → ℤ → Bool`, with the two wall
columns extended uniformly so that the released crossing theorem applies.

## Main results

* `hCut_boxMem_closed`, `vCut_boxMem_closed` — **every cut side of the
  left-reachable set is a closed primal bond**.  This is the primal content the
  cut-graph module assumed.
* `closedGraph` — the genuine closed-bond graph on `DVert k n`: cells adjacent
  across a closed shared bond, plus the below/above exterior links.
* `closed_crossing_of_walls` — exact box wall premises (left wall inside,
  right wall outside the reachable set) give a closed-bond path below → above,
  through the released `reachable_of_cut_le`.
* `exists_open_crossing_of_no_closed_dual` and
  `exists_primal_open_walk_of_no_closed_dual` — **if the closed-bond graph has no
  below-to-above path, then the primal configuration carries an open
  left-to-right crossing.**
* `gridAdj_cellPt`, `closed_edge_crossed`, `closed_bottom_crossed`,
  `closed_top_crossed`, `closed_edge_dualOpen`, `closed_bottom_dualOpen`,
  `closed_top_dualOpen` — every step of the closed-bond graph is realised by the
  actual `gridCrossEquiv` crossing edge of a closed primal bond, and is open in
  the dual configuration `dualConfig gridCrossEquiv ω`.  `cellPt`,
  `belowPt`, `abovePt`, `belowPt_eq_iff`, `row_reachable`,
  `row_vertices_reachable`, `belowRow_infinite`, `aboveRow_infinite`,
  `belowRow_inter_neighbors_finite`, `aboveRow_inter_neighbors_finite` record
  that the two outer vertices of `DVert` stand for connected, locally finite,
  infinite exterior rows of the dual lattice, not for single dual vertices.
* `leftReach_mono`, `closedGraph_anti` — monotonicity in the open-bond
  configuration.
* `allOpen_no_closed_crossing`, `allOpen_right_reachable`,
  `allOpen_duality_instance` — the all-open configuration is a consistency
  instance: the duality hypothesis holds, and its conclusion is verified both
  through the theorem and independently along the open bottom row.
* `noAdj_allClosed`, `allClosed_right_not_reachable`,
  `allClosed_closed_crossing` — the complementary instance: in the all-closed
  configuration the closed-crossing hypothesis holds and its conclusion is
  produced in the graph with the most closed edges.
* `dualOpen_iff_closed`, `bondClosed_iff_dualOpen` — closed primal bond ↔
  `dualConfig gridCrossEquiv` open dual bond.

No `GlobalAtMostOne`, cofinal exhaustion, FK measure, or Theorem 1.11 claim is
made here; the converse implication (an open primal crossing forces the absence
of a closed dual crossing) is the plane/Jordan direction and is *not* proved.
-/

namespace FK.PlaneTopology.PrimalClosedDuality

open Finset
open FK.PlaneTopology.CutCrossing
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.Configuration

attribute [local instance] Classical.propDecidable

/-! ## 1. The primal box, its walls, and open bonds -/

/-- The vertex rectangle `[0,k+1] × [0,n]` of the primal box. -/
def inBox (k n : ℕ) (p : GridV) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ (k : ℤ) + 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ (n : ℤ)

/-- The vertices of the finite primal box. -/
abbrev BVert (k n : ℕ) : Type := {p : GridV // inBox k n p}

/-- The left wall of the box. -/
def leftWall (k n : ℕ) : Set (BVert k n) := {v | v.1.1 = 0}

/-- The right wall of the box. -/
def rightWall (k n : ℕ) : Set (BVert k n) := {v | v.1.1 = (k : ℤ) + 1}

/-- The bottom wall of the box. -/
def bottomWall (k n : ℕ) : Set (BVert k n) := {v | v.1.2 = 0}

/-- The top wall of the box. -/
def topWall (k n : ℕ) : Set (BVert k n) := {v | v.1.2 = (n : ℤ)}

/-- A primal bond is open when the corresponding edge of `ω` is open. -/
def bondOpen (ω : gridGraph.edgeSet → Bool) (p q : GridV) : Prop :=
  ∃ h : gridAdj p q, ω ⟨s(p, q), h⟩ = true

/-- A primal bond is closed when it is not open. -/
def bondClosed (ω : gridGraph.edgeSet → Bool) (p q : GridV) : Prop := ¬ bondOpen ω p q

lemma bondOpen_iff {ω : gridGraph.edgeSet → Bool} {p q : GridV} (h : gridAdj p q) :
    bondOpen ω p q ↔ ω ⟨s(p, q), h⟩ = true := by
  constructor
  · rintro ⟨h', hh⟩
    have he : (⟨s(p, q), h'⟩ : gridGraph.edgeSet) = ⟨s(p, q), h⟩ := Subtype.ext rfl
    rwa [he] at hh
  · intro hh
    exact ⟨h, hh⟩

lemma bondOpen_comm {ω : gridGraph.edgeSet → Bool} {p q : GridV} (h : bondOpen ω p q) :
    bondOpen ω q p := by
  obtain ⟨hpq, hopen⟩ := h
  refine ⟨gridAdj_symm hpq, ?_⟩
  have he : (⟨s(q, p), gridAdj_symm hpq⟩ : gridGraph.edgeSet) = ⟨s(p, q), hpq⟩ :=
    Subtype.ext Sym2.eq_swap
  rw [he, hopen]

lemma bondClosed_comm {ω : gridGraph.edgeSet → Bool} {p q : GridV} (h : bondClosed ω p q) :
    bondClosed ω q p := fun hop => h (bondOpen_comm hop)

lemma bondClosed_iff {ω : gridGraph.edgeSet → Bool} {p q : GridV} (h : gridAdj p q) :
    bondClosed ω p q ↔ ω ⟨s(p, q), h⟩ = false := by
  unfold bondClosed
  rw [bondOpen_iff h]
  constructor
  · intro hc
    cases hv : ω ⟨s(p, q), h⟩ with
    | false => rfl
    | true => exact absurd hv hc
  · intro hv ho
    rw [ho] at hv
    exact absurd hv (by simp)

/-- The primal open subgraph of the box. -/
noncomputable def primalGraph (ω : gridGraph.edgeSet → Bool) (k n : ℕ) :
    SimpleGraph (BVert k n) where
  Adj u v := bondOpen ω u.1 v.1
  symm := ⟨fun _ _ h => bondOpen_comm h⟩
  loopless := ⟨fun u h => by
    obtain ⟨hg, -⟩ := h
    exact gridAdj_irrefl u.1 hg⟩

/-- The box vertices reachable from the left wall by open primal paths. -/
def leftReach (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : Set (BVert k n) :=
  {v | ∃ u : BVert k n, u ∈ leftWall k n ∧ (primalGraph ω k n).Reachable u v}

lemma leftReach_of_leftWall {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {v : BVert k n}
    (hv : v ∈ leftWall k n) : v ∈ leftReach ω k n :=
  ⟨v, hv, SimpleGraph.Reachable.refl v⟩

lemma leftReach_step {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {u v : BVert k n}
    (h : (primalGraph ω k n).Adj u v) (hu : u ∈ leftReach ω k n) : v ∈ leftReach ω k n := by
  obtain ⟨w, hw, hwu⟩ := hu
  exact ⟨w, hw, hwu.trans ⟨SimpleGraph.Walk.cons h SimpleGraph.Walk.nil⟩⟩

/-- The left-reachable set is a union of primal open components: crossing an open
bond does not leave it. -/
theorem leftReach_transfer {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {u v : BVert k n}
    (h : (primalGraph ω k n).Adj u v) : u ∈ leftReach ω k n ↔ v ∈ leftReach ω k n :=
  ⟨leftReach_step h, fun hv => leftReach_step (SimpleGraph.Adj.symm h) hv⟩

/-! ## 2. The membership function of the left-reachable set -/

/-- The characteristic function of the left-reachable set, extended to all of
`ℤ × ℤ`: the left column is declared uniformly inside, so the released crossing
theorem (which asks for the whole column) applies without extra hypotheses. -/
noncomputable def boxMem (ω : gridGraph.edgeSet → Bool) (k n : ℕ) (i j : ℤ) : Bool := by
  classical
  exact if h : inBox k n (i, j) then
      (if (⟨(i, j), h⟩ : BVert k n) ∈ leftReach ω k n then true else false)
    else if i = 0 then true else false

lemma boxMem_of_inBox {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {i j : ℤ}
    (h : inBox k n (i, j)) :
    boxMem ω k n i j
      = (if (⟨(i, j), h⟩ : BVert k n) ∈ leftReach ω k n then true else false) := by
  simp only [boxMem, dite_eq_left h]

/-- The left wall is inside the left-reachable set. -/
lemma boxMem_left {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {j : ℤ}
    (h0 : 0 ≤ j) (hj : j ≤ (n : ℤ)) : boxMem ω k n 0 j = true := by
  have hbox : inBox k n ((0 : ℤ), j) := ⟨le_refl 0, by positivity, h0, hj⟩
  rw [boxMem_of_inBox hbox]
  have hmem : (⟨((0 : ℤ), j), hbox⟩ : BVert k n) ∈ leftReach ω k n :=
    leftReach_of_leftWall (by simp [leftWall])
  rw [ite_eq_left hmem]

/-- A right-wall vertex outside the left-reachable set. -/
lemma boxMem_right {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {j : ℤ}
    (h0 : 0 ≤ j) (hj : j ≤ (n : ℤ))
    (hout : ∀ v : BVert k n, v ∈ rightWall k n → v ∉ leftReach ω k n) :
    boxMem ω k n ((k : ℤ) + 1) j = false := by
  have hbox : inBox k n (((k : ℤ) + 1), j) := ⟨by positivity, le_refl _, h0, hj⟩
  rw [boxMem_of_inBox hbox]
  have hmem : (⟨(((k : ℤ) + 1), j), hbox⟩ : BVert k n) ∉ leftReach ω k n :=
    hout _ (by simp [rightWall])
  rw [ite_eq_right hmem]

/-- The whole left column is inside, not just the box part. -/
lemma boxMem_left_col {ω : gridGraph.edgeSet → Bool} {k n : ℕ} (j : ℤ) :
    boxMem ω k n 0 j = true := by
  by_cases h : inBox k n ((0 : ℤ), j)
  · exact boxMem_left h.2.2.1 h.2.2.2
  · simp only [boxMem, dite_eq_right h, ite_true]

/-- The whole right column is outside, not just the box part. -/
lemma boxMem_right_col {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    (hout : ∀ v : BVert k n, v ∈ rightWall k n → v ∉ leftReach ω k n) (j : ℤ) :
    boxMem ω k n ((k : ℤ) + 1) j = false := by
  by_cases h : inBox k n (((k : ℤ) + 1), j)
  · exact boxMem_right h.2.2.1 h.2.2.2 hout
  · have hne : ((k : ℤ) + 1) ≠ 0 := by positivity
    simp only [boxMem, dite_eq_right h, ite_eq_right hne]

/-! ## 3. Cut sides of the left-reachable set are closed bonds -/

/-- **A horizontal cut bond of the left-reachable set is a closed primal bond.**
If exactly one endpoint of the bond `(i,j)–(i+1,j)` lies in the left-reachable
set, the bond cannot be open: crossing it would carry reachability along. -/
theorem hCut_boxMem_closed {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {i j : ℤ}
    (hi0 : 0 ≤ i) (hi : i ≤ (k : ℤ)) (hj0 : 0 ≤ j) (hj : j ≤ (n : ℤ))
    (hcut : hCut (boxMem ω k n) i j = true) : bondClosed ω (i, j) (i + 1, j) := by
  intro hopen
  have h1 : inBox k n (i, j) := ⟨hi0, by omega, hj0, hj⟩
  have h2 : inBox k n (i + 1, j) := ⟨by omega, by omega, hj0, hj⟩
  have hne : boxMem ω k n i j ≠ boxMem ω k n (i + 1) j := bne_iff_ne.mp hcut
  rw [boxMem_of_inBox h1, boxMem_of_inBox h2] at hne
  have hadj : (primalGraph ω k n).Adj (⟨(i, j), h1⟩ : BVert k n) ⟨(i + 1, j), h2⟩ := hopen
  have hiff := leftReach_transfer hadj
  by_cases hA : (⟨(i, j), h1⟩ : BVert k n) ∈ leftReach ω k n
  · have hB : (⟨(i + 1, j), h2⟩ : BVert k n) ∈ leftReach ω k n := hiff.mp hA
    rw [ite_eq_left hA, ite_eq_left hB] at hne
    exact absurd rfl hne
  · by_cases hB : (⟨(i + 1, j), h2⟩ : BVert k n) ∈ leftReach ω k n
    · exact hA (hiff.mpr hB)
    · rw [ite_eq_right hA, ite_eq_right hB] at hne
      exact absurd rfl hne

/-- **A vertical cut bond of the left-reachable set is a closed primal bond.** -/
theorem vCut_boxMem_closed {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {i j : ℤ}
    (hi0 : 0 ≤ i) (hi : i ≤ (k : ℤ) + 1) (hj0 : 0 ≤ j) (hj : j + 1 ≤ (n : ℤ))
    (hcut : vCut (boxMem ω k n) i j = true) : bondClosed ω (i, j) (i, j + 1) := by
  intro hopen
  have h1 : inBox k n (i, j) := ⟨hi0, hi, hj0, by omega⟩
  have h2 : inBox k n (i, j + 1) := ⟨hi0, hi, by omega, hj⟩
  have hne : boxMem ω k n i j ≠ boxMem ω k n i (j + 1) := bne_iff_ne.mp hcut
  rw [boxMem_of_inBox h1, boxMem_of_inBox h2] at hne
  have hadj : (primalGraph ω k n).Adj (⟨(i, j), h1⟩ : BVert k n) ⟨(i, j + 1), h2⟩ := hopen
  have hiff := leftReach_transfer hadj
  by_cases hA : (⟨(i, j), h1⟩ : BVert k n) ∈ leftReach ω k n
  · have hB : (⟨(i, j + 1), h2⟩ : BVert k n) ∈ leftReach ω k n := hiff.mp hA
    rw [ite_eq_left hA, ite_eq_left hB] at hne
    exact absurd rfl hne
  · by_cases hB : (⟨(i, j + 1), h2⟩ : BVert k n) ∈ leftReach ω k n
    · exact hA (hiff.mpr hB)
    · rw [ite_eq_right hA, ite_eq_right hB] at hne
      exact absurd rfl hne

/-! ## 4. The closed-bond graph on `DVert` -/

/-- Two box cells share a **closed** bond.  This is `CellCut` with the
membership-change condition replaced by the primal closedness of the shared
bond; the bond itself is the same bond, at the same coordinates. -/
def CellClosed (ω : gridGraph.edgeSet → Bool) (i j i' j' : ℤ) : Prop :=
  (j' = j ∧ (i' = i + 1 ∨ i = i' + 1) ∧
      bondClosed ω (min i i' + 1, j) (min i i' + 1, j + 1)) ∨
    (i' = i ∧ (j' = j + 1 ∨ j = j' + 1) ∧
      bondClosed ω (i, min j j' + 1) (i + 1, min j j' + 1))

lemma CellClosed_comm {ω : gridGraph.edgeSet → Bool} {i j i' j' : ℤ}
    (h : CellClosed ω i j i' j') : CellClosed ω i' j' i j := by
  unfold CellClosed at *
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl ⟨h1.symm, h2.symm, ?_⟩
    subst h1; rw [min_comm]; exact h3
  · refine Or.inr ⟨h1.symm, h2.symm, ?_⟩
    subst h1; rw [min_comm]; exact h3

/-- Adjacency of the closed-bond graph: cells adjacent across a closed shared
bond, the below/above vertices adjacent to the bottom/top row across a closed
bond. -/
def DClosed (ω : gridGraph.edgeSet → Bool) (k n : ℕ) : DVert k n → DVert k n → Prop
  | Sum.inl c, Sum.inl d =>
      CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ)
  | Sum.inl c, Sum.inr s =>
      (s = 0 ∧ ((c.2 : ℕ) : ℤ) = 0 ∧
        bondClosed ω (((c.1 : ℕ) : ℤ), 0) (((c.1 : ℕ) : ℤ) + 1, 0)) ∨
      (s = 1 ∧ ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧
        bondClosed ω (((c.1 : ℕ) : ℤ), (n : ℤ)) (((c.1 : ℕ) : ℤ) + 1, (n : ℤ)))
  | Sum.inr s, Sum.inl c =>
      (s = 0 ∧ ((c.2 : ℕ) : ℤ) = 0 ∧
        bondClosed ω (((c.1 : ℕ) : ℤ), 0) (((c.1 : ℕ) : ℤ) + 1, 0)) ∨
      (s = 1 ∧ ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧
        bondClosed ω (((c.1 : ℕ) : ℤ), (n : ℤ)) (((c.1 : ℕ) : ℤ) + 1, (n : ℤ)))
  | Sum.inr _, Sum.inr _ => False

lemma DClosed_symm {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {x y : DVert k n}
    (h : DClosed ω k n x y) : DClosed ω k n y x := by
  obtain (c | s) := x <;> obtain (d | t) := y <;> simp only [DClosed] at *
  all_goals first
    | exact CellClosed_comm h
    | exact h

lemma DClosed_irrefl {ω : gridGraph.edgeSet → Bool} {k n : ℕ} {x : DVert k n} :
    ¬ DClosed ω k n x x := by
  obtain (c | s) := x
  · simp only [DClosed, CellClosed]
    rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> omega
  · simp [DClosed]

/-- The closed-bond graph of the box: the dual graph of the primal-**closed**
bonds, on the same `DVert` type as `cutGraph`. -/
noncomputable def closedGraph (ω : gridGraph.edgeSet → Bool) (k n : ℕ) :
    SimpleGraph (DVert k n) where
  Adj := DClosed ω k n
  symm := ⟨fun _ _ h => DClosed_symm h⟩
  loopless := ⟨fun _ h => DClosed_irrefl h⟩

/-- Bounds on the cell coordinates, in the form used by `omega`. -/
lemma cell_fst_le {k n : ℕ} (c : Fin (k + 1) × Fin n) : ((c.1 : ℕ) : ℤ) ≤ (k : ℤ) := by
  have := c.1.isLt; omega

lemma cell_snd_lt {k n : ℕ} (c : Fin (k + 1) × Fin n) : ((c.2 : ℕ) : ℤ) + 1 ≤ (n : ℤ) := by
  have := c.2.isLt; omega

/-- **Inclusion of the cut graph in the closed-bond graph.**  Every edge of the
released `cutGraph` for the left-reachable membership function is an edge of the
closed-bond graph: each cut side is a closed bond. -/
theorem DAdj_le_closed (ω : gridGraph.edgeSet → Bool) (k n : ℕ) :
    ∀ x y : DVert k n, DAdj (boxMem ω k n) k n x y → (closedGraph ω k n).Adj x y := by
  intro x y h
  obtain (c | s) := x
  · obtain (d | t) := y
    · -- cell next to cell
      have hc1 := cell_fst_le c
      have hc2 := cell_snd_lt c
      have hd1 := cell_fst_le d
      have hd2 := cell_snd_lt d
      have hmin : min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ≤ (k : ℤ) :=
        le_trans (min_le_left _ _) hc1
      show CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ)
      have hh : CellCut (boxMem ω k n) ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ)
          ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := h
      unfold CellCut at hh
      unfold CellClosed
      rcases hh with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · refine Or.inl ⟨h1, h2, ?_⟩
        exact vCut_boxMem_closed (ω := ω)
          (i := min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) + 1) (j := ((c.2 : ℕ) : ℤ))
          (by omega) (by omega) (by omega) (by omega) h3
      · refine Or.inr ⟨h1, h2, ?_⟩
        have hmin2 : min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1 ≤ (n : ℤ) := by
          have := min_le_left ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ); omega
        exact hCut_boxMem_closed (ω := ω)
          (i := ((c.1 : ℕ) : ℤ)) (j := min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1)
          (by omega) (by omega) (by omega) hmin2 h3
    · -- cell next to the outside, below or above
      have hc1 := cell_fst_le c
      have hh : (t = 0 ∧ ((c.2 : ℕ) : ℤ) = 0 ∧
          hCut (boxMem ω k n) ((c.1 : ℕ) : ℤ) 0 = true) ∨
          (t = 1 ∧ ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧
          hCut (boxMem ω k n) ((c.1 : ℕ) : ℤ) (n : ℤ) = true) := h
      show (t = 0 ∧ ((c.2 : ℕ) : ℤ) = 0 ∧
          bondClosed ω (((c.1 : ℕ) : ℤ), 0) (((c.1 : ℕ) : ℤ) + 1, 0)) ∨
          (t = 1 ∧ ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧
          bondClosed ω (((c.1 : ℕ) : ℤ), (n : ℤ)) (((c.1 : ℕ) : ℤ) + 1, (n : ℤ)))
      rcases hh with ⟨rfl, hj, hb⟩ | ⟨rfl, hj, hb⟩
      · exact Or.inl ⟨rfl, hj, hCut_boxMem_closed (by omega) hc1 (le_refl 0) (by omega) hb⟩
      · exact Or.inr ⟨rfl, hj, hCut_boxMem_closed (by omega) hc1 (by omega) (le_refl _) hb⟩
  · obtain (d | t) := y
    · -- outside next to a cell
      have hd1 := cell_fst_le d
      have hh : (s = 0 ∧ ((d.2 : ℕ) : ℤ) = 0 ∧
          hCut (boxMem ω k n) ((d.1 : ℕ) : ℤ) 0 = true) ∨
          (s = 1 ∧ ((d.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧
          hCut (boxMem ω k n) ((d.1 : ℕ) : ℤ) (n : ℤ) = true) := h
      show (s = 0 ∧ ((d.2 : ℕ) : ℤ) = 0 ∧
          bondClosed ω (((d.1 : ℕ) : ℤ), 0) (((d.1 : ℕ) : ℤ) + 1, 0)) ∨
          (s = 1 ∧ ((d.2 : ℕ) : ℤ) = (n : ℤ) - 1 ∧
          bondClosed ω (((d.1 : ℕ) : ℤ), (n : ℤ)) (((d.1 : ℕ) : ℤ) + 1, (n : ℤ)))
      rcases hh with ⟨rfl, hj, hb⟩ | ⟨rfl, hj, hb⟩
      · exact Or.inl ⟨rfl, hj, hCut_boxMem_closed (by omega) hd1 (le_refl 0) (by omega) hb⟩
      · exact Or.inr ⟨rfl, hj, hCut_boxMem_closed (by omega) hd1 (by omega) (le_refl _) hb⟩
    · -- outside next to outside
      have hh : False := h
      exact hh.elim

/-! ## 5. Closed dual crossing from exact wall premises -/

/-- **Closed-bond crossing.**  If no vertex of the right wall is left-reachable
(the exact wall premise), the closed bonds of the primal configuration contain a
path in the closed-bond graph from below the box to above it.

The left wall needs no hypothesis: every left-wall vertex is left-reachable by
the empty open path (`leftReach_of_leftWall`). -/
theorem closed_crossing_of_walls {ω : gridGraph.edgeSet → Bool} {k n : ℕ} (hn : 0 < n)
    (hout : ∀ v : BVert k n, v ∈ rightWall k n → v ∉ leftReach ω k n) :
    (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1) :=
  reachable_of_cut_le (a := boxMem ω k n) hn (fun j => boxMem_left_col j)
    (fun j => boxMem_right_col hout j) (closedGraph ω k n)
    (fun x y hxy => DAdj_le_closed ω k n x y hxy)

/-- **Finite primal/closed-dual duality.**  If the closed-bond graph of the box
has no path from below to above, then the primal open configuration has an open
path from the left wall to the right wall inside the box. -/
theorem exists_open_crossing_of_no_closed_dual {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    (hn : 0 < n) (hno : ¬ (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)) :
    ∃ v : BVert k n, v ∈ rightWall k n ∧ v ∈ leftReach ω k n := by
  by_contra hcon
  have hout : ∀ v : BVert k n, v ∈ rightWall k n → v ∉ leftReach ω k n := by
    intro v hv hmem
    exact hcon ⟨v, hv, hmem⟩
  exact hno (closed_crossing_of_walls hn hout)

/-- The same statement in walk form: an open primal walk from the left wall to
the right wall inside the box. -/
theorem exists_primal_open_walk_of_no_closed_dual {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    (hn : 0 < n) (hno : ¬ (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)) :
    ∃ u v : BVert k n,
      u ∈ leftWall k n ∧ v ∈ rightWall k n ∧ (primalGraph ω k n).Reachable u v := by
  obtain ⟨v, hv, u, hu, hwalk⟩ := exists_open_crossing_of_no_closed_dual hn hno
  exact ⟨u, v, hu, hv, hwalk⟩



/-! ## 6. Plane realisation: every closed link is a genuine crossing edge -/

/-- The dual lattice point labelling the centre of a box cell. -/
def cellPt {k n : ℕ} (c : Fin (k + 1) × Fin n) : GridV :=
  (((c.1 : ℕ) : ℤ), ((c.2 : ℕ) : ℤ))

/-- The dual lattice point of the exterior row below the box, attached to column
`c.1`. -/
def belowPt {k n : ℕ} (c : Fin (k + 1) × Fin n) : GridV := (((c.1 : ℕ) : ℤ), -1)

/-- The dual lattice point of the exterior row above the box, attached to column
`c.1`. -/
def abovePt {k n : ℕ} (c : Fin (k + 1) × Fin n) : GridV := (((c.1 : ℕ) : ℤ), (n : ℤ))

lemma cellPt_injective {k n : ℕ} : Function.Injective (@cellPt k n) := by
  intro c d h
  have h1 : ((c.1 : ℕ) : ℤ) = ((d.1 : ℕ) : ℤ) := congrArg Prod.fst h
  have h2 : ((c.2 : ℕ) : ℤ) = ((d.2 : ℕ) : ℤ) := congrArg Prod.snd h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The unoriented dual edge crossed by a primal bond, as a value. -/
lemma crossEdge_val {p q : GridV} (h : gridAdj p q) :
    (crossEdge ⟨s(p, q), h⟩).val = s(dualLo p q, dualHi p q) := by
  rw [crossEdge_apply]
  rfl

/-- A vertical primal bond crosses the horizontal dual edge between the two cells
it separates. -/
theorem crossEdge_vert_bond {i j : ℤ} (h : gridAdj (i, j) (i, j + 1)) :
    (crossEdge ⟨s((i, j), (i, j + 1)), h⟩).val = s((i - 1, j), (i, j)) := by
  rw [crossEdge_val, dualLo_vert (rfl : (i : ℤ) = i) (Or.inr rfl),
    dualHi_vert (rfl : (i : ℤ) = i) (Or.inr rfl)]
  simp only [min_self, min_eq_left (by omega : j ≤ j + 1)]

/-- A horizontal primal bond crosses the vertical dual edge between the two cells
it separates. -/
theorem crossEdge_horiz_bond {i j : ℤ} (h : gridAdj (i, j) (i + 1, j)) :
    (crossEdge ⟨s((i, j), (i + 1, j)), h⟩).val = s((i, j - 1), (i, j)) := by
  rw [crossEdge_val, dualLo_horiz (rfl : (j : ℤ) = j) (Or.inr rfl),
    dualHi_horiz (rfl : (j : ℤ) = j) (Or.inr rfl)]
  simp only [min_eq_left (by omega : i ≤ i + 1)]

/-- Cell-to-cell closed adjacency is a genuine unit edge of the dual lattice. -/
theorem gridAdj_cellPt {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c d : Fin (k + 1) × Fin n}
    (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inl d)) : gridAdj (cellPt c) (cellPt d) := by
  have hc1 := cell_fst_le c
  have hc2 := cell_snd_lt c
  have hd1 := cell_fst_le d
  have hd2 := cell_snd_lt d
  have h' : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := h
  unfold CellClosed at h'
  simp only [cellPt]
  rcases h' with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · rcases h2 with h2 | h2
    · exact Or.inr ⟨by omega, Or.inr (by omega)⟩
    · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
  · rcases h2 with h2 | h2
    · exact Or.inl ⟨by omega, Or.inr (by omega)⟩
    · exact Or.inl ⟨by omega, Or.inl (by omega)⟩

/-- **Plane realisation of a cell-to-cell step.**  A closed adjacency between two
cells is crossed by the actual `gridCrossEquiv` dual edge joining their centres,
and the crossed primal bond is closed. -/
theorem closed_edge_crossed {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c d : Fin (k + 1) × Fin n}
    (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inl d)) :
    ∃ (p q : GridV) (hpq : gridAdj p q), ω ⟨s(p, q), hpq⟩ = false ∧
      (crossEdge ⟨s(p, q), hpq⟩).val = s(cellPt c, cellPt d) := by
  have h' : CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := h
  unfold CellClosed at h'
  rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hb : gridAdj (min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) + 1, ((c.2 : ℕ) : ℤ))
        (min ((c.1 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) + 1, ((c.2 : ℕ) : ℤ) + 1) :=
      Or.inl ⟨rfl, Or.inr rfl⟩
    refine ⟨_, _, hb, (bondClosed_iff hb).mp h3, ?_⟩
    simp only [cellPt]
    rw [crossEdge_vert_bond hb]
    rcases h2 with h2 | h2
    · rw [h2, h1, min_eq_left (by omega : ((c.1 : ℕ) : ℤ) ≤ ((c.1 : ℕ) : ℤ) + 1)]
      rw [show ((c.1 : ℕ) : ℤ) + 1 - 1 = ((c.1 : ℕ) : ℤ) by ring]
    · rw [h2, h1, min_eq_right (by omega : ((d.1 : ℕ) : ℤ) ≤ ((d.1 : ℕ) : ℤ) + 1)]
      rw [show ((d.1 : ℕ) : ℤ) + 1 - 1 = ((d.1 : ℕ) : ℤ) by ring]
      exact Sym2.eq_swap
  · have hb : gridAdj (((c.1 : ℕ) : ℤ), min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1)
        (((c.1 : ℕ) : ℤ) + 1, min ((c.2 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) + 1) :=
      Or.inr ⟨rfl, Or.inr rfl⟩
    refine ⟨_, _, hb, (bondClosed_iff hb).mp h3, ?_⟩
    simp only [cellPt]
    rw [crossEdge_horiz_bond hb]
    rcases h2 with h2 | h2
    · rw [h2, h1, min_eq_left (by omega : ((c.2 : ℕ) : ℤ) ≤ ((c.2 : ℕ) : ℤ) + 1)]
      rw [show ((c.2 : ℕ) : ℤ) + 1 - 1 = ((c.2 : ℕ) : ℤ) by ring]
    · rw [h2, h1, min_eq_right (by omega : ((d.2 : ℕ) : ℤ) ≤ ((d.2 : ℕ) : ℤ) + 1)]
      rw [show ((d.2 : ℕ) : ℤ) + 1 - 1 = ((d.2 : ℕ) : ℤ) by ring]
      exact Sym2.eq_swap

/-- **Plane realisation of the below link.**  The edge from a bottom-row cell to
the exterior vertex below the box is the actual crossing edge of the bottom bond,
joining the cell centre to the exterior dual vertex one row below. -/
theorem closed_bottom_crossed {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c : Fin (k + 1) × Fin n} (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inr 0)) :
    ∃ (hb : gridAdj (((c.1 : ℕ) : ℤ), 0) ((((c.1 : ℕ) : ℤ)) + 1, 0)),
      ω ⟨s((((c.1 : ℕ) : ℤ), 0), ((((c.1 : ℕ) : ℤ)) + 1, 0)), hb⟩ = false ∧
        (crossEdge ⟨s((((c.1 : ℕ) : ℤ), 0), ((((c.1 : ℕ) : ℤ)) + 1, 0)), hb⟩).val
            = s(belowPt c, cellPt c) ∧
          gridAdj (belowPt c) (cellPt c) := by
  have hh : DClosed ω k n (Sum.inl c) (Sum.inr 0) := h
  unfold DClosed at hh
  have hb : gridAdj (((c.1 : ℕ) : ℤ), 0) ((((c.1 : ℕ) : ℤ)) + 1, 0) :=
    Or.inr ⟨rfl, Or.inr rfl⟩
  rcases hh with ⟨-, hc0, hbc⟩ | ⟨h10, -, -⟩
  · refine ⟨hb, (bondClosed_iff hb).mp hbc, ?_, ?_⟩
    · simp only [belowPt, cellPt]
      rw [crossEdge_horiz_bond hb, hc0]
      norm_num
    · simp only [belowPt, cellPt, hc0]
      exact Or.inl ⟨rfl, Or.inr (by norm_num)⟩
  · exact absurd h10 (by norm_num)

/-- **Plane realisation of the above link.** -/
theorem closed_top_crossed {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c : Fin (k + 1) × Fin n} (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inr 1)) :
    ∃ (hb : gridAdj (((c.1 : ℕ) : ℤ), (n : ℤ)) ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ))),
      ω ⟨s((((c.1 : ℕ) : ℤ), (n : ℤ)), ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ))), hb⟩ = false ∧
        (crossEdge ⟨s((((c.1 : ℕ) : ℤ), (n : ℤ)), ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ))), hb⟩).val
            = s(cellPt c, abovePt c) ∧
          gridAdj (cellPt c) (abovePt c) := by
  have hh : DClosed ω k n (Sum.inl c) (Sum.inr 1) := h
  unfold DClosed at hh
  have hb : gridAdj (((c.1 : ℕ) : ℤ), (n : ℤ)) ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ)) :=
    Or.inr ⟨rfl, Or.inr rfl⟩
  rcases hh with ⟨h01, -, -⟩ | ⟨-, hc1, hbc⟩
  · exact absurd h01 (by norm_num)
  · refine ⟨hb, (bondClosed_iff hb).mp hbc, ?_, ?_⟩
    · simp only [abovePt, cellPt]
      rw [crossEdge_horiz_bond hb, hc1]
    · simp only [abovePt, cellPt, hc1]
      exact Or.inl ⟨rfl, Or.inr (by norm_num)⟩

/-! ## 7. The exterior rows are infinite connected dual regions -/

/-- The dual row of unit faces below the box. -/
def belowRow : Set GridV := {p | p.2 = -1}

/-- The dual row of unit faces above the box. -/
def aboveRow (n : ℕ) : Set GridV := {p | p.2 = (n : ℤ)}

/-- A dual row is connected: consecutive row vertices are dual-adjacent. -/
theorem row_reachable (j : ℤ) (m : ℕ) :
    gridGraph.Reachable ((0 : ℤ), j) ((m : ℤ), j) := by
  induction m with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
      have hstep : gridGraph.Adj ((m : ℤ), j) (((m : ℤ) + 1), j) := Or.inr ⟨rfl, Or.inr rfl⟩
      have hcast : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      exact ih.trans ⟨SimpleGraph.Walk.cons hstep SimpleGraph.Walk.nil⟩

theorem row_vertices_reachable (j : ℤ) (a b : ℕ) :
    gridGraph.Reachable ((a : ℤ), j) ((b : ℤ), j) :=
  (row_reachable j a).symm.trans (row_reachable j b)

theorem belowRow_infinite : belowRow.Infinite := by
  have hfin : (Set.range (fun m : ℕ => (((m : ℤ)), (-1 : ℤ)) : ℕ → GridV)).Infinite := by
    refine Set.infinite_range_of_injective ?_
    intro m m' h
    have h1 : ((m : ℤ)) = ((m' : ℤ)) := congrArg Prod.fst h
    omega
  refine Set.Infinite.mono ?_ hfin
  rintro p ⟨m, rfl⟩
  simp [belowRow]

theorem aboveRow_infinite (n : ℕ) : (aboveRow n).Infinite := by
  have hfin : (Set.range (fun m : ℕ => (((m : ℤ)), ((n : ℤ))) : ℕ → GridV)).Infinite := by
    refine Set.infinite_range_of_injective ?_
    intro m m' h
    have h1 : ((m : ℤ)) = ((m' : ℤ)) := congrArg Prod.fst h
    omega
  refine Set.Infinite.mono ?_ hfin
  rintro p ⟨m, rfl⟩
  simp [aboveRow]

/-! ## 8. The closed-bond graph is the dual-open bond graph -/

/-- The dual edge crossed by a primal bond is open in the dual configuration
`dualConfig gridCrossEquiv ω` exactly when the primal bond is closed. -/
theorem dualOpen_iff_closed (ω : gridGraph.edgeSet → Bool) (e : gridGraph.edgeSet) :
    dualConfig gridCrossEquiv ω (crossEdge e) = true ↔ ω e = false := by
  have hinv : gridCrossEquiv.symm (crossEdge e) = e := Equiv.left_inv gridCrossEquiv e
  have hval : dualConfig gridCrossEquiv ω (crossEdge e) = !(ω e) := by
    simp only [dualConfig, hinv]
  rw [hval]
  cases h : ω e <;> simp

/-- Version for a specific bond, with the crossed dual edge written out. -/
theorem bondClosed_iff_dualOpen {ω : gridGraph.edgeSet → Bool} {p q : GridV}
    (h : gridAdj p q) :
    bondClosed ω p q ↔ dualConfig gridCrossEquiv ω (crossEdge ⟨s(p, q), h⟩) = true :=
  (bondClosed_iff h).trans (dualOpen_iff_closed ω ⟨s(p, q), h⟩).symm

/-! ## 9. Monotonicity in the open-bond configuration -/

lemma bondOpen_mono {ω ω' : gridGraph.edgeSet → Bool}
    (h : ∀ e, ω e = true → ω' e = true) {p q : GridV} (hopen : bondOpen ω p q) :
    bondOpen ω' p q := by
  obtain ⟨hpq, hv⟩ := hopen
  exact ⟨hpq, h _ hv⟩

lemma bondClosed_anti {ω ω' : gridGraph.edgeSet → Bool}
    (h : ∀ e, ω e = true → ω' e = true) {p q : GridV} (hc : bondClosed ω' p q) :
    bondClosed ω p q :=
  fun hop => hc (bondOpen_mono h hop)

/-- Adding open bonds only enlarges the left-reachable set. -/
theorem leftReach_mono {ω ω' : gridGraph.edgeSet → Bool}
    (h : ∀ e, ω e = true → ω' e = true) {k n : ℕ} :
    leftReach ω k n ⊆ leftReach ω' k n := by
  rintro v ⟨u, hu, hwalk⟩
  exact ⟨u, hu, SimpleGraph.Reachable.map
    ⟨id, fun {x y} hxy => bondOpen_mono h hxy⟩ hwalk⟩

/-- Adding open bonds only removes closed-bond adjacencies. -/
theorem closedGraph_anti {ω ω' : gridGraph.edgeSet → Bool}
    (h : ∀ e, ω e = true → ω' e = true) {k n : ℕ} :
    ∀ x y, (closedGraph ω' k n).Adj x y → (closedGraph ω k n).Adj x y := by
  intro x y hxy
  obtain (c | s) := x <;> obtain (d | t) := y
  · have h' : CellClosed ω' ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ)
        ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := hxy
    show CellClosed ω ((c.1 : ℕ) : ℤ) ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ)
    unfold CellClosed at h' ⊢
    rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, bondClosed_anti h h3⟩
    · exact Or.inr ⟨h1, h2, bondClosed_anti h h3⟩
  · have h' : DClosed ω' k n (Sum.inl c) (Sum.inr t) := hxy
    show DClosed ω k n (Sum.inl c) (Sum.inr t)
    unfold DClosed at h' ⊢
    rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, bondClosed_anti h h3⟩
    · exact Or.inr ⟨h1, h2, bondClosed_anti h h3⟩
  · have h' : DClosed ω' k n (Sum.inr s) (Sum.inl d) := hxy
    show DClosed ω k n (Sum.inr s) (Sum.inl d)
    unfold DClosed at h' ⊢
    rcases h' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, bondClosed_anti h h3⟩
    · exact Or.inr ⟨h1, h2, bondClosed_anti h h3⟩
  · exact hxy

/-! ## 10. The all-open configuration: a consistency instance

The hypothesis of the duality theorem is satisfiable, and its conclusion is
true, for the all-open configuration: there is no closed bond at all, and the
bottom row of the box is an open primal crossing.  This is an independent
verification of the conclusion, not merely an application of the theorem. -/

/-- A closedness statement of the all-open configuration forces the two vertices
not to be lattice neighbours. -/
theorem not_gridAdj_of_bondClosed_allOpen {p q : GridV}
    (hc : bondClosed (fun _ : gridGraph.edgeSet => true) p q) : ¬ gridAdj p q :=
  fun h => hc ⟨h, rfl⟩

/-- The closed-bond graph of the all-open configuration has no edge. -/
theorem closedGraph_allOpen_no_adj (k n : ℕ) :
    ∀ x y : DVert k n, ¬ (closedGraph (fun _ : gridGraph.edgeSet => true) k n).Adj x y := by
  intro x y hxy
  obtain (c | s) := x <;> obtain (d | t) := y
  · have h' : CellClosed (fun _ : gridGraph.edgeSet => true) ((c.1 : ℕ) : ℤ)
        ((c.2 : ℕ) : ℤ) ((d.1 : ℕ) : ℤ) ((d.2 : ℕ) : ℤ) := hxy
    unfold CellClosed at h'
    rcases h' with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact not_gridAdj_of_bondClosed_allOpen h3 (Or.inl ⟨rfl, Or.inr rfl⟩)
    · exact not_gridAdj_of_bondClosed_allOpen h3 (Or.inr ⟨rfl, Or.inr rfl⟩)
  · have h' : DClosed (fun _ : gridGraph.edgeSet => true) k n (Sum.inl c) (Sum.inr t) := hxy
    unfold DClosed at h'
    rcases h' with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact not_gridAdj_of_bondClosed_allOpen h3 (Or.inr ⟨rfl, Or.inr rfl⟩)
    · exact not_gridAdj_of_bondClosed_allOpen h3 (Or.inr ⟨rfl, Or.inr rfl⟩)
  · have h' : DClosed (fun _ : gridGraph.edgeSet => true) k n (Sum.inr s) (Sum.inl d) := hxy
    unfold DClosed at h'
    rcases h' with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
    · exact not_gridAdj_of_bondClosed_allOpen h3 (Or.inr ⟨rfl, Or.inr rfl⟩)
    · exact not_gridAdj_of_bondClosed_allOpen h3 (Or.inr ⟨rfl, Or.inr rfl⟩)
  · exact hxy

/-- A graph without edges has no nontrivial reachability. -/
theorem eq_of_reachable_of_no_adj {V : Type*} {G : SimpleGraph V}
    (hempty : ∀ x y, ¬ G.Adj x y) {u v : V} (h : G.Reachable u v) : u = v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hxy _ _ => exact absurd hxy (hempty _ _)

/-- Hence the all-open configuration has no closed dual crossing. -/
theorem allOpen_no_closed_crossing {k n : ℕ} :
    ¬ (closedGraph (fun _ : gridGraph.edgeSet => true) k n).Reachable (Sum.inr 0) (Sum.inr 1) := by
  intro h
  have heq : (Sum.inr 0 : DVert k n) = Sum.inr 1 :=
    eq_of_reachable_of_no_adj (closedGraph_allOpen_no_adj k n) h
  exact absurd heq (by simp)

/-- Bounds helper for bottom-row box vertices. -/
lemma inBox_bottom {k n : ℕ} (m : ℕ) (hm : (m : ℤ) ≤ (k : ℤ) + 1) :
    inBox k n ((m : ℤ), 0) :=
  ⟨Int.natCast_nonneg m, hm, le_refl 0, Int.natCast_nonneg n⟩

/-- **Independent verification of the conclusion.**  In the all-open
configuration the bottom row of the box is an open primal path, so the right wall
is left-reachable. -/
theorem allOpen_bottom_walk (k n m : ℕ) (hm : (m : ℤ) ≤ (k : ℤ) + 1) :
    (primalGraph (fun _ : gridGraph.edgeSet => true) k n).Reachable
      (⟨((0 : ℤ), 0), inBox_bottom (k := k) (n := n) 0 (by omega)⟩ : BVert k n)
      (⟨((m : ℤ), 0), inBox_bottom (k := k) (n := n) m hm⟩ : BVert k n) := by
  induction m with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ m ih =>
      have hm' : ((m : ℤ)) ≤ (k : ℤ) + 1 := by
        have h := hm
        push_cast at h
        omega
      have hstep : (primalGraph (fun _ : gridGraph.edgeSet => true) k n).Adj
          (⟨((m : ℤ), 0), inBox_bottom (k := k) (n := n) m hm'⟩ : BVert k n)
          (⟨(((m + 1 : ℕ) : ℤ), 0), inBox_bottom (k := k) (n := n) (m + 1) hm⟩ : BVert k n) :=
        ⟨Or.inr ⟨rfl, Or.inr (by push_cast; ring)⟩, rfl⟩
      exact (ih hm').trans ⟨SimpleGraph.Walk.cons hstep SimpleGraph.Walk.nil⟩

/-- The right wall is left-reachable in the all-open configuration, proved
independently of the duality theorem, by walking along the open bottom row. -/
theorem allOpen_right_reachable {k n : ℕ} :
    ∃ v : BVert k n, v ∈ rightWall k n ∧
      v ∈ leftReach (fun _ : gridGraph.edgeSet => true) k n := by
  have hwalk := allOpen_bottom_walk k n (k + 1) (by push_cast; omega)
  have hend : (⟨(((k + 1 : ℕ) : ℤ), 0),
        inBox_bottom (k := k) (n := n) (k + 1) (by push_cast; omega)⟩ : BVert k n)
      = ⟨(((k : ℤ) + 1), 0),
        ⟨by positivity, le_refl _, le_refl 0, Int.natCast_nonneg n⟩⟩ :=
    Subtype.ext (Prod.ext (by push_cast; ring) rfl)
  rw [hend] at hwalk
  exact ⟨⟨(((k : ℤ) + 1), 0), ⟨by positivity, le_refl _, le_refl 0, Int.natCast_nonneg n⟩⟩,
    by simp [rightWall],
    ⟨⟨((0 : ℤ), 0), inBox_bottom (k := k) (n := n) 0 (by omega)⟩,
      by simp [leftWall], hwalk⟩⟩

/-- The all-closed configuration: the primal open graph has no edge at all. -/
theorem noAdj_allClosed {k n : ℕ} :
    ∀ x y : BVert k n, ¬ (primalGraph (fun _ : gridGraph.edgeSet => false) k n).Adj x y := by
  intro x y hxy
  exact Exists.elim hxy (fun _ hv => by simp at hv)

/-- In the all-closed configuration no right-wall vertex is left-reachable, so the
hypothesis of the closed-crossing theorem holds. -/
theorem allClosed_right_not_reachable {k n : ℕ} :
    ∀ v : BVert k n, v ∈ rightWall k n →
      v ∉ leftReach (fun _ : gridGraph.edgeSet => false) k n := by
  rintro v hv ⟨u, hu, hwalk⟩
  have hEq : u = v := eq_of_reachable_of_no_adj noAdj_allClosed hwalk
  have h1 : u.1.1 = 0 := hu
  have h2 : u.1.1 = (k : ℤ) + 1 := hEq ▸ hv
  omega

/-- **Second consistency instance.**  In the all-closed configuration the
closed-bond graph is maximally connected, and the closed-crossing theorem
produces a genuine below-to-above path there. -/
theorem allClosed_closed_crossing {k n : ℕ} (hn : 0 < n) :
    (closedGraph (fun _ : gridGraph.edgeSet => false) k n).Reachable (Sum.inr 0) (Sum.inr 1) :=
  closed_crossing_of_walls hn allClosed_right_not_reachable

/-- The duality theorem applied to the all-open configuration produces exactly
the conclusion verified independently above. -/
theorem allOpen_duality_instance {k n : ℕ} (hn : 0 < n) :
    ∃ v : BVert k n, v ∈ rightWall k n ∧
      v ∈ leftReach (fun _ : gridGraph.edgeSet => true) k n :=
  exists_open_crossing_of_no_closed_dual hn allOpen_no_closed_crossing

/-! ## 11. The same edges in the dual-configuration language -/

lemma belowPt_mem_belowRow {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    belowPt c ∈ belowRow := rfl

lemma abovePt_mem_aboveRow {k n : ℕ} (c : Fin (k + 1) × Fin n) :
    abovePt c ∈ aboveRow n := rfl

/-- Two cells attach to the same exterior dual point below exactly when they lie
in the same column: the exterior vertex absorbs the whole row, which is why it is
a region and not a dual vertex. -/
lemma belowPt_eq_iff {k n : ℕ} (c d : Fin (k + 1) × Fin n) :
    belowPt c = belowPt d ↔ c.1 = d.1 := by
  constructor
  · intro h
    have h1 : ((c.1 : ℕ) : ℤ) = ((d.1 : ℕ) : ℤ) := congrArg Prod.fst h
    exact Fin.ext (by exact_mod_cast h1)
  · intro h
    have h1 : ((c.1 : ℕ) : ℤ) = ((d.1 : ℕ) : ℤ) := by rw [h]
    unfold belowPt
    rw [h1]

/-- The analogous statement for the exterior row above the box. -/
lemma abovePt_eq_iff {k n : ℕ} (c d : Fin (k + 1) × Fin n) :
    abovePt c = abovePt d ↔ c.1 = d.1 := by
  constructor
  · intro h
    have h1 : ((c.1 : ℕ) : ℤ) = ((d.1 : ℕ) : ℤ) := congrArg Prod.fst h
    exact Fin.ext (by exact_mod_cast h1)
  · intro h
    have h1 : ((c.1 : ℕ) : ℤ) = ((d.1 : ℕ) : ℤ) := by rw [h]
    unfold abovePt
    rw [h1]

/-- The below exterior point attached to a bottom-row cell is a genuine unit dual
neighbour of that cell centre. -/
lemma gridAdj_belowPt_cellPt {k n : ℕ} (c : Fin (k + 1) × Fin n)
    (hc0 : ((c.2 : ℕ) : ℤ) = 0) : gridAdj (belowPt c) (cellPt c) := by
  simp only [belowPt, cellPt, hc0]
  exact Or.inl ⟨rfl, Or.inr (by norm_num)⟩

/-- The above exterior point attached to a top-row cell is a genuine unit dual
neighbour of that cell centre. -/
lemma gridAdj_cellPt_abovePt {k n : ℕ} (c : Fin (k + 1) × Fin n)
    (hc1 : ((c.2 : ℕ) : ℤ) = (n : ℤ) - 1) : gridAdj (cellPt c) (abovePt c) := by
  simp only [abovePt, cellPt, hc1]
  exact Or.inl ⟨rfl, Or.inr (by ring)⟩

/-- A cell-to-cell closed step is an **open** edge of the dual configuration
`dualConfig gridCrossEquiv ω` on the actual crossed dual edge. -/
theorem closed_edge_dualOpen {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c d : Fin (k + 1) × Fin n}
    (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inl d)) :
    ∃ (p q : GridV) (hpq : gridAdj p q),
      dualConfig gridCrossEquiv ω (crossEdge ⟨s(p, q), hpq⟩) = true ∧
        (crossEdge ⟨s(p, q), hpq⟩).val = s(cellPt c, cellPt d) := by
  obtain ⟨p, q, hpq, hfalse, hval⟩ := closed_edge_crossed h
  exact ⟨p, q, hpq, (dualOpen_iff_closed ω _).mpr hfalse, hval⟩

/-- The below link is a dual-open edge of the crossed dual configuration. -/
theorem closed_bottom_dualOpen {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c : Fin (k + 1) × Fin n} (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inr 0)) :
    ∃ (hb : gridAdj (((c.1 : ℕ) : ℤ), 0) ((((c.1 : ℕ) : ℤ)) + 1, 0)),
      dualConfig gridCrossEquiv ω
          (crossEdge ⟨s((((c.1 : ℕ) : ℤ), 0), ((((c.1 : ℕ) : ℤ)) + 1, 0)), hb⟩) = true ∧
        (crossEdge ⟨s((((c.1 : ℕ) : ℤ), 0), ((((c.1 : ℕ) : ℤ)) + 1, 0)), hb⟩).val
            = s(belowPt c, cellPt c) := by
  obtain ⟨hb, hfalse, hval, -⟩ := closed_bottom_crossed h
  exact ⟨hb, (dualOpen_iff_closed ω _).mpr hfalse, hval⟩

/-- The above link is a dual-open edge of the crossed dual configuration. -/
theorem closed_top_dualOpen {ω : gridGraph.edgeSet → Bool} {k n : ℕ}
    {c : Fin (k + 1) × Fin n} (h : (closedGraph ω k n).Adj (Sum.inl c) (Sum.inr 1)) :
    ∃ (hb : gridAdj (((c.1 : ℕ) : ℤ), (n : ℤ)) ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ))),
      dualConfig gridCrossEquiv ω
          (crossEdge ⟨s((((c.1 : ℕ) : ℤ), (n : ℤ)), ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ))), hb⟩) = true ∧
        (crossEdge ⟨s((((c.1 : ℕ) : ℤ), (n : ℤ)), ((((c.1 : ℕ) : ℤ)) + 1, (n : ℤ))), hb⟩).val
            = s(cellPt c, abovePt c) := by
  obtain ⟨hb, hfalse, hval, -⟩ := closed_top_crossed h
  exact ⟨hb, (dualOpen_iff_closed ω _).mpr hfalse, hval⟩

/-- **Box-uniform form.**  If no box admits a closed below-to-above crossing, then
every box admits an open primal left-to-right crossing.  This is the finite input
for the usual compactness step towards an infinite primal open cluster; that step
itself is *not* formalised here. -/
theorem exists_open_crossing_of_no_closed_crossing_any {ω : gridGraph.edgeSet → Bool}
    (h : ∀ k n : ℕ, 0 < n →
      ¬ (closedGraph ω k n).Reachable (Sum.inr 0) (Sum.inr 1)) (k n : ℕ) (hn : 0 < n) :
    ∃ u v : BVert k n,
      u ∈ leftWall k n ∧ v ∈ rightWall k n ∧ (primalGraph ω k n).Reachable u v :=
  exists_primal_open_walk_of_no_closed_dual hn (h k n hn)

/-- The exterior rows are locally finite: a dual vertex meets only finitely many
vertices of a row.  Collapsing the row into the single outer vertex of
`DVert` is therefore a genuine collapse of a locally finite dual region. -/
theorem belowRow_inter_neighbors_finite (p : GridV) :
    ({q : GridV | q ∈ belowRow ∧ gridAdj q p}).Finite := by
  refine Set.Finite.subset (finite_neighborSet p) ?_
  rintro q ⟨-, hq⟩
  exact gridAdj_symm hq

theorem aboveRow_inter_neighbors_finite (n : ℕ) (p : GridV) :
    ({q : GridV | q ∈ aboveRow n ∧ gridAdj q p}).Finite := by
  refine Set.Finite.subset (finite_neighborSet p) ?_
  rintro q ⟨-, hq⟩
  exact gridAdj_symm hq

end FK.PlaneTopology.PrimalClosedDuality

/-! ## 9. Principal declarations and trust -/

#print axioms FK.PlaneTopology.PrimalClosedDuality.leftReach_transfer
#print axioms FK.PlaneTopology.PrimalClosedDuality.boxMem_left_col
#print axioms FK.PlaneTopology.PrimalClosedDuality.boxMem_right_col
#print axioms FK.PlaneTopology.PrimalClosedDuality.hCut_boxMem_closed
#print axioms FK.PlaneTopology.PrimalClosedDuality.vCut_boxMem_closed
#print axioms FK.PlaneTopology.PrimalClosedDuality.CellClosed_comm
#print axioms FK.PlaneTopology.PrimalClosedDuality.DClosed_symm
#print axioms FK.PlaneTopology.PrimalClosedDuality.DClosed_irrefl
#print axioms FK.PlaneTopology.PrimalClosedDuality.DAdj_le_closed
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_crossing_of_walls
#print axioms FK.PlaneTopology.PrimalClosedDuality.exists_open_crossing_of_no_closed_dual
#print axioms FK.PlaneTopology.PrimalClosedDuality.exists_primal_open_walk_of_no_closed_dual
#print axioms FK.PlaneTopology.PrimalClosedDuality.cellPt_injective
#print axioms FK.PlaneTopology.PrimalClosedDuality.crossEdge_vert_bond
#print axioms FK.PlaneTopology.PrimalClosedDuality.crossEdge_horiz_bond
#print axioms FK.PlaneTopology.PrimalClosedDuality.gridAdj_cellPt
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_edge_crossed
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_bottom_crossed
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_top_crossed
#print axioms FK.PlaneTopology.PrimalClosedDuality.row_reachable
#print axioms FK.PlaneTopology.PrimalClosedDuality.row_vertices_reachable
#print axioms FK.PlaneTopology.PrimalClosedDuality.belowRow_infinite
#print axioms FK.PlaneTopology.PrimalClosedDuality.aboveRow_infinite
#print axioms FK.PlaneTopology.PrimalClosedDuality.belowRow_inter_neighbors_finite
#print axioms FK.PlaneTopology.PrimalClosedDuality.aboveRow_inter_neighbors_finite
#print axioms FK.PlaneTopology.PrimalClosedDuality.dualOpen_iff_closed
#print axioms FK.PlaneTopology.PrimalClosedDuality.bondClosed_iff_dualOpen
#print axioms FK.PlaneTopology.PrimalClosedDuality.leftReach_mono
#print axioms FK.PlaneTopology.PrimalClosedDuality.closedGraph_anti
#print axioms FK.PlaneTopology.PrimalClosedDuality.allOpen_no_closed_crossing
#print axioms FK.PlaneTopology.PrimalClosedDuality.allOpen_bottom_walk
#print axioms FK.PlaneTopology.PrimalClosedDuality.allOpen_right_reachable
#print axioms FK.PlaneTopology.PrimalClosedDuality.allOpen_duality_instance
#print axioms FK.PlaneTopology.PrimalClosedDuality.noAdj_allClosed
#print axioms FK.PlaneTopology.PrimalClosedDuality.allClosed_right_not_reachable
#print axioms FK.PlaneTopology.PrimalClosedDuality.allClosed_closed_crossing
#print axioms FK.PlaneTopology.PrimalClosedDuality.belowPt_eq_iff
#print axioms FK.PlaneTopology.PrimalClosedDuality.abovePt_eq_iff
#print axioms FK.PlaneTopology.PrimalClosedDuality.gridAdj_belowPt_cellPt
#print axioms FK.PlaneTopology.PrimalClosedDuality.gridAdj_cellPt_abovePt
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_edge_dualOpen
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_bottom_dualOpen
#print axioms FK.PlaneTopology.PrimalClosedDuality.closed_top_dualOpen
#print axioms FK.PlaneTopology.PrimalClosedDuality.exists_open_crossing_of_no_closed_crossing_any
