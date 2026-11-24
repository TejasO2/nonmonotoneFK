import FK.GridDualConfigBridge

/-!
# Closed staircase barriers force dual percolation

`FK.GridDualConfigBridge` identifies the closed-bond cell graph `cellClosedGraph ω`
with the dual configuration `dualConfig gridCrossEquiv ω`.  The present module
supplies the missing `*`-to-adjacency upgrade: a closed *staircase* ray (an
infinite path of closed primal bonds that turns at every vertex) has its "corner
cells" joined by shared closed bonds, hence produces a genuinely infinite
adjacency (dual) component.

No `sorry`/`admit`, no custom axiom, no `unsafe`, no `native_decide`, no heartbeat
override.  The residual step (constructing such a staircase ray from two infinite
primal clusters) is *not* asserted here.
-/

namespace FK.PlaneTopology.BlockedStaircase

open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PrimalClosedDuality
open FK.PlaneTopology.GridCofinalCrossing
open FK.PlaneTopology.GridDualConfigBridge
open FK.Configuration
open CurvatureVariance.Infra.Percolation

attribute [local instance] Classical.propDecidable

variable {ω : gridGraph.edgeSet → Bool}

/-! ## 1. The two cells adjacent to a primal bond -/

/-- The lower (horizontal bond) resp. left (vertical bond) cell adjacent to the
primal bond with endpoints `p`, `q`. -/
def sideLo (p q : GridV) : GridV :=
  if p.2 = q.2 then (min p.1 q.1, min p.2 q.2 - 1) else (min p.1 q.1 - 1, min p.2 q.2)

/-- The upper (horizontal bond) resp. right (vertical bond) cell adjacent to the
primal bond with endpoints `p`, `q`. -/
def sideHi (p q : GridV) : GridV :=
  (min p.1 q.1, min p.2 q.2)

/-- `c` is one of the two cells adjacent to the primal bond `p`--`q`. -/
def IsSideCell (p q : GridV) (c : GridV) : Prop :=
  c = sideLo p q ∨ c = sideHi p q

lemma sideLo_comm (p q : GridV) : sideLo p q = sideLo q p := by
  unfold sideLo
  by_cases h : p.2 = q.2
  · rw [if_pos h, if_pos h.symm, min_comm p.1 q.1, min_comm p.2 q.2]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), min_comm p.1 q.1, min_comm p.2 q.2]

lemma sideHi_comm (p q : GridV) : sideHi p q = sideHi q p := by
  simp only [sideHi, min_comm]

/-- Side-cell description for a horizontal bond. -/
lemma sideLo_horiz {p q : GridV} (h : p.2 = q.2) :
    sideLo p q = (min p.1 q.1, min p.2 q.2 - 1) := by
  unfold sideLo
  rw [if_pos h]

/-- Side-cell description for a vertical bond. -/
lemma sideLo_vert {p q : GridV} (h : p.1 = q.1) (h2 : ¬ p.2 = q.2) :
    sideLo p q = (min p.1 q.1 - 1, min p.2 q.2) := by
  unfold sideLo
  rw [if_neg h2]

/-- A closed primal bond joins its two side cells in the closed cell graph. -/
theorem CellClosed_sideCells {p q : GridV} (h : gridAdj p q)
    (hc : bondClosed ω p q) :
    CellClosed ω (sideLo p q).1 (sideLo p q).2 (sideHi p q).1 (sideHi p q).2 := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · -- vertical bond, `q` south of `p`
    rw [sideLo_vert h1 (by omega)]
    simp only [sideHi]
    rw [min_eq_right (by omega : q.1 ≤ p.1), min_eq_right (by omega : q.2 ≤ p.2)]
    refine Or.inl ⟨rfl, Or.inl (by omega), ?_⟩
    rw [min_eq_left (by omega : q.1 - 1 ≤ q.1)]
    have hp : p = (q.1, q.2 + 1) := by ext <;> simp_all <;> omega
    rw [hp] at hc
    simpa using bondClosed_comm hc
  · -- vertical bond, `q` north of `p`
    rw [sideLo_vert h1 (by omega)]
    simp only [sideHi]
    rw [min_eq_right (by omega : q.1 ≤ p.1), min_eq_left (by omega : p.2 ≤ q.2)]
    refine Or.inl ⟨rfl, Or.inl (by omega), ?_⟩
    rw [min_eq_left (by omega : q.1 - 1 ≤ q.1)]
    have hp : p = (q.1, p.2) := by
      refine Prod.ext ?_ ?_
      · exact h1
      · rfl
    have hq : q = (q.1, p.2 + 1) := by
      refine Prod.ext ?_ ?_
      · rfl
      · exact h2
    rw [hp, hq] at hc
    simpa using hc
  · -- horizontal bond, `q` west of `p`
    rw [sideLo_horiz h1]
    simp only [sideHi]
    rw [min_eq_right (by omega : q.1 ≤ p.1), min_eq_right (by omega : q.2 ≤ p.2)]
    refine Or.inr ⟨rfl, Or.inl (by omega), ?_⟩
    rw [min_eq_left (by omega : q.2 - 1 ≤ q.2)]
    have hp : p = (q.1 + 1, q.2) := by ext <;> simp_all <;> omega
    rw [hp] at hc
    simpa using bondClosed_comm hc
  · -- horizontal bond, `q` east of `p`
    rw [sideLo_horiz h1]
    simp only [sideHi]
    rw [min_eq_left (by omega : p.1 ≤ q.1), min_eq_left (by omega : p.2 ≤ q.2)]
    refine Or.inr ⟨rfl, Or.inl (by omega), ?_⟩
    rw [min_eq_left (by omega : p.2 - 1 ≤ p.2)]
    have hq : q = (p.1 + 1, p.2) := by ext <;> simp_all <;> omega
    rw [hq] at hc
    simpa using hc


/-! ## 1b. Explicit side cells by direction -/

lemma sideHi_east {p q : GridV} (h1 : p.2 = q.2) (h2 : q.1 = p.1 + 1) :
    sideHi p q = (p.1, p.2) := by
  simp only [sideHi, min_eq_left (by omega : p.1 ≤ q.1), min_eq_left (by omega : p.2 ≤ q.2)]

lemma sideLo_east {p q : GridV} (h1 : p.2 = q.2) (h2 : q.1 = p.1 + 1) :
    sideLo p q = (p.1, p.2 - 1) := by
  rw [sideLo_horiz h1]
  simp only [min_eq_left (by omega : p.1 ≤ q.1), min_eq_left (by omega : p.2 ≤ q.2)]

lemma sideHi_west {p q : GridV} (h1 : p.2 = q.2) (h2 : p.1 = q.1 + 1) :
    sideHi p q = (q.1, p.2) := by
  simp only [sideHi, min_eq_right (by omega : q.1 ≤ p.1), min_eq_left (by omega : p.2 ≤ q.2)]

lemma sideLo_west {p q : GridV} (h1 : p.2 = q.2) (h2 : p.1 = q.1 + 1) :
    sideLo p q = (q.1, p.2 - 1) := by
  rw [sideLo_horiz h1]
  simp only [min_eq_right (by omega : q.1 ≤ p.1), min_eq_left (by omega : p.2 ≤ q.2)]

lemma sideHi_north {p q : GridV} (h1 : p.1 = q.1) (h2 : q.2 = p.2 + 1) :
    sideHi p q = (p.1, p.2) := by
  simp only [sideHi, min_eq_left (by omega : p.1 ≤ q.1), min_eq_left (by omega : p.2 ≤ q.2)]

lemma sideLo_north {p q : GridV} (h1 : p.1 = q.1) (h2 : q.2 = p.2 + 1) :
    sideLo p q = (p.1 - 1, p.2) := by
  rw [sideLo_vert h1 (by omega)]
  simp only [min_eq_left (by omega : p.1 ≤ q.1), min_eq_left (by omega : p.2 ≤ q.2)]

lemma sideHi_south {p q : GridV} (h1 : p.1 = q.1) (h2 : p.2 = q.2 + 1) :
    sideHi p q = (p.1, q.2) := by
  simp only [sideHi, min_eq_left (by omega : p.1 ≤ q.1), min_eq_right (by omega : q.2 ≤ p.2)]

lemma sideLo_south {p q : GridV} (h1 : p.1 = q.1) (h2 : p.2 = q.2 + 1) :
    sideLo p q = (p.1 - 1, q.2) := by
  rw [sideLo_vert h1 (by omega)]
  simp only [min_eq_left (by omega : p.1 ≤ q.1), min_eq_right (by omega : q.2 ≤ p.2)]

/-- The two side cells of a genuine bond are distinct. -/
lemma sideLo_ne_sideHi {p q : GridV} (h : gridAdj p q) : sideLo p q ≠ sideHi p q := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · rw [sideLo_vert h1 (by omega)]
    simp only [sideHi]
    rw [min_eq_right (by omega : q.1 ≤ p.1), min_eq_right (by omega : q.2 ≤ p.2)]
    intro hc
    have := congrArg Prod.fst hc
    simp at this
  · rw [sideLo_vert h1 (by omega)]
    simp only [sideHi]
    rw [min_eq_right (by omega : q.1 ≤ p.1), min_eq_left (by omega : p.2 ≤ q.2)]
    intro hc
    have := congrArg Prod.fst hc
    simp at this
  · rw [sideLo_horiz h1]
    simp only [sideHi]
    rw [min_eq_right (by omega : q.1 ≤ p.1), min_eq_right (by omega : q.2 ≤ p.2)]
    intro hc
    have := congrArg Prod.snd hc
    simp at this
  · rw [sideLo_horiz h1]
    simp only [sideHi]
    rw [min_eq_left (by omega : p.1 ≤ q.1), min_eq_left (by omega : p.2 ≤ q.2)]
    intro hc
    have := congrArg Prod.snd hc
    simp at this

/-! ## 2. The inner corner cell of a turn -/

/-- Horizontal step. -/
def HorizStep (p q : GridV) : Prop := p.2 = q.2

/-- Vertical step. -/
def VertStep (p q : GridV) : Prop := p.1 = q.1

/-- The "inner corner" cell determined by three consecutive lattice vertices. -/
def corner (p q r : GridV) : GridV :=
  (min (min p.1 q.1) r.1, min (min p.2 q.2) r.2)

lemma corner_swap (p q r : GridV) : corner r q p = corner p q r := by
  simp only [corner]
  exact Prod.ext (by ac_rfl) (by ac_rfl)

/-- At a turn, the corner cell is a side cell of the incoming bond. -/
theorem corner_isSide_first {p q r : GridV} (h1 : gridAdj p q) (h2 : gridAdj q r)
    (hturn : (HorizStep p q ∧ VertStep q r) ∨ (VertStep p q ∧ HorizStep q r)) :
    IsSideCell p q (corner p q r) := by
  rcases h1 with ⟨c1, hs | hs⟩ | ⟨c2, hw | he⟩
  · -- first step vertical, `q` south of `p`
    rcases h2 with ⟨-, hb | ht⟩ | ⟨hr, hwr | her⟩
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
    · left
      have e1 : min p.1 q.1 = q.1 := min_eq_right (by omega)
      have e2 : min p.2 q.2 = q.2 := min_eq_right (by omega)
      have e3 : min (min p.1 q.1) r.1 = r.1 := by
        rw [e1]
        exact min_eq_right (by omega)
      have e4 : min (min p.2 q.2) r.2 = q.2 := by
        rw [e2]
        exact min_eq_left (by omega)
      simp only [corner, sideLo, if_neg (by omega : ¬ p.2 = q.2)]
      rw [e3, e4, e1, e2]
      exact Prod.ext (by omega) (by omega)
    · right
      have e1 : min p.1 q.1 = q.1 := min_eq_right (by omega)
      have e2 : min p.2 q.2 = q.2 := min_eq_right (by omega)
      have e3 : min (min p.1 q.1) r.1 = q.1 := by
        rw [e1]
        exact min_eq_left (by omega)
      have e4 : min (min p.2 q.2) r.2 = q.2 := by
        rw [e2]
        exact min_eq_left (by omega)
      simp only [corner, sideHi]
      rw [e3, e4, e1, e2]
  · -- first step vertical, `q` north of `p`
    rcases h2 with ⟨-, hb | ht⟩ | ⟨hr, hwr | her⟩
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
    · left
      have e1 : min p.1 q.1 = q.1 := min_eq_right (by omega)
      have e2 : min p.2 q.2 = p.2 := min_eq_left (by omega)
      have e3 : min (min p.1 q.1) r.1 = r.1 := by
        rw [e1]
        exact min_eq_right (by omega)
      have e4 : min (min p.2 q.2) r.2 = p.2 := by
        rw [e2]
        exact min_eq_left (by omega)
      simp only [corner, sideLo, if_neg (by omega : ¬ p.2 = q.2)]
      rw [e3, e4, e1, e2]
      exact Prod.ext (by omega) (by omega)
    · right
      have e1 : min p.1 q.1 = q.1 := min_eq_right (by omega)
      have e2 : min p.2 q.2 = p.2 := min_eq_left (by omega)
      have e3 : min (min p.1 q.1) r.1 = q.1 := by
        rw [e1]
        exact min_eq_left (by omega)
      have e4 : min (min p.2 q.2) r.2 = p.2 := by
        rw [e2]
        exact min_eq_left (by omega)
      simp only [corner, sideHi]
      rw [e3, e4, e1, e2]
  · -- first step horizontal, `q` west of `p`
    rcases h2 with ⟨hqr1, hb | ht⟩ | ⟨hr, hwr | her⟩
    · left
      have e1 : min p.1 q.1 = q.1 := min_eq_right (by omega)
      have e2 : min p.2 q.2 = q.2 := min_eq_right (by omega)
      have e3 : min (min p.1 q.1) r.1 = q.1 := by
        rw [e1]
        exact min_eq_left (by omega)
      have e4 : min (min p.2 q.2) r.2 = r.2 := by
        rw [e2]
        exact min_eq_right (by omega)
      simp only [corner, sideLo, if_pos c2]
      rw [e3, e4, e1, e2]
      exact Prod.ext (by omega) (by omega)
    · right
      have e1 : min p.1 q.1 = q.1 := min_eq_right (by omega)
      have e2 : min p.2 q.2 = q.2 := min_eq_right (by omega)
      have e3 : min (min p.1 q.1) r.1 = q.1 := by
        rw [e1]
        exact min_eq_left (by omega)
      have e4 : min (min p.2 q.2) r.2 = q.2 := by
        rw [e2]
        exact min_eq_left (by omega)
      simp only [corner, sideHi]
      rw [e3, e4, e1, e2]
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
  · -- first step horizontal, `q` east of `p`
    rcases h2 with ⟨hqr1, hb | ht⟩ | ⟨hr, hwr | her⟩
    · left
      have e1 : min p.1 q.1 = p.1 := min_eq_left (by omega)
      have e2 : min p.2 q.2 = p.2 := min_eq_left (by omega)
      have e3 : min (min p.1 q.1) r.1 = p.1 := by
        rw [e1]
        exact min_eq_left (by omega)
      have e4 : min (min p.2 q.2) r.2 = r.2 := by
        rw [e2]
        exact min_eq_right (by omega)
      simp only [corner, sideLo, if_pos c2]
      rw [e3, e4, e1, e2]
      exact Prod.ext (by omega) (by omega)
    · right
      have e1 : min p.1 q.1 = p.1 := min_eq_left (by omega)
      have e2 : min p.2 q.2 = p.2 := min_eq_left (by omega)
      have e3 : min (min p.1 q.1) r.1 = p.1 := by
        rw [e1]
        exact min_eq_left (by omega)
      have e4 : min (min p.2 q.2) r.2 = p.2 := by
        rw [e2]
        exact min_eq_left (by omega)
      simp only [corner, sideHi]
      rw [e3, e4, e1, e2]
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)
    · exfalso
      rcases hturn with ⟨hq, hr⟩ | ⟨hp, hs'⟩ <;> (simp only [HorizStep, VertStep] at *; omega)

/-- At a turn, the corner cell is a side cell of the outgoing bond. -/
theorem corner_isSide_second {p q r : GridV} (h1 : gridAdj p q) (h2 : gridAdj q r)
    (hturn : (HorizStep p q ∧ VertStep q r) ∨ (VertStep p q ∧ HorizStep q r)) :
    IsSideCell q r (corner p q r) := by
  have hturn' : (HorizStep r q ∧ VertStep q p) ∨ (VertStep r q ∧ HorizStep q p) := by
    rcases hturn with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inr ⟨b.symm, a.symm⟩
    · exact Or.inl ⟨b.symm, a.symm⟩
  have h := corner_isSide_first (p := r) (q := q) (r := p) (gridAdj_symm h2) (gridAdj_symm h1) hturn'
  simp only [IsSideCell, corner_swap p q r, sideLo_comm, sideHi_comm] at h
  exact h


/-! ## 3. Closed staircase rays and their corner cells -/

/-- An infinite closed staircase ray: a ray of closed primal bonds that turns at
every vertex. -/
structure StaircaseRay (ω : gridGraph.edgeSet → Bool) where
  /-- the ray of lattice vertices -/
  v : ℕ → GridV
  /-- every step is a closed primal bond -/
  closed : ∀ n, gridAdj (v n) (v (n + 1)) ∧ bondClosed ω (v n) (v (n + 1))
  /-- consecutive steps are perpendicular -/
  turn : ∀ n, (HorizStep (v n) (v (n + 1)) ∧ VertStep (v (n + 1)) (v (n + 2))) ∨
    (VertStep (v n) (v (n + 1)) ∧ HorizStep (v (n + 1)) (v (n + 2)))

namespace StaircaseRay

variable {ω : gridGraph.edgeSet → Bool} (S : StaircaseRay ω)

/-- The inner corner cell at the `n`-th vertex of the ray. -/
def cell (n : ℕ) : GridV := corner (S.v n) (S.v (n + 1)) (S.v (n + 2))

lemma cell_isSide_in (n : ℕ) : IsSideCell (S.v n) (S.v (n + 1)) (S.cell n) :=
  corner_isSide_first (S.closed n).1 (S.closed (n + 1)).1 (S.turn n)

lemma cell_isSide_out (n : ℕ) : IsSideCell (S.v (n + 1)) (S.v (n + 2)) (S.cell n) :=
  corner_isSide_second (S.closed n).1 (S.closed (n + 1)).1 (S.turn n)

/-- Consecutive corner cells lie in the same closed cell component. -/
theorem cell_succ_reachable (n : ℕ) :
    (cellClosedGraph ω).Reachable (S.cell n) (S.cell (n + 1)) := by
  have hg := (S.closed (n + 1)).1
  have hb := (S.closed (n + 1)).2
  have hbase := CellClosed_sideCells (ω := ω) hg hb
  have hin := S.cell_isSide_out n
  have hout := S.cell_isSide_in (n + 1)
  rcases hin with h | h <;> rcases hout with h' | h'
  · rw [h, h']
  · rw [h, h']
    exact SimpleGraph.Adj.reachable hbase
  · rw [h, h']
    exact SimpleGraph.Adj.reachable (CellClosed_comm hbase)
  · rw [h, h']

/-- **The `*`-to-adjacency upgrade.**  A closed staircase ray with injective
corner sequence produces an infinite component of the closed cell graph. -/
theorem exists_infinite_cellComponent (hinj : Function.Injective S.cell) :
    ∃ c : GridV, {c' : GridV | (cellClosedGraph ω).Reachable c c'}.Infinite := by
  refine ⟨S.cell 0, ?_⟩
  have hmono : Set.range S.cell ⊆
      {c' : GridV | (cellClosedGraph ω).Reachable (S.cell 0) c'} := by
    rintro _ ⟨n, rfl⟩
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (S.cell_succ_reachable n)
  exact (Set.infinite_range_of_injective hinj).mono hmono

/-- The same statement in the repository's dual percolation language
`dualConfig gridCrossEquiv ω`: an infinite dual-open cluster. -/
theorem exists_infinite_dualCluster (hinj : Function.Injective S.cell) :
    ∃ c : GridV,
      {c' : GridV | OpenConnected gridDual (dualConfig gridCrossEquiv ω) Set.univ c c'}.Infinite := by
  obtain ⟨c, hc⟩ := S.exists_infinite_cellComponent hinj
  refine ⟨c, hc.mono ?_⟩
  intro c' hc'
  exact (FK.PlaneTopology.GridDualConfigBridge.cellReach_iff_openConnected (ω := ω)).mp hc'

/-- **Dual non-percolation forbids such a staircase barrier.** -/
theorem not_injective_cell_of_noInfiniteOpenCluster
    (h : FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω)) :
    ¬ Function.Injective S.cell := by
  intro hinj
  obtain ⟨c, hc⟩ := S.exists_infinite_dualCluster hinj
  exact hc (h c)

end StaircaseRay

end FK.PlaneTopology.BlockedStaircase

namespace FK.PlaneTopology.BlockedStaircase

open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.GridDualIncidence
open FK.PlaneTopology.PrimalClosedDuality
open FK.PlaneTopology.GridCofinalCrossing
open FK.PlaneTopology.GridDualConfigBridge
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open CurvatureVariance.Infra.Percolation

/-! ## 3b. Sanity checks on the concrete staircase `(0,0) → (1,0) → (1,1) → (2,1)` -/

section SanityCheck

/-- The corner cell of the first turn of the up-right staircase. -/
example : corner ((0 : ℤ), (0 : ℤ)) (1, 0) (1, 1) = ((0 : ℤ), (0 : ℤ)) := by
  norm_num [corner]

/-- The corner cell of the second turn. -/
example : corner ((1 : ℤ), (0 : ℤ)) (1, 1) (2, 1) = ((1 : ℤ), (0 : ℤ)) := by
  norm_num [corner]

/-- The two corner cells of the first two turns are `CellClosed`-adjacent in the
all-closed configuration (the shared closed bond is the vertical bond
`(1,0) -- (1,1)`). -/
example : CellClosed (fun _ : gridGraph.edgeSet => false) 0 0 1 0 := by
  refine Or.inl ⟨rfl, Or.inl (by norm_num), ?_⟩
  simp [bondClosed, bondOpen]

end SanityCheck

/-! ## 4. Conditional assembly: the residual planar input

The upgrade above turns a *closed staircase barrier* into dual percolation.  What
remains for the deterministic planar uniqueness step is the *existence* of such a
barrier between two distinct infinite open clusters.  We state that input as a
predicate (a definition, not an axiom) and record exactly what it buys. -/

/-- **Residual planar input.**  Any two vertices lying in distinct infinite open
clusters are separated by an infinite closed staircase barrier whose corner cell
sequence is injective.

Geometrically this is the "blocking closed `*`-barrier" of the classical planar
uniqueness argument: a closed curve separating the two clusters that turns at
every lattice vertex (a straight through-vertex would be passable by an open
path).  Constructing it from the two clusters is the remaining step; it is *not*
asserted anywhere in this file. -/
def StaircaseBarrierExists (ω : gridGraph.edgeSet → Bool) : Prop :=
  ∀ x y : GridV,
    ExteriorInfiniteCluster gridGraph ω Set.univ x →
    ExteriorInfiniteCluster gridGraph ω Set.univ y →
    ¬ OpenConnected gridGraph ω Set.univ x y →
    ∃ S : StaircaseRay ω, Function.Injective S.cell

/-- **Two infinite clusters force dual percolation**, given the staircase barrier
input. -/
theorem exists_infinite_dualCluster_of_distinct_infinite_clusters
    (h : StaircaseBarrierExists ω) {x y : GridV}
    (hx : ExteriorInfiniteCluster gridGraph ω Set.univ x)
    (hy : ExteriorInfiniteCluster gridGraph ω Set.univ y)
    (hxy : ¬ OpenConnected gridGraph ω Set.univ x y) :
    ∃ c : GridV,
      {c' : GridV | OpenConnected gridDual (dualConfig gridCrossEquiv ω) Set.univ c c'}.Infinite := by
  obtain ⟨S, hinj⟩ := h x y hx hy hxy
  exact S.exists_infinite_dualCluster hinj

/-- **Conditional planar uniqueness step.**  Dual non-percolation together with
the residual staircase barrier input implies `GlobalAtMostOne`.  The only unproved
ingredient is the binder `h`; the `*`-to-adjacency upgrade it is fed into is proved
in §3. -/
theorem globalAtMostOne_of_staircaseBarriers
    (h : StaircaseBarrierExists ω)
    (hdual : FK.Planar.NoInfiniteOpenCluster gridDual (dualConfig gridCrossEquiv ω)) :
    GlobalAtMostOne gridGraph ω := by
  intro x y hx hy
  by_contra hxy
  obtain ⟨S, hinj⟩ := h x y hx hy hxy
  exact S.not_injective_cell_of_noInfiniteOpenCluster hdual hinj

end FK.PlaneTopology.BlockedStaircase

/-! ## 5. Principal declarations and trust -/

#print axioms FK.PlaneTopology.BlockedStaircase.CellClosed_sideCells
#print axioms FK.PlaneTopology.BlockedStaircase.sideLo_ne_sideHi
#print axioms FK.PlaneTopology.BlockedStaircase.corner_isSide_first
#print axioms FK.PlaneTopology.BlockedStaircase.corner_isSide_second
#print axioms FK.PlaneTopology.BlockedStaircase.StaircaseRay.cell_succ_reachable
#print axioms FK.PlaneTopology.BlockedStaircase.StaircaseRay.exists_infinite_cellComponent
#print axioms FK.PlaneTopology.BlockedStaircase.StaircaseRay.exists_infinite_dualCluster
#print axioms FK.PlaneTopology.BlockedStaircase.StaircaseRay.not_injective_cell_of_noInfiniteOpenCluster
#print axioms FK.PlaneTopology.BlockedStaircase.exists_infinite_dualCluster_of_distinct_infinite_clusters
#print axioms FK.PlaneTopology.BlockedStaircase.globalAtMostOne_of_staircaseBarriers
