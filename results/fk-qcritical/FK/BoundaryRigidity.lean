/-
Sharpness of boundary-independence: away from `q = 1` and the `p` endpoints the
finite FK law genuinely depends on the boundary partition.  The witness is the
two-vertex, one-edge labelled multigraph: with the edge open the two vertices
are joined whatever boundary is used, while with the edge closed the free
boundary keeps them apart and the wired boundary does not.  The resulting FK
point masses have ratios `p / (q (1 - p))` (free) and `p / (1 - p)` (wired), so
they can only agree at `q = 1` (or `p ∈ {0,1}`).

Only the standard axioms are used.
-/
import FK.QOneLine
import FK.PlanarForestDuality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.InfiniteVolume.QOne

open FK.Finite

noncomputable section

/-- The two-vertex, one-edge labelled multigraph: a single edge from `false` to
`true`. -/
abbrev unitEdgeGraph : LabelledMultigraph where
  Vertex := Bool
  Edge := Fin 1
  source := fun _ => false
  target := fun _ => true

instance : Nonempty unitEdgeGraph.Vertex := ⟨false⟩

/-- With the unique edge open the two vertices are joined, so the free boundary
has one component. -/
lemma componentCount_free_allOpen_unitEdge :
    unitEdgeGraph.componentCount unitEdgeGraph.freeBoundary unitEdgeGraph.allOpen = 1 := by
  apply LabelledMultigraph.componentCount_eq_one_of_preconnected _ _ _ false
  intro x y
  by_cases hxy : x = y
  · subst hxy
    exact SimpleGraph.Reachable.refl x
  · have hedge : unitEdgeGraph.Joins (0 : Fin 1) x y := by
      cases x <;> cases y <;> simp_all [unitEdgeGraph, LabelledMultigraph.Joins]
    exact (SimpleGraph.Adj.reachable ⟨hxy, Or.inr ⟨0, rfl, hedge⟩⟩)

/-- With the unique edge closed the free boundary leaves two isolated vertices. -/
lemma componentCount_free_allClosed_unitEdge :
    unitEdgeGraph.componentCount unitEdgeGraph.freeBoundary unitEdgeGraph.allClosed = 2 := by
  rw [LabelledMultigraph.componentCount_free_allClosed]
  change Nat.card Bool = 2
  simp

/-- Whatever the configuration, the wired boundary has a single component. -/
lemma componentCount_wired_unitEdge_any (ω : unitEdgeGraph.Configuration) :
    unitEdgeGraph.componentCount unitEdgeGraph.wiredBoundary ω = 1 :=
  LabelledMultigraph.componentCount_wired unitEdgeGraph ω

/-- The Bernoulli edge weight of the open configuration of the one-edge graph. -/
lemma edgeWeight_allOpen_unitEdge (p : NNReal) :
    unitEdgeGraph.edgeWeight p unitEdgeGraph.allOpen = p := by
  rw [LabelledMultigraph.edgeWeight, Fintype.prod_unique]
  simp [LabelledMultigraph.allOpen]

/-- The Bernoulli edge weight of the closed configuration of the one-edge graph. -/
lemma edgeWeight_allClosed_unitEdge (p : NNReal) :
    unitEdgeGraph.edgeWeight p unitEdgeGraph.allClosed = 1 - p := by
  rw [LabelledMultigraph.edgeWeight, Fintype.prod_unique]
  simp [LabelledMultigraph.allClosed]

/-- Free boundary, open edge: FK weight `p * q`. -/
lemma fkWeight_free_allOpen_unitEdge {q p : NNReal} :
    unitEdgeGraph.fkWeight q p unitEdgeGraph.freeBoundary unitEdgeGraph.allOpen = p * q := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_allOpen_unitEdge,
    componentCount_free_allOpen_unitEdge, pow_one]

/-- Free boundary, closed edge: FK weight `(1 - p) * q ^ 2`. -/
lemma fkWeight_free_allClosed_unitEdge {q p : NNReal} :
    unitEdgeGraph.fkWeight q p unitEdgeGraph.freeBoundary unitEdgeGraph.allClosed =
      (1 - p) * q ^ 2 := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_allClosed_unitEdge,
    componentCount_free_allClosed_unitEdge]

/-- Wired boundary, open edge: FK weight `p * q`. -/
lemma fkWeight_wired_allOpen_unitEdge {q p : NNReal} :
    unitEdgeGraph.fkWeight q p unitEdgeGraph.wiredBoundary unitEdgeGraph.allOpen = p * q := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_allOpen_unitEdge,
    componentCount_wired_unitEdge_any, pow_one]

/-- Wired boundary, closed edge: FK weight `(1 - p) * q`. -/
lemma fkWeight_wired_allClosed_unitEdge {q p : NNReal} :
    unitEdgeGraph.fkWeight q p unitEdgeGraph.wiredBoundary unitEdgeGraph.allClosed =
      (1 - p) * q := by
  rw [LabelledMultigraph.fkWeight, edgeWeight_allClosed_unitEdge,
    componentCount_wired_unitEdge_any, pow_one]

/-- **Boundary dependence away from `q = 1`**: on the two-vertex one-edge graph
the free and wired FK laws differ whenever `q ≠ 1` and `0 < p < 1`.  The open
configuration has the same weight under both boundaries, while the closed
configuration has weights `(1 - p) q ^ 2` and `(1 - p) q`, so normalized
agreement at both configurations forces `q = 1`. -/
theorem fkPMF_freeBoundary_ne_wiredBoundary {q p : NNReal} (hq : 0 < q) (hq1 : q ≠ 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    unitEdgeGraph.fkPMF hq hp1.le unitEdgeGraph.freeBoundary ≠
      unitEdgeGraph.fkPMF hq hp1.le unitEdgeGraph.wiredBoundary := by
  intro h
  have ho : (unitEdgeGraph.fkPMF hq hp1.le unitEdgeGraph.freeBoundary)
        unitEdgeGraph.allOpen =
      (unitEdgeGraph.fkPMF hq hp1.le unitEdgeGraph.wiredBoundary) unitEdgeGraph.allOpen := by
    rw [h]
  have hc : (unitEdgeGraph.fkPMF hq hp1.le unitEdgeGraph.freeBoundary)
        unitEdgeGraph.allClosed =
      (unitEdgeGraph.fkPMF hq hp1.le unitEdgeGraph.wiredBoundary) unitEdgeGraph.allClosed := by
    rw [h]
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.fkPMF_apply] at ho hc
  rw [fkWeight_free_allOpen_unitEdge, fkWeight_wired_allOpen_unitEdge] at ho
  rw [fkWeight_free_allClosed_unitEdge, fkWeight_wired_allClosed_unitEdge] at hc
  have hoNN : p * q / unitEdgeGraph.partitionFunction q p unitEdgeGraph.freeBoundary =
      p * q / unitEdgeGraph.partitionFunction q p unitEdgeGraph.wiredBoundary :=
    ENNReal.coe_injective ho
  have hcNN : (1 - p) * q ^ 2 /
        unitEdgeGraph.partitionFunction q p unitEdgeGraph.freeBoundary =
      (1 - p) * q / unitEdgeGraph.partitionFunction q p unitEdgeGraph.wiredBoundary :=
    ENNReal.coe_injective hc
  have hZf : unitEdgeGraph.partitionFunction q p unitEdgeGraph.freeBoundary ≠ 0 :=
    (LabelledMultigraph.partitionFunction_pos unitEdgeGraph hq hp1.le _).ne'
  have hZw : unitEdgeGraph.partitionFunction q p unitEdgeGraph.wiredBoundary ≠ 0 :=
    (LabelledMultigraph.partitionFunction_pos unitEdgeGraph hq hp1.le _).ne'
  have hpq : p * q ≠ 0 := mul_ne_zero hp0.ne' hq.ne'
  have h1p : (1 - p : NNReal) ≠ 0 := by
    intro h0
    have hle : (1 : NNReal) ≤ p := tsub_eq_zero_iff_le.mp h0
    exact absurd hle (not_le.mpr hp1)
  have e1 : p * q * unitEdgeGraph.partitionFunction q p unitEdgeGraph.wiredBoundary =
      p * q * unitEdgeGraph.partitionFunction q p unitEdgeGraph.freeBoundary :=
    (div_eq_div_iff hZf hZw).mp hoNN
  have eZ : unitEdgeGraph.partitionFunction q p unitEdgeGraph.wiredBoundary =
      unitEdgeGraph.partitionFunction q p unitEdgeGraph.freeBoundary :=
    mul_left_cancel₀ hpq e1
  have e2 : (1 - p) * q ^ 2 * unitEdgeGraph.partitionFunction q p unitEdgeGraph.wiredBoundary =
      (1 - p) * q * unitEdgeGraph.partitionFunction q p unitEdgeGraph.freeBoundary :=
    (div_eq_div_iff hZf hZw).mp hcNN
  rw [eZ] at e2
  have e3 : (1 - p) * q ^ 2 = (1 - p) * q := mul_right_cancel₀ hZf e2
  have e4 : q ^ 2 = q := mul_left_cancel₀ h1p e3
  have e5 : q * q = q * 1 := by
    rw [pow_two] at e4
    simpa using e4
  exact hq1 (mul_left_cancel₀ hq.ne' e5)

/-- At `q = 1` every finite FK law is independent of the boundary partition. -/
theorem fkPMF_boundary_independent_of_q_one {p : NNReal} (hp : p ≤ 1)
    (G : LabelledMultigraph) (ξ ξ' : G.BoundaryPartition) :
    G.fkPMF (q := 1) zero_lt_one hp ξ = G.fkPMF (q := 1) zero_lt_one hp ξ' := by
  rw [LabelledMultigraph.fkPMF_q_one (G := G) hp ξ,
    LabelledMultigraph.fkPMF_q_one (G := G) hp ξ']

/-- **Finite characterisation of boundary-independence.**  For interior `p` and
`q > 0`, finite FK laws are independent of the boundary partition on every
finite labelled multigraph exactly when `q = 1`.  Together with `fkPMF_q_one`
this pins boundary-independence to the classical `q = 1` line (and to the
`p ∈ {0,1}` endpoints, where both laws are point masses). -/
theorem fkPMF_boundary_independent_iff {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (∀ (G : LabelledMultigraph.{0, 0}) (ξ ξ' : G.BoundaryPartition),
        G.fkPMF hq hp1.le ξ = G.fkPMF hq hp1.le ξ') ↔ q = 1 := by
  constructor
  · intro h
    by_contra hq1
    exact fkPMF_freeBoundary_ne_wiredBoundary hq hq1 hp0 hp1
      (h unitEdgeGraph unitEdgeGraph.freeBoundary unitEdgeGraph.wiredBoundary)
  · rintro rfl
    exact fun G ξ ξ' => fkPMF_boundary_independent_of_q_one hp1.le G ξ ξ'

end

end FK.InfiniteVolume.QOne
