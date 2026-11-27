import FK.AGShift
import FK.PcPos

open Set MeasureTheory ProbabilityTheory
open CurvatureVariance.Infra.Percolation
open scoped SimpleGraph Sym2

namespace FK.AGShift

universe u

variable {V : Type u} [Countable V] (G : SimpleGraph V) [G.LocallyFinite] (o : V)

/-- The paper's Remark 1.5: positivity of `p_c` is derivable, not an additional
source hypothesis. -/
theorem criticalProb_pos_of_quasiTransitive
    (hconn : G.Connected) (hqt : FK.QuasiTransitive.IsQuasiTransitive G) :
    0 < criticalProb G o := by
  obtain ⟨Δ, hΔ⟩ := FK.QuasiTransitive.exists_degree_bound G hconn hqt
  have hΔ0 : 0 < Δ + 1 := Nat.zero_lt_succ _
  apply CurvatureVariance.Infra.Percolation.criticalProb_pos (d := Δ + 1) hconn _ hΔ0
  intro v
  rw [SimpleGraph.ncard_neighborSet]
  exact (hΔ v).trans (Nat.le_succ Δ)

/-- Build the repository's package from exactly the graph hypotheses printed in
Theorem 1.4.  Proof irrelevance makes this equivalent to the old package, whose
`pc_pos` field is now filled by the first-moment theorem. -/
theorem PaperGraphHypotheses.of_source
    (hinfinite : Infinite V)
    (hconn : G.Connected)
    (hqt : FK.QuasiTransitive.IsQuasiTransitive G)
    (hpc1 : criticalProb G o < 1)
    (hpivotal : ∃ e : G.edgeSet, FK.EssentialEnhancement.OnDoubleRay e ∧
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (e : Sym2 V) ∈ c.edges) :
    PaperGraphHypotheses G o where
  infinite := hinfinite
  connected := hconn
  quasiTransitive := hqt
  pc_pos := criticalProb_pos_of_quasiTransitive G o hconn hqt
  pc_lt_one := hpc1
  pivotal := hpivotal


end FK.AGShift
