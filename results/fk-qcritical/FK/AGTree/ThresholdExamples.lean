import FK.AGTree.SharpThreshold

/-!
# Concrete rates on both sides of the exact critical value `1/2`

`TreeSharpThreshold` proves that for the base law (no open class-`1` edges) the percolation
probability vanishes for `2 r₀ < 1` and is positive for `1 < 2 r₀`.  This file instantiates
the two sides at the concrete rates `3/10` (the paper's base rate) and `3/5`, and records the
activated shift at `(3/10, 1/2)`.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-- The base rate `3/5`, above the critical value `1/2`. -/
noncomputable def p35 : unitInterval := ⟨3/5, by norm_num⟩

theorem two_mul_p0_lt_one : 2 * (((enhRate p0 0) 0 : unitInterval) : ℝ) < 1 := by
  norm_num [enhRate, p0]

theorem one_lt_two_mul_p35 : 1 < 2 * (((enhRate p35 0) 0 : unitInterval) : ℝ) := by
  norm_num [enhRate, p35]

/-- **Exact base nonpercolation at the paper's rate `3/10`**, from the sharp threshold
`2 r₀ < 1` (not only from `3 r₀ < 1`). -/
theorem base_nonpercolation_sharp :
    pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} = 0 :=
  pr_percolation_zero_of_two_mul_lt_one (enhRate p0 0) base_rate_one two_mul_p0_lt_one

/-- At base rate `3/5`, above `1/2`, the tree percolates. -/
theorem perc_at_three_fifths :
    0 < pr (enhRate p35 0) {ω : G.edgeSet → Bool | Perc ω} :=
  (base_critical_one_half (enhRate p35 0) (by norm_num [enhRate])).2 one_lt_two_mul_p35

/-- The two concrete rates straddle the critical value: `(3/10, 0)` does not percolate and
`(3/5, 0)` does. -/
theorem rates_straddle_half :
    pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} = 0 ∧
      0 < pr (enhRate p35 0) {ω : G.edgeSet → Bool | Perc ω} :=
  ⟨base_nonpercolation_sharp, perc_at_three_fifths⟩

/-- The activated law `(3/10, 1/2)` percolates although the base law `(3/10, 0)` does not. -/
theorem activation_moves_across_threshold :
    pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} = 0 ∧
      0 < pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} :=
  ⟨base_nonpercolation_sharp, activated_percolation⟩

end Ultra
