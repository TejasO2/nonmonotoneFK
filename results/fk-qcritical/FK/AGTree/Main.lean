import FK.AGTree.Shift

/-!
# A strict phase point for the activated two-class tree

At base rate `3/10` with independent activation at rate `1/2`, the root cluster percolates.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal unitInterval Topology

/-- The activated law: class-`0` letters at `p`, class-`1` letters at `s`. -/
noncomputable def enhRate (p s : unitInterval) : Fin 2 → unitInterval :=
  fun j => if j = 0 then p else s

/-- Base rate `3/10`. -/
noncomputable def p0 : unitInterval := ⟨3/10, by norm_num⟩

/-- Activation rate `1/2`. -/
noncomputable def s0 : unitInterval := ⟨1/2, by norm_num⟩

/-- **The activated law percolates at base rate `3/10` with activation `1/2`.** -/
theorem enh_cluster_pos :
    0 < pr (enhRate p0 s0) {ω | Cluster ω V.root} := by
  have hfac : ∀ a : A, (1 - (enhRate p0 s0 (acls a) : ℝ)) +
      (enhRate p0 s0 (acls a) : ℝ) * (fun _ : Fin 2 => (9/10 : ℝ)) (acls a)
      ≤ 97/100 := by
    intro a
    fin_cases a <;> norm_num [acls, enhRate, p0, s0]
  refine cluster_pos_of_uniform (enhRate p0 s0)
    (fun _ => (9/10 : ℝ)) (97/100) (fun _ => by norm_num) (fun _ => by norm_num)
    (by norm_num) (by norm_num) hfac (fun _ => by norm_num) (by norm_num)

end Ultra
