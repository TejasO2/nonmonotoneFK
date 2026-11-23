import FK.Theorem14
import CurvatureVariance.Infra.Percolation.Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

namespace FK.Phases

/-- An edge is open with the stated parameter, not its complement. -/
theorem bernoulliProduct_apply_open {E : Type*} (r : E → unitInterval) (e : E) :
    (bernoulliProduct r : Measure (EdgeConfiguration E)) {ω | ω e = true} =
      ENNReal.ofReal (r e : ℝ) := by
  have h := congrArg (fun μ : Measure Bool => μ {true}) (map_eval_bernoulliProduct r e)
  rw [Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton true),
    CurvatureVariance.Infra.Percolation.bernoulliMeasure_true] at h
  exact h

/-- An edge is closed with probability one minus its stated parameter. -/
theorem bernoulliProduct_apply_closed {E : Type*} (r : E → unitInterval) (e : E) :
    (bernoulliProduct r : Measure (EdgeConfiguration E)) {ω | ω e = false} =
      ENNReal.ofReal (1 - (r e : ℝ)) := by
  have h := congrArg (fun μ : Measure Bool => μ {false}) (map_eval_bernoulliProduct r e)
  rw [Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton false),
    CurvatureVariance.Infra.Percolation.bernoulliMeasure_false] at h
  exact h

end FK.Phases
