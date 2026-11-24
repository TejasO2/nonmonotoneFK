/-
Infinite-volume sharpness of the `q = 1` collapse: away from `q = 1` the FK
limit class is not a singleton.  On the project's existing one-box exhaustion of
the two-vertex graph (`NoncoherentCounterexample.oneEdgeExhaustion`) the constant
free and wired boundary schedules have different limits at `q = 2`, `p = 1/2`:
their common box carries the finite free/wired FK laws, which differ (`1/3`
versus `1/2` for the open configuration).

Only the standard axioms are used.
-/
import FK.QOneLine
import FK.NoncoherentCounterexample

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.InfiniteVolume.QOne

noncomputable section

open FK.InfiniteVolume
open FK.InfiniteVolume.NoncoherentCounterexample

/-- The constant free-boundary finite-volume law of the one-edge box. -/
def freeOneEdgeLimit : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet) :=
  oneEdgeBox.finiteVolumeLaw (q := 2) (p := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary

/-- It is a genuine FK limit along the constant free boundary schedule. -/
theorem isFKLimit_freeOneEdgeLimit :
    IsFKLimit oneEdgeExhaustion (q := 2) (p := (1 / 2 : NNReal))
      (by norm_num) (by norm_num)
      (fun _ => oneEdgeBox.graph.freeBoundary) freeOneEdgeLimit :=
  tendsto_const_nhds

/-- The free and wired finite-volume laws of the one-edge box differ: their masses
on the global lift of the open interior configuration are `1/3` and `1/2`. -/
theorem finiteVolumeLaw_free_ne_wired_oneEdge :
    oneEdgeBox.finiteVolumeLaw (q := 2) (p := (1 / 2 : NNReal))
        (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary ≠
      oneEdgeBox.finiteVolumeLaw (q := 2) (p := (1 / 2 : NNReal))
        (by norm_num) (by norm_num) oneEdgeBox.graph.wiredBoundary := by
  intro h
  have hm := congrArg (fun ν : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet) =>
    (ν : Measure (Configuration TwoVertexGraph.edgeSet)).real
      (oneEdgeBox.interiorRestriction ⁻¹' {oneEdgeBox.graph.allOpen})) h
  simp only [FiniteBox.finiteVolumeLaw] at hm
  rw [FiniteBox.conditionalLaw_real_interior_preimage oneEdgeBox (q := 2)
        (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        (fun _ => oneEdgeBox.graph.freeBoundary) oneEdgeBox.closedExterior
        MeasurableSet.of_discrete,
      FiniteBox.conditionalLaw_real_interior_preimage oneEdgeBox (q := 2)
        (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        (fun _ => oneEdgeBox.graph.wiredBoundary) oneEdgeBox.closedExterior
        MeasurableSet.of_discrete] at hm
  rw [Measure.real, Measure.real,
    FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton,
    FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton,
    oneEdge_free_allOpen_mass, oneEdge_wired_allOpen_mass] at hm
  norm_num at hm

/-- **The `q = 1` collapse is sharp at the infinite-volume level**: away from
`q = 1` the FK limit class of a fixed exhaustion can contain two distinct laws.
The witness is the degenerate one-box exhaustion of the two-vertex graph with the
constant free and wired boundary schedules at `q = 2`, `p = 1/2`. -/
theorem exists_two_fkLimits_oneEdge :
    ∃ μ ν : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet),
      μ ∈ FKLimitMeasures oneEdgeExhaustion (q := 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) ∧
      ν ∈ FKLimitMeasures oneEdgeExhaustion (q := 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) ∧ μ ≠ ν := by
  refine ⟨wiredOneEdgeLimit, freeOneEdgeLimit, ⟨fun _ => oneEdgeBox.graph.wiredBoundary,
    isFKLimit_wiredOneEdgeLimit⟩, ⟨fun _ => oneEdgeBox.graph.freeBoundary,
    isFKLimit_freeOneEdgeLimit⟩, ?_⟩
  intro h
  apply finiteVolumeLaw_free_ne_wired_oneEdge
  exact h.symm

end

end FK.InfiniteVolume.QOne
