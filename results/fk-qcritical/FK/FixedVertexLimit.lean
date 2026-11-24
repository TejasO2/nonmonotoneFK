import FK.MonotoneLimitExistence
import FK.StageLawUpTBound

open Filter MeasureTheory Set
set_option linter.unusedSectionVars false
namespace FK.InfiniteVolume
variable {E V : Type} [Countable E] [Fintype V] [DecidableEq V] [DecidableEq E]

/-- **Genuine infinite-volume weak limits on a covering fixed-vertex family.**
For a covering nested family of edge sets on one finite vertex set, at `1 ≤ q`,
`0 < p < 1` and any fixed boundary partition `ξ`, the finite-volume FK laws with
constant boundary `ξ` converge weakly; the case `ξ = ⊥` is the free boundary. -/
theorem exists_isFKLimit_fixedVertexFamily
    (F : FK.InfiniteVolume.NoEscape.FixedVertexFamily E V) (hcov : ∀ e : E, ∃ n, e ∈ F.edges n)
    {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1) (ξ : Setoid V) :
    ∃ φ : ProbabilityMeasure (Configuration E),
      IsFKLimit ⟨F.box, F.monotone, hcov⟩ (lt_of_lt_of_le zero_lt_one hq) hp1.le
        (fun n => ξ) φ := by
  refine exists_isFKLimit_of_eventually_mono_upT ⟨F.box, F.monotone, hcov⟩
    (lt_of_lt_of_le zero_lt_one hq) hp1.le (fun n => ξ) ?_
  intro S T
  exact fixedVertexFamily_eventually_mono_upT F hcov hq hp0 hp1 ξ S T

#print axioms FK.InfiniteVolume.exists_isFKLimit_fixedVertexFamily
end FK.InfiniteVolume
