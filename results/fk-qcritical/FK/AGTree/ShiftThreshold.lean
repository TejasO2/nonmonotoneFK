import FK.AGTree.BaseNonpercolation

/-!
# A strict percolation phase transition on the two-class tree

`TreeBaseNonpercolation` proves that the two-class tree bond law has no infinite open cluster
as soon as the class-`1` rate is zero and `3 r₀ < 1`.  The existing development
(`FK/AGTree/Shift.lean`) proves that at base rate `3/10` with independent activation at rate
`1/2` the root lies in an infinite forward cluster with positive probability.  Combining the
two through the open-percolation interface `TreeInterface` gives a genuine strict phase
transition for the *same* graph and the *same* percolation event (existence of an infinite
open cluster), not merely a nonzero forward-cluster probability:

* `base_nonpercolation`: the base law `(3/10, 0)` has percolation probability zero;
* `activated_percolation`: the activated law `(3/10, 1/2)` has positive percolation
  probability;
* `strict_critical_shift`: `0 = ℙ_{(3/10,0)}(percolation) < ℙ_{(3/10,1/2)}(percolation)`.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

/-- The percolation event: some vertex lies in an infinite open cluster. -/
def Perc (ω : G.edgeSet → Bool) : Prop := ∃ u : V, InfiniteClusterAt ω u

/-! ### The base law -/

/-- The base law `(3/10, 0)` has no open class-`1` edges. -/
theorem base_rate_one : ((enhRate p0 0) 1 : ℝ) = 0 := by
  simp [enhRate]

/-- The base law `(3/10, 0)` satisfies the subcritical hypothesis `3 r₀ < 1`. -/
theorem base_threshold : 3 * (((enhRate p0 0) 0 : unitInterval) : ℝ) < 1 := by
  simp only [enhRate, if_pos (rfl : (0 : Fin 2) = 0), p0]
  norm_num

/-- **Base nonpercolation at rate `3/10`.** -/
theorem base_nonpercolation : pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} = 0 :=
  pr_percolation_zero (enhRate p0 0) base_rate_one base_threshold

/-- Almost surely all open clusters of the base law are finite. -/
theorem base_ae_finite : ∀ᵐ ω ∂(law (enhRate p0 0)), ∀ u : V, FiniteClusterAt ω u :=
  ae_finite_clusters (enhRate p0 0) base_rate_one base_threshold

/-! ### The activated law -/

/-- **Activated percolation at rates `(3/10, 1/2)`**, transferred from the positive forward
cluster of `enh_cluster_pos` through the open-percolation interface. -/
theorem activated_percolation : 0 < pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} := by
  have hmono : pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Cluster ω V.root} ≤
      pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} :=
    pr_mono _ (fun ω hω => ⟨V.root, cluster_infinite hω⟩)
  linarith [enh_cluster_pos]

/-- **The strict phase transition**: the percolation probability of the activated law exceeds
that of the base law on the same graph. -/
theorem strict_critical_shift :
    pr (enhRate p0 0) {ω : G.edgeSet → Bool | Perc ω} <
      pr (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} := by
  rw [base_nonpercolation]
  exact activated_percolation

/-- The activated law's infinite-cluster event has positive measure. -/
theorem activated_percolation_measure :
    0 < law (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} := by
  have hpos : 0 < (law (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω}).toReal := by
    have h := activated_percolation
    rwa [pr, measureReal_def] at h
  by_contra hle
  push_neg at hle
  have hzero : law (enhRate p0 s0) {ω : G.edgeSet → Bool | Perc ω} = 0 :=
    le_antisymm hle zero_le
  rw [hzero] at hpos
  simp at hpos

end Ultra
