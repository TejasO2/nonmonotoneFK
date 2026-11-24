import FK.ReferenceBaseline
import FK.SubcriticalBaseline

/-!
# The reference baseline for the actual AG percolation event

`FK.ReferenceBaseline` proves the ordinary Bernoulli supercritical dichotomy
for `ClusterCover.HasInfiniteCluster`. `FK.SubcriticalBaseline` identifies that
event with `FK.EssentialWindow.Percolating G`. This module records the resulting
baseline in the exact event presentation used by the reference windows.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

namespace FK.ReferenceBaseline

open CurvatureVariance.Infra.Percolation FK.ClusterCover

variable {V : Type*} [Countable V]

/-- Above the reference critical parameter, the actual AG percolation event has
full mass for the ordinary Bernoulli bond law. No connectivity is needed: the
root critical definition and product-space zero-one law are enough. -/
theorem percolation_percolating_eq_one (G : SimpleGraph V) (o : V)
    {p : I} (hp : criticalProb G o < (p : ℝ)) :
    percolation G p (FK.EssentialWindow.Percolating G) = 1 := by
  rw [FK.PercolationRoot.percolating_eq_hasInfiniteCluster G]
  exact percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt G o hp

/-- The supercritical reference baseline for `Percolating G`, including boosted
enhanced edges. The unenhanced base already has full mass, and increasing the
clean product weights preserves it for the increasing percolation event. -/
theorem incMass_percolating_eq_one (G : SimpleGraph V) (o : V)
    (S : Set G.edgeSet) {a ε : ℝ} (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε)
    (haε1 : a + ε ≤ 1) (hpc : criticalProb G o < a) :
    FK.AGDifferentialShift.incMass (FK.EssentialWindow.Percolating G) S a ε = 1 := by
  rw [FK.PercolationRoot.percolating_eq_hasInfiniteCluster G]
  exact incMass_hasInfiniteCluster_eq_one_of_nonneg G o S ha0 hε0 haε1 hpc

end FK.ReferenceBaseline

#print axioms FK.ReferenceBaseline.percolation_percolating_eq_one
#print axioms FK.ReferenceBaseline.incMass_percolating_eq_one
