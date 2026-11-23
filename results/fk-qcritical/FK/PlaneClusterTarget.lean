import FK.ConventionTransport

/-!
# The still-unproved deterministic plane-cluster target

This file records the exact remaining proposition using the repository's
actual global `SimpleGraph` percolation relations. It is a definition, not a
proof, an axiom, or an existence certificate.
-/

namespace FK.Planar

open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

/-- Every open component of the global graph is finite. -/
def NoInfiniteOpenCluster {V : Type*} (G : SimpleGraph V)
    (ω : G.edgeSet → Bool) : Prop :=
  ∀ x, {y | OpenConnected G ω Set.univ x y}.Finite

lemma noInfiniteOpenCluster_iff {V : Type*} (G : SimpleGraph V)
    (ω : G.edgeSet → Bool) :
    NoInfiniteOpenCluster G ω ↔ ∀ x, ¬ ExteriorInfiniteCluster G ω Set.univ x := by
  constructor
  · intro h x hx
    exact hx (h x)
  · intro h x
    by_contra hn
    exact h x hn

/-- **Unproved target.** For a genuine plane-dual pair with matching edge
labels, absence of an infinite dual-open cluster for the complementary
configuration must imply at most one infinite primal-open cluster. This
predicate is intentionally not paired with a theorem asserting it. -/
def DualNonpercolationForcesPrimalAtMostOne {V F : Type*}
    (G : SimpleGraph V) (GD : SimpleGraph F)
    (edge : G.edgeSet ≃ GD.edgeSet) : Prop :=
  ∀ ω : G.edgeSet → Bool,
    NoInfiniteOpenCluster GD (dualConfig edge ω) → GlobalAtMostOne G ω

end FK.Planar
