import FK.AGPackingDensity
import FK.AGUniformSleevePacking
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Positive density of the uniform sleeve packing

This file connects the abstract covering count `density_ncard` to the actual
uniform whole-template sleeve packing of `FK/AGUniformSleevePacking.lean`, using
the line-graph edge metric of the sleeved graph `graph H`.

The two numeric inputs are kept explicit, exactly as in the abstract theorem:

* `hcover`: every edge of `graph H` is within line-graph distance `K` of the
  pivot of some packed device.  On the packing produced by
  `exists_uniform_sleeve_packing` this is its `BoundedDistance` component.
* `hD`: every radius-`K` line-graph ball around a pivot has at most `D` edges.
* `hlin`: the radius-`n` line-graph ball at `f` has at least `n + 1` edges.

Under those, the number of packed devices whose pivot lies in the radius
`n + K` ball is at least `(n + 1)/D`.  Injectivity of the pivot map is not an
extra hypothesis: it is `pivot_injOn_of_uniform_packing`, derived from pairwise
disjointness of the whole translated templates.

This is a density statement for the real bounded-range devices of the sleeve
graph.  It does not assert a strict critical shift, an `hAG` reference law, or
any derivative/limit interchange.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped Sym2 BigOperators ENNReal

namespace FK.AGPackingDensity.PackedSleeve

open FK.AGImplant.Sleeve

variable {V : Type*} [DecidableEq V] (H : SimpleGraph V) [H.LocallyFinite]

/-- The covering hypothesis of `packed_sleeves_density` is exactly the
`BoundedDistance` component of `exists_uniform_sleeve_packing`: every edge of
`graph H` is within line-graph distance `K` of a transported base-bond pivot of
some packed device. -/
lemma cover_of_boundedDistance (gconn : (graph H).Connected)
    [Nonempty (graph H).edgeSet] {e₀ : H.edgeSet}
    {M : Set (H ≃g H)} {K : ℕ}
    (hK : ∀ e : (graph H).edgeSet,
      ∃ p ∈ (fun φ : H ≃g H => (automorphism H φ).mapEdgeSet (baseEdge H e₀)) '' M,
        (graph H).lineGraph.dist e p ≤ K) :
    ∀ g : (graph H).edgeSet, ∃ φ ∈ M,
      (lineMetric (graph H) gconn).dist g ((automorphism H φ).mapEdgeSet (baseEdge H e₀)) ≤ K := by
  intro g
  obtain ⟨p, ⟨φ, hφM, rfl⟩, hp⟩ := hK g
  exact ⟨φ, hφM, hp⟩

/-- **The uniform sleeve packing has positive density `1/D`.**  Every packed
device whose pivot is within line-graph distance `n + K` of `f` is counted by a
`Set.ncard` over the (possibly infinite) automorphism index; no finiteness or
countability of the packing is assumed. -/
theorem packed_sleeves_density
    (S : Finset H.edgeSet) {e₀ : H.edgeSet} (he₀ : e₀ ∈ S)
    [Nonempty (graph H).edgeSet] (gconn : (graph H).Connected)
    {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    {K D : ℕ}
    (hcover : ∀ g : (graph H).edgeSet, ∃ φ ∈ M,
      (lineMetric (graph H) gconn).dist g ((automorphism H φ).mapEdgeSet (baseEdge H e₀)) ≤ K)
    (hD : ∀ φ : M,
      ((lineMetric (graph H) gconn).ball
        ((automorphism H φ.1).mapEdgeSet (baseEdge H e₀)) K).card ≤ D)
    (f : (graph H).edgeSet) (n : ℕ)
    (hlin : n + 1 ≤ ((lineMetric (graph H) gconn).ball f n).card) :
    n + 1 ≤ D * (Set.ncard {φ : M | (lineMetric (graph H) gconn).dist f
      ((automorphism H φ.1).mapEdgeSet (baseEdge H e₀)) ≤ n + K}) := by
  classical
  let p : M → (graph H).edgeSet :=
    fun φ => (automorphism H φ.1).mapEdgeSet (baseEdge H e₀)
  have hinj : Function.Injective p := by
    intro a b hab
    have h := pivot_injOn_of_uniform_packing H S he₀ hM a.2 b.2 hab
    exact Subtype.ext h
  exact density_ncard (lineMetric (graph H) gconn) (p := p) hinj
    (fun g => by
      obtain ⟨φ, hφM, hφ⟩ := hcover g
      exact ⟨⟨φ, hφM⟩, ((lineMetric (graph H) gconn).dist_comm _ g).trans_le hφ⟩)
    (fun i => hD i) f n hlin

end FK.AGPackingDensity.PackedSleeve
