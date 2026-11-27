import FK.GenericNestedGood

open scoped ENNReal NNReal BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling

namespace FK.NestedRegionExploration

/-- The public finite FK nested triple is definitionally the explicit glue of
its first/upper and smaller/upper ordered couplings. -/
theorem fkNestedOrderedTriple_eq_nestedOrderedTriple
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    let cS : PMF.OrderedCoupling
        ((finIndexedGraph VS nS sS tS).fkPMF hq hp₁.le ξ)
        (splitLaw e
          ((finIndexedGraph VD nD sD tD).bernoulliProductPMF
            (upperRateNN_le_one hq hp₁.le))
          (GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))) := by
      rw [splitLaw_bernoulliProductPMF e (upperRateNN_le_one hq hp₁.le)]
      exact fkUpperOrderedCoupling sS tS ξ hq hp₀ hp₁
    fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁ =
      nestedOrderedTriple e cS (fkUpperOrderedCoupling sD tD τ hq hp₀ hp₁) := by
  intro cS
  rfl

end FK.NestedRegionExploration
