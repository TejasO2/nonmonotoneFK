import FK.NestedAdaptiveCore

/-! # Original big-box and small-restricted laws of the nested adaptive triple -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling FK.FinitePlane FK.RegionSeal
open FK.NestedFinDLR

/-- The first marginal transported back to the original big graph is its actual
finite FK law. -/
theorem nestedAdaptiveTriple_map_fst_original {V : Type*} [Fintype V]
    {G D O : LabelledMultigraph} {eV : V ≃ G.Vertex}
    (e : D.Edge ⊕ O.Edge ≃ G.Edge)
    (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    (nestedAdaptiveTriple e τ ξO (transportBoundary eV e ξ) hq hp₀ hp₁ B e₀).dist.map
      (fun z => G.transportConfig eV e z.1) = G.fkPMF hq hp₁.le ξ := by
  let T := nestedAdaptiveTriple e τ ξO (transportBoundary eV e ξ) hq hp₀ hp₁ B e₀
  have ht := T.map_fst
  exact (PMF.map_comp (fun z : (D.Edge ⊕ O.Edge → Bool) ×
    (D.Edge ⊕ O.Edge → Bool) × (D.Edge ⊕ O.Edge → Bool) => z.1) T.dist
    (G.transportConfig eV e)).symm.trans
      ((congrArg (PMF.map (G.transportConfig eV e)) ht).trans
        (map_transport_fkPMF G eV e ξ hq hp₁.le))

/-- The second marginal restricted to the small edge type is exactly the
small-box FK law. -/
theorem nestedAdaptiveTriple_map_snd_restrict_left {V : Type*} [Fintype V]
    {G D O : LabelledMultigraph} {eV : V ≃ G.Vertex}
    (e : D.Edge ⊕ O.Edge ≃ G.Edge)
    (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    (nestedAdaptiveTriple e τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
      (fun z => z.2.1 ∘ Sum.inl) = D.fkPMF hq hp₁.le τ := by
  let T := nestedAdaptiveTriple e τ ξO ξ hq hp₀ hp₁ B e₀
  have ht := T.map_snd
  exact (PMF.map_comp (fun z : (D.Edge ⊕ O.Edge → Bool) ×
    (D.Edge ⊕ O.Edge → Bool) × (D.Edge ⊕ O.Edge → Bool) => z.2.1) T.dist
    (fun ω => ω ∘ Sum.inl)).symm.trans
      ((congrArg (PMF.map (fun ω : D.Edge ⊕ O.Edge → Bool => ω ∘ Sum.inl)) ht).trans
        (productJoinLaw_map_left _ _))

/-- Transport of a Bernoulli product back to the original big graph is the
original Bernoulli product. -/
theorem map_nested_bernoulli {V : Type*} [Fintype V]
    {G D O : LabelledMultigraph} {eV : V ≃ G.Vertex}
    (e : D.Edge ⊕ O.Edge ≃ G.Edge) {r : NNReal} (hr : r ≤ 1) :
    ((nestedBig (eV := eV) e).bernoulliProductPMF hr).map (G.transportConfig eV e) =
      G.bernoulliProductPMF hr := by
  apply PMF.ext
  intro ω
  rw [pmf_map_equiv_apply]
  rw [(nestedBig (eV := eV) e).bernoulliProductPMF_apply,
    G.bernoulliProductPMF_apply]
  have hw := G.edgeWeight_transport eV e r ((G.transportConfig eV e).symm ω)
  simpa using hw.symm

/-- The third marginal transported back to the original big graph is the actual
upper Bernoulli product. -/
theorem nestedAdaptiveTriple_map_thd_original {V : Type*} [Fintype V]
    {G D O : LabelledMultigraph} {eV : V ≃ G.Vertex}
    (e : D.Edge ⊕ O.Edge ≃ G.Edge)
    (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : (nestedBig (eV := eV) e).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    (nestedAdaptiveTriple e τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
      (fun z => G.transportConfig eV e z.2.2) =
      G.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le := by
  let T := nestedAdaptiveTriple e τ ξO ξ hq hp₀ hp₁ B e₀
  have ht := T.map_thd
  exact (PMF.map_comp (fun z : (D.Edge ⊕ O.Edge → Bool) ×
    (D.Edge ⊕ O.Edge → Bool) × (D.Edge ⊕ O.Edge → Bool) => z.2.2) T.dist
    (G.transportConfig eV e)).symm.trans
      ((congrArg (PMF.map (G.transportConfig eV e)) ht).trans
        (map_nested_bernoulli e (upperRateNN_lt_one hq hp₀ hp₁).le))

end FK.Adaptive
