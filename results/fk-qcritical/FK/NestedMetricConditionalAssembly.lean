import FK.NestedMetricGeometry
import FK.NestedConditionalAssembly

/-!
# Metric-scale input for nested conditional assembly

This file specializes the pairwise finite-volume interface of
`NestedConditionalAssembly` to the canonical centered metric exhaustion.  For
a cylinder base `J`, both scale maps are `n ↦ 2 * n`.  Once
`n ≥ dataWidth G o J (roots J)`, the finite metric estimate applies at
`m = 2 * n - dataWidth G o J (roots J)`, with both boxes at radius `2 * n`.
Antitonicity of `farConnection` then gives exactly the required arm bound.

The theorems are conditional reductions for this fixed centered exhaustion and
fixed boundary-assignment class.  The common-upper good-intersection identity
is an explicit premise.  In the first theorem the complement inclusion is also
explicit; the second obtains it from an actual maximal-split certificate.
Neither theorem is a proof of general strong uniqueness.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory SimpleGraph Sym2

namespace FK.InfiniteVolume.NestedMetricGeometry

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedAssembly
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata

universe u uU uK

variable {V : Type u} {G : SimpleGraph V}

/-- Fixed-class DLR uniqueness on the centered metric exhaustion, from the
actual diagonal metric finite-volume comparison.  Only the diagonal case
`r = m + dataWidth` of the nested estimate is needed.  Conditional assembly
uses the uniform scale map `n ↦ 2 * n` for both exterior laws; for each fixed
cylinder base, the smaller-scale parameter is eventually `2 * n - dataWidth`.
-/
theorem eq_dlr_metricBox_of_diagonal_nested_good
    [Countable V] [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures (metricBoxExhaustion hG o) Φ hq hp₁.le)
    (hν : ν ∈ DLRMeasures (metricBoxExhaustion hG o) Φ hq hp₁.le)
    (hzero : ∀ x, percolationProb G x
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)) = 0)
    (roots : Finset G.edgeSet → Finset V)
    (C : ∀ (J : Finset G.edgeSet) (m : ℕ),
      Set ((metricBox hG o (m + dataWidth G o J (roots J))).indexedGraph
        (edgeIndex _)).Configuration)
    (hgood : ∀ (J : Finset G.edgeSet) (S : Set (J → Bool)) (m : ℕ)
      (ω ξ : Configuration G.edgeSet),
      let r := m + dataWidth G o J (roots J)
      let t := metricNestedTriple hG o (le_refl r)
        (Φ.partition r (FKLimit.exteriorRestriction (metricBox hG o r).edges ω))
        (Φ.partition r (FKLimit.exteriorRestriction (metricBox hG o r).edges ξ))
        hq hp₀ hp₁
      let BS := metricBox hG o r
      let e := metricNestedEquiv hG o (le_refl r)
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_smaller_metricBox hG o J (roots J) m)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C J m)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_smaller_metricBox hG o J (roots J) m)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C J m)))
    (hD : ∀ (J : Finset G.edgeSet) (m : ℕ),
      let r := m + dataWidth G o J (roots J)
      let BS := metricBox hG o r
      let e := metricNestedEquiv hG o (le_refl r)
      (restrictΔ e ⁻¹' C J m)ᶜ ⊆ BS.reindex (edgeIndex BS) ⁻¹'
        closedLocalEvent BS
          (NestedAssembly.farConnection G (roots J) o
            (m + dataWidth G o J (roots J)))) :
    μ = ν := by
  apply eq_dlr_of_pairwise_finiteVolume_farConnection
    hG (metricBoxExhaustion hG o) Φ hq hp₁.le μ ν hμ hν
    (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))
    (NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero _ hzero)
    roots (fun _ => o) (fun J => dataWidth G o J (roots J))
    (fun J a ha => dist_le_dataWidth G o J ha)
  intro κ ξ _ _
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  refine ⟨fun n => 2 * n, fun n => 2 * n, htwo, htwo, ?_⟩
  intro J S
  apply Eventually.of_forall
  intro z
  filter_upwards [eventually_ge_atTop (dataWidth G o J (roots J))] with n hn
  let w := dataWidth G o J (roots J)
  let m := 2 * n - w
  have hnw : w ≤ 2 * n := by
    dsimp [w]
    omega
  have hnm : n ≤ m := by
    dsimp [m, w]
    omega
  have h := metricBox_cylinder_abs_sub_le_farConnection_of_good_of_le
    hG o hq hp₀ hp₁ J S (roots J) m (m + w) (le_refl _)
    (Φ.partition (m + w)
      (FKLimit.exteriorRestriction (metricBox hG o (m + w)).edges z.1))
    (Φ.partition (m + w)
      (FKLimit.exteriorRestriction (metricBox hG o (m + w)).edges z.2))
    (C J m) (hgood J S m z.1 z.2) (hD J m)
  have hmono := measureReal_mono
    ((NestedAssembly.farConnection_add_antitone (roots J) o w) hnm)
    (measure_ne_top (percolation G
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))) _)
  dsimp only [m, w] at h hmono
  have hr : 2 * n - dataWidth G o J (roots J) + dataWidth G o J (roots J) = 2 * n :=
    Nat.sub_add_cancel hnw
  rw [hr] at h hmono
  exact h.trans hmono

/-- The maximal-split version of `eq_dlr_metricBox_of_diagonal_nested_good`.
At every cylinder base `J` and scale `m`, the smaller indexed graph has an
actual finite split presentation.  The vertex map sends every left vertex into
`roots J`, every right vertex beyond the smaller metric radius, and every split
edge to the prescribed global edge.  These data prove `hD`; only the
common-upper good-intersection identity remains stochastic input. -/
theorem eq_dlr_metricBox_of_diagonal_maximalSplit_good
    [Countable V] [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures (metricBoxExhaustion hG o) Φ hq hp₁.le)
    (hν : ν ∈ DLRMeasures (metricBoxExhaustion hG o) Φ hq hp₁.le)
    (hzero : ∀ x, percolationProb G x
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)) = 0)
    (roots : Finset G.edgeSet → Finset V)
    (C : ∀ (J : Finset G.edgeSet) (m : ℕ),
      Set ((metricBox hG o (m + dataWidth G o J (roots J))).indexedGraph
        (edgeIndex _)).Configuration)
    (mI kO : Finset G.edgeSet → ℕ → ℕ)
    (U : Finset G.edgeSet → ℕ → Type uU)
    (K : Finset G.edgeSet → ℕ → Type uK)
    [∀ J m, Fintype (U J m)] [∀ J m, Fintype (K J m)]
    (si : ∀ J m, Fin (mI J m) → U J m)
    (ti : ∀ J m, Fin (mI J m) → U J m)
    (so xo : ∀ J m, Fin (kO J m) → U J m ⊕ K J m)
    (d : ∀ (J : Finset G.edgeSet) (m : ℕ),
      (Fin (mI J m) ⊕ Fin (kO J m)) ≃
        Fin (Fintype.card (metricBox hG o
          (m + dataWidth G o J (roots J))).edges))
    (hC : ∀ (J : Finset G.edgeSet) (m : ℕ),
      let BD := metricBox hG o (m + dataWidth G o J (roots J))
      C J m = (fun ρ : (BD.indexedGraph (edgeIndex BD)).Configuration =>
        ρ ∘ d J m) ⁻¹' maximalSplitStratum (si J m) (ti J m) (so J m) (xo J m))
    (f : ∀ J m, U J m ⊕ K J m → V)
    (hend : ∀ (J : Finset G.edgeSet) (m : ℕ)
      (a : (ambientOfSum (splitSource (si J m) (so J m))
        (splitTarget (ti J m) (xo J m))).Edge),
      s(f J m ((ambientOfSum (splitSource (si J m) (so J m))
          (splitTarget (ti J m) (xo J m))).source a),
        f J m ((ambientOfSum (splitSource (si J m) (so J m))
          (splitTarget (ti J m) (xo J m))).target a)) =
        (((edgeIndex (metricBox hG o (m + dataWidth G o J (roots J))))
          (d J m a)).1).1)
    (hleft : ∀ J m u, f J m (Sum.inl u) ∈ roots J)
    (hfar : ∀ J m k, m + dataWidth G o J (roots J) ≤ G.dist o (f J m (Sum.inr k)))
    (hgood : ∀ (J : Finset G.edgeSet) (S : Set (J → Bool)) (m : ℕ)
      (ω ξ : Configuration G.edgeSet),
      let r := m + dataWidth G o J (roots J)
      let t := metricNestedTriple hG o (le_refl r)
        (Φ.partition r (FKLimit.exteriorRestriction (metricBox hG o r).edges ω))
        (Φ.partition r (FKLimit.exteriorRestriction (metricBox hG o r).edges ξ))
        hq hp₀ hp₁
      let BS := metricBox hG o r
      let e := metricNestedEquiv hG o (le_refl r)
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_smaller_metricBox hG o J (roots J) m)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C J m)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (base_subset_smaller_metricBox hG o J (roots J) m)) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C J m))) :
    μ = ν := by
  apply eq_dlr_metricBox_of_diagonal_nested_good
    hG o hq hp₀ hp₁ Φ μ ν hμ hν hzero roots C hgood
  intro J m
  dsimp only
  rw [hC J m]
  exact OpenPathGeometry.bad_maximalSplit_subset_closedLocalEvent
    (metricBox hG o (m + dataWidth G o J (roots J)))
    (metricBox hG o (m + dataWidth G o J (roots J)))
    (edgeIndex _) (edgeIndex _)
    (nested_metricBox_edges hG o (le_refl _))
    (si J m) (ti J m) (so J m) (xo J m) (d J m) (f J m) (hend J m)
    (roots J) o (m + dataWidth G o J (roots J)) (hleft J m) (hfar J m)

end FK.InfiniteVolume.NestedMetricGeometry

#print axioms FK.InfiniteVolume.NestedMetricGeometry.eq_dlr_metricBox_of_diagonal_nested_good
#print axioms FK.InfiniteVolume.NestedMetricGeometry.eq_dlr_metricBox_of_diagonal_maximalSplit_good
