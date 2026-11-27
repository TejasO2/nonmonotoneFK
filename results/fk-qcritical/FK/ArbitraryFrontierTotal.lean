import FK.ComparableNonpercolating

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

noncomputable section

namespace FK.ArbitraryFrontierTotal

open FK.InfiniteVolume FK.RandomClosedBoundary FK.SourceRegions
open FK.ComparableNonpercolating
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The unit-total part of the finite-base DLR stratum identity, stated for an
arbitrary probability law. No DLR identity for the law is included. -/
def HasUnitStratumTotals {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)) : Prop :=
  ∀ (T : Set V), T.Finite →
    ∑' s : Finset V, stratumTerm (G := G) hq hp ρ T s = 1

/-- A unit-stratum-total upper law has exactly the same frontier masses as
every canonical DLR law that it dominates. -/
theorem frontier_mass_eq_of_unitStratumTotals_of_stochasticallyDominates
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hdom : FKLimit.StochasticallyDominates ρ μ)
    (hρsum : HasUnitStratumTotals (G := G) hq hp ρ) (s : Finset V) :
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) =
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure ρ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) := by
  let f := stratumTerm (G := G) hq hp ρ (s : Set V)
  let g := stratumTerm (G := G) hq hp μ (s : Set V)
  have hle : ∀ t : Finset V, f t ≤ g t := by
    intro t
    by_cases hst : (s : Set V) ⊆ (t : Set V)
    · simp only [f, g, stratumTerm, dif_pos hst]
      exact mul_le_mul_of_nonneg_right
        (exterior_frontier_le_of_stochasticallyDominates (G := G) hdom
          (t : Set V) t.finite_toSet) (by simp)
    · simp only [f, g, stratumTerm, dif_neg hst, le_refl]
  have hsum : ∑' t : Finset V, f t = ∑' t : Finset V, g t := by
    rw [hρsum (s : Set V) s.finite_toSet,
      tsum_stratumTerm_eq_one (G := G) hq hp μ hμ hμfin s.finite_toSet]
  have htop : ∑' t : Finset V, f t ≠ ∞ := by
    rw [hρsum (s : Set V) s.finite_toSet]
    exact ENNReal.one_ne_top
  have hterm := eq_of_le_of_tsum_eq_tsum_ne_top htop hle hsum s
  dsimp [f, g] at hterm
  rw [stratumTerm_base_self, stratumTerm_base_self] at hterm
  exact hterm.symm

/-- Two canonical DLR laws dominated by one unit-stratum-total law are equal.
The upper law is not assumed to be DLR. -/
theorem eq_of_unitStratumTotals_of_stochasticallyDominates
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hν : CanonicalRegionDLR (G := G) hq hp ν)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hνfin : FiniteRegionOnFiniteBases (G := G) ν)
    (hρμ : FKLimit.StochasticallyDominates ρ μ)
    (hρν : FKLimit.StochasticallyDominates ρ ν)
    (hρsum : HasUnitStratumTotals (G := G) hq hp ρ) : μ = ν := by
  apply eq_of_canonicalRegionDLR_of_frontier_mass_eq (G := G) hq hp μ ν hμ hν hμfin hνfin
  intro s
  exact (frontier_mass_eq_of_unitStratumTotals_of_stochasticallyDominates
    (G := G) hq hp μ ρ hμ hμfin hρμ hρsum s).trans
    (frontier_mass_eq_of_unitStratumTotals_of_stochasticallyDominates
      (G := G) hq hp ν ρ hν hνfin hρν hρsum s).symm

/-- Source-convention form, with nonpercolation of the lower laws supplied
explicitly. -/
theorem eq_of_sourceDLR_of_unitStratumTotals_of_stochasticallyDominates
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ ν ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) (hν : ν ∈ SourceDLRMeasures Φ)
    (hμnp : ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hνnp : ∀ᵐ ω ∂(ν : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hρμ : FKLimit.StochasticallyDominates ρ μ)
    (hρν : FKLimit.StochasticallyDominates ρ ν)
    (hρsum : HasUnitStratumTotals (G := G) hq hp ρ) : μ = ν := by
  apply eq_of_unitStratumTotals_of_stochasticallyDominates (G := G) hq hp μ ν ρ
  · exact canonicalRegionDLR_of_sourceDLR_of_ae_nonPercolating hq hp Φ hΦ μ hμ hμnp
  · exact canonicalRegionDLR_of_sourceDLR_of_ae_nonPercolating hq hp Φ hΦ ν hν hνnp
  · exact finiteRegionOnFiniteBases_of_ae_nonPercolating μ hμnp
  · exact finiteRegionOnFiniteBases_of_ae_nonPercolating ν hνnp
  · exact hρμ
  · exact hρν
  · exact hρsum

/-- Nonpercolation passes from an upper law to a dominated lower law through
the existing countable ordered-coupling theorem. -/
theorem ae_nonPercolating_of_stochasticallyDominates (hG : G.Connected)
    {μ ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)}
    (hdom : FKLimit.StochasticallyDominates ρ μ)
    (hρnp : ∀ᵐ ω ∂(ρ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G := by
  obtain ⟨γ, hγμ, hγρ, hγord⟩ :=
    FKLimit.exists_orderedCoupling_of_stochasticallyDominates hdom
  apply FK.ae_nonPercolating_of_orderedCoupling G hG (γ := (γ : Measure _))
    (μ := (μ : Measure _)) (ρ := (ρ : Measure _))
  · exact congrArg Subtype.val hγμ
  · exact congrArg Subtype.val hγρ
  · exact hγord
  · exact hρnp

/-- Exact arbitrary-upper source form after adding only the unit-stratum-total
condition to the nonpercolating-dominant hypotheses. -/
theorem eq_of_sourceDLR_of_nonPercolating_unitStratumTotals_dominant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ) (hG : G.Connected)
    (μ ν ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) (hν : ν ∈ SourceDLRMeasures Φ)
    (hρnp : ∀ᵐ ω ∂(ρ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hρμ : FKLimit.StochasticallyDominates ρ μ)
    (hρν : FKLimit.StochasticallyDominates ρ ν)
    (hρsum : HasUnitStratumTotals (G := G) hq hp ρ) : μ = ν := by
  apply eq_of_sourceDLR_of_unitStratumTotals_of_stochasticallyDominates
    (G := G) hq hp Φ hΦ μ ν ρ hμ hν
  · exact ae_nonPercolating_of_stochasticallyDominates hG hρμ hρnp
  · exact ae_nonPercolating_of_stochasticallyDominates hG hρν hρnp
  · exact hρμ
  · exact hρν
  · exact hρsum

end FK.ArbitraryFrontierTotal
