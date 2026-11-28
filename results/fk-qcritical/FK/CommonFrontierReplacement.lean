import FK.DominatedSourceCompactness

/-!
# Exact replacement criteria for arbitrary-dominant uniqueness

This module isolates what a compactness or barycentre argument would have to
produce in order to prove equality of two nonpercolating canonical-region DLR
laws. It proves two exact equivalences:

* a common source-DLR upper law for the two candidates exists if and only if
  the candidates are equal;
* a common canonical-DLR lower bound on all closed-frontier masses exists if
  and only if the candidates are equal.

No arbitrary-dominant uniqueness theorem is asserted. In particular, the
construction of either replacement from an arbitrary non-DLR dominant remains
an external input, logically equivalent to the pairwise equality itself.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

noncomputable section

namespace FK.CommonFrontierReplacement

open FK.InfiniteVolume FK.RandomClosedBoundary FK.SourceRegions
open FK.ComparableNonpercolating
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- If one canonical DLR law has smaller closed-frontier masses than another,
pointwise order and the two unit stratum totals force every corresponding
frontier mass to agree. No stochastic order between the global laws is needed. -/
theorem frontier_mass_eq_of_frontier_mass_le
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ κ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hκ : CanonicalRegionDLR (G := G) hq hp κ)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hκfin : FiniteRegionOnFiniteBases (G := G) κ)
    (hmass : ∀ s : Finset V,
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet) ≤
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure κ :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet)) (s : Finset V) :
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) =
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure κ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) := by
  let f := stratumTerm (G := G) hq hp μ (s : Set V)
  let g := stratumTerm (G := G) hq hp κ (s : Set V)
  have hle : ∀ t : Finset V, f t ≤ g t := by
    intro t
    by_cases hst : (s : Set V) ⊆ (t : Set V)
    · simp only [f, g, stratumTerm, dif_pos hst]
      exact mul_le_mul_of_nonneg_right (hmass t) (by simp)
    · simp only [f, g, stratumTerm, dif_neg hst, le_refl]
  have hsum : ∑' t : Finset V, f t = ∑' t : Finset V, g t := by
    rw [tsum_stratumTerm_eq_one (G := G) hq hp μ hμ hμfin s.finite_toSet,
      tsum_stratumTerm_eq_one (G := G) hq hp κ hκ hκfin s.finite_toSet]
  have htop : ∑' t : Finset V, f t ≠ ∞ := by
    rw [tsum_stratumTerm_eq_one (G := G) hq hp μ hμ hμfin s.finite_toSet]
    exact ENNReal.one_ne_top
  have hterm := eq_of_le_of_tsum_eq_tsum_ne_top htop hle hsum s
  dsimp [f, g] at hterm
  rw [stratumTerm_base_self, stratumTerm_base_self] at hterm
  exact hterm

/-- Frontier-mass minorisation between canonical nonpercolating DLR laws is
already an equality criterion. -/
theorem eq_of_frontier_mass_le
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ κ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hκ : CanonicalRegionDLR (G := G) hq hp κ)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hκfin : FiniteRegionOnFiniteBases (G := G) κ)
    (hmass : ∀ s : Finset V,
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet) ≤
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure κ :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet)) : μ = κ := by
  apply eq_of_canonicalRegionDLR_of_frontier_mass_eq (G := G) hq hp μ κ hμ hκ hμfin hκfin
  exact frontier_mass_eq_of_frontier_mass_le (G := G) hq hp μ κ hμ hκ hμfin hκfin hmass

/-- Exact common-frontier-minorant criterion. Producing another canonical DLR
law `κ` with finite-base regions and with frontier masses below those of both
`μ` and `ν` is equivalent to proving `μ = ν`. -/
theorem eq_iff_exists_common_frontier_minorant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hν : CanonicalRegionDLR (G := G) hq hp ν)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hνfin : FiniteRegionOnFiniteBases (G := G) ν) :
    (∃ κ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet),
      CanonicalRegionDLR (G := G) hq hp κ ∧
      FiniteRegionOnFiniteBases (G := G) κ ∧
      ∀ s : Finset V,
        ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure κ :
          Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
          (frontierExterior (G := G) (s : Set V) s.finite_toSet) ≤
        ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
          Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
          (frontierExterior (G := G) (s : Set V) s.finite_toSet) ∧
        ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure κ :
          Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
          (frontierExterior (G := G) (s : Set V) s.finite_toSet) ≤
        ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure ν :
          Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
          (frontierExterior (G := G) (s : Set V) s.finite_toSet)) ↔ μ = ν := by
  constructor
  · rintro ⟨κ, hκ, hκfin, hmass⟩
    have hκμ : κ = μ := eq_of_frontier_mass_le (G := G) hq hp κ μ hκ hμ hκfin hμfin
      (fun s => (hmass s).1)
    have hκν : κ = ν := eq_of_frontier_mass_le (G := G) hq hp κ ν hκ hν hκfin hνfin
      (fun s => (hmass s).2)
    exact hκμ.symm.trans hκν
  · intro h
    subst ν
    exact ⟨μ, hμ, hμfin, fun s => ⟨le_rfl, le_rfl⟩⟩

/-- Exact common-DLR-upper criterion for one geometric source convention. A
source-DLR law above both nonpercolating candidates exists precisely when the
candidates coincide. -/
theorem eq_iff_exists_common_sourceDLR_dominant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ ν : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) (hν : ν ∈ SourceDLRMeasures Φ)
    (hμnp : ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hνnp : ∀ᵐ ω ∂(ν : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    (∃ κ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet),
      κ ∈ SourceDLRMeasures Φ ∧
      (∀ᵐ ω ∂(κ : Measure (FKLimit.Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G) ∧
      FKLimit.StochasticallyDominates κ μ ∧
      FKLimit.StochasticallyDominates κ ν) ↔ μ = ν := by
  constructor
  · rintro ⟨κ, hκ, hκnp, hκμ, hκν⟩
    have hμκ : μ = κ :=
      eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating hq hp Φ hΦ
        μ κ hμ hκ hμnp hκnp hκμ
    have hνκ : ν = κ :=
      eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating hq hp Φ hΦ
        ν κ hν hκ hνnp hκnp hκν
    exact hμκ.trans hνκ.symm
  · intro h
    subst ν
    exact ⟨μ, hμ, hμnp, (fun _ _ _ => le_rfl), (fun _ _ _ => le_rfl)⟩

/-- The same criterion with the exact arbitrary-upper hypotheses of Theorem
5.1. The upper law `ρ` is not assumed to be DLR or to have unit stratum
totals. Downward nonpercolation is supplied by the accepted ordered-kernel
theorem. This equivalence is only an obstruction diagnosis: no construction of
the displayed common DLR upper law from `ρ` is claimed. -/
theorem eq_iff_exists_common_sourceDLR_dominant_of_nonPercolating_upper
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ ν ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) (hν : ν ∈ SourceDLRMeasures Φ)
    (hρnp : ∀ᵐ ω ∂(ρ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hρμ : FKLimit.StochasticallyDominates ρ μ)
    (hρν : FKLimit.StochasticallyDominates ρ ν) :
    (∃ κ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet),
      κ ∈ SourceDLRMeasures Φ ∧
      (∀ᵐ ω ∂(κ : Measure (FKLimit.Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G) ∧
      FKLimit.StochasticallyDominates κ μ ∧
      FKLimit.StochasticallyDominates κ ν) ↔ μ = ν := by
  apply eq_iff_exists_common_sourceDLR_dominant (G := G) hq hp Φ hΦ μ ν hμ hν
  · exact FKLimit.ae_nonPercolating_of_stochasticallyDominates G hρμ hρnp
  · exact FKLimit.ae_nonPercolating_of_stochasticallyDominates G hρν hρnp

end FK.CommonFrontierReplacement

#print axioms FK.CommonFrontierReplacement.frontier_mass_eq_of_frontier_mass_le
#print axioms FK.CommonFrontierReplacement.eq_of_frontier_mass_le
#print axioms FK.CommonFrontierReplacement.eq_iff_exists_common_frontier_minorant
#print axioms FK.CommonFrontierReplacement.eq_iff_exists_common_sourceDLR_dominant
#print axioms FK.CommonFrontierReplacement.eq_iff_exists_common_sourceDLR_dominant_of_nonPercolating_upper
