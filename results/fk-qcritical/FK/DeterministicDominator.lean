import FK.SourceUniqueness
import FK.SourceConventionFree

/-!
# Uniqueness under a deterministic nonpercolating dominant

A fixed configuration with finite open clusters determines an adaptive closed
frontier exhaustion. Consequently the closed-frontier uniqueness mechanism
applies without any ordered-coupling or random-fibre argument. This covers
nonpercolating configurations having infinitely many open edges, including ones
for which no boundary of a prescribed interval exhaustion is ever closed.

The result is deliberately scoped to a `Measure.dirac` dominant. It is not the
general Theorem 5.1 domination statement.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory

noncomputable section

namespace FK.SourceUniqueness.DeterministicDominator

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.RandomClosedBoundary
open FK.SourceRegions

universe u

section AdaptiveExhaustion

variable {V : Type u} {G : SimpleGraph V} {η : G.edgeSet → Bool}

/-- A closed-frontier exhaustion is, in particular, a source vertex exhaustion. -/
noncomputable def adaptiveVertexExhaustion
    (E : ClosedBoundaryExhaustion G (openSubgraph G η)) : VertexExhaustion V where
  region n := (E.finite n).toFinset
  monotone := by
    intro m n hmn x hx
    exact (E.finite n).mem_toFinset.mpr
      (E.monotone hmn ((E.finite m).mem_toFinset.mp hx))
  covers v := by
    have hv : v ∈ ⋃ n, E.region n := by
      rw [E.exhaustive]
      exact Set.mem_univ v
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
    exact ⟨n, (E.finite n).mem_toFinset.mpr hn⟩

@[simp] theorem coe_adaptiveVertexExhaustion_region
    (E : ClosedBoundaryExhaustion G (openSubgraph G η)) (n : ℕ) :
    ((adaptiveVertexExhaustion E).region n : Set V) = E.region n := by
  ext x
  simp [adaptiveVertexExhaustion]

end AdaptiveExhaustion

section ClosedFrontier

variable {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]

/-- A graph-closed frontier closes every labelled edge in `SourceBoundary`. -/
theorem boundaryClosed_sourceBoundary_of_closedBoundary
    (E : VertexExhaustion V) (n : ℕ) {η : G.edgeSet → Bool}
    (hclosed : ClosedBoundary G (openSubgraph G η) (E.region n : Set V)) :
    BoundaryClosed (SourceBoundary E.box E.data) n η := by
  intro e he
  apply frontier_closed hclosed
  · obtain ⟨w, hw⟩ := he.2
    exact ⟨E.data.vertex n w, hw, w.2⟩
  · by_contra hout
    push Not at hout
    apply he.1
    change e ∈ (E.box (G := G) n).edges
    exact (E.mem_box_edges_iff n e).2 hout

/-- Conversely, closed source-boundary labels give a graph-closed frontier. -/
theorem closedBoundary_of_boundaryClosed_sourceBoundary
    (E : VertexExhaustion V) (n : ℕ) {η : G.edgeSet → Bool}
    (hclosed : BoundaryClosed (SourceBoundary E.box E.data) n η) :
    ClosedBoundary G (openSubgraph G η) (E.region n : Set V) := by
  apply closedBoundary_of_forall_frontier_false
  intro e hin hout
  apply hclosed e
  constructor
  · change e ∉ (E.box (G := G) n).edges
    rw [E.mem_box_edges_iff]
    intro he
    obtain ⟨x, hx, hxout⟩ := hout
    exact hxout (he x hx)
  · obtain ⟨x, hx, hxin⟩ := hin
    exact ⟨⟨x, hxin⟩, hx⟩

/-- Closedness of the two boundary representations is equivalent. -/
theorem boundaryClosed_sourceBoundary_iff
    (E : VertexExhaustion V) (n : ℕ) {η : G.edgeSet → Bool} :
    BoundaryClosed (SourceBoundary E.box E.data) n η ↔
      ClosedBoundary G (openSubgraph G η) (E.region n : Set V) :=
  ⟨closedBoundary_of_boundaryClosed_sourceBoundary E n,
    boundaryClosed_sourceBoundary_of_closedBoundary E n⟩

end ClosedFrontier

section Convention

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}

/-- Every geometric all-region source convention is free at a closed frontier
of every vertex exhaustion. -/
theorem isFreeAtClosedBoundary_assignment
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (hΦ : IsSourceGeometry Φ) :
    IsFreeAtClosedBoundary E.exhaustion (assignment E Φ)
      (SourceBoundary E.box E.data) := by
  intro n ω hω
  have hclosed : ClosedBoundary G (openSubgraph G ω) (E.region n : Set V) :=
    closedBoundary_of_boundaryClosed_sourceBoundary E n hω
  have hzero : ClosedBoundary G (openSubgraph G (fun _ => false))
      (E.region n : Set V) := by
    apply closedBoundary_of_forall_frontier_false
    simp
  have hre : restrictExterior (G := G) (E.region n : Set V)
      (E.region n).finite_toSet (fun _ => false) = (E.box (G := G) n).closedExterior := rfl
  change Φ.partition (E.region n) (restrictExterior (G := G)
      (E.region n : Set V) (E.region n).finite_toSet ω) =
    Φ.partition (E.region n) (E.box (G := G) n).closedExterior
  rw [sourcePartition_restrict_eq_bot Φ hΦ (E.region n) hclosed]
  rw [← hre]
  exact (sourcePartition_restrict_eq_bot Φ hΦ (E.region n) hzero).symm

end Convention

section Main

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- Closed frontiers occur along the whole adaptive exhaustion, hence in
particular frequently at infinity. -/
theorem ae_frequently_boundaryClosed_dirac
    {η : G.edgeSet → Bool} (E : ClosedBoundaryExhaustion G (openSubgraph G η)) :
    ∀ᵐ ξ ∂(MeasureTheory.diracProba η : Measure (Configuration G.edgeSet)),
      FrequentlyBoundaryClosed
        (SourceBoundary (adaptiveVertexExhaustion E).box
          (adaptiveVertexExhaustion E).data) ξ := by
  change ∀ᵐ ξ ∂(Measure.dirac η), FrequentlyBoundaryClosed
    (SourceBoundary (adaptiveVertexExhaustion E).box (adaptiveVertexExhaustion E).data) ξ
  rw [MeasureTheory.ae_dirac_iff]
  · exact Filter.Frequently.of_forall fun n =>
      boundaryClosed_sourceBoundary_of_closedBoundary (adaptiveVertexExhaustion E) n
        (by simpa only [coe_adaptiveVertexExhaustion_region] using E.closed n)
  · exact measurableSet_frequentlyBoundaryClosed _

/-- **Deterministic-dominant source uniqueness.** Let `η` have a finite
closed-frontier exhaustion. If `δ_η` dominates every law of a geometric
all-region source convention, that source DLR class is pairwise equal. -/
theorem pairwise_eq_sourceDLR_of_dirac_dominates
    {η : G.edgeSet → Bool} (E : ClosedBoundaryExhaustion G (openSubgraph G η))
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (hdom : ∀ μ ∈ SourceDLRMeasures Φ,
      FKLimit.StochasticallyDominates (MeasureTheory.diracProba η) μ) :
    ∀ μ ∈ SourceDLRMeasures Φ, ∀ ν ∈ SourceDLRMeasures Φ, μ = ν := by
  intro μ hμ ν hν
  refine forall_eq_of_dominated_frequently_boundaryClosed
    (adaptiveVertexExhaustion E).exhaustion (assignment (adaptiveVertexExhaustion E) Φ) hq hp
    (SourceBoundary (adaptiveVertexExhaustion E).box (adaptiveVertexExhaustion E).data)
    (isFreeAtClosedBoundary_assignment (adaptiveVertexExhaustion E) Φ hΦ)
    (MeasureTheory.diracProba η)
    (ae_frequently_boundaryClosed_dirac E) ?_
    μ ((mem_sourceDLR_iff_mem_dlr_restrict (adaptiveVertexExhaustion E) Φ μ).1 hμ)
    ν ((mem_sourceDLR_iff_mem_dlr_restrict (adaptiveVertexExhaustion E) Φ ν).1 hν)
  intro κ hκ
  exact hdom κ ((mem_sourceDLR_iff_mem_dlr_restrict (adaptiveVertexExhaustion E) Φ κ).2 hκ)

/-- Subsingleton form of deterministic-dominant source uniqueness. -/
theorem subsingleton_sourceDLR_of_dirac_dominates
    {η : G.edgeSet → Bool} (E : ClosedBoundaryExhaustion G (openSubgraph G η))
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (hdom : ∀ μ ∈ SourceDLRMeasures Φ,
      FKLimit.StochasticallyDominates (MeasureTheory.diracProba η) μ) :
    Subsingleton (SourceDLRMeasures Φ) :=
  ⟨fun μ ν => Subtype.ext
    (pairwise_eq_sourceDLR_of_dirac_dominates hq hp E Φ hΦ hdom μ μ.2 ν ν.2)⟩

/-- If the source class is nonempty, deterministic domination identifies it as
an actual singleton. -/
theorem sourceDlr_eq_singleton_of_dirac_dominates
    {η : G.edgeSet → Bool} (E : ClosedBoundaryExhaustion G (openSubgraph G η))
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ₀ : ProbabilityMeasure (Configuration G.edgeSet)) (hμ₀ : μ₀ ∈ SourceDLRMeasures Φ)
    (hdom : ∀ μ ∈ SourceDLRMeasures Φ,
      FKLimit.StochasticallyDominates (MeasureTheory.diracProba η) μ) :
    SourceDLRMeasures Φ = {μ₀} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hμ₀, fun μ hμ => ?_⟩
  exact pairwise_eq_sourceDLR_of_dirac_dominates hq hp E Φ hΦ hdom μ hμ μ₀ hμ₀

/-- Nonpercolating-configuration form, with the adaptive exhaustion constructed
by the public graph theorem. -/
theorem pairwise_eq_sourceDLR_of_dirac_nonPercolating
    [Nonempty V] (hG : G.Preconnected) {η : G.edgeSet → Bool}
    (hη : η ∈ FK.NonPercolating G)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (hdom : ∀ μ ∈ SourceDLRMeasures Φ,
      FKLimit.StochasticallyDominates (MeasureTheory.diracProba η) μ) :
    ∀ μ ∈ SourceDLRMeasures Φ, ∀ ν ∈ SourceDLRMeasures Φ, μ = ν := by
  let E : ClosedBoundaryExhaustion G (openSubgraph G η) :=
    Classical.choice (FK.nonempty_closedBoundaryExhaustion_of_nonPercolating G hG η hη)
  exact pairwise_eq_sourceDLR_of_dirac_dominates hq hp E Φ hΦ hdom

/-- Nonempty singleton form directly from nonpercolation of the deterministic
configuration. -/
theorem sourceDlr_eq_singleton_of_dirac_nonPercolating
    [Nonempty V] (hG : G.Preconnected) {η : G.edgeSet → Bool}
    (hη : η ∈ FK.NonPercolating G)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ₀ : ProbabilityMeasure (Configuration G.edgeSet)) (hμ₀ : μ₀ ∈ SourceDLRMeasures Φ)
    (hdom : ∀ μ ∈ SourceDLRMeasures Φ,
      FKLimit.StochasticallyDominates (MeasureTheory.diracProba η) μ) :
    SourceDLRMeasures Φ = {μ₀} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hμ₀, fun μ hμ => ?_⟩
  exact pairwise_eq_sourceDLR_of_dirac_nonPercolating hq hp hG hη Φ hΦ hdom
    μ hμ μ₀ hμ₀

end Main

end FK.SourceUniqueness.DeterministicDominator
