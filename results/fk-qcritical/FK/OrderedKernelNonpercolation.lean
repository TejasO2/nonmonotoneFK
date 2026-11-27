import FK.ConditionallyIndependentOrderedCoupling
import FK.ClusterTail
import FK.StrongUniqueness

/-!
# Nonpercolation along an ordered conditional kernel

The pairwise Strassen kernel returned by `exists_dominatedKernel` disintegrates
an ordered coupling over its dominating marginal.  This file transfers lower
(measurable, decreasing) properties through that disintegration directly.  In
particular, a dominating law with no infinite open cluster forces the dominated
law to have no infinite open cluster.  No connectedness or local-finiteness is
needed for the latter statement: measurability is proved by the countable union
over vertices in `FK.ClusterTail`.

The final statements use exactly the project's `StochasticallyDominates` and
`FK.NonPercolating` conventions and do not construct a second coupling.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FKLimit

variable {E : Type*} [Countable E]

/-- A decreasing property of the dominating coordinate holds inside almost every
ordered fibre.  This fibre-level statement needs neither measurability of the
property nor a marginal identity; only the integrated form below needs joint
measurability. -/
theorem ae_fibre_mem_of_dominatedKernel
    {ρ : Measure (Configuration E)} [IsProbabilityMeasure ρ]
    (K : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K]
    (hsupp : ∀ᵐ η ∂ρ, K η {ξ : Configuration E | ξ ≤ η} = 1)
    {B : Set (Configuration E)} (hlower : IsLowerSet B)
    (hρ : ∀ᵐ η ∂ρ, η ∈ B) :
    ∀ᵐ η ∂ρ, ∀ᵐ ξ ∂K η, ξ ∈ B := by
  filter_upwards [hsupp, hρ] with η hηsupp hηB
  have hle : ∀ᵐ ξ ∂K η, ξ ≤ η :=
    (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_le_fst_fixed η)).2 hηsupp
  filter_upwards [hle] with ξ hξ
  exact hlower hξ hηB

/-- The integrated form of `ae_fibre_mem_of_dominatedKernel`: the same lower
property holds almost surely under the second marginal of `ρ ⊗ₘ K`. -/
theorem ae_snd_mem_of_dominatedKernel
    {ρ μ : Measure (Configuration E)} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    (K : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K]
    (hsupp : ∀ᵐ η ∂ρ, K η {ξ : Configuration E | ξ ≤ η} = 1)
    (hmarg : (ρ ⊗ₘ K).map Prod.snd = μ)
    {B : Set (Configuration E)} (hB : MeasurableSet B) (hlower : IsLowerSet B)
    (hρ : ∀ᵐ η ∂ρ, η ∈ B) :
    ∀ᵐ ξ ∂μ, ξ ∈ B := by
  have hfibre := ae_fibre_mem_of_dominatedKernel K hsupp hlower hρ
  have hpair : ∀ᵐ z ∂(ρ ⊗ₘ K), z.2 ∈ B :=
    Measure.ae_compProd_of_ae_ae (hB.preimage measurable_snd) hfibre
  have hmapped : ∀ᵐ ξ ∂(ρ ⊗ₘ K).map Prod.snd, ξ ∈ B :=
    (MeasureTheory.ae_map_iff measurable_snd.aemeasurable hB).2 hpair
  rwa [hmarg] at hmapped

/-- Fibre-level nonpercolation for `HasInfiniteCluster`, with no connectedness
or local-finiteness assumption. -/
theorem ae_fibre_not_hasInfiniteCluster_of_dominatedKernel
    {V : Type*} [Countable V] (G : SimpleGraph V)
    {ρ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure ρ]
    (K : Kernel (G.edgeSet → Bool) (G.edgeSet → Bool)) [IsMarkovKernel K]
    (hsupp : ∀ᵐ η ∂ρ, K η {ξ : G.edgeSet → Bool | ξ ≤ η} = 1)
    (hρ : ρ {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω} = 0) :
    ∀ᵐ η ∂ρ, ∀ᵐ ξ ∂K η, ¬ FK.ClusterCover.HasInfiniteCluster G ξ := by
  let B : Set (G.edgeSet → Bool) :=
    {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω}ᶜ
  have hlower : IsLowerSet B := by
    intro ω η hωη hη hω
    exact hη (FK.ClusterTail.isUpperSet_hasInfiniteCluster G hωη hω)
  have hρae : ∀ᵐ η ∂ρ, η ∈ B := by
    rw [MeasureTheory.ae_iff]
    simpa only [B, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hρ
  exact ae_fibre_mem_of_dominatedKernel K hsupp hlower hρae

/-- Nonpercolation transfer through the actual graph event, in zero-mass form.
Only countability of the vertex type is required. -/
theorem measure_hasInfiniteCluster_eq_zero_of_dominatedKernel
    {V : Type*} [Countable V] (G : SimpleGraph V)
    {ρ μ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    (K : Kernel (G.edgeSet → Bool) (G.edgeSet → Bool)) [IsMarkovKernel K]
    (hsupp : ∀ᵐ η ∂ρ, K η {ξ : G.edgeSet → Bool | ξ ≤ η} = 1)
    (hmarg : (ρ ⊗ₘ K).map Prod.snd = μ)
    (hρ : ρ {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω} = 0) :
    μ {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω} = 0 := by
  let B : Set (G.edgeSet → Bool) :=
    {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω}ᶜ
  have hB : MeasurableSet B := (FK.ClusterTail.measurableSet_hasInfiniteCluster G).compl
  have hlower : IsLowerSet B := by
    intro ω η hωη hη hω
    exact hη (FK.ClusterTail.isUpperSet_hasInfiniteCluster G hωη hω)
  have hρae : ∀ᵐ η ∂ρ, η ∈ B := by
    rw [MeasureTheory.ae_iff]
    simpa only [B, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hρ
  have hμae := ae_snd_mem_of_dominatedKernel K hsupp hmarg hB hlower hρae
  rw [MeasureTheory.ae_iff] at hμae
  simpa only [B, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using hμae

/-- Finite open-walk clusters are exactly the complement of
`ClusterCover.HasInfiniteCluster`; no graph hypotheses are needed for this
pointwise equivalence. -/
lemma nonPercolating_iff_not_hasInfiniteCluster
    {V : Type*} (G : SimpleGraph V) (ω : G.edgeSet → Bool) :
    ω ∈ FK.NonPercolating G ↔ ¬ FK.ClusterCover.HasInfiniteCluster G ω := by
  constructor
  · intro h ⟨x, hx⟩
    rw [FK.ClusterCover.clusterAvoid_empty_eq] at hx
    exact hx (h x)
  · intro h o
    apply Set.not_infinite.mp
    intro hinf
    apply h
    refine ⟨o, ?_⟩
    rwa [FK.ClusterCover.clusterAvoid_empty_eq]

/-- Nonpercolation holds in almost every ordered conditional fibre, not merely
under the integrated dominated law. -/
theorem ae_fibre_nonPercolating_of_dominatedKernel
    {V : Type*} [Countable V] (G : SimpleGraph V)
    {ρ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure ρ]
    (K : Kernel (G.edgeSet → Bool) (G.edgeSet → Bool)) [IsMarkovKernel K]
    (hsupp : ∀ᵐ η ∂ρ, K η {ξ : G.edgeSet → Bool | ξ ≤ η} = 1)
    (hρ : ∀ᵐ η ∂ρ, η ∈ FK.NonPercolating G) :
    ∀ᵐ η ∂ρ, ∀ᵐ ξ ∂K η, ξ ∈ FK.NonPercolating G :=
  ae_fibre_mem_of_dominatedKernel K hsupp (FK.isLowerSet_nonPercolating G) hρ

/-- The nonpercolating-dominant input of Theorem 5.1, in kernel form and using
`FK.NonPercolating`, the full-support hypothesis of the closed-frontier
exhaustion.  Measurability goes through the complement of `HasInfiniteCluster`,
so connectedness and local finiteness are unnecessary here. -/
theorem ae_nonPercolating_of_dominatedKernel
    {V : Type*} [Countable V] (G : SimpleGraph V)
    {ρ μ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ]
    (K : Kernel (G.edgeSet → Bool) (G.edgeSet → Bool)) [IsMarkovKernel K]
    (hsupp : ∀ᵐ η ∂ρ, K η {ξ : G.edgeSet → Bool | ξ ≤ η} = 1)
    (hmarg : (ρ ⊗ₘ K).map Prod.snd = μ)
    (hρ : ∀ᵐ η ∂ρ, η ∈ FK.NonPercolating G) :
    ∀ᵐ ξ ∂μ, ξ ∈ FK.NonPercolating G := by
  let B : Set (G.edgeSet → Bool) :=
    {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω}ᶜ
  have hB : MeasurableSet B := (FK.ClusterTail.measurableSet_hasInfiniteCluster G).compl
  have hlower : IsLowerSet B := by
    intro ω η hωη hη hω
    exact hη (FK.ClusterTail.isUpperSet_hasInfiniteCluster G hωη hω)
  have hρB : ∀ᵐ η ∂ρ, η ∈ B := by
    filter_upwards [hρ] with η hη
    exact (nonPercolating_iff_not_hasInfiniteCluster G η).1 hη
  have hμB := ae_snd_mem_of_dominatedKernel K hsupp hmarg hB hlower hρB
  filter_upwards [hμB] with ξ hξ
  exact (nonPercolating_iff_not_hasInfiniteCluster G ξ).2 hξ

/-- **Direct stochastic-domination corollary.**  A nonpercolating stochastic
dominant forces every dominated configuration law to be almost surely
nonpercolating.  The kernel is precisely the one supplied by
`exists_dominatedKernel`; no extra graph event or ordered coupling is assumed. -/
theorem ae_nonPercolating_of_stochasticallyDominates
    {V : Type*} [Countable V] (G : SimpleGraph V)
    {ρ μ : ProbabilityMeasure (G.edgeSet → Bool)}
    (hdom : StochasticallyDominates ρ μ)
    (hρ : ∀ᵐ η ∂(ρ : Measure (G.edgeSet → Bool)), η ∈ FK.NonPercolating G) :
    ∀ᵐ ξ ∂(μ : Measure (G.edgeSet → Bool)), ξ ∈ FK.NonPercolating G := by
  classical
  obtain ⟨K, hK, hsupp, -, hmarg⟩ := exists_dominatedKernel hdom
  let _ : IsMarkovKernel K := hK
  exact ae_nonPercolating_of_dominatedKernel G K hsupp hmarg hρ

/-- The same stochastic-domination corollary for the increasing event
`HasInfiniteCluster`, without connectedness or local finiteness. -/
theorem measure_hasInfiniteCluster_eq_zero_of_stochasticallyDominates
    {V : Type*} [Countable V] (G : SimpleGraph V)
    {ρ μ : ProbabilityMeasure (G.edgeSet → Bool)}
    (hdom : StochasticallyDominates ρ μ)
    (hρ : (ρ : Measure (G.edgeSet → Bool))
      {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω} = 0) :
    (μ : Measure (G.edgeSet → Bool))
      {ω : G.edgeSet → Bool | FK.ClusterCover.HasInfiniteCluster G ω} = 0 := by
  classical
  obtain ⟨K, hK, hsupp, -, hmarg⟩ := exists_dominatedKernel hdom
  let _ : IsMarkovKernel K := hK
  exact measure_hasInfiniteCluster_eq_zero_of_dominatedKernel G K hsupp hmarg hρ


end FKLimit
