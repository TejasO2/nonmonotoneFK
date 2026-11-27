import FK.SourceFamily
import FK.ComparableNonpercolating
import FK.CoherentMixtures
import FK.NonlocalWeakLimit
import FK.GlobalFiniteEnergy
import FK.OrderedKernelNonpercolation

/-!
# Weak compactness of source DLR laws below a nonpercolating dominant

This module proves a compactness statement, not the arbitrary-dominant
uniqueness theorem.  If source DLR laws converge weakly and are eventually
dominated by one nonpercolating law, then their limit is still source DLR,
nonpercolating, and dominated by that law.  The geometric convention is locally
constant on the resulting zero-infinite-cluster exterior support.  Coherence
upgrades DLR closure on one vertex exhaustion to all finite vertex regions.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

noncomputable section

namespace FK.SourceUniqueness.DominatedCompactness

open FK.InfiniteVolume FK.InfiniteVolume.ConventionGeometry
open FK.InfiniteVolume.ConventionTransport FK.InfiniteVolume.NonlocalInterior
open FK.InfiniteVolume.GlobalFiniteEnergy FK.SourceRegions
open FK.InfiniteVolume.CoherentMixtures

universe u

/-- Closing one finite box preserves nonpercolation on every exterior fibre.
No graph connectedness or DLR hypothesis is needed. -/
theorem ae_nonPercolating_closeInside
    {V : Type u} [Countable V] {G : SimpleGraph V}
    (B : FiniteBox G.edgeSet) (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      closeInside B η ∈ FK.NonPercolating G := by
  let Bset : Set (Configuration G.edgeSet) :=
    {ω | ¬ FK.ClusterCover.HasInfiniteCluster G ω}
  have hBmeas : MeasurableSet Bset :=
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G).compl
  have hclose : closeBox B ≤ (fun ω => ω) := by
    intro ω e
    by_cases he : e ∈ B.edges
    · simp [closeBox, FiniteBox.glue, he]
    · simp [closeBox, FiniteBox.glue, he, FiniteBox.split]
  have hpoint : ∀ ω : Configuration G.edgeSet,
      ω ∈ FK.NonPercolating G → closeBox B ω ∈ Bset := by
    intro ω hω
    exact (FKLimit.nonPercolating_iff_not_hasInfiniteCluster G _).1
      (FK.isLowerSet_nonPercolating G (hclose ω) hω)
  have hmapped : ∀ᵐ ξ ∂Measure.map (closeBox B)
      (μ : Measure (Configuration G.edgeSet)), ξ ∈ Bset := by
    apply (ae_map_iff (measurable_closeBox B).aemeasurable hBmeas).2
    filter_upwards [hμ] with ω hω
    exact hpoint ω hω
  have hsplit : Measurable (fun ω : Configuration G.edgeSet =>
      (B.splitEquiv ω).1) := measurable_fst.comp B.splitEquiv.measurable
  have hmapeq : Measure.map (closeInside B)
      (B.exteriorMeasure μ : Measure B.Exterior) =
      Measure.map (closeBox B) (μ : Measure (Configuration G.edgeSet)) := by
    change Measure.map (closeInside B)
        (Measure.map (fun ω : Configuration G.edgeSet => (B.splitEquiv ω).1)
          (μ : Measure (Configuration G.edgeSet))) = _
    rw [Measure.map_map (measurable_closeInside B) hsplit]
    rfl
  rw [← hmapeq] at hmapped
  have hout := (ae_map_iff (measurable_closeInside B).aemeasurable hBmeas).1 hmapped
  filter_upwards [hout] with η hη
  exact (FKLimit.nonPercolating_iff_not_hasInfiniteCluster G _).2 hη

/-- Nonpercolation gives the exterior uniqueness needed for local constancy at
all boxes of actual graph data.  The conclusion is vacuous on every fibre:
there are no infinite exterior components at all. -/
theorem aeAtMostOne_geometry_of_nonPercolating
    {V : Type u} {G : SimpleGraph V} [Countable V]
    {box : ℕ → FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G box)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) : AEAtMostOne data.geometry μ := by
  intro n
  filter_upwards [ae_nonPercolating_closeInside (box n) μ hμ] with η hη
  intro x y hx _hy
  exact (hx (hη (data.vertex n x))).elim

/-- A fixed nonpercolating stochastic upper bound passes through weak limits
along an arbitrary nontrivial filter. -/
theorem stochasticallyDominates_const_of_tendsto
    {E : Type u} [Countable E] {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (FKLimit.Configuration E)}
    {μ ρ : ProbabilityMeasure (FKLimit.Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hdom : ∀ᶠ i in l, FKLimit.StochasticallyDominates ρ (μs i)) :
    FKLimit.StochasticallyDominates ρ μ := by
  apply FKLimit.stochasticallyDominates_of_cylinderDominates
  intro A S hAS hA
  apply le_of_tendsto_of_tendsto
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAS.isClopen)
    tendsto_const_nhds
  filter_upwards [hdom] with i hi
  exact hi A hAS.measurableSet hA

/-- A fixed stochastic lower bound also passes through weak limits along an
arbitrary nontrivial filter. -/
theorem stochasticallyDominates_of_tendsto_const
    {E : Type u} [Countable E] {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (FKLimit.Configuration E)}
    {μ ρ : ProbabilityMeasure (FKLimit.Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hdom : ∀ᶠ i in l, FKLimit.StochasticallyDominates (μs i) ρ) :
    FKLimit.StochasticallyDominates μ ρ := by
  apply FKLimit.stochasticallyDominates_of_cylinderDominates
  intro A S hAS hA
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAS.isClopen)
  filter_upwards [hdom] with i hi
  exact hi A hAS.measurableSet hA

/-- **Dominated weak closure of a geometric all-region source class.**
The approximating laws must already be source DLR; this theorem does not turn
the arbitrary dominant itself into a DLR law. -/
theorem mem_sourceDLR_of_tendsto_of_dominated
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (hΦ : IsSourceGeometry Φ)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ ρ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hμs : ∀ᶠ i in l, μs i ∈ SourceDLRMeasures Φ)
    (hdom : ∀ᶠ i in l, FKLimit.StochasticallyDominates ρ (μs i))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    μ ∈ SourceDLRMeasures Φ ∧
      FKLimit.StochasticallyDominates ρ μ ∧
      ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G := by
  have hdomlim : FKLimit.StochasticallyDominates ρ μ :=
    stochasticallyDominates_const_of_tendsto hμ hdom
  have hμnp : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    FKLimit.ae_nonPercolating_of_stochasticallyDominates G hdomlim hρ
  have hunique : AEAtMostOne E.data.geometry μ :=
    aeAtMostOne_geometry_of_nonPercolating E.data μ hμnp
  refine ⟨?_, hdomlim, hμnp⟩
  apply (mem_sourceDLR_iff_mem_dlr_restrict E Φ μ).2
  intro n
  apply isDLR_of_tendsto_of_ae_eventually_eq (E.box n) hq hp
    ((assignment E Φ).partition n) ((assignment E Φ).measurable_partition n) hμ
  · filter_upwards [hμs] with i hi
    exact mem_dlr_restrict hi n
  · filter_upwards [hunique n] with η hη
    exact eventually_partition_eq_of_atMostOne E.data (assignment E Φ)
      (isGeometric_assignment E Φ hΦ) n η hη

/-- More generally, it suffices that the approximants are eventually DLR at
each fixed box of one vertex exhaustion.  This is the form applicable to
coherent finite-volume conditional stages. -/
theorem mem_sourceDLR_of_tendsto_of_eventually_dlr
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (hΦ : IsSourceGeometry Φ)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ ρ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ n, ∀ᶠ i in l, (E.box n).IsDLR hq hp
      ((assignment E Φ).partition n) ((assignment E Φ).measurable_partition n)
      (μs i))
    (hdom : ∀ᶠ i in l, FKLimit.StochasticallyDominates ρ (μs i))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    μ ∈ SourceDLRMeasures Φ ∧
      FKLimit.StochasticallyDominates ρ μ ∧
      ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G := by
  have hdomlim : FKLimit.StochasticallyDominates ρ μ :=
    stochasticallyDominates_const_of_tendsto hμ hdom
  have hμnp : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    FKLimit.ae_nonPercolating_of_stochasticallyDominates G hdomlim hρ
  have hunique : AEAtMostOne E.data.geometry μ :=
    aeAtMostOne_geometry_of_nonPercolating E.data μ hμnp
  refine ⟨?_, hdomlim, hμnp⟩
  apply (mem_sourceDLR_iff_mem_dlr_restrict E Φ μ).2
  intro n
  apply isDLR_of_tendsto_of_ae_eventually_eq (E.box n) hq hp
    ((assignment E Φ).partition n) ((assignment E Φ).measurable_partition n) hμ
  · exact hDLR n
  · filter_upwards [hunique n] with η hη
    exact eventually_partition_eq_of_atMostOne E.data (assignment E Φ)
      (isGeometric_assignment E Φ hΦ) n η hη

/-- Arbitrary probability-weighted mixtures preserve source DLR membership,
one common stochastic upper bound, and consequently nonpercolation. -/
theorem mem_sourceDLR_mixture_of_dominated
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    {ι : Type*} [MeasurableSpace ι]
    (τ : Measure ι) [IsProbabilityMeasure τ]
    (κ : Kernel ι (Configuration G.edgeSet)) [IsMarkovKernel κ]
    (hκ : ∀ i, InfiniteVolume.CoherentMixtures.outputLaw κ i ∈ SourceDLRMeasures Φ)
    (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ i, FKLimit.StochasticallyDominates ρ
      (InfiniteVolume.CoherentMixtures.outputLaw κ i))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    InfiniteVolume.CoherentMixtures.mixture τ κ ∈ SourceDLRMeasures Φ ∧
      FKLimit.StochasticallyDominates ρ
        (InfiniteVolume.CoherentMixtures.mixture τ κ) ∧
      ∀ᵐ ω ∂((InfiniteVolume.CoherentMixtures.mixture τ κ : ProbabilityMeasure
        (Configuration G.edgeSet)) : Measure (Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G := by
  have hmem : mixture τ κ ∈ SourceDLRMeasures Φ := by
    apply (mem_sourceDLR_iff_mem_dlr_restrict E Φ (mixture τ κ)).2
    exact mem_dlrMeasures_mixture E.exhaustion (assignment E Φ) hq hp τ κ
      (fun i => mem_dlr_restrict (hκ i))
  have hdomMix : FKLimit.StochasticallyDominates ρ (mixture τ κ) := by
    intro A hA hAup
    have hle : ((mixture τ κ : ProbabilityMeasure (Configuration G.edgeSet)) :
        Measure (Configuration G.edgeSet)) A ≤ (ρ : Measure _) A := by
      rw [coe_mixture, Measure.bind_apply hA κ.aemeasurable]
      calc
        (∫⁻ i, κ i A ∂τ) ≤ ∫⁻ _i, (ρ : Measure (Configuration G.edgeSet)) A ∂τ := by
          apply lintegral_mono
          intro i
          have hi := hdom i A hA hAup
          change κ i A ≤ (ρ : Measure (Configuration G.edgeSet)) A
          change (outputLaw κ i : Measure (Configuration G.edgeSet)) A ≤
            (ρ : Measure (Configuration G.edgeSet)) A
          rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
            ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
          exact_mod_cast hi
        _ = (ρ : Measure (Configuration G.edgeSet)) A := by simp
    change (((mixture τ κ : ProbabilityMeasure (Configuration G.edgeSet)) :
      Measure (Configuration G.edgeSet)) A).toNNReal ≤ ((ρ : Measure _) A).toNNReal
    exact (ENNReal.toNNReal_le_toNNReal
      (measure_ne_top ((mixture τ κ : ProbabilityMeasure (Configuration G.edgeSet)) :
        Measure (Configuration G.edgeSet)) A)
      (measure_ne_top (ρ : Measure (Configuration G.edgeSet)) A)).mpr hle
  exact ⟨hmem, hdomMix,
    FKLimit.ae_nonPercolating_of_stochasticallyDominates G hdomMix hρ⟩

/-- Coherent finite-volume conditional stages attached to a source convention
and an exterior sequence. -/
noncomputable def sourceConditionalStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (η : ∀ n, (E.box (G := G) n).Exterior) (n : ℕ) :
    ProbabilityMeasure (Configuration G.edgeSet) :=
  (E.box n).conditionalLaw hq hp ((assignment E Φ).partition n) (η n)

/-- Sequential compactness of the part of a geometric source class lying below
one nonpercolating law. -/
theorem exists_subseq_tendsto_sourceDLR_of_dominated
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (hΦ : IsSourceGeometry Φ)
    (μs : ℕ → ProbabilityMeasure (Configuration G.edgeSet))
    (hμs : ∀ n, μs n ∈ SourceDLRMeasures Φ)
    (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ρ (μs n))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
      μ ∈ SourceDLRMeasures Φ ∧
      FKLimit.StochasticallyDominates ρ μ ∧
      ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G := by
  obtain ⟨μ, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq μs
  obtain ⟨hμ, hdomμ, hnpμ⟩ := mem_sourceDLR_of_tendsto_of_dominated E Φ hΦ
    hlim (Eventually.of_forall (fun n => hμs (φ n)))
    (Eventually.of_forall (fun n => hdom (φ n))) hρ
  exact ⟨μ, φ, hφ, hlim, hμ, hdomμ, hnpμ⟩

/-- **A DLR replacement from dominated coherent finite-volume stages.**  Unlike
`mem_sourceDLR_of_tendsto_of_dominated`, the stages need not be global DLR
laws.  The explicit extra input is stochastic domination of every stage by the
nonpercolating law `ρ`. -/
theorem exists_subseq_tendsto_sourceDLR_of_conditionalLaw_dominated
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (hΦ : IsSourceGeometry Φ) (η : ∀ n, (E.box n).Exterior)
    (ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ρ
      (sourceConditionalStage E Φ η n))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (sourceConditionalStage E Φ η ∘ φ) atTop (𝓝 μ) ∧
      μ ∈ SourceDLRMeasures Φ ∧
      FKLimit.StochasticallyDominates ρ μ ∧
      ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
        ω ∈ FK.NonPercolating G := by
  obtain ⟨μ, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq (sourceConditionalStage E Φ η)
  have hstage : ∀ m, ∀ᶠ n in atTop, (E.box m).IsDLR hq hp
      ((assignment E Φ).partition m) ((assignment E Φ).measurable_partition m)
      (sourceConditionalStage E Φ η n) := by
    intro m
    filter_upwards [eventually_ge_atTop m] with n hmn
    exact Φ.compatible (E.monotone hmn) (η n)
  have hstageφ : ∀ m, ∀ᶠ n in atTop, (E.box m).IsDLR hq hp
      ((assignment E Φ).partition m) ((assignment E Φ).measurable_partition m)
      ((sourceConditionalStage E Φ η ∘ φ) n) := by
    intro m
    exact hφ.tendsto_atTop.eventually (hstage m)
  obtain ⟨hμ, hdomμ, hnpμ⟩ := mem_sourceDLR_of_tendsto_of_eventually_dlr E Φ hΦ
    hlim hstageφ (Eventually.of_forall (fun n => hdom (φ n))) hρ
  exact ⟨μ, φ, hφ, hlim, hμ, hdomμ, hnpμ⟩

/-- **Common DLR replacement under a two-sided stage sandwich.**  If every
coherent conditional stage lies above both given source laws and below the
nonpercolating law `ρ`, compactness produces a source-DLR law above both.  The
accepted comparable-law theorem then collapses all three laws to the same one.
This is a scoped sufficient replacement criterion, not the arbitrary-dominant
 theorem. -/
theorem exists_common_sourceDLR_dominant_of_conditionalLaw_sandwiched
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (E : VertexExhaustion V) (Φ : SourceConvention G hq hp)
    (hΦ : IsSourceGeometry Φ) (η : ∀ n, (E.box n).Exterior)
    (μ ν ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) (hν : ν ∈ SourceDLRMeasures Φ)
    (hUpper : ∀ n, FKLimit.StochasticallyDominates ρ
      (sourceConditionalStage E Φ η n))
    (hLowerμ : ∀ n, FKLimit.StochasticallyDominates
      (sourceConditionalStage E Φ η n) μ)
    (hLowerν : ∀ n, FKLimit.StochasticallyDominates
      (sourceConditionalStage E Φ η n) ν)
    (hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∃ κ : ProbabilityMeasure (Configuration G.edgeSet),
      κ ∈ SourceDLRMeasures Φ ∧ FKLimit.StochasticallyDominates ρ κ ∧
      μ = κ ∧ ν = κ := by
  obtain ⟨κ, φ, hφ, hlim, hκ, hρκ, hκnp⟩ :=
    exists_subseq_tendsto_sourceDLR_of_conditionalLaw_dominated E Φ hΦ η ρ hUpper hρ
  have hκμ : FKLimit.StochasticallyDominates κ μ :=
    stochasticallyDominates_of_tendsto_const hlim
      (Eventually.of_forall (fun n => hLowerμ (φ n)))
  have hκν : FKLimit.StochasticallyDominates κ ν :=
    stochasticallyDominates_of_tendsto_const hlim
      (Eventually.of_forall (fun n => hLowerν (φ n)))
  have hμnp : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    FKLimit.ae_nonPercolating_of_stochasticallyDominates G hκμ hκnp
  have hνnp : ∀ᵐ ω ∂(ν : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    FKLimit.ae_nonPercolating_of_stochasticallyDominates G hκν hκnp
  have hμeq : μ = κ :=
    FK.ComparableNonpercolating.eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating
      hq hp Φ hΦ μ κ hμ hκ hμnp hκnp hκμ
  have hνeq : ν = κ :=
    FK.ComparableNonpercolating.eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating
      hq hp Φ hΦ ν κ hν hκ hνnp hκnp hκν
  exact ⟨κ, hκ, hρκ, hμeq, hνeq⟩

end FK.SourceUniqueness.DominatedCompactness
