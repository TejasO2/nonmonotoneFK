import FK.ConventionEndpoints

/-!
# Weak-limit closure for continuous finite-box FK specifications

The DLR equation is weakly closed when the conditional global FK laws vary
continuously with the exterior configuration.  We also prove this continuity
for locally constant boundary partitions.  Infinite-component free/wired
assignments are not asserted to satisfy that hypothesis.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.InteriorWeakLimit

noncomputable section

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FiniteBox

variable {E : Type*} [Countable E] (B : FiniteBox E)

/-- Splitting global configurations is continuous in the product topology. -/
lemma continuous_split : Continuous B.split := by
  apply Continuous.prodMk
  · exact continuous_pi fun e ↦ continuous_apply e.1
  · exact continuous_pi fun e ↦ continuous_apply e.1

/-- Gluing an exterior and an interior configuration is continuous. -/
lemma continuous_glue : Continuous B.glue := by
  apply continuous_pi
  intro e
  change Continuous (fun z : B.Exterior × B.Interior ↦
    if he : e ∈ B.edges then z.2 ⟨e, he⟩ else z.1 ⟨e, he⟩)
  by_cases he : e ∈ B.edges
  · simp only [he, dite_true]
    exact (continuous_apply (⟨e, he⟩ : B.edges)).comp continuous_snd
  · simp only [he, dite_false]
    exact (continuous_apply (⟨e, he⟩ : {e : E // e ∉ B.edges})).comp continuous_fst

lemma continuous_exteriorRestriction :
    Continuous (fun ω ↦ (B.splitEquiv ω).1) :=
  continuous_fst.comp (continuous_split B)

/-- Integrating against a conditional global FK law is integration against
its actual finite interior FK PMF after gluing. -/
lemma integral_conditionalLaw {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    (f : BoundedContinuousFunction (Configuration E) ℝ) :
    ∫ ω, f ω ∂(B.conditionalLaw hq hp α η : Measure (Configuration E)) =
      ∫ ξ, f (B.glue (η, ξ))
        ∂(B.graph.fkMeasure hq hp (α η)) := by
  rw [show (B.conditionalLaw hq hp α η : Measure (Configuration E)) =
      Measure.map (fun ω : B.Interior ↦ B.glue (η, ω))
        (B.graph.fkMeasure hq hp (α η)) from rfl]
  exact MeasureTheory.integral_map
    (B.measurable_glue_const_left η).aemeasurable f.continuous.aestronglyMeasurable

/-- Reassemble a global law from its exterior marginal and the actual FK
kernel.  `IsDLR` says precisely that this reconstruction is the original law. -/
noncomputable def reconstruct {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) : ProbabilityMeasure (Configuration E) :=
  ⟨Measure.map B.glue ((B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ
      B.fkKernel hq hp α hα),
    (Measure.isProbabilityMeasure_map_iff B.splitEquiv.symm.measurable.aemeasurable).2
      inferInstance⟩

lemma eq_reconstruct_of_isDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) :
    μ = reconstruct B hq hp α hα μ := by
  apply Subtype.ext
  exact B.measure_eq_map_glue_compProd hq hp α hα μ hμ

/-- Bochner integrals against the FK reconstruction, written as exterior
integrals of the actual conditional global FK laws. -/
lemma integral_reconstruct {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (f : BoundedContinuousFunction (Configuration E) ℝ) :
    ∫ ω, f ω ∂(reconstruct B hq hp α hα μ : Measure (Configuration E)) =
      ∫ η, (∫ ω, f ω ∂(B.conditionalLaw hq hp α η : Measure (Configuration E)))
        ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
  let ρ : Measure (B.Exterior × B.Interior) :=
    (B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ B.fkKernel hq hp α hα
  let g : BoundedContinuousFunction (B.Exterior × B.Interior) ℝ :=
    f.compContinuous ⟨B.glue, continuous_glue B⟩
  have hg : Integrable (fun z ↦ f (B.glue z)) ρ := g.integrable ρ
  change ∫ ω, f ω ∂(Measure.map B.glue ρ) = _
  rw [MeasureTheory.integral_map (continuous_glue B).measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  change (∫ z, f (B.glue z) ∂ρ) = _
  rw [Measure.integral_compProd hg]
  apply integral_congr_ae
  filter_upwards [] with η
  exact (integral_conditionalLaw B hq hp α η f).symm

lemma isDLR_of_eq_reconstruct {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ = reconstruct B hq hp α hα μ) :
    B.IsDLR hq hp α hα μ := by
  apply B.splitEquiv.map_apply_eq_iff_map_symm_apply_eq.mpr
  exact congrArg Subtype.val hμ

lemma isDLR_iff_eq_reconstruct {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) :
    B.IsDLR hq hp α hα μ ↔ μ = reconstruct B hq hp α hα μ :=
  ⟨eq_reconstruct_of_isDLR B hq hp α hα μ, isDLR_of_eq_reconstruct B hq hp α hα μ⟩

/-- For a locally constant boundary partition, conditional FK integrations
are continuous.  The exterior configuration still varies continuously; only
the finite FK measure is locally fixed. -/
lemma tendsto_integral_conditionalLaw_of_isLocallyConstant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {α : B.Exterior → B.BoundaryPartition} (hα : IsLocallyConstant α)
    (η : B.Exterior) (f : BoundedContinuousFunction (Configuration E) ℝ) :
    Tendsto (fun ζ ↦ ∫ ω, f ω ∂(B.conditionalLaw hq hp α ζ : Measure (Configuration E)))
      (𝓝 η) (𝓝 (∫ ω, f ω ∂(B.conditionalLaw hq hp α η : Measure (Configuration E)))) := by
  let ν : Measure B.Interior := B.graph.fkMeasure hq hp (α η)
  haveI : IsProbabilityMeasure ν := by
    exact FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp (α η)
  have hmeas : ∀ᶠ ζ in 𝓝 η, AEStronglyMeasurable (fun ξ ↦ f (B.glue (ζ, ξ))) ν := by
    filter_upwards [] with ζ
    exact (f.continuous.comp ((continuous_glue B).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  have hbound : ∀ᶠ ζ in 𝓝 η, ∀ᵐ ξ ∂ν, ‖f (B.glue (ζ, ξ))‖ ≤ ‖f‖ := by
    filter_upwards [] with ζ
    filter_upwards [] with ξ
    exact f.norm_coe_le_norm _
  have hlim : ∀ᵐ ξ ∂ν, Tendsto (fun ζ ↦ f (B.glue (ζ, ξ))) (𝓝 η)
      (𝓝 (f (B.glue (η, ξ)))) := by
    filter_upwards [] with ξ
    exact (f.continuous.comp ((continuous_glue B).comp
      (continuous_id.prodMk continuous_const))).continuousAt
  have ht : Tendsto (fun ζ ↦ ∫ ξ, f (B.glue (ζ, ξ)) ∂ν) (𝓝 η)
      (𝓝 (∫ ξ, f (B.glue (η, ξ)) ∂ν)) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖)
      hmeas hbound (integrable_const ‖f‖) hlim
  simp_rw [integral_conditionalLaw B hq hp α]
  apply ht.congr'
  filter_upwards [hα.eventually_eq η] with ζ hζ
  change (∫ ξ, f (B.glue (ζ, ξ)) ∂B.graph.fkMeasure hq hp (α η)) = _
  rw [hζ]

/-- Conditional global FK laws vary continuously for every locally constant
boundary partition. -/
lemma continuous_conditionalLaw_of_isLocallyConstant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {α : B.Exterior → B.BoundaryPartition} (hα : IsLocallyConstant α) :
    Continuous (B.conditionalLaw hq hp α) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  rw [continuous_iff_continuousAt]
  intro η
  exact tendsto_integral_conditionalLaw_of_isLocallyConstant B hq hp hα η f

/-- Every fixed finite-box boundary setoid gives a continuous conditional FK
specification, even though the exterior part of the conditional law varies. -/
lemma continuous_conditionalLaw_const {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (β : B.BoundaryPartition) :
    Continuous (B.conditionalLaw hq hp (fun _ ↦ β)) :=
  continuous_conditionalLaw_of_isLocallyConstant B hq hp (IsLocallyConstant.const β)

/-- Exterior marginals are continuous under weak convergence. -/
lemma tendsto_exteriorMeasure {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun i ↦ B.exteriorMeasure (μs i)) l (𝓝 (B.exteriorMeasure μ)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hμ
    (continuous_exteriorRestriction B)

/-- FK reconstruction is weakly continuous for a continuous conditional-law
specification.  No continuity is assumed for the boundary partition itself. -/
lemma tendsto_reconstruct {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (hcond : Continuous (B.conditionalLaw hq hp α))
    {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun i ↦ reconstruct B hq hp α hα (μs i)) l
      (𝓝 (reconstruct B hq hp α hα μ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  let g : C(B.Exterior, ℝ) :=
    ⟨fun η ↦ ∫ ω, f ω ∂(B.conditionalLaw hq hp α η : Measure (Configuration E)),
      ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp hcond f⟩
  let gb : BoundedContinuousFunction B.Exterior ℝ := BoundedContinuousFunction.mkOfCompact g
  have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_exteriorMeasure B hμ) gb
  simpa only [integral_reconstruct B hq hp α hα, gb, g,
    BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using hlim

/-- A weak limit of DLR laws is DLR when its fixed FK specification is
continuous in the exterior configuration. -/
lemma isDLR_of_tendsto {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (hcond : Continuous (B.conditionalLaw hq hp α))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp α hα (μs i)) :
    B.IsDLR hq hp α hα μ := by
  apply isDLR_of_eq_reconstruct B hq hp α hα μ
  apply tendsto_nhds_unique (l := l) (f := μs) (a := μ)
    (b := reconstruct B hq hp α hα μ)
  · exact hμ
  · apply (tendsto_reconstruct B hq hp α hα hcond hμ).congr'
    filter_upwards [hDLR] with i hi
    exact (eq_reconstruct_of_isDLR B hq hp α hα (μs i) hi).symm

/-- Locally constant specifications need no separate analytic continuity
assumption in the weak-limit closure theorem. -/
lemma isDLR_of_tendsto_of_isLocallyConstant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (hlocal : IsLocallyConstant α)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp α hα (μs i)) :
    B.IsDLR hq hp α hα μ :=
  isDLR_of_tendsto B hq hp α hα
    (continuous_conditionalLaw_of_isLocallyConstant B hq hp hlocal) hμ hDLR

end FiniteBox

/-- Weak closure of the full DLR class of a continuous measurable boundary
assignment. -/
lemma mem_dlrMeasures_of_tendsto {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hcond : ∀ n, Continuous ((exh.box n).conditionalLaw hq hp (Φ.partition n)))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp) :
    μ ∈ DLRMeasures exh Φ hq hp := by
  intro n
  exact FiniteBox.isDLR_of_tendsto (exh.box n) hq hp (Φ.partition n)
    (Φ.measurable_partition n) (hcond n) hμ
    (hDLR.mono fun _ hi ↦ hi n)

/-- Locally constant measurable boundary assignments have weakly closed DLR
classes, with no separate continuity hypothesis. -/
lemma mem_dlrMeasures_of_tendsto_of_isLocallyConstant {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hlocal : ∀ n, IsLocallyConstant (Φ.partition n))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp) :
    μ ∈ DLRMeasures exh Φ hq hp :=
  mem_dlrMeasures_of_tendsto exh Φ hq hp
    (fun n ↦ FiniteBox.continuous_conditionalLaw_of_isLocallyConstant
      (exh.box n) hq hp (hlocal n)) hμ hDLR

/-- The canonical weak limit along a coherent convention belongs to its Gibbs
class when all its boundary partitions are locally constant.  The nesting
input is the convention's actual `compatible` field, separately at each fixed
small box; no arbitrary interior weak-limit hypothesis is assumed. -/
theorem mem_gibbsMeasures_of_tendsto_finiteVolumeLaw_of_isLocallyConstant
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : BoundaryConvention exh hq hp)
    (hlocal : ∀ n, IsLocallyConstant (Φ.partition n))
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ)) :
    μ ∈ GibbsMeasures exh Φ := by
  intro m
  apply FiniteBox.isDLR_of_tendsto_of_isLocallyConstant (exh.box m) hq hp
    (Φ.partition m) (Φ.measurable_partition m) (hlocal m) hμ
  filter_upwards [exh.eventually_subset (exh.box m).edges] with n hn
  simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using
    Φ.compatible m n hn (exh.box n).closedExterior

/-- Interior-parameter intersection with convention transport on an actual
countable simple graph.  A locally constant coherent source specification is
used only to obtain DLR compatibility of its genuine canonical weak limit;
the target is any geometrically valid assignment, including the canonical
free and wired-at-infinity assignments. -/
theorem mem_dlrMeasures_of_tendsto_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le)
    (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    (hlocal : ∀ n, IsLocallyConstant (Φ.partition n))
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp₁.le
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp₁.le := by
  have hμΦ : μ ∈ GibbsMeasures exh Φ :=
    mem_gibbsMeasures_of_tendsto_finiteVolumeLaw_of_isLocallyConstant
      exh Φ hlocal hμ
  exact data.mem_dlrMeasures_of_global_atMostOne exh hq hp₀ hp₁
    Φ.toBoundaryAssignment Ψ hΦ hΨ μ hμΦ hglobal

/-- Wired-at-infinity form of the actual simple-graph weak-limit/Gibbs
intersection, with the remaining analytic hypothesis recorded explicitly as
local constancy of the coherent source specification. -/
theorem mem_dlrMeasures_wired_of_tendsto_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hlocal : ∀ n, IsLocallyConstant (Φ.partition n))
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp₁.le
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh data.wired hq hp₁.le :=
  mem_dlrMeasures_of_tendsto_of_globalAtMostOne exh data hq hp₀ hp₁
    Φ data.wired hΦ data.wired_isGeometric hlocal hμ hglobal

end

end FK.InfiniteVolume.InteriorWeakLimit
