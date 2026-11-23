import FK.NonlocalWeakLimit

/-!
# Nonlocal coherent finite-volume weak limits

These theorems remove global local constancy from coherent finite-volume weak
limits.  The uniqueness input is the actual exterior-at-most-one-cluster event
at the limit, since that is what makes every geometric convention locally
constant.  The weaker global uniqueness event can be converted to this input
only after a DLR law is available (see `aeAtMostOne_geometry_of_global`); it is
not silently used here as a circular substitute.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.NonlocalInterior

open ConventionGeometry
open ConventionTransport

noncomputable section

/-- A weak limit of one coherent convention's finite FK laws, with an
arbitrary exterior configuration at every larger box, is a Gibbs law for that
convention as soon as it has almost surely at most one infinite exterior
component.  No global local-constancy assumption is made. -/
theorem mem_gibbsMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hunique : ConventionTransport.AEAtMostOne data.geometry μ) :
    μ ∈ GibbsMeasures exh Φ := by
  intro m
  apply isDLR_of_tendsto_of_ae_eventually_eq (exh.box m) hq hp
    (Φ.partition m) (Φ.measurable_partition m) hμ
  · filter_upwards [exh.eventually_subset (exh.box m).edges] with n hn
    exact Φ.compatible m n hn (η n)
  · filter_upwards [hunique m] with ζ hζ
    exact eventually_partition_eq_of_atMostOne data Φ.toBoundaryAssignment hΦ m ζ hζ

/-- The same arbitrary-exterior coherent weak limit belongs to every
geometrically valid target assignment.  This is the nonlocal interior
convention-transport statement with the precise exterior-uniqueness
hypothesis made explicit. -/
theorem mem_dlrMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp)
    (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hunique : ConventionTransport.AEAtMostOne data.geometry μ) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  have hsource : μ ∈ DLRMeasures exh Φ.toBoundaryAssignment hq hp :=
    mem_gibbsMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne exh data hq hp
      Φ hΦ η hμ hunique
  exact ConventionTransport.mem_dlrMeasures_of_atMostOne exh data.geometry
    Φ.toBoundaryAssignment Ψ hq hp hΦ hΨ hsource hunique

/-- The closed-exterior specialization is an arbitrary-boundary-sequence
replacement for the locally constant coherent weak-limit theorem, with
exterior uniqueness replacing local constancy. -/
theorem mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_aeAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp)
    (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hunique : ConventionTransport.AEAtMostOne data.geometry μ) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  apply mem_dlrMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne exh data hq hp
    Φ Ψ hΦ hΨ (fun n => (exh.box n).closedExterior) _ hunique
  simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using hμ

end

end FK.InfiniteVolume.NonlocalInterior
