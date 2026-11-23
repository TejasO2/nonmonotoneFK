import FK.InteriorWeakLimit

/-!
# Endpoint normalization for locally coherent interior weak limits

The public `InteriorWeakLimit` transport to a target geometric assignment only
needed the interior-parameter API, although `ConventionEndpoints` already
provides the same geometric DLR transport at every `p ≤ 1`.  These corollaries
expose that all-rate statement.  They do not remove local constancy, coherent
nesting, the specified finite-volume sequence, or global at-most-one-cluster.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.InteriorWeakLimit

noncomputable section

/-- All-rate version of `mem_dlrMeasures_of_tendsto_of_globalAtMostOne`.
The endpoint cases are discharged by the public closed/open DLR theorems via
`ConventionTransport.mem_dlrMeasures_of_globalAtMostOne_of_le_one`. -/
theorem mem_dlrMeasures_of_tendsto_of_globalAtMostOne_of_le_one
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp)
    (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    (hlocal : ∀ n, IsLocallyConstant (Φ.partition n))
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  have hμΦ : μ ∈ GibbsMeasures exh Φ :=
    mem_gibbsMeasures_of_tendsto_finiteVolumeLaw_of_isLocallyConstant
      exh Φ hlocal hμ
  exact ConventionTransport.mem_dlrMeasures_of_globalAtMostOne_of_le_one
    exh data hq hp Φ.toBoundaryAssignment Ψ hΦ hΨ μ hμΦ hglobal

/-- All-rate wired-at-infinity specialization.  The remaining hypotheses are
exactly those of the general locally coherent source/target transport. -/
theorem mem_dlrMeasures_wired_of_tendsto_of_globalAtMostOne_of_le_one
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : BoundaryConvention exh hq hp)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hlocal : ∀ n, IsLocallyConstant (Φ.partition n))
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh data.wired hq hp :=
  mem_dlrMeasures_of_tendsto_of_globalAtMostOne_of_le_one
    exh data hq hp Φ data.wired hΦ data.wired_isGeometric hlocal hμ hglobal

end

end FK.InfiniteVolume.InteriorWeakLimit

#print axioms FK.InfiniteVolume.InteriorWeakLimit.mem_dlrMeasures_of_tendsto_of_globalAtMostOne_of_le_one
#print axioms FK.InfiniteVolume.InteriorWeakLimit.mem_dlrMeasures_wired_of_tendsto_of_globalAtMostOne_of_le_one
