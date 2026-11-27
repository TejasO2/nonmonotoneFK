import FK.FiniteExteriorDetermination
import FK.DualLimit
import FK.PlaneClusterTarget
import FK.ClusterTail
import FK.BernoulliDuality

/-!
# Global measure assembly for planar strong uniqueness

This file supplies the graph-level cluster-count step in the proof of
Theorem 1.11.  A primal lower bound is dualized to an upper bound, a null
percolation event is transferred to the dual law, and the genuine plane
implication `DualNonpercolationForcesPrimalAtMostOne` is applied pointwise to
the complementary configuration.  With a separate primal supercriticality
input this proves almost-sure existence and uniqueness of the infinite primal
cluster, not merely a conditional statement about a fixed circuit.

The plane implication itself is deliberately an input: it is the remaining
Jordan/circuit theorem attacked by the planar-construction direction.  No
`GraphicDualCertificate`, spherical exhaustion, or graph-specific example is
assumed here.
-/

open Filter MeasureTheory Set
open scoped ENNReal unitInterval Classical

namespace FK.Planar

open FK.Configuration
open FK.ClusterCover
open FK.ClusterTail
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

noncomputable section

/-- Absence of an infinite open component is precisely the complement of the
project's tail-measurable `HasInfiniteCluster` event. -/
lemma noInfiniteOpenCluster_iff_not_hasInfiniteCluster {V : Type*}
    (G : SimpleGraph V) (ω : G.edgeSet → Bool) :
    NoInfiniteOpenCluster G ω ↔ ¬ HasInfiniteCluster G ω := by
  rw [noInfiniteOpenCluster_iff]
  simp only [HasInfiniteCluster, ExteriorInfiniteCluster,
    clusterAvoid_empty_eq, not_exists]

/-- The no-infinite-component event is measurable on every countable graph;
no connectedness or local finiteness is needed. -/
lemma measurableSet_noInfiniteOpenCluster {V : Type*} [Countable V]
    (G : SimpleGraph V) : MeasurableSet {ω | NoInfiniteOpenCluster G ω} := by
  have hset : {ω | NoInfiniteOpenCluster G ω} =
      {ω | HasInfiniteCluster G ω}ᶜ := by
    ext ω
    exact noInfiniteOpenCluster_iff_not_hasInfiniteCluster G ω
  rw [hset]
  exact (measurableSet_hasInfiniteCluster G).compl

/-- The actual form of domination transfer on a graph's own edge type. -/
theorem ae_noInfiniteOpenCluster_of_stochDom {V : Type*} [Countable V]
    (G : SimpleGraph V) (μ ρ : Measure (G.edgeSet → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (hdom : StochDom μ ρ)
    (hzero : ρ {ω | HasInfiniteCluster G ω} = 0) :
    ∀ᵐ ω ∂μ, NoInfiniteOpenCluster G ω := by
  have hμzero : μ {ω | HasInfiniteCluster G ω} = 0 := by
    apply le_antisymm _ zero_le
    calc
      μ {ω | HasInfiniteCluster G ω} ≤ ρ {ω | HasInfiniteCluster G ω} := by
        apply hdom _ (measurableSet_hasInfiniteCluster G)
        rintro ω ζ hle ⟨x, hx⟩
        refine ⟨x, ?_⟩
        rw [clusterAvoid_empty_eq] at hx ⊢
        exact hx.mono fun y hy => hy.mono_config hle
      _ = 0 := hzero
  have hae : ∀ᵐ ω ∂μ, ω ∉ {ω | HasInfiniteCluster G ω} :=
    measure_eq_zero_iff_ae_notMem.mp hμzero
  filter_upwards [hae] with ω hω
  exact (noInfiniteOpenCluster_iff_not_hasInfiniteCluster G ω).mpr hω

/-- **The Theorem 1.11 cluster-geometry assembly.**  If the dual of the
primal law has no infinite component almost surely, then the primal law has at
most one infinite component almost surely. -/
theorem ae_globalAtMostOne_of_ae_dual_noInfiniteOpenCluster
    {V F : Type*} [Countable V] [Countable F]
    (G : SimpleGraph V) (GD : SimpleGraph F) (edge : G.edgeSet ≃ GD.edgeSet)
    (φ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure φ]
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge)
    (hdual : ∀ᵐ ω' ∂(Measure.map (dualMeasurableEquiv edge) φ),
      NoInfiniteOpenCluster GD ω') :
    ∀ᵐ ω ∂φ, GlobalAtMostOne G ω := by
  have hpre : ∀ᵐ ω ∂φ, dualMeasurableEquiv edge ω ∈
      {ω' | NoInfiniteOpenCluster GD ω'} :=
    (ae_map_iff (dualMeasurableEquiv edge).measurable.aemeasurable
      (measurableSet_noInfiniteOpenCluster GD)).mp hdual
  filter_upwards [hpre] with ω hω
  exact hgeometry ω hω

/-- At least one infinite cluster and at most one infinite cluster, in the
actual global graph semantics used by the FK development. -/
def ExactlyOneInfiniteCluster {V : Type*} (G : SimpleGraph V)
    (ω : G.edgeSet → Bool) : Prop :=
  HasInfiniteCluster G ω ∧ GlobalAtMostOne G ω

/-- With primal supercriticality as well as dual nonpercolation, the primal
law has exactly one infinite open component almost surely. -/
theorem ae_exactlyOneInfiniteCluster
    {V F : Type*} [Countable V] [Countable F]
    (G : SimpleGraph V) (GD : SimpleGraph F) (edge : G.edgeSet ≃ GD.edgeSet)
    (φ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure φ]
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge)
    (hsuper : ∀ᵐ ω ∂φ, HasInfiniteCluster G ω)
    (hdual : ∀ᵐ ω' ∂(Measure.map (dualMeasurableEquiv edge) φ),
      NoInfiniteOpenCluster GD ω') :
    ∀ᵐ ω ∂φ, ExactlyOneInfiniteCluster G ω := by
  filter_upwards [hsuper,
    ae_globalAtMostOne_of_ae_dual_noInfiniteOpenCluster G GD edge φ hgeometry hdual]
    with ω hsuperω hunique
  exact ⟨hsuperω, hunique⟩

/-- A nonpercolating stochastic majorant for the dual law gives the required
almost-sure dual input. -/
theorem ae_exactlyOneInfiniteCluster_of_dual_stochDom
    {V F : Type*} [Countable V] [Countable F]
    (G : SimpleGraph V) (GD : SimpleGraph F) (edge : G.edgeSet ≃ GD.edgeSet)
    (φ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure φ]
    (ρ : Measure (GD.edgeSet → Bool)) [IsProbabilityMeasure ρ]
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge)
    (hdom : StochDom (Measure.map (dualMeasurableEquiv edge) φ) ρ)
    (hzero : ρ {ω | HasInfiniteCluster GD ω} = 0)
    (hsuper : ∀ᵐ ω ∂φ, HasInfiniteCluster G ω) :
    ∀ᵐ ω ∂φ, ExactlyOneInfiniteCluster G ω := by
  apply ae_exactlyOneInfiniteCluster G GD edge φ hgeometry hsuper
  exact ae_noInfiniteOpenCluster_of_stochDom GD _ ρ hdom hzero

/-- A full-mass increasing event remains full under a lower stochastic
bound. -/
theorem ae_hasInfiniteCluster_of_stochDom_of_measure_eq_one {V : Type*}
    [Countable V] (G : SimpleGraph V) (ρ μ : Measure (G.edgeSet → Bool))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (hdom : StochDom ρ μ) (hone : ρ {ω | HasInfiniteCluster G ω} = 1) :
    ∀ᵐ ω ∂μ, HasInfiniteCluster G ω := by
  have hμ : μ {ω | HasInfiniteCluster G ω} = 1 := by
    apply le_antisymm
    · calc
        μ {ω | HasInfiniteCluster G ω} ≤ μ Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := IsProbabilityMeasure.measure_univ
    · rw [← hone]
      apply hdom _ (measurableSet_hasInfiniteCluster G)
      rintro ω ζ hle ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [clusterAvoid_empty_eq] at hx ⊢
      exact hx.mono fun y hy => hy.mono_config hle
  have hnull : μ {ω | HasInfiniteCluster G ω}ᶜ = 0 := by
    rw [measure_compl (measurableSet_hasInfiniteCluster G) (measure_ne_top μ _),
      hμ, IsProbabilityMeasure.measure_univ, tsub_self]
  have hae := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with ω hω
  simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hω

/-- **Exact enhanced-Bernoulli form of Theorem 1.11's cluster step.**  The
primal inhomogeneous product `p` is a lower bound for the FK law.  Its exact
complementary dual product is nonpercolating, while the primal product is
supercritical.  Both oriented phase inputs are on the actual graph edge
types, with no schematic `HasInfinite` or `NoDualInfinite` predicates. -/
theorem ae_exactlyOneInfiniteCluster_of_primal_bernoulliProduct_stochDom
    {V F : Type*} [Countable V] [Countable F]
    (G : SimpleGraph V) (GD : SimpleGraph F) (edge : G.edgeSet ≃ GD.edgeSet)
    (p : G.edgeSet → unitInterval) (φ : Measure (G.edgeSet → Bool))
    [IsProbabilityMeasure φ]
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge)
    (hlower : StochDom (bernoulliProduct p) φ)
    (hzero : bernoulliProduct (fun f => σ (p (edge.symm f)))
      {ω | HasInfiniteCluster GD ω} = 0)
    (hone : bernoulliProduct p {ω | HasInfiniteCluster G ω} = 1) :
    ∀ᵐ ω ∂φ, ExactlyOneInfiniteCluster G ω := by
  have hsuper : ∀ᵐ ω ∂φ, HasInfiniteCluster G ω :=
    ae_hasInfiniteCluster_of_stochDom_of_measure_eq_one G (bernoulliProduct p) φ
      hlower hone
  apply ae_exactlyOneInfiniteCluster_of_dual_stochDom G GD edge φ
    (bernoulliProduct (fun f => σ (p (edge.symm f)))) hgeometry _ hzero hsuper
  exact dual_stochDom_bernoulliProduct edge p φ hlower

/-- Complementation transports agreement on a finite primal edge support to
agreement on its image in the dual. -/
lemma dualConfig_agree_on_image {E E' : Type*} (edge : E ≃ E')
    {ω ζ : E → Bool} {D : Set E} (hagree : ∀ e ∈ D, ω e = ζ e) :
    ∀ f ∈ edge '' D, dualConfig edge ω f = dualConfig edge ζ f := by
  rintro f ⟨e, he, rfl⟩
  simp only [dualConfig, Equiv.symm_apply_apply, hagree e he]

lemma finite_image_dual_support {E E' : Type*} (edge : E ≃ E') {D : Set E}
    (hD : D.Finite) : (edge '' D).Finite := hD.image edge

end

end FK.Planar
