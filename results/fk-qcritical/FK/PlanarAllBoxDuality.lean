import FK.PlanarAEKernelDuality
import FK.CoherentAllBoxesAdapters

/-!
# All-finite-box convention replacement and planar dual transport

The source proof of Theorem 1.11 starts with an arbitrary geometric convention,
but equation (12) is applied after replacing it by the exterior-component
convention at configurations having at most one infinite cluster.  The public
`DualLimit` interface instead assumes the DLR equations for the particular
convention entering its finite duality premise.

This file proves that replacement at every finite box for an actual global
simple graph.  Interior FK finite-volume measures have full support, so global
at-most-one uniqueness upgrades to at-most-one exterior uniqueness on almost
every exterior fibre.  All geometric source partitions therefore agree with
the canonical free exterior-component partition almost everywhere.  The DLR
kernel can be replaced on those fibres, after which the existing dual transport
applies.  No compatibility of the original convention is discarded: it is used
in its `AllBoxConvention` DLR class; the new conclusion is explicitly all-box.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.Planar.AllBoxDuality

open FK.InfiniteVolume
open FK.InfiniteVolume.CoherentAllBoxes
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u v

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- Measurability of the canonical free exterior-component partition on every
finite box, without selecting an exhaustion. -/
lemma measurable_components {V : Type u} {G : SimpleGraph V} [Countable V]
    (data : AllBoxSimpleGraphBoxData.{u, v} G) (B : FiniteBox.{u, v} G.edgeSet) :
    Measurable (data.geometry.components B) := by
  exact measurable_openPathSetoid G (closeInside B) (measurable_closeInside B)
    Set.univ (data.vertex B)

/-- Global at-most-one uniqueness gives exterior at-most-one uniqueness on
almost every fibre at every finite box. -/
lemma ae_atMostOne_exterior {V : Type u} {G : SimpleGraph V} [Countable V]
    (data : AllBoxSimpleGraphBoxData.{u, v} G) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω)
    (B : FiniteBox.{u, v} G.edgeSet) :
    ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      AtMostOneInfiniteCluster (data.geometry.components B η)
        (data.geometry.infinite B η) := by
  have hae := ae_forall_interior_of_ae_glue B hq hp₁.le
    (Φ.partition B) (Φ.measurable_partition B) μ (hμ B)
    (fun η ξ => fkMeasure_singleton_pos B hq hp₀ hp₁ (Φ.partition B) η ξ)
    (measurableSet_globalAtMostOne G) hglobal
  filter_upwards [hae] with η hη
  intro x y hx hy
  exact hη (fun _ => false) (data.vertex B x) (data.vertex B y) hx hy

/-- **All-box free-convention replacement.**  No exhaustion restriction and no
free-`AllBoxConvention` packaging are needed. -/
theorem isDLR_freeComponents_of_globalAtMostOne
    {V : Type u} {G : SimpleGraph V} [Countable V]
    (data : AllBoxSimpleGraphBoxData.{u, v} G) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω)
    (B : FiniteBox.{u, v} G.edgeSet) :
    B.IsDLR hq hp₁.le (data.geometry.components B) (measurable_components data B) μ := by
  apply B.isDLR_of_ae_partition_eq hq hp₁.le (Φ.partition B)
    (data.geometry.components B) (Φ.measurable_partition B)
    (measurable_components data B) μ (hμ B)
  filter_upwards [ae_atMostOne_exterior data hq hp₀ hp₁ Φ μ hμ hglobal B] with η hη
  exact eq_openComponents_of_finite_separation _ _ _ (hΦ.1 B η) (hΦ.2 B η) hη

/-- Equation (12) only needs to be supplied for the free exterior-component
representative.  Its complement then satisfies the dual DLR equations at every
box of an arbitrary family. -/
theorem isDLR_map_cfgDual_allBoxes_of_globalAtMostOne
    {V : Type u} {G : SimpleGraph V} [Countable V]
    {ι : Type*} (box : ι → FiniteBox.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)]
    (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (hfreeDual : ∀ i (η : (box i).Exterior) (ω : (box i).Interior),
      (box i).graph.fkPMF hq hp₁.le
          (data.geometry.components (box i) (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i η)
          (intDual (box i) ω))
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    ∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
      (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i) (hαD i)
      (ProbabilityMeasure.map μ (cfgDual G.edgeSet)) := by
  apply isDLR_map_cfgDual_allBoxes box Vd s t hq hp₁.le
    (fun i => data.geometry.components (box i))
    (fun i => measurable_components data (box i)) αD hαD hfreeDual μ
  intro i
  exact isDLR_freeComponents_of_globalAtMostOne data hq hp₀ hp₁ Φ hΦ μ hμ hglobal (box i)

/-- **All-convention primal DLR uniqueness from dual uniqueness.**  The old
`hdualizable` quantification over every original source convention is not an
input.  Only the actual free equation-(12) identity and uniqueness of the dual
class remain. -/
theorem eq_map_of_allBoxes_unique_dual_of_globalAtMostOne
    {V : Type u} {G : SimpleGraph V} [Countable V]
    {ι : Type*} (box : ι → FiniteBox.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)]
    (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (hfreeDual : ∀ i (η : (box i).Exterior) (ω : (box i).Interior),
      (box i).graph.fkPMF hq hp₁.le
          (data.geometry.components (box i) (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i η)
          (intDual (box i) ω))
    (ν₀ : ProbabilityMeasure (Configuration G.edgeSet))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration G.edgeSet),
      (∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
        (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i) (hαD i) ν) → ν = ν₀)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ = ProbabilityMeasure.map ν₀ (cfgDual G.edgeSet) := by
  apply eq_map_of_allBoxes_unique_dual box Vd s t hq hp₁.le
    (fun i => data.geometry.components (box i))
    (fun i => measurable_components data (box i)) αD hαD hfreeDual ν₀ huniq μ
  intro i
  exact isDLR_freeComponents_of_globalAtMostOne data hq hp₀ hp₁ Φ hΦ μ hμ hglobal (box i)

/-- Source-scope version with equation (12) required only almost everywhere
under the exterior marginals of the complemented primal law. -/
theorem isDLR_map_cfgDual_allBoxes_of_globalAtMostOne_of_ae
    {V : Type u} {G : SimpleGraph V} [Countable V]
    {ι : Type*} (box : ι → FiniteBox.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)]
    (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω)
    (hfreeDual : ∀ i, ∀ᵐ η ∂((box i).exteriorMeasure
      (ProbabilityMeasure.map μ (cfgDual G.edgeSet)) : Measure (box i).Exterior),
      ∀ ω : (box i).Interior,
      (box i).graph.fkPMF hq hp₁.le
          (data.geometry.components (box i) (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i η)
          (intDual (box i) ω)) :
    ∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
      (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i) (hαD i)
      (ProbabilityMeasure.map μ (cfgDual G.edgeSet)) := by
  apply isDLR_map_cfgDual_allBoxes_of_ae box Vd s t hq hp₁.le
    (fun i => data.geometry.components (box i))
    (fun i => measurable_components data (box i)) αD hαD μ _ hfreeDual
  intro i
  exact isDLR_freeComponents_of_globalAtMostOne data hq hp₀ hp₁ Φ hΦ μ hμ hglobal (box i)

/-- **All-box primal identification from a.e. equation (12).**  There is no
pointwise duality premise on the null set of exterior configurations with
several infinite components. -/
theorem eq_map_of_allBoxes_unique_dual_of_globalAtMostOne_of_ae
    {V : Type u} {G : SimpleGraph V} [Countable V]
    {ι : Type*} (box : ι → FiniteBox.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)]
    (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (ν₀ : ProbabilityMeasure (Configuration G.edgeSet))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration G.edgeSet),
      (∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
        (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i) (hαD i) ν) → ν = ν₀)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω)
    (hfreeDual : ∀ i, ∀ᵐ η ∂((box i).exteriorMeasure
      (ProbabilityMeasure.map μ (cfgDual G.edgeSet)) : Measure (box i).Exterior),
      ∀ ω : (box i).Interior,
      (box i).graph.fkPMF hq hp₁.le
          (data.geometry.components (box i) (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i η)
          (intDual (box i) ω)) :
    μ = ProbabilityMeasure.map ν₀ (cfgDual G.edgeSet) := by
  have hdual : ∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
      (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i) (hαD i)
      (ProbabilityMeasure.map μ (cfgDual G.edgeSet)) :=
    isDLR_map_cfgDual_allBoxes_of_globalAtMostOne_of_ae box data Vd s t hq hp₀ hp₁
      Φ hΦ αD hαD μ hμ hglobal hfreeDual
  have hkey : ProbabilityMeasure.map μ (cfgDual G.edgeSet) = ν₀ := huniq _ hdual
  calc
    μ = ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual G.edgeSet))
        (cfgDual G.edgeSet) := (map_cfgDual_map_cfgDual μ).symm
    _ = ProbabilityMeasure.map ν₀ (cfgDual G.edgeSet) := by rw [hkey]

/-- **Theorem 1.11, all-box DLR and enhanced-Bernoulli component.**  Global
at-most-one is derived internally from the genuine planar geometry and the two
inhomogeneous product phase inputs.  Every source-convention DLR law satisfying
those bounds is the complement of the unique dual law, and carries exactly one
infinite primal component almost surely. -/
theorem eq_dual_and_ae_exactlyOne_of_allBoxes_of_ae
    {V F : Type u} [Countable V] [Countable F]
    {G : SimpleGraph V} {GD : SimpleGraph F} (edge : G.edgeSet ≃ GD.edgeSet)
    {ι : Type*} (box : ι → FiniteBox.{u, v} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, v} G)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)]
    (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : AllBoxConvention.{u, v} G.edgeSet hq hp₁.le)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (ν₀ : ProbabilityMeasure (Configuration G.edgeSet))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration G.edgeSet),
      (∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
        (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i) (hαD i) ν) → ν = ν₀)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ AllBoxDLRMeasures Φ)
    (hfreeDual : ∀ i, ∀ᵐ η ∂((box i).exteriorMeasure
      (ProbabilityMeasure.map μ (cfgDual G.edgeSet)) : Measure (box i).Exterior),
      ∀ ω : (box i).Interior,
      (box i).graph.fkPMF hq hp₁.le
          (data.geometry.components (box i) (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp₁.le) (αD i η)
          (intDual (box i) ω))
    (rate : G.edgeSet → unitInterval)
    (hlower : FK.Configuration.StochDom (FK.Configuration.bernoulliProduct rate) (μ : Measure _))
    (hzero : FK.Configuration.bernoulliProduct (fun f => σ (rate (edge.symm f)))
      {ω | FK.ClusterCover.HasInfiniteCluster GD ω} = 0)
    (hone : FK.Configuration.bernoulliProduct rate
      {ω | FK.ClusterCover.HasInfiniteCluster G ω} = 1)
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge) :
    μ = ProbabilityMeasure.map ν₀ (cfgDual G.edgeSet) ∧
      ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ExactlyOneInfiniteCluster G ω := by
  have hcluster : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ExactlyOneInfiniteCluster G ω :=
    ae_exactlyOneInfiniteCluster_of_primal_bernoulliProduct_stochDom
      G GD edge rate (μ : Measure (Configuration G.edgeSet)) hgeometry hlower hzero hone
  have hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω := by
    filter_upwards [hcluster] with ω hω
    exact hω.2
  exact ⟨eq_map_of_allBoxes_unique_dual_of_globalAtMostOne_of_ae box data Vd s t
    hq hp₀ hp₁ Φ hΦ αD hαD ν₀ huniq μ hμ hglobal hfreeDual, hcluster⟩


end

end FK.Planar.AllBoxDuality
