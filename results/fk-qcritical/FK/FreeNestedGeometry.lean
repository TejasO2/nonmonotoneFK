import FK.GrowingFamilyDLR
import FK.GraphConnectionTransport
import FK.GlobalFiniteEnergy
import FK.EndpointGlobalFiniteEnergy
import FK.StageEventGeometry
import FK.MetricGrowingFamily
import FK.CoherentAllBoxes

/-! The free specification on nested boxes embedded in one simple graph. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- Closing the small-box interior after restricting a global configuration is
simply closing those global coordinates. -/
lemma closeInside_exteriorRestriction_apply {E : Type*} (B : FiniteBox E)
    (ω : Configuration E) (e : E) :
    closeInside B (FKLimit.exteriorRestriction B.edges ω) e =
      if e ∈ B.edges then false else ω e := by
  by_cases he : e ∈ B.edges <;>
    simp [closeInside, FiniteBox.glue, FKLimit.exteriorRestriction, he]

/-- Nested free boundaries agree on every exterior obtained from one global
configuration.  This is the geometric Markov identity behind the free
convention; no uniqueness or probabilistic hypothesis is involved. -/
theorem inducedBoundary_free_exteriorRestriction
    {B C : FiniteBox G.edgeSet} (N : NestedBox B C)
    (dataB : SimpleGraphBoxData G (fun _ : ℕ => B))
    (dataC : SimpleGraphBoxData G (fun _ : ℕ => C))
    (hvert : ∀ x : B.Vertex, dataC.vertex 0 (N.vert x) = dataB.vertex 0 x)
    (hinj : Function.Injective (dataC.vertex 0))
    (η : C.Exterior) (ω : Configuration G.edgeSet)
    (hω : ∀ (e : G.edgeSet) (he : e ∉ C.edges), ω e = η ⟨e, he⟩) :
    inducedBoundary N (dataC.free.partition 0 η)
        (FKLimit.exteriorRestriction B.edges ω) =
      dataB.free.partition 0 (FKLimit.exteriorRestriction B.edges ω) := by
  classical
  let ηB : B.Exterior := FKLimit.exteriorRestriction B.edges ω
  let ω₀ : Configuration G.edgeSet := closeInside B ηB
  have hω₀ (e : G.edgeSet) : ω₀ e = if e ∈ B.edges then false else ω e := by
    by_cases he : e ∈ B.edges <;>
      simp [ω₀, ηB, closeInside, FiniteBox.glue, FKLimit.exteriorRestriction, he]
  have houtC : FKLimit.exteriorRestriction C.edges ω₀ = η := by
    funext e
    change ω₀ e.1 = η e
    have heB : e.1 ∉ B.edges := fun he => e.2 (N.edge_sub _ he)
    rw [hω₀]
    simp only [heB, ↓reduceIte]
    exact hω e.1 e.2
  have hcloseC : closeInside C (FKLimit.exteriorRestriction C.edges ω₀) =
      closeInside C η := by rw [houtC]
  have hfreeC : dataC.free.partition 0
      (FKLimit.exteriorRestriction C.edges ω₀) = dataC.free.partition 0 η := by
    change openPathSetoid G (closeInside C
      (FKLimit.exteriorRestriction C.edges ω₀)) Set.univ (dataC.vertex 0) = _
    rw [hcloseC]
    rfl
  have hconfig : FK.Finite.SpecificationNesting.interiorClosed N.ide
      (FK.Finite.SpecificationNesting.combine N.ide (fun _ => false)
        (annulusOfExterior N ηB)) = (fun e : C.edges => ω₀ e.1) := by
    funext e
    by_cases he : (e.1 : G.edgeSet) ∈ B.edges
    · have heI : e ∈ N.ide := he
      simp [FK.Finite.SpecificationNesting.interiorClosed, heI, hω₀, he]
    · have heI : e ∉ N.ide := he
      have hval : annulusOfExterior N ηB
          (⟨e, heI⟩ : {f : C.graph.Edge // f ∉ N.ide}) = ω e.1 := by
        rfl
      simp [FK.Finite.SpecificationNesting.interiorClosed,
        FK.Finite.SpecificationNesting.combine, heI, hval, hω₀, he]
  apply Setoid.ext
  intro x y
  change (FK.Finite.SpecificationNesting.fixedGraph N.ide
      (dataC.free.partition 0 η)
      (FK.Finite.SpecificationNesting.combine N.ide (fun _ => false)
        (annulusOfExterior N ηB))).Reachable (N.vert x) (N.vert y) ↔ _
  change _ ↔ OpenConnected G ω₀ Set.univ (dataB.vertex 0 x) (dataB.vertex 0 y)
  rw [← hvert x, ← hvert y]
  rw [openConnected_iff_freeComponents dataC hinj ω₀ (N.vert x) (N.vert y)]
  change (C.graph.connectionGraph (dataC.free.partition 0 η)
      (FK.Finite.SpecificationNesting.interiorClosed N.ide
        (FK.Finite.SpecificationNesting.combine N.ide (fun _ => false)
          (annulusOfExterior N ηB)))).Reachable (N.vert x) (N.vert y) ↔ _
  rw [hconfig, hfreeC]

end FK.NestedFinDLR

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

local instance boundaryPartitionMeasurableSpaceFree (W : Type*) : MeasurableSpace (Setoid W) := ⊤

local instance finiteSetoidFree (W : Type*) [Finite W] : Finite (Setoid W) := by
  classical
  apply Finite.of_injective (fun α : Setoid W => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- A genuine larger-box FK law with its actual free exterior boundary is DLR
at every nested smaller box for the canonical free specification. -/
theorem isDLR_free_conditionalLaw_nested
    {B C : FiniteBox G.edgeSet} (N : NestedBox B C)
    (dataB : SimpleGraphBoxData G (fun _ : ℕ => B))
    (dataC : SimpleGraphBoxData G (fun _ : ℕ => C))
    (hvert : ∀ x : B.Vertex, dataC.vertex 0 (N.vert x) = dataB.vertex 0 x)
    (hinj : Function.Injective (dataC.vertex 0))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (η : C.Exterior) :
    B.IsDLR hq hp₁.le (dataB.free.partition 0) (dataB.measurable_components 0)
      (C.conditionalLaw hq hp₁.le (fun _ => dataC.free.partition 0 η) η) := by
  classical
  have hD : B.IsDLR hq hp₁.le
      (inducedBoundary N (dataC.free.partition 0 η))
      (measurable_inducedBoundary N (dataC.free.partition 0 η))
      (C.conditionalLaw hq hp₁.le (fun _ => dataC.free.partition 0 η) η) :=
    isDLR_conditionalLaw_nested (N := N) (hq := hq) (hp₀ := hp₀) (hp₁ := hp₁)
      (dataC.free.partition 0 η) η
  refine B.isDLR_of_ae_partition_eq hq hp₁.le _ _
    (measurable_inducedBoundary N (dataC.free.partition 0 η))
    (dataB.measurable_components 0) _ hD ?_
  let f : C.Interior → B.Exterior := fun ζ =>
    FKLimit.exteriorRestriction B.edges (C.glue (η, ζ))
  have hf : Measurable f :=
    FKLimit.measurable_exteriorRestriction B.edges |>.comp (C.measurable_glue_const_left η)
  have hmap : (B.exteriorMeasure
      (C.conditionalLaw hq hp₁.le (fun _ => dataC.free.partition 0 η) η) :
        Measure B.Exterior) =
      Measure.map f (C.graph.fkMeasure hq hp₁.le (dataC.free.partition 0 η)) := by
    change Measure.map (FKLimit.exteriorRestriction B.edges)
      (Measure.map (fun ζ : C.Interior => C.glue (η, ζ))
        (C.graph.fkMeasure hq hp₁.le (dataC.free.partition 0 η))) = _
    rw [Measure.map_map (FKLimit.measurable_exteriorRestriction B.edges)
      (C.measurable_glue_const_left η)]
    rfl
  rw [hmap]
  have hset : MeasurableSet {ζ : B.Exterior |
      inducedBoundary N (dataC.free.partition 0 η) ζ = dataB.free.partition 0 ζ} :=
    measurableSet_eq_fun (measurable_inducedBoundary N (dataC.free.partition 0 η))
      (dataB.measurable_components 0)
  refine (ae_map_iff hf.aemeasurable hset).2 ?_
  filter_upwards with ζ
  exact inducedBoundary_free_exteriorRestriction N dataB dataC hvert hinj η
    (C.glue (η, ζ)) (fun e he => by simp [FiniteBox.glue, he])

end FK.NestedFinDLR

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- The actual finite-volume FK law on the `n`-th box with the boundary induced
by one fixed global exterior configuration. -/
noncomputable def externalFreeLaw {F : GrowingFamily G.edgeSet}
    (data : SimpleGraphBoxData G F.box) (ξ : Configuration G.edgeSet)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (n : ℕ) :
    ProbabilityMeasure (Configuration G.edgeSet) :=
  (F.box n).conditionalLaw hq hp
    (fun _ => data.free.partition n (FKLimit.exteriorRestriction (F.box n).edges ξ))
    (FKLimit.exteriorRestriction (F.box n).edges ξ)

/-- **Fixed-exterior weak-limit half of Proposition 1.8(2).**  On any genuine
nested graph exhaustion, a weak limit of the FK laws generated by one fixed
exterior configuration is DLR for the free specification, and hence for every
geometric convention, whenever its law has at most one infinite open cluster.
The parameter range is the full interior range; endpoint rates are handled by
the existing deterministic endpoint theorems. -/
theorem mem_dlrMeasures_of_tendsto_externalFreeLaw_of_globalAtMostOne
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      data.vertex n ((F.nest m n hmn).vert x) = data.vertex m x)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : Configuration G.edgeSet) (Ψ : BoundaryAssignment F.box)
    (hΨ : IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLaw data ξ hq hp₁.le n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures F.exh Ψ hq hp₁.le := by
  classical
  have hDLR : ∀ m : ℕ, ∀ᶠ n in atTop, (F.box m).IsDLR hq hp₁.le
      (data.free.partition m) (data.measurable_components m)
      (externalFreeLaw data ξ hq hp₁.le n) := by
    intro m
    filter_upwards [eventually_ge_atTop m] with n hmn
    exact isDLR_free_conditionalLaw_nested (F.nest m n hmn)
      (constantBoxData data m) (constantBoxData data n)
      (hvert m n hmn) (hinj n) hq hp₀ hp₁
        (FKLimit.exteriorRestriction (F.box n).edges ξ)
  have hunique : AEAtMostOne data.geometry μ := by
    intro m
    have hgood := GlobalFiniteEnergy.ae_globalAtMostOne_closeInside_of_tendsto_of_isDLR
      (F.box m) hq hp₀ hp₁ (data.free.partition m) (data.measurable_components m)
      hμ (hDLR m) hglobal
    filter_upwards [hgood] with η hη
    intro x y hx hy
    exact hη (data.vertex m x) (data.vertex m y) hx hy
  have hsource : μ ∈ DLRMeasures F.exh data.free hq hp₁.le := by
    apply NoncoherentStabilization.mem_dlrMeasures_of_tendsto_of_locallyStabilizes_of_atMostOne
      F.exh data (fun _ : ℕ => data.free) data.free data.free_isGeometric
      (hq := hq) (hp := hp₁.le) hμ hDLR ?_ hunique
    intro m
    filter_upwards with η
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    exact Eventually.of_forall (fun _ _ _ => rfl)
  exact ConventionTransport.mem_dlrMeasures_of_atMostOne F.exh data.geometry
    data.free Ψ hq hp₁.le data.free_isGeometric hΨ hsource hunique

end FK.NestedFinDLR

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- All-rate form of the fixed-exterior weak-limit theorem. -/
theorem mem_dlrMeasures_of_tendsto_externalFreeLaw_of_globalAtMostOne_of_le_one
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      data.vertex n ((F.nest m n hmn).vert x) = data.vertex m x)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : Configuration G.edgeSet) (Ψ : BoundaryAssignment F.box)
    (hΨ : IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLaw data ξ hq hp n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures F.exh Ψ hq hp := by
  classical
  by_cases hpzero : p = 0
  · subst p
    exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_zero_of_tendsto_conditionalLaw
      F.exh hq
      (fun n _ => data.free.partition n (FKLimit.exteriorRestriction (F.box n).edges ξ))
      (fun n => FKLimit.exteriorRestriction (F.box n).edges ξ) Ψ hμ
  by_cases hpone : p = 1
  · subst p
    exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_one_of_tendsto_conditionalLaw
      F.exh hq
      (fun n _ => data.free.partition n (FKLimit.exteriorRestriction (F.box n).edges ξ))
      (fun n => FKLimit.exteriorRestriction (F.box n).edges ξ) Ψ hμ
  have hp₀ : 0 < p := pos_iff_ne_zero.mpr hpzero
  have hp₁ : p < 1 := lt_of_le_of_ne hp hpone
  exact mem_dlrMeasures_of_tendsto_externalFreeLaw_of_globalAtMostOne
    F data hinj hvert hq hp₀ hp₁ ξ Ψ hΨ hμ hglobal

/-- Canonical metric-box instance of the all-rate fixed-exterior theorem. -/
theorem mem_dlrMeasures_of_tendsto_metricExternalFreeLaw_of_globalAtMostOne
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : Configuration G.edgeSet) (Ψ : BoundaryAssignment (NestedMetricGeometry.metricBox hG o))
    (hΨ : IsGeometric (NestedMetricGeometry.metricBoxData hG o).geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLaw (F := metricGrowingFamily hG o)
      (NestedMetricGeometry.metricBoxData hG o) ξ hq hp n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures (NestedMetricGeometry.metricBoxExhaustion hG o) Ψ hq hp := by
  exact mem_dlrMeasures_of_tendsto_externalFreeLaw_of_globalAtMostOne_of_le_one
    (metricGrowingFamily hG o) (NestedMetricGeometry.metricBoxData hG o)
    (NestedMetricGeometry.metricBoxData_vertex_injective hG o)
    (fun _ _ h _ => metricGrowingFamily_compat hG o h _)
    hq hp ξ Ψ hΨ hμ hglobal

end FK.NestedFinDLR

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- Fixed-exterior Proposition 1.8(2) with the target DLR equations tested at
**every** finite box.  The supplied all-box convention is genuinely coherent
and geometric; compatibility is not inferred from a bare assignment. -/
theorem mem_allBoxDLRMeasures_of_tendsto_externalFreeLaw_of_globalAtMostOne
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : CoherentAllBoxes.AllBoxSimpleGraphBoxData G)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : CoherentAllBoxes.AllBoxConvention G.edgeSet hq hp)
    (hΦ : CoherentAllBoxes.IsAllBoxGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective ((data.restrictionData F.exh).vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      (data.restrictionData F.exh).vertex n ((F.nest m n hmn).vert x) =
        (data.restrictionData F.exh).vertex m x)
    (ξ : Configuration G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLaw (data.restrictionData F.exh)
      ξ hq hp n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ CoherentAllBoxes.AllBoxDLRMeasures Φ := by
  apply (CoherentAllBoxes.mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction
    F.exh Φ μ).2
  exact mem_dlrMeasures_of_tendsto_externalFreeLaw_of_globalAtMostOne_of_le_one
    F (data.restrictionData F.exh) hinj hvert hq hp ξ
    (CoherentAllBoxes.restriction F.exh Φ).toBoundaryAssignment
    (CoherentAllBoxes.isGeometric_restriction F.exh data.geometry Φ hΦ)
    hμ hglobal

end FK.NestedFinDLR

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- The finite-volume law with the actual free boundary induced by the `n`-th
members of an arbitrary exterior-configuration schedule. -/
noncomputable def externalFreeLawAt {F : GrowingFamily G.edgeSet}
    (data : SimpleGraphBoxData G F.box) (η : ∀ n, (F.box n).Exterior)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (n : ℕ) :
    ProbabilityMeasure (Configuration G.edgeSet) :=
  (F.box n).conditionalLaw hq hp (fun _ => data.free.partition n (η n)) (η n)

/-- **General exterior-schedule weak-limit half of Proposition 1.8(2).**
Every larger law has the exact smaller free DLR equation proved above.  Global
at-most-one-cluster uniqueness at the weak limit supplies exterior uniqueness
and quasilocality; after closure, all geometric target conventions coincide. -/
theorem mem_dlrMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      data.vertex n ((F.nest m n hmn).vert x) = data.vertex m x)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (η : ∀ n, (F.box n).Exterior) (Ψ : BoundaryAssignment F.box)
    (hΨ : IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLawAt data η hq hp₁.le n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures F.exh Ψ hq hp₁.le := by
  classical
  have hDLR : ∀ m : ℕ, ∀ᶠ n in atTop, (F.box m).IsDLR hq hp₁.le
      (data.free.partition m) (data.measurable_components m)
      (externalFreeLawAt data η hq hp₁.le n) := by
    intro m
    filter_upwards [eventually_ge_atTop m] with n hmn
    exact isDLR_free_conditionalLaw_nested (F.nest m n hmn)
      (constantBoxData data m) (constantBoxData data n)
      (hvert m n hmn) (hinj n) hq hp₀ hp₁ (η n)
  have hunique : AEAtMostOne data.geometry μ := by
    intro m
    have hgood := GlobalFiniteEnergy.ae_globalAtMostOne_closeInside_of_tendsto_of_isDLR
      (F.box m) hq hp₀ hp₁ (data.free.partition m) (data.measurable_components m)
      hμ (hDLR m) hglobal
    filter_upwards [hgood] with η hη
    intro x y hx hy
    exact hη (data.vertex m x) (data.vertex m y) hx hy
  have hsource : μ ∈ DLRMeasures F.exh data.free hq hp₁.le := by
    apply NoncoherentStabilization.mem_dlrMeasures_of_tendsto_of_locallyStabilizes_of_atMostOne
      F.exh data (fun _ : ℕ => data.free) data.free data.free_isGeometric
      (hq := hq) (hp := hp₁.le) hμ hDLR ?_ hunique
    intro m
    filter_upwards with η
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    exact Eventually.of_forall (fun _ _ _ => rfl)
  exact ConventionTransport.mem_dlrMeasures_of_atMostOne F.exh data.geometry
    data.free Ψ hq hp₁.le data.free_isGeometric hΨ hsource hunique

/-- All-rate arbitrary-exterior-schedule form. -/
theorem mem_dlrMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne_of_le_one
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      data.vertex n ((F.nest m n hmn).vert x) = data.vertex m x)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (η : ∀ n, (F.box n).Exterior) (Ψ : BoundaryAssignment F.box)
    (hΨ : IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLawAt data η hq hp n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures F.exh Ψ hq hp := by
  classical
  by_cases hpzero : p = 0
  · subst p
    exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_zero_of_tendsto_conditionalLaw
      F.exh hq (fun n _ => data.free.partition n (η n)) η Ψ hμ
  by_cases hpone : p = 1
  · subst p
    exact EndpointGlobalFiniteEnergy.mem_dlrMeasures_one_of_tendsto_conditionalLaw
      F.exh hq (fun n _ => data.free.partition n (η n)) η Ψ hμ
  have hp₀ : 0 < p := pos_iff_ne_zero.mpr hpzero
  have hp₁ : p < 1 := lt_of_le_of_ne hp hpone
  exact mem_dlrMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne
    F data hinj hvert hq hp₀ hp₁ η Ψ hΨ hμ hglobal

/-- Arbitrary-exterior-schedule version with DLR equations at every finite box. -/
theorem mem_allBoxDLRMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : CoherentAllBoxes.AllBoxSimpleGraphBoxData G)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : CoherentAllBoxes.AllBoxConvention G.edgeSet hq hp)
    (hΦ : CoherentAllBoxes.IsAllBoxGeometric data.geometry Φ)
    (hinj : ∀ n, Function.Injective ((data.restrictionData F.exh).vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      (data.restrictionData F.exh).vertex n ((F.nest m n hmn).vert x) =
        (data.restrictionData F.exh).vertex m x)
    (η : ∀ n, (F.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLawAt (data.restrictionData F.exh)
      η hq hp n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ CoherentAllBoxes.AllBoxDLRMeasures Φ := by
  apply (CoherentAllBoxes.mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction
    F.exh Φ μ).2
  exact mem_dlrMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne_of_le_one
    F (data.restrictionData F.exh) hinj hvert hq hp η
    (CoherentAllBoxes.restriction F.exh Φ).toBoundaryAssignment
    (CoherentAllBoxes.isGeometric_restriction F.exh data.geometry Φ hΦ)
    hμ hglobal

/-- Metric-box realization of the arbitrary-exterior-schedule theorem. -/
theorem mem_dlrMeasures_of_tendsto_metricExternalFreeLawAt_of_globalAtMostOne
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (η : ∀ n, (NestedMetricGeometry.metricBox hG o n).Exterior)
    (Ψ : BoundaryAssignment (NestedMetricGeometry.metricBox hG o))
    (hΨ : IsGeometric (NestedMetricGeometry.metricBoxData hG o).geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => externalFreeLawAt (F := metricGrowingFamily hG o)
      (NestedMetricGeometry.metricBoxData hG o) η hq hp n) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures (NestedMetricGeometry.metricBoxExhaustion hG o) Ψ hq hp := by
  exact mem_dlrMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne_of_le_one
    (metricGrowingFamily hG o) (NestedMetricGeometry.metricBoxData hG o)
    (NestedMetricGeometry.metricBoxData_vertex_injective hG o)
    (fun _ _ h _ => metricGrowingFamily_compat hG o h _)
    hq hp η Ψ hΨ hμ hglobal

end FK.NestedFinDLR

namespace FK.NestedFinDLR

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.NestedMixture
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- The two source branches of `FK(p,q)` in the paper: a Gibbs law for some
coherent geometric convention, or a weak limit of actual exterior-configuration
FK laws.  Arbitrary unrelated setoid schedules are deliberately not included. -/
inductive AllBoxFKMeasureSource (F : GrowingFamily G.edgeSet)
    (data : CoherentAllBoxes.AllBoxSimpleGraphBoxData G)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet)) : Prop where
  | gibbs (Φ : CoherentAllBoxes.AllBoxConvention G.edgeSet hq hp)
      (hΦ : CoherentAllBoxes.IsAllBoxGeometric data.geometry Φ)
      (hμ : μ ∈ CoherentAllBoxes.AllBoxDLRMeasures Φ) : AllBoxFKMeasureSource F data hq hp μ
  | externalLimit (η : ∀ n, (F.box n).Exterior)
      (hμ : Tendsto (fun n => externalFreeLawAt (data.restrictionData F.exh)
        η hq hp n) atTop (𝓝 μ)) : AllBoxFKMeasureSource F data hq hp μ

/-- **Proposition 1.8(2), all-box source-union form.**  At every `q > 0` and
`0 ≤ p ≤ 1`, an FK measure in either source branch which almost surely has at
most one infinite open cluster is DLR for every coherent geometric convention,
at every finite box. -/
theorem proposition_1_8_2_allBox
    [G.LocallyFinite] (F : GrowingFamily G.edgeSet)
    (data : CoherentAllBoxes.AllBoxSimpleGraphBoxData G)
    (hinj : ∀ n, Function.Injective ((data.restrictionData F.exh).vertex n))
    (hvert : ∀ (m n : ℕ) (hmn : m ≤ n) (x : (F.box m).Vertex),
      (data.restrictionData F.exh).vertex n ((F.nest m n hmn).vert x) =
        (data.restrictionData F.exh).vertex m x)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : CoherentAllBoxes.AllBoxConvention G.edgeSet hq hp)
    (hΦ : CoherentAllBoxes.IsAllBoxGeometric data.geometry Φ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hsource : AllBoxFKMeasureSource F data hq hp μ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ CoherentAllBoxes.AllBoxDLRMeasures Φ := by
  cases hsource with
  | gibbs Θ hΘ hμ =>
      exact CoherentAllBoxes.mem_allBoxDLRMeasures_of_globalAtMostOne_of_le_one
        F.exh data hq hp Θ Φ hΘ hΦ μ hμ hglobal
  | externalLimit η hμ =>
      exact mem_allBoxDLRMeasures_of_tendsto_externalFreeLawAt_of_globalAtMostOne
        F data Φ hΦ hinj hvert η hμ hglobal

end FK.NestedFinDLR
