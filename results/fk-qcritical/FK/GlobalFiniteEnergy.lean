import FK.NonlocalFiniteVolume

/-!
# Finite-energy closure and global uniqueness for nonlocal FK weak limits

This module proves the pre-DLR finite-energy step needed to apply
`NonlocalFiniteVolume` under global at-most-one-cluster uniqueness.  A uniform
lower bound on every finite FK point mass gives a close-box domination bound
for every DLR approximant.  That bound passes to the weak limit, and hence the
closed-box law is absolutely continuous with respect to the limit law.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.GlobalFiniteEnergy

open ConventionGeometry ConventionTransport

noncomputable section

/-- A continuous-pushforward domination bound passes through weak convergence.

The proof first passes integrals of bounded continuous functions to the limit,
then obtains the inequality on closed sets by outer approximation, and finally
on all Borel sets by compact inner regularity.  This last step is essential for
applications to nonlocal zero-one events. -/
theorem measure_map_le_smul_of_tendsto
    {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [SecondCountableTopology X]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X] [T2Space X]
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hμ : Tendsto μs l (𝓝 μ))
    (T : X → X) (hT : Continuous T) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hbound : ∀ᶠ i in l,
      (((μs i).map T : ProbabilityMeasure X) : Measure X) ≤
        c • (μs i : Measure X)) :
    ((μ.map T : ProbabilityMeasure X) : Measure X) ≤
      c • (μ : Measure X) := by
  have hmap : Tendsto (fun i => (μs i).map T) l
      (𝓝 (μ.map T)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hμ hT
  have htest (f : BoundedContinuousFunction X ℝ≥0) :
      (∫⁻ x, (f x : ℝ≥0∞) ∂(μ.map T : Measure X)) ≤
        c * ∫⁻ x, (f x : ℝ≥0∞) ∂(μ : Measure X) := by
    apply le_of_tendsto_of_tendsto
      (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hmap f)
      (ENNReal.Tendsto.const_mul
        (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ f) (Or.inr hc))
    filter_upwards [hbound] with i hi
    calc
      (∫⁻ x, (f x : ℝ≥0∞) ∂((μs i).map T : Measure X)) ≤
          ∫⁻ x, (f x : ℝ≥0∞) ∂(c • (μs i : Measure X)) :=
        lintegral_mono' hi le_rfl
      _ = c * ∫⁻ x, (f x : ℝ≥0∞) ∂(μs i : Measure X) := by
        rw [lintegral_smul_measure]
        rfl
  have hclosed {F : Set X} (hF : IsClosed F) :
      (μ.map T : Measure X) F ≤ (c • (μ : Measure X)) F := by
    rw [Measure.smul_apply, smul_eq_mul]
    apply le_of_tendsto_of_tendsto
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF
        (μ.map T : Measure X))
      (ENNReal.Tendsto.const_mul
        (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (μ : Measure X)) (Or.inr hc))
    exact Eventually.of_forall fun n => htest (hF.apprSeq n)
  apply Measure.le_iff.mpr
  intro A hA
  rw [hA.measure_eq_iSup_isCompact (μ.map T : Measure X)]
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  exact (hclosed hK.isClosed).trans (measure_mono hKA)

/-- Replace every coordinate of a finite box by `false`, preserving its exterior. -/
def closeBox {E : Type*} (B : FiniteBox E) : Configuration E → Configuration E :=
  fun ω => B.glue ((B.split ω).1, fun _ => false)

lemma closeBox_eq_glue {E : Type*} (B : FiniteBox E) (η : B.Exterior)
    (ξ : B.Interior) : closeBox B (B.glue (η, ξ)) = B.glue (η, fun _ => false) := by
  rw [closeBox, B.split_glue]

lemma closeBox_eq_closeInside_split {E : Type*} (B : FiniteBox E)
    (ω : Configuration E) :
    closeBox B ω = closeInside B (B.split ω).1 := by
  rfl

@[simp] lemma closeBox_exterior {E : Type*} (B : FiniteBox E)
    (ω : Configuration E) : (B.split (closeBox B ω)).1 = (B.split ω).1 := by
  rw [closeBox, B.split_glue]

lemma continuous_closeBox {E : Type*} [Countable E] (B : FiniteBox E) :
    Continuous (closeBox B) := by
  exact (InteriorWeakLimit.FiniteBox.continuous_glue B).comp
    ((InteriorWeakLimit.FiniteBox.continuous_exteriorRestriction B).prodMk continuous_const)

lemma measurable_closeBox {E : Type*} [Countable E] (B : FiniteBox E) :
    Measurable (closeBox B) :=
  (continuous_closeBox B).measurable

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

local instance fintypeSetoid (V : Type*) [Finite V] : Fintype (Setoid V) :=
  Fintype.ofFinite _

/-- A uniform positive floor for all normalized FK point masses on a fixed
finite graph, at interior edge parameters.  Noncomputably taking the finite
minimum avoids any estimate on the graph's component count. -/
noncomputable def pointFloor (G : FK.Finite.LabelledMultigraph) (q p : NNReal) : NNReal :=
  Finset.univ.inf' Finset.univ_nonempty fun z : G.BoundaryPartition × G.Configuration =>
    G.fkWeight q p z.1 z.2 / G.partitionFunction q p z.1

lemma pointFloor_pos (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < pointFloor G q p := by
  apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
  intro z _hz
  exact div_pos (G.fkWeight_pos hq hp₀ hp₁ z.1 z.2)
    (G.partitionFunction_pos hq hp₁.le z.1)

lemma pointFloor_le (G : FK.Finite.LabelledMultigraph) (q p : NNReal)
    (ξ : G.BoundaryPartition) (ξ₀ : G.Configuration) :
    pointFloor G q p ≤ G.fkWeight q p ξ ξ₀ / G.partitionFunction q p ξ :=
  Finset.inf'_le _ (Finset.mem_univ (ξ, ξ₀))

lemma coe_pointFloor_le_fkPMF (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) (ξ₀ : G.Configuration) :
    (pointFloor G q p : ℝ≥0∞) ≤ G.fkPMF hq hp ξ ξ₀ := by
  rw [G.fkPMF_apply hq hp]
  exact_mod_cast pointFloor_le G q p ξ ξ₀

/-- Finite-energy domination for one DLR law.

Close-box mass of an event is at most the reciprocal of the uniform finite FK
point-mass floor times the original mass of the same event. -/
theorem measure_map_closeBox_le_of_isDLR {E : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp₁.le α hα μ) :
    Measure.map (closeBox B) (μ : Measure (Configuration E)) ≤
      (pointFloor B.graph q p : ℝ≥0∞)⁻¹ • (μ : Measure (Configuration E)) := by
  let ξ₀ : B.Interior := fun _ => false
  let c : ℝ≥0∞ := (pointFloor B.graph q p : ℝ≥0∞)
  have hc₀ : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (pointFloor_pos B.graph hq hp₀ hp₁).ne'
  have hctop : c ≠ ∞ := by simp [c]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply (measurable_closeBox B) hA, Measure.smul_apply, smul_eq_mul]
  rw [B.apply_of_isDLR hq hp₁.le α hα μ hμ ((measurable_closeBox B) hA),
    B.apply_of_isDLR hq hp₁.le α hα μ hμ hA]
  calc
    (∫⁻ η, (B.conditionalLaw hq hp₁.le α η : Measure (Configuration E))
        (closeBox B ⁻¹' A) ∂(B.exteriorMeasure μ : Measure B.Exterior)) ≤
        ∫⁻ η, c⁻¹ * (B.conditionalLaw hq hp₁.le α η : Measure (Configuration E)) A
          ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
      apply lintegral_mono
      intro η
      change (Measure.map (fun ξ : B.Interior => B.glue (η, ξ))
        (B.graph.fkMeasure hq hp₁.le (α η))) (closeBox B ⁻¹' A) ≤
          c⁻¹ * (Measure.map (fun ξ : B.Interior => B.glue (η, ξ))
            (B.graph.fkMeasure hq hp₁.le (α η))) A
      rw [Measure.map_apply (B.measurable_glue_const_left η) ((measurable_closeBox B) hA),
        Measure.map_apply (B.measurable_glue_const_left η) hA]
      by_cases hξ₀ : B.glue (η, ξ₀) ∈ A
      · have hpre : (fun ξ : B.Interior => B.glue (η, ξ)) ⁻¹' (closeBox B ⁻¹' A) =
            Set.univ := by
          ext ξ
          simp [closeBox_eq_glue, ξ₀, hξ₀]
        have hfloor : c ≤ (B.graph.fkMeasure hq hp₁.le (α η))
            ((fun ξ : B.Interior => B.glue (η, ξ)) ⁻¹' A) := by
          have hpoint : c ≤ (B.graph.fkMeasure hq hp₁.le (α η)) {ξ₀} := by
            rw [FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
            exact coe_pointFloor_le_fkPMF B.graph hq hp₁.le (α η) ξ₀
          exact hpoint.trans (measure_mono (Set.singleton_subset_iff.mpr hξ₀))
        rw [hpre]
        let _ : IsProbabilityMeasure (B.graph.fkMeasure hq hp₁.le (α η)) :=
          FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp₁.le (α η)
        rw [measure_univ]
        calc
          (1 : ℝ≥0∞) = c⁻¹ * c := (ENNReal.inv_mul_cancel hc₀ hctop).symm
          _ ≤ c⁻¹ * (B.graph.fkMeasure hq hp₁.le (α η))
              ((fun ξ : B.Interior => B.glue (η, ξ)) ⁻¹' A) := by gcongr
      · have hpre : (fun ξ : B.Interior => B.glue (η, ξ)) ⁻¹' (closeBox B ⁻¹' A) = ∅ := by
          ext ξ
          simp [closeBox_eq_glue, ξ₀, hξ₀]
        simp [hpre]
    _ = c⁻¹ * ∫⁻ η, (B.conditionalLaw hq hp₁.le α η : Measure (Configuration E)) A
          ∂(B.exteriorMeasure μ : Measure B.Exterior) :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc₀)

/-- The uniform close-box domination bound passes to an arbitrary weak limit of
laws which are eventually DLR on that box. -/
theorem measure_map_closeBox_le_of_tendsto_of_isDLR {E ι : Type*} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp₁.le α hα (μs i)) :
    Measure.map (closeBox B) (μ : Measure (Configuration E)) ≤
      (pointFloor B.graph q p : ℝ≥0∞)⁻¹ • (μ : Measure (Configuration E)) := by
  let c : ℝ≥0∞ := (pointFloor B.graph q p : ℝ≥0∞)
  have hc₀ : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (pointFloor_pos B.graph hq hp₀ hp₁).ne'
  have h := measure_map_le_smul_of_tendsto hμ (closeBox B) (continuous_closeBox B)
    (c := c⁻¹) (ENNReal.inv_ne_top.mpr hc₀) ?_
  · simpa only [ProbabilityMeasure.toMeasure_map, c] using h
  · filter_upwards [hDLR] with i hi
    simpa only [ProbabilityMeasure.toMeasure_map, c] using
      measure_map_closeBox_le_of_isDLR B hq hp₀ hp₁ α hα (μs i) hi

/-- Closing a fixed box preserves null events for a weak limit of its DLR laws. -/
theorem absolutelyContinuous_map_closeBox_of_tendsto_of_isDLR {E ι : Type*} [Countable E]
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp₁.le α hα (μs i)) :
    Measure.map (closeBox B) (μ : Measure (Configuration E)) ≪ (μ : Measure (Configuration E)) :=
  Measure.absolutelyContinuous_of_le_smul
    (measure_map_closeBox_le_of_tendsto_of_isDLR B hq hp₀ hp₁ α hα hμ hDLR)

/-- Global at-most-one-cluster uniqueness remains almost sure after closing a
finite box, for a weak limit of laws eventually DLR on that box. -/
theorem ae_globalAtMostOne_closeInside_of_tendsto_of_isDLR
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (B : FiniteBox G.edgeSet) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp₁.le α hα (μs i))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      GlobalAtMostOne G (closeInside B η) := by
  have hac := absolutelyContinuous_map_closeBox_of_tendsto_of_isDLR
    B hq hp₀ hp₁ α hα hμ hDLR
  have hclosed : ∀ᵐ ω ∂(Measure.map (closeBox B) (μ : Measure (Configuration G.edgeSet))),
      GlobalAtMostOne G ω := hac.ae_le hglobal
  have hsplit : Measurable (fun ω : Configuration G.edgeSet => (B.splitEquiv ω).1) :=
    measurable_fst.comp B.splitEquiv.measurable
  have hmapeq : Measure.map (closeInside B) (B.exteriorMeasure μ : Measure B.Exterior) =
      Measure.map (closeBox B) (μ : Measure (Configuration G.edgeSet)) := by
    change Measure.map (closeInside B)
      (Measure.map (fun ω : Configuration G.edgeSet => (B.splitEquiv ω).1)
        (μ : Measure (Configuration G.edgeSet))) = _
    rw [Measure.map_map (measurable_closeInside B) hsplit]
    rfl
  rw [← hmapeq] at hclosed
  exact (ae_map_iff (measurable_closeInside B).aemeasurable
    (measurableSet_globalAtMostOne G)).mp hclosed

/-- The pre-DLR global-to-exterior uniqueness step for a coherent
finite-volume weak limit.  It uses finite energy of the approximants, not the
DLR-only theorem `aeAtMostOne_geometry_of_global`. -/
theorem aeAtMostOne_geometry_of_tendsto_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le) (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp₁.le
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    ConventionTransport.AEAtMostOne data.geometry μ := by
  intro m
  have hDLR : ∀ᶠ n in atTop, (exh.box m).IsDLR hq hp₁.le
      (Φ.partition m) (Φ.measurable_partition m)
      ((exh.box n).conditionalLaw hq hp₁.le (Φ.partition n) (η n)) := by
    filter_upwards [exh.eventually_subset (exh.box m).edges] with n hn
    exact Φ.compatible m n hn (η n)
  have hgood := ae_globalAtMostOne_closeInside_of_tendsto_of_isDLR
    (exh.box m) hq hp₀ hp₁ (Φ.partition m) (Φ.measurable_partition m) hμ hDLR hglobal
  filter_upwards [hgood] with ζ hζ
  intro x y hx hy
  exact hζ (data.vertex m x) (data.vertex m y) hx hy

/-- Proposition 1.8(2), Gibbs form, for arbitrary exterior configurations in a
coherent finite-volume sequence.  Global uniqueness at the limit replaces the
former separate exterior-uniqueness hypothesis. -/
theorem mem_gibbsMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp₁.le
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ GibbsMeasures exh Φ := by
  apply NonlocalInterior.mem_gibbsMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne
    exh data hq hp₁.le Φ hΦ η hμ
  exact aeAtMostOne_geometry_of_tendsto_of_globalAtMostOne
    exh data hq hp₀ hp₁ Φ η hμ hglobal

/-- Full target-convention form for an arbitrary-exterior coherent
finite-volume weak limit with global at-most-one-cluster uniqueness. -/
theorem mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le) (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    (η : ∀ n, (exh.box n).Exterior)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp₁.le
      (Φ.partition n) (η n)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp₁.le := by
  apply NonlocalInterior.mem_dlrMeasures_of_tendsto_conditionalLaw_of_aeAtMostOne
    exh data hq hp₁.le Φ Ψ hΦ hΨ η hμ
  exact aeAtMostOne_geometry_of_tendsto_of_globalAtMostOne
    exh data hq hp₀ hp₁ Φ η hμ hglobal

/-- Closed-exterior specialization with no local-constancy assumption on the
coherent source specification. -/
theorem mem_dlrMeasures_of_tendsto_finiteVolumeLaw_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryConvention exh hq hp₁.le) (Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp₁.le
      (Φ.partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp₁.le := by
  apply mem_dlrMeasures_of_tendsto_conditionalLaw_of_globalAtMostOne
    exh data hq hp₀ hp₁ Φ Ψ hΦ hΨ (fun n => (exh.box n).closedExterior) _ hglobal
  simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using hμ

/-- Global-to-exterior uniqueness for an arbitrary weak limit of DLR laws on a
fixed specification.  No coherence or finite-volume representation of the
approximants is required. -/
theorem aeAtMostOne_geometry_of_tendsto_dlr_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment exh.box) {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp₁.le)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    ConventionTransport.AEAtMostOne data.geometry μ := by
  intro m
  have hgood := ae_globalAtMostOne_closeInside_of_tendsto_of_isDLR
    (exh.box m) hq hp₀ hp₁ (Φ.partition m) (Φ.measurable_partition m) hμ
    (hDLR.mono fun _ hi => hi m) hglobal
  filter_upwards [hgood] with ζ hζ
  intro x y hx hy
  exact hζ (data.vertex m x) (data.vertex m y) hx hy

/-- Weak closure of a geometric FK specification under global uniqueness.

The source DLR identity is proved first by almost-everywhere local constancy;
only then is the existing convention transport applied. -/
theorem mem_dlrMeasures_of_tendsto_dlr_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ Ψ : BoundaryAssignment exh.box)
    (hΦ : ConventionTransport.IsGeometric data.geometry Φ)
    (hΨ : ConventionTransport.IsGeometric data.geometry Ψ)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, μs i ∈ DLRMeasures exh Φ hq hp₁.le)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp₁.le := by
  have hunique := aeAtMostOne_geometry_of_tendsto_dlr_of_globalAtMostOne
    exh data hq hp₀ hp₁ Φ hμ hDLR hglobal
  have hsource : μ ∈ DLRMeasures exh Φ hq hp₁.le := by
    apply NonlocalInterior.mem_dlrMeasures_of_tendsto_of_ae_eventually_eq
      exh Φ hq hp₁.le hμ hDLR
    intro m
    filter_upwards [hunique m] with ζ hζ
    exact NonlocalInterior.eventually_partition_eq_of_atMostOne data Φ hΦ m ζ hζ
  exact ConventionTransport.mem_dlrMeasures_of_atMostOne exh data.geometry
    Φ Ψ hq hp₁.le hΦ hΨ hsource hunique

end

end FK.InfiniteVolume.GlobalFiniteEnergy
