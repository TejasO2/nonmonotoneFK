import FK.Theorem110Scope

/-!
# A non-vacuous instance of the assembled Theorem 1.10 at interior parameters

Stage 21, direction 8 (`m1`, swarm `smwu4rrf3`).

`theorem_1_10_geometric_family` (`Theorem110GeomFamily.lean`) needs four inputs:
`hne`, `hstoch`, `h5_1`, `h518`.  This file discharges all four on the
two-vertex graph with one edge at `q = p = 1/2` — the exact example on which the
*unrestricted* family of stage 18 fails (`Theorem110Scope.lean`), so the
geometric correction is validated, not merely stated.

Ingredients:

* `conditionalLaw_isDLR`: a finite-volume conditional law is DLR for its own
  boundary assignment.  This one-box equation is not in the repository; it is
  what makes `DLRMeasures` nonempty in concrete cases.
* `map_interiorRestriction_injective`: on a box that already contains every edge
  of the graph the interior restriction is injective on measures, because the
  exterior space is a subsingleton and `glue` inverts `interiorRestriction`.
* `dlrMeasures_oneEdge_free_singleton`: the free convention has exactly one DLR
  law on the one-edge exhaustion.
* `geometricFKLimits_oneEdge_eq`: every geometric limit is the free one (from
  `Theorem110Scope.isGeometricFKLimit_eq_freeOneEdgeLimit`).
* `bernoulliDominates_oneEdge`: the free FK law at `p = q = 1/2` is dominated by
  Bernoulli percolation at `s = 2/3`, and `2/3 < p_c = 1`.
* `theorem_1_10_oneEdge`: the assembled Theorem 1.10, instantiated:
  the geometric family is a singleton `{freeOneEdgeLimit}` and the unique law is
  a.s. non-percolating.
-/

set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.Scope

open FK.Finite FK.Finite.LabelledMultigraph
open FK.InfiniteVolume.NoncoherentCounterexample
open FK.InfiniteVolume.ConventionTransport
open CurvatureVariance.Infra.Percolation
open scoped Topology

noncomputable section

/-! ## The one-box DLR equation -/

section GeneralBox

variable {E : Type*} [Countable E]

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

/-- `dirac a ⊗ₘ κ` is the image of `κ a` under `Prod.mk a`. -/
theorem dirac_compProd_eq_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] (a : α) (κ : Kernel α β) [IsSFiniteKernel κ] :
    Measure.dirac a ⊗ₘ κ = Measure.map (Prod.mk a) (κ a) := by
  ext s hs
  rw [Measure.dirac_compProd_apply hs,
    Measure.map_apply measurable_prodMk_left hs]

/-- **A finite-volume conditional law is DLR for its own boundary assignment.**

This is the one-box equation `IsDLR`: its split law is the product of the
exterior point mass with the actual FK kernel. -/
theorem conditionalLaw_isDLR (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (η : B.Exterior) : B.IsDLR hq hp α hα (B.conditionalLaw hq hp α η) := by
  unfold FiniteBox.IsDLR
  have hsplit : B.splitEquiv ∘ (fun ω : B.Interior => B.glue (η, ω)) =
      fun ω => (η, ω) := by
    funext ω
    exact B.split_glue (η, ω)
  have hglue : Measurable (fun ω : B.Interior => B.glue (η, ω)) :=
    B.measurable_glue_const_left η
  have hmap : Measure.map B.splitEquiv (Measure.map (fun ω : B.Interior => B.glue (η, ω))
      (B.graph.fkMeasure hq hp (α η))) =
      Measure.map (fun ω : B.Interior => (η, ω)) (B.graph.fkMeasure hq hp (α η)) := by
    rw [Measure.map_map B.splitEquiv.measurable hglue, hsplit]
  rw [show (B.conditionalLaw hq hp α η : Measure (Configuration E)) =
    Measure.map (fun ω : B.Interior => B.glue (η, ω))
      (B.graph.fkMeasure hq hp (α η)) from rfl, hmap]
  have hext : (B.exteriorMeasure (B.conditionalLaw hq hp α η) : Measure B.Exterior) =
      Measure.dirac η := by
    have hprob : IsProbabilityMeasure (B.graph.fkMeasure hq hp (α η)) :=
      FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure B.graph hq hp (α η)
    haveI := hprob
    have hfirst : Measurable (fun ω : Configuration E => (B.splitEquiv ω).1) :=
      B.splitEquiv.measurable.fst
    have hone : ((fun ω : Configuration E => (B.splitEquiv ω).1) ∘
        (fun ω : B.Interior => B.glue (η, ω))) = fun _ => η := by
      funext ω
      rw [Function.comp_apply, FiniteBox.splitEquiv_apply, B.split_glue]
    have : ((B.exteriorMeasure (B.conditionalLaw hq hp α η) : ProbabilityMeasure B.Exterior) :
        Measure B.Exterior) =
        Measure.map (fun ω : Configuration E => (B.splitEquiv ω).1)
          (Measure.map (fun ω : B.Interior => B.glue (η, ω))
            (B.graph.fkMeasure hq hp (α η))) := rfl
    rw [this, Measure.map_map hfirst hglue, hone, Measure.map_const,
      measure_univ, one_smul]
  rw [hext, dirac_compProd_eq_map]
  rfl

end GeneralBox

/-! ## Measure-level injectivity of the interior restriction on the one-edge box -/

section Injectivity

/-- `glue` with the unique exterior point inverts `interiorRestriction`. -/
theorem oneEdge_glue_interiorRestriction (ω : Configuration TwoVertexGraph.edgeSet) :
    oneEdgeBox.glue (default, oneEdgeBox.interiorRestriction ω) = ω := by
  have hsplit : oneEdgeBox.split ω = (default, oneEdgeBox.interiorRestriction ω) := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  rw [← hsplit]
  exact oneEdgeBox.glue_split ω

/-- On the one-edge box the interior restriction is injective on probability
measures. -/
theorem map_interiorRestriction_injective :
    Function.Injective (fun μ : Measure (Configuration TwoVertexGraph.edgeSet) =>
      Measure.map oneEdgeBox.interiorRestriction μ) := by
  intro μ ν h
  have hcomp : (fun x : oneEdgeBox.Interior => oneEdgeBox.glue (default, x)) ∘
      oneEdgeBox.interiorRestriction = id := by
    funext ω
    exact oneEdge_glue_interiorRestriction ω
  have hm := congrArg (fun ρ => Measure.map
    (fun x : oneEdgeBox.Interior => oneEdgeBox.glue (default, x)) ρ) h
  rw [Measure.map_map (oneEdgeBox.measurable_glue_const_left default)
      oneEdgeBox.measurable_interiorRestriction,
    Measure.map_map (oneEdgeBox.measurable_glue_const_left default)
      oneEdgeBox.measurable_interiorRestriction, hcomp, Measure.map_id,
    Measure.map_id] at hm
  exact hm

end Injectivity

theorem oneEdge_free_partition_any (n : ℕ) (η : (oneEdgeExhaustion.box n).Exterior) :
    oneEdgeBoxData.free.partition n η = oneEdgeBox.graph.freeBoundary := by
  apply Setoid.ext
  intro x y
  change OpenConnected TwoVertexGraph (closeInside oneEdgeBox η) Set.univ x y ↔ x = y
  have hclosed : closeInside oneEdgeBox η = (fun _ => false) := by
    funext e
    have he : e ∈ oneEdgeBox.edges := Finset.mem_univ e
    simp [closeInside, FiniteBox.glue, he]
  rw [hclosed]
  exact openConnected_allClosed_iff x y

/-! ## The free convention has exactly one DLR law on the one-edge exhaustion -/

section DLR

theorem dlrMeasures_oneEdge_free_singleton :
    DLRMeasures oneEdgeExhaustion oneEdgeBoxData.free
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num) =
        {freeOneEdgeLimit} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · intro n
    have hlaw : (oneEdgeExhaustion.box n).conditionalLaw (q := 1 / 2) (p := (1 / 2 : NNReal))
        (by norm_num) (by norm_num) (oneEdgeBoxData.free.partition n)
        (oneEdgeExhaustion.box n).closedExterior = freeOneEdgeLimit := by
      apply Subtype.ext
      simp only [FiniteBox.conditionalLaw, freeOneEdgeLimit, FiniteBox.finiteVolumeLaw]
      rw [oneEdge_free_partition_any n]
      rfl
    rw [← hlaw]
    exact conditionalLaw_isDLR oneEdgeBox (by norm_num) (by norm_num)
      (oneEdgeBoxData.free.partition n) (oneEdgeBoxData.free.measurable_partition n)
      oneEdgeBox.closedExterior
  · intro μ hμ
    have hD0 : oneEdgeBox.IsDLR (q := 1 / 2) (p := (1 / 2 : NNReal))
        (by norm_num) (by norm_num) (oneEdgeBoxData.free.partition 0)
        (oneEdgeBoxData.free.measurable_partition 0) μ := hμ 0
    have himg := map_interiorRestriction_of_isDLR_of_subsingleton oneEdgeBox
      (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
      (oneEdgeBoxData.free.partition 0) (oneEdgeBoxData.free.measurable_partition 0)
      μ hD0
    rw [oneEdge_free_partition (default : oneEdgeBox.Exterior)] at himg
    have himgfree : Measure.map oneEdgeBox.interiorRestriction
        (freeOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)) =
        oneEdgeBox.graph.fkMeasure (q := 1 / 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary := by
      simpa [freeOneEdgeLimit, FiniteBox.finiteVolumeLaw] using
        oneEdgeBox.map_interiorRestriction_conditionalLaw
          (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
          (fun _ => oneEdgeBox.graph.freeBoundary) oneEdgeBox.closedExterior
    exact Subtype.ext (map_interiorRestriction_injective (himg.trans himgfree.symm))

end DLR

/-! ## The Bernoulli domination at `s = 2/3` -/

section Domination

/-- The all-open global configuration of the two-vertex graph. -/
def allOpenConfig : Configuration TwoVertexGraph.edgeSet := fun _ => true

/-- The all-closed global configuration of the two-vertex graph. -/
def allClosedConfig : Configuration TwoVertexGraph.edgeSet := fun _ => false

lemma eq_allOpen_or_allClosed (ω : Configuration TwoVertexGraph.edgeSet) :
    ω = allOpenConfig ∨ ω = allClosedConfig := by
  by_cases h : ω twoVertexEdge = true
  · left
    funext e
    rw [Subsingleton.elim e twoVertexEdge]
    exact h
  · right
    funext e
    rw [Subsingleton.elim e twoVertexEdge]
    cases hv : ω twoVertexEdge
    · rfl
    · exact absurd hv h

lemma interiorRestriction_allOpenConfig :
    oneEdgeBox.interiorRestriction allOpenConfig = oneEdgeBox.graph.allOpen := rfl

lemma glue_allOpenConfig :
    oneEdgeBox.glue (default, oneEdgeBox.graph.allOpen) = allOpenConfig := by
  funext e
  have he : e ∈ oneEdgeBox.edges := Finset.mem_univ e
  simp [FiniteBox.glue, he, LabelledMultigraph.allOpen, allOpenConfig]

/-- The free limit gives mass `2/3` to the all-open configuration. -/
theorem freeOneEdgeLimit_allOpen :
    (freeOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)) {allOpenConfig} =
      (2 / 3 : NNReal) := by
  have hpre : oneEdgeBox.interiorRestriction ⁻¹' {oneEdgeBox.graph.allOpen} =
      {allOpenConfig} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← oneEdge_glue_interiorRestriction ω, h, glue_allOpenConfig]
    · intro h
      rw [h, interiorRestriction_allOpenConfig]
  rw [← hpre, ← Measure.map_apply oneEdgeBox.measurable_interiorRestriction
    (MeasurableSet.of_discrete)]
  rw [show Measure.map oneEdgeBox.interiorRestriction
      (freeOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)) =
      oneEdgeBox.graph.fkMeasure (q := 1 / 2) (p := (1 / 2 : NNReal))
        (by norm_num) (by norm_num) oneEdgeBox.graph.freeBoundary from by
    simpa [freeOneEdgeLimit, FiniteBox.finiteVolumeLaw] using
      oneEdgeBox.map_interiorRestriction_conditionalLaw
        (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        (fun _ => oneEdgeBox.graph.freeBoundary) oneEdgeBox.closedExterior]
  rw [LabelledMultigraph.fkMeasure, PMF.toMeasure_apply_singleton _ _
    MeasurableSet.of_discrete]
  exact oneEdge_free_allOpen_mass_half

/-- The Bernoulli reference law at `2/3` gives mass `2/3` to the all-open
configuration. -/
theorem percolation_allOpen :
    CurvatureVariance.Infra.Percolation.percolation TwoVertexGraph
      (⟨2 / 3, by norm_num⟩ : unitInterval) {allOpenConfig} =
        ENNReal.ofReal (2 / 3 : ℝ) := by
  have hset : {allOpenConfig} = {ω : TwoVertexGraph.edgeSet → Bool |
      CurvatureVariance.Infra.Percolation.IsOpenEdge TwoVertexGraph ω
        (s(false, true))} := by
    ext ω
    constructor
    · intro h
      rw [h]
      exact ⟨by rw [SimpleGraph.mem_edgeSet]; simp, rfl⟩
    · rintro ⟨he, hω⟩
      rw [Set.mem_singleton_iff]
      funext e
      rw [Subsingleton.elim e twoVertexEdge]
      exact hω
  rw [hset, CurvatureVariance.Infra.Percolation.percolation_isOpenEdge
    (he := by rw [SimpleGraph.mem_edgeSet]; simp)]

/-- The free FK limit at `p = q = 1/2` is dominated on increasing events by
Bernoulli percolation at rate `2/3`. -/
theorem bernoulliDominates_oneEdge :
    BernoulliDominates TwoVertexGraph (⟨2 / 3, by norm_num⟩ : unitInterval)
      freeOneEdgeLimit := by
  intro A hA hU
  by_cases hOpen : allOpenConfig ∈ A
  · by_cases hClosed : allClosedConfig ∈ A
    · have hAuniv : A = Set.univ := by
        apply Set.eq_univ_of_forall
        intro ω
        rcases eq_allOpen_or_allClosed ω with rfl | rfl
        · exact hOpen
        · exact hClosed
      rw [hAuniv]
      simp
    · have hAsing : A = {allOpenConfig} := by
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨hOpen, ?_⟩
        intro ω hω
        rcases eq_allOpen_or_allClosed ω with h | h
        · exact h
        · exact absurd (h ▸ hω) hClosed
      rw [hAsing, freeOneEdgeLimit_allOpen, percolation_allOpen,
        ← ENNReal.ofReal_coe_nnreal]
      norm_num
  · have hAempty : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      rcases eq_allOpen_or_allClosed ω with h | h
      · exact hOpen (h ▸ hω)
      · exact hOpen (hU (show allClosedConfig ≤ allOpenConfig from
          fun _ => by simp [allClosedConfig, allOpenConfig]) (h ▸ hω))
    rw [hAempty]
    simp

end Domination

/-! ## The instance of the assembled Theorem 1.10 -/

section Instance

/-- **Theorem 1.10 on the two-vertex graph at `q = p = 1/2`.**

All four inputs of `theorem_1_10_geometric_family` are discharged here:
`hne` (a geometric limit exists), `hstoch` (Bernoulli domination at `s = 2/3`,
below `p_c = 1`), `h5_1` (the free geometric DLR class is a singleton) and
`h518` (every geometric limit is the free limit, which lies in that class).

This is the same example on which the *unrestricted* family of stage 18 fails,
so it shows that the geometric restriction is exactly what makes the paper's
conclusion true there. -/
theorem theorem_1_10_oneEdge :
    (∃! μ : ProbabilityMeasure (Configuration TwoVertexGraph.edgeSet),
        μ ∈ FKFamilyGeom oneEdgeExhaustion oneEdgeBoxData
          (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)) ∧
      ∀ᵐ ω ∂(freeOneEdgeLimit : Measure (Configuration TwoVertexGraph.edgeSet)),
        ω ∈ NonPercolating TwoVertexGraph := by
  refine theorem_1_10_geometric_family (G := TwoVertexGraph) SimpleGraph.connected_top
    oneEdgeExhaustion oneEdgeBoxData (q := 1 / 2) (p := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) (s := (⟨2 / 3, by norm_num⟩ : unitInterval))
    (Φ₀ := ⟨oneEdgeBoxData.free, oneEdgeBoxData.free_isGeometric⟩)
    (μ₀ := freeOneEdgeLimit) ?_ ?_ ?_ ?_ ?_
  · intro x
    rw [criticalProb_twoVertex]
    norm_num
  · obtain ⟨Φ, η, hlim⟩ : ∃ (Φ : GeomConvention oneEdgeExhaustion oneEdgeBoxData)
        (η : ∀ n, (oneEdgeExhaustion.box n).Exterior),
        IsFKLimit oneEdgeExhaustion (q := 1 / 2) (p := (1 / 2 : NNReal))
          (by norm_num) (by norm_num) (fun n => Φ.1.partition n (η n)) freeOneEdgeLimit := by
      refine ⟨⟨oneEdgeBoxData.free, oneEdgeBoxData.free_isGeometric⟩,
        fun _ => default, ?_⟩
      have hconst : (fun n => (oneEdgeExhaustion.box n).finiteVolumeLaw
          (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
          ((⟨oneEdgeBoxData.free, oneEdgeBoxData.free_isGeometric⟩ :
            GeomConvention oneEdgeExhaustion oneEdgeBoxData).1.partition n
              ((fun _ => default) n))) = fun _ => freeOneEdgeLimit := by
        funext n
        rw [show (⟨oneEdgeBoxData.free, oneEdgeBoxData.free_isGeometric⟩ :
            GeomConvention oneEdgeExhaustion oneEdgeBoxData).1.partition n
              ((fun _ => default) n) = oneEdgeBox.graph.freeBoundary from
          oneEdge_free_partition_any n (default : (oneEdgeExhaustion.box n).Exterior)]
        rfl
      change Tendsto (fun n => (oneEdgeExhaustion.box n).finiteVolumeLaw
        (q := 1 / 2) (p := (1 / 2 : NNReal)) (by norm_num) (by norm_num)
        ((⟨oneEdgeBoxData.free, oneEdgeBoxData.free_isGeometric⟩ :
          GeomConvention oneEdgeExhaustion oneEdgeBoxData).1.partition n
            ((fun _ => default) n))) atTop (𝓝 freeOneEdgeLimit)
      rw [hconst]
      exact tendsto_const_nhds
    exact ⟨freeOneEdgeLimit, ⟨Φ, η, hlim⟩⟩
  · intro φ hφ
    rw [isGeometricFKLimit_eq_freeOneEdgeLimit hφ]
    exact bernoulliDominates_oneEdge
  · exact dlrMeasures_oneEdge_free_singleton
  · intro μ hμ
    rw [isGeometricFKLimit_eq_freeOneEdgeLimit hμ, dlrMeasures_oneEdge_free_singleton]
    exact Set.mem_singleton _

end Instance

end

end FK.InfiniteVolume.Scope
