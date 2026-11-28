import FK.ClassicalSubcriticalNonpercolating
import FK.ArbitraryNestedEquationNine
import FK.SourceWindow

/-!
# Classical source uniqueness at every bounded rate

The zero-rate source family is deterministic.  At the other endpoint the same
coordinate argument identifies the all-open law.  Between the endpoints we use
the proved ordinary-upper nonpercolation theorem.  No seed edge, enhancement,
or edge-free-graph assumption occurs.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology

namespace FK.ClassicalSubcritical

open FK.InfiniteVolume
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.SourceUniqueness
open FK.SourceWindow
open FK.Adaptive.NestedSumGeometry
open FK.Exploration.FKCoupling
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u

/-- Every member of the source family at unit rate is the all-open point mass.
The DLR branch is restricted to one arbitrary vertex exhaustion; no coherence
argument is needed. -/
theorem eq_openLaw_of_mem_sourceFKMeasures_one
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {q : NNReal} (hq : 0 < q)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) hq (p := 1) le_rfl) :
    μ = FK.MainIntegration.Endpoint.openLaw G.edgeSet := by
  apply FK.MainIntegration.Endpoint.eq_openLaw_of_ae_open
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  rcases hμ with hμ | ⟨E, α, hα, hlim⟩
  · obtain ⟨Φ, hΦ, hμ⟩ := Set.mem_iUnion.mp hμ
    let E : VertexExhaustion V :=
      Classical.choice (VertexExhaustion.exists_vertexExhaustion (V := V))
    have hrestr : μ ∈ DLRMeasures (E.exhaustion (G := G)) (assignment E Φ)
        hq (p := 1) le_rfl := mem_dlr_restrict hμ
    simpa using FK.MainIntegration.Endpoint.dlr_apply_closed_one
      (E.exhaustion (G := G)) (assignment E Φ) hq hrestr e
  · simpa using FK.MainIntegration.Endpoint.fkLimit_apply_closed_one
      (E.exhaustion (G := G)) hq α hlim e

/-- The literal upper rate at `p = 1` is one, for every positive `q`. -/
lemma upperRateNN_one {q : NNReal} (hq : 0 < q) : upperRateNN q 1 = 1 := by
  apply le_antisymm (upperRateNN_le_one hq le_rfl)
  exact le_max_left 1 (primeNN q 1)

/-- The ordinary upper product at `p = 1` is the all-open point mass. -/
theorem globalBernoulli_one_eq_openLaw
    {E : Type*} [Countable E] {q : NNReal} (hq : 0 < q) :
    globalBernoulli E (upperRateNN_le_one hq (p := 1) le_rfl) =
      FK.MainIntegration.Endpoint.openLaw E := by
  change FKLimit.bernoulliProduct
    (fun _ : E => unitOfNN (upperRateNN q 1) (upperRateNN_le_one hq le_rfl)) =
      FK.MainIntegration.Endpoint.openLaw E
  have hfun : (fun _ : E => unitOfNN (upperRateNN q 1)
      (upperRateNN_le_one hq le_rfl)) = (fun _ : E => (1 : unitInterval)) := by
    funext e
    apply Subtype.ext
    change (upperRateNN q 1 : ℝ) = 1
    exact_mod_cast upperRateNN_one hq
  rw [hfun]
  exact FK.MainIntegration.Endpoint.bernoulliProduct_one_eq_openLaw

/-- The full source family at unit rate is the all-open singleton.  This is a
uniqueness statement only: on an infinite graph the all-open law percolates. -/
theorem sourceFKMeasures_one
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {q : NNReal} (hq : 0 < q) :
    SourceFKMeasures (G := G) hq (p := 1) le_rfl =
      {FK.MainIntegration.Endpoint.openLaw G.edgeSet} := by
  obtain ⟨μ, hμ⟩ := sourceWeakLimits_nonempty (G := G) hq (p := 1) le_rfl
  have hμopen : μ = FK.MainIntegration.Endpoint.openLaw G.edgeSet :=
    eq_openLaw_of_mem_sourceFKMeasures_one hq
      (mem_sourceFKMeasures_of_weak hq (p := 1) le_rfl hμ)
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · rw [← hμopen]
    exact mem_sourceFKMeasures_of_weak hq (p := 1) le_rfl hμ
  · intro ν hν
    exact eq_openLaw_of_mem_sourceFKMeasures_one hq hν

/-- **Uniform source singleton core.**  The endpoint-inclusive arbitrary
`NestedBox` equation (9) gives existence and uniqueness for every bounded rate
as soon as the literal ordinary upper product is nonpercolating. -/
theorem sourceFKMeasures_existsUnique_of_nonpercolating_upper_all
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet (upperRateNN_le_one hq hp) :
      Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G) :
    ∃! μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ SourceFKMeasures (G := G) hq hp := by
  obtain ⟨w, hw⟩ := sourceWeakLimits_nonempty (G := G) hq hp
  exact existsUnique_sourceFKMeasures_of_nested_boundaryBounds hq hp
    (globalBernoulli G.edgeSet (upperRateNN_le_one hq hp)) hρ (edgeRoots G)
    (hasNestedBoundaryBounds_of_equationNine hq hp
      (nestedEquationNine_upperBernoulli (G := G) hq hp)) ⟨w, hw⟩

/-- Zero-rate classical source uniqueness and nonpercolation, exposed alongside
the interior and unit-rate wrappers. -/
theorem sourceFKMeasures_singleton_and_nonpercolating_zero
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) {q : NNReal} (hq : 0 < q) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq (p := 0) bot_le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G :=
  FK.SourceWindow.sourceFKMeasures_zero hG hq

/-- **Classical source uniqueness at every `0 ≤ p ≤ 1` from actual ordinary
upper nonpercolation.**  At `p = 1` the hypothesis says precisely that the
all-open point mass is nonpercolating; it is not asserted automatically. -/
theorem sourceFKMeasures_singleton_of_nonpercolating_upper_all
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet (upperRateNN_le_one hq hp) :
      Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  by_cases hp0 : p = 0
  · subst p
    exact sourceFKMeasures_singleton_and_nonpercolating_zero hG hq
  · have hp0' : 0 < p := pos_iff_ne_zero.mpr hp0
    by_cases hp1 : p = 1
    · subst p
      refine ⟨FK.MainIntegration.Endpoint.openLaw G.edgeSet,
        sourceFKMeasures_one hq, ?_⟩
      rw [← globalBernoulli_one_eq_openLaw (E := G.edgeSet) hq]
      exact hρ
    · have hp1' : p < 1 := lt_of_le_of_ne hp hp1
      have hρ' : ∀ᵐ ω ∂(globalBernoulli G.edgeSet
          (upperRateNN_lt_one hq hp0' hp1').le : Measure (Configuration G.edgeSet)),
          ω ∈ FK.NonPercolating G := by
        exact hρ
      exact sourceFKMeasures_singleton_of_nonpercolating_upper hq hp0' hp1' hρ'

/-- One-root zero upper percolation probability gives the same all-parameter
source theorem on a connected graph, including the critical zero-`θ` case. -/
theorem sourceFKMeasures_singleton_of_zero_percolationProb_upper_all
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hs : percolationProb G o
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp)) = 0) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  have hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet (upperRateNN_le_one hq hp) :
      Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
    exact FK.InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp))
      (fun x => (FK.PercolationRoot.percolationProb_eq_zero_iff_root
        (o := o) (x := x) hG _).mp hs)
  exact sourceFKMeasures_singleton_of_nonpercolating_upper_all hG hq hp hρ

/-- The strict ordinary-upper subcritical wrapper now includes `p = 0` and all
positive `q`, without a separate positive-rate premise. -/
theorem sourceFKMeasures_singleton_and_nonpercolating_of_lt_criticalProb
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {o : V} (hG : G.Connected) {q p : NNReal}
    (hq : 0 < q) (hp1 : p < 1)
    (hs : (upperRateNN q p : ℝ) < criticalProb G o) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  by_cases hp0 : p = 0
  · subst p
    exact sourceFKMeasures_singleton_and_nonpercolating_zero hG hq
  · exact sourceFKMeasures_singleton_and_nonpercolating hG hq
      (pos_iff_ne_zero.mpr hp0) hp1 hs

end
end FK.ClassicalSubcritical

#print axioms FK.ClassicalSubcritical.eq_openLaw_of_mem_sourceFKMeasures_one
#print axioms FK.ClassicalSubcritical.upperRateNN_one
#print axioms FK.ClassicalSubcritical.globalBernoulli_one_eq_openLaw
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_one
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_existsUnique_of_nonpercolating_upper_all
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_zero
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_of_nonpercolating_upper_all
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_of_zero_percolationProb_upper_all
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_of_lt_criticalProb

#check @FK.ClassicalSubcritical.eq_openLaw_of_mem_sourceFKMeasures_one
#check @FK.ClassicalSubcritical.upperRateNN_one
#check @FK.ClassicalSubcritical.globalBernoulli_one_eq_openLaw
#check @FK.ClassicalSubcritical.sourceFKMeasures_one
#check @FK.ClassicalSubcritical.sourceFKMeasures_existsUnique_of_nonpercolating_upper_all
#check @FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_zero
#check @FK.ClassicalSubcritical.sourceFKMeasures_singleton_of_nonpercolating_upper_all
#check @FK.ClassicalSubcritical.sourceFKMeasures_singleton_of_zero_percolationProb_upper_all
#check @FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_of_lt_criticalProb
