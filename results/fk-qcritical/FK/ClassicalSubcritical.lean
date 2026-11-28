import FK.SourceNestedEquationNine
import FK.SourceLowerWindow
import FK.SubcriticalBaseline
import FK.QOneLine

/-!
# Immediate closed subcritical source wrappers for `q ≤ 1`

For `q < 1`, empty separated-device families specialize Proposition 4.2(1) to
the constant upper Bernoulli law at `max p p'`.  Combined with the completed
arbitrary-nested equation (9), this proves source-family uniqueness whenever
that ordinary Bernoulli law is subcritical.  The `q = 1` endpoint uses the
already proved `QOneLine` collapse.  No AG input is used.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Topology Classical

namespace FK.ClassicalSubcritical

open FK.InfiniteVolume
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.SourceUniqueness
open FK.SourceWindow
open FK.Exploration.FKCoupling
open FK.Adaptive.NestedSumGeometry
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u

/-- The empty set is a separated device family for the empty device map. -/
lemma empty_isSeparatedDeviceFamily {E : Type*} :
    FKLimit.IsSeparatedDeviceFamily (∅ : Set E) (fun _ => ∅) := by
  intro e he
  simp at he

/-- For `q < 1`, `upperRateNN` is exactly the prime parameter, not a larger
additional rate. -/
lemma upperRateNN_eq_primeNN_of_q_lt_one {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    upperRateNN q p = primeNN q p := by
  have hp : (p : ℝ) ∈ Set.Ioo 0 1 :=
    ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  have hppNN : p < primeNN q p := by
    rw [← NNReal.coe_lt_coe, coe_primeNN q p hq hp1.le]
    simpa only [FK.prime, FKLimit.fkSingletonParameter] using hpp
  exact max_eq_right hppNN.le

/-- At `q = 1` the same global rate collapses to the original parameter. -/
lemma upperRateNN_q_one {p : NNReal} (hp : p ≤ 1) :
    upperRateNN 1 p = p := by
  have hprime : primeNN 1 p = p := by
    apply NNReal.coe_injective
    rw [coe_primeNN 1 p zero_lt_one hp]
    simp [FK.prime]
  simp [upperRateNN, hprime]

/-- The empty-cycle upper parameters in Proposition 4.2(1) are the constant
parameters used by `globalBernoulli` at `upperRateNN`. -/
lemma ltUpperParameters_empty_eq_globalRate {E : Type*} {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ)) (L : ℕ) :
    FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L (∅ : Set E) =
      fun _ => unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp1.le) := by
  funext e
  apply Subtype.ext
  simp only [FKLimit.ltUpperParameters, FKLimit.unitParameters,
    FKLimit.loweredOn, Set.mem_empty_iff_false, ite_false, unitOfNN]
  rw [upperRateNN_eq_primeNN_of_q_lt_one hq hp0 hp1 hq1,
    coe_primeNN q p hq hp1.le]
  rfl

/-- Empty-device Proposition 4.2(1), with its dominant written in precisely
the form used by the arbitrary-nested uniqueness theorem. -/
theorem globalBernoulli_dominates_sourceFKMeasure_q_lt_one
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (e₀ : G.edgeSet) {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) hq hp1.le) :
    FKLimit.StochasticallyDominates
      (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp0 hp1).le) μ := by
  obtain ⟨E, hsource, hne⟩ :=
    exists_nonempty_sourceFKMeasure_tail hq hp1.le e₀ hμ
  let hp : (p : ℝ) ∈ Set.Ioo 0 1 :=
    ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  have hcomp := FK.Prop42Source.proposition_4_2_lt
    (E.exhaustion (G := G)) (E.data (G := G)) (E.data_vertex_injective (G := G))
    hq hp0 hp1 hq1 hsource
    (∅ : Set G.edgeSet) (fun _ => ∅) 0 empty_isSeparatedDeviceFamily
    (by intro f hf; simp at hf) (by intro f hf; simp at hf)
    (∅ : Set G.edgeSet) (fun _ => ∅) 0 empty_isSeparatedDeviceFamily
    (by intro f hf; simp at hf) (by intro f hf; simp at hf) hne
  have hdom := hcomp.2
  change FKLimit.StochasticallyDominates
    (FKLimit.bernoulliProduct
      (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp 0 ∅)) μ at hdom
  rw [ltUpperParameters_empty_eq_globalRate hq hp0 hp1 hq1 hp hqR hpp 0] at hdom
  exact hdom

/-- The constant global Bernoulli law is definitionally the ordinary
percolation law at the same unit-interval rate. -/
theorem ae_nonPercolating_globalBernoulli_of_lt_criticalProb
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {o : V} (hG : G.Connected) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hs : (upperRateNN q p : ℝ) < criticalProb G o) :
    ∀ᵐ ω ∂(globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp0 hp1).le :
      Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  exact FK.PercolationRoot.ae_nonPercolating_percolation_of_lt_criticalProb_single
    hG (s := unitOfNN (upperRateNN q p) (upperRateNN_lt_one hq hp0 hp1).le) hs

/-- On an edge-free graph every configuration is the all-closed
configuration, hence is nonpercolating. -/
lemma nonPercolating_of_isEmpty_edges
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    [IsEmpty G.edgeSet] (ω : Configuration G.edgeSet) :
    ω ∈ FK.NonPercolating G := by
  have hω : ω = fun _ => false := by
    funext e
    exact isEmptyElim e
  rw [hω]
  exact SourceWindow.nonPercolating_allClosed

/-- **Immediate closed subcritical source theorem, `q < 1`.**  If the
constant upper rate `max p p'` is below ordinary Bernoulli criticality at one
root, then the full public `SourceFKMeasures` family is a singleton and its
unique law is almost surely nonpercolating. -/
theorem sourceFKMeasures_singleton_and_nonpercolating_q_lt_one
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {o : V} (hG : G.Connected) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (hs : (upperRateNN q p : ℝ) < criticalProb G o) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  have hρ := ae_nonPercolating_globalBernoulli_of_lt_criticalProb hG hq hp0 hp1 hs
  obtain ⟨μ, hμ, huniq⟩ :=
    canonicalSource_existsUnique_sourceFKMeasures hq hp0 hp1 hρ
  refine ⟨μ, Set.eq_singleton_iff_unique_mem.mpr ⟨hμ, huniq⟩, ?_⟩
  cases isEmpty_or_nonempty G.edgeSet with
  | inl hE =>
      let _ := hE
      exact Filter.Eventually.of_forall nonPercolating_of_isEmpty_edges
  | inr hE =>
      let _ := hE
      let e₀ : G.edgeSet := Classical.choice hE
      exact FKLimit.ae_nonPercolating_of_stochasticallyDominates G
        (globalBernoulli_dominates_sourceFKMeasure_q_lt_one hq hp0 hp1 hq1 e₀ hμ) hρ

/-- The existing `QOneLine` collapse also applies to the public source
family: both arbitrary source weak limits and every all-region source DLR law
are the same constant Bernoulli product. -/
theorem sourceFKMeasures_q_one_eq_bernoulliConst
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {p : NNReal} (hp : p ≤ 1) :
    SourceFKMeasures (G := G) (q := 1) zero_lt_one hp =
      {FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp} := by
  obtain ⟨μ, hμ⟩ := sourceWeakLimits_nonempty (G := G) (q := 1) zero_lt_one hp
  have hμeq : μ = FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp := by
    obtain ⟨E, α, _hα, hlim⟩ := hμ
    exact FK.InfiniteVolume.QOne.eq_bernoulliConst_of_isFKLimit_q_one
      (E.exhaustion (G := G)) hp α hlim
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨?_, ?_⟩
  · rw [← hμeq]
    exact mem_sourceFKMeasures_of_weak (q := 1) zero_lt_one hp hμ
  · intro ν hν
    rcases hν with hν | ⟨E, α, _hα, hlim⟩
    · obtain ⟨Φ, _hΦ, hν⟩ := Set.mem_iUnion.mp hν
      let E : VertexExhaustion V :=
        Classical.choice (VertexExhaustion.exists_vertexExhaustion (V := V))
      have hνr : ν ∈ DLRMeasures (E.exhaustion (G := G)) (assignment E Φ)
          (q := 1) zero_lt_one hp := mem_dlr_restrict hν
      exact FK.InfiniteVolume.QOne.eq_bernoulliConst_of_mem_dlrMeasures_q_one
        (E.exhaustion (G := G)) (assignment E Φ) hp hνr
    · exact FK.InfiniteVolume.QOne.eq_bernoulliConst_of_isFKLimit_q_one
        (E.exhaustion (G := G)) hp α hlim

/-- The `q = 1` endpoint, proved from the established Bernoulli collapse and
the same single-root subcritical criterion. -/
theorem sourceFKMeasures_singleton_and_nonpercolating_q_one
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {o : V} (hG : G.Connected) {p : NNReal} (hp1 : p < 1)
    (hs : (p : ℝ) < criticalProb G o) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) (q := 1) zero_lt_one hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  refine ⟨FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp1.le,
    sourceFKMeasures_q_one_eq_bernoulliConst hp1.le, ?_⟩
  exact FK.PercolationRoot.ae_nonPercolating_percolation_of_lt_criticalProb_single
    hG (s := unitOfNN p hp1.le) hs

/-- **Immediate closed subcritical source theorem for `q ≤ 1`.**  The strict
case uses empty-device Proposition 4.2 and arbitrary nested equation (9); the
endpoint uses the established `q = 1` Bernoulli collapse. -/
theorem sourceFKMeasures_singleton_and_nonpercolating_q_le_one
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {o : V} (hG : G.Connected) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q ≤ 1)
    (hs : (upperRateNN q p : ℝ) < criticalProb G o) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  rcases eq_or_lt_of_le hq1 with rfl | hq1
  · exact sourceFKMeasures_singleton_and_nonpercolating_q_one hG hp1
      (by simpa only [upperRateNN_q_one hp1.le] using hs)
  · exact sourceFKMeasures_singleton_and_nonpercolating_q_lt_one
      hG hq hp0 hp1 hq1 hs

end

end FK.ClassicalSubcritical

#print axioms FK.ClassicalSubcritical.globalBernoulli_dominates_sourceFKMeasure_q_lt_one
#print axioms FK.ClassicalSubcritical.ae_nonPercolating_globalBernoulli_of_lt_criticalProb
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_q_lt_one
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_q_one_eq_bernoulliConst
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_q_one
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating_q_le_one
