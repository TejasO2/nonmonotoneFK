import FK.ClassicalSubcritical
import FK.ClassicalSubcriticalGt

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology

namespace FK.ClassicalSubcritical

open FK.InfiniteVolume
open FK.SourceUniqueness
open FK.Adaptive.NestedSumGeometry
open FK.Exploration.FKCoupling
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u

/-- **Interior-parameter classical subcritical strong uniqueness.** For every
positive `q`, the literal condition `max (p, p') < p_c(G,o)` makes the full
source FK family a singleton whose law does not percolate. -/
theorem sourceFKMeasures_singleton_and_nonpercolating
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {o : V} (hG : G.Connected) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hs : (upperRateNN q p : ℝ) < criticalProb G o) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  by_cases hq1 : q ≤ 1
  · exact sourceFKMeasures_singleton_and_nonpercolating_q_le_one
      hG hq hp0 hp1 hq1 hs
  · have hq1 : 1 < q := lt_of_not_ge hq1
    have hrate : upperRateNN q p = p :=
      ClassicalSubcriticalGt.upperRateNN_eq_of_one_lt_q hp0 hp1 hq1
    have hsp : (p : ℝ) < criticalProb G o := by rwa [← hrate]
    cases isEmpty_or_nonempty G.edgeSet with
    | inl hE =>
        let _ := hE
        have hρ := ClassicalSubcriticalGt.ae_nonPercolating_globalUpper_of_one_lt_q
          hG o hp0 hp1 hq1 hsp
        obtain ⟨μ, hμ, huniq⟩ :=
          canonicalSource_existsUnique_sourceFKMeasures hq hp0 hp1 hρ
        refine ⟨μ, Set.eq_singleton_iff_unique_mem.mpr ⟨hμ, huniq⟩, ?_⟩
        exact Filter.Eventually.of_forall nonPercolating_of_isEmpty_edges
    | inr hE =>
        let _ := hE
        let e₀ : G.edgeSet := Classical.choice hE
        exact ClassicalSubcriticalGt.sourceFKMeasures_singleton_of_one_lt_q_subcritical
          hG o hp0 hp1 hq1 e₀ hsp

end
end FK.ClassicalSubcritical

#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_and_nonpercolating
