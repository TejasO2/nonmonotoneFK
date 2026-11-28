import FK.ClassicalSubcriticalAssembly

/-!
# Strong source uniqueness from a nonpercolating ordinary upper law

This discharges strict subcriticality of the ordinary product directly rather
than assuming it through a strict inequality below `criticalProb`. In
particular it includes parameters at critical probability whose ordinary
percolation probability vanishes.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology

namespace FK.ClassicalSubcritical

open FK.InfiniteVolume
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.SourceUniqueness
open FK.Adaptive.NestedSumGeometry
open FK.Exploration.FKCoupling
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u

/-- **Classical strong uniqueness from nonpercolation of the literal ordinary
upper product.** This includes the critical case with zero ordinary
percolation probability, without any enhanced/AG input. -/
theorem sourceFKMeasures_singleton_of_nonpercolating_upper
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet
      (upperRateNN_lt_one hq hp0 hp1).le : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  obtain ⟨μ, hμ, huniq⟩ := canonicalSource_existsUnique_sourceFKMeasures hq hp0 hp1 hρ
  refine ⟨μ, Set.eq_singleton_iff_unique_mem.mpr ⟨hμ, huniq⟩, ?_⟩
  rcases lt_trichotomy q 1 with hq1 | rfl | hq1
  · cases isEmpty_or_nonempty G.edgeSet with
    | inl hE =>
        let _ := hE
        exact Filter.Eventually.of_forall nonPercolating_of_isEmpty_edges
    | inr hE =>
        let _ := hE
        let e₀ : G.edgeSet := Classical.choice hE
        exact FKLimit.ae_nonPercolating_of_stochasticallyDominates G
          (globalBernoulli_dominates_sourceFKMeasure_q_lt_one hq hp0 hp1 hq1 e₀ hμ) hρ
  · have hset := sourceFKMeasures_q_one_eq_bernoulliConst (G := G) hp1.le
    have hμB : μ = FK.InfiniteVolume.QOne.bernoulliConst (E := G.edgeSet) p hp1.le := by
      apply Set.mem_singleton_iff.mp
      rw [← hset]
      exact hμ
    rw [hμB]
    simpa only [globalBernoulli, upperRateNN_q_one hp1.le] using hρ
  · cases isEmpty_or_nonempty G.edgeSet with
    | inl hE =>
        let _ := hE
        exact Filter.Eventually.of_forall nonPercolating_of_isEmpty_edges
    | inr hE =>
        let _ := hE
        let e₀ : G.edgeSet := Classical.choice hE
        exact FKLimit.ae_nonPercolating_of_stochasticallyDominates G
          (ClassicalSubcriticalGt.globalUpper_dominates_sourceFKMeasures_of_one_lt_q
            hp0 hp1 hq1 e₀ hμ) hρ

/-- Zero ordinary one-root percolation probability at the literal upper rate
suffices, including when that rate is exactly critical. -/
theorem sourceFKMeasures_singleton_of_zero_percolationProb_upper
    {V : Type u} [Countable V] [Nonempty V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hs : percolationProb G o
      (unitOfNN (upperRateNN q p) (upperRateNN_lt_one hq hp0 hp1).le) = 0) :
    ∃ μ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) hq hp1.le = {μ} ∧
        ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  have hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet
      (upperRateNN_lt_one hq hp0 hp1).le : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G := by
    exact FK.InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero
      (unitOfNN (upperRateNN q p) (upperRateNN_lt_one hq hp0 hp1).le)
      (fun x => (FK.PercolationRoot.percolationProb_eq_zero_iff_root
        (o := o) (x := x) hG _).mp hs)
  exact sourceFKMeasures_singleton_of_nonpercolating_upper hq hp0 hp1 hρ

end
end FK.ClassicalSubcritical

#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_of_nonpercolating_upper
#print axioms FK.ClassicalSubcritical.sourceFKMeasures_singleton_of_zero_percolationProb_upper
