import FK.SourceNestedEquationNine
import FK.SourceLowerWindow
import FK.SubcriticalBaseline

/-!
# Immediate closed subcritical source wrapper for `1 < q`

This file specializes Proposition 4.2(2) to empty enhanced sets and joins the
resulting ordinary Bernoulli dominant to arbitrary-nested equation (9).
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology

namespace FK.ClassicalSubcriticalGt

open FK.InfiniteVolume
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.Adaptive.NestedSumGeometry
open FK.SourceUniqueness
open FK.SourceWindow
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- For `1 < q`, the singleton rate is below `p`, so the global upper rate is
literally `p`, not merely bounded by it. -/
theorem upperRateNN_eq_of_one_lt_q {q p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₁ : 1 < q) :
    FK.Exploration.FKCoupling.upperRateNN q p = p := by
  let hq : 0 < q := lt_trans zero_lt_one hq₁
  let hp : (p : ℝ) ∈ Ioo 0 1 :=
    ⟨by exact_mod_cast hp₀, by exact_mod_cast hp₁⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq₁)
  apply NNReal.eq
  change max (p : ℝ)
    ((FK.Exploration.FKCoupling.primeNN q p : NNReal) : ℝ) = (p : ℝ)
  rw [FK.Exploration.FKCoupling.coe_primeNN q p hq hp₁.le]
  exact max_eq_left hpp.le

/-- With no enhanced star edges, Proposition 4.2(2)'s upper parameters are
the constant ordinary parameter `p`. -/
theorem gtUpperParameters_empty {E : Type*} {q p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₁ : 1 < q) (Delta : ℕ) :
    let hq : 0 < q := lt_trans zero_lt_one hq₁
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp₀, by exact_mod_cast hp₁⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq₁)
    FKLimit.gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta (∅ : Set E) =
      fun _ => unitOfNN p hp₁.le := by
  dsimp only
  funext e
  apply Subtype.ext
  simp [FKLimit.gtUpperParameters, FKLimit.unitParameters, FKLimit.loweredOn,
    unitOfNN]

/-- The ordinary global Bernoulli law at `upperRateNN q p` is nonpercolating
when `1 < q` and `p` is below the critical probability at one root. -/
theorem ae_nonPercolating_globalUpper_of_one_lt_q
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₁ : 1 < q)
    (hsub : (p : ℝ) < criticalProb G o) :
    ∀ᵐ ω ∂(globalBernoulli G.edgeSet
      (FK.Exploration.FKCoupling.upperRateNN_lt_one
        (lt_trans zero_lt_one hq₁) hp₀ hp₁).le : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G := by
  let hq : 0 < q := lt_trans zero_lt_one hq₁
  have hrate : FK.Exploration.FKCoupling.upperRateNN q p = p :=
    upperRateNN_eq_of_one_lt_q hp₀ hp₁ hq₁
  have hs : ((unitOfNN (FK.Exploration.FKCoupling.upperRateNN q p)
      (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le) : unitInterval) : ℝ) <
      criticalProb G o := by
    change (FK.Exploration.FKCoupling.upperRateNN q p : ℝ) < criticalProb G o
    rwa [hrate]
  change ∀ᵐ ω ∂(percolation G (unitOfNN
    (FK.Exploration.FKCoupling.upperRateNN q p)
    (FK.Exploration.FKCoupling.upperRateNN_le_one hq hp₁.le))),
    ω ∈ FK.NonPercolating G
  exact FK.PercolationRoot.ae_nonPercolating_percolation_of_lt_criticalProb_single
    hG hs

/-- Empty star and cycle families are legal in Proposition 4.2(2).  Thus every
source weak limit and every source geometric all-region DLR law is dominated
by the ordinary global Bernoulli law at `p = upperRateNN q p`. -/
theorem globalUpper_dominates_sourceFKMeasures_of_one_lt_q
    [Countable G.edgeSet] [Nonempty V] {q p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₁ : 1 < q) (e₀ : G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) (lt_trans zero_lt_one hq₁) hp₁.le) :
    FKLimit.StochasticallyDominates
      (globalBernoulli G.edgeSet
        (FK.Exploration.FKCoupling.upperRateNN_lt_one
          (lt_trans zero_lt_one hq₁) hp₀ hp₁).le) μ := by
  let hq : 0 < q := lt_trans zero_lt_one hq₁
  obtain ⟨E, hsource, hne⟩ :=
    exists_nonempty_sourceFKMeasure_tail hq hp₁.le e₀ hμ
  have hcomp := FK.Prop42Source.proposition_4_2_gt
    (E.exhaustion (G := G)) (E.data (G := G))
    (E.data_vertex_injective (G := G)) hp₀ hp₁ hq₁ hsource
    (∅ : Set G.edgeSet) (fun _ => ∅) 0
    (by simp [FKLimit.IsSeparatedDeviceFamily]) (by simp) (by simp)
    (∅ : Set G.edgeSet) (fun _ => ∅) 0
    (by simp [FKLimit.IsSeparatedDeviceFamily]) (by simp) (by simp) hne
  have hu := hcomp.2
  rw [gtUpperParameters_empty hp₀ hp₁ hq₁ 0] at hu
  have hrate : FK.Exploration.FKCoupling.upperRateNN q p = p :=
    upperRateNN_eq_of_one_lt_q hp₀ hp₁ hq₁
  simpa only [globalBernoulli, hrate] using hu

/-- Every member of the full source family is almost surely nonpercolating in
the immediate closed subcritical regime `1 < q`, `0 < p < p_c(G,o)`. -/
theorem ae_nonPercolating_sourceFKMeasure_of_one_lt_q
    [Countable G.edgeSet] [Nonempty V]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₁ : 1 < q) (e₀ : G.edgeSet)
    (hsub : (p : ℝ) < criticalProb G o)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) (lt_trans zero_lt_one hq₁) hp₁.le) :
    ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  exact FKLimit.ae_nonPercolating_of_stochasticallyDominates G
    (globalUpper_dominates_sourceFKMeasures_of_one_lt_q hp₀ hp₁ hq₁ e₀ hμ)
    (ae_nonPercolating_globalUpper_of_one_lt_q hG o hp₀ hp₁ hq₁ hsub)

/-- **Immediate closed subcritical wrapper for `1 < q`.**  Arbitrary-nested
 equation (9) and empty-device Proposition 4.2(2) give a singleton full source
family, including source DLR laws, whose unique law does not percolate. -/
theorem sourceFKMeasures_singleton_of_one_lt_q_subcritical
    [Countable G.edgeSet]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (hq₁ : 1 < q) (e₀ : G.edgeSet)
    (hsub : (p : ℝ) < criticalProb G o) :
    ∃ μ₀ : ProbabilityMeasure (Configuration G.edgeSet),
      SourceFKMeasures (G := G) (lt_trans zero_lt_one hq₁) hp₁.le = {μ₀} ∧
        ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)), ω ∈ FK.NonPercolating G := by
  let _ : Nonempty V := ⟨o⟩
  let hq : 0 < q := lt_trans zero_lt_one hq₁
  let ρ : ProbabilityMeasure (Configuration G.edgeSet) :=
    globalBernoulli G.edgeSet
      (FK.Exploration.FKCoupling.upperRateNN_lt_one hq hp₀ hp₁).le
  have hρ : ∀ᵐ ω ∂(ρ : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G :=
    ae_nonPercolating_globalUpper_of_one_lt_q hG o hp₀ hp₁ hq₁ hsub
  refine theorem_1_10_modulo_AG_window_and_lemma_2_1 hq hp₁.le ρ hρ
    (edgeRoots G) (sourceNestedEquationNine hq hp₀ hp₁) ?_
  intro μ hμ
  exact globalUpper_dominates_sourceFKMeasures_of_one_lt_q hp₀ hp₁ hq₁ e₀
    (mem_sourceFKMeasures_of_weak hq hp₁.le hμ)

end

end FK.ClassicalSubcriticalGt

#check FK.ClassicalSubcriticalGt.upperRateNN_eq_of_one_lt_q
#check FK.ClassicalSubcriticalGt.gtUpperParameters_empty
#check FK.ClassicalSubcriticalGt.ae_nonPercolating_globalUpper_of_one_lt_q
#check FK.ClassicalSubcriticalGt.globalUpper_dominates_sourceFKMeasures_of_one_lt_q
#check FK.ClassicalSubcriticalGt.ae_nonPercolating_sourceFKMeasure_of_one_lt_q
#check FK.ClassicalSubcriticalGt.sourceFKMeasures_singleton_of_one_lt_q_subcritical

#print axioms FK.ClassicalSubcriticalGt.upperRateNN_eq_of_one_lt_q
#print axioms FK.ClassicalSubcriticalGt.gtUpperParameters_empty
#print axioms FK.ClassicalSubcriticalGt.ae_nonPercolating_globalUpper_of_one_lt_q
#print axioms FK.ClassicalSubcriticalGt.globalUpper_dominates_sourceFKMeasures_of_one_lt_q
#print axioms FK.ClassicalSubcriticalGt.ae_nonPercolating_sourceFKMeasure_of_one_lt_q
#print axioms FK.ClassicalSubcriticalGt.sourceFKMeasures_singleton_of_one_lt_q_subcritical
