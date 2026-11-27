import FK.DualEnhancedProfiles

/-!
# The source lower window and its planar dual

`FK.SourceWindow` exposes the arbitrary-exhaustion upper product used for
Theorem 1.10.  This file supplies the complementary lower product used in
Theorem 1.11, proves its stochastic lower bound for the whole source family,
and identifies its open/closed dual with the exact upper product at `p*`.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Topology Classical

namespace FK.SourceWindow

open FK.InfiniteVolume
open FK.SourceUniqueness
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u v

/-- The lower Bernoulli product associated with the source devices. -/
noncomputable def lowerLaw {V : Type u} [Countable V] {G : SimpleGraph V}
    [G.LocallyFinite] (Sstar Scycle : Set G.edgeSet) (Delta L : ℕ)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    ProbabilityMeasure (Configuration G.edgeSet) :=
  FKLimit.bernoulliProduct
    (FK.Phases.lowerWeights Sstar Scycle (Delta - 1) (L - 1)
      (show 0 ≤ (p : ℝ) by positivity)
      (show (p : ℝ) ≤ 1 by exact_mod_cast hp)
      (show 0 < (q : ℝ) by exact_mod_cast hq))

section ParameterIdentification

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal}

/-- In the `q < 1` regime, `lowerLaw` is Proposition 4.2's lower star-
enhanced product. -/
theorem lowerLaw_eq_ltLowerParameters (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : q < 1) (Sstar Scycle : Set G.edgeSet) (Delta L : ℕ) :
    lowerLaw Sstar Scycle Delta L hq hp1.le =
      FKLimit.bernoulliProduct
        (FKLimit.ltLowerParameters (p : ℝ) (q : ℝ)
          (show (p : ℝ) ∈ Ioo 0 1 by
            exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
          (show 0 < (q : ℝ) by exact_mod_cast hq)
          ((FKLimit.self_lt_fkSingletonParameter_iff
              (show (p : ℝ) ∈ Ioo 0 1 by
                exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
              (show 0 < (q : ℝ) by exact_mod_cast hq)).2
            (by exact_mod_cast hq1))
          Delta Sstar) := by
  let hp : (p : ℝ) ∈ Ioo 0 1 :=
    ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  change FKLimit.bernoulliProduct _ = FKLimit.bernoulliProduct _
  rw [FK.MainIntegration.ltLowerParameters_eq_lowerWeights hp hqR hpp
    Sstar Scycle Delta L]

/-- In the `1 < q` regime, `lowerLaw` is Proposition 4.2's lower cycle-
enhanced product. -/
theorem lowerLaw_eq_gtLowerParameters (hp0 : 0 < p) (hp1 : p < 1)
    (hq1 : 1 < q) (Sstar Scycle : Set G.edgeSet) (Delta L : ℕ) :
    lowerLaw Sstar Scycle Delta L (lt_trans zero_lt_one hq1) hp1.le =
      FKLimit.bernoulliProduct
        (FKLimit.gtLowerParameters (p : ℝ) (q : ℝ)
          (show (p : ℝ) ∈ Ioo 0 1 by
            exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
          (show 0 < (q : ℝ) by exact_mod_cast (lt_trans zero_lt_one hq1))
          ((FKLimit.fkSingletonParameter_lt_self_iff
              (show (p : ℝ) ∈ Ioo 0 1 by
                exact ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩)
              (show 0 < (q : ℝ) by exact_mod_cast (lt_trans zero_lt_one hq1))).2
            (by exact_mod_cast hq1))
          L Scycle) := by
  let hp : (p : ℝ) ∈ Ioo 0 1 :=
    ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hq1)
  let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
  change FKLimit.bernoulliProduct _ = FKLimit.bernoulliProduct _
  rw [FK.MainIntegration.gtLowerParameters_eq_lowerWeights hp hqR hpp
    Sstar Scycle Delta L]

end ParameterIdentification

section SourceComparison

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
variable {q p : NNReal}

/-- Every source FK law can be tested by Proposition 4.2 on some tail of an
induced vertex exhaustion.  For weak limits this is their own exhaustion; for
all-region geometric DLR laws it is an arbitrary exhaustion with the source
convention restricted to it. -/
theorem exists_nonempty_sourceFKMeasure_tail [Nonempty V]
    (hq : 0 < q) (hp : p ≤ 1) (e₀ : G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) hq hp) :
    ∃ E : VertexExhaustion V,
      FK.Prop42Source.SourceFKMeasure (E.exhaustion (G := G)) (E.data (G := G))
        hq hp μ ∧ ∀ n, Nonempty ((E.box (G := G) n).edges) := by
  rcases hμ with hμ | ⟨E, hE⟩
  · obtain ⟨Φ, hΦ, hμ⟩ := Set.mem_iUnion.mp hμ
    let E₀ : VertexExhaustion V :=
      Classical.choice (VertexExhaustion.exists_vertexExhaustion (V := V))
    obtain ⟨k, hne⟩ := exists_tail_nonempty_edges E₀ e₀
    let E := E₀.tail k
    refine ⟨E, Or.inr ⟨assignment E Φ, ?_, mem_dlr_restrict hμ⟩, hne⟩
    exact FK.Prop42Source.sourceConvention_of_isGeometric (E.data (G := G))
      (isGeometric_assignment E Φ hΦ) (E.data_vertex_injective (G := G))
  · obtain ⟨k, hne⟩ := exists_tail_nonempty_edges E e₀
    exact ⟨E.tail k, Or.inl (isSourceFKLimit_tail hq hp E k hE), hne⟩

/-- Proposition 4.2's lower comparison for every arbitrary-exhaustion source
weak limit and every geometric all-region source DLR law (`q < 1`). -/
theorem lowerLaw_dominatedBy_sourceFKMeasures_q_lt_one [Nonempty V]
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) hq hp1.le) :
    FKLimit.StochasticallyDominates μ
      (lowerLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le) := by
  obtain ⟨E, hsource, hne⟩ := exists_nonempty_sourceFKMeasure_tail hq hp1.le e₀ hμ
  have hcomp := FK.Prop42Source.proposition_4_2_lt
    (E.exhaustion (G := G)) (E.data (G := G)) (E.data_vertex_injective (G := G))
    hq hp0 hp1 hq1 hsource
    D.Sstar D.Dstar D.Delta D.separatedStar D.starDevice D.cardStar
    D.Scycle D.Dcycle D.L D.separatedCycle D.cycleDevice D.cardCycle hne
  rw [lowerLaw_eq_ltLowerParameters hq hp0 hp1 hq1
    D.Sstar D.Scycle D.Delta D.L]
  exact hcomp.1

/-- The `1 < q` lower comparison for the same full source family. -/
theorem lowerLaw_dominatedBy_sourceFKMeasures_one_lt_q [Nonempty V]
    (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : μ ∈ SourceFKMeasures (G := G) (lt_trans zero_lt_one hq1) hp1.le) :
    FKLimit.StochasticallyDominates μ
      (lowerLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1) hp1.le) := by
  let hq : 0 < q := lt_trans zero_lt_one hq1
  obtain ⟨E, hsource, hne⟩ := exists_nonempty_sourceFKMeasure_tail hq hp1.le e₀ hμ
  have hcomp := FK.Prop42Source.proposition_4_2_gt
    (E.exhaustion (G := G)) (E.data (G := G)) (E.data_vertex_injective (G := G))
    hp0 hp1 hq1 hsource
    D.Sstar D.Dstar D.Delta D.separatedStar D.starDevice D.cardStar
    D.Scycle D.Dcycle D.L D.separatedCycle D.cycleDevice D.cardCycle hne
  rw [lowerLaw_eq_gtLowerParameters hp0 hp1 hq1 D.Sstar D.Scycle D.Delta D.L]
  exact hcomp.1

end SourceComparison

section ProductDuality

open FK.Configuration
open FK.Planar.EnhancedProfiles

variable {V : Type u} {F : Type v} [Countable V] [Countable F]
variable {G : SimpleGraph V} {GD : SimpleGraph F} [G.LocallyFinite] [GD.LocallyFinite]

/-- The dual of the exact primal lower product is the exact upper product at
`p*`, with star/cycle data exchanged (`q < 1`). -/
theorem map_dual_lowerLaw_q_lt_one (edge : G.edgeSet ≃ GD.edgeSet)
    (D : SourceEnhancementDevices G) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    Measure.map (dualMeasurableEquiv edge)
        (lowerLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le : Measure _) =
      (upperLaw (edge '' D.Scycle) (edge '' D.Sstar) D.L D.Delta hq
        (FK.FinitePlane.dualParameter_le_one hq hp1.le) : Measure _) := by
  change Measure.map (dualMeasurableEquiv edge) (bernoulliProduct
      (FK.Phases.lowerWeights D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) _ _ _)) =
    FKLimit.bernoulliProduct
      (FK.Phases.upperWeights (edge '' D.Scycle) (edge '' D.Sstar)
        (D.L - 1) (D.Delta - 1) _ _ _)
  rw [map_dual_bernoulliProduct]
  congr 1
  exact sigma_lowerWeights_eq_upperWeights_dualParameter_q_lt_one
    edge D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) hq hp0 hp1 hq1

/-- The `1 < q` product-duality identity. -/
theorem map_dual_lowerLaw_one_lt_q (edge : G.edgeSet ≃ GD.edgeSet)
    (D : SourceEnhancementDevices G) {q p : NNReal}
    (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q) :
    Measure.map (dualMeasurableEquiv edge)
        (lowerLaw D.Sstar D.Scycle D.Delta D.L (lt_trans zero_lt_one hq1) hp1.le :
          Measure _) =
      (upperLaw (edge '' D.Scycle) (edge '' D.Sstar) D.L D.Delta
        (lt_trans zero_lt_one hq1)
        (FK.FinitePlane.dualParameter_le_one (lt_trans zero_lt_one hq1) hp1.le) :
          Measure _) := by
  let hq : 0 < q := lt_trans zero_lt_one hq1
  change Measure.map (dualMeasurableEquiv edge) (bernoulliProduct
      (FK.Phases.lowerWeights D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) _ _ _)) =
    FKLimit.bernoulliProduct
      (FK.Phases.upperWeights (edge '' D.Scycle) (edge '' D.Sstar)
        (D.L - 1) (D.Delta - 1) _ _ _)
  rw [map_dual_bernoulliProduct]
  congr 1
  exact sigma_lowerWeights_eq_upperWeights_dualParameter_one_lt_q
    edge D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) hp0 hp1 hq1

end ProductDuality

end

end FK.SourceWindow
