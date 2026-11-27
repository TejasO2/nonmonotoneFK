import FK.SourceLowerWindow

/-!
# Source-measure assembly for the cluster part of Theorem 1.11

The public planar all-box theorem takes genericlower/upper phase inputs.  This
module constructs those inputs from the source's devices and AG shift
predicates.  It proves almost-sure existence and uniqueness of the primal
infinite cluster for **every** member of the arbitrary-exhaustion source FK
family.  Finite equation (12), dual DLR uniqueness and the continuous planar
geometry remain separate inputs; no strong-uniqueness or AG theorem is claimed.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Topology Classical

namespace FK.Planar.SourceWindowAssembly

open FK.InfiniteVolume
open FK.SourceUniqueness
open FK.SourceWindow
open FK.Configuration
open FK.ClusterCover
open FK.Planar
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u v

/-- The phase-library percolation event is the cluster-cover event used by the
planar measure assembly. -/
lemma percolating_eq_hasInfiniteCluster {V : Type*} (G : SimpleGraph V) :
    FK.EssentialWindow.Percolating G = {ω | HasInfiniteCluster G ω} := by
  ext ω
  simp only [FK.EssentialWindow.Percolating, HasInfiniteCluster,
    clusterAvoid_empty_eq, Set.mem_setOf_eq]

section QLess

variable {V : Type u} {F : Type v} [Countable V] [Countable F]
variable {G : SimpleGraph V} {GD : SimpleGraph F} [G.LocallyFinite] [GD.LocallyFinite]

/-- **Exactly one infinite cluster on the full source FK family, `q < 1`.**

The two AG inputs are kept in their primitive shift form.  The primal
activation applies to `D.Sstar`; after open/closed duality the dual
deactivation applies to `edge '' D.Sstar`, which is the active cycle set of the
exchanged upper profile.  The only geometric input is the named planar
cluster implication. -/
theorem exists_exactlyOneInfiniteCluster_window_q_lt_one
    (hG : G.Connected) (hGD : GD.Connected) (o : V) (oD : F)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    (hpcD0 : 0 < criticalProb GD oD) (hpcD1 : criticalProb GD oD < 1)
    {q : NNReal} (hq : 0 < q) (hq1 : q < 1)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (edge : G.edgeSet ≃ GD.edgeSet)
    (hact : FK.AGShift.ActivationShift (FK.EssentialWindow.Percolating G)
      (criticalProb G o) D.Sstar)
    (hdeact : FK.AGShift.DeactivationShift (FK.EssentialWindow.Percolating GD)
      (criticalProb GD oD) (edge '' D.Sstar))
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge) :
    ∃ δ γ : ℝ, 0 < δ ∧ 0 < γ ∧
      ∀ (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1),
        criticalProb G o - δ < min (p : ℝ)
            (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) →
          max ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ)
            (FK.Enhancement.fkPrime
              ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) (q : ℝ)) <
            criticalProb GD oD + γ →
          ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
            μ ∈ SourceFKMeasures (G := G) hq hp1.le →
            ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
              ExactlyOneInfiniteCluster G ω := by
  letI : Nonempty V := ⟨o⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
  obtain ⟨δ, hδ, hwin⟩ :=
    FK.AGShift.lowerWindow_of_activationShift_q_lt_one
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) (q : ℝ) hqR hq1R
      (FK.EssentialWindow.isUpperSet_percolating G)
      (FK.EssentialWindow.measurableSet_percolating G hG) hact hpc0 hpc1
  obtain ⟨γ, hγ, hwinD⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_q_lt_one
      (edge '' D.Scycle) (edge '' D.Sstar) (D.L - 1) (D.Delta - 1)
      (q : ℝ) hqR hq1R
      (FK.EssentialWindow.isUpperSet_percolating GD)
      (FK.EssentialWindow.measurableSet_percolating GD hGD) hdeact hpcD0 hpcD1
  refine ⟨δ, γ, hδ, hγ, ?_⟩
  intro p hp0 hp1 hprimal hdual μ hμ
  let r := FK.FinitePlane.dualParameter q p
  let hr : r ≤ 1 := FK.FinitePlane.dualParameter_le_one hq hp1.le
  let rate : G.edgeSet → unitInterval := FK.Phases.lowerWeights
    D.Sstar D.Scycle (D.Delta - 1) (D.L - 1)
    (show 0 ≤ (p : ℝ) by positivity) (show (p : ℝ) ≤ 1 by exact_mod_cast hp1.le)
    (show 0 < (q : ℝ) by exact_mod_cast hq)
  have hpIcc : (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hp1.le⟩
  have hone : (lowerLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le : Measure _)
      {ω | HasInfiniteCluster G ω} = 1 := by
    rw [← percolating_eq_hasInfiniteCluster]
    exact hwin (p : ℝ) hpIcc hprimal
  have hrIcc : ((r : NNReal) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hr⟩
  have hzeroUpper :
      (upperLaw (edge '' D.Scycle) (edge '' D.Sstar) D.L D.Delta hq hr : Measure _)
        (FK.EssentialWindow.Percolating GD) = 0 :=
    hwinD ((r : NNReal) : ℝ) hrIcc hdual
  have hzero : bernoulliProduct (fun f => σ (rate (edge.symm f)))
      {ω | HasInfiniteCluster GD ω} = 0 := by
    change bernoulliProduct (fun f => σ (FK.Phases.lowerWeights
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) _ _ _ (edge.symm f)))
        {ω | HasInfiniteCluster GD ω} = 0
    rw [FK.Planar.EnhancedProfiles.sigma_lowerWeights_eq_upperWeights_dualParameter_q_lt_one
      edge D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) hq hp0 hp1 hq1]
    rw [← percolating_eq_hasInfiniteCluster]
    exact hzeroUpper
  have hlowerPM := lowerLaw_dominatedBy_sourceFKMeasures_q_lt_one
    hq hp0 hp1 hq1 D e₀ hμ
  have hlower : StochDom (bernoulliProduct rate) (μ : Measure _) := by
    intro A hA hAupper
    change (lowerLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le : Measure _) A ≤
      (μ : Measure _) A
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact_mod_cast hlowerPM A hA hAupper
  exact ae_exactlyOneInfiniteCluster_of_primal_bernoulliProduct_stochDom
    G GD edge rate (μ : Measure _) hgeometry hlower hzero hone

end QLess

section QGreater

variable {V : Type u} {F : Type v} [Countable V] [Countable F]
variable {G : SimpleGraph V} {GD : SimpleGraph F} [G.LocallyFinite] [GD.LocallyFinite]

/-- The `1 < q` companion.  The active primal set is `D.Scycle`, and this is
also the active star set of the exchanged dual upper profile. -/
theorem exists_exactlyOneInfiniteCluster_window_one_lt_q
    (hG : G.Connected) (hGD : GD.Connected) (o : V) (oD : F)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    (hpcD0 : 0 < criticalProb GD oD) (hpcD1 : criticalProb GD oD < 1)
    {q : NNReal} (hq1 : 1 < q)
    (D : SourceEnhancementDevices G) (e₀ : G.edgeSet)
    (edge : G.edgeSet ≃ GD.edgeSet)
    (hact : FK.AGShift.ActivationShift (FK.EssentialWindow.Percolating G)
      (criticalProb G o) D.Scycle)
    (hdeact : FK.AGShift.DeactivationShift (FK.EssentialWindow.Percolating GD)
      (criticalProb GD oD) (edge '' D.Scycle))
    (hgeometry : DualNonpercolationForcesPrimalAtMostOne G GD edge) :
    ∃ δ γ : ℝ, 0 < δ ∧ 0 < γ ∧
      ∀ (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1),
        criticalProb G o - δ < min (p : ℝ)
            (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) →
          max ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ)
            (FK.Enhancement.fkPrime
              ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ) (q : ℝ)) <
            criticalProb GD oD + γ →
          ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
            μ ∈ SourceFKMeasures (G := G) (lt_trans zero_lt_one hq1) hp1.le →
            ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
              ExactlyOneInfiniteCluster G ω := by
  letI : Nonempty V := ⟨o⟩
  let hq : 0 < q := lt_trans zero_lt_one hq1
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : 1 < (q : ℝ) := by exact_mod_cast hq1
  obtain ⟨δ, hδ, hwin⟩ :=
    FK.AGShift.lowerWindow_of_activationShift_one_lt_q
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) (q : ℝ) hqR hq1R
      (FK.EssentialWindow.isUpperSet_percolating G)
      (FK.EssentialWindow.measurableSet_percolating G hG) hact hpc0 hpc1
  obtain ⟨γ, hγ, hwinD⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_one_lt_q
      (edge '' D.Scycle) (edge '' D.Sstar) (D.L - 1) (D.Delta - 1)
      (q : ℝ) hqR hq1R
      (FK.EssentialWindow.isUpperSet_percolating GD)
      (FK.EssentialWindow.measurableSet_percolating GD hGD) hdeact hpcD0 hpcD1
  refine ⟨δ, γ, hδ, hγ, ?_⟩
  intro p hp0 hp1 hprimal hdual μ hμ
  let r := FK.FinitePlane.dualParameter q p
  let hr : r ≤ 1 := FK.FinitePlane.dualParameter_le_one hq hp1.le
  let rate : G.edgeSet → unitInterval := FK.Phases.lowerWeights
    D.Sstar D.Scycle (D.Delta - 1) (D.L - 1)
    (show 0 ≤ (p : ℝ) by positivity) (show (p : ℝ) ≤ 1 by exact_mod_cast hp1.le)
    (show 0 < (q : ℝ) by exact_mod_cast hq)
  have hpIcc : (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hp1.le⟩
  have hone : (lowerLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le : Measure _)
      {ω | HasInfiniteCluster G ω} = 1 := by
    rw [← percolating_eq_hasInfiniteCluster]
    exact hwin (p : ℝ) hpIcc hprimal
  have hrIcc : ((r : NNReal) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hr⟩
  have hzeroUpper :
      (upperLaw (edge '' D.Scycle) (edge '' D.Sstar) D.L D.Delta hq hr : Measure _)
        (FK.EssentialWindow.Percolating GD) = 0 :=
    hwinD ((r : NNReal) : ℝ) hrIcc hdual
  have hzero : bernoulliProduct (fun f => σ (rate (edge.symm f)))
      {ω | HasInfiniteCluster GD ω} = 0 := by
    change bernoulliProduct (fun f => σ (FK.Phases.lowerWeights
      D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) _ _ _ (edge.symm f)))
        {ω | HasInfiniteCluster GD ω} = 0
    rw [FK.Planar.EnhancedProfiles.sigma_lowerWeights_eq_upperWeights_dualParameter_one_lt_q
      edge D.Sstar D.Scycle (D.Delta - 1) (D.L - 1) hp0 hp1 hq1]
    rw [← percolating_eq_hasInfiniteCluster]
    exact hzeroUpper
  have hlowerPM := lowerLaw_dominatedBy_sourceFKMeasures_one_lt_q
    hp0 hp1 hq1 D e₀ hμ
  have hlower : StochDom (bernoulliProduct rate) (μ : Measure _) := by
    intro A hA hAupper
    change (lowerLaw D.Sstar D.Scycle D.Delta D.L hq hp1.le : Measure _) A ≤
      (μ : Measure _) A
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact_mod_cast hlowerPM A hA hAupper
  exact ae_exactlyOneInfiniteCluster_of_primal_bernoulliProduct_stochDom
    G GD edge rate (μ : Measure _) hgeometry hlower hzero hone

end QGreater

end

end FK.Planar.SourceWindowAssembly
