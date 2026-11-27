import FK.PlanarSourceAssembly

/-!
# Dual source singleton at the original Theorem 1.11 window

The exchanged enhanced profile is fed into `FK.SourceWindow`'s exact
arbitrary-source upper-window theorem.  A record checks the dual device data;
it is not constructed from an edge bijection.  The dual nested equation (9),
AG deactivation shift, and dual graph hypotheses stay explicit.  The finite
free duality and the identification of the dual box DLR class with this source
singleton are left to the public planar all-box assembly.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal unitInterval Topology Classical

namespace FK.Planar.SourceWindowAssembly

open FK.InfiniteVolume
open FK.SourceUniqueness
open FK.SourceWindow
open FK.Configuration
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u v

/-- The exact data compatibility needed to identify the exchanged primal
lower profile with a dual source device's upper profile. -/
structure ExchangedDevices {V : Type u} {F : Type v}
    {G : SimpleGraph V} {GD : SimpleGraph F} [G.LocallyFinite] [GD.LocallyFinite]
    (edge : G.edgeSet ≃ GD.edgeSet) (D : SourceEnhancementDevices G)
    (DD : SourceEnhancementDevices GD) : Prop where
  star : DD.Sstar = edge '' D.Scycle
  cycle : DD.Scycle = edge '' D.Sstar
  Delta : DD.Delta = D.L
  L : DD.L = D.Delta

section DeviceIdentity

variable {V : Type u} {F : Type v} {G : SimpleGraph V} {GD : SimpleGraph F}
variable [Countable V] [Countable F] [G.LocallyFinite] [GD.LocallyFinite]

/-- Matching devices have definitionally matching upper source laws. -/
theorem upperLaw_exchanged (edge : G.edgeSet ≃ GD.edgeSet)
    (D : SourceEnhancementDevices G) (DD : SourceEnhancementDevices GD)
    (M : ExchangedDevices edge D DD) {q r : NNReal} (hq : 0 < q) (hr : r ≤ 1) :
    upperLaw DD.Sstar DD.Scycle DD.Delta DD.L hq hr =
      upperLaw (edge '' D.Scycle) (edge '' D.Sstar) D.L D.Delta hq hr := by
  rw [M.star, M.cycle, M.Delta, M.L]

end DeviceIdentity

section QLess

variable {V : Type u} {F : Type v} [Countable V] [Countable F]
variable {G : SimpleGraph V} {GD : SimpleGraph F} [G.LocallyFinite] [GD.LocallyFinite]

/-- **Dual source strong uniqueness in the original parameter window, `q < 1`.**
The conclusion is only the singleton supplied by Theorem 1.10 on the dual graph;
it is not a primal strong-uniqueness claim. -/
theorem exists_dual_source_singleton_window_q_lt_one
    (hGD : GD.Connected) (oD : F)
    (hpcD0 : 0 < criticalProb GD oD) (hpcD1 : criticalProb GD oD < 1)
    {q : NNReal} (hq : 0 < q) (hq1 : q < 1)
    (D : SourceEnhancementDevices G) (DD : SourceEnhancementDevices GD)
    (edge : G.edgeSet ≃ GD.edgeSet) (M : ExchangedDevices edge D DD)
    (eD0 : GD.edgeSet)
    (hdeact : FK.AGShift.DeactivationShift (FK.EssentialWindow.Percolating GD)
      (criticalProb GD oD) (edge '' D.Sstar))
    (roots : Finset GD.edgeSet → Finset F)
    (hEq9 : ∀ {p : NNReal} (hp0 : 0 < p) (hp1 : p < 1),
      NestedEquationNine (G := GD) hq (FK.FinitePlane.dualParameter_le_one hq hp1.le)
        (upperLaw DD.Sstar DD.Scycle DD.Delta DD.L hq
          (FK.FinitePlane.dualParameter_le_one hq hp1.le)) roots) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1),
        min (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) >
          1 - criticalProb GD oD - γ →
        ∃ ν₀ : ProbabilityMeasure (Configuration GD.edgeSet),
          SourceFKMeasures (G := GD) hq (FK.FinitePlane.dualParameter_le_one hq hp1.le) =
            {ν₀} ∧
          ∀ᵐ ω ∂(ν₀ : Measure (Configuration GD.edgeSet)),
            ω ∈ FK.NonPercolating GD := by
  letI : Nonempty F := ⟨oD⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : (q : ℝ) < 1 := by exact_mod_cast hq1
  obtain ⟨γ, hγ, hwinD⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_q_lt_one
      (edge '' D.Scycle) (edge '' D.Sstar) (D.L - 1) (D.Delta - 1)
      (q : ℝ) hqR hq1R
      (FK.EssentialWindow.isUpperSet_percolating GD)
      (FK.EssentialWindow.measurableSet_percolating GD hGD) hdeact hpcD0 hpcD1
  refine ⟨γ, hγ, ?_⟩
  intro p hp0 hp1 hwindow
  let r := FK.FinitePlane.dualParameter q p
  let hr : r ≤ 1 := FK.FinitePlane.dualParameter_le_one hq hp1.le
  have hr0 : 0 < r := FK.FinitePlane.dualParameter_pos hq hp0 hp1
  have hr1 : r < 1 := FK.FinitePlane.dualParameter_lt_one hq hp0 hp1.le
  have hrIcc : ((r : NNReal) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hr⟩
  have hw : min (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) >
      1 - criticalProb GD oD - γ := hwindow
  have hdual : max ((r : NNReal) : ℝ)
      (FK.Enhancement.fkPrime ((r : NNReal) : ℝ) (q : ℝ)) <
        criticalProb GD oD + γ :=
    (FK.InfiniteVolume.parameter_window_iff_dualParameter hq hp1.le
      (criticalProb GD oD) γ).2 hw
  have hzero : (upperLaw DD.Sstar DD.Scycle DD.Delta DD.L hq hr : Measure _)
      (FK.EssentialWindow.Percolating GD) = 0 := by
    rw [upperLaw_exchanged edge D DD M hq hr]
    exact hwinD ((r : NNReal) : ℝ) hrIcc hdual
  exact unique_of_upperLaw_zero_q_lt_one hq hr0 hr1 hq1 DD eD0 roots
    (hEq9 hp0 hp1) hzero

end QLess

section QGreater

variable {V : Type u} {F : Type v} [Countable V] [Countable F]
variable {G : SimpleGraph V} {GD : SimpleGraph F} [G.LocallyFinite] [GD.LocallyFinite]

/-- The `1 < q` dual source singleton window. -/
theorem exists_dual_source_singleton_window_one_lt_q
    (hGD : GD.Connected) (oD : F)
    (hpcD0 : 0 < criticalProb GD oD) (hpcD1 : criticalProb GD oD < 1)
    {q : NNReal} (hq1 : 1 < q)
    (D : SourceEnhancementDevices G) (DD : SourceEnhancementDevices GD)
    (edge : G.edgeSet ≃ GD.edgeSet) (M : ExchangedDevices edge D DD)
    (eD0 : GD.edgeSet)
    (hdeact : FK.AGShift.DeactivationShift (FK.EssentialWindow.Percolating GD)
      (criticalProb GD oD) (edge '' D.Scycle))
    (roots : Finset GD.edgeSet → Finset F)
    (hEq9 : ∀ {p : NNReal} (hp0 : 0 < p) (hp1 : p < 1),
      NestedEquationNine (G := GD) (lt_trans zero_lt_one hq1)
        (FK.FinitePlane.dualParameter_le_one (lt_trans zero_lt_one hq1) hp1.le)
        (upperLaw DD.Sstar DD.Scycle DD.Delta DD.L (lt_trans zero_lt_one hq1)
          (FK.FinitePlane.dualParameter_le_one (lt_trans zero_lt_one hq1) hp1.le)) roots) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (p : NNReal) (hp0 : 0 < p) (hp1 : p < 1),
        min (p : ℝ) (FK.Enhancement.fkPrime (p : ℝ) (q : ℝ)) >
          1 - criticalProb GD oD - γ →
        ∃ ν₀ : ProbabilityMeasure (Configuration GD.edgeSet),
          SourceFKMeasures (G := GD) (lt_trans zero_lt_one hq1)
            (FK.FinitePlane.dualParameter_le_one (lt_trans zero_lt_one hq1) hp1.le) =
            {ν₀} ∧
          ∀ᵐ ω ∂(ν₀ : Measure (Configuration GD.edgeSet)),
            ω ∈ FK.NonPercolating GD := by
  letI : Nonempty F := ⟨oD⟩
  let hq : 0 < q := lt_trans zero_lt_one hq1
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1R : 1 < (q : ℝ) := by exact_mod_cast hq1
  obtain ⟨γ, hγ, hwinD⟩ :=
    FK.AGShift.upperWindow_of_deactivationShift_one_lt_q
      (edge '' D.Scycle) (edge '' D.Sstar) (D.L - 1) (D.Delta - 1)
      (q : ℝ) hqR hq1R
      (FK.EssentialWindow.isUpperSet_percolating GD)
      (FK.EssentialWindow.measurableSet_percolating GD hGD) hdeact hpcD0 hpcD1
  refine ⟨γ, hγ, ?_⟩
  intro p hp0 hp1 hwindow
  let r := FK.FinitePlane.dualParameter q p
  let hr : r ≤ 1 := FK.FinitePlane.dualParameter_le_one hq hp1.le
  have hr0 : 0 < r := FK.FinitePlane.dualParameter_pos hq hp0 hp1
  have hr1 : r < 1 := FK.FinitePlane.dualParameter_lt_one hq hp0 hp1.le
  have hrIcc : ((r : NNReal) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, by exact_mod_cast hr⟩
  have hw : min (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) >
      1 - criticalProb GD oD - γ := hwindow
  have hdual : max ((r : NNReal) : ℝ)
      (FK.Enhancement.fkPrime ((r : NNReal) : ℝ) (q : ℝ)) <
        criticalProb GD oD + γ :=
    (FK.InfiniteVolume.parameter_window_iff_dualParameter hq hp1.le
      (criticalProb GD oD) γ).2 hw
  have hzero : (upperLaw DD.Sstar DD.Scycle DD.Delta DD.L hq hr : Measure _)
      (FK.EssentialWindow.Percolating GD) = 0 := by
    rw [upperLaw_exchanged edge D DD M hq hr]
    exact hwinD ((r : NNReal) : ℝ) hrIcc hdual
  exact unique_of_upperLaw_zero_one_lt_q hr0 hr1 hq1 DD eD0 roots
    (hEq9 hp0 hp1) hzero

end QGreater

end

end FK.Planar.SourceWindowAssembly
