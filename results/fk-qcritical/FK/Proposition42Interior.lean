import FK.Proposition42DLR

/-!
# Interior, two-sided active-device DLR comparisons

The real-parameter and strict-prime-direction proofs are constructed here from
the interior `$q$` branch.  The remaining inputs are the DLR class itself, graph
nonemptiness, admissibility, and explicit finite cutset/path devices.
-/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology
open FKEnhancement

noncomputable section

/-- Complete interior `q < 1` DLR sandwich from actual star/cycle devices. -/
theorem lt_dlr_sandwich_of_active_devices_interior
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (Sstar : Set E) (Dstar : E → Finset E) (starAdmissible : ℕ → E → Prop)
    (Delta : ℕ) (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (hStarDevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Sstar Dstar starAdmissible n →
      ∃ χ : Finset (exh.box n).edges,
        (χ : Set (exh.box n).edges) ∈ CutsetFamily
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges (edgeExhaustionOfBox exh)
            Sstar Dstar starAdmissible n)) : Set (exh.box n).edges) e ∧
        χ.card ≤ Delta - 1)
    (Scycle : Set E) (Dcycle : E → Finset E) (cycleAdmissible : ℕ → E → Prop)
    (L : ℕ) (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    (Γ : ∀ n η, (exh.box n).edges → Set (Finset (exh.box n).edges))
    (hΓ : ∀ n η e, e ∈ activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle cycleAdmissible n) →
      OpenPath.AuxiliaryPaths (activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle cycleAdmissible n))
        e (Γ n η e))
    (hΓK : ∀ n η e, e ∈ activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle cycleAdmissible n) →
      ∀ {ω : OpenPath.Config (exh.box n).edges}, OpenPath.SomePathOpen (Γ n η e) ω →
        graphConnectionEvent (exh.box n).graph (Φ.partition n η) e (OpenPath.configToBool ω))
    (hCycleDevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Scycle Dcycle cycleAdmissible n →
      ∃ γ : Finset (exh.box n).edges, γ ∈ Γ n η e ∧ γ.card ≤ L - 1) :
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
      (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct
      (FKLimit.ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) ∧
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct
      (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  dsimp only
  let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) :=
    (FKLimit.self_lt_fkSingletonParameter_iff hp hqR).2 (by exact_mod_cast hq1)
  exact ⟨lt_dlr_lower_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar starAdmissible Delta hStar hstarAdm hne hStarDevices,
    lt_dlr_upper_of_active_cycle_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Scycle Dcycle cycleAdmissible L hCycle hcycleAdm hne Γ hΓ hΓK hCycleDevices⟩

/-- Complete interior `q > 1` DLR sandwich from actual star/cycle devices. -/
theorem gt_dlr_sandwich_of_active_devices_interior
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ
      (lt_trans zero_lt_one hq1 : 0 < q) hp1.le)
    (Sstar : Set E) (Dstar : E → Finset E) (starAdmissible : ℕ → E → Prop)
    (Delta : ℕ) (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (hStarDevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Sstar Dstar starAdmissible n →
      ∃ χ : Finset (exh.box n).edges,
        (χ : Set (exh.box n).edges) ∈ CutsetFamily
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges (edgeExhaustionOfBox exh)
            Sstar Dstar starAdmissible n)) : Set (exh.box n).edges) e ∧
        χ.card ≤ Delta - 1)
    (Scycle : Set E) (Dcycle : E → Finset E) (cycleAdmissible : ℕ → E → Prop)
    (L : ℕ) (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    (Γ : ∀ n η, (exh.box n).edges → Set (Finset (exh.box n).edges))
    (hΓ : ∀ n η e, e ∈ activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle cycleAdmissible n) →
      @OpenPath.AuxiliaryPaths _ (Classical.decEq _) (activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle cycleAdmissible n))
        e (Γ n η e))
    (hΓK : ∀ n η e, e ∈ activeWithinFinset (exh.box n)
        (FKLimit.activeEdges (edgeExhaustionOfBox exh) Scycle Dcycle cycleAdmissible n) →
      ∀ {ω : OpenPath.Config (exh.box n).edges}, OpenPath.SomePathOpen (Γ n η e) ω →
        FK.Finite.Conditional.endpointsConnectedWithout (exh.box n).graph (Φ.partition n η)
          e (OpenPath.configToBool ω))
    (hCycleDevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Scycle Dcycle cycleAdmissible n →
      ∃ γ : Finset (exh.box n).edges, γ ∈ Γ n η e ∧ γ.card ≤ L - 1) :
    let hq : 0 < q := lt_trans zero_lt_one hq1
    let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
    let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
      (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct
      (FKLimit.gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) ∧
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct
      (FKLimit.gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  dsimp only
  let hq : 0 < q := lt_trans zero_lt_one hq1
  let hp : (p : ℝ) ∈ Ioo 0 1 := ⟨by exact_mod_cast hp0, by exact_mod_cast hp1⟩
  let hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ) :=
    (FKLimit.fkSingletonParameter_lt_self_iff hp hqR).2 (by exact_mod_cast hq1)
  exact ⟨gt_dlr_lower_of_active_cycle_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Scycle Dcycle cycleAdmissible L hCycle hcycleAdm hne Γ hΓ hΓK hCycleDevices,
    gt_dlr_upper_of_active_star_devices exh Φ hq hp0 hp1 hq1 hp hqR hpp hμ
      Sstar Dstar starAdmissible Delta hStar hstarAdm hne hStarDevices⟩

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.lt_dlr_sandwich_of_active_devices_interior
#print axioms FK.EnhancedTransport.gt_dlr_sandwich_of_active_devices_interior
