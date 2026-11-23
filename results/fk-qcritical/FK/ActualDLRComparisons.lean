import FK.DLRCylinderTransport
import FK.EnhancedProducts

/-!
# Actual enhanced finite comparisons transported to DLR laws

The only finite-rate inputs here are coordinatewise bounds against the exact
closed-cutset enhancement sizes.  The stochastic finite comparisons themselves
are obtained from the actual canonical FK dynamics, not assumed again.
-/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology
open FKEnhancement

noncomputable section

/-- Actual finite lower closed-cutset comparison above an arbitrary
coordinatewise minorant of the exact enhanced rates. -/
theorem cutset_lower_comparison_of_rate_bound
    (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) (hne : Nonempty G.Edge)
    (r : G.Edge → unitInterval)
    (hr : r ≤ lowerEnhancedRates (graphConnectionEvent G ξ) enhanced
      (actualLower_le_prime hq hp0 hp1 hq1)) :
    StochasticallyDominates (bernoulliProduct r) (G.fkMeasure hq hp1.le ξ) := by
  exact (finite_bernoulliProduct_mono hr).trans
    (graphConnectionEvent_lower_comparison_canonical G hq hp0 hp1 hq1 ξ enhanced hne)

/-- Actual finite upper closed-cutset comparison below an arbitrary
coordinatewise majorant of the exact enhanced rates. -/
theorem cutset_upper_comparison_of_rate_bound
    (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) (hne : Nonempty G.Edge)
    (r : G.Edge → unitInterval)
    (hr : upperEnhancedRates (graphConnectionEvent G ξ) enhanced
      (actualPrime_le_lower hq hp0 hp1 hq1) ≤ r) :
    StochasticallyDominates (G.fkMeasure hq hp1.le ξ) (bernoulliProduct r) := by
  exact (graphConnectionEvent_upper_comparison_canonical G hq hp0 hp1 hq1 ξ enhanced hne).trans
    (finite_bernoulliProduct_mono hr)

/-- DLR lower closed-cutset comparison.  `enhanced` and its exact enhancement
sizes may depend on the box and on the actual exterior-induced boundary
setoid.  No exterior marginal product law and no finite stochastic-comparison
hypothesis is required. -/
theorem dlr_lower_cutset_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, (exh.box n).Exterior → Set (exh.box n).edges)
    (hr : ∀ n η, (fun e : (exh.box n).edges => rs n e.1) ≤
      lowerEnhancedRates (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
        (enhanced n η) (actualLower_le_prime hq hp0 hp1 hq1)) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) := by
  apply FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_eventually_lower
    exh Φ hq hp1.le hμ rs r hrs
  intro n η
  exact cutset_lower_comparison_of_rate_bound (exh.box n).graph hq hp0 hp1 hq1
    (Φ.partition n η) (enhanced n η) (hne n) _ (hr n η)

/-- DLR upper closed-cutset comparison for `q > 1`, again with arbitrary
exterior-induced boundary setoids and arbitrary DLR exterior marginal. -/
theorem dlr_upper_cutset_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, (exh.box n).Exterior → Set (exh.box n).edges)
    (hr : ∀ n η, upperEnhancedRates
        (graphConnectionEvent (exh.box n).graph (Φ.partition n η)) (enhanced n η)
        (actualPrime_le_lower hq hp0 hp1 hq1) ≤
      (fun e : (exh.box n).edges => rs n e.1)) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ := by
  apply FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_eventually_upper
    exh Φ hq hp1.le hμ rs r hrs
  intro n η
  exact cutset_upper_comparison_of_rate_bound (exh.box n).graph hq hp0 hp1 hq1
    (Φ.partition n η) (enhanced n η) (hne n) _ (hr n η)

/-- Exact normalized rates of the canonical upper open-path comparison. -/
noncomputable def pathUpperRates (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (enhanced : Finset G.Edge) (Γ : G.Edge → Set (Finset G.Edge)) : G.Edge → unitInterval := by
  let hp : (p : ℝ) ∈ Icc 0 1 := ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩
  let hp' : FK.prime (q : ℝ) (p : ℝ) ∈ Icc 0 1 :=
    FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le)
  let h : (p : ℝ) ≤ FK.prime (q : ℝ) (p : ℝ) :=
    (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
      (by exact_mod_cast hq) (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) (by exact_mod_cast hq1)).le
  exact FKLimit.unitParameters
    (OpenPath.upperProductParameters enhanced (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) hp Γ)
    (fun e => (OpenPath.upperProductParameters_mem_Icc enhanced hp hp'.2 h Γ e).1)
    (fun e => (OpenPath.upperProductParameters_mem_Icc enhanced hp hp'.2 h Γ e).2)

/-- Exact normalized rates of the canonical lower open-path comparison. -/
noncomputable def pathLowerRates (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (enhanced : Finset G.Edge) (Γ : G.Edge → Set (Finset G.Edge)) : G.Edge → unitInterval := by
  let hp : (p : ℝ) ≤ 1 := by exact_mod_cast hp1.le
  let hp' : FK.prime (q : ℝ) (p : ℝ) ∈ Icc 0 1 :=
    FK.prime_mem_Icc (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
      (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le)
  let h : FK.prime (q : ℝ) (p : ℝ) ≤ (p : ℝ) :=
    (FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
      (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
      (by exact_mod_cast hp0) (by exact_mod_cast hp1) (by exact_mod_cast hq1)).le
  exact FKLimit.unitParameters
    (OpenPath.lowerProductParameters enhanced (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) hp' Γ)
    (fun e => (OpenPath.lowerProductParameters_mem_Icc enhanced hp hp' h Γ e).1)
    (fun e => (OpenPath.lowerProductParameters_mem_Icc enhanced hp hp' h Γ e).2)

/-- Actual finite upper open-path comparison below a coordinatewise majorant. -/
theorem path_upper_comparison_of_rate_bound
    (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (hΓ : ∀ e ∈ enhanced, OpenPath.AuxiliaryPaths enhanced e (Γ e))
    (hΓK : ∀ e ∈ enhanced, ∀ {ω : OpenPath.Config G.Edge},
      OpenPath.SomePathOpen (Γ e) ω → graphConnectionEvent G ξ e (OpenPath.configToBool ω))
    (hne : Nonempty G.Edge) (r : G.Edge → unitInterval)
    (hr : pathUpperRates G hq hp0 hp1 hq1 enhanced Γ ≤ r) :
    StochasticallyDominates (G.fkMeasure hq hp1.le ξ) (bernoulliProduct r) := by
  let hp : (p : ℝ) ∈ Icc 0 1 := ⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩
  let hp' : FK.prime (q : ℝ) (p : ℝ) ∈ Icc 0 1 :=
    FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le)
  let h : (p : ℝ) ≤ FK.prime (q : ℝ) (p : ℝ) :=
    (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
      (by exact_mod_cast hq) (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) (by exact_mod_cast hq1)).le
  have hcomp := FKEnhancement.CanonicalDynamics.graphConnectionEvent_upper_path_comparison_canonical
    G hq hp0 hp1 hq1 ξ enhanced Γ hΓ hΓK hne
  rw [upperProductPMF_map_configToBool_toMeasure enhanced
    (⟨p.coe_nonneg, by exact_mod_cast hp1.le⟩ : (p : ℝ) ∈ Icc 0 1)
    (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity)
      (by exact_mod_cast hp1.le)).2
    (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
      (by exact_mod_cast hq) (by exact_mod_cast hp0)
      (by exact_mod_cast hp1) (by exact_mod_cast hq1)).le Γ] at hcomp
  exact hcomp.trans (finite_bernoulliProduct_mono hr)

/-- Actual finite lower open-path comparison above a coordinatewise minorant. -/
theorem path_lower_comparison_of_rate_bound
    (G : FK.Finite.LabelledMultigraph) {q p : NNReal}
    (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (hΓ : OpenPath.HasEnhancingPaths enhanced Γ)
    (hΓK : ∀ e ∈ enhanced, ∀ {ω : OpenPath.Config G.Edge},
      OpenPath.SomePathOpen (Γ e) ω →
        FK.Finite.Conditional.endpointsConnectedWithout G ξ e (OpenPath.configToBool ω))
    (hne : Nonempty G.Edge) (r : G.Edge → unitInterval)
    (hr : r ≤ pathLowerRates G hp0 hp1 hq1 enhanced Γ) :
    StochasticallyDominates (bernoulliProduct r)
      (G.fkMeasure (lt_trans zero_lt_one hq1 : 0 < q) hp1.le ξ) := by
  let hp : (p : ℝ) ≤ 1 := by exact_mod_cast hp1.le
  let hp' : FK.prime (q : ℝ) (p : ℝ) ∈ Icc 0 1 :=
    FK.prime_mem_Icc (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
      (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le)
  let h : FK.prime (q : ℝ) (p : ℝ) ≤ (p : ℝ) :=
    (FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
      (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
      (by exact_mod_cast hp0) (by exact_mod_cast hp1) (by exact_mod_cast hq1)).le
  have hcomp := OpenPath.LowerPathCoupling.lower_path_comparison_of_one_lt_q_canonical
    G hq1 hp0 hp1 ξ enhanced Γ hΓ hΓK hne
  erw [lowerProductPMF_map_configToBool_toMeasure enhanced hp hp' h Γ] at hcomp
  exact (finite_bernoulliProduct_mono hr).trans hcomp

/-- DLR upper open-path comparison from actual path semantics. -/
theorem dlr_upper_path_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, (exh.box n).Exterior → Finset (exh.box n).edges)
    (Γ : ∀ n η, (exh.box n).edges → Set (Finset (exh.box n).edges))
    (hΓ : ∀ n η e, e ∈ enhanced n η → OpenPath.AuxiliaryPaths (enhanced n η) e (Γ n η e))
    (hΓK : ∀ n η e, e ∈ enhanced n η → ∀ {ω : OpenPath.Config (exh.box n).edges},
      OpenPath.SomePathOpen (Γ n η e) ω →
        graphConnectionEvent (exh.box n).graph (Φ.partition n η) e (OpenPath.configToBool ω))
    (hr : ∀ n η, pathUpperRates (exh.box n).graph hq hp0 hp1 hq1 (enhanced n η) (Γ n η) ≤
      (fun e : (exh.box n).edges => rs n e.1)) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ := by
  apply FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_eventually_upper
    exh Φ hq hp1.le hμ rs r hrs
  intro n η
  exact path_upper_comparison_of_rate_bound (exh.box n).graph hq hp0 hp1 hq1
    (Φ.partition n η) (enhanced n η) (Γ n η) (hΓ n η) (hΓK n η) (hne n) _ (hr n η)

/-- DLR lower open-path comparison from actual path semantics. -/
theorem dlr_lower_path_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ (lt_trans zero_lt_one hq1) hp1.le)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, (exh.box n).Exterior → Finset (exh.box n).edges)
    (Γ : ∀ n η, (exh.box n).edges → Set (Finset (exh.box n).edges))
    (hΓ : ∀ n η, @OpenPath.HasEnhancingPaths _ (Classical.decEq _) (enhanced n η) (Γ n η))
    (hΓK : ∀ n η e, e ∈ enhanced n η → ∀ {ω : OpenPath.Config (exh.box n).edges},
      OpenPath.SomePathOpen (Γ n η e) ω →
        FK.Finite.Conditional.endpointsConnectedWithout (exh.box n).graph (Φ.partition n η) e
          (OpenPath.configToBool ω))
    (hr : ∀ n η, (fun e : (exh.box n).edges => rs n e.1) ≤
      pathLowerRates (exh.box n).graph hp0 hp1 hq1 (enhanced n η) (Γ n η)) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) := by
  apply FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_eventually_lower
    exh Φ (lt_trans zero_lt_one hq1) hp1.le hμ rs r hrs
  intro n η
  exact path_lower_comparison_of_rate_bound (exh.box n).graph hp0 hp1 hq1
    (Φ.partition n η) (enhanced n η) (Γ n η) (hΓ n η) (hΓK n η) (hne n) _ (hr n η)

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.cutset_lower_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.cutset_upper_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.dlr_lower_cutset_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.dlr_upper_cutset_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.path_upper_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.path_lower_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.dlr_upper_path_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.dlr_lower_path_comparison_of_rate_bound
