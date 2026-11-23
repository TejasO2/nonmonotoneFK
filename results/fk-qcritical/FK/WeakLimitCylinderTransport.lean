import FK.ActualDLRComparisons

/-! Box-local enhanced comparisons transport to FK weak-limit classes. -/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal unitInterval Classical BigOperators
open FKEnhancement FK.InfiniteVolume

noncomputable section

/-- Interior lower comparisons pass to an FK weak limit on every cylinder,
without comparing exterior laws. -/
theorem cylinderDominates_of_isFKLimit_eventually_lower
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))
      ((exh.box n).graph.fkMeasure hq hp (α n))) :
    FKLimit.CylinderDominates μ (FKLimit.bernoulliProduct r) := by
  intro A S hdep hAupper
  have hlim : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp (α n) A) atTop
      (𝓝 (μ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hdep.isClopen
  apply ge_of_tendsto hlim
  filter_upwards [exh.eventually_subset S, hrs A S hdep] with n hnS hnr
  rw [← hnr]
  exact (exh.box n).apply_le_finiteVolumeLaw_local_lower hq hp (α n) (rs n)
    (hlocal n) hdep.measurableSet hAupper (hdep.mono hnS)

/-- Interior upper comparisons pass to an FK weak limit on every cylinder. -/
theorem cylinderDominates_of_isFKLimit_eventually_upper
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (α n))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))) :
    FKLimit.CylinderDominates (FKLimit.bernoulliProduct r) μ := by
  intro A S hdep hAupper
  have hlim : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp (α n) A) atTop
      (𝓝 (μ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hdep.isClopen
  apply le_of_tendsto hlim
  filter_upwards [exh.eventually_subset S, hrs A S hdep] with n hnS hnr
  rw [← hnr]
  exact (exh.box n).le_apply_finiteVolumeLaw_local_upper hq hp (α n) (rs n)
    (hlocal n) hdep.measurableSet hAupper (hdep.mono hnS)

/-- Full lower comparison for an FK weak limit. -/
theorem stochasticallyDominates_of_isFKLimit_eventually_lower
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))
      ((exh.box n).graph.fkMeasure hq hp (α n))) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) :=
  FKLimit.stochasticallyDominates_of_cylinderDominates
    (cylinderDominates_of_isFKLimit_eventually_lower exh hq hp α hμ rs r hrs hlocal)

/-- Full upper comparison for an FK weak limit. -/
theorem stochasticallyDominates_of_isFKLimit_eventually_upper
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (α n))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ :=
  FKLimit.stochasticallyDominates_of_cylinderDominates
    (cylinderDominates_of_isFKLimit_eventually_upper exh hq hp α hμ rs r hrs hlocal)

/-- Actual cutset lower comparison for an FK weak limit. -/
theorem fkLimit_lower_cutset_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp1.le α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, Set (exh.box n).edges)
    (hr : ∀ n, (fun e : (exh.box n).edges => rs n e.1) ≤
      lowerEnhancedRates (graphConnectionEvent (exh.box n).graph (α n)) (enhanced n)
        (actualLower_le_prime hq hp0 hp1 hq1)) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) := by
  apply stochasticallyDominates_of_isFKLimit_eventually_lower exh hq hp1.le α hμ rs r hrs
  intro n
  exact cutset_lower_comparison_of_rate_bound (exh.box n).graph hq hp0 hp1 hq1
    (α n) (enhanced n) (hne n) _ (hr n)

/-- Actual cutset upper comparison for an FK weak limit. -/
theorem fkLimit_upper_cutset_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp1.le α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, Set (exh.box n).edges)
    (hr : ∀ n, upperEnhancedRates (graphConnectionEvent (exh.box n).graph (α n))
        (enhanced n) (actualPrime_le_lower hq hp0 hp1 hq1) ≤
      (fun e : (exh.box n).edges => rs n e.1)) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ := by
  apply stochasticallyDominates_of_isFKLimit_eventually_upper exh hq hp1.le α hμ rs r hrs
  intro n
  exact cutset_upper_comparison_of_rate_bound (exh.box n).graph hq hp0 hp1 hq1
    (α n) (enhanced n) (hne n) _ (hr n)

/-- Actual path upper comparison for an FK weak limit. -/
theorem fkLimit_upper_path_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)} (hμ : IsFKLimit exh hq hp1.le α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, Finset (exh.box n).edges)
    (Γ : ∀ n, (exh.box n).edges → Set (Finset (exh.box n).edges))
    (hΓ : ∀ n e, e ∈ enhanced n → OpenPath.AuxiliaryPaths (enhanced n) e (Γ n e))
    (hΓK : ∀ n e, e ∈ enhanced n → ∀ {ω : OpenPath.Config (exh.box n).edges},
      OpenPath.SomePathOpen (Γ n e) ω → graphConnectionEvent (exh.box n).graph (α n) e
        (OpenPath.configToBool ω))
    (hr : ∀ n, pathUpperRates (exh.box n).graph hq hp0 hp1 hq1 (enhanced n) (Γ n) ≤
      (fun e : (exh.box n).edges => rs n e.1)) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ := by
  apply stochasticallyDominates_of_isFKLimit_eventually_upper exh hq hp1.le α hμ rs r hrs
  intro n
  exact path_upper_comparison_of_rate_bound (exh.box n).graph hq hp0 hp1 hq1
    (α n) (enhanced n) (Γ n) (hΓ n) (hΓK n) (hne n) _ (hr n)

/-- Actual path lower comparison for an FK weak limit. -/
theorem fkLimit_lower_path_comparison_of_rate_bound
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {q p : NNReal} (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : IsFKLimit exh (lt_trans zero_lt_one hq1 : 0 < q) hp1.le α μ)
    (rs : ℕ → E → unitInterval) (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (enhanced : ∀ n, Finset (exh.box n).edges)
    (Γ : ∀ n, (exh.box n).edges → Set (Finset (exh.box n).edges))
    (hΓ : ∀ n, @OpenPath.HasEnhancingPaths _ (Classical.decEq _) (enhanced n) (Γ n))
    (hΓK : ∀ n e, e ∈ enhanced n → ∀ {ω : OpenPath.Config (exh.box n).edges},
      OpenPath.SomePathOpen (Γ n e) ω →
        FK.Finite.Conditional.endpointsConnectedWithout (exh.box n).graph (α n) e
          (OpenPath.configToBool ω))
    (hr : ∀ n, (fun e : (exh.box n).edges => rs n e.1) ≤
      pathLowerRates (exh.box n).graph hp0 hp1 hq1 (enhanced n) (Γ n)) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) := by
  apply stochasticallyDominates_of_isFKLimit_eventually_lower exh
    (lt_trans zero_lt_one hq1) hp1.le α hμ rs r hrs
  intro n
  exact path_lower_comparison_of_rate_bound (exh.box n).graph hp0 hp1 hq1
    (α n) (enhanced n) (Γ n) (hΓ n) (hΓK n) (hne n) _ (hr n)

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.cylinderDominates_of_isFKLimit_eventually_lower
#print axioms FK.EnhancedTransport.cylinderDominates_of_isFKLimit_eventually_upper
#print axioms FK.EnhancedTransport.fkLimit_lower_cutset_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.fkLimit_upper_cutset_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.fkLimit_upper_path_comparison_of_rate_bound
#print axioms FK.EnhancedTransport.fkLimit_lower_path_comparison_of_rate_bound
