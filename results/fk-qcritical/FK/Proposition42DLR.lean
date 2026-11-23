import FK.ActualDLRComparisons
import FK.DeviceBounds

/-! Exact active-device specializations of the actual DLR comparison theorems. -/

namespace FK.EnhancedTransport

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal unitInterval Classical BigOperators Topology
open FKEnhancement

noncomputable section

/-- Forget the graph structure of a box exhaustion, retaining its edge sets. -/
def edgeExhaustionOfBox {E : Type*} (exh : FK.InfiniteVolume.BoxExhaustion E) :
    FKLimit.EdgeExhaustion E where
  box n := (exh.box n).edges
  monotone := exh.monotone
  covers := exh.covers

/-- The global active edge set, considered inside one finite box. -/
def activeWithinFinset {E : Type*} (B : FK.InfiniteVolume.FiniteBox E)
    (A : Finset E) : Finset B.edges :=
  Finset.univ.filter (fun e => e.1 ∈ A)

@[simp] lemma mem_activeWithinFinset {E : Type*} {B : FK.InfiniteVolume.FiniteBox E}
    {A : Finset E} {e : B.edges} : e ∈ activeWithinFinset B A ↔ e.1 ∈ A := by
  simp [activeWithinFinset]

/-- The `p < p'`, lower star-device DLR comparison.  The remaining inputs
are finite closed-cutset devices of cardinality at most `Delta - 1`; no
stochastic-comparison, product-exterior, or enhancement-bound hypothesis is
assumed. -/
theorem lt_dlr_lower_of_active_star_devices
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (hp : (p : ℝ) ∈ Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ))
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (Sstar : Set E) (Dstar : E → Finset E) (starAdmissible : ℕ → E → Prop)
    (Delta : ℕ) (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (hdevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Sstar Dstar starAdmissible n →
      ∃ χ : Finset (exh.box n).edges,
        (χ : Set (exh.box n).edges) ∈ CutsetFamily
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges (edgeExhaustionOfBox exh)
            Sstar Dstar starAdmissible n)) : Set (exh.box n).edges) e ∧
        χ.card ≤ Delta - 1) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct
      (FKLimit.ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) := by
  let edgeExh := edgeExhaustionOfBox exh
  let base : E → unitInterval := FKLimit.unitParameters (fun _ : E => (p : ℝ))
    (fun _ => hp.1.le) (fun _ => hp.2.le)
  let step : E → unitInterval := FKLimit.ltLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar
  let rs : ℕ → E → unitInterval := fun n =>
    FKLimit.activeParameters edgeExh Sstar Dstar starAdmissible base step n
  have hD : ∀ e ∈ Sstar, e ∈ Dstar e := fun e he => (hStar e he).1
  have hsel : FKLimit.selectParameters base step Sstar = step := by
    dsimp only [base, step]
    apply FKLimit.selectParameters_raisedOn_unit
  have hmain := dlr_lower_cutset_comparison_of_rate_bound exh Φ hq hp0 hp1 hq1 hμ rs
    (FKLimit.selectParameters base step Sstar)
    (fun A T hAT => FKLimit.eventually_bernoulliProduct_active edgeExh Sstar Dstar
      starAdmissible base step hD hstarAdm A T hAT) hne
    (fun n _ => (↑(activeWithinFinset (exh.box n)
      (FKLimit.activeEdges edgeExh Sstar Dstar starAdmissible n)) : Set (exh.box n).edges))
    (by
      intro n η e
      by_cases he : e.1 ∈ FKLimit.activeEdges edgeExh Sstar Dstar starAdmissible n
      · obtain ⟨χ, hχ, hcard⟩ := hdevices n η e he
        have heps := cutsetEpsilon_ge_pow_of_card_le
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
            starAdmissible n)) : Set (exh.box n).edges)
          (actualLowerParameter p hp1.le) (actualPrimeParameter hq hp1.le) e χ (Delta - 1)
          hχ hcard
        have heps' : FKLimit.starEpsilon (p : ℝ) (q : ℝ) Delta ≤
            cutsetEpsilon (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
              (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
                starAdmissible n)) : Set (exh.box n).edges)
              (actualLowerParameter p hp1.le) (actualPrimeParameter hq hp1.le) e := by
          simpa only [FKLimit.starEpsilon, FKLimit.fkSingletonParameter, FK.prime,
            actualLowerParameter, actualPrimeParameter] using heps
        have hSstar : e.1 ∈ Sstar := FKLimit.activeEdges_subset he
        have hel : e ∈ activeWithinFinset (exh.box n)
          (FKLimit.activeEdges edgeExh Sstar Dstar starAdmissible n) := by simpa using he
        have hleft : (rs n e.1 : ℝ) = (p : ℝ) + FKLimit.starEpsilon (p : ℝ) (q : ℝ) Delta := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, step,
            FKLimit.ltLowerParameters, FKLimit.raisedOn, hSstar]
        have hright : (lowerEnhancedRates
            (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
            (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
              starAdmissible n)) : Set (exh.box n).edges)
            (actualLower_le_prime hq hp0 hp1 hq1) e : ℝ) =
            (p : ℝ) + cutsetEpsilon (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
              (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
                starAdmissible n)) : Set (exh.box n).edges)
              (actualLowerParameter p hp1.le) (actualPrimeParameter hq hp1.le) e := by
          simp [lowerEnhancedRates, lowerEnhancedRate, hel, actualLowerParameter]
        change (rs n e.1 : ℝ) ≤ (lowerEnhancedRates
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
            starAdmissible n)) : Set (exh.box n).edges)
          (actualLower_le_prime hq hp0 hp1 hq1) e : ℝ)
        rw [hleft, hright]
        exact add_le_add_right heps' (p : ℝ)
      · have hleft : (rs n e.1 : ℝ) = (p : ℝ) := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, base]
        have hright : (lowerEnhancedRates
            (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
            (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
              starAdmissible n)) : Set (exh.box n).edges)
            (actualLower_le_prime hq hp0 hp1 hq1) e : ℝ) = (p : ℝ) := by
          simp [lowerEnhancedRates, lowerEnhancedRate, mem_activeWithinFinset, he,
            actualLowerParameter]
        change (rs n e.1 : ℝ) ≤ (lowerEnhancedRates
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
            starAdmissible n)) : Set (exh.box n).edges)
          (actualLower_le_prime hq hp0 hp1 hq1) e : ℝ)
        rw [hleft, hright])
  rw [hsel] at hmain
  exact hmain

/-- The `p < p'`, upper cycle-device DLR comparison. -/
theorem lt_dlr_upper_of_active_cycle_devices
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1)
    (hp : (p : ℝ) ∈ Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : (p : ℝ) < FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ))
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (Scycle : Set E) (Dcycle : E → Finset E) (cycleAdmissible : ℕ → E → Prop)
    (L : ℕ) (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    (hne : ∀ n, Nonempty (exh.box n).edges)
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
    (hdevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Scycle Dcycle cycleAdmissible n →
      ∃ γ : Finset (exh.box n).edges, γ ∈ Γ n η e ∧ γ.card ≤ L - 1) :
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct
        (FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) μ := by
  let edgeExh := edgeExhaustionOfBox exh
  let prime : ℝ := FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ)
  let base : E → unitInterval := FKLimit.unitParameters (fun _ : E => prime)
    (fun _ => (FKLimit.fkSingletonParameter_pos hp hqR).le)
    (fun _ => (FKLimit.fkSingletonParameter_lt_one hp hqR).le)
  let step : E → unitInterval := FKLimit.ltUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle
  let rs : ℕ → E → unitInterval := fun n =>
    FKLimit.activeParameters edgeExh Scycle Dcycle cycleAdmissible base step n
  have hD : ∀ e ∈ Scycle, e ∈ Dcycle e := fun e he => (hCycle e he).1
  have hsel : FKLimit.selectParameters base step Scycle = step := by
    dsimp only [base, step]
    apply FKLimit.selectParameters_loweredOn_unit
  have hmain := dlr_upper_path_comparison_of_rate_bound exh Φ hq hp0 hp1 hq1 hμ rs
    (FKLimit.selectParameters base step Scycle)
    (fun A T hAT => FKLimit.eventually_bernoulliProduct_active edgeExh Scycle Dcycle
      cycleAdmissible base step hD hcycleAdm A T hAT) hne
    (fun n _ => activeWithinFinset (exh.box n)
      (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) Γ hΓ hΓK
    (by
      intro n η e
      by_cases he : e.1 ∈ FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n
      · obtain ⟨γ, hγ, hcard⟩ := hdevices n η e he
        have hpReal : (p : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
        have hprob := @pathEventProbability_ge_pow_of_card_le
          (exh.box n).edges _ (Classical.decEq _) (p : ℝ) hpReal (Γ n η e)
          γ (L - 1) hγ hcard
        have heps' : FKLimit.cycleEpsilon (p : ℝ) (q : ℝ) L ≤
            @OpenPath.pathBonus (exh.box n).edges _ (Classical.decEq _)
              (p : ℝ) (FK.prime (q : ℝ) (p : ℝ) - (p : ℝ)) hpReal (Γ n η e) := by
          unfold FKLimit.cycleEpsilon OpenPath.pathBonus
          rw [min_eq_left hpp.le, abs_of_pos (sub_pos.mpr hpp)]
          exact mul_le_mul_of_nonneg_left hprob (sub_nonneg.mpr hpp.le)
        have hS : e.1 ∈ Scycle := FKLimit.activeEdges_subset he
        have hel : e ∈ activeWithinFinset (exh.box n)
          (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n) := by simpa using he
        have hleft : (rs n e.1 : ℝ) =
            FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) -
              FKLimit.cycleEpsilon (p : ℝ) (q : ℝ) L := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, step,
            FKLimit.ltUpperParameters, FKLimit.loweredOn, hS]
        have hright : (pathUpperRates (exh.box n).graph hq hp0 hp1 hq1
            (activeWithinFinset (exh.box n)
              (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ) =
            FK.prime (q : ℝ) (p : ℝ) -
              @OpenPath.pathBonus (exh.box n).edges _ (Classical.decEq _)
                (p : ℝ) (FK.prime (q : ℝ) (p : ℝ) - (p : ℝ)) hpReal (Γ n η e) := by
          simp [pathUpperRates, OpenPath.upperProductParameters, OpenPath.enhancedUpper,
            OpenPath.pathBonus, hel, hpReal]
        change (pathUpperRates (exh.box n).graph hq hp0 hp1 hq1
          (activeWithinFinset (exh.box n)
            (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ) ≤
          (rs n e.1 : ℝ)
        rw [hleft, hright]
        exact sub_le_sub_left heps' _
      · have hleft : (rs n e.1 : ℝ) = FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, base, prime]
        have hright : (pathUpperRates (exh.box n).graph hq hp0 hp1 hq1
            (activeWithinFinset (exh.box n)
              (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ) =
            FK.prime (q : ℝ) (p : ℝ) := by
          simp [pathUpperRates, OpenPath.upperProductParameters, mem_activeWithinFinset, he]
        change (pathUpperRates (exh.box n).graph hq hp0 hp1 hq1
          (activeWithinFinset (exh.box n)
            (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ) ≤
          (rs n e.1 : ℝ)
        rw [hleft, hright]
        exact le_rfl)
  rw [hsel] at hmain
  exact hmain

/-- The `p' < p`, lower cycle-device DLR comparison. -/
theorem gt_dlr_lower_of_active_cycle_devices
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (hp : (p : ℝ) ∈ Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ))
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (Scycle : Set E) (Dcycle : E → Finset E) (cycleAdmissible : ℕ → E → Prop)
    (L : ℕ) (hCycle : FKLimit.IsSeparatedDeviceFamily Scycle Dcycle)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    (hne : ∀ n, Nonempty (exh.box n).edges)
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
    (hdevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Scycle Dcycle cycleAdmissible n →
      ∃ γ : Finset (exh.box n).edges, γ ∈ Γ n η e ∧ γ.card ≤ L - 1) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct
      (FKLimit.gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle)) := by
  let edgeExh := edgeExhaustionOfBox exh
  let prime : ℝ := FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ)
  let base : E → unitInterval := FKLimit.unitParameters (fun _ : E => prime)
    (fun _ => (FKLimit.fkSingletonParameter_pos hp hqR).le)
    (fun _ => (FKLimit.fkSingletonParameter_lt_one hp hqR).le)
  let step : E → unitInterval := FKLimit.gtLowerParameters (p : ℝ) (q : ℝ) hp hqR hpp L Scycle
  let rs : ℕ → E → unitInterval := fun n =>
    FKLimit.activeParameters edgeExh Scycle Dcycle cycleAdmissible base step n
  have hD : ∀ e ∈ Scycle, e ∈ Dcycle e := fun e he => (hCycle e he).1
  have hsel : FKLimit.selectParameters base step Scycle = step := by
    dsimp only [base, step]
    apply FKLimit.selectParameters_raisedOn_unit
  have hmain := dlr_lower_path_comparison_of_rate_bound exh Φ hp0 hp1 hq1 hμ rs
    (FKLimit.selectParameters base step Scycle)
    (fun A T hAT => FKLimit.eventually_bernoulliProduct_active edgeExh Scycle Dcycle
      cycleAdmissible base step hD hcycleAdm A T hAT) hne
    (fun n _ => activeWithinFinset (exh.box n)
      (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) Γ
    (fun n η => @OpenPath.HasEnhancingPaths.mk _ (Classical.decEq _)
      (activeWithinFinset (exh.box n)
        (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) (hΓ n η) (by
        intro e he
        obtain ⟨γ, hγ, _⟩ := hdevices n η e (by simpa using he)
        exact ⟨γ, hγ⟩)) hΓK
    (by
      intro n η e
      by_cases he : e.1 ∈ FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n
      · obtain ⟨γ, hγ, hcard⟩ := hdevices n η e he
        let hpReal : FK.prime (q : ℝ) (p : ℝ) ∈ Icc (0 : ℝ) 1 :=
          FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp1.le)
        have hprob := @pathEventProbability_ge_pow_of_card_le
          (exh.box n).edges _ (Classical.decEq _) (FK.prime (q : ℝ) (p : ℝ)) hpReal
          (Γ n η e) γ (L - 1) hγ hcard
        have heps' : FKLimit.cycleEpsilon (p : ℝ) (q : ℝ) L ≤
            @OpenPath.pathBonus (exh.box n).edges _ (Classical.decEq _)
              (FK.prime (q : ℝ) (p : ℝ)) ((p : ℝ) - FK.prime (q : ℝ) (p : ℝ)) hpReal
              (Γ n η e) := by
          unfold FKLimit.cycleEpsilon OpenPath.pathBonus
          rw [min_eq_right hpp.le]
          have habs : |FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) - (p : ℝ)| =
              (p : ℝ) - FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) := by
            rw [show FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) - (p : ℝ) =
              -((p : ℝ) - FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ)) by ring,
              abs_neg, abs_of_pos (sub_pos.mpr hpp)]
          rw [habs]
          exact mul_le_mul_of_nonneg_left hprob (sub_nonneg.mpr hpp.le)
        have hS : e.1 ∈ Scycle := FKLimit.activeEdges_subset he
        have hel : e ∈ activeWithinFinset (exh.box n)
          (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n) := by simpa using he
        have hleft : (rs n e.1 : ℝ) =
            FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) +
              FKLimit.cycleEpsilon (p : ℝ) (q : ℝ) L := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, step,
            FKLimit.gtLowerParameters, FKLimit.raisedOn, hS]
        have hright : (pathLowerRates (exh.box n).graph hp0 hp1 hq1
            (activeWithinFinset (exh.box n)
              (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ) =
            FK.prime (q : ℝ) (p : ℝ) +
              @OpenPath.pathBonus (exh.box n).edges _ (Classical.decEq _)
                (FK.prime (q : ℝ) (p : ℝ)) ((p : ℝ) - FK.prime (q : ℝ) (p : ℝ)) hpReal
                (Γ n η e) := by
          simp [pathLowerRates, OpenPath.lowerProductParameters, OpenPath.enhancedLower,
            OpenPath.pathBonus, hel, hpReal]
        change (rs n e.1 : ℝ) ≤ (pathLowerRates (exh.box n).graph hp0 hp1 hq1
          (activeWithinFinset (exh.box n)
            (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ)
        rw [hleft, hright]
        exact add_le_add_right heps' _
      · have hleft : (rs n e.1 : ℝ) = FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, base, prime]
        have hright : (pathLowerRates (exh.box n).graph hp0 hp1 hq1
            (activeWithinFinset (exh.box n)
              (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ) =
            FK.prime (q : ℝ) (p : ℝ) := by
          simp [pathLowerRates, OpenPath.lowerProductParameters, mem_activeWithinFinset, he]
        change (rs n e.1 : ℝ) ≤ (pathLowerRates (exh.box n).graph hp0 hp1 hq1
          (activeWithinFinset (exh.box n)
            (FKLimit.activeEdges edgeExh Scycle Dcycle cycleAdmissible n)) (Γ n η) e : ℝ)
        rw [hleft, hright]
        exact le_rfl)
  rw [hsel] at hmain
  exact hmain

/-- The `p' < p`, upper star-device DLR comparison. -/
theorem gt_dlr_upper_of_active_star_devices
    {E : Type*} [Countable E] (exh : FK.InfiniteVolume.BoxExhaustion E)
    (Φ : FK.InfiniteVolume.BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q)
    (hp : (p : ℝ) ∈ Ioo 0 1) (hqR : 0 < (q : ℝ))
    (hpp : FKLimit.fkSingletonParameter (p : ℝ) (q : ℝ) < (p : ℝ))
    {μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration E)}
    (hμ : μ ∈ FK.InfiniteVolume.DLRMeasures exh Φ hq hp1.le)
    (Sstar : Set E) (Dstar : E → Finset E) (starAdmissible : ℕ → E → Prop)
    (Delta : ℕ) (hStar : FKLimit.IsSeparatedDeviceFamily Sstar Dstar)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hne : ∀ n, Nonempty (exh.box n).edges)
    (hdevices : ∀ n η e, e.1 ∈ FKLimit.activeEdges (edgeExhaustionOfBox exh)
        Sstar Dstar starAdmissible n →
      ∃ χ : Finset (exh.box n).edges,
        (χ : Set (exh.box n).edges) ∈ CutsetFamily
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges (edgeExhaustionOfBox exh)
            Sstar Dstar starAdmissible n)) : Set (exh.box n).edges) e ∧
        χ.card ≤ Delta - 1) :
    FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct
        (FKLimit.gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar)) μ := by
  let edgeExh := edgeExhaustionOfBox exh
  let base : E → unitInterval := FKLimit.unitParameters (fun _ : E => (p : ℝ))
    (fun _ => hp.1.le) (fun _ => hp.2.le)
  let step : E → unitInterval := FKLimit.gtUpperParameters (p : ℝ) (q : ℝ) hp hqR hpp Delta Sstar
  let rs : ℕ → E → unitInterval := fun n =>
    FKLimit.activeParameters edgeExh Sstar Dstar starAdmissible base step n
  have hD : ∀ e ∈ Sstar, e ∈ Dstar e := fun e he => (hStar e he).1
  have hsel : FKLimit.selectParameters base step Sstar = step := by
    dsimp only [base, step]
    apply FKLimit.selectParameters_loweredOn_unit
  have hmain := dlr_upper_cutset_comparison_of_rate_bound exh Φ hq hp0 hp1 hq1 hμ rs
    (FKLimit.selectParameters base step Sstar)
    (fun A T hAT => FKLimit.eventually_bernoulliProduct_active edgeExh Sstar Dstar
      starAdmissible base step hD hstarAdm A T hAT) hne
    (fun n _ => (↑(activeWithinFinset (exh.box n)
      (FKLimit.activeEdges edgeExh Sstar Dstar starAdmissible n)) : Set (exh.box n).edges))
    (by
      intro n η e
      by_cases he : e.1 ∈ FKLimit.activeEdges edgeExh Sstar Dstar starAdmissible n
      · obtain ⟨χ, hχ, hcard⟩ := hdevices n η e he
        have heps := cutsetEpsilon_ge_pow_of_card_le
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
            starAdmissible n)) : Set (exh.box n).edges)
          (actualLowerParameter p hp1.le) (actualPrimeParameter hq hp1.le) e χ (Delta - 1)
          hχ hcard
        have heps' : FKLimit.starEpsilon (p : ℝ) (q : ℝ) Delta ≤
            cutsetEpsilon (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
              (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
                starAdmissible n)) : Set (exh.box n).edges)
              (actualLowerParameter p hp1.le) (actualPrimeParameter hq hp1.le) e := by
          simpa only [FKLimit.starEpsilon, FKLimit.fkSingletonParameter, FK.prime,
            actualLowerParameter, actualPrimeParameter] using heps
        have hSstar : e.1 ∈ Sstar := FKLimit.activeEdges_subset he
        have hel : e ∈ activeWithinFinset (exh.box n)
          (FKLimit.activeEdges edgeExh Sstar Dstar starAdmissible n) := by simpa using he
        have hleft : (rs n e.1 : ℝ) = (p : ℝ) - FKLimit.starEpsilon (p : ℝ) (q : ℝ) Delta := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, step,
            FKLimit.gtUpperParameters, FKLimit.loweredOn, hSstar]
        have hright : (upperEnhancedRates
            (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
            (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
              starAdmissible n)) : Set (exh.box n).edges)
            (actualPrime_le_lower hq hp0 hp1 hq1) e : ℝ) =
            (p : ℝ) - cutsetEpsilon (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
              (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
                starAdmissible n)) : Set (exh.box n).edges)
              (actualLowerParameter p hp1.le) (actualPrimeParameter hq hp1.le) e := by
          simp [upperEnhancedRates, upperEnhancedRate, hel, actualLowerParameter]
        change (upperEnhancedRates
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
            starAdmissible n)) : Set (exh.box n).edges)
          (actualPrime_le_lower hq hp0 hp1 hq1) e : ℝ) ≤ (rs n e.1 : ℝ)
        rw [hleft, hright]
        exact sub_le_sub_left heps' (p : ℝ)
      · have hleft : (rs n e.1 : ℝ) = (p : ℝ) := by
          simp [rs, FKLimit.activeParameters, FKLimit.selectParameters, he, base]
        have hright : (upperEnhancedRates
            (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
            (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
              starAdmissible n)) : Set (exh.box n).edges)
            (actualPrime_le_lower hq hp0 hp1 hq1) e : ℝ) = (p : ℝ) := by
          simp [upperEnhancedRates, upperEnhancedRate, mem_activeWithinFinset, he,
            actualLowerParameter]
        change (upperEnhancedRates
          (graphConnectionEvent (exh.box n).graph (Φ.partition n η))
          (↑(activeWithinFinset (exh.box n) (FKLimit.activeEdges edgeExh Sstar Dstar
            starAdmissible n)) : Set (exh.box n).edges)
          (actualPrime_le_lower hq hp0 hp1 hq1) e : ℝ) ≤ (rs n e.1 : ℝ)
        rw [hleft, hright])
  rw [hsel] at hmain
  exact hmain

end

end FK.EnhancedTransport

#print axioms FK.EnhancedTransport.lt_dlr_lower_of_active_star_devices
#print axioms FK.EnhancedTransport.lt_dlr_upper_of_active_cycle_devices
#print axioms FK.EnhancedTransport.gt_dlr_lower_of_active_cycle_devices
#print axioms FK.EnhancedTransport.gt_dlr_upper_of_active_star_devices
