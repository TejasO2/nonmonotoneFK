import FK.AdaptiveTripleStopping

/-! # The synchronized finite FK triple and its exact good-intersection law -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set MeasureTheory
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling
open FK.RegionSeal FK.FinitePlane

local instance {E : Type*} [Fintype E] [DecidableEq E] : MeasurableSpace (Assignment E) := ⊤

/-- Positive-p version used in all constructions. -/
noncomputable def sideLawOf {G : LabelledMultigraph} (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) : Side → PMF G.Configuration
  | .left => G.fkPMF hq hp₁.le α
  | .right => G.fkPMF hq hp₁.le β
  | .upper => G.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le

lemma sideLawOf_pos {G : LabelledMultigraph} (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ∀ s ω, sideLawOf α β hq hp₀ hp₁ s ω ≠ 0 := by
  intro s
  cases s with
  | left => exact fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω
  | right => exact fun ω => fkPMF_ne_zero G hq hp₀ hp₁ β ω
  | upper =>
      intro ω
      exact bernoulliProductPMF_ne_zero G α (upperRateNN_pos hp₀)
        (upperRateNN_lt_one hq hp₀ hp₁) ω

/-- The full synchronized adaptive FK/FK/Bernoulli coupling. -/
noncomputable def fkAdaptiveTriple {G : LabelledMultigraph}
    (B : Set G.Vertex) (e₀ : G.Edge) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.OrderedTripleCoupling (G.fkPMF hq hp₁.le α) (G.fkPMF hq hp₁.le β)
      (G.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le) where
  dist := (runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
    blank blank blank (Fintype.card G.Edge)).map (fun z =>
      (decodeOption z.1, decodeOption z.2.1, decodeOption z.2.2))
  map_fst := by
    rw [PMF.map_comp]
    change (runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
      blank blank blank (Fintype.card G.Edge)).map (fun z => decodeOption z.1) = _
    have hcond := runTriple_map_side (μ := sideLawOf α β hq hp₀ hp₁)
      (hμ := sideLawOf_pos α β hq hp₀ hp₁) (fkTripleStep G α β hq hp₀ hp₁)
      (frontierNext B e₀)
      (fun s h₁ h₂ k e he => fkTripleStep_map_side G α β hq hp₀ hp₁ s h₁ h₂ k he)
      (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk) Side.left
      blank blank blank (by simp) (by simp) (Fintype.card G.Edge) (by simp)
    simpa only [pick, sideLawOf] using hcond.trans (cond_blank _ _)
  map_snd := by
    rw [PMF.map_comp]
    change (runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
      blank blank blank (Fintype.card G.Edge)).map (fun z => decodeOption z.2.1) = _
    have hcond := runTriple_map_side (μ := sideLawOf α β hq hp₀ hp₁)
      (hμ := sideLawOf_pos α β hq hp₀ hp₁) (fkTripleStep G α β hq hp₀ hp₁)
      (frontierNext B e₀)
      (fun s h₁ h₂ k e he => fkTripleStep_map_side G α β hq hp₀ hp₁ s h₁ h₂ k he)
      (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk) Side.right
      blank blank blank (by simp) (by simp) (Fintype.card G.Edge) (by simp)
    simpa only [pick, sideLawOf] using hcond.trans (cond_blank _ _)
  map_thd := by
    rw [PMF.map_comp]
    change (runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
      blank blank blank (Fintype.card G.Edge)).map (fun z => decodeOption z.2.2) = _
    have hcond := runTriple_map_side (μ := sideLawOf α β hq hp₀ hp₁)
      (hμ := sideLawOf_pos α β hq hp₀ hp₁) (fkTripleStep G α β hq hp₀ hp₁)
      (frontierNext B e₀)
      (fun s h₁ h₂ k e he => fkTripleStep_map_side G α β hq hp₀ hp₁ s h₁ h₂ k he)
      (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk) Side.upper
      blank blank blank (by simp) (by simp) (Fintype.card G.Edge) (by simp)
    simpa only [pick, sideLawOf] using hcond.trans (cond_blank _ _)
  rel_fst := by
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (runTriple_ordered (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
      (fun h₁ h₂ k e hh₁ hh₂ hke z hz => fkTripleStep_ordered G α β hq hp₀ hp₁
        h₁ h₂ k hh₁ hh₂ hke hz)
      (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
      blank blank blank (by simp) (by simp) (by simp [decodeOption, blank])
      (by simp [decodeOption, blank]) _ (by simp) hw).1
  rel_snd := by
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact (runTriple_ordered (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
      (fun h₁ h₂ k e hh₁ hh₂ hke z hz => fkTripleStep_ordered G α β hq hp₀ hp₁
        h₁ h₂ k hh₁ hh₂ hke hz)
      (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
      blank blank blank (by simp) (by simp) (by simp [decodeOption, blank])
      (by simp [decodeOption, blank]) _ (by simp) hw).2

/-- The synchronized full law factors through its stopped law. -/
theorem fkAdaptiveTriple_eq_stopped_bind {G : LabelledMultigraph}
    (B : Set G.Vertex) (e₀ : G.Edge) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (fkAdaptiveTriple B e₀ α β hq hp₀ hp₁).dist =
      ((runTripleUntil (fkTripleStep G α β hq hp₀ hp₁)
        (frontierNext B e₀) (frontierExhausted B) blank blank blank
        (Fintype.card G.Edge)).bind (fun z =>
          runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
            z.1 z.2.1 z.2.2 (unrevealed z.2.2).card)).map (fun z =>
              (decodeOption z.1, decodeOption z.2.1, decodeOption z.2.2)) := by
  change (runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
    blank blank blank (Fintype.card G.Edge)).map _ = _
  rw [runTriple_eq_runTripleUntil_bind (fkTripleStep G α β hq hp₀ hp₁)
    (frontierNext B e₀) (frontierExhausted B)
    (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
    blank blank blank (by simp) (by simp) _ (by simp)]

/-- **Exact good-intersection identity at the maximal explored cutset.**  For
any family of events on the unrevealed interiors, the resumed first-interior
and second-interior intersection masses agree. -/
theorem fkAdaptiveTriple_good_intersection {G : LabelledMultigraph}
    (B : Set G.Vertex) (e₀ : G.Edge) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : ∀ k : Assignment G.Edge, Set (RegionSeal.Internal G (interior B k) → Bool))
    (hwireα : ∀ k : Assignment G.Edge, ∀ v ∈ interior B k, ∀ w : G.Vertex, α.r v w → v = w)
    (hwireβ : ∀ k : Assignment G.Edge, ∀ v ∈ interior B k, ∀ w : G.Vertex, β.r v w → v = w) :
    let stopLaw := runTripleUntil (fkTripleStep G α β hq hp₀ hp₁)
      (frontierNext B e₀) (frontierExhausted B) blank blank blank (Fintype.card G.Edge)
    let resume := fun z : Assignment G.Edge × Assignment G.Edge × Assignment G.Edge =>
      runTriple (fkTripleStep G α β hq hp₀ hp₁) (frontierNext B e₀)
        z.1 z.2.1 z.2.2 (unrevealed z.2.2).card
    (stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))).toMeasure
      {x | restrictI G (interior B x.1.2.2) (decodeOption x.2.1) ∈ A x.1.2.2} =
    (stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))).toMeasure
      {x | restrictI G (interior B x.1.2.2) (decodeOption x.2.2.1) ∈ A x.1.2.2} := by
  intro stopLaw resume
  let L : Set ((Assignment G.Edge × Assignment G.Edge × Assignment G.Edge) ×
      (Assignment G.Edge × Assignment G.Edge × Assignment G.Edge)) :=
    {x | restrictI G (interior B x.1.2.2) (decodeOption x.2.1) ∈ A x.1.2.2}
  let R : Set ((Assignment G.Edge × Assignment G.Edge × Assignment G.Edge) ×
      (Assignment G.Edge × Assignment G.Edge × Assignment G.Edge)) :=
    {x | restrictI G (interior B x.1.2.2) (decodeOption x.2.2.1) ∈ A x.1.2.2}
  change (stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))).toMeasure L =
    (stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))).toMeasure R
  rw [PMF.toMeasure_bind_apply _ _ L MeasurableSet.of_discrete,
    PMF.toMeasure_bind_apply _ _ R MeasurableSet.of_discrete]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ stopLaw.support
  · have hi := runTripleUntil_frontier_invariants B e₀ (fkTripleStep G α β hq hp₀ hp₁)
      (fun h₁ h₂ k e hh₁ hh₂ hke w hw => fkTripleStep_ordered G α β hq hp₀ hp₁
        h₁ h₂ k hh₁ hh₂ hke hw) hz
    have hfree := runTripleUntil_free_interiors B e₀ α β hq hp₀ hp₁ hwireα hwireβ hz
    have hm (s : Side) :
        (resume z).map (fun w => decodeOption (pick s w.1 w.2.1 w.2.2)) =
          cond (sideLawOf α β hq hp₀ hp₁ s) (sideLawOf_pos α β hq hp₀ hp₁ s)
            (pick s z.1 z.2.1 z.2.2) := by
      exact runTriple_map_side (μ := sideLawOf α β hq hp₀ hp₁)
        (hμ := sideLawOf_pos α β hq hp₀ hp₁) (fkTripleStep G α β hq hp₀ hp₁)
        (frontierNext B e₀)
        (fun s h₁ h₂ k e he => fkTripleStep_map_side G α β hq hp₀ hp₁ s h₁ h₂ k he)
        (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk) s
        z.1 z.2.1 z.2.2 hi.1 hi.2.1 _ rfl
    have hmL := hm Side.left
    change (resume z).map (fun w => decodeOption w.1) = _ at hmL
    have hmL' : (resume z).map (fun w => decodeOption w.1) =
        cond (G.fkPMF hq hp₁.le α) (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω) z.1 := by
      simpa only [sideLawOf, pick] using hmL
    have hpushL : (resume z).map (fun w =>
        restrictI G (interior B z.2.2) (decodeOption w.1)) =
        (regionGraph G (interior B z.2.2)).fkPMF hq hp₁.le
          (regionGraph G (interior B z.2.2)).freeBoundary := by
      exact (PMF.map_comp (fun w : Assignment G.Edge × Assignment G.Edge × Assignment G.Edge =>
        decodeOption w.1) (resume z) (restrictI G (interior B z.2.2))).symm.trans
          ((congrArg (PMF.map (restrictI G (interior B z.2.2))) hmL').trans hfree.1)
    have hmR := hm Side.right
    change (resume z).map (fun w => decodeOption w.2.1) = _ at hmR
    have hmR' : (resume z).map (fun w => decodeOption w.2.1) =
        cond (G.fkPMF hq hp₁.le β) (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ β ω) z.2.1 := by
      simpa only [sideLawOf, pick] using hmR
    have hpushR : (resume z).map (fun w =>
        restrictI G (interior B z.2.2) (decodeOption w.2.1)) =
        (regionGraph G (interior B z.2.2)).fkPMF hq hp₁.le
          (regionGraph G (interior B z.2.2)).freeBoundary := by
      exact (PMF.map_comp (fun w : Assignment G.Edge × Assignment G.Edge × Assignment G.Edge =>
        decodeOption w.2.1) (resume z) (restrictI G (interior B z.2.2))).symm.trans
          ((congrArg (PMF.map (restrictI G (interior B z.2.2))) hmR').trans hfree.2)
    have hmeasL : (resume z).toMeasure {w |
        restrictI G (interior B z.2.2) (decodeOption w.1) ∈ A z.2.2} =
        ((resume z).map (fun w => restrictI G (interior B z.2.2)
          (decodeOption w.1))).toMeasure (A z.2.2) := by
      symm
      exact PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete
    have hmeasR : (resume z).toMeasure {w |
        restrictI G (interior B z.2.2) (decodeOption w.2.1) ∈ A z.2.2} =
        ((resume z).map (fun w => restrictI G (interior B z.2.2)
          (decodeOption w.2.1))).toMeasure (A z.2.2) := by
      symm
      exact PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete
    have hjointL : ((resume z).map (fun w => (z, w))).toMeasure L =
        (resume z).toMeasure {w |
          restrictI G (interior B z.2.2) (decodeOption w.1) ∈ A z.2.2} := by
      rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete]
      rfl
    have hjointR : ((resume z).map (fun w => (z, w))).toMeasure R =
        (resume z).toMeasure {w |
          restrictI G (interior B z.2.2) (decodeOption w.2.1) ∈ A z.2.2} := by
      rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete]
      rfl
    rw [hjointL, hjointR, hmeasL, hmeasR, hpushL, hpushR]
  · have hz0 : stopLaw z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
    simp [hz0]

end FK.Adaptive
