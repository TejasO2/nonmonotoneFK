import FK.RightWiredSequential

/-!
# Good-intersection masses for the right-wired ordered triple

The unnormalized lower-interior intersections with the common maximal upper
stratum have equal mass.  This is the substantive input to equation (9).
-/

namespace FK.Exploration.RightWiredGood

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior FK.Exploration.WiredMaximalStrata
open FK.Exploration.RightWiredSequential

local instance : MeasurableSpace (List Bool × List Bool × List Bool) := ⊤

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Sequential triple continuations retain all three initial histories. -/
theorem extendTriple_prefix_support
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (x₁ x₂ y : List Bool) (n : ℕ) {z : List Bool × List Bool × List Bool}
    (hz : z ∈ (extendTriple step x₁ x₂ y n).support) :
    x₁ <+: z.1 ∧ x₂ <+: z.2.1 ∧ y <+: z.2.2 := by
  induction n generalizing x₁ x₂ y z with
  | zero =>
      have h : z = (x₁, x₂, y) := (PMF.mem_support_pure_iff _ _).mp hz
      subst z
      exact ⟨List.prefix_rfl, List.prefix_rfl, List.prefix_rfl⟩
  | succ n ih =>
      rw [extendTriple, PMF.mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨h₁, h₂, h₃⟩ := ih (x₁ ++ [w.1]) (x₂ ++ [w.2.1]) (y ++ [w.2.2]) hz
      exact ⟨(List.prefix_append _ _).trans h₁,
        (List.prefix_append _ _).trans h₂, (List.prefix_append _ _).trans h₃⟩

/-- Short Boolean lookup configurations are fixed by an initial list prefix. -/
lemma toConfig_eq_of_prefix {x y : List Bool} {n : ℕ}
    (hx : x.length = n) (h : x <+: y) : toConfig n x = toConfig n y := by
  funext i
  have hix : i.1 < x.length := by omega
  have hiy : i.1 < y.length := lt_of_lt_of_le hix h.length_le
  change x.getD i.1 false = y.getD i.1 false
  rw [List.getD_eq_getElem _ _ hix, List.getD_eq_getElem _ _ hiy]
  exact h.getElem (i := i.1) hix

/-- The canonical closed-interior completion depends only on the exposed
initial exterior history. -/
lemma ambientOfHistory_eq_of_prefix {x y : List Bool}
    (hx : x.length = k) (h : x <+: y) :
    ambientOfHistory (m := m) (k := k) x = ambientOfHistory (m := m) (k := k) y := by
  funext a
  cases a with
  | inl a => rfl
  | inr a => exact congrFun (toConfig_eq_of_prefix hx h) a

/-- The maximal event on exposed triple histories. -/
def maximalHistory
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K) :
    Set (List Bool × List Bool × List Bool) :=
  {z | ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo}

/-- The decoded full upper configuration belongs to the maximal split
stratum exactly when its exposed upper history does. -/
theorem toAmbient_toConfig_mem_maximal_iff
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (hright : ExteriorHasRight so xo) (y : List Bool) :
    toAmbientConfig si ti so xo (toConfig (k + m) y) ∈ maximalSplitStratum si ti so xo ↔
      ambientOfHistory (m := m) y ∈ maximalSplitStratum si ti so xo := by
  have hext : exteriorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y)) =
      exteriorConfig (ambientOfHistory (m := m) y) := by
    funext i
    change toAmbientConfig si ti so xo (toConfig (k + m) y) (Sum.inr i) =
      ambientOfHistory (m := m) y (Sum.inr i)
    rw [toAmbientConfig_inr]
    rfl
  constructor
  · intro h
    exact mem_maximalSplitStratum_of_exterior_eq si ti so xo h hright hext.symm
  · intro h
    exact mem_maximalSplitStratum_of_exterior_eq si ti so xo h hright hext

/-- Measures of two events agree if they agree on every support point. -/
lemma pmf_toMeasure_eq_of_support {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) (E F : Set α)
    (h : ∀ a ∈ p.support, (a ∈ E ↔ a ∈ F)) :
    p.toMeasure E = p.toMeasure F := by
  rw [p.toMeasure_apply_eq_tsum, p.toMeasure_apply_eq_tsum]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · have hiff := h a ha
    by_cases haE : a ∈ E
    · have haF : a ∈ F := hiff.mp haE
      rw [Set.indicator_of_mem haE, Set.indicator_of_mem haF]
    · have haF : a ∉ F := fun hF => haE (hiff.mpr hF)
      rw [Set.indicator_of_notMem haE, Set.indicator_of_notMem haF]
  · have hp : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr ha
    simp [Set.indicator_apply, hp]

/-- Per-branch exact first-interior continuation on a maximal prefix. -/
lemma remainder_first_interior
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    {z : List Bool × List Bool × List Bool}
    (hz : z ∈ (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      [] [] [] k).support) (hzM : z ∈ maximalHistory si ti so xo) :
    (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      z.1 z.2.1 z.2.2 m).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  have hlen := extendTriple_length_support _ [] [] [] k hz
  have hM : ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo := hzM
  have hy : z.2.2 = exteriorHistory (m := m) (ambientOfHistory z.2.2) :=
    (exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.2.2)).symm
  have hstep : ∀ x₁ x₂ y, (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂
      x₁ x₂ y).map (fun z => (z.1, z.2.2)) =
      rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₁ x₁ y := by
    intro x₁ x₂ y
    exact rightWiredTripleStep_map_fst si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y
  have hzpair : (z.1, z.2.2) ∈
      (extendPair (rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₁) [] [] k).support := by
    rw [← extendTriple_map_fst_thd _ _ hstep [] [] [] k]
    rw [PMF.mem_support_map_iff]
    exact ⟨z, hz, rfl⟩
  calc
    (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      z.1 z.2.1 z.2.2 m).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) =
      ((extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
        z.1 z.2.1 z.2.2 m).map (fun w => (w.1, w.2.2))).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
          rw [PMF.map_comp]
          rfl
    _ = (extendPair (rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₁)
        z.1 z.2.2 m).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
          rw [extendTriple_map_fst_thd _ _ hstep]
    _ = _ := by
      exact pair_interior_continuation_rightWired si ti so xo hq hp₀ hp₁
        ζ₁ (ambientOfHistory z.2.2) hright hM hzpair hy

/-- Per-branch exact second-interior continuation on a maximal prefix. -/
lemma remainder_second_interior
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    {z : List Bool × List Bool × List Bool}
    (hz : z ∈ (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      [] [] [] k).support) (hzM : z ∈ maximalHistory si ti so xo) :
    (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      z.1 z.2.1 z.2.2 m).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  have hlen := extendTriple_length_support _ [] [] [] k hz
  have hM : ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo := hzM
  have hy : z.2.2 = exteriorHistory (m := m) (ambientOfHistory z.2.2) :=
    (exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.2.2)).symm
  have hstep : ∀ x₁ x₂ y, (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂
      x₁ x₂ y).map (fun z => (z.2.1, z.2.2)) =
      rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₂ x₂ y := by
    intro x₁ x₂ y
    exact rightWiredTripleStep_map_snd si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ x₁ x₂ y
  have hzpair : (z.2.1, z.2.2) ∈
      (extendPair (rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₂) [] [] k).support := by
    rw [← extendTriple_map_snd_thd _ _ hstep [] [] [] k]
    rw [PMF.mem_support_map_iff]
    exact ⟨z, hz, rfl⟩
  calc
    (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      z.1 z.2.1 z.2.2 m).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1))) =
      ((extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
        z.1 z.2.1 z.2.2 m).map (fun w => (w.2.1, w.2.2))).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
          rw [PMF.map_comp]
          rfl
    _ = (extendPair (rightWiredUpperStep si ti so xo hq hp₀ hp₁ ζ₂)
        z.2.1 z.2.2 m).map (fun w =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
          rw [extendTriple_map_snd_thd _ _ hstep]
    _ = _ := by
      exact pair_interior_continuation_rightWired si ti so xo hq hp₀ hp₁
        ζ₂ (ambientOfHistory z.2.2) hright hM hzpair hy

end FK.Exploration.RightWiredGood

namespace FK.Exploration.RightWiredGood

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior FK.Exploration.WiredMaximalStrata
open FK.Exploration.RightWiredSequential

local instance : MeasurableSpace (List Bool × List Bool × List Bool) := ⊤

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- The two lower-interior events have equal unnormalized mass on the common
maximal upper stratum. -/
theorem good_intersection_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    (A : Set (Fin m → Bool)) :
    (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      [] [] [] (k + m)).toMeasure
      ({w | interiorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.1)) ∈ A} ∩ maximalHistory si ti so xo) =
    (extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
      [] [] [] (k + m)).toMeasure
      ({w | interiorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.2.1)) ∈ A} ∩ maximalHistory si ti so xo) := by
  let step := rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂
  let pfx := extendTriple step [] [] [] k
  let M := maximalHistory si ti so xo
  let A₁ : Set (List Bool × List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A}
  let A₂ : Set (List Bool × List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1)) ∈ A}
  let free := (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary
  change (extendTriple step [] [] [] (k + m)).toMeasure (A₁ ∩ M) =
    (extendTriple step [] [] [] (k + m)).toMeasure (A₂ ∩ M)
  have hdecomp : extendTriple step [] [] [] (k + m) = pfx.bind fun z =>
      extendTriple step z.1 z.2.1 z.2.2 m := extendTriple_add step [] [] [] k m
  rw [hdecomp]
  rw [PMF.toMeasure_bind_apply _ _ (A₁ ∩ M) MeasurableSet.of_discrete,
    PMF.toMeasure_bind_apply _ _ (A₂ ∩ M) MeasurableSet.of_discrete]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ pfx.support
  · have hlen := extendTriple_length_support step [] [] [] k hz
    by_cases hzM : z ∈ M
    · have hstable : ∀ w ∈ (extendTriple step z.1 z.2.1 z.2.2 m).support, w ∈ M := by
        intro w hw
        have hpre := (extendTriple_prefix_support step z.1 z.2.1 z.2.2 m hw).2.2
        have heq := ambientOfHistory_eq_of_prefix (m := m)
          (by simpa using hlen.2.2) hpre
        change ambientOfHistory (m := m) w.2.2 ∈ maximalSplitStratum si ti so xo
        rw [← heq]
        exact hzM
      have hm₁ : (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₁ ∩ M) =
          free.toMeasure A := by
        calc
          (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₁ ∩ M) =
              (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure A₁ := by
            apply pmf_toMeasure_eq_of_support
            intro w hw
            exact ⟨fun h => h.1, fun h => ⟨h, hstable w hw⟩⟩
          _ = ((extendTriple step z.1 z.2.1 z.2.2 m).map (fun w =>
              interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)))).toMeasure A := by
            rw [← PMF.toMeasure_map _ _ (by intro s hs; exact MeasurableSet.of_discrete),
              MeasureTheory.Measure.map_apply (by intro s hs; exact MeasurableSet.of_discrete) MeasurableSet.of_discrete]
            rfl
          _ = free.toMeasure A := by
            rw [remainder_first_interior si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ hright hz hzM]
            rfl
      have hm₂ : (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₂ ∩ M) =
          free.toMeasure A := by
        calc
          (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₂ ∩ M) =
              (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure A₂ := by
            apply pmf_toMeasure_eq_of_support
            intro w hw
            exact ⟨fun h => h.1, fun h => ⟨h, hstable w hw⟩⟩
          _ = ((extendTriple step z.1 z.2.1 z.2.2 m).map (fun w =>
              interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1)))).toMeasure A := by
            rw [← PMF.toMeasure_map _ _ (by intro s hs; exact MeasurableSet.of_discrete),
              MeasureTheory.Measure.map_apply (by intro s hs; exact MeasurableSet.of_discrete) MeasurableSet.of_discrete]
            rfl
          _ = free.toMeasure A := by
            rw [remainder_second_interior si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ hright hz hzM]
            rfl
      rw [hm₁, hm₂]
    · have hnone : ∀ w ∈ (extendTriple step z.1 z.2.1 z.2.2 m).support, w ∉ M := by
        intro w hw
        have hpre := (extendTriple_prefix_support step z.1 z.2.1 z.2.2 m hw).2.2
        have heq := ambientOfHistory_eq_of_prefix (m := m)
          (by simpa using hlen.2.2) hpre
        change ambientOfHistory (m := m) w.2.2 ∉ maximalSplitStratum si ti so xo
        rw [← heq]
        exact hzM
      have hzero₁ : (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₁ ∩ M) = 0 := by
        calc
          (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₁ ∩ M) =
              (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure ∅ := by
            apply pmf_toMeasure_eq_of_support
            intro w hw
            exact ⟨fun h => (hnone w hw h.2).elim, fun h => h.elim⟩
          _ = 0 := by simp
      have hzero₂ : (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₂ ∩ M) = 0 := by
        calc
          (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure (A₂ ∩ M) =
              (extendTriple step z.1 z.2.1 z.2.2 m).toMeasure ∅ := by
            apply pmf_toMeasure_eq_of_support
            intro w hw
            exact ⟨fun h => (hnone w hw h.2).elim, fun h => h.elim⟩
          _ = 0 := by simp
      rw [hzero₁, hzero₂]
  · have hz0 : pfx z = 0 := (PMF.apply_eq_zero_iff pfx z).mpr hz
    simp [hz0]

end FK.Exploration.RightWiredGood
