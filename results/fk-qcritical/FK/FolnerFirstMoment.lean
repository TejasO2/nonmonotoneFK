import Mathlib.MeasureTheory.Function.Intersectivity
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# First-moment obstruction for invariant marked points

This file isolates the analytic step of a Burton--Keane/Følner argument.
It deliberately contains no percolation geometry.  `A v` is the event that
`v` is a marked centre.  If at most `b` marked centres can occur in a finite
window `F`, and every event in the window has mass at least `c`, then
`F.card * c ≤ b`.  Consequently, a vanishing boundary/window ratio forces the
common lower bound to vanish.

The final structure records exactly the invariance needed to obtain a common
mass: a measure-preserving configuration map pulling each vertex event back to
one root event.  No group action, ergodicity, insertion tolerance, or Følner
sequence is defined implicitly by that structure.
-/

open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter

namespace FK.BurtonKeane.Folner

universe u v
variable {Ω : Type u} {V : Type v} [MeasurableSpace Ω]

/-- The number of marked vertices in a finite window, written as a sum of
indicators. -/
noncomputable def markedCount (A : V → Set Ω) (F : Finset V) (ω : Ω) : ℕ := by
  classical
  exact (F.filter fun v => ω ∈ A v).card

omit [MeasurableSpace Ω] in
lemma sum_indicator_one_eq_markedCount (A : V → Set Ω) (F : Finset V) (ω : Ω) :
    (∑ v ∈ F, (A v).indicator (1 : Ω → ℝ≥0∞) ω) = markedCount A F ω := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole, markedCount]

/-- First-moment identity for the random number of marked centres. -/
theorem lintegral_sum_indicator_one {μ : Measure Ω} (A : V → Set Ω)
    (hA : ∀ v, MeasurableSet (A v)) (F : Finset V) :
    (∫⁻ ω, ∑ v ∈ F, (A v).indicator (1 : Ω → ℝ≥0∞) ω ∂μ) =
      ∑ v ∈ F, μ (A v) := by
  rw [lintegral_finsetSum]
  · simp_rw [lintegral_indicator_one (hA _)]
  · intro v hv
    exact measurable_one.indicator (hA v)

/-- **Finite-window first-moment bound.**  A configurationwise bound on the
number of marked centres bounds the sum of their probabilities. -/
theorem card_mul_le_of_markedCount_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : V → Set Ω) (hA : ∀ v, MeasurableSet (A v)) (F : Finset V)
    (b : ℕ) (hbound : ∀ ω, markedCount A F ω ≤ b)
    (c : ℝ≥0∞) (hc : ∀ v ∈ F, c ≤ μ (A v)) :
    (F.card : ℝ≥0∞) * c ≤ (b : ℝ≥0∞) := by
  have hupper :
      (∫⁻ ω, ∑ v ∈ F, (A v).indicator (1 : Ω → ℝ≥0∞) ω ∂μ) ≤ (b : ℝ≥0∞) := by
    calc
      (∫⁻ ω, ∑ v ∈ F, (A v).indicator (1 : Ω → ℝ≥0∞) ω ∂μ)
          ≤ ∫⁻ _ω : Ω, (b : ℝ≥0∞) ∂μ := by
            apply lintegral_mono
            intro ω
            change (∑ v ∈ F, (A v).indicator (1 : Ω → ℝ≥0∞) ω) ≤ (b : ℝ≥0∞)
            rw [sum_indicator_one_eq_markedCount]
            exact_mod_cast hbound ω
      _ = (b : ℝ≥0∞) := by simp
  rw [lintegral_sum_indicator_one A hA F] at hupper
  calc
    (F.card : ℝ≥0∞) * c = F.card • c := by rw [nsmul_eq_mul]
    _ ≤ ∑ v ∈ F, μ (A v) := Finset.card_nsmul_le_sum F (fun v => μ (A v)) c hc
    _ ≤ (b : ℝ≥0∞) := hupper

/-- The density bound in boundary-over-window form. -/
theorem le_div_of_markedCount_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : V → Set Ω) (hA : ∀ v, MeasurableSet (A v)) {F : Finset V}
    (hF : F.Nonempty) (b : ℕ) (hbound : ∀ ω, markedCount A F ω ≤ b)
    (c : ℝ≥0∞) (hc : ∀ v ∈ F, c ≤ μ (A v)) :
    c ≤ (b : ℝ≥0∞) / (F.card : ℝ≥0∞) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hF)))
    (Or.inl (ENNReal.natCast_ne_top F.card))).mpr
  simpa only [mul_comm] using card_mul_le_of_markedCount_le A hA F b hbound c hc

/-- **Følner obstruction.**  If the marked-centre bound is sublinear along a
sequence of nonempty windows, no strictly positive uniform lower bound for
all the marked-event probabilities is possible. -/
theorem eq_zero_of_folner {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : V → Set Ω) (hA : ∀ v, MeasurableSet (A v))
    (F : ℕ → Finset V) (b : ℕ → ℕ) (hF : ∀ n, (F n).Nonempty)
    (hbound : ∀ n ω, markedCount A (F n) ω ≤ b n)
    (hfolner : Tendsto (fun n => (b n : ℝ≥0∞) / (F n).card) atTop (𝓝 0))
    (c : ℝ≥0∞) (hc : ∀ n v, v ∈ F n → c ≤ μ (A v)) :
    c = 0 := by
  apply bot_unique
  exact ge_of_tendsto hfolner (Eventually.of_forall fun n =>
    le_div_of_markedCount_le A hA (hF n) (b n) (hbound n) c (hc n))

/-- Events homogeneous over one orbit.  `shift v` need not come from a group:
it is simply a probability-preserving configuration map pulling the event at
`v` back to the root event. -/
structure HomogeneousEvents (Ω : Type u) (V : Type v) [MeasurableSpace Ω]
    (μ : Measure Ω) (root : V) where
  event : V → Set Ω
  shift : V → Ω → Ω
  measurableSet_event : ∀ v, MeasurableSet (event v)
  measurePreserving_shift : ∀ v, MeasurePreserving (shift v) μ μ
  preimage_event : ∀ v, shift v ⁻¹' event v = event root

namespace HomogeneousEvents

variable {μ : Measure Ω} {root : V}

/-- All vertex events in one invariant orbit have the root's mass. -/
theorem measure_event (E : HomogeneousEvents Ω V μ root) (v : V) :
    μ (E.event v) = μ (E.event root) := by
  calc
    μ (E.event v) = μ (E.shift v ⁻¹' E.event v) :=
      (E.measurePreserving_shift v).measure_preimage
        (E.measurableSet_event v).nullMeasurableSet |>.symm
    _ = μ (E.event root) := congrArg μ (E.preimage_event v)

/-- Homogeneous marked centres cannot have positive probability along a
Følner sequence if their configurationwise count has sublinear boundary bound. -/
theorem measure_root_eq_zero_of_folner {μ : Measure Ω} [IsProbabilityMeasure μ]
    {root : V} (E : HomogeneousEvents Ω V μ root)
    (F : ℕ → Finset V) (b : ℕ → ℕ) (hF : ∀ n, (F n).Nonempty)
    (hbound : ∀ n ω, markedCount E.event (F n) ω ≤ b n)
    (hfolner : Tendsto (fun n => (b n : ℝ≥0∞) / (F n).card) atTop (𝓝 0)) :
    μ (E.event root) = 0 := by
  apply eq_zero_of_folner (μ := μ) E.event E.measurableSet_event F b hF hbound hfolner
    (c := μ (E.event root))
  intro n v hv
  rw [E.measure_event v]

end HomogeneousEvents
end FK.BurtonKeane.Folner
