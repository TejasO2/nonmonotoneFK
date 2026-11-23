import FK.RightWiredGood

/-!
# Equation (9) for right-wired finite FK explorations

The good-intersection equality is transported to actual finite configurations.
The ordered triple coupling then gives the equation-(9) absolute-difference
bound, with no conditional-good-law assumption left in the statement.
-/

namespace FK.Exploration.RightWiredEquationNine

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior FK.Exploration.WiredMaximalStrata
open FK.Exploration.RightWiredSequential FK.Exploration.RightWiredGood

local instance : MeasurableSpace (List Bool × List Bool × List Bool) := ⊤

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Package the explicit process as a `TripleCoupling` with actual finite
marginals. -/
noncomputable def rightWiredTripleCoupling
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :
    PMF.TripleCoupling (rightWiredLaw si ti so xo hq hp₁ ζ₁)
      (rightWiredLaw si ti so xo hq hp₁ ζ₂)
      ((finIndexedGraph (U ⊕ K) (k + m)
        (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le)) where
  dist := rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂
  map_fst := rightWiredTriple_map_fst si ti so xo hq hp₀ hp₁ ζ₁ ζ₂
  map_snd := rightWiredTriple_map_snd si ti so xo hq hp₀ hp₁ ζ₁ ζ₂
  map_thd := rightWiredTriple_map_thd si ti so xo hq hp₀ hp₁ ζ₁ ζ₂

/-- Configuration-level equality of the good intersections. -/
theorem config_good_intersection_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    (A : Set (Fin m → Bool)) :
    (rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).toMeasure
      ((fun z => z.1) ⁻¹' ((fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A) ∩
        (fun z => z.2.2) ⁻¹'
          {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}) =
    (rightWiredTriple si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).toMeasure
      ((fun z => z.2.1) ⁻¹' ((fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A) ∩
        (fun z => z.2.2) ⁻¹'
          {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}) := by
  let P := extendTriple (rightWiredTripleStep si ti so xo hq hp₀ hp₁ ζ₁ ζ₂)
    [] [] [] (k + m)
  let E₁ : Set ((Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool)) :=
    (fun z => z.1) ⁻¹' ((fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A) ∩
      (fun z => z.2.2) ⁻¹'
        {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
  let E₂ : Set ((Fin (k + m) → Bool) × (Fin (k + m) → Bool) × (Fin (k + m) → Bool)) :=
    (fun z => z.2.1) ⁻¹' ((fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A) ∩
      (fun z => z.2.2) ⁻¹'
        {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
  have hset₁ : decodeTriple ⁻¹' E₁ =
      {w | interiorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.1)) ∈ A} ∩ maximalHistory si ti so xo := by
    ext w
    change (interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A ∧
        toAmbientConfig si ti so xo (toConfig (k + m) w.2.2) ∈
          maximalSplitStratum si ti so xo) ↔
      (interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)) ∈ A ∧
        ambientOfHistory (m := m) w.2.2 ∈ maximalSplitStratum si ti so xo)
    rw [toAmbient_toConfig_mem_maximal_iff si ti so xo hright]
  have hset₂ : decodeTriple ⁻¹' E₂ =
      {w | interiorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.2.1)) ∈ A} ∩ maximalHistory si ti so xo := by
    ext w
    change (interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1)) ∈ A ∧
        toAmbientConfig si ti so xo (toConfig (k + m) w.2.2) ∈
          maximalSplitStratum si ti so xo) ↔
      (interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1)) ∈ A ∧
        ambientOfHistory (m := m) w.2.2 ∈ maximalSplitStratum si ti so xo)
    rw [toAmbient_toConfig_mem_maximal_iff si ti so xo hright]
  change (P.map decodeTriple).toMeasure E₁ = (P.map decodeTriple).toMeasure E₂
  rw [← PMF.toMeasure_map decodeTriple P (by intro s hs; exact MeasurableSet.of_discrete),
    MeasureTheory.Measure.map_apply (by intro s hs; exact MeasurableSet.of_discrete)
      MeasurableSet.of_discrete,
    MeasureTheory.Measure.map_apply (by intro s hs; exact MeasurableSet.of_discrete)
      MeasurableSet.of_discrete]
  rw [hset₁, hset₂]
  exact good_intersection_rightWired si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ hright A

/-- **Equation (9) for finite right-wired explorations.**  The local event is
pulled back from the actual interior graph.  The exceptional event is the
complement of the canonical maximal closed-cutset stratum of the common
Bernoulli upper configuration. -/
theorem equation_nine_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    (A : Set (Fin m → Bool)) :
    let A' : Set (Fin (k + m) → Bool) :=
      (fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A
    let C : Set (Fin (k + m) → Bool) :=
      {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
    |(rightWiredLaw si ti so xo hq hp₁ ζ₁).toMeasure.real A' -
        (rightWiredLaw si ti so xo hq hp₁ ζ₂).toMeasure.real A'| ≤
      ((finIndexedGraph (U ⊕ K) (k + m)
        (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le)).toMeasure.real Cᶜ := by
  intro A' C
  apply (rightWiredTripleCoupling si ti so xo hq hp₀ hp₁ ζ₁ ζ₂).equation_nine_abs_bound
    MeasurableSet.of_discrete MeasurableSet.of_discrete MeasurableSet.of_discrete
  exact config_good_intersection_rightWired si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ hright A

end FK.Exploration.RightWiredEquationNine
