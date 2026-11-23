import FK.RightWiredEquationNine

/-!
# Restriction of the second marginal in the right-wired equation (9)

The public right-wired theorem compares two FK laws on one configuration type.
Lemma 2.1 instead prescribes only the restriction of its second coordinate to
the smaller box.  This file records the exact measure-theoretic consequence
available after such a restriction: if the local observation factors through
the restriction map, equation (9) compares the first law with the pushed-forward
second marginal.

The hypothesis `hsecond` is intentionally prominent.  Identifying the
right-wired law's pushforward with an actual `φ_Δ^τ`, for a genuinely nested
`Λ ⊆ Δ ⊆ Σ`, is a remaining graph/model construction and is not claimed here.
-/

namespace FK.Exploration.RightWiredRestriction

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior FK.Exploration.WiredMaximalStrata
open FK.Exploration.RightWiredSequential FK.Exploration.RightWiredGood

open MeasureTheory

universe u

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- **Equation (9) after restricting the second marginal.**  The target
configuration type `D` is arbitrary: it may be the configurations on `E_Δ`.
The map `readΛ` recovers the `Λ`-local observation from the restriction to `D`.

This theorem does not assert that `μΔ` is an FK measure.  That identification
is supplied separately by `hsecond` in each application. -/
theorem equation_nine_rightWired_second_restrict
    {D : Type u} [MeasurableSpace D]
    (restrictΔ : (Fin (k + m) → Bool) → D) (readΛ : D → (Fin m → Bool))
    (μΔ : Measure D)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    (A : Set (Fin m → Bool)) (hA : MeasurableSet A)
    (hrestrict : Measurable restrictΔ) (hread : Measurable readΛ)
    (hreadcomp : readΛ ∘ restrictΔ =
      fun ω ↦ interiorConfig (toAmbientConfig si ti so xo ω))
    (hsecond : μΔ = Measure.map restrictΔ
      (rightWiredLaw si ti so xo hq hp₁ ζ₂).toMeasure) :
    let A' : Set (Fin (k + m) → Bool) :=
      (fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A
    let C : Set (Fin (k + m) → Bool) :=
      {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
    |(rightWiredLaw si ti so xo hq hp₁ ζ₁).toMeasure.real A' -
        μΔ.real (readΛ ⁻¹' A)| ≤
      ((finIndexedGraph (U ⊕ K) (k + m)
        (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le)).toMeasure.real Cᶜ := by
  intro A' C
  have hset : restrictΔ ⁻¹' (readΛ ⁻¹' A) = A' := by
    ext ω
    change (readΛ ∘ restrictΔ) ω ∈ A ↔
      interiorConfig (toAmbientConfig si ti so xo ω) ∈ A
    rw [hreadcomp]
  have hsecondreal : μΔ.real (readΛ ⁻¹' A) =
      (rightWiredLaw si ti so xo hq hp₁ ζ₂).toMeasure.real A' := by
    simp only [measureReal_def, hsecond, Measure.map_apply hrestrict (hread hA), hset]
  rw [hsecondreal]
  exact RightWiredEquationNine.equation_nine_rightWired si ti so xo
    hq hp₀ hp₁ ζ₁ ζ₂ hright A

/-- Actual-FK form of the restriction corollary.  The second term is literally
`B.fkMeasure` with arbitrary boundary setoid `α`.  The sole marginal-model
premise is `hsecond`: this FK law is the restriction of the second right-wired
coordinate.  In particular, arbitrary left/cross wiring is not smuggled into
the scoped split-graph result. -/
theorem equation_nine_rightWired_second_fkRestriction
    (B : LabelledMultigraph) (α : B.BoundaryPartition)
    (restrictΔ : (Fin (k + m) → Bool) → B.Configuration)
    (readΛ : B.Configuration → (Fin m → Bool))
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo)
    (A : Set (Fin m → Bool)) (hA : MeasurableSet A)
    (hrestrict : Measurable restrictΔ) (hread : Measurable readΛ)
    (hreadcomp : readΛ ∘ restrictΔ =
      fun ω ↦ interiorConfig (toAmbientConfig si ti so xo ω))
    (hsecond : B.fkMeasure hq hp₁.le α = Measure.map restrictΔ
      (rightWiredLaw si ti so xo hq hp₁ ζ₂).toMeasure) :
    let A' : Set (Fin (k + m) → Bool) :=
      (fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) ⁻¹' A
    let C : Set (Fin (k + m) → Bool) :=
      {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
    |(rightWiredLaw si ti so xo hq hp₁ ζ₁).toMeasure.real A' -
        (B.fkMeasure hq hp₁.le α).real (readΛ ⁻¹' A)| ≤
      ((finIndexedGraph (U ⊕ K) (k + m)
        (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target).bernoulliProductPMF
          (upperRateNN_le_one hq hp₁.le)).toMeasure.real Cᶜ := by
  exact equation_nine_rightWired_second_restrict restrictΔ readΛ
    (B.fkMeasure hq hp₁.le α) si ti so xo hq hp₀ hp₁ ζ₁ ζ₂ hright A hA
    hrestrict hread hreadcomp hsecond

end FK.Exploration.RightWiredRestriction
