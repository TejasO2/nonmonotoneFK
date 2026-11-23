import FK.PlanarParameters
import FK.BernoulliDuality

/-!
# Abstract reduction for Theorem 1.11

This file isolates the exact logical part of the strong-supercritical
uniqueness argument.  `Primal` and `Dual` must be instantiated by all FK(p,q)
measures (every convention) on the primal and dual graph respectively.  The
finite-volume limit/duality identification, enhanced domination, and planar
cluster-count geometry are explicit hypotheses, not definitions of FK measures.
No result below claims to prove those external inputs.
-/

namespace FK.Planar

open MeasureTheory Set
open FK.Configuration

/-- Strong uniqueness for a nonempty family of probability laws. -/
def StrongUniqueness {Ω : Type*} [MeasurableSpace Ω]
    (Laws : Set (Measure Ω)) : Prop :=
  ∃! μ, μ ∈ Laws

/-- If dualization sends every primal law into a family having strong
uniqueness, then the primal family has strong uniqueness. -/
theorem strongUniqueness_of_dual {E E' : Type*}
    (e : E ≃ E') (Primal : Set (Measure (E → Bool)))
    (Dual : Set (Measure (E' → Bool))) (hPrimal : Primal.Nonempty)
    (hDual : StrongUniqueness Dual)
    (hmaps : ∀ φ ∈ Primal, Measure.map (dualMeasurableEquiv e) φ ∈ Dual) :
    StrongUniqueness Primal := by
  obtain ⟨ν, hν, hνunique⟩ := hDual
  obtain ⟨φ, hφ⟩ := hPrimal
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply (dualMeasurableEquiv e).map_measurableEquiv_injective
  calc
    Measure.map (dualMeasurableEquiv e) ψ = ν :=
      hνunique _ (hmaps ψ hψ)
    _ = Measure.map (dualMeasurableEquiv e) φ :=
      (hνunique _ (hmaps φ hφ)).symm

/-- Explicit representation of every primal law as the inverse dual image of
the unique dual law. -/
theorem primal_eq_inverse_dual {E E' : Type*}
    (e : E ≃ E') (Primal : Set (Measure (E → Bool)))
    (Dual : Set (Measure (E' → Bool))) {ν : Measure (E' → Bool)}
    (_hν : ν ∈ Dual) (hνunique : ∀ ψ ∈ Dual, ψ = ν)
    (hmaps : ∀ φ ∈ Primal, Measure.map (dualMeasurableEquiv e) φ ∈ Dual)
    {φ : Measure (E → Bool)} (hφ : φ ∈ Primal) :
    φ = Measure.map (dualMeasurableEquiv e).symm ν := by
  apply (dualMeasurableEquiv e).map_apply_eq_iff_map_symm_apply_eq.mp
  exact hνunique _ (hmaps φ hφ)

/-- The planar cluster-count step: at least one primal infinite cluster plus
absence of dual infinite clusters gives exactly one primal infinite cluster.
The geometric implication `hgeometry` is the input from planar duality. -/
theorem ae_exactly_one_infinite {E E' : Type*} (e : E ≃ E')
    (φ : Measure (E → Bool))
    (HasInfinite AtMostOne : Set (E → Bool)) (NoDualInfinite : Set (E' → Bool))
    (hNoDualMeasurable : MeasurableSet NoDualInfinite)
    (hsuper : ∀ᵐ ω ∂φ, ω ∈ HasInfinite)
    (hdualsub : ∀ᵐ ω' ∂(Measure.map (dualMeasurableEquiv e) φ),
      ω' ∈ NoDualInfinite)
    (hgeometry : ∀ ω, dualMeasurableEquiv e ω ∈ NoDualInfinite → ω ∈ AtMostOne) :
    ∀ᵐ ω ∂φ, ω ∈ HasInfinite ∩ AtMostOne := by
  have hpre : ∀ᵐ ω ∂φ, dualMeasurableEquiv e ω ∈ NoDualInfinite :=
    (ae_map_iff (dualMeasurableEquiv e).measurable.aemeasurable
      hNoDualMeasurable).mp hdualsub
  filter_upwards [hsuper, hpre] with ω hω hωdual
  exact ⟨hω, hgeometry ω hωdual⟩

/-- Faithful abstract form of the deduction in Theorem 1.11.

* `Primal` is `FK(p,q)` on `G`, including every convention at infinity.
* `Dual` is `FK(p*,q)` on `G*`, again including every convention.
* `c` is `pc(G*)` and `δ` is `δ''` in the paper.
* `hDualStrong` is Theorem 1.10 applied on `G*`.
* `hmaps` packages Proposition 1.8(1), equation (12), and exhaustion by finite
  subgraphs; its usual proof uses the a.e. at-most-one-infinite conclusion.
* `hsuper` is the enhanced supercritical lower domination for `G`.
* `hdualsub` is the enhanced dual upper domination plus essential enhancements.
* `hgeometry` is the planar assertion that no infinite dual cluster forces at
  most one infinite primal cluster.

The conclusion is strong uniqueness and a.s. exactly one infinite cluster for
the unique FK law, with all graph-specific probabilistic input still explicit.
-/
theorem theorem_1_11_abstract {E E' : Type*} (e : E ≃ E')
    {q p c δ : ℝ} (hq : 0 < q) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hwindow : min p (prime q p) > 1 - c - δ)
    (Primal : Set (Measure (E → Bool))) (Dual : Set (Measure (E' → Bool)))
    (hPrimal : Primal.Nonempty)
    (hDualStrong : max (dual q p) (prime q (dual q p)) < c + δ →
      StrongUniqueness Dual)
    (hmaps : ∀ φ ∈ Primal, Measure.map (dualMeasurableEquiv e) φ ∈ Dual)
    (HasInfinite AtMostOne : Set (E → Bool)) (NoDualInfinite : Set (E' → Bool))
    (hNoDualMeasurable : MeasurableSet NoDualInfinite)
    (hsuper : ∀ φ ∈ Primal, ∀ᵐ ω ∂φ, ω ∈ HasInfinite)
    (hdualsub : ∀ φ ∈ Primal,
      ∀ᵐ ω' ∂(Measure.map (dualMeasurableEquiv e) φ), ω' ∈ NoDualInfinite)
    (hgeometry : ∀ ω, dualMeasurableEquiv e ω ∈ NoDualInfinite → ω ∈ AtMostOne) :
    StrongUniqueness Primal ∧
      ∀ φ ∈ Primal, ∀ᵐ ω ∂φ, ω ∈ HasInfinite ∩ AtMostOne := by
  have hdualwindow : max (dual q p) (prime q (dual q p)) < c + δ :=
    (parameter_window_iff hq hp₀ hp₁).mp hwindow
  have hunique : StrongUniqueness Primal :=
    strongUniqueness_of_dual e Primal Dual hPrimal (hDualStrong hdualwindow) hmaps
  refine ⟨hunique, ?_⟩
  intro φ hφ
  exact ae_exactly_one_infinite e φ HasInfinite AtMostOne NoDualInfinite
    hNoDualMeasurable (hsuper φ hφ) (hdualsub φ hφ) hgeometry

end FK.Planar
