import FK.RandomRegionConvergence

/-!
# The exterior net: exhaustion-uniform exceptional sets

`FK.RandomRegion.HasNetExteriorConvergence` postulates one `μ`-null set off which
the exterior conditionals converge along the *net* of finite edge sets.  This
file proves the strongest unconditional statement that survives in that
direction: a single null set serves *every* exhaustion in a countable family
simultaneously. No full directed-net assertion or arbitrary measurable-event convergence is
proved here; the main property remains a hypothesis whose scope must be checked, while a
countable family now shares one joint exceptional set.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace FKLimit

variable {E : Type*}

/-- **One null set for countably many exhaustions.**  For a probability law `μ`,
a measurable event `A` and any countable family `Λ k` of monotone cofinal
sequences of finite edge sets, there is a single `μ`-null set off which the
exterior conditional probabilities of `A` converge to the tail conditional
probability, simultaneously for every `k`. -/
theorem tendsto_ae_condExp_indicator_outside_to_tail_all_exhaustions
    {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (Λ : ℕ → ℕ → Finset E) (hmono : ∀ k, Monotone (Λ k))
    (hcof : ∀ k (T : Finset E), ∃ n, T ⊆ Λ k n)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ,
      Tendsto (fun n => (μ⟦A | outsideSigma (Λ k n)⟧) ω) atTop
        (𝓝 ((μ⟦A | tailSigma⟧) ω)) := by
  refine ae_all_iff.2 fun k => ?_
  exact tendsto_ae_condExp_indicator_outside_to_tail (Λ k) (hmono k) (hcof k) hA

/-- Tail-trivial specialization of the simultaneous statement: one null set off
which the exterior conditionals of `A` converge to the unconditional mass along
every exhaustion in a countable family. -/
theorem tendsto_ae_condExp_indicator_outside_to_real_all_exhaustions
    {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (Λ : ℕ → ℕ → Finset E) (hmono : ∀ k, Monotone (Λ k))
    (hcof : ∀ k (T : Finset E), ∃ n, T ⊆ Λ k n)
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (htail : FK.ZeroOneOn tailSigma μ) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ,
      Tendsto (fun n => (μ⟦A | outsideSigma (Λ k n)⟧) ω) atTop (𝓝 (μ.real A)) := by
  refine ae_all_iff.2 fun k => ?_
  exact tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn (Λ k)
    (hmono k) (hcof k) hA htail

/-- **Net-exterior convergence from a countable covering of exhaustions.**
If the convergence of `HasNetExteriorConvergence` is known to be decided by a
countable family of exhaustions, then it holds.  Concretely: suppose that for
every `ω` and every `ε > 0` the net-threshold for `ω` is reached at one of the
sets `Λ k n` of a fixed countable family of exhaustions; then the net statement
holds off the single null set of
`tendsto_ae_condExp_indicator_outside_to_tail_all_exhaustions`.  This records
exactly the gap between the countable and the full net statement. -/
theorem hasNetExteriorConvergence_of_countable_exhaustions
    {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (Λ : ℕ → ℕ → Finset E) (hmono : ∀ k, Monotone (Λ k))
    (hcof : ∀ k (T : Finset E), ∃ n, T ⊆ Λ k n)
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hcover : ∀ ω, (∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
        |(μ⟦A | outsideSigma S⟧) ω - (μ⟦A | tailSigma⟧) ω| ≤ ε) ∨
      (∃ k : ℕ, ¬ Tendsto (fun n => (μ⟦A | outsideSigma (Λ k n)⟧) ω) atTop
        (𝓝 ((μ⟦A | tailSigma⟧) ω)))) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
      |(μ⟦A | outsideSigma S⟧) ω - (μ⟦A | tailSigma⟧) ω| ≤ ε := by
  filter_upwards [tendsto_ae_condExp_indicator_outside_to_tail_all_exhaustions
    Λ hmono hcof hA] with ω hω
  rcases hcover ω with h | ⟨k, hk⟩
  · exact h
  · exact absurd (hω k) hk

end FKLimit

#print axioms FKLimit.tendsto_ae_condExp_indicator_outside_to_tail_all_exhaustions
#print axioms FKLimit.tendsto_ae_condExp_indicator_outside_to_real_all_exhaustions
#print axioms FKLimit.hasNetExteriorConvergence_of_countable_exhaustions
