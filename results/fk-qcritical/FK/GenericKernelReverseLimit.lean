import FK.ReverseMartingale
import FK.ConditionallyIndependentOrderedCoupling

/-!
# The reverse-martingale theorem available in every kernel fibre

This separates two uses of a dominated ordered kernel `K` that must not be
confused.  For every fixed `η` and every fixed `L²` observable `f`, the law
`K η` has its own downward convergence theorem, with limit `(K η)[f | tail]`.
No DLR property, stochastic order, second-marginal identity, or relation to
another law is needed.  The theorem is packaged separately for arbitrary
Markov kernels and for the kernels returned by `exists_dominatedKernel`.

The result concerns one fixed `f`.  It does not assert convergence of a
changing triangular array of conditional expectations of another law, nor
identify the fibre limit with that other law's tail conditional expectation.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

namespace FKLimit

universe u v

/-- Downward convergence for an arbitrary real `L²` observable on an exterior
filtration.  This exposes the underlying measure in the target and is useful
when that measure is a conditional fibre rather than an FK law. -/
theorem tendsto_ae_condExp_outside_to_tail
    {E : Type u} {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {f : Configuration E → ℝ} (hf : MemLp f 2 μ)
    (hbdd : ∃ R : ℝ, ∀ n, ∀ᵐ ω ∂μ, |(μ[f | outsideSigma (S n)]) ω| ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ[f | outsideSigma (S n)]) ω) atTop
      (𝓝 ((μ[f | tailSigma]) ω)) := by
  have hanti : Antitone (fun n ↦ outsideSigma (S n)) := by
    intro m n hmn
    exact outsideSigma_anti (hS hmn)
  have hle : ∀ n, outsideSigma (S n) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    fun n ↦ outsideSigma_le _
  have hleInf : (⨅ n, outsideSigma (S n)) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    (iInf_le (fun n ↦ outsideSigma (S n)) 0).trans (hle 0)
  have h := FK.tendsto_ae_condExp_iInf_of_memLp_two_of_bounded
    (μ := μ) (G := fun n ↦ outsideSigma (S n)) hanti hle hleInf hf hbdd
  simpa only [iInf_outsideSigma_eq_tailSigma S hcof] using h

/-- **Generic Markov-fibre reverse limit.**  For every Markov kernel `K`, every
parameter `η`, and every fixed `L²` real observable `f`, conditional
expectations under `K η` converge to the tail conditional expectation under
that same fibre law. -/
theorem tendsto_ae_condExp_outside_to_tail_fibre
    {E : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (K : Kernel Ω (Configuration E)) (hK : IsMarkovKernel K) (η : Ω)
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {f : Configuration E → ℝ} (hf : MemLp f 2 (K η))
    (hbdd : ∃ R : ℝ, ∀ n, ∀ᵐ ω ∂(K η), |(K η)[f | outsideSigma (S n)] ω| ≤ R) :
    ∀ᵐ ω ∂(K η), Tendsto (fun n ↦ (K η)[f | outsideSigma (S n)] ω) atTop
      (𝓝 ((K η)[f | tailSigma] ω)) := by
  letI : IsMarkovKernel K := hK
  exact tendsto_ae_condExp_outside_to_tail S hS hcof hf hbdd

/-- Bounded-measurable form of the generic fibre theorem.  Measurability and
one pointwise bound supply both the `L²` hypothesis and all conditional bounds,
so no additional integrability input is required from a fibre user. -/
theorem tendsto_ae_condExp_bounded_outside_to_tail_fibre
    {E : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (K : Kernel Ω (Configuration E)) (hK : IsMarkovKernel K) (η : Ω)
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {f : Configuration E → ℝ} (hf : Measurable f)
    {R : ℝ} (hR : ∀ ω, |f ω| ≤ R) :
    ∀ᵐ ω ∂(K η), Tendsto (fun n ↦ (K η)[f | outsideSigma (S n)] ω) atTop
      (𝓝 ((K η)[f | tailSigma] ω)) := by
  letI : IsMarkovKernel K := hK
  have hfLp : MemLp f 2 (K η) := by
    apply MemLp.of_bound hf.aestronglyMeasurable R
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hR ω
  apply tendsto_ae_condExp_outside_to_tail_fibre K hK η S hS hcof hfLp
  refine ⟨R, fun n ↦ ae_bdd_abs_condExp_of_ae_bdd_abs ?_⟩
  exact Filter.Eventually.of_forall hR

/-- Indicator-specialized generic fibre limit, with no boundedness side
condition left for the user.  Both the sequence and its target are conditional
probabilities under the actual fibre law `K η`. -/
theorem tendsto_ae_condExp_indicator_outside_to_tail_fibre
    {E : Type u} {Ω : Type v} [MeasurableSpace Ω]
    (K : Kernel Ω (Configuration E)) (hK : IsMarkovKernel K) (η : Ω)
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(K η), Tendsto
      (fun n ↦ (K η)[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (S n)] ω)
      atTop (𝓝 ((K η)[A.indicator (fun _ ↦ (1 : ℝ)) | tailSigma] ω)) := by
  letI : IsMarkovKernel K := hK
  exact tendsto_ae_condExp_indicator_outside_to_tail S hS hcof hA

/-- The two dominated ordered kernels each satisfy the generic fibre theorem
under any fixed monotone cofinal region sequence.  The pair of limits is
written separately as `(K₁ η)[f | tail]` and `(K₂ η)[f | tail]`, without an
unjustified equality between them or with a marginal tail conditional. -/
theorem tendsto_ae_condExp_indicator_outside_to_tail_dominated_pair
    {E : Type u} [Countable E]
    {μ₁ μ₂ ρ : ProbabilityMeasure (Configuration E)}
    (h₁ : StochasticallyDominates ρ μ₁) (h₂ : StochasticallyDominates ρ μ₂)
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∃ K₁ K₂ : Kernel (Configuration E) (Configuration E),
      IsMarkovKernel K₁ ∧ IsMarkovKernel K₂ ∧
      (∀ᵐ η ∂(ρ : Measure (Configuration E)), K₁ η {ξ | ξ ≤ η} = 1) ∧
      (∀ᵐ η ∂(ρ : Measure (Configuration E)), K₂ η {ξ | ξ ≤ η} = 1) ∧
      (((ρ : Measure (Configuration E)) ⊗ₘ K₁).map Prod.snd =
        (μ₁ : Measure (Configuration E))) ∧
      (((ρ : Measure (Configuration E)) ⊗ₘ K₂).map Prod.snd =
        (μ₂ : Measure (Configuration E))) ∧
      (∀ η, ∀ᵐ ω ∂(K₁ η), Tendsto
        (fun n ↦ (K₁ η)[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (S n)] ω)
        atTop (𝓝 ((K₁ η)[A.indicator (fun _ ↦ (1 : ℝ)) | tailSigma] ω))) ∧
      (∀ η, ∀ᵐ ω ∂(K₂ η), Tendsto
        (fun n ↦ (K₂ η)[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (S n)] ω)
        atTop (𝓝 ((K₂ η)[A.indicator (fun _ ↦ (1 : ℝ)) | tailSigma] ω))) := by
  obtain ⟨K₁, hK₁, hsupp₁, -, hmarg₁⟩ := exists_dominatedKernel h₁
  obtain ⟨K₂, hK₂, hsupp₂, -, hmarg₂⟩ := exists_dominatedKernel h₂
  refine ⟨K₁, K₂, hK₁, hK₂, hsupp₁, hsupp₂, hmarg₁, hmarg₂, ?_, ?_⟩
  · intro η
    exact tendsto_ae_condExp_indicator_outside_to_tail_fibre K₁ hK₁ η S hS hcof hA
  · intro η
    exact tendsto_ae_condExp_indicator_outside_to_tail_fibre K₂ hK₂ η S hS hcof hA


end FKLimit
