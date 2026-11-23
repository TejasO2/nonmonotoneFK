import Mathlib

/-!
# Uniqueness from agreeing conditional limits

This file formalizes the final measure-theoretic step of Theorem 5.1 in
Beffara--Faipeur--Oke (arXiv:2512.16486).  Two probability measures are
compared on a common auxiliary probability space.  On every cylinder, their
conditional-probability sequences converge to the respective unconditional
masses (extremality/tail-triviality and backward martingale convergence), and
the sequences eventually agree (the common free-boundary specification).
We prove that these hypotheses imply equality of the two measures.
-/

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace FK

variable {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]

/-- On each set in `cylinders`, two sequences of real-valued functions on an
auxiliary probability space represent the conditional masses under `μ` and
`ν`.  They have the respective unconditional limits and eventually agree.
No conditional-expectation API is imposed here: the DLR and martingale facts
that produce these sequences remain explicit mathematical inputs. -/
structure CommonConditionalLimits
    (μ ν : Measure Ω) (ρ : Measure Θ) (cylinders : Set (Set Ω)) : Prop where
  sequences : ∀ A ∈ cylinders, ∃ f g : ℕ → Θ → ℝ,
    (∀ᵐ z ∂ρ, Tendsto (fun n => f n z) atTop (𝓝 (μ A).toReal)) ∧
    (∀ᵐ z ∂ρ, Tendsto (fun n => g n z) atTop (𝓝 (ν A).toReal)) ∧
    (∀ᵐ z ∂ρ, (fun n => f n z) =ᶠ[atTop] (fun n => g n z))

/-- Eventually equal conditional-probability sequences with unconditional
limits identify the masses of every cylinder, hence identify the measures.
The two probability-measure instances on `μ` and `ν` also give the common
finite/univ extensionality hypotheses; the instance on `ρ` makes its almost-
everywhere filter nontrivial. -/
theorem measure_eq_of_commonConditionalLimits
    (μ ν : Measure Ω) (ρ : Measure Θ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (cylinders : Set (Set Ω))
    (hgen : ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom cylinders)
    (hpi : IsPiSystem cylinders)
    (hlim : CommonConditionalLimits μ ν ρ cylinders) : μ = ν := by
  refine MeasureTheory.ext_of_generate_finite cylinders hgen hpi ?_ (by simp)
  intro A hA
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)]
  obtain ⟨f, g, hf, hg, hfg⟩ := hlim.sequences A hA
  have heq : ∀ᵐ z ∂ρ, (μ A).toReal = (ν A).toReal := by
    filter_upwards [hf, hg, hfg] with z hzf hzg hzfg
    exact tendsto_nhds_unique (Tendsto.congr' hzfg hzf) hzg
  exact heq.exists.choose_spec

/-- Specialization to the ordinary finite-coordinate cylinders on a product
measurable space.  For configurations on edges, take every coordinate type
to be `Bool` (or another two-element measurable type). -/
theorem measure_eq_pi_of_commonConditionalLimits
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ ν : Measure (∀ i, α i)) (ρ : Measure Ξ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hlim : CommonConditionalLimits μ ν ρ (measurableCylinders α)) : μ = ν := by
  exact measure_eq_of_commonConditionalLimits μ ν ρ (measurableCylinders α)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders hlim

/-- Any two members of a probability family with the common conditional-limit
property are equal. -/
theorem pairwise_eq_of_commonConditionalLimits
    (S : Set (Measure Ω)) (ρ : Measure Θ) (cylinders : Set (Set Ω))
    [IsProbabilityMeasure ρ]
    (hprob : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hgen : ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom cylinders)
    (hpi : IsPiSystem cylinders)
    (hlim : ∀ μ ∈ S, ∀ ν ∈ S, CommonConditionalLimits μ ν ρ cylinders) :
    ∀ μ ∈ S, ∀ ν ∈ S, μ = ν := by
  intro μ hμ ν hν
  let _ : IsProbabilityMeasure μ := hprob μ hμ
  let _ : IsProbabilityMeasure ν := hprob ν hν
  exact measure_eq_of_commonConditionalLimits μ ν ρ cylinders hgen hpi
    (hlim μ hμ ν hν)

/-- A nonempty probability family with common conditional limits is a
singleton.  Nonempty is separate, as needed when the family consists of the
extremal Gibbs measures and existence is supplied by Gibbs theory. -/
theorem exists_eq_singleton_of_commonConditionalLimits
    (S : Set (Measure Ω)) (ρ : Measure Θ) (cylinders : Set (Set Ω))
    [IsProbabilityMeasure ρ]
    (hprob : ∀ μ ∈ S, IsProbabilityMeasure μ)
    (hgen : ‹MeasurableSpace Ω› = MeasurableSpace.generateFrom cylinders)
    (hpi : IsPiSystem cylinders)
    (hlim : ∀ μ ∈ S, ∀ ν ∈ S, CommonConditionalLimits μ ν ρ cylinders)
    (hne : S.Nonempty) : ∃ μ, S = {μ} := by
  obtain ⟨μ₀, hμ₀⟩ := hne
  refine ⟨μ₀, Set.Subset.antisymm ?_ ?_⟩
  · intro μ hμ
    rw [Set.mem_singleton_iff]
    exact pairwise_eq_of_commonConditionalLimits S ρ cylinders hprob hgen hpi
      hlim μ hμ μ₀ hμ₀
  · exact Set.singleton_subset_iff.mpr hμ₀

end FK
