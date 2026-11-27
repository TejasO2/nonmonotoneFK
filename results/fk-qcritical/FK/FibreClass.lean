import FK.FibreCylinder

/-!
# Class packaging for the fibred cylinder criterion

These are deliberately generic packaging lemmas, not claims that the fibre
common-limit input has already been proved. Once the ordered splice supplies
`OrderedTripleFibreCylinderLimits` for every pair in a class, the class is a
subsingleton and, separately, a singleton when nonempty.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FK.InfiniteVolume

universe u

variable {E : Type u} [Countable E]

/-- Every pair carrying an ordered-triple fibre cylinder limit is equal. -/
theorem eq_of_exists_orderedTriple_fibreCylinderLimits
    {𝒢 : Set (ProbabilityMeasure (Configuration E))}
    (h : ∀ μ₁ ∈ 𝒢, ∀ μ₂ ∈ 𝒢,
      ∃ γ : ProbabilityMeasure
        (Configuration E × Configuration E × Configuration E),
        γ.map (fun z ↦ z.1) = μ₁ ∧ γ.map (fun z ↦ z.2.1) = μ₂ ∧
          OrderedTripleFibreCylinderLimits γ μ₁ μ₂) :
    ∀ μ₁ ∈ 𝒢, ∀ μ₂ ∈ 𝒢, μ₁ = μ₂ := by
  intro μ₁ hμ₁ μ₂ hμ₂
  obtain ⟨γ, hm₁, hm₂, hcyl⟩ := h μ₁ hμ₁ μ₂ hμ₂
  exact probabilityMeasure_eq_of_orderedTriple_fibreCylinderLimits
    γ μ₁ μ₂ hm₁ hm₂ hcyl

/-- The subtype of laws in a class with pairwise fibre cylinder limits is a
subsingleton. No existence assertion is made. -/
theorem subsingleton_of_exists_orderedTriple_fibreCylinderLimits
    {𝒢 : Set (ProbabilityMeasure (Configuration E))}
    (h : ∀ μ₁ ∈ 𝒢, ∀ μ₂ ∈ 𝒢,
      ∃ γ : ProbabilityMeasure
        (Configuration E × Configuration E × Configuration E),
        γ.map (fun z ↦ z.1) = μ₁ ∧ γ.map (fun z ↦ z.2.1) = μ₂ ∧
          OrderedTripleFibreCylinderLimits γ μ₁ μ₂) :
    Subsingleton 𝒢 := by
  constructor
  intro μ₁ μ₂
  apply Subtype.ext
  exact eq_of_exists_orderedTriple_fibreCylinderLimits h μ₁ μ₁.2 μ₂ μ₂.2

/-- A nonempty class with pairwise fibre cylinder limits is exactly a
singleton. Nonemptiness is a separate conclusion hypothesis, so this theorem
never manufactures a DLR law. -/
theorem exists_eq_singleton_of_exists_orderedTriple_fibreCylinderLimits
    {𝒢 : Set (ProbabilityMeasure (Configuration E))}
    (h : ∀ μ₁ ∈ 𝒢, ∀ μ₂ ∈ 𝒢,
      ∃ γ : ProbabilityMeasure
        (Configuration E × Configuration E × Configuration E),
        γ.map (fun z ↦ z.1) = μ₁ ∧ γ.map (fun z ↦ z.2.1) = μ₂ ∧
          OrderedTripleFibreCylinderLimits γ μ₁ μ₂)
    (hne : 𝒢.Nonempty) :
    ∃ μ₀, 𝒢 = {μ₀} := by
  obtain ⟨μ₀, hμ₀⟩ := hne
  refine ⟨μ₀, Set.eq_singleton_iff_unique_mem.mpr ⟨hμ₀, ?_⟩⟩
  intro μ hμ
  exact eq_of_exists_orderedTriple_fibreCylinderLimits h μ hμ μ₀ hμ₀

end FK.InfiniteVolume
