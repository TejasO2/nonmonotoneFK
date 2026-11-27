import FK.SpecificationDeviation
import FK.ConditionallyIndependentOrderedCoupling

/-!
# Final cylinder step for the fibred Theorem 5.1 argument

If the two exterior conditional probability sequences, evaluated on the two
lower coordinates of an ordered triple, are eventually equal and converge to
their respective tail conditional expectations, then their limits agree almost
surely. Integrating against the first two marginals identifies the two
unconditional masses. No tail zero--one law is used.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FK.InfiniteVolume

universe u v

variable {E : Type u} [Countable E]
variable {Θ : Type v} [MeasurableSpace Θ]

/-- Integrate two tail conditional expectations which agree almost surely on a
coupling. This is the final analytic step of the common-fibre argument. -/
theorem measureReal_eq_of_integral_condExp_ae_eq
    (γ : ProbabilityMeasure Θ)
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (X Y : Θ → Configuration E) (hX : Measurable X) (hY : Measurable Y)
    (hXμ : (γ : Measure Θ).map X = (μ₁ : Measure (Configuration E)))
    (hYμ : (γ : Measure Θ).map Y = (μ₂ : Measure (Configuration E)))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hlim : ∀ᵐ z ∂(γ : Measure Θ),
      ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) (X z) =
        ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) (Y z)) :
    (μ₁ : Measure (Configuration E)).real A =
      (μ₂ : Measure (Configuration E)).real A := by
  let F : Θ → ℝ := fun z ↦
    ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
      FKLimit.tailSigma]) (X z)
  let G : Θ → ℝ := fun z ↦
    ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
      FKLimit.tailSigma]) (Y z)
  have hF : AEStronglyMeasurable F (γ : Measure Θ) := by
    apply AEStronglyMeasurable.comp_aemeasurable _ hX.aemeasurable
    rw [hXμ]
    exact (stronglyMeasurable_condExp.mono FKLimit.tailSigma_le).aestronglyMeasurable
  have hG : AEStronglyMeasurable G (γ : Measure Θ) := by
    apply AEStronglyMeasurable.comp_aemeasurable _ hY.aemeasurable
    rw [hYμ]
    exact (stronglyMeasurable_condExp.mono FKLimit.tailSigma_le).aestronglyMeasurable
  have hIntEq : ∫ z, F z ∂(γ : Measure Θ) = ∫ z, G z ∂(γ : Measure Θ) :=
    integral_congr_ae hlim
  have hIntF : ∫ z, F z ∂(γ : Measure Θ) =
      ∫ ω, ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
        FKLimit.tailSigma]) ω ∂(μ₁ : Measure (Configuration E)) := by
    change ∫ z, (fun ω ↦
      ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
        FKLimit.tailSigma]) ω) (X z) ∂(γ : Measure Θ) = _
    rw [← hXμ]
    exact (integral_map (μ := (γ : Measure Θ)) (φ := X) hX.aemeasurable
      ((stronglyMeasurable_condExp.mono FKLimit.tailSigma_le).aestronglyMeasurable)).symm
  have hIntG : ∫ z, G z ∂(γ : Measure Θ) =
      ∫ ω, ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
        FKLimit.tailSigma]) ω ∂(μ₂ : Measure (Configuration E)) := by
    change ∫ z, (fun ω ↦
      ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
        FKLimit.tailSigma]) ω) (Y z) ∂(γ : Measure Θ) = _
    rw [← hYμ]
    exact (integral_map (μ := (γ : Measure Θ)) (φ := Y) hY.aemeasurable
      ((stronglyMeasurable_condExp.mono FKLimit.tailSigma_le).aestronglyMeasurable)).symm
  have htower₁ : ∫ ω, ((μ₁ : Measure (Configuration E))[
      A.indicator (fun _ ↦ (1 : ℝ)) | FKLimit.tailSigma]) ω
        ∂(μ₁ : Measure (Configuration E)) =
      (μ₁ : Measure (Configuration E)).real A := by
    rw [integral_condExp FKLimit.tailSigma_le,
      integral_indicator_const (1 : ℝ) hA]
    simp
  have htower₂ : ∫ ω, ((μ₂ : Measure (Configuration E))[
      A.indicator (fun _ ↦ (1 : ℝ)) | FKLimit.tailSigma]) ω
        ∂(μ₂ : Measure (Configuration E)) =
      (μ₂ : Measure (Configuration E)).real A := by
    rw [integral_condExp FKLimit.tailSigma_le,
      integral_indicator_const (1 : ℝ) hA]
    simp
  rw [← htower₁, ← htower₂, ← hIntF, ← hIntG]
  exact hIntEq

/-- Two eventually equal random exterior sequences with tail-conditional
limits have almost surely equal limits. -/
theorem ae_condExp_eq_of_tendsto_eventuallyEq
    (γ : ProbabilityMeasure Θ)
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (X Y : Θ → Configuration E)
    {A : Set (Configuration E)} (M N : ℕ → Θ → ℝ)
    (hlim₁ : ∀ᵐ z ∂(γ : Measure Θ), Tendsto (fun n ↦ M n z) atTop
      (𝓝 (((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
        FKLimit.tailSigma]) (X z))))
    (hlim₂ : ∀ᵐ z ∂(γ : Measure Θ), Tendsto (fun n ↦ N n z) atTop
      (𝓝 (((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
        FKLimit.tailSigma]) (Y z))))
    (heq : ∀ᵐ z ∂(γ : Measure Θ),
      (fun n ↦ M n z) =ᶠ[atTop] (fun n ↦ N n z)) :
    ∀ᵐ z ∂(γ : Measure Θ),
      ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) (X z) =
        ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) (Y z) := by
  filter_upwards [hlim₁, hlim₂, heq] with z hz₁ hz₂ hzeq
  exact tendsto_nhds_unique (hz₁.congr' hzeq) hz₂

/-- Final cylinder equality for an ordered triple. -/
theorem measureReal_eq_orderedTriple_of_tendsto_eventuallyEq
    (γ : ProbabilityMeasure
      (Configuration E × Configuration E × Configuration E))
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (hm₁ : γ.map (fun z ↦ z.1) = μ₁)
    (hm₂ : γ.map (fun z ↦ z.2.1) = μ₂)
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (M N : ℕ → Configuration E × Configuration E × Configuration E → ℝ)
    (hlim₁ : ∀ᵐ z ∂(γ : Measure
      (Configuration E × Configuration E × Configuration E)),
      Tendsto (fun n ↦ M n z) atTop
        (𝓝 (((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) z.1)))
    (hlim₂ : ∀ᵐ z ∂(γ : Measure
      (Configuration E × Configuration E × Configuration E)),
      Tendsto (fun n ↦ N n z) atTop
        (𝓝 (((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) z.2.1)))
    (heq : ∀ᵐ z ∂(γ : Measure
      (Configuration E × Configuration E × Configuration E)),
      (fun n ↦ M n z) =ᶠ[atTop] (fun n ↦ N n z)) :
    (μ₁ : Measure (Configuration E)).real A =
      (μ₂ : Measure (Configuration E)).real A := by
  have hm₁' : (γ : Measure
      (Configuration E × Configuration E × Configuration E)).map (fun z ↦ z.1) =
      (μ₁ : Measure (Configuration E)) := by
    rw [← ProbabilityMeasure.toMeasure_map]
    exact congrArg Subtype.val hm₁
  have hm₂' : (γ : Measure
      (Configuration E × Configuration E × Configuration E)).map (fun z ↦ z.2.1) =
      (μ₂ : Measure (Configuration E)) := by
    rw [← ProbabilityMeasure.toMeasure_map]
    exact congrArg Subtype.val hm₂
  exact measureReal_eq_of_integral_condExp_ae_eq γ μ₁ μ₂
    (fun z ↦ z.1) (fun z ↦ z.2.1) measurable_fst measurable_snd.fst hm₁' hm₂' hA
    (ae_condExp_eq_of_tendsto_eventuallyEq γ μ₁ μ₂ (fun z ↦ z.1) (fun z ↦ z.2.1)
      M N hlim₁ hlim₂ heq)

/-- The exact output needed from the fixed-fibre common-limit theorem. For
each finite-support cylinder, two real sequences on the ordered triple have
the respective tail-conditional limits and agree eventually almost surely. -/
def OrderedTripleFibreCylinderLimits
    (γ : ProbabilityMeasure
      (Configuration E × Configuration E × Configuration E))
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∀ (S : Finset E) (A : Set (Configuration E)),
    FKLimit.DependsOnCoordinates A S →
    ∃ M N : ℕ → Configuration E × Configuration E × Configuration E → ℝ,
      (∀ᵐ z ∂(γ : Measure
        (Configuration E × Configuration E × Configuration E)),
        Tendsto (fun n ↦ M n z) atTop
          (𝓝 (((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
            FKLimit.tailSigma]) z.1))) ∧
      (∀ᵐ z ∂(γ : Measure
        (Configuration E × Configuration E × Configuration E)),
        Tendsto (fun n ↦ N n z) atTop
          (𝓝 (((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
            FKLimit.tailSigma]) z.2.1))) ∧
      (∀ᵐ z ∂(γ : Measure
        (Configuration E × Configuration E × Configuration E)),
        (fun n ↦ M n z) =ᶠ[atTop] (fun n ↦ N n z))

/-- All-cylinder form. Each cylinder has its own random region family and its
own support threshold, exactly as in the fibre common-limit theorem. -/
theorem probabilityMeasure_eq_of_orderedTriple_fibreCylinderLimits
    (γ : ProbabilityMeasure
      (Configuration E × Configuration E × Configuration E))
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (hm₁ : γ.map (fun z ↦ z.1) = μ₁)
    (hm₂ : γ.map (fun z ↦ z.2.1) = μ₂)
    (hcyl : OrderedTripleFibreCylinderLimits γ μ₁ μ₂) :
    μ₁ = μ₂ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_forall_real_dependsOn
  intro S A hAS
  obtain ⟨M, N, hlim₁, hlim₂, heq⟩ := hcyl S A hAS
  exact measureReal_eq_orderedTriple_of_tendsto_eventuallyEq γ μ₁ μ₂ hm₁ hm₂
    hAS.measurableSet M N hlim₁ hlim₂ heq

/-- Region-explicit form of the fixed-fibre input.  `T n η` is the actual
finite edge region in the fixed configuration `η`; `g (T n η)` is the common
free finite-region value after the cylinder support has entered the region.
The two long limits are tail conditional probabilities, not unconditional
masses, so no tail-zero-one assertion is encoded here. -/
def OrderedTripleRegionCylinderLimits
    (γ : ProbabilityMeasure
      (Configuration E × Configuration E × Configuration E))
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (T : ℕ → Configuration E → Finset E) (g : Finset E → ℝ) : Prop :=
  ∀ (S : Finset E) (A : Set (Configuration E)),
    FKLimit.DependsOnCoordinates A S →
    (∀ᵐ z ∂(γ : Measure
      (Configuration E × Configuration E × Configuration E)),
      Tendsto (fun n ↦
        ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.outsideSigma (T n z.2.2)]) z.1) atTop
        (𝓝 (((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) z.1))) ∧
    (∀ᵐ z ∂(γ : Measure
      (Configuration E × Configuration E × Configuration E)),
      Tendsto (fun n ↦
        ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.outsideSigma (T n z.2.2)]) z.2.1) atTop
        (𝓝 (((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.tailSigma]) z.2.1))) ∧
    (∀ᵐ z ∂(γ : Measure
      (Configuration E × Configuration E × Configuration E)),
      ∀ᶠ n in atTop,
        ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.outsideSigma (T n z.2.2)]) z.1 = g (T n z.2.2) ∧
        ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
          FKLimit.outsideSigma (T n z.2.2)]) z.2.1 = g (T n z.2.2))

/-- Forget the concrete finite-region presentation after extracting eventual
agreement of the two exterior sequences. -/
lemma orderedTripleFibreCylinderLimits_of_region
    (γ : ProbabilityMeasure
      (Configuration E × Configuration E × Configuration E))
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (T : ℕ → Configuration E → Finset E) (g : Finset E → ℝ)
    (h : OrderedTripleRegionCylinderLimits γ μ₁ μ₂ T g) :
    OrderedTripleFibreCylinderLimits γ μ₁ μ₂ := by
  intro S A hAS
  obtain ⟨hlim₁, hlim₂, hg⟩ := h S A hAS
  refine ⟨
    (fun n z ↦ ((μ₁ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
      FKLimit.outsideSigma (T n z.2.2)]) z.1),
    (fun n z ↦ ((μ₂ : Measure (Configuration E))[A.indicator (fun _ ↦ (1 : ℝ)) |
      FKLimit.outsideSigma (T n z.2.2)]) z.2.1), hlim₁, hlim₂, ?_⟩
  filter_upwards [hg] with z hz
  filter_upwards [hz] with n hn
  exact hn.1.trans hn.2.symm

/-- Cylinder conclusion directly from region-edge `Finset` exhaustions and a
common free-region value. -/
theorem probabilityMeasure_eq_of_orderedTriple_regionCylinderLimits
    (γ : ProbabilityMeasure
      (Configuration E × Configuration E × Configuration E))
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (hm₁ : γ.map (fun z ↦ z.1) = μ₁)
    (hm₂ : γ.map (fun z ↦ z.2.1) = μ₂)
    (T : ℕ → Configuration E → Finset E) (g : Finset E → ℝ)
    (h : OrderedTripleRegionCylinderLimits γ μ₁ μ₂ T g) :
    μ₁ = μ₂ :=
  probabilityMeasure_eq_of_orderedTriple_fibreCylinderLimits γ μ₁ μ₂ hm₁ hm₂
    (orderedTripleFibreCylinderLimits_of_region γ μ₁ μ₂ T g h)

end FK.InfiniteVolume
