import FK.ConfigurationTail
import FK.InfiniteVolume

/-!
# Extremality and tail triviality

This file proves the conditioning part of the extremal-Gibbs argument.  A
probability measure which cannot be decomposed nontrivially inside a family is
zero--one on a sigma-algebra, provided conditioning the measure on each event
of positive mass in that sigma-algebra stays in the family.  No independence
or FKG assumption is used.
-/

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

namespace FK

/-- Conditioning commutes with pushforward by a measurable function. -/
lemma map_cond {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {T : Set β} (hT : MeasurableSet T) :
    Measure.map f μ[|f ⁻¹' T] = (Measure.map f μ)[|T] := by
  simp only [ProbabilityTheory.cond]
  rw [Measure.map_smul _ hf.aemeasurable, ← Measure.restrict_map hf hT,
    Measure.map_apply hf hT]

/-- Restricting a comp-product to `T ×ˢ univ` restricts precisely its left
marginal to `T`. -/
lemma restrict_compProd_prod_univ {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) [SFinite μ]
    (κ : ProbabilityTheory.Kernel α β) [IsSFiniteKernel κ]
    {T : Set α} (hT : MeasurableSet T) :
    (μ ⊗ₘ κ).restrict (T ×ˢ Set.univ) = (μ.restrict T) ⊗ₘ κ := by
  ext s hs
  rw [Measure.restrict_apply hs,
    Measure.compProd_apply (hs.inter (hT.prod MeasurableSet.univ)),
    Measure.compProd_apply hs]
  rw [← MeasureTheory.lintegral_indicator hT]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ T
  · simp [ha]
  · simp [ha]

/-- Conditioning a Markov comp-product on an event which depends only on its
left coordinate conditions the left marginal and leaves the kernel unchanged. -/
lemma cond_compProd_prod_univ {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) [SFinite μ]
    (κ : ProbabilityTheory.Kernel α β) [IsMarkovKernel κ]
    {T : Set α} (hT : MeasurableSet T) :
    (μ ⊗ₘ κ)[|T ×ˢ Set.univ] = μ[|T] ⊗ₘ κ := by
  have hmass : (μ ⊗ₘ κ) (T ×ˢ Set.univ) = μ T := by
    rw [Measure.compProd_apply_prod hT MeasurableSet.univ]
    simp
  simp only [ProbabilityTheory.cond]
  rw [hmass, restrict_compProd_prod_univ μ κ hT, Measure.compProd_smul_left]

/-- A Markov-kernel mixture is constant if all of its component laws are
constant, with no measurability assumption on the componentwise equalities. -/
lemma bind_eq_of_forall_kernel_eq {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] (ρ : Measure ι) [IsProbabilityMeasure ρ]
    (κ : ProbabilityTheory.Kernel ι Ω) [IsMarkovKernel κ] (μ : Measure Ω)
    (hκ : ∀ x, κ x = μ) : Measure.bind ρ κ = μ := by
  ext A hA
  rw [Measure.bind_apply hA κ.aemeasurable]
  calc
    (∫⁻ x, κ x A ∂ρ) = ∫⁻ _x, μ A ∂ρ := lintegral_congr fun x ↦ by rw [hκ x]
    _ = μ A := by simp

/-- A positive-mass conditioning operation packaged as a probability measure. -/
noncomputable def condProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA : (μ : Measure Ω) A ≠ 0) :
    ProbabilityMeasure Ω :=
  ⟨(μ : Measure Ω)[|A], ProbabilityTheory.cond_isProbabilityMeasure hA⟩

@[simp] lemma coe_condProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (A : Set Ω) (hA : (μ : Measure Ω) A ≠ 0) :
    (condProbabilityMeasure μ A hA : Measure Ω) = (μ : Measure Ω)[|A] := rfl

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- `μ` is extremal in `S`: nontrivial convex decompositions with both
components in `S` are impossible.  Requiring only the left component to equal
`μ` is equivalent to requiring both, by commutativity of addition. -/
def IsExtremalIn (S : Set (@Measure Ω m₀)) (μ : @Measure Ω m₀) : Prop :=
  μ ∈ S ∧ ∀ ν ∈ S, ∀ ρ ∈ S, ∀ c d : ℝ≥0∞,
    c ≠ 0 → d ≠ 0 → c + d = 1 → μ = c • ν + d • ρ → ν = μ

/-- Simplex uniqueness: if every extremal law in `S` is the specified `μ₀`,
then every Markov-kernel mixture of extremal laws is also `μ₀`. -/
lemma eq_of_isExtremalIn_kernelMixture {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] {S : Set (Measure Ω)} {μ₀ : Measure Ω}
    (hunique : ∀ ν, IsExtremalIn S ν → ν = μ₀)
    (ρ : Measure ι) [IsProbabilityMeasure ρ]
    (κ : ProbabilityTheory.Kernel ι Ω) [IsMarkovKernel κ]
    (hκ : ∀ x, IsExtremalIn S (κ x)) : Measure.bind ρ κ = μ₀ :=
  bind_eq_of_forall_kernel_eq ρ κ μ₀ fun x ↦ hunique (κ x) (hκ x)

/-- Multiplying a conditional probability by the mass of its conditioning
set recovers the restriction.  This also holds at mass zero. -/
lemma mass_smul_cond {μ : @Measure Ω m₀} [IsFiniteMeasure μ] (A : Set Ω) :
    μ A • μ[|A] = μ.restrict A := by
  rw [ProbabilityTheory.cond, smul_smul]
  by_cases hA : μ A = 0
  · simp only [hA, zero_mul, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hA).symm
  · rw [ENNReal.mul_inv_cancel hA (measure_ne_top μ A), one_smul]

/-- The decomposition of a probability measure into its conditional laws on
an event and its complement. -/
lemma measure_eq_mass_smul_cond_add_compl {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : MeasurableSet[m₀] A) :
    μ = μ A • μ[|A] + μ Aᶜ • μ[|Aᶜ] := by
  rw [mass_smul_cond (μ := μ) A, mass_smul_cond (μ := μ) Aᶜ]
  exact (Measure.restrict_add_restrict_compl (μ := μ) hA).symm

/-- Extremality gives a zero--one law on every sigma-algebra whose positive-
mass events admit conditioning within the ambient family. -/
theorem zeroOneOn_of_extremalIn
    {m₁ : MeasurableSpace Ω} (hm : m₁ ≤ m₀)
    {S : Set (@Measure Ω m₀)} {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    (hext : IsExtremalIn S μ)
    (hcond : ∀ A : Set Ω, MeasurableSet[m₁] A → μ A ≠ 0 →
      @ProbabilityTheory.cond Ω m₀ μ A ∈ S) :
    ZeroOneOn m₁ μ := by
  intro A hA
  by_contra h
  push Not at h
  have hA0 : μ A ≠ 0 := h.1
  have hA1 : μ A ≠ 1 := h.2
  have hAmeas : MeasurableSet[m₀] A := hm A hA
  have hAc0 : μ Aᶜ ≠ 0 := by
    rwa [ne_eq, prob_compl_eq_zero_iff hAmeas]
  have hsum : μ A + μ Aᶜ = 1 := by
    have h := congrArg (fun ν : @Measure Ω m₀ ↦ ν Set.univ)
      (Measure.restrict_add_restrict_compl (μ := μ) hAmeas)
    simpa [Measure.restrict_apply hAmeas, Measure.restrict_apply hAmeas.compl,
      Measure.add_apply] using h
  have hν : μ[|A] = μ :=
    hext.2 μ[|A] (hcond A hA hA0) μ[|Aᶜ]
      (hcond Aᶜ hA.compl hAc0) (μ A) (μ Aᶜ) hA0 hAc0 hsum
      (measure_eq_mass_smul_cond_add_compl hAmeas)
  have hone : μ A = 1 := by
    calc
      μ A = μ[A | A] := (congrArg (fun ν : @Measure Ω m₀ ↦ ν A) hν).symm
      _ = 1 := ProbabilityTheory.cond_apply_self hA0 (measure_ne_top μ A)
  exact hA1 hone

end FK


namespace FK.InfiniteVolume.FiniteBox

open FK

universe u v

variable {E : Type u}

local instance exteriorBoundaryMeasurableSpace (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤

local instance exteriorFiniteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- Conditioning a DLR law on an event depending only on the exterior of the
box preserves the same exact FK specification.  Positive mass is used only to
package the conditioned law as a probability measure. -/
theorem isDLR_cond_exterior {q p : NNReal} (B : FiniteBox E)
    (hq : 0 < q) (hp : p ≤ 1) (α : B.Exterior → B.BoundaryPartition)
    (hα : Measurable α) (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) {T : Set B.Exterior} (hT : MeasurableSet T)
    (hμT : (μ : Measure (Configuration E))
      ((fun ω ↦ (B.splitEquiv ω).1) ⁻¹' T) ≠ 0) :
    B.IsDLR hq hp α hα
      (FK.condProbabilityMeasure μ ((fun ω ↦ (B.splitEquiv ω).1) ⁻¹' T) hμT) := by
  let f : Configuration E → B.Exterior := fun ω ↦ (B.splitEquiv ω).1
  have hf : Measurable f := measurable_fst.comp B.splitEquiv.measurable
  have hpre : B.splitEquiv ⁻¹' (T ×ˢ Set.univ) = f ⁻¹' T := by
    ext ω
    simp [f]
  have hleft : Measure.map B.splitEquiv ((μ : Measure (Configuration E))[|f ⁻¹' T]) =
      (Measure.map B.splitEquiv (μ : Measure (Configuration E)))[|T ×ˢ Set.univ] := by
    have hmap := FK.map_cond (μ : Measure (Configuration E)) B.splitEquiv.measurable
      (hT.prod MeasurableSet.univ)
    rwa [hpre] at hmap
  change Measure.map B.splitEquiv ((μ : Measure (Configuration E))[|f ⁻¹' T]) =
    (B.exteriorMeasure
      (FK.condProbabilityMeasure μ (f ⁻¹' T) hμT) : Measure B.Exterior) ⊗ₘ
        B.fkKernel hq hp α hα
  rw [hleft, hμ, FK.cond_compProd_prod_univ _ _ hT]
  congr 1
  change (Measure.map f (μ : Measure (Configuration E)))[|T] =
    Measure.map f ((μ : Measure (Configuration E))[|f ⁻¹' T])
  exact (FK.map_cond (μ : Measure (Configuration E)) hf hT).symm

/-- Complement-free formulation of `isDLR_cond_exterior` using the exterior
sigma-algebra from `ConfigurationTail`. -/
theorem isDLR_cond_of_outside {q p : NNReal} (B : FiniteBox E)
    (hq : 0 < q) (hp : p ≤ 1) (α : B.Exterior → B.BoundaryPartition)
    (hα : Measurable α) (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ) {A : Set (Configuration E)}
    (hA : MeasurableSet[FKLimit.outsideSigma B.edges] A)
    (hμA : (μ : Measure (Configuration E)) A ≠ 0) :
    B.IsDLR hq hp α hα (FK.condProbabilityMeasure μ A hμA) := by
  obtain ⟨T, hT, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hA
  change FKLimit.exteriorRestriction B.edges ⁻¹' T = A at hpre
  change (fun ω ↦ (B.splitEquiv ω).1) ⁻¹' T = A at hpre
  subst A
  exact isDLR_cond_exterior B hq hp α hα μ hμ hT hμA

end FK.InfiniteVolume.FiniteBox

namespace FK.InfiniteVolume

open FK

universe u v

/-- A DLR family is closed under conditioning on a positive-mass event in the
exact exterior tail. -/
theorem mem_dlrMeasures_cond_tail {E : Type u} (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    {A : Set (Configuration E)} (hA : MeasurableSet[FKLimit.tailSigma] A)
    (hμA : (μ : Measure (Configuration E)) A ≠ 0) :
    FK.condProbabilityMeasure μ A hμA ∈ DLRMeasures exh Φ hq hp := by
  intro n
  exact FiniteBox.isDLR_cond_of_outside (exh.box n) hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ (hμ n)
    (FKLimit.tailSigma_le_outsideSigma (exh.box n).edges A hA) hμA

/-- Extremal DLR laws are tail trivial.  The family of measures is the image
of the actual bundled DLR probability measures under coercion to `Measure`.
This removes tail triviality as a separate hypothesis: only conditioning
extremality within the DLR simplex is required. -/
theorem zeroOneOn_tailSigma_of_extremal_dlr {E : Type u}
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun ν : ProbabilityMeasure (Configuration E) ↦ (ν : Measure (Configuration E))) ''
        DLRMeasures exh Φ hq hp) (μ : Measure (Configuration E))) :
    FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (Configuration E)) := by
  apply FK.zeroOneOn_of_extremalIn FKLimit.tailSigma_le hext
  intro A hA hpos
  exact ⟨FK.condProbabilityMeasure μ A hpos,
    mem_dlrMeasures_cond_tail exh Φ hq hp μ hμ hA hpos, rfl⟩

/-- Uniqueness from common backward conditional limits, with both tail-
triviality inputs derived from extremality in the actual DLR simplex. -/
theorem measure_eq_of_backwardConditionalLimits_of_extremal_dlr
    {E Θ : Type u} [MeasurableSpace Θ]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hextμ : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦ (η : Measure (Configuration E))) ''
        DLRMeasures exh Φ hq hp) (μ : Measure (Configuration E)))
    (hextν : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦ (η : Measure (Configuration E))) ''
        DLRMeasures exh Φ hq hp) (ν : Measure (Configuration E)))
    (ρ : Measure Θ) [IsProbabilityMeasure ρ]
    (X Y : Θ → Configuration E) (hX : Measurable X) (hY : Measurable Y)
    (hXμ : Measure.map X ρ = (μ : Measure (Configuration E)))
    (hYν : Measure.map Y ρ = (ν : Measure (Configuration E)))
    (cylinders : Set (Set (Configuration E)))
    (hcyl : ∀ A ∈ cylinders, MeasurableSet A)
    (hgen : (MeasurableSpace.pi : MeasurableSpace (Configuration E)) =
      MeasurableSpace.generateFrom cylinders)
    (hpi : IsPiSystem cylinders)
    (hseq : ∀ A ∈ cylinders, ∃ f g : ℕ → Θ → ℝ,
      (∀ᵐ z ∂ρ, Tendsto (fun n ↦ f n z) atTop
        (𝓝 (((μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) (X z)))) ∧
      (∀ᵐ z ∂ρ, Tendsto (fun n ↦ g n z) atTop
        (𝓝 (((ν : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) (Y z)))) ∧
      (∀ᵐ z ∂ρ, (fun n ↦ f n z) =ᶠ[atTop] (fun n ↦ g n z))) :
    (μ : Measure (Configuration E)) = (ν : Measure (Configuration E)) := by
  exact FK.measure_eq_of_backwardConditionalLimits_of_zeroOneOn
    (μ : Measure (Configuration E)) (ν : Measure (Configuration E)) ρ
    FKLimit.tailSigma FKLimit.tailSigma_le X Y hX hY hXμ hYν
    (zeroOneOn_tailSigma_of_extremal_dlr exh Φ hq hp μ hμ hextμ)
    (zeroOneOn_tailSigma_of_extremal_dlr exh Φ hq hp ν hν hextν)
    cylinders hcyl hgen hpi hseq

end FK.InfiniteVolume
