import FK.ExtremalTail

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace FK

/-- A real function which is almost-everywhere strongly measurable for every
member of a decreasing sequence of sigma-algebras has one common representative
measurable for their infimum. -/
theorem aestronglyMeasurable_iInf_of_antitone
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
    (f : Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable[G n] f μ) :
    AEStronglyMeasurable[⨅ n, G n] f μ := by
  let r : ℕ → Ω → ℝ := fun n ↦ (hf n).mk f
  have hr : ∀ n, StronglyMeasurable[G n] (r n) := fun n ↦ (hf n).stronglyMeasurable_mk
  have hrf : ∀ n, r n =ᵐ[μ] f := fun n ↦ (hf n).ae_eq_mk.symm
  have hall : ∀ᵐ x ∂μ, ∀ n, r n x = f x := by
    rw [ae_all_iff]
    exact hrf
  let L : Ω → ℝ := fun x ↦ liminf (fun n ↦ r n x) atTop
  have hL : StronglyMeasurable[⨅ n, G n] L := by
    apply Measurable.stronglyMeasurable
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro k
    have htail : ∀ n : ℕ, StronglyMeasurable[G k] (fun x ↦ r (n + k) x) := by
      intro n
      exact (hr (n + k)).mono (hG (Nat.le_add_left k n))
    have hm : Measurable[G k] (fun x ↦ liminf (fun n ↦ r (n + k) x) atTop) := by
      apply Measurable.liminf
      intro n
      exact (htail n).measurable
    have heq : (fun x ↦ liminf (fun n ↦ r (n + k) x) atTop) = L := by
      funext x
      exact liminf_nat_add (fun n ↦ r n x) k
    rw [← heq]
    exact hm hs
  refine ⟨L, hL, ?_⟩
  filter_upwards [hall] with x hx
  have ht : Tendsto (fun n ↦ r n x) atTop (𝓝 (f x)) := by
    simp only [hx]
    exact tendsto_const_nhds
  exact ht.liminf_eq.symm


/-- The decreasing sequence of `L²` spaces over a decreasing sequence of
sigma-algebras has the expected infimum. -/
theorem iInf_lpMeas_of_antitone
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) :
    (⨅ n, lpMeas ℝ ℝ (G n) 2 μ) = lpMeas ℝ ℝ (⨅ n, G n) 2 μ := by
  ext f
  simp only [Submodule.mem_iInf, mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · exact aestronglyMeasurable_iInf_of_antitone G hG f
  · intro hf n
    exact hf.mono (iInf_le G n)

/-- Lévy's decreasing projection theorem in an abstract real Hilbert space. -/
theorem tendsto_starProjection_iInf
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : ℕ → Submodule ℝ H) [∀ n, (U n).HasOrthogonalProjection]
    [(⨅ n, U n).HasOrthogonalProjection]
    (hU : Antitone U) (x : H) :
    Tendsto (fun n ↦ (U n).starProjection x) atTop
      (𝓝 ((⨅ n, U n).starProjection x)) := by
  have hW : Monotone (fun n ↦ (U n)ᗮ) := by
    intro m n hmn
    exact Submodule.orthogonal_le (hU hmn)
  have hlim := Submodule.starProjection_tendsto_closure_iSup
    (fun n ↦ (U n)ᗮ) hW x
  have hsub : (⨆ n, (U n)ᗮ).topologicalClosureᗮ = ⨅ n, U n := by
    calc
      (⨆ n, (U n)ᗮ).topologicalClosureᗮ = (⨆ n, (U n)ᗮ)ᗮ :=
        Submodule.orthogonal_closure _
      _ = ⨅ n, (U n)ᗮᗮ := (Submodule.iInf_orthogonal (fun n ↦ (U n)ᗮ)).symm
      _ = ⨅ n, U n := by simp only [Submodule.orthogonal_orthogonal]
  have htarget : x - (⨆ n, (U n)ᗮ).topologicalClosure.starProjection x =
      (⨅ n, U n).starProjection x := by
    have h := (Submodule.starProjection_orthogonal_val
      (K := (⨆ n, (U n)ᗮ).topologicalClosure) x).symm
    simpa only [← hsub] using h
  rw [← htarget]
  have heq : (fun n ↦ (U n).starProjection x) =
      fun n ↦ x - (U n)ᗮ.starProjection x := by
    funext n
    have h := Submodule.starProjection_orthogonal_val (K := (U n)ᗮ) x
    simpa only [Submodule.orthogonal_orthogonal] using h
  rw [heq]
  exact tendsto_const_nhds.sub hlim

/-- Downward `L²` convergence of the actual `condExpL2` projections. -/
theorem tendsto_condExpL2_iInf
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ] {G : ℕ → MeasurableSpace Ω}
    (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (hGm₀ : (⨅ n, G n) ≤ m₀) (x : Lp ℝ 2 μ) :
    Tendsto (fun n ↦ ((condExpL2 ℝ ℝ (hGm n) x : lpMeas ℝ ℝ (G n) 2 μ) : Lp ℝ 2 μ))
      atTop (𝓝 ((condExpL2 ℝ ℝ hGm₀ x : lpMeas ℝ ℝ (⨅ n, G n) 2 μ) : Lp ℝ 2 μ)) := by
  let _ : Fact ((⨅ n, G n) ≤ m₀) := ⟨hGm₀⟩
  let _ (n : ℕ) : Fact (G n ≤ m₀) := ⟨hGm n⟩
  let _ : (⨅ n, lpMeas ℝ ℝ (G n) 2 μ).HasOrthogonalProjection := by
    rw [iInf_lpMeas_of_antitone G hG]
    infer_instance
  have hlim := tendsto_starProjection_iInf
    (fun n ↦ lpMeas ℝ ℝ (G n) 2 μ) (fun m n hmn ↦ by
      intro f hf
      rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
      exact hf.mono (hG hmn)) x
  change Tendsto (fun n ↦ (lpMeas ℝ ℝ (G n) 2 μ).starProjection x) atTop
    (𝓝 ((lpMeas ℝ ℝ (⨅ n, G n) 2 μ).starProjection x))
  simpa only [iInf_lpMeas_of_antitone G hG] using hlim


/-- Ordinary conditional expectations of an `L²` real function converge in
`L²`, and hence in `L¹`, along a decreasing sequence of sigma-algebras. -/
theorem tendsto_eLpNorm_one_condExp_iInf_of_memLp_two
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ] {G : ℕ → MeasurableSpace Ω}
    (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (hGm₀ : (⨅ n, G n) ≤ m₀) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n ↦ eLpNorm (μ[f | G n] - μ[f | ⨅ n, G n]) 1 μ) atTop (𝓝 0) := by
  have hL2 := tendsto_condExpL2_iInf hG hGm hGm₀ hf.toLp
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n ↦ ((condExpL2 ℝ ℝ (hGm n) hf.toLp : lpMeas ℝ ℝ (G n) 2 μ) : Lp ℝ 2 μ))
    ((condExpL2 ℝ ℝ hGm₀ hf.toLp : lpMeas ℝ ℝ (⨅ n, G n) 2 μ) : Lp ℝ 2 μ)).mp hL2
  have hnorm' : Tendsto (fun n ↦ eLpNorm (μ[f | G n] - μ[f | ⨅ n, G n]) 2 μ)
      atTop (𝓝 0) := by
    apply hnorm.congr
    intro n
    apply eLpNorm_congr_ae
    exact (hf.condExpL2_ae_eq_condExp (hGm n)).sub
      (hf.condExpL2_ae_eq_condExp hGm₀)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm'
  · intro n
    exact bot_le
  · intro n
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

end FK

namespace FKLimit

/-- A cofinal sequence of finite edge sets has the exterior tail as the
infimum of its exterior sigma-algebras. -/
theorem iInf_outsideSigma_eq_tailSigma {E : Type*} (S : ℕ → Finset E)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n) :
    (⨅ n, outsideSigma (S n)) = tailSigma (E := E) := by
  apply le_antisymm
  · refine le_iInf fun T ↦ ?_
    obtain ⟨n, hn⟩ := hcof T
    exact (iInf_le (fun n ↦ outsideSigma (S n)) n).trans (outsideSigma_anti hn)
  · exact le_iInf fun n ↦ tailSigma_le_outsideSigma (S n)

/-- Downward `L¹` convergence to the actual exterior tail for an `L²`
function on finite edge configurations. -/
theorem tendsto_eLpNorm_one_condExp_outside_to_tail_of_memLp_two
    {E : Type*} {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {f : Configuration E → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun n ↦ eLpNorm (μ[f | outsideSigma (S n)] - μ[f | tailSigma]) 1 μ)
      atTop (𝓝 0) := by
  have hanti : Antitone (fun n ↦ outsideSigma (S n)) := by
    intro m n hmn
    exact outsideSigma_anti (hS hmn)
  have hle : ∀ n, outsideSigma (S n) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) := fun n ↦ outsideSigma_le _
  have hleInf : (⨅ n, outsideSigma (S n)) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    (iInf_le (fun n ↦ outsideSigma (S n)) 0).trans (hle 0)
  have h := FK.tendsto_eLpNorm_one_condExp_iInf_of_memLp_two
    hanti hle hleInf hf
  simpa only [iInf_outsideSigma_eq_tailSigma S hcof] using h

/-- The exterior-tail downward theorem for conditional probabilities. -/
theorem tendsto_eLpNorm_one_condExp_indicator_outside_to_tail
    {E : Type*} {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    Tendsto (fun n ↦ eLpNorm (μ⟦A | outsideSigma (S n)⟧ - μ⟦A | tailSigma⟧) 1 μ)
      atTop (𝓝 0) := by
  apply tendsto_eLpNorm_one_condExp_outside_to_tail_of_memLp_two S hS hcof
  exact memLp_indicator_const 2 hA.nullMeasurableSet (1 : ℝ) (Or.inr (measure_ne_top μ A))

end FKLimit

namespace FK.InfiniteVolume

open FK

/-- Uniqueness of extremal DLR measures from eventual agreement of their
actual exterior conditional probabilities.  Unlike
`measure_eq_of_backwardConditionalLimits_of_extremal_dlr`, this theorem does
not assume backward convergence or convergence to the tail: both are proved
from the decreasing exterior filtration and refined subsequences. -/
theorem measure_eq_of_eventualOutsideAgreement_of_extremal_dlr
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
    (hagree : ∀ A ∈ cylinders,
      ∀ᵐ z ∂ρ,
        (fun n ↦ (((μ : Measure (Configuration E))⟦A |
          FKLimit.outsideSigma (exh.box n).edges⟧) (X z))) =ᶠ[atTop]
        (fun n ↦ (((ν : Measure (Configuration E))⟦A |
          FKLimit.outsideSigma (exh.box n).edges⟧) (Y z)))) :
    (μ : Measure (Configuration E)) = (ν : Measure (Configuration E)) := by
  apply measure_eq_of_backwardConditionalLimits_of_extremal_dlr
    exh Φ hq hp μ ν hμ hν hextμ hextν ρ X Y hX hY hXμ hYν
    cylinders hcyl hgen hpi
  intro A hA
  let S : ℕ → Finset E := fun n ↦ (exh.box n).edges
  have hcof : ∀ T : Finset E, ∃ n, T ⊆ S n := by
    intro T
    exact (exh.eventually_subset T).exists
  have hμL1 := FKLimit.tendsto_eLpNorm_one_condExp_indicator_outside_to_tail
    (μ := (μ : Measure (Configuration E))) S exh.monotone hcof (hcyl A hA)
  have hνL1 := FKLimit.tendsto_eLpNorm_one_condExp_indicator_outside_to_tail
    (μ := (ν : Measure (Configuration E))) S exh.monotone hcof (hcyl A hA)
  have hμim := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hμL1
  have hνim := tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hνL1
  obtain ⟨u, hu, hμae⟩ := hμim.exists_seq_tendsto_ae
  obtain ⟨v, hv, hνae⟩ := (hνim.comp hu.tendsto_atTop).exists_seq_tendsto_ae
  have hμae' : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ (((μ : Measure (Configuration E))⟦A |
        FKLimit.outsideSigma (S (u (v n)))⟧) ω)) atTop
        (𝓝 (((μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) ω)) := by
    filter_upwards [hμae] with ω hω
    simpa only [Function.comp_def] using hω.comp hv.tendsto_atTop
  have hμρ : ∀ᵐ z ∂ρ,
      Tendsto (fun n ↦ (((μ : Measure (Configuration E))⟦A |
        FKLimit.outsideSigma (S (u (v n)))⟧) (X z))) atTop
        (𝓝 (((μ : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) (X z))) := by
    exact (Measure.tendsto_ae_map (μ := ρ) hX.aemeasurable).eventually (by
      rwa [hXμ])
  have hνae' : ∀ᵐ ω ∂(ν : Measure (Configuration E)),
      Tendsto (fun n ↦ (((ν : Measure (Configuration E))⟦A |
        FKLimit.outsideSigma (S (u (v n)))⟧) ω)) atTop
        (𝓝 (((ν : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) ω)) := by
    filter_upwards [hνae] with ω hω
    simpa only [Function.comp_def] using hω
  have hνρ : ∀ᵐ z ∂ρ,
      Tendsto (fun n ↦ (((ν : Measure (Configuration E))⟦A |
        FKLimit.outsideSigma (S (u (v n)))⟧) (Y z))) atTop
        (𝓝 (((ν : Measure (Configuration E))⟦A | FKLimit.tailSigma⟧) (Y z))) := by
    exact (Measure.tendsto_ae_map (μ := ρ) hY.aemeasurable).eventually (by
      rwa [hYν])
  refine ⟨
    fun n z ↦ (((μ : Measure (Configuration E))⟦A |
      FKLimit.outsideSigma (S (u (v n)))⟧) (X z)),
    fun n z ↦ (((ν : Measure (Configuration E))⟦A |
      FKLimit.outsideSigma (S (u (v n)))⟧) (Y z)),
    hμρ, hνρ, ?_⟩
  filter_upwards [hagree A hA] with z hz
  simpa only [Function.comp_def, S] using
    hz.comp_tendsto (hu.comp hv).tendsto_atTop

end FK.InfiniteVolume
