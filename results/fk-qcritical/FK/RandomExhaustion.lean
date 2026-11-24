import FK.UniformUpcrossing
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Random closed-frontier exhaustions: measurability, fibre constancy, martingale limits

The source (`arXiv:2512.16486v1`, proof of Theorem 5.1) conditions a Gibbs law
`μ` on the exterior `ℱ_{S_n(ω₃)^c}` of a **random** region `S_n(ω₃)` read off a
dominating configuration `ω₃`, identifies the conditional probability with the
free-boundary finite-region law, and passes to the limit by reverse-martingale
convergence.  Three measure-theoretic facts are needed for that argument; they
are supplied here.

* `measurable_family_apply` and `measurable_randomRegion_condExp`: the map
  `(ω, η) ↦ μ⟦A | outsideSigma (T η)⟧ ω` is jointly measurable in `(ω, η)` for
  every measurable region map `T`.  This is exactly the input listed as missing
  in the module docstring of `FK/UniformUpcrossing.lean`.
* `ae_notMem_of_countable_null` and `ae_condExp_eq_of_frontier_projection`:
  **fibre constancy**.  If for every finite region `S` the conditional
  probability `μ⟦A | outsideSigma S⟧` equals a region-only value `g S` on the
  event that the frontier of `S` is closed, then for **any** coupling whose
  `π`-marginal is `μ` the conditional probability computed at the coupled
  configuration equals `g` of the random region.  No product structure of the
  coupling is used: the proof only needs the `π`-marginal of the relevant bad
  set, which is available because the region map is `Finset`-valued and hence
  has countable range.  `ae_condExp_eq_of_dominated_coupling` assembles the
  two-fibre form, which is the source's step *"by uniqueness of conditional
  expectation … `μ₁(C | ℱ_{S_n^c})(ω₁) = μ₂(C | ℱ_{S_n^c})(ω₂)`"*.
* `tendsto_ae_condExp_randomRegion_prod`: for a **product** coupling the random
  exhaustion does give the reverse-martingale limit: `(μ ⊗ ℙ)`-almost every
  `(ω, η)` has `μ⟦A | outsideSigma (S_n η)⟧ ω → μ.real A`.  The proof applies
  the deterministic reverse-martingale theorem fibrewise and transfers the
  almost-sure statement to the product measure with `MeasureTheory.Measure.ae_prod_iff_ae_ae`; joint
  measurability is what makes the transfer legal.

`integral_condExp_eq_of_dominated_coupling` records what survives
unconditionally from the source's two steps: the `ν`-integral of each fibrewise
conditional probability equals `∫ g (S_n η) ∂ℙ`, the free-region average.  The
final comment block explains why that identity is not by itself the uniqueness
conclusion, and why the two coupling requirements above are mutually exclusive
at the level used, so the source's last step needs an additional argument.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace FK

/-! ## Joint measurability of a countably indexed measurable family -/

/-- A family of measurable functions indexed by a measurable-singleton type is
jointly measurable in the argument and the index. -/
theorem measurable_family_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable β] [MeasurableSingletonClass β]
    {f : β → α → γ} (hf : ∀ b, Measurable (f b)) :
    Measurable (fun p : α × β ↦ f p.2 p.1) := by
  intro s hs
  have h : (fun p : α × β ↦ f p.2 p.1) ⁻¹' s =
      ⋃ b : β, (f b ⁻¹' s) ×ˢ ({b} : Set β) := by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨p.2, hp, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact hb
  rw [h]
  exact MeasurableSet.iUnion fun b ↦ (hf b hs).prod (measurableSet_singleton b)

/-- **Marginal form of fibre constancy.**  Let `ν` be any coupling whose
`π`-marginal is `μ`, let `T` be a region map with countable range, and suppose
the "bad" set attached to every region is `μ`-null.  Then `ν`-almost every
point has `π`-image outside the bad set of its own region.

Only the `π`-marginal of `ν` is used; no disintegration, conditional
independence or product structure is required. -/
theorem ae_notMem_of_countable_null {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {ν : Measure β} [IsProbabilityMeasure ν]
    (π : β → α) (hπ : Measurable π) (hν : ν.map π = μ) {ι : Type*} [Countable ι]
    (T : β → ι) (N : ι → Set α) (hN : ∀ i, MeasurableSet (N i)) (hN0 : ∀ i, μ (N i) = 0) :
    ∀ᵐ p ∂ν, π p ∉ N (T p) := by
  classical
  have hsubset : {p : β | π p ∈ N (T p)} ⊆ {p : β | π p ∈ ⋃ i, N i} := by
    intro p hp
    exact mem_iUnion.2 ⟨T p, hp⟩
  have hnull : ν {p : β | π p ∈ ⋃ i, N i} = 0 := by
    have hM : MeasurableSet (⋃ i, N i) := MeasurableSet.iUnion hN
    have h1 : ν (π ⁻¹' (⋃ i, N i)) = ν.map π (⋃ i, N i) :=
      (Measure.map_apply hπ hM).symm
    have h2 : ν {p : β | π p ∈ ⋃ i, N i} = ν (π ⁻¹' (⋃ i, N i)) := rfl
    rw [h2, h1, hν]
    exact measure_iUnion_null hN0
  have hν0 : ν {p : β | π p ∈ N (T p)} = 0 := measure_mono_null hsubset hnull
  rw [ae_iff]
  simpa only [not_not] using hν0

end FK

namespace FKLimit

open FK

/-- Joint measurability of the random-region exterior conditional probability. -/
theorem measurable_randomRegion_condExp {E : Type*} [Countable E]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    {A : Set (Configuration E)}
    {Ω' : Type*} [MeasurableSpace Ω'] (T : Ω' → Finset E) (hT : Measurable T) :
    Measurable (fun p : Configuration E × Ω' ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1) := by
  classical
  have hfam : Measurable (fun q : Configuration E × Finset E ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma q.2] q.1) := by
    refine FK.measurable_family_apply (f := fun (S : Finset E) (ω : Configuration E) ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω) ?_
    intro S
    have h := stronglyMeasurable_condExp (μ := μ) (m := outsideSigma S)
      (f := A.indicator (fun _ ↦ (1 : ℝ)))
    exact (h.mono (outsideSigma_le S)).measurable
  have hpair : Measurable (fun p : Configuration E × Ω' ↦ (p.1, T p.2)) :=
    measurable_fst.prodMk (hT.comp measurable_snd)
  exact hfam.comp hpair

/-- **Fibre constancy along a random closed-frontier region.**

`Front S ω` is the assertion that the frontier of the finite region `S` is
closed in `ω` (the source's `ω|_{∂S} = 0`).  Hypothesis `hid` is the source's
identification "the conditional law given the exterior is the free-boundary
finite-region law"; it concerns one fixed finite region at a time, hence is
available for each of the countably many regions separately. -/
theorem ae_condExp_eq_of_frontier_projection {E : Type*} [Countable E]
    {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    {β : Type*} [MeasurableSpace β] {ν : Measure β} [IsProbabilityMeasure ν]
    (π : β → Configuration E) (hπ : Measurable π) (hν : ν.map π = μ)
    {A : Set (Configuration E)} (T : β → Finset E) (Front : Finset E → Configuration E → Prop)
    (g : Finset E → ℝ)
    (hFront : ∀ S, MeasurableSet {ω : Configuration E | Front S ω})
    (hid : ∀ S, ∀ᵐ ω ∂μ, Front S ω →
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hfront : ∀ᵐ p ∂ν, Front (T p) (π p)) :
    ∀ᵐ p ∂ν, μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p)] (π p) = g (T p) := by
  classical
  have hmeas : ∀ S : Finset E, Measurable (fun ω : Configuration E ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω) := by
    intro S
    have h := stronglyMeasurable_condExp (μ := μ) (m := outsideSigma S)
      (f := A.indicator (fun _ ↦ (1 : ℝ)))
    exact (h.mono (outsideSigma_le S)).measurable
  have hN0 : ∀ S : Finset E, μ {ω : Configuration E | ¬ (Front S ω →
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)} = 0 := by
    intro S
    rw [← ae_iff]
    exact hid S
  have hN : ∀ S : Finset E, MeasurableSet {ω : Configuration E | ¬ (Front S ω →
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)} := by
    intro S
    have h1 : {ω : Configuration E | ¬ (Front S ω →
        μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)} =
        {ω : Configuration E | Front S ω} ∩
          {ω : Configuration E | μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω ≠ g S} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Classical.not_imp]
    rw [h1]
    exact MeasurableSet.inter (hFront S) (hmeas S (measurableSet_singleton (g S))).compl
  have hbad := FK.ae_notMem_of_countable_null π hπ hν T
    (fun S : Finset E ↦ {ω : Configuration E | ¬ (Front S ω →
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)}) hN hN0
  filter_upwards [hbad, hfront] with p hp hpfront
  exact (Classical.byContradiction hp) hpfront

/-- **Two-fibre agreement (the source's pre-limit step, made rigorous).**

Let `ν` couple the two laws `μ₁`, `μ₂` with the dominating law `ℙ` so that
`ω₁ ≤ ω₃` and `ω₂ ≤ ω₃` almost surely, and let `T n` be a measurable random
region read off `ω₃` whose frontier is `ℙ`-almost surely closed.  If for each
fixed finite region `S` the exterior conditional probability of `A` under `μ_i`
is the free-boundary region value `g S` whenever the frontier of `S` is closed,
then `ν`-almost surely both conditional probabilities, evaluated at the
respective coupled configurations, equal `g (T n ω₃)` for every `n`. -/
theorem ae_condExp_eq_of_dominated_coupling {E : Type*} [Countable E]
    {μ₁ μ₂ ℙ : Measure (Configuration E)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ℙ]
    {ν : Measure (Configuration E × Configuration E × Configuration E)}
    [IsProbabilityMeasure ν]
    (h₁ : ν.map (fun p ↦ p.1) = μ₁) (h₂ : ν.map (fun p ↦ p.2.1) = μ₂)
    (h₃ : ν.map (fun p ↦ p.2.2) = ℙ)
    {A : Set (Configuration E)} (T : ℕ → Configuration E → Finset E)
    (hT : ∀ n, Measurable (T n))
    (Front : Finset E → Configuration E → Prop) (g : Finset E → ℝ)
    (hFrontJoint : MeasurableSet {q : Configuration E × Finset E | Front q.2 q.1})
    (hid₁ : ∀ S, ∀ᵐ ω ∂μ₁, Front S ω →
      μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hid₂ : ∀ S, ∀ᵐ ω ∂μ₂, Front S ω →
      μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hfront : ∀ᵐ η ∂ℙ, ∀ n, Front (T n η) η)
    (hmono : ∀ S ω ω', ω ≤ ω' → Front S ω' → Front S ω)
    (hle₁ : ∀ᵐ p ∂ν, p.1 ≤ p.2.2) (hle₂ : ∀ᵐ p ∂ν, p.2.1 ≤ p.2.2) :
    ∀ᵐ p ∂ν, ∀ n,
      μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.1 = g (T n p.2.2) ∧
      μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.2.1 = g (T n p.2.2) := by
  classical
  have hFront : ∀ S, MeasurableSet {ω : Configuration E | Front S ω} := by
    intro S
    exact hFrontJoint.preimage (measurable_id.prodMk measurable_const)
  -- transfer the closed-frontier statement from `ℙ` to the coupling
  have hset : MeasurableSet {y : Configuration E | ∀ n, Front (T n y) y} := by
    have : {y : Configuration E | ∀ n, Front (T n y) y} =
        ⋂ n, (fun y ↦ (y, T n y)) ⁻¹' {q : Configuration E × Finset E | Front q.2 q.1} := by
      ext y
      simp only [mem_iInter, mem_preimage, mem_ofPred_eq]
    rw [this]
    exact MeasurableSet.iInter fun n ↦ hFrontJoint.preimage (measurable_id.prodMk (hT n))
  have hfrontν : ∀ᵐ p ∂ν, ∀ n, Front (T n p.2.2) p.2.2 := by
    have h := hfront
    rw [← h₃] at h
    rw [ae_map_iff (measurable_snd.snd.aemeasurable) hset] at h
    exact h
  have hfront₁ : ∀ᵐ p ∂ν, ∀ n, Front (T n p.2.2) p.1 := by
    filter_upwards [hfrontν, hle₁] with p hF hle
    exact fun n ↦ hmono _ _ _ hle (hF n)
  have hfront₂ : ∀ᵐ p ∂ν, ∀ n, Front (T n p.2.2) p.2.1 := by
    filter_upwards [hfrontν, hle₂] with p hF hle
    exact fun n ↦ hmono _ _ _ hle (hF n)
  have hstep₁ : ∀ n, ∀ᵐ p ∂ν,
      μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.1 = g (T n p.2.2) := by
    intro n
    have h := ae_condExp_eq_of_frontier_projection (μ := μ₁) (ν := ν)
      (π := fun p : Configuration E × Configuration E × Configuration E ↦ p.1)
      measurable_fst h₁ (T := fun p : Configuration E × Configuration E × Configuration E ↦
        T n p.2.2) (Front := Front) (g := g) hFront hid₁ (by
          filter_upwards [hfront₁] with p hF
          exact hF n)
    simpa only using h
  have hstep₂ : ∀ n, ∀ᵐ p ∂ν,
      μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.2.1 = g (T n p.2.2) := by
    intro n
    have h := ae_condExp_eq_of_frontier_projection (μ := μ₂) (ν := ν)
      (π := fun p : Configuration E × Configuration E × Configuration E ↦ p.2.1)
      measurable_snd.fst h₂ (T := fun p : Configuration E × Configuration E × Configuration E ↦
        T n p.2.2) (Front := Front) (g := g) hFront hid₂ (by
          filter_upwards [hfront₂] with p hF
          exact hF n)
    simpa only using h
  rw [ae_all_iff]
  intro n
  filter_upwards [hstep₁ n, hstep₂ n] with p h1 h2
  exact ⟨h1, h2⟩

/-- **Random-exhaustion reverse martingale, product coupling.**

For a product coupling `μ ⊗ ℙ` and a measurable increasing cofinal random
exhaustion `T n(η)`, the exterior conditional probabilities converge
`(μ ⊗ ℙ)`-almost everywhere to the unconditional mass, provided the tail
`σ`-algebra of `μ` is trivial.  This supplies the input named as missing in the
module docstring of `FK/UniformUpcrossing.lean`.

The proof applies `tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn`
fibrewise in `η` and transfers the almost-sure statement to the product measure
with `MeasureTheory.Measure.ae_prod_iff_ae_ae`; joint measurability
(`measurable_randomRegion_condExp`) is what makes the measurable set available. -/
theorem tendsto_ae_condExp_randomRegion_prod {E : Type*} [Countable E]
    {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (hμ : ZeroOneOn tailSigma μ)
    {Ω' : Type*} [MeasurableSpace Ω'] (T : ℕ → Ω' → Finset E)
    (hT : ∀ n, Measurable (T n))
    (P : Measure Ω') [IsProbabilityMeasure P]
    (hmono : ∀ (η : Ω') n, T n η ⊆ T (n + 1) η)
    (hcof : ∀ᵐ η ∂P, ∀ K : Finset E, ∃ n, K ⊆ T n η)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∀ᵐ p ∂(μ.prod P), Tendsto (fun n ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1) atTop
        (𝓝 (μ.real A)) := by
  classical
  have hmono' : ∀ η : Ω', Monotone (fun n ↦ T n η) := fun η ↦
    monotone_nat_of_le_succ (fun n ↦ hmono η n)
  have hmeas : ∀ n, Measurable (fun p : Configuration E × Ω' ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1) := fun n ↦
    measurable_randomRegion_condExp μ (T n) (hT n)
  -- the good set at each rational approximation level
  have hgood : ∀ k : ℕ, MeasurableSet {p : Configuration E × Ω' | ∀ᶠ n in atTop,
      |μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1 - μ.real A| <
        ((k : ℝ) + 1)⁻¹} := by
    intro k
    have hset : {p : Configuration E × Ω' | ∀ᶠ n in atTop,
        |μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1 - μ.real A| <
          ((k : ℝ) + 1)⁻¹} =
        ⋃ N : ℕ, ⋂ n ∈ Set.Ici N, {p : Configuration E × Ω' |
          |μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1 - μ.real A| <
            ((k : ℝ) + 1)⁻¹} := by
      ext p
      simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, mem_iInter, mem_Ici]
    rw [hset]
    refine MeasurableSet.iUnion fun N ↦ MeasurableSet.iInter fun n ↦
      MeasurableSet.iInter fun _ ↦ ?_
    have hcont : Measurable (fun p : Configuration E × Ω' ↦
        |μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1 - μ.real A|) :=
      (continuous_abs.measurable).comp ((hmeas n).sub measurable_const)
    exact hcont measurableSet_Iio
  have hfib : ∀ᵐ η ∂P, ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n η)] ω) atTop
        (𝓝 (μ.real A)) := by
    filter_upwards [hcof] with η hcofη
    exact tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn (μ := μ)
      (fun n ↦ T n η) (hmono' η) hcofη hA hμ
  have hk : ∀ k : ℕ, ∀ᵐ p ∂(μ.prod P), ∀ᶠ n in atTop,
      |μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2)] p.1 - μ.real A| <
        ((k : ℝ) + 1)⁻¹ := by
    intro k
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (hgood k), MeasureTheory.Measure.ae_ae_comm (hgood k)]
    filter_upwards [hfib] with η hη
    filter_upwards [hη] with ω hω
    rw [Metric.tendsto_atTop] at hω
    obtain ⟨N, hN⟩ := hω ((k : ℝ) + 1)⁻¹ (by positivity)
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have hNn := hN n hn
    rw [Real.dist_eq] at hNn
    exact hNn
  have hall := ae_all_iff.2 hk
  filter_upwards [hall] with p hp
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hklt⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp k)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact lt_trans (hN n hn) (by simpa only [one_div] using hklt)

/-- **What survives unconditionally from the source's two steps.**

Under the hypotheses of `ae_condExp_eq_of_dominated_coupling`, the coupling
integral of each fibrewise conditional probability equals the average of the
free-region values `g (T n η)` against the dominating law.  This is an
unconditional identity: it uses only the marginal of the coupling and the
finite-region free-boundary identification.

The source's final step is the further claim `μ_i (A) = ∫ g (T n η) ∂ℙ`, whose
proof is *not* supplied by either of the two results above. -/
theorem integral_condExp_eq_of_dominated_coupling {E : Type*} [Countable E]
    {μ₁ μ₂ ℙ : Measure (Configuration E)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ℙ]
    {ν : Measure (Configuration E × Configuration E × Configuration E)}
    [IsProbabilityMeasure ν]
    (h₁ : ν.map (fun p ↦ p.1) = μ₁) (h₂ : ν.map (fun p ↦ p.2.1) = μ₂)
    (h₃ : ν.map (fun p ↦ p.2.2) = ℙ)
    {A : Set (Configuration E)} (T : ℕ → Configuration E → Finset E)
    (hT : ∀ n, Measurable (T n))
    (Front : Finset E → Configuration E → Prop) (g : Finset E → ℝ)
    (hFrontJoint : MeasurableSet {q : Configuration E × Finset E | Front q.2 q.1})
    (hid₁ : ∀ S, ∀ᵐ ω ∂μ₁, Front S ω →
      μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hid₂ : ∀ S, ∀ᵐ ω ∂μ₂, Front S ω →
      μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hfront : ∀ᵐ η ∂ℙ, ∀ n, Front (T n η) η)
    (hmono : ∀ S ω ω', ω ≤ ω' → Front S ω' → Front S ω)
    (hle₁ : ∀ᵐ p ∂ν, p.1 ≤ p.2.2) (hle₂ : ∀ᵐ p ∂ν, p.2.1 ≤ p.2.2)
    (hg : ∀ n, Measurable (fun η : Configuration E ↦ g (T n η)))
    (n : ℕ) :
    (∫ p, μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.1 ∂ν =
        ∫ η, g (T n η) ∂ℙ) ∧
      (∫ p, μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.2.1 ∂ν =
        ∫ η, g (T n η) ∂ℙ) := by
  classical
  have hpair := ae_condExp_eq_of_dominated_coupling h₁ h₂ h₃ T hT Front g hFrontJoint
    hid₁ hid₂ hfront hmono hle₁ hle₂
  have h₁' : ∫ p, μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.1 ∂ν =
      ∫ p, g (T n p.2.2) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hpair] with p hp
    exact (hp n).1
  have h₂' : ∫ p, μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.2.1 ∂ν =
      ∫ p, g (T n p.2.2) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hpair] with p hp
    exact (hp n).2
  have hmarg : ∫ p, g (T n p.2.2) ∂ν =
      ∫ η, g (T n η) ∂ℙ := by
    have hφ : AEMeasurable (fun p : Configuration E × Configuration E × Configuration E ↦ p.2.2) ν :=
      measurable_snd.snd.aemeasurable
    have hgm : AEStronglyMeasurable (fun η : Configuration E ↦ g (T n η))
        (Measure.map (fun p : Configuration E × Configuration E × Configuration E ↦ p.2.2) ν) :=
      (hg n).aestronglyMeasurable
    rw [← h₃]
    rw [integral_map hφ hgm]
  exact ⟨h₁'.trans hmarg, h₂'.trans hmarg⟩

/-- **The mass identity holds for a product coupling.**

For the *product* coupling `μ ⊗ ℙ` the fibrewise conditional probability does
integrate to the unconditional mass — for **every** measurable region map, with
no tail triviality and no exhaustion hypothesis.  The proof is Fubini in the
order (inner `ω`, outer `η`) together with the tower property of the conditional
expectation at the fixed region `T η`.

This is the sharp counterpart of
`integral_condExp_eq_of_dominated_coupling`: the identity `∫ fibre = μ (A)` is a
*product-coupling* phenomenon.  A domination coupling `ω ≤ ω₃` — which is what
makes the frontier of the random region closed, hence the fibre value equal to
the free-region value — is not a product coupling in the nondegenerate case,
and there the fibre integral is `∫ g (S_n η) ∂ℙ` instead. -/
theorem integral_condExp_randomRegion_prod {E : Type*} [Countable E]
    {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] (T : Ω' → Finset E) (hT : Measurable T)
    (P : Measure Ω') [IsProbabilityMeasure P]
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∫ p, μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1 ∂(μ.prod P) =
      μ.real A := by
  classical
  have hmeas : Measurable (fun p : Configuration E × Ω' ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1) :=
    measurable_randomRegion_condExp μ T hT
  -- pointwise two-sided bounds for each fixed region
  have hbS : ∀ S : Finset E, ∀ᵐ ω ∂μ,
      0 ≤ μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω ∧
        μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω ≤ 1 := by
    intro S
    have hnn : 0 ≤ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] :=
      condExp_nonneg (Eventually.of_forall fun ω ↦ by
        rw [Set.indicator_apply]
        split_ifs <;> norm_num)
    have hint : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hA
    have hle : μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ≤ᵐ[μ]
        μ[(fun _ ↦ (1 : ℝ)) | outsideSigma S] :=
      condExp_mono hint (integrable_const 1) (Eventually.of_forall fun ω ↦ by
        rw [Set.indicator_apply]
        split_ifs <;> norm_num)
    rw [condExp_const (outsideSigma_le S) (1 : ℝ)] at hle
    filter_upwards [hnn, hle] with ω h1 h2
    exact ⟨h1, by simpa using h2⟩
  -- a global two-sided bound on the product space, via the countable range of `T`
  have hbdd : ∀ᵐ p ∂(μ.prod P),
      ‖μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1‖ ≤ 1 := by
    set M : Set (Configuration E) := ⋃ S : Finset E,
      {ω : Configuration E | ¬ (0 ≤ μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω ∧
        μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω ≤ 1)} with hMdef
    have hM0 : μ M = 0 := by
      refine measure_iUnion_null fun S ↦ ?_
      rw [← ae_iff]
      exact hbS S
    have hcompl : ∀ᵐ p ∂(μ.prod P), p.1 ∉ M := by
      rw [ae_iff]
      have hsub : {p : Configuration E × Ω' | ¬ p.1 ∉ M} ⊆ M ×ˢ Set.univ := by
        intro p hp
        simp only [mem_ofPred_eq, not_not] at hp
        exact ⟨hp, trivial⟩
      refine measure_mono_null hsub ?_
      rw [Measure.prod_prod, hM0]
      simp
    filter_upwards [hcompl] with p hp
    have hgood := hbS (T p.2)
    have : 0 ≤ μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1 ∧
        μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1 ≤ 1 := by
      by_contra hc
      exact hp (mem_iUnion.2 ⟨T p.2, hc⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  have hint : Integrable (fun p : Configuration E × Ω' ↦
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T p.2)] p.1) (μ.prod P) :=
    ⟨hmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 1) hbdd⟩
  rw [integral_prod_symm _ hint]
  -- the inner integral is the unconditional mass, for every region
  have hinner : ∀ η : Ω', ∫ ω, μ[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T η)] ω ∂μ =
      μ.real A := by
    intro η
    have hint2 : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hA
    rw [integral_condExp (outsideSigma_le (T η))]
    rw [integral_indicator hA]
    simp [Measure.real, Measure.restrict_apply MeasurableSet.univ]
  simp only [hinner]
  simp


/-- **The frontier predicate of the source, concretely.**

For a region `S` with frontier edge set `frontier S`, the source's condition
`ω|_{∂S} = 0` is `∀ e ∈ frontier S, ω e = false`.  Both auxiliary hypotheses of
`ae_condExp_eq_of_dominated_coupling` — joint measurability of the frontier
predicate and its downward closure under `ω ≤ ω'` — are automatic for this
predicate, so only the paper's own two inputs remain: the frontier is `ℙ`-a.e.
closed along the random exhaustion, and the free-boundary identification at each
fixed finite region. -/
def closedFrontier (frontier : Finset E → Finset E) :
    Finset E → Configuration E → Prop :=
  fun S ω ↦ ∀ e ∈ frontier S, ω e = false

theorem measurableSet_closedFrontier {E : Type*} [Countable E]
    (frontier : Finset E → Finset E) :
    MeasurableSet {q : Configuration E × Finset E | closedFrontier frontier q.2 q.1} := by
  have h : {q : Configuration E × Finset E | closedFrontier frontier q.2 q.1} =
      ⋃ S : Finset E, ({q : Configuration E × Finset E | q.2 = S} ∩
        ⋂ e ∈ frontier S, {q : Configuration E × Finset E | q.1 e = false}) := by
    ext q
    simp only [closedFrontier, mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · intro hq
      exact ⟨q.2, rfl, hq⟩
    · rintro ⟨S, rfl, hq⟩
      exact hq
  rw [h]
  refine MeasurableSet.iUnion fun S ↦ MeasurableSet.inter ?_ ?_
  · exact measurable_snd (measurableSet_singleton S)
  · refine MeasurableSet.iInter fun e ↦ MeasurableSet.iInter fun _ ↦ ?_
    have hev : Measurable (fun q : Configuration E × Finset E ↦ q.1 e) :=
      (measurable_pi_apply (X := fun _ : E ↦ Bool) e).comp measurable_fst
    exact hev (measurableSet_singleton false)

theorem closedFrontier_mono {E : Type*} (frontier : Finset E → Finset E) :
    ∀ (S : Finset E) (ω ω' : Configuration E), ω ≤ ω' →
      closedFrontier frontier S ω' → closedFrontier frontier S ω := by
  intro S ω ω' hle h e he
  have h' : ω' e = false := h e he
  have h2 : ω e ≤ ω' e := hle e
  rw [h'] at h2
  cases hx : ω e
  · rfl
  · rw [hx] at h2
    exact absurd h2 (by simp)

/-- **Two-fibre agreement for the source's concrete frontier condition.**

This is `ae_condExp_eq_of_dominated_coupling` with both auxiliary frontier
hypotheses discharged.  The remaining inputs are exactly the paper's:
`∀ᵐ η ∂ℙ, ∀ n, η|_{∂S_n(η)} = 0` (the closed-frontier random exhaustion, which
the source derives from `ℙ (∃ infinite cluster) = 0`) and the free-boundary
identification at each fixed finite region. -/
theorem ae_condExp_eq_of_dominated_coupling_frontier {E : Type*} [Countable E]
    {μ₁ μ₂ ℙ : Measure (Configuration E)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ℙ]
    {ν : Measure (Configuration E × Configuration E × Configuration E)}
    [IsProbabilityMeasure ν]
    (h₁ : ν.map (fun p ↦ p.1) = μ₁) (h₂ : ν.map (fun p ↦ p.2.1) = μ₂)
    (h₃ : ν.map (fun p ↦ p.2.2) = ℙ)
    {A : Set (Configuration E)} (T : ℕ → Configuration E → Finset E)
    (hT : ∀ n, Measurable (T n)) (frontier : Finset E → Finset E) (g : Finset E → ℝ)
    (hid₁ : ∀ S, ∀ᵐ ω ∂μ₁, closedFrontier frontier S ω →
      μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hid₂ : ∀ S, ∀ᵐ ω ∂μ₂, closedFrontier frontier S ω →
      μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma S] ω = g S)
    (hfront : ∀ᵐ η ∂ℙ, ∀ n, ∀ e ∈ frontier (T n η), η e = false)
    (hle₁ : ∀ᵐ p ∂ν, p.1 ≤ p.2.2) (hle₂ : ∀ᵐ p ∂ν, p.2.1 ≤ p.2.2) :
    ∀ᵐ p ∂ν, ∀ n,
      μ₁[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.1 = g (T n p.2.2) ∧
      μ₂[A.indicator (fun _ ↦ (1 : ℝ)) | outsideSigma (T n p.2.2)] p.2.1 = g (T n p.2.2) :=
  ae_condExp_eq_of_dominated_coupling h₁ h₂ h₃ T hT (closedFrontier frontier) g
    (measurableSet_closedFrontier frontier) hid₁ hid₂ hfront
    (closedFrontier_mono frontier) hle₁ hle₂
