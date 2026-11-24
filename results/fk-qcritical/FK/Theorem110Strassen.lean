import FK.StrassenCountable
import FK.SubcriticalPercolation

/-!
# Theorem 1.10 assembly with the coupling input discharged

Stage 21, direction 8 (`m1`, swarm `smwu4rrf3`).  This file removes residual
**(R4)** of `docs/THEOREM110-ASSEMBLY.md`: the input

```
hdom : ∀ φ ∈ FKLimitMeasures exh hq hp,
  ∃ γ, γ.map Prod.fst = φ ∧ γ.map Prod.snd = percolation G s ∧ z.1 ≤ z.2 a.e.
```

of `FK.InfiniteVolume.theorem_1_10_modulo_inputs` was taken as an unexplained
coupling.  The FK comparison inequalities of the paper (Theorem 1.2,
Theorem 1.4(1)) are proved in this development in the *increasing-event* form
`FKLimit.StochasticallyDominates`; the paper's proof of Theorem 5.1 uses the
*coupling* form.  The gap between the two is Strassen's hard direction, which is
now available on the countable product as
`FKLimit.exists_orderedCoupling_of_stochasticallyDominates`
(`FK/StrassenCountable.lean`).

Proved here:

* `bernoulliDominates_iff_stochasticallyDominates` — the `ℝ≥0∞`-valued event
  form used for Strassen and the project's `ℝ≥0`-valued
  `FKLimit.StochasticallyDominates` are the same statement;
* `exists_orderedCoupling_percolation_iff` — for the subcritical Bernoulli
  reference law, coupling form `↔` event form, so the paper's two formulations
  are interchangeable and neither hides an extra hypothesis;
* `ae_nonPercolating_of_bernoulli_domination` — a law dominated on increasing
  events by the subcritical Bernoulli law is a.s. non-percolating (no coupling);
* `subcritical_domination_coupling_form` — the `hdom` input of the assembly
  derived from the event comparison;
* `ae_nonPercolating_of_subcritical_domination_inequality` and
  `theorem_1_10_of_subcritical_domination_inequality` — Theorem 1.10 with
  `hdom` replaced by the proved event comparison;
* `FKFamilyAll`, `theorem_1_10_exhaustion_independent` — the paper's family
  `⋃_Φ 𝒢^Φ ∪ 𝒲` is exhaustion-independent, so the conclusion is stated and
  proved when the inputs range over **every** box exhaustion;
* `exists_subexhaustion_isFKLimit_of_assignments` — for an arbitrary sequence of
  boundary conventions on a fixed exhaustion some coarsening has a genuine FK
  weak limit, i.e. the paper's `𝒲` is nonempty however conventions are chosen.

`h5_1` (Theorem 5.1) and `h518` (Proposition 1.8(2) for the selected
convention) remain explicit hypotheses; `docs/THEOREM110-STRASSEN.md` records
why they cannot be removed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal unitInterval

namespace FK.InfiniteVolume

universe u v

/-! ## The subcritical Bernoulli reference law -/

section Bernoulli

variable {V : Type*} {G : SimpleGraph V}

/-- The subcritical Bernoulli reference law of the paper, as a probability
measure on the configuration space of `G`. -/
noncomputable def bernoulliRef (G : SimpleGraph V) (s : unitInterval) :
    ProbabilityMeasure (Configuration G.edgeSet) :=
  ⟨CurvatureVariance.Infra.Percolation.percolation G s, inferInstance⟩

@[simp] lemma bernoulliRef_coe (G : SimpleGraph V) (s : unitInterval) :
    (bernoulliRef G s : Measure (Configuration G.edgeSet)) =
      CurvatureVariance.Infra.Percolation.percolation G s := rfl

/-- The event form of the domination input, with `ℝ≥0∞`-valued probabilities:
`φ` is below the Bernoulli reference law on every measurable increasing event.
This is the form in which Strassen's theorem is stated. -/
def BernoulliDominates (G : SimpleGraph V) (s : unitInterval)
    (φ : ProbabilityMeasure (Configuration G.edgeSet)) : Prop :=
  ∀ A : Set (Configuration G.edgeSet), MeasurableSet A → IsUpperSet A →
    (φ : Measure (Configuration G.edgeSet)) A ≤
      CurvatureVariance.Infra.Percolation.percolation G s A

/-- The `ℝ≥0∞` event form and the project's `ℝ≥0`-valued
`FKLimit.StochasticallyDominates` are the same statement. -/
theorem bernoulliDominates_iff_stochasticallyDominates {s : unitInterval}
    {φ : ProbabilityMeasure (Configuration G.edgeSet)} :
    BernoulliDominates G s φ ↔ FKLimit.StochasticallyDominates (bernoulliRef G s) φ := by
  unfold BernoulliDominates FKLimit.StochasticallyDominates
  constructor
  · intro h A hA hU
    refine (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr ?_
    simpa using h A hA hU
  · intro h A hA hU
    have h' := h A hA hU
    have h'' : ((φ : Measure (Configuration G.edgeSet)) A).toNNReal ≤
        ((bernoulliRef G s : Measure (Configuration G.edgeSet)) A).toNNReal := by
      simpa [ProbabilityMeasure.coeFn_def] using h'
    exact (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h''

end Bernoulli

/-! ## The coupling and event forms are equivalent (Strassen) -/

section Equivalence

variable {V : Type*} [Countable V] {G : SimpleGraph V} {s : unitInterval}

/-- **Residual (R4) discharged.**  For the subcritical Bernoulli reference law,
"there is a monotone coupling of `φ` below the reference law" (the paper's form
of the domination input, used in the proof of Theorem 5.1) is *equivalent* to
the increasing-event comparison `BernoulliDominates G s φ`, which is what the
comparison theorems of this development produce.

The forward direction is Strassen's easy direction; the backward direction is
the hard direction, proved on the countable product in `FK/StrassenCountable.lean`
via finite weighted Hall transport and compactness. -/
theorem exists_orderedCoupling_percolation_iff
    {φ : ProbabilityMeasure (Configuration G.edgeSet)} :
    (∃ γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool)),
        γ.map Prod.fst = (φ : Measure (G.edgeSet → Bool)) ∧
          γ.map Prod.snd = CurvatureVariance.Infra.Percolation.percolation G s ∧
            ∀ᵐ z ∂γ, z.1 ≤ z.2) ↔
      BernoulliDominates G s φ := by
  have hiff := CountableStrassen.strassen_iff
    (μ := (φ : Measure (Configuration G.edgeSet)))
    (ν := CurvatureVariance.Infra.Percolation.percolation G s)
  constructor
  · rintro ⟨γ, hfst, hsnd, hord⟩ A hA hU
    refine hiff.2 ⟨γ, ?_, hfst, hsnd, hord⟩ A hA hU
    refine ⟨?_⟩
    have h1 : Measure.map Prod.fst γ Set.univ = 1 := by rw [hfst]; simp
    rwa [Measure.map_apply measurable_fst MeasurableSet.univ] at h1
  · intro h
    obtain ⟨γ, -, hfst, hsnd, hord⟩ := hiff.1 h
    exact ⟨γ, hfst, hsnd, hord⟩

end Equivalence

/-! ## Subcritical Bernoulli domination gives non-percolation, directly -/

section NonPercolation

variable {V : Type*} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- **The paper's step "`φ`-a.s. there is no infinite cluster", from the event
form of the domination input.**

`NonPercolating G` is a lower set, so its complement is a measurable increasing
event; the Bernoulli reference law gives that complement mass zero below `p_c`,
and domination transfers the zero.  No coupling is needed. -/
theorem ae_nonPercolating_of_bernoulli_domination (hG : G.Connected) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    {φ : ProbabilityMeasure (Configuration G.edgeSet)}
    (h : BernoulliDominates G s φ) :
    ∀ᵐ ω ∂(φ : Measure (Configuration G.edgeSet)), ω ∈ NonPercolating G := by
  have hbern : CurvatureVariance.Infra.Percolation.percolation G s
      (NonPercolating G)ᶜ = 0 := by
    have hae := FK.ae_nonPercolating_percolation_of_lt_criticalProb (V := V) (G := G) hG hs
    rw [ae_iff] at hae
    exact hae
  have hφ : (φ : Measure (Configuration G.edgeSet)) (NonPercolating G)ᶜ = 0 :=
    FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates
      ((bernoulliDominates_iff_stochasticallyDominates (G := G) (s := s)).mp h)
      (measurableSet_nonPercolating G hG).compl (isLowerSet_nonPercolating G).compl hbern
  rw [ae_iff]
  exact hφ

/-- **The subcritical half of Theorem 1.10 from the event form.**  Every FK weak
limit of the exhaustion dominated on increasing events by the subcritical
Bernoulli law is almost surely non-percolating. -/
theorem ae_nonPercolating_of_subcritical_domination_inequality
    (hG : G.Connected) (exh : BoxExhaustion G.edgeSet) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    (hstoch : ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp → BernoulliDominates G s φ) :
    ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp →
        ∀ᵐ ω ∂(φ : Measure (Configuration G.edgeSet)), ω ∈ NonPercolating G := by
  intro φ hφ
  exact ae_nonPercolating_of_bernoulli_domination hG hs (hstoch φ hφ)

omit [G.LocallyFinite] in
/-- The `hdom` input of `theorem_1_10_modulo_inputs`, derived from the event
comparison through Strassen. -/
theorem subcritical_domination_coupling_form
    (exh : BoxExhaustion G.edgeSet) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {s : unitInterval}
    (hstoch : ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp → BernoulliDominates G s φ) :
    ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp →
        ∃ γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool)),
          γ.map Prod.fst = (φ : Measure (G.edgeSet → Bool)) ∧
            γ.map Prod.snd = CurvatureVariance.Infra.Percolation.percolation G s ∧
              ∀ᵐ z ∂γ, z.1 ≤ z.2 := by
  intro φ hφ
  exact (exists_orderedCoupling_percolation_iff (G := G) (s := s)).2 (hstoch φ hφ)

end NonPercolation

/-! ## Theorem 1.10 with the coupling input discharged -/

section MainAssembly

variable {V : Type*} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- **Theorem 1.10 modulo Theorem 5.1 and Proposition 1.8(2), with the
domination input in its proved increasing-event form.**

Compared with `FK.InfiniteVolume.theorem_1_10_modulo_inputs`, the hypothesis
`hdom` (an unexplained ordered coupling) is gone; the input is now
`hstoch`, the increasing-event comparison that the comparison theorems of this
development actually prove.  Strassen's hard direction
(`exists_orderedCoupling_percolation_iff`) converts it into the coupling form
used by the paper's proof of Theorem 5.1. -/
theorem theorem_1_10_of_subcritical_domination_inequality
    (hG : G.Connected) (exh : BoxExhaustion G.edgeSet) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    (hne : (FKLimitMeasures exh hq hp).Nonempty)
    (hstoch : ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp → BernoulliDominates G s φ)
    (Φ : BoundaryAssignment exh.box)
    {μ₀ : ProbabilityMeasure (Configuration G.edgeSet)}
    (h5_1 : DLRMeasures exh Φ hq hp = {μ₀})
    (h518 : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ FKLimitMeasures exh hq hp → μ ∈ DLRMeasures exh Φ hq hp) :
    (∃! μ : ProbabilityMeasure (Configuration G.edgeSet),
        μ ∈ FKFamily exh hq hp) ∧
      ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)), ω ∈ NonPercolating G :=
  theorem_1_10_modulo_inputs hG exh hq hp hs hne
    (subcritical_domination_coupling_form exh hq hp hstoch) Φ h5_1 h518

end MainAssembly

/-! ## The paper's family is exhaustion-independent -/

section ExhaustionIndependent

universe w

variable {V : Type w} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The paper's total family `⋃_Φ 𝒢^Φ ∪ 𝒲` is quantified over *all* box
exhaustions, not over one fixed exhaustion: a DLR measure may be tested on any
exhaustion and a weak limit may be taken along any exhaustion.  `FKFamilyAll`
collects the union over every exhaustion of the configuration space `G.edgeSet`,
so a singleton statement about it is the exhaustion-independent one. -/
def FKFamilyAll {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    Set (ProbabilityMeasure (Configuration G.edgeSet)) :=
  ⋃ exh : BoxExhaustion.{w, w} G.edgeSet, FKFamily exh hq hp

omit [G.LocallyFinite] in
theorem mem_fkFamilyAll_of_mem_fkFamily {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (exh : BoxExhaustion.{w, w} G.edgeSet)
    {ν : ProbabilityMeasure (Configuration G.edgeSet)}
    (hν : ν ∈ FKFamily exh hq hp) : ν ∈ FKFamilyAll (G := G) hq hp :=
  Set.mem_iUnion.mpr ⟨exh, hν⟩

end ExhaustionIndependent

/-! ## The paper's `𝒲` is nonempty for any convention sequence, after coarsening -/

section Coarsening

universe a b

variable {E : Type a} [Countable E]

/-- **Nonemptiness of the weak-limit class for an arbitrary convention
sequence.**

The existing `exists_boxExhaustion_fkLimitMeasures_nonempty` uses the constant
free assignment.  The paper's `𝒲` allows an *arbitrary* sequence of boundary
conventions; here we show that for any such sequence some coarsening of the
exhaustion has a genuine FK weak limit, so `𝒲` is nonempty however the
conventions are chosen.  This is a compactness statement about the coarsened
exhaustion; it does not assert convergence along the originally prescribed
sequence. -/
theorem exists_subexhaustion_isFKLimit_of_assignments (exh : BoxExhaustion.{a, b} E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition) :
    ∃ (exh' : BoxExhaustion.{a, b} E) (α' : ∀ n, (exh'.box n).BoundaryPartition)
      (μ : ProbabilityMeasure (Configuration E)), IsFKLimit exh' hq hp α' μ := by
  classical
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq
    (fun n => (exh.box n).finiteVolumeLaw hq hp (α n))
  have hmono : Monotone (fun n => (exh.box (φ n)).edges) :=
    fun a b hab => exh.monotone (hφ.monotone hab)
  have hcov : ∀ e : E, ∃ n, e ∈ (exh.box (φ n)).edges := by
    intro e
    obtain ⟨N, hN⟩ := exh.covers e
    obtain ⟨n, hn⟩ := (hφ.tendsto_atTop.eventually (eventually_ge_atTop N)).exists
    exact ⟨n, exh.monotone hn hN⟩
  exact ⟨⟨fun n => exh.box (φ n), hmono, hcov⟩, fun n => α (φ n), ν, hν⟩

end Coarsening

/-! ## Theorem 1.10 in the exhaustion-independent form -/

section ExhaustionIndependentMain

universe w

variable {V : Type w} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- **Theorem 1.10 of arXiv:2512.16486v1, exhaustion-independent form, with the
domination input discharged.**

The paper's family `⋃_Φ 𝒢^Φ ∪ 𝒲` quantifies both over the boundary convention
and over the exhaustion, so the two remaining inputs are stated over *every*
exhaustion:

* `hstoch` : the increasing-event comparison of Theorem 1.2 / Theorem 1.4(1)
  against Bernoulli percolation at a rate `s` below `p_c` (Theorem 1.4(1) is the
  AG reference shift that supplies it; nothing here assumes it);
* `h5_1` : Theorem 5.1 of the paper, for every convention and every exhaustion;
* `h518` : Proposition 1.8(2), every FK limit is Gibbs for some convention;
* `hne` : nonemptiness of the limit class for each exhaustion.

Conclusion: strong uniqueness of the full exhaustion-independent family, and
almost-sure non-percolation of the unique measure.  The ordered coupling used by
the paper's proof is *not* an input: it is produced from `hstoch` by
`exists_orderedCoupling_percolation_iff`. -/
theorem theorem_1_10_exhaustion_independent
    (hG : G.Connected) (exh₀ : BoxExhaustion.{w, w} G.edgeSet) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    (hne : ∀ exh : BoxExhaustion.{w, w} G.edgeSet, (FKLimitMeasures exh hq hp).Nonempty)
    (hstoch : ∀ (exh : BoxExhaustion.{w, w} G.edgeSet)
      (φ : ProbabilityMeasure (Configuration G.edgeSet)),
      φ ∈ FKLimitMeasures exh hq hp → BernoulliDominates G s φ)
    {μ₀ : ProbabilityMeasure (Configuration G.edgeSet)}
    (h5_1 : ∀ (exh : BoxExhaustion.{w, w} G.edgeSet)
      (Φ : BoundaryAssignment exh.box), DLRMeasures exh Φ hq hp = {μ₀})
    (h518 : ∀ (exh : BoxExhaustion.{w, w} G.edgeSet)
      (μ : ProbabilityMeasure (Configuration G.edgeSet)),
      μ ∈ FKLimitMeasures exh hq hp →
        ∃ Φ : BoundaryAssignment exh.box, μ ∈ DLRMeasures exh Φ hq hp) :
    (∀ exh : BoxExhaustion.{w, w} G.edgeSet, ∃! μ, μ ∈ FKFamily exh hq hp) ∧
      (∀ ν : ProbabilityMeasure (Configuration G.edgeSet),
        ν ∈ FKFamilyAll (G := G) (q := q) (p := p) hq hp → ν = μ₀) ∧
      ∀ᵐ ω ∂(μ₀ : Measure (Configuration G.edgeSet)), ω ∈ NonPercolating G := by
  have hlim : ∀ (exh : BoxExhaustion.{w, w} G.edgeSet)
      (μ : ProbabilityMeasure (Configuration G.edgeSet)),
      μ ∈ FKLimitMeasures exh hq hp → μ = μ₀ := by
    intro exh μ hμ
    obtain ⟨Φ, hΦ⟩ := h518 exh μ hμ
    rw [h5_1 exh Φ] at hΦ
    exact Set.mem_singleton_iff.mp hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro exh
    obtain ⟨w₀, hw₀⟩ := hne exh
    refine ⟨w₀, mem_fkFamily_of_mem_fkLimit hq hp exh hw₀, ?_⟩
    intro ν hν
    have hν₀ : ν = μ₀ := eq_of_unique_fkLimit hq hp exh (fun μ hμ => hlim exh μ hμ) ν hν
    rw [hν₀, hlim exh w₀ hw₀]
  · intro ν hν
    obtain ⟨exh, hν⟩ := Set.mem_iUnion.mp hν
    exact eq_of_unique_fkLimit hq hp exh (fun μ hμ => hlim exh μ hμ) ν hν
  · obtain ⟨w₀, hw₀⟩ := hne exh₀
    have hμ₀ : μ₀ ∈ FKLimitMeasures exh₀ hq hp := by
      rw [← hlim exh₀ w₀ hw₀]
      exact hw₀
    exact ae_nonPercolating_of_subcritical_domination_inequality hG exh₀ hq hp hs
      (hstoch exh₀) μ₀ hμ₀

end ExhaustionIndependentMain

end FK.InfiniteVolume
