import FK.NestedArmUniqueness
import FK.EssentialWindow
import FK.Theorem110Assembly

/-!
# Below the critical probability, Bernoulli percolation does not percolate

Stage 18, direction 8.  Theorems 1.9 and 1.10 of arXiv:2512.16486v1 both start
from the assertion that, when `max (p, p') < p_c (G)`, every FK limit measure is
dominated by a *subcritical* percolation, hence is a.s. non-percolating.  The
existing development defines `criticalProb` as `sSup {p : I | θ(p) = 0}` and
separately converts `θ ≡ 0` into almost-sure non-percolation
(`NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero`), but
the link `s < criticalProb → θ(s) = 0` was missing.

This file supplies it:

* `percolationProb_mono`: `θ` is nondecreasing in `p`, from the proved
  stochastic domination of Bernoulli product laws with ordered parameters
  (`EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le`) and the fact
  that `{cluster of o infinite}` is a measurable upper set.
* `percolationProb_eq_zero_of_lt_criticalProb`: `s < p_c (o)` implies `θ_o (s) = 0`.
  The proof is the contrapositive: if `θ(s) ≠ 0` then monotonicity kills every
  zero of `θ` above `s`, so `p_c = sSup {θ = 0} ≤ s`.
* `ae_nonPercolating_percolation_of_lt_criticalProb`: below `p_c` at every root,
  the Bernoulli product law is a.s. non-percolating.
* `ae_nonPercolating_of_dominated_by_subcritical`: any law monotonically
  dominated by that Bernoulli law is a.s. non-percolating — the paper's step
  "This implies that `φ`-a.s. there is no infinite cluster".
-/

open MeasureTheory ProbabilityTheory CurvatureVariance.Infra.Percolation
open scoped ENNReal unitInterval

namespace CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V} {o : V}

/-- The event that the open cluster of `o` is infinite is an upper set of
configurations. -/
theorem isUpperSet_infiniteOpenCluster (o : V) :
    IsUpperSet {ω : G.edgeSet → Bool | {x | OpenConnected G ω Set.univ o x}.Infinite} := by
  intro ω η hωη hω
  exact Set.Infinite.mono (fun x hx => OpenConnected.mono_config hx hωη) hω

/-- The event that the open cluster of `o` is infinite is measurable on a
countable connected locally finite graph. -/
theorem measurableSet_infiniteOpenCluster [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (o : V) :
    MeasurableSet {ω : G.edgeSet → Bool | {x | OpenConnected G ω Set.univ o x}.Infinite} := by
  rw [setOf_infinite_eq_iInter_armEvent hG o]
  exact MeasurableSet.iInter fun n => measurableSet_armEvent o n

/-- The percolation probability is nondecreasing in the parameter. -/
theorem percolationProb_mono [Countable V] [G.LocallyFinite] (hG : G.Connected)
    {p q : I} (hpq : p ≤ q) : percolationProb G o p ≤ percolationProb G o q := by
  rw [percolationProb_eq, percolationProb_eq]
  have hA : MeasurableSet
      {ω : G.edgeSet → Bool | {x | OpenConnected G ω Set.univ o x}.Infinite} :=
    measurableSet_infiniteOpenCluster hG o
  have hAu : IsUpperSet
      {ω : G.edgeSet → Bool | {x | OpenConnected G ω Set.univ o x}.Infinite} :=
    isUpperSet_infiniteOpenCluster o
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
    (E := G.edgeSet) (r := fun _ => p) (s := fun _ => q) (fun _ => hpq)
  exact FK.EssentialWindow.measure_le_of_stochasticallyDominates hdom hA hAu

/-- **Below the critical probability the percolation probability vanishes.**
`criticalProb G o` is `sSup {p : I | θ_o (p) = 0}`, so every `s` strictly below it
is a zero of `θ_o`. -/
theorem percolationProb_eq_zero_of_lt_criticalProb [Countable V] [G.LocallyFinite]
    (hG : G.Connected) {s : I} (hs : (s : ℝ) < criticalProb G o) :
    percolationProb G o s = 0 := by
  by_contra hne
  have hZle : ∀ a ∈ (Subtype.val '' {p : I | percolationProb G o p = 0}), a ≤ (s : ℝ) := by
    rintro _ ⟨q, hq, rfl⟩
    by_contra hlt
    have hsq : s ≤ q := le_of_lt (not_le.mp hlt)
    have hmono : percolationProb G o s ≤ percolationProb G o q :=
      percolationProb_mono (G := G) (o := o) hG hsq
    rw [hq] at hmono
    exact hne (le_antisymm hmono bot_le)
  have hsup : criticalProb G o ≤ (s : ℝ) := Real.sSup_le hZle s.2.1
  linarith

end CurvatureVariance.Infra.Percolation

namespace FK

/-- **Subcritical Bernoulli percolation does not percolate.**  If the Bernoulli
parameter is below the critical probability at every root, the product law is
almost surely non-percolating. -/
theorem ae_nonPercolating_percolation_of_lt_criticalProb {V : Type*} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x) :
    ∀ᵐ ω ∂(CurvatureVariance.Infra.Percolation.percolation G s),
      ω ∈ NonPercolating G :=
  InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero s
    (fun x => CurvatureVariance.Infra.Percolation.percolationProb_eq_zero_of_lt_criticalProb
      hG (hs x))

/-- **The subcritical domination step of Theorems 1.9 and 1.10.**  A law coupled
monotonically below a subcritical Bernoulli law is almost surely
non-percolating. -/
theorem ae_nonPercolating_of_dominated_by_subcritical {V : Type*} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected) {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    {μ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure μ]
    {γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool))}
    (hγfst : γ.map Prod.fst = μ)
    (hγsnd : γ.map Prod.snd = CurvatureVariance.Infra.Percolation.percolation G s)
    (horder : ∀ᵐ z ∂γ, z.1 ≤ z.2) :
    ∀ᵐ ω ∂μ, ω ∈ NonPercolating G :=
  ae_nonPercolating_of_orderedCoupling G hG hγfst hγsnd horder
    (ae_nonPercolating_percolation_of_lt_criticalProb hG hs)

end FK

namespace FK.InfiniteVolume

universe u v

/-- **The subcritical half of Theorem 1.10.**

Instantiate the abstract FK limit class at the edge type of an actual connected
locally finite graph.  If every FK limit measure is monotonically dominated by
Bernoulli percolation at a parameter below `p_c`, then every FK limit measure is
almost surely non-percolating.  This is the paper's step "This implies that
`φ`-a.s. there is no infinite cluster", and it needs no uniqueness input. -/
theorem ae_nonPercolating_of_subcritical_domination {V : Type u} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (exh : BoxExhaustion G.edgeSet) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    (hdom : ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp →
        ∃ γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool)),
          γ.map Prod.fst = (φ : Measure (G.edgeSet → Bool)) ∧
            γ.map Prod.snd = CurvatureVariance.Infra.Percolation.percolation G s ∧
              ∀ᵐ z ∂γ, z.1 ≤ z.2) :
    ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp →
        ∀ᵐ ω ∂(φ : Measure (G.edgeSet → Bool)), ω ∈ NonPercolating G := by
  intro φ hφ
  obtain ⟨γ, hγfst, hγsnd, hγord⟩ := hdom φ hφ
  exact ae_nonPercolating_of_dominated_by_subcritical hG hs hγfst hγsnd hγord

/-- **Theorem 1.10 modulo three named inputs.**

Conclusion of Theorem 1.10 of arXiv:2512.16486v1 — strong uniqueness together
with subcriticality of the unique FK measure — from:

* `hdom`: the domination conclusion of Theorem 1.4(1) (via Theorem 1.2 and the
  enhanced comparisons), at a Bernoulli parameter below `p_c`;
* `h5_1`: Theorem 5.1 of the paper for the chosen convention, i.e. that one
  convention class is a singleton;
* `h518`: Proposition 1.8(2), that every FK limit measure with at most one
  infinite cluster is Gibbs for that convention;
* `hne`: the standard compactness fact that some FK limit measure exists.

The strong-uniqueness half is `theorem_1_10_modulo_theorem_5_1`.  The
subcriticality half uses neither `h5_1` nor `h518` except to place `μ₀` in the
weak-limit class: the unique FK measure is a limit because the weak-limit class
is a nonempty subset of the total family. -/
theorem theorem_1_10_modulo_inputs {V : Type u} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (exh : BoxExhaustion G.edgeSet) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {s : unitInterval}
    (hs : ∀ x : V, (s : ℝ) < CurvatureVariance.Infra.Percolation.criticalProb G x)
    (hne : (FKLimitMeasures exh hq hp).Nonempty)
    (hdom : ∀ φ : ProbabilityMeasure (Configuration G.edgeSet),
      φ ∈ FKLimitMeasures exh hq hp →
        ∃ γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool)),
          γ.map Prod.fst = (φ : Measure (G.edgeSet → Bool)) ∧
            γ.map Prod.snd = CurvatureVariance.Infra.Percolation.percolation G s ∧
              ∀ᵐ z ∂γ, z.1 ≤ z.2)
    (Φ : BoundaryAssignment exh.box)
    {μ₀ : ProbabilityMeasure (Configuration G.edgeSet)}
    (h5_1 : DLRMeasures exh Φ hq hp = {μ₀})
    (h518 : ∀ μ : ProbabilityMeasure (Configuration G.edgeSet),
      μ ∈ FKLimitMeasures exh hq hp → μ ∈ DLRMeasures exh Φ hq hp) :
    (∃! μ : ProbabilityMeasure (Configuration G.edgeSet),
        μ ∈ FKFamily exh hq hp) ∧
      ∀ᵐ ω ∂(μ₀ : Measure (G.edgeSet → Bool)), ω ∈ NonPercolating G := by
  have hstrong := (theorem_1_10_modulo_theorem_5_1 hq hp exh Φ h5_1 h518).2
  have hμ₀ : μ₀ ∈ FKLimitMeasures exh hq hp := by
    obtain ⟨w, hw⟩ := hne
    have hmem : w ∈ DLRMeasures exh Φ hq hp := h518 w hw
    rw [h5_1] at hmem
    rw [Set.mem_singleton_iff] at hmem
    rwa [hmem] at hw
  exact ⟨hstrong,
    ae_nonPercolating_of_subcritical_domination hG exh hq hp hs hdom μ₀ hμ₀⟩

end FK.InfiniteVolume
