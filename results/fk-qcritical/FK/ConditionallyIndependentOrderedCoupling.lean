import FK.StrassenCountable

/-!
# Conditionally independent ordered couplings dominated by a common law

Source: Beffara--Faipeur--Oke, arXiv:2512.16486v1, proof of Theorem 5.1
(uniqueness through domination by a subcritical percolation).

The paper needs a coupling `(ω₁, ω₂, ω₃)` of two Gibbs measures `μ₁, μ₂` and a
common dominating law `ρ`, with `ω₁ ≤ ω₃` and `ω₂ ≤ ω₃` almost surely.  The
present module constructs the *conditionally independent* such coupling as the
fibre product

  `γ = ∫ ρ(dη) δ_η ⊗ ν₁(·|η) ⊗ ν₂(·|η)`,

where `νᵢ(·|η)` is the conditional law of `ωᵢ` given `ω₃ = η` in an ordinary
pairwise Strassen coupling of `μᵢ` and `ρ`; it is a genuine Markov kernel
supported on the lower cone `{ξ | ξ ≤ η}`.

Main results:

* `exists_dominatedKernel` — a pairwise ordered coupling of `μ` and `ρ`
  disintegrates into `ρ ⊗ₘ K` with `K η` supported on `{ξ | ξ ≤ η}`.
* `condIndepTripleLaw` — the fibre-product law on `Configuration E³`.
* `condIndepTripleLaw_fst/snd/third` — its three marginals.
* `prodKernel_support_fst/snd` — a.e. order support over the common coordinate.
* `condIndepTripleLaw_lintegral_mul` — the genuine conditional-independence
  identity: for measurable `f, g`, the joint integral of `f(ω₁) g(ω₂)`
  factorizes into the product of the two conditional integrals over `η`.
* `exists_condIndepOrderedTriple` — existence of the triple with all three
  marginals, a.e. order and the explicit kernel factorization.
* `HasOrderedTriple` and `hasOrderedTriple_iff` — existence of a triple with a
  common dominating coordinate is *equivalent* to `μ₁ ⪯ ρ` and `μ₂ ⪯ ρ`;
  no joint-extremality or martingale-optimality condition is needed.

Nonpercolation of `ρ` is deliberately not used here: it enters only when the
a.e. closed-boundary exhaustion `S_n(ω₃)` of the paper is built and the
reverse-martingale comparison along that random exhaustion is applied.

All results use only public imports and the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); the audit is at the end of the file.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace FKLimit

variable {E : Type*} [Countable E]

noncomputable def condIndepTripleLaw (ρ : Measure (Configuration E))
    (K1 K2 : Kernel (Configuration E) (Configuration E)) :
    Measure (Configuration E × Configuration E × Configuration E) :=
  (ρ ⊗ₘ (K1 ×ₖ K2)).map fun p : Configuration E × (Configuration E × Configuration E) =>
    (p.2.1, p.2.2, p.1)

lemma measurable_perm :
    Measurable fun p : Configuration E × (Configuration E × Configuration E) =>
      (p.2.1, p.2.2, p.1) := by
  fun_prop

lemma measurableSet_le_snd_fst :
    MeasurableSet {z : Configuration E × Configuration E | z.2 ≤ z.1} := by
  have h : {z : Configuration E × Configuration E | z.2 ≤ z.1}
      = ⋂ e : E, {z | z.2 e ≤ z.1 e} := by
    ext z
    simp [Pi.le_def]
  rw [h]
  refine MeasurableSet.iInter (fun e => ?_)
  have hcont : Continuous (fun f : E → Bool => f e) := continuous_apply e
  have h2e : Measurable fun z : Configuration E × Configuration E => z.2 e :=
    hcont.measurable.comp (measurable_snd : Measurable fun z : Configuration E × Configuration E => z.2)
  have h1e : Measurable fun z : Configuration E × Configuration E => z.1 e :=
    hcont.measurable.comp (measurable_fst : Measurable fun z : Configuration E × Configuration E => z.1)
  have hm : Measurable fun z : Configuration E × Configuration E => (z.1 e, z.2 e) := h1e.prod h2e
  exact MeasurableSet.preimage (t := {w : Bool × Bool | w.2 ≤ w.1})
    (Set.toFinite _).measurableSet hm

/-- The cone mass `η ↦ K η {ξ | ξ ≤ η}` is measurable in `η`, so the a.e.
support statement can be integrated against `ρ`. -/
lemma measurable_kernel_cone (K : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K] :
    Measurable fun η => K η {ξ : Configuration E | ξ ≤ η} := by
  have h : (fun η => K η {ξ : Configuration E | ξ ≤ η})
      = fun η => K η (Prod.mk η ⁻¹' {z : Configuration E × Configuration E | z.2 ≤ z.1}) := by
    funext η; rfl
  rw [h]
  exact Kernel.measurable_kernel_prodMk_left measurableSet_le_snd_fst

lemma measurableSet_le_fst_fixed (η : Configuration E) :
    MeasurableSet {ξ : Configuration E | ξ ≤ η} := by
  have h : {ξ : Configuration E | ξ ≤ η}
      = Prod.mk η ⁻¹' {z : Configuration E × Configuration E | z.2 ≤ z.1} := rfl
  rw [h]
  exact MeasurableSet.preimage measurableSet_le_snd_fst measurable_prodMk_left

lemma condIndepTripleLaw_third (ρ : Measure (Configuration E)) [IsProbabilityMeasure ρ]
    (K1 K2 : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K1] [IsMarkovKernel K2] :
    (condIndepTripleLaw ρ K1 K2).map (fun z : Configuration E × Configuration E × Configuration E => z.2.2) = ρ := by
  rw [condIndepTripleLaw, Measure.map_map (by fun_prop) measurable_perm]
  have h : (fun z : Configuration E × Configuration E × Configuration E => z.2.2)
      ∘ (fun p : Configuration E × (Configuration E × Configuration E) =>
          (p.2.1, p.2.2, p.1)) = Prod.fst := by
    funext p; rfl
  rw [h]
  exact Measure.fst_compProd ρ (K1 ×ₖ K2)


lemma condIndepTripleLaw_fst (ρ : Measure (Configuration E)) [IsProbabilityMeasure ρ]
    (K1 K2 : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K1] [IsMarkovKernel K2] :
    (condIndepTripleLaw ρ K1 K2).map (fun z : Configuration E × Configuration E × Configuration E => z.1)
      = (ρ ⊗ₘ K1).snd := by
  rw [condIndepTripleLaw, Measure.map_map (by fun_prop) measurable_perm]
  have h : (fun z : Configuration E × Configuration E × Configuration E => z.1)
      ∘ (fun p : Configuration E × (Configuration E × Configuration E) =>
          (p.2.1, p.2.2, p.1)) = Prod.fst ∘ Prod.snd := by
    funext p; rfl
  rw [h]
  rw [← Measure.map_map measurable_fst measurable_snd]
  rw [show Measure.map Prod.snd (ρ ⊗ₘ (K1 ×ₖ K2)) = (ρ ⊗ₘ (K1 ×ₖ K2)).snd from rfl]
  rw [Measure.snd_compProd]
  rw [Measure.map_comp (μ := ρ) (κ := K1 ×ₖ K2) (f := Prod.fst) measurable_fst]
  have hfst : (K1 ×ₖ K2).map Prod.fst = K1 := by
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod K1 K2
  rw [hfst, ← Measure.snd_compProd]

lemma condIndepTripleLaw_snd (ρ : Measure (Configuration E)) [IsProbabilityMeasure ρ]
    (K1 K2 : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K1] [IsMarkovKernel K2] :
    (condIndepTripleLaw ρ K1 K2).map (fun z : Configuration E × Configuration E × Configuration E => z.2.1)
      = (ρ ⊗ₘ K2).snd := by
  rw [condIndepTripleLaw, Measure.map_map (by fun_prop) measurable_perm]
  have h : (fun z : Configuration E × Configuration E × Configuration E => z.2.1)
      ∘ (fun p : Configuration E × (Configuration E × Configuration E) =>
          (p.2.1, p.2.2, p.1)) = Prod.snd ∘ Prod.snd := by
    funext p; rfl
  rw [h]
  rw [← Measure.map_map measurable_snd measurable_snd]
  rw [show Measure.map Prod.snd (ρ ⊗ₘ (K1 ×ₖ K2)) = (ρ ⊗ₘ (K1 ×ₖ K2)).snd from rfl]
  rw [Measure.snd_compProd]
  rw [Measure.map_comp (μ := ρ) (κ := K1 ×ₖ K2) (f := Prod.snd) measurable_snd]
  have hsnd : (K1 ×ₖ K2).map Prod.snd = K2 := by
    rw [← Kernel.snd_eq]
    exact Kernel.snd_prod K1 K2
  rw [hsnd, ← Measure.snd_compProd]


lemma ae_eq_one_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {p : α → Prop} (hp : MeasurableSet {a | p a})
    (h : ∀ᵐ a ∂μ, p a) : μ {a | p a} = 1 := by
  have h0 : μ {a | p a}ᶜ = 0 := by
    simpa [Set.compl_ofPred] using (MeasureTheory.ae_iff (μ := μ) (p := p)).mp h
  have hsum := measure_add_measure_compl (μ := μ) hp
  rw [h0, add_zero, measure_univ] at hsum
  exact hsum

theorem exists_dominatedKernel {μ ρ : ProbabilityMeasure (Configuration E)}
    (hdom : StochasticallyDominates ρ μ) :
    ∃ K : Kernel (Configuration E) (Configuration E), IsMarkovKernel K ∧
      (∀ᵐ η ∂(ρ : Measure (Configuration E)), K η {ξ | ξ ≤ η} = 1) ∧
      ((ρ : Measure (Configuration E)) ⊗ₘ K).fst = (ρ : Measure _) ∧
      (((ρ : Measure (Configuration E)) ⊗ₘ K).map Prod.snd) = (μ : Measure _) := by
  classical
  obtain ⟨κ, hfst, hsnd, hord⟩ :=
    CountableStrassen.exists_orderedCoupling_of_dominates (E := E) (μ := μ) (ν := ρ)
      (fun A hA hup => by
        have h := hdom A hA hup
        rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
          ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
        exact_mod_cast h)
  have hκm : (κ : Measure ((E → Bool) × (E → Bool))).map Prod.fst = (μ : Measure (E → Bool)) := by
    have := congrArg (fun x : ProbabilityMeasure (E → Bool) =>
      (x : Measure (E → Bool))) hfst
    simpa using this
  have hκs : (κ : Measure ((E → Bool) × (E → Bool))).map Prod.snd = (ρ : Measure (E → Bool)) := by
    have := congrArg (fun x : ProbabilityMeasure (E → Bool) =>
      (x : Measure (E → Bool))) hsnd
    simpa using this
  let ν : Measure ((E → Bool) × (E → Bool)) := (κ : Measure ((E → Bool) × (E → Bool))).map Prod.swap
  have hνfst : ν.fst = (ρ : Measure (E → Bool)) := by
    have h1 : ν.fst = (κ : Measure ((E → Bool) × (E → Bool))).map Prod.snd := by
      rw [Measure.fst]
      change ((κ : Measure ((E → Bool) × (E → Bool))).map Prod.swap).map Prod.fst
        = (κ : Measure ((E → Bool) × (E → Bool))).map Prod.snd
      rw [Measure.map_map measurable_fst measurable_swap]
      congr 1
    rw [h1, hκs]
  have hνsnd : ν.map Prod.snd = (μ : Measure (E → Bool)) := by
    change ((κ : Measure ((E → Bool) × (E → Bool))).map Prod.swap).map Prod.snd
      = (μ : Measure (E → Bool))
    rw [Measure.map_map measurable_snd measurable_swap]
    have hcomp : (Prod.snd ∘ Prod.swap : ((E → Bool) × (E → Bool)) → (E → Bool)) = Prod.fst := by
      funext z; rfl
    rw [hcomp, hκm]
  have hνord : ∀ᵐ z ∂ν, z.2 ≤ z.1 := by
    change ∀ᵐ z ∂(κ : Measure ((E → Bool) × (E → Bool))).map Prod.swap, z.2 ≤ z.1
    refine (MeasureTheory.ae_map_iff measurable_swap.aemeasurable ?_).mpr ?_
    · simpa using (measurableSet_le_snd_fst (E := E))
    · filter_upwards [hord] with z hz
      simpa using hz
  have hdis : ν.fst ⊗ₘ ν.condKernel = ν := Measure.disintegrate ν ν.condKernel
  have hae : ∀ᵐ η ∂ν.fst, ∀ᵐ ξ ∂ν.condKernel η, ξ ≤ η := by
    have hνord' : ∀ᵐ z ∂(ν.fst ⊗ₘ ν.condKernel), z.2 ≤ z.1 := by rwa [hdis]
    exact (Measure.ae_compProd_iff (measurableSet_le_snd_fst (E := E))).mp hνord'
  have hsupp : ∀ᵐ η ∂ν.fst, ν.condKernel η {ξ : E → Bool | ξ ≤ η} = 1 := by
    filter_upwards [hae] with η hη
    exact ae_eq_one_of_ae (measurableSet_le_fst_fixed η) hη
  refine ⟨ν.condKernel, inferInstance, ?_, ?_, ?_⟩
  · rw [hνfst] at hsupp
    exact hsupp
  · rw [← hνfst]
    exact Measure.fst_compProd ν.fst ν.condKernel
  · rw [← hνfst]
    rw [hdis]
    exact hνsnd


lemma measurableSet_le_fst_snd :
    MeasurableSet {z : Configuration E × Configuration E | z.1 ≤ z.2} := by
  have h : {z : Configuration E × Configuration E | z.1 ≤ z.2}
      = Prod.swap ⁻¹' {z : Configuration E × Configuration E | z.2 ≤ z.1} := rfl
  rw [h]
  exact MeasurableSet.preimage measurableSet_le_snd_fst measurable_swap

lemma measurableSet_fst_le_fixed (η : Configuration E) :
    MeasurableSet {q : Configuration E × Configuration E | q.1 ≤ η} := by
  have h : {q : Configuration E × Configuration E | q.1 ≤ η}
      = (fun q : Configuration E × Configuration E => (q.1, η)) ⁻¹'
        {z : Configuration E × Configuration E | z.1 ≤ z.2} := rfl
  rw [h]
  have hm : Measurable fun q : Configuration E × Configuration E => (q.1, η) := by
    fun_prop
  exact MeasurableSet.preimage measurableSet_le_fst_snd hm

lemma measurableSet_snd_le_fixed (η : Configuration E) :
    MeasurableSet {q : Configuration E × Configuration E | q.2 ≤ η} := by
  have h : {q : Configuration E × Configuration E | q.2 ≤ η}
      = (fun q : Configuration E × Configuration E => (q.2, η)) ⁻¹'
        {z : Configuration E × Configuration E | z.1 ≤ z.2} := rfl
  rw [h]
  have hm : Measurable fun q : Configuration E × Configuration E => (q.2, η) := by
    fun_prop
  exact MeasurableSet.preimage measurableSet_le_fst_snd hm

lemma measurableSet_pair_fst_le :
    MeasurableSet {p : Configuration E × (Configuration E × Configuration E) | p.2.1 ≤ p.1} := by
  have h : {p : Configuration E × (Configuration E × Configuration E) | p.2.1 ≤ p.1}
      = (fun p : Configuration E × (Configuration E × Configuration E) => (p.2.1, p.1)) ⁻¹'
        {z : Configuration E × Configuration E | z.1 ≤ z.2} := rfl
  rw [h]
  have hm : Measurable fun p : Configuration E × (Configuration E × Configuration E) =>
      (p.2.1, p.1) := by
    fun_prop
  exact MeasurableSet.preimage measurableSet_le_fst_snd hm

lemma measurableSet_pair_snd_le :
    MeasurableSet {p : Configuration E × (Configuration E × Configuration E) | p.2.2 ≤ p.1} := by
  have h : {p : Configuration E × (Configuration E × Configuration E) | p.2.2 ≤ p.1}
      = (fun p : Configuration E × (Configuration E × Configuration E) => (p.2.2, p.1)) ⁻¹'
        {z : Configuration E × Configuration E | z.1 ≤ z.2} := rfl
  rw [h]
  have hm : Measurable fun p : Configuration E × (Configuration E × Configuration E) =>
      (p.2.2, p.1) := by
    fun_prop
  exact MeasurableSet.preimage measurableSet_le_fst_snd hm

lemma prodKernel_support_fst {ρ : Measure (Configuration E)} [IsProbabilityMeasure ρ]
    (K1 K2 : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K1] [IsMarkovKernel K2]
    (h1 : ∀ᵐ η ∂ρ, K1 η {ξ : Configuration E | ξ ≤ η} = 1) :
    ∀ᵐ p ∂(ρ ⊗ₘ (K1 ×ₖ K2)), p.2.1 ≤ p.1 := by
  refine Measure.ae_compProd_of_ae_ae measurableSet_pair_fst_le ?_
  filter_upwards [h1] with η hη
  have hq : (K1 ×ₖ K2) η {q : Configuration E × Configuration E | q.1 ≤ η} = 1 := by
    rw [show {q : Configuration E × Configuration E | q.1 ≤ η}
        = Prod.fst ⁻¹' {ξ : Configuration E | ξ ≤ η} from rfl]
    rw [← Measure.map_apply measurable_fst (measurableSet_le_fst_fixed η)]
    rw [← Kernel.fst_apply]
    rw [Kernel.fst_prod]
    exact hη
  exact (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_fst_le_fixed η)).mpr hq

lemma prodKernel_support_snd {ρ : Measure (Configuration E)} [IsProbabilityMeasure ρ]
    (K1 K2 : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K1] [IsMarkovKernel K2]
    (h2 : ∀ᵐ η ∂ρ, K2 η {ξ : Configuration E | ξ ≤ η} = 1) :
    ∀ᵐ p ∂(ρ ⊗ₘ (K1 ×ₖ K2)), p.2.2 ≤ p.1 := by
  refine Measure.ae_compProd_of_ae_ae measurableSet_pair_snd_le ?_
  filter_upwards [h2] with η hη
  have hq : (K1 ×ₖ K2) η {q : Configuration E × Configuration E | q.2 ≤ η} = 1 := by
    rw [show {q : Configuration E × Configuration E | q.2 ≤ η}
        = Prod.snd ⁻¹' {ξ : Configuration E | ξ ≤ η} from rfl]
    rw [← Measure.map_apply measurable_snd (measurableSet_le_fst_fixed η)]
    rw [← Kernel.snd_apply]
    rw [Kernel.snd_prod]
    exact hη
  exact (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_snd_le_fixed η)).mpr hq


lemma measurableSet_triple_fst_le :
    MeasurableSet {z : Configuration E × Configuration E × Configuration E | z.1 ≤ z.2.2} := by
  have h : {z : Configuration E × Configuration E × Configuration E | z.1 ≤ z.2.2}
      = (fun z : Configuration E × Configuration E × Configuration E => (z.1, z.2.2)) ⁻¹'
        {w : Configuration E × Configuration E | w.1 ≤ w.2} := rfl
  rw [h]
  have hm : Measurable fun z : Configuration E × Configuration E × Configuration E =>
      (z.1, z.2.2) := by
    fun_prop
  exact MeasurableSet.preimage measurableSet_le_fst_snd hm

lemma measurableSet_triple_snd_le :
    MeasurableSet {z : Configuration E × Configuration E × Configuration E | z.2.1 ≤ z.2.2} := by
  have h : {z : Configuration E × Configuration E × Configuration E | z.2.1 ≤ z.2.2}
      = (fun z : Configuration E × Configuration E × Configuration E => (z.2.1, z.2.2)) ⁻¹'
        {w : Configuration E × Configuration E | w.1 ≤ w.2} := rfl
  rw [h]
  have hm : Measurable fun z : Configuration E × Configuration E × Configuration E =>
      (z.2.1, z.2.2) := by
    fun_prop
  exact MeasurableSet.preimage measurableSet_le_fst_snd hm

/-- **The conditionally independent ordered triple.**  If two probability measures
`μ1`, `μ2` are both stochastically dominated by the same `ρ`, then there is a
probability measure `γ` on triples `(ω1, ω2, η)` whose marginals are `μ1`, `μ2`,
`ρ`, whose first two coordinates are a.s. below the third, and which is built as
`ρ ⊗ₘ (K1 ×ₖ K2)`: conditionally on `η`, the coordinates `ω1` and `ω2` are
independent with laws `K1 η`, `K2 η`, each supported on the lower cone
`{ξ | ξ ≤ η}`.  No joint-extremality or martingale-optimality condition on the
pairwise couplings is needed: the two pairwise Strassen couplings are
disintegrated over their common `ρ`-marginal and combined by the product
kernel. -/
theorem exists_condIndepOrderedTriple {μ1 μ2 ρ : ProbabilityMeasure (Configuration E)}
    (h1 : StochasticallyDominates ρ μ1) (h2 : StochasticallyDominates ρ μ2) :
    ∃ (γ : ProbabilityMeasure (Configuration E × Configuration E × Configuration E))
      (K1 K2 : Kernel (Configuration E) (Configuration E)),
      IsMarkovKernel K1 ∧ IsMarkovKernel K2 ∧
      γ.map (fun z => z.1) = μ1 ∧
      γ.map (fun z => z.2.1) = μ2 ∧
      γ.map (fun z => z.2.2) = ρ ∧
      (∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
        z.1 ≤ z.2.2) ∧
      (∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
        z.2.1 ≤ z.2.2) ∧
      (γ : Measure (Configuration E × Configuration E × Configuration E))
        = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 ∧
      (∀ᵐ η ∂(ρ : Measure (Configuration E)), K1 η {ξ | ξ ≤ η} = 1) ∧
      (∀ᵐ η ∂(ρ : Measure (Configuration E)), K2 η {ξ | ξ ≤ η} = 1) := by
  classical
  obtain ⟨K1, hK1markov, hK1supp, -, hK1marg⟩ := exists_dominatedKernel h1
  obtain ⟨K2, hK2markov, hK2supp, -, hK2marg⟩ := exists_dominatedKernel h2
  let γ0 : Measure (Configuration E × Configuration E × Configuration E) :=
    condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2
  have hγ0prob : IsProbabilityMeasure γ0 := by
    dsimp [γ0, condIndepTripleLaw]
    infer_instance
  let γ : ProbabilityMeasure (Configuration E × Configuration E × Configuration E) := ⟨γ0, hγ0prob⟩
  have hγcoe : (γ : Measure (Configuration E × Configuration E × Configuration E)) = γ0 := rfl
  have hmap1 : γ.map (fun z : Configuration E × Configuration E × Configuration E => z.1) = μ1 := by
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [ProbabilityMeasure.toMeasure_map]
    change Measure.map (fun z : Configuration E × Configuration E × Configuration E => z.1) γ0
      = (μ1 : Measure (Configuration E))
    rw [show γ0 = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 from rfl]
    rw [condIndepTripleLaw_fst]
    simpa [Measure.snd] using hK1marg
  have hmap2 : γ.map (fun z : Configuration E × Configuration E × Configuration E => z.2.1) = μ2 := by
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [ProbabilityMeasure.toMeasure_map]
    change Measure.map (fun z : Configuration E × Configuration E × Configuration E => z.2.1) γ0
      = (μ2 : Measure (Configuration E))
    rw [show γ0 = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 from rfl]
    rw [condIndepTripleLaw_snd]
    simpa [Measure.snd] using hK2marg
  have hmap3 : γ.map (fun z : Configuration E × Configuration E × Configuration E => z.2.2) = ρ := by
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [ProbabilityMeasure.toMeasure_map]
    change Measure.map (fun z : Configuration E × Configuration E × Configuration E => z.2.2) γ0
      = (ρ : Measure (Configuration E))
    rw [show γ0 = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 from rfl]
    exact condIndepTripleLaw_third (ρ : Measure (Configuration E)) K1 K2
  have horder1 : ∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      z.1 ≤ z.2.2 := by
    rw [hγcoe]
    rw [show γ0 = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 from rfl]
    rw [condIndepTripleLaw]
    refine (MeasureTheory.ae_map_iff measurable_perm.aemeasurable (measurableSet_triple_fst_le (E := E))).mpr ?_
    exact prodKernel_support_fst K1 K2 hK1supp
  have horder2 : ∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      z.2.1 ≤ z.2.2 := by
    rw [hγcoe]
    rw [show γ0 = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 from rfl]
    rw [condIndepTripleLaw]
    refine (MeasureTheory.ae_map_iff measurable_perm.aemeasurable (measurableSet_triple_snd_le (E := E))).mpr ?_
    exact prodKernel_support_snd K1 K2 hK2supp
  exact ⟨γ, K1, K2, hK1markov, hK2markov, hmap1, hmap2, hmap3,
    horder1, horder2, hγcoe.trans (show γ0 = condIndepTripleLaw (ρ : Measure (Configuration E)) K1 K2 from rfl),
    hK1supp, hK2supp⟩


/-- Existence of a (not necessarily conditionally independent) triple coupling with
a common dominating third coordinate. -/
def HasOrderedTriple (μ1 μ2 ρ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∃ γ : ProbabilityMeasure (Configuration E × Configuration E × Configuration E),
    γ.map (fun z => z.1) = μ1 ∧
    γ.map (fun z => z.2.1) = μ2 ∧
    γ.map (fun z => z.2.2) = ρ ∧
    (∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      z.1 ≤ z.2.2) ∧
    (∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      z.2.1 ≤ z.2.2)

/-- A triple coupling determines the two pairwise dominations by projection. -/
theorem stochasticallyDominates_of_hasOrderedTriple
    {μ1 μ2 ρ : ProbabilityMeasure (Configuration E)}
    (h : HasOrderedTriple μ1 μ2 ρ) :
    StochasticallyDominates ρ μ1 ∧ StochasticallyDominates ρ μ2 := by
  obtain ⟨γ, hm1, hm2, hm3, ho1, ho2⟩ := h
  constructor
  · intro A hA hup
    have hmono : (γ : Measure (Configuration E × Configuration E × Configuration E))
        {z : Configuration E × Configuration E × Configuration E | z.1 ∈ A} ≤
        (γ : Measure (Configuration E × Configuration E × Configuration E))
          {z : Configuration E × Configuration E × Configuration E | z.2.2 ∈ A} := by
      apply measure_mono_ae
      filter_upwards [ho1] with z hz hzA
      exact hup hz hzA
    have hENN : (μ1 : Measure (Configuration E)) A ≤ (ρ : Measure (Configuration E)) A := by
      calc (μ1 : Measure (Configuration E)) A
          = (γ : Measure _) {z : Configuration E × Configuration E × Configuration E | z.1 ∈ A} := by
            rw [← hm1]
            exact ProbabilityMeasure.map_apply' γ (f := fun z : Configuration E × Configuration E × Configuration E => z.1) (by fun_prop) hA
        _ ≤ (γ : Measure _) {z : Configuration E × Configuration E × Configuration E | z.2.2 ∈ A} := hmono
        _ = (ρ : Measure (Configuration E)) A := by
            rw [← hm3]
            exact (ProbabilityMeasure.map_apply' γ (f := fun z : Configuration E × Configuration E × Configuration E => z.2.2) (by fun_prop) hA).symm
    exact ENNReal.coe_le_coe.mp (by simpa using hENN)
  · intro A hA hup
    have hmono : (γ : Measure (Configuration E × Configuration E × Configuration E))
        {z : Configuration E × Configuration E × Configuration E | z.2.1 ∈ A} ≤
        (γ : Measure (Configuration E × Configuration E × Configuration E))
          {z : Configuration E × Configuration E × Configuration E | z.2.2 ∈ A} := by
      apply measure_mono_ae
      filter_upwards [ho2] with z hz hzA
      exact hup hz hzA
    have hENN : (μ2 : Measure (Configuration E)) A ≤ (ρ : Measure (Configuration E)) A := by
      calc (μ2 : Measure (Configuration E)) A
          = (γ : Measure _) {z : Configuration E × Configuration E × Configuration E | z.2.1 ∈ A} := by
            rw [← hm2]
            exact ProbabilityMeasure.map_apply' γ (f := fun z : Configuration E × Configuration E × Configuration E => z.2.1) (by fun_prop) hA
        _ ≤ (γ : Measure _) {z : Configuration E × Configuration E × Configuration E | z.2.2 ∈ A} := hmono
        _ = (ρ : Measure (Configuration E)) A := by
            rw [← hm3]
            exact (ProbabilityMeasure.map_apply' γ (f := fun z : Configuration E × Configuration E × Configuration E => z.2.2) (by fun_prop) hA).symm
    exact ENNReal.coe_le_coe.mp (by simpa using hENN)

/-- **Equivalence: a common dominating coordinate exists iff both measures are
dominated by it.**  In particular, the conditionally independent ordered triple of
`exists_condIndepOrderedTriple` exists exactly under the usual pairwise domination
hypotheses; no additional joint-extremality condition is needed. -/
theorem hasOrderedTriple_iff {μ1 μ2 ρ : ProbabilityMeasure (Configuration E)} :
    HasOrderedTriple μ1 μ2 ρ ↔
      StochasticallyDominates ρ μ1 ∧ StochasticallyDominates ρ μ2 := by
  constructor
  · exact stochasticallyDominates_of_hasOrderedTriple
  · rintro ⟨h1, h2⟩
    obtain ⟨γ, K1, K2, -, -, hm1, hm2, hm3, ho1, ho2, -, -, -⟩ :=
      exists_condIndepOrderedTriple h1 h2
    exact ⟨γ, hm1, hm2, hm3, ho1, ho2⟩


/-- **Conditional independence, in integral form.**  Under the fibre-product law,
for bounded measurable functions of `ω1` and `ω2` the joint integral factors over
`η` into the product of the two conditional integrals.  This is the substantive
content of "conditionally independent given the dominating coordinate". -/
theorem condIndepTripleLaw_lintegral_mul
    (ρ : Measure (Configuration E)) [IsProbabilityMeasure ρ]
    (K1 K2 : Kernel (Configuration E) (Configuration E)) [IsMarkovKernel K1] [IsMarkovKernel K2]
    {f g : Configuration E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ z, f z.1 * g z.2.1 ∂(condIndepTripleLaw ρ K1 K2)
      = ∫⁻ η, (∫⁻ ξ, f ξ ∂K1 η) * (∫⁻ ξ, g ξ ∂K2 η) ∂ρ := by
  rw [condIndepTripleLaw]
  rw [MeasureTheory.lintegral_map (f := fun z : Configuration E × Configuration E × Configuration E =>
    f z.1 * g z.2.1) (g := fun p : Configuration E × (Configuration E × Configuration E) =>
      (p.2.1, p.2.2, p.1)) (by fun_prop) measurable_perm]
  rw [Measure.lintegral_compProd (f := fun p : Configuration E × (Configuration E × Configuration E) =>
    f p.2.1 * g p.2.2) (by fun_prop)]
  congr 1 with η
  rw [Kernel.prod_apply]
  exact MeasureTheory.lintegral_prod_mul hf.aemeasurable hg.aemeasurable

end FKLimit


/-! ## Axiom audit -/

#print axioms FKLimit.measurable_perm
#print axioms FKLimit.measurableSet_le_snd_fst
#print axioms FKLimit.measurableSet_le_fst_fixed
#print axioms FKLimit.measurableSet_le_fst_snd
#print axioms FKLimit.measurableSet_fst_le_fixed
#print axioms FKLimit.measurableSet_snd_le_fixed
#print axioms FKLimit.measurableSet_pair_fst_le
#print axioms FKLimit.measurableSet_pair_snd_le
#print axioms FKLimit.measurableSet_triple_fst_le
#print axioms FKLimit.measurableSet_triple_snd_le
#print axioms FKLimit.ae_eq_one_of_ae
#print axioms FKLimit.condIndepTripleLaw
#print axioms FKLimit.measurable_kernel_cone
#print axioms FKLimit.condIndepTripleLaw_fst
#print axioms FKLimit.condIndepTripleLaw_snd
#print axioms FKLimit.condIndepTripleLaw_third
#print axioms FKLimit.condIndepTripleLaw_lintegral_mul
#print axioms FKLimit.exists_dominatedKernel
#print axioms FKLimit.prodKernel_support_fst
#print axioms FKLimit.prodKernel_support_snd
#print axioms FKLimit.exists_condIndepOrderedTriple
#print axioms FKLimit.HasOrderedTriple
#print axioms FKLimit.stochasticallyDominates_of_hasOrderedTriple
#print axioms FKLimit.hasOrderedTriple_iff
