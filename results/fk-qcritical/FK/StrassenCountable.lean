import Mathlib
import FK.FiniteTransport
import FK.CountableOrderedCoupling
import FK.Proposition42

/-!
# Countable Strassen ordered coupling on `E → Bool`

The finite Strassen theorem of `FK.FiniteTransport` gives, for every finite coordinate
set `S`, an ordered coupling of the two `S`-marginals of probability measures `μ ν` on
the countable configuration space `E → Bool`.  This file performs the measure-level
infinite-volume lifting, which was the gap recorded in
`docs/FINITE-STRASSEN-TRANSPORT.md` ("a gluing lemma ... it feeds the standard
compactness assembly: ... this assembly is not formalised here").

## Finite-coordinate conditional fibre extension

* `condKernel_fibre_eq_one` : the conditional kernel of the graph law of `μ` along the
  finite projection `S` is concentrated on the matching fibre for a.e. `S`-coordinate.
  (Proved from `Measure.disintegrate` by comparing the mass of the graph set.)
* `exists_glued_coupling` : an ordered coupling `π` of the `S`-marginals extends to a
  genuine coupling `κ` of `μ` and `ν` with `κ`-a.e. order on `S` **and exact `S × S`
  cylinder marginal `π`**.  The construction samples the exterior coordinates from the
  two conditional kernels; it is a gluing step, not a restatement of finite Strassen.

## Cofinal compactness and measurable order

* `goodSet`, `isClosed_goodSet`, `goodSet_nonempty`, `goodSet_antitone` : the candidate
  sets of probability measures with prescribed marginals and full order on `S` are closed
  in the compact space `ProbabilityMeasure (C × C)` (Portmanteau for the closed level set,
  continuous marginals), nonempty at every finite level, and antitone in `S`.
* `order_eq_iInter_levelOrder` : the full pointwise order is the countable intersection of
  the closed finite-level order sets, so measure-one order at every finite level gives
  full pointwise-order support.

## Main results

* `exists_orderedCoupling_of_dominates` : **Strassen's hard direction on the countable
  product** — exact marginals, probability normalization and `κ`-a.e. pointwise order,
  obtained from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`.
* `exists_orderedCoupling_support` : the same with full mass on the closed order relation.
* `strassen_iff` : both directions (the converse uses
  `FiniteTransport.stochasticallyDominates_of_orderedCoupling`).
* `lintegral_le_of_stochasticallyDominates`,
  `measure_eq_zero_of_stochasticallyDominates` : transfer corollaries at the countable
  level (monotone observables, null upper events).
* `OrderedCylinderSystem`, `exists_global_coupling_of_system` : **projective-limit form** —
  any consistent ordered family of finite-cylinder couplings of `μ` and `ν` is realized by
  a global ordered coupling whose `S`-cylinder marginals are exactly the prescribed laws.
* `cylinderSystem`, `exists_orderedCylinderSystem`,
  `nonempty_orderedCylinderSystem_self` : the converse construction (the cylinder system of
  a global coupling), existence of systems from domination, and a direct diagonal
  non-vacuity example.
* `FKLimit.exists_orderedCoupling_of_stochasticallyDominates` (and its support form) :
  adapters to the project convention `FKLimit.StochasticallyDominates` on
  `Configuration E = E → Bool`.

Only the standard axioms are used (`propext`, `Classical.choice`, `Quot.sound`); the
finite-cylinder input is `FiniteTransport.exists_cylinder_ordered_coupling`, and the
infinite-volume statements are proved here rather than assumed.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace CountableStrassen


variable {E : Type*} [Countable E]

/-- Restriction of a configuration to a finite coordinate set. -/
def projF (S : Finset E) (x : E → Bool) : S → Bool := fun i => x i

lemma measurable_projF (S : Finset E) : Measurable (projF S) := by
  unfold projF; fun_prop

lemma continuous_projF (S : Finset E) : Continuous (projF S) := by
  unfold projF; fun_prop

/-- The graph map `x ↦ (x|_S, x)`. -/
def graphF (S : Finset E) (x : E → Bool) : (S → Bool) × (E → Bool) := (projF S x, x)

lemma measurable_graphF (S : Finset E) : Measurable (graphF S) :=
  (measurable_projF S).prod measurable_id

theorem graphF_fst (S : Finset E) (μ : Measure (E → Bool)) :
    (μ.map (graphF S)).fst = μ.map (projF S) := by
  have hid : Prod.fst ∘ graphF S = projF S := by funext x; rfl
  rw [Measure.fst, Measure.map_map measurable_fst (measurable_graphF S), hid]

theorem graphF_snd (S : Finset E) (μ : Measure (E → Bool)) :
    (μ.map (graphF S)).snd = μ := by
  have hid : Prod.snd ∘ graphF S = id := by funext x; rfl
  rw [Measure.snd, Measure.map_map measurable_snd (measurable_graphF S), hid, Measure.map_id]

/-- Disintegration of the graph law along the finite coordinate projection. -/
theorem graphF_disintegrate (S : Finset E) (μ : Measure (E → Bool)) [IsProbabilityMeasure μ] :
    μ.map (graphF S) = (μ.map (projF S)) ⊗ₘ (μ.map (graphF S)).condKernel := by
  rw [← graphF_fst S μ]
  exact (Measure.disintegrate (μ.map (graphF S)) (μ.map (graphF S)).condKernel).symm

/-- The finite-coordinate order condition, as a set of pairs of configurations. -/
def levelOrderF (S : Finset E) : Set ((E → Bool) × (E → Bool)) :=
  {z | projF S z.1 ≤ projF S z.2}

lemma levelOrderF_measurable (S : Finset E) : MeasurableSet (levelOrderF S) := by
  have h : levelOrderF S = (fun z : (E → Bool) × (E → Bool) => (projF S z.1, projF S z.2)) ⁻¹'
      {w : (S → Bool) × (S → Bool) | w.1 ≤ w.2} := rfl
  rw [h]
  exact MeasurableSet.preimage (Set.toFinite _).measurableSet
    ((measurable_projF S).comp measurable_fst |>.prod
      ((measurable_projF S).comp measurable_snd))

lemma isClosed_le_pairF (S : Finset E) :
    IsClosed {w : (S → Bool) × (S → Bool) | w.1 ≤ w.2} :=
  (Set.toFinite _).isClosed

lemma levelOrderF_closed (S : Finset E) : IsClosed (levelOrderF S) := by
  have hcont : Continuous fun z : (E → Bool) × (E → Bool) =>
      (projF S z.1, projF S z.2) :=
    ((continuous_projF S).comp continuous_fst).prodMk
      ((continuous_projF S).comp continuous_snd)
  exact (isClosed_le_pairF S).preimage hcont

/-- The full pointwise order is the intersection of the finite-level ones. -/
lemma order_eq_iInter_levelOrder :
    {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2} = ⋂ S : Finset E, levelOrderF S := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, levelOrderF]
  constructor
  · intro h S i
    exact h i
  · intro h e
    have h2 : projF {e} z.1 ≤ projF {e} z.2 := h {e}
    have h3 := h2 ⟨e, Finset.mem_singleton_self e⟩
    simpa [projF] using h3

/-- **Fibre support of the finite-coordinate conditional kernel.**  For the conditional
kernel of the graph law of `μ` along `S`, almost every `S`-coordinate `a` gets a law
concentrated on the fibre `{x | x|_S = a}`. -/
theorem condKernel_fibre_eq_one (S : Finset E) (μ : Measure (E → Bool)) [IsProbabilityMeasure μ] :
    ∀ᵐ a ∂(μ.map (projF S)),
      ((μ.map (graphF S)).condKernel a) {x : E → Bool | projF S x = a} = 1 := by
  classical
  set ρ : Measure ((S → Bool) × (E → Bool)) := μ.map (graphF S) with hρ
  set k : Kernel (S → Bool) (E → Bool) := ρ.condKernel with hk
  have hρprob : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_graphF S).aemeasurable).2 inferInstance
  set G : Set ((S → Bool) × (E → Bool)) := {w | w.1 = projF S w.2} with hGdef
  have hG : MeasurableSet G := by
    have h : G = (fun w : (S → Bool) × (E → Bool) => (w.1, projF S w.2)) ⁻¹'
        {v : (S → Bool) × (S → Bool) | v.1 = v.2} := rfl
    rw [h]
    have hm : Measurable fun w : (S → Bool) × (E → Bool) => (w.1, projF S w.2) :=
      measurable_fst.prodMk ((measurable_projF S).comp measurable_snd)
    exact hm (Set.toFinite _).measurableSet
  have hρG : ρ G = 1 := by
    rw [hρ, Measure.map_apply (measurable_graphF S) hG]
    have hone : graphF S ⁻¹' G = Set.univ := by
      ext x; simp [G, graphF]
    rw [hone, measure_univ]
  have hdis : ρ = (μ.map (projF S)) ⊗ₘ k := by
    rw [hρ, hk]; exact graphF_disintegrate S μ
  have hcompl : ((μ.map (projF S)) ⊗ₘ k) Gᶜ = 0 := by
    rw [← hdis, measure_compl hG (measure_ne_top ρ G), hρG, measure_univ, tsub_self]
  rw [Measure.compProd_apply hG.compl] at hcompl
  have hsec : ∀ a : S → Bool, Prod.mk a ⁻¹' Gᶜ = {x : E → Bool | projF S x = a}ᶜ := by
    intro a
    ext x
    simp [G, eq_comm]
  simp_rw [hsec] at hcompl
  have hmeas : Measurable fun a : S → Bool => k a ({x : E → Bool | projF S x = a}ᶜ) := by
    have h : Measurable fun a : S → Bool => k a (Prod.mk a ⁻¹' Gᶜ) :=
      Kernel.measurable_kernel_prodMk_left hG.compl
    simpa only [hsec] using h
  have hzero := (lintegral_eq_zero_iff hmeas).mp hcompl
  have hae : ∀ᵐ a ∂(μ.map (projF S)), k a ({x : E → Bool | projF S x = a}ᶜ) = 0 := by
    filter_upwards [hzero] with a ha
    simpa using ha
  filter_upwards [hae] with a ha
  have htop : k a Set.univ = 1 := measure_univ
  have hfib : MeasurableSet {x : E → Bool | projF S x = a} :=
    (Set.toFinite ({a} : Set (S → Bool))).measurableSet.preimage (measurable_projF S)
  have hsum : k a {x : E → Bool | projF S x = a} + k a {x : E → Bool | projF S x = a}ᶜ
      = 1 := by
    rw [measure_add_measure_compl hfib, htop]
  rw [ha, add_zero] at hsum
  exact hsum



variable {E : Type*} [Countable E]

/-- **Finite-coordinate gluing lemma.**  Given an ordered coupling `π` of the two
`S`-marginals of probability measures `μ ν` on `E → Bool`, there is a coupling `κ` of
`μ` and `ν` whose `S`-coordinates are ordered almost surely. -/
theorem exists_glued_coupling (S : Finset E) (μ ν : Measure (E → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure ((S → Bool) × (S → Bool))) [IsProbabilityMeasure π]
    (hπ1 : π.map Prod.fst = μ.map (projF S)) (hπ2 : π.map Prod.snd = ν.map (projF S))
    (hord : ∀ᵐ a ∂π, a.1 ≤ a.2) :
    ∃ κ : Measure ((E → Bool) × (E → Bool)), IsProbabilityMeasure κ ∧
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
      κ.map (Prod.map (projF S) (projF S)) = π ∧ κ (levelOrderF S) = 1 := by
  classical
  set kμ : Kernel (S → Bool) (E → Bool) := (μ.map (graphF S)).condKernel with hkμ
  set kν : Kernel (S → Bool) (E → Bool) := (ν.map (graphF S)).condKernel with hkν
  have hμmarkov : IsMarkovKernel kμ := by rw [hkμ]; infer_instance
  have hνmarkov : IsMarkovKernel kν := by rw [hkν]; infer_instance
  set κ0 : Kernel ((S → Bool) × (S → Bool)) ((E → Bool) × (E → Bool)) :=
    (kμ.comap Prod.fst measurable_fst) ×ₖ (kν.comap Prod.snd measurable_snd) with hκ0
  have hκ0markov : IsMarkovKernel κ0 := by rw [hκ0]; infer_instance
  refine ⟨κ0 ∘ₘ π, inferInstance, ?_, ?_, ?_, ?_⟩
  · -- first marginal
    rw [Measure.map_comp π κ0 measurable_fst]
    have hκ0fst : κ0.map Prod.fst = kμ.comap Prod.fst measurable_fst := by
      rw [← Kernel.fst_eq κ0, hκ0]
      exact Kernel.fst_prod _ _
    rw [hκ0fst, ← Kernel.comp_deterministic_eq_comap,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, hπ1]
    rw [← Measure.snd_compProd (μ.map (projF S)) kμ, hkμ, ← graphF_disintegrate, graphF_snd]
  · -- second marginal
    rw [Measure.map_comp π κ0 measurable_snd]
    have hκ0snd : κ0.map Prod.snd = kν.comap Prod.snd measurable_snd := by
      rw [← Kernel.snd_eq κ0, hκ0]
      exact Kernel.snd_prod _ _
    rw [hκ0snd, ← Kernel.comp_deterministic_eq_comap,
      ← Measure.comp_assoc, Measure.deterministic_comp_eq_map, hπ2]
    rw [← Measure.snd_compProd (ν.map (projF S)) kν, hkν, ← graphF_disintegrate, graphF_snd]
  · -- exact `S × S` cylinder marginal
    have hfibpre : ∀ z : S → Bool, MeasurableSet (projF S ⁻¹' ({z} : Set (S → Bool))) :=
      fun z => (Set.toFinite _).measurableSet.preimage (measurable_projF S)
    have hfibμ' : ∀ᵐ a ∂π,
        ((μ.map (graphF S)).condKernel a.1) {x : E → Bool | projF S x = a.1} = 1 := by
      refine MeasureTheory.ae_of_ae_map (f := Prod.fst) (p := fun b : S → Bool =>
        ((μ.map (graphF S)).condKernel b) {x : E → Bool | projF S x = b} = 1)
        measurable_fst.aemeasurable ?_
      rw [hπ1]
      exact condKernel_fibre_eq_one S μ
    have hfibν' : ∀ᵐ a ∂π,
        ((ν.map (graphF S)).condKernel a.2) {y : E → Bool | projF S y = a.2} = 1 := by
      refine MeasureTheory.ae_of_ae_map (f := Prod.snd) (p := fun b : S → Bool =>
        ((ν.map (graphF S)).condKernel b) {x : E → Bool | projF S x = b} = 1)
        measurable_snd.aemeasurable ?_
      rw [hπ2]
      exact condKernel_fibre_eq_one S ν
    have hker : ∀ᵐ a ∂π,
        (κ0.map (Prod.map (projF S) (projF S))) a
          = Kernel.deterministic id measurable_id a := by
      filter_upwards [hfibμ', hfibν'] with a h1 h2
      rw [Kernel.map_apply _ ((measurable_projF S).prodMap (measurable_projF S)) a,
        Kernel.deterministic_apply]
      have happly : κ0 a = (kμ a.1).prod (kν a.2) := by
        rw [hκ0, Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]
      rw [happly]
      have hdiracμ : (kμ a.1).map (projF S) = Measure.dirac a.1 := by
        have h1' : (kμ a.1) (projF S ⁻¹' ({a.1} : Set (S → Bool))) = 1 := by
          rw [hkμ]; exact h1
        apply Measure.ext_of_singleton
        intro z
        rw [Measure.map_apply (measurable_projF S) (measurableSet_singleton z),
          Measure.dirac_apply]
        by_cases hz : z = a.1
        · subst hz
          simp [h1']
        · have hmem : a.1 ∉ ({z} : Set (S → Bool)) := fun h => hz h.symm
          rw [Set.indicator_of_notMem hmem]
          have hsub : projF S ⁻¹' ({z} : Set (S → Bool)) ⊆
              (projF S ⁻¹' ({a.1} : Set (S → Bool)))ᶜ := by
            intro x hx
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
            simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
            rw [hx]; exact hz
          have hcompl : (kμ a.1) (projF S ⁻¹' ({a.1} : Set (S → Bool)))ᶜ = 0 := by
            rw [measure_compl (hfibpre a.1) (measure_ne_top _ _), h1', measure_univ, tsub_self]
          exact measure_mono_null hsub hcompl
      have hdiracν : (kν a.2).map (projF S) = Measure.dirac a.2 := by
        have h2' : (kν a.2) (projF S ⁻¹' ({a.2} : Set (S → Bool))) = 1 := by
          rw [hkν]; exact h2
        apply Measure.ext_of_singleton
        intro z
        rw [Measure.map_apply (measurable_projF S) (measurableSet_singleton z),
          Measure.dirac_apply]
        by_cases hz : z = a.2
        · subst hz
          simp [h2']
        · have hmem : a.2 ∉ ({z} : Set (S → Bool)) := fun h => hz h.symm
          rw [Set.indicator_of_notMem hmem]
          have hsub : projF S ⁻¹' ({z} : Set (S → Bool)) ⊆
              (projF S ⁻¹' ({a.2} : Set (S → Bool)))ᶜ := by
            intro x hx
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
            simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
            rw [hx]; exact hz
          have hcompl : (kν a.2) (projF S ⁻¹' ({a.2} : Set (S → Bool)))ᶜ = 0 := by
            rw [measure_compl (hfibpre a.2) (measure_ne_top _ _), h2', measure_univ, tsub_self]
          exact measure_mono_null hsub hcompl
      rw [(Measure.map_prod_map (kμ a.1) (kν a.2)
          (measurable_projF S) (measurable_projF S)).symm, hdiracμ, hdiracν,
        Measure.dirac_prod_dirac]
      rfl
    calc (κ0 ∘ₘ π).map (Prod.map (projF S) (projF S))
        = (κ0.map (Prod.map (projF S) (projF S))) ∘ₘ π :=
          Measure.map_comp π κ0 ((measurable_projF S).prodMap (measurable_projF S))
      _ = (Kernel.deterministic id measurable_id) ∘ₘ π := Measure.comp_congr hker
      _ = π.map id := Measure.deterministic_comp_eq_map measurable_id
      _ = π := Measure.map_id
  · -- order on the finite coordinates
    have hL : MeasurableSet (levelOrderF S) := levelOrderF_measurable S
    rw [Measure.bind_apply hL κ0.aemeasurable]
    have hfibμ' : ∀ᵐ a ∂π,
        ((μ.map (graphF S)).condKernel a.1) {x : E → Bool | projF S x = a.1} = 1 := by
      refine MeasureTheory.ae_of_ae_map (f := Prod.fst) (p := fun b : S → Bool =>
        ((μ.map (graphF S)).condKernel b) {x : E → Bool | projF S x = b} = 1)
        measurable_fst.aemeasurable ?_
      rw [hπ1]
      exact condKernel_fibre_eq_one S μ
    have hfibν' : ∀ᵐ a ∂π,
        ((ν.map (graphF S)).condKernel a.2) {y : E → Bool | projF S y = a.2} = 1 := by
      refine MeasureTheory.ae_of_ae_map (f := Prod.snd) (p := fun b : S → Bool =>
        ((ν.map (graphF S)).condKernel b) {x : E → Bool | projF S x = b} = 1)
        measurable_snd.aemeasurable ?_
      rw [hπ2]
      exact condKernel_fibre_eq_one S ν
    have hpt : ∀ᵐ a ∂π, κ0 a (levelOrderF S) = 1 := by
      filter_upwards [hord, hfibμ', hfibν'] with a ha hfibμ hfibν
      have happly : κ0 a = (kμ a.1).prod (kν a.2) := by
        rw [hκ0, Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]
      rw [happly]
      have hle : (kμ a.1) {x : E → Bool | projF S x = a.1} *
          (kν a.2) {y : E → Bool | projF S y = a.2} ≤
          ((kμ a.1).prod (kν a.2)) (levelOrderF S) := by
        rw [← Measure.prod_prod]
        refine measure_mono ?_
        intro z hz
        rw [Set.mem_prod] at hz
        simp only [Set.mem_ofPred_eq, levelOrderF]
        rw [hz.1, hz.2]
        exact ha
      have h1 : (kμ a.1) {x : E → Bool | projF S x = a.1} = 1 := by
        rw [hkμ]; exact hfibμ
      have h2 : (kν a.2) {y : E → Bool | projF S y = a.2} = 1 := by
        rw [hkν]; exact hfibν
      rw [h1, h2, one_mul] at hle
      refine le_antisymm ?_ hle
      calc ((kμ a.1).prod (kν a.2)) (levelOrderF S)
          ≤ ((kμ a.1).prod (kν a.2)) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by rw [measure_univ]
    calc ∫⁻ a, κ0 a (levelOrderF S) ∂π = ∫⁻ a, (1 : ℝ≥0∞) ∂π := lintegral_congr_ae hpt
      _ = 1 := by simp



variable {E : Type*} [Countable E]

/-- Converting a `ProbabilityMeasure` pushforward identity to the underlying measure. -/
lemma pm_map_eq_iff {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : ProbabilityMeasure X) (f : X → Y) (μ : ProbabilityMeasure Y) :
    κ.map f = μ ↔ (κ : Measure X).map f = (μ : Measure Y) := by
  constructor
  · intro h
    rw [← h, ProbabilityMeasure.toMeasure_map]
  · intro h
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [ProbabilityMeasure.toMeasure_map, h]

/-- The compact candidate set: probability measures on the product configuration space
with the two prescribed marginals and full order on the finite coordinate set `S`. -/
def goodSet (μ ν : ProbabilityMeasure (E → Bool)) (S : Finset E) :
    Set (ProbabilityMeasure ((E → Bool) × (E → Bool))) :=
  {κ | κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
    (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S) = 1}

theorem goodSet_antitone {μ ν : ProbabilityMeasure (E → Bool)} {S T : Finset E}
    (hST : S ⊆ T) : goodSet μ ν T ⊆ goodSet μ ν S := by
  rintro κ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  have hsub : levelOrderF T ⊆ levelOrderF S := by
    intro z hz i
    exact hz ⟨i.1, hST i.2⟩
  have hone : (1 : ℝ≥0∞) ≤ (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S) := by
    rw [← h3]
    exact measure_mono hsub
  exact le_antisymm (by
    calc (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)
        ≤ (κ : Measure ((E → Bool) × (E → Bool))) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ) hone

theorem isClosed_goodSet {μ ν : ProbabilityMeasure (E → Bool)} (S : Finset E) :
    IsClosed (goodSet μ ν S) := by
  classical
  refine isClosed_iff_forall_filter.mpr ?_
  intro κ F hFne hFs hFn
  have hcont1 : Continuous fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
      x.map Prod.fst := ProbabilityMeasure.continuous_map continuous_fst
  have hcont2 : Continuous fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
      x.map Prod.snd := ProbabilityMeasure.continuous_map continuous_snd
  have hev : ∀ᶠ x in F, x ∈ goodSet μ ν S := le_principal_iff.mp hFs
  refine ⟨?_, ?_, ?_⟩
  · refine IsClosed.mem_of_tendsto (s := {μ}) isClosed_singleton ?_
      (hev.mono (fun x hx => hx.1))
    exact (hcont1.tendsto κ).comp hFn
  · refine IsClosed.mem_of_tendsto (s := {ν}) isClosed_singleton ?_
      (hev.mono (fun x hx => hx.2.1))
    exact (hcont2.tendsto κ).comp hFn
  · have hconst : (fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
        (x : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)) =ᶠ[F] fun _ => (1 : ℝ≥0∞) :=
      hev.mono (fun x hx => hx.2.2)
    have hlim : limsup (fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
        (x : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)) F = 1 := by
      rw [limsup_congr hconst, limsup_const (1 : ℝ≥0∞)]
    have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hFn
      (levelOrderF_closed S)
    have hone : (1 : ℝ≥0∞) ≤
        (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S) := hlim ▸ hle
    refine le_antisymm ?_ hone
    calc (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)
        ≤ (κ : Measure ((E → Bool) × (E → Bool))) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ

theorem goodSet_nonempty {μ ν : ProbabilityMeasure (E → Bool)}
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A →
      (μ : Measure (E → Bool)) A ≤ (ν : Measure (E → Bool)) A) (S : Finset E) :
    (goodSet μ ν S).Nonempty := by
  classical
  obtain ⟨π, hπprob, hπ1, hπ2, hπord⟩ :=
    FiniteTransport.exists_cylinder_ordered_coupling (E := E) (μ : Measure (E → Bool))
      (ν : Measure (E → Bool)) ‹∀ A, MeasurableSet A → IsUpperSet A →
        (μ : Measure _) A ≤ (ν : Measure _) A› S
  have hπprob_inst := hπprob
  obtain ⟨κ, hκprob, hfst, hsnd, -, hL⟩ :=
    exists_glued_coupling S (μ : Measure (E → Bool)) (ν : Measure (E → Bool)) π hπ1 hπ2 hπord
  refine ⟨⟨κ, hκprob⟩, ?_, ?_, hL⟩
  · exact (pm_map_eq_iff ⟨κ, hκprob⟩ Prod.fst μ).mpr hfst
  · exact (pm_map_eq_iff ⟨κ, hκprob⟩ Prod.snd ν).mpr hsnd

/-- **Countable Strassen, hard direction.**  If `μ` is stochastically dominated by `ν`
on the countable configuration space `E → Bool`, there is a coupling of `μ` and `ν` whose
coordinates are pointwise ordered almost surely. -/
theorem exists_orderedCoupling_of_dominates {μ ν : ProbabilityMeasure (E → Bool)}
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A →
      (μ : Measure (E → Bool)) A ≤ (ν : Measure (E → Bool)) A) :
    ∃ κ : ProbabilityMeasure ((E → Bool) × (E → Bool)),
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
      ∀ᵐ z ∂(κ : Measure ((E → Bool) × (E → Bool))), z.1 ≤ z.2 := by
  classical
  have hdir : Directed (· ⊇ ·) (goodSet μ ν) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · exact goodSet_antitone (Finset.subset_union_left)
    · exact goodSet_antitone (Finset.subset_union_right)
  have hne : ∀ S : Finset E, (goodSet μ ν S).Nonempty := goodSet_nonempty hdom
  obtain ⟨κ, hκ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (goodSet μ ν) hdir hne
    (fun S => isCompact_univ.of_isClosed_subset (isClosed_goodSet S) (Set.subset_univ _))
    (fun S => isClosed_goodSet S)
  have hκS : ∀ S : Finset E, κ ∈ goodSet μ ν S := Set.mem_iInter.mp hκ
  refine ⟨κ, (hκS ∅).1, (hκS ∅).2.1, ?_⟩
  have hnull : ∀ S : Finset E,
      (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)ᶜ = 0 := by
    intro S
    rw [measure_compl (levelOrderF_measurable S) (measure_ne_top _ _), (hκS S).2.2,
      measure_univ, tsub_self]
  have hunion : (κ : Measure ((E → Bool) × (E → Bool))) (⋃ S : Finset E, (levelOrderF S)ᶜ)
      = 0 := measure_iUnion_null hnull
  have hcompl : (⋂ S : Finset E, levelOrderF S)ᶜ = ⋃ S : Finset E, (levelOrderF S)ᶜ :=
    Set.compl_iInter _
  rw [← hcompl] at hunion
  have hmeas : MeasurableSet (⋂ S : Finset E, levelOrderF S) :=
    MeasurableSet.iInter (fun S => levelOrderF_measurable S)
  have hlast : (κ : Measure ((E → Bool) × (E → Bool))) (⋂ S : Finset E, levelOrderF S) = 1 := by
    have hsum := measure_add_measure_compl (μ := (κ : Measure ((E → Bool) × (E → Bool)))) hmeas
    rw [hunion, measure_univ, add_zero] at hsum
    exact hsum
  have horder1 : (κ : Measure ((E → Bool) × (E → Bool)))
      {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2} = 1 := by
    rw [order_eq_iInter_levelOrder]
    exact hlast
  have hordermeas : MeasurableSet {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2} := by
    rw [order_eq_iInter_levelOrder]
    exact hmeas
  rw [ae_iff]
  rw [show {z : (E → Bool) × (E → Bool) | ¬ z.1 ≤ z.2}
      = {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2}ᶜ from rfl,
    measure_compl hordermeas (measure_ne_top _ _), horder1, measure_univ, tsub_self]


/-- Pointwise-order support form: the coupling carries full mass on the (closed) order
relation. -/
theorem exists_orderedCoupling_support {μ ν : ProbabilityMeasure (E → Bool)}
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A →
      (μ : Measure (E → Bool)) A ≤ (ν : Measure (E → Bool)) A) :
    ∃ κ : ProbabilityMeasure ((E → Bool) × (E → Bool)),
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
      (κ : Measure ((E → Bool) × (E → Bool))) {z | z.1 ≤ z.2} = 1 := by
  obtain ⟨κ, h1, h2, h3⟩ := exists_orderedCoupling_of_dominates hdom
  refine ⟨κ, h1, h2, ?_⟩
  have hcomp : (κ : Measure ((E → Bool) × (E → Bool)))
      {z : (E → Bool) × (E → Bool) | ¬ z.1 ≤ z.2} = 0 := by
    exact ae_iff.mp h3
  have hnull : ∀ S : Finset E,
      (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)ᶜ = 0 := by
    intro S
    refine measure_mono_null ?_ hcomp
    intro z hz hzord
    exact hz (fun i => hzord i)
  have hunion : (κ : Measure ((E → Bool) × (E → Bool)))
      (⋃ S : Finset E, (levelOrderF S)ᶜ) = 0 := measure_iUnion_null hnull
  have hmeas : MeasurableSet (⋂ S : Finset E, levelOrderF S) :=
    MeasurableSet.iInter (fun S => levelOrderF_measurable S)
  have hsum : (κ : Measure ((E → Bool) × (E → Bool))) (⋂ S : Finset E, levelOrderF S) = 1 := by
    have h := measure_add_measure_compl (μ := (κ : Measure ((E → Bool) × (E → Bool)))) hmeas
    rw [Set.compl_iInter, hunion, measure_univ, add_zero] at h
    exact h
  rw [order_eq_iInter_levelOrder]
  exact hsum

/-- **Strassen's theorem on the countable configuration space, both directions.** -/
theorem strassen_iff {μ ν : Measure (E → Bool)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A → μ A ≤ ν A) ↔
      ∃ κ : Measure ((E → Bool) × (E → Bool)), IsProbabilityMeasure κ ∧
        κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧ ∀ᵐ z ∂κ, z.1 ≤ z.2 := by
  constructor
  · intro hdom
    obtain ⟨κ, h1, h2, h3⟩ := exists_orderedCoupling_of_dominates
      (μ := ⟨μ, ‹IsProbabilityMeasure μ›⟩) (ν := ⟨ν, ‹IsProbabilityMeasure ν›⟩)
      (by simpa using hdom)
    exact ⟨(κ : Measure ((E → Bool) × (E → Bool))), inferInstance,
      (pm_map_eq_iff κ Prod.fst ⟨μ, inferInstance⟩).mp h1,
      (pm_map_eq_iff κ Prod.snd ⟨ν, inferInstance⟩).mp h2, h3⟩
  · rintro ⟨κ, hprob, hfst, hsnd, hord⟩ A hA hup
    exact FiniteTransport.stochasticallyDominates_of_orderedCoupling hfst hsnd hord A hA hup

/-- Increasing nonnegative observables are monotone in expectation under stochastic
domination on the countable configuration space. -/
theorem lintegral_le_of_stochasticallyDominates {μ ν : Measure (E → Bool)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A → μ A ≤ ν A)
    {f : (E → Bool) → ℝ≥0∞} (hf : Measurable f) (hmono : Monotone f) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ y, f y ∂ν := by
  obtain ⟨κ, hfst, hsnd, hord⟩ :=
    exists_orderedCoupling_of_dominates
      (μ := ⟨μ, ‹IsProbabilityMeasure μ›⟩) (ν := ⟨ν, ‹IsProbabilityMeasure ν›⟩)
      (by simpa using hdom)
  have hfst' : (κ : Measure ((E → Bool) × (E → Bool))).map Prod.fst = μ :=
    (pm_map_eq_iff κ Prod.fst ⟨μ, inferInstance⟩).mp hfst
  have hsnd' : (κ : Measure ((E → Bool) × (E → Bool))).map Prod.snd = ν :=
    (pm_map_eq_iff κ Prod.snd ⟨ν, inferInstance⟩).mp hsnd
  exact FiniteTransport.lintegral_le_of_orderedCoupling hfst' hsnd' hord hf hmono

/-- An upper event that is null under the dominating measure is null under the dominated
one, at the countable level. -/
lemma measure_eq_zero_of_stochasticallyDominates {μ ν : Measure (E → Bool)}
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A → μ A ≤ ν A)
    {A : Set (E → Bool)} (hA : MeasurableSet A) (hup : IsUpperSet A) (hν : ν A = 0) :
    μ A = 0 :=
  le_antisymm (hν ▸ hdom A hA hup) (by simp)

/-! ### Realizing a consistent ordered finite-cylinder system (projective limit) -/

/-- Restriction of a configuration on `T` to a subset `S ⊆ T`. -/
def projSub {S T : Finset E} (h : S ⊆ T) (x : T → Bool) : S → Bool := fun i => x ⟨i.1, h i.2⟩

lemma measurable_projSub {S T : Finset E} (h : S ⊆ T) : Measurable (projSub h) := by
  unfold projSub; fun_prop

lemma continuous_projSub {S T : Finset E} (h : S ⊆ T) : Continuous (projSub h) := by
  unfold projSub; fun_prop

/-- A consistent ordered system of finite-cylinder couplings of `μ` and `ν`: every finite
coordinate set carries an ordered coupling of the two marginals, and the couplings are
compatible under restriction.  Such a system is the input of the countable Strassen lift;
it is *not* constructed here (that is a finite-dimensional selection problem), but any such
system is realized by a global ordered coupling with exactly these cylinder laws. -/
structure OrderedCylinderSystem (μ ν : ProbabilityMeasure (E → Bool)) where
  law : (S : Finset E) → Measure ((S → Bool) × (S → Bool))
  isProb : ∀ S, IsProbabilityMeasure (law S)
  fst_eq : ∀ S, (law S).map Prod.fst = (μ : Measure (E → Bool)).map (projF S)
  snd_eq : ∀ S, (law S).map Prod.snd = (ν : Measure (E → Bool)).map (projF S)
  ordered : ∀ S, ∀ᵐ z ∂(law S), z.1 ≤ z.2
  consistent : ∀ (S T : Finset E) (h : S ⊆ T),
    (law T).map (Prod.map (projSub h) (projSub h)) = law S

/-- Candidate set with the exact prescribed cylinder law. -/
def cylGoodSet {μ ν : ProbabilityMeasure (E → Bool)} (𝒮 : OrderedCylinderSystem μ ν)
    (S : Finset E) : Set (ProbabilityMeasure ((E → Bool) × (E → Bool))) :=
  {κ | κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
    κ.map (Prod.map (projF S) (projF S)) = ⟨𝒮.law S, 𝒮.isProb S⟩ ∧
    (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S) = 1}

theorem cylGoodSet_nonempty {μ ν : ProbabilityMeasure (E → Bool)}
    (𝒮 : OrderedCylinderSystem μ ν) (S : Finset E) : (cylGoodSet 𝒮 S).Nonempty := by
  classical
  have h𝒮S : IsProbabilityMeasure (𝒮.law S) := 𝒮.isProb S
  obtain ⟨κ, hκprob, hfst, hsnd, hcyl, hL⟩ :=
    exists_glued_coupling S (μ : Measure (E → Bool)) (ν : Measure (E → Bool))
      (𝒮.law S) (𝒮.fst_eq S) (𝒮.snd_eq S) (𝒮.ordered S)
  exact ⟨⟨κ, hκprob⟩, (pm_map_eq_iff ⟨κ, hκprob⟩ Prod.fst μ).mpr hfst,
    (pm_map_eq_iff ⟨κ, hκprob⟩ Prod.snd ν).mpr hsnd,
    (pm_map_eq_iff ⟨κ, hκprob⟩ (Prod.map (projF S) (projF S)) ⟨𝒮.law S, 𝒮.isProb S⟩).mpr hcyl,
    hL⟩

lemma cylGoodSet_antitone {μ ν : ProbabilityMeasure (E → Bool)}
    (𝒮 : OrderedCylinderSystem μ ν) {S T : Finset E} (hST : S ⊆ T) :
    cylGoodSet 𝒮 T ⊆ cylGoodSet 𝒮 S := by
  rintro κ ⟨h1, h2, h3, h4⟩
  have h3' : (κ : Measure ((E → Bool) × (E → Bool))).map (Prod.map (projF T) (projF T))
      = 𝒮.law T := (pm_map_eq_iff κ _ ⟨𝒮.law T, 𝒮.isProb T⟩).mp h3
  refine ⟨h1, h2, ?_, ?_⟩
  · refine (pm_map_eq_iff κ _ ⟨𝒮.law S, 𝒮.isProb S⟩).mpr ?_
    have hcomp : (Prod.map (projSub hST) (projSub hST)) ∘
        (Prod.map (projF T) (projF T)) = Prod.map (projF S) (projF S) := by
      funext x
      rfl
    calc (κ : Measure ((E → Bool) × (E → Bool))).map (Prod.map (projF S) (projF S))
        = (κ : Measure ((E → Bool) × (E → Bool))).map
            ((Prod.map (projSub hST) (projSub hST)) ∘ (Prod.map (projF T) (projF T))) := by
          rw [hcomp]
      _ = ((κ : Measure ((E → Bool) × (E → Bool))).map
            (Prod.map (projF T) (projF T))).map (Prod.map (projSub hST) (projSub hST)) :=
          (Measure.map_map ((measurable_projSub hST).prodMap (measurable_projSub hST))
            ((measurable_projF T).prodMap (measurable_projF T))).symm
      _ = (𝒮.law T).map (Prod.map (projSub hST) (projSub hST)) := by rw [h3']
      _ = 𝒮.law S := 𝒮.consistent S T hST
  · have hsub : levelOrderF T ⊆ levelOrderF S := by
      intro z hz i
      exact hz ⟨i.1, hST i.2⟩
    have hone : (1 : ℝ≥0∞) ≤
        (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S) := by
      rw [← h4]
      exact measure_mono hsub
    refine le_antisymm ?_ hone
    calc (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)
        ≤ (κ : Measure ((E → Bool) × (E → Bool))) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ

theorem isClosed_cylGoodSet {μ ν : ProbabilityMeasure (E → Bool)}
    (𝒮 : OrderedCylinderSystem μ ν) (S : Finset E) : IsClosed (cylGoodSet 𝒮 S) := by
  classical
  refine isClosed_iff_forall_filter.mpr ?_
  intro κ F hFne hFs hFn
  have hcont1 : Continuous fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
      x.map Prod.fst := ProbabilityMeasure.continuous_map continuous_fst
  have hcont2 : Continuous fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
      x.map Prod.snd := ProbabilityMeasure.continuous_map continuous_snd
  have hcont3 : Continuous fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
      x.map (Prod.map (projF S) (projF S)) :=
    ProbabilityMeasure.continuous_map ((continuous_projF S).prodMap (continuous_projF S))
  have hev : ∀ᶠ x in F, x ∈ cylGoodSet 𝒮 S := le_principal_iff.mp hFs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsClosed.mem_of_tendsto (s := {μ}) isClosed_singleton ((hcont1.tendsto κ).comp hFn)
      (hev.mono (fun x hx => hx.1))
  · exact IsClosed.mem_of_tendsto (s := {ν}) isClosed_singleton ((hcont2.tendsto κ).comp hFn)
      (hev.mono (fun x hx => hx.2.1))
  · exact IsClosed.mem_of_tendsto (s := {⟨𝒮.law S, 𝒮.isProb S⟩}) isClosed_singleton
      ((hcont3.tendsto κ).comp hFn) (hev.mono (fun x hx => hx.2.2.1))
  · have hconst : (fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
        (x : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)) =ᶠ[F] fun _ => (1 : ℝ≥0∞) :=
      hev.mono (fun x hx => hx.2.2.2)
    have hlim : limsup (fun x : ProbabilityMeasure ((E → Bool) × (E → Bool)) =>
        (x : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)) F = 1 := by
      rw [limsup_congr hconst, limsup_const (1 : ℝ≥0∞)]
    have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hFn
      (levelOrderF_closed S)
    have hone : (1 : ℝ≥0∞) ≤
        (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S) := hlim ▸ hle
    refine le_antisymm ?_ hone
    calc (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)
        ≤ (κ : Measure ((E → Bool) × (E → Bool))) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ

/-- **Realization of a consistent ordered finite-cylinder system.**  Any compatible family
of ordered finite-cylinder couplings of two probability measures on `E → Bool` is the
cylinder system of a single global ordered coupling.  This is the projective-limit form of
the countable Strassen lift: the finite systems are input, the global ordered coupling with
*exactly* the prescribed cylinder marginals is constructed. -/
theorem exists_global_coupling_of_system {μ ν : ProbabilityMeasure (E → Bool)}
    (𝒮 : OrderedCylinderSystem μ ν) :
    ∃ κ : ProbabilityMeasure ((E → Bool) × (E → Bool)),
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
      (∀ᵐ z ∂(κ : Measure ((E → Bool) × (E → Bool))), z.1 ≤ z.2) ∧
      (∀ S : Finset E,
        (κ : Measure ((E → Bool) × (E → Bool))).map (Prod.map (projF S) (projF S))
          = 𝒮.law S) := by
  classical
  have hdir : Directed (· ⊇ ·) (cylGoodSet 𝒮) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · exact cylGoodSet_antitone 𝒮 Finset.subset_union_left
    · exact cylGoodSet_antitone 𝒮 Finset.subset_union_right
  obtain ⟨κ, hκ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (cylGoodSet 𝒮) hdir (fun S => cylGoodSet_nonempty 𝒮 S)
    (fun S => isCompact_univ.of_isClosed_subset (isClosed_cylGoodSet 𝒮 S) (Set.subset_univ _))
    (fun S => isClosed_cylGoodSet 𝒮 S)
  have hκS : ∀ S : Finset E, κ ∈ cylGoodSet 𝒮 S := Set.mem_iInter.mp hκ
  refine ⟨κ, (hκS ∅).1, (hκS ∅).2.1, ?_, fun S =>
    (pm_map_eq_iff κ _ ⟨𝒮.law S, 𝒮.isProb S⟩).mp (hκS S).2.2.1⟩
  have hnull : ∀ S : Finset E,
      (κ : Measure ((E → Bool) × (E → Bool))) (levelOrderF S)ᶜ = 0 := by
    intro S
    rw [measure_compl (levelOrderF_measurable S) (measure_ne_top _ _), (hκS S).2.2.2,
      measure_univ, tsub_self]
  have hunion : (κ : Measure ((E → Bool) × (E → Bool))) (⋃ S : Finset E, (levelOrderF S)ᶜ)
      = 0 := measure_iUnion_null hnull
  have hcompl : (⋂ S : Finset E, levelOrderF S)ᶜ = ⋃ S : Finset E, (levelOrderF S)ᶜ :=
    Set.compl_iInter _
  rw [← hcompl] at hunion
  have hmeas : MeasurableSet (⋂ S : Finset E, levelOrderF S) :=
    MeasurableSet.iInter (fun S => levelOrderF_measurable S)
  have hlast : (κ : Measure ((E → Bool) × (E → Bool))) (⋂ S : Finset E, levelOrderF S) = 1 := by
    have hsum := measure_add_measure_compl (μ := (κ : Measure ((E → Bool) × (E → Bool)))) hmeas
    rw [hunion, measure_univ, add_zero] at hsum
    exact hsum
  have horder1 : (κ : Measure ((E → Bool) × (E → Bool)))
      {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2} = 1 := by
    rw [order_eq_iInter_levelOrder]
    exact hlast
  have hordermeas : MeasurableSet {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2} := by
    rw [order_eq_iInter_levelOrder]
    exact hmeas
  rw [ae_iff]
  rw [show {z : (E → Bool) × (E → Bool) | ¬ z.1 ≤ z.2}
      = {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2}ᶜ from rfl,
    measure_compl hordermeas (measure_ne_top _ _), horder1, measure_univ, tsub_self]

/-- **The cylinder system of a global ordered coupling.**  Conversely to
`exists_global_coupling_of_system`, every global coupling with the two marginals and
pointwise order generates a genuine `OrderedCylinderSystem`; hence the hypothesis class of
the projective-limit theorem is exactly the class of cylinder systems of global ordered
couplings (no extra compatibility is hidden in the definition). -/
noncomputable def cylinderSystem {μ ν : ProbabilityMeasure (E → Bool)}
    (κ : ProbabilityMeasure ((E → Bool) × (E → Bool)))
    (hμ : κ.map Prod.fst = μ) (hν : κ.map Prod.snd = ν)
    (hord : ∀ᵐ z ∂(κ : Measure ((E → Bool) × (E → Bool))), z.1 ≤ z.2) :
    OrderedCylinderSystem μ ν where
  law S := (κ : Measure ((E → Bool) × (E → Bool))).map (Prod.map (projF S) (projF S))
  isProb S := by
    have hmeas : Measurable (Prod.map (projF S) (projF S)) :=
      (measurable_projF S).prodMap (measurable_projF S)
    exact (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  fst_eq S := by
    have hmeas : Measurable (Prod.map (projF S) (projF S)) :=
      (measurable_projF S).prodMap (measurable_projF S)
    have hcomp : Prod.fst ∘ (Prod.map (projF S) (projF S)) = projF S ∘ Prod.fst := rfl
    calc ((κ : Measure ((E → Bool) × (E → Bool))).map (Prod.map (projF S) (projF S))).map
          Prod.fst
        = (κ : Measure ((E → Bool) × (E → Bool))).map
            (Prod.fst ∘ (Prod.map (projF S) (projF S))) := by
          rw [Measure.map_map measurable_fst hmeas]
      _ = (κ : Measure ((E → Bool) × (E → Bool))).map (projF S ∘ Prod.fst) := by rw [hcomp]
      _ = ((κ : Measure ((E → Bool) × (E → Bool))).map Prod.fst).map (projF S) := by
          rw [Measure.map_map (measurable_projF S) measurable_fst]
      _ = (μ : Measure (E → Bool)).map (projF S) := by
          rw [(pm_map_eq_iff κ Prod.fst μ).mp hμ]
  snd_eq S := by
    have hmeas : Measurable (Prod.map (projF S) (projF S)) :=
      (measurable_projF S).prodMap (measurable_projF S)
    have hcomp : Prod.snd ∘ (Prod.map (projF S) (projF S)) = projF S ∘ Prod.snd := rfl
    calc ((κ : Measure ((E → Bool) × (E → Bool))).map (Prod.map (projF S) (projF S))).map
          Prod.snd
        = (κ : Measure ((E → Bool) × (E → Bool))).map
            (Prod.snd ∘ (Prod.map (projF S) (projF S))) := by
          rw [Measure.map_map measurable_snd hmeas]
      _ = (κ : Measure ((E → Bool) × (E → Bool))).map (projF S ∘ Prod.snd) := by rw [hcomp]
      _ = ((κ : Measure ((E → Bool) × (E → Bool))).map Prod.snd).map (projF S) := by
          rw [Measure.map_map (measurable_projF S) measurable_snd]
      _ = (ν : Measure (E → Bool)).map (projF S) := by
          rw [(pm_map_eq_iff κ Prod.snd ν).mp hν]
  ordered S := by
    have hmeas : Measurable (Prod.map (projF S) (projF S)) :=
      (measurable_projF S).prodMap (measurable_projF S)
    refine (MeasureTheory.ae_map_iff (p := fun z : (S → Bool) × (S → Bool) => z.1 ≤ z.2)
      hmeas.aemeasurable (isClosed_le_pairF S).measurableSet).mpr ?_
    exact hord.mono (fun z hz i => hz i)
  consistent S T h := by
    have hS : Measurable (Prod.map (projF S) (projF S)) :=
      (measurable_projF S).prodMap (measurable_projF S)
    have hT : Measurable (Prod.map (projF T) (projF T)) :=
      (measurable_projF T).prodMap (measurable_projF T)
    have hsub : Measurable (Prod.map (projSub h) (projSub h)) :=
      (measurable_projSub h).prodMap (measurable_projSub h)
    have hcomp : (Prod.map (projSub h) (projSub h)) ∘ (Prod.map (projF T) (projF T))
        = Prod.map (projF S) (projF S) := by
      funext x
      rfl
    rw [Measure.map_map hsub hT, hcomp]

/-- **Existence of ordered cylinder systems from domination.**  Combining the countable
Strassen theorem with `cylinderSystem`: every dominated pair of probability measures on
`E → Bool` admits a consistent ordered finite-cylinder system.  Together with
`exists_global_coupling_of_system` this shows that the compatibility input of the
projective-limit theorem is not an extra obstruction. -/
theorem exists_orderedCylinderSystem {μ ν : ProbabilityMeasure (E → Bool)}
    (hdom : ∀ A : Set (E → Bool), MeasurableSet A → IsUpperSet A →
      (μ : Measure (E → Bool)) A ≤ (ν : Measure (E → Bool)) A) :
    Nonempty (OrderedCylinderSystem μ ν) := by
  obtain ⟨κ, hμ, hν, hord⟩ := exists_orderedCoupling_of_dominates hdom
  exact ⟨cylinderSystem κ hμ hν hord⟩

/-- **Non-vacuity of the cylinder-system class.**  For a single probability measure `μ`
the diagonal system on every finite coordinate set is a genuine ordered cylinder system.
It is built here directly from the diagonal graph law, without using domination or the
countable Strassen theorem, so the compatibility input of
`exists_global_coupling_of_system` is not circular. -/
theorem nonempty_orderedCylinderSystem_self (μ : ProbabilityMeasure (E → Bool)) :
    Nonempty (OrderedCylinderSystem μ μ) := by
  classical
  have hmeas : Measurable (fun x : E → Bool => (x, x)) :=
    measurable_id.prodMk measurable_id
  have hprob : IsProbabilityMeasure ((μ : Measure (E → Bool)).map fun x => (x, x)) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  obtain ⟨κ, hκ⟩ : ∃ κ : ProbabilityMeasure ((E → Bool) × (E → Bool)),
      (κ : Measure ((E → Bool) × (E → Bool))) = (μ : Measure (E → Bool)).map
        (fun x => (x, x)) := ⟨⟨_, hprob⟩, rfl⟩
  have hfst : κ.map Prod.fst = μ := by
    refine (pm_map_eq_iff κ Prod.fst μ).mpr ?_
    rw [hκ, Measure.map_map measurable_fst hmeas,
      show Prod.fst ∘ (fun x : E → Bool => (x, x)) = id from rfl, Measure.map_id]
  have hsnd : κ.map Prod.snd = μ := by
    refine (pm_map_eq_iff κ Prod.snd μ).mpr ?_
    rw [hκ, Measure.map_map measurable_snd hmeas,
      show Prod.snd ∘ (fun x : E → Bool => (x, x)) = id from rfl, Measure.map_id]
  have hord : ∀ᵐ z ∂(κ : Measure ((E → Bool) × (E → Bool))), z.1 ≤ z.2 := by
    have hmeas2 : MeasurableSet {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2} := by
      rw [order_eq_iInter_levelOrder]
      exact MeasurableSet.iInter (fun S => levelOrderF_measurable S)
    rw [ae_iff, hκ,
      show {a : (E → Bool) × (E → Bool) | ¬ a.1 ≤ a.2}
        = {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2}ᶜ from rfl,
      Measure.map_apply hmeas hmeas2.compl]
    have hempty : (fun x : E → Bool => (x, x)) ⁻¹'
        {z : (E → Bool) × (E → Bool) | z.1 ≤ z.2}ᶜ = ∅ := by
      ext x
      simp
    rw [hempty, measure_empty]
  exact ⟨cylinderSystem κ hfst hsnd hord⟩

end CountableStrassen

namespace FKLimit

/-- Countable Strassen with the project's `FKLimit.StochasticallyDominates` convention:
for probability measures on the genuine configuration space `Configuration E = E → Bool`,
cylindrical domination produces a coupling supported on the pointwise order. -/
theorem exists_orderedCoupling_of_stochasticallyDominates {E : Type*} [Countable E]
    {ν μ : ProbabilityMeasure (Configuration E)} (h : StochasticallyDominates ν μ) :
    ∃ κ : ProbabilityMeasure (Configuration E × Configuration E),
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
      ∀ᵐ z ∂(κ : Measure (Configuration E × Configuration E)), z.1 ≤ z.2 := by
  have hdom : ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A →
      (μ : Measure (Configuration E)) A ≤ (ν : Measure (Configuration E)) A := by
    intro A hA hU
    have hle := h A hA hU
    simp only [ProbabilityMeasure.coeFn_def] at hle
    exact (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hle
  exact CountableStrassen.exists_orderedCoupling_of_dominates hdom

/-- Pointwise-order support form of the FK-convention coupling. -/
theorem exists_orderedCoupling_support_of_stochasticallyDominates {E : Type*} [Countable E]
    {ν μ : ProbabilityMeasure (Configuration E)} (h : StochasticallyDominates ν μ) :
    ∃ κ : ProbabilityMeasure (Configuration E × Configuration E),
      κ.map Prod.fst = μ ∧ κ.map Prod.snd = ν ∧
      (κ : Measure (Configuration E × Configuration E))
        {z | z.1 ≤ z.2} = 1 := by
  have hdom : ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A →
      (μ : Measure (Configuration E)) A ≤ (ν : Measure (Configuration E)) A := by
    intro A hA hU
    have hle := h A hA hU
    simp only [ProbabilityMeasure.coeFn_def] at hle
    exact (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hle
  exact CountableStrassen.exists_orderedCoupling_support hdom

end FKLimit
