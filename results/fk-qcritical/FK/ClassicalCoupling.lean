import Mathlib

/-!
# Finite coupling ingredients for the classical subcritical uniqueness proof

This file isolates two steps of Section 2 of Beffara--Faipeur--Oke
(arXiv:2512.16486): the elementary monotone coupling at one edge, and the
measure-theoretic deduction of equation (9) from equality on the event on
which a closed cutset separates the local event from the outer boundary.
-/

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FKModel

/-- The Bernoulli probability mass function on `Bool`, with `true` meaning
open.  We use `NNReal` with a bound rather than silently restricting the edge
parameter to the interior of `[0,1]`. -/
noncomputable def bernoulliPMF (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => cond b p (1 - p)) (by
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    exact add_tsub_cancel_of_le (ENNReal.coe_le_coe.mpr hp))

@[simp] lemma bernoulliPMF_apply (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) :
    bernoulliPMF p hp b = cond b p (1 - p) := by
  simp only [bernoulliPMF, PMF.ofFintype_apply]
  exact Eq.symm (Bool.apply_cond ENNReal.ofNNReal)

/-- Masses of the usual coupling of two Bernoulli variables with the same
uniform random variable.  There is no mass at `(true,false)`. -/
private def boolCouplingMass (a b : ℝ≥0) : Bool × Bool → ℝ≥0∞
  | (false, false) => ↑(1 - b)
  | (false, true) => ↑(b - a)
  | (true, false) => 0
  | (true, true) => ↑a

private lemma sum_boolCouplingMass {a b : ℝ≥0} (_ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) : ∑ x, boolCouplingMass a b x = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, boolCouplingMass]
  simp only [add_zero, ← ENNReal.coe_add, ← ENNReal.coe_one]
  norm_cast
  rw [← add_assoc, add_tsub_cancel_of_le hab, add_tsub_cancel_of_le hb]

/-- An explicit monotone coupling of two Bernoulli laws. -/
noncomputable def boolCoupling (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) : PMF (Bool × Bool) :=
  PMF.ofFintype (boolCouplingMass a b) (sum_boolCouplingMass ha hb hab)

@[simp] lemma boolCoupling_apply (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) (x : Bool × Bool) :
    boolCoupling a b ha hb hab x = boolCouplingMass a b x := by
  simp [boolCoupling]

/-- The impossible ordered pair has coupling mass zero. -/
@[simp] lemma boolCoupling_true_false (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) : boolCoupling a b ha hb hab (true, false) = 0 := by
  rfl

private lemma nnreal_false_mass_identity {a b : ℝ≥0} (hb : b ≤ 1) (hab : a ≤ b) :
    b - a + (1 - b) = 1 - a := by
  calc
    b - a + (1 - b) = b + 1 - (a + b) := tsub_add_tsub_comm hab hb
    _ = 1 + b - (a + b) := by rw [add_comm b 1]
    _ = 1 - a := add_tsub_add_eq_tsub_right _ _ _

/-- The first coordinate of the explicit coupling has the smaller Bernoulli law. -/
lemma map_fst_boolCoupling (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) : (boolCoupling a b ha hb hab).map Prod.fst = bernoulliPMF a ha := by
  ext c
  cases c <;>
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      boolCouplingMass]
  rw [← ENNReal.coe_sub]
  norm_cast
  exact nnreal_false_mass_identity hb hab

/-- The second coordinate of the explicit coupling has the larger Bernoulli law. -/
lemma map_snd_boolCoupling (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) : (boolCoupling a b ha hb hab).map Prod.snd = bernoulliPMF b hb := by
  ext c
  cases c <;>
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      boolCouplingMass]
  exact add_tsub_cancel_of_le (ENNReal.coe_le_coe.mpr hab)

/-- Measure-theoretic form of the first marginal identity. -/
lemma measure_map_fst_boolCoupling (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) :
    Measure.map Prod.fst (boolCoupling a b ha hb hab).toMeasure =
      (bernoulliPMF a ha).toMeasure := by
  rw [PMF.toMeasure_map Prod.fst _ measurable_fst, map_fst_boolCoupling]

/-- Measure-theoretic form of the second marginal identity. -/
lemma measure_map_snd_boolCoupling (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) :
    Measure.map Prod.snd (boolCoupling a b ha hb hab).toMeasure =
      (bernoulliPMF b hb).toMeasure := by
  rw [PMF.toMeasure_map Prod.snd _ measurable_snd, map_snd_boolCoupling]

/-- The explicit Bernoulli coupling is almost surely ordered. -/
lemma boolCoupling_ae_le (a b : ℝ≥0) (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : a ≤ b) :
    ∀ᵐ x ∂(boolCoupling a b ha hb hab).toMeasure, x.1 ≤ x.2 := by
  rw [MeasureTheory.ae_iff]
  have hbad : {x : Bool × Bool | ¬x.1 ≤ x.2} = {(true, false)} := by
    ext ⟨x, y⟩
    cases x <;> cases y <;> simp
  rw [hbad, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    boolCoupling_true_false]

/-- Independent edgewise monotone coupling on a finite edge index type.  A
sample records both edge states at every edge; its two configuration marginals
are obtained by projecting each pair. -/
noncomputable def productBoolCoupling {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) : Measure (∀ _ : ι, Bool × Bool) :=
  Measure.pi (fun i => (boolCoupling (a i) (b i) (ha i) (hb i) (hab i)).toMeasure)

/-- The first configuration marginal is inhomogeneous Bernoulli percolation
with parameters `a`. -/
lemma productBoolCoupling_map_fst {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) :
    Measure.map (fun z i => (z i).1) (productBoolCoupling a b ha hb hab) =
      Measure.pi (fun i => (bernoulliPMF (a i) (ha i)).toMeasure) := by
  unfold productBoolCoupling
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  congr 1
  funext i
  exact measure_map_fst_boolCoupling (a i) (b i) (ha i) (hb i) (hab i)

/-- The second configuration marginal is inhomogeneous Bernoulli percolation
with parameters `b`. -/
lemma productBoolCoupling_map_snd {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) :
    Measure.map (fun z i => (z i).2) (productBoolCoupling a b ha hb hab) =
      Measure.pi (fun i => (bernoulliPMF (b i) (hb i)).toMeasure) := by
  unfold productBoolCoupling
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  congr 1
  funext i
  exact measure_map_snd_boolCoupling (a i) (b i) (ha i) (hb i) (hab i)

/-- Almost surely, the second configuration is pointwise above the first. -/
lemma productBoolCoupling_ae_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) :
    ∀ᵐ z ∂(productBoolCoupling a b ha hb hab), ∀ i, (z i).1 ≤ (z i).2 := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_iff]
  unfold productBoolCoupling
  have hi := boolCoupling_ae_le (a i) (b i) (ha i) (hb i) (hab i)
  rw [MeasureTheory.ae_iff] at hi
  exact Measure.pi_eval_preimage_null
    (fun j => (boolCoupling (a j) (b j) (ha j) (hb j) (hab j)).toMeasure)
    (i := i) (s := {x : Bool × Bool | ¬x.1 ≤ x.2}) hi

/-- A measurable ordered coupling gives stochastic domination on every
increasing event.  No independence or product structure is needed here. -/
lemma measure_le_of_coupling {Ω Ωc : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ωc] [Preorder Ωc] (Ψ : Measure Ω) (μ ν : Measure Ωc)
    (f g : Ω → Ωc) (hf : Measurable f) (hg : Measurable g)
    (hμ : Measure.map f Ψ = μ) (hν : Measure.map g Ψ = ν)
    (hle : ∀ᵐ x ∂Ψ, f x ≤ g x) {A : Set Ωc} (hA : MeasurableSet A)
    (hmono : ∀ ⦃x y : Ωc⦄, x ≤ y → x ∈ A → y ∈ A) :
    μ A ≤ ν A := by
  rw [← hμ, ← hν, Measure.map_apply hf hA, Measure.map_apply hg hA]
  apply measure_mono_ae
  filter_upwards [hle] with x hx
  exact hmono hx

/-- Stochastic comparison of two finite inhomogeneous Bernoulli product laws,
using the explicit edgewise coupling. -/
lemma productBernoulli_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) {A : Set (∀ _ : ι, Bool)}
    (hA : MeasurableSet A)
    (hmono : ∀ ⦃x y : (∀ _ : ι, Bool)⦄, x ≤ y → x ∈ A → y ∈ A) :
    (Measure.pi (fun i => (bernoulliPMF (a i) (ha i)).toMeasure)) A ≤
      (Measure.pi (fun i => (bernoulliPMF (b i) (hb i)).toMeasure)) A := by
  refine measure_le_of_coupling (productBoolCoupling a b ha hb hab)
    (Measure.pi (fun i => (bernoulliPMF (a i) (ha i)).toMeasure))
    (Measure.pi (fun i => (bernoulliPMF (b i) (hb i)).toMeasure))
    (fun z i => (z i).1) (fun z i => (z i).2)
    (Measurable.of_eval (fun i => (measurable_pi_apply i).fst))
    (Measurable.of_eval (fun i => (measurable_pi_apply i).snd))
    (productBoolCoupling_map_fst a b ha hb hab)
    (productBoolCoupling_map_snd a b ha hb hab) ?_ hA hmono
  simpa only [Pi.le_def] using productBoolCoupling_ae_le a b ha hb hab

/-- Real-probability form of `productBernoulli_le`. -/
lemma productBernoulli_real_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ha : ∀ i, a i ≤ 1) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) {A : Set (∀ _ : ι, Bool)}
    (hA : MeasurableSet A)
    (hmono : ∀ ⦃x y : (∀ _ : ι, Bool)⦄, x ≤ y → x ∈ A → y ∈ A) :
    (Measure.pi (fun i => (bernoulliPMF (a i) (ha i)).toMeasure)).real A ≤
      (Measure.pi (fun i => (bernoulliPMF (b i) (hb i)).toMeasure)).real A := by
  exact ENNReal.toReal_mono (by finiteness) (productBernoulli_le a b ha hb hab hA hmono)

/-- Two probability measures on a product measurable space are equal whenever
 they agree on every measurable finite-base cylinder. -/
lemma measure_ext_of_eq_on_measurableCylinders {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ ν : Measure (∀ i, α i))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ s ∈ measurableCylinders α, μ s = ν s) :
    μ = ν := by
  exact MeasureTheory.ext_of_generate_finite (measurableCylinders α)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders h (by simp)

/-- Boolean special case: agreement on every finite-support cylinder, with an
arbitrary base event, implies equality of probability measures.  The ambient
edge index type need not be finite. -/
lemma measure_ext_of_eq_on_boolCylinders {ι : Type*}
    (μ ν : Measure (∀ _ : ι, Bool)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ (I : Finset ι) (S : Set (∀ _i : I, Bool)),
      μ (cylinder I S) = ν (cylinder I S)) :
    μ = ν := by
  apply measure_ext_of_eq_on_measurableCylinders μ ν
  intro t ht
  obtain ⟨I, S, _hS, rfl⟩ := (mem_measurableCylinders t).mp ht
  exact h I S

/-- Split an event according to a measurable no-crossing event. -/
lemma measure_split_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A C : Set Ω} (hA : MeasurableSet A) (hC : MeasurableSet C) :
    μ A = μ (A ∩ C) + μ (A ∩ Cᶜ) := by
  have hd : Disjoint (A ∩ C) (A ∩ Cᶜ) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxC hxCc
    exact hxCc.2 hxC.2
  calc
    μ A = μ ((A ∩ C) ∪ (A ∩ Cᶜ)) := by
      congr 1
      ext x
      by_cases hx : x ∈ C <;> simp_all
    _ = μ (A ∩ C) + μ (A ∩ Cᶜ) := measure_union hd (hA.inter hC.compl)

/-- Elementary non-asymptotic estimate behind equation (9) of Section 2.
Here `C` is the event on which a closed cutset exists, and `h` is the
consequence of the free-boundary Markov property after conditioning on the
maximal cutset. -/
lemma measure_le_add_of_inter_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A B C : Set Ω} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (h : μ (A ∩ C) = μ (B ∩ C)) :
    μ A ≤ μ B + μ Cᶜ := by
  calc
    μ A = μ (A ∩ C) + μ (A ∩ Cᶜ) := measure_split_inter μ hA hC
    _ = μ (B ∩ C) + μ (A ∩ Cᶜ) := by rw [h]
    _ ≤ μ B + μ Cᶜ :=
      add_le_add (measure_mono inter_subset_left) (measure_mono inter_subset_right)

/-- Real-probability form of `measure_le_add_of_inter_eq`. -/
lemma measureReal_sub_le_of_inter_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A B C : Set Ω}
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (h : μ (A ∩ C) = μ (B ∩ C)) :
    μ.real A - μ.real B ≤ μ.real Cᶜ := by
  rw [sub_le_iff_le_add]
  have hbound := measure_le_add_of_inter_eq μ hA hC h
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  simpa only [measureReal_def, ENNReal.toReal_add (measure_ne_top μ _)
    (measure_ne_top μ _), add_comm] using hreal

/-- Equation (9), stated for arbitrary measurable observation maps from a
coupling.  The first map is `ω ↦ ω₁` and the second is `ω ↦ ω₂` in the paper. -/
lemma equation_nine_bound {Ω Ω₁ Ω₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (Ψ : Measure Ω)
    [IsProbabilityMeasure Ψ] (μ : Measure Ω₁) (ν : Measure Ω₂)
    (f : Ω → Ω₁) (g : Ω → Ω₂) (hf : Measurable f) (hg : Measurable g)
    (hμ : Measure.map f Ψ = μ) (hν : Measure.map g Ψ = ν)
    {A : Set Ω₁} {B : Set Ω₂} {C : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hgood : Ψ (f ⁻¹' A ∩ C) = Ψ (g ⁻¹' B ∩ C)) :
    μ.real A - ν.real B ≤ Ψ.real Cᶜ := by
  have hfirst : μ.real A = Ψ.real (f ⁻¹' A) := by
    calc
      μ.real A = (Measure.map f Ψ).real A := by rw [hμ]
      _ = Ψ.real (f ⁻¹' A) := by
        simp only [measureReal_def, Measure.map_apply hf hA]
  have hsecond : ν.real B = Ψ.real (g ⁻¹' B) := by
    calc
      ν.real B = (Measure.map g Ψ).real B := by rw [hν]
      _ = Ψ.real (g ⁻¹' B) := by
        simp only [measureReal_def, Measure.map_apply hg hB]
  rw [hfirst, hsecond]
  exact measureReal_sub_le_of_inter_eq Ψ (hf hA) hC hgood

/-- Symmetric form of the closed-cutset estimate. -/
lemma measureReal_abs_sub_le_of_inter_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A B C : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (h : μ (A ∩ C) = μ (B ∩ C)) :
    |μ.real A - μ.real B| ≤ μ.real Cᶜ := by
  have hforward := measureReal_sub_le_of_inter_eq μ hA hC h
  have hreverse := measureReal_sub_le_of_inter_eq μ hB hC h.symm
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- Absolute-value version of `equation_nine_bound`, obtained by applying the
one-sided estimate in both directions. -/
lemma equation_nine_abs_bound {Ω Ω₁ Ω₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (Ψ : Measure Ω)
    [IsProbabilityMeasure Ψ] (μ : Measure Ω₁) (ν : Measure Ω₂)
    (f : Ω → Ω₁) (g : Ω → Ω₂) (hf : Measurable f) (hg : Measurable g)
    (hμ : Measure.map f Ψ = μ) (hν : Measure.map g Ψ = ν)
    {A : Set Ω₁} {B : Set Ω₂} {C : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hgood : Ψ (f ⁻¹' A ∩ C) = Ψ (g ⁻¹' B ∩ C)) :
    |μ.real A - ν.real B| ≤ Ψ.real Cᶜ := by
  have hforward := equation_nine_bound Ψ μ ν f g hf hg hμ hν hA hB hC hgood
  have hreverse := equation_nine_bound Ψ ν μ g f hg hf hν hμ hB hA hC hgood.symm
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- Equality on a no-crossing event follows from equality on every stratum of
a countable disjoint cutset decomposition.  In Lemma 2.1 the strata are the
possible values of the maximal closed cutset `M`. -/
lemma measure_inter_eq_of_disjoint_stratification {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) {X Y C : Set Ω}
    (D : ι → Set Ω) (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hC : C = ⋃ i, D i) (hdisj : Pairwise (Function.onFun Disjoint D))
    (hD : ∀ i, MeasurableSet (D i))
    (hstratum : ∀ i, μ (X ∩ D i) = μ (Y ∩ D i)) :
    μ (X ∩ C) = μ (Y ∩ C) := by
  have hdisjX : Pairwise (Function.onFun Disjoint fun i => X ∩ D i) := by
    intro i j hij
    exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hij)
  have hdisjY : Pairwise (Function.onFun Disjoint fun i => Y ∩ D i) := by
    intro i j hij
    exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hij)
  calc
    μ (X ∩ C) = μ (⋃ i, X ∩ D i) := by rw [hC, Set.inter_iUnion]
    _ = ∑' i, μ (X ∩ D i) := measure_iUnion hdisjX (fun i => hX.inter (hD i))
    _ = ∑' i, μ (Y ∩ D i) := tsum_congr hstratum
    _ = μ (⋃ i, Y ∩ D i) :=
      (measure_iUnion hdisjY (fun i => hY.inter (hD i))).symm
    _ = μ (Y ∩ C) := by rw [← Set.inter_iUnion, ← hC]

/-- Equation (9) with its no-crossing intersection equality proved from the
per-maximal-cutset laws, rather than assumed as a single black box. -/
lemma equation_nine_bound_of_stratification {Ω Ω₁ Ω₂ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [Countable ι] (Ψ : Measure Ω) [IsProbabilityMeasure Ψ]
    (μ : Measure Ω₁) (ν : Measure Ω₂)
    (f : Ω → Ω₁) (g : Ω → Ω₂) (hf : Measurable f) (hg : Measurable g)
    (hμ : Measure.map f Ψ = μ) (hν : Measure.map g Ψ = ν)
    {A : Set Ω₁} {B : Set Ω₂} {C : Set Ω} (D : ι → Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : C = ⋃ i, D i) (hdisj : Pairwise (Function.onFun Disjoint D))
    (hD : ∀ i, MeasurableSet (D i))
    (hstratum : ∀ i, Ψ (f ⁻¹' A ∩ D i) = Ψ (g ⁻¹' B ∩ D i)) :
    μ.real A - ν.real B ≤ Ψ.real Cᶜ := by
  have hCmeas : MeasurableSet C := hC ▸ MeasurableSet.iUnion hD
  apply equation_nine_bound Ψ μ ν f g hf hg hμ hν hA hB hCmeas
  exact measure_inter_eq_of_disjoint_stratification Ψ D (hf hA) (hg hB)
    hC hdisj hD hstratum

/-- The nested-limits step in the deduction of Theorem 1.9 from equation (9).
For each fixed `m`, the estimate is required eventually in `n`, exactly as for
`Σₙ` exhausting the graph after a fixed `Δₘ`. -/
lemma eq_of_tendsto_of_eventually_abs_sub_le {a b r : ℕ → ℝ} {A B : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hr : Tendsto r atTop (𝓝 0))
    (hbound : ∀ m, ∀ᶠ n in atTop, |a n - b m| ≤ r m) :
    A = B := by
  have hlim : ∀ m, |A - b m| ≤ r m := by
    intro m
    exact le_of_tendsto ((ha.sub tendsto_const_nhds).abs) (hbound m)
  have hleft : Tendsto (fun m => |A - b m|) atTop (𝓝 |A - B|) :=
    (tendsto_const_nhds.sub hb).abs
  have hzero : |A - B| ≤ 0 := le_of_tendsto_of_tendsto' hleft hr hlim
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)

/-- A version of the nested-limits step using equation (9) literally, together
with its counterpart after exchanging the two boundary conditions. -/
lemma eq_of_tendsto_of_two_sided_cutset_bounds {a b r : ℕ → ℝ} {A B : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hr : Tendsto r atTop (𝓝 0))
    (hforward : ∀ m, ∀ᶠ n in atTop, a n - b m ≤ r m)
    (hreverse : ∀ m, ∀ᶠ n in atTop, b m - a n ≤ r m) :
    A = B := by
  apply eq_of_tendsto_of_eventually_abs_sub_le ha hb hr
  intro m
  filter_upwards [hforward m, hreverse m] with n hfn hrn
  exact abs_le.mpr ⟨by linarith, hfn⟩

/-- Abstract weak-limit uniqueness theorem directly modelled on Theorem 1.9.
The hypotheses `hμ` and `hν` are weak convergence on local cylinder events;
`hforward` and `hreverse` are equation (9) and its boundary-exchanged form.
No FK-specific clause is hidden in the statement. -/
lemma measure_eq_of_two_sided_cutset_bounds_on_cylinders {ι : Type*}
    (μ ν : Measure (∀ _ : ι, Bool)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (μs νs : ℕ → Measure (∀ _ : ι, Bool))
    (r : ℕ → ℝ)
    (hμ : ∀ (I : Finset ι) (S : Set (∀ _i : I, Bool)),
      Tendsto (fun n => (μs n).real (cylinder I S)) atTop
        (𝓝 (μ.real (cylinder I S))))
    (hν : ∀ (I : Finset ι) (S : Set (∀ _i : I, Bool)),
      Tendsto (fun m => (νs m).real (cylinder I S)) atTop
        (𝓝 (ν.real (cylinder I S))))
    (hr : Tendsto r atTop (𝓝 0))
    (hforward : ∀ (I : Finset ι) (S : Set (∀ _i : I, Bool)) (m : ℕ),
      ∀ᶠ n in atTop, (μs n).real (cylinder I S) -
        (νs m).real (cylinder I S) ≤ r m)
    (hreverse : ∀ (I : Finset ι) (S : Set (∀ _i : I, Bool)) (m : ℕ),
      ∀ᶠ n in atTop, (νs m).real (cylinder I S) -
        (μs n).real (cylinder I S) ≤ r m) :
    μ = ν := by
  apply measure_ext_of_eq_on_boolCylinders μ ν
  intro I S
  apply (measureReal_eq_measureReal_iff (measure_ne_top μ _)
    (measure_ne_top ν _)).mp
  exact eq_of_tendsto_of_two_sided_cutset_bounds (hμ I S) (hν I S) hr
    (hforward I S) (hreverse I S)

end FKModel
