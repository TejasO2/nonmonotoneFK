import FK.Coupling
import FK.ClassicalCoupling

/-!
# Gluing two finite couplings through their common second marginal

This file supplies the finite triple-coupling step used in the exploration
proof of Lemma 2.1 of arXiv:2512.16486.  Conditional independence given the
common marginal is made explicit by a product-over-fiber mass formula.  No
independence or positivity is assumed of the input couplings.
-/

open scoped ENNReal BigOperators

namespace PMF

universe u v w

/-- A probability mass function on triples with prescribed coordinate laws.
The product type is right nested: a triple is `(a, b, c)`. -/
structure TripleCoupling {α : Type u} {β : Type v} {γ : Type w}
    (μ : PMF α) (ρ : PMF β) (ν : PMF γ) where
  dist : PMF (α × β × γ)
  map_fst : dist.map (fun x => x.1) = μ
  map_snd : dist.map (fun x => x.2.1) = ρ
  map_thd : dist.map (fun x => x.2.2) = ν

/-- A triple coupling whose first and second coordinates satisfy prescribed
relations to the third coordinate almost surely (equivalently, on the PMF
support). -/
structure RelativeTripleCoupling {α : Type u} {β : Type v} {γ : Type w}
    (μ : PMF α) (ρ : PMF β) (ν : PMF γ)
    (r : α → γ → Prop) (s : β → γ → Prop)
    extends TripleCoupling μ ρ ν where
  rel_fst : ∀ x ∈ dist.support, r x.1 x.2.2
  rel_snd : ∀ x ∈ dist.support, s x.2.1 x.2.2

namespace Coupling

variable {α : Type u} {β : Type v} {γ : Type w}
variable {μ : PMF α} {ρ : PMF β} {ν : PMF γ}

/-- The mass of a fiber of the second marginal of a coupling. -/
lemma sum_apply_fst [Fintype α] [Fintype γ] (c : Coupling μ ν) (b : γ) :
    ∑ a, c.dist (a, b) = ν b := by
  classical
  have h := congrArg (fun p : PMF γ => p b) c.map_snd
  simpa [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.sum_ite_eq'] using h

/-- The mass of a fiber of the first marginal of a coupling. -/
lemma sum_apply_snd [Fintype α] [Fintype γ] (c : Coupling μ ν) (a : α) :
    ∑ b, c.dist (a, b) = μ a := by
  classical
  have h := congrArg (fun p : PMF α => p a) c.map_fst
  have hs : (∑ x, ∑ b, if a = x then c.dist (x, b) else 0) =
      ∑ b, c.dist (a, b) := by
    calc
      (∑ x, ∑ b, if a = x then c.dist (x, b) else 0) =
          ∑ b, if a = a then c.dist (a, b) else 0 := by
        apply Finset.sum_eq_single a
        · intro x _ hxa
          simp [Ne.symm hxa]
        · intro ha
          simp at ha
      _ = ∑ b, c.dist (a, b) := by simp
  have h' : (∑ x, ∑ b, if a = x then c.dist (x, b) else 0) = μ a := by
    simpa only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Prod.fst] using h
  rwa [hs] at h'

/-- A pair has zero mass whenever its second marginal coordinate has zero mass. -/
lemma apply_eq_zero_of_snd_eq_zero [Fintype α] [Fintype γ]
    (c : Coupling μ ν) (a : α) {b : γ} (hb : ν b = 0) : c.dist (a, b) = 0 := by
  classical
  have hle : c.dist (a, b) ≤ ∑ x, c.dist (x, b) := by
    exact Finset.single_le_sum
      (fun x _ => (zero_le : 0 ≤ c.dist (x, b))) (Finset.mem_univ a)
  rw [c.sum_apply_fst, hb] at hle
  exact bot_unique hle

/-- Conditionally independent gluing mass on a common third-coordinate fiber.
The formula is also correct when `ν c = 0`: both pair masses then vanish. -/
noncomputable def glueMass [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) : α × β × γ → ℝ≥0∞
  | (a, b, c) => c₁.dist (a, c) * c₂.dist (b, c) / ν c

/-- Summing out the second lower coordinate recovers the first input coupling. -/
lemma sum_glueMass_snd [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) (a : α) (c : γ) :
    ∑ b, glueMass c₁ c₂ (a, b, c) = c₁.dist (a, c) := by
  classical
  by_cases hc : ν c = 0
  · have h₁ : c₁.dist (a, c) = 0 := c₁.apply_eq_zero_of_snd_eq_zero a hc
    have h₂ : ∀ b, c₂.dist (b, c) = 0 :=
      fun b => c₂.apply_eq_zero_of_snd_eq_zero b hc
    simp [glueMass, h₁, h₂, hc]
  · simp only [glueMass, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum, c₂.sum_apply_fst, mul_assoc,
      ENNReal.mul_inv_cancel hc (ν.apply_ne_top c), mul_one]

/-- Summing out the first lower coordinate recovers the second input coupling. -/
lemma sum_glueMass_fst [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) (b : β) (c : γ) :
    ∑ a, glueMass c₁ c₂ (a, b, c) = c₂.dist (b, c) := by
  classical
  by_cases hc : ν c = 0
  · have h₁ : ∀ a, c₁.dist (a, c) = 0 :=
      fun a => c₁.apply_eq_zero_of_snd_eq_zero a hc
    have h₂ : c₂.dist (b, c) = 0 := c₂.apply_eq_zero_of_snd_eq_zero b hc
    simp [glueMass, h₁, h₂, hc]
  · simp only [glueMass, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul, c₁.sum_apply_fst,
      mul_comm (ν c) (c₂.dist (b, c)), mul_assoc,
      ENNReal.mul_inv_cancel hc (ν.apply_ne_top c), mul_one]

/-- The explicitly glued mass is normalized. -/
lemma sum_glueMass [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) :
    ∑ x, glueMass c₁ c₂ x = 1 := by
  classical
  calc
    ∑ x, glueMass c₁ c₂ x = ∑ a, ∑ b, ∑ c, glueMass c₁ c₂ (a, b, c) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ a, ∑ c, ∑ b, glueMass c₁ c₂ (a, b, c) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a, ∑ c, c₁.dist (a, c) := by
      simp_rw [sum_glueMass_snd]
    _ = ∑ c, ν c := by
      rw [Finset.sum_comm]
      simp_rw [c₁.sum_apply_fst]
    _ = 1 := by
      simpa only [tsum_fintype] using ν.tsum_coe

/-- The normalized PMF obtained by conditional independence on each fiber. -/
noncomputable def glueDist [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) : PMF (α × β × γ) :=
  PMF.ofFintype (glueMass c₁ c₂) (sum_glueMass c₁ c₂)

@[simp] lemma glueDist_apply [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) (x : α × β × γ) :
    glueDist c₁ c₂ x = glueMass c₁ c₂ x := rfl

/-- The `(first, third)` projection of the glued PMF is the first coupling. -/
lemma map_glueDist_fst_thd [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) :
    (glueDist c₁ c₂).map (fun x => (x.1, x.2.2)) = c₁.dist := by
  classical
  ext ⟨a, c⟩
  calc
    ((glueDist c₁ c₂).map (fun x => (x.1, x.2.2))) (a, c) =
        ∑ b, glueMass c₁ c₂ (a, b, c) := by
      simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, glueDist_apply,
        Prod.ext_iff, ite_and, Finset.sum_ite_eq]
    _ = c₁.dist (a, c) := sum_glueMass_snd c₁ c₂ a c

/-- The `(second, third)` projection of the glued PMF is the second coupling. -/
lemma map_glueDist_snd_thd [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) :
    (glueDist c₁ c₂).map (fun x => (x.2.1, x.2.2)) = c₂.dist := by
  classical
  ext ⟨b, c⟩
  calc
    ((glueDist c₁ c₂).map (fun x => (x.2.1, x.2.2))) (b, c) =
        ∑ a, glueMass c₁ c₂ (a, b, c) := by
      simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, glueDist_apply,
        Prod.ext_iff, ite_and, Finset.sum_ite_eq]
    _ = c₂.dist (b, c) := sum_glueMass_fst c₁ c₂ b c

/-- Glue two couplings with the same second marginal, preserving all three
coordinate marginals. -/
noncomputable def glue [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) : TripleCoupling μ ρ ν where
  dist := glueDist c₁ c₂
  map_fst := by
    calc
      (glueDist c₁ c₂).map (fun x => x.1) =
          ((glueDist c₁ c₂).map (fun x => (x.1, x.2.2))).map Prod.fst := by
        rw [PMF.map_comp]
        rfl
      _ = c₁.dist.map Prod.fst := by rw [map_glueDist_fst_thd]
      _ = μ := c₁.map_fst
  map_snd := by
    calc
      (glueDist c₁ c₂).map (fun x => x.2.1) =
          ((glueDist c₁ c₂).map (fun x => (x.2.1, x.2.2))).map Prod.fst := by
        rw [PMF.map_comp]
        rfl
      _ = c₂.dist.map Prod.fst := by rw [map_glueDist_snd_thd]
      _ = ρ := c₂.map_fst
  map_thd := by
    calc
      (glueDist c₁ c₂).map (fun x => x.2.2) =
          ((glueDist c₁ c₂).map (fun x => (x.1, x.2.2))).map Prod.snd := by
        rw [PMF.map_comp]
        rfl
      _ = c₁.dist.map Prod.snd := by rw [map_glueDist_fst_thd]
      _ = ν := c₁.map_snd

/-- Positive glued mass forces positive mass in the first input pair. -/
lemma pair_fst_thd_mem_support_of_glue_support [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) {x : α × β × γ}
    (hx : x ∈ (glueDist c₁ c₂).support) : (x.1, x.2.2) ∈ c₁.dist.support := by
  rw [PMF.mem_support_iff] at hx ⊢
  intro hzero
  apply hx
  rcases x with ⟨a, b, c⟩
  simp [glueMass, hzero]

/-- Positive glued mass forces positive mass in the second input pair. -/
lemma pair_snd_thd_mem_support_of_glue_support [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν) {x : α × β × γ}
    (hx : x ∈ (glueDist c₁ c₂).support) : (x.2.1, x.2.2) ∈ c₂.dist.support := by
  rw [PMF.mem_support_iff] at hx ⊢
  intro hzero
  apply hx
  rcases x with ⟨a, b, c⟩
  simp [glueMass, hzero]

/-- Glue two pair couplings while preserving relations to their common
coordinate on the support. -/
noncomputable def glueRelative [Fintype α] [Fintype β] [Fintype γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν)
    (r : α → γ → Prop) (s : β → γ → Prop)
    (hr : ∀ x ∈ c₁.dist.support, r x.1 x.2)
    (hs : ∀ x ∈ c₂.dist.support, s x.1 x.2) :
    RelativeTripleCoupling μ ρ ν r s where
  toTripleCoupling := glue c₁ c₂
  rel_fst _x hx := hr _ (pair_fst_thd_mem_support_of_glue_support c₁ c₂ hx)
  rel_snd _x hx := hs _ (pair_snd_thd_mem_support_of_glue_support c₁ c₂ hx)

end Coupling

/-- The special case of a relative triple coupling used in Lemma 2.1:
`ω₁ ≤ ω₃` and `ω₂ ≤ ω₃` on the support. -/
abbrev OrderedTripleCoupling {α : Type u} [LE α] (μ ρ ν : PMF α) :=
  RelativeTripleCoupling μ ρ ν (fun a c => a ≤ c) (fun b c => b ≤ c)

namespace OrderedCoupling

variable {α : Type u} [LE α] {μ ρ ν : PMF α}

/-- Combine the two ordered couplings of Lemma 2.1 through their common upper
configuration. -/
noncomputable def glue [Fintype α] (c₁ : OrderedCoupling μ ν)
    (c₂ : OrderedCoupling ρ ν) : OrderedTripleCoupling μ ρ ν :=
  Coupling.glueRelative c₁.toCoupling c₂.toCoupling _ _
    (fun x hx => c₁.ordered x hx) (fun x hx => c₂.ordered x hx)

end OrderedCoupling

/-- A predicate valid on every support point of a PMF holds almost everywhere.
Finiteness makes the exceptional set measurable from singleton measurability. -/
lemma ae_of_forall_mem_support {δ : Type*} [MeasurableSpace δ]
    [MeasurableSingletonClass δ] [Finite δ] (p : PMF δ) {r : δ → Prop}
    (hr : ∀ x ∈ p.support, r x) : ∀ᵐ x ∂p.toMeasure, r x := by
  rw [MeasureTheory.ae_iff]
  apply (p.toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet).2
  exact Set.disjoint_left.mpr (fun x hx hnx => hnx (hr x hx))

namespace RelativeTripleCoupling

variable {α : Type u} {β : Type v} {γ : Type w}
variable {μ : PMF α} {ρ : PMF β} {ν : PMF γ} {r : α → γ → Prop} {s : β → γ → Prop}

/-- The first relation of a relative triple coupling holds almost surely. -/
lemma ae_rel_fst [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace (α × β × γ)] [MeasurableSingletonClass (α × β × γ)]
    (t : RelativeTripleCoupling μ ρ ν r s) :
    ∀ᵐ x ∂t.dist.toMeasure, r x.1 x.2.2 :=
  ae_of_forall_mem_support t.dist t.rel_fst

/-- The second relation of a relative triple coupling holds almost surely. -/
lemma ae_rel_snd [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace (α × β × γ)] [MeasurableSingletonClass (α × β × γ)]
    (t : RelativeTripleCoupling μ ρ ν r s) :
    ∀ᵐ x ∂t.dist.toMeasure, s x.2.1 x.2.2 :=
  ae_of_forall_mem_support t.dist t.rel_snd

end RelativeTripleCoupling

namespace TripleCoupling

open MeasureTheory

variable {α : Type u} {β : Type v} {γ : Type w}
variable {μ : PMF α} {ρ : PMF β} {ν : PMF γ}

/-- Equation (9), with the three marginal conditions supplied by an actual
finite triple coupling.  The remaining `hgood` hypothesis is precisely the
free-boundary Markov property on the event that a closed cutset exists. -/
lemma equation_nine_abs_bound [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (t : TripleCoupling μ ρ ν)
    {A : Set α} {B : Set β} {C : Set γ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hgood : t.dist.toMeasure ((fun x => x.1) ⁻¹' A ∩ (fun x => x.2.2) ⁻¹' C) =
      t.dist.toMeasure ((fun x => x.2.1) ⁻¹' B ∩ (fun x => x.2.2) ⁻¹' C)) :
    |μ.toMeasure.real A - ρ.toMeasure.real B| ≤ ν.toMeasure.real Cᶜ := by
  let f : α × β × γ → α := fun x => x.1
  let g : α × β × γ → β := fun x => x.2.1
  let h : α × β × γ → γ := fun x => x.2.2
  have hf : Measurable f := measurable_fst
  have hg : Measurable g := measurable_fst.comp measurable_snd
  have hh : Measurable h := measurable_snd.comp measurable_snd
  have hfst : Measure.map f t.dist.toMeasure = μ.toMeasure := by
    rw [PMF.toMeasure_map f t.dist hf, t.map_fst]
  have hsnd : Measure.map g t.dist.toMeasure = ρ.toMeasure := by
    rw [PMF.toMeasure_map g t.dist hg, t.map_snd]
  have hthd : Measure.map h t.dist.toMeasure = ν.toMeasure := by
    rw [PMF.toMeasure_map h t.dist hh, t.map_thd]
  have hbad : t.dist.toMeasure.real (h ⁻¹' C)ᶜ = ν.toMeasure.real Cᶜ := by
    apply congrArg ENNReal.toReal
    rw [← hthd, Measure.map_apply hh hC.compl, Set.preimage_compl]
  calc
    |μ.toMeasure.real A - ρ.toMeasure.real B| ≤
        t.dist.toMeasure.real (h ⁻¹' C)ᶜ := by
      exact FKModel.equation_nine_abs_bound t.dist.toMeasure μ.toMeasure ρ.toMeasure
        f g hf hg hfst hsnd hA hB (hh hC) hgood
    _ = ν.toMeasure.real Cᶜ := hbad

end TripleCoupling

namespace Coupling

open MeasureTheory

variable {α : Type u} {β : Type v} {γ : Type w}
variable {μ : PMF α} {ρ : PMF β} {ν : PMF γ}

/-- Equation (9) for the explicit glued coupling, with its good-event
intersection equality reduced to equality of the two input pair measures.
On a maximal-cutset stratum this last equality is the common free FK law of
the two interior configurations. -/
lemma equation_nine_abs_bound_of_pair_eq [Fintype α] [Fintype β] [Fintype γ]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (c₁ : Coupling μ ν) (c₂ : Coupling ρ ν)
    {A : Set α} {B : Set β} {C : Set γ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hpair : c₁.dist.toMeasure (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' C) =
      c₂.dist.toMeasure (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' C)) :
    |μ.toMeasure.real A - ρ.toMeasure.real B| ≤ ν.toMeasure.real Cᶜ := by
  let p₁ : α × β × γ → α × γ := fun x => (x.1, x.2.2)
  let p₂ : α × β × γ → β × γ := fun x => (x.2.1, x.2.2)
  let S₁ : Set (α × γ) := Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' C
  let S₂ : Set (β × γ) := Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' C
  have hp₁ : Measurable p₁ := by fun_prop
  have hp₂ : Measurable p₂ := by fun_prop
  have hS₁ : MeasurableSet S₁ := measurable_fst hA |>.inter (measurable_snd hC)
  have hS₂ : MeasurableSet S₂ := measurable_fst hB |>.inter (measurable_snd hC)
  have hmap₁ : Measure.map p₁ (glueDist c₁ c₂).toMeasure = c₁.dist.toMeasure := by
    rw [PMF.toMeasure_map p₁ (glueDist c₁ c₂) hp₁, map_glueDist_fst_thd]
  have hmap₂ : Measure.map p₂ (glueDist c₁ c₂).toMeasure = c₂.dist.toMeasure := by
    rw [PMF.toMeasure_map p₂ (glueDist c₁ c₂) hp₂, map_glueDist_snd_thd]
  apply (glue c₁ c₂).equation_nine_abs_bound hA hB hC
  change (glueDist c₁ c₂).toMeasure (p₁ ⁻¹' S₁) =
    (glueDist c₁ c₂).toMeasure (p₂ ⁻¹' S₂)
  rw [← Measure.map_apply hp₁ hS₁, hmap₁, ← Measure.map_apply hp₂ hS₂, hmap₂]
  exact hpair

end Coupling
end PMF
