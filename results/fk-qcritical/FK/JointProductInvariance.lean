import FK.OpenPathEnhancement

noncomputable section

local instance (priority := low) finProbPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# Joint product invariance for an enhanced update and auxiliary refresh

This file proves the finite joint-distribution step used in Section 3 of
Beffara--Faipeur--Oke (arXiv:2512.16486).  The enhanced coordinate may depend
on the *old* auxiliary configuration.  Once every auxiliary coordinate is
independently refreshed, the enhanced coordinate, the new auxiliary
configuration, and every untouched coordinate are independent again.

The argument is entirely finite and uses `OpenPath.FinProb`.  No Markov-chain
convergence or FK-specific conditional law is assumed here.
-/

open scoped BigOperators
open Set

namespace OpenPath.FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A point mass as a finite probability law. -/
def pure (a : α) : OpenPath.FinProb α where
  mass b := if b = a then 1 else 0
  mass_nonneg b := by split_ifs <;> norm_num
  sum_mass := by simp

@[simp] lemma pure_mass (a b : α) :
    (pure a).mass b = if b = a then 1 else 0 := rfl

/-- The independent product of two finite probability laws. -/
noncomputable def prod (μ : OpenPath.FinProb α) (ν : OpenPath.FinProb β) :
    OpenPath.FinProb (α × β) where
  mass x := μ.mass x.1 * ν.mass x.2
  mass_nonneg x := mul_nonneg (μ.mass_nonneg _) (ν.mass_nonneg _)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, μ.mass a * ν.mass b) = ∑ a, μ.mass a * (∑ b, ν.mass b) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ = 1 := by simp [OpenPath.FinProb.sum_mass]

@[simp] lemma prod_mass (μ : OpenPath.FinProb α) (ν : OpenPath.FinProb β)
    (x : α × β) : (prod μ ν).mass x = μ.mass x.1 * ν.mass x.2 := rfl

@[simp] lemma prod_map_fst (μ : FinProb α) (ν : FinProb β) :
    (μ.prod ν).map Prod.fst = μ := by
  apply FinProb.ext
  intro a
  change (∑ x : α × β, if x.1 = a then μ.mass x.1 * ν.mass x.2 else 0) = _
  rw [Fintype.sum_prod_type]
  simp [← Finset.mul_sum, ν.sum_mass]

@[simp] lemma prod_map_snd (μ : FinProb α) (ν : FinProb β) :
    (μ.prod ν).map Prod.snd = ν := by
  apply FinProb.ext
  intro b
  change (∑ x : α × β, if x.2 = b then μ.mass x.1 * ν.mass x.2 else 0) = _
  rw [Fintype.sum_prod_type]
  simp [← Finset.sum_mul, μ.sum_mass]

/-- Coordinatewise maps send an independent finite product to the product of
its mapped coordinate laws. -/
lemma pi_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α' : ι → Type*} {β' : ι → Type*} [∀ i, Fintype (α' i)] [∀ i, Fintype (β' i)]
    (μ : ∀ i, OpenPath.FinProb (α' i)) (f : ∀ i, α' i → β' i) :
    (OpenPath.FinProb.pi μ).map (fun x i => f i (x i)) =
      OpenPath.FinProb.pi (fun i => (μ i).map (f i)) := by
  apply OpenPath.FinProb.ext
  intro y
  simp only [OpenPath.FinProb.mass_map, OpenPath.FinProb.pi_mass]
  rw [Fintype.prod_sum]
  simp [funext_iff, Fintype.prod_ite_zero]

lemma event_preimage_map (μ : OpenPath.FinProb α) (f : α → β) (A : Set β) :
    μ.event (f ⁻¹' A) = (μ.map f).event A := by
  rw [OpenPath.FinProb.event_map]
  rfl

/-- Mapping a finite law by an equivalence does not require a sum in order to
compute its mass: the unique preimage is given by the inverse equivalence. -/
lemma mass_map_equiv (D : α ≃ β) (μ : OpenPath.FinProb α) (b : β) :
    (μ.map D).mass b = μ.mass (D.symm b) := by
  rw [OpenPath.FinProb.mass_map]
  have h (a : α) : D a = b ↔ a = D.symm b := by
    constructor
    · intro ha
      rw [← ha, D.symm_apply_apply]
    · intro ha
      rw [ha, D.apply_symm_apply]
  simp_rw [h]
  simp

/-- Mapping the output of a finite bind is the same as mapping each kernel
output. -/
lemma map_bind {γ : Type*} [Fintype γ] (μ : OpenPath.FinProb α)
    (κ : α → OpenPath.FinProb β) (f : β → γ) :
    (μ.bind κ).map f = μ.bind (fun a => (κ a).map f) := by
  apply OpenPath.FinProb.ext
  intro c
  change (∑ b, if f b = c then (∑ a, μ.mass a * (κ a).mass b) else 0) =
    ∑ a, μ.mass a * (∑ b, if f b = c then (κ a).mass b else 0)
  calc
    (∑ b, if f b = c then (∑ a, μ.mass a * (κ a).mass b) else 0) =
        ∑ b, ∑ a, μ.mass a * (if f b = c then (κ a).mass b else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : f b = c <;> simp [hb]
    _ = ∑ a, ∑ b, μ.mass a * (if f b = c then (κ a).mass b else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

/-- Binding after a change of variables by an equivalence composes the kernel
with that equivalence. -/
lemma bind_map_equiv {γ : Type*} [Fintype γ] (D : α ≃ β)
    (μ : OpenPath.FinProb α) (κ : β → OpenPath.FinProb γ) :
    (μ.map D).bind κ = μ.bind (fun a => κ (D a)) := by
  apply OpenPath.FinProb.ext
  intro c
  simp only [OpenPath.FinProb.mass_bind, mass_map_equiv]
  exact Fintype.sum_equiv D.symm _ _ (fun b => by simp)

@[simp] lemma map_equiv_symm (D : α ≃ β) (μ : OpenPath.FinProb α) :
    (μ.map D).map D.symm = μ := by
  apply OpenPath.FinProb.ext
  intro a
  rw [mass_map_equiv, mass_map_equiv]
  simp

end OpenPath.FinProb

namespace JointInvariance

open OpenPath

variable {ε α ρ : Type*} [Fintype ε] [Fintype α] [Fintype ρ]

/-- The product law on `(enhanced, auxiliary), untouched`. -/
noncomputable def blockLaw (ν : OpenPath.FinProb ε) (μ : OpenPath.FinProb α)
    (ξ : OpenPath.FinProb ρ) : OpenPath.FinProb ((ε × α) × ρ) :=
  (ν.prod μ).prod ξ

/-- One enhanced block update.  Only the old auxiliary state is supplied to
`κ`; the old enhanced state is discarded.  Every auxiliary state is refreshed
independently with law `μ`, and the untouched coordinate is retained. -/
noncomputable def blockKernel (μ : OpenPath.FinProb α) (κ : α → OpenPath.FinProb ε) :
    (ε × α) × ρ → OpenPath.FinProb ((ε × α) × ρ) :=
  fun s => ((κ s.1.2).prod μ).prod (FinProb.pure s.2)

/-- Exact output law after enhancement and a complete auxiliary refresh.
The three output blocks are independent, the refreshed auxiliary and untouched
laws are unchanged, and the enhanced law is the old auxiliary mixture of `κ`. -/
theorem blockLaw_bind_blockKernel (ν : OpenPath.FinProb ε) (μ : OpenPath.FinProb α)
    (ξ : OpenPath.FinProb ρ) (κ : α → OpenPath.FinProb ε) :
    (blockLaw ν μ ξ).bind (blockKernel μ κ) =
      blockLaw (μ.bind κ) μ ξ := by
  apply OpenPath.FinProb.ext
  rintro ⟨⟨e', a'⟩, r'⟩
  simp only [OpenPath.FinProb.mass_bind, blockLaw, blockKernel,
    FinProb.prod_mass, FinProb.pure_mass]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  -- Sum out the untouched old coordinate, then the discarded enhanced bit.
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  rw [Finset.sum_comm]
  calc
    (∑ a : α, ∑ x : ε,
        ν.mass x * μ.mass a * ξ.mass r' * ((κ a).mass e' * μ.mass a')) =
        ∑ a : α, μ.mass a * (κ a).mass e' * ξ.mass r' * μ.mass a' := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ x : ε, ν.mass x * μ.mass a * ξ.mass r' *
            ((κ a).mass e' * μ.mass a')) =
            (∑ x : ε, ν.mass x) *
              (μ.mass a * ξ.mass r' * ((κ a).mass e' * μ.mass a')) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by rw [ν.sum_mass]; ring
    _ = (∑ a : α, μ.mass a * (κ a).mass e') * (ξ.mass r' * μ.mass a') := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((μ.bind κ).mass e' * μ.mass a') * ξ.mass r' := by
      simp only [OpenPath.FinProb.mass_bind]
      ring

/-- If the auxiliary mixture of the enhanced kernel is the enhanced marginal,
the joint product law is exactly invariant under the block update. -/
theorem blockLaw_invariant (ν : OpenPath.FinProb ε) (μ : OpenPath.FinProb α)
    (ξ : OpenPath.FinProb ρ) (κ : α → OpenPath.FinProb ε)
    (hκ : μ.bind κ = ν) :
    (blockLaw ν μ ξ).bind (blockKernel μ κ) = blockLaw ν μ ξ := by
  rw [blockLaw_bind_blockKernel, hκ]

variable {S : Type*} [Fintype S]

/-- The enhanced block kernel transported to any equivalent finite state
space.  In applications `S` is the full indexed pair configuration and `D`
separates the enhanced edge, auxiliary edges, and all remaining edges. -/
noncomputable def transportedBlockKernel (D : S ≃ (ε × α) × ρ)
    (μ : OpenPath.FinProb α) (κ : α → OpenPath.FinProb ε) : S → OpenPath.FinProb S :=
  fun s => (blockKernel μ κ (D s)).map D.symm

/-- Transporting the block update commutes with finite bind. -/
theorem map_bind_transportedBlockKernel (D : S ≃ (ε × α) × ρ)
    (law : OpenPath.FinProb S) (μ : OpenPath.FinProb α)
    (κ : α → OpenPath.FinProb ε) :
    ((law.map D).bind (blockKernel μ κ)).map D.symm =
      law.bind (transportedBlockKernel D μ κ) := by
  rw [OpenPath.FinProb.map_bind, OpenPath.FinProb.bind_map_equiv]
  rfl

/-- Joint invariance on the original state space.  The only hypotheses are the
proved block-decomposition identity for the input law and the one-coordinate
mixture identity for the enhanced kernel. -/
theorem bind_transportedBlockKernel_invariant (D : S ≃ (ε × α) × ρ)
    (law : OpenPath.FinProb S) (ν : OpenPath.FinProb ε) (μ : OpenPath.FinProb α)
    (ξ : OpenPath.FinProb ρ) (κ : α → OpenPath.FinProb ε)
    (hμ : law.map D = blockLaw ν μ ξ) (hκ : μ.bind κ = ν) :
    law.bind (transportedBlockKernel D μ κ) = law := by
  rw [← map_bind_transportedBlockKernel, hμ, blockLaw_invariant ν μ ξ κ hκ,
    ← hμ, OpenPath.FinProb.map_equiv_symm]

/-- Joint invariance in the `p' ≤ p` enhancement direction.  On `C`, the
ordered pair is refreshed at `(p,p)`; off `C`, at `(p',p)`.  Its averaged
first marginal has the exact `enhancedLower` rate. -/
theorem blockLaw_lowerEnhanced_invariant
    (μ : OpenPath.FinProb α) (ξ : OpenPath.FinProb ρ) (C : Set α)
    (p p' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp'0 : 0 ≤ p') (h : p' ≤ p) :
    let ν := OpenPath.coupledPair (OpenPath.enhancedLower p p' (μ.event C)) p
      (OpenPath.enhancedLower_mem_unit hp1 hp'0 h (μ.event_mem_Icc C)).1
      (OpenPath.enhancedLower_mem_Icc hp1 hp'0 h (μ.event_mem_Icc C)).2 hp1
    (blockLaw ν μ ξ).bind (blockKernel μ (fun a =>
      if a ∈ C then OpenPath.coupledPair p p hp0 le_rfl hp1 else
        OpenPath.coupledPair p' p hp'0 h hp1)) = blockLaw ν μ ξ := by
  dsimp only
  apply blockLaw_invariant
  exact OpenPath.averagedLowerPair_eq μ C p p' hp0 hp1 hp'0 h

/-- Joint invariance in the `p ≤ p'` enhancement direction.  On `C`, the
ordered pair is refreshed at `(p,p)`; off `C`, at `(p,p')`.  Its averaged
second marginal has the exact `enhancedUpper` rate. -/
theorem blockLaw_upperEnhanced_invariant
    (μ : OpenPath.FinProb α) (ξ : OpenPath.FinProb ρ) (C : Set α)
    (p p' : ℝ) (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1) (h : p ≤ p') :
    let ν := OpenPath.coupledPair p (OpenPath.enhancedUpper p p' (μ.event C)) hp0
      (OpenPath.enhancedUpper_mem_Icc hp0 h (μ.event_mem_Icc C)).1
      (OpenPath.enhancedUpper_mem_unit hp0 hp'1 h (μ.event_mem_Icc C)).2
    (blockLaw ν μ ξ).bind (blockKernel μ (fun a =>
      if a ∈ C then OpenPath.coupledPair p p hp0 le_rfl (h.trans hp'1) else
        OpenPath.coupledPair p p' hp0 h hp'1)) = blockLaw ν μ ξ := by
  dsimp only
  apply blockLaw_invariant
  exact OpenPath.averagedUpperPair_eq μ C p p' hp0 hp'1 h

section IndexedProduct

variable {E β : Type*} [Fintype E] [DecidableEq E] [Fintype β]

/-- Auxiliary indices in the complement of the distinguished enhanced edge. -/
abbrev AuxiliaryIndex (E : Type*) [DecidableEq E] (e : E) (A : Finset E) :=
  {j : {i : E // i ≠ e} // (j : E) ∈ A}

/-- Indices neither enhanced nor refreshed in the block update. -/
abbrev RemainingIndex (E : Type*) [DecidableEq E] (e : E) (A : Finset E) :=
  {j : {i : E // i ≠ e} // (j : E) ∉ A}

/-- Separate an indexed configuration into the enhanced value, its auxiliary
configuration, and the configuration left untouched by the block update. -/
noncomputable def indexedBlockEquiv (e : E) (A : Finset E) :
    (E → β) ≃ (β × (AuxiliaryIndex E e A → β)) × (RemainingIndex E e A → β) :=
  ((Equiv.piSplitAt e (fun _ : E => β)).trans
    (Equiv.prodCongr (Equiv.refl β)
      (Equiv.piEquivPiSubtypeProd
        (fun j : {i : E // i ≠ e} => (j : E) ∈ A) (fun _ => β)))).trans
    (Equiv.prodAssoc β (AuxiliaryIndex E e A → β) (RemainingIndex E e A → β)).symm

/-- The product indexed law, written on the three-block state space. -/
noncomputable def indexedBlockLaw (ν : E → OpenPath.FinProb β)
    (e : E) (A : Finset E) :
    OpenPath.FinProb ((β × (AuxiliaryIndex E e A → β)) ×
      (RemainingIndex E e A → β)) :=
  blockLaw (ν e) (OpenPath.FinProb.pi (fun a => ν a.1.1))
    (OpenPath.FinProb.pi (fun r => ν r.1.1))

/-- A product law over all indices really is the product of its enhanced,
auxiliary, and untouched restrictions. -/
theorem map_pi_indexedBlockEquiv (ν : E → OpenPath.FinProb β)
    (e : E) (A : Finset E) :
    (OpenPath.FinProb.pi ν).map (indexedBlockEquiv e A) = indexedBlockLaw ν e A := by
  apply OpenPath.FinProb.ext
  rintro ⟨⟨b, a⟩, r⟩
  rw [OpenPath.FinProb.mass_map_equiv]
  change (∏ i : E, (ν i).mass ((indexedBlockEquiv e A).symm ⟨⟨b, a⟩, r⟩ i)) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ e]
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun j : {i : E // i ≠ e} => (j : E) ∈ A)
    (fun j => (ν j.1).mass ((indexedBlockEquiv e A).symm ⟨⟨b, a⟩, r⟩ j.1))]
  have hne_aux (x : AuxiliaryIndex E e A) : (x.1.1 : E) ≠ e := x.1.2
  have hne_rest (x : RemainingIndex E e A) : (x.1.1 : E) ≠ e := x.1.2
  have hA_aux (x : AuxiliaryIndex E e A) : (x.1.1 : E) ∈ A := x.2
  have hA_rest (x : RemainingIndex E e A) : (x.1.1 : E) ∉ A := x.2
  simp [indexedBlockLaw, blockLaw, indexedBlockEquiv, Equiv.piSplitAt,
    Equiv.piEquivPiSubtypeProd, hne_aux, hne_rest, hA_aux, hA_rest, mul_assoc]

/-- Full indexed joint-product invariance.  Only the finite one-coordinate
mixture identity is required; the product decomposition is proved above. -/
theorem pi_bind_transportedBlockKernel_invariant (ν : E → OpenPath.FinProb β)
    (e : E) (A : Finset E) (κ : (AuxiliaryIndex E e A → β) → OpenPath.FinProb β)
    (hκ : (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).bind κ = ν e) :
    (OpenPath.FinProb.pi ν).bind (transportedBlockKernel (indexedBlockEquiv e A)
      (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)) κ) =
        OpenPath.FinProb.pi ν := by
  exact bind_transportedBlockKernel_invariant (indexedBlockEquiv e A)
    (OpenPath.FinProb.pi ν) (ν e)
    (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1))
    (OpenPath.FinProb.pi (fun r : RemainingIndex E e A => ν r.1.1)) κ
    (map_pi_indexedBlockEquiv ν e A) hκ

/-- Full ordered joint-product invariance for the lower enhanced rate, in the
`p' ≤ p` direction.  Local laws on untouched edges may be arbitrary; this is
what permits other enhanced edges to have their own stationary rates. -/
theorem pi_lowerEnhanced_invariant
    (ν : E → OpenPath.FinProb (OpenPath.Bit × OpenPath.Bit)) (e : E) (A : Finset E)
    (C : Set (AuxiliaryIndex E e A → OpenPath.Bit × OpenPath.Bit))
    (p p' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp'0 : 0 ≤ p') (h : p' ≤ p)
    (hνe : ν e = OpenPath.coupledPair
      (OpenPath.enhancedLower p p'
        ((OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).event C)) p
      (OpenPath.enhancedLower_mem_unit hp1 hp'0 h
        ((OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).event_mem_Icc C)).1
      (OpenPath.enhancedLower_mem_Icc hp1 hp'0 h
        ((OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).event_mem_Icc C)).2 hp1) :
    (OpenPath.FinProb.pi ν).bind (transportedBlockKernel (indexedBlockEquiv e A)
      (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)) (fun a =>
        if a ∈ C then OpenPath.coupledPair p p hp0 le_rfl hp1 else
          OpenPath.coupledPair p' p hp'0 h hp1)) = OpenPath.FinProb.pi ν := by
  apply pi_bind_transportedBlockKernel_invariant
  rw [hνe]
  exact OpenPath.averagedLowerPair_eq _ C p p' hp0 hp1 hp'0 h

/-- Full ordered joint-product invariance for the upper enhanced rate, in the
`p ≤ p'` direction. -/
theorem pi_upperEnhanced_invariant
    (ν : E → OpenPath.FinProb (OpenPath.Bit × OpenPath.Bit)) (e : E) (A : Finset E)
    (C : Set (AuxiliaryIndex E e A → OpenPath.Bit × OpenPath.Bit))
    (p p' : ℝ) (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1) (h : p ≤ p')
    (hνe : ν e = OpenPath.coupledPair p
      (OpenPath.enhancedUpper p p'
        ((OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).event C)) hp0
      (OpenPath.enhancedUpper_mem_Icc hp0 h
        ((OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).event_mem_Icc C)).1
      (OpenPath.enhancedUpper_mem_unit hp0 hp'1 h
        ((OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)).event_mem_Icc C)).2) :
    (OpenPath.FinProb.pi ν).bind (transportedBlockKernel (indexedBlockEquiv e A)
      (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1)) (fun a =>
        if a ∈ C then OpenPath.coupledPair p p hp0 le_rfl (h.trans hp'1) else
          OpenPath.coupledPair p p' hp0 h hp'1)) = OpenPath.FinProb.pi ν := by
  apply pi_bind_transportedBlockKernel_invariant
  rw [hνe]
  exact OpenPath.averagedUpperPair_eq _ C p p' hp0 hp'1 h

/-- The edgewise independent ordered coupling of two inhomogeneous Bernoulli
configuration laws. -/
noncomputable def orderedPairProduct (y z : E → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hyz : ∀ e, y e ≤ z e) (hz : ∀ e, z e ≤ 1) :
    OpenPath.FinProb (E → OpenPath.Bit × OpenPath.Bit) :=
  OpenPath.FinProb.pi (fun e => OpenPath.coupledPair (y e) (z e) (hy e) (hyz e) (hz e))

/-- The first marginal of `orderedPairProduct` is the existing finite product
law with the lower rates. -/
theorem orderedPairProduct_map_fst (y z : E → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hyz : ∀ e, y e ≤ z e) (hz : ∀ e, z e ≤ 1) :
    (orderedPairProduct y z hy hyz hz).map (fun ω e => (ω e).1) =
      OpenPath.productLaw y (fun e => ⟨(hy e), (hyz e).trans (hz e)⟩) := by
  unfold orderedPairProduct OpenPath.productLaw
  rw [OpenPath.FinProb.pi_map]
  congr 1
  funext e
  exact OpenPath.coupledPair_fst (y e) (z e) (hy e) (hyz e) (hz e)

/-- The second marginal is the product law with the upper rates. -/
theorem orderedPairProduct_map_snd (y z : E → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hyz : ∀ e, y e ≤ z e) (hz : ∀ e, z e ≤ 1) :
    (orderedPairProduct y z hy hyz hz).map (fun ω e => (ω e).2) =
      OpenPath.productLaw z (fun e => ⟨(hy e).trans (hyz e), hz e⟩) := by
  unfold orderedPairProduct OpenPath.productLaw
  rw [OpenPath.FinProb.pi_map]
  congr 1
  funext e
  exact OpenPath.coupledPair_snd (y e) (z e) (hy e) (hyz e) (hz e)

/-- Exact probability of any lower-configuration event under the edgewise
ordered pair product. -/
theorem orderedPairProduct_event_fst (y z : E → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hyz : ∀ e, y e ≤ z e) (hz : ∀ e, z e ≤ 1) (B : Set (OpenPath.Config E)) :
    (orderedPairProduct y z hy hyz hz).event ((fun ω e => (ω e).1) ⁻¹' B) =
      (OpenPath.productLaw y (fun e => ⟨(hy e), (hyz e).trans (hz e)⟩)).event B := by
  rw [OpenPath.FinProb.event_preimage_map, orderedPairProduct_map_fst]

/-- Exact probability of any upper-configuration event under the edgewise
ordered pair product. -/
theorem orderedPairProduct_event_snd (y z : E → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hyz : ∀ e, y e ≤ z e) (hz : ∀ e, z e ≤ 1) (B : Set (OpenPath.Config E)) :
    (orderedPairProduct y z hy hyz hz).event ((fun ω e => (ω e).2) ⁻¹' B) =
      (OpenPath.productLaw z (fun e => ⟨(hy e).trans (hyz e), hz e⟩)).event B := by
  rw [OpenPath.FinProb.event_preimage_map, orderedPairProduct_map_snd]

/-- The open-path certificate probability in the joint product law is exactly
`OpenPath.pathEventProbability` at the lower (i.e. `min`) homogeneous rate. -/
theorem orderedPairProduct_pathEventProbability (r s : ℝ)
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s ≤ 1) (Γ : Set (Finset E)) :
    (orderedPairProduct (fun _ => r) (fun _ => s)
      (fun _ => hr0) (fun _ => hrs) (fun _ => hs1)).event
        ((fun ω e => (ω e).1) ⁻¹' {ω | OpenPath.SomePathOpen Γ ω}) =
      OpenPath.pathEventProbability r ⟨hr0, hrs.trans hs1⟩ Γ := by
  rw [orderedPairProduct_event_fst]
  rfl

end IndexedProduct

end JointInvariance
