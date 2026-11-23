import Mathlib

noncomputable section

local instance (priority := low) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# Open-path enhancement: finite probability update lemmas

This file develops finite, exact ingredients of Proposition 3.2 of
Beffara--Faipeur--Oke (arXiv:2512.16486). It does not identify stationary
distributions of the full heat-bath chain. The proved results include the
ordered update, exact enhanced one-bit laws, and positivity/bounds for
path-event enhancement parameters.
-/

open scoped BigOperators
open Set

namespace OpenPath

/-- A probability law on a finite type, presented by its real point masses. -/
structure FinProb (α : Type*) [Fintype α] where
  mass : α → ℝ
  mass_nonneg : ∀ a, 0 ≤ mass a
  sum_mass : ∑ a, mass a = 1

namespace FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

@[ext] lemma ext {μ ν : FinProb α} (h : ∀ a, μ.mass a = ν.mass a) : μ = ν := by
  cases μ
  cases ν
  simp_all only [mk.injEq]
  funext a
  exact h a

/-- Probability of an event on a finite type. -/
noncomputable def event (μ : FinProb α) (A : Set α) : ℝ := by
  exact ∑ a, if a ∈ A then μ.mass a else 0

lemma event_nonneg (μ : FinProb α) (A : Set α) : 0 ≤ μ.event A := by
  unfold event
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact μ.mass_nonneg a
  · exact le_rfl

lemma event_le_one (μ : FinProb α) (A : Set α) : μ.event A ≤ 1 := by
  calc
    μ.event A ≤ ∑ a, μ.mass a := by
      unfold event
      apply Finset.sum_le_sum
      intro a _
      split_ifs
      · exact le_rfl
      · exact μ.mass_nonneg a
    _ = 1 := μ.sum_mass

lemma event_mem_Icc (μ : FinProb α) (A : Set α) : μ.event A ∈ Icc (0 : ℝ) 1 :=
  ⟨μ.event_nonneg A, μ.event_le_one A⟩

lemma event_complement (μ : FinProb α) (A : Set α) :
    μ.event Aᶜ = 1 - μ.event A := by
  have h : (∑ a, ((if a ∈ A then μ.mass a else 0) +
      (if a ∈ Aᶜ then μ.mass a else 0))) = ∑ a, μ.mass a := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ A <;> simp [ha]
  simp only [Set.mem_compl_iff] at h
  simp only [event, Set.mem_compl_iff]
  rw [Finset.sum_add_distrib, μ.sum_mass] at h
  linear_combination h

/-- The law of a deterministic function of a finite random variable. -/
noncomputable def map (f : α → β) (μ : FinProb α) : FinProb β := by
  let m : β → ℝ := fun b => ∑ a, if f a = b then μ.mass a else 0
  refine { mass := m, mass_nonneg := ?_, sum_mass := ?_ }
  · intro b
    dsimp [m]
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact μ.mass_nonneg a
    · exact le_rfl
  · dsimp [m]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    exact μ.sum_mass

/-- Composition with a finite Markov kernel. -/
noncomputable def bind (μ : FinProb α) (κ : α → FinProb β) : FinProb β where
  mass b := ∑ a, μ.mass a * (κ a).mass b
  mass_nonneg b := by
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (μ.mass_nonneg a) ((κ a).mass_nonneg b)
  sum_mass := by
    calc
      ∑ b, ∑ a, μ.mass a * (κ a).mass b = ∑ a, ∑ b, μ.mass a * (κ a).mass b :=
        Finset.sum_comm
      _ = ∑ a, μ.mass a * (∑ b, (κ a).mass b) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ = ∑ a, μ.mass a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [(κ a).sum_mass, mul_one]
      _ = 1 := μ.sum_mass

lemma mass_map (f : α → β) (μ : FinProb α) (b : β) :
    (μ.map f).mass b = ∑ a, if f a = b then μ.mass a else 0 := rfl

lemma mass_bind (μ : FinProb α) (κ : α → FinProb β) (b : β) :
    (μ.bind κ).mass b = ∑ a, μ.mass a * (κ a).mass b := rfl

/-- Average two constants, with one branch occurring on `A`. -/
lemma sum_mass_mul_ite (μ : FinProb α) (A : Set α) (c d : ℝ) :
    (∑ a, μ.mass a * if a ∈ A then c else d) =
      μ.event A * c + (1 - μ.event A) * d := by
  have hA : (∑ a, μ.mass a * if a ∈ A then c else 0) = μ.event A * c := by
    rw [event, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ A <;> simp [ha]
  have hAc : (∑ a, μ.mass a * if a ∈ A then 0 else d) =
      (1 - μ.event A) * d := by
    calc
      (∑ a, μ.mass a * if a ∈ A then 0 else d) =
          ∑ a, (if a ∈ Aᶜ then μ.mass a else 0) * d := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ∈ A <;> simp [ha]
      _ = μ.event Aᶜ * d := by
        simp only [event, Set.mem_compl_iff, Finset.sum_mul]
      _ = (1 - μ.event A) * d := by rw [event_complement]
  calc
    (∑ a, μ.mass a * if a ∈ A then c else d) =
        (∑ a, μ.mass a * if a ∈ A then c else 0) +
          ∑ a, μ.mass a * if a ∈ A then 0 else d := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ A <;> simp [ha]
    _ = μ.event A * c + (1 - μ.event A) * d := by rw [hA, hAc]

/-- An ordered coupling of finite laws. -/
structure OrderedCoupling [Preorder α] (μ ν : FinProb α) where
  law : FinProb (α × α)
  fst : law.map Prod.fst = μ
  snd : law.map Prod.snd = ν
  ordered : ∀ a, law.mass a ≠ 0 → a.1 ≤ a.2

/-- Stochastic domination using increasing events, as in the paper. -/
def StochLe [Preorder α] (μ ν : FinProb α) : Prop :=
  ∀ A : Set α, (∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, a ≤ b → b ∈ A) → μ.event A ≤ ν.event A

end FinProb

/-- Bits are ordered with `0` closed and `1` open. -/
abbrev Bit := Fin 2

/-- A Bernoulli law with probability `r` of bit `1`. -/
def bitLaw (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : FinProb Bit where
  mass b := if b = 1 then r else 1 - r
  mass_nonneg b := by
    rcases hr with ⟨hr0, hr1⟩
    split_ifs <;> linarith
  sum_mass := by
    rw [Fin.sum_univ_two]
    norm_num

@[simp] lemma bitLaw_mass_one (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    (bitLaw r hr).mass 1 = r := by simp [bitLaw]

@[simp] lemma bitLaw_mass_zero (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    (bitLaw r hr).mass 0 = 1 - r := by simp [bitLaw]

/-- Independent finite product of probability laws. -/
noncomputable def FinProb.pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (μ : ∀ i, FinProb (α i)) : FinProb (∀ i, α i) where
  mass f := ∏ i, (μ i).mass (f i)
  mass_nonneg f := Finset.prod_nonneg fun i _ => (μ i).mass_nonneg (f i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp only [FinProb.sum_mass, Finset.prod_const_one]

@[simp] lemma FinProb.pi_mass {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (μ : ∀ i, FinProb (α i)) (f : ∀ i, α i) :
    (FinProb.pi μ).mass f = ∏ i, (μ i).mass (f i) := rfl

/-- A finite configuration of open and closed edges. -/
abbrev Config (E : Type*) := E → Bit

/-- Independent, possibly inhomogeneous, bond percolation. -/
noncomputable def productLaw {E : Type*} [Fintype E] [DecidableEq E] (r : E → ℝ)
    (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1) : FinProb (Config E) :=
  FinProb.pi (fun e => bitLaw (r e) (hr e))

lemma productLaw_mass_pos {E : Type*} [Fintype E] [DecidableEq E] (r : E → ℝ)
    (hr : ∀ e, 0 < r e ∧ r e < 1) (ω : Config E) :
    0 < (productLaw r (fun e => ⟨(hr e).1.le, (hr e).2.le⟩)).mass ω := by
  unfold productLaw
  rw [FinProb.pi_mass]
  apply Finset.prod_pos
  intro e _
  change 0 < (if ω e = 1 then r e else 1 - r e)
  split_ifs with h
  · exact (hr e).1
  · linarith [(hr e).2]

lemma event_pos_of_mass_pos {α : Type*} [Fintype α] {μ : FinProb α}
    (hm : ∀ a, 0 < μ.mass a) {A : Set α} (hA : ∃ a, a ∈ A) : 0 < μ.event A := by
  obtain ⟨a, ha⟩ := hA
  unfold FinProb.event
  apply Finset.sum_pos'
  · intro b _
    split_ifs
    · exact μ.mass_nonneg b
    · exact le_rfl
  · refine ⟨a, Finset.mem_univ a, ?_⟩
    simp [ha, hm a]

/-- A set of edges is open in a configuration. -/
def OpenEdges {E : Type*} [DecidableEq E] (γ : Finset E) (ω : Config E) : Prop :=
  ∀ e ∈ γ, ω e = 1

/-- At least one member of a collection `Γ` of paths is open. -/
def SomePathOpen {E : Type*} [DecidableEq E] (Γ : Set (Finset E))
    (ω : Config E) : Prop := ∃ γ ∈ Γ, OpenEdges γ ω

/-- Path-openness only increases when edges are added. -/
lemma SomePathOpen.monotone {E : Type*} [DecidableEq E] {Γ : Set (Finset E)}
    {ω ξ : Config E} (h : ω ≤ ξ) (hω : SomePathOpen Γ ω) : SomePathOpen Γ ξ := by
  obtain ⟨γ, hγ, hopen⟩ := hω
  refine ⟨γ, hγ, ?_⟩
  intro e he
  have hle := h e
  rw [hopen e he] at hle
  apply Fin.ext
  simp only [Fin.le_iff_val_le_val, Fin.val_one] at hle ⊢
  omega

/-- A nonempty path collection has positive product probability whenever all
edge parameters lie strictly between zero and one. -/
lemma somePathOpen_event_pos {E : Type*} [Fintype E] [DecidableEq E]
    (r : E → ℝ) (hr : ∀ e, 0 < r e ∧ r e < 1) {Γ : Set (Finset E)}
    (hΓ : Γ.Nonempty) :
    0 < (productLaw r (fun e => ⟨(hr e).1.le, (hr e).2.le⟩)).event
      {ω | SomePathOpen Γ ω} := by
  obtain ⟨γ, hγ⟩ := hΓ
  apply event_pos_of_mass_pos
  · exact productLaw_mass_pos r hr
  · refine ⟨fun _ => 1, ?_⟩
    exact ⟨γ, hγ, by simp [OpenEdges]⟩

end OpenPath

namespace OpenPath

/-- The unique coordinatewise coupling of two two-point laws using one uniform
variable. Its only ordered states with positive mass are `00`, `01`, and `11`. -/
def coupledPair (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    FinProb (Bit × Bit) where
  mass b := if b = (1, 1) then y else if b = (0, 1) then z - y else
    if b = (0, 0) then 1 - z else 0
  mass_nonneg b := by
    split_ifs <;> linarith
  sum_mass := by
    change (∑ b : Bit × Bit, if b = (1, 1) then y else if b = (0, 1) then z - y else
      if b = (0, 0) then 1 - z else 0) = 1
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_two]

@[simp] lemma coupledPair_mass_11 (y z : ℝ) (hy hyz hz) :
    (coupledPair y z hy hyz hz).mass (1, 1) = y := by
  simp [coupledPair]

@[simp] lemma coupledPair_mass_01 (y z : ℝ) (hy hyz hz) :
    (coupledPair y z hy hyz hz).mass (0, 1) = z - y := by
  simp [coupledPair]

@[simp] lemma coupledPair_mass_00 (y z : ℝ) (hy hyz hz) :
    (coupledPair y z hy hyz hz).mass (0, 0) = 1 - z := by
  simp [coupledPair]

@[simp] lemma coupledPair_mass_10 (y z : ℝ) (hy hyz hz) :
    (coupledPair y z hy hyz hz).mass (1, 0) = 0 := by
  simp [coupledPair]

lemma coupledPair_ordered (y z : ℝ) (hy hyz hz) {b : Bit × Bit}
    (hb : (coupledPair y z hy hyz hz).mass b ≠ 0) : b.1 ≤ b.2 := by
  rcases b with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp_all [coupledPair]

lemma coupledPair_fst (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (coupledPair y z hy hyz hz).map Prod.fst =
      bitLaw y ⟨hy, hyz.trans hz⟩ := by
  apply FinProb.ext
  intro b
  fin_cases b <;>
    simp [FinProb.mass_map, coupledPair, bitLaw, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma coupledPair_snd (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (coupledPair y z hy hyz hz).map Prod.snd =
      bitLaw z ⟨hy.trans hyz, hz⟩ := by
  apply FinProb.ext
  intro b
  fin_cases b <;>
    simp [FinProb.mass_map, coupledPair, bitLaw, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The enhanced lower open probability in Proposition 3.2(2). -/
def enhancedLower (p p' a : ℝ) : ℝ := p' + (p - p') * a

/-- The enhanced upper open probability in Proposition 3.2(1). -/
def enhancedUpper (p p' a : ℝ) : ℝ := p' - (p' - p) * a

lemma enhancedLower_mem_Icc {p p' a : ℝ} (_hp : p ≤ 1) (hp'0 : 0 ≤ p')
    (h : p' ≤ p) (ha : a ∈ Icc (0 : ℝ) 1) :
    enhancedLower p p' a ∈ Icc (0 : ℝ) p := by
  rcases ha with ⟨ha0, ha1⟩
  constructor
  · dsimp [enhancedLower]
    positivity
  · dsimp [enhancedLower]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ha1)]

lemma enhancedLower_mem_unit {p p' a : ℝ} (hp : p ≤ 1) (hp'0 : 0 ≤ p')
    (h : p' ≤ p) (ha : a ∈ Icc (0 : ℝ) 1) :
    enhancedLower p p' a ∈ Icc (0 : ℝ) 1 :=
  ⟨(enhancedLower_mem_Icc hp hp'0 h ha).1,
    (enhancedLower_mem_Icc hp hp'0 h ha).2.trans hp⟩

lemma enhancedUpper_mem_Icc {p p' a : ℝ} (_hp0 : 0 ≤ p) (h : p ≤ p')
    (ha : a ∈ Icc (0 : ℝ) 1) : enhancedUpper p p' a ∈ Icc p p' := by
  rcases ha with ⟨ha0, ha1⟩
  constructor
  · dsimp [enhancedUpper]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ha1)]
  · dsimp [enhancedUpper]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) ha0]

lemma enhancedUpper_mem_unit {p p' a : ℝ} (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1)
    (h : p ≤ p') (ha : a ∈ Icc (0 : ℝ) 1) :
    enhancedUpper p p' a ∈ Icc (0 : ℝ) 1 :=
  ⟨hp0.trans (enhancedUpper_mem_Icc hp0 h ha).1,
    (enhancedUpper_mem_Icc hp0 h ha).2.trans hp'1⟩

/-- Average of the enhanced update of the ordered pair over the old
auxiliary configuration. This is the `p > p'` branch of Proposition 3.2. -/
noncomputable def averagedLowerPair {α : Type*} [Fintype α] (ν : FinProb α)
    (A : Set α) (p p' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp'0 : 0 ≤ p') (h : p' ≤ p) : FinProb (Bit × Bit) :=
  ν.bind (fun a => if a ∈ A then coupledPair p p hp0 le_rfl hp1 else
    coupledPair p' p hp'0 h hp1)

/-- Average enhanced pair law in the `p < p'` branch of Proposition 3.2. -/
noncomputable def averagedUpperPair {α : Type*} [Fintype α] (ν : FinProb α)
    (A : Set α) (p p' : ℝ) (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1)
    (h : p ≤ p') : FinProb (Bit × Bit) :=
  ν.bind (fun a => if a ∈ A then coupledPair p p hp0 le_rfl (h.trans hp'1) else
    coupledPair p p' hp0 h hp'1)

/-- Exact stationary enhanced bit law for the lower comparison. -/
lemma averagedLowerPair_eq {α : Type*} [Fintype α] (ν : FinProb α)
    (A : Set α) (p p' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp'0 : 0 ≤ p') (h : p' ≤ p) :
    averagedLowerPair ν A p p' hp0 hp1 hp'0 h =
      coupledPair (enhancedLower p p' (ν.event A)) p
        (enhancedLower_mem_unit hp1 hp'0 h (ν.event_mem_Icc A)).1
        (enhancedLower_mem_Icc hp1 hp'0 h (ν.event_mem_Icc A)).2 hp1 := by
  have he0 : 0 ≤ enhancedLower p p' (ν.event A) :=
    (enhancedLower_mem_Icc hp1 hp'0 h (ν.event_mem_Icc A)).1
  have hep : enhancedLower p p' (ν.event A) ≤ p :=
    (enhancedLower_mem_Icc hp1 hp'0 h (ν.event_mem_Icc A)).2
  apply FinProb.ext
  intro b
  change (∑ a, ν.mass a * (if a ∈ A then coupledPair p p hp0 le_rfl hp1 else
    coupledPair p' p hp'0 h hp1).mass b) =
      (coupledPair (enhancedLower p p' (ν.event A)) p he0 hep hp1).mass b
  simp_rw [apply_ite (fun q : FinProb (Bit × Bit) => q.mass b)]
  rw [FinProb.sum_mass_mul_ite]
  rcases b with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [coupledPair, enhancedLower] <;> ring

/-- Exact stationary enhanced bit law for the upper comparison. -/
lemma averagedUpperPair_eq {α : Type*} [Fintype α] (ν : FinProb α)
    (A : Set α) (p p' : ℝ) (hp0 : 0 ≤ p) (hp'1 : p' ≤ 1)
    (h : p ≤ p') :
    averagedUpperPair ν A p p' hp0 hp'1 h =
      coupledPair p (enhancedUpper p p' (ν.event A)) hp0
        (enhancedUpper_mem_Icc hp0 h (ν.event_mem_Icc A)).1
        (enhancedUpper_mem_unit hp0 hp'1 h (ν.event_mem_Icc A)).2 := by
  have hep : p ≤ enhancedUpper p p' (ν.event A) :=
    (enhancedUpper_mem_Icc hp0 h (ν.event_mem_Icc A)).1
  have he1 : enhancedUpper p p' (ν.event A) ≤ 1 :=
    (enhancedUpper_mem_unit hp0 hp'1 h (ν.event_mem_Icc A)).2
  apply FinProb.ext
  intro b
  change (∑ a, ν.mass a * (if a ∈ A then coupledPair p p hp0 le_rfl (h.trans hp'1) else
    coupledPair p p' hp0 h hp'1).mass b) =
      (coupledPair p (enhancedUpper p p' (ν.event A)) hp0 hep he1).mass b
  simp_rw [apply_ite (fun q : FinProb (Bit × Bit) => q.mass b)]
  rw [FinProb.sum_mass_mul_ite]
  rcases b with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [coupledPair, enhancedUpper] <;> ring

/-- The FK conditional threshold of one edge. -/
def fkThreshold {E : Type*} (p p' : ℝ) (K : Config E → Prop) (ω : Config E) : ℝ :=
  if K ω then p else p'

/-- One uniform variable opens an edge exactly below its threshold. -/
def coinOpen (u r : ℝ) : Bit := if u < r then 1 else 0

lemma coinOpen_mono {u a b : ℝ} (h : a ≤ b) : coinOpen u a ≤ coinOpen u b := by
  by_cases ha : u < a
  · have hb : u < b := ha.trans_le h
    simp [coinOpen, ha, hb]
  · by_cases hb : u < b <;> simp [coinOpen, ha, hb]

/-- The common-uniform enhanced update of the triple `(Y,X,Z)`. On an open
path in `Y`, all three thresholds are `p`; otherwise they are respectively
`lo`, the FK threshold of `X`, and `hi`. -/
def pathEnhancedBits {E : Type*} [DecidableEq E] (p p' lo hi : ℝ)
    (K : Config E → Prop) (Γ : Set (Finset E)) (y x : Config E) (u : ℝ) :
    Bit × Bit × Bit :=
  if SomePathOpen Γ y then
    (coinOpen u p, coinOpen u (fkThreshold p p' K x), coinOpen u p) else
    (coinOpen u lo, coinOpen u (fkThreshold p p' K x), coinOpen u hi)

/-- The pathwise order preservation at an enhanced update. The hypotheses
`lo ≤ p,p' ≤ hi` specialize to `(lo,hi)=(p',p)` and `(p,p')`, respectively. -/
lemma pathEnhancedBits_ordered {E : Type*} [DecidableEq E]
    {p p' lo hi : ℝ} (hlo : lo ≤ p) (hlo' : lo ≤ p')
    (hhi : p ≤ hi) (hhi' : p' ≤ hi)
    {K : Config E → Prop} (hK : ∀ {ω ξ}, ω ≤ ξ → K ω → K ξ)
    {Γ : Set (Finset E)} (hΓ : ∀ {ω}, SomePathOpen Γ ω → K ω)
    {y x : Config E} (hyx : y ≤ x) (u : ℝ) :
    let b := pathEnhancedBits p p' lo hi K Γ y x u
    b.1 ≤ b.2.1 ∧ b.2.1 ≤ b.2.2 := by
  dsimp [pathEnhancedBits]
  split_ifs with hpath
  · have hxK : K x := hK hyx (hΓ hpath)
    simp [fkThreshold, hxK]
  · have hpth : lo ≤ fkThreshold p p' K x := by
      dsimp [fkThreshold]
      split_ifs <;> assumption
    have hpth' : fkThreshold p p' K x ≤ hi := by
      dsimp [fkThreshold]
      split_ifs <;> assumption
    exact ⟨coinOpen_mono hpth, coinOpen_mono hpth'⟩

/-- In the path case the middle component also actually uses threshold `p`;
this lemma makes the use of `K` in the proof explicit. -/
lemma fkThreshold_of_path {E : Type*} [DecidableEq E]
    {p p' : ℝ} {K : Config E → Prop} {Γ : Set (Finset E)}
    (hK : ∀ {ω ξ}, ω ≤ ξ → K ω → K ξ)
    (hΓ : ∀ {ω}, SomePathOpen Γ ω → K ω)
    {y x : Config E} (hyx : y ≤ x) (hpath : SomePathOpen Γ y) :
    fkThreshold p p' K x = p := by
  rw [fkThreshold, if_pos (hK hyx (hΓ hpath))]

/-- Update one coordinate of a configuration. -/
def updateAt {E : Type*} [DecidableEq E] (ω : Config E) (e : E) (b : Bit) :
    Config E := Function.update ω e b

lemma updateAt_mono {E : Type*} [DecidableEq E] {y x : Config E}
    (hyx : y ≤ x) {e : E} {a b : Bit} (hab : a ≤ b) :
    updateAt y e a ≤ updateAt x e b := by
  intro f
  by_cases hf : f = e
  · subst f
    simpa [updateAt] using hab
  · simpa [updateAt, Function.update_of_ne hf] using hyx f

/-- Apply `pathEnhancedBits` at edge `e` to all three configurations. -/
def pathEnhancedUpdate {E : Type*} [DecidableEq E] (e : E) (p p' lo hi : ℝ)
    (K : Config E → Prop) (Γ : Set (Finset E))
    (y x z : Config E) (u : ℝ) : Config E × Config E × Config E :=
  let b := pathEnhancedBits p p' lo hi K Γ y x u
  (updateAt y e b.1, updateAt x e b.2.1, updateAt z e b.2.2)

/-- Configuration-level order preservation for the open-path enhancement. -/
lemma pathEnhancedUpdate_ordered {E : Type*} [DecidableEq E]
    {p p' lo hi : ℝ} (hlo : lo ≤ p) (hlo' : lo ≤ p')
    (hhi : p ≤ hi) (hhi' : p' ≤ hi)
    {K : Config E → Prop} (hK : ∀ {ω ξ}, ω ≤ ξ → K ω → K ξ)
    {Γ : Set (Finset E)} (hΓ : ∀ {ω}, SomePathOpen Γ ω → K ω)
    {y x z : Config E} (hyx : y ≤ x) (hxz : x ≤ z) (e : E) (u : ℝ) :
    let c := pathEnhancedUpdate e p p' lo hi K Γ y x z u
    c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2 := by
  have hb := pathEnhancedBits_ordered hlo hlo' hhi hhi' hK hΓ hyx u
  dsimp [pathEnhancedUpdate]
  exact ⟨updateAt_mono hyx hb.1, updateAt_mono hxz hb.2⟩

end OpenPath

namespace OpenPath
namespace FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

lemma event_map (μ : FinProb α) (f : α → β) (A : Set β) :
    (μ.map f).event A = ∑ a, if f a ∈ A then μ.mass a else 0 := by
  calc
    (μ.map f).event A = ∑ b, ∑ a, if b ∈ A then
        (if f a = b then μ.mass a else 0) else 0 := by
      simp only [event, mass_map]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b ∈ A <;> simp [hb]
    _ = ∑ a, ∑ b, if b ∈ A then
        (if f a = b then μ.mass a else 0) else 0 := Finset.sum_comm
    _ = ∑ a, if f a ∈ A then μ.mass a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a ∈ A
      · rw [Finset.sum_eq_single (f a)]
        · simp [ha]
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      · simp only [ha, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro b _
        by_cases hb : f a = b
        · subst b
          simp [ha]
        · simp [hb]

/-- A coupling on the different points of the coordinatewise order gives
stochastic domination for all increasing events. -/
lemma stochLe_of_orderedCoupling [Preorder α] {μ ν : FinProb α}
    (c : OrderedCoupling μ ν) : StochLe μ ν := by
  intro A hA
  calc
    μ.event A = (c.law.map Prod.fst).event A := by rw [c.fst]
    _ = ∑ a, if a.1 ∈ A then c.law.mass a else 0 := event_map _ _ _
    _ ≤ ∑ a, if a.2 ∈ A then c.law.mass a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a.1 ∈ A
      · by_cases ha' : a.2 ∈ A
        · simp [ha, ha']
        · have hz : c.law.mass a = 0 := by
            by_contra hn
            exact ha' (hA ha (c.ordered a hn))
          simp [ha, ha', hz]
      · simp only [ha, ↓reduceIte]
        split_ifs
        · exact c.law.mass_nonneg a
        · exact le_rfl
    _ = (c.law.map Prod.snd).event A := (event_map _ _ _).symm
    _ = ν.event A := by rw [c.snd]

lemma stochLe_refl [Preorder α] (μ : FinProb α) : StochLe μ μ := by
  intro A _
  exact le_rfl

lemma stochLe_trans [Preorder α] {μ ν ρ : FinProb α}
    (hμν : StochLe μ ν) (hνρ : StochLe ν ρ) : StochLe μ ρ := by
  intro A hA
  exact (hμν A hA).trans (hνρ A hA)

/-- Pointwise convergence of all finite probability masses. -/
def LawTendsto {ι : Type*} (l : Filter ι) (μn : ι → FinProb α)
    (μ : FinProb α) : Prop :=
  ∀ a, Filter.Tendsto (fun n => (μn n).mass a) l (nhds (μ.mass a))

lemma LawTendsto.event {ι : Type*} {l : Filter ι} {μn : ι → FinProb α}
    {μ : FinProb α} (hμ : LawTendsto l μn μ) (A : Set α) :
    Filter.Tendsto (fun n => (μn n).event A) l (nhds (μ.event A)) := by
  simp only [FinProb.event]
  apply tendsto_finsetSum Finset.univ
  intro a _
  by_cases ha : a ∈ A
  · simpa [ha] using hμ a
  · simpa [ha] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (0 : ℝ)) l (nhds 0))

/-- Stochastic domination passes to finite weak distributional limits. -/
lemma stochLe_of_tendsto [Preorder α] {ι : Type*} {l : Filter ι} [l.NeBot]
    {μn νn : ι → FinProb α} {μ ν : FinProb α}
    (h : ∀ n, StochLe (μn n) (νn n))
    (hμ : LawTendsto l μn μ) (hν : LawTendsto l νn ν) : StochLe μ ν := by
  intro A hA
  exact le_of_tendsto_of_tendsto (hμ.event A) (hν.event A)
    (Filter.Eventually.of_forall fun n => h n A hA)

end FinProb

/-- All candidate paths for `e` avoid `e` and use only auxiliary edges. -/
def AuxiliaryPaths {E : Type*} [DecidableEq E] (enhanced : Finset E) (e : E)
    (Γ : Set (Finset E)) : Prop :=
  ∀ γ ∈ Γ, e ∉ γ ∧ ∀ f ∈ γ, f ∉ enhanced

/-- Each enhanced edge has at least one admissible path. -/
structure HasEnhancingPaths {E : Type*} [DecidableEq E] (enhanced : Finset E)
    (Γ : E → Set (Finset E)) : Prop where
  auxiliary : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e)
  nonempty : ∀ e ∈ enhanced, (Γ e).Nonempty

/-- Probability of the open-path event under a homogeneous product law. -/
noncomputable def pathEventProbability {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (Γ : Set (Finset E)) : ℝ :=
  (productLaw (fun _ => r) (fun _ => hr)).event {ω | SomePathOpen Γ ω}

lemma pathEventProbability_mem_Icc {E : Type*} [Fintype E] [DecidableEq E]
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (Γ : Set (Finset E)) :
    pathEventProbability r hr Γ ∈ Icc (0 : ℝ) 1 := by
  exact FinProb.event_mem_Icc _ _

/-- The bonus `d * P_r(some path is open)`. -/
noncomputable def pathBonus {E : Type*} [Fintype E] [DecidableEq E]
    (r d : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (Γ : Set (Finset E)) : ℝ :=
  d * pathEventProbability r hr Γ

lemma pathBonus_nonneg {E : Type*} [Fintype E] [DecidableEq E]
    {r d : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hd : 0 ≤ d) (Γ : Set (Finset E)) :
    0 ≤ pathBonus r d hr Γ :=
  mul_nonneg hd (pathEventProbability_mem_Icc r hr Γ).1

lemma pathBonus_le {E : Type*} [Fintype E] [DecidableEq E]
    {r d : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hd : 0 ≤ d) (Γ : Set (Finset E)) :
    pathBonus r d hr Γ ≤ d := by
  calc
    pathBonus r d hr Γ ≤ d * 1 :=
      mul_le_mul_of_nonneg_left (pathEventProbability_mem_Icc r hr Γ).2 hd
    _ = d := mul_one d

lemma pathBonus_pos {E : Type*} [Fintype E] [DecidableEq E]
    {r d : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hd : 0 < d) {Γ : Set (Finset E)} (hΓ : Γ.Nonempty) :
    0 < pathBonus r d hr Γ := by
  apply mul_pos hd
  exact somePathOpen_event_pos (fun _ : E => r) (fun _ => ⟨hr0, hr1⟩) hΓ

/-- Exact relation to the lower product parameter `p' + ε_e`. -/
lemma enhancedLower_eq_add_pathBonus {E : Type*} [Fintype E] [DecidableEq E]
    (p p' : ℝ) (hp' : p' ∈ Icc (0 : ℝ) 1) (Γ : Set (Finset E)) :
    enhancedLower p p' (pathEventProbability p' hp' Γ) =
      p' + pathBonus p' (p - p') hp' Γ := rfl

/-- Exact relation to the upper product parameter `p' - ε_e`. -/
lemma enhancedUpper_eq_sub_pathBonus {E : Type*} [Fintype E] [DecidableEq E]
    (p p' : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (Γ : Set (Finset E)) :
    enhancedUpper p p' (pathEventProbability p hp Γ) =
      p' - pathBonus p (p' - p) hp Γ := rfl

/-- Just the non-identically-zero bonus needed for the lower half of
Theorem 1.2. -/
lemma exists_lower_pathBonus_pos {E : Type*} [Fintype E] [DecidableEq E]
    {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ) (he : enhanced.Nonempty)
    {p p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (hp'0 : 0 < p') (hp'1 : p' < 1)
    (h : p' < p) :
    ∃ e ∈ enhanced, 0 < pathBonus p' (p - p') hp' (Γ e) := by
  obtain ⟨e, he⟩ := he
  exact ⟨e, he, pathBonus_pos hp' hp'0 hp'1 (sub_pos.mpr h) (hΓ.nonempty e he)⟩

/-- Just the non-identically-zero bonus needed for the upper half of
Theorem 1.2. -/
lemma exists_upper_pathBonus_pos {E : Type*} [Fintype E] [DecidableEq E]
    {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ) (he : enhanced.Nonempty)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1)
    (h : p < p') :
    ∃ e ∈ enhanced, 0 < pathBonus p (p' - p) hp (Γ e) := by
  obtain ⟨e, he⟩ := he
  exact ⟨e, he, pathBonus_pos hp hp0 hp1 (sub_pos.mpr h) (hΓ.nonempty e he)⟩

/-- Inhomogeneous upper comparison parameters, equal to `p'` off the enhanced
set and to `p' - ε_e` on it. -/
noncomputable def upperProductParameters {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) : E → ℝ := fun e =>
  if e ∈ enhanced then enhancedUpper p p' (pathEventProbability p hp (Γ e)) else p'

/-- Inhomogeneous lower comparison parameters, equal to `p'` off the enhanced
set and to `p' + ε_e` on it. -/
noncomputable def lowerProductParameters {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) : E → ℝ := fun e =>
  if e ∈ enhanced then enhancedLower p p' (pathEventProbability p' hp' (Γ e)) else p'

lemma upperProductParameters_mem_Icc {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (Γ : E → Set (Finset E)) (e : E) :
    upperProductParameters enhanced p p' hp Γ e ∈ Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ enhanced
  · rw [upperProductParameters, if_pos he]
    exact enhancedUpper_mem_unit hp.1 hp'1 h (pathEventProbability_mem_Icc p hp (Γ e))
  · rw [upperProductParameters, if_neg he]
    exact ⟨hp.1.trans h, hp'1⟩

lemma lowerProductParameters_mem_Icc {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (h : p' ≤ p) (Γ : E → Set (Finset E)) (e : E) :
    lowerProductParameters enhanced p p' hp' Γ e ∈ Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ enhanced
  · rw [lowerProductParameters, if_pos he]
    exact enhancedLower_mem_unit hp1 hp'.1 h (pathEventProbability_mem_Icc p' hp' (Γ e))
  · rw [lowerProductParameters, if_neg he]
    exact hp'

end OpenPath

namespace OpenPath

/-- Upper enhancement sizes, extended by zero outside the enhanced edge set. -/
noncomputable def upperEpsilon {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) : E → ℝ := fun e =>
  if e ∈ enhanced then pathBonus p (p' - p) hp (Γ e) else 0

/-- Lower enhancement sizes, extended by zero outside the enhanced edge set. -/
noncomputable def lowerEpsilon {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) : E → ℝ := fun e =>
  if e ∈ enhanced then pathBonus p' (p - p') hp' (Γ e) else 0

lemma upperProductParameters_eq (E : Type*) [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) :
    upperProductParameters enhanced p p' hp Γ =
      fun e => p' - upperEpsilon enhanced p p' hp Γ e := by
  funext e
  by_cases he : e ∈ enhanced <;>
    simp [upperProductParameters, upperEpsilon, he,
      ← enhancedUpper_eq_sub_pathBonus p p' hp (Γ e)]

lemma lowerProductParameters_eq (E : Type*) [Fintype E] [DecidableEq E]
    (enhanced : Finset E) (p p' : ℝ) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (Γ : E → Set (Finset E)) :
    lowerProductParameters enhanced p p' hp' Γ =
      fun e => p' + lowerEpsilon enhanced p p' hp' Γ e := by
  funext e
  by_cases he : e ∈ enhanced <;>
    simp [lowerProductParameters, lowerEpsilon, he,
      ← enhancedLower_eq_add_pathBonus p p' hp' (Γ e)]

lemma upperEpsilon_mem_Icc {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hp'1 : p' ≤ 1) (h : p ≤ p') (Γ : E → Set (Finset E)) (e : E) :
    upperEpsilon enhanced p p' hp Γ e ∈ Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ enhanced
  · rw [upperEpsilon, if_pos he]
    refine ⟨pathBonus_nonneg hp (sub_nonneg.mpr h) _, ?_⟩
    exact (pathBonus_le hp (sub_nonneg.mpr h) _).trans (by linarith [hp.1])
  · simp [upperEpsilon, he]

lemma lowerEpsilon_mem_Icc {E : Type*} [Fintype E] [DecidableEq E]
    (enhanced : Finset E) {p p' : ℝ} (hp1 : p ≤ 1)
    (hp' : p' ∈ Icc (0 : ℝ) 1) (h : p' ≤ p)
    (Γ : E → Set (Finset E)) (e : E) :
    lowerEpsilon enhanced p p' hp' Γ e ∈ Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ enhanced
  · rw [lowerEpsilon, if_pos he]
    refine ⟨pathBonus_nonneg hp' (sub_nonneg.mpr h) _, ?_⟩
    exact (pathBonus_le hp' (sub_nonneg.mpr h) _).trans (by linarith [hp'.1])
  · simp [lowerEpsilon, he]

lemma upperEpsilon_pos {E : Type*} [Fintype E] [DecidableEq E]
    {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1)
    (h : p < p') {e : E} (he : e ∈ enhanced) :
    0 < upperEpsilon enhanced p p' hp Γ e := by
  rw [upperEpsilon, if_pos he]
  exact pathBonus_pos hp hp0 hp1 (sub_pos.mpr h) (hΓ.nonempty e he)

lemma lowerEpsilon_pos {E : Type*} [Fintype E] [DecidableEq E]
    {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ)
    {p p' : ℝ} (hp' : p' ∈ Icc (0 : ℝ) 1) (hp'0 : 0 < p') (hp'1 : p' < 1)
    (h : p' < p) {e : E} (he : e ∈ enhanced) :
    0 < lowerEpsilon enhanced p p' hp' Γ e := by
  rw [lowerEpsilon, if_pos he]
  exact pathBonus_pos hp' hp'0 hp'1 (sub_pos.mpr h) (hΓ.nonempty e he)

/-- Nondegeneracy in the deduction of Theorem 1.2 from Proposition 3.2(1).
Only the comparison inequality is an input; the displayed enhancement sizes,
their bounds, their strict positivity, and the exact product law are conclusions. -/
theorem upper_comparison_with_strict_bonus {E : Type*} [Fintype E] [DecidableEq E]
    (φ : FinProb (Config E)) {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ) (henh : enhanced.Nonempty)
    {p p' : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hp'1 : p' ≤ 1) (h : p < p')
    (hcomparison : FinProb.StochLe φ
      (productLaw (upperProductParameters enhanced p p' hp Γ)
        (upperProductParameters_mem_Icc enhanced hp hp'1 h.le Γ))) :
    ∃ ε : E → ℝ, (∀ e, ε e ∈ Icc (0 : ℝ) 1) ∧ (∃ e, 0 < ε e) ∧
      ∃ hr : ∀ e, (p' - ε e) ∈ Icc (0 : ℝ) 1,
        FinProb.StochLe φ (productLaw (fun e => p' - ε e) hr) := by
  let ε := upperEpsilon enhanced p p' hp Γ
  have hε : ∀ e, ε e ∈ Icc (0 : ℝ) 1 :=
    upperEpsilon_mem_Icc enhanced hp hp'1 h.le Γ
  have hpos : ∃ e, 0 < ε e := by
    obtain ⟨e, he⟩ := henh
    exact ⟨e, upperEpsilon_pos hΓ hp hp0 hp1 h he⟩
  have heq : (fun e => p' - ε e) = upperProductParameters enhanced p p' hp Γ :=
    (upperProductParameters_eq E enhanced p p' hp Γ).symm
  have hr : ∀ e, (p' - ε e) ∈ Icc (0 : ℝ) 1 := by
    intro e
    rw [congrFun heq e]
    exact upperProductParameters_mem_Icc enhanced hp hp'1 h.le Γ e
  refine ⟨ε, hε, hpos, hr, ?_⟩
  simpa only [heq] using hcomparison

/-- Nondegeneracy in the deduction of Theorem 1.2 from Proposition 3.2(2). -/
theorem lower_comparison_with_strict_bonus {E : Type*} [Fintype E] [DecidableEq E]
    (φ : FinProb (Config E)) {enhanced : Finset E} {Γ : E → Set (Finset E)}
    (hΓ : HasEnhancingPaths enhanced Γ) (henh : enhanced.Nonempty)
    {p p' : ℝ} (hp1 : p ≤ 1) (hp' : p' ∈ Icc (0 : ℝ) 1)
    (hp'0 : 0 < p') (hp'1 : p' < 1) (h : p' < p)
    (hcomparison : FinProb.StochLe
      (productLaw (lowerProductParameters enhanced p p' hp' Γ)
        (lowerProductParameters_mem_Icc enhanced hp1 hp' h.le Γ)) φ) :
    ∃ ε : E → ℝ, (∀ e, ε e ∈ Icc (0 : ℝ) 1) ∧ (∃ e, 0 < ε e) ∧
      ∃ hr : ∀ e, (p' + ε e) ∈ Icc (0 : ℝ) 1,
        FinProb.StochLe (productLaw (fun e => p' + ε e) hr) φ := by
  let ε := lowerEpsilon enhanced p p' hp' Γ
  have hε : ∀ e, ε e ∈ Icc (0 : ℝ) 1 :=
    lowerEpsilon_mem_Icc enhanced hp1 hp' h.le Γ
  have hpos : ∃ e, 0 < ε e := by
    obtain ⟨e, he⟩ := henh
    exact ⟨e, lowerEpsilon_pos hΓ hp' hp'0 hp'1 h he⟩
  have heq : (fun e => p' + ε e) = lowerProductParameters enhanced p p' hp' Γ :=
    (lowerProductParameters_eq E enhanced p p' hp' Γ).symm
  have hr : ∀ e, (p' + ε e) ∈ Icc (0 : ℝ) 1 := by
    intro e
    rw [congrFun heq e]
    exact lowerProductParameters_mem_Icc enhanced hp1 hp' h.le Γ e
  refine ⟨ε, hε, hpos, hr, ?_⟩
  simpa only [heq] using hcomparison

end OpenPath
