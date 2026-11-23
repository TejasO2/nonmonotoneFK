import FK.OpenPathEnhancement

/-!
# Finite heat-bath and block Glauber kernels

This file supplies the Markov-kernel part of Section 3 of
Beffara--Faipeur--Oke (arXiv:2512.16486).  A heat-bath update is described by
its exact conditional factorization, rather than by a stochastic ordering
hypothesis.  We prove invariance of a single update, sequential updates, and
clock mixtures.  No convergence theorem is assumed.
-/

noncomputable section

local instance (priority := low) glauberPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

open scoped BigOperators
open Set Filter

namespace Glauber

open OpenPath

variable {α β γ ι : Type*}

/-- A finite probability law is invariant for a finite Markov kernel. -/
def Invariant [Fintype α] (μ : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α) : Prop :=
  μ.bind κ = μ

namespace FinProb

variable [Fintype α] [Fintype β] [Fintype γ]

/-- The point mass at one configuration. -/
def dirac (a : α) : OpenPath.FinProb α where
  mass b := if b = a then 1 else 0
  mass_nonneg b := by split_ifs <;> norm_num
  sum_mass := by simp

/-- Associativity of finite probabilistic bind, at the level of laws. -/
lemma bind_assoc (μ : OpenPath.FinProb α) (κ : α → OpenPath.FinProb β)
    (η : β → OpenPath.FinProb γ) :
    (μ.bind κ).bind η = μ.bind fun a => (κ a).bind η := by
  classical
  ext c
  simp only [OpenPath.FinProb.mass_bind]
  calc
    (∑ b, (∑ a, μ.mass a * (κ a).mass b) * (η b).mass c) =
        ∑ b, ∑ a, μ.mass a * ((κ a).mass b * (η b).mass c) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc]
    _ = ∑ a, ∑ b, μ.mass a * ((κ a).mass b * (η b).mass c) := Finset.sum_comm
    _ = ∑ a, μ.mass a * ∑ b, (κ a).mass b * (η b).mass c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

end FinProb

section ProductRefresh

variable [Fintype β] [Fintype γ]

lemma sum_prod_ite_fst (b : β) (f : β × γ → ℝ) :
    (∑ x : β × γ, if x.1 = b then f x else 0) = ∑ y, f (b, y) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro b' _ hb'
    apply Finset.sum_eq_zero
    intro y _
    simp [hb']
  · simp

/-- The law on the first coordinate of a finite law on a product, without
normalization. -/
def outsideMass (μ : OpenPath.FinProb (β × γ)) (b : β) : ℝ :=
  ∑ y, μ.mass (b, y)

/-- Exact normalized conditional law of the second coordinate given the
first.  The product form also covers zero-mass first coordinates. -/
def HasProductConditional (μ : OpenPath.FinProb (β × γ))
    (c : β → OpenPath.FinProb γ) : Prop :=
  ∀ b y, μ.mass (b, y) = outsideMass μ b * (c b).mass y

/-- Refresh the second coordinate from its conditional law, leaving the first
coordinate fixed. -/
def refresh (c : β → OpenPath.FinProb γ) :
    β × γ → OpenPath.FinProb (β × γ) :=
  fun x => (c x.1).map fun y => (x.1, y)

/-- Conditional resampling preserves a finite joint law. -/
theorem refresh_invariant (μ : OpenPath.FinProb (β × γ))
    (c : β → OpenPath.FinProb γ) (hc : HasProductConditional μ c) :
    Invariant μ (refresh c) := by
  classical
  unfold Invariant
  ext ⟨b, y⟩
  calc
    (μ.bind (refresh c)).mass (b, y) =
        ∑ x : β × γ, if x.1 = b then μ.mass x * (c b).mass y else 0 := by
      simp only [OpenPath.FinProb.mass_bind]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x.1 = b
      · subst b
        simp [refresh, OpenPath.FinProb.mass_map]
      · simp [refresh, OpenPath.FinProb.mass_map, hx]
    _ = ∑ y', μ.mass (b, y') * (c b).mass y :=
      sum_prod_ite_fst b _
    _ = outsideMass μ b * (c b).mass y := by
      rw [outsideMass, Finset.sum_mul]
    _ = μ.mass (b, y) := (hc b y).symm

end ProductRefresh

section ConjugatedRefresh

variable [Fintype α] [Fintype β] [Fintype γ]

/-- Pull a coordinate refreshing kernel back along an equivalence. -/
def refreshConj (ρ : α ≃ β × γ) (c : β → OpenPath.FinProb γ) :
    α → OpenPath.FinProb α :=
  fun a => (c (ρ a).1).map fun y => ρ.symm ((ρ a).1, y)

/-- The outside-coordinate mass of a law presented in an equivalent product
representation. -/
def outsideMassConj (ρ : α ≃ β × γ) (μ : OpenPath.FinProb α) (b : β) : ℝ :=
  ∑ y, μ.mass (ρ.symm (b, y))

/-- Exact conditional factorization in an equivalent product representation. -/
def HasConjConditional (ρ : α ≃ β × γ) (μ : OpenPath.FinProb α)
    (c : β → OpenPath.FinProb γ) : Prop :=
  ∀ b y, μ.mass (ρ.symm (b, y)) = outsideMassConj ρ μ b * (c b).mass y

/-- Coordinate heat-bath updates remain invariant in the original state
space; no measurability or countability assumptions are needed. -/
theorem refreshConj_invariant (ρ : α ≃ β × γ) (μ : OpenPath.FinProb α)
    (c : β → OpenPath.FinProb γ) (hc : HasConjConditional ρ μ c) :
    Invariant μ (refreshConj ρ c) := by
  classical
  unfold Invariant
  ext z
  calc
    (μ.bind (refreshConj ρ c)).mass z =
        ∑ a, if (ρ a).1 = (ρ z).1 then
          μ.mass a * (c (ρ z).1).mass (ρ z).2 else 0 := by
      simp only [OpenPath.FinProb.mass_bind]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (ρ a).1 = (ρ z).1
      · have hmass : (∑ y, if ρ.symm ((ρ a).1, y) = z then
            (c (ρ a).1).mass y else 0) = (c (ρ a).1).mass (ρ z).2 := by
          rw [Finset.sum_eq_single (ρ z).2]
          · simp [ha]
          · intro y _ hy
            have hne : ρ.symm ((ρ a).1, y) ≠ z := by
              intro h
              have h' := congrArg ρ h
              simp [ha] at h'
              exact hy (congrArg Prod.snd h')
            simp [hne]
          · simp
        simp only [ha, ↓reduceIte]
        simp only [refreshConj, OpenPath.FinProb.mass_map]
        rw [hmass, ← ha]
      · simp only [ha, ↓reduceIte]
        simp only [refreshConj, OpenPath.FinProb.mass_map]
        apply (mul_eq_zero.mpr (Or.inr ?_))
        apply Finset.sum_eq_zero
        intro y _
        have hne : ρ.symm ((ρ a).1, y) ≠ z := by
          intro h
          have h' := congrArg ρ h
          have hp : ((ρ a).1, y) = ((ρ z).1, (ρ z).2) := by simpa using h'
          exact ha (Prod.ext_iff.mp hp).1
        simp [hne]
    _ = ∑ x : β × γ, if x.1 = (ρ z).1 then
          μ.mass (ρ.symm x) * (c (ρ z).1).mass (ρ z).2 else 0 := by
      simpa using Equiv.sum_comp ρ (fun x : β × γ =>
        if x.1 = (ρ z).1 then μ.mass (ρ.symm x) * (c (ρ z).1).mass (ρ z).2 else 0)
    _ = ∑ y, μ.mass (ρ.symm ((ρ z).1, y)) * (c (ρ z).1).mass (ρ z).2 :=
      sum_prod_ite_fst (ρ z).1 _
    _ = outsideMassConj ρ μ (ρ z).1 * (c (ρ z).1).mass (ρ z).2 := by
      rw [outsideMassConj, Finset.sum_mul]
    _ = μ.mass (ρ.symm (ρ z)) := (hc (ρ z).1 (ρ z).2).symm
    _ = μ.mass z := by rw [ρ.symm_apply_apply]

end ConjugatedRefresh

section Composition

variable [Fintype α]

/-- Sequential composition of finite kernels, in chronological order. -/
def seq (κ η : α → OpenPath.FinProb α) : α → OpenPath.FinProb α :=
  fun a => (κ a).bind η

lemma invariant_seq {μ : OpenPath.FinProb α} {κ η : α → OpenPath.FinProb α}
    (hκ : Invariant μ κ) (hη : Invariant μ η) : Invariant μ (seq κ η) := by
  unfold Invariant seq
  rw [← FinProb.bind_assoc, hκ, hη]

/-- Update each coordinate in a list, in list order. -/
def sweep : List (α → OpenPath.FinProb α) → α → OpenPath.FinProb α
  | [] => fun a => FinProb.dirac a
  | κ :: l => seq κ (sweep l)

lemma invariant_sweep {μ : OpenPath.FinProb α} :
    ∀ l : List (α → OpenPath.FinProb α),
      (∀ κ ∈ l, Invariant μ κ) → Invariant μ (sweep l) := by
  intro l
  induction l with
  | nil =>
      intro _
      unfold Invariant sweep
      ext a
      simp [FinProb.dirac, OpenPath.FinProb.mass_bind]
  | cons κ l ih =>
      intro h
      exact invariant_seq (h κ (by simp))
        (ih fun η hη => h η (by simp [hη]))

end Composition

section ClockMixture

variable [Fintype α] [Fintype ι]

/-- Mix update kernels according to an independent finite clock law. -/
def mixture (ρ : OpenPath.FinProb ι) (κ : ι → α → OpenPath.FinProb α) :
    α → OpenPath.FinProb α :=
  fun a => ρ.bind fun i => κ i a

/-- A clock mixture of invariant updates is invariant. -/
theorem mixture_invariant (μ : OpenPath.FinProb α) (ρ : OpenPath.FinProb ι)
    (κ : ι → α → OpenPath.FinProb α) (hκ : ∀ i, Invariant μ (κ i)) :
    Invariant μ (mixture ρ κ) := by
  classical
  unfold Invariant mixture
  ext b
  calc
    (μ.bind (fun a => ρ.bind fun i => κ i a)).mass b =
        ∑ i, ρ.mass i * ∑ a, μ.mass a * (κ i a).mass b := by
      simp only [OpenPath.FinProb.mass_bind]
      calc
        (∑ a, μ.mass a * ∑ i, ρ.mass i * (κ i a).mass b) =
            ∑ a, ∑ i, μ.mass a * (ρ.mass i * (κ i a).mass b) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
        _ = ∑ i, ∑ a, μ.mass a * (ρ.mass i * (κ i a).mass b) := Finset.sum_comm
        _ = ∑ i, ρ.mass i * ∑ a, μ.mass a * (κ i a).mass b := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ i, ρ.mass i * μ.mass b := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := congrArg (fun ν : OpenPath.FinProb α => ν.mass b) (hκ i)
      exact congrArg (fun x => ρ.mass i * x) hi
    _ = μ.mass b := by
      rw [← Finset.sum_mul, ρ.sum_mass, one_mul]

end ClockMixture

end Glauber


namespace Glauber

section Configurations

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-- The coordinates other than one edge. -/
abbrev OffConfig (B E : Type*) [DecidableEq E] (e : E) :=
  {f : E // f ≠ e} → B

/-- Split a bit configuration into an off-edge configuration and the bit at
that edge. -/
def configSplit (B : Type*) (e : E) : (E → B) ≃ OffConfig B E e × B :=
  (Equiv.funSplitAt e B).trans (Equiv.prodComm _ _)

@[simp] lemma configSplit_apply_fst (e : E) (ω : E → B) :
    (configSplit B e ω).1 = (fun f => ω f.1) := rfl

@[simp] lemma configSplit_apply_snd (e : E) (ω : E → B) :
    (configSplit B e ω).2 = ω e := rfl

/-- Recombining the off-edge part of `ω` with a new bit is precisely
`Function.update` at the edge. -/
lemma configSplit_symm_update (e : E) (ω : E → B) (b : B) :
    (configSplit B e).symm ((configSplit B e ω).1, b) = Function.update ω e b := by
  ext f
  by_cases hf : f = e
  · subst f
    simp [configSplit, Equiv.funSplitAt_symm_apply]
  · simp [configSplit, Equiv.funSplitAt_symm_apply, hf, Function.update_of_ne]

/-- A family of exact conditional laws, one for each off-edge configuration. -/
abbrev EdgeConditionals (B E : Type*) [Fintype E] [DecidableEq E] [Fintype B] :=
  ∀ e : E, OffConfig B E e → OpenPath.FinProb B

/-- The Section 3 heat-bath update of one edge. -/
def edgeUpdate (c : EdgeConditionals B E) (e : E) :
    (E → B) → OpenPath.FinProb (E → B) :=
  refreshConj (configSplit B e) (c e)

/-- This update only changes `e`, and draws its new bit from the supplied
conditional law of the off-edge configuration. -/
lemma edgeUpdate_eq_map (c : EdgeConditionals B E) (e : E) (ω : E → B) :
    edgeUpdate c e ω = (c e (fun f => ω f.1)).map (Function.update ω e) := by
  unfold edgeUpdate refreshConj
  simp only [configSplit_apply_fst]
  congr 1

/-- Exact singleton conditional law of a configuration law, expressed by a
product factorization on the off-edge fibers. -/
def HasEdgeConditional (μ : OpenPath.FinProb (E → B))
    (c : EdgeConditionals B E) (e : E) : Prop :=
  HasConjConditional (configSplit B e) μ (c e)

/-- A configuration law with its singleton conditional law is invariant under
that edge's heat-bath update. -/
theorem edgeUpdate_invariant (μ : OpenPath.FinProb (E → B))
    (c : EdgeConditionals B E) {e : E} (he : HasEdgeConditional μ c e) :
    Invariant μ (edgeUpdate c e) :=
  refreshConj_invariant (configSplit B e) μ (c e) he

/-- `auxiliary` is a duplicate-free enumeration of precisely the edges outside
`enhanced`, as in the modified dynamics of Propositions 3.1 and 3.2. -/
def IsAuxiliaryEnumeration (enhanced : Finset E) (auxiliary : List E) : Prop :=
  auxiliary.Nodup ∧ ∀ f, f ∈ auxiliary ↔ f ∉ enhanced

/-- The coordinates refreshed after the clock at `e` rings. -/
def blockCoordinates (enhanced : Finset E) (auxiliary : List E) (e : E) : List E :=
  if e ∈ enhanced then e :: auxiliary else [e]

/-- One jump of the modified block dynamics.  At an enhanced edge, the edge is
updated first and then every auxiliary edge is refreshed sequentially in the
listed order.  At any other edge, only that edge is updated. -/
def blockUpdate (c : EdgeConditionals B E) (enhanced : Finset E)
    (auxiliary : List E) (e : E) : (E → B) → OpenPath.FinProb (E → B) :=
  sweep (List.map (edgeUpdate c) (blockCoordinates enhanced auxiliary e))

/-- Every block consists of invariant updates, so it preserves the FK law once
its singleton conditional laws are supplied. -/
theorem blockUpdate_invariant (μ : OpenPath.FinProb (E → B))
    (c : EdgeConditionals B E) (hc : ∀ e, HasEdgeConditional μ c e)
    (enhanced : Finset E) (auxiliary : List E) (e : E) :
    Invariant μ (blockUpdate c enhanced auxiliary e) := by
  apply invariant_sweep
  intro κ hκ
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hκ
  exact edgeUpdate_invariant μ c (hc f)

/-- The discrete jump chain associated with independent edge clocks.  The clock
law may be nonuniform; the uniform choice is simply a particular input. -/
def modifiedJump (ρ : OpenPath.FinProb E) (c : EdgeConditionals B E)
    (enhanced : Finset E) (auxiliary : List E) :
    (E → B) → OpenPath.FinProb (E → B) :=
  mixture ρ (blockUpdate c enhanced auxiliary)

/-- FK invariance of the modified block Glauber jump chain. -/
theorem modifiedJump_invariant (μ : OpenPath.FinProb (E → B))
    (ρ : OpenPath.FinProb E) (c : EdgeConditionals B E)
    (hc : ∀ e, HasEdgeConditional μ c e) (enhanced : Finset E) (auxiliary : List E) :
    Invariant μ (modifiedJump ρ c enhanced auxiliary) := by
  apply mixture_invariant
  intro e
  exact blockUpdate_invariant μ c hc enhanced auxiliary e

end Configurations

end Glauber


namespace Glauber

section PMFBridge

variable {α : Type*} [Fintype α]

/-- Regard a `PMF` on a finite type as the real-mass probability law used by
`OpenPath.FinProb`. -/
noncomputable def ofPMF (μ : PMF α) : OpenPath.FinProb α where
  mass a := (μ a).toReal
  mass_nonneg _ := ENNReal.toReal_nonneg
  sum_mass := by
    classical
    calc
      (∑ a, (μ a).toReal) = (∑ a, μ a).toReal :=
        (ENNReal.toReal_sum (fun a _ => μ.apply_ne_top a)).symm
      _ = (∑' a, μ a).toReal := by rw [tsum_fintype]
      _ = 1 := by rw [μ.tsum_coe, ENNReal.toReal_one]

@[simp] lemma ofPMF_mass (μ : PMF α) (a : α) :
    (ofPMF μ).mass a = (μ a).toReal := rfl

end PMFBridge

namespace FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

@[simp] lemma bind_dirac (a : α) (κ : α → OpenPath.FinProb β) :
    (dirac a).bind κ = κ a := by
  classical
  ext b
  simp [OpenPath.FinProb.mass_bind, dirac]

lemma exists_mass_pos (μ : OpenPath.FinProb α) : ∃ a, 0 < μ.mass a := by
  classical
  by_contra h
  push Not at h
  have hz : ∀ a, μ.mass a = 0 := fun a => le_antisymm (h a) (μ.mass_nonneg a)
  have hs := μ.sum_mass
  simp [hz] at hs

lemma bind_mass_pos {μ : OpenPath.FinProb α} {κ : α → OpenPath.FinProb β}
    (a : α) (ha : 0 < μ.mass a) {b : β} (hb : 0 < (κ a).mass b) :
    0 < (μ.bind κ).mass b := by
  rw [OpenPath.FinProb.mass_bind]
  apply Finset.sum_pos'
  · intro x _
    exact mul_nonneg (μ.mass_nonneg x) ((κ x).mass_nonneg b)
  · exact ⟨a, Finset.mem_univ a, mul_pos ha hb⟩

end FinProb

section KernelIteration

variable {α ι : Type*} [Fintype α]

/-- The kernel of the discrete chain after `n` jumps.  The recursive equation
uses the first jump followed by `n` further jumps. -/
def iterate (κ : α → OpenPath.FinProb α) : ℕ → α → OpenPath.FinProb α
  | 0 => fun a => FinProb.dirac a
  | n + 1 => seq κ (iterate κ n)

@[simp] lemma iterate_zero (κ : α → OpenPath.FinProb α) :
    iterate κ 0 = fun a => FinProb.dirac a := rfl

@[simp] lemma iterate_succ (κ : α → OpenPath.FinProb α) (n : ℕ) :
    iterate κ (n + 1) = seq κ (iterate κ n) := rfl

lemma iterate_invariant {μ : OpenPath.FinProb α} {κ : α → OpenPath.FinProb α}
    (hκ : Invariant μ κ) (n : ℕ) : Invariant μ (iterate κ n) := by
  induction n with
  | zero =>
      unfold Invariant
      ext a
      simp [OpenPath.FinProb.mass_bind, FinProb.dirac]
  | succ n ih => exact invariant_seq hκ ih

lemma seq_assoc (κ η ξ : α → OpenPath.FinProb α) :
    seq (seq κ η) ξ = seq κ (seq η ξ) := by
  funext a
  change ((κ a).bind η).bind ξ = (κ a).bind (fun x => (η x).bind ξ)
  exact FinProb.bind_assoc (κ a) η ξ

lemma sweep_append (l₁ l₂ : List (α → OpenPath.FinProb α)) :
    sweep (l₁ ++ l₂) = seq (sweep l₁) (sweep l₂) := by
  induction l₁ with
  | nil =>
      ext a b
      simp [sweep, seq, OpenPath.FinProb.mass_bind, FinProb.dirac]
  | cons κ l ih =>
      simp only [List.cons_append, sweep]
      rw [ih, seq_assoc]

lemma sweep_flatMap {F : ι → List (α → OpenPath.FinProb α)} (l : List ι) :
    sweep (List.flatMap F l) = sweep (l.map fun i => sweep (F i)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      change sweep (F i ++ List.flatMap F l) =
        seq (sweep (F i)) (sweep (List.map (fun i => sweep (F i)) l))
      rw [sweep_append, ih]

/-- A schedule of conditional clock choices has positive probability of
producing its deterministic target trajectory whenever every individual
transition on that trajectory is positive. -/
lemma iterate_mixture_pos_of_sweep [Fintype ι] (ρ : OpenPath.FinProb ι)
    (hρ : ∀ i, 0 < ρ.mass i) (κ : ι → α → OpenPath.FinProb α) :
    ∀ (l : List ι) (a b : α),
      0 < ((FinProb.dirac a).bind (sweep (l.map κ))).mass b →
      0 < ((FinProb.dirac a).bind (iterate (mixture ρ κ) l.length)).mass b := by
  intro l
  induction l with
  | nil =>
      intro a b h
      exact h
  | cons i l ih =>
      intro a b h
      simp only [List.map_cons, sweep] at h
      unfold seq at h
      rw [← FinProb.bind_assoc, OpenPath.FinProb.mass_bind] at h
      have hnonneg : ∀ x ∈ Finset.univ,
          0 ≤ ((FinProb.dirac a).bind (κ i)).mass x *
            (sweep (l.map κ) x).mass b := by
        intro x _
        exact mul_nonneg (((FinProb.dirac a).bind (κ i)).mass_nonneg x)
          ((sweep (l.map κ) x).mass_nonneg b)
      obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg hnonneg).1 h
      rw [FinProb.bind_dirac] at hx
      have hax : 0 < (κ i a).mass x :=
        pos_of_mul_pos_left hx ((sweep (l.map κ) x).mass_nonneg b)
      have hxb : 0 < (sweep (l.map κ) x).mass b :=
        pos_of_mul_pos_right hx ((κ i a).mass_nonneg x)
      rw [List.length_cons, iterate_succ]
      unfold seq
      rw [← FinProb.bind_assoc]
      apply FinProb.bind_mass_pos x
      · rw [FinProb.bind_dirac]
        exact FinProb.bind_mass_pos i (hρ i) hax
      · have hi := ih x b (by simpa using hxb)
        simpa using hi

end KernelIteration

end Glauber


namespace Glauber

section ConfigurationReachability

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

@[simp] lemma edgeUpdate_update_mass (c : EdgeConditionals B E) (e : E)
    (ω : E → B) (b : B) :
    (edgeUpdate c e ω).mass (Function.update ω e b) = (c e (fun f => ω f.1)).mass b := by
  classical
  rw [edgeUpdate_eq_map, OpenPath.FinProb.mass_map, Finset.sum_eq_single b]
  · simp
  · intro a _ ha
    have hne : Function.update ω e a ≠ Function.update ω e b := by
      intro h
      apply ha
      have h' := congrArg (fun ξ : E → B => ξ e) h
      simpa using h'
    simp [hne]
  · simp

/-- Apply the bits of `η` successively at the listed coordinates. -/
def forceBits (ω η : E → B) : List E → (E → B)
  | [] => ω
  | e :: l => forceBits (Function.update ω e (η e)) η l

@[simp] lemma forceBits_nil (ω η : E → B) : forceBits ω η [] = ω := rfl

lemma forceBits_cons (ω η : E → B) (e : E) (l : List E) :
    forceBits ω η (e :: l) = forceBits (Function.update ω e (η e)) η l := rfl

lemma forceBits_apply (l : List E) (ω η : E → B) (f : E) :
    forceBits ω η l f = if f ∈ l then η f else ω f := by
  induction l generalizing ω with
  | nil => simp [forceBits]
  | cons e l ih =>
      rw [forceBits_cons, ih]
      by_cases hfl : f ∈ l
      · simp [hfl]
      · by_cases hfe : f = e
        · subst f
          simp [hfl]
        · simp [hfl, hfe, Function.update_of_ne]

lemma forceBits_eq_of_forall_mem {l : List E} (hl : ∀ f, f ∈ l) (ω η : E → B) :
    forceBits ω η l = η := by
  ext f
  simp only [forceBits_apply, hl f, ↓reduceIte]

/-- Every list of single-coordinate heat-bath updates has positive probability
of following its prescribed bit trajectory when all conditional bits are
positive. -/
lemma sweep_edgeUpdate_forceBits_pos (c : EdgeConditionals B E)
    (hc : ∀ e off b, 0 < (c e off).mass b) :
    ∀ (l : List E) (ω η : E → B),
      0 < ((FinProb.dirac ω).bind
        (sweep (l.map (edgeUpdate c)))).mass (forceBits ω η l) := by
  intro l
  induction l with
  | nil =>
      intro ω η
      simp [sweep, forceBits, OpenPath.FinProb.mass_bind, FinProb.dirac]
  | cons e l ih =>
      intro ω η
      simp only [List.map_cons, sweep]
      unfold seq
      rw [← FinProb.bind_assoc]
      apply FinProb.bind_mass_pos (Function.update ω e (η e))
      · rw [FinProb.bind_dirac, edgeUpdate_update_mass]
        exact hc e _ _
      · have hi := ih (Function.update ω e (η e)) η
        simpa only [FinProb.bind_dirac, forceBits_cons] using hi

/-- The individual coordinates updated by a full schedule of modified blocks. -/
def expandedSchedule (enhanced : Finset E) (auxiliary : List E) (schedule : List E) : List E :=
  schedule.flatMap (blockCoordinates enhanced auxiliary)

lemma mem_blockCoordinates_self (enhanced : Finset E) (auxiliary : List E) (e : E) :
    e ∈ blockCoordinates enhanced auxiliary e := by
  by_cases he : e ∈ enhanced <;> simp [blockCoordinates, he]

lemma mem_expandedSchedule_of_mem {enhanced : Finset E} {auxiliary : List E}
    {schedule : List E} {e : E} (he : e ∈ schedule) :
    e ∈ expandedSchedule enhanced auxiliary schedule := by
  apply List.mem_flatMap.mpr
  exact ⟨e, he, mem_blockCoordinates_self enhanced auxiliary e⟩

lemma forceBits_expandedSchedule {enhanced : Finset E} {auxiliary : List E}
    {schedule : List E} (hschedule : ∀ e, e ∈ schedule) (ω η : E → B) :
    forceBits ω η (expandedSchedule enhanced auxiliary schedule) = η :=
  forceBits_eq_of_forall_mem
    (fun e => mem_expandedSchedule_of_mem (enhanced := enhanced) (hschedule e)) ω η

lemma sweep_blockUpdate_eq_expanded (c : EdgeConditionals B E)
    (enhanced : Finset E) (auxiliary : List E) (schedule : List E) :
    sweep (schedule.map (blockUpdate c enhanced auxiliary)) =
      sweep ((expandedSchedule enhanced auxiliary schedule).map (edgeUpdate c)) := by
  unfold blockUpdate expandedSchedule
  rw [List.map_flatMap]
  exact (sweep_flatMap
    (F := fun e => List.map (edgeUpdate c) (blockCoordinates enhanced auxiliary e)) schedule).symm

/-- **Irreducibility in exact finite-time form.**  A full clock schedule makes
every target configuration reachable with positive probability.  In
particular the modified jump chain is irreducible whenever all edge clocks and
all singleton conditional bits are positive. -/
theorem modifiedJump_iterate_pos (c : EdgeConditionals B E)
    (hc : ∀ e off b, 0 < (c e off).mass b) (ρ : OpenPath.FinProb E)
    (hρ : ∀ e, 0 < ρ.mass e) (enhanced : Finset E) (auxiliary : List E)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) (ω η : E → B) :
    0 < ((FinProb.dirac ω).bind
      (iterate (modifiedJump ρ c enhanced auxiliary) schedule.length)).mass η := by
  apply iterate_mixture_pos_of_sweep ρ hρ
    (blockUpdate c enhanced auxiliary) schedule ω η
  rw [sweep_blockUpdate_eq_expanded,
    ← forceBits_expandedSchedule (enhanced := enhanced) hschedule ω η]
  exact sweep_edgeUpdate_forceBits_pos c hc _ ω η

/-- A finite kernel is irreducible when each target has positive probability at
some finite time from every source. -/
def Irreducible {α : Type*} [Fintype α] (κ : α → OpenPath.FinProb α) : Prop :=
  ∀ a b, ∃ n, 0 < (iterate κ n a).mass b

theorem modifiedJump_irreducible (c : EdgeConditionals B E)
    (hc : ∀ e off b, 0 < (c e off).mass b) (ρ : OpenPath.FinProb E)
    (hρ : ∀ e, 0 < ρ.mass e) (enhanced : Finset E) (auxiliary : List E)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    Irreducible (modifiedJump ρ c enhanced auxiliary) := by
  intro ω η
  refine ⟨schedule.length, ?_⟩
  simpa using modifiedJump_iterate_pos c hc ρ hρ enhanced auxiliary schedule hschedule ω η

end ConfigurationReachability

end Glauber


namespace Glauber

section Aperiodicity

variable {α E B : Type*} [Fintype α] [Fintype E] [DecidableEq E] [Fintype B]

/-- A positive transition at both `n` and `n+1`, a strong finite-state
aperiodicity certificate. -/
def StronglyAperiodic (κ : α → OpenPath.FinProb α) : Prop :=
  ∃ n, (∀ a b, 0 < (iterate κ n a).mass b) ∧
    (∀ a b, 0 < (iterate κ (n + 1) a).mass b)

lemma iterate_succ_pos_of_forall_pos (κ : α → OpenPath.FinProb α) {n : ℕ}
    (hn : ∀ a b, 0 < (iterate κ n a).mass b) (a b : α) :
    0 < (iterate κ (n + 1) a).mass b := by
  obtain ⟨x, hx⟩ := FinProb.exists_mass_pos (κ a)
  change 0 < ((κ a).bind (iterate κ n)).mass b
  exact FinProb.bind_mass_pos x hx (hn x b)

theorem modifiedJump_stronglyAperiodic (c : EdgeConditionals B E)
    (hc : ∀ e off b, 0 < (c e off).mass b) (ρ : OpenPath.FinProb E)
    (hρ : ∀ e, 0 < ρ.mass e) (enhanced : Finset E) (auxiliary : List E)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    StronglyAperiodic (modifiedJump ρ c enhanced auxiliary) := by
  have hn : ∀ ω η, 0 < (iterate (modifiedJump ρ c enhanced auxiliary)
      schedule.length ω).mass η := by
    intro ω η
    simpa using modifiedJump_iterate_pos c hc ρ hρ enhanced auxiliary schedule hschedule ω η
  exact ⟨schedule.length, hn,
    fun ω η => iterate_succ_pos_of_forall_pos _ hn ω η⟩

end Aperiodicity

end Glauber


namespace Glauber

section VariationContraction

variable {α : Type*} [Fintype α]

/-- Unnormalized total-variation distance between finite real-mass laws. -/
def variation (μ ν : OpenPath.FinProb α) : ℝ :=
  ∑ a, |μ.mass a - ν.mass a|

lemma variation_nonneg (μ ν : OpenPath.FinProb α) : 0 ≤ variation μ ν := by
  unfold variation
  exact Finset.sum_nonneg fun a _ => abs_nonneg _

lemma variation_le_two (μ ν : OpenPath.FinProb α) : variation μ ν ≤ 2 := by
  unfold variation
  calc
    (∑ a, |μ.mass a - ν.mass a|) ≤ ∑ a, (μ.mass a + ν.mass a) := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_sub_le_iff]
      constructor <;> linarith [μ.mass_nonneg a, ν.mass_nonneg a]
    _ = 2 := by rw [Finset.sum_add_distrib, μ.sum_mass, ν.sum_mass]; norm_num

@[simp] lemma variation_self (μ : OpenPath.FinProb α) : variation μ μ = 0 := by
  simp [variation]

namespace FinProb

lemma bind_dirac_right (μ : OpenPath.FinProb α) :
    μ.bind (fun a => dirac a) = μ := by
  classical
  ext b
  simp [OpenPath.FinProb.mass_bind, dirac]

end FinProb

lemma bind_sub_mass (μ ν : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (δ : ℝ) (b : α) :
    (μ.bind κ).mass b - (ν.bind κ).mass b =
      ∑ a, (μ.mass a - ν.mass a) * ((κ a).mass b - δ) := by
  have hzero : ∑ a, (μ.mass a - ν.mass a) * δ = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, μ.sum_mass, ν.sum_mass]
    ring
  simp only [OpenPath.FinProb.mass_bind, ← Finset.sum_sub_distrib]
  calc
    (∑ a, (μ.mass a * (κ a).mass b - ν.mass a * (κ a).mass b)) =
        ∑ a, (μ.mass a - ν.mass a) * (κ a).mass b := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a, (μ.mass a - ν.mass a) * ((κ a).mass b - δ)) +
        ∑ a, (μ.mass a - ν.mass a) * δ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hzero, add_zero]

/-- Doeblin contraction for a kernel whose entries have a common lower bound. -/
lemma variation_bind_le (μ ν : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (δ : ℝ) (hδ : ∀ a b, δ ≤ (κ a).mass b) :
    variation (μ.bind κ) (ν.bind κ) ≤
      (1 - (Fintype.card α : ℝ) * δ) * variation μ ν := by
  classical
  have hrow (a : α) : ∑ b, ((κ a).mass b - δ) =
      1 - (Fintype.card α : ℝ) * δ := by
    rw [Finset.sum_sub_distrib, (κ a).sum_mass]
    simp [nsmul_eq_mul]
  have hres (a b : α) : 0 ≤ (κ a).mass b - δ := sub_nonneg.mpr (hδ a b)
  unfold variation
  calc
    (∑ b, |(μ.bind κ).mass b - (ν.bind κ).mass b|) =
        ∑ b, |∑ a, (μ.mass a - ν.mass a) * ((κ a).mass b - δ)| := by
      apply Finset.sum_congr rfl
      intro b _
      rw [bind_sub_mass]
    _ ≤ ∑ b, ∑ a, |(μ.mass a - ν.mass a) * ((κ a).mass b - δ)| := by
      apply Finset.sum_le_sum
      intro b _
      simpa using Finset.abs_sum_le_sum_abs
        (fun a => (μ.mass a - ν.mass a) * ((κ a).mass b - δ)) Finset.univ
    _ = ∑ a, |μ.mass a - ν.mass a| * (1 - (Fintype.card α : ℝ) * δ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [abs_mul, abs_of_nonneg (hres a _)]
      rw [← Finset.mul_sum, hrow]
    _ = (1 - (Fintype.card α : ℝ) * δ) * ∑ a, |μ.mass a - ν.mass a| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _

lemma variation_bind_iterate_le (μ ν : OpenPath.FinProb α)
    (κ : α → OpenPath.FinProb α) (δ : ℝ) (hδ : ∀ a b, δ ≤ (κ a).mass b)
    (hs : 0 ≤ 1 - (Fintype.card α : ℝ) * δ) :
    ∀ r : ℕ, variation (μ.bind (iterate κ r)) (ν.bind (iterate κ r)) ≤
      (1 - (Fintype.card α : ℝ) * δ) ^ r * variation μ ν := by
  intro r
  induction r generalizing μ ν with
  | zero => simp [FinProb.bind_dirac_right]
  | succ r ih =>
      let s : ℝ := 1 - (Fintype.card α : ℝ) * δ
      have hstep := variation_bind_le μ ν κ δ hδ
      calc
        variation (μ.bind (iterate κ (r + 1))) (ν.bind (iterate κ (r + 1))) =
            variation ((μ.bind κ).bind (iterate κ r)) ((ν.bind κ).bind (iterate κ r)) := by
          rw [iterate_succ]
          unfold seq
          rw [FinProb.bind_assoc, FinProb.bind_assoc]
        _ ≤ s ^ r * variation (μ.bind κ) (ν.bind κ) := ih (μ.bind κ) (ν.bind κ)
        _ ≤ s ^ r * (s * variation μ ν) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hs r)
        _ = s ^ (r + 1) * variation μ ν := by rw [pow_succ]; ring

/-- Pointwise distributional convergence for a finite kernel with a positive
Doeblin minorization and the specified invariant law. -/
theorem tendsto_bind_iterate_of_invariant [Nonempty α]
    (μ π : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (hπ : Invariant π κ) (δ : ℝ) (hδ : ∀ a b, δ ≤ (κ a).mass b)
    (hs0 : 0 ≤ 1 - (Fintype.card α : ℝ) * δ)
    (hs1 : 1 - (Fintype.card α : ℝ) * δ < 1) :
    OpenPath.FinProb.LawTendsto Filter.atTop (fun r => μ.bind (iterate κ r)) π := by
  let s : ℝ := 1 - (Fintype.card α : ℝ) * δ
  intro b
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  change Filter.Tendsto (fun r => |(μ.bind (iterate κ r)).mass b - π.mass b|)
    Filter.atTop (nhds 0)
  apply squeeze_zero (fun r => abs_nonneg _)
    (g := fun r => s ^ r * variation μ π)
  · intro r
    have hv := variation_bind_iterate_le μ π κ δ hδ hs0 r
    have hπr : π.bind (iterate κ r) = π := iterate_invariant hπ r
    rw [hπr] at hv
    exact (Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => abs_nonneg _)
      (Finset.mem_univ b)).trans hv
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).mul_const (variation μ π)

end VariationContraction

end Glauber


namespace Glauber

section PositivePowerConvergence

variable {α : Type*} [Fintype α]

lemma iterate_add (κ : α → OpenPath.FinProb α) (m n : ℕ) :
    iterate κ (m + n) = seq (iterate κ m) (iterate κ n) := by
  induction m generalizing n with
  | zero =>
      ext a b
      simp [seq, OpenPath.FinProb.mass_bind, FinProb.dirac]
  | succ m ih =>
      rw [Nat.succ_add, iterate_succ, ih, iterate_succ, ← seq_assoc]

lemma bind_iterate_add (μ : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (m n : ℕ) :
    μ.bind (iterate κ (m + n)) = (μ.bind (iterate κ m)).bind (iterate κ n) := by
  rw [iterate_add]
  unfold seq
  rw [FinProb.bind_assoc]

lemma iterate_seq_comm (κ : α → OpenPath.FinProb α) (m n : ℕ) :
    seq (iterate κ m) (iterate κ n) = seq (iterate κ n) (iterate κ m) := by
  rw [← iterate_add, ← iterate_add, Nat.add_comm]

lemma iterate_mul (κ : α → OpenPath.FinProb α) (N r : ℕ) :
    iterate κ (N * r) = iterate (iterate κ N) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Nat.mul_succ, iterate_add, ih, iterate_succ, ← ih]
      exact iterate_seq_comm κ (N * r) N

/-- Choose a positive Doeblin lower bound for a strictly positive finite
kernel.  Halving its least entry also makes the contraction factor less than
one. -/
lemma exists_doeblin_delta [Nonempty α] (κ : α → OpenPath.FinProb α)
    (hκ : ∀ a b, 0 < (κ a).mass b) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ a b, δ ≤ (κ a).mass b) ∧
      0 ≤ 1 - (Fintype.card α : ℝ) * δ ∧
      1 - (Fintype.card α : ℝ) * δ < 1 := by
  classical
  let m : ℝ := Finset.inf' (Finset.univ : Finset (α × α)) Finset.univ_nonempty
    (fun p => (κ p.1).mass p.2)
  have hmpos : 0 < m := by
    apply Finset.inf'_mem (Set.Ioi (0 : ℝ))
      (fun a ha b hb => by
        change 0 < min a b
        exact lt_min ha hb) Finset.univ Finset.univ_nonempty
    intro p _
    exact hκ p.1 p.2
  have hm (a b : α) : m ≤ (κ a).mass b :=
    Finset.inf'_le (fun p : α × α => (κ p.1).mass p.2) (Finset.mem_univ (a, b))
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hcard : (Fintype.card α : ℝ) * m ≤ 1 := by
    calc
      (Fintype.card α : ℝ) * m = ∑ _b : α, m := by simp [nsmul_eq_mul]
      _ ≤ ∑ b, (κ a₀).mass b := by
        apply Finset.sum_le_sum
        intro b _
        exact hm a₀ b
      _ = 1 := (κ a₀).sum_mass
  have hcardpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine ⟨m / 2, by positivity, ?_, ?_, ?_⟩
  · intro a b
    exact (by linarith [hm a b] : m / 2 ≤ (κ a).mass b)
  · nlinarith
  · nlinarith

/-- A strictly positive `N`-step kernel suffices for pointwise convergence of
the original chain to any invariant law. -/
theorem tendsto_bind_iterate_of_positive_power [Nonempty α]
    (μ π : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (hπ : Invariant π κ) {N : ℕ} (hN : 0 < N)
    (hpos : ∀ a b, 0 < (iterate κ N a).mass b) :
    OpenPath.FinProb.LawTendsto Filter.atTop (fun n => μ.bind (iterate κ n)) π := by
  let R : α → OpenPath.FinProb α := iterate κ N
  obtain ⟨δ, hδpos, hδ, hs0, hs1⟩ := exists_doeblin_delta R hpos
  let s : ℝ := 1 - (Fintype.card α : ℝ) * δ
  have hπR : Invariant π R := iterate_invariant hπ N
  intro b
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  change Filter.Tendsto (fun n => |(μ.bind (iterate κ n)).mass b - π.mass b|)
    Filter.atTop (nhds 0)
  have hdiv : Filter.Tendsto (fun n => n / N) Filter.atTop Filter.atTop :=
    Nat.tendsto_div_const_atTop (Nat.ne_of_gt hN)
  have hgeo : Filter.Tendsto (fun n => s ^ (n / N) * 2) Filter.atTop (nhds 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).comp hdiv
    simpa using hp.mul_const 2
  apply squeeze_zero (fun n => abs_nonneg _) (g := fun n => s ^ (n / N) * 2) _ hgeo
  intro n
  let k := n % N
  let r := n / N
  let μk : OpenPath.FinProb α := μ.bind (iterate κ k)
  have hlaw : μ.bind (iterate κ n) = μk.bind (iterate R r) := by
    change μ.bind (iterate κ n) = (μ.bind (iterate κ k)).bind (iterate (iterate κ N) r)
    rw [← Nat.mod_add_div n N]
    change μ.bind (iterate κ (k + N * r)) = _
    rw [bind_iterate_add, iterate_mul]
  have hv := variation_bind_iterate_le μk π R δ hδ hs0 r
  have hπr : π.bind (iterate R r) = π := iterate_invariant hπR r
  rw [hπr, ← hlaw] at hv
  calc
    |(μ.bind (iterate κ n)).mass b - π.mass b| ≤ variation (μ.bind (iterate κ n)) π := by
      unfold variation
      exact Finset.single_le_sum
        (f := fun a : α => |(μ.bind (iterate κ n)).mass a - π.mass a|)
        (fun a (_ : a ∈ Finset.univ) => abs_nonneg _) (Finset.mem_univ b)
    _ ≤ s ^ r * variation μk π := hv
    _ ≤ s ^ r * 2 := mul_le_mul_of_nonneg_left (variation_le_two μk π) (pow_nonneg hs0 r)
    _ = s ^ (n / N) * 2 := rfl

end PositivePowerConvergence

end Glauber


namespace Glauber

section ModifiedJumpConvergence

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]
  [Nonempty E] [Nonempty B]

/-- **Convergence of the modified block Glauber jump chain.**  Under positive
edge clocks and positive singleton conditional bits, every initial finite law
converges pointwise in mass to the law determined by the exact conditional
factorizations. -/
theorem modifiedJump_tendsto (μ π : OpenPath.FinProb (E → B))
    (ρ : OpenPath.FinProb E) (c : EdgeConditionals B E)
    (hc : ∀ e, HasEdgeConditional π c e)
    (hcpos : ∀ e off b, 0 < (c e off).mass b) (hρ : ∀ e, 0 < ρ.mass e)
    (enhanced : Finset E) (auxiliary : List E)
    (schedule : List E) (hschedule : ∀ e, e ∈ schedule) :
    OpenPath.FinProb.LawTendsto Filter.atTop
      (fun n => μ.bind (iterate (modifiedJump ρ c enhanced auxiliary) n)) π := by
  let e₀ : E := Classical.choice (inferInstance : Nonempty E)
  have hN : 0 < schedule.length := List.length_pos_of_mem (hschedule e₀)
  have hπ : Invariant π (modifiedJump ρ c enhanced auxiliary) :=
    modifiedJump_invariant π ρ c hc enhanced auxiliary
  have hpos : ∀ ω η, 0 < (iterate (modifiedJump ρ c enhanced auxiliary)
      schedule.length ω).mass η := by
    intro ω η
    simpa using modifiedJump_iterate_pos c hcpos ρ hρ enhanced auxiliary schedule hschedule ω η
  exact tendsto_bind_iterate_of_positive_power μ π _ hπ hN hpos

end ModifiedJumpConvergence

end Glauber
