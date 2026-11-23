import Mathlib

/-! # Ordered couplings and stochastic comparison of update kernels

This file supplies the paper-independent probabilistic engine for
Beffara--Faipeur--Oke, arXiv:2512.16486. It defines domination by all increasing
events, constructs ordered couplings, composes them along discrete-time update
kernels, passes comparisons to limits, and compares finite real expectations.

All convergence and one-step coupling assumptions are explicit. In particular,
this file does not assert the convergence, stationarity, FK-specific update, or
Strassen-coupling results that are not proved here.
-/

open Filter Set Topology
open scoped ENNReal

namespace PMF

universe u v w z

/-- A probability measure on pairs with prescribed first and second marginals. -/
structure Coupling {α : Type u} {β : Type v} (μ : PMF α) (ν : PMF β) where
  dist : PMF (α × β)
  map_fst : dist.map Prod.fst = μ
  map_snd : dist.map Prod.snd = ν

namespace Coupling

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
variable {μ : PMF α} {ν : PMF β}

/-- The independent coupling of two probability mass functions. -/
noncomputable def product (μ : PMF α) (ν : PMF β) : Coupling μ ν where
  dist := μ.bind fun a => ν.map fun b => (a, b)
  map_fst := by
    rw [PMF.map_bind]
    have hfst (a : α) : (ν.map fun b => (a, b)).map Prod.fst = PMF.pure a := by
      rw [PMF.map_comp]
      change ν.map (Function.const β a) = PMF.pure a
      exact PMF.map_const ν a
    simp_rw [hfst]
    exact PMF.bind_pure μ
  map_snd := by
    rw [PMF.map_bind]
    have hsnd (a : α) : (ν.map fun b => (a, b)).map Prod.snd = ν := by
      rw [PMF.map_comp]
      change ν.map id = ν
      exact PMF.map_id ν
    simp_rw [hsnd]
    exact PMF.bind_const μ ν

/-- Compose a coupling of the current states with couplings of the update laws. -/
noncomputable def bind (c : Coupling μ ν) (K : α → PMF γ) (L : β → PMF δ)
    (step : ∀ a b, Coupling (K a) (L b)) : Coupling (μ.bind K) (ν.bind L) where
  dist := c.dist.bind fun x => (step x.1 x.2).dist
  map_fst := by
    rw [PMF.map_bind]
    simp_rw [(step _ _).map_fst]
    change c.dist.bind (K ∘ Prod.fst) = μ.bind K
    rw [← PMF.bind_map, c.map_fst]
  map_snd := by
    rw [PMF.map_bind]
    simp_rw [(step _ _).map_snd]
    change c.dist.bind (L ∘ Prod.snd) = ν.bind L
    rw [← PMF.bind_map, c.map_snd]

end Coupling

/-- A coupling supported on pairs ordered by `Prod.fst ≤ Prod.snd`. -/
structure OrderedCoupling {α : Type u} [LE α] (μ ν : PMF α)
    extends Coupling μ ν where
  ordered : ∀ x ∈ dist.support, x.1 ≤ x.2

namespace OrderedCoupling

section Diagonal

variable {α : Type u} [Preorder α]

/-- The diagonal coupling, supported on `(a,a)`. -/
noncomputable def diagonal (μ : PMF α) : OrderedCoupling μ μ where
  dist := μ.map fun a => (a, a)
  map_fst := by
    rw [PMF.map_comp]
    change μ.map id = μ
    exact PMF.map_id μ
  map_snd := by
    rw [PMF.map_comp]
    change μ.map id = μ
    exact PMF.map_id μ
  ordered x hx := by
    rw [PMF.mem_support_map_iff] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact le_rfl

end Diagonal

end OrderedCoupling

/-- Stochastic domination, quantified over all increasing (upper) events exactly as
in Beffara--Faipeur--Oke, Section 1.2. -/
def StochLe {α : Type u} [LE α] (μ ν : PMF α) : Prop :=
  ∀ A : Set α, IsUpperSet A → μ.toOuterMeasure A ≤ ν.toOuterMeasure A

namespace OrderedCoupling

variable {α : Type u} [LE α] {μ ν : PMF α}

/-- An ordered coupling gives the increasing-event inequality. -/
theorem stochLe (c : OrderedCoupling μ ν) : StochLe μ ν := by
  intro A hA
  calc
    μ.toOuterMeasure A = c.dist.toOuterMeasure (Prod.fst ⁻¹' A) := by
      have h := congrArg (fun p : PMF α => p.toOuterMeasure A) c.map_fst
      rw [PMF.toOuterMeasure_map_apply] at h
      exact h.symm
    _ ≤ c.dist.toOuterMeasure (Prod.snd ⁻¹' A) := by
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hzero : c.dist x = 0
      · by_cases hx : x.1 ∈ A <;> by_cases hx' : x.2 ∈ A <;>
          simp [hx, hx', hzero]
      · by_cases hx : x.1 ∈ A
        · have hx' : x.2 ∈ A := hA (c.ordered x hzero) hx
          simp [Set.indicator_of_mem, hx, hx']
        · simp [Set.indicator_of_notMem, hx]
    _ = ν.toOuterMeasure A := by
      have h := congrArg (fun p : PMF α => p.toOuterMeasure A) c.map_snd
      rw [PMF.toOuterMeasure_map_apply] at h
      exact h

end OrderedCoupling

end PMF


namespace PMF.OrderedCoupling

variable {α : Type u} [LE α] {μ ν : PMF α}

/-- Compose ordered dynamics. The supplied update coupling is required only on
comparable current states; away from them we use the independent coupling. -/
noncomputable def bind (c : OrderedCoupling μ ν) (K L : α → PMF α)
    (step : ∀ a b, a ≤ b → OrderedCoupling (K a) (L b)) :
    OrderedCoupling (μ.bind K) (ν.bind L) := by
  classical
  let allStep : ∀ a b, Coupling (K a) (L b) := fun a b =>
    if h : a ≤ b then (step a b h).toCoupling else Coupling.product (K a) (L b)
  let combined : Coupling (μ.bind K) (ν.bind L) := c.toCoupling.bind K L allStep
  exact
    { toCoupling := combined
      ordered := by
        intro x hx
        change x ∈ (c.dist.bind fun y => (allStep y.1 y.2).dist).support at hx
        obtain ⟨y, hy, hxy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
        have hy_le : y.1 ≤ y.2 := c.ordered y hy
        have hxy' : x ∈ (step y.1 y.2 hy_le).dist.support := by
          simpa only [allStep, dif_pos hy_le] using hxy
        exact (step y.1 y.2 hy_le).ordered x hxy' }

end PMF.OrderedCoupling

namespace PMF

variable {α : Type u} [LE α]

/-- Discrete-time evolution of a mass function under an update kernel. -/
noncomputable def bindIterate (μ : PMF α) (K : α → PMF α) : ℕ → PMF α
  | 0 => μ
  | n + 1 => (bindIterate μ K n).bind K

omit [LE α] in
@[simp] theorem bindIterate_zero (μ : PMF α) (K : α → PMF α) :
    bindIterate μ K 0 = μ := rfl

omit [LE α] in
@[simp] theorem bindIterate_succ (μ : PMF α) (K : α → PMF α) (n : ℕ) :
    bindIterate μ K (n + 1) = (bindIterate μ K n).bind K := rfl

/-- An ordered coupling of the initial laws and ordered couplings of the update
laws at every comparable pair give an ordered coupling at every finite time. -/
theorem nonempty_orderedCoupling_bindIterate {μ ν : PMF α} {K L : α → PMF α}
    (h₀ : Nonempty (OrderedCoupling μ ν))
    (hstep : ∀ {a b}, a ≤ b → Nonempty (OrderedCoupling (K a) (L b))) (n : ℕ) :
    Nonempty (OrderedCoupling (bindIterate μ K n) (bindIterate ν L n)) := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
      obtain ⟨c⟩ := ih
      exact ⟨c.bind K L fun _ _ h => Classical.choice (hstep h)⟩

/-- The same induction stated directly as the paper's increasing-event order. -/
theorem stochLe_bindIterate {μ ν : PMF α} {K L : α → PMF α}
    (h₀ : Nonempty (OrderedCoupling μ ν))
    (hstep : ∀ {a b}, a ≤ b → Nonempty (OrderedCoupling (K a) (L b))) (n : ℕ) :
    StochLe (bindIterate μ K n) (bindIterate ν L n) := by
  obtain ⟨c⟩ := nonempty_orderedCoupling_bindIterate h₀ hstep n
  exact c.stochLe

namespace StochLe

theorem refl (μ : PMF α) : StochLe μ μ := fun _ _ => le_rfl

theorem trans {μ ν ρ : PMF α} (hμν : StochLe μ ν) (hνρ : StochLe ν ρ) :
    StochLe μ ρ := fun A hA => (hμν A hA).trans (hνρ A hA)

/-- Increasing-event inequalities pass to two-sided weak limits. The limit
hypotheses are only for increasing events, not for arbitrary test functions. -/
theorem of_tendsto {μ ν : PMF α} {μs νs : ℕ → PMF α}
    (hμ : ∀ A, IsUpperSet A →
      Tendsto (fun n => (μs n).toOuterMeasure A) atTop (𝓝 (μ.toOuterMeasure A)))
    (hν : ∀ A, IsUpperSet A →
      Tendsto (fun n => (νs n).toOuterMeasure A) atTop (𝓝 (ν.toOuterMeasure A)))
    (h : ∀ n, StochLe (μs n) (νs n)) : StochLe μ ν := by
  intro A hA
  exact le_of_tendsto_of_tendsto' (hμ A hA) (hν A hA) fun n => h n A hA

end StochLe

end PMF


namespace PMF

variable {α : Type u} [Preorder α]

/-- Starting both coupled processes from the same law preserves their order at
every finite time. -/
theorem stochLe_bindIterate_of_common_initial {μ : PMF α} {K L : α → PMF α}
    (hstep : ∀ {a b}, a ≤ b → Nonempty (OrderedCoupling (K a) (L b))) (n : ℕ) :
    StochLe (bindIterate μ K n) (bindIterate μ L n) :=
  stochLe_bindIterate ⟨OrderedCoupling.diagonal μ⟩ hstep n

/-- Common initial law, comparable one-step updates, and convergence of the two
sequences on increasing events imply domination of the limiting laws. This is
an explicit hypothesis-level interface for the limiting argument in Section 3;
no convergence or stationarity theorem is silently assumed. -/
theorem stochLe_of_common_initial_limit {μ ν ρ : PMF α} {K L : α → PMF α}
    (hstep : ∀ {a b}, a ≤ b → Nonempty (OrderedCoupling (K a) (L b)))
    (hK : ∀ A, IsUpperSet A →
      Tendsto (fun n => (bindIterate ρ K n).toOuterMeasure A) atTop
        (𝓝 (μ.toOuterMeasure A)))
    (hL : ∀ A, IsUpperSet A →
      Tendsto (fun n => (bindIterate ρ L n).toOuterMeasure A) atTop
        (𝓝 (ν.toOuterMeasure A))) : StochLe μ ν :=
  StochLe.of_tendsto hK hL (stochLe_bindIterate_of_common_initial hstep)

/-- Expectation of a real observable on a finite state space. -/
noncomputable def finiteExpectation {β : Type v} [Fintype β]
    (μ : PMF β) (f : β → ℝ) : ℝ := ∑ b, (μ b).toReal * f b

namespace Coupling

variable {β : Type v} {γ : Type w} [Fintype β] [Fintype γ]
variable {μ : PMF β} {ν : PMF γ}

/-- The first marginal computes expectations by summing over the coupling. -/
theorem finiteExpectation_fst (c : Coupling μ ν) (f : β → ℝ) :
    finiteExpectation μ f = ∑ x, (c.dist x).toReal * f x.1 := by
  classical
  have hmass (a : β) : μ a = ∑ x : β × γ, if a = x.1 then c.dist x else 0 := by
    have h := congrArg (fun p : PMF β => p a) c.map_fst
    rw [PMF.map_apply] at h
    simpa only [tsum_fintype] using h.symm
  unfold finiteExpectation
  calc
    (∑ a, (μ a).toReal * f a) =
        ∑ a, (∑ x : β × γ, if a = x.1 then c.dist x else 0).toReal * f a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hmass a]
    _ = ∑ a, (∑ x : β × γ, (if a = x.1 then c.dist x else 0).toReal) * f a := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      rw [ENNReal.toReal_sum]
      intro x _
      split_ifs
      · exact c.dist.apply_ne_top x
      · exact ENNReal.zero_ne_top
    _ = ∑ a, ∑ x : β × γ,
        if a = x.1 then (c.dist x).toReal * f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x : β × γ, ∑ a,
        if a = x.1 then (c.dist x).toReal * f a else 0 := Finset.sum_comm
    _ = ∑ x, (c.dist x).toReal * f x.1 := by
      apply Finset.sum_congr rfl
      intro x _
      simp

/-- The second marginal computes expectations by summing over the coupling. -/
theorem finiteExpectation_snd (c : Coupling μ ν) (f : γ → ℝ) :
    finiteExpectation ν f = ∑ x, (c.dist x).toReal * f x.2 := by
  classical
  have hmass (b : γ) : ν b = ∑ x : β × γ, if b = x.2 then c.dist x else 0 := by
    have h := congrArg (fun p : PMF γ => p b) c.map_snd
    rw [PMF.map_apply] at h
    simpa only [tsum_fintype] using h.symm
  unfold finiteExpectation
  calc
    (∑ b, (ν b).toReal * f b) =
        ∑ b, (∑ x : β × γ, if b = x.2 then c.dist x else 0).toReal * f b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [hmass b]
    _ = ∑ b, (∑ x : β × γ, (if b = x.2 then c.dist x else 0).toReal) * f b := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      rw [ENNReal.toReal_sum]
      intro x _
      split_ifs
      · exact c.dist.apply_ne_top x
      · exact ENNReal.zero_ne_top
    _ = ∑ b, ∑ x : β × γ,
        if b = x.2 then (c.dist x).toReal * f b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x : β × γ, ∑ b,
        if b = x.2 then (c.dist x).toReal * f b else 0 := Finset.sum_comm
    _ = ∑ x, (c.dist x).toReal * f x.2 := by
      apply Finset.sum_congr rfl
      intro x _
      simp

end Coupling

namespace OrderedCoupling

variable {β : Type v} [Preorder β] [Fintype β] {μ ν : PMF β}

/-- Ordered couplings compare every monotone real observable on a finite state
space. There are no boundedness or integrability side conditions because the
state space is finite. -/
theorem finiteExpectation_mono (c : OrderedCoupling μ ν) {f : β → ℝ}
    (hf : Monotone f) : finiteExpectation μ f ≤ finiteExpectation ν f := by
  rw [c.toCoupling.finiteExpectation_fst, c.toCoupling.finiteExpectation_snd]
  apply Finset.sum_le_sum
  intro x _
  by_cases hzero : c.dist x = 0
  · simp [hzero]
  · exact mul_le_mul_of_nonneg_left (hf (c.ordered x hzero)) ENNReal.toReal_nonneg

end OrderedCoupling

end PMF


namespace PMF

variable {β : Type v} [Fintype β]

@[simp] theorem finiteExpectation_const (μ : PMF β) (c : ℝ) :
    finiteExpectation μ (fun _ => c) = c := by
  classical
  have hmass : ∑ b, (μ b).toReal = 1 := by
    calc
      (∑ b, (μ b).toReal) = (∑ b, μ b).toReal :=
        (ENNReal.toReal_sum (fun b _ => μ.apply_ne_top b)).symm
      _ = (∑' b, μ b).toReal := by rw [tsum_fintype]
      _ = 1 := by rw [μ.tsum_coe, ENNReal.toReal_one]
  unfold finiteExpectation
  rw [← Finset.sum_mul, hmass, one_mul]

variable [Preorder β]

/-- The monotone-observable form of finite-time comparison of two update
kernels. -/
theorem finiteExpectation_bindIterate_mono {μ ν : PMF β} {K L : β → PMF β}
    (h₀ : Nonempty (OrderedCoupling μ ν))
    (hstep : ∀ {a b}, a ≤ b → Nonempty (OrderedCoupling (K a) (L b)))
    {f : β → ℝ} (hf : Monotone f) (n : ℕ) :
    finiteExpectation (bindIterate μ K n) f ≤
      finiteExpectation (bindIterate ν L n) f := by
  obtain ⟨c⟩ := nonempty_orderedCoupling_bindIterate h₀ hstep n
  exact c.finiteExpectation_mono hf

end PMF


namespace PMF.OrderedCoupling

variable {α : Type u} {γ : Type w} [LE α]

/-- Couple two update functions by evaluating them at the same random seed.
Only order on the support of the seed distribution is required. This is the
abstract form of a shared-uniform threshold coupling. -/
noncomputable def ofMapPair (ρ : PMF γ) (f g : γ → α)
    (hfg : ∀ r ∈ ρ.support, f r ≤ g r) :
    OrderedCoupling (ρ.map f) (ρ.map g) where
  dist := ρ.map fun r => (f r, g r)
  map_fst := by
    rw [PMF.map_comp]
    rfl
  map_snd := by
    rw [PMF.map_comp]
    rfl
  ordered x hx := by
    rw [PMF.mem_support_map_iff] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact hfg r hr

end PMF.OrderedCoupling

namespace PMF.StochLe

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

/-- Increasing-event domination is preserved by a common monotone map. -/
theorem map {μ ν : PMF α} (h : StochLe μ ν) {f : α → β} (hf : Monotone f) :
    StochLe (μ.map f) (ν.map f) := by
  intro A hA
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact h _ (hA.preimage hf)

end PMF.StochLe
