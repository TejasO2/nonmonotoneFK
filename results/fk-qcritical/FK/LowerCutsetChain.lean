import FK.ClosedCutsetBridge

/-!
# Closed-cutset enhanced ordered-pair dynamics

This file removes the full-support restriction from the finite convergence
argument, then constructs the lower closed-cutset pair dynamics.  The Doeblin
minorant is weighted by the stationary law, so states of stationary mass zero
are allowed.
-/

namespace Glauber

open scoped Topology
open Filter

section StationarySupportContraction

variable {α : Type*} [Fintype α]

/-- A kernel difference with a stationary-law-weighted common component. -/
lemma bind_sub_mass_stationary (μ ν π : OpenPath.FinProb α)
    (κ : α → OpenPath.FinProb α) (δ : ℝ) (b : α) :
    (μ.bind κ).mass b - (ν.bind κ).mass b =
      ∑ a, (μ.mass a - ν.mass a) * ((κ a).mass b - δ * π.mass b) := by
  have hzero : ∑ a, (μ.mass a - ν.mass a) * (δ * π.mass b) = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, μ.sum_mass, ν.sum_mass]
    ring
  simp only [OpenPath.FinProb.mass_bind, ← Finset.sum_sub_distrib]
  calc
    (∑ a, (μ.mass a * (κ a).mass b - ν.mass a * (κ a).mass b)) =
        ∑ a, (μ.mass a - ν.mass a) * (κ a).mass b := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a, (μ.mass a - ν.mass a) * ((κ a).mass b - δ * π.mass b)) +
        ∑ a, (μ.mass a - ν.mass a) * (δ * π.mass b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hzero, add_zero]

/-- Doeblin contraction with the minorant `δ • π`, rather than a positive
constant at every state. -/
lemma variation_bind_le_stationary (μ ν π : OpenPath.FinProb α)
    (κ : α → OpenPath.FinProb α) (δ : ℝ)
    (hδ : ∀ a b, δ * π.mass b ≤ (κ a).mass b) :
    variation (μ.bind κ) (ν.bind κ) ≤ (1 - δ) * variation μ ν := by
  classical
  have hrow (a : α) : ∑ b, ((κ a).mass b - δ * π.mass b) = 1 - δ := by
    rw [Finset.sum_sub_distrib, (κ a).sum_mass, ← Finset.mul_sum, π.sum_mass]
    ring
  have hres (a b : α) : 0 ≤ (κ a).mass b - δ * π.mass b :=
    sub_nonneg.mpr (hδ a b)
  unfold variation
  calc
    (∑ b, |(μ.bind κ).mass b - (ν.bind κ).mass b|) =
        ∑ b, |∑ a, (μ.mass a - ν.mass a) *
          ((κ a).mass b - δ * π.mass b)| := by
      apply Finset.sum_congr rfl
      intro b _
      rw [bind_sub_mass_stationary]
    _ ≤ ∑ b, ∑ a, |(μ.mass a - ν.mass a) *
          ((κ a).mass b - δ * π.mass b)| := by
      apply Finset.sum_le_sum
      intro b _
      simpa using Finset.abs_sum_le_sum_abs
        (fun a => (μ.mass a - ν.mass a) *
          ((κ a).mass b - δ * π.mass b)) Finset.univ
    _ = ∑ a, |μ.mass a - ν.mass a| * (1 - δ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [abs_mul, abs_of_nonneg (hres a _)]
      rw [← Finset.mul_sum, hrow]
    _ = (1 - δ) * ∑ a, |μ.mass a - ν.mass a| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _

lemma variation_bind_iterate_le_stationary (μ ν π : OpenPath.FinProb α)
    (κ : α → OpenPath.FinProb α) (δ : ℝ)
    (hδ : ∀ a b, δ * π.mass b ≤ (κ a).mass b) (hs : 0 ≤ 1 - δ) :
    ∀ r : ℕ, variation (μ.bind (iterate κ r)) (ν.bind (iterate κ r)) ≤
      (1 - δ) ^ r * variation μ ν := by
  intro r
  induction r generalizing μ ν with
  | zero => simp [FinProb.bind_dirac_right]
  | succ r ih =>
      let s : ℝ := 1 - δ
      have hstep := variation_bind_le_stationary μ ν π κ δ hδ
      calc
        variation (μ.bind (iterate κ (r + 1))) (ν.bind (iterate κ (r + 1))) =
            variation ((μ.bind κ).bind (iterate κ r))
              ((ν.bind κ).bind (iterate κ r)) := by
          rw [iterate_succ]
          unfold seq
          rw [FinProb.bind_assoc, FinProb.bind_assoc]
        _ ≤ s ^ r * variation (μ.bind κ) (ν.bind κ) := ih (μ.bind κ) (ν.bind κ)
        _ ≤ s ^ r * (s * variation μ ν) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hs r)
        _ = s ^ (r + 1) * variation μ ν := by rw [pow_succ]; ring

/-- Convergence under a stationary-law-weighted Doeblin minorant. -/
theorem tendsto_bind_iterate_of_invariant_stationary [Nonempty α]
    (μ π : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (hπ : Invariant π κ) (δ : ℝ)
    (hδ : ∀ a b, δ * π.mass b ≤ (κ a).mass b)
    (hs0 : 0 ≤ 1 - δ) (hs1 : 1 - δ < 1) :
    OpenPath.FinProb.LawTendsto atTop (fun r => μ.bind (iterate κ r)) π := by
  let s : ℝ := 1 - δ
  intro b
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  change Tendsto (fun r => |(μ.bind (iterate κ r)).mass b - π.mass b|)
    atTop (nhds 0)
  apply squeeze_zero (fun r => abs_nonneg _)
    (g := fun r => s ^ r * variation μ π)
  · intro r
    have hv := variation_bind_iterate_le_stationary μ π π κ δ hδ hs0 r
    have hπr : π.bind (iterate κ r) = π := iterate_invariant hπ r
    rw [hπr] at hv
    exact (Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => abs_nonneg _)
      (Finset.mem_univ b)).trans hv
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).mul_const (variation μ π)

end StationarySupportContraction

section StationarySupportPositivePower

variable {α : Type*} [Fintype α]

/-- A finite kernel which is positive at the stationary support has an
everywhere-defined positive multiple of that stationary law as a Doeblin
minorant. -/
lemma exists_stationary_doeblin_delta [Nonempty α]
    (κ : α → OpenPath.FinProb α) (π : OpenPath.FinProb α)
    (hκ : ∀ a b, 0 < π.mass b → 0 < (κ a).mass b) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ a b, δ * π.mass b ≤ (κ a).mass b) ∧
      0 ≤ 1 - δ ∧ 1 - δ < 1 := by
  classical
  let m : ℝ := Finset.inf' (Finset.univ : Finset (α × α)) Finset.univ_nonempty
    (fun p => if π.mass p.2 = 0 then 1 else (κ p.1).mass p.2 / π.mass p.2)
  have hmpos : 0 < m := by
    apply Finset.inf'_mem (Set.Ioi (0 : ℝ))
      (fun a ha b hb => by
        change 0 < min a b
        exact lt_min ha hb) Finset.univ Finset.univ_nonempty
    intro p _
    by_cases hb : π.mass p.2 = 0
    · simp [hb]
    · have hbpos : 0 < π.mass p.2 :=
        lt_of_le_of_ne (π.mass_nonneg p.2) (Ne.symm hb)
      simpa [hb] using div_pos (hκ p.1 p.2 hbpos) hbpos
  have hm (a b : α) : m ≤ if π.mass b = 0 then 1 else
      (κ a).mass b / π.mass b :=
    Finset.inf'_le (fun p : α × α => if π.mass p.2 = 0 then 1 else
      (κ p.1).mass p.2 / π.mass p.2) (Finset.mem_univ (a, b))
  let δ : ℝ := min (m / 2) (1 / 2)
  have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδm : δ ≤ m := (min_le_left _ _).trans (by linarith)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  refine ⟨δ, hδpos, ?_, by linarith, by linarith⟩
  intro a b
  by_cases hb : π.mass b = 0
  · simp [hb, (κ a).mass_nonneg b]
  · have hbpos : 0 < π.mass b :=
      lt_of_le_of_ne (π.mass_nonneg b) (Ne.symm hb)
    have hm' := hm a b
    simp only [hb, if_false] at hm'
    calc
      δ * π.mass b ≤ m * π.mass b :=
        mul_le_mul_of_nonneg_right hδm (π.mass_nonneg b)
      _ ≤ (κ a).mass b := (le_div_iff₀ hbpos).mp hm'

/-- Positive reachability of the stationary support at one common positive
power suffices for convergence from every initial finite law.  No positivity
is required at states where the invariant law vanishes. -/
theorem tendsto_bind_iterate_of_stationary_support_positive_power [Nonempty α]
    (μ π : OpenPath.FinProb α) (κ : α → OpenPath.FinProb α)
    (hπ : Invariant π κ) {N : ℕ} (hN : 0 < N)
    (hpos : ∀ a b, 0 < π.mass b → 0 < (iterate κ N a).mass b) :
    OpenPath.FinProb.LawTendsto atTop (fun n => μ.bind (iterate κ n)) π := by
  let R : α → OpenPath.FinProb α := iterate κ N
  obtain ⟨δ, hδpos, hδ, hs0, hs1⟩ := exists_stationary_doeblin_delta R π hpos
  let s : ℝ := 1 - δ
  have hπR : Invariant π R := iterate_invariant hπ N
  intro b
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  change Tendsto (fun n => |(μ.bind (iterate κ n)).mass b - π.mass b|)
    atTop (nhds 0)
  have hdiv : Tendsto (fun n => n / N) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.ne_of_gt hN)
  have hgeo : Tendsto (fun n => s ^ (n / N) * 2) atTop (nhds 0) := by
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
  have hv := variation_bind_iterate_le_stationary μk π π R δ hδ hs0 r
  have hπr : π.bind (iterate R r) = π := iterate_invariant hπR r
  rw [hπr, ← hlaw] at hv
  calc
    |(μ.bind (iterate κ n)).mass b - π.mass b| ≤ variation (μ.bind (iterate κ n)) π := by
      unfold variation
      exact Finset.single_le_sum
        (f := fun a : α => |(μ.bind (iterate κ n)).mass a - π.mass a|)
        (fun a (_ : a ∈ Finset.univ) => abs_nonneg _)
        (Finset.mem_univ b)
    _ ≤ s ^ r * variation μk π := hv
    _ ≤ s ^ r * 2 := mul_le_mul_of_nonneg_left (variation_le_two μk π) (pow_nonneg hs0 r)
    _ = s ^ (n / N) * 2 := rfl

end StationarySupportPositivePower

end Glauber


namespace Glauber

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Exact mass formula for a conjugated coordinate refresh. -/
lemma bind_refreshConj_mass (ρ : α ≃ β × γ) (μ : OpenPath.FinProb α)
    (c : β → OpenPath.FinProb γ) (z : α) :
    (μ.bind (refreshConj ρ c)).mass z =
      outsideMassConj ρ μ (ρ z).1 * (c (ρ z).1).mass (ρ z).2 := by
  classical
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
        (μ.mass (ρ.symm x) * (c (ρ z).1).mass (ρ z).2) else 0 := by
      simpa using Equiv.sum_comp ρ (fun x : β × γ =>
        if x.1 = (ρ z).1 then μ.mass (ρ.symm x) * (c (ρ z).1).mass (ρ z).2 else 0)
    _ = ∑ y, μ.mass (ρ.symm ((ρ z).1, y)) * (c (ρ z).1).mass (ρ z).2 :=
      sum_prod_ite_fst (ρ z).1 _
    _ = outsideMassConj ρ μ (ρ z).1 * (c (ρ z).1).mass (ρ z).2 := by
      rw [outsideMassConj, Finset.sum_mul]

section ProductRefresh

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

lemma pi_mass_configSplit_symm (ν : E → OpenPath.FinProb B) (e : E)
    (off : OffConfig B E e) (b : B) :
    (OpenPath.FinProb.pi ν).mass ((configSplit B e).symm (off, b)) =
      (ν e).mass b * ∏ a : {a : E // a ≠ e}, (ν a.1).mass (off a) := by
  rw [OpenPath.FinProb.pi_mass, Fintype.prod_eq_mul_prod_subtype_ne _ e]
  congr 1
  · change (ν e).mass ((configSplit B e ((configSplit B e).symm (off, b))).2) = _
    simp
  · apply Finset.prod_congr rfl
    intro a _
    change (ν a.1).mass ((configSplit B e ((configSplit B e).symm (off, b))).1 a) = _
    simp

lemma pi_outsideMassConj (ν : E → OpenPath.FinProb B) (e : E)
    (off : OffConfig B E e) :
    outsideMassConj (configSplit B e) (OpenPath.FinProb.pi ν) off =
      ∏ a : {a : E // a ≠ e}, (ν a.1).mass (off a) := by
  classical
  rw [outsideMassConj]
  simp_rw [pi_mass_configSplit_symm]
  rw [← Finset.sum_mul, (ν e).sum_mass, one_mul]

/-- Refreshing one coordinate of an indexed product replaces precisely that
coordinate's factor. -/
theorem pi_bind_edgeUpdate_const (ν : E → OpenPath.FinProb B)
    (c : EdgeConditionals B E) (e : E) (ξ : OpenPath.FinProb B)
    (hc : ∀ off, c e off = ξ) :
    (OpenPath.FinProb.pi ν).bind (edgeUpdate c e) =
      OpenPath.FinProb.pi (Function.update ν e ξ) := by
  apply OpenPath.FinProb.ext
  intro z
  rw [edgeUpdate, bind_refreshConj_mass, pi_outsideMassConj, hc]
  rw [OpenPath.FinProb.pi_mass, Fintype.prod_eq_mul_prod_subtype_ne _ e]
  change (∏ a : {a : E // a ≠ e}, (ν a.1).mass (z a.1)) * ξ.mass (z e) = _
  simp only [Function.update_self]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [Function.update_of_ne a.2]

/-- A duplicate-free sequential sweep of constant coordinate conditionals
replaces the corresponding factors of an indexed product. -/
theorem pi_bind_sweep_edgeUpdate_const (ν ξ : E → OpenPath.FinProb B)
    (c : EdgeConditionals B E) :
    ∀ l : List E, l.Nodup → (∀ e ∈ l, ∀ off, c e off = ξ e) →
      (OpenPath.FinProb.pi ν).bind (sweep (l.map (edgeUpdate c))) =
        OpenPath.FinProb.pi (fun e => if e ∈ l then ξ e else ν e) := by
  intro l
  induction l generalizing ν with
  | nil =>
      intro _ _
      change (OpenPath.FinProb.pi ν).bind (fun a => FinProb.dirac a) =
        OpenPath.FinProb.pi ν
      exact FinProb.bind_dirac_right _
  | cons e l ih =>
      intro hl hc
      simp only [List.nodup_cons] at hl
      simp only [List.map_cons, sweep]
      unfold seq
      rw [← FinProb.bind_assoc,
        pi_bind_edgeUpdate_const ν c e (ξ e) (hc e (by simp)),
        ih (Function.update ν e (ξ e)) hl.2
          (fun f hf => hc f (by simp [hf]))]
      congr 1
      funext a
      by_cases hae : a = e
      · subst a
        simp [hl.1]
      · by_cases hal : a ∈ l <;> simp [Function.update_of_ne hae, hae, hal]

lemma pi_dirac (ω : E → B) :
    OpenPath.FinProb.pi (fun e => FinProb.dirac (ω e)) = FinProb.dirac ω := by
  apply OpenPath.FinProb.ext
  intro η
  by_cases h : η = ω
  · subst η
    simp [OpenPath.FinProb.pi_mass, FinProb.dirac]
  · have hne : ∃ e, η e ≠ ω e := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨e, he⟩ := hne
    rw [OpenPath.FinProb.pi_mass]
    simp only [FinProb.dirac]
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [he]

/-- After one enhanced-edge update from a deterministic configuration, the
law is a product: random at the updated edge and deterministic elsewhere. -/
lemma dirac_bind_edgeUpdate (c : EdgeConditionals B E) (e : E) (ω : E → B) :
    (FinProb.dirac ω).bind (edgeUpdate c e) =
      OpenPath.FinProb.pi (Function.update (fun f => FinProb.dirac (ω f)) e
        (c e (fun f => ω f.1))) := by
  let c' : EdgeConditionals B E := fun f off =>
    if f = e then c e (fun g => ω g.1) else c f off
  have hkernel : edgeUpdate c e ω = edgeUpdate c' e ω := by
    rw [edgeUpdate_eq_map, edgeUpdate_eq_map]
    simp [c']
  calc
    (FinProb.dirac ω).bind (edgeUpdate c e) =
        (FinProb.dirac ω).bind (edgeUpdate c' e) := by
      rw [FinProb.bind_dirac, FinProb.bind_dirac, hkernel]
    _ = (OpenPath.FinProb.pi (fun f => FinProb.dirac (ω f))).bind
        (edgeUpdate c' e) := by rw [pi_dirac]
    _ = _ := pi_bind_edgeUpdate_const _ c' e (c e (fun f => ω f.1)) (by
      intro off
      simp [c'])

end ProductRefresh

end Glauber


namespace OpenPath.FinProb

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B]

lemma pure_eq_glauberDirac (a : B) : pure a = Glauber.FinProb.dirac a := by
  apply FinProb.ext
  intro b
  rfl

lemma pi_pure (ω : ι → B) :
    FinProb.pi (fun i => pure (ω i)) = pure ω := by
  simp only [pure_eq_glauberDirac]
  exact Glauber.pi_dirac ω

end OpenPath.FinProb

namespace Glauber

open JointInvariance

section BlockNormalForms

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-- One enhanced edge followed by a duplicate-free list of constant
auxiliary refreshes, written as an indexed product with untouched point-mass
factors. -/
lemma dirac_bind_enhanced_sweep (c : EdgeConditionals B E)
    (ξ : E → OpenPath.FinProb B) (e : E) (auxiliary : List E)
    (haux : auxiliary.Nodup) (he : e ∉ auxiliary)
    (hc : ∀ f ∈ auxiliary, ∀ off, c f off = ξ f) (ω : E → B) :
    (FinProb.dirac ω).bind (sweep ((e :: auxiliary).map (edgeUpdate c))) =
      OpenPath.FinProb.pi (fun f => if f ∈ auxiliary then ξ f else
        Function.update (fun a => FinProb.dirac (ω a)) e
          (c e (fun a => ω a.1)) f) := by
  simp only [List.map_cons, sweep]
  unfold seq
  rw [← FinProb.bind_assoc, dirac_bind_edgeUpdate,
    pi_bind_sweep_edgeUpdate_const _ ξ c auxiliary haux hc]

/-- The simultaneous enhanced/auxiliary block transported through
`indexedBlockEquiv` has the corresponding explicit product normal form. -/
lemma transportedBlockKernel_eq_pi (ξ : E → OpenPath.FinProb B) (e : E)
    (A : Finset E) (κ : (AuxiliaryIndex E e A → B) → OpenPath.FinProb B)
    (ω : E → B) :
    transportedBlockKernel (indexedBlockEquiv e A)
        (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ξ a.1.1)) κ ω =
      OpenPath.FinProb.pi (fun f => if f = e then
        κ (((indexedBlockEquiv (β := B) e A) ω).1.2)
        else if f ∈ A then ξ f else OpenPath.FinProb.pure (ω f)) := by
  let D := indexedBlockEquiv (β := B) e A
  let ν : E → OpenPath.FinProb B := fun f => if f = e then κ (D ω).1.2
    else if f ∈ A then ξ f else OpenPath.FinProb.pure (ω f)
  have hνe : ν e = κ (D ω).1.2 := by simp [ν]
  have hνaux : (fun a : AuxiliaryIndex E e A => ν a.1.1) =
      (fun a => ξ a.1.1) := by
    funext a
    simp [ν, a.1.2, a.2]
  have hνrest : (fun r : RemainingIndex E e A => ν r.1.1) =
      (fun r => OpenPath.FinProb.pure (ω r.1.1)) := by
    funext r
    simp [ν, r.1.2, r.2]
  have hrest : (OpenPath.FinProb.pi
      (fun r : RemainingIndex E e A => ν r.1.1)) = OpenPath.FinProb.pure (D ω).2 := by
    rw [hνrest]
    have hp := OpenPath.FinProb.pi_pure (fun r : RemainingIndex E e A => ω r.1.1)
    rw [hp]
    congr 1
  have hdecomp := map_pi_indexedBlockEquiv ν e A
  change (OpenPath.FinProb.pi ν).map D =
    blockLaw (ν e) (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ν a.1.1))
      (OpenPath.FinProb.pi (fun r : RemainingIndex E e A => ν r.1.1)) at hdecomp
  rw [hνe, hνaux, hrest] at hdecomp
  change ((((κ (D ω).1.2).prod
      (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ξ a.1.1))).prod
      (OpenPath.FinProb.pure (D ω).2)).map D.symm) = OpenPath.FinProb.pi ν
  change (blockLaw (κ (D ω).1.2)
      (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e A => ξ a.1.1))
      (OpenPath.FinProb.pure (D ω).2)).map D.symm = _
  rw [← hdecomp, OpenPath.FinProb.map_equiv_symm]

/-- Exact sequential/simultaneous block identity.  The enhanced conditional
may use the old auxiliary state. -/
theorem dirac_blockUpdate_eq_transportedBlockKernel (c : EdgeConditionals B E)
    (ξ : E → OpenPath.FinProb B) (enhanced : Finset E)
    (e : E) (he : e ∈ enhanced) (auxiliary : List E)
    (haux : auxiliary.Nodup) (heaux : e ∉ auxiliary)
    (hc : ∀ f ∈ auxiliary, ∀ off, c f off = ξ f)
    (κ : (AuxiliaryIndex E e auxiliary.toFinset → B) → OpenPath.FinProb B)
    (hκ : ∀ ω : E → B, c e (fun a => ω a.1) =
      κ (((indexedBlockEquiv (β := B) e auxiliary.toFinset) ω).1.2)) (ω : E → B) :
    (FinProb.dirac ω).bind (blockUpdate c enhanced auxiliary e) =
      transportedBlockKernel (indexedBlockEquiv e auxiliary.toFinset)
        (OpenPath.FinProb.pi (fun a : AuxiliaryIndex E e auxiliary.toFinset => ξ a.1.1))
        κ ω := by
  rw [blockUpdate, blockCoordinates, if_pos he]
  rw [dirac_bind_enhanced_sweep c ξ e auxiliary haux heaux hc,
    transportedBlockKernel_eq_pi ξ e auxiliary.toFinset κ]
  congr 1
  funext f
  by_cases hfa : f ∈ auxiliary
  · have hfe : f ≠ e := by
      intro h
      subst f
      exact heaux hfa
    have hfA : f ∈ auxiliary.toFinset := List.mem_toFinset.mpr hfa
    simp [hfa, hfA, hfe]
  · have hfA : f ∉ auxiliary.toFinset := by simpa using hfa
    by_cases hfe : f = e
    · subst f
      simp [hfa, hκ ω]
    · simp [hfa, hfA, hfe, OpenPath.FinProb.pure_eq_glauberDirac]

end BlockNormalForms

end Glauber


namespace FKEnhancement

open Set
open scoped Classical BigOperators unitInterval
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- Recombine an off-edge indexed pair configuration with the upper bit closed
at the distinguished edge. -/
def pairUpperOff (e : E) (off : Glauber.OffConfig (Bool × Bool) E e) :
    Configuration E := fun f => if hf : f = e then false else (off ⟨f, hf⟩).2

/-- Extend an upper auxiliary configuration by `false` outside its index set.
The value on enhanced edges is irrelevant to closed-cutset certificates. -/
def pairAuxiliaryUpper (e : E) (A : Finset E)
    (a : JointInvariance.AuxiliaryIndex E e A → Bool × Bool) : Configuration E :=
  fun f => if hf : f = e then false else
    if hA : f ∈ A then (a ⟨⟨f, hf⟩, hA⟩).2 else false

/-- The local lower-enhanced/reference ordered pair factor. -/
def lowerCutsetLocalPair (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (e : E) : OpenPath.FinProb (Bool × Bool) :=
  boolPair (lowerEnhancedRate K enhanced p p' e) (max p p' : I)
    (lowerEnhancedRate_nonneg K enhanced hp e)
    (by simpa [max_eq_right hp] using lowerEnhancedRate_le K enhanced hp e)
    (max p p' : I).2.2

/-- Singleton conditionals for the outer enhanced ordered-pair chain.  Only an
enhanced edge may use the closed-cutset certificate. -/
def lowerCutsetPairConditionals (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') :
    Glauber.EdgeConditionals (Bool × Bool) E := by
  classical
  exact fun e off =>
    if e ∈ enhanced then
      cutsetOuterPairLaw K enhanced e p p' (pairUpperOff e off)
    else
      boolPair (p : ℝ) (p' : ℝ) p.2.1 hp p'.2.2

/-- The enhanced kernel seen from the auxiliary coordinates alone. -/
def lowerCutsetAuxKernel (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p ≤ p') (e : E) (A : Finset E)
    (a : JointInvariance.AuxiliaryIndex E e A → Bool × Bool) :
    OpenPath.FinProb (Bool × Bool) := by
  classical
  exact if HasClosedCutset K enhanced e (pairAuxiliaryUpper e A a) then
    boolPair p' p' p'.2.1 le_rfl p'.2.2
  else boolPair p p' p.2.1 hp p'.2.2

lemma hasClosedCutset_update (K : E → Configuration E → Prop)
    (enhanced : Set E) (e : E) (z : Configuration E) (b : Bool) :
    HasClosedCutset K enhanced e (Function.update z e b) ↔
      HasClosedCutset K enhanced e z := by
  constructor <;>
    rintro ⟨χ, hχ, hclosed⟩ <;>
    refine ⟨χ, hχ, ?_⟩
  · intro a ha
    have hae : a ≠ e := (hχ.1 ha).2
    simpa [Function.update_of_ne hae] using hclosed a ha
  · intro a ha
    have hae : a ≠ e := (hχ.1 ha).2
    simpa [Function.update_of_ne hae] using hclosed a ha

lemma hasClosedCutset_congr_of_aux_eq {K : E → Configuration E → Prop}
    {enhanced : Set E} {e : E} {z w : Configuration E}
    (h : ∀ a, a ∉ enhanced → a ≠ e → z a = w a) :
    HasClosedCutset K enhanced e z ↔ HasClosedCutset K enhanced e w := by
  constructor <;>
    rintro ⟨χ, hχ, hclosed⟩ <;>
    refine ⟨χ, hχ, ?_⟩
  · intro a ha
    have hs := hχ.1 ha
    rw [← h a hs.1 hs.2]
    exact hclosed a ha
  · intro a ha
    have hs := hχ.1 ha
    rw [h a hs.1 hs.2]
    exact hclosed a ha

lemma pairUpperOff_apply_aux (e : E) (ω : E → Bool × Bool)
    (a : E) (ha : a ≠ e) :
    pairUpperOff e (fun f : {f : E // f ≠ e} => ω f.1) a = (ω a).2 := by
  simp [pairUpperOff, ha]

lemma pairAuxiliaryUpper_apply (e : E) (A : Finset E)
    (a : JointInvariance.AuxiliaryIndex E e A → Bool × Bool)
    (f : E) (hfe : f ≠ e) (hfA : f ∈ A) :
    pairAuxiliaryUpper e A a f = (a ⟨⟨f, hfe⟩, hfA⟩).2 := by
  simp [pairAuxiliaryUpper, hfe, hfA]

lemma indexedBlockEquiv_aux_apply (e : E) (A : Finset E) (ω : E → Bool × Bool)
    (a : JointInvariance.AuxiliaryIndex E e A) :
    (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A) ω).1.2 a) = ω a.1.1 := rfl

/-- The enhanced singleton conditional depends on the old full configuration
only through the transported auxiliary coordinates. -/
lemma lowerCutsetPairConditionals_enhanced_aux
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (e : E) (he : e ∈ enhanced) (auxiliary : List E)
    (hA : ∀ f, f ∈ auxiliary ↔ f ∉ enhanced) (ω : E → Bool × Bool) :
    lowerCutsetPairConditionals K enhanced hp e (fun a => ω a.1) =
      lowerCutsetAuxKernel K enhanced hp e auxiliary.toFinset
        (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e
          auxiliary.toFinset) ω).1.2) := by
  simp only [lowerCutsetPairConditionals, if_pos he]
  unfold cutsetOuterPairLaw lowerCutsetAuxKernel
  have hc : HasClosedCutset K enhanced e (pairUpperOff e (fun a => ω a.1)) ↔
      HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset
        (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e
          auxiliary.toFinset) ω).1.2)) := by
    apply hasClosedCutset_congr_of_aux_eq
    intro a hae haee
    have haA : a ∈ auxiliary.toFinset := List.mem_toFinset.mpr ((hA a).mpr hae)
    rw [pairUpperOff_apply_aux e ω a haee,
      pairAuxiliaryUpper_apply e auxiliary.toFinset _ a haee haA]
    rfl
  split_ifs <;> simp_all [min_eq_left hp, max_eq_right hp]

lemma lowerCutsetPairConditionals_not_enhanced
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (e : E) (he : e ∉ enhanced) (off) :
    lowerCutsetPairConditionals K enhanced hp e off =
      lowerCutsetLocalPair K enhanced hp e := by
  simp [lowerCutsetPairConditionals, lowerCutsetLocalPair, lowerEnhancedRate,
    he, max_eq_right hp]

lemma lowerCutsetPairLaw_eq_pi (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') :
    lowerCutsetPairLaw K enhanced hp =
      OpenPath.FinProb.pi (lowerCutsetLocalPair K enhanced hp) := by
  unfold lowerCutsetPairLaw
  congr 1

end

end FKEnhancement


namespace FKEnhancement

open Set
open scoped Classical BigOperators unitInterval
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

lemma lowerCutset_auxiliaryRestriction_map (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (e : E) (A : Finset E) :
    (OpenPath.FinProb.pi (lowerCutsetLocalPair K enhanced hp)).map
      (fun w => ((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A) w).1.2) =
      OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
        lowerCutsetLocalPair K enhanced hp a.1.1) := by
  let D := JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A
  let ν := lowerCutsetLocalPair K enhanced hp
  have hdecomp := JointInvariance.map_pi_indexedBlockEquiv ν e A
  change (OpenPath.FinProb.pi ν).map D = JointInvariance.blockLaw (ν e)
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
    (OpenPath.FinProb.pi (fun r : JointInvariance.RemainingIndex E e A => ν r.1.1))
    at hdecomp
  change (OpenPath.FinProb.pi ν).map (fun w => (D w).1.2) = _
  rw [show (fun w => (D w).1.2) = (fun t => t.1.2) ∘ D from rfl,
    ← GlauberCoupling.map_map, hdecomp]
  change ((((ν e).prod (OpenPath.FinProb.pi
      (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))).prod
      (OpenPath.FinProb.pi (fun r : JointInvariance.RemainingIndex E e A => ν r.1.1))).map
      (fun t => t.1.2)) = _
  rw [show (fun t : ((Bool × Bool) ×
      (JointInvariance.AuxiliaryIndex E e A → Bool × Bool)) ×
      (JointInvariance.RemainingIndex E e A → Bool × Bool) => t.1.2) =
      Prod.snd ∘ Prod.fst from rfl, ← GlauberCoupling.map_map]
  simp
  rfl

lemma boolProduct_certificateEvent_eq_cutsetWeight (K : E → Configuration E → Prop)
    (enhanced : Set E) (p p' : I) (e : E) :
    (boolProduct (fun _ => (max p p' : I)) (fun _ => (max p p' : I).2)).event
      (certificateEvent K enhanced e) = cutsetWeight K enhanced p p' e := by
  rw [← OpenPath.FinProb.toPMF_toMeasure_toReal]
  unfold cutsetWeight certificateProbability
  rw [toPMF_boolProduct_toMeasure]

/-- The certificate average seen by an enhanced block is exactly the weight
defined from the full upper Bernoulli product. -/
theorem lowerCutset_auxCertificate_event (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p ≤ p') (e : E) (auxiliary : List E)
    (hA : ∀ f, f ∈ auxiliary ↔ f ∉ enhanced) :
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      auxiliary.toFinset => lowerCutsetLocalPair K enhanced hp a.1.1)).event
      {a | HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset a)} =
        cutsetWeight K enhanced p p' e := by
  let D := JointInvariance.indexedBlockEquiv (β := Bool × Bool) e auxiliary.toFinset
  let ν := lowerCutsetLocalPair K enhanced hp
  let R := fun w : E → Bool × Bool => (D w).1.2
  let U := fun w : E → Bool × Bool => fun e => (w e).2
  let C : Set (JointInvariance.AuxiliaryIndex E e auxiliary.toFinset → Bool × Bool) :=
    {a | HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset a)}
  have haux : (OpenPath.FinProb.pi ν).map R =
      OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e auxiliary.toFinset =>
        ν a.1.1) := lowerCutset_auxiliaryRestriction_map K enhanced hp e auxiliary.toFinset
  have hupper : (OpenPath.FinProb.pi ν).map U =
      boolProduct (fun _ => (max p p' : I)) (fun _ => (max p p' : I).2) := by
    rw [← lowerCutsetPairLaw_eq_pi]
    exact lowerCutsetPairLaw_map_snd K enhanced hp
  have hevent : R ⁻¹' C = U ⁻¹' certificateEvent K enhanced e := by
    ext w
    change HasClosedCutset K enhanced e (pairAuxiliaryUpper e auxiliary.toFinset (R w)) ↔
      HasClosedCutset K enhanced e (U w)
    apply hasClosedCutset_congr_of_aux_eq
    intro a hae haee
    have haA : a ∈ auxiliary.toFinset := List.mem_toFinset.mpr ((hA a).mpr hae)
    rw [pairAuxiliaryUpper_apply e auxiliary.toFinset (R w) a haee haA]
    rfl
  change (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
    auxiliary.toFinset => ν a.1.1)).event C = cutsetWeight K enhanced p p' e
  calc
    (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e
      auxiliary.toFinset => ν a.1.1)).event C =
        ((OpenPath.FinProb.pi ν).map R).event C := by rw [haux]
    _ = (OpenPath.FinProb.pi ν).event (R ⁻¹' C) := by
      rw [OpenPath.FinProb.event_preimage_map]
    _ = (OpenPath.FinProb.pi ν).event (U ⁻¹' certificateEvent K enhanced e) := by
      rw [hevent]
    _ = ((OpenPath.FinProb.pi ν).map U).event (certificateEvent K enhanced e) := by
      rw [OpenPath.FinProb.event_preimage_map]
    _ = (boolProduct (fun _ => (max p p' : I)) (fun _ => (max p p' : I).2)).event
        (certificateEvent K enhanced e) := by rw [hupper]
    _ = cutsetWeight K enhanced p p' e :=
      boolProduct_certificateEvent_eq_cutsetWeight K enhanced p p' e

end

end FKEnhancement


namespace Glauber

variable {α : Type*} [Fintype α]

lemma sweep_singleton (κ : α → OpenPath.FinProb α) : sweep [κ] = κ := by
  funext a
  simpa [sweep, seq] using FinProb.bind_dirac_right (κ a)

end Glauber

namespace FKEnhancement

open Set
open scoped Classical BigOperators unitInterval
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- Invariance of the stationary lower ordered pair under one enhanced block. -/
theorem lowerCutsetPairLaw_enhancedBlock_invariant
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary)
    (e : E) (he : e ∈ enhanced) :
    Glauber.Invariant (lowerCutsetPairLaw K enhanced hp)
      (Glauber.blockUpdate (lowerCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e) := by
  let ν := lowerCutsetLocalPair K enhanced hp
  let A := auxiliary.toFinset
  let C : Set (JointInvariance.AuxiliaryIndex E e A → Bool × Bool) :=
    {a | HasClosedCutset K enhanced e (pairAuxiliaryUpper e A a)}
  have hA : ∀ f, f ∈ auxiliary ↔ f ∉ enhanced := by
    intro f
    rw [haux.2 f]
    simp
  have he' : e ∈ enhanced.toFinset := Set.mem_toFinset.mpr he
  have heaux : e ∉ auxiliary := by
    intro h
    exact (hA e).mp h he
  have hC : (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
      ν a.1.1)).event C = cutsetWeight K enhanced p p' e := by
    exact lowerCutset_auxCertificate_event K enhanced hp e auxiliary hA
  have hνe : ν e = boolPair
      ((p : ℝ) + closedCutsetEnhancement p p'
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event C)) p'
      (add_nonneg p.2.1 (mul_nonneg (abs_nonneg _)
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1))
      (enhancedOpenRate_le p.2.1 hp
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).1
        ((OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A =>
          ν a.1.1)).event_mem_Icc C).2) p'.2.2 := by
    change lowerCutsetLocalPair K enhanced hp e = _
    apply OpenPath.FinProb.ext
    rintro ⟨i, j⟩
    cases i <;> cases j <;>
      simp [boolPair, lowerCutsetLocalPair, lowerEnhancedRate, he,
        max_eq_right hp, cutsetEpsilon, hC]
  have hstat := pi_lowerBoolPair_invariant ν e A C (p : ℝ) (p' : ℝ)
    p.2.1 p'.2.2 hp hνe
  have hc : ∀ f ∈ auxiliary, ∀ off,
      lowerCutsetPairConditionals K enhanced hp f off = ν f := by
    intro f hf off
    exact lowerCutsetPairConditionals_not_enhanced K enhanced hp f ((hA f).mp hf) off
  have hκ : ∀ ω : E → Bool × Bool,
      lowerCutsetPairConditionals K enhanced hp e (fun a => ω a.1) =
        lowerCutsetAuxKernel K enhanced hp e A
          (((JointInvariance.indexedBlockEquiv (β := Bool × Bool) e A) ω).1.2) := by
    intro ω
    exact lowerCutsetPairConditionals_enhanced_aux K enhanced hp e he auxiliary hA ω
  have hlift := Glauber.dirac_blockUpdate_eq_transportedBlockKernel
    (lowerCutsetPairConditionals K enhanced hp) ν enhanced.toFinset e he' auxiliary
    haux.1 heaux hc (lowerCutsetAuxKernel K enhanced hp e A) hκ
  unfold Glauber.Invariant
  rw [lowerCutsetPairLaw_eq_pi]
  change (OpenPath.FinProb.pi ν).bind _ = OpenPath.FinProb.pi ν
  calc
    (OpenPath.FinProb.pi ν).bind
        (Glauber.blockUpdate (lowerCutsetPairConditionals K enhanced hp)
          enhanced.toFinset auxiliary e) =
      (OpenPath.FinProb.pi ν).bind
        (JointInvariance.transportedBlockKernel
          (JointInvariance.indexedBlockEquiv e A)
          (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
          (lowerCutsetAuxKernel K enhanced hp e A)) := by
      congr 1
      funext ω
      simpa using hlift ω
    _ = OpenPath.FinProb.pi ν := by
      change (OpenPath.FinProb.pi ν).bind
        (JointInvariance.transportedBlockKernel
          (JointInvariance.indexedBlockEquiv e A)
          (OpenPath.FinProb.pi (fun a : JointInvariance.AuxiliaryIndex E e A => ν a.1.1))
          (fun a => if HasClosedCutset K enhanced e (pairAuxiliaryUpper e A a) then
            boolPair p' p' p'.2.1 le_rfl p'.2.2
            else boolPair p p' p.2.1 hp p'.2.2)) = OpenPath.FinProb.pi ν
      simpa [C] using hstat

/-- The lower ordered product is invariant for every actual modified-block
clock update. -/
theorem lowerCutsetPairLaw_blockUpdate_invariant
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) (e : E) :
    Glauber.Invariant (lowerCutsetPairLaw K enhanced hp)
      (Glauber.blockUpdate (lowerCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e) := by
  by_cases he : e ∈ enhanced
  · exact lowerCutsetPairLaw_enhancedBlock_invariant K enhanced hp auxiliary haux e he
  · let ν := lowerCutsetLocalPair K enhanced hp
    unfold Glauber.Invariant
    rw [lowerCutsetPairLaw_eq_pi]
    change (OpenPath.FinProb.pi ν).bind _ = OpenPath.FinProb.pi ν
    have hblock : Glauber.blockUpdate (lowerCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e =
        Glauber.edgeUpdate (lowerCutsetPairConditionals K enhanced hp) e := by
      simp [Glauber.blockUpdate, Glauber.blockCoordinates, he, Glauber.sweep_singleton]
    rw [hblock, Glauber.pi_bind_edgeUpdate_const ν
      (lowerCutsetPairConditionals K enhanced hp) e (ν e)
      (lowerCutsetPairConditionals_not_enhanced K enhanced hp e he)]
    simp

/-- Stationary pair equation for the actual lower modified jump chain. -/
theorem lowerCutsetPairLaw_modifiedJump_invariant
    (K : E → Configuration E → Prop) (enhanced : Set E) {p p' : I}
    (hp : p ≤ p') (ρ : OpenPath.FinProb E) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) :
    Glauber.Invariant (lowerCutsetPairLaw K enhanced hp)
      (Glauber.modifiedJump ρ (lowerCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary) := by
  apply Glauber.mixture_invariant
  intro e
  exact lowerCutsetPairLaw_blockUpdate_invariant K enhanced hp auxiliary haux e

end

end FKEnhancement
