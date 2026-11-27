import FK.AGLocalPivotMSS

/-!
# Cylinder-scale local pivot estimates for essential enhancement

For an arbitrary ambient coordinate type, every approximating event is required
to be a genuine cylinder.  Its derivative and expected pivot sums are computed
on the finite support.  The repaired mean-value argument is then run on the
ambient profile, with no finite-coordinate assumption on the target event.
-/

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal Topology

namespace FK.AGLocalPivot.Cylinder

open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- Continuity of an ambient cylinder mass follows from its finite-support
restriction. -/
theorem continuous_massPair_cylinder {E : Type u} [DecidableEq E]
    (A : Set (E → Bool)) (S : Set E) (support : Finset E)
    (hdep : FKLimit.DependsOnCoordinates A support) :
    Continuous (massPair A S) := by
  have hfun : massPair A S =
      massPair (E := support) (support.restrict '' A)
        {e : support | (e : E) ∈ S} := by
    funext u
    exact mass_eq_mass_restrict A S support hdep u.1 u.2
  rw [hfun]
  exact continuous_massPair _ _

/-- Strict decrement shift on an arbitrary ambient edge type.  All pivot
sums are on the finite support of the corresponding cylinder event. -/
theorem exists_subcritical_shift_cylinder_window
    {E : Type u} [Countable E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (support : ℕ → Finset E)
    (hdep : ∀ n, FKLimit.DependsOnCoordinates (An n) (support n))
    (pc c E₀ : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (htrade : ∀ (n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
      0 < ε → ε ≤ E₀ → ε < b →
      c * pivotTotal (fun a : support n => decWeight S a.val (b, ε))
          ((support n).restrict '' An n) ≤
        pivotOn {e : support n | (e : E) ∈ S}
          (fun a : support n => decWeight S a.val (b, ε)) ((support n).restrict '' An n))
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2) (hε1 : ε < (1 - pc) / 2)
    (hεE₀ : ε ≤ E₀) :
    ∃ b, pc < b ∧ b ≤ 1 ∧ ε ≤ b ∧ mass A S b ε = 0 := by
  set b₀ : ℝ := pc - c * ε / 2 with hb₀
  set b₁ : ℝ := pc + c * ε / 2 with hb₁
  have hcε : 0 < c * ε := mul_pos hc0 hε0
  have hb₀pc2 : pc / 2 ≤ b₀ := by rw [hb₀]; nlinarith
  have hb₀0 : 0 < b₀ := by rw [hb₀]; nlinarith
  have hb₀pc : b₀ < pc := by rw [hb₀]; nlinarith
  have hb₁pc : pc < b₁ := by rw [hb₁]; nlinarith
  have hb₁1 : b₁ ≤ 1 := by rw [hb₁]; nlinarith
  have hεb₁ : ε ≤ b₁ := by rw [hb₁]; nlinarith
  refine ⟨b₁, hb₁pc, hb₁1, hεb₁, ?_⟩
  have hb0t : ∀ t : ℝ, 0 < t → t ≤ ε → 0 < b₀ + c * t := by
    intro t ht0 _
    nlinarith [mul_pos hc0 ht0]
  have hb1t : ∀ t : ℝ, 0 < t → t ≤ ε → b₀ + c * t < 1 := by
    intro t _ htε
    have hct : c * t ≤ c * ε := by nlinarith
    have hb₀eq : b₀ + c * ε = b₁ := by rw [hb₀, hb₁]; ring
    nlinarith
  have hεt : ∀ t : ℝ, t ∈ Ioo (0:ℝ) ε → t < b₀ + c * t := by
    intro t ht
    have ht_pc : t < pc / 2 := lt_of_lt_of_le ht.2 hεpc.le
    have h1 : t < b₀ := by rw [hb₀]; nlinarith
    nlinarith [mul_pos hc0 ht.1]
  have hstep : ∀ n, mass (An n) S b₁ ε ≤ mass (An n) S b₀ 0 := by
    intro n
    have hcont : ContinuousOn
        ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) (Icc 0 ε) :=
      ((continuous_massPair_cylinder (An n) S (support n) (hdep n)).comp
        (by fun_prop : Continuous fun s : ℝ => (b₀ + c * s, 0 + 1 * s))).continuousOn
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s))
          ((tradeCLM
            (pivotTotal (fun a : support n => decWeight S a.val
              (b₀ + c * t, 0 + 1 * t)) ((support n).restrict '' An n))
            (pivotOn {e : support n | (e : E) ∈ S}
              (fun a : support n => decWeight S a.val (b₀ + c * t, 0 + 1 * t))
              ((support n).restrict '' An n))) (c, 1)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hbt0 : 0 < b₀ + c * t := hb0t t ht0 htε.le
      have hbt1 : b₀ + c * t < 1 := hb1t t ht0 htε.le
      have hεtt : 0 + 1 * t < b₀ + c * t := by simpa using hεt t ht
      have hle : (0:ℝ) ≤ 0 + 1 * t := by linarith
      have hF := massPair_deriv_decomp_cylinder (hAn n) S (support n) (hdep n)
        hbt0 hbt1 hle hεtt
      have hline : HasDerivAt (fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) (c, (1:ℝ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => b₀ + c * s) c t := by
          simpa using (hasDerivAt_const_mul (x := t) c).const_add b₀
        have h2 : HasDerivAt (fun s : ℝ => (0:ℝ) + 1 * s) 1 t := by
          simpa using (hasDerivAt_id (x := t)).const_add (0:ℝ)
        exact h1.prodMk h2
      exact hF.comp_hasDerivAt t hline
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        ((tradeCLM
          (pivotTotal (fun a : support n => decWeight S a.val
            (b₀ + c * t, 0 + 1 * t)) ((support n).restrict '' An n))
          (pivotOn {e : support n | (e : E) ∈ S}
            (fun a : support n => decWeight S a.val (b₀ + c * t, 0 + 1 * t))
            ((support n).restrict '' An n))) (c, 1)) ≤ 0 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hpos : (0:ℝ) < 0 + 1 * t := by linarith
      have hlt : 0 + 1 * t < b₀ + c * t := by simpa using hεt t ht
      have hεE₀t : 0 + 1 * t ≤ E₀ := by
        have : t ≤ ε := ht.2.le
        linarith
      have hmem : b₀ + c * t ∈ Icc (pc / 2) ((1 + pc) / 2) := by
        constructor
        · nlinarith [hb₀pc2, mul_nonneg hc0.le ht0.le]
        · nlinarith [hb₀, ht.2.le, hc1, hε1, hε0.le, hc0.le]
      exact tradeCLM_trade_nonpos _ _ c (htrade n _ _ hmem hpos hεE₀t hlt)
    have hval := le_of_deriv_nonpos hε0 hderiv' hcont hbound
    have h₁ : ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) ε =
        mass (An n) S b₁ ε := by
      change mass (An n) S (b₀ + c * ε) (0 + 1 * ε) = mass (An n) S b₁ ε
      rw [show b₀ + c * ε = b₁ by rw [hb₀, hb₁]; ring,
        show 0 + 1 * ε = ε by ring]
    have h₀ : ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) 0 =
        mass (An n) S b₀ 0 := by
      change mass (An n) S (b₀ + c * 0) (0 + 1 * 0) = mass (An n) S b₀ 0
      norm_num
    rw [h₁, h₀] at hval
    exact hval
  have hub : mass A S b₁ ε ≤ mass A S b₀ 0 :=
    le_of_tendsto_of_tendsto (hconv b₁ ε) (hconv b₀ 0) (Eventually.of_forall hstep)
  rw [hbase b₀ hb₀0.le hb₀pc] at hub
  exact le_antisymm hub (mass_nonneg A S b₁ ε)

end FK.AGLocalPivot.Cylinder


namespace FK.AGLocalPivot.Cylinder

open Set MeasureTheory Filter
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- The decrement `hAG` input from a uniform trade on cylinder supports. -/
theorem decrement_AGInput_of_cylinder_windowTrade
    {E : Type u} [Countable E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (support : ℕ → Finset E)
    (hdep : ∀ n, FKLimit.DependsOnCoordinates (An n) (support n))
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (hwindow : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → ε < b →
        c * pivotTotal (fun a : support n => decWeight S a.val (b, ε))
            ((support n).restrict '' An n) ≤
          pivotOn {e : support n | (e : E) ∈ S}
            (fun a : support n => decWeight S a.val (b, ε)) ((support n).restrict '' An n))
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < pc / 2 →
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
  obtain ⟨c, hc0, hc1, htrade⟩ := hwindow
  intro ε hε0 hεpc
  set E₀ : ℝ := min (pc / 4) ((1 - pc) / 4) with hE₀
  set ε' : ℝ := min ε E₀ with hε'
  have hE₀pos : 0 < E₀ := lt_min (by linarith) (by linarith)
  have hε'0 : 0 < ε' := lt_min hε0 hE₀pos
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'E₀ : ε' ≤ E₀ := min_le_right _ _
  have hε'pc : ε' < pc / 2 := lt_of_le_of_lt hε'ε hεpc
  have hε'1 : ε' < (1 - pc) / 2 := by
    have h1 : E₀ ≤ (1 - pc) / 4 := min_le_right _ _
    have h2 : ε' ≤ (1 - pc) / 4 := hε'E₀.trans h1
    linarith
  obtain ⟨b, hpcb, hb1, hε'b, hmass⟩ :=
    exists_subcritical_shift_cylinder_window A An S support hdep pc c E₀ hpc0 hpc1
      hc0 hc1 hAn (fun n b ε hb hε0 hεE₀ hεb =>
        have hmem := hb
        have hsmall : ε ≤ min (pc / 4) ((1 - pc) / 4) := hεE₀
        htrade n b ε hmem hε0 hsmall hεb)
      hconv hbase ε' hε'0 hε'pc hε'1 hε'E₀
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  have hεb : ε ≤ b := by linarith
  refine ⟨b, hpcb, hb1, hεb, ?_⟩
  have hmono : mass A S b ε ≤ mass A S b ε' := mass_anti_decrement hA hmeas S hε'ε
  have hzero : mass A S b ε = 0 :=
    le_antisymm (by rw [hmass] at hmono; exact hmono) (mass_nonneg A S b ε)
  have hm : ((FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
      hb0 hb1 hε0.le hεb) : Measure (E → Bool)) A) = 0 := by
    have h := hzero
    rw [mass_eq_decrementProfile A S hb0 hb1 hε0.le hεb] at h
    rcases (ENNReal.toReal_eq_zero_iff _).mp h with h' | h'
    · exact h'
    · exact absurd h' (measure_ne_top _ _)
  exact hm

/-- The decrement rate restricted to an approximation's cylinder support. -/
noncomputable def decrementSupportRate {E : Type u} {pc : ℝ} (S : Set E)
    (support : ℕ → Finset E) (p : DecrementPoint pc) (e : support p.n) : ℝ :=
  decWeight S e.val (p.b, p.ε)

/-- The support-restricted decrement rate is a Bernoulli parameter. -/
lemma decrementSupportRate_mem {E : Type u} {pc : ℝ} (S : Set E)
    (support : ℕ → Finset E) (p : DecrementPoint pc) (e : support p.n) :
    decrementSupportRate S support p e ∈ Icc (0 : ℝ) 1 := by
  exact ⟨PivotTradeAGRepair.decWeight_nonneg _ _, PivotTradeAGRepair.decWeight_le_one _ _⟩

/-- Uniform cylinder-support pivot trade from actual local modification maps. -/
theorem exists_decrement_cylinder_windowTrade_of_local_modifications
    {E : Type u} [Countable E] [DecidableEq E]
    (An : ℕ → Set (E → Bool)) (S : Set E) (support : ℕ → Finset E)
    (pc : ℝ)
    (R : (p : DecrementPoint pc) → support p.n → Finset (support p.n))
    (candidate : (p : DecrementPoint pc) → support p.n → Finset (support p.n))
    (T : (p : DecrementPoint pc) → (e : support p.n) →
      (support p.n → Bool) → (support p.n → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : DecrementPoint pc) (e : support p.n) b,
      δ ≤ coordinateWeight (decrementSupportRate S support p e) b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hcand : ∀ p e z, z ∈ candidate p e → (z : E) ∈ S)
    (hmap : ∀ p e ω, Pivotal ((support p.n).restrict '' An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal ((support p.n).restrict '' An p.n) z (T p e ω))
    (hmultiplicity : ∀ (p : DecrementPoint pc) (z : support p.n),
      Nat.card {e // z ∈ candidate p e} ≤ K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → ε < b →
        c * pivotTotal (fun a : support n => decWeight S a.val (b, ε))
            ((support n).restrict '' An n) ≤
          pivotOn {e : support n | (e : E) ∈ S}
            (fun a : support n => decWeight S a.val (b, ε)) ((support n).restrict '' An n) := by
  obtain ⟨c, hc0, hc1, hnormal⟩ := exists_pivotTrade_constant (N := N) (K := K) hK hδ0 hδ1
  refine ⟨c, hc0, hc1, ?_⟩
  intro n b ε hb hε0 hε hεb
  let p : DecrementPoint pc := ⟨n, b, ε, hb, hε0, hε, hεb⟩
  apply hnormal
  let r : support n → ℝ := decrementSupportRate S support p
  have hr : ∀ e, r e ∈ Icc (0 : ℝ) 1 := decrementSupportRate_mem S support p
  let cand : support n → Finset {z : support n // (z : E) ∈ S} := fun e =>
    Finset.subtype (fun z : support n => (z : E) ∈ S) (candidate p e)
  have hmap' : ∀ e ω, Pivotal ((support n).restrict '' An n) e ω →
      ∃ z ∈ cand e, Pivotal ((support n).restrict '' An n) z.1 (T p e ω) := by
    intro e ω hω
    obtain ⟨z, hz, hzpiv⟩ := hmap p e ω hω
    refine ⟨⟨z, hcand p e z hz⟩, Finset.mem_subtype.mpr hz, hzpiv⟩
  have hmult' : ∀ z : {z : support n // (z : E) ∈ S}, Nat.card {e // z ∈ cand e} ≤ K := by
    intro z
    have heq : Nat.card {e // z ∈ cand e} = Nat.card {e // z.1 ∈ candidate p e} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun e => by simp [cand])
    rw [heq]
    exact hmultiplicity p z.1
  have h := pivotTrade_of_local_modifications
    (r := r) (hr := hr) (A := (support n).restrict '' An n)
    (S := {e : support n | (e : E) ∈ S}) (R := R p) (candidate := cand) (T := T p)
    (N := N) (K := K) (δ := δ) hδ0.le hδ1
    (by
      intro e bit
      simpa only [boolLaw, coordinateWeight] using hδlaw p e bit)
    (hsupport p) (hlocal p) hmap' hmult'
  have hr_eq : decrementSupportRate S support p =
      (fun a : support n => decWeight S a.val (b, ε)) := by
    rfl
  rw [show r = (fun a : support n => decWeight S a.val (b, ε)) from hr_eq] at h
  exact h

end FK.AGLocalPivot.Cylinder


namespace FK.AGLocalPivot.Cylinder

open Set MeasureTheory Filter
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- **General-countable-coordinate subcritical AG analytic shift.**  The target
`A` and every cylinder `An n` live on the same ambient edge type.  Local maps
are required only on the finite supports. -/
theorem decrement_AGInput_of_cylinder_local_modifications
    {E : Type u} [Countable E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (support : ℕ → Finset E)
    (hdep : ∀ n, FKLimit.DependsOnCoordinates (An n) (support n))
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (R : (p : DecrementPoint pc) → support p.n → Finset (support p.n))
    (candidate : (p : DecrementPoint pc) → support p.n → Finset (support p.n))
    (T : (p : DecrementPoint pc) → (e : support p.n) →
      (support p.n → Bool) → (support p.n → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : DecrementPoint pc) (e : support p.n) b,
      δ ≤ coordinateWeight (decrementSupportRate S support p e) b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hcand : ∀ p e z, z ∈ candidate p e → (z : E) ∈ S)
    (hmap : ∀ p e ω, Pivotal ((support p.n).restrict '' An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal ((support p.n).restrict '' An p.n) z (T p e ω))
    (hmultiplicity : ∀ (p : DecrementPoint pc) (z : support p.n),
      Nat.card {e // z ∈ candidate p e} ≤ K)
    (hAn : ∀ n, IsUpperSet (An n))
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < pc / 2 →
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
  have hwindow := exists_decrement_cylinder_windowTrade_of_local_modifications
    An S support pc R candidate T N K hK δ hδ0 hδ1 hδlaw hsupport hlocal
      hcand hmap hmultiplicity
  exact decrement_AGInput_of_cylinder_windowTrade A An S support hdep pc hpc0 hpc1
    hAn hwindow hconv hbase hA hmeas

end FK.AGLocalPivot.Cylinder


namespace FK.AGLocalPivot.Cylinder

open Set MeasureTheory Filter
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- Continuity of an ambient cylinder increment mass. -/
theorem continuous_incMassPair_cylinder {E : Type u} [DecidableEq E]
    (A : Set (E → Bool)) (S : Set E) (support : Finset E)
    (hdep : FKLimit.DependsOnCoordinates A support) :
    Continuous (incMassPair A S) := by
  have hfun : incMassPair A S =
      incMassPair (E := support) (support.restrict '' A)
        {e : support | (e : E) ∈ S} := by
    funext u
    exact incMass_eq_incMass_restrict A S support hdep u.1 u.2
  rw [hfun]
  exact continuous_incMassPair _ _

/-- Strict increment shift on an arbitrary ambient edge type. -/
theorem exists_supercritical_shift_cylinder_window
    {E : Type u} [Countable E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (support : ℕ → Finset E)
    (hdep : ∀ n, FKLimit.DependsOnCoordinates (An n) (support n))
    (pc c E₀ : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (htrade : ∀ (n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
      0 < ε → ε ≤ E₀ → a + ε < 1 →
      c * pivotTotal (fun a' : support n => incWeight S a'.val (a, ε))
          ((support n).restrict '' An n) ≤
        pivotOn {e : support n | (e : E) ∈ S}
          (fun a' : support n => incWeight S a'.val (a, ε)) ((support n).restrict '' An n))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1 - pc) / 2) (hεpc : ε < pc / 2)
    (hεE₀ : ε ≤ E₀) :
    ∃ a, 0 ≤ a ∧ a < pc ∧ a + ε ≤ 1 ∧ incMass A S a ε = 1 := by
  set a₀ : ℝ := pc + c * ε / 2 with ha₀
  set a₁ : ℝ := pc - c * ε / 2 with ha₁
  have hcε : 0 < c * ε := mul_pos hc0 hε0
  have ha₀pc : pc < a₀ := by rw [ha₀]; nlinarith
  have ha₀1 : a₀ < 1 := by rw [ha₀]; nlinarith
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; nlinarith
  have ha₁pc : a₁ < pc := by rw [ha₁]; nlinarith
  have hεa₁ : a₁ + ε ≤ 1 := by rw [ha₁]; nlinarith
  refine ⟨a₁, ha₁0, ha₁pc, hεa₁, ?_⟩
  have ha0t : ∀ t : ℝ, 0 < t → t ≤ ε → 0 < a₀ + (-c) * t := by
    intro t _ _
    nlinarith [mul_pos hc0 (show (0:ℝ) < t by linarith)]
  have ha1t : ∀ t : ℝ, 0 < t → t ≤ ε → a₀ + (-c) * t < 1 := by
    intro t _ htε
    nlinarith
  have hsumt : ∀ t : ℝ, t ∈ Ioo (0:ℝ) ε → a₀ + (-c) * t + (0 + 1 * t) < 1 := by
    intro t ht
    have hct : (0:ℝ) < t := ht.1
    have htε : t < ε := ht.2
    nlinarith
  have hstep : ∀ n, incMass (An n) S a₁ ε ≥ incMass (An n) S a₀ 0 := by
    intro n
    have hcont : ContinuousOn
        ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) (Icc 0 ε) :=
      ((continuous_incMassPair_cylinder (An n) S (support n) (hdep n)).comp
        (by fun_prop : Continuous fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))).continuousOn
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))
          ((incTradeCLM (pivotTotal (fun a' : support n => incWeight S a'.val
              (a₀ + (-c) * t, 0 + 1 * t)) ((support n).restrict '' An n))
            (pivotOn {e : support n | (e : E) ∈ S}
              (fun a' : support n => incWeight S a'.val (a₀ + (-c) * t, 0 + 1 * t))
              ((support n).restrict '' An n))) (-c, 1)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hat0 : 0 < a₀ + (-c) * t := ha0t t ht0 htε.le
      have hat1 : a₀ + (-c) * t < 1 := ha1t t ht0 htε.le
      have hsum : a₀ + (-c) * t + (0 + 1 * t) < 1 := hsumt t ht
      have hle : (0:ℝ) ≤ 0 + 1 * t := by linarith
      have hF := incMassPair_deriv_decomp_cylinder (hAn n) S (support n) (hdep n)
        hat0 hat1 hle hsum
      have hline : HasDerivAt (fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) ((-c), (1:ℝ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => a₀ + (-c) * s) (-c) t := by
          simpa using (hasDerivAt_const_mul (x := t) (-c)).const_add a₀
        have h2 : HasDerivAt (fun s : ℝ => (0:ℝ) + 1 * s) 1 t := by
          simpa using (hasDerivAt_id (x := t)).const_add (0:ℝ)
        exact h1.prodMk h2
      exact hF.comp_hasDerivAt t hline
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        0 ≤ ((incTradeCLM (pivotTotal (fun a' : support n => incWeight S a'.val
              (a₀ + (-c) * t, 0 + 1 * t)) ((support n).restrict '' An n))
            (pivotOn {e : support n | (e : E) ∈ S}
              (fun a' : support n => incWeight S a'.val (a₀ + (-c) * t, 0 + 1 * t))
              ((support n).restrict '' An n))) (-c, 1)) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hpos : (0:ℝ) < 0 + 1 * t := by linarith
      have hsum : a₀ + (-c) * t + (0 + 1 * t) < 1 := hsumt t ht
      have hεE₀t : 0 + 1 * t ≤ E₀ := by linarith [ht.2.le]
      have hmem : a₀ + (-c) * t ∈ Icc (pc / 2) ((1 + pc) / 2) := by
        constructor
        · nlinarith [ha₀, ha₁, ht.2.le, hc1, hε0.le, hc0.le]
        · nlinarith [ha₀, ha₀1, ht.1.le, hc0.le]
      exact incTradeCLM_trade_nonneg _ _ c (htrade n _ _ hmem hpos hεE₀t hsum)
    have hval := le_of_deriv_nonneg hε0 hderiv' hcont hbound
    have h₁ : ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) ε =
        incMass (An n) S a₁ ε := by
      change incMass (An n) S (a₀ + (-c) * ε) (0 + 1 * ε) = incMass (An n) S a₁ ε
      rw [show a₀ + (-c) * ε = a₁ by rw [ha₀, ha₁]; ring,
        show 0 + 1 * ε = ε by ring]
    have h₀ : ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) 0 =
        incMass (An n) S a₀ 0 := by
      change incMass (An n) S (a₀ + (-c) * 0) (0 + 1 * 0) = incMass (An n) S a₀ 0
      norm_num
    rw [h₁, h₀] at hval
    exact hval
  have hlow : incMass A S a₀ 0 ≤ incMass A S a₁ ε :=
    le_of_tendsto_of_tendsto (hconv a₀ 0) (hconv a₁ ε) (Eventually.of_forall hstep)
  rw [hbase a₀ ha₀pc ha₀1.le] at hlow
  exact le_antisymm (incMass_le_one A S a₁ ε) hlow

/-- The increment `hAG` input from a uniform trade on cylinder supports. -/
theorem increment_AGInput_of_cylinder_windowTrade
    {E : Type u} [Countable E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (support : ℕ → Finset E)
    (hdep : ∀ n, FKLimit.DependsOnCoordinates (An n) (support n))
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (hwindow : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → a + ε < 1 →
        c * pivotTotal (fun a' : support n => incWeight S a'.val (a, ε))
            ((support n).restrict '' An n) ≤
          pivotOn {e : support n | (e : E) ∈ S}
            (fun a' : support n => incWeight S a'.val (a, ε)) ((support n).restrict '' An n))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < (1 - pc) / 2 →
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ _hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
          ha0 hε0.le haε1) : Measure (E → Bool)) A = 1 := by
  obtain ⟨c, hc0, hc1, htrade⟩ := hwindow
  intro ε hε0 hεpc
  set E₀ : ℝ := min (pc / 4) ((1 - pc) / 4) with hE₀
  set ε' : ℝ := min ε E₀ with hε'
  have hE₀pos : 0 < E₀ := lt_min (by linarith) (by linarith)
  have hε'0 : 0 < ε' := lt_min hε0 hE₀pos
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'E₀ : ε' ≤ E₀ := min_le_right _ _
  have hε'pc : ε' < pc / 2 := by
    have h1 : E₀ ≤ pc / 4 := by rw [hE₀]; exact min_le_left _ _
    have h2 : ε' ≤ pc / 4 := hε'E₀.trans h1
    linarith
  have hε'1 : ε' < (1 - pc) / 2 := by
    have h1 : E₀ ≤ (1 - pc) / 4 := by rw [hE₀]; exact min_le_right _ _
    have h2 : ε' ≤ (1 - pc) / 4 := hε'E₀.trans h1
    linarith
  obtain ⟨a, ha0, hapc, haε1, hmass⟩ :=
    exists_supercritical_shift_cylinder_window A An S support hdep pc c E₀ hpc0 hpc1
      hc0 hc1 hAn (fun n a ε ha hε0 hεE₀ haε => htrade n a ε ha hε0 hεE₀ haε)
      hconv hbase ε' hε'0 hε'1 hε'pc hε'E₀
  have haε1' : a + ε ≤ 1 := by linarith
  refine ⟨a, ha0, hapc, haε1', ?_⟩
  have hmono : incMass A S a ε' ≤ incMass A S a ε := incMass_mono_increment hA hmeas S hε'ε
  have hone : incMass A S a ε = 1 :=
    le_antisymm (incMass_le_one A S a ε) (by rw [hmass] at hmono; exact hmono)
  have hm : ((FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
      ha0 hε0.le haε1') : Measure (E → Bool)) A) = 1 := by
    have h := hone
    rw [incMass_eq_incrementProfile A S ha0 hε0.le haε1'] at h
    exact (ENNReal.toReal_eq_one_iff _).mp h
  exact hm

end FK.AGLocalPivot.Cylinder


namespace FK.AGLocalPivot.Cylinder

open Set MeasureTheory Filter
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- The increment rate restricted to an approximation's cylinder support. -/
noncomputable def incrementSupportRate {E : Type u} {pc : ℝ} (S : Set E)
    (support : ℕ → Finset E) (p : IncrementPoint pc) (e : support p.n) : ℝ :=
  incWeight S e.val (p.a, p.ε)

/-- The support-restricted increment rate is a Bernoulli parameter. -/
lemma incrementSupportRate_mem {E : Type u} {pc : ℝ} (S : Set E)
    (support : ℕ → Finset E) (p : IncrementPoint pc) (e : support p.n) :
    incrementSupportRate S support p e ∈ Icc (0 : ℝ) 1 := by
  exact PivotTradeAGRepairIncrement.incWeight_mem _ _

/-- Uniform increment-window trade from local modification maps on the actual
cylinder supports. -/
theorem exists_increment_cylinder_windowTrade_of_local_modifications
    {E : Type u} [Countable E] [DecidableEq E]
    (An : ℕ → Set (E → Bool)) (S : Set E) (support : ℕ → Finset E)
    (pc : ℝ)
    (R : (p : IncrementPoint pc) → support p.n → Finset (support p.n))
    (candidate : (p : IncrementPoint pc) → support p.n → Finset (support p.n))
    (T : (p : IncrementPoint pc) → (e : support p.n) →
      (support p.n → Bool) → (support p.n → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : IncrementPoint pc) (e : support p.n) b,
      δ ≤ coordinateWeight (incrementSupportRate S support p e) b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hcand : ∀ p e z, z ∈ candidate p e → (z : E) ∈ S)
    (hmap : ∀ p e ω, Pivotal ((support p.n).restrict '' An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal ((support p.n).restrict '' An p.n) z (T p e ω))
    (hmultiplicity : ∀ (p : IncrementPoint pc) (z : support p.n),
      Nat.card {e // z ∈ candidate p e} ≤ K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → a + ε < 1 →
        c * pivotTotal (fun a' : support n => incWeight S a'.val (a, ε))
            ((support n).restrict '' An n) ≤
          pivotOn {e : support n | (e : E) ∈ S}
            (fun a' : support n => incWeight S a'.val (a, ε)) ((support n).restrict '' An n) := by
  obtain ⟨c, hc0, hc1, hnormal⟩ := exists_pivotTrade_constant (N := N) (K := K) hK hδ0 hδ1
  refine ⟨c, hc0, hc1, ?_⟩
  intro n a ε ha hε0 hε haε
  let p : IncrementPoint pc := ⟨n, a, ε, ha, hε0, hε, haε⟩
  apply hnormal
  let r : support n → ℝ := incrementSupportRate S support p
  have hr : ∀ e, r e ∈ Icc (0 : ℝ) 1 := incrementSupportRate_mem S support p
  let cand : support n → Finset {z : support n // (z : E) ∈ S} := fun e =>
    Finset.subtype (fun z : support n => (z : E) ∈ S) (candidate p e)
  have hmap' : ∀ e ω, Pivotal ((support n).restrict '' An n) e ω →
      ∃ z ∈ cand e, Pivotal ((support n).restrict '' An n) z.1 (T p e ω) := by
    intro e ω hω
    obtain ⟨z, hz, hzpiv⟩ := hmap p e ω hω
    refine ⟨⟨z, hcand p e z hz⟩, Finset.mem_subtype.mpr hz, hzpiv⟩
  have hmult' : ∀ z : {z : support n // (z : E) ∈ S}, Nat.card {e // z ∈ cand e} ≤ K := by
    intro z
    have heq : Nat.card {e // z ∈ cand e} = Nat.card {e // z.1 ∈ candidate p e} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun e => by simp [cand])
    rw [heq]
    exact hmultiplicity p z.1
  have h := pivotTrade_of_local_modifications
    (r := r) (hr := hr) (A := (support n).restrict '' An n)
    (S := {e : support n | (e : E) ∈ S}) (R := R p) (candidate := cand) (T := T p)
    (N := N) (K := K) (δ := δ) hδ0.le hδ1
    (by
      intro e bit
      simpa only [boolLaw, coordinateWeight] using hδlaw p e bit)
    (hsupport p) (hlocal p) hmap' hmult'
  have hr_eq : incrementSupportRate S support p =
      (fun a' : support n => incWeight S a'.val (a, ε)) := by
    rfl
  rw [show r = (fun a' : support n => incWeight S a'.val (a, ε)) from hr_eq] at h
  exact h

/-- **General-countable-coordinate supercritical AG analytic shift.** -/
theorem increment_AGInput_of_cylinder_local_modifications
    {E : Type u} [Countable E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (support : ℕ → Finset E)
    (hdep : ∀ n, FKLimit.DependsOnCoordinates (An n) (support n))
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (R : (p : IncrementPoint pc) → support p.n → Finset (support p.n))
    (candidate : (p : IncrementPoint pc) → support p.n → Finset (support p.n))
    (T : (p : IncrementPoint pc) → (e : support p.n) →
      (support p.n → Bool) → (support p.n → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : IncrementPoint pc) (e : support p.n) b,
      δ ≤ coordinateWeight (incrementSupportRate S support p e) b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hcand : ∀ p e z, z ∈ candidate p e → (z : E) ∈ S)
    (hmap : ∀ p e ω, Pivotal ((support p.n).restrict '' An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal ((support p.n).restrict '' An p.n) z (T p e ω))
    (hmultiplicity : ∀ (p : IncrementPoint pc) (z : support p.n),
      Nat.card {e // z ∈ candidate p e} ≤ K)
    (hAn : ∀ n, IsUpperSet (An n))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < (1 - pc) / 2 →
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ _hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
          ha0 hε0.le haε1) : Measure (E → Bool)) A = 1 := by
  have hwindow := exists_increment_cylinder_windowTrade_of_local_modifications
    An S support pc R candidate T N K hK δ hδ0 hδ1 hδlaw hsupport hlocal
      hcand hmap hmultiplicity
  exact increment_AGInput_of_cylinder_windowTrade A An S support hdep pc hpc0 hpc1
    hAn hwindow hconv hbase hA hmeas

end FK.AGLocalPivot.Cylinder
