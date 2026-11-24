/-
Worker m4, swarm smwuwykef.  Direction D (essential-device pivot trade).

# The strict decrement shift from a *window* pivot trade

`FK.AGMassDerivative.decrement_AGInput_of_pivotTrade` derives the strict decrement
shift of `FK.AGDifferentialShift` from the whole-region pivot trade inequality.
`PivotTradeObstruction` shows that hypothesis is false (minimal cycle device),
`PivotTradeWindow` shows that a positive trade constant exists on every compact
window of the open weight cube.

This file re-runs the strict-shift assembly with the trade required only on the
compact window the mean value theorem actually traverses:

  `b ∈ [pc/2, (1+pc)/2]`,  `0 < ε ≤ min (pc/4) ((1-pc)/4)`,  `ε < b`.

Main results:
* `exists_subcritical_shift_window`: the strict decrement shift with the trade
  hypothesis restricted to that window (the derivative data is discharged by
  `massPair_deriv_decomp`, so no analytic premise remains);
* `decrement_AGInput_of_windowTrade`: the `hAG` decrement input in the same
  quantifier shape as `decrement_AGInput_of_pivotTrade`, whose only finite-volume
  geometric input is a uniform-in-`n` trade constant on that window.

`PivotTradeWindow.exists_decrement_window_trade` supplies a constant for each
fixed approximating event `An n`; uniformity in `n` is the remaining quantitative
input and is stated explicitly, not hidden.
-/
import FK.PivotTradeWindow

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal Topology

namespace FK.PivotTradeAGRepair

open FK.MargulisRussoFinite FK.AGMassDerivative FK.AGDifferentialShift

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Strict decrement shift, window trade form.**  The trade inequality is only
required on the compact window traversed by the segment
`(b, ε) = (pc - c·ε/2 + c·t, t)`, `t ∈ (0, ε)`. -/
theorem exists_subcritical_shift_window
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c E₀ : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (htrade : ∀ (n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
      0 < ε → ε ≤ E₀ → ε < b →
      c * pivotTotal (fun a => decWeight S a (b, ε)) (An n) ≤
        pivotOn S (fun a => decWeight S a (b, ε)) (An n))
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
      ((continuous_massPair (An n) S).comp (by fun_prop : Continuous
        fun s : ℝ => (b₀ + c * s, 0 + 1 * s))).continuousOn
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s))
          ((tradeCLM (pivotTotal (fun a => decWeight S a (b₀ + c * t, 0 + 1 * t)) (An n))
            (pivotOn S (fun a => decWeight S a (b₀ + c * t, 0 + 1 * t)) (An n)))
            (c, 1)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hbt0 : 0 < b₀ + c * t := hb0t t ht0 htε.le
      have hbt1 : b₀ + c * t < 1 := hb1t t ht0 htε.le
      have hεtt : 0 + 1 * t < b₀ + c * t := by simpa using hεt t ht
      have hle : (0:ℝ) ≤ 0 + 1 * t := by linarith
      have hF := massPair_deriv_decomp (hAn n) S hbt0 hbt1 hle hεtt
      have hline : HasDerivAt (fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) (c, (1:ℝ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => b₀ + c * s) c t := by
          simpa using (hasDerivAt_const_mul (x := t) c).const_add b₀
        have h2 : HasDerivAt (fun s : ℝ => (0:ℝ) + 1 * s) 1 t := by
          simpa using (hasDerivAt_id (x := t)).const_add (0:ℝ)
        exact h1.prodMk h2
      exact hF.comp_hasDerivAt t hline
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        ((tradeCLM (pivotTotal (fun a => decWeight S a (b₀ + c * t, 0 + 1 * t)) (An n))
          (pivotOn S (fun a => decWeight S a (b₀ + c * t, 0 + 1 * t)) (An n)))
          (c, 1)) ≤ 0 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hpos : (0:ℝ) < 0 + 1 * t := by linarith
      have hlt : 0 + 1 * t < b₀ + c * t := by simpa using hεt t ht
      have hεE₀t : 0 + 1 * t ≤ E₀ := by
        have : t ≤ ε := ht.2.le
        linarith
      -- the moving base stays inside the compact window
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

/-- **The decrement `hAG` input from a uniform window trade constant.**  Identical
conclusion to `FK.AGMassDerivative.decrement_AGInput_of_pivotTrade`, but the pivot
trade is required only on the compact window
`b ∈ [pc/2, (1+pc)/2]`, `0 < ε ≤ min (pc/4) ((1-pc)/4)`, where it is satisfiable
(see `FK.PivotTradeWindow.exists_decrement_window_trade`). -/
theorem decrement_AGInput_of_windowTrade
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (hwindow : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → ε < b →
        c * pivotTotal (fun a => decWeight S a (b, ε)) (An n) ≤
          pivotOn S (fun a => decWeight S a (b, ε)) (An n))
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
    exists_subcritical_shift_window A An S pc c E₀ hpc0 hpc1 hc0 hc1 hAn htrade
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


omit [Fintype E] [DecidableEq E] in
/-- Pointwise bound: clamped decrement weights are nonnegative. -/
theorem decWeight_nonneg (a : E) (u : ℝ × ℝ) : 0 ≤ decWeight S a u := by
  rw [decWeight_apply]
  exact le_max_left _ _

omit [Fintype E] [DecidableEq E] in
/-- Pointwise bound: clamped decrement weights are at most one. -/
theorem decWeight_le_one (a : E) (u : ℝ × ℝ) : decWeight S a u ≤ 1 := by
  rw [decWeight_apply]
  exact max_le zero_le_one (min_le_left _ _)

/-- **Satisfiability of the uniform window input** in the constant-sequence case:
an essential enhanced set gives a trade constant `c ∈ (0,1]` on the window. -/
theorem exists_uniform_window_trade_const (A₀ : Set (E → Bool)) (S : Set E) (pc : ℝ)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hS : S.Nonempty)
    (hess : ∀ e ∈ S, ∃ off : Glauber.OffConfig Bool E e, OffPivotal A₀ e off) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (_n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
      0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → ε < b →
      c * pivotTotal (fun a => decWeight S a (b, ε)) A₀ ≤
        pivotOn S (fun a => decWeight S a (b, ε)) A₀ := by
  have hβ : 0 < pc / 2 := by linarith
  have hβB : pc / 2 ≤ (1 + pc) / 2 := by linarith
  have hB : (1 + pc) / 2 < 1 := by linarith
  have hη : 0 ≤ min (pc / 4) ((1 - pc) / 4) :=
    le_min (by linarith) (by linarith)
  have hηβ : min (pc / 4) ((1 - pc) / 4) < pc / 2 := by
    have h : min (pc / 4) ((1 - pc) / 4) ≤ pc / 4 := min_le_left _ _
    linarith
  obtain ⟨c, hc0, hc⟩ :=
    FK.PivotTradeWindow.exists_decrement_window_trade A₀ S hβ hβB hB hη hηβ hS hess
  refine ⟨min c 1, lt_min hc0 one_pos, min_le_right _ _, ?_⟩
  intro n b ε hb hε0 hεη hεb
  have hcle : min c 1 ≤ c := min_le_left _ _
  have hP : 0 ≤ pivotTotal (fun a => decWeight S a (b, ε)) A₀ := by
    refine FK.PivotTradeWindow.pivotTotal_nonneg (fun a => ?_)
    exact ⟨(decWeight_nonneg a (b, ε)), (decWeight_le_one a (b, ε))⟩
  calc min c 1 * pivotTotal (fun a => decWeight S a (b, ε)) A₀
      ≤ c * pivotTotal (fun a => decWeight S a (b, ε)) A₀ :=
        mul_le_mul_of_nonneg_right hcle hP
    _ ≤ pivotOn S (fun a => decWeight S a (b, ε)) A₀ := hc b hb ε ⟨hε0.le, hεη⟩


end
end FK.PivotTradeAGRepair
