/-
Worker m4, swarm smwuwykef.  Direction D (essential-device pivot trade).

# The strict increment shift from a *window* pivot trade

Supercritical companion of `FK.PivotTradeAGRepair`.  The whole-region increment
trade hypothesis of `FK.AGMassDerivative.increment_AGInput_of_pivotTrade` is
replaced by a trade constant required only on the compact window
`a ∈ [pc/2, (1+pc)/2]`, `0 < ε ≤ E₀`, `a + ε < 1`, which is satisfiable by
`FK.PivotTradeWindow.exists_increment_window_trade`.

Main results:
* `exists_supercritical_shift_window`;
* `increment_AGInput_of_windowTrade` (identical quantifier shape to the original
  `increment_AGInput_of_pivotTrade`, satisfiable hypothesis);
* `exists_uniform_window_trade_const_increment`: satisfiability of a uniform
  window constant for a constant approximating sequence.
-/
import FK.PivotTradeWindow

open Set MeasureTheory Filter
open scoped Classical BigOperators ENNReal Topology

namespace FK.PivotTradeAGRepairIncrement

open FK.MargulisRussoFinite FK.AGMassDerivative FK.AGDifferentialShift

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
/-- Pointwise bound: clamped increment weights lie in `[0,1]`. -/
theorem incWeight_mem (a : E) (u : ℝ × ℝ) :
    incWeight S a u ∈ Icc (0 : ℝ) 1 := by
  rw [incWeight_apply]
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- **Strict increment shift, window trade form.** -/
theorem exists_supercritical_shift_window
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c E₀ : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (htrade : ∀ (n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
      0 < ε → ε ≤ E₀ → a + ε < 1 →
      0 ≤ (incTradeCLM (pivotTotal (fun a' => incWeight S a' (a, ε)) (An n))
        (pivotOn S (fun a' => incWeight S a' (a, ε)) (An n))) (-c, 1))
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
      ((continuous_incMassPair (An n) S).comp (by fun_prop : Continuous
        fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))).continuousOn
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))
          ((incTradeCLM (pivotTotal (fun a' => incWeight S a' (a₀ + (-c) * t, 0 + 1 * t))
              (An n))
            (pivotOn S (fun a' => incWeight S a' (a₀ + (-c) * t, 0 + 1 * t)) (An n)))
            (-c, 1)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hat0 : 0 < a₀ + (-c) * t := ha0t t ht0 htε.le
      have hat1 : a₀ + (-c) * t < 1 := ha1t t ht0 htε.le
      have hsum : a₀ + (-c) * t + (0 + 1 * t) < 1 := hsumt t ht
      have hle : (0:ℝ) ≤ 0 + 1 * t := by linarith
      have hF := incMassPair_deriv_decomp (hAn n) S hat0 hat1 hle hsum
      have hline : HasDerivAt (fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) ((-c), (1:ℝ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => a₀ + (-c) * s) (-c) t := by
          simpa using (hasDerivAt_const_mul (x := t) (-c)).const_add a₀
        have h2 : HasDerivAt (fun s : ℝ => (0:ℝ) + 1 * s) 1 t := by
          simpa using (hasDerivAt_id (x := t)).const_add (0:ℝ)
        exact h1.prodMk h2
      exact hF.comp_hasDerivAt t hline
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        0 ≤ ((incTradeCLM (pivotTotal (fun a' => incWeight S a' (a₀ + (-c) * t, 0 + 1 * t))
            (An n))
          (pivotOn S (fun a' => incWeight S a' (a₀ + (-c) * t, 0 + 1 * t)) (An n)))
          (-c, 1)) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hpos : (0:ℝ) < 0 + 1 * t := by linarith
      have hsum : a₀ + (-c) * t + (0 + 1 * t) < 1 := hsumt t ht
      have hεE₀t : 0 + 1 * t ≤ E₀ := by linarith [ht.2.le]
      have hmem : a₀ + (-c) * t ∈ Icc (pc / 2) ((1 + pc) / 2) := by
        constructor
        · nlinarith [ha₀, ha₁, ht.2.le, hc1, hε0.le, hc0.le]
        · nlinarith [ha₀, ha₀1, ht.1, hc0.le]
      exact htrade n _ _ hmem hpos hεE₀t hsum
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

/-- **The increment `hAG` input from a uniform window trade constant.** -/
theorem increment_AGInput_of_windowTrade
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (hwindow : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → a + ε < 1 →
        c * pivotTotal (fun a' => incWeight S a' (a, ε)) (An n) ≤
          pivotOn S (fun a' => incWeight S a' (a, ε)) (An n))
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
    have h1 : E₀ ≤ pc / 4 := min_le_left _ _
    have h2 : ε' ≤ pc / 4 := hε'E₀.trans h1
    linarith
  have hε'1 : ε' < (1 - pc) / 2 := by
    have h1 : E₀ ≤ (1 - pc) / 4 := min_le_right _ _
    have h2 : ε' ≤ (1 - pc) / 4 := hε'E₀.trans h1
    linarith
  obtain ⟨a, ha0, hapc, haε1, hmass⟩ :=
    exists_supercritical_shift_window A An S pc c E₀ hpc0 hpc1 hc0 hc1 hAn
      (fun n a ε ha hε0 hεE₀ haε =>
        incTradeCLM_trade_nonneg _ _ c (htrade n a ε ha hε0 hεE₀ haε))
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

/-- **Satisfiability of the uniform window input** on the increment side. -/
theorem exists_uniform_window_trade_const_increment (A₀ : Set (E → Bool)) (S : Set E) (pc : ℝ)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hS : S.Nonempty)
    (hess : ∀ e ∈ S, ∃ off : Glauber.OffConfig Bool E e, OffPivotal A₀ e off) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (_n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
      0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → a + ε < 1 →
      c * pivotTotal (fun a' => incWeight S a' (a, ε)) A₀ ≤
        pivotOn S (fun a' => incWeight S a' (a, ε)) A₀ := by
  have hα : 0 < pc / 2 := by linarith
  have hαA : pc / 2 ≤ (1 + pc) / 2 := by linarith
  have hη : 0 ≤ min (pc / 4) ((1 - pc) / 4) := le_min (by linarith) (by linarith)
  have hAη : (1 + pc) / 2 + min (pc / 4) ((1 - pc) / 4) < 1 := by
    have h1 : min (pc / 4) ((1 - pc) / 4) ≤ (1 - pc) / 4 := min_le_right _ _
    linarith
  obtain ⟨c, hc0, hc⟩ :=
    FK.PivotTradeWindow.exists_increment_window_trade A₀ S hα hαA hη hAη hS hess
  refine ⟨min c 1, lt_min hc0 one_pos, min_le_right _ _, ?_⟩
  intro n a ε ha hε0 hεη haε
  have hcle : min c 1 ≤ c := min_le_left _ _
  have hP : 0 ≤ pivotTotal (fun a' => incWeight S a' (a, ε)) A₀ :=
    FK.PivotTradeWindow.pivotTotal_nonneg (fun a' => incWeight_mem a' (a, ε))
  calc min c 1 * pivotTotal (fun a' => incWeight S a' (a, ε)) A₀
      ≤ c * pivotTotal (fun a' => incWeight S a' (a, ε)) A₀ :=
        mul_le_mul_of_nonneg_right hcle hP
    _ ≤ pivotOn S (fun a' => incWeight S a' (a, ε)) A₀ := hc a ha ε ⟨hε0.le, hεη⟩

end
end FK.PivotTradeAGRepairIncrement
