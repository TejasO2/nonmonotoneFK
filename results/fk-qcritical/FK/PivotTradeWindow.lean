/-
Worker m4, swarm smwuwykef.  Direction D (essential-device pivot trade).

# A compact-window pivot trade constant, and the corrected AG hypothesis

`PivotTradeObstruction` shows that the pivot trade inequality with one constant
`c > 0` over the *whole* open region `0 < ε < b < 1` is unsatisfiable already for
the minimal cycle device.  The strict-shift assembly
(`FK.AGMassDerivative.exists_subcritical_decrement_interior`) uses the trade only
along the segment `(b, ε) = (b₀ + c t, t)`, `t ∈ (0, ε₀)`, i.e. inside a
**compact window** around the critical parameter.  Here we prove that on every
compact window of weight vectors inside `(0,1)^E` a positive trade constant does
exist, provided the enhancement set is *essential* in the configuration-level
sense of Aizenman--Grimmett (each enhanced edge is pivotal for some off-edge
configuration).  Consequently the corrected hypothesis

  `∀ b ∈ Icc β B, ∀ ε ∈ Icc 0 η, c * pivotTotal (decWeight S (b,ε)) A ≤
      pivotOn S (decWeight S (b,ε)) A`,   with `0 < β ≤ B < 1`, `η < β`

is satisfiable, whereas the old whole-region form is not.

Main results:
* `continuous_pivotTotal`, `continuous_pivotOn`: the pivotal masses are continuous
  in the weight vector (finite sums of products of coordinate weights);
* `offPivotalWeight_pos`, `pivotOn_pos`: essentiality ⟺ strict positivity of the
  corresponding pivotal masses on the open weight cube;
* `exists_trade_constant_of_compact`: a positive constant on any compact window;
* `exists_decrement_window_trade`, `exists_increment_window_trade`: the two box
  corollaries actually needed by the decrement/increment trade segments.
-/
import FK.PivotTradeObstruction

open Set
open scoped Classical BigOperators

namespace FK.PivotTradeWindow

open FK.MargulisRussoFinite FK.AGMassDerivative

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### Continuity of the pivotal masses in the weight vector -/

omit [Fintype E] [DecidableEq E] in
/-- A single coordinate factor is continuous in the weight vector. -/
theorem continuous_coordinateWeight (e : E) (b : Bool) :
    Continuous fun r : E → ℝ => coordinateWeight (r e) b := by
  cases b
  · refine (continuous_const.sub (continuous_apply e) :
      Continuous fun r : E → ℝ => (1 : ℝ) - r e).congr (fun r => ?_)
    simp [coordinateWeight]
  · simpa only [coordinateWeight_true] using
      (continuous_apply e : Continuous fun r : E → ℝ => r e)

theorem continuous_eventWeight (A : Set (E → Bool)) :
    Continuous fun r : E → ℝ => eventWeight r A := by
  classical
  have hfun : (fun r : E → ℝ => eventWeight r A) =
      fun r => ∑ ω : E → Bool,
        if ω ∈ A then ∏ e, coordinateWeight (r e) (ω e) else 0 := rfl
  rw [hfun]
  refine continuous_finsetSum _ (fun ω _ => ?_)
  by_cases h : ω ∈ A
  · simp only [h, ite_true]
    exact continuous_finsetProd _ (fun e _ => continuous_coordinateWeight e (ω e))
  · simp only [h, ite_false]
    exact continuous_const

theorem continuous_offPivotalWeight (A : Set (E → Bool)) (e : E) :
    Continuous fun r : E → ℝ => offPivotalWeight r e A := by
  have hfun : (fun r : E → ℝ => offPivotalWeight r e A) =
      fun r => eventWeight r {ω : E → Bool | FK.AGPeeling.Pivotal A e ω} := by
    funext r
    exact (eventWeight_pivotal r A e).symm
  rw [hfun]
  exact continuous_eventWeight _

theorem continuous_pivotTotal (A : Set (E → Bool)) :
    Continuous fun r : E → ℝ => pivotTotal r A := by
  have hfun : (fun r : E → ℝ => pivotTotal r A) =
      fun r => ∑ e, offPivotalWeight r e A := rfl
  rw [hfun]
  exact continuous_finsetSum _ (fun e _ => continuous_offPivotalWeight A e)

theorem continuous_pivotOn (S : Set E) (A : Set (E → Bool)) :
    Continuous fun r : E → ℝ => pivotOn S r A := by
  have hfun : (fun r : E → ℝ => pivotOn S r A) =
      fun r => ∑ e ∈ Finset.univ.filter (fun e => e ∈ S), offPivotalWeight r e A := rfl
  rw [hfun]
  exact continuous_finsetSum _ (fun e _ => continuous_offPivotalWeight A e)

/-! ### Continuity of the clamped profiles as maps of the parameter plane -/

omit [Fintype E] [DecidableEq E] in
theorem continuous_decWeight (S : Set E) (e : E) :
    Continuous fun u : ℝ × ℝ => decWeight S e u := by
  have hfun : (fun u : ℝ × ℝ => decWeight S e u) =
      fun u => if e ∈ S then max 0 (min 1 (u.1 - u.2)) else max 0 (min 1 u.1) := by
    funext u
    rw [decWeight_apply]
    by_cases h : e ∈ S <;> simp [h]
  rw [hfun]
  by_cases h : e ∈ S
  · simp only [h, ite_true]
    exact (continuous_const.max (continuous_const.min (continuous_fst.sub continuous_snd)))
  · simp only [h, ite_false]
    exact continuous_const.max (continuous_const.min continuous_fst)

omit [Fintype E] [DecidableEq E] in
theorem continuous_incrementWeight (S : Set E) (e : E) :
    Continuous fun u : ℝ × ℝ => incWeight S e u := by
  have hfun : (fun u : ℝ × ℝ => incWeight S e u) =
      fun u => if e ∈ S then max 0 (min 1 (u.1 + u.2)) else max 0 (min 1 u.1) := by
    funext u
    rw [incWeight_apply]
    by_cases h : e ∈ S <;> simp [h]
  rw [hfun]
  by_cases h : e ∈ S
  · simp only [h, ite_true]
    exact continuous_const.max (continuous_const.min (continuous_fst.add continuous_snd))
  · simp only [h, ite_false]
    exact continuous_const.max (continuous_const.min continuous_fst)

omit [Fintype E] [DecidableEq E] in
/-- The clamped decrement profile as a continuous map into the weight space. -/
theorem continuous_decProfile (S : Set E) :
    Continuous fun u : ℝ × ℝ => (fun a => decWeight S a u) :=
  continuous_pi (fun e => continuous_decWeight S e)

omit [Fintype E] [DecidableEq E] in
/-- The clamped increment profile as a continuous map into the weight space. -/
theorem continuous_incProfile (S : Set E) :
    Continuous fun u : ℝ × ℝ => (fun a => incWeight S a u) :=
  continuous_pi (fun e => continuous_incrementWeight S e)

/-! ### Positivity: essentiality of an enhanced edge -/

theorem offConfigurationWeight_pos {r : E → ℝ} (hr : ∀ a, 0 < r a ∧ r a < 1) (e : E)
    (off : Glauber.OffConfig Bool E e) : 0 < offConfigurationWeight r e off := by
  classical
  rw [offConfigurationWeight]
  refine Finset.prod_pos (fun a _ => ?_)
  cases h : off a
  · simpa only [coordinateWeight_false] using sub_pos.mpr (hr a.1).2
  · simpa only [coordinateWeight_true] using (hr a.1).1

/-- On the open weight cube, the pivotal mass of `e` is strictly positive exactly
when `e` is pivotal for some off-edge configuration, i.e. exactly when `e` is an
essential enhanced edge. -/
theorem offPivotalWeight_pos_iff {r : E → ℝ} (hr : ∀ a, 0 < r a ∧ r a < 1) (e : E)
    {A : Set (E → Bool)} :
    0 < offPivotalWeight r e A ↔ ∃ off : Glauber.OffConfig Bool E e, OffPivotal A e off := by
  classical
  constructor
  · intro h
    by_contra hcon
    have hzero : offPivotalWeight r e A = 0 := by
      rw [offPivotalWeight]
      exact Finset.sum_eq_zero (fun off _ => by
        by_cases hp : OffPivotal A e off
        · exact absurd ⟨off, hp⟩ hcon
        · simp [hp])
    rw [hzero] at h
    exact lt_irrefl _ h
  · rintro ⟨off, hoff⟩
    rw [offPivotalWeight]
    refine Finset.sum_pos' (fun off _ => ?_) ⟨off, Finset.mem_univ off, ?_⟩
    · by_cases hp : OffPivotal A e off
      · rw [ite_eq_left hp]
        exact (offConfigurationWeight_pos hr e off).le
      · simp [hp]
    · rw [ite_eq_left hoff]
      exact offConfigurationWeight_pos hr e off

/-- Essentiality of every edge of a nonempty `S` makes the enhanced pivotal mass
strictly positive throughout the open weight cube. -/
theorem pivotOn_pos {A : Set (E → Bool)} {S : Set E} (hS : S.Nonempty)
    (hess : ∀ e ∈ S, ∃ off : Glauber.OffConfig Bool E e, OffPivotal A e off)
    {r : E → ℝ} (hr : ∀ a, 0 < r a ∧ r a < 1) : 0 < pivotOn S r A := by
  classical
  obtain ⟨e₀, he₀S⟩ := hS
  rw [pivotOn]
  have hmem : e₀ ∈ Finset.univ.filter (fun e => e ∈ S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, he₀S⟩
  refine Finset.sum_pos' (fun e _ => ?_) ⟨e₀, hmem, ?_⟩
  · refine offPivotalWeight_nonneg (fun a => ⟨(hr a).1.le, (hr a).2.le⟩) e
  · exact (offPivotalWeight_pos_iff hr e₀).mpr (hess e₀ he₀S)

theorem pivotTotal_nonneg {A : Set (E → Bool)} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Icc (0 : ℝ) 1) : 0 ≤ pivotTotal r A :=
  Finset.sum_nonneg (fun e _ => offPivotalWeight_nonneg hr e)

theorem pivotOn_nonneg {A : Set (E → Bool)} {S : Set E} {r : E → ℝ}
    (hr : ∀ a, r a ∈ Icc (0 : ℝ) 1) : 0 ≤ pivotOn S r A := by
  classical
  rw [pivotOn]
  exact Finset.sum_nonneg (fun e _ => offPivotalWeight_nonneg hr e)

/-! ### The compact-window trade constant -/

/-- **A positive trade constant exists on every compact window of the open weight
cube**, provided `S` is nonempty and every `e ∈ S` is essential.  This is the
satisfiable replacement for the whole-region pivot trade inequality refuted in
`PivotTradeObstruction`. -/
theorem exists_trade_constant_of_compact (A : Set (E → Bool)) (S : Set E)
    (K : Set (E → ℝ)) (hK : IsCompact K) (hne : K.Nonempty)
    (hint : ∀ r ∈ K, ∀ a, 0 < r a ∧ r a < 1)
    (hS : S.Nonempty) (hess : ∀ e ∈ S, ∃ off : Glauber.OffConfig Bool E e, OffPivotal A e off) :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ K, c * pivotTotal r A ≤ pivotOn S r A := by
  classical
  obtain ⟨r₀, hr₀K, hmin⟩ := hK.exists_isMinOn hne (continuous_pivotOn S A).continuousOn
  obtain ⟨r₁, hr₁K, hmax⟩ := hK.exists_isMaxOn hne (continuous_pivotTotal A).continuousOn
  have hm : 0 < pivotOn S r₀ A := pivotOn_pos hS hess (hint r₀ hr₀K)
  have hM : 0 ≤ pivotTotal r₁ A :=
    pivotTotal_nonneg (fun a => ⟨(hint r₁ hr₁K a).1.le, (hint r₁ hr₁K a).2.le⟩)
  refine ⟨pivotOn S r₀ A / (pivotTotal r₁ A + 1), by positivity, ?_⟩
  intro r hrK
  have hP : pivotTotal r A ≤ pivotTotal r₁ A := hmax hrK
  have hO : pivotOn S r₀ A ≤ pivotOn S r A := hmin hrK
  have hPr : 0 ≤ pivotTotal r A :=
    pivotTotal_nonneg (fun a => ⟨(hint r hrK a).1.le, (hint r hrK a).2.le⟩)
  have hstep : pivotOn S r₀ A / (pivotTotal r₁ A + 1) * pivotTotal r A ≤
      pivotOn S r₀ A / (pivotTotal r₁ A + 1) * pivotTotal r₁ A :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have hsecond : pivotOn S r₀ A / (pivotTotal r₁ A + 1) * pivotTotal r₁ A ≤
      pivotOn S r₀ A := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  exact hstep.trans (hsecond.trans hO)

/-- **Decrement window.**  For the clamped decrement profile with
`b ∈ [β, B]`, `ε ∈ [0, η]`, `0 < β ≤ B < 1`, `η < β`, an essential enhanced set
carries a positive fraction `c` of the total pivotal mass. -/
theorem exists_decrement_window_trade (A : Set (E → Bool)) (S : Set E)
    {β B η : ℝ} (hβ : 0 < β) (hβB : β ≤ B) (hB : B < 1) (hη : 0 ≤ η) (hηβ : η < β)
    (hS : S.Nonempty) (hess : ∀ e ∈ S, ∃ off : Glauber.OffConfig Bool E e, OffPivotal A e off) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ Icc β B, ∀ ε ∈ Icc (0 : ℝ) η,
      c * pivotTotal (fun a => decWeight S a (b, ε)) A ≤
        pivotOn S (fun a => decWeight S a (b, ε)) A := by
  classical
  set P : Set (ℝ × ℝ) := Icc β B ×ˢ Icc (0 : ℝ) η with hP
  have hPc : IsCompact P := isCompact_Icc.prod isCompact_Icc
  have hPne : P.Nonempty := ⟨(β, 0), ⟨⟨le_rfl, hβB⟩, ⟨le_rfl, hη⟩⟩⟩
  have hKc : IsCompact ((fun u : ℝ × ℝ => (fun a => decWeight S a u)) '' P) :=
    hPc.image (continuous_decProfile S)
  have hKne : ((fun u : ℝ × ℝ => (fun a => decWeight S a u)) '' P).Nonempty :=
    hPne.image _
  have hint : ∀ r ∈ ((fun u : ℝ × ℝ => (fun a => decWeight S a u)) '' P),
      ∀ a, 0 < r a ∧ r a < 1 := by
    rintro r ⟨⟨b, ε⟩, ⟨hb, hε⟩, rfl⟩ a
    have hbβ : β ≤ b := hb.1
    have hbB : b ≤ B := hb.2
    have hε0 : 0 ≤ ε := hε.1
    have hεη : ε ≤ η := hε.2
    have hbpos : 0 < b := lt_of_lt_of_le hβ hbβ
    have hblt : b < 1 := lt_of_le_of_lt hbB hB
    show 0 < decWeight S a (b, ε) ∧ decWeight S a (b, ε) < 1
    rw [decWeight_apply]
    have hbε0 : 0 < b - ε := by linarith
    have hbε1 : b - ε < 1 := by linarith
    by_cases h : a ∈ S
    · simp only [h, ite_true]
      constructor
      · exact lt_of_lt_of_le hbε0 (le_trans (le_min hbε1.le le_rfl) (le_max_right _ _))
      · exact lt_of_le_of_lt (max_le hbε0.le (min_le_right _ _)) hbε1
    · simp only [h, ite_false]
      constructor
      · exact lt_of_lt_of_le hbpos (le_trans (le_min hblt.le le_rfl) (le_max_right _ _))
      · exact lt_of_le_of_lt (max_le hbpos.le (min_le_right _ _)) hblt
  obtain ⟨c, hc0, hc⟩ := exists_trade_constant_of_compact A S _ hKc hKne hint hS hess
  refine ⟨c, hc0, ?_⟩
  intro b hb ε hε
  exact hc _ ⟨(b, ε), ⟨hb, hε⟩, rfl⟩

/-- **Increment window.**  The analogue for the clamped increment profile with
`a ∈ [α, A]`, `ε ∈ [0, η]`, `0 < α ≤ A`, `A + η < 1`. -/
theorem exists_increment_window_trade (A : Set (E → Bool)) (S : Set E)
    {α Aa η : ℝ} (hα : 0 < α) (hαA : α ≤ Aa) (hη : 0 ≤ η) (hAη : Aa + η < 1)
    (hS : S.Nonempty) (hess : ∀ e ∈ S, ∃ off : Glauber.OffConfig Bool E e, OffPivotal A e off) :
    ∃ c : ℝ, 0 < c ∧ ∀ a ∈ Icc α Aa, ∀ ε ∈ Icc (0 : ℝ) η,
      c * pivotTotal (fun a' => incWeight S a' (a, ε)) A ≤
        pivotOn S (fun a' => incWeight S a' (a, ε)) A := by
  classical
  set P : Set (ℝ × ℝ) := Icc α Aa ×ˢ Icc (0 : ℝ) η with hP
  have hPc : IsCompact P := isCompact_Icc.prod isCompact_Icc
  have hPne : P.Nonempty := ⟨(α, 0), ⟨⟨le_rfl, hαA⟩, ⟨le_rfl, hη⟩⟩⟩
  have hKc : IsCompact ((fun u : ℝ × ℝ => (fun a => incWeight S a u)) '' P) :=
    hPc.image (continuous_incProfile S)
  have hKne : ((fun u : ℝ × ℝ => (fun a => incWeight S a u)) '' P).Nonempty :=
    hPne.image _
  have hint : ∀ r ∈ ((fun u : ℝ × ℝ => (fun a => incWeight S a u)) '' P),
      ∀ a, 0 < r a ∧ r a < 1 := by
    rintro r ⟨⟨a, ε⟩, ⟨ha, hε⟩, rfl⟩ a'
    have haα : α ≤ a := ha.1
    have haA : a ≤ Aa := ha.2
    have hε0 : 0 ≤ ε := hε.1
    have hεη : ε ≤ η := hε.2
    have hapos : 0 < a := lt_of_lt_of_le hα haα
    have halta1 : a < 1 := by linarith
    show 0 < incWeight S a' (a, ε) ∧ incWeight S a' (a, ε) < 1
    rw [incWeight_apply]
    have haε0 : 0 < a + ε := by linarith
    have haε1 : a + ε < 1 := by linarith
    by_cases h : a' ∈ S
    · simp only [h, ite_true]
      constructor
      · exact lt_of_lt_of_le haε0 (le_trans (le_min haε1.le le_rfl) (le_max_right _ _))
      · exact lt_of_le_of_lt (max_le haε0.le (min_le_right _ _)) haε1
    · simp only [h, ite_false]
      constructor
      · exact lt_of_lt_of_le hapos (le_trans (le_min halta1.le le_rfl) (le_max_right _ _))
      · exact lt_of_le_of_lt (max_le hapos.le (min_le_right _ _)) halta1
  obtain ⟨c, hc0, hc⟩ := exists_trade_constant_of_compact A S _ hKc hKne hint hS hess
  refine ⟨c, hc0, ?_⟩
  intro a ha ε hε
  exact hc _ ⟨(a, ε), ⟨ha, hε⟩, rfl⟩

end
end FK.PivotTradeWindow
