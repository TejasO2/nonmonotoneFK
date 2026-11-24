/-
Worker m4, swarm smwuwykef.  Direction D (essential-device pivot trade).

# The uniform pivot trade `c · pivotTotal ≤ pivotOn` is unsatisfiable

`FK.AGMassDerivative.decrement_AGInput_of_pivotTrade` reduces the strict
decrement shift to

  `hpivot : ∀ n b ε, 0 < b → b < 1 → 0 < ε → ε < b →
      c * pivotTotal (decWeight S (b,ε)) (An n) ≤ pivotOn S (decWeight S (b,ε)) (An n)`

with a **single** `c > 0` and the **whole** open parameter region `0 < ε < b < 1`.
This file shows that this hypothesis is false already for the minimal instance of
the source's *above-enhancement* geometry (arXiv:2512.16486v1, Proposition
"above_enhancement"): the graph with two parallel edges `u--v`, the enhanced set
`S = {e₀}`, and the endpoint-connection event `{e₀ open} ∪ {e₁ open}`, which is
exactly the case where `e₁` is a path joining the endpoints of `e₀` inside
`E \ {e₀}` (a cycle of length two in the multigraph).  The enhancement is
essential: `e₀` is pivotal in every configuration with `e₁` closed.

Exact pivotal masses (proved below, no surrogates):

  `pivotOn {e₀} r A = 1 - r e₁`,  `pivotTotal r A = (1 - r e₁) + (1 - r e₀)`,

so on the decrement profile (`r e₀ = b - ε`, `r e₁ = b`)

  `pivotOn = 1 - b`,  `pivotTotal = 2 * (1 - b) + ε`,

and the ratio `pivotOn / pivotTotal → 0` as `b → 1` with `ε > 0` fixed.  Hence for
every `c > 0` some admissible `(b, ε)` violates the trade; the quantifier range
must be cut down to a compact window (see `PivotTradeWindow`).

The same file also records that the trade *does* hold on a concrete compact
window for this gadget, so the repaired hypothesis is not vacuous.
-/
import FK.AGMassDerivative

open Set
open scoped Classical BigOperators

namespace FK.PivotTradeObstruction

open FK.MargulisRussoFinite FK.AGMassDerivative

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### Basic event-weight computations -/

/-- `eventWeight` of a single coordinate being open is that coordinate's weight. -/
theorem eventWeight_coordinate_true (r : E → ℝ) (e : E) :
    eventWeight r {ω : E → Bool | ω e = true} = r e := by
  rw [eventWeight_eq_coordinate r _ e]
  have h1 : offEventWeight r e {ω : E → Bool | ω e = true} true = 1 := by
    rw [offEventWeight, ← sum_offConfigurationWeight r e]
    apply Finset.sum_congr rfl
    intro off _
    exact ite_eq_left (by simp)
  have h0 : offEventWeight r e {ω : E → Bool | ω e = true} false = 0 := by
    rw [offEventWeight]
    exact Finset.sum_eq_zero (fun off _ => ite_eq_right (by simp))
  rw [h1, h0]
  ring

/-- The total product mass splits over an event and its complement. -/
theorem eventWeight_add_compl (r : E → ℝ) (A : Set (E → Bool)) :
    eventWeight r A + eventWeight r Aᶜ = 1 := by
  rw [← eventWeight_univ r]
  unfold eventWeight
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω ∈ A
  · simp [h]
  · simp [h]

/-- Complement form of the event weight. -/
theorem eventWeight_compl (r : E → ℝ) (A : Set (E → Bool)) :
    eventWeight r Aᶜ = 1 - eventWeight r A := by
  have h := eventWeight_add_compl r A
  linarith

/-! ### The minimal above-enhancement device: two parallel edges -/

/-- The endpoint-connection event on the two-edge multigraph `u -- v`:
`e₀ = 0` is the enhanced edge, `e₁ = 1` the auxiliary parallel edge. -/
def parallelEvent : Set (Fin 2 → Bool) := {ω | ω 0 = true ∨ ω 1 = true}

theorem parallelEvent_isUpperSet : IsUpperSet parallelEvent := by
  intro ω η hωη hω
  rcases hω with h | h
  · exact Or.inl (Bool.le_iff_imp.mp (hωη 0) h)
  · exact Or.inr (Bool.le_iff_imp.mp (hωη 1) h)

/-- The enhanced edge is pivotal exactly when the auxiliary edge is closed. -/
theorem pivotal_parallelEvent_zero (ω : Fin 2 → Bool) :
    FK.AGPeeling.Pivotal parallelEvent 0 ω ↔ ω 1 = false := by
  unfold FK.AGPeeling.Pivotal parallelEvent
  simp [FK.EssentialEnhancement.forceEdge]

/-- The auxiliary edge is pivotal exactly when the enhanced edge is closed. -/
theorem pivotal_parallelEvent_one (ω : Fin 2 → Bool) :
    FK.AGPeeling.Pivotal parallelEvent 1 ω ↔ ω 0 = false := by
  unfold FK.AGPeeling.Pivotal parallelEvent
  simp [FK.EssentialEnhancement.forceEdge]

/-- Exact pivotal mass of the enhanced edge. -/
theorem offPivotalWeight_parallelEvent_zero (r : Fin 2 → ℝ) :
    offPivotalWeight r 0 parallelEvent = 1 - r 1 := by
  rw [← eventWeight_pivotal r parallelEvent 0]
  have hset : {ω : Fin 2 → Bool | FK.AGPeeling.Pivotal parallelEvent 0 ω} =
      {ω : Fin 2 → Bool | ω 1 = true}ᶜ := by
    ext ω
    simp [pivotal_parallelEvent_zero]
  rw [hset, eventWeight_compl, eventWeight_coordinate_true]

/-- Exact pivotal mass of the auxiliary edge. -/
theorem offPivotalWeight_parallelEvent_one (r : Fin 2 → ℝ) :
    offPivotalWeight r 1 parallelEvent = 1 - r 0 := by
  rw [← eventWeight_pivotal r parallelEvent 1]
  have hset : {ω : Fin 2 → Bool | FK.AGPeeling.Pivotal parallelEvent 1 ω} =
      {ω : Fin 2 → Bool | ω 0 = true}ᶜ := by
    ext ω
    simp [pivotal_parallelEvent_one]
  rw [hset, eventWeight_compl, eventWeight_coordinate_true]

/-- The general singleton formula for the enhanced pivotal mass. -/
theorem pivotOn_singleton (e : E) (r : E → ℝ) (A : Set (E → Bool)) :
    pivotOn {e} r A = offPivotalWeight r e A := by
  rw [pivotOn, Finset.sum_filter]
  simp only [Set.mem_singleton_iff]
  rw [Finset.sum_ite_eq']
  simp

/-- The enhanced (`S = {0}`) pivotal mass of the parallel gadget. -/
theorem pivotOn_parallelEvent (r : Fin 2 → ℝ) :
    pivotOn {0} r parallelEvent = 1 - r 1 := by
  rw [pivotOn_singleton, offPivotalWeight_parallelEvent_zero]

/-- The total pivotal mass of the parallel gadget. -/
theorem pivotTotal_parallelEvent (r : Fin 2 → ℝ) :
    pivotTotal r parallelEvent = (1 - r 1) + (1 - r 0) := by
  rw [pivotTotal, Fin.sum_univ_two, offPivotalWeight_parallelEvent_zero,
    offPivotalWeight_parallelEvent_one]

/-! ### Evaluation of the decrement profile on the gadget -/

omit [Fintype E] [DecidableEq E] in
theorem decWeight_self (S : Set E) {e : E} (he : e ∈ S) (b ε : ℝ) :
    decWeight S e (b, ε) = max 0 (min 1 (b - ε)) := by
  rw [decWeight_apply]
  simp [he]

omit [Fintype E] [DecidableEq E] in
theorem decWeight_of_not_mem (S : Set E) {e : E} (he : e ∉ S) (b ε : ℝ) :
    decWeight S e (b, ε) = max 0 (min 1 b) := by
  rw [decWeight_apply]
  simp [he]

omit [Fintype E] [DecidableEq E] in
/-- Evaluation of the clamped increment weight on the enhanced set. -/
theorem incWeight_of_mem (S : Set E) {e : E} (he : e ∈ S) (a ε : ℝ) :
    incWeight S e (a, ε) = max 0 (min 1 (a + ε)) := by
  rw [incWeight_apply]
  simp [he]

omit [Fintype E] [DecidableEq E] in
/-- Evaluation of the clamped increment weight off the enhanced set. -/
theorem incWeight_of_not_mem (S : Set E) {e : E} (he : e ∉ S) (a ε : ℝ) :
    incWeight S e (a, ε) = max 0 (min 1 a) := by
  rw [incWeight_apply]
  simp [he]

omit [Fintype E] [DecidableEq E] in
/-- The clamped decrement weight off `S` is the base weight. -/
theorem decWeight_off (S : Set E) {e : E} (he : e ∉ S) (b ε : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) :
    decWeight S e (b, ε) = b := by
  rw [decWeight_of_not_mem _ he b ε, min_eq_right hb1.le, max_eq_right hb0.le]

omit [Fintype E] [DecidableEq E] in
/-- The clamped decrement weight on `S` is `b - ε`. -/
theorem decWeight_on (S : Set E) {e : E} (he : e ∈ S) (b ε : ℝ)
    (hε0 : 0 < ε) (hεb : ε < b) (hb1 : b < 1) :
    decWeight S e (b, ε) = b - ε := by
  rw [decWeight_self _ he b ε, min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Pivotal masses along the decrement trade profile. -/
theorem pivot_masses_decrement (b ε : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 < ε) (hεb : ε < b) :
    pivotOn {0} (fun a => decWeight {0} a (b, ε)) parallelEvent = 1 - b ∧
      pivotTotal (fun a => decWeight {0} a (b, ε)) parallelEvent = 2 * (1 - b) + ε := by
  have hon : ∀ a : Fin 2, a = 0 → decWeight {0} a (b, ε) = b - ε := by
    intro a ha; subst ha
    exact decWeight_on (S := ({0} : Set (Fin 2))) (by simp) b ε hε0 hεb hb1
  have hoff : ∀ a : Fin 2, a ≠ 0 → decWeight {0} a (b, ε) = b := by
    intro a ha
    have : a = 1 := by fin_cases a <;> simp_all
    subst this
    exact decWeight_off (S := ({0} : Set (Fin 2))) (by simp) b ε hb0 hb1
  have hr0 : decWeight {0} (0 : Fin 2) (b, ε) = b - ε := hon 0 rfl
  have hr1 : decWeight {0} (1 : Fin 2) (b, ε) = b := hoff 1 (by decide)
  rw [pivotOn_parallelEvent, pivotTotal_parallelEvent, hr0, hr1]
  constructor <;> ring

/-! ### The obstruction -/

/-- **The uniform pivot trade inequality fails for the minimal cycle device.**
For every candidate rate `c > 0` there are admissible parameters
`0 < ε < b < 1` at which `c * pivotTotal > pivotOn`. -/
theorem not_uniform_pivotTrade :
    ∀ c : ℝ, 0 < c → ∃ b ε : ℝ, 0 < b ∧ b < 1 ∧ 0 < ε ∧ ε < b ∧
      pivotOn {0} (fun a => decWeight {0} a (b, ε)) parallelEvent <
        c * pivotTotal (fun a => decWeight {0} a (b, ε)) parallelEvent := by
  intro c hc
  set δ : ℝ := min (c / 8) (1 / 4) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδc : δ ≤ c / 8 := min_le_left _ _
  refine ⟨1 - δ, 1 / 2, by linarith, by linarith, by norm_num, by linarith, ?_⟩
  have hb0 : 0 < 1 - δ := by linarith
  have hb1 : 1 - δ < 1 := by linarith
  have hεb : (1 : ℝ) / 2 < 1 - δ := by linarith
  obtain ⟨hon, htot⟩ := pivot_masses_decrement (1 - δ) (1 / 2) hb0 hb1 (by norm_num) hεb
  rw [hon, htot]
  have hpos : 0 < 2 * (1 - (1 - δ)) + 1 / 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hδc hc.le, hc]

/-! ### Non-vacuity of the window repair: an explicit trade constant -/

/-- On the compact window `b ∈ [1/4, 1/2]`, `ε ∈ (0, 1/8]` the same gadget
satisfies the trade with the explicit constant `1/4`.  So restricting the
quantifier range repairs the hypothesis rather than trivialising it. -/
theorem pivotTrade_on_window {b ε : ℝ} (hb0 : 1 / 4 ≤ b) (hb1 : b ≤ 1 / 2)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    1 / 4 * pivotTotal (fun a => decWeight {0} a (b, ε)) parallelEvent ≤
      pivotOn {0} (fun a => decWeight {0} a (b, ε)) parallelEvent := by
  have hbpos : 0 < b := by linarith
  have hblt : b < 1 := by linarith
  have hεb : ε < b := by linarith
  obtain ⟨hon, htot⟩ := pivot_masses_decrement b ε hbpos hblt hε0 hεb
  rw [hon, htot]
  have h2 : ε ≤ 2 * (1 - b) := by linarith
  linarith


/-! ### The failure is specific to the decrement side -/

/-- On the increment profile the same parallel gadget satisfies the trade with the
constant `1/2` on the *whole* region `0 < a`, `a + ε < 1`.  So the obstruction above
is genuinely one-sided: it is the decreasing profile of the above-enhancement
geometry that cannot carry a uniform constant, not the gadget itself. -/
theorem pivotTrade_increment_parallelEvent {a ε : ℝ} (ha0 : 0 < a) (hε0 : 0 < ε)
    (haε1 : a + ε < 1) :
    1 / 2 * pivotTotal (fun a' => incWeight {0} a' (a, ε)) parallelEvent ≤
      pivotOn {0} (fun a' => incWeight {0} a' (a, ε)) parallelEvent := by
  have ha1 : a < 1 := by linarith
  have h0 : incWeight {0} (0 : Fin 2) (a, ε) = a + ε := by
    rw [incWeight_of_mem _ (by simp) a ε, min_eq_right haε1.le, max_eq_right (by linarith)]
  have h1 : incWeight {0} (1 : Fin 2) (a, ε) = a := by
    rw [incWeight_of_not_mem _ (by simp) a ε, min_eq_right ha1.le, max_eq_right ha0.le]
  rw [pivotOn_parallelEvent, pivotTotal_parallelEvent, h0, h1]
  linarith

end
end FK.PivotTradeObstruction
