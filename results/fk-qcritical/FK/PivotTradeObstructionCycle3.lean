/-
Worker m4, swarm smwuwykef.  Direction D (essential-device pivot trade).

# The uniform pivot trade fails on the minimal simple cycle device (triangle)

`PivotTradeObstruction` refutes the whole-region pivot trade on the two-edge
(parallel-edge) device.  This file removes the parallel-edge objection: the same
failure occurs on a **simple** 3-cycle `u - x - v - u` with the enhanced edge
`e₀ = uv` and the auxiliary path `u - x - v` inside `E \ {e₀}` — literally the
minimal instance of the source's *above-enhancement* hypothesis
(arXiv:2512.16486v1: for every `e ∈ Ẽ` there is a path joining the endpoints of
`e` in `E \ Ẽ`), i.e. a cycle-device of length `L = 3`.

Exact pivotal masses on the triangle (`r e₀ = w`, `r (ux) = r (xv) = b`):

  `pivotOn {e₀} r A = 1 - r(ux) * r(xv)`,   `pivotTotal r A = pivotOn + 2 b (1 - w)`

(`A` = the event that `u` and `v` are connected).  On the decrement profile
`w = b - ε` this gives `pivotOn = 1 - b²`, `pivotTotal = 1 - b² + 2 b (1 - b + ε)`,
so `pivotOn / pivotTotal → 0` as `b → 1` with `ε > 0` fixed, and no single
`c > 0` works.  The enhancement is essential: `e₀` is pivotal exactly when the
auxiliary path is not fully open.
-/
import FK.PivotTradeObstruction

open Set
open scoped Classical BigOperators

namespace FK.PivotTradeObstructionCycle3

open FK.MargulisRussoFinite FK.AGMassDerivative FK.PivotTradeObstruction

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### Event masses of coordinate conditions -/

/-- Mass of one coordinate being closed. -/
theorem eventWeight_coordinate_false (r : E → ℝ) (a : E) :
    eventWeight r {ω : E → Bool | ω a = false} = 1 - r a := by
  have hset : {ω : E → Bool | ω a = false} = {ω : E → Bool | ω a = true}ᶜ := by
    ext ω
    show ω a = false ↔ ¬ (ω a = true)
    cases ω a <;> simp
  rw [hset, eventWeight_compl, eventWeight_coordinate_true]

/-- An off-edge coordinate sum sees the coordinate weight (both forced values). -/
theorem offEventWeight_coordinate_eq (r : E → ℝ) {a e : E} (hae : a ≠ e) (v u : Bool) :
    offEventWeight r e {ω : E → Bool | ω a = v} u = coordinateWeight (r a) v := by
  have hsplit := eventWeight_eq_coordinate (Function.update r e (if u then 1 else 0))
    {ω : E → Bool | ω a = v} e
  have hval : (Function.update r e (if u then 1 else 0)) e = if u then 1 else 0 := by
    simp
  have hcoord : eventWeight (Function.update r e (if u then 1 else 0))
      {ω : E → Bool | ω a = v} = coordinateWeight (r a) v := by
    cases v
    · rw [eventWeight_coordinate_false, Function.update_of_ne hae]
      simp [coordinateWeight]
    · rw [eventWeight_coordinate_true, Function.update_of_ne hae]
      simp [coordinateWeight]
  have hinv : offEventWeight (Function.update r e (if u then 1 else 0)) e
      {ω : E → Bool | ω a = v} true =
      offEventWeight r e {ω : E → Bool | ω a = v} true :=
    offEventWeight_update r e _ true _
  have hinv' : offEventWeight (Function.update r e (if u then 1 else 0)) e
      {ω : E → Bool | ω a = v} false =
      offEventWeight r e {ω : E → Bool | ω a = v} false :=
    offEventWeight_update r e _ false _
  rw [hval, hcoord, hinv, hinv'] at hsplit
  cases u
  · simp only [Bool.false_eq_true, ite_false] at hsplit ⊢
    linarith
  · simp only [ite_true] at hsplit
    linarith

/-- Mass of a conjunction of two coordinate conditions. -/
theorem eventWeight_pair (r : E → ℝ) {a b : E} (hab : a ≠ b) :
    eventWeight r {ω : E → Bool | ω a = true ∧ ω b = true} = r a * r b := by
  have hsplit := eventWeight_eq_coordinate r {ω : E → Bool | ω a = true ∧ ω b = true} a
  have htrue : offEventWeight r a {ω : E → Bool | ω a = true ∧ ω b = true} true = r b := by
    have heq : offEventWeight r a {ω : E → Bool | ω a = true ∧ ω b = true} true =
        offEventWeight r a {ω : E → Bool | ω b = true} true := by
      rw [offEventWeight, offEventWeight]
      apply Finset.sum_congr rfl
      intro off _
      have hiff : (splice a off true ∈ {ω : E → Bool | ω a = true ∧ ω b = true}) ↔
          (splice a off true ∈ {ω : E → Bool | ω b = true}) := by
        simp
      by_cases h : splice a off true ∈ {ω : E → Bool | ω b = true}
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hc => h (hiff.mp hc)), ite_eq_right h]
    rw [heq, offEventWeight_coordinate_eq r (Ne.symm hab) true true, coordinateWeight_true]
  have hfalse : offEventWeight r a {ω : E → Bool | ω a = true ∧ ω b = true} false = 0 := by
    rw [offEventWeight]
    exact Finset.sum_eq_zero (fun off _ => by
      have hnot : splice a off false ∉ {ω : E → Bool | ω a = true ∧ ω b = true} := by simp
      rw [ite_eq_right hnot])
  rw [htrue, hfalse] at hsplit
  rw [hsplit]
  ring

/-- Mass of a closed-open conjunction of two coordinate conditions. -/
theorem eventWeight_pair_false_true (r : E → ℝ) {a b : E} (hab : a ≠ b) :
    eventWeight r {ω : E → Bool | ω a = false ∧ ω b = true} = (1 - r a) * r b := by
  have hsplit := eventWeight_eq_coordinate r {ω : E → Bool | ω a = false ∧ ω b = true} a
  have htrue : offEventWeight r a {ω : E → Bool | ω a = false ∧ ω b = true} true = 0 := by
    rw [offEventWeight]
    exact Finset.sum_eq_zero (fun off _ => by
      have hnot : splice a off true ∉ {ω : E → Bool | ω a = false ∧ ω b = true} := by simp
      rw [ite_eq_right hnot])
  have hfalse : offEventWeight r a {ω : E → Bool | ω a = false ∧ ω b = true} false = r b := by
    have heq : offEventWeight r a {ω : E → Bool | ω a = false ∧ ω b = true} false =
        offEventWeight r a {ω : E → Bool | ω b = true} false := by
      rw [offEventWeight, offEventWeight]
      apply Finset.sum_congr rfl
      intro off _
      have hiff : (splice a off false ∈ {ω : E → Bool | ω a = false ∧ ω b = true}) ↔
          (splice a off false ∈ {ω : E → Bool | ω b = true}) := by
        simp
      by_cases h : splice a off false ∈ {ω : E → Bool | ω b = true}
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (fun hc => h (hiff.mp hc)), ite_eq_right h]
    rw [heq, offEventWeight_coordinate_eq r (Ne.symm hab) true false, coordinateWeight_true]
  rw [htrue, hfalse] at hsplit
  rw [hsplit]
  ring

/-! ### The triangle device -/

/-- Configuration type of the triangle `u - x - v - u`: edge `0 = uv` is enhanced,
edges `1 = ux`, `2 = xv` are the auxiliary path. -/
abbrev TriEvent : Set (Fin 3 → Bool) := {ω | ω 0 = true ∨ (ω 1 = true ∧ ω 2 = true)}

theorem triEvent_isUpperSet : IsUpperSet TriEvent := by
  intro ω η hωη hω
  rcases hω with h | ⟨h1, h2⟩
  · exact Or.inl (Bool.le_iff_imp.mp (hωη 0) h)
  · exact Or.inr ⟨Bool.le_iff_imp.mp (hωη 1) h1, Bool.le_iff_imp.mp (hωη 2) h2⟩

/-- On the triangle the enhanced edge is pivotal exactly when the auxiliary path
is not fully open. -/
theorem pivotal_triEvent_zero (ω : Fin 3 → Bool) :
    FK.AGPeeling.Pivotal TriEvent 0 ω ↔ ¬ (ω 1 = true ∧ ω 2 = true) := by
  unfold FK.AGPeeling.Pivotal TriEvent
  cases h : ω 0 <;> cases h2 : ω 2 <;> simp_all [FK.EssentialEnhancement.forceEdge]

/-- The first auxiliary edge is pivotal exactly when `e₀` is closed and the second
auxiliary edge is open. -/
theorem pivotal_triEvent_one (ω : Fin 3 → Bool) :
    FK.AGPeeling.Pivotal TriEvent 1 ω ↔ (ω 0 = false ∧ ω 2 = true) := by
  unfold FK.AGPeeling.Pivotal TriEvent
  cases h : ω 0 <;> cases h2 : ω 2 <;> simp_all [FK.EssentialEnhancement.forceEdge]

/-- The second auxiliary edge is pivotal exactly when `e₀` is closed and the first
auxiliary edge is open. -/
theorem pivotal_triEvent_two (ω : Fin 3 → Bool) :
    FK.AGPeeling.Pivotal TriEvent 2 ω ↔ (ω 0 = false ∧ ω 1 = true) := by
  unfold FK.AGPeeling.Pivotal TriEvent
  cases h : ω 0 <;> cases h2 : ω 2 <;> simp_all [FK.EssentialEnhancement.forceEdge]

theorem offPivotalWeight_triEvent_zero (r : Fin 3 → ℝ) :
    offPivotalWeight r 0 TriEvent = 1 - r 1 * r 2 := by
  rw [← eventWeight_pivotal r TriEvent 0]
  have hset : {ω : Fin 3 → Bool | FK.AGPeeling.Pivotal TriEvent 0 ω} =
      {ω : Fin 3 → Bool | ω 1 = true ∧ ω 2 = true}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, pivotal_triEvent_zero]
  rw [hset, eventWeight_compl, eventWeight_pair r (by decide)]

theorem offPivotalWeight_triEvent_one (r : Fin 3 → ℝ) :
    offPivotalWeight r 1 TriEvent = (1 - r 0) * r 2 := by
  rw [← eventWeight_pivotal r TriEvent 1]
  have hset : {ω : Fin 3 → Bool | FK.AGPeeling.Pivotal TriEvent 1 ω} =
      {ω : Fin 3 → Bool | ω 0 = false ∧ ω 2 = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, pivotal_triEvent_one]
  rw [hset, eventWeight_pair_false_true r (by decide)]

theorem offPivotalWeight_triEvent_two (r : Fin 3 → ℝ) :
    offPivotalWeight r 2 TriEvent = (1 - r 0) * r 1 := by
  rw [← eventWeight_pivotal r TriEvent 2]
  have hset : {ω : Fin 3 → Bool | FK.AGPeeling.Pivotal TriEvent 2 ω} =
      {ω : Fin 3 → Bool | ω 0 = false ∧ ω 1 = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, pivotal_triEvent_two]
  rw [hset, eventWeight_pair_false_true r (by decide)]

/-- Exact pivotal masses of the triangle device. -/
theorem pivot_masses_tri (r : Fin 3 → ℝ) :
    pivotOn {0} r TriEvent = 1 - r 1 * r 2 ∧
      pivotTotal r TriEvent = (1 - r 1 * r 2) + (1 - r 0) * r 2 + (1 - r 0) * r 1 := by
  refine ⟨?_, ?_⟩
  · rw [pivotOn_singleton, offPivotalWeight_triEvent_zero]
  · rw [pivotTotal, Fin.sum_univ_three, offPivotalWeight_triEvent_zero,
      offPivotalWeight_triEvent_one, offPivotalWeight_triEvent_two]

/-- Along the decrement profile the triangle has `pivotOn = 1 - b²`. -/
theorem pivot_masses_tri_decrement (b ε : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hε0 : 0 < ε) (hεb : ε < b) :
    pivotOn {0} (fun a => decWeight {0} a (b, ε)) TriEvent = 1 - b * b ∧
      pivotTotal (fun a => decWeight {0} a (b, ε)) TriEvent =
        1 - b * b + 2 * b * (1 - b + ε) := by
  obtain ⟨hon, htot⟩ := pivot_masses_tri (fun a => decWeight {0} a (b, ε))
  have h0 : decWeight {0} (0 : Fin 3) (b, ε) = b - ε :=
    decWeight_on (S := ({0} : Set (Fin 3))) (by simp) b ε hε0 hεb hb1
  have h1 : decWeight {0} (1 : Fin 3) (b, ε) = b :=
    decWeight_off (S := ({0} : Set (Fin 3))) (by simp) b ε hb0 hb1
  have h2 : decWeight {0} (2 : Fin 3) (b, ε) = b :=
    decWeight_off (S := ({0} : Set (Fin 3))) (by simp) b ε hb0 hb1
  simp only [h0, h1, h2] at hon htot
  refine ⟨hon, ?_⟩
  rw [htot]
  ring

/-- **The whole-region uniform pivot trade fails on the simple triangle device.**
For every `c > 0` there are admissible `0 < ε < b < 1` with
`c * pivotTotal > pivotOn`. -/
theorem not_uniform_pivotTrade_tri :
    ∀ c : ℝ, 0 < c → ∃ b ε : ℝ, 0 < b ∧ b < 1 ∧ 0 < ε ∧ ε < b ∧
      pivotOn {0} (fun a => decWeight {0} a (b, ε)) TriEvent <
        c * pivotTotal (fun a => decWeight {0} a (b, ε)) TriEvent := by
  intro c hc
  set δ : ℝ := min (c / 8) (1 / 4) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδc : δ ≤ c / 8 := min_le_left _ _
  refine ⟨1 - δ, 1 / 2, by linarith, by linarith, by norm_num, by linarith, ?_⟩
  have hb0 : 0 < 1 - δ := by linarith
  have hb1 : 1 - δ < 1 := by linarith
  have hεb : (1 : ℝ) / 2 < 1 - δ := by linarith
  obtain ⟨hon, htot⟩ := pivot_masses_tri_decrement (1 - δ) (1 / 2) hb0 hb1 (by norm_num) hεb
  rw [hon, htot]
  have h1 : 0 < 1 - δ := by linarith
  have h2 : (3:ℝ)/4 ≤ 2*(1-δ)*(1 - (1-δ) + 1/2) := by nlinarith
  have hpos : (0:ℝ) ≤ 1 - (1-δ)*(1-δ) := by
    nlinarith [mul_nonneg hδ0.le (by linarith : (0:ℝ) ≤ 2 - 2*δ)]
  have h5 : c*((3:ℝ)/4) ≤ c * (1 - (1-δ)*(1-δ) + 2*(1-δ)*(1 - (1-δ) + 1/2)) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    linarith
  have h3 : 1 - (1-δ)*(1-δ) ≤ 2*δ := by nlinarith
  nlinarith [h3, h5, hc]

end
end FK.PivotTradeObstructionCycle3
