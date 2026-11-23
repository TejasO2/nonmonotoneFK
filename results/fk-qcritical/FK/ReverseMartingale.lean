import FK.ExteriorIdentification
import FK.ClassicalCoupling
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Reverse martingales on a decreasing filtration

The forward upcrossing estimate is applied to finite reversals.  This file
keeps the combinatorial reversal lemmas separate from their measure-theoretic
application.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace FK

/-- Explicit pairs of low/high visits force the same number of upcrossings.
Only the visits below `2 * K` are used; `t (2 * K)` is the terminal horizon. -/
theorem le_upcrossingsBefore_of_explicit_visits
    {Ω : Type*} (a b : ℝ) (f : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ → ℕ) (K : ℕ)
    (hab : a < b)
    (hstep : ∀ j < 2 * K, t j < t (j + 1))
    (hlow : ∀ j < K, f (t (2 * j)) ω < a)
    (hhigh : ∀ j < K, b < f (t (2 * j + 1)) ω) :
    K ≤ upcrossingsBefore a b f (t (2 * K)) ω := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hstep' : ∀ j < 2 * K, t j < t (j + 1) := by
        intro j hj
        exact hstep j (by omega)
      have hlow' : ∀ j < K, f (t (2 * j)) ω < a := by
        intro j hj
        exact hlow j (by omega)
      have hhigh' : ∀ j < K, b < f (t (2 * j + 1)) ω := by
        intro j hj
        exact hhigh j (by omega)
      have hIH := ih hstep' hlow' hhigh'
      have hlast := upcrossingsBefore_lt_of_exists_upcrossing (f := f) (ω := ω)
        hab (N := t (2 * K)) (N₁ := t (2 * K)) (N₂ := t (2 * K + 1))
        le_rfl (hlow K (by omega))
        (hstep (2 * K) (by omega)).le (hhigh K (by omega))
      have hmono : upcrossingsBefore a b f (t (2 * K + 1) + 1) ω ≤
          upcrossingsBefore a b f (t (2 * (K + 1))) ω := by
        apply upcrossingsBefore_mono hab
        have ht := hstep (2 * K + 1) (by omega)
        convert Nat.succ_le_of_lt ht using 1 <;> omega
      exact (Nat.succ_le_of_lt (hIH.trans_lt hlast)).trans hmono

/-- Two frequently visited strict bands admit a strictly increasing sequence
which alternates between them. -/
theorem exists_alternating_visits
    {Ω : Type*} (a b : ℝ) (f : ℕ → Ω → ℝ) (ω : Ω)
    (hlow : ∃ᶠ n in atTop, f n ω < a) (hhigh : ∃ᶠ n in atTop, b < f n ω) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      (∀ j, f (t (2 * j)) ω < a) ∧ (∀ j, b < f (t (2 * j + 1)) ω) := by
  have hl : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ f n ω < a := frequently_atTop.1 hlow
  have hh : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ b < f n ω := frequently_atTop.1 hhigh
  choose low hlowge hlowval using hl
  choose high hhighge hhighval using hh
  let t : ℕ → ℕ := Nat.rec (low 0) (fun n tn ↦
    if Even n then high (tn + 1) else low (tn + 1))
  have htzero : t 0 = low 0 := rfl
  have htsucc (n : ℕ) : t (n + 1) =
      if Even n then high (t n + 1) else low (t n + 1) := rfl
  have htmono : StrictMono t := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [htsucc]
    split_ifs
    · exact (Nat.lt_succ_self _).trans_le (hhighge _)
    · exact (Nat.lt_succ_self _).trans_le (hlowge _)
  have heven (j : ℕ) : Even (2 * j) := ⟨j, by omega⟩
  have hodd (j : ℕ) : ¬ Even (2 * j + 1) := by
    rintro ⟨r, hr⟩
    omega
  have htlow : ∀ j, f (t (2 * j)) ω < a := by
    intro j
    cases j with
    | zero => simpa [htzero] using hlowval 0
    | succ j =>
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, htsucc,
          if_neg (hodd j)]
        exact hlowval _
  have hthigh : ∀ j, b < f (t (2 * j + 1)) ω := by
    intro j
    rw [htsucc, if_pos (heven j)]
    exact hhighval _
  exact ⟨t, htmono, htlow, hthigh⟩

/-- Reversing the first `2 * K` alternating visits turns them into explicit
upcrossing visits for the negated process.  The conclusion persists at every
larger reversal horizon. -/
theorem le_upcrossingsBefore_reverse_neg_of_alternating_visits
    {Ω : Type*} (a b : ℝ) (f : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ → ℕ)
    (ht : StrictMono t)
    (htlow : ∀ j, f (t (2 * j)) ω < a)
    (hthigh : ∀ j, b < f (t (2 * j + 1)) ω)
    (hab : a < b) (K N : ℕ) (hN : t (2 * K) ≤ N) :
    K ≤ upcrossingsBefore (-b) (-a) (fun k ω ↦ -f (N - k) ω) (N + 1) ω := by
  let s : ℕ → ℕ := fun j ↦
    if j < 2 * K then N - t (2 * K - 1 - j) else N + 1
  have htmono : Monotone t := ht.monotone
  have hbound {r : ℕ} (hr : r ≤ 2 * K) : t r ≤ N :=
    (htmono hr).trans hN
  have hsstep : ∀ j < 2 * K, s j < s (j + 1) := by
    intro j hj
    by_cases hnext : j + 1 < 2 * K
    · have hrnext : 2 * K - 1 - (j + 1) < 2 * K - 1 - j := by omega
      have hrnextN : t (2 * K - 1 - (j + 1)) < N := by
        have hlt : t (2 * K - 1 - (j + 1)) < t (2 * K) :=
          ht (by omega)
        exact hlt.trans_le hN
      simpa only [s, if_pos hj, if_pos hnext] using
        Nat.sub_lt_sub_left hrnextN (ht hrnext)
    · have hlast : j + 1 = 2 * K := by omega
      have hnon := not_lt.1 hnext
      simp only [s, if_pos hj, hlast, lt_irrefl, if_neg]
      exact (Nat.sub_le _ _).trans_lt (Nat.lt_succ_self N)
  have hslow : ∀ j < K, (-f (N - s (2 * j)) ω) < -b := by
    intro j hj
    have hjeven : 2 * j < 2 * K := by omega
    have hr : 2 * K - 1 - 2 * j = 2 * (K - j - 1) + 1 := by omega
    have hrN : t (2 * K - 1 - 2 * j) ≤ N := hbound (by omega)
    have hs : s (2 * j) = N - t (2 * K - 1 - 2 * j) := by simp only [s, if_pos hjeven]
    rw [hs, Nat.sub_sub_self hrN, hr]
    exact neg_lt_neg (hthigh (K - j - 1))
  have hshigh : ∀ j < K, -a < (-f (N - s (2 * j + 1)) ω) := by
    intro j hj
    have hjodd : 2 * j + 1 < 2 * K := by omega
    have hr : 2 * K - 1 - (2 * j + 1) = 2 * (K - j - 1) := by omega
    have hrN : t (2 * K - 1 - (2 * j + 1)) ≤ N := hbound (by omega)
    have hs : s (2 * j + 1) = N - t (2 * K - 1 - (2 * j + 1)) := by
      simp only [s, if_pos hjodd]
    rw [hs, Nat.sub_sub_self hrN, hr]
    exact neg_lt_neg (htlow (K - j - 1))
  have hab' : -b < -a := neg_lt_neg hab
  have hmain := le_upcrossingsBefore_of_explicit_visits (-b) (-a)
    (fun k ω ↦ -f (N - k) ω) ω s K hab' hsstep hslow hshigh
  rw [show s (2 * K) = N + 1 by simp [s]] at hmain
  exact hmain

end FK

namespace FK

section ReverseFiltration

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
variable (G : ℕ → MeasurableSpace Ω) (hG : Antitone G)
variable (hGm : ∀ n, G n ≤ m₀)

/-- The filtration obtained by reversing a decreasing sequence below `N`. -/
def reverseFiltration (N : ℕ) : Filtration ℕ m₀ where
  seq k := G (N - k)
  mono' := by
    intro k l hkl
    exact hG (by omega)
  le' k := hGm (N - k)

/-- Conditional expectations on a decreasing filtration become an ordinary
forward martingale after reversing time below `N`. -/
theorem martingale_reverseFiltration_condExp
    {μ : @Measure Ω m₀} [IsProbabilityMeasure μ] (g : Ω → ℝ) (N : ℕ) :
    Martingale (fun k ↦ μ[g | G (N - k)]) (reverseFiltration G hG hGm N) μ := by
  refine ⟨fun k ↦ stronglyMeasurable_condExp, fun k l hkl ↦ ?_⟩
  change μ[μ[g | G (N - l)] | G (N - k)] =ᵐ[μ] μ[g | G (N - k)]
  exact condExp_condExp_of_le (hG (by omega)) (hGm (N - l))

end ReverseFiltration

end FK

namespace FK

/-- Real Markov/Doob bound for the number of upcrossings of a finite
reversal.  The right side uses only the time-zero conditional expectation,
not the reversal horizon. -/
theorem measureReal_reverse_upcrossingsBefore_le
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (g : Ω → ℝ) (a b : ℝ) (hab : a < b) (K N : ℕ) (hK : 0 < K) :
    μ.real {ω | (K : ℝ) ≤ (upcrossingsBefore (-b) (-a)
      (fun k ω ↦ -(μ[g | G (N - k)]) ω) (N + 1) ω : ℝ)} ≤
      (∫ ω, (b - (μ[g | G 0]) ω)⁺ ∂μ) / ((K : ℝ) * (b - a)) := by
  let f : ℕ → Ω → ℝ := fun k ω ↦ -(μ[g | G (N - k)]) ω
  have hm : Martingale f (reverseFiltration G hG hGm N) μ :=
    (martingale_reverseFiltration_condExp G hG hGm g N).neg
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω ↦ (upcrossingsBefore (-b) (-a) f (N + 1) ω : ℝ))
    (Eventually.of_forall fun ω ↦ Nat.cast_nonneg _)
    (hm.stronglyAdapted.integrable_upcrossingsBefore (neg_lt_neg hab)) (K : ℝ)
  have hdoob := hm.submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part
    (-b) (-a) (N + 1)
  have hdoob' : (b - a) * ∫ ω, (upcrossingsBefore (-b) (-a) f (N + 1) ω : ℝ) ∂μ ≤
      ∫ ω, (b - (μ[g | G 0]) ω)⁺ ∂μ := by
    simpa only [neg_sub_neg, Nat.sub_eq_zero_of_le (Nat.le_succ N), f] using hdoob
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast hK) (sub_pos.2 hab))).2
  calc
    μ.real {ω | (K : ℝ) ≤ (upcrossingsBefore (-b) (-a) f (N + 1) ω : ℝ)} *
        ((K : ℝ) * (b - a)) =
        ((K : ℝ) * μ.real {ω | (K : ℝ) ≤
          (upcrossingsBefore (-b) (-a) f (N + 1) ω : ℝ)}) * (b - a) := by ring
    _ ≤ (∫ ω, (upcrossingsBefore (-b) (-a) f (N + 1) ω : ℝ) ∂μ) * (b - a) :=
      mul_le_mul_of_nonneg_right hmark (sub_pos.2 hab).le
    _ = (b - a) * ∫ ω, (upcrossingsBefore (-b) (-a) f (N + 1) ω : ℝ) ∂μ := by ring
    _ ≤ _ := hdoob'

end FK

namespace FK

/-- Non-strict version of `upcrossingsBefore_lt_of_exists_upcrossing`. -/
theorem upcrossingsBefore_lt_of_exists_upcrossing_of_le
    {Ω : Type*} {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} (hab : a < b)
    {N N₁ N₂ : ℕ} (hN₁ : N ≤ N₁) (hN₁' : f N₁ ω ≤ a)
    (hN₂ : N₁ ≤ N₂) (hN₂' : b ≤ f N₂ ω) :
    upcrossingsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω := by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup
    (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_ofPred_eq, upperCrossingTime_succ_eq, hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'⟩
  rw [lowerCrossingTime, hittingBtwn_le_iff_of_lt _ (Nat.lt_succ_self _)]
  refine ⟨N₁, ⟨le_trans ?_ hN₁, hN₂⟩, hN₁'⟩
  by_cases! hN : 0 < N
  · have htime : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
      Nat.sSup_mem (upperCrossingTime_lt_nonempty hN)
      (upperCrossingTime_lt_bddAbove hab)
    rw [upperCrossingTime_eq_upperCrossingTime_of_lt
      (hN₁.trans (hN₂.trans <| Nat.le_succ _)) htime]
    exact htime.le
  · rw [Nat.le_zero] at hN
    rw [hN, upcrossingsBefore_zero, upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero']

/-- Explicit non-strict low/high visits force the same number of upcrossings. -/
theorem le_upcrossingsBefore_of_explicit_visits_of_le
    {Ω : Type*} (a b : ℝ) (f : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ → ℕ) (K : ℕ)
    (hab : a < b) (hstep : ∀ j < 2 * K, t j < t (j + 1))
    (hlow : ∀ j < K, f (t (2 * j)) ω ≤ a)
    (hhigh : ∀ j < K, b ≤ f (t (2 * j + 1)) ω) :
    K ≤ upcrossingsBefore a b f (t (2 * K)) ω := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hstep' : ∀ j < 2 * K, t j < t (j + 1) := by
        intro j hj
        exact hstep j (by omega)
      have hlow' : ∀ j < K, f (t (2 * j)) ω ≤ a := by
        intro j hj
        exact hlow j (by omega)
      have hhigh' : ∀ j < K, b ≤ f (t (2 * j + 1)) ω := by
        intro j hj
        exact hhigh j (by omega)
      have hIH := ih hstep' hlow' hhigh'
      have hlast := upcrossingsBefore_lt_of_exists_upcrossing_of_le (f := f) (ω := ω)
        hab (N := t (2 * K)) (N₁ := t (2 * K)) (N₂ := t (2 * K + 1))
        le_rfl (hlow K (by omega))
        (hstep (2 * K) (by omega)).le (hhigh K (by omega))
      have hmono : upcrossingsBefore a b f (t (2 * K + 1) + 1) ω ≤
          upcrossingsBefore a b f (t (2 * (K + 1))) ω := by
        apply upcrossingsBefore_mono hab
        have ht := hstep (2 * K + 1) (by omega)
        convert Nat.succ_le_of_lt ht using 1 <;> omega
      exact (Nat.succ_le_of_lt (hIH.trans_lt hlast)).trans hmono

end FK

namespace FK

/-- Completed upcrossings of a finite reversal persist at every larger
reversal horizon. -/
theorem upcrossingsBefore_reverse_mono
    {Ω : Type*} (a b : ℝ) (f : ℕ → Ω → ℝ) (ω : Ω) (hab : a < b)
    {N M : ℕ} (hNM : N ≤ M) :
    upcrossingsBefore a b (fun k ω ↦ f (N - k) ω) (N + 1) ω ≤
      upcrossingsBefore a b (fun k ω ↦ f (M - k) ω) (M + 1) ω := by
  let K := upcrossingsBefore a b (fun k ω ↦ f (N - k) ω) (N + 1) ω
  change K ≤ _
  by_cases hK : K = 0
  · simp [hK]
  let u : ℕ → ℕ := fun r ↦ lowerCrossingTime a b (fun k ω ↦ f (N - k) ω) (N + 1) r ω
  let v : ℕ → ℕ := fun r ↦ upperCrossingTime a b (fun k ω ↦ f (N - k) ω) (N + 1) r ω
  have hu (r : ℕ) (hr : r < K) : u r < N + 1 := by
    exact lowerCrossingTime_lt_of_lt_upcrossingsBefore (Nat.succ_pos N) hab hr
  have hv (r : ℕ) (hr : r + 1 ≤ K) : v (r + 1) < N + 1 := by
    exact upperCrossingTime_lt_of_le_upcrossingsBefore (Nat.succ_pos N) hab hr
  let t : ℕ → ℕ := fun j ↦ if j < 2 * K then
    (if Even j then u (j / 2) else v (j / 2 + 1)) else N + 1
  have htu (r : ℕ) (hr : r < K) : t (2 * r) = u r := by
    have hdiv : (2 * r) / 2 = r := by omega
    simp only [t, if_pos (by omega : 2 * r < 2 * K),
      if_pos (⟨r, by omega⟩ : Even (2 * r)), hdiv]
    rw [if_pos (even_two_mul r)]
  have htv (r : ℕ) (hr : r < K) : t (2 * r + 1) = v (r + 1) := by
    have hdiv : (2 * r + 1) / 2 = r := by omega
    simp only [t, if_pos (by omega : 2 * r + 1 < 2 * K),
      if_neg (by rintro ⟨s, hs⟩; omega : ¬ Even (2 * r + 1)), hdiv]
  have htnext (r : ℕ) (hr : r + 1 < K) : t (2 * r + 1 + 1) = u (r + 1) := by
    have hdiv : (2 * r + 1 + 1) / 2 = r + 1 := by omega
    simp only [t, if_pos (by omega : 2 * r + 1 + 1 < 2 * K),
      if_pos (⟨r + 1, by omega⟩ : Even (2 * r + 1 + 1)), hdiv]
    have he : Even (2 * r + 1 + 1) := ⟨r + 1, by omega⟩
    rw [if_pos he]
  have htlast (r : ℕ) (hr : r + 1 = K) : t (2 * r + 1 + 1) = N + 1 := by
    simp only [t, if_neg (by omega : ¬2 * r + 1 + 1 < 2 * K)]
  have htstep : ∀ j < 2 * K, t j < t (j + 1) := by
    intro j hj
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
    · have hr : r < K := by omega
      have hvpos : v (r + 1) ≠ N + 1 := (hv r hr).ne
      have hst := lowerCrossingTime_lt_upperCrossingTime (f := fun k ω ↦ f (N - k) ω)
        (ω := ω) hab hvpos
      rw [htu r hr, htv r hr]
      simpa [u, v] using hst
    · have hr : r + 1 ≤ K := by omega
      by_cases hlast : r + 1 = K
      · rw [htv r (by omega), htlast r hlast]
        exact hv r hr
      · have hrnext : r + 1 < K := by omega
        have hupos : u (r + 1) ≠ N + 1 := (hu (r + 1) hrnext).ne
        have hst := upperCrossingTime_lt_lowerCrossingTime
          (f := fun k ω ↦ f (N - k) ω) (ω := ω) hab hupos
        rw [htv r (by omega), htnext r hrnext]
        simpa [u, v] using hst
  have huntop (k : ℕ) : ((k : WithTop ℕ).untopA) = k := rfl
  have htlow : ∀ r < K, f (N - t (2 * r)) ω ≤ a := by
    intro r hr
    have hval := stoppedValue_lowerCrossingTime
      (f := fun k ω ↦ f (N - k) ω) (ω := ω) (N := N + 1) (n := r) (hu r hr).ne
    change f (N - ((u r : WithTop ℕ).untopA)) ω ≤ a at hval
    rw [huntop] at hval
    rwa [htu r hr]
  have hthigh : ∀ r < K, b ≤ f (N - t (2 * r + 1)) ω := by
    intro r hr
    have hval := stoppedValue_upperCrossingTime
      (f := fun k ω ↦ f (N - k) ω) (ω := ω) (N := N + 1) (n := r)
      (hv r (by omega)).ne
    change b ≤ f (N - ((v (r + 1) : WithTop ℕ).untopA)) ω at hval
    rw [huntop] at hval
    rwa [htv r hr]
  have hsbound : ∀ j < 2 * K, t j ≤ N := by
    intro j hj
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
    · have hr : r < K := by omega
      rw [htu r hr]
      exact Nat.lt_succ_iff.mp (hu r hr)
    · have hr : r + 1 ≤ K := by omega
      rw [htv r (by omega)]
      exact Nat.lt_succ_iff.mp (hv r hr)
  let s : ℕ → ℕ := fun j ↦ t j + (M - N)
  have hsstep : ∀ j < 2 * K, s j < s (j + 1) := by
    intro j hj
    exact Nat.add_lt_add_right (htstep j hj) _
  have hslow : ∀ r < K, f (M - s (2 * r)) ω ≤ a := by
    intro r hr
    have heq : M - s (2 * r) = N - t (2 * r) := by
      have hb := hsbound (2 * r) (by omega)
      dsimp [s]
      omega
    rw [heq]
    exact htlow r hr
  have hshigh : ∀ r < K, b ≤ f (M - s (2 * r + 1)) ω := by
    intro r hr
    have heq : M - s (2 * r + 1) = N - t (2 * r + 1) := by
      have hb := hsbound (2 * r + 1) (by omega)
      dsimp [s]
      omega
    rw [heq]
    exact hthigh r hr
  have hmain := le_upcrossingsBefore_of_explicit_visits_of_le a b
    (fun k ω ↦ f (M - k) ω) ω s K hab hsstep hslow hshigh
  have htend : t (2 * K) = N + 1 := by simp [t]
  have hst : s (2 * K) = M + 1 := by
    dsimp [s]
    rw [htend]
    omega
  rw [hst] at hmain
  exact hmain

end FK


namespace FK

/-- A reverse conditional-expectation process cannot oscillate infinitely often
across a fixed nontrivial interval, except on a null set.  The proof uses the
finite-reversal upcrossing estimate and continuity from below; no boundedness
or integrability assumption on the original function is needed here. -/
theorem ae_not_frequently_alternating_condExp
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (g : Ω → ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂μ, ¬((∃ᶠ n in atTop, (μ[g | G n]) ω < a) ∧
      ∃ᶠ n in atTop, b < (μ[g | G n]) ω) := by
  let C : ℝ := ∫ ω, (b - (μ[g | G 0]) ω)⁺ ∂μ
  let H : Set Ω := {ω | (∃ᶠ n in atTop, (μ[g | G n]) ω < a) ∧
    ∃ᶠ n in atTop, b < (μ[g | G n]) ω}
  have hbound (K : ℕ) (hK : 0 < K) :
      μ.real H ≤ C / ((K : ℝ) * (b - a)) := by
    let U : ℕ → Set Ω := fun N ↦ {ω | (K : ℝ) ≤
      (upcrossingsBefore (-b) (-a)
        (fun k ω ↦ -(μ[g | G (N - k)]) ω) (N + 1) ω : ℝ)}
    have hUN (N : ℕ) : μ.real (U N) ≤ C / ((K : ℝ) * (b - a)) := by
      exact measureReal_reverse_upcrossingsBefore_le G hG hGm g a b hab K N hK
    have hUmono : Monotone U := by
      intro N M hNM ω hω
      have hmono := upcrossingsBefore_reverse_mono (-b) (-a)
        (fun k ω ↦ -(μ[g | G k]) ω) ω (neg_lt_neg hab) hNM
      change (K : ℝ) ≤ (upcrossingsBefore (-b) (-a)
        (fun k ω ↦ -(μ[g | G (N - k)]) ω) (N + 1) ω : ℝ) at hω
      change (K : ℝ) ≤ (upcrossingsBefore (-b) (-a)
        (fun k ω ↦ -(μ[g | G (M - k)]) ω) (M + 1) ω : ℝ)
      exact hω.trans (by exact_mod_cast hmono)
    have hHU : H ⊆ ⋃ N, U N := by
      intro ω hω
      obtain ⟨t, ht, htlow, hthigh⟩ := exists_alternating_visits a b
        (fun n ↦ μ[g | G n]) ω hω.1 hω.2
      refine Set.mem_iUnion.2 ⟨t (2 * K), ?_⟩
      change (K : ℝ) ≤ (upcrossingsBefore (-b) (-a)
        (fun k ω ↦ -(μ[g | G (t (2 * K) - k)]) ω)
        (t (2 * K) + 1) ω : ℝ)
      have hmain := le_upcrossingsBefore_reverse_neg_of_alternating_visits
        a b (fun n ↦ μ[g | G n]) ω t ht htlow hthigh hab K
        (t (2 * K)) le_rfl
      exact_mod_cast hmain
    have hlimE : Tendsto (fun N ↦ μ (U N)) atTop (𝓝 (μ (⋃ N, U N))) := by
      simpa only [Function.comp_def] using
        (tendsto_measure_iUnion_atTop (μ := μ) hUmono)
    have hlimReal : Tendsto (fun N ↦ μ.real (U N)) atTop
        (𝓝 (μ.real (⋃ N, U N))) := by
      have h := (ENNReal.tendsto_toReal (measure_ne_top μ (⋃ N, U N))).comp hlimE
      simpa only [Measure.real, Function.comp_def] using h
    have hU : μ.real (⋃ N, U N) ≤ C / ((K : ℝ) * (b - a)) :=
      le_of_tendsto hlimReal (Eventually.of_forall hUN)
    exact (measureReal_mono hHU).trans hU
  have hden : Tendsto (fun K : ℕ ↦ C / ((K : ℝ) * (b - a))) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (C / (b - a))
    apply h.congr'
    filter_upwards [] with K
    rw [mul_comm, div_mul_eq_div_div]
  have hle : μ.real H ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hden ?_
    filter_upwards [eventually_gt_atTop 0] with K hK
    exact hbound K hK
  have hzero : μ.real H = 0 := le_antisymm hle measureReal_nonneg
  have hnull : μ H = 0 := (measureReal_eq_zero_iff (measure_ne_top μ H)).1 hzero
  rw [ae_iff]
  simpa only [H, not_not] using hnull

/-- Lévy's downward theorem, existence form, for reverse conditional
expectations which are bounded uniformly in probability by one deterministic
constant. -/
theorem exists_ae_tendsto_condExp_iInf_of_bounded
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ]
    {G : ℕ → MeasurableSpace Ω} (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (g : Ω → ℝ)
    (hbdd : ∃ R : ℝ, ∀ n, ∀ᵐ ω ∂μ, |(μ[g | G n]) ω| ≤ R) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n ↦ (μ[g | G n]) ω) atTop (𝓝 c) := by
  obtain ⟨R, hR⟩ := hbdd
  have hosc : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      ¬((∃ᶠ n in atTop, (μ[g | G n]) ω < (a : ℝ)) ∧
        ∃ᶠ n in atTop, (b : ℝ) < (μ[g | G n]) ω) := by
    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab
    exact ae_not_frequently_alternating_condExp G hG hGm g (Rat.cast_lt.2 hab)
  have hRall : ∀ᵐ ω ∂μ, ∀ n, |(μ[g | G n]) ω| ≤ R := ae_all_iff.2 hR
  filter_upwards [hosc, hRall] with ω hωosc hωR
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n ↦ |(μ[g | G n]) ω|) :=
    Filter.isBoundedUnder_of ⟨R, hωR⟩
  refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_
    (isBoundedUnder_le_abs.1 hb).1 (isBoundedUnder_le_abs.1 hb).2
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  exact hωosc a b (Rat.cast_lt.1 hab)

end FK


namespace FK

/-- Lévy's downward theorem to the infimum sigma-algebra, in the bounded
`L²` case.  The existing `L¹` projection theorem identifies the pointwise
limit; the upcrossing argument above supplies the full almost-everywhere
sequence, not merely a subsequence. -/
theorem tendsto_ae_condExp_iInf_of_memLp_two_of_bounded
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ]
    {G : ℕ → MeasurableSpace Ω} (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (hGm₀ : (⨅ n, G n) ≤ m₀) {g : Ω → ℝ} (hg : MemLp g 2 μ)
    (hbdd : ∃ R : ℝ, ∀ n, ∀ᵐ ω ∂μ, |(μ[g | G n]) ω| ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ[g | G n]) ω) atTop
      (𝓝 ((μ[g | ⨅ n, G n]) ω)) := by
  classical
  let c : Ω → ℝ := fun ω ↦ if h : ∃ c : ℝ,
      Tendsto (fun n ↦ (μ[g | G n]) ω) atTop (𝓝 c) then h.choose else 0
  have hc : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ[g | G n]) ω) atTop (𝓝 (c ω)) := by
    filter_upwards [exists_ae_tendsto_condExp_iInf_of_bounded hG hGm g hbdd] with ω hω
    simp only [c, dif_pos hω]
    exact hω.choose_spec
  have hcIn : TendstoInMeasure μ (fun n ↦ μ[g | G n]) atTop c :=
    tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (stronglyMeasurable_condExp.mono (hGm n)).aestronglyMeasurable) hc
  have htailIn : TendstoInMeasure μ (fun n ↦ μ[g | G n]) atTop μ[g | ⨅ n, G n] :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (tendsto_eLpNorm_one_condExp_iInf_of_memLp_two hG hGm hGm₀ hg)
  have heq : c =ᵐ[μ] μ[g | ⨅ n, G n] := tendstoInMeasure_ae_unique hcIn htailIn
  filter_upwards [hc, heq] with ω hω hωeq
  rwa [hωeq] at hω

/-- Almost-everywhere downward convergence of elementary conditional
probabilities. -/
theorem tendsto_ae_condExp_indicator_iInf
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}
    [IsProbabilityMeasure μ]
    {G : ℕ → MeasurableSpace Ω} (hG : Antitone G) (hGm : ∀ n, G n ≤ m₀)
    (hGm₀ : (⨅ n, G n) ≤ m₀) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ⟦A | G n⟧) ω) atTop
      (𝓝 ((μ⟦A | ⨅ n, G n⟧) ω)) := by
  apply tendsto_ae_condExp_iInf_of_memLp_two_of_bounded hG hGm hGm₀
  · exact memLp_indicator_const 2 hA.nullMeasurableSet (1 : ℝ)
      (Or.inr (measure_ne_top μ A))
  · refine ⟨1, fun n ↦ ?_⟩
    apply ae_bdd_abs_condExp_of_ae_bdd_abs
    filter_upwards [] with ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]

end FK

namespace FKLimit

open FK

/-- Full almost-everywhere reverse-martingale convergence on the exterior
filtration determined by a monotone cofinal sequence of finite edge sets. -/
theorem tendsto_ae_condExp_indicator_outside_to_tail
    {E : Type*} {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {A : Set (Configuration E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ⟦A | outsideSigma (S n)⟧) ω) atTop
      (𝓝 ((μ⟦A | tailSigma⟧) ω)) := by
  have hanti : Antitone (fun n ↦ outsideSigma (S n)) := by
    intro m n hmn
    exact outsideSigma_anti (hS hmn)
  have hle : ∀ n, outsideSigma (S n) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    fun n ↦ outsideSigma_le _
  have hleInf : (⨅ n, outsideSigma (S n)) ≤
      (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    (iInf_le (fun n ↦ outsideSigma (S n)) 0).trans (hle 0)
  have h := FK.tendsto_ae_condExp_indicator_iInf (μ := μ)
    (G := fun n ↦ outsideSigma (S n)) hanti hle hleInf hA
  simpa only [iInf_outsideSigma_eq_tailSigma S hcof] using h

/-- If the exterior tail is zero--one, exterior conditional probabilities
converge almost everywhere to the unconditional mass. -/
theorem tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn
    {E : Type*} {μ : Measure (Configuration E)} [IsProbabilityMeasure μ]
    (S : ℕ → Finset E) (hS : Monotone S)
    (hcof : ∀ T : Finset E, ∃ n, T ⊆ S n)
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (htail : FK.ZeroOneOn tailSigma μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (μ⟦A | outsideSigma (S n)⟧) ω) atTop
      (𝓝 (μ.real A)) := by
  filter_upwards [tendsto_ae_condExp_indicator_outside_to_tail S hS hcof hA,
    condExp_indicator_of_zeroOneOn_tailSigma μ htail hA] with ω hlim hconst
  simpa only [hconst] using hlim

end FKLimit


namespace FK.InfiniteVolume

open FK

universe u v

/-- Almost-everywhere convergence of the actual exterior finite-FK conditional
probabilities for an extremal DLR law.  Unlike the earlier `L¹` theorem, the
conclusion is full-sequence pointwise convergence on a full-measure set. -/
theorem tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
    {E : Type u} (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)))
    {A : Set (Configuration E)} {T : Finset E}
    (hAT : FKLimit.DependsOnCoordinates A T) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ ((exh.box n).conditionalLaw hq hp (Φ.partition n)
        (FKLimit.exteriorRestriction (exh.box n).edges ω) :
        Measure (Configuration E)).real A) atTop
        (𝓝 ((μ : Measure (Configuration E)).real A)) := by
  have htail : FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (Configuration E)) :=
    zeroOneOn_tailSigma_of_extremal_dlr exh Φ hq hp μ hμ hext
  let S : ℕ → Finset E := fun n ↦ (exh.box n).edges
  have hcof : ∀ T : Finset E, ∃ n, T ⊆ S n := by
    intro T
    exact (exh.eventually_subset T).exists
  have hbase := FKLimit.tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn
    (μ := (μ : Measure (Configuration E))) S exh.monotone hcof
    hAT.measurableSet htail
  have hid : ∀ᵐ ω ∂(μ : Measure (Configuration E)), ∀ n,
      T ⊆ (exh.box n).edges →
      ((μ : Measure (Configuration E))⟦A |
        FKLimit.outsideSigma (exh.box n).edges⟧) ω =
        ((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real A := by
    rw [ae_all_iff]
    intro n
    by_cases hn : T ⊆ (exh.box n).edges
    · filter_upwards [(exh.box n).condExp_of_dependsOn_edges_of_isDLR hq hp
        (Φ.partition n) (Φ.measurable_partition n) μ (hμ n) (hAT.mono hn)] with ω hω
      exact fun _ ↦ hω
    · exact Eventually.of_forall fun _ h ↦ (hn h).elim
  filter_upwards [hbase, hid] with ω hlim hidω
  apply hlim.congr'
  filter_upwards [exh.eventually_subset T] with n hn
  exact hidω n hn

end FK.InfiniteVolume


namespace FK.InfiniteVolume

lemma dependsOnCoordinates_cylinder {E : Type*} (I : Finset E)
    (S : Set (I → Bool)) : FKLimit.DependsOnCoordinates (MeasureTheory.cylinder I S) I := by
  intro ω η h
  simp only [MeasureTheory.mem_cylinder, Finset.restrict_def]
  have heq : (fun e : I ↦ ω e.1) = (fun e : I ↦ η e.1) := by
    funext e
    exact h e.1 e.2
  rw [heq]

/-- On a countable Boolean configuration space, convergence of masses of all
finite-base cylinders implies weak convergence.  Compactness supplies every
subsequential limit, and the cylinder hypothesis identifies that limit. -/
theorem tendsto_probabilityMeasure_of_cylinder_tendsto
    {E : Type*} [Countable E]
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    (h : ∀ (I : Finset E) (S : Set (I → Bool)),
      Tendsto (fun n ↦ μs n (MeasureTheory.cylinder I S)) atTop
        (𝓝 (μ (MeasureTheory.cylinder I S)))) :
    Tendsto μs atTop (𝓝 μ) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq (fun k ↦ μs (ns k))
  have hνμ : ν = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    apply FKModel.measure_ext_of_eq_on_boolCylinders
    intro I S
    have hleft := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
      (dependsOnCoordinates_cylinder I S).isClopen
    have hright := (h I S).comp (hns.comp hφ.tendsto_atTop)
    simpa [ProbabilityMeasure.coeFn_def, measure_ne_top] using
      congrArg (fun x : NNReal ↦ (x : ENNReal)) (tendsto_nhds_unique hleft hright)
  refine ⟨φ, ?_⟩
  simpa only [Function.comp_def, hνμ] using hν

/-- **Weak almost-everywhere limiting laws for extremal DLR measures.**
Conditional on the exterior of the exhaustion boxes, the actual finite FK
laws converge weakly to the original extremal DLR law almost surely.

The convergence takes place in the weak topology on `ProbabilityMeasure` of
the compact metrizable Boolean product.  No measurability of the random
probability-measure-valued map is required by this pointwise statement. -/
theorem tendsto_ae_exteriorConditionalLaw_probabilityMeasure_of_extremal_dlr
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E))) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ (exh.box n).conditionalLaw hq hp (Φ.partition n)
        (FKLimit.exteriorRestriction (exh.box n).edges ω)) atTop (𝓝 μ) := by
  have hcyl (I : Finset E) (S : Set (I → Bool)) :
      ∀ᵐ ω ∂(μ : Measure (Configuration E)),
        Tendsto (fun n ↦ (((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real (MeasureTheory.cylinder I S))) atTop
          (𝓝 ((μ : Measure (Configuration E)).real (MeasureTheory.cylinder I S))) :=
    tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
      exh Φ hq hp μ hμ hext (dependsOnCoordinates_cylinder I S)
  have hI : ∀ I : Finset E, ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      ∀ S : Set (I → Bool),
        Tendsto (fun n ↦ (((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real (MeasureTheory.cylinder I S))) atTop
          (𝓝 ((μ : Measure (Configuration E)).real (MeasureTheory.cylinder I S))) :=
    fun I ↦ ae_all_iff.2 (hcyl I)
  filter_upwards [ae_all_iff.2 hI] with ω hω
  apply tendsto_probabilityMeasure_of_cylinder_tendsto
  intro I S
  rw [← NNReal.tendsto_coe]
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hω I S

end FK.InfiniteVolume


namespace FK.InfiniteVolume

/-- Weak convergence on countable Boolean configurations is equivalent to
real-valued convergence on every finite-base cylinder. -/
theorem tendsto_probabilityMeasure_iff_cylinder_real_tendsto
    {E : Type*} [Countable E]
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E)) :
    Tendsto μs atTop (𝓝 μ) ↔
      ∀ (I : Finset E) (S : Set (I → Bool)),
        Tendsto (fun n ↦ (μs n : Measure (Configuration E)).real
          (MeasureTheory.cylinder I S)) atTop
          (𝓝 ((μ : Measure (Configuration E)).real (MeasureTheory.cylinder I S))) := by
  constructor
  · intro h I S
    have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
      (dependsOnCoordinates_cylinder I S).isClopen
    rw [← NNReal.tendsto_coe] at ht
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using ht
  · intro h
    apply tendsto_probabilityMeasure_of_cylinder_tendsto
    intro I S
    rw [← NNReal.tendsto_coe]
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h I S

namespace FiniteBox

/-- Changing the exterior of a conditional FK law does not change the mass of
an event supported on the box.  This compares the actual external-boundary
law with the closed-exterior extension used by `FKLimitMeasures`. -/
theorem finiteVolumeLaw_real_eq_conditionalLaw_real_of_dependsOn
    {E : Type*} (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {A : Set (Configuration E)} {T : Finset E}
    (hAT : FKLimit.DependsOnCoordinates A T) (hT : T ⊆ B.edges) :
    (B.finiteVolumeLaw hq hp (α η) : Measure (Configuration E)).real A =
      (B.conditionalLaw hq hp α η : Measure (Configuration E)).real A := by
  have hA : A = B.interiorRestriction ⁻¹' (B.interiorRestriction '' A) :=
    B.eq_preimage_interiorRestriction_image (hAT.mono hT)
  rw [hA]
  rw [B.conditionalLaw_real_interior_preimage hq hp α η MeasurableSet.of_discrete]
  change (B.conditionalLaw hq hp (fun _ ↦ α η) B.closedExterior :
    Measure (Configuration E)).real (B.interiorRestriction ⁻¹'
      (B.interiorRestriction '' A)) = _
  rw [B.conditionalLaw_real_interior_preimage hq hp (fun _ ↦ α η)
    B.closedExterior MeasurableSet.of_discrete]

end FiniteBox

/-- Along an exhaustion, external-boundary conditional laws and their
closed-exterior finite-volume representatives have the same weak limits. -/
theorem tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (η : ∀ n, (exh.box n).Exterior)
    (μ : ProbabilityMeasure (Configuration E)) :
    Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw hq hp (α n (η n))) atTop (𝓝 μ) ↔
      Tendsto (fun n ↦ (exh.box n).conditionalLaw hq hp (α n) (η n)) atTop (𝓝 μ) := by
  rw [tendsto_probabilityMeasure_iff_cylinder_real_tendsto,
    tendsto_probabilityMeasure_iff_cylinder_real_tendsto]
  apply forall_congr'
  intro I
  apply forall_congr'
  intro S
  apply Filter.tendsto_congr'
  filter_upwards [exh.eventually_subset I] with n hn
  exact ((exh.box n).finiteVolumeLaw_real_eq_conditionalLaw_real_of_dependsOn
    hq hp (α n) (η n) (dependsOnCoordinates_cylinder I S) hn)

end FK.InfiniteVolume


namespace FK.InfiniteVolume

open FK

/-- **Proposition 1.8(1), including its weak-limit-class inclusion.**  Every
extremal DLR measure is an actual weak limit of finite FK measures with
deterministically chosen boundary partitions.  The boundary partitions are
obtained by selecting one configuration in the full-measure convergence set
above; the canonical closed-exterior representatives have the same weak
limit. -/
theorem mem_fkLimitMeasures_of_extremal_dlr
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    (hext : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E))) :
    μ ∈ FKLimitMeasures exh hq hp := by
  have hae := tendsto_ae_exteriorConditionalLaw_probabilityMeasure_of_extremal_dlr
    exh Φ hq hp μ hμ hext
  obtain ⟨ω, hω⟩ := hae.exists
  let η : ∀ n, (exh.box n).Exterior := fun n ↦
    FKLimit.exteriorRestriction (exh.box n).edges ω
  refine ⟨fun n ↦ Φ.partition n (η n), ?_⟩
  exact (tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw
    exh hq hp Φ.partition η μ).2 hω

end FK.InfiniteVolume
