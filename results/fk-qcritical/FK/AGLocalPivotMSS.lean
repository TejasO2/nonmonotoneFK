import FK.AGPivotTransport
import FK.AGMassDerivative
import FK.PivotTradeAGRepair
import FK.PivotTradeAGRepairIncrement

/-!
# Uniform MSS pivot trade from bounded-local modifications

The geometric AG input in this file is an actual family of local modification
maps.  A map for `e` sends every `e`-pivotal configuration to a configuration
with a pivotal enhanced edge from the candidate list for `e`.  Uniform support
and candidate-multiplicity bounds convert these maps into the expected-pivot
comparison used by Margulis--Russo.
-/

open Set
open scoped Classical BigOperators Topology

namespace FK.AGLocalPivot

open OpenPath FK.AGPeeling FK.MargulisRussoFinite

noncomputable section

universe u v w

/-- Finite subadditivity for an event indexed by a finset. -/
lemma finProb_event_exists_le {Ω : Type w} [Fintype Ω]
    (μ : FinProb Ω) {F : Type v} {s : Finset F} (B : F → Set Ω) :
    μ.event {ω | ∃ z ∈ s, ω ∈ B z} ≤ ∑ z ∈ s, μ.event (B z) := by
  classical
  unfold FinProb.event
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  simp only [Set.mem_ofPred_eq]
  by_cases hω : ∃ z ∈ s, ω ∈ B z
  · rw [ite_eq_left hω]
    obtain ⟨z, hz, hωz⟩ := hω
    have hterm : (if ω ∈ B z then μ.mass ω else 0) = μ.mass ω := ite_eq_left hωz
    calc
      μ.mass ω = (if ω ∈ B z then μ.mass ω else 0) := hterm.symm
      _ ≤ ∑ a ∈ s, if ω ∈ B a then μ.mass ω else 0 := by
        apply Finset.single_le_sum (fun a _ => ?_) hz
        split_ifs
        · exact μ.mass_nonneg ω
        · exact le_rfl
  · rw [ite_eq_right hω]
    exact Finset.sum_nonneg fun a _ => by
      split_ifs
      · exact μ.mass_nonneg ω
      · exact le_rfl

/-- Reindex a double sum over candidates by the target coordinate. -/
lemma sum_candidates {E : Type u} {F : Type v} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (candidate : E → Finset F) (B : F → ℝ) :
    (∑ e, ∑ z ∈ candidate e, B z) =
      ∑ z, ∑ _e ∈ Finset.univ.filter (fun e => z ∈ candidate e), B z := by
  classical
  calc
    (∑ e, ∑ z ∈ candidate e, B z) =
        ∑ e, ∑ z, if z ∈ candidate e then B z else 0 := by
      apply Finset.sum_congr rfl
      intro _ _
      simp
    _ = ∑ z, ∑ e, if z ∈ candidate e then B z else 0 := Finset.sum_comm
    _ = ∑ z, ∑ e ∈ Finset.univ.filter (fun e => z ∈ candidate e), B z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_filter]

/-- Bounded candidate multiplicity bounds the double sum by a target sum. -/
lemma sum_candidates_le_of_card_le {E : Type u} {F : Type v} [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]
    (candidate : E → Finset F) (B : F → ℝ) (hB : ∀ z, 0 ≤ B z) (K : ℕ)
    (hmultiplicity : ∀ z,
      (Finset.univ.filter (fun e => z ∈ candidate e)).card ≤ K) :
    (∑ e, ∑ z ∈ candidate e, B z) ≤ K * ∑ z, B z := by
  classical
  rw [sum_candidates candidate B]
  calc
    (∑ z, ∑ e ∈ Finset.univ.filter (fun e => z ∈ candidate e), B z) =
        ∑ z, ((Finset.univ.filter (fun e => z ∈ candidate e)).card : ℝ) * B z := by
      apply Finset.sum_congr rfl
      intro z _
      simp
    _ ≤ ∑ z, (K : ℝ) * B z := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (hmultiplicity z)) (hB z)
    _ = K * ∑ z, B z := by rw [Finset.mul_sum]

/-- **Global local-modification transport.**  Uniformly bounded local supports
and candidate multiplicity turn pointwise pivot conversion into a comparison of
expected pivotal counts.  The right side is the enhanced target sum; no map is
required to be injective. -/
theorem sum_pivot_le_of_local_modifications
    {E : Type u} {F : Type v} {X : Type w} [Fintype E] [Fintype F] [Fintype X]
    [DecidableEq E] [DecidableEq F] [DecidableEq X]
    (ν : X → FinProb Bool) (i : E → X) (j : F → X)
    (A : Set (X → Bool))
    (R : E → Finset X) (candidate : E → Finset F)
    (T : E → (X → Bool) → (X → Bool))
    (N K : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδν : ∀ x b, δ ≤ (ν x).mass b)
    (hsupport : ∀ e, (R e).card ≤ N)
    (hlocal : ∀ e, IsLocalModification (R e) (T e))
    (hmap : ∀ e ω, Pivotal A (i e) ω →
      ∃ z ∈ candidate e, Pivotal A (j z) (T e ω))
    (hmultiplicity : ∀ z, Nat.card {e // z ∈ candidate e} ≤ K) :
    δ ^ N * ∑ e, (FinProb.pi ν).event {ω | Pivotal A (i e) ω} ≤
      (2 : ℝ) ^ N * K *
        ∑ z, (FinProb.pi ν).event {ω | Pivotal A (j z) ω} := by
  classical
  let μ := FinProb.pi ν
  let source : E → Set (X → Bool) :=
    fun e => {ω | Pivotal A (i e) ω}
  let target : F → Set (X → Bool) :=
    fun z => {ω | Pivotal A (j z) ω}
  have hm' (z : F) : (Finset.univ.filter (fun e => z ∈ candidate e)).card ≤ K := by
    have h := hmultiplicity z
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  have hpoint (e : E) :
      δ ^ N * μ.event (source e) ≤
        (2 : ℝ) ^ N * ∑ z ∈ candidate e, μ.event (target z) := by
    have hbase := local_pi_event_mul_le ν (R e) δ hδ0 hδν (T e) (hlocal e)
      (source e) {ω | ∃ z ∈ candidate e, ω ∈ target z} (hmap e)
    have hδpow : δ ^ N ≤ δ ^ (R e).card :=
      pow_le_pow_of_le_one hδ0 hδ1 (hsupport e)
    have hleft : δ ^ N * μ.event (source e) ≤
        δ ^ (R e).card * μ.event (source e) :=
      mul_le_mul_of_nonneg_right hδpow (μ.event_nonneg _)
    have hcard : ((2 ^ (R e).card : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by
      norm_cast
      exact pow_le_pow_right₀ (by omega) (hsupport e)
    have htarget_nonnegative : 0 ≤ μ.event {ω | ∃ z ∈ candidate e, ω ∈ target z} :=
      μ.event_nonneg _
    have hright : ((2 ^ (R e).card : ℕ) : ℝ) *
          μ.event {ω | ∃ z ∈ candidate e, ω ∈ target z} ≤
        (2 : ℝ) ^ N * μ.event {ω | ∃ z ∈ candidate e, ω ∈ target z} := by
      exact mul_le_mul_of_nonneg_right hcard htarget_nonnegative
    calc
      δ ^ N * μ.event (source e) ≤ δ ^ (R e).card * μ.event (source e) := hleft
      _ ≤ ((2 ^ (R e).card : ℕ) : ℝ) *
          μ.event {ω | ∃ z ∈ candidate e, ω ∈ target z} := hbase
      _ ≤ (2 : ℝ) ^ N * μ.event {ω | ∃ z ∈ candidate e, ω ∈ target z} := hright
      _ ≤ (2 : ℝ) ^ N * ∑ z ∈ candidate e, μ.event (target z) := by
        exact mul_le_mul_of_nonneg_left
          (finProb_event_exists_le μ target) (by positivity)
  calc
    δ ^ N * ∑ e, μ.event (source e) =
        ∑ e, δ ^ N * μ.event (source e) := by rw [Finset.mul_sum]
    _ ≤ ∑ e, (2 : ℝ) ^ N * ∑ z ∈ candidate e, μ.event (target z) := by
      exact Finset.sum_le_sum fun e _ => hpoint e
    _ = (2 : ℝ) ^ N * ∑ e, ∑ z ∈ candidate e, μ.event (target z) := by
      rw [← Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ N * (K * ∑ z, μ.event (target z)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_candidates_le_of_card_le candidate _ (fun z => μ.event_nonneg _) K
          hm') (by positivity)
    _ = (2 : ℝ) ^ N * K * ∑ z, μ.event (target z) := by ring

end

end FK.AGLocalPivot


namespace FK.AGLocalPivot

open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison

noncomputable section

/-- **Uniform finite pivot trade from local modifications, in the derivative
coordinates.**  The candidates range over the enhanced edge subtype, so the
right-hand side is exactly `pivotOn S`, not a larger all-edge sum. -/
theorem pivotTrade_of_local_modifications
    {E : Type u} [Fintype E] [DecidableEq E] (r : E → ℝ) (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (S : Set E)
    (R : E → Finset E) (candidate : E → Finset {z // z ∈ S})
    (T : E → (E → Bool) → (E → Bool))
    (N K : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ e b, δ ≤ (boolLaw (r e) (hr e)).mass b)
    (hsupport : ∀ e, (R e).card ≤ N)
    (hlocal : ∀ e, IsLocalModification (R e) (T e))
    (hmap : ∀ e ω, Pivotal A e ω →
      ∃ z ∈ candidate e, Pivotal A z.1 (T e ω))
    (hmultiplicity : ∀ z : {z // z ∈ S}, Nat.card {e // z ∈ candidate e} ≤ K) :
    δ ^ N * pivotTotal r A ≤ (2 : ℝ) ^ N * K * pivotOn S r A := by
  have h := sum_pivot_le_of_local_modifications
    (ν := fun e : E => boolLaw (r e) (hr e)) (i := fun e : E => e)
    (j := fun z : {z // z ∈ S} => (z : E)) A R candidate T N K δ hδ0 hδ1
    hδlaw hsupport hlocal hmap hmultiplicity
  change δ ^ N * ∑ e, (boolProduct r hr).event {ω | Pivotal A e ω} ≤
    (2 : ℝ) ^ N * K *
      ∑ z : {z // z ∈ S}, (boolProduct r hr).event {ω | Pivotal A z.1 ω} at h
  have hpiv (e : E) :
      (boolProduct r hr).event {ω | Pivotal A e ω} = offPivotalWeight r e A := by
    rw [← eventWeight_pivotal r A e]
    exact (eventWeight_eq_boolProduct_event r hr _).symm
  have htotal :
      (∑ e, (boolProduct r hr).event {ω | Pivotal A e ω}) = pivotTotal r A := by
    unfold pivotTotal
    exact Finset.sum_congr rfl fun e _ => hpiv e
  have henhanced :
      (∑ z : {z // z ∈ S}, (boolProduct r hr).event {ω | Pivotal A z.1 ω}) =
        pivotOn S r A := by
    unfold pivotOn
    symm
    calc
      (∑ e ∈ Finset.univ.filter (fun e => e ∈ S), offPivotalWeight r e A) =
          ∑ z : {z // z ∈ S}, offPivotalWeight r z.1 A :=
        Finset.sum_subtype (p := fun e => e ∈ S)
          (s := Finset.univ.filter (fun e => e ∈ S)) (by intro x; simp) _
      _ = ∑ z : {z // z ∈ S}, (boolProduct r hr).event {ω | Pivotal A z.1 ω} :=
        Finset.sum_congr rfl fun z _ => (hpiv z.1).symm
  rwa [htotal, henhanced] at h

end

end FK.AGLocalPivot

namespace FK.AGLocalPivot
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison

/-- Positive denominator normalized from the local fibre and likelihood-ratio
constants. -/
lemma exists_pivotTrade_constant {N K : ℕ} {δ : ℝ} (hK : 0 < K)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ T P : ℝ, δ ^ N * T ≤ (2 : ℝ) ^ N * K * P →
        c * T ≤ P := by
  let D : ℝ := (2 : ℝ) ^ N * K
  have hD : 0 < D := mul_pos (pow_pos (by norm_num) _) (by exact_mod_cast hK)
  refine ⟨δ ^ N / D, div_pos (pow_pos hδ0 _) hD, ?_, ?_⟩
  · apply (div_le_one hD).2
    have hnum : δ ^ N ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have htwo : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    have hKreal : 1 ≤ (K : ℝ) := by exact_mod_cast hK
    exact hnum.trans (by dsimp [D]; nlinarith)
  · intro T P h
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hD).2
    simpa only [D, mul_comm] using h

/-- **Scale-uniform MSS pivot trade.**  If the arm events (or any other family
of finite events) have bounded-local pivot modifications with constants
independent of the index, one positive trade constant works for all of them.
The `hmap` premise is the precise remaining geometric assertion; the proof
supplies all probability transport and global aggregation. -/
theorem exists_uniform_pivotTrade_of_local_modifications
    {E : Type u} {ι : Type v} [Fintype E]
    (r : ι → E → ℝ) (hr : ∀ i e, r i e ∈ Icc (0 : ℝ) 1)
    (A : ι → Set (E → Bool)) (S : Set E)
    (R : ι → E → Finset E) (candidate : ι → E → Finset {z // z ∈ S})
    (T : ι → E → (E → Bool) → (E → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ i e b, δ ≤ (boolLaw (r i e) (hr i e)).mass b)
    (hsupport : ∀ i e, (R i e).card ≤ N)
    (hlocal : ∀ i e, IsLocalModification (R i e) (T i e))
    (hmap : ∀ i e ω, Pivotal (A i) e ω →
      ∃ z ∈ candidate i e, Pivotal (A i) z.1 (T i e ω))
    (hmultiplicity : ∀ i (z : {z // z ∈ S}),
      Nat.card {e // z ∈ candidate i e} ≤ K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ i, c * pivotTotal (r i) (A i) ≤ pivotOn S (r i) (A i) := by
  obtain ⟨c, hc0, hc1, hnormal⟩ := exists_pivotTrade_constant (N := N) (K := K) hK hδ0 hδ1
  refine ⟨c, hc0, hc1, fun i => ?_⟩
  exact hnormal _ _ (pivotTrade_of_local_modifications (r i) (hr i) (A i) S
    (R i) (candidate i) (T i) N K δ hδ0.le hδ1 (hδlaw i) (hsupport i)
    (hlocal i) (hmap i) (hmultiplicity i))


end FK.AGLocalPivot


namespace FK.AGLocalPivot

open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison

/-- An approximation index together with a point of the repaired decrement
window.  Keeping the inequalities in the type avoids any derivative or local
modification assertion at clamp collisions. -/
structure DecrementPoint (pc : ℝ) where
  n : ℕ
  b : ℝ
  ε : ℝ
  hb : b ∈ Icc (pc / 2) ((1 + pc) / 2)
  hε0 : 0 < ε
  hε : ε ≤ min (pc / 4) ((1 - pc) / 4)
  hεb : ε < b

/-- The inhomogeneous Bernoulli rate at a decrement-window point. -/
noncomputable def decrementRate {E : Type u} {pc : ℝ} (S : Set E)
    (p : DecrementPoint pc) (e : E) : ℝ :=
  decWeight S e (p.b, p.ε)

/-- Decrement-window rates are genuine Bernoulli parameters. -/
lemma decrementRate_mem {E : Type u} {pc : ℝ} (S : Set E)
    (p : DecrementPoint pc) (e : E) :
    decrementRate S p e ∈ Icc (0 : ℝ) 1 := by
  exact ⟨PivotTradeAGRepair.decWeight_nonneg e (p.b, p.ε),
    PivotTradeAGRepair.decWeight_le_one e (p.b, p.ε)⟩

/-- The exact window-trade input of the repaired subcritical AG theorem, now
proved from explicit bounded-local pivot modifications. -/
theorem exists_decrement_windowTrade_of_local_modifications
    {E : Type u} [Fintype E]
    (An : ℕ → Set (E → Bool)) (S : Set E) (pc : ℝ)
    (R : DecrementPoint pc → E → Finset E)
    (candidate : DecrementPoint pc → E → Finset {z // z ∈ S})
    (T : DecrementPoint pc → E → (E → Bool) → (E → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : DecrementPoint pc) e b,
      δ ≤ (boolLaw (decrementRate S p e) (decrementRate_mem S p e)).mass b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hmap : ∀ p e ω, Pivotal (An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal (An p.n) z.1 (T p e ω))
    (hmultiplicity : ∀ p (z : {z // z ∈ S}),
      Nat.card {e // z ∈ candidate p e} ≤ K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (b ε : ℝ), b ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → ε < b →
        c * pivotTotal (fun a => decWeight S a (b, ε)) (An n) ≤
          pivotOn S (fun a => decWeight S a (b, ε)) (An n) := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_uniform_pivotTrade_of_local_modifications
    (r := decrementRate S) (hr := decrementRate_mem S) (A := fun p => An p.n)
    (S := S) (R := R) (candidate := candidate) (T := T) N K hK δ hδ0 hδ1
    hδlaw hsupport hlocal hmap hmultiplicity
  refine ⟨c, hc0, hc1, ?_⟩
  intro n b ε hb hε0 hε hεb
  let p : DecrementPoint pc := ⟨n, b, ε, hb, hε0, hε, hεb⟩
  exact hc p

end FK.AGLocalPivot


namespace FK.AGLocalPivot

open Set MeasureTheory Filter
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- **Subcritical essential-enhancement shift from explicit local pivot maps.**
This is the AG analytic theorem with its genuine geometric and infinite-volume
inputs exposed.  It proves the same `hAG` conclusion consumed by the public FK
phase-window bridges; it does not claim that essentialness alone constructs the
maps. -/
theorem decrement_AGInput_of_local_modifications
    {E : Type u} [Fintype E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (R : DecrementPoint pc → E → Finset E)
    (candidate : DecrementPoint pc → E → Finset {z // z ∈ S})
    (T : DecrementPoint pc → E → (E → Bool) → (E → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : DecrementPoint pc) e b,
      δ ≤ (boolLaw (decrementRate S p e) (decrementRate_mem S p e)).mass b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hmap : ∀ p e ω, Pivotal (An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal (An p.n) z.1 (T p e ω))
    (hmultiplicity : ∀ p (z : {z // z ∈ S}),
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
  obtain ⟨c, hc0, hc1, hwindow⟩ :=
    exists_decrement_windowTrade_of_local_modifications An S pc R candidate T
      N K hK δ hδ0 hδ1 hδlaw hsupport hlocal hmap hmultiplicity
  exact PivotTradeAGRepair.decrement_AGInput_of_windowTrade A An S pc hpc0 hpc1 hAn
    ⟨c, hc0, hc1, hwindow⟩ hconv hbase hA hmeas

end FK.AGLocalPivot


namespace FK.AGLocalPivot

open Set MeasureTheory Filter
open OpenPath FK.AGPeeling FK.MargulisRussoFinite FK.AGMassDerivative
open FK.Finite.Comparison FK.AGDifferentialShift

/-- An approximation index together with a point of the repaired increment
window. -/
structure IncrementPoint (pc : ℝ) where
  n : ℕ
  a : ℝ
  ε : ℝ
  ha : a ∈ Icc (pc / 2) ((1 + pc) / 2)
  hε0 : 0 < ε
  hε : ε ≤ min (pc / 4) ((1 - pc) / 4)
  haε : a + ε < 1

/-- The increasing inhomogeneous rate at an increment-window point. -/
noncomputable def incrementRate {E : Type u} {pc : ℝ} (S : Set E)
    (p : IncrementPoint pc) (e : E) : ℝ :=
  incWeight S e (p.a, p.ε)

/-- Increment-window rates are genuine Bernoulli parameters. -/
lemma incrementRate_mem {E : Type u} {pc : ℝ} (S : Set E)
    (p : IncrementPoint pc) (e : E) : incrementRate S p e ∈ Icc (0 : ℝ) 1 := by
  exact PivotTradeAGRepairIncrement.incWeight_mem e (p.a, p.ε)

/-- Increment-window trade from explicit bounded-local modifications. -/
theorem exists_increment_windowTrade_of_local_modifications
    {E : Type u} [Fintype E]
    (An : ℕ → Set (E → Bool)) (S : Set E) (pc : ℝ)
    (R : IncrementPoint pc → E → Finset E)
    (candidate : IncrementPoint pc → E → Finset {z // z ∈ S})
    (T : IncrementPoint pc → E → (E → Bool) → (E → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : IncrementPoint pc) e b,
      δ ≤ (boolLaw (incrementRate S p e) (incrementRate_mem S p e)).mass b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hmap : ∀ p e ω, Pivotal (An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal (An p.n) z.1 (T p e ω))
    (hmultiplicity : ∀ p (z : {z // z ∈ S}),
      Nat.card {e // z ∈ candidate p e} ≤ K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (n : ℕ) (a ε : ℝ), a ∈ Icc (pc / 2) ((1 + pc) / 2) →
        0 < ε → ε ≤ min (pc / 4) ((1 - pc) / 4) → a + ε < 1 →
        c * pivotTotal (fun a' => incWeight S a' (a, ε)) (An n) ≤
          pivotOn S (fun a' => incWeight S a' (a, ε)) (An n) := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_uniform_pivotTrade_of_local_modifications
    (r := incrementRate S) (hr := incrementRate_mem S) (A := fun p => An p.n)
    (S := S) (R := R) (candidate := candidate) (T := T) N K hK δ hδ0 hδ1
    hδlaw hsupport hlocal hmap hmultiplicity
  refine ⟨c, hc0, hc1, ?_⟩
  intro n a ε ha hε0 hε haε
  let p : IncrementPoint pc := ⟨n, a, ε, ha, hε0, hε, haε⟩
  exact hc p

/-- **Supercritical essential-enhancement shift from explicit local pivot
maps.**  It exposes the same geometric, convergence, and supercritical-baseline
inputs as the repaired public increment theorem. -/
theorem increment_AGInput_of_local_modifications
    {E : Type u} [Fintype E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (R : IncrementPoint pc → E → Finset E)
    (candidate : IncrementPoint pc → E → Finset {z // z ∈ S})
    (T : IncrementPoint pc → E → (E → Bool) → (E → Bool))
    (N K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδlaw : ∀ (p : IncrementPoint pc) e b,
      δ ≤ (boolLaw (incrementRate S p e) (incrementRate_mem S p e)).mass b)
    (hsupport : ∀ p e, (R p e).card ≤ N)
    (hlocal : ∀ p e, IsLocalModification (R p e) (T p e))
    (hmap : ∀ p e ω, Pivotal (An p.n) e ω →
      ∃ z ∈ candidate p e, Pivotal (An p.n) z.1 (T p e ω))
    (hmultiplicity : ∀ p (z : {z // z ∈ S}),
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
  obtain ⟨c, hc0, hc1, hwindow⟩ :=
    exists_increment_windowTrade_of_local_modifications An S pc R candidate T
      N K hK δ hδ0 hδ1 hδlaw hsupport hlocal hmap hmultiplicity
  exact PivotTradeAGRepairIncrement.increment_AGInput_of_windowTrade A An S pc
    hpc0 hpc1 hAn ⟨c, hc0, hc1, hwindow⟩ hconv hbase hA hmeas

end FK.AGLocalPivot
