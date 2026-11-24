/-
# The Aizenman--Grimmett enhancement input of Theorem 1.4, isolated

The proof of Theorem 1.4 of Beffara--Faipeur--Oke (arXiv:2512.16486) reduces the
strict critical-point shift to a statement about *product Bernoulli measures*
whose weights are enhanced (or thinned) on a set `S` of edges.  This file gives
that statement its two natural forms

* `ActivationShift`   -- the enhancement form of Aizenman--Grimmett, i.e.
  Conjecture 1 of Balister--Bollobas--Riordan, *Essential enhancements
  revisited*, arXiv:1402.0834, for the edge-activation rule supported on `S`;
* `DeactivationShift` -- its thinning mirror image, needed for the upper window.

For each form we prove the exact equivalence with the `hAG` hypothesis consumed
by `FK.EssentialWindow.upperWindow_of_AG_*` and `lowerWindow_of_AG_*`, and the
resulting parameter windows.  Nothing here asserts a shift: both predicates are
ordinary propositions about genuine product measures.
-/
import FK.AGWindow
import FK.EssentialEnhancement
import FK.FKQuasiTransitiveDevices
import FK.ClusterTail
import CurvatureVariance.Infra.Percolation.Critical

open Set MeasureTheory ProbabilityTheory
open Classical
open CurvatureVariance.Infra.Percolation
open scoped ENNReal NNReal unitInterval

namespace FK.AGShift

noncomputable section

variable {E : Type*} [Countable E]

/-! ## Real-valued weights and their clamped unit-interval profiles

Using a proof-free clamped profile keeps every statement free of dependent
proof arguments; the comparison with the proof-carrying profiles of
`FK.EssentialWindow` is a single lemma below. -/

/-- Clamp a real weight into the unit interval. -/
def clampProfile (w : E → ℝ) : E → unitInterval :=
  fun e => ⟨max 0 (min 1 (w e)), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem coe_clampProfile {w : E → ℝ} (h0 : ∀ e, 0 ≤ w e) (h1 : ∀ e, w e ≤ 1) (e : E) :
    (clampProfile w e : ℝ) = w e := by
  show max 0 (min 1 (w e)) = w e
  rw [min_eq_right (h1 e), max_eq_right (h0 e)]

/-- Weights when every edge of `S` is enhanced from `a` to `a + ε`. -/
def incWeight (S : Set E) (a ε : ℝ) (e : E) : ℝ :=
  if e ∈ S then a + ε else a

/-- Weights when every edge of `S` is thinned from `b` to `b - ε`. -/
def decWeight (S : Set E) (b ε : ℝ) (e : E) : ℝ :=
  if e ∈ S then b - ε else b

/-- Weights when every edge of `S` receives an independent activation of
probability `s` on top of the base probability `p`. -/
def actWeight (S : Set E) (p s : ℝ) (e : E) : ℝ :=
  if e ∈ S then p + s * (1 - p) else p

/-- Weights when every edge of `S` is thinned by an independent deactivation of
probability `s`. -/
def deactWeight (S : Set E) (b s : ℝ) (e : E) : ℝ :=
  if e ∈ S then b * (1 - s) else b

def incProfile (S : Set E) (a ε : ℝ) : E → unitInterval := clampProfile (incWeight S a ε)
def decProfile (S : Set E) (b ε : ℝ) : E → unitInterval := clampProfile (decWeight S b ε)
def actProfile (S : Set E) (p s : ℝ) : E → unitInterval := clampProfile (actWeight S p s)
def deactProfile (S : Set E) (b s : ℝ) : E → unitInterval := clampProfile (deactWeight S b s)

@[simp] theorem coe_incProfile {S : Set E} {a ε : ℝ} (ha0 : 0 ≤ a) (haε1 : a + ε ≤ 1)
    (hε0 : 0 ≤ ε) (e : E) : (incProfile S a ε e : ℝ) = incWeight S a ε e := by
  apply coe_clampProfile
  · intro e; unfold incWeight; split_ifs <;> linarith
  · intro e; unfold incWeight; split_ifs <;> linarith

@[simp] theorem coe_decProfile {S : Set E} {b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hε0 : 0 ≤ ε) (hεb : ε ≤ b) (e : E) : (decProfile S b ε e : ℝ) = decWeight S b ε e := by
  apply coe_clampProfile
  · intro e; unfold decWeight; split_ifs <;> linarith
  · intro e; unfold decWeight; split_ifs <;> linarith

@[simp] theorem coe_actProfile {S : Set E} {p s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (e : E) : (actProfile S p s e : ℝ) = actWeight S p s e := by
  apply coe_clampProfile
  · intro e; unfold actWeight; split_ifs <;> nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hp1)]
  · intro e; unfold actWeight; split_ifs
    · nlinarith [mul_le_mul_of_nonneg_right hs1 (sub_nonneg.mpr hp1)]
    · exact hp1

@[simp] theorem coe_deactProfile {S : Set E} {b s : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (e : E) :
    (deactProfile S b s e : ℝ) = deactWeight S b s e := by
  apply coe_clampProfile
  · intro e; unfold deactWeight; split_ifs
    · exact mul_nonneg hb0 (sub_nonneg.mpr hs1)
    · exact hb0
  · intro e; unfold deactWeight; split_ifs
    · nlinarith [mul_nonneg hb0 hs0]
    · exact hb1

/-! ### Agreement with the proof-carrying profiles of `FK.EssentialWindow` -/

theorem incProfile_eq (S : Set E) (a ε : ℝ) (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε) (haε1 : a + ε ≤ 1) :
    incProfile S a ε = FK.EssentialWindow.incrementProfile S a ε ha0 hε0 haε1 := by
  funext e
  apply Subtype.ext
  rw [coe_incProfile ha0 haε1 hε0]
  simp only [incWeight, FK.EssentialWindow.incrementProfile]
  split_ifs <;> rfl

theorem decProfile_eq (S : Set E) (b ε : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hε0 : 0 ≤ ε)
    (hεb : ε ≤ b) :
    decProfile S b ε = FK.EssentialWindow.decrementProfile S b ε hb0 hb1 hε0 hεb := by
  funext e
  apply Subtype.ext
  rw [coe_decProfile hb0 hb1 hε0 hεb]
  simp only [decWeight, FK.EssentialWindow.decrementProfile]
  split_ifs <;> rfl

/-! ## The two shift statements -/

/-- **Aizenman--Grimmett strict shift, activation form.**  For every activation
probability `s > 0` there is a threshold `π < pc` such that the `s`-activated
model percolates for every base parameter `p` in `(π, pc)`.

At `pc = p_c(G)`, `A` the percolation event and `S` a set of edges at bounded
distance from every edge, this is exactly Conjecture 1 of
Balister--Bollobas--Riordan (arXiv:1402.0834) for the edge-activation rule
supported on `S`: their `π(s)` is this `π`, and the bounded-distance density of
`S` is what makes the activation density positive in their statement. -/
def ActivationShift (A : Set (E → Bool)) (pc : ℝ) (S : Set E) : Prop :=
  ∀ (s : ℝ) (_hs0 : 0 < s) (_hs1 : s ≤ 1),
    ∃ π : ℝ, π < pc ∧
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), π < p → p < pc →
        ((FKLimit.bernoulliProduct (actProfile S p s)) : Measure (E → Bool)) A = 1

/-- **Strict shift, deactivation form.**  For every thinning probability `s > 0`
there is a threshold `π > pc` such that the `s`-thinned model does not percolate
for any base parameter `b` in `(pc, π)`.  This is the mirror image of the
Aizenman--Grimmett statement needed for the upper window of Theorem 1.4. -/
def DeactivationShift (A : Set (E → Bool)) (pc : ℝ) (S : Set E) : Prop :=
  ∀ (s : ℝ) (_hs0 : 0 < s) (_hs1 : s ≤ 1),
    ∃ π : ℝ, pc < π ∧
      ∀ (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1), pc < b → b < π →
        ((FKLimit.bernoulliProduct (deactProfile S b s)) : Measure (E → Bool)) A = 0

/-! ### Monotonicity in the enhanced set -/

theorem actWeight_mono {S T : Set E} {p s : ℝ} (hST : S ⊆ T) (hp1 : p ≤ 1) (hs0 : 0 ≤ s)
    (e : E) : actWeight S p s e ≤ actWeight T p s e := by
  unfold actWeight
  by_cases he : e ∈ S
  · rw [if_pos he, if_pos (hST he)]
  · rw [if_neg he]
    by_cases heT : e ∈ T
    · rw [if_pos heT]
      have hnn : 0 ≤ s * (1 - p) := mul_nonneg hs0 (sub_nonneg.mpr hp1)
      linarith
    · rw [if_neg heT]

theorem deactWeight_anti {S T : Set E} {b s : ℝ} (hST : S ⊆ T) (hb0 : 0 ≤ b) (hs0 : 0 ≤ s)
    (e : E) : deactWeight T b s e ≤ deactWeight S b s e := by
  unfold deactWeight
  by_cases he : e ∈ S
  · rw [if_pos he, if_pos (hST he)]
  · rw [if_neg he]
    by_cases heT : e ∈ T
    · rw [if_pos heT]
      have hnn : 0 ≤ b * s := mul_nonneg hb0 hs0
      linarith
    · rw [if_neg heT]

/-- Enlarging the enhanced set preserves the activation shift: the resulting
law is pointwise larger, so percolation at a base below `pc` is preserved. -/
theorem ActivationShift.mono {A : Set (E → Bool)} {pc : ℝ} {S T : Set E}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hST : S ⊆ T) (h : ActivationShift A pc S) : ActivationShift A pc T := by
  intro s hs0 hs1
  obtain ⟨π, hπ, hshift⟩ := h s hs0 hs1
  refine ⟨π, hπ, ?_⟩
  intro p hp0 hp1 hpπ hppc
  have hper := hshift p hp0 hp1 hpπ hppc
  have hle : actProfile S p s ≤ actProfile T p s := by
    intro e
    rw [Subtype.mk_le_mk, coe_actProfile hp0 hp1 hs0.le hs1,
      coe_actProfile hp0 hp1 hs0.le hs1]
    exact actWeight_mono hST hp1 hs0.le e
  exact FK.EssentialWindow.measure_eq_one_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (actProfile S p s))
    (μ := FKLimit.bernoulliProduct (actProfile T p s))
    (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hper

/-- Enlarging the thinned set preserves the deactivation shift: thinning more
edges gives a pointwise smaller law, so nonpercolation at a base above `pc` is
preserved. -/
theorem DeactivationShift.mono {A : Set (E → Bool)} {pc : ℝ} {S T : Set E}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hST : S ⊆ T) (h : DeactivationShift A pc S) : DeactivationShift A pc T := by
  intro s hs0 hs1
  obtain ⟨π, hπ, hshift⟩ := h s hs0 hs1
  refine ⟨π, hπ, ?_⟩
  intro b hb0 hb1 hpcb hbπ
  have hzero := hshift b hb0 hb1 hpcb hbπ
  have hle : deactProfile T b s ≤ deactProfile S b s := by
    intro e
    rw [Subtype.mk_le_mk, coe_deactProfile hb0 hb1 hs0.le hs1,
      coe_deactProfile hb0 hb1 hs0.le hs1]
    exact deactWeight_anti hST hb0 hs0.le e
  exact FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (deactProfile S b s))
    (μ := FKLimit.bernoulliProduct (deactProfile T b s))
    (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hzero

/-! ## Equivalence with the `hAG` hypotheses of the window lemmas -/

/-- **Activation shift implies the increment form**: the exact `hAG` hypothesis
of `FK.EssentialWindow.lowerWindow_of_AG_q_lt_one`. -/
theorem hAGlower_of_activationShift {A : Set (E → Bool)} {pc : ℝ} {S : Set E}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (h : ActivationShift A pc S) (hpc0 : 0 < pc) (hpc : pc < 1) :
    ∀ (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < (1 - pc) / 2),
      ∃ a, ∃ (ha0 : 0 ≤ a) (_hapc : a < pc) (haε1 : a + ε ≤ 1),
        ((FKLimit.bernoulliProduct
          (FK.EssentialWindow.incrementProfile S a ε ha0 hε0.le haε1)) :
            Measure (E → Bool)) A = 1 := by
  intro ε hε0 hεlt
  have hgap : 0 < 1 - pc := by linarith
  have hs0 : 0 < ε / (1 - pc) := div_pos hε0 hgap
  have hs1 : ε / (1 - pc) ≤ 1 := by rw [div_le_one hgap]; linarith
  obtain ⟨π, hπ, hshift⟩ := h (ε / (1 - pc)) hs0 hs1
  set p : ℝ := (max π 0 + pc) / 2 with hp_def
  have hmax_lt : max π 0 < pc := max_lt hπ hpc0
  have hp_gt : max π 0 < p := by rw [hp_def]; linarith
  have hp_lt : p < pc := by rw [hp_def]; linarith
  have hp0 : 0 ≤ p := le_of_lt (lt_of_le_of_lt (le_max_right π 0) hp_gt)
  have hp1 : p ≤ 1 := hp_lt.le.trans hpc.le
  have hper : ((FKLimit.bernoulliProduct (actProfile S p (ε / (1 - pc)))) :
      Measure (E → Bool)) A = 1 :=
    hshift p hp0 hp1 (lt_of_le_of_lt (le_max_left π 0) hp_gt) hp_lt
  set a : ℝ := p + ε * (pc - p) / (1 - pc) with ha_def
  have hkey : a = p + (ε / (1 - pc)) * (pc - p) := by rw [ha_def]; field_simp
  have hkey' : a + ε = p + (ε / (1 - pc)) * (1 - p) := by rw [ha_def]; field_simp; ring
  have hpa : p ≤ a := by
    rw [hkey]; have h1 : 0 ≤ (ε / (1 - pc)) * (pc - p) := mul_nonneg hs0.le (by linarith)
    linarith
  have ha0 : 0 ≤ a := hp0.trans hpa
  have hapc : a < pc := by
    have hlt : ε / (1 - pc) < 1 := by rw [div_lt_one hgap]; linarith
    have hpos : (0:ℝ) < pc - p := by linarith
    have hmul : (ε / (1 - pc)) * (pc - p) < 1 * (pc - p) := mul_lt_mul_of_pos_right hlt hpos
    rw [hkey]; linarith
  have haε1 : a + ε ≤ 1 := by
    rw [hkey']
    have hle : (ε / (1 - pc)) * (1 - p) ≤ 1 * (1 - p) :=
      mul_le_mul_of_nonneg_right hs1 (by linarith)
    linarith
  refine ⟨a, ha0, hapc, haε1, ?_⟩
  rw [← incProfile_eq S a ε ha0 hε0.le haε1]
  have hle : actProfile S p (ε / (1 - pc)) ≤ incProfile S a ε := by
    intro e
    rw [Subtype.mk_le_mk, coe_actProfile hp0 hp1 hs0.le hs1, coe_incProfile ha0 haε1 hε0.le]
    unfold actWeight incWeight
    split_ifs with he
    · rw [hkey']
    · exact hpa
  exact FK.EssentialWindow.measure_eq_one_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (actProfile S p (ε / (1 - pc))))
    (μ := FKLimit.bernoulliProduct (incProfile S a ε))
    (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hper

/-- **The increment form implies the activation shift.** -/
theorem activationShift_of_hAGlower {A : Set (E → Bool)} {pc : ℝ} {S : Set E}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) (hpc : pc < 1)
    (h : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < (1 - pc) / 2),
      ∃ a, ∃ (ha0 : 0 ≤ a) (_hapc : a < pc) (haε1 : a + ε ≤ 1),
        ((FKLimit.bernoulliProduct
          (FK.EssentialWindow.incrementProfile S a ε ha0 hε0.le haε1)) :
            Measure (E → Bool)) A = 1) :
    ActivationShift A pc S := by
  intro s hs0 hs1
  have hgap : 0 < 1 - pc := by linarith
  set ε : ℝ := s * (1 - pc) / 4 with hε_def
  have hε0 : 0 < ε := by rw [hε_def]; positivity
  have hεlt : ε < (1 - pc) / 2 := by
    rw [hε_def]
    have h1 : s * (1 - pc) ≤ 1 * (1 - pc) := mul_le_mul_of_nonneg_right hs1 hgap.le
    nlinarith [h1]
  obtain ⟨a, ha0, hapc, haε1, hinc⟩ := h ε hε0 hεlt
  rw [← incProfile_eq S a ε ha0 hε0.le haε1] at hinc
  refine ⟨a, hapc, ?_⟩
  intro p hp0 hp1 hp_gt hp_lt
  have hkey : a + ε ≤ p + s * (1 - p) := by
    have h1 : ε ≤ s * (1 - a) := by
      rw [hε_def]
      nlinarith [mul_nonneg hs0.le (show (0:ℝ) ≤ 1 - a by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (show (0:ℝ) ≤ p - a by linarith)]
  have hle : incProfile S a ε ≤ actProfile S p s := by
    intro e
    rw [Subtype.mk_le_mk, coe_actProfile hp0 hp1 hs0.le hs1, coe_incProfile ha0 haε1 hε0.le]
    unfold actWeight incWeight
    split_ifs with he
    · exact hkey
    · exact hp_gt.le
  exact FK.EssentialWindow.measure_eq_one_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (incProfile S a ε))
    (μ := FKLimit.bernoulliProduct (actProfile S p s))
    (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hinc

/-- **Deactivation shift implies the decrement form**: the exact `hAG` hypothesis
of `FK.EssentialWindow.upperWindow_of_AG_q_lt_one`. -/
theorem hAGupper_of_deactivationShift {A : Set (E → Bool)} {pc : ℝ} {S : Set E}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (h : DeactivationShift A pc S) (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    ∀ (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < pc / 2),
      ∃ b, ∃ (hpcb : pc < b) (hb1 : b ≤ 1) (hεb : ε ≤ b),
        ((FKLimit.bernoulliProduct
          (FK.EssentialWindow.decrementProfile S b ε (hpc0.le.trans hpcb.le) hb1
            hε0.le hεb)) : Measure (E → Bool)) A = 0 := by
  intro ε hε0 hεlt
  set s : ℝ := ε / pc with hs_def
  have hs0 : 0 < s := div_pos hε0 hpc0
  have hs1 : s < 1 := by rw [hs_def, div_lt_one hpc0]; linarith
  obtain ⟨π, hπ, hshift⟩ := h s hs0 hs1.le
  set κ : ℝ := ε / (pc - ε) with hκ_def
  have hpcε : 0 < pc - ε := by linarith
  have hκ0 : 0 < κ := div_pos hε0 hpcε
  have h1κ : 0 < 1 + κ := by linarith
  set η : ℝ := min (π - pc) (1 - pc) / (2 * (1 + κ)) with hη_def
  have hmin : 0 < min (π - pc) (1 - pc) := lt_min (by linarith) (by linarith)
  have hη0 : 0 < η := div_pos hmin (by positivity)
  have hηeq : η * (1 + κ) = min (π - pc) (1 - pc) / 2 := by rw [hη_def]; field_simp
  have hηπ : pc + η * (1 + κ) < π := by
    have h1 : min (π - pc) (1 - pc) / 2 < π - pc := by
      have := min_le_left (π - pc) (1 - pc); linarith
    linarith
  have hη1 : pc + η * (1 + κ) ≤ 1 := by
    have h1 : min (π - pc) (1 - pc) / 2 < 1 - pc := by
      have := min_le_right (π - pc) (1 - pc); linarith
    linarith
  have hηle : η ≤ η * (1 + κ) := by nlinarith [mul_nonneg hη0.le hκ0.le]
  have hb1' : pc + η ≤ 1 := by linarith
  have hεb' : ε ≤ pc + η := by linarith
  set b : ℝ := pc + η with hb_def
  have hpcb : pc < b := by rw [hb_def]; linarith
  have hb1 : b ≤ 1 := by rw [hb_def]; exact hb1'
  have hεb : ε ≤ b := by rw [hb_def]; exact hεb'
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  refine ⟨b, hpcb, hb1, hεb, ?_⟩
  rw [← decProfile_eq S b ε hb0 hb1 hε0.le hεb]
  have h1s : 0 < 1 - s := by linarith
  set δ : ℝ := (b * s - ε) / (1 - s) with hδ_def
  have hδeq : δ = η * κ := by
    rw [hδ_def, hb_def, hs_def, hκ_def]
    field_simp
    ring
  have hδ0 : 0 ≤ δ := by rw [hδeq]; positivity
  set β : ℝ := b + δ with hβ_def
  have hβval : β = pc + η * (1 + κ) := by rw [hβ_def, hb_def, hδeq]; ring
  have hβπ : β < π := by rw [hβval]; exact hηπ
  have hβ1 : β ≤ 1 := by rw [hβval]; exact hη1
  have hβpc : pc < β := by rw [hβval]; nlinarith [mul_pos hη0 h1κ]
  have hβ0 : 0 ≤ β := hpc0.le.trans hβpc.le
  have hbβ : b ≤ β := by rw [hβ_def]; linarith
  have hkey : b - ε ≤ β * (1 - s) := by
    have hδs : δ * (1 - s) = b * s - ε := by rw [hδ_def]; field_simp
    rw [hβ_def]; nlinarith [hδs]
  have hle : decProfile S b ε ≤ deactProfile S β s := by
    intro e
    rw [Subtype.mk_le_mk, coe_decProfile hb0 hb1 hε0.le hεb,
      coe_deactProfile hβ0 hβ1 hs0.le hs1.le]
    unfold decWeight deactWeight
    split_ifs with he
    · exact hkey
    · exact hbβ
  have hzero : ((FKLimit.bernoulliProduct (deactProfile S β s)) :
      Measure (E → Bool)) A = 0 := hshift β hβ0 hβ1 hβpc hβπ
  exact FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (deactProfile S β s))
    (μ := FKLimit.bernoulliProduct (decProfile S b ε))
    (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hzero

/-- **The decrement form implies the deactivation shift.** -/
theorem deactivationShift_of_hAGupper {A : Set (E → Bool)} {pc : ℝ} {S : Set E}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) (hpc0 : 0 < pc)
    (h : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεlt : ε < pc / 2),
      ∃ b, ∃ (hpcb : pc < b) (hb1 : b ≤ 1) (hεb : ε ≤ b),
        ((FKLimit.bernoulliProduct
          (FK.EssentialWindow.decrementProfile S b ε (hpc0.le.trans hpcb.le) hb1
            hε0.le hεb)) : Measure (E → Bool)) A = 0) :
    DeactivationShift A pc S := by
  intro s hs0 hs1
  set ε : ℝ := s * pc / 4 with hε_def
  have hε0 : 0 < ε := by rw [hε_def]; positivity
  have hεlt : ε < pc / 2 := by
    rw [hε_def]
    have h1 : s * pc ≤ 1 * pc := mul_le_mul_of_nonneg_right hs1 hpc0.le
    nlinarith [h1]
  obtain ⟨b, hpcb, hb1, hεb, hdec⟩ := h ε hε0 hεlt
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  rw [← decProfile_eq S b ε hb0 hb1 hε0.le hεb] at hdec
  rcases eq_or_lt_of_le hs1 with h1 | h1
  · -- degenerate case: thinning removes every edge of `S`
    subst h1
    refine ⟨b, hpcb, ?_⟩
    intro β hβ0 hβ1 hpcβ hβb
    have hle : deactProfile S β 1 ≤ decProfile S b ε := by
      intro e
      rw [Subtype.mk_le_mk, coe_deactProfile hβ0 hβ1 hs0.le le_rfl,
        coe_decProfile hb0 hb1 hε0.le hεb]
      unfold deactWeight decWeight
      split_ifs with he
      · linarith
      · linarith
    exact FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates
      (ν := FKLimit.bernoulliProduct (decProfile S b ε))
      (μ := FKLimit.bernoulliProduct (deactProfile S β 1))
      (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hdec
  · -- nondegenerate case
    have h1s : 0 < 1 - s := by linarith
    refine ⟨min b ((b - ε) / (1 - s)), ?_, ?_⟩
    · refine lt_min hpcb ?_
      rw [lt_div_iff₀ h1s]
      nlinarith [mul_pos hs0 hpc0]
    · intro β hβ0 hβ1 hpcβ hβlt
      have hβb : β ≤ b := (le_min_iff.mp hβlt.le).1
      have hβs : β * (1 - s) ≤ b - ε := by
        have h2 := (le_min_iff.mp hβlt.le).2
        rwa [le_div_iff₀ h1s] at h2
      have hle : deactProfile S β s ≤ decProfile S b ε := by
        intro e
        rw [Subtype.mk_le_mk, coe_deactProfile hβ0 hβ1 hs0.le hs1,
          coe_decProfile hb0 hb1 hε0.le hεb]
        unfold deactWeight decWeight
        split_ifs with he
        · exact hβs
        · exact hβb
      exact FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates
        (ν := FKLimit.bernoulliProduct (decProfile S b ε))
        (μ := FKLimit.bernoulliProduct (deactProfile S β s))
        (FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA hdec

/-! ## The parameter windows and Theorem 1.4 -/

theorem upperWindow_of_deactivationShift_q_lt_one {A : Set (E → Bool)} {pc : ℝ}
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (h : DeactivationShift A pc Ee) (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.upperWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (hAGupper_of_deactivationShift (S := Ee) hA hmeas h hpc0 hpc1)

theorem upperWindow_of_deactivationShift_one_lt_q {A : Set (E → Bool)} {pc : ℝ}
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (h : DeactivationShift A pc Eb) (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.upperWindow_of_AG_one_lt_q A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (hAGupper_of_deactivationShift (S := Eb) hA hmeas h hpc0 hpc1)

theorem lowerWindow_of_activationShift_q_lt_one {A : Set (E → Bool)} {pc : ℝ}
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (h : ActivationShift A pc Eb) (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.lowerWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (hAGlower_of_activationShift (S := Eb) hA hmeas h hpc0 hpc1)

theorem lowerWindow_of_activationShift_one_lt_q {A : Set (E → Bool)} {pc : ℝ}
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (h : ActivationShift A pc Ee) (hpc0 : 0 < pc) (hpc1 : pc < 1) :
    FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.lowerWindow_of_AG_one_lt_q A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (hAGlower_of_activationShift (S := Ee) hA hmeas h hpc0 hpc1)

/-- **Theorem 1.4 from Proposition 4.2's comparison and the two shift
statements.**  This is the exact content of the paper's proof: the geometric
device machinery (already proved in `FK.Theorem14`) supplies the comparison
input and the enhanced sets, and the only external probabilistic ingredient is
the strict shift for the two product laws.  No other hypothesis is used. -/
theorem extendedPhases_of_shifts_q_lt_one
    {A : Set (E → Bool)} {pc : ℝ}
    {fk : ℝ → ℝ → Set (ProbabilityMeasure (E → Bool))}
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hcompare : ∀ (p : ℝ) (hp : p ∈ Icc (0:ℝ) 1), ∀ φ ∈ fk p q,
      FK.Phases.StochLe (FK.Phases.bernoulliProduct
        (FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq)) φ ∧
      FK.Phases.StochLe φ (FK.Phases.bernoulliProduct
        (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq)))
    (hact : ActivationShift A pc Eb) (hdeact : DeactivationShift A pc Ee) :
    ∃ δ, ∃ δ', 0 < δ ∧ 0 < δ' ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), max p (FK.Enhancement.fkPrime p q) < pc + δ' →
        ∃ μ : ProbabilityMeasure (E → Bool), (μ : Measure (E → Bool)) A = 0 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe φ μ) ∧ (∀ φ ∈ fk p q, (φ : Measure (E → Bool)) A = 0)) ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), pc - δ < min p (FK.Enhancement.fkPrime p q) →
        ∃ μ : ProbabilityMeasure (E → Bool), (μ : Measure (E → Bool)) A = 1 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe μ φ) ∧ (∀ φ ∈ fk p q, (φ : Measure (E → Bool)) A = 1)) := by
  have hupper := upperWindow_of_deactivationShift_q_lt_one Eb Ee n m q hq hq1
    hA hmeas hdeact hpc0 hpc1
  have hlower := lowerWindow_of_activationShift_q_lt_one Eb Ee n m q hq hq1
    hA hmeas hact hpc0 hpc1
  exact FK.Phases.extended_phases_of_comparison_and_essentialEnhancement
    A pc fk Eb Ee n m hA hmeas q hq (ne_of_lt hq1) hcompare hupper hlower

/-- **Theorem 1.4 from the two shifts, antiferromagnetic regime `1 < q`.**  The
roles of the two enhanced sets are exchanged, exactly as in Proposition 4.2. -/
theorem extendedPhases_of_shifts_one_lt_q
    {A : Set (E → Bool)} {pc : ℝ}
    {fk : ℝ → ℝ → Set (ProbabilityMeasure (E → Bool))}
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hcompare : ∀ (p : ℝ) (hp : p ∈ Icc (0:ℝ) 1), ∀ φ ∈ fk p q,
      FK.Phases.StochLe (FK.Phases.bernoulliProduct
        (FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq)) φ ∧
      FK.Phases.StochLe φ (FK.Phases.bernoulliProduct
        (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq)))
    (hact : ActivationShift A pc Ee) (hdeact : DeactivationShift A pc Eb) :
    ∃ δ, ∃ δ', 0 < δ ∧ 0 < δ' ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), max p (FK.Enhancement.fkPrime p q) < pc + δ' →
        ∃ μ : ProbabilityMeasure (E → Bool), (μ : Measure (E → Bool)) A = 0 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe φ μ) ∧ (∀ φ ∈ fk p q, (φ : Measure (E → Bool)) A = 0)) ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1), pc - δ < min p (FK.Enhancement.fkPrime p q) →
        ∃ μ : ProbabilityMeasure (E → Bool), (μ : Measure (E → Bool)) A = 1 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe μ φ) ∧ (∀ φ ∈ fk p q, (φ : Measure (E → Bool)) A = 1)) := by
  have hupper := upperWindow_of_deactivationShift_one_lt_q Eb Ee n m q hq hq1
    hA hmeas hdeact hpc0 hpc1
  have hlower := lowerWindow_of_activationShift_one_lt_q Eb Ee n m q hq hq1
    hA hmeas hact hpc0 hpc1
  exact FK.Phases.extended_phases_of_comparison_and_essentialEnhancement
    A pc fk Eb Ee n m hA hmeas q hq (ne_of_gt hq1) hcompare hupper hlower

/-! ## The scope of the paper's hypotheses -/

/-- The graph hypotheses of Theorem 1.4 of Beffara--Faipeur--Oke, verbatim:
`G` is infinite, locally finite, connected and quasi-transitive, `p_c(G) < 1`,
and `G` contains an edge that lies on a cycle **and** on a doubly-infinite path.
Local finiteness is the typeclass `[G.LocallyFinite]`.

The field `pc_pos` records `0 < p_c(G)`, which the paper's Remark 1.5 notes is
automatic for bounded-degree graphs; it is kept explicit because the parameter
windows are stated for `0 < pc`. -/
structure PaperGraphHypotheses {V : Type*} [Countable V] (G : SimpleGraph V) (o : V) : Prop where
  infinite : Infinite V
  connected : G.Connected
  quasiTransitive : FK.QuasiTransitive.IsQuasiTransitive G
  pc_pos : 0 < criticalProb G o
  pc_lt_one : criticalProb G o < 1
  /-- An edge lying on a cycle and on a doubly-infinite path simultaneously. -/
  pivotal : ∃ e : G.edgeSet, FK.EssentialEnhancement.OnDoubleRay e ∧
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ (e : Sym2 V) ∈ c.edges

/-- The complete external probabilistic content of Theorem 1.4 at the paper's
scope: the two strict shift statements for the genuine percolation event of `G`
at `p_c(G)`, on the two enhanced edge sets supplied by Proposition 4.2. -/
def PaperShiftInput {V : Type*} [Countable V] (G : SimpleGraph V) (o : V)
    (Eb Ee : Set G.edgeSet) : Prop :=
  ActivationShift (FK.EssentialWindow.Percolating G) (criticalProb G o) Eb ∧
    DeactivationShift (FK.EssentialWindow.Percolating G) (criticalProb G o) Ee

/-! ## Drop-in form for `FK.Theorem14.extended_phases_from_uniform_devices` -/

set_option linter.unusedVariables false in
/-- The repository's device theorem with its two AG window hypotheses replaced by
the two shift predicates.  Nothing else is used. -/
theorem extended_phases_from_uniform_devices_of_shifts_q_lt_one
    {E StarDevice CycleDevice : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ)
    (fk : ℝ → ℝ → Set (ProbabilityMeasure (E → Bool)))
    (starSupport : StarDevice → Set E) (starDevices : Set StarDevice)
    (starPivot : StarDevice → E)
    (cycleSupport : CycleDevice → Set E) (cycleDevices : Set CycleDevice)
    (cyclePivot : CycleDevice → E)
    (essential : E → Prop) (n m : ℕ)
    (hstarPivot : ∀ d, starPivot d ∈ starSupport d)
    (hcyclePivot : ∀ d, cyclePivot d ∈ cycleSupport d)
    (hstarEssential : ∀ d, essential (starPivot d))
    (hcycleEssential : ∀ d, essential (cyclePivot d))
    (edgeDist : E → E → ℕ)
    (htriangle : ∀ a b c, edgeDist a c ≤ edgeDist a b + edgeDist b c)
    (Ks Rs Kc Rc : ℕ)
    (hlocalStar : ∀ e, ∃ d ∈ starDevices, ∀ f ∈ starSupport d, edgeDist e f ≤ Ks)
    (hdiamStar : ∀ d ∈ starDevices, ∀ f ∈ starSupport d,
      edgeDist f (starPivot d) ≤ Rs)
    (hlocalCycle : ∀ e, ∃ d ∈ cycleDevices, ∀ f ∈ cycleSupport d, edgeDist e f ≤ Kc)
    (hdiamCycle : ∀ d ∈ cycleDevices, ∀ f ∈ cycleSupport d,
      edgeDist f (cyclePivot d) ≤ Rc)
    (hA : FK.Phases.IsIncreasingEvent A) (hmeas : MeasurableSet A)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hcompare : ∀ (Ms : Set StarDevice) (Mc : Set CycleDevice),
      Ms ⊆ starDevices → Mc ⊆ cycleDevices →
      FK.Theorem14.AuxiliaryFree starSupport starPivot Ms →
      FK.Theorem14.AuxiliaryFree cycleSupport cyclePivot Mc →
      FK.Theorem14.ComparisonInput fk (starPivot '' Ms) (cyclePivot '' Mc) n m q hq)
    (hshiftUpper : ∀ (Eb Ee : Set E),
      FK.Theorem14.AllEssential essential Eb → FK.Theorem14.AllEssential essential Ee →
      FK.Theorem14.BoundedDistance edgeDist Eb → FK.Theorem14.BoundedDistance edgeDist Ee →
      DeactivationShift A pc Ee)
    (hshiftLower : ∀ (Eb Ee : Set E),
      FK.Theorem14.AllEssential essential Eb → FK.Theorem14.AllEssential essential Ee →
      FK.Theorem14.BoundedDistance edgeDist Eb → FK.Theorem14.BoundedDistance edgeDist Ee →
      ActivationShift A pc Eb) :
    FK.Theorem14.ExtendedPhaseStatement A pc fk q :=
  FK.Theorem14.extended_phases_from_uniform_devices
    A pc fk starSupport starDevices starPivot cycleSupport cycleDevices cyclePivot
    essential n m hstarPivot hcyclePivot hstarEssential hcycleEssential
    edgeDist htriangle Ks Rs Kc Rc hlocalStar hdiamStar hlocalCycle hdiamCycle
    hA hmeas q hq (ne_of_lt hq1) hcompare
    (fun Eb Ee h1 h2 h3 h4 =>
      upperWindow_of_deactivationShift_q_lt_one Eb Ee n m q hq hq1
        hA hmeas (hshiftUpper Eb Ee h1 h2 h3 h4) hpc0 hpc1)
    (fun Eb Ee h1 h2 h3 h4 =>
      lowerWindow_of_activationShift_q_lt_one Eb Ee n m q hq hq1
        hA hmeas (hshiftLower Eb Ee h1 h2 h3 h4) hpc0 hpc1)

set_option linter.unusedVariables false in
/-- The repository's device theorem with its two AG window hypotheses replaced by
the two shift predicates.  Nothing else is used. -/
theorem extended_phases_from_uniform_devices_of_shifts_one_lt_q
    {E StarDevice CycleDevice : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ)
    (fk : ℝ → ℝ → Set (ProbabilityMeasure (E → Bool)))
    (starSupport : StarDevice → Set E) (starDevices : Set StarDevice)
    (starPivot : StarDevice → E)
    (cycleSupport : CycleDevice → Set E) (cycleDevices : Set CycleDevice)
    (cyclePivot : CycleDevice → E)
    (essential : E → Prop) (n m : ℕ)
    (hstarPivot : ∀ d, starPivot d ∈ starSupport d)
    (hcyclePivot : ∀ d, cyclePivot d ∈ cycleSupport d)
    (hstarEssential : ∀ d, essential (starPivot d))
    (hcycleEssential : ∀ d, essential (cyclePivot d))
    (edgeDist : E → E → ℕ)
    (htriangle : ∀ a b c, edgeDist a c ≤ edgeDist a b + edgeDist b c)
    (Ks Rs Kc Rc : ℕ)
    (hlocalStar : ∀ e, ∃ d ∈ starDevices, ∀ f ∈ starSupport d, edgeDist e f ≤ Ks)
    (hdiamStar : ∀ d ∈ starDevices, ∀ f ∈ starSupport d,
      edgeDist f (starPivot d) ≤ Rs)
    (hlocalCycle : ∀ e, ∃ d ∈ cycleDevices, ∀ f ∈ cycleSupport d, edgeDist e f ≤ Kc)
    (hdiamCycle : ∀ d ∈ cycleDevices, ∀ f ∈ cycleSupport d,
      edgeDist f (cyclePivot d) ≤ Rc)
    (hA : FK.Phases.IsIncreasingEvent A) (hmeas : MeasurableSet A)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hcompare : ∀ (Ms : Set StarDevice) (Mc : Set CycleDevice),
      Ms ⊆ starDevices → Mc ⊆ cycleDevices →
      FK.Theorem14.AuxiliaryFree starSupport starPivot Ms →
      FK.Theorem14.AuxiliaryFree cycleSupport cyclePivot Mc →
      FK.Theorem14.ComparisonInput fk (starPivot '' Ms) (cyclePivot '' Mc) n m q hq)
    (hshiftUpper : ∀ (Eb Ee : Set E),
      FK.Theorem14.AllEssential essential Eb → FK.Theorem14.AllEssential essential Ee →
      FK.Theorem14.BoundedDistance edgeDist Eb → FK.Theorem14.BoundedDistance edgeDist Ee →
      DeactivationShift A pc Eb)
    (hshiftLower : ∀ (Eb Ee : Set E),
      FK.Theorem14.AllEssential essential Eb → FK.Theorem14.AllEssential essential Ee →
      FK.Theorem14.BoundedDistance edgeDist Eb → FK.Theorem14.BoundedDistance edgeDist Ee →
      ActivationShift A pc Ee) :
    FK.Theorem14.ExtendedPhaseStatement A pc fk q :=
  FK.Theorem14.extended_phases_from_uniform_devices
    A pc fk starSupport starDevices starPivot cycleSupport cycleDevices cyclePivot
    essential n m hstarPivot hcyclePivot hstarEssential hcycleEssential
    edgeDist htriangle Ks Rs Kc Rc hlocalStar hdiamStar hlocalCycle hdiamCycle
    hA hmeas q hq (ne_of_gt hq1) hcompare
    (fun Eb Ee h1 h2 h3 h4 =>
      upperWindow_of_deactivationShift_one_lt_q Eb Ee n m q hq hq1
        hA hmeas (hshiftUpper Eb Ee h1 h2 h3 h4) hpc0 hpc1)
    (fun Eb Ee h1 h2 h3 h4 =>
      lowerWindow_of_activationShift_one_lt_q Eb Ee n m q hq hq1
        hA hmeas (hshiftLower Eb Ee h1 h2 h3 h4) hpc0 hpc1)

/-! ## The root convention: BBR's positive-root-probability form

Balister--Bollobás--Riordan state the conclusion for the probability `θ(p,s)`
that *the origin* lies in an infinite cluster.  `ActivationShift` above is
stated for an arbitrary increasing event `A`; the paper applies it at the
existence-of-an-infinite-cluster event.  The bridge is the Kolmogorov zero--one
law: a positive probability for the root event forces probability one for the
existence event.  The converse (probability one for existence forcing a positive
probability for a *fixed* root) needs quasi-transitivity and is not claimed. -/

section RootConvention

variable {V : Type*} [Countable V] (G : SimpleGraph V) [G.LocallyFinite] (o : V)

/-- The cluster of the fixed root `o` is infinite. -/
def RootPercolating : Set (G.edgeSet → Bool) :=
  {ω | {x | OpenConnected G ω Set.univ o x}.Infinite}

theorem rootPercolating_subset : RootPercolating G o ⊆ FK.EssentialWindow.Percolating G :=
  fun ω h => ⟨o, h⟩

theorem measurableSet_rootPercolating (hG : G.Connected) : MeasurableSet (RootPercolating G o) := by
  have h := FK.ClusterTail.measurable_openCluster (G := G) o
  exact MeasurableSet.setOfPred_infinite.preimage h

/-- **Inhomogeneous cylinder independence** for the product Boolean law. -/
theorem measure_inter_eq_mul_of_dependsOn_bernoulliProduct {ι : Type*}
    (r : ι → unitInterval) {A B : Set (ι → Bool)} {D₁ D₂ : Set ι}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAD : DependsOn (· ∈ A) D₁)
    (hBD : DependsOn (· ∈ B) D₂) (hD : Disjoint D₁ D₂) :
    (FKLimit.bernoulliProduct r : Measure (ι → Bool)) (A ∩ B) =
      (FKLimit.bernoulliProduct r : Measure (ι → Bool)) A *
        (FKLimit.bernoulliProduct r : Measure (ι → Bool)) B := by
  have hind := CurvatureVariance.Infra.EfronStein.indepFun_restrict_infinitePi
    (μ := fun i => bernoulliMeasure true false (r i)) D₁ D₂ hD
  rw [CurvatureVariance.Infra.Percolation.eq_preimage_restrict_of_dependsOn hAD,
    CurvatureVariance.Infra.Percolation.eq_preimage_restrict_of_dependsOn hBD]
  exact hind.measure_inter_preimage_eq_mul _ _
    (CurvatureVariance.Infra.Percolation.measurable_extendFalse D₁ hA)
    (CurvatureVariance.Infra.Percolation.measurable_extendFalse D₂ hB)

/-- **Kolmogorov zero--one law for the existence of an infinite cluster** under
an inhomogeneous Bernoulli product law. -/
theorem percolating_zero_or_one (hG : G.Connected) (r : G.edgeSet → unitInterval) :
    (FKLimit.bernoulliProduct r : Measure (G.edgeSet → Bool))
        (FK.EssentialWindow.Percolating G) = 0 ∨
      (FKLimit.bernoulliProduct r : Measure (G.edgeSet → Bool))
        (FK.EssentialWindow.Percolating G) = 1 := by
  have hEq : FK.EssentialWindow.Percolating G = {ω : G.edgeSet → Bool |
      FK.ClusterCover.HasInfiniteCluster G ω} := by
    ext ω
    simp only [FK.EssentialWindow.Percolating, FK.ClusterCover.HasInfiniteCluster,
      Set.mem_setOf_eq, FK.ClusterCover.clusterAvoid_empty_eq]
  rw [hEq]
  refine FK.ClusterTail.measure_eq_zero_or_one_of_cylinder_indep
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G) (fun S => ?_) (fun S B hB hBS => ?_)
  · exact FK.ClusterTail.dependsOn_hasInfiniteCluster G (S : Set G.edgeSet) S.finite_toSet
  · exact measure_inter_eq_mul_of_dependsOn_bernoulliProduct r
      (FK.ClusterTail.measurableSet_hasInfiniteCluster G) hB
      (FK.ClusterTail.dependsOn_hasInfiniteCluster G (S : Set G.edgeSet) S.finite_toSet)
      hBS (Set.disjoint_left.mpr fun a ha ha' => ha ha')

/-- **BBR's form: positive probability for the root cluster.**  For every
activation probability `s > 0` there is `π < pc` such that for every base
parameter `p ∈ (π, pc)` the root cluster of `o` is infinite with positive
probability.  This is literally `θ(p,s) > 0` in Conjecture 1 of
Balister--Bollobás--Riordan (arXiv:1402.0834), for the edge-activation rule
supported on `S`. -/
def RootShift (pc : ℝ) (S : Set G.edgeSet) : Prop :=
  ∀ (s : ℝ) (_hs0 : 0 < s) (_hs1 : s ≤ 1),
    ∃ π : ℝ, π < pc ∧
      ∀ (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1), π < p → p < pc →
        0 < ((FKLimit.bernoulliProduct (actProfile S p s)) :
          Measure (G.edgeSet → Bool)) (RootPercolating G o)

/-- **BBR's positive-root form implies the existence-event form** used above, by
the zero--one law. -/
theorem activationShift_of_rootShift (hG : G.Connected) {pc : ℝ} {S : Set G.edgeSet}
    (h : RootShift G o pc S) :
    ActivationShift (FK.EssentialWindow.Percolating G) pc S := by
  intro s hs0 hs1
  obtain ⟨π, hπ, hpos⟩ := h s hs0 hs1
  refine ⟨π, hπ, ?_⟩
  intro p hp0 hp1 hpπ hppc
  have hroot := hpos p hp0 hp1 hpπ hppc
  have hle : ((FKLimit.bernoulliProduct (actProfile S p s)) :
      Measure (G.edgeSet → Bool)) (RootPercolating G o) ≤
      ((FKLimit.bernoulliProduct (actProfile S p s)) :
        Measure (G.edgeSet → Bool)) (FK.EssentialWindow.Percolating G) :=
    measure_mono (rootPercolating_subset G o)
  have hne : ((FKLimit.bernoulliProduct (actProfile S p s)) :
      Measure (G.edgeSet → Bool)) (FK.EssentialWindow.Percolating G) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hroot hle)
  rcases percolating_zero_or_one G hG (actProfile S p s) with h0 | h1
  · exact absurd h0 hne
  · exact h1

end RootConvention

/-! ## Theorem 1.4 at the paper's own scope -/

set_option linter.unusedVariables false in
/-- **Theorem 1.4 of Beffara--Faipeur--Oke, modulo the two shift statements.**
At the genuine percolation event of `G` and `pc = p_c(G)`, for
`q < 1`.  Every hypothesis is either a paper hypothesis
(`PaperGraphHypotheses`), the Proposition 4.2 comparison, or the two shift
statements `PaperShiftInput`; nothing else. -/
theorem theorem_1_4_of_shifts_q_lt_one
    {V : Type*} [Countable V] (G : SimpleGraph V) [G.LocallyFinite] (o : V)
    (hG : PaperGraphHypotheses G o)
    (Eb Ee : Set G.edgeSet) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    {fk : ℝ → ℝ → Set (ProbabilityMeasure (G.edgeSet → Bool))}
    (hcompare : ∀ (p : ℝ) (hp : p ∈ Icc (0:ℝ) 1), ∀ φ ∈ fk p q,
      FK.Phases.StochLe (FK.Phases.bernoulliProduct
        (FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq)) φ ∧
      FK.Phases.StochLe φ (FK.Phases.bernoulliProduct
        (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq)))
    (hshift : PaperShiftInput G o Eb Ee) :
    ∃ δ, ∃ δ', 0 < δ ∧ 0 < δ' ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1),
        max p (FK.Enhancement.fkPrime p q) < criticalProb G o + δ' →
        ∃ μ : ProbabilityMeasure (G.edgeSet → Bool), (μ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 0 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe φ μ) ∧
          (∀ φ ∈ fk p q, (φ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 0)) ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1),
        criticalProb G o - δ < min p (FK.Enhancement.fkPrime p q) →
        ∃ μ : ProbabilityMeasure (G.edgeSet → Bool), (μ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 1 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe μ φ) ∧
          (∀ φ ∈ fk p q, (φ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 1)) :=
  extendedPhases_of_shifts_q_lt_one Eb Ee n m q hq hq1
    (FK.EssentialWindow.isUpperSet_percolating G)
    (FK.EssentialWindow.measurableSet_percolating G hG.connected)
    hG.pc_pos hG.pc_lt_one hcompare hshift.1 hshift.2

set_option linter.unusedVariables false in
/-- **Theorem 1.4 modulo the shifts, supercritical side `1 < q`.** -/
theorem theorem_1_4_of_shifts_one_lt_q
    {V : Type*} [Countable V] (G : SimpleGraph V) [G.LocallyFinite] (o : V)
    (hG : PaperGraphHypotheses G o)
    (Eb Ee : Set G.edgeSet) (n m : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    {fk : ℝ → ℝ → Set (ProbabilityMeasure (G.edgeSet → Bool))}
    (hcompare : ∀ (p : ℝ) (hp : p ∈ Icc (0:ℝ) 1), ∀ φ ∈ fk p q,
      FK.Phases.StochLe (FK.Phases.bernoulliProduct
        (FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq)) φ ∧
      FK.Phases.StochLe φ (FK.Phases.bernoulliProduct
        (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq)))
    (hshift : PaperShiftInput G o Ee Eb) :
    ∃ δ, ∃ δ', 0 < δ ∧ 0 < δ' ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1),
        max p (FK.Enhancement.fkPrime p q) < criticalProb G o + δ' →
        ∃ μ : ProbabilityMeasure (G.edgeSet → Bool), (μ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 0 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe φ μ) ∧
          (∀ φ ∈ fk p q, (φ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 0)) ∧
      (∀ p (_hp : p ∈ Icc (0 : ℝ) 1),
        criticalProb G o - δ < min p (FK.Enhancement.fkPrime p q) →
        ∃ μ : ProbabilityMeasure (G.edgeSet → Bool), (μ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 1 ∧
          (∀ φ ∈ fk p q, FK.Phases.StochLe μ φ) ∧
          (∀ φ ∈ fk p q, (φ : Measure (G.edgeSet → Bool))
            (FK.EssentialWindow.Percolating G) = 1)) :=
  extendedPhases_of_shifts_one_lt_q Eb Ee n m q hq hq1
    (FK.EssentialWindow.isUpperSet_percolating G)
    (FK.EssentialWindow.measurableSet_percolating G hG.connected)
    hG.pc_pos hG.pc_lt_one hcompare hshift.1 hshift.2

end

end FK.AGShift
