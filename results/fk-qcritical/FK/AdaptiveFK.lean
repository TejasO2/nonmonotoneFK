import FK.AdaptiveDisintegration
import FK.FKSequentialCoupling

/-! # FK and Bernoulli conditional bits on arbitrary revealed fibres -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Decompose the real mass of a configuration event along the two values of
one prescribed coordinate. -/
lemma mass_toReal_decompose (μ : PMF (E → Bool)) (S : Set (E → Bool)) (e : E) :
    (∑' ω, S.indicator (⇑μ) ω).toReal =
      ∑ off : Glauber.OffConfig Bool E e, ∑ b : Bool,
        if (Glauber.configSplit Bool e).symm (off, b) ∈ S then
          ((Glauber.ofPMF μ).mass ((Glauber.configSplit Bool e).symm (off, b))) else 0 := by
  rw [tsum_fintype]
  have htop : ∀ ω ∈ Finset.univ, S.indicator (⇑μ) ω ≠ ∞ := by
    intro ω _
    by_cases hω : ω ∈ S
    · simp [Set.indicator_of_mem hω, μ.apply_ne_top]
    · simp [Set.indicator_of_notMem hω]
  rw [ENNReal.toReal_sum htop]
  calc
    _ = ∑ z : Glauber.OffConfig Bool E e × Bool,
        ((S.indicator (⇑μ)) ((Glauber.configSplit Bool e).symm z)).toReal := by
      simpa only [(Glauber.configSplit Bool e).symm_apply_apply] using
        (Equiv.sum_comp (Glauber.configSplit Bool e)
          (fun z => ((S.indicator (⇑μ)) ((Glauber.configSplit Bool e).symm z)).toReal))
    _ = ∑ off : Glauber.OffConfig Bool E e, ∑ b : Bool,
        ((S.indicator (⇑μ)) ((Glauber.configSplit Bool e).symm (off, b))).toReal := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro off _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : (Glauber.configSplit Bool e).symm (off, b) ∈ S
      · rw [if_pos h, Set.indicator_of_mem h]
        rfl
      · rw [if_neg h, Set.indicator_of_notMem h]
        simp

/-- The off-edge fibres compatible with a partial assignment. -/
def OffCompatible (h : Assignment E) (e : E) : Set (Glauber.OffConfig Bool E e) :=
  {off | fullOff e off ∈ Fiber h}

lemma offCompatible_iff_recombine {h : Assignment E} {e : E} (he : h e = none)
    (off : Glauber.OffConfig Bool E e) (b : Bool) :
    (Glauber.configSplit Bool e).symm (off, b) ∈ Fiber h ↔ off ∈ OffCompatible h e := by
  unfold OffCompatible
  constructor <;> intro H a c ha
  · have hae : a ≠ e := by
      intro hae
      subst a
      rw [he] at ha
      contradiction
    have hv := H a c ha
    rw [recombine_off, Function.update_of_ne hae] at hv
    exact hv
  · have hae : a ≠ e := by
      intro hae
      subst a
      rw [he] at ha
      contradiction
    have hv := H a c ha
    rw [recombine_off, Function.update_of_ne hae]
    exact hv

lemma mass_toReal_eq_selected (μ : PMF (E → Bool)) {h : Assignment E} {e : E}
    (he : h e = none) :
    (mass μ h).toReal = selectedSum (OffCompatible h e)
      (Glauber.outsideMassConj (Glauber.configSplit Bool e) (Glauber.ofPMF μ)) := by
  rw [mass, mass_toReal_decompose μ (Fiber h) e]
  unfold selectedSum Glauber.outsideMassConj
  apply Finset.sum_congr rfl
  intro off _
  rw [Fintype.sum_bool]
  by_cases ho : off ∈ OffCompatible h e
  · have ht : (Glauber.configSplit Bool e).symm (off, true) ∈ Fiber h :=
      (offCompatible_iff_recombine he off true).2 ho
    have hf : (Glauber.configSplit Bool e).symm (off, false) ∈ Fiber h :=
      (offCompatible_iff_recombine he off false).2 ho
    simp [ho, ht, hf, add_comm]
  · have ht : (Glauber.configSplit Bool e).symm (off, true) ∉ Fiber h := by
      intro H
      exact ho ((offCompatible_iff_recombine he off true).1 H)
    have hf : (Glauber.configSplit Bool e).symm (off, false) ∉ Fiber h := by
      intro H
      exact ho ((offCompatible_iff_recombine he off false).1 H)
    simp [ho, ht, hf]

lemma reveal_mass_open_toReal_eq_selected (μ : PMF (E → Bool)) {h : Assignment E}
    {e : E} (he : h e = none) :
    (mass μ (reveal h e true)).toReal = selectedSum (OffCompatible h e) (fun off =>
      (Glauber.ofPMF μ).mass ((Glauber.configSplit Bool e).symm (off, true))) := by
  rw [mass, mass_toReal_decompose μ (Fiber (reveal h e true)) e]
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro off _
  rw [Fintype.sum_bool]
  by_cases ho : off ∈ OffCompatible h e
  · have hh : (Glauber.configSplit Bool e).symm (off, true) ∈ Fiber h :=
      (offCompatible_iff_recombine he off true).2 ho
    have ht : (Glauber.configSplit Bool e).symm (off, true) ∈ Fiber (reveal h e true) :=
      (mem_fiber_reveal_iff he).2 ⟨hh, by rw [recombine_off]; simp⟩
    have hf : (Glauber.configSplit Bool e).symm (off, false) ∉ Fiber (reveal h e true) := by
      intro H
      have hb := ((mem_fiber_reveal_iff he).1 H).2
      rw [recombine_off] at hb
      simp at hb
    simp [ho, ht, hf]
  · have ht : (Glauber.configSplit Bool e).symm (off, true) ∉ Fiber (reveal h e true) := by
      intro H
      exact ho ((offCompatible_iff_recombine he off true).1
        ((mem_fiber_reveal_iff he).1 H).1)
    have hf : (Glauber.configSplit Bool e).symm (off, false) ∉ Fiber (reveal h e true) := by
      intro H
      exact ho ((offCompatible_iff_recombine he off false).1
        ((mem_fiber_reveal_iff he).1 H).1)
    simp [ho, ht, hf]

/-- Any uniform bound on singleton heat-bath open rates remains valid after
conditioning on an arbitrary partial configuration. -/
theorem bit_true_toReal_le_of_bound (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) {h : Assignment E} {e : E} (he : h e = none)
    (c : Glauber.EdgeConditionals Bool E)
    (hc : Glauber.HasEdgeConditional (Glauber.ofPMF μ) c e)
    (r : ℝ) (hr : ∀ off, (c e off).mass true ≤ r) :
    (bit μ hμ h e true).toReal ≤ r := by
  have hm := selected_openMass_le (Glauber.ofPMF μ) c e hc r hr (OffCompatible h e)
  rw [← reveal_mass_open_toReal_eq_selected μ he, ← mass_toReal_eq_selected μ he] at hm
  have hp : 0 < (mass μ h).toReal := ENNReal.toReal_pos
    (ne_of_gt (mass_pos_of_positive μ hμ h)) (mass_ne_top μ h)
  rw [bit_apply he, ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_mul_inv]
  exact (div_le_iff₀ hp).2 hm

/-- Exact constant singleton rates also pass to an arbitrary revealed fibre. -/
theorem bit_true_toReal_eq_of_constant (μ : PMF (E → Bool))
    (hμ : ∀ ω, μ ω ≠ 0) {h : Assignment E} {e : E} (he : h e = none)
    (c : Glauber.EdgeConditionals Bool E)
    (hc : Glauber.HasEdgeConditional (Glauber.ofPMF μ) c e)
    (r : ℝ) (hr : ∀ off, (c e off).mass true = r) :
    (bit μ hμ h e true).toReal = r := by
  have hm := selected_openMass_eq (Glauber.ofPMF μ) c e hc r hr (OffCompatible h e)
  rw [← reveal_mass_open_toReal_eq_selected μ he, ← mass_toReal_eq_selected μ he] at hm
  have hp : 0 < (mass μ h).toReal := ENNReal.toReal_pos
    (ne_of_gt (mass_pos_of_positive μ hμ h)) (mass_ne_top μ h)
  rw [bit_apply he, ENNReal.toReal_mul, ENNReal.toReal_inv, ← div_eq_mul_inv]
  exact (div_eq_iff hp.ne').2 hm

/-- Bernoulli product laws have the expected conditional bit at every
unrevealed coordinate. -/
theorem bit_bernoulliProductPMF (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) {r : NNReal} (hr0 : 0 < r) (hr1 : r < 1)
    {k : Assignment G.Edge} {e : G.Edge} (he : k e = none) :
    bit (G.bernoulliProductPMF hr1.le)
      (by
        intro ω
        rw [← G.fkPMF_q_one hr1.le ξ]
        exact fkPMF_ne_zero G zero_lt_one hr0 hr1 ξ ω) k e =
      FKModel.bernoulliPMF r hr1.le := by
  let ν := G.bernoulliProductPMF hr1.le
  let hν : ∀ ω, ν ω ≠ 0 := by
    intro ω
    change G.bernoulliProductPMF hr1.le ω ≠ 0
    rw [← G.fkPMF_q_one hr1.le ξ]
    exact fkPMF_ne_zero G zero_lt_one hr0 hr1 ξ ω
  let c : Glauber.EdgeConditionals Bool G.Edge :=
    fun _ _ => boolLaw (r : ℝ) ⟨hr0.le, hr1.le⟩
  have hc : Glauber.HasEdgeConditional (Glauber.ofPMF ν) c e := by
    rw [G.ofPMF_bernoulliProductPMF hr1.le]
    exact boolProduct_hasEdgeConditional (fun _ : G.Edge => (r : ℝ))
      (fun _ => ⟨hr0.le, hr1.le⟩) e
  apply eq_of_true_toReal_eq
  rw [bit_true_toReal_eq_of_constant ν hν he c hc (r : ℝ) (fun off => by apply boolLaw_true)]
  rw [FKModel.bernoulliPMF_apply]
  rfl

/-- The actual FK upper conditional bound on every partial-assignment fibre. -/
theorem fk_bit_true_toReal_le (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    {h : Assignment G.Edge} {e : G.Edge} (he : h e = none) :
    (bit (G.fkPMF hq hp1.le ξ)
      (fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω) h e true).toReal ≤
      (upperRateNN q p : ℝ) := by
  have hb := bit_true_toReal_le_of_bound (G.fkPMF hq hp1.le ξ)
    (fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω) he
    (fkConditionals G hq hp1.le ξ) (fk_hasEdgeConditional G hq hp1.le ξ e)
    (fkHi q p) (fun off => fkRate_le_max G ξ e off)
  simpa [coe_upperRateNN q p hq hp1.le] using hb

end FK.Adaptive
