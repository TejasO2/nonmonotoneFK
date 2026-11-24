/-
# Sharpness and non-vacuity of the Aizenman–Grimmett input of Theorem 1.4

The public development reduces Theorem 1.4 of arXiv:2512.16486v1 to the
predicate `FK.EssentialWindow.UpperWindow` / `LowerWindow`, and further to a
single "Aizenman–Grimmett" hypothesis on one inhomogeneous Bernoulli product
law (`FK.EssentialWindow.upperWindow_of_AG_q_lt_one`).  This file records facts
about that input that are *not* in the public tree:

* `AGInput` names the single input explicitly and `upperWindow_of_AGInput`
  re-derives the window from it: the public reduction is a statement about one
  inhomogeneous product law, with no FK content left.
* `exists_subcritical_decrement_of_upperWindow` proves a converse at the level
  of that single law: `UpperWindow` itself *forces* a base `b > pc` and a
  decrement `E' ≥ 0` for which the decrement product has zero mass.  Hence the
  Aizenman–Grimmett content cannot be removed from this route by weakening the
  window: that conclusion itself yields one strictly enhanced product law, at a
  base above `pc`, that does not percolate.  So Theorem 1.4(1) *implies* the
  existence of a strict critical shift; the shift is not an artefact of the
  chosen interface.
* The input is monotone in the enhanced set (`AGInput_of_subset`,
  `upperWindow_of_subset`): enlarging `S` preserves it.  The paper's maximal
  device packing is therefore the most favourable case.
* The predicates are sharp: `not_upperWindow_univ` and `not_AGInput_univ` show
  that the event must be proper (for `A = univ` the required zero mass is
  impossible), and `not_AGInput_empty_percolating` shows that the enhanced set
  must be nonempty — with `S = ∅` the decrement profile is the *homogeneous* law
  at a base above `pc`, which percolates.  A genuinely present enhancement is
  therefore needed, not just a formal one.
* `AGInput_percolating_univ` and `upperWindow_percolating_univ` show the pair is
  consistent at the paper's parameters: when every edge is enhanced the input,
  hence the window, holds for the actual percolation event, using only the
  public theorem that Bernoulli percolation below `p_c` does not percolate.

Nothing here assumes any part of the paper's conclusions.
-/
import FK.AGWindow
import FK.SubcriticalBaseline
import FK.ReferenceBaselinePercolating

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.AGSharpness

open FK.EssentialWindow FK.Enhancement CurvatureVariance.Infra.Percolation Classical

noncomputable section

/-! ## The single-law form of the Aizenman–Grimmett input -/

/-- The Aizenman–Grimmett input of `upperWindow_of_AG_q_lt_one`, stated as a
predicate on the enhanced set: for every sufficiently small decrement `ε` there
is a base `b` strictly above `pc` such that the product law which is `b` off `S`
and `b - ε` on `S` has zero mass on the increasing event `A`. -/
def AGInput {E : Type*} (A : Set (E → Bool)) (pc : ℝ) (hpc0 : 0 < pc)
    (S : Set E) : Prop :=
  ∀ (ε : ℝ) (hε0 : 0 < ε), ε < pc / 2 →
    ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
      (FKLimit.bernoulliProduct
        (decrementProfile S b ε (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) :
          Measure (E → Bool)) A = 0

/-- `AGInput` implies the upper parameter window: the public analytic reduction,
re-exposed for the named predicate. -/
theorem upperWindow_of_AGInput {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hAG : AGInput A pc hpc0 Ee) :
    UpperWindow A pc Eb Ee n m q hq :=
  upperWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas hAG

/-! ## Monotonicity in the enhanced set

Lowering more coordinates makes the product law smaller, and `A` is increasing,
so a zero-mass conclusion survives when the enhanced set grows. -/

/-- The decrement profile of a larger enhanced set is pointwise smaller. -/
theorem decrementProfile_le_of_subset {E : Type*} {S T : Set E} (hST : S ⊆ T)
    {b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hε0 : 0 ≤ ε) (hεb : ε ≤ b) :
    decrementProfile T b ε hb0 hb1 hε0 hεb ≤
      decrementProfile S b ε hb0 hb1 hε0 hεb := by
  intro e
  change ((decrementProfile T b ε hb0 hb1 hε0 hεb e : unitInterval) : ℝ) ≤
    ((decrementProfile S b ε hb0 hb1 hε0 hεb e : unitInterval) : ℝ)
  simp only [decrementProfile]
  by_cases he : e ∈ S
  · rw [if_pos (hST he), if_pos he]
  · by_cases heT : e ∈ T
    · rw [if_pos heT, if_neg he]
      exact sub_le_self b hε0
    · rw [if_neg heT, if_neg he]

/-- `AGInput` is monotone in the enhanced set. -/
theorem AGInput_of_subset {E : Type*} [Countable E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) {pc : ℝ} {hpc0 : 0 < pc}
    {S T : Set E} (hST : S ⊆ T) (hAG : AGInput A pc hpc0 S) :
    AGInput A pc hpc0 T := by
  intro ε hε0 hεpc
  obtain ⟨b, hpcb, hb1, hεb, hzero⟩ := hAG ε hε0 hεpc
  refine ⟨b, hpcb, hb1, hεb, ?_⟩
  have hle := measure_le_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct
      (decrementProfile S b ε (hpc0.le.trans hpcb.le) hb1 hε0.le hεb))
    (μ := FKLimit.bernoulliProduct
      (decrementProfile T b ε (hpc0.le.trans hpcb.le) hb1 hε0.le hεb))
    (stochasticallyDominates_bernoulliProduct_of_le
      (decrementProfile_le_of_subset hST (hpc0.le.trans hpcb.le) hb1 hε0.le hεb))
    hmeas hA
  exact le_antisymm (hle.trans_eq hzero) bot_le

/-- The same monotonicity for the window predicate. -/
theorem upperWindow_of_subset {E : Type*} [Countable E] {A : Set (E → Bool)}
    (hmeas : MeasurableSet A) (hA : IsUpperSet A)
    {pc : ℝ} {Eb Ee Ee' : Set E} {n m : ℕ} {q : ℝ} {hq : 0 < q}
    (hsub : Ee ⊆ Ee') (hW : UpperWindow A pc Eb Ee n m q hq) :
    UpperWindow A pc Eb Ee' n m q hq := by
  obtain ⟨δ', hδ', H⟩ := hW
  refine ⟨δ', hδ', ?_⟩
  intro p hp hwin
  have hle := measure_le_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq))
    (μ := FKLimit.bernoulliProduct (FK.Phases.upperWeights Eb Ee' n m hp.1 hp.2 hq))
    (stochasticallyDominates_bernoulliProduct_of_le ?_) hmeas hA
  · exact le_antisymm (hle.trans_eq (H p hp hwin)) bot_le
  · intro e
    change ((FK.Phases.upperWeights Eb Ee' n m hp.1 hp.2 hq e : unitInterval) : ℝ) ≤
      ((FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq e : unitInterval) : ℝ)
    rw [FK.Phases.coe_upperWeights, FK.Phases.coe_upperWeights]
    by_cases hlt : p ≤ fkPrime p q
    · rw [FK.Phases.upperWeightsReal_of_le hlt, FK.Phases.upperWeightsReal_of_le hlt]
      by_cases he : e ∈ Ee
      · rw [if_pos he, if_pos (hsub he)]
      · by_cases he' : e ∈ Ee'
        · rw [if_neg he, if_pos he']
          simpa using sub_le_self (fkPrime p q) (pathEnhancement_nonneg hp.1 hp.2 hq m)
        · rw [if_neg he, if_neg he']
    · have hgt : fkPrime p q < p := lt_of_not_ge hlt
      rw [FK.Phases.upperWeightsReal_of_ge hgt, FK.Phases.upperWeightsReal_of_ge hgt]

end

end FK.AGSharpness

namespace FK.AGSharpness

open FK.EssentialWindow FK.Enhancement CurvatureVariance.Infra.Percolation Classical

noncomputable section

/-! ## Sharpness of the predicates -/

/-- With the total event the required zero mass is impossible: neither the
window predicate nor the Aizenman–Grimmett input can be satisfied by taking a
trivial event. -/
theorem not_upperWindow_univ {E : Type*} {pc : ℝ} (hpc0 : 0 ≤ pc)
    (Eb Ee : Set E) (n m : ℕ) (q : ℝ) (hq : 0 < q) :
    ¬ UpperWindow (Set.univ : Set (E → Bool)) pc Eb Ee n m q hq := by
  rintro ⟨δ', hδ', H⟩
  have hp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hfk : fkPrime 0 q = 0 := by simp [fkPrime]
  have hwin : max (0 : ℝ) (fkPrime 0 q) < pc + δ' := by
    rw [hfk, max_self]; linarith
  have h := H 0 hp hwin
  have hone : (FKLimit.bernoulliProduct
      (FK.Phases.upperWeights Eb Ee n m hp.1 hp.2 hq) : Measure (E → Bool))
        (Set.univ : Set (E → Bool)) = 1 := measure_univ
  rw [hone] at h
  exact one_ne_zero h

/-- The Aizenman–Grimmett input fails for the total event. -/
theorem not_AGInput_univ {E : Type*} {pc : ℝ} (hpc0 : 0 < pc) (S : Set E) :
    ¬ AGInput (Set.univ : Set (E → Bool)) pc hpc0 S := by
  intro hAG
  have hε0 : (0 : ℝ) < pc / 4 := by linarith
  have hεpc : pc / 4 < pc / 2 := by linarith
  obtain ⟨b, hpcb, hb1, hεb, hzero⟩ := hAG (pc / 4) hε0 hεpc
  have hone : (FKLimit.bernoulliProduct
      (decrementProfile S b (pc / 4) (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) :
        Measure (E → Bool)) (Set.univ : Set (E → Bool)) = 1 := measure_univ
  rw [hone] at hzero
  exact one_ne_zero hzero

/-! ## The window conclusion forces a single subcritical decrement law

This is the converse of `upperWindow_of_AGInput` at the level of the single
inhomogeneous law: it shows that the Aizenman–Grimmett content is *implied by*
the window conclusion, so no weakening of the window can remove it. -/

/-- The path enhancement never exceeds the FK upper parameter. -/
theorem pathEnhancement_le_fkPrime {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ) :
    pathEnhancement p q m ≤ fkPrime p q := by
  have hp' : p ≤ fkPrime p q := le_fkPrime_of_q_le_one hp0 hp1 hq hq1
  have h := pathEnhancement_le_gap hp0 hp1 hq m
  rw [abs_of_nonneg (sub_nonneg.mpr hp')] at h
  linarith

set_option warn.classDefReducibility false in
/-- In the antiferromagnetic regime the upper product law of Proposition 4.2 is
exactly a decrement profile based at the FK upper parameter. -/
theorem exists_subcritical_decrement_of_upperWindow {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ) (q : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hW : UpperWindow A pc Eb Ee n m q hq) :
    ∃ b, ∃ _ : pc < b, ∃ _ : 0 ≤ b, ∃ _ : b ≤ 1,
      ∃ E' : ℝ, ∃ hE'0 : 0 ≤ E', ∃ _ : E' ≤ b, 0 < E' ∧
      (FKLimit.bernoulliProduct
        (decrementProfile Ee b E' ‹0 ≤ b› ‹b ≤ 1› hE'0 ‹E' ≤ b› :
          E → unitInterval) : Measure (E → Bool)) A = 0 := by
  obtain ⟨δ', hδ', H⟩ := hW
  set d : ℝ := min δ' (1 - pc) / 2 with hd
  have hd0 : 0 < d := by
    have : 0 < min δ' (1 - pc) := lt_min hδ' (by linarith)
    rw [hd]; linarith
  have hdlt : d < δ' := by
    have : d ≤ δ' / 2 := by rw [hd]; linarith [min_le_left δ' (1 - pc)]
    linarith
  have hdle : d ≤ (1 - pc) / 2 := by
    have : d ≤ (1 - pc) / 2 := by rw [hd]; linarith [min_le_right δ' (1 - pc)]
    exact this
  set c : ℝ := pc + d with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hc1 : c ≤ 1 := by rw [hc]; linarith
  have hc1' : c < 1 := by rw [hc]; linarith
  have hc0' : 0 < c := by rw [hc]; linarith
  set p₁ : ℝ := fkParameterInverse q c with hp₁def
  have hp₁0 : 0 ≤ p₁ := fkParameterInverse_nonneg hq hc0 hc1
  have hp₁1 : p₁ ≤ 1 := fkParameterInverse_le_one hq hc0 hc1
  have hp₁1' : p₁ < 1 := fkParameterInverse_lt_one hq hc0 hc1'
  have hp₁pos : 0 < p₁ := by
    rw [hp₁def, fkParameterInverse]
    exact div_pos (mul_pos hq hc0') (fkParameterInverse_denominator_pos hq hc0 hc1)
  have hp₁' : fkPrime p₁ q = c := fkPrime_fkParameterInverse hq hc0 hc1
  have hp₁le : p₁ ≤ fkPrime p₁ q := le_fkPrime_of_q_le_one hp₁0 hp₁1 hq hq1.le
  have hpcb : pc < fkPrime p₁ q := by rw [hp₁']; rw [hc]; linarith
  have hb1 : fkPrime p₁ q ≤ 1 := by rw [hp₁']; exact hc1
  have hwin : max p₁ (fkPrime p₁ q) < pc + δ' := by
    rw [max_eq_right hp₁le, hp₁']
    rw [hc]; linarith
  have hzero := H p₁ ⟨hp₁0, hp₁1⟩ hwin
  refine ⟨fkPrime p₁ q, hpcb, hpc0.le.trans hpcb.le, hb1, pathEnhancement p₁ q m,
    pathEnhancement_nonneg hp₁0 hp₁1 hq m,
    pathEnhancement_le_fkPrime hp₁0 hp₁1 hq hq1.le m,
    pathEnhancement_pos hp₁pos hp₁1' hq hq1.ne m, ?_⟩
  have hb0 : 0 ≤ fkPrime p₁ q := hpc0.le.trans hpcb.le
  have hε0 : 0 ≤ pathEnhancement p₁ q m := pathEnhancement_nonneg hp₁0 hp₁1 hq m
  have hεb : pathEnhancement p₁ q m ≤ fkPrime p₁ q :=
    pathEnhancement_le_fkPrime hp₁0 hp₁1 hq hq1.le m
  have hle : decrementProfile Ee (fkPrime p₁ q) (pathEnhancement p₁ q m)
        hb0 hb1 hε0 hεb ≤
      FK.Phases.upperWeights Eb Ee n m hp₁0 hp₁1 hq := by
    intro e
    change ((decrementProfile Ee (fkPrime p₁ q) (pathEnhancement p₁ q m)
        hb0 hb1 hε0 hεb e : unitInterval) : ℝ) ≤
      ((FK.Phases.upperWeights Eb Ee n m hp₁0 hp₁1 hq e : unitInterval) : ℝ)
    rw [FK.Phases.coe_upperWeights,
      FK.Phases.upperWeightsReal_of_le hp₁le]
    simp only [decrementProfile]
    by_cases he : e ∈ Ee
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he]
      simp
  have hle' := measure_le_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (FK.Phases.upperWeights Eb Ee n m hp₁0 hp₁1 hq))
    (μ := FKLimit.bernoulliProduct (decrementProfile Ee (fkPrime p₁ q)
      (pathEnhancement p₁ q m) hb0 hb1 hε0 hεb))
    (stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA
  exact le_antisymm (hle'.trans_eq hzero) bot_le

end

end FK.AGSharpness

namespace FK.AGSharpness

open FK.EssentialWindow FK.Enhancement CurvatureVariance.Infra.Percolation Classical

noncomputable section

/-! ## Non-vacuity at the paper's parameters: the fully enhanced product

When *every* edge is enhanced the decrement profile collapses to the homogeneous
Bernoulli law, and both Aizenman–Grimmett inputs follow from the proved
one-sided reference baselines of the public tree
(`FK.PercolationRoot.percolation_percolating_eq_zero` below `p_c` and
`FK.ReferenceBaseline.percolation_percolating_eq_one` above it).  This produces
unconditional `UpperWindow`/`LowerWindow` statements for the paper's actual
percolation event `Percolating G` at the paper's parameters (`0 < p_c < 1`,
`q < 1`), so the two predicates used by Theorem 1.4 are consistent and the
residual input is a real mathematical statement, not an unsatisfiable one. -/

/-- The Aizenman–Grimmett input fails for the empty enhanced set: the decrement
profile is then the homogeneous law at a base above `pc`, which percolates. -/
theorem not_AGInput_empty_percolating {V : Type*} [Countable V] (G : SimpleGraph V)
    (o : V) (hpc0 : 0 < criticalProb G o) :
    ¬ AGInput (Percolating G) (criticalProb G o) hpc0 (∅ : Set G.edgeSet) := by
  intro hAG
  have hε0 : (0 : ℝ) < criticalProb G o / 4 := by linarith
  have hεpc : criticalProb G o / 4 < criticalProb G o / 2 := by linarith
  obtain ⟨b, hpcb, hb1, hεb, hzero⟩ := hAG (criticalProb G o / 4) hε0 hεpc
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  have hfun : decrementProfile (∅ : Set G.edgeSet) b (criticalProb G o / 4)
      hb0 hb1 hε0.le hεb = fun _ => (⟨b, hb0, hb1⟩ : unitInterval) := by
    funext e
    apply Subtype.ext
    simp [decrementProfile]
  rw [hfun] at hzero
  have hone : (FKLimit.bernoulliProduct
      (fun _ : G.edgeSet => (⟨b, hb0, hb1⟩ : unitInterval)) :
        Measure (G.edgeSet → Bool)) (Percolating G) = 1 :=
    FK.ReferenceBaseline.percolation_percolating_eq_one G o hpcb
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- The Aizenman–Grimmett subcritical input holds when every edge is enhanced. -/
theorem AGInput_percolating_univ {V : Type*} [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1) :
    AGInput (Percolating G) (criticalProb G o) hpc0 (Set.univ : Set G.edgeSet) := by
  intro ε hε0 hεpc
  set pc : ℝ := criticalProb G o
  have hpc0' : 0 < pc := hpc0
  set b : ℝ := min (pc + ε / 2) ((1 + pc) / 2)
  have hpcb : pc < b := lt_min (by linarith) (by linarith)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (by linarith)
  have hεb : ε ≤ b := le_min (by linarith) (by linarith)
  have hb0 : 0 ≤ b := hpc0'.le.trans hpcb.le
  have hble : b - ε < pc := by
    have h1 : b ≤ pc + ε / 2 := min_le_left _ _
    linarith
  refine ⟨b, hpcb, hb1, hεb, ?_⟩
  have hs0 : 0 ≤ b - ε := by linarith
  have hs1 : b - ε ≤ 1 := by linarith
  have hfun : decrementProfile (Set.univ : Set G.edgeSet) b ε hb0 hb1 hε0.le hεb
      = fun _ => (⟨b - ε, hs0, hs1⟩ : unitInterval) := by
    funext e
    apply Subtype.ext
    simp [decrementProfile]
  rw [hfun]
  exact FK.PercolationRoot.percolation_percolating_eq_zero hG hs0 hble

/-- Consequently the upper window of Theorem 1.4 holds, for every `Eb` and every
enhancement length `m`, in the fully enhanced case. -/
theorem upperWindow_percolating_univ {V : Type*} [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] (hG : G.Connected) (o : V) (Eb : Set G.edgeSet) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1) :
    UpperWindow (Percolating G) (criticalProb G o) Eb
      (Set.univ : Set G.edgeSet) n m q hq :=
  upperWindow_percolating_of_AG_q_lt_one G hG (criticalProb G o) Eb Set.univ n m q hq hq1
    hpc0 hpc1 (AGInput_percolating_univ G hG o hpc0 hpc1)

/-- The Aizenman–Grimmett supercritical input holds when every edge is enhanced. -/
theorem lowerAGInput_percolating_univ {V : Type*} [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] (_hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < (1 - criticalProb G o) / 2 →
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ _ : a < criticalProb G o, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct
          (incrementProfile (Set.univ : Set G.edgeSet) a ε ha0 hε0.le haε1) :
            Measure (G.edgeSet → Bool)) (Percolating G) = 1 := by
  intro ε hε0 hεpc
  set pc : ℝ := criticalProb G o
  have hpc0' : 0 < pc := hpc0
  have hpc1' : pc < 1 := hpc1
  set a : ℝ := max (pc - ε / 2) (pc / 2)
  have ha0 : 0 ≤ a := le_trans (by linarith : 0 ≤ pc / 2) (le_max_right _ _)
  have hapc : a < pc := max_lt (by linarith) (by linarith)
  have haε1 : a + ε ≤ 1 := by linarith
  have hgt : pc < a + ε := by
    have h1 : pc - ε / 2 ≤ a := le_max_left _ _
    linarith
  have ht0 : 0 ≤ a + ε := by linarith
  refine ⟨a, ha0, hapc, haε1, ?_⟩
  have hfun : incrementProfile (Set.univ : Set G.edgeSet) a ε ha0 hε0.le haε1
      = fun _ => (⟨a + ε, ht0, haε1⟩ : unitInterval) := by
    funext e
    apply Subtype.ext
    simp [incrementProfile]
  rw [hfun]
  exact FK.ReferenceBaseline.percolation_percolating_eq_one G o hgt

/-- Consequently the lower window of Theorem 1.4 holds, for every `Ee` and every
devices size `n`, in the fully enhanced case. -/
theorem lowerWindow_percolating_univ {V : Type*} [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] (hG : G.Connected) (o : V) (Ee : Set G.edgeSet) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1) :
    LowerWindow (Percolating G) (criticalProb G o) (Set.univ : Set G.edgeSet) Ee
      n m q hq :=
  lowerWindow_percolating_of_AG_q_lt_one G hG (criticalProb G o) Set.univ Ee n m q hq hq1
    hpc0 hpc1 (lowerAGInput_percolating_univ G hG o hpc0 hpc1)

end

end FK.AGSharpness

namespace FK.AGSharpness

open FK.EssentialWindow FK.Enhancement CurvatureVariance.Infra.Percolation Classical

noncomputable section

/-! ## The supercritical mirror

`LowerWindow` is the supercritical input of Theorem 1.4(2).  The same two facts
hold: it is monotone in the enhanced set, and it forces a single *supercritical*
increment law based strictly below `pc`. -/

/-- The increment profile of a larger enhanced set is pointwise larger. -/
theorem incrementProfile_le_of_subset {E : Type*} {S T : Set E} (hST : S ⊆ T)
    {a ε : ℝ} (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε) (haε1 : a + ε ≤ 1) :
    incrementProfile S a ε ha0 hε0 haε1 ≤
      incrementProfile T a ε ha0 hε0 haε1 := by
  intro e
  change ((incrementProfile S a ε ha0 hε0 haε1 e : unitInterval) : ℝ) ≤
    ((incrementProfile T a ε ha0 hε0 haε1 e : unitInterval) : ℝ)
  simp only [incrementProfile]
  by_cases he : e ∈ S
  · have heT : e ∈ T := hST he
    rw [if_pos he, if_pos heT]
  · by_cases heT : e ∈ T
    · rw [if_neg he, if_pos heT]
      exact le_add_of_nonneg_right hε0
    · rw [if_neg he, if_neg heT]

/-- `LowerWindow` is monotone in the enhanced set. -/
theorem lowerWindow_of_subset {E : Type*} [Countable E] {A : Set (E → Bool)}
    (hmeas : MeasurableSet A) (hA : IsUpperSet A)
    {pc : ℝ} {Eb Eb' Ee : Set E} {n m : ℕ} {q : ℝ} {hq : 0 < q}
    (hsub : Eb ⊆ Eb') (hW : LowerWindow A pc Eb Ee n m q hq) :
    LowerWindow A pc Eb' Ee n m q hq := by
  obtain ⟨δ, hδ, H⟩ := hW
  refine ⟨δ, hδ, ?_⟩
  intro p hp hwin
  have hpoint : FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq ≤
      FK.Phases.lowerWeights Eb' Ee n m hp.1 hp.2 hq := by
    intro e
    change ((FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq e : unitInterval) : ℝ) ≤
      ((FK.Phases.lowerWeights Eb' Ee n m hp.1 hp.2 hq e : unitInterval) : ℝ)
    rw [FK.Phases.coe_lowerWeights, FK.Phases.coe_lowerWeights]
    by_cases hlt : p ≤ fkPrime p q
    · rw [FK.Phases.lowerWeightsReal_of_le hlt, FK.Phases.lowerWeightsReal_of_le hlt]
      by_cases he : e ∈ Eb
      · rw [if_pos he, if_pos (hsub he)]
      · by_cases he' : e ∈ Eb'
        · rw [if_neg he, if_pos he']
          have h := cutsetEnhancement_nonneg hp.1 hp.2 hq n
          linarith
        · rw [if_neg he, if_neg he']
    · have hgt : fkPrime p q < p := lt_of_not_ge hlt
      rw [FK.Phases.lowerWeightsReal_of_ge hgt, FK.Phases.lowerWeightsReal_of_ge hgt]
  have hmono := measure_le_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le hpoint) hmeas hA
  have h1 := H p hp hwin
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = (FKLimit.bernoulliProduct
        (FK.Phases.lowerWeights Eb Ee n m hp.1 hp.2 hq) : Measure (E → Bool)) A := h1.symm
    _ ≤ (FKLimit.bernoulliProduct
        (FK.Phases.lowerWeights Eb' Ee n m hp.1 hp.2 hq) : Measure (E → Bool)) A := hmono

end

end FK.AGSharpness

namespace FK.AGSharpness

open FK.EssentialWindow FK.Enhancement CurvatureVariance.Infra.Percolation Classical

noncomputable section

/-! ## Which device family each window uses

Proposition 4.2 pairs the *star* devices with the lower bound and the *cycle*
devices with the upper bound.  In the antiferromagnetic regime `q < 1` the upper
product law of the public interface does not involve the star set at all, and in
the ferromagnetic regime `1 < q` the lower product law does not involve the
cycle set.  The next two theorems record that dispatch exactly, which is the
formal counterpart of the source's label pairing (the one corrected in
`docs/ERRATA-AND-DEVIATIONS.md` for the proof of Theorem 1.4). -/

/-- For `q ≤ 1` the upper product law does not depend on the star set. -/
theorem upperWeights_indep_Eb {E : Type*} (Eb Eb' Ee : Set E) (n m : ℕ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    FK.Phases.upperWeights Eb Ee n m hp0 hp1 hq =
      FK.Phases.upperWeights Eb' Ee n m hp0 hp1 hq := by
  funext e
  apply Subtype.ext
  rw [FK.Phases.coe_upperWeights, FK.Phases.coe_upperWeights,
    FK.Phases.upperWeightsReal_of_le (le_fkPrime_of_q_le_one hp0 hp1 hq hq1),
    FK.Phases.upperWeightsReal_of_le (le_fkPrime_of_q_le_one hp0 hp1 hq hq1)]

/-- For `q ≤ 1` the upper window depends on the cycle set only. -/
theorem upperWindow_indep_Eb {E : Type*} [Countable E] {A : Set (E → Bool)}
    {pc : ℝ} {Eb Eb' Ee : Set E} {n m : ℕ} {q : ℝ} {hq : 0 < q} (hq1 : q ≤ 1) :
    UpperWindow A pc Eb Ee n m q hq ↔ UpperWindow A pc Eb' Ee n m q hq := by
  constructor
  · intro hW
    obtain ⟨δ', hδ', H⟩ := hW
    refine ⟨δ', hδ', ?_⟩
    intro p hp hwin
    rw [← upperWeights_indep_Eb Eb Eb' Ee n m hp.1 hp.2 hq hq1]
    exact H p hp hwin
  · intro hW
    obtain ⟨δ', hδ', H⟩ := hW
    refine ⟨δ', hδ', ?_⟩
    intro p hp hwin
    rw [upperWeights_indep_Eb Eb Eb' Ee n m hp.1 hp.2 hq hq1]
    exact H p hp hwin

/-- For `q ≤ 1` the lower product law does not depend on the cycle set. -/
theorem lowerWeights_indep_Ee {E : Type*} (Eb Ee Ee' : Set E) (n m : ℕ) {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    FK.Phases.lowerWeights Eb Ee n m hp0 hp1 hq =
      FK.Phases.lowerWeights Eb Ee' n m hp0 hp1 hq := by
  funext e
  apply Subtype.ext
  rw [FK.Phases.coe_lowerWeights, FK.Phases.coe_lowerWeights,
    FK.Phases.lowerWeightsReal_of_le (le_fkPrime_of_q_le_one hp0 hp1 hq hq1),
    FK.Phases.lowerWeightsReal_of_le (le_fkPrime_of_q_le_one hp0 hp1 hq hq1)]

/-- For `q ≤ 1` the lower window depends on the star set only. -/
theorem lowerWindow_indep_Ee {E : Type*} [Countable E] {A : Set (E → Bool)}
    {pc : ℝ} {Eb Ee Ee' : Set E} {n m : ℕ} {q : ℝ} {hq : 0 < q} (hq1 : q ≤ 1) :
    LowerWindow A pc Eb Ee n m q hq ↔ LowerWindow A pc Eb Ee' n m q hq := by
  constructor
  · intro hW
    obtain ⟨δ, hδ, H⟩ := hW
    refine ⟨δ, hδ, ?_⟩
    intro p hp hwin
    rw [← lowerWeights_indep_Ee Eb Ee Ee' n m hp.1 hp.2 hq hq1]
    exact H p hp hwin
  · intro hW
    obtain ⟨δ, hδ, H⟩ := hW
    refine ⟨δ, hδ, ?_⟩
    intro p hp hwin
    rw [lowerWeights_indep_Ee Eb Ee Ee' n m hp.1 hp.2 hq hq1]
    exact H p hp hwin

end

end FK.AGSharpness

namespace FK.AGSharpness

open FK.EssentialWindow FK.Enhancement CurvatureVariance.Infra.Percolation Classical

noncomputable section

/-! ## The converse in the ferromagnetic regime `1 < q`

For `1 < q` the *upper* product law of Proposition 4.2 is based at `p` and
decremented on the star set `Eb`; the same sharpness argument then extracts a
subcritical decrement law with base strictly above `pc`, without needing the
parameter inverse. -/

set_option warn.classDefReducibility false in
/-- For `1 < q`, `UpperWindow` forces a subcritical decrement product law based
strictly above `pc` and decremented on the star set. -/
theorem exists_subcritical_decrement_of_upperWindow_one_lt_q {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ) (q : ℝ)
    (hq : 0 < q) (hq1 : 1 < q) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hW : UpperWindow A pc Eb Ee n m q hq) :
    ∃ b, ∃ _ : pc < b, ∃ _ : 0 ≤ b, ∃ _ : b ≤ 1,
      ∃ E' : ℝ, ∃ hE'0 : 0 ≤ E', ∃ _ : E' ≤ b, 0 < E' ∧
      (FKLimit.bernoulliProduct
        (decrementProfile Eb b E' ‹0 ≤ b› ‹b ≤ 1› hE'0 ‹E' ≤ b› :
          E → unitInterval) : Measure (E → Bool)) A = 0 := by
  obtain ⟨δ', hδ', H⟩ := hW
  set d : ℝ := min δ' (1 - pc) / 2 with hd
  have hd0 : 0 < d := by
    have : 0 < min δ' (1 - pc) := lt_min hδ' (by linarith)
    rw [hd]; linarith
  have hdlt : d < δ' := by
    have : d ≤ δ' / 2 := by rw [hd]; linarith [min_le_left δ' (1 - pc)]
    linarith
  have hdle : d ≤ (1 - pc) / 2 := by
    have : d ≤ (1 - pc) / 2 := by rw [hd]; linarith [min_le_right δ' (1 - pc)]
    exact this
  set p₁ : ℝ := pc + d with hp₁
  have hp₁0 : 0 < p₁ := by rw [hp₁]; linarith
  have hp₁1 : p₁ ≤ 1 := by rw [hp₁]; linarith
  have hp₁1' : p₁ < 1 := by rw [hp₁]; linarith
  have hlt : fkPrime p₁ q < p₁ := (fkPrime_lt_iff hp₁0 hp₁1' hq).2 hq1
  have hwin : max p₁ (fkPrime p₁ q) < pc + δ' := by
    rw [max_eq_left hlt.le]; rw [hp₁]; linarith
  have hzero := H p₁ ⟨hp₁0.le, hp₁1⟩ hwin
  have hcut0 : 0 ≤ cutsetEnhancement p₁ q n := cutsetEnhancement_nonneg hp₁0.le hp₁1 hq n
  have hcutb : cutsetEnhancement p₁ q n ≤ p₁ := by
    have h := cutsetEnhancement_le_gap hp₁0.le hp₁1 hq n
    rw [abs_of_neg (sub_neg.mpr hlt)] at h
    have hp'0 := fkPrime_nonneg hp₁0.le hp₁1 hq
    linarith
  refine ⟨p₁, by rw [hp₁]; linarith, hp₁0.le, hp₁1, cutsetEnhancement p₁ q n,
    hcut0, hcutb, cutsetEnhancement_pos hp₁0 hp₁1' hq (ne_of_gt hq1) n, ?_⟩
  have hle : decrementProfile Eb p₁ (cutsetEnhancement p₁ q n)
        hp₁0.le hp₁1 hcut0 hcutb ≤
      FK.Phases.upperWeights Eb Ee n m hp₁0.le hp₁1 hq := by
    intro e
    change ((decrementProfile Eb p₁ (cutsetEnhancement p₁ q n)
        hp₁0.le hp₁1 hcut0 hcutb e : unitInterval) : ℝ) ≤
      ((FK.Phases.upperWeights Eb Ee n m hp₁0.le hp₁1 hq e : unitInterval) : ℝ)
    rw [FK.Phases.coe_upperWeights, FK.Phases.upperWeightsReal_of_ge hlt]
    simp only [decrementProfile]
    by_cases he : e ∈ Eb
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he]
      simp
  have hle' := measure_le_of_stochasticallyDominates
    (ν := FKLimit.bernoulliProduct (FK.Phases.upperWeights Eb Ee n m hp₁0.le hp₁1 hq))
    (μ := FKLimit.bernoulliProduct (decrementProfile Eb p₁ (cutsetEnhancement p₁ q n)
      hp₁0.le hp₁1 hcut0 hcutb))
    (stochasticallyDominates_bernoulliProduct_of_le hle) hmeas hA
  exact le_antisymm (hle'.trans_eq hzero) bot_le

end

end FK.AGSharpness
