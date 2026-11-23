import FK.EssentialWindow
import FK.StrongUniqueness

/-!
# Actual percolation reference laws for essential-enhancement windows

The deep Aizenman--Grimmett strict-shift theorem is not available in the
vendored percolation library.  This file isolates the exact increasing event
on which its reference-law conclusions are needed, and proves the elementary
profile monotonicity used to move those conclusions to endpoint-safe bases.
No strict shift is asserted here.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical

noncomputable section

/-- Some vertex has an infinite open-walk cluster.  This is the actual
percolation event used by the theorem, rather than an arbitrary upper event. -/
def Percolating {V : Type*} (G : SimpleGraph V) : Set (G.edgeSet → Bool) :=
  {ω | ∃ o, {x | OpenConnected G ω Set.univ o x}.Infinite}

/-- Percolation is the complement of the nonpercolation event already used by
`StrongUniqueness`. -/
theorem percolating_eq_compl_nonPercolating {V : Type*} (G : SimpleGraph V) :
    Percolating G = (FK.NonPercolating G)ᶜ := by
  ext ω
  simp only [Percolating, FK.NonPercolating, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨o, ho⟩ hfin
    exact ho (hfin o)
  · intro h
    push_neg at h
    obtain ⟨o, ho⟩ := h
    exact ⟨o, Set.not_finite.mp ho⟩

/-- Percolation is an increasing configuration event. -/
theorem isUpperSet_percolating {V : Type*} (G : SimpleGraph V) :
    IsUpperSet (Percolating G) := by
  intro ω η hωη hω
  obtain ⟨o, ho⟩ := hω
  refine ⟨o, ho.mono ?_⟩
  intro x hx
  exact OpenConnected.mono_config hx hωη

/-- Under the standing graph hypotheses, the actual percolation event is
measurable. -/
theorem measurableSet_percolating {V : Type*} [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected) :
    MeasurableSet (Percolating G) := by
  rw [percolating_eq_compl_nonPercolating]
  exact (FK.measurableSet_nonPercolating G hG).compl

/-- Almost-sure nonpercolation is exactly zero mass for the actual increasing
percolation event. -/
theorem ae_nonPercolating_iff_measure_percolating_eq_zero {V : Type*}
    (G : SimpleGraph V) (μ : Measure (G.edgeSet → Bool)) :
    (∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) ↔ μ (Percolating G) = 0 := by
  rw [ae_iff]
  have hs : {ω | ω ∉ FK.NonPercolating G} = Percolating G := by
    rw [percolating_eq_compl_nonPercolating]
    rfl
  rw [hs]

/-- The base of a decrement profile can be decreased without leaving the
unit interval. -/
theorem decrementProfile_mono {E : Type*} (S : Set E) {b c ε : ℝ}
    {hb0 : 0 ≤ b} {hb1 : b ≤ 1} {hc0 : 0 ≤ c} {hc1 : c ≤ 1}
    {hε0 : 0 ≤ ε} {hεb : ε ≤ b} {hεc : ε ≤ c} (hbc : b ≤ c) :
    decrementProfile S b ε hb0 hb1 hε0 hεb ≤
      decrementProfile S c ε hc0 hc1 hε0 hεc := by
  intro e
  change ((decrementProfile S b ε hb0 hb1 hε0 hεb e : unitInterval) : ℝ) ≤
    ((decrementProfile S c ε hc0 hc1 hε0 hεc e : unitInterval) : ℝ)
  simp only [decrementProfile]
  split_ifs
  · exact sub_le_sub_right hbc ε
  · exact hbc

/-- The base of an increment profile can be increased without leaving the unit
interval. -/
theorem incrementProfile_mono {E : Type*} (S : Set E) {a c ε : ℝ}
    {ha0 : 0 ≤ a} {hc0 : 0 ≤ c} {hε0 : 0 ≤ ε}
    {haε1 : a + ε ≤ 1} {hcε1 : c + ε ≤ 1} (hac : a ≤ c) :
    incrementProfile S a ε ha0 hε0 haε1 ≤
      incrementProfile S c ε hc0 hε0 hcε1 := by
  intro e
  change ((incrementProfile S a ε ha0 hε0 haε1 e : unitInterval) : ℝ) ≤
    ((incrementProfile S c ε hc0 hε0 hcε1 e : unitInterval) : ℝ)
  simp only [incrementProfile]
  split_ifs
  · change a + ε ≤ c + ε
    linarith
  · exact hac

/-- A zero-mass reference conclusion at base `c` persists at every smaller
base `b`, for the same decrement and enhanced set. -/
theorem measure_decrementProfile_eq_zero_of_le {E : Type*} [Countable E]
    (S : Set E) {A : Set (E → Bool)} (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    {b c ε : ℝ} {hb0 : 0 ≤ b} {hb1 : b ≤ 1} {hc0 : 0 ≤ c} {hc1 : c ≤ 1}
    {hε0 : 0 < ε} {hεb : ε ≤ b} {hεc : ε ≤ c} (hbc : b ≤ c)
    (href : (FKLimit.bernoulliProduct
      (decrementProfile S c ε hc0 hc1 hε0.le hεc) : Measure (E → Bool)) A = 0) :
    (FKLimit.bernoulliProduct
      (decrementProfile S b ε hb0 hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
  exact measure_eq_zero_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le
      (decrementProfile_mono S hbc)) hmeas hA href

/-- A full-mass reference conclusion at base `a` persists at every larger base
`c`, for the same increment and enhanced set. -/
theorem measure_incrementProfile_eq_one_of_le {E : Type*} [Countable E]
    (S : Set E) {A : Set (E → Bool)} (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    {a c ε : ℝ} {ha0 : 0 ≤ a} {hc0 : 0 ≤ c} {hε0 : 0 < ε}
    {haε1 : a + ε ≤ 1} {hcε1 : c + ε ≤ 1} (hac : a ≤ c)
    (href : (FKLimit.bernoulliProduct
      (incrementProfile S a ε ha0 hε0.le haε1) : Measure (E → Bool)) A = 1) :
    (FKLimit.bernoulliProduct
      (incrementProfile S c ε hc0 hε0.le hcε1) : Measure (E → Bool)) A = 1 := by
  exact measure_eq_one_of_stochasticallyDominates
    (stochasticallyDominates_bernoulliProduct_of_le
      (incrementProfile_mono S hac)) hmeas hA href

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- In the Antiferromagnetic regime `q ≤ 1`, the FK transformation cannot
increase the parameter by more than the factor `q⁻¹`. -/
theorem q_mul_fkPrime_le {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) : q * fkPrime p q ≤ p := by
  have hd : 0 < p + q * (1 - p) := denominator_pos hp0 hp1 hq
  have hqD : q ≤ p + q * (1 - p) := by
    have h := mul_nonneg hp0 (sub_nonneg.mpr hq1)
    nlinarith
  have hdiv : 0 ≤ p / (p + q * (1 - p)) := div_nonneg hp0 hd.le
  calc
    q * fkPrime p q = q * (p / (p + q * (1 - p))) := rfl
    _ ≤ (p + q * (1 - p)) * (p / (p + q * (1 - p))) :=
      mul_le_mul_of_nonneg_right hqD hdiv
    _ = p := by field_simp

/-- Analytic assembly of the upper window for `q < 1`.

The only probabilistic input is `hAG`: for every sufficiently small positive
constant decrement, some base strictly above `pc` gives a zero-mass reference
law.  This is the precise Aizenman--Grimmett strict-shift input.  The compact
set, the uniform path-enhancement bound, the endpoint margins, and the final
window are proved here; none is an additional hypothesis. -/
theorem upperWindow_of_AG_q_lt_one {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2),
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (decrementProfile Ee b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (E → Bool)) A = 0) :
    UpperWindow A pc Eb Ee n m q hq := by
  let B : ℝ := (pc + 1) / 2
  let K : Set ℝ := Set.Icc (q * pc / 2) B
  have hBpc : pc < B := by dsimp [B]; linarith
  have hB1 : B < 1 := by dsimp [B]; linarith
  have hL0 : 0 < q * pc / 2 := div_pos (mul_pos hq hpc0) (by norm_num)
  have hKopen : K ⊆ Set.Ioo 0 1 := by
    rintro p ⟨hpL, hpU⟩
    exact ⟨hL0.trans_le hpL, hpU.trans_lt hB1⟩
  obtain ⟨η, hη0, hη⟩ := exists_pos_pathEnhancement hq hq1.ne
    (K := K) isCompact_Icc hKopen m
  let ε : ℝ := min η (pc / 4)
  have hε0 : 0 < ε := lt_min hη0 (by positivity)
  have hεη : ε ≤ η := min_le_left _ _
  have hεpc : ε < pc / 2 := by
    have h := min_le_right η (pc / 4)
    dsimp [ε]
    linarith
  obtain ⟨b₀, hpcb₀, hb₀1, hεb₀, href₀⟩ := hAG ε hε0 hεpc
  let b : ℝ := min b₀ B
  have hpcb : pc < b := lt_min hpcb₀ hBpc
  have hb1 : b ≤ 1 := (min_le_right _ _).trans hB1.le
  have hεb : ε ≤ b := by linarith
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  have href : (FKLimit.bernoulliProduct
      (decrementProfile Ee b ε hb0 hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
    exact measure_decrementProfile_eq_zero_of_le Ee hA hmeas (hε0 := hε0)
      (show b ≤ b₀ from min_le_left _ _) href₀
  apply upperWindow_of_decrementProfile_q_lt_one A pc Eb Ee n m q hq hq1
    hpc0.le hA hmeas b ε K hpcb hb1 hε0 hεb
  · intro p hp hpwindow hp'lower
    have hp'upper : fkPrime p q < b :=
      (le_max_right p (fkPrime p q)).trans_lt hpwindow
    have hpple : p ≤ fkPrime p q := le_fkPrime_of_q_le_one hp.1 hp.2 hq hq1.le
    refine ⟨?_, ?_⟩
    · have hlow : q * pc / 2 < p := by
        calc
          q * pc / 2 < q * (b - ε) := by
            convert mul_lt_mul_of_pos_left (show pc / 2 < b - ε by linarith) hq using 1 <;>
              ring
          _ < q * fkPrime p q := mul_lt_mul_of_pos_left hp'lower hq
          _ ≤ p := q_mul_fkPrime_le hp.1 hp.2 hq hq1.le
      exact hlow.le
    · exact hpple.trans (hp'upper.le.trans (min_le_right _ _))
  · exact href
  · intro p hpK
    exact hεη.trans (hη p hpK)

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- Analytic assembly of the lower window for `q < 1`.  As in the upper
case, `hAG` is the sole external probabilistic input; the uniform cutset
bound and all parameter-cover and endpoint arguments are proved. -/
theorem lowerWindow_of_AG_q_lt_one {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < (1 - pc) / 2),
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (incrementProfile Eb a ε ha0 hε0.le haε1) :
          Measure (E → Bool)) A = 1) :
    LowerWindow A pc Eb Ee n m q hq := by
  let B : ℝ := (pc + 1) / 2
  let K : Set ℝ := Set.Icc (pc / 2) B
  have hB1 : B < 1 := by dsimp [B]; linarith
  have hpcB : pc < B := by dsimp [B]; linarith
  have hKopen : K ⊆ Set.Ioo 0 1 := by
    rintro p ⟨hpL, hpU⟩
    exact ⟨(by positivity : 0 < pc / 2).trans_le hpL, hpU.trans_lt hB1⟩
  obtain ⟨η, hη0, hη⟩ := exists_pos_cutsetEnhancement hq hq1.ne
    (K := K) isCompact_Icc hKopen n
  let ε : ℝ := min η ((1 - pc) / 4)
  have hε0 : 0 < ε := lt_min hη0 (by positivity)
  have hεη : ε ≤ η := min_le_left _ _
  have hεpc : ε < (1 - pc) / 2 := by
    have h := min_le_right η ((1 - pc) / 4)
    dsimp [ε]
    linarith
  obtain ⟨a₀, ha₀0, ha₀pc, ha₀ε1, href₀⟩ := hAG ε hε0 hεpc
  let a : ℝ := max a₀ (pc / 2)
  have ha_lower : pc / 2 ≤ a := le_max_right _ _
  have ha0 : 0 ≤ a := (by positivity : 0 ≤ pc / 2).trans ha_lower
  have hapc : a < pc := max_lt ha₀pc (by linarith)
  have haε1 : a + ε ≤ 1 := by
    have h := min_le_right η ((1 - pc) / 4)
    dsimp [ε] at hεpc ⊢
    linarith
  have href : (FKLimit.bernoulliProduct
      (incrementProfile Eb a ε ha0 hε0.le haε1) : Measure (E → Bool)) A = 1 := by
    exact measure_incrementProfile_eq_one_of_le Eb hA hmeas (hε0 := hε0)
      (show a₀ ≤ a from le_max_left _ _) href₀
  apply lowerWindow_of_incrementProfile_q_lt_one A pc Eb Ee n m q hq hq1
    hA hmeas a ε K hapc ha0 hε0 haε1
  · intro p hp hpwindow hpupper
    have hpa : a < p := hpwindow.trans_le (min_le_left _ _)
    refine ⟨(ha_lower.trans_lt hpa).le, ?_⟩
    dsimp [B]
    linarith
  · exact href
  · intro p hpK
    exact hεη.trans (hη p hpK)

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- Analytic assembly of the upper window for `1 < q`. -/
theorem upperWindow_of_AG_one_lt_q {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2),
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (decrementProfile Eb b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (E → Bool)) A = 0) :
    UpperWindow A pc Eb Ee n m q hq := by
  let B : ℝ := (pc + 1) / 2
  let K : Set ℝ := Set.Icc (pc / 2) B
  have hBpc : pc < B := by dsimp [B]; linarith
  have hB1 : B < 1 := by dsimp [B]; linarith
  have hKopen : K ⊆ Set.Ioo 0 1 := by
    rintro p ⟨hpL, hpU⟩
    exact ⟨(by positivity : 0 < pc / 2).trans_le hpL, hpU.trans_lt hB1⟩
  obtain ⟨η, hη0, hη⟩ := exists_pos_cutsetEnhancement hq hq1.ne'
    (K := K) isCompact_Icc hKopen n
  let ε : ℝ := min η (pc / 4)
  have hε0 : 0 < ε := lt_min hη0 (by positivity)
  have hεη : ε ≤ η := min_le_left _ _
  have hεpc : ε < pc / 2 := by
    have h := min_le_right η (pc / 4)
    dsimp [ε]
    linarith
  obtain ⟨b₀, hpcb₀, hb₀1, hεb₀, href₀⟩ := hAG ε hε0 hεpc
  let b : ℝ := min b₀ B
  have hpcb : pc < b := lt_min hpcb₀ hBpc
  have hb1 : b ≤ 1 := (min_le_right _ _).trans hB1.le
  have hεb : ε ≤ b := by linarith
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  have href : (FKLimit.bernoulliProduct
      (decrementProfile Eb b ε hb0 hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
    exact measure_decrementProfile_eq_zero_of_le Eb hA hmeas (hε0 := hε0)
      (show b ≤ b₀ from min_le_left _ _) href₀
  apply upperWindow_of_decrementProfile_one_lt_q A pc Eb Ee n m q hq hq1
    hpc0.le hA hmeas b ε K hpcb hb1 hε0 hεb
  · intro p hp hpwindow hplower
    have hpupper : p < b := (le_max_left p (fkPrime p q)).trans_lt hpwindow
    refine ⟨(show pc / 2 < p by linarith).le, ?_⟩
    exact hpupper.le.trans (min_le_right _ _)
  · exact href
  · intro p hpK
    exact hεη.trans (hη p hpK)

/-- On the closed parameter interval, `p ↦ p / (p + q (1-p))` is strictly
increasing for every positive `q`, including both endpoints. -/
theorem strictMonoOn_fkPrime {q : ℝ} (hq : 0 < q) :
    StrictMonoOn (fun p : ℝ ↦ fkPrime p q) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hdx : 0 < x + q * (1 - x) := denominator_pos hx.1 hx.2 hq
  have hdy : 0 < y + q * (1 - y) := denominator_pos hy.1 hy.2 hq
  simp only [fkPrime]
  rw [div_lt_div_iff₀ hdx hdy]
  have hmul := mul_lt_mul_of_pos_left hxy hq
  nlinarith

/-- The inverse of the FK parameter map, written explicitly on the closed
unit square. -/
def fkParameterInverse (q c : ℝ) : ℝ := q * c / (1 + (q - 1) * c)

lemma fkParameterInverse_denominator_pos {q c : ℝ} (hq : 0 < q)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : 0 < 1 + (q - 1) * c := by
  have hd := denominator_pos (p := 1 - c) (q := q)
    (sub_nonneg.mpr hc1) (by linarith) hq
  nlinarith

lemma fkParameterInverse_nonneg {q c : ℝ} (hq : 0 < q) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ fkParameterInverse q c := by
  exact div_nonneg (mul_nonneg hq.le hc0)
    (fkParameterInverse_denominator_pos hq hc0 hc1).le

lemma fkParameterInverse_le_one {q c : ℝ} (hq : 0 < q) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    fkParameterInverse q c ≤ 1 := by
  rw [fkParameterInverse, div_le_one (fkParameterInverse_denominator_pos hq hc0 hc1)]
  nlinarith

lemma fkParameterInverse_lt_one {q c : ℝ} (hq : 0 < q) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    fkParameterInverse q c < 1 := by
  rw [fkParameterInverse, div_lt_one (fkParameterInverse_denominator_pos hq hc0 hc1.le)]
  have h := fkParameterInverse_denominator_pos hq hc0 hc1.le
  nlinarith

lemma fkPrime_fkParameterInverse {q c : ℝ} (hq : 0 < q) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    fkPrime (fkParameterInverse q c) q = c := by
  have hd := fkParameterInverse_denominator_pos hq hc0 hc1
  have hu0 := fkParameterInverse_nonneg hq hc0 hc1
  have hu1 := fkParameterInverse_le_one hq hc0 hc1
  have hD := denominator_pos hu0 hu1 hq
  rw [fkPrime]
  apply (div_eq_iff hD.ne').2
  have hu : fkParameterInverse q c * (1 + (q - 1) * c) = q * c := by
    exact div_mul_cancel₀ (q * c) hd.ne'
  nlinarith [hu]

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- Analytic assembly of the lower window for `1 < q`.  The upper endpoint
of the compact parameter set is the explicit inverse FK parameter of
`(pc + 1) / 2`; this is what keeps the cover away from `p = 1`. -/
theorem lowerWindow_of_AG_one_lt_q {E : Type*} [Countable E]
    (A : Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < (1 - pc) / 2),
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (incrementProfile Ee a ε ha0 hε0.le haε1) :
          Measure (E → Bool)) A = 1) :
    LowerWindow A pc Eb Ee n m q hq := by
  let B : ℝ := (pc + 1) / 2
  let U : ℝ := fkParameterInverse q B
  let K : Set ℝ := Set.Icc (pc / 2) U
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hB1 : B < 1 := by dsimp [B]; linarith
  have hU0 : 0 ≤ U := fkParameterInverse_nonneg hq hB0 hB1.le
  have hU1 : U < 1 := fkParameterInverse_lt_one hq hB0 hB1
  have hUmem : U ∈ Set.Icc (0 : ℝ) 1 := ⟨hU0, hU1.le⟩
  have hUFK : fkPrime U q = B := fkPrime_fkParameterInverse hq hB0 hB1.le
  have hKopen : K ⊆ Set.Ioo 0 1 := by
    rintro p ⟨hpL, hpU⟩
    exact ⟨(by positivity : 0 < pc / 2).trans_le hpL, hpU.trans_lt hU1⟩
  obtain ⟨η, hη0, hη⟩ := exists_pos_pathEnhancement hq hq1.ne'
    (K := K) isCompact_Icc hKopen m
  let ε : ℝ := min η ((1 - pc) / 4)
  have hε0 : 0 < ε := lt_min hη0 (by positivity)
  have hεη : ε ≤ η := min_le_left _ _
  have hεpc : ε < (1 - pc) / 2 := by
    have h := min_le_right η ((1 - pc) / 4)
    dsimp [ε]
    linarith
  obtain ⟨a₀, ha₀0, ha₀pc, ha₀ε1, href₀⟩ := hAG ε hε0 hεpc
  let a : ℝ := max a₀ (pc / 2)
  have ha_lower : pc / 2 ≤ a := le_max_right _ _
  have ha0 : 0 ≤ a := (by positivity : 0 ≤ pc / 2).trans ha_lower
  have hapc : a < pc := max_lt ha₀pc (by linarith)
  have haε1 : a + ε ≤ 1 := by
    have h := min_le_right η ((1 - pc) / 4)
    dsimp [ε] at hεpc ⊢
    linarith
  have href : (FKLimit.bernoulliProduct
      (incrementProfile Ee a ε ha0 hε0.le haε1) : Measure (E → Bool)) A = 1 := by
    exact measure_incrementProfile_eq_one_of_le Ee hA hmeas (hε0 := hε0)
      (show a₀ ≤ a from le_max_left _ _) href₀
  apply lowerWindow_of_incrementProfile_one_lt_q A pc Eb Ee n m q hq hq1
    hA hmeas a ε K hapc ha0 hε0 haε1
  · intro p hp hpwindow hpupper
    have hp'lower : a < fkPrime p q := hpwindow.trans_le (min_le_right _ _)
    have hp'le : fkPrime p q ≤ p := fkPrime_le_of_one_le_q hp.1 hp.2 hq hq1.le
    refine ⟨(ha_lower.trans_lt (hp'lower.trans_le hp'le)).le, ?_⟩
    · by_contra hnot
      have hUp : U < p := lt_of_not_ge hnot
      have hm := strictMonoOn_fkPrime hq hUmem hp hUp
      change fkPrime U q < fkPrime p q at hm
      rw [hUFK] at hm
      dsimp [B] at hm
      linarith
  · exact href
  · intro p hpK
    exact hεη.trans (hη p hpK)

end

end FK.EssentialWindow

namespace FK.EssentialWindow

open CurvatureVariance.Infra.Percolation
open FK.Enhancement Classical
open scoped ENNReal NNReal unitInterval

noncomputable section

/-- The homogeneous `FKLimit` product law is definitionally the vendored
Bernoulli percolation law; this identifies the root percolation probability
without changing the `true`-open convention. -/
theorem percolationProb_eq_fkLimit {V : Type*} (G : SimpleGraph V) (o : V) (p : unitInterval) :
    percolationProb G o p =
      (FKLimit.bernoulliProduct (fun _ : G.edgeSet ↦ p) : Measure (G.edgeSet → Bool))
        {ω | {x | OpenConnected G ω Set.univ o x}.Infinite} := by
  rw [percolationProb_eq]
  rfl

/-- The actual percolation version of `upperWindow_of_AG_q_lt_one`. -/
theorem upperWindow_percolating_of_AG_q_lt_one {V : Type*} [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected)
    (pc : ℝ) (Eb Ee : Set G.edgeSet) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2),
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (decrementProfile Ee b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (G.edgeSet → Bool))
          (Percolating G) = 0) :
    UpperWindow (Percolating G) pc Eb Ee n m q hq :=
  upperWindow_of_AG_q_lt_one (Percolating G) pc Eb Ee n m q hq hq1 hpc0 hpc1
    (isUpperSet_percolating G) (measurableSet_percolating G hG) hAG

/-- The actual percolation version of `lowerWindow_of_AG_q_lt_one`. -/
theorem lowerWindow_percolating_of_AG_q_lt_one {V : Type*} [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected)
    (pc : ℝ) (Eb Ee : Set G.edgeSet) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < (1 - pc) / 2),
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (incrementProfile Eb a ε ha0 hε0.le haε1) :
          Measure (G.edgeSet → Bool)) (Percolating G) = 1) :
    LowerWindow (Percolating G) pc Eb Ee n m q hq :=
  lowerWindow_of_AG_q_lt_one (Percolating G) pc Eb Ee n m q hq hq1 hpc0 hpc1
    (isUpperSet_percolating G) (measurableSet_percolating G hG) hAG

/-- The actual percolation version of `upperWindow_of_AG_one_lt_q`. -/
theorem upperWindow_percolating_of_AG_one_lt_q {V : Type*} [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected)
    (pc : ℝ) (Eb Ee : Set G.edgeSet) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2),
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (decrementProfile Eb b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (G.edgeSet → Bool))
          (Percolating G) = 0) :
    UpperWindow (Percolating G) pc Eb Ee n m q hq :=
  upperWindow_of_AG_one_lt_q (Percolating G) pc Eb Ee n m q hq hq1 hpc0 hpc1
    (isUpperSet_percolating G) (measurableSet_percolating G hG) hAG

/-- The actual percolation version of `lowerWindow_of_AG_one_lt_q`. -/
theorem lowerWindow_percolating_of_AG_one_lt_q {V : Type*} [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected)
    (pc : ℝ) (Eb Ee : Set G.edgeSet) (n m : ℕ)
    (q : ℝ) (hq : 0 < q) (hq1 : 1 < q) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (hAG : ∀ (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < (1 - pc) / 2),
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (incrementProfile Ee a ε ha0 hε0.le haε1) :
          Measure (G.edgeSet → Bool)) (Percolating G) = 1) :
    LowerWindow (Percolating G) pc Eb Ee n m q hq :=
  lowerWindow_of_AG_one_lt_q (Percolating G) pc Eb Ee n m q hq hq1 hpc0 hpc1
    (isUpperSet_percolating G) (measurableSet_percolating G hG) hAG

end

end FK.EssentialWindow
