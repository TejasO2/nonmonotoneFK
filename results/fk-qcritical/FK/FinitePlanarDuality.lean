import FK.ConfigurationDuality
import FK.PlanarParameters

/-!
# Finite plane FK weights and the Euler relation

This file proves the algebraic part of finite planar FK duality.  Vertex and
edge types are finite, `K` and `KDual` are the actual component counts in an
intended application, and Euler's formula is the explicit hypothesis
```
KDual (dualConfig e ω) + card V = K ω + 1 + openCard ω.
```
No graph embedding or connectivity definition is hidden in `K`: the geometric
obligation is stated separately from the normalized probability calculation.
-/

namespace FK.FinitePlane

open scoped ENNReal BigOperators
open FK.Configuration

/-- The product `p^|ω| (1-p)^|E\ω|`, written without truncating subtraction of
natural cardinals until the final exponent. -/
def edgeWeight {E : Type*} [Fintype E] (p closed : NNReal) (ω : E → Bool) : NNReal :=
  ∏ e, if ω e then p else closed

/-- Number of open edges in a finite configuration. -/
def openCard {E : Type*} [Fintype E] (ω : E → Bool) : ℕ :=
  (Finset.univ.filter fun e => ω e).card

/-- Unnormalised finite FK weight; `K` includes all connected components,
including isolated vertices, as required by Euler's formula. -/
def fkWeight {E : Type*} [Fintype E] (q p : NNReal) (K : (E → Bool) → ℕ)
    (ω : E → Bool) : NNReal :=
  edgeWeight p (1 - p) ω * q ^ K ω

/-- The real planar-dual parameter viewed as a nonnegative real. -/
noncomputable def dualParameter (q p : NNReal) : NNReal :=
  Real.toNNReal (FK.dual (q : ℝ) (p : ℝ))

lemma coe_dualParameter {q p : NNReal} (hq : 0 < q) (hp₁ : p ≤ 1) :
    (dualParameter q p : ℝ) = FK.dual (q : ℝ) (p : ℝ) := by
  apply Real.coe_toNNReal
  exact FK.dual_nonneg (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁)

lemma dualParameter_pos {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p)
    (hp₁ : p < 1) : 0 < dualParameter q p := by
  rw [← NNReal.coe_pos, coe_dualParameter hq hp₁.le]
  exact FK.dual_pos (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁)

lemma dualParameter_le_one {q p : NNReal} (hq : 0 < q) (hp₁ : p ≤ 1) :
    dualParameter q p ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_dualParameter hq hp₁]
  exact FK.dual_le_one (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁)

lemma dualParameter_lt_one {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p)
    (hp₁ : p ≤ 1) : dualParameter q p < 1 := by
  rw [← NNReal.coe_lt_coe, coe_dualParameter hq hp₁]
  exact FK.dual_lt_one (by exact_mod_cast hq) (by exact_mod_cast hp₀)
    (by exact_mod_cast hp₁)

lemma dualParameter_odds_cross {q p : NNReal} (hq : 0 < q) (hp₁ : p ≤ 1) :
    q * (1 - p) * (1 - dualParameter q p) = p * dualParameter q p := by
  have hdual := coe_dualParameter hq hp₁
  have hdual_le := dualParameter_le_one hq hp₁
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_sub hp₁,
    NNReal.coe_sub hdual_le, hdual]
  exact FK.dual_odds_cross (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁)

lemma openCard_le_card {E : Type*} [Fintype E] (ω : E → Bool) :
    openCard ω ≤ Fintype.card E := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma edgeWeight_eq_pow {E : Type*} [Fintype E] (p closed : NNReal)
    (ω : E → Bool) :
    edgeWeight p closed ω =
      p ^ openCard ω * closed ^ (Fintype.card E - openCard ω) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset E)) (fun e => ω e)
  have hclosed : (Finset.univ.filter fun e => ¬ω e).card =
      Fintype.card E - openCard ω := by
    rw [Finset.card_univ] at hc
    dsimp [openCard]
    omega
  simp only [edgeWeight, Finset.prod_ite, Finset.prod_const]
  change p ^ openCard ω * closed ^ (Finset.univ.filter fun e => ¬ω e).card = _
  rw [hclosed]

/-- Complementation and reindexing exchange the open and closed edge weights. -/
lemma edgeWeight_dual {E E' : Type*} [Fintype E] [Fintype E']
    (e : E ≃ E') (p closed : NNReal) (ω : E → Bool) :
    edgeWeight p closed (dualConfig e ω) = edgeWeight closed p ω := by
  classical
  unfold edgeWeight
  rw [← Equiv.prod_comp e]
  apply Finset.prod_congr rfl
  intro x _
  cases hx : ω x <;> simp [dualConfig, hx]

/-- The cross-multiplied dual-odds relation raised to the number of open edges,
together with Euler's formula, gives the exact weight identity after clearing
normalising denominators. -/
lemma dual_weight_algebra {q p ps : NNReal}
    (hcross : q * (1 - p) * (1 - ps) = p * ps)
    {o m kd kv k : ℕ} (hom : o ≤ m) (heuler : kd + kv = k + 1 + o) :
    ((1 - ps) ^ o * ps ^ (m - o) * q ^ kd) *
        ((1 - p) ^ m * q ^ kv) =
      ps ^ m * q * (p ^ o * (1 - p) ^ (m - o) * q ^ k) := by
  have hY : (1 - p) ^ m = (1 - p) ^ (m - o) * (1 - p) ^ o := by
    rw [← pow_add, Nat.sub_add_cancel hom]
  have hX : ps ^ m = ps ^ (m - o) * ps ^ o := by
    rw [← pow_add, Nat.sub_add_cancel hom]
  have hq : q ^ kd * q ^ kv = q ^ k * q * q ^ o := by
    rw [← pow_add, heuler]
    simp only [pow_add, pow_one]
  have hcrosspow : q ^ o * (1 - p) ^ o * (1 - ps) ^ o = p ^ o * ps ^ o := by
    calc
      q ^ o * (1 - p) ^ o * (1 - ps) ^ o =
          (q * (1 - p) * (1 - ps)) ^ o := by simp [mul_pow]
      _ = (p * ps) ^ o := congrArg (· ^ o) hcross
      _ = p ^ o * ps ^ o := by rw [mul_pow]
  calc
    ((1 - ps) ^ o * ps ^ (m - o) * q ^ kd) * ((1 - p) ^ m * q ^ kv) =
        ps ^ (m - o) * (1 - p) ^ (m - o) * (1 - p) ^ o * (1 - ps) ^ o *
          (q ^ kd * q ^ kv) := by rw [hY]; ring
    _ = ps ^ (m - o) * (1 - p) ^ (m - o) * q ^ k * q *
          (q ^ o * (1 - p) ^ o * (1 - ps) ^ o) := by rw [hq]; ring
    _ = ps ^ (m - o) * (1 - p) ^ (m - o) * q ^ k * q * (p ^ o * ps ^ o) := by
      rw [hcrosspow]
    _ = ps ^ m * q * (p ^ o * (1 - p) ^ (m - o) * q ^ k) := by
      rw [hX]; ring

/-- Under Euler's component-count relation and the dual-odds relation, all dual
weights are one positive constant times the corresponding primal weights. -/
theorem dual_fkWeight_proportional {V E E' : Type*} [Fintype V] [Fintype E]
    [Fintype E'] (e : E ≃ E') (q p ps : NNReal) (K : (E → Bool) → ℕ)
    (KDual : (E' → Bool) → ℕ) (hp1 : p < 1) (hq : 0 < q)
    (hcross : q * (1 - p) * (1 - ps) = p * ps)
    (heuler : ∀ ω, KDual (dualConfig e ω) + Fintype.card V =
      K ω + 1 + openCard ω) (ω : E → Bool) :
    fkWeight q ps KDual (dualConfig e ω) =
      (ps ^ Fintype.card E * q /
        ((1 - p) ^ Fintype.card E * q ^ Fintype.card V)) * fkWeight q p K ω := by
  have hden : (1 - p) ^ Fintype.card E * q ^ Fintype.card V ≠ 0 := by
    have hclosed : 0 < 1 - p := tsub_pos_of_lt hp1
    exact mul_ne_zero (pow_ne_zero _ hclosed.ne') (pow_ne_zero _ hq.ne')
  have halg := dual_weight_algebra (q := q) (p := p) (ps := ps) hcross
    (openCard_le_card ω) (heuler ω)
  rw [fkWeight, fkWeight, edgeWeight_dual, edgeWeight_eq_pow, edgeWeight_eq_pow]
  calc
    (1 - ps) ^ openCard ω * ps ^ (Fintype.card E - openCard ω) *
        q ^ KDual (dualConfig e ω) =
        (ps ^ Fintype.card E * q *
          (p ^ openCard ω * (1 - p) ^ (Fintype.card E - openCard ω) * q ^ K ω)) /
          ((1 - p) ^ Fintype.card E * q ^ Fintype.card V) :=
      (eq_div_iff hden).2 halg
    _ = (ps ^ Fintype.card E * q /
        ((1 - p) ^ Fintype.card E * q ^ Fintype.card V)) *
        (p ^ openCard ω * (1 - p) ^ (Fintype.card E - openCard ω) * q ^ K ω) :=
      (div_mul_eq_mul_div _ _ _).symm

lemma tsum_coe_ne_zero_of_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → NNReal) (hw : ∀ a, 0 < w a) :
    (∑' a, (w a : ℝ≥0∞)) ≠ 0 := by
  rw [tsum_fintype]
  have hpos : 0 < ∑ a, w a :=
    Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty
  exact_mod_cast hpos.ne'

lemma tsum_coe_ne_top {Ω : Type*} [Fintype Ω] (w : Ω → NNReal) :
    (∑' a, (w a : ℝ≥0∞)) ≠ ∞ := by
  simp [tsum_fintype]

/-- Normalised probability mass function attached to finite positive weights. -/
noncomputable def normalizedPMF {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → NNReal) (hw : ∀ a, 0 < w a) : PMF Ω :=
  PMF.normalize (fun a => (w a : ℝ≥0∞))
    (tsum_coe_ne_zero_of_pos w hw) (tsum_coe_ne_top w)

@[simp] lemma normalizedPMF_apply {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → NNReal) (hw : ∀ a, 0 < w a) (a : Ω) :
    normalizedPMF w hw a = (w a : ℝ≥0∞) * (∑' b, (w b : ℝ≥0∞))⁻¹ := rfl

lemma pmf_map_equiv_apply {α β : Type*} [Fintype α] [Fintype β]
    (d : α ≃ β) (P : PMF α) (b : β) : P.map d b = P (d.symm b) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  have heq : ∀ a, (b = d a) ↔ a = d.symm b := by
    intro a
    constructor
    · intro hba
      exact (d.eq_symm_apply).2 hba.symm
    · intro ha
      exact ((d.eq_symm_apply).1 ha).symm
  simp_rw [heq]
  simp

/-- Normalisation cancels the common constant in Euler-dual FK weights. -/
theorem normalizedPMF_map_eq_of_proportional {α β : Type*} [Fintype α]
    [Fintype β] [Nonempty α] [Nonempty β] (d : α ≃ β)
    (w : α → NNReal) (wDual : β → NNReal) (c : NNReal) (hc : 0 < c)
    (hw : ∀ a, 0 < w a) (hwDual : ∀ b, 0 < wDual b)
    (hprop : ∀ a, wDual (d a) = c * w a) :
    PMF.map d (normalizedPMF w hw) = normalizedPMF wDual hwDual := by
  classical
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc.ne'
  have hctop : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hsum : (∑' b, (wDual b : ℝ≥0∞)) = (c : ℝ≥0∞) * ∑' a, (w a : ℝ≥0∞) := by
    calc
      (∑' b, (wDual b : ℝ≥0∞)) = ∑' a, (wDual (d a) : ℝ≥0∞) :=
        (d.tsum_eq (fun b => (wDual b : ℝ≥0∞))).symm
      _ = ∑' a, (c : ℝ≥0∞) * (w a : ℝ≥0∞) := by
        congr 1
        funext a
        exact_mod_cast hprop a
      _ = (c : ℝ≥0∞) * ∑' a, (w a : ℝ≥0∞) := ENNReal.tsum_mul_left
  ext b
  have hb : wDual b = c * w (d.symm b) := by
    simpa using hprop (d.symm b)
  rw [pmf_map_equiv_apply, normalizedPMF_apply, normalizedPMF_apply, hsum, hb]
  simp only [ENNReal.coe_mul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
  symm
  calc
    ((c : ℝ≥0∞) * (w (d.symm b) : ℝ≥0∞)) *
        ((c : ℝ≥0∞)⁻¹ * (∑' a, (w a : ℝ≥0∞))⁻¹) =
        ((c : ℝ≥0∞) * (c : ℝ≥0∞)⁻¹) *
          ((w (d.symm b) : ℝ≥0∞) * (∑' a, (w a : ℝ≥0∞))⁻¹) := by ac_rfl
    _ = (w (d.symm b) : ℝ≥0∞) * (∑' a, (w a : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.mul_inv_cancel hc0 hctop, one_mul]

lemma fkWeight_pos {E : Type*} [Fintype E] {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (K : (E → Bool) → ℕ) (ω : E → Bool) :
    0 < fkWeight q p K ω := by
  unfold fkWeight edgeWeight
  apply mul_pos
  · apply Finset.prod_pos
    intro e _
    split_ifs
    · exact hp₀
    · exact tsub_pos_of_lt hp₁
  · exact pow_pos hq _

/-- Finite no-boundary FK duality, reduced exactly to Euler's component-count
relation.  The parameters are the actual `p` and `p* = 1-p'`, with
`0 < p < 1` and `q > 0`. -/
theorem finite_planar_fk_duality {V E E' : Type*} [Fintype V] [Fintype E]
    [Fintype E'] [DecidableEq E] [DecidableEq E'] (e : E ≃ E') (q p : NNReal) (K : (E → Bool) → ℕ)
    (KDual : (E' → Bool) → ℕ) (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ω, KDual (dualConfig e ω) + Fintype.card V =
      K ω + 1 + openCard ω) :
    PMF.map (dualEquiv e)
      (normalizedPMF (fkWeight q p K) (fun ω => fkWeight_pos hq hp₀ hp₁ K ω)) =
      normalizedPMF (fkWeight q (dualParameter q p) KDual)
        (fun η => fkWeight_pos hq (dualParameter_pos hq hp₀ hp₁)
          (dualParameter_lt_one hq hp₀ hp₁.le) KDual η) := by
  let c : NNReal := (dualParameter q p) ^ Fintype.card E * q /
    ((1 - p) ^ Fintype.card E * q ^ Fintype.card V)
  have hc : 0 < c := by
    apply div_pos
    · exact mul_pos (pow_pos (dualParameter_pos hq hp₀ hp₁) _) hq
    · exact mul_pos (pow_pos (tsub_pos_of_lt hp₁) _) (pow_pos hq _)
  have hprop : ∀ ω, fkWeight q (dualParameter q p) KDual (dualEquiv e ω) =
      c * fkWeight q p K ω := by
    intro ω
    exact dual_fkWeight_proportional e q p (dualParameter q p) K KDual hp₁ hq
      (dualParameter_odds_cross hq hp₁.le) heuler ω
  exact normalizedPMF_map_eq_of_proportional (dualEquiv e) _ _ c hc _ _ hprop

end FK.FinitePlane
