import Mathlib

/-!
# Fibres of finite configurations and conditional edge laws

This file isolates the exact finite calculation behind equation (2) of
Beffara--Faipeur--Oke.  No positivity of either individual configuration weight
is required: conditioning is only on a fibre of positive mass, including the
endpoint cases `p = 0` and `p = 1`.
-/

namespace FK.FiniteFiber

open scoped ENNReal BigOperators

abbrev Config (E : Type*) := E → Bool

variable {E : Type*}

/-- The two configurations extending a fixed off-edge restriction. -/
def withEdge [DecidableEq E] (e : E) (b : Bool) (ω : Config E) : Config E :=
  Function.update ω e b

/-- Configurations having the same restriction to `E \ {e}` as `ω`. -/
def offFiber [DecidableEq E] (e : E) (ω : Config E) : Set (Config E) :=
  {ξ | ∀ a, a ≠ e → ξ a = ω a}

lemma mem_offFiber_iff [DecidableEq E] {e : E} {ω ξ : Config E} :
    ξ ∈ offFiber e ω ↔ ∀ a, a ≠ e → ξ a = ω a := Iff.rfl

@[simp] lemma withEdge_edge [DecidableEq E] (e : E) (b : Bool) (ω : Config E) :
    withEdge e b ω e = b := by simp [withEdge]

@[simp] lemma withEdge_off [DecidableEq E] {e a : E} (ha : a ≠ e)
    (b : Bool) (ω : Config E) : withEdge e b ω a = ω a := by
  simp [withEdge, Function.update_of_ne ha]

lemma withEdge_mem_offFiber [DecidableEq E] (e : E) (b : Bool) (ω : Config E) :
    withEdge e b ω ∈ offFiber e ω := by
  intro a ha
  exact withEdge_off ha b ω

lemma eq_withEdge_of_mem_offFiber [DecidableEq E] {e : E} {ω ξ : Config E}
    (hξ : ξ ∈ offFiber e ω) : ξ = withEdge e (ξ e) ω := by
  funext a
  by_cases ha : a = e
  · subst a
    simp
  · exact (hξ a ha).trans (withEdge_off ha (ξ e) ω).symm

lemma mem_offFiber_iff_eq [DecidableEq E] {e : E} {ω ξ : Config E} :
    ξ ∈ offFiber e ω ↔ ξ = withEdge e true ω ∨ ξ = withEdge e false ω := by
  constructor
  · intro hξ
    rw [eq_withEdge_of_mem_offFiber hξ]
    cases ξ e <;> simp
  · rintro (rfl | rfl) <;> exact withEdge_mem_offFiber _ _ _

lemma withEdge_true_ne_false [DecidableEq E] (e : E) (ω : Config E) :
    withEdge e true ω ≠ withEdge e false ω := by
  intro h
  have := congrFun h e
  simp at this

/-- The total mass on an off-edge fibre is the sum of its two configuration
masses.  The sum is finite even when the ambient edge type is not finite. -/
lemma tsum_indicator_offFiber [DecidableEq E] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] (e : E) (ω : Config E) (f : Config E → M) :
    ∑' ξ, (offFiber e ω).indicator f ξ =
      f (withEdge e true ω) + f (withEdge e false ω) := by
  classical
  rw [tsum_eq_sum (s := {withEdge e true ω, withEdge e false ω})]
  · simpa [Set.indicator_of_mem, withEdge_mem_offFiber] using
      (Finset.sum_pair (f := fun ξ => (offFiber e ω).indicator f ξ)
        (withEdge_true_ne_false e ω))
  · intro ξ hξ
    apply Set.indicator_apply_eq_zero.mpr
    intro hmem
    exact (hξ (by simpa using (mem_offFiber_iff_eq.mp hmem))).elim

/-- After conditioning on the off-edge fibre, the open coordinate has exactly
the mass of the unique open extension. -/
lemma filter_map_coordinate_true [DecidableEq E]
    (μ : PMF (Config E)) (e : E) (ω : Config E)
    (h : ∃ ξ ∈ offFiber e ω, ξ ∈ μ.support) :
    (μ.filter (offFiber e ω) h).map (fun ξ => ξ e) true =
      (μ.filter (offFiber e ω) h) (withEdge e true ω) := by
  classical
  rw [PMF.map_apply]
  apply Eq.trans (b := @ite ℝ≥0∞ (true = withEdge e true ω e)
    (Classical.propDecidable _) ((μ.filter (offFiber e ω) h) (withEdge e true ω)) 0)
  · apply tsum_eq_single (f := fun ξ : Config E =>
      @ite ℝ≥0∞ (true = ξ e) (Classical.propDecidable _)
        ((μ.filter (offFiber e ω) h) ξ) 0) (withEdge e true ω)
    intro ξ hξ
    by_cases htrue : ξ e = true
    · simp only [htrue, ite_true]
      by_cases hmem : ξ ∈ offFiber e ω
      · have heq : ξ = withEdge e true ω := by
          rw [eq_withEdge_of_mem_offFiber hmem, htrue]
        exact (hξ heq).elim
      · exact PMF.filter_apply_eq_zero_of_notMem h hmem
    · simp [htrue]
  · simp

/-- Conditioning a finite configuration law on an off-edge fibre gives the
expected open-edge ratio.  This formulation allows zero open or closed mass;
only the conditioned fibre and the normalization are required to be nonzero.
It is the denominator-free analytic core of equation (2). -/
lemma filter_withEdge_true_toReal [DecidableEq E]
    (μ : PMF (Config E)) (e : E) (ω : Config E)
    (h : ∃ ξ ∈ offFiber e ω, ξ ∈ μ.support)
    (wo wc c : ℝ≥0∞)
    (hopen : μ (withEdge e true ω) = wo * c)
    (hclosed : μ (withEdge e false ω) = wc * c)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hwotop : wo ≠ ∞) (hwctop : wc ≠ ∞)
    (hsum : wo + wc ≠ 0) :
    ((μ.filter (offFiber e ω) h) (withEdge e true ω)).toReal =
      wo.toReal / (wo.toReal + wc.toReal) := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hctop⟩
  have hsumR : wo.toReal + wc.toReal ≠ 0 := by
    rw [← ENNReal.toReal_add hwotop hwctop]
    exact ENNReal.toReal_ne_zero.mpr ⟨hsum, ENNReal.add_ne_top.mpr ⟨hwotop, hwctop⟩⟩
  rw [PMF.filter_apply, Set.indicator_of_mem (withEdge_mem_offFiber e true ω),
    tsum_indicator_offFiber, hopen, hclosed, ← add_mul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_add hwotop hwctop]
  field_simp [hc, hsumR]

/-- The conditional probability of the open coordinate, rather than merely
the mass of one configuration in the conditioned law. -/
lemma filter_map_coordinate_true_toReal [DecidableEq E]
    (μ : PMF (Config E)) (e : E) (ω : Config E)
    (h : ∃ ξ ∈ offFiber e ω, ξ ∈ μ.support)
    (wo wc c : ℝ≥0∞)
    (hopen : μ (withEdge e true ω) = wo * c)
    (hclosed : μ (withEdge e false ω) = wc * c)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hwotop : wo ≠ ∞) (hwctop : wc ≠ ∞)
    (hsum : wo + wc ≠ 0) :
    ((μ.filter (offFiber e ω) h).map (fun ξ => ξ e) true).toReal =
      wo.toReal / (wo.toReal + wc.toReal) := by
  rw [filter_map_coordinate_true]
  exact filter_withEdge_true_toReal μ e ω h wo wc c hopen hclosed
    hc0 hctop hwotop hwctop hsum

end FK.FiniteFiber
