import FK.AGBoundedCoordinateBridge

/-!
# Monotone finite-family reference curves on sleeved graphs

The bounded-coordinate bridge compares the two endpoints of its differential
line. This module keeps the intermediate finite-trace inequalities and
transports them to actual independently activated arm and percolation
probabilities. The index type is finite throughout. No infinite indexed
product of activation families, disjointness assumption, `hAG` hypothesis, or
strict critical-point shift is used or asserted.

The speed is the established explicit constant
`independentComparisonSpeed a b R`. All coordinates remain in the unit
interval on the subtype `Icc 0 T`, so no endpoint-rate argument is hidden.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.AGImplant.Sleeve.BoundedCoordinate.ReferenceCurve

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.BoundedCoordinate

universe u v

/-- Unit-interval rates at an interior point of the admissible comparison
line. Feasibility on the closed interval gives bounds at every intermediate
time, not only at its endpoints. -/
noncomputable def unitLineOfBox {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (p s a b T : ℝ) (R : ℕ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (graph H).edgeSet ⊕ ι → unitInterval :=
  unitIndependentLine H S p s (independentComparisonSpeed a b R) t (fun x => by
    have hbox := independentLine_parameters_mem_box
      (independentComparisonSpeed_nonneg R ha.le hb.le) ht hp0 hs0 hpT hsT
    have hx := independentLine_mem_box H S hp0 hbox.1 hbox.2 x
    exact ⟨ha.le.trans hx.1, hx.2.trans hb.le⟩)

@[simp] lemma coe_unitLineOfBox {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (p s a b T : ℝ) (R : ℕ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (x : (graph H).edgeSet ⊕ ι) :
    (unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT ht x : ℝ) =
      independentLine H S p s (independentComparisonSpeed a b R) t x := rfl

/-- Actual finite-family enhanced-arm probability along the admissible line. -/
noncomputable def armCurve {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (R : ℕ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) (t : ↥(Icc (0 : ℝ) T)) : ℝ :=
  (infiniteProductLaw
    (unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT t.property)
    (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal

/-- **Monotonicity of every actual finite-family arm probability.** The proof
uses a finite coordinate trace separately at each radius; no derivative is
exchanged with an infinite limit. -/
theorem monotone_armCurve {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    Monotone (armCurve H S o n p s a b T R ha hb hp0 hs0 hpT hsT) := by
  classical
  intro t u htu
  let K := coordinates H hG S o n
  have hRK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K :=
    baseSupport_subset_coordinates H hG S o n
  have haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K :=
    activation_mem_coordinates H hG S o n
  have hdep : DependsOn (fun χ => χ ∈ deviceArmEvent (graph H)
      (independentSupport H S) o n) (K : Set ((graph H).edgeSet ⊕ ι)) :=
    dependsOn_deviceArmEvent H hG S o n
  have htTrace := eventWeight_traceEvent
    (unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT t.property) K
    (deviceArmEvent (graph H) (independentSupport H S) o n) hdep
  have huTrace := eventWeight_traceEvent
    (unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT u.property) K
    (deviceArmEvent (graph H) (independentSupport H S) o n) hdep
  change (infiniteProductLaw _ (deviceArmEvent (graph H)
    (independentSupport H S) o n)).toReal ≤
      (infiniteProductLaw _ (deviceArmEvent (graph H)
        (independentSupport H S) o n)).toReal
  calc
    _ = eventWeight (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) t.1 x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) := by
      simpa only [coe_unitLineOfBox] using htTrace.symm
    _ ≤ eventWeight (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) u.1 x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) :=
      monotoneOn_traceEventWeight_independentLine H S R hR hcard o n hRK haK
        p s a b T ha hb hp0 hs0 hpT hsT t.property u.property htu
    _ = _ := by
      simpa only [coe_unitLineOfBox] using huTrace

/-- Actual finite-family enhanced-percolation probability along the
admissible line. -/
noncomputable def percolationCurve {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (R : ℕ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) (t : ↥(Icc (0 : ℝ) T)) : ℝ :=
  (infiniteProductLaw
    (unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT t.property)
    (independentPercolationEvent H S o)).toReal

/-- **Monotonicity of actual finite-family enhanced percolation.** The two
one-sided limits are limits of arm probabilities. Every approximant is ordered
by `monotone_armCurve`; convergence is continuity from above, not an
interchange of differentiation and infinite-volume limits. -/
theorem monotone_percolationCurve {V : Type v} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    Monotone (percolationCurve H S o p s a b T R ha hb hp0 hs0 hpT hsT) := by
  classical
  intro t u htu
  let rt := unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT t.property
  let ru := unitLineOfBox H S p s a b T R ha hb hp0 hs0 hpT hsT u.property
  change (infiniteProductLaw rt (independentPercolationEvent H S o)).toReal ≤
    (infiniteProductLaw ru (independentPercolationEvent H S o)).toReal
  apply le_of_tendsto_of_tendsto
    (tendsto_infiniteProductLaw_deviceArmEvent_independent H hG S o rt)
    (tendsto_infiniteProductLaw_deviceArmEvent_independent H hG S o ru)
  exact Filter.Eventually.of_forall fun n =>
    monotone_armCurve H hG S R hR hcard o n p s a b T ha hb hp0 hs0 hpT hsT htu

/-- A zero percolation probability propagates backwards along the proved
comparison curve. This is a zero/nonzero phase statement, not a strict shift. -/
theorem percolationCurve_eq_zero_of_le {V : Type v} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) {t u : ↥(Icc (0 : ℝ) T)}
    (htu : t ≤ u)
    (hu : percolationCurve H S o p s a b T R ha hb hp0 hs0 hpT hsT u = 0) :
    percolationCurve H S o p s a b T R ha hb hp0 hs0 hpT hsT t = 0 := by
  apply le_antisymm
  · exact (monotone_percolationCurve H hG S R hR hcard o p s a b T
      ha hb hp0 hs0 hpT hsT htu).trans_eq hu
  · exact ENNReal.toReal_nonneg

/-- Positive percolation propagates forwards with the explicit normalized
trade-off `p ↦ p - independentComparisonSpeed a b R * t` on moved annuli and
`s ↦ s + t` on all selected activations. -/
theorem percolationCurve_pos_of_pos_of_le {V : Type v} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) {t u : ↥(Icc (0 : ℝ) T)}
    (htu : t ≤ u)
    (ht : 0 < percolationCurve H S o p s a b T R ha hb hp0 hs0 hpT hsT t) :
    0 < percolationCurve H S o p s a b T R ha hb hp0 hs0 hpT hsT u :=
  ht.trans_le (monotone_percolationCurve H hG S R hR hcard o p s a b T
    ha hb hp0 hs0 hpT hsT htu)

/-- The largest time allowed jointly by the lower moved-bond constraint and
the upper activation constraint. The denominator is the explicit normalized
differential speed, so this time is independent of the finite index type. -/
noncomputable def maximalTime (p s a b : ℝ) (R : ℕ) : ℝ :=
  min ((p - a) / independentComparisonSpeed a b R) (b - s)

lemma maximalTime_nonneg {p s a b : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b) :
    0 ≤ maximalTime p s a b R := by
  have hc : 0 < independentComparisonSpeed a b R :=
    independentComparisonSpeed_pos hR ha hb
  exact le_min (div_nonneg (sub_nonneg.mpr hp0.1) hc.le)
    (sub_nonneg.mpr hs0.2)

lemma maximalTime_pos {p s a b : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1)
    (hp : a < p) (hs : s < b) :
    0 < maximalTime p s a b R := by
  have hc : 0 < independentComparisonSpeed a b R :=
    independentComparisonSpeed_pos hR ha hb
  exact lt_min (div_pos (sub_pos.mpr hp) hc) (sub_pos.mpr hs)

/-- Every time satisfying both endpoint constraints is bounded by the
constructed maximal time. -/
lemma le_maximalTime {p s a b T : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    T ≤ maximalTime p s a b R := by
  have hc : 0 < independentComparisonSpeed a b R :=
    independentComparisonSpeed_pos hR ha hb
  apply le_min
  · apply (le_div_iff₀ hc).2
    calc
      T * independentComparisonSpeed a b R =
          independentComparisonSpeed a b R * T := mul_comm _ _
      _ ≤ p - a := by linarith [hpT.1]
  · linarith [hsT.2]

lemma mul_maximalTime_le {p s a b : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1) :
    independentComparisonSpeed a b R * maximalTime p s a b R ≤ p - a := by
  let c := independentComparisonSpeed a b R
  have hc : 0 < c := independentComparisonSpeed_pos hR ha hb
  have h := mul_le_mul_of_nonneg_left
    (show maximalTime p s a b R ≤ (p - a) / c from min_le_left _ _) hc.le
  have hz : c ≠ 0 := ne_of_gt hc
  calc
    c * maximalTime p s a b R ≤ c * ((p - a) / c) := h
    _ = p - a := by field_simp

lemma maximalTime_le_sub {p s a b : ℝ} (R : ℕ) :
    maximalTime p s a b R ≤ b - s := min_le_right _ _

/-- The constructed maximal time satisfies the moved-bond endpoint box. -/
lemma moved_mem_box_maximalTime {p s a b : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b) :
    p - independentComparisonSpeed a b R * maximalTime p s a b R ∈ Icc a b := by
  have hc : 0 ≤ independentComparisonSpeed a b R :=
    (independentComparisonSpeed_pos hR ha hb).le
  have hT : 0 ≤ maximalTime p s a b R :=
    maximalTime_nonneg hR ha hb hp0 hs0
  have hmul := mul_maximalTime_le (p := p) (s := s) hR ha hb
  exact ⟨by linarith, by
    have hnonneg : 0 ≤ independentComparisonSpeed a b R * maximalTime p s a b R :=
      mul_nonneg hc hT
    linarith [hp0.2]⟩

/-- The constructed maximal time satisfies the activation endpoint box. -/
lemma activation_mem_box_maximalTime {p s a b : ℝ} {R : ℕ}
    (hR : 0 < R) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b) :
    s + maximalTime p s a b R ∈ Icc a b := by
  have hT : 0 ≤ maximalTime p s a b R :=
    maximalTime_nonneg hR ha hb hp0 hs0
  have hle := maximalTime_le_sub (p := p) (s := s) (a := a) (b := b) R
  exact ⟨by linarith [hs0.1], by linarith⟩

/-- Canonical version of the monotone finite-family percolation comparison.
Only the initial box and common positive annulus cardinality are supplied;
the largest admissible elapsed time and both endpoint checks are constructed. -/
theorem monotone_percolationCurve_maximalTime {V : Type v} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet)
    (p s a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b) :
    Monotone (percolationCurve H S o p s a b (maximalTime p s a b R) R
      ha hb hp0 hs0
      (moved_mem_box_maximalTime hR ha hb hp0 hs0)
      (activation_mem_box_maximalTime hR ha hb hp0 hs0)) := by
  exact monotone_percolationCurve H hG S R hR hcard o p s a b
    (maximalTime p s a b R) ha hb hp0 hs0
    (moved_mem_box_maximalTime hR ha hb hp0 hs0)
    (activation_mem_box_maximalTime hR ha hb hp0 hs0)

end FK.AGImplant.Sleeve.BoundedCoordinate.ReferenceCurve
