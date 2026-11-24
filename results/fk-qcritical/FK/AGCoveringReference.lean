import FK.InfinitePackedSleeves

/-!
# Covering essential-enhancement reference shift

`FK.InfinitePackedSleeves` compares the two endpoints of the global trade-off
line of the sleeved essential-enhancement construction: every selected base
bond moves down at speed `c` and every device activation moves up at speed `1`.
This module

* identifies the exact hypothesis under which the *uniform* reference shift is
  a consequence of that line: every base bond must be selected by some device.
  Under that covering hypothesis the endpoint rate profile is an explicit
  three-rate profile (original bonds, remaining sleeve edges, activations), and
  the statement becomes a quantitative trade: lowering every original bond by
  `c * T` and raising every activation by `T` does not decrease percolation;
* upgrades the endpoint comparison to a monotone comparison at every pair of
  admissible times, for an *arbitrary* device index type (no finiteness, no
  countability, no cardinality bound), with an index-independent maximal time;
* derives the quantitative strict decrement of the critical original-bond rate.

The final section (`...CoveringReference.Ext`) supplies the *spoke pivot
transport*: the exact analogue, for the bypass spokes, of the accepted
original-bond activation-pivot transport.  It is what an extension of the line
to the whole template needs, and it is independent of covering and of the box.

What is *not* proved here is stated precisely in `RESULTS.md`: without the
covering hypothesis the trade-off only lowers the selected bonds, so no
homogeneous-rate conclusion follows from it, and the paper's positive-density
hypothesis needs a separate density-to-uniform step.  Extending the moved set to
the bypass spokes is deliberate non-claim.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

universe u v

variable {V : Type u}

/-! ## Box arithmetic -/

/-- A rate in the admissible box is a unit-interval rate. -/
lemma mem_unit_of_box {a b x : ℝ} (ha : 0 < a) (hb : b < 1) (hx : x ∈ Set.Icc a b) :
    x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ha.le.trans hx.1, hx.2.trans hb.le⟩

/-- Every coordinate of the global trade-off line is a unit-interval rate. -/
lemma globalLine_mem_unit {H : SimpleGraph V} {ι : Type v} {S : ι → Finset H.edgeSet}
    {p s c a b t : ℝ} (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Set.Icc a b)
    (hmt : p - c * t ∈ Set.Icc a b) (hst : s + t ∈ Set.Icc a b) :
    ∀ x, globalLine H S p s c t x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  cases x with
  | inl f =>
      by_cases h : ∃ i, f ∈ annulus H (S i)
      · simp only [globalLine, Sum.elim_inl, h, if_true]
        exact mem_unit_of_box ha hb hmt
      · simp only [globalLine, Sum.elim_inl, h, if_false]
        exact mem_unit_of_box ha hb hp
  | inr i =>
      simp only [globalLine, Sum.elim_inr]
      exact mem_unit_of_box ha hb hst

/-! ## The covering hypothesis and the explicit endpoint profiles -/

/-- Every original bond is selected by some device of the family. -/
def CoveringBase {H : SimpleGraph V} {ι : Type v} (S : ι → Finset H.edgeSet) : Prop :=
  ∀ e : H.edgeSet, ∃ i, e ∈ S i

/-- Real-valued profile with a common rate on all coordinates of the sleeve
graph. -/
noncomputable def uniformReal {ι : Type v} (H : SimpleGraph V) (p s : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun _ => p) (fun _ => s)

/-- Real-valued three-rate profile: `bb` on the original (annular) bonds, `gg`
on the remaining sleeve edges (the bypass spokes), `ss` on the activations. -/
noncomputable def threeReal {ι : Type v} (H : SimpleGraph V) (bb gg ss : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun f => if ∃ e : H.edgeSet, baseEdge H e = f then bb else gg)
    (fun _ => ss)

@[simp] lemma uniformReal_inl {ι : Type v} (H : SimpleGraph V) (p s : ℝ)
    (f : (graph H).edgeSet) : uniformReal (ι := ι) H p s (Sum.inl f) = p := rfl

@[simp] lemma uniformReal_inr {ι : Type v} (H : SimpleGraph V) (p s : ℝ) (i : ι) :
    uniformReal (ι := ι) H p s (Sum.inr i) = s := rfl

@[simp] lemma threeReal_inr {ι : Type v} (H : SimpleGraph V) (bb gg ss : ℝ) (i : ι) :
    threeReal (ι := ι) H bb gg ss (Sum.inr i) = ss := rfl

/-- The global trade-off line starts at the uniform profile. -/
lemma globalLine_zero_eq_uniformReal {H : SimpleGraph V} {ι : Type v}
    (S : ι → Finset H.edgeSet) (p s c : ℝ) :
    globalLine H S p s c 0 = uniformReal (ι := ι) H p s := by
  funext x
  cases x with
  | inl f =>
      by_cases h : ∃ i, f ∈ annulus H (S i)
      · simp only [globalLine, Sum.elim_inl, h, if_true, uniformReal_inl]
        ring
      · simp only [globalLine, Sum.elim_inl, h, if_false, uniformReal_inl]
  | inr i =>
      simp only [globalLine, Sum.elim_inr, uniformReal_inr]
      ring

/-- **Covering makes the endpoint of the trade-off line a three-rate profile.**
This is exactly where the covering hypothesis is used: the selected bonds then
are all original bonds. -/
lemma globalLine_eq_threeReal_of_covering {H : SimpleGraph V} {ι : Type v}
    (S : ι → Finset H.edgeSet) (hcov : CoveringBase S) (p s c T : ℝ) :
    globalLine H S p s c T = threeReal (ι := ι) H (p - c * T) p (s + T) := by
  funext x
  cases x with
  | inr i => simp only [globalLine, threeReal, Sum.elim_inr]
  | inl f =>
      by_cases hf : ∃ e : H.edgeSet, baseEdge H e = f
      · obtain ⟨e, rfl⟩ := hf
        have hex : ∃ i, baseEdge H e ∈ annulus H (S i) := by
          obtain ⟨i, hi⟩ := hcov e
          exact ⟨i, baseEdge_mem_annulus H (S i) hi⟩
        simp only [globalLine, threeReal, Sum.elim_inl, hex, if_true,
          (show ∃ e' : H.edgeSet, baseEdge H e' = baseEdge H e from ⟨e, rfl⟩), if_true]
      · have hno : ¬ ∃ i, f ∈ annulus H (S i) := by
          rintro ⟨i, hi⟩
          obtain ⟨e, _he, hge⟩ := Finset.mem_image.mp hi
          exact hf ⟨e, hge⟩
        simp only [globalLine, threeReal, Sum.elim_inl, hno, hf, if_false]

/-! ## Unit-interval packaging -/

/-- Uniform unit-interval rate profile. -/
noncomputable def uniformPoint {ι : Type v} (H : SimpleGraph V) (p s : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (graph H).edgeSet ⊕ ι → unitInterval :=
  Sum.elim (fun _ => ⟨p, hp⟩) (fun _ => ⟨s, hs⟩)

/-- Three-rate unit-interval rate profile. -/
noncomputable def threePoint {ι : Type v} (H : SimpleGraph V) (bb gg ss : ℝ)
    (hbb : bb ∈ Set.Icc (0 : ℝ) 1) (hgg : gg ∈ Set.Icc (0 : ℝ) 1)
    (hss : ss ∈ Set.Icc (0 : ℝ) 1) :
    (graph H).edgeSet ⊕ ι → unitInterval :=
  Sum.elim (fun f => if ∃ e : H.edgeSet, baseEdge H e = f then ⟨bb, hbb⟩ else ⟨gg, hgg⟩)
    (fun _ => ⟨ss, hss⟩)

@[simp] lemma coe_uniformPoint {ι : Type v} (H : SimpleGraph V) (p s : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (x : (graph H).edgeSet ⊕ ι) :
    ((uniformPoint H p s hp hs x : unitInterval) : ℝ) = uniformReal (ι := ι) H p s x := by
  cases x with
  | inl f => rfl
  | inr i => rfl

@[simp] lemma coe_threePoint {ι : Type v} (H : SimpleGraph V) (bb gg ss : ℝ)
    (hbb : bb ∈ Set.Icc (0 : ℝ) 1) (hgg : gg ∈ Set.Icc (0 : ℝ) 1)
    (hss : ss ∈ Set.Icc (0 : ℝ) 1) (x : (graph H).edgeSet ⊕ ι) :
    ((threePoint H bb gg ss hbb hgg hss x : unitInterval) : ℝ) =
      threeReal (ι := ι) H bb gg ss x := by
  cases x with
  | inl f =>
      by_cases h : ∃ e : H.edgeSet, baseEdge H e = f
      · simp only [threePoint, threeReal, Sum.elim_inl, h, if_true]
      · simp only [threePoint, threeReal, Sum.elim_inl, h, if_false]
  | inr i => rfl

lemma unitGlobalLine_zero_eq_uniformPoint {H : SimpleGraph V} {ι : Type v}
    {S : ι → Finset H.edgeSet} {p s c : ℝ}
    {hr : ∀ x, globalLine H S p s c 0 x ∈ Set.Icc (0 : ℝ) 1}
    {hp : p ∈ Set.Icc (0 : ℝ) 1} {hs : s ∈ Set.Icc (0 : ℝ) 1} :
    unitGlobalLine H S p s c 0 hr = uniformPoint (ι := ι) H p s hp hs := by
  funext x
  refine Subtype.ext ?_
  rw [coe_unitGlobalLine, coe_uniformPoint, globalLine_zero_eq_uniformReal]

lemma unitGlobalLine_eq_threePoint_of_covering {H : SimpleGraph V} {ι : Type v}
    {S : ι → Finset H.edgeSet} (hcov : CoveringBase S) {p s c T : ℝ}
    {hr : ∀ x, globalLine H S p s c T x ∈ Set.Icc (0 : ℝ) 1}
    {hbb : p - c * T ∈ Set.Icc (0 : ℝ) 1} {hgg : p ∈ Set.Icc (0 : ℝ) 1}
    {hss : s + T ∈ Set.Icc (0 : ℝ) 1} :
    unitGlobalLine H S p s c T hr =
      threePoint (ι := ι) H (p - c * T) p (s + T) hbb hgg hss := by
  funext x
  refine Subtype.ext ?_
  rw [coe_unitGlobalLine, coe_threePoint, globalLine_eq_threeReal_of_covering S hcov]

/-! ## The covering reference comparison -/

/-- **Covering essential-enhancement reference comparison.**

Let `H` be a connected locally finite graph with countable vertex type, and let
`S` be an edge-unique family of equally sized device annuli covering every
original bond.  Then moving every original bond down at speed
`c = independentComparisonSpeed a b R` and every activation up at speed `1`
cannot decrease the percolation probability: the model with original-bond rate
`p` and activation rate `s` is dominated, in the percolation event, by the
model with original-bond rate `p - c * T`, remaining sleeve-edge rate `p` and
activation rate `s + T`.

The device index type is arbitrary: it is neither finite nor countable, and no
bound on its cardinality enters. -/
theorem covering_reference_comparison {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (hcov : CoveringBase S) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b) :
    (infiniteProductLaw
        (uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
          (mem_unit_of_box ha hb hs0))
        (globalPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw
        (threePoint (ι := ι) H (p - independentComparisonSpeed a b R * T) p (s + T)
          (mem_unit_of_box ha hb hpT) (mem_unit_of_box ha hb hp0)
          (mem_unit_of_box ha hb hsT))
        (globalPercolationEvent H S o)).toReal := by
  have hr0 : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Set.Icc (0 : ℝ) 1 := by
    refine globalLine_mem_unit (S := S) (c := independentComparisonSpeed a b R)
      (t := 0) ha hb hp0 ?_ ?_
    · simpa using hp0
    · simpa using hs0
  have hrT : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) T x ∈
      Set.Icc (0 : ℝ) 1 :=
    globalLine_mem_unit (S := S) (c := independentComparisonSpeed a b R) (t := T)
      ha hb hp0 hpT hsT
  have hmain := infiniteProductLaw_globalPercolation_globalLine_le H hG S hunique
    R hR hcard o p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT
  have h0 : unitGlobalLine H S p s (independentComparisonSpeed a b R) 0 hr0 =
      uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hs0) :=
    unitGlobalLine_zero_eq_uniformPoint (S := S)
      (c := independentComparisonSpeed a b R) (hr := hr0)
      (hp := mem_unit_of_box ha hb hp0) (hs := mem_unit_of_box ha hb hs0)
  have hT' : unitGlobalLine H S p s (independentComparisonSpeed a b R) T hrT =
      threePoint (ι := ι) H (p - independentComparisonSpeed a b R * T) p (s + T)
        (mem_unit_of_box ha hb hpT) (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hsT) :=
    unitGlobalLine_eq_threePoint_of_covering (S := S) hcov
      (c := independentComparisonSpeed a b R) (T := T) (hr := hrT)
      (hbb := mem_unit_of_box ha hb hpT) (hgg := mem_unit_of_box ha hb hp0)
      (hss := mem_unit_of_box ha hb hsT)
  rw [h0, hT'] at hmain
  exact hmain

end FK.AGImplant.Sleeve.CoveringReference

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.AGImplant.Sleeve.CoveringReference
open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

/-! ## The comparison at every pair of admissible times

`FK.InfinitePackedSleeves` proves the endpoint comparison only.  The finite-index
module `FK.AGFiniteReferenceCurve` proves the full criterion curve but requires a
`Fintype` device index.  The next two statements give the full monotone curve for
an arbitrary device index: every finite arm is monotone on the whole admissible
time interval, and the percolation probabilities follow by continuity from above.
-/

/-- **Arm monotonicity on the whole admissible interval, arbitrary index.** -/
theorem deviceArmEvent_globalLine_mono {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b)
    {t u : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hu : u ∈ Set.Icc (0 : ℝ) T) (htu : t ≤ u)
    (hrt : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) t x ∈
      Set.Icc (0 : ℝ) 1)
    (hru : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) u x ∈
      Set.Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitGlobalLine H S p s (independentComparisonSpeed a b R) t hrt)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal ≤
      (infiniteProductLaw (unitGlobalLine H S p s (independentComparisonSpeed a b R) u hru)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal := by
  classical
  let L := FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n
  let J := incidentFinset H S hunique L
  let K := localCoordinates H hG S J o n
  let c := independentComparisonSpeed a b R
  have hJ : incidentDevices H S L ⊆ J := by
    intro i hi
    exact (mem_incidentFinset H S hunique).2 hi
  have hdep : DependsOn (fun χ => χ ∈ deviceArmEvent (graph H)
      (independentSupport H S) o n) (K : Set ((graph H).edgeSet ⊕ ι)) :=
    dependsOn_deviceArmEvent_local H hG S o n hJ
  have hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K :=
    baseSupportOn_subset_localCoordinates H hG S J o n
  have haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K := by
    intro i hi
    exact activation_mem_localCoordinates H hG S o n hi
  have hdisj : ∀ (i j : J), i ≠ j →
      Disjoint (annulus H (S i.1)) (annulus H (S j.1)) :=
    disjoint_annuli_of_edgeUnique H S hunique
  have hweight (v : ℝ) : eventWeight (fun x : K => globalLine H S p s c v x.1)
      (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) =
      eventWeight (fun x : K => localLine H S J p s c v x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) := by
    congr 2
    funext x
    exact globalLine_eq_localLine_on_trace H hG S hunique o n hJ p s c v x.2
  calc
    _ = eventWeight (fun x : K => globalLine H S p s c t x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      (eventWeight_traceEvent (unitGlobalLine H S p s c t hrt) K _ hdep).symm
    _ = eventWeight (fun x : K => localLine H S J p s c t x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      hweight t
    _ ≤ eventWeight (fun x : K => localLine H S J p s c u x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      monotoneOn_localTraceEventWeight H S J hdisj R hR (fun i _ => hcard i) o n hBK haK
        p s a b T ha hb hp0 hs0 hpT hsT ht hu htu
    _ = eventWeight (fun x : K => globalLine H S p s c u x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      (hweight u).symm
    _ = _ := eventWeight_traceEvent (unitGlobalLine H S p s c u hru) K _ hdep

/-- **Percolation monotonicity on the whole admissible interval, arbitrary
index.**  Only probabilities are passed to the decreasing arm limit. -/
theorem globalLine_percolation_mono {V : Type u} [Countable V] (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b)
    {t u : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hu : u ∈ Set.Icc (0 : ℝ) T) (htu : t ≤ u)
    (hrt : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) t x ∈
      Set.Icc (0 : ℝ) 1)
    (hru : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) u x ∈
      Set.Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitGlobalLine H S p s (independentComparisonSpeed a b R) t hrt)
        (globalPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw (unitGlobalLine H S p s (independentComparisonSpeed a b R) u hru)
        (globalPercolationEvent H S o)).toReal := by
  apply le_of_tendsto_of_tendsto
    (tendsto_infiniteProductLaw_deviceArmEvent_global H hG S hunique o
      (unitGlobalLine H S p s (independentComparisonSpeed a b R) t hrt))
    (tendsto_infiniteProductLaw_deviceArmEvent_global H hG S hunique o
      (unitGlobalLine H S p s (independentComparisonSpeed a b R) u hru))
  exact Filter.Eventually.of_forall fun n =>
    deviceArmEvent_globalLine_mono H hG S hunique R hR hcard o n p s a b T ha hb
      hp0 hs0 hpT hsT ht hu htu hrt hru

end FK.AGImplant.Sleeve.CoveringReference

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.AGImplant.Sleeve.CoveringReference
open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

/-! ## Index-independent maximal time and the diagonal (uniform) profile -/

/-- Largest elapsed time allowed by the lower original-bond constraint and the
upper activation constraint.  It does not depend on the device index type or on
its cardinality. -/
noncomputable def refMaxTime (p s a b : ℝ) (R : ℕ) : ℝ :=
  min ((p - a) / independentComparisonSpeed a b R) (b - s)

lemma refMaxTime_moved {p s a b : ℝ} {R : ℕ} (hR : 0 < R) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b) :
    p - independentComparisonSpeed a b R * refMaxTime p s a b R ∈ Set.Icc a b := by
  have hc : 0 < independentComparisonSpeed a b R := independentComparisonSpeed_pos hR ha hb
  have hT : 0 ≤ refMaxTime p s a b R :=
    le_min (div_nonneg (sub_nonneg.mpr hp0.1) hc.le) (sub_nonneg.mpr hs0.2)
  have hmul : independentComparisonSpeed a b R * refMaxTime p s a b R ≤ p - a := by
    calc independentComparisonSpeed a b R * refMaxTime p s a b R
        ≤ independentComparisonSpeed a b R * ((p - a) / independentComparisonSpeed a b R) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
      _ = p - a := by field_simp
  have hnonneg : 0 ≤ independentComparisonSpeed a b R * refMaxTime p s a b R :=
    mul_nonneg hc.le hT
  exact ⟨by linarith, by linarith [hp0.2]⟩

lemma refMaxTime_activation {p s a b : ℝ} {R : ℕ}
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b) :
    s + refMaxTime p s a b R ∈ Set.Icc a b := by
  have hle : refMaxTime p s a b R ≤ b - s := min_le_right _ _
  have hT : 0 ≤ refMaxTime p s a b R :=
    le_min (div_nonneg (sub_nonneg.mpr hp0.1) (independentComparisonSpeed_nonneg R ha hb))
      (sub_nonneg.mpr hs0.2)
  exact ⟨by linarith [hs0.1], by linarith⟩

/-- The diagonal (uniform-rate) profile agrees with the three-rate profile when
the original-bond rate and the remaining sleeve-edge rate coincide. -/
lemma threePoint_diag {H : SimpleGraph V} {ι : Type v} (p s : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    threePoint (ι := ι) H p p s hp hp hs = uniformPoint (ι := ι) H p s hp hs := by
  funext x
  cases x with
  | inl f =>
      by_cases h : ∃ e : H.edgeSet, baseEdge H e = f
      · simp only [threePoint, uniformPoint, Sum.elim_inl, h, if_true]
      · simp only [threePoint, uniformPoint, Sum.elim_inl, h, if_false]
  | inr i => rfl

/-- The uniform-rate percolation probability is the diagonal three-rate one. -/
lemma uniformPerc_eq_threePerc {H : SimpleGraph V} {ι : Type v}
    {S : ι → Finset H.edgeSet} (o : V ⊕ H.edgeSet) (p s : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (infiniteProductLaw (uniformPoint (ι := ι) H p s hp hs)
        (globalPercolationEvent H S o)) =
      (infiniteProductLaw (threePoint (ι := ι) H p p s hp hp hs)
        (globalPercolationEvent H S o)) := by
  rw [threePoint_diag]

/-! ## The quantitative strict decrement of the critical original-bond rate -/

/-- Set of original-bond rates at which the sleeve model with remaining
sleeve-edge rate `gg` and activation rate `ss` percolates. -/
def PercBaseSet {H : SimpleGraph V} {ι : Type v} (S : ι → Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) (gg ss : ℝ)
    (hgg : gg ∈ Set.Icc (0 : ℝ) 1) (hss : ss ∈ Set.Icc (0 : ℝ) 1) : Set ℝ :=
  {bb | ∃ (hbb : bb ∈ Set.Icc (0 : ℝ) 1),
    0 < (infiniteProductLaw (threePoint (ι := ι) H bb gg ss hbb hgg hss)
      (globalPercolationEvent H S o)).toReal}

/-- **Strict decrement of the critical original-bond rate under activation.**

On a covering edge-unique family of equally sized devices, if the sleeve model
percolates at original-bond rate `p` and activation rate `s`, then at activation
rate `s + T` it already percolates at original-bond rate `p - c * T`, where
`c = independentComparisonSpeed a b R > 0`.  Hence the critical original-bond
rate at fixed remaining sleeve-edge rate `p` and activation rate `s + T` is at
most `p - c * T`, which is strictly below `p` whenever `T > 0`.

The threshold is the genuine infimum of the percolating original-bond rates in
`[0,1]`, and it is strictly decreased by the activation. -/
theorem covering_criticalBase_decrement {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (hcov : CoveringBase S) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 < T)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b)
    (hpos : 0 < (infiniteProductLaw
      (uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hs0))
      (globalPercolationEvent H S o)).toReal) :
    sInf (PercBaseSet S o p (s + T) (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hsT)) ≤ p - independentComparisonSpeed a b R * T := by
  have hcmp := covering_reference_comparison H hG S hunique R hR hcard hcov o
    p s a b T ha hb hT.le hp0 hs0 hpT hsT
  have hpos' : 0 < (infiniteProductLaw
      (threePoint (ι := ι) H (p - independentComparisonSpeed a b R * T) p (s + T)
        (mem_unit_of_box ha hb hpT) (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hsT))
      (globalPercolationEvent H S o)).toReal := lt_of_lt_of_le hpos hcmp
  refine csInf_le ?_ ?_
  · exact ⟨0, by rintro bb ⟨hbb, -⟩; exact hbb.1⟩
  · exact ⟨mem_unit_of_box ha hb hpT, hpos'⟩

end FK.AGImplant.Sleeve.CoveringReference

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.AGImplant.Sleeve.CoveringReference
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

/-! ## The singleton family: a covering edge-unique family on every graph

The covering hypothesis of `covering_reference_comparison` is not vacuous.  On
*every* graph the family that selects each original bond on its own is
edge-unique, has constant annulus cardinality one, and covers every bond.  The
inputs are therefore satisfied by the one-shared-activation-per-bond sleeve
model on any countable locally finite connected graph.
-/

lemma edges_singleton {V : Type u} (H : SimpleGraph V) (e : H.edgeSet) :
    edges H ({e} : Finset H.edgeSet) = {leftSpoke H e, rightSpoke H e} := by
  classical
  simp [edges]

lemma leftSpoke_injective {V : Type u} (H : SimpleGraph V) :
    Function.Injective (leftSpoke H) := by
  intro e f h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inr e) =
    s(Sum.inl (f : Sym2 V).out.1, Sum.inr f) at hval
  rcases Sym2.eq_iff.mp hval with ⟨_h₁, h₂⟩ | ⟨h₁, _h₂⟩
  · simpa using h₂
  · simp at h₁

lemma rightSpoke_injective {V : Type u} (H : SimpleGraph V) :
    Function.Injective (rightSpoke H) := by
  intro e f h
  have hval := congrArg Subtype.val h
  change s(Sum.inr e, Sum.inl (e : Sym2 V).out.2) =
    s(Sum.inr f, Sum.inl (f : Sym2 V).out.2) at hval
  rcases Sym2.eq_iff.mp hval with ⟨h₁, _h₂⟩ | ⟨h₁, _h₂⟩
  · simpa using h₁
  · simp at h₁

/-- A left spoke of one bond equals a right spoke of another only if the bonds
coincide.  (No looplessness is needed for this implication.) -/
lemma eq_of_leftSpoke_eq_rightSpoke {V : Type u} (H : SimpleGraph V)
    {e f : H.edgeSet} (h : leftSpoke H e = rightSpoke H f) : e = f := by
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inr e) =
    s(Sum.inr f, Sum.inl (f : Sym2 V).out.2) at hval
  rcases Sym2.eq_iff.mp hval with ⟨h₁, _h₂⟩ | ⟨_h₁, h₂⟩
  · simp at h₁
  · simpa using h₂

/-- Membership in the template of a singleton annulus. -/
lemma mem_template_singleton {V : Type u} (H : SimpleGraph V) (x : H.edgeSet)
    (g : (graph H).edgeSet) :
    g ∈ template H ({x} : Finset H.edgeSet) ↔
      g = baseEdge H x ∨ g = leftSpoke H x ∨ g = rightSpoke H x := by
  classical
  rw [mem_template, edges_singleton]
  constructor
  · rintro (h | h)
    · left
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      rw [Finset.mem_singleton] at hy
      rw [hy]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      tauto
  · rintro (rfl | rfl | rfl)
    · exact Or.inl (baseEdge_mem_annulus H {x} (Finset.mem_singleton_self x))
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)

/-- The singleton sleeve family is edge-unique. -/
lemma edgeUnique_singleton {V : Type u} (H : SimpleGraph V) :
    EdgeUnique H (fun e : H.edgeSet => ({e} : Finset H.edgeSet)) := by
  intro g e₁ h₁ e₂ h₂
  simp only [Set.mem_setOf_eq] at h₁ h₂
  rw [mem_template_singleton] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with k | k | k
  · exact baseEdge_injective H k
  · exact absurd k (baseEdge_ne_leftSpoke H e₁ e₂)
  · exact absurd k (baseEdge_ne_rightSpoke H e₁ e₂)
  · exact absurd k.symm (baseEdge_ne_leftSpoke H e₂ e₁)
  · exact leftSpoke_injective H k
  · exact eq_of_leftSpoke_eq_rightSpoke H k
  · exact absurd k.symm (baseEdge_ne_rightSpoke H e₂ e₁)
  · exact (eq_of_leftSpoke_eq_rightSpoke H k.symm).symm
  · exact rightSpoke_injective H k

/-- The singleton sleeve family covers every original bond. -/
lemma coveringBase_singleton {V : Type u} (H : SimpleGraph V) :
    CoveringBase (fun e : H.edgeSet => ({e} : Finset H.edgeSet)) := by
  intro e
  exact ⟨e, Finset.mem_singleton_self e⟩

@[simp] lemma card_singleton_annulus {V : Type u} (H : SimpleGraph V) (e : H.edgeSet) :
    (({e} : Finset H.edgeSet)).card = 1 := rfl

/-- **Reference shift for the one-shared-activation-per-bond sleeve model.**

On any connected locally finite graph with countable vertex type, the sleeve
model that attaches a separate two-edge bypass to every bond, and opens each
bypass with its own activation coordinate, satisfies the quantitative
trade-off: lowering every original bond by `c * T` and raising every activation
by `T` does not decrease the percolation probability. -/
theorem singleton_sleeve_reference_comparison {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b 1 * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b) :
    (infiniteProductLaw
        (uniformPoint (ι := H.edgeSet) H p s (mem_unit_of_box ha hb hp0)
          (mem_unit_of_box ha hb hs0))
        (globalPercolationEvent H (fun e : H.edgeSet => ({e} : Finset H.edgeSet)) o)).toReal ≤
      (infiniteProductLaw
        (threePoint (ι := H.edgeSet) H (p - independentComparisonSpeed a b 1 * T) p (s + T)
          (mem_unit_of_box ha hb hpT) (mem_unit_of_box ha hb hp0)
          (mem_unit_of_box ha hb hsT))
        (globalPercolationEvent H (fun e : H.edgeSet => ({e} : Finset H.edgeSet)) o)).toReal :=
  covering_reference_comparison H hG (fun e : H.edgeSet => ({e} : Finset H.edgeSet))
    (edgeUnique_singleton H) 1 (by norm_num) (fun _ => rfl)
    (coveringBase_singleton H) o p s a b T ha hb hT hp0 hs0 hpT hsT

/-- Strict decrement of the critical original-bond rate for the
one-shared-activation-per-bond sleeve model on any connected locally finite
countable graph. -/
theorem singleton_sleeve_criticalBase_decrement {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 < T)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b 1 * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b)
    (hpos : 0 < (infiniteProductLaw
      (uniformPoint (ι := H.edgeSet) H p s (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hs0))
      (globalPercolationEvent H (fun e : H.edgeSet => ({e} : Finset H.edgeSet)) o)).toReal) :
    sInf (PercBaseSet (fun e : H.edgeSet => ({e} : Finset H.edgeSet)) o p (s + T)
        (mem_unit_of_box ha hb hp0) (mem_unit_of_box ha hb hsT)) ≤
      p - independentComparisonSpeed a b 1 * T :=
  covering_criticalBase_decrement H hG (fun e : H.edgeSet => ({e} : Finset H.edgeSet))
    (edgeUnique_singleton H) 1 (by norm_num) (fun _ => rfl)
    (coveringBase_singleton H) o p s a b T ha hb hT hp0 hs0 hpT hsT hpos

end FK.AGImplant.Sleeve.CoveringReference

/-! ## Axiom audit -/

#print axioms FK.AGImplant.Sleeve.CoveringReference.covering_reference_comparison
#print axioms FK.AGImplant.Sleeve.CoveringReference.covering_criticalBase_decrement
#print axioms FK.AGImplant.Sleeve.CoveringReference.globalLine_percolation_mono
#print axioms FK.AGImplant.Sleeve.CoveringReference.deviceArmEvent_globalLine_mono
#print axioms FK.AGImplant.Sleeve.CoveringReference.globalLine_eq_threeReal_of_covering
#print axioms FK.AGImplant.Sleeve.CoveringReference.singleton_sleeve_reference_comparison
#print axioms FK.AGImplant.Sleeve.CoveringReference.singleton_sleeve_criticalBase_decrement
#print axioms FK.AGImplant.Sleeve.CoveringReference.edgeUnique_singleton
#print axioms FK.AGImplant.Sleeve.CoveringReference.refMaxTime_moved
#print axioms FK.AGImplant.Sleeve.CoveringReference.refMaxTime_activation

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.AGImplant.Sleeve.CoveringReference
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

/-! ## The general (not necessarily covering) trade-off, in explicit form

`FK.InfinitePackedSleeves` states the trade-off with the rate profile hidden
inside `unitGlobalLine` and with two unit-interval side conditions supplied by
the caller.  The next statement removes those side conditions (they are
constructed from the box) and writes the initial profile as the explicit
uniform profile.  The final profile is `globalLine` itself, i.e. `p - c * T`
exactly on the *selected* bonds and `p` on every unselected bond and on every
bypass spoke.  This is the form in which the inhomogeneity is visible. -/

/-- **General trade-off of the sleeved essential-enhancement line.** -/
theorem general_reference_tradeoff {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b) :
    (infiniteProductLaw
        (uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
          (mem_unit_of_box ha hb hs0))
        (globalPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw
        (unitGlobalLine H S p s (independentComparisonSpeed a b R) T
          (globalLine_mem_unit (S := S) (c := independentComparisonSpeed a b R)
            (t := T) ha hb hp0 hpT hsT))
        (globalPercolationEvent H S o)).toReal := by
  have hr0 : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Set.Icc (0 : ℝ) 1 := by
    refine globalLine_mem_unit (S := S) (c := independentComparisonSpeed a b R)
      (t := 0) ha hb hp0 ?_ ?_
    · simpa using hp0
    · simpa using hs0
  have hrT : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) T x ∈
      Set.Icc (0 : ℝ) 1 :=
    globalLine_mem_unit (S := S) (c := independentComparisonSpeed a b R) (t := T)
      ha hb hp0 hpT hsT
  have hmain := infiniteProductLaw_globalPercolation_globalLine_le H hG S hunique
    R hR hcard o p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT
  have h0 : unitGlobalLine H S p s (independentComparisonSpeed a b R) 0 hr0 =
      uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hs0) :=
    unitGlobalLine_zero_eq_uniformPoint (S := S)
      (c := independentComparisonSpeed a b R) (hr := hr0)
      (hp := mem_unit_of_box ha hb hp0) (hs := mem_unit_of_box ha hb hs0)
  rw [h0] at hmain
  exact hmain

/-- **Covering criterion curve with index-independent maximal time.**

With a covering edge-unique family of equal annulus size `R`, the percolation
probability of the sleeved model is monotone along the whole admissible line up
to the explicit maximal time `refMaxTime p s a b R`, which depends neither on
the device index type nor on its cardinality. -/
theorem covering_monotone_curve {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (p s a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    {t u : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (refMaxTime p s a b R))
    (hu : u ∈ Set.Icc (0 : ℝ) (refMaxTime p s a b R)) (htu : t ≤ u)
    (hrt : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) t x ∈
      Set.Icc (0 : ℝ) 1)
    (hru : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) u x ∈
      Set.Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitGlobalLine H S p s (independentComparisonSpeed a b R) t hrt)
        (globalPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw (unitGlobalLine H S p s (independentComparisonSpeed a b R) u hru)
        (globalPercolationEvent H S o)).toReal :=
  globalLine_percolation_mono H hG S hunique R hR hcard o p s a b
    (refMaxTime p s a b R) ha hb hp0 hs0
    (refMaxTime_moved hR ha hb hp0 hs0) (refMaxTime_activation ha.le hb.le hp0 hs0)
    ht hu htu hrt hru

#print axioms FK.AGImplant.Sleeve.CoveringReference.general_reference_tradeoff
#print axioms FK.AGImplant.Sleeve.CoveringReference.covering_monotone_curve

end FK.AGImplant.Sleeve.CoveringReference

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.AGImplant.Sleeve.CoveringReference
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

/-! ## Strictness and the maximal-time form -/

/-- **The critical original-bond rate is strictly below the percolating rate.**
Under the covering hypothesis, if the sleeve model percolates at original-bond
rate `p` and activation rate `s`, then for every positive elapsed time the
critical original-bond rate at activation rate `s + T` (at fixed spoke rate `p`)
is strictly smaller than `p`. -/
theorem covering_criticalBase_lt {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (hcov : CoveringBase S) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 < T)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Set.Icc a b)
    (hsT : s + T ∈ Set.Icc a b)
    (hpos : 0 < (infiniteProductLaw
      (uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hs0))
      (globalPercolationEvent H S o)).toReal) :
    sInf (PercBaseSet S o p (s + T) (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hsT)) < p := by
  have hle := covering_criticalBase_decrement H hG S hunique R hR hcard hcov o
    p s a b T ha hb hT hp0 hs0 hpT hsT hpos
  have hc : 0 < independentComparisonSpeed a b R := independentComparisonSpeed_pos hR ha hb
  have : 0 < independentComparisonSpeed a b R * T := mul_pos hc hT
  linarith

/-- **Decrement at the maximal admissible time.**  The explicit
index-independent maximal elapsed time gives the strongest decrement available
on the box. -/
theorem covering_criticalBase_decrement_maxTime {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (hcov : CoveringBase S) (o : V ⊕ H.edgeSet)
    (p s a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Set.Icc a b) (hs0 : s ∈ Set.Icc a b)
    (hT : 0 < refMaxTime p s a b R) (hsT : s + refMaxTime p s a b R ∈ Set.Icc a b)
    (hpos : 0 < (infiniteProductLaw
      (uniformPoint (ι := ι) H p s (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hs0))
      (globalPercolationEvent H S o)).toReal) :
    sInf (PercBaseSet S o p (s + refMaxTime p s a b R) (mem_unit_of_box ha hb hp0)
        (mem_unit_of_box ha hb hsT)) ≤
      p - independentComparisonSpeed a b R * refMaxTime p s a b R :=
  covering_criticalBase_decrement H hG S hunique R hR hcard hcov o
    p s a b (refMaxTime p s a b R) ha hb hT hp0 hs0
    (refMaxTime_moved hR ha hb hp0 hs0) hsT hpos

#print axioms FK.AGImplant.Sleeve.CoveringReference.covering_criticalBase_lt
#print axioms FK.AGImplant.Sleeve.CoveringReference.covering_criticalBase_decrement_maxTime

end FK.AGImplant.Sleeve.CoveringReference

namespace FK.AGImplant.Sleeve.CoveringReference

open FK.AGImplant.Sleeve.CoveringReference
open FK.AGImplant.Sleeve.GlobalInfinite

/-! ## The trade constant is not uniform in the parameter box

The speed `independentComparisonSpeed a b R = (min a (1-b))^R / (2^R R)` needs
`0 < a` and `b < 1`, i.e. every coordinate must stay strictly inside `(0,1)`,
and it degenerates at both ends of that window.  The following exact arithmetic
statement records that no positive constant bounds the speed for all boxes, so
the comparison cannot be integrated over a parameter interval whose endpoints
approach `0` or `1`.  This is the precise sense in which the present chain does
*not* supply the Aizenman–Grimmett derivative-integration step. -/

lemma independentComparisonSpeed_one (a b : ℝ) :
    independentComparisonSpeed a b 1 = sleeveMinorant a b / 2 := by
  simp [independentComparisonSpeed]

/-- **No uniform positive speed.**  For every proposed constant `c > 0` there is
an admissible box whose trade speed is smaller than `c`. -/
lemma exists_box_speed_lt (c : ℝ) (hc : 0 < c) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      independentComparisonSpeed a b 1 < c := by
  have hc4 : 0 < min (1 / 4 : ℝ) c := lt_min (by norm_num) hc
  refine ⟨min (1 / 4 : ℝ) c, 1 / 2, hc4, ?_, by norm_num, ?_⟩
  · have : min (1 / 4 : ℝ) c ≤ 1 / 4 := min_le_left _ _
    linarith
  · rw [independentComparisonSpeed_one]
    have hmin : sleeveMinorant (min (1 / 4 : ℝ) c) (1 / 2) = min (1 / 4 : ℝ) c := by
      rw [sleeveMinorant, min_eq_left]
      have h1 : min (1 / 4 : ℝ) c ≤ 1 / 4 := min_le_left _ _
      linarith
    rw [hmin]
    have hle : min (1 / 4 : ℝ) c ≤ c := min_le_right _ _
    linarith

#print axioms FK.AGImplant.Sleeve.CoveringReference.exists_box_speed_lt

end FK.AGImplant.Sleeve.CoveringReference

namespace FK.AGImplant.Sleeve.CoveringReference.Ext

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite
open FK.AGImplant.Sleeve.CoveringReference

/-!
## Spoke pivot transport

The uniform-rate upgrade of `covering_reference_comparison` needs the trade-off
line to move the *bypass spokes* as well as the original bonds.  The naive
domination "a spoke is at least as pivotal as its activation" is **false**: take
the configuration with the activation closed and the spoke's own coordinate
open; closing that spoke removes the arm, while closing the activation does not.
The correct statement closes every spoke of the device first.  With the whole
spoke set closed, a spoke pivot does transport to the activation pivot, because
the activation opens all of that device's spokes at once.

These statements are independent of the covering hypothesis and of any
parameter box.
-/

variable {V : Type u} {ι : Type v}

/-- `AddsEdge` is unaffected by forcing an ordinary bond coordinate. -/
lemma addsEdge_force_inl {E : Type u} {F : Type v} (support : F → Set E)
    (χ : JointConfig E F) (x : E) (b : Bool) (e : E) :
    AddsEdge support (forceEdge χ (Sum.inl x) b) e ↔ AddsEdge support χ e := by
  have h : ∀ z : F, (forceEdge χ (Sum.inl x) b) (Sum.inr z) = χ (Sum.inr z) :=
    fun z => forceEdge_of_ne χ (by simp : (Sum.inr z : E ⊕ F) ≠ Sum.inl x) b
  constructor
  · rintro ⟨z, hz, hez⟩
    exact ⟨z, by rw [h z] at hz; exact hz, hez⟩
  · rintro ⟨z, hz, hez⟩
    exact ⟨z, by rw [h z]; exact hz, hez⟩

/-- Forcing one ordinary bond open does not change the device configuration
away from that bond. -/
lemma deviceConfig_force_inl_true {E : Type u} {F : Type v} (support : F → Set E)
    (χ : JointConfig E F) (x : E) (e : E) :
    deviceConfig support (forceEdge χ (Sum.inl x) true) e =
      if e = x then true else deviceConfig support χ e := by
  classical
  by_cases h : e = x
  · subst h
    rw [if_pos rfl]
    unfold deviceConfig
    rw [addsEdge_force_inl]
    split_ifs with hh
    · rfl
    · exact forceEdge_same χ _ true
  · rw [if_neg h]
    unfold deviceConfig
    rw [addsEdge_force_inl,
      forceEdge_of_ne χ (by simp [h] : (Sum.inl e : E ⊕ F) ≠ Sum.inl x) true]

@[simp] lemma annularClose_inl {E : Type u} {F : Type v} (R : Finset E)
    (χ : JointConfig E F) (e : E) :
    annularClose R χ (Sum.inl e) = if e ∈ R then false else χ (Sum.inl e) := rfl

/-- Closing the activations of a single device can only remove additions. -/
lemma addsEdge_close_act_imp {E : Type u} {F : Type v} (support : F → Set E)
    (R : Finset E) (χ : JointConfig E F) (i : F) (e : E)
    (h : AddsEdge support (forceEdge (annularClose R χ) (Sum.inr i) false) e) :
    AddsEdge support χ e := by
  rcases h with ⟨z, hz, hez⟩
  refine ⟨z, ?_, hez⟩
  by_cases hz' : z = i
  · subst hz'
    rw [forceEdge_same] at hz
    exact absurd hz (by simp)
  · rw [forceEdge_of_ne _ (by simp [hz']) false, annularClose_inr] at hz
    exact hz

/-- Opening the activation of a device whose support does not contain `e`
leaves additions at `e` unchanged. -/
lemma addsEdge_open_act_iff_of_notMem {E : Type u} {F : Type v} (support : F → Set E)
    (R : Finset E) (χ : JointConfig E F) (i : F) (e : E) (he : e ∉ support i) :
    AddsEdge support (forceEdge (annularClose R χ) (Sum.inr i) true) e ↔
      AddsEdge support χ e := by
  constructor
  · rintro ⟨z, hz, hez⟩
    refine ⟨z, ?_, hez⟩
    by_cases hz' : z = i
    · subst hz'
      exact absurd hez he
    · rw [forceEdge_of_ne _ (by simp [hz']) true, annularClose_inr] at hz
      exact hz
  · rintro ⟨z, hz, hez⟩
    refine ⟨z, ?_, hez⟩
    by_cases hz' : z = i
    · subst hz'
      exact forceEdge_same _ _ true
    · rw [forceEdge_of_ne _ (by simp [hz']) true, annularClose_inr]
      exact hz

/-- Forcing one ordinary bond closed does not change the device configuration
away from that bond. -/
lemma deviceConfig_force_inl_false {E : Type u} {F : Type v} (support : F → Set E)
    (χ : JointConfig E F) (x : E) (e : E) (he : e ≠ x) :
    deviceConfig support (forceEdge χ (Sum.inl x) false) e = deviceConfig support χ e := by
  unfold deviceConfig
  rw [addsEdge_force_inl,
    forceEdge_of_ne χ (by simp [he] : (Sum.inl e : E ⊕ F) ≠ Sum.inl x) false]

/-- **One side of the spoke transport.**  Opening a spoke is no better than
closing all spokes of the device and opening its activation. -/
lemma deviceConfig_force_spoke_le_close_open {V : Type u} {ι : Type v}
    (H : SimpleGraph V) (S : ι → Finset H.edgeSet) (i : ι)
    {f : (graph H).edgeSet} (hf : f ∈ edges H (S i))
    (χ : JointConfig (graph H).edgeSet ι) :
    deviceConfig (independentSupport H S) (forceEdge χ (Sum.inl f) true) ≤
      deviceConfig (independentSupport H S)
        (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) true) := by
  classical
  intro e
  rw [deviceConfig_force_inl_true]
  by_cases hef : e = f
  · rw [if_pos hef]
    have htrue : deviceConfig (independentSupport H S)
        (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) true) e = true :=
      deviceConfig_eq_true_of_mem _ _ i e (forceEdge_same _ _ true) (by rw [hef]; exact hf)
    rw [htrue]
  · rw [if_neg hef]
    by_cases heR : e ∈ edges H (S i)
    · have htrue : deviceConfig (independentSupport H S)
          (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) true) e = true :=
        deviceConfig_eq_true_of_mem _ _ i e (forceEdge_same _ _ true) (by simpa using heR)
      rw [htrue]
      exact le_top
    · have hcoe : (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) true) (Sum.inl e)
          = χ (Sum.inl e) := by
        rw [forceEdge_of_ne _ (by simp) true, annularClose_inl, if_neg heR]
      have hadd := addsEdge_open_act_iff_of_notMem (support := independentSupport H S)
        (R := edges H (S i)) (χ := χ) (i := i) (e := e) (by simpa using heR)
      unfold deviceConfig
      rw [hcoe, hadd]

/-- **Other side of the spoke transport.**  Closing all spokes of the device and
closing its activation is no better than closing a single spoke. -/
lemma close_act_deviceConfig_le_force_spoke {V : Type u} {ι : Type v}
    (H : SimpleGraph V) (S : ι → Finset H.edgeSet) (i : ι)
    {f : (graph H).edgeSet} (hf : f ∈ edges H (S i))
    (χ : JointConfig (graph H).edgeSet ι) :
    deviceConfig (independentSupport H S)
        (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) false) ≤
      deviceConfig (independentSupport H S) (forceEdge χ (Sum.inl f) false) := by
  classical
  have hfR : f ∈ edges H (S i) := hf
  have hle : ∀ e, AddsEdge (independentSupport H S)
      (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) false) e →
      AddsEdge (independentSupport H S) χ e :=
    fun e h => addsEdge_close_act_imp _ _ _ _ _ h
  intro e
  by_cases hef : e = f
  · rw [hef]
    have hcoe : (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) false) (Sum.inl f)
        = false := by
      rw [forceEdge_of_ne _ (by simp) false, annularClose_inl, if_pos hfR]
    have hRadd : AddsEdge (independentSupport H S) (forceEdge χ (Sum.inl f) false) f ↔
        AddsEdge (independentSupport H S) χ f := addsEdge_force_inl _ _ _ _ _
    unfold deviceConfig
    rw [hcoe, forceEdge_same, hRadd]
    split_ifs with h1 h2
    · exact le_top
    · exact absurd (hle f h1) h2
    · exact le_top
    · exact bot_le
  · rw [deviceConfig_force_inl_false _ _ _ _ hef]
    by_cases heR : e ∈ edges H (S i)
    · have hcoe : (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) false) (Sum.inl e)
          = false := by
        rw [forceEdge_of_ne _ (by simp) false, annularClose_inl, if_pos heR]
      unfold deviceConfig
      rw [hcoe]
      split_ifs with h1 h2
      · exact le_top
      · exact absurd (hle e h1) h2
      · exact le_top
      · exact bot_le
    · have hcoe : (forceEdge (annularClose (edges H (S i)) χ) (Sum.inr i) false) (Sum.inl e)
          = χ (Sum.inl e) := by
        rw [forceEdge_of_ne _ (by simp) false, annularClose_inl, if_neg heR]
      unfold deviceConfig
      rw [hcoe]
      split_ifs with h1 h2
      · exact le_top
      · exact absurd (hle e h1) h2
      · exact le_top
      · rfl

end FK.AGImplant.Sleeve.CoveringReference.Ext

namespace FK.AGImplant.Sleeve.CoveringReference.Ext

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite

/-- Monotone-in-the-device-configuration form of the spoke pivot transport. -/
theorem activationPivotal_of_spokePivotal_of_mono {V : Type u} {ι : Type v}
    (H : SimpleGraph V) (S : ι → Finset H.edgeSet) (i : ι)
    {f : (graph H).edgeSet} (hf : f ∈ edges H (S i))
    (A : Set (JointConfig (graph H).edgeSet ι))
    (hA : ∀ {χ ξ : JointConfig (graph H).edgeSet ι},
      deviceConfig (independentSupport H S) χ ≤ deviceConfig (independentSupport H S) ξ →
        χ ∈ A → ξ ∈ A)
    {χ : JointConfig (graph H).edgeSet ι} (hpiv : EdgePivotal A f χ) :
    ActivationPivotal A i (annularClose (edges H (S i)) χ) := by
  constructor
  · exact hA (deviceConfig_force_spoke_le_close_open H S i hf χ) hpiv.1
  · intro hmem
    exact hpiv.2 (hA (close_act_deviceConfig_le_force_spoke H S i hf χ) hmem)

/-- **Spoke pivot transport.**  If one bypass spoke of device `i` is pivotal for
an increasing joint event then, after closing every spoke of that device, its
activation is pivotal for the same event.

This is the exact replacement of the (false) naive domination statement
"a spoke is at least as pivotal as its activation".  It is the missing
geometric ingredient for extending the trade-off line of
`FK.InfinitePackedSleeves` to the bypass spokes. -/
theorem activationPivotal_of_spokePivotal {V : Type u} {ι : Type v}
    (H : SimpleGraph V) (S : ι → Finset H.edgeSet) (i : ι)
    {f : (graph H).edgeSet} (hf : f ∈ edges H (S i))
    (B : Set ((graph H).edgeSet → Bool)) (hB : IsUpperSet B)
    {χ : JointConfig (graph H).edgeSet ι}
    (hpiv : EdgePivotal (deviceEvent (independentSupport H S) B) f χ) :
    ActivationPivotal (deviceEvent (independentSupport H S) B) i
      (annularClose (edges H (S i)) χ) :=
  activationPivotal_of_spokePivotal_of_mono H S i hf _
    (fun {_χ _ξ} h hχ => hB h hχ) hpiv

/-- Arm-event specialization of the spoke pivot transport. -/
theorem activationPivotal_deviceArmEvent_of_spokePivotal {V : Type u} {ι : Type v}
    (H : SimpleGraph V) (S : ι → Finset H.edgeSet) (i : ι)
    {f : (graph H).edgeSet} (hf : f ∈ edges H (S i))
    {o : V ⊕ H.edgeSet} (n : ℕ) {χ : JointConfig (graph H).edgeSet ι}
    (hpiv : EdgePivotal (deviceArmEvent (graph H) (independentSupport H S) o n) f χ) :
    ActivationPivotal (deviceArmEvent (graph H) (independentSupport H S) o n) i
      (annularClose (edges H (S i)) χ) :=
  activationPivotal_of_spokePivotal_of_mono H S i hf _
    (fun {_χ _ξ} h hχ => isUpperSet_armEvent o n h hχ) hpiv

#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.activationPivotal_of_spokePivotal
#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.activationPivotal_deviceArmEvent_of_spokePivotal
#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.addsEdge_force_inl
#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.deviceConfig_force_inl_true
#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.deviceConfig_force_spoke_le_close_open
#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.close_act_deviceConfig_le_force_spoke

end FK.AGImplant.Sleeve.CoveringReference.Ext

namespace FK.AGImplant.Sleeve.CoveringReference.Ext

/-! ## Trace-level spoke pivot bound -/

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.GlobalInfinite
open FK.AGImplant.Sleeve.IndexedInfinite

variable {V : Type u} {ι : Type v}

/-- **Trace-level spoke pivot transport.**  On a finite edge trace a single
bypass spoke contributes at most the likelihood factor `δ` and the fibre factor
`2` against its device's activation pivot. -/
lemma globalTrace_spokePivotal_event_mul_le
    (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet)
    (i : ι) {o : V ⊕ H.edgeSet} (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (edges H (S i)) ⊆ K)
    (haK : (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b)
    {x : K} (hx : x ∈ traceFinset
      (bondCoordinates (F := ι) (edges H (S i))) K hRK) :
    δ ^ (edges H (S i)).card * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ} ≤
      ((2 ^ (edges H (S i)).card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n))
            ⟨Sum.inr i, haK⟩ ξ} := by
  classical
  let a : K := ⟨Sum.inr i, haK⟩
  have hmap : ∀ ξ : K → Bool,
      Pivotal (traceEvent K (deviceArmEvent (graph H)
        (independentSupport H S) o n)) x ξ →
      Pivotal (traceEvent K (deviceArmEvent (graph H)
        (independentSupport H S) o n)) a
        (traceClose (bondCoordinates (F := ι) (edges H (S i))) ξ) := by
    intro ξ hp
    have hxR := (mem_traceFinset (hRK := hRK) x).1 hx
    rcases Finset.mem_map.mp hxR with ⟨f, hf, hfx⟩
    have hxf : x.1 = Sum.inl f := hfx.symm
    have hpFull : EdgePivotal
        (deviceArmEvent (graph H) (independentSupport H S) o n) f (traceExtend K ξ) := by
      have hp' := (pivotal_traceEvent K _ x ξ).1 hp
      change Pivotal _ (Sum.inl f) _
      rw [← hxf]
      exact hp'
    have haFull := activationPivotal_deviceArmEvent_of_spokePivotal H S i hf n hpFull
    apply (pivotal_traceEvent K _ a _).2
    change Pivotal _ (Sum.inr i) _
    rw [FK.AGImplant.Sleeve.IndexedInfinite.traceExtend_traceClose_annular hRK]
    exact haFull
  have h := local_pi_event_mul_le ν
    (traceFinset (bondCoordinates (F := ι) (edges H (S i))) K hRK)
    δ hδ hν (traceClose (bondCoordinates (F := ι) (edges H (S i))))
    (traceClose_isLocalModification hRK)
    {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}
    {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) a ξ}
    (by intro ξ hξ; exact hmap ξ hξ)
  simpa only [card_traceFinset, card_bondCoordinates, a] using h

/-- **Per-device spoke pivot sum.**  All bypass spokes of one device that occur
on a finite trace cost at most `2` per spoke against that device's
activation-pivot weight, with the likelihood factor `δ ^ |spokes|` on the left. -/
lemma globalTrace_sum_spokePivotal_event_mul_le
    (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet)
    (i : ι) {o : V ⊕ H.edgeSet} (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (edges H (S i)) ⊆ K)
    (haK : (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b) :
    δ ^ (edges H (S i)).card *
        (∑ x ∈ traceFinset (bondCoordinates (F := ι) (edges H (S i))) K hRK,
          (OpenPath.FinProb.pi ν).event
            {ξ | Pivotal (traceEvent K
              (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}) ≤
      ((2 ^ (edges H (S i)).card : ℕ) : ℝ) *
        (∑ _x ∈ traceFinset (bondCoordinates (F := ι) (edges H (S i))) K hRK,
          (OpenPath.FinProb.pi ν).event
            {ξ | Pivotal (traceEvent K
              (deviceArmEvent (graph H) (independentSupport H S) o n))
                ⟨Sum.inr i, haK⟩ ξ}) := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx =>
    globalTrace_spokePivotal_event_mul_le H S i (o := o) n hRK haK ν δ hδ hν hx

#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.globalTrace_spokePivotal_event_mul_le
#print axioms FK.AGImplant.Sleeve.CoveringReference.Ext.globalTrace_sum_spokePivotal_event_mul_le

end FK.AGImplant.Sleeve.CoveringReference.Ext
