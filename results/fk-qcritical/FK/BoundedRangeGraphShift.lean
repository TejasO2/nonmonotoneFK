import FK.AGInfiniteLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Probability.BorelCantelli

/-!
# A bounded-range strict shift on a logarithmic bundle chain

This module constructs a connected locally finite simple graph whose
random route edges occur in bundles. There are `2^k` bundles of width `k+1`.
One stem edge of every two-edge route is deterministically open; the other edge
has an independent bond bit and an independent activation bit, and the activation
opens only that one edge. The resulting ordinary critical parameter is `1/2`.
At activation rate `1/4`, the normalized OR law gives enhanced critical parameter
exactly `1/3`; the strict shift is therefore `1/3 < 1/2`.

No synchronized or unbounded-range activation is used, and this is not claimed
as the general Aizenman--Grimmett reference theorem. The deterministic stems make
the full edge law inhomogeneous, although every non-deterministic edge has the
same bond and activation parameters.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal Topology unitInterval Sym2 BigOperators

namespace FK.AGBoundedRangeBundleShift

open CurvatureVariance.Infra.Percolation
open FK.AGGadget (orUnit)

/-- The number of routes in bundle `n`: width `k+1` occurs `2^k` times. -/
def width (n : ℕ) : ℕ := Nat.log 2 (n + 1) + 1

lemma width_pos (n : ℕ) : 0 < width n := by
  simp [width]

instance (n : ℕ) : Nonempty (Fin (width n)) := ⟨⟨0, width_pos n⟩⟩

/-- Failure probability of a bundle after stripping off its block indexing. -/
def positiveFailure (p : unitInterval) (n : ℕ) : ℝ :=
  (1 - (p : ℝ)) ^ (Nat.log 2 n + 1)

/-- Failure probability of bundle `n`. -/
def bundleFailure (p : unitInterval) (n : ℕ) : ℝ := positiveFailure p (n + 1)

lemma bundleFailure_eq (p : unitInterval) (n : ℕ) :
    bundleFailure p n = (1 - (p : ℝ)) ^ width n := rfl

lemma positiveFailure_nonneg (p : unitInterval) (n : ℕ) : 0 ≤ positiveFailure p n := by
  exact pow_nonneg (sub_nonneg.mpr p.property.2) _

lemma bundleFailure_nonneg (p : unitInterval) (n : ℕ) : 0 ≤ bundleFailure p n :=
  positiveFailure_nonneg p _

lemma positiveFailure_antitone (p : unitInterval) :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → positiveFailure p n ≤ positiveFailure p m := by
  intro m n _ hmn
  exact pow_le_pow_of_le_one (sub_nonneg.mpr p.property.2)
    (by linarith [p.property.1]) (Nat.add_le_add_right (Nat.log_mono_right hmn) 1)

lemma condensed_positiveFailure (p : unitInterval) (k : ℕ) :
    (2 : ℝ) ^ k * positiveFailure p (2 ^ k) =
      (1 - (p : ℝ)) * (2 * (1 - (p : ℝ))) ^ k := by
  rw [positiveFailure, Nat.log_pow Nat.one_lt_two, pow_succ, mul_pow]
  ring

/-- Above `1/2`, bundle failures are summable, by Cauchy condensation. -/
theorem summable_bundleFailure_of_half_lt {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) :
    Summable (bundleFailure p) := by
  have ha0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have ha1 : 2 * (1 - (p : ℝ)) < 1 := by linarith
  have hg : Summable (fun k : ℕ => (2 * (1 - (p : ℝ))) ^ k) :=
    summable_geometric_of_lt_one (mul_nonneg (by norm_num) ha0) ha1
  have hc : Summable (fun k : ℕ => (2 : ℝ) ^ k * positiveFailure p (2 ^ k)) := by
    apply (hg.mul_left (1 - (p : ℝ))).congr
    intro k
    exact (condensed_positiveFailure p k).symm
  exact (summable_nat_add_iff (f := positiveFailure p) 1).2
    ((summable_condensed_iff_of_nonneg (positiveFailure_nonneg p)
      (positiveFailure_antitone p)).1 hc)

/-- At and below `1/2`, bundle failures are not summable. -/
theorem not_summable_bundleFailure_of_le_half {p : unitInterval} (hp : (p : ℝ) ≤ 1 / 2) :
    ¬ Summable (bundleFailure p) := by
  intro hs
  have ha : 0 < 1 - (p : ℝ) := by linarith [p.property.2]
  have hfull : Summable (positiveFailure p) :=
    (summable_nat_add_iff (f := positiveFailure p) 1).1 hs
  have hc : Summable (fun k : ℕ => (2 : ℝ) ^ k * positiveFailure p (2 ^ k)) :=
    ((summable_condensed_iff_of_nonneg (positiveFailure_nonneg p)
      (positiveFailure_antitone p)).2 hfull)
  have hg : Summable (fun k : ℕ => (2 * (1 - (p : ℝ))) ^ k) := by
    have hm := hc.mul_left (1 - (p : ℝ))⁻¹
    apply hm.congr
    intro k
    rw [condensed_positiveFailure]
    field_simp
  have hr := (summable_geometric_iff_norm_lt_one.1 hg)
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) ha.le)] at hr
  linarith

lemma tsum_ofReal_bundleFailure_ne_top {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) :
    (∑' n, ENNReal.ofReal (bundleFailure p n)) ≠ ∞ :=
  (summable_bundleFailure_of_half_lt hp).tsum_ofReal_ne_top

lemma tsum_ofReal_bundleFailure_eq_top {p : unitInterval} (hp : (p : ℝ) ≤ 1 / 2) :
    (∑' n, ENNReal.ofReal (bundleFailure p n)) = ∞ := by
  by_contra htop
  have hs := ENNReal.summable_toReal htop
  apply not_summable_bundleFailure_of_le_half hp
  apply hs.congr
  intro n
  exact ENNReal.toReal_ofReal (bundleFailure_nonneg p n)


/-- Routes are indexed independently inside each bundle. -/
abbrev RouteState := ∀ n : ℕ, (Fin (width n) → Bool)

/-- The independent law of all route bits in one bundle. -/
noncomputable def routeLaw (p : unitInterval) (n : ℕ) :
    Measure (Fin (width n) → Bool) :=
  Measure.infinitePi fun _ => bernoulliMeasure true false p

instance (p : unitInterval) (n : ℕ) : IsProbabilityMeasure (routeLaw p n) := by
  unfold routeLaw
  infer_instance

/-- The actual independent bond product, grouped by bundles. -/
noncomputable def bondLaw (p : unitInterval) : Measure RouteState :=
  Measure.infinitePi (routeLaw p)

instance (p : unitInterval) : IsProbabilityMeasure (bondLaw p) := by
  unfold bondLaw
  infer_instance

/-- A block is crossed when at least one of its route bits is open. -/
def OpenBlock (n : ℕ) : Set (Fin (width n) → Bool) := {x | ∃ i, x i = true}

/-- A block fails exactly when every route bit is closed. -/
def ClosedBlock (n : ℕ) : Set (Fin (width n) → Bool) := {x | ∀ i, x i = false}

lemma openBlock_eq_compl_closedBlock (n : ℕ) :
    OpenBlock n = (ClosedBlock n)ᶜ := by
  ext x
  simp only [OpenBlock, ClosedBlock, mem_setOf_eq, mem_compl_iff]
  constructor
  · rintro ⟨i, hi⟩ h
    rw [h i] at hi
    contradiction
  · intro h
    by_contra hn
    apply h
    intro i
    cases hi : x i with
    | false => rfl
    | true => exact (hn ⟨i, hi⟩).elim

lemma measurableSet_closedBlock (n : ℕ) : MeasurableSet (ClosedBlock n) := by
  have heq : ClosedBlock n = (Set.univ : Set (Fin (width n))).pi (fun _ => {false}) := by
    ext x
    simp [ClosedBlock]
  rw [heq]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_singleton false)

lemma measurableSet_openBlock (n : ℕ) : MeasurableSet (OpenBlock n) := by
  rw [openBlock_eq_compl_closedBlock]
  exact (measurableSet_closedBlock n).compl

lemma closedBlock_measure (p : unitInterval) (n : ℕ) :
    routeLaw p n (ClosedBlock n) = ENNReal.ofReal (bundleFailure p n) := by
  have heq : ClosedBlock n =
      (↑(Finset.univ : Finset (Fin (width n))) : Set (Fin (width n))).pi
        (fun _ => {false}) := by
    ext x
    simp [ClosedBlock]
  rw [heq, routeLaw, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton false)]
  simp only [bernoulliMeasure_false, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, bundleFailure_eq]
  exact (ENNReal.ofReal_pow (sub_nonneg.mpr p.property.2) (width n)).symm

lemma openBlock_measure (p : unitInterval) (n : ℕ) :
    routeLaw p n (OpenBlock n) = 1 - ENNReal.ofReal (bundleFailure p n) := by
  rw [openBlock_eq_compl_closedBlock,
    measure_compl (measurableSet_closedBlock n) (measure_ne_top _ _),
    closedBlock_measure, measure_univ]

/-- Global events obtained by evaluating one bundle coordinate. -/
def BundleOpen (n : ℕ) : Set RouteState := (fun ω => ω n) ⁻¹' OpenBlock n

def BundleClosed (n : ℕ) : Set RouteState := (fun ω => ω n) ⁻¹' ClosedBlock n

lemma measurableSet_bundleOpen (n : ℕ) : MeasurableSet (BundleOpen n) :=
  measurable_pi_apply n (measurableSet_openBlock n)

lemma measurableSet_bundleClosed (n : ℕ) : MeasurableSet (BundleClosed n) :=
  measurable_pi_apply n (measurableSet_closedBlock n)

lemma bundleOpen_measure (p : unitInterval) (n : ℕ) :
    bondLaw p (BundleOpen n) = routeLaw p n (OpenBlock n) := by
  exact (measurePreserving_eval_infinitePi (fun n : ℕ => routeLaw p n) n).measure_preimage
    (measurableSet_openBlock n).nullMeasurableSet

lemma bundleClosed_measure (p : unitInterval) (n : ℕ) :
    bondLaw p (BundleClosed n) = ENNReal.ofReal (bundleFailure p n) := by
  change (Measure.infinitePi (routeLaw p))
    ((fun ω => ω n) ⁻¹' ClosedBlock n) = _
  rw [(measurePreserving_eval_infinitePi (fun n : ℕ => routeLaw p n) n).measure_preimage
    (measurableSet_closedBlock n).nullMeasurableSet]
  exact closedBlock_measure p n

lemma iIndepSet_bundleClosed (p : unitInterval) : iIndepSet BundleClosed (bondLaw p) := by
  apply (iIndepSet_iff_meas_biInter measurableSet_bundleClosed).2
  intro N
  have hindep : iIndepFun (fun n (ω : RouteState) => ω n) (bondLaw p) := by
    exact iIndepFun_infinitePi
      (P := routeLaw p) (X := fun n (x : Fin (width n) → Bool) => x)
      (fun _ => measurable_id)
  have h := hindep.measure_inter_preimage_eq_mul N
    (sets := fun n => ClosedBlock n) (fun _ _ => measurableSet_closedBlock _)
  simpa only [BundleClosed, Set.preimage, bondLaw] using h

/-- Every bundle is crossed. -/
def AllCrossed : Set RouteState := {ω | ∀ n, ∃ i, ω n i = true}

lemma allCrossed_eq_univ_pi : AllCrossed = Set.univ.pi OpenBlock := by
  ext ω
  simp only [AllCrossed, OpenBlock, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    true_implies]

lemma allCrossed_subset_compl_limsup_bundleClosed :
    AllCrossed ⊆ (limsup BundleClosed atTop)ᶜ := by
  intro ω hω hlim
  rw [mem_limsup_iff_frequently_mem, frequently_atTop] at hlim
  obtain ⟨n, _, hn⟩ := hlim 0
  obtain ⟨i, hi⟩ := hω n
  have hfalse : ω n i = false := hn i
  rw [hfalse] at hi
  contradiction

lemma measurableSet_limsup_bundleClosed : MeasurableSet (limsup BundleClosed atTop) := by
  rw [limsup_eq_iInf_iSup_of_nat]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i =>
    MeasurableSet.iUnion fun _ => measurableSet_bundleClosed i

/-- Subcritical and critical bundle laws almost surely have a failed bundle. -/
theorem allCrossed_null_of_le_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    bondLaw p AllCrossed = 0 := by
  apply measure_mono_null allCrossed_subset_compl_limsup_bundleClosed
  have hlim : bondLaw p (limsup BundleClosed atTop) = 1 := by
    apply measure_limsup_eq_one measurableSet_bundleClosed (iIndepSet_bundleClosed p)
    simp_rw [bundleClosed_measure]
    exact tsum_ofReal_bundleFailure_eq_top hp
  rw [measure_compl measurableSet_limsup_bundleClosed (measure_ne_top _ _), hlim,
    measure_univ]
  simp

/-- Crossing precisely the first `N` bundles. -/
def PrefixCrossed (N : ℕ) : Set RouteState :=
  (↑(Finset.range N) : Set ℕ).pi OpenBlock

lemma prefixCrossed_antitone : Antitone PrefixCrossed := by
  intro m n hmn ω hω i hi
  apply hω i
  simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢
  omega

lemma allCrossed_eq_iInter_prefix : AllCrossed = ⋂ n, PrefixCrossed n := by
  ext ω
  simp only [AllCrossed, PrefixCrossed, mem_setOf_eq, mem_iInter, Set.mem_pi,
    Finset.coe_range, mem_Iio]
  constructor
  · intro h N n _; exact h n
  · intro h n; exact h (n + 1) n (Nat.lt_succ_self n)

lemma measurableSet_prefixCrossed (N : ℕ) : MeasurableSet (PrefixCrossed N) :=
  MeasurableSet.pi (Finset.range N).countable_toSet (fun _ _ => measurableSet_openBlock _)

lemma prefixCrossed_measure (p : unitInterval) (N : ℕ) :
    bondLaw p (PrefixCrossed N) =
      ∏ n ∈ Finset.range N, routeLaw p n (OpenBlock n) := by
  exact Measure.infinitePi_pi _ (fun _ _ => measurableSet_openBlock _)

lemma bundleFailure_lt_one {p : unitInterval} (hp0 : 0 < (p : ℝ)) (n : ℕ) :
    bundleFailure p n < 1 := by
  have ha0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have ha1 : 1 - (p : ℝ) < 1 := by linarith
  rw [bundleFailure_eq]
  calc
    (1 - (p : ℝ)) ^ width n ≤ (1 - (p : ℝ)) ^ 1 :=
      pow_le_pow_of_le_one ha0 ha1.le (width_pos n)
    _ = 1 - (p : ℝ) := pow_one _
    _ < 1 := ha1

lemma toReal_openBlock_measure (p : unitInterval) (n : ℕ) :
    (routeLaw p n (OpenBlock n)).toReal = 1 - bundleFailure p n := by
  rw [openBlock_measure]
  have hle : ENNReal.ofReal (bundleFailure p n) ≤ 1 := by
    rw [← closedBlock_measure p n]
    exact prob_le_one
  rw [ENNReal.toReal_sub_of_le hle (by simp)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal (bundleFailure_nonneg p n)]

lemma toReal_prefixCrossed_measure (p : unitInterval) (N : ℕ) :
    (bondLaw p (PrefixCrossed N)).toReal =
      ∏ n ∈ Finset.range N, (1 - bundleFailure p n) := by
  rw [prefixCrossed_measure, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro n _
  exact toReal_openBlock_measure p n

/-- Above `1/2`, all bundles are crossed with positive probability. -/
theorem allCrossed_pos_of_half_lt {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) :
    bondLaw p AllCrossed ≠ 0 := by
  have hs := summable_bundleFailure_of_half_lt hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hfac : ∀ n, 1 + (-bundleFailure p n) ≠ 0 := by
    intro n
    have := bundleFailure_lt_one hp0 n
    linarith
  have hnorm : Summable (fun n => ‖-bundleFailure p n‖) := by
    simpa [Real.norm_of_nonneg (bundleFailure_nonneg p _)] using hs.norm
  have hprod : Multipliable (fun n => 1 - bundleFailure p n) := by
    convert Real.multipliable_one_add_of_summable hs.neg using 1 <;> simp
  have hprod_ne : (∏' n, (1 - bundleFailure p n)) ≠ 0 := by
    convert tprod_one_add_ne_zero_of_summable hfac hnorm using 1 <;> simp
  intro hzero
  have hmeasure : Tendsto (fun N => bondLaw p (PrefixCrossed N)) atTop (𝓝 0) := by
    rw [← hzero, allCrossed_eq_iInter_prefix]
    exact tendsto_measure_iInter_atTop
      (fun n => (measurableSet_prefixCrossed n).nullMeasurableSet)
      prefixCrossed_antitone ⟨0, measure_ne_top _ _⟩
  have hreal0 : Tendsto (fun N => (bondLaw p (PrefixCrossed N)).toReal) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hmeasure
  have hreal : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 - bundleFailure p n)) atTop
      (𝓝 (∏' n, (1 - bundleFailure p n))) := hprod.hasProd.tendsto_prod_nat
  have hreal0' : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 - bundleFailure p n)) atTop
      (𝓝 0) := by
    apply hreal0.congr'
    exact Filter.Eventually.of_forall (fun N => toReal_prefixCrossed_measure p N)
  exact hprod_ne (tendsto_nhds_unique hreal hreal0')

/-! ### The actual connected locally finite route graph -/

/-- A backbone vertex or an internal vertex of one two-edge route. -/
abbrev Vertex := ℕ ⊕ (Σ n : ℕ, Fin (width n))

/-- The index of one random route edge. -/
abbrev Route := Σ n : ℕ, Fin (width n)

/-- The `n`-th vertex on the backbone. -/
def backbone (n : ℕ) : Vertex := Sum.inl n

/-- The internal vertex of route `r`. -/
def middle (r : Route) : Vertex := Sum.inr r

lemma backbone_injective : Function.Injective backbone := by
  intro m n h
  exact Sum.inl.inj h

lemma middle_injective : Function.Injective middle := by
  intro r q h
  exact Sum.inr.inj h

/-- Consecutive bundles of internally disjoint two-edge paths.  The edge from
`backbone r.1` to `middle r` is random, and the edge from `middle r` to
`backbone (r.1+1)` is a deterministic stem. -/
def bundleGraph : SimpleGraph Vertex where
  Adj u v := match u, v with
    | Sum.inl n, Sum.inr r => n = r.1 ∨ n = r.1 + 1
    | Sum.inr r, Sum.inl n => n = r.1 ∨ n = r.1 + 1
    | _, _ => False
  symm := ⟨by
    rintro (n | r) (m | q) h <;> simp_all [or_comm]⟩
  loopless := ⟨by
    rintro (n | r) h <;> simp_all⟩

/-- The random first edge of route `r`. -/
def routeEdge (r : Route) : bundleGraph.edgeSet :=
  ⟨s(backbone r.1, middle r), Or.inl rfl⟩

/-- The deterministically open second edge of route `r`. -/
def stemEdge (r : Route) : bundleGraph.edgeSet :=
  ⟨s(middle r, backbone (r.1 + 1)), Or.inr rfl⟩

@[simp] lemma routeEdge_apply (r : Route) :
    (routeEdge r : Sym2 Vertex) = s(backbone r.1, middle r) := rfl

@[simp] lemma stemEdge_apply (r : Route) :
    (stemEdge r : Sym2 Vertex) = s(middle r, backbone (r.1 + 1)) := rfl

lemma routeEdge_injective : Function.Injective routeEdge := by
  intro r q h
  have h' := congrArg Subtype.val h
  rw [routeEdge_apply, routeEdge_apply, Sym2.eq_iff] at h'
  rcases h' with h' | h'
  · exact middle_injective h'.2
  · simp [backbone, middle] at h'

lemma stemEdge_injective : Function.Injective stemEdge := by
  intro r q h
  have h' := congrArg Subtype.val h
  rw [stemEdge_apply, stemEdge_apply, Sym2.eq_iff] at h'
  rcases h' with h' | h'
  · exact middle_injective h'.1
  · simp [backbone, middle] at h'

lemma routeEdge_ne_stemEdge (r q : Route) : routeEdge r ≠ stemEdge q := by
  intro h
  have h' := congrArg Subtype.val h
  rw [routeEdge_apply, stemEdge_apply, Sym2.eq_iff] at h'
  rcases h' with h' | h'
  · simp [backbone, middle] at h'
  · have hr : r = q := middle_injective h'.2
    have hn : r.1 = q.1 + 1 := backbone_injective h'.1
    subst q
    omega

lemma backbone_reachable (n : ℕ) : bundleGraph.Reachable (backbone 0) (backbone n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let r : Route := ⟨n, ⟨0, width_pos n⟩⟩
      exact ih.trans ((show bundleGraph.Adj (backbone n) (middle r) from Or.inl rfl).reachable.trans
        (show bundleGraph.Adj (middle r) (backbone (n + 1)) from Or.inr rfl).reachable)

lemma bundleGraph_connected : bundleGraph.Connected := by
  apply bundleGraph.connected_iff_exists_forall_reachable.2
  refine ⟨backbone 0, ?_⟩
  rintro (n | r)
  · exact backbone_reachable n
  · exact (backbone_reachable r.1).trans
      (show bundleGraph.Adj (backbone r.1) (middle r) from Or.inl rfl).reachable

/-- Each backbone vertex meets only the routes in its two adjacent bundles;
each internal route vertex has exactly two neighbours. -/
noncomputable instance bundleGraphLocallyFinite : bundleGraph.LocallyFinite := by
  intro v
  cases v with
  | inl n =>
      apply Set.Finite.fintype
      apply ((Set.finite_range (fun i : Fin (width n) => middle ⟨n, i⟩)).union
        (Set.finite_range (fun i : Fin (width (n - 1)) => middle ⟨n - 1, i⟩))).subset
      intro w hw
      cases w with
      | inl m => exact (show False from hw).elim
      | inr r =>
          change n = r.1 ∨ n = r.1 + 1 at hw
          rcases hw with h | h
          · apply Or.inl
            subst n
            exact ⟨r.2, rfl⟩
          · apply Or.inr
            have hn : n - 1 = r.1 := by omega
            rw [hn]
            exact ⟨r.2, rfl⟩
  | inr r =>
      apply Set.Finite.fintype
      apply ((Set.finite_singleton (backbone (r.1 + 1))).insert (backbone r.1)).subset
      intro w hw
      cases w with
      | inl n =>
          change n = r.1 ∨ n = r.1 + 1 at hw
          rcases hw with h | h
          · subst n
            simp [backbone]
          · subst n
            simp [backbone]
      | inr q => exact (show False from hw).elim

/-- The graph configuration with all stem edges deterministically open. -/
noncomputable def graphConfig (ω : RouteState) : bundleGraph.edgeSet → Bool :=
  fun e => if h : ∃ r, routeEdge r = e then
    ω (Classical.choose h).1 (Classical.choose h).2 else true

@[simp] lemma graphConfig_routeEdge (ω : RouteState) (r : Route) :
    graphConfig ω (routeEdge r) = ω r.1 r.2 := by
  have h : ∃ q, routeEdge q = routeEdge r := ⟨r, rfl⟩
  rw [graphConfig, dif_pos h]
  have hq : Classical.choose h = r := routeEdge_injective (Classical.choose_spec h)
  rw [hq]

@[simp] lemma graphConfig_stemEdge (ω : RouteState) (r : Route) :
    graphConfig ω (stemEdge r) = true := by
  rw [graphConfig, dif_neg]
  rintro ⟨q, hq⟩
  exact routeEdge_ne_stemEdge q r hq

lemma measurable_graphConfig : Measurable graphConfig := by
  apply measurable_pi_iff.2
  intro e
  unfold graphConfig
  split
  · fun_prop
  · exact measurable_const

/-- The actual infinite open-cluster event at the first backbone vertex. -/
def RootPercolates : Set (bundleGraph.edgeSet → Bool) :=
  {η | {x | OpenConnected bundleGraph η Set.univ (backbone 0) x}.Infinite}

lemma measurableSet_rootPercolates : MeasurableSet RootPercolates := by
  rw [RootPercolates, setOf_infinite_eq_iInter_armEvent bundleGraph_connected (backbone 0)]
  exact MeasurableSet.iInter fun n => measurableSet_armEvent (backbone 0) n

lemma openConnected_backbone (ω : RouteState) (hω : ω ∈ AllCrossed) (n : ℕ) :
    OpenConnected bundleGraph (graphConfig ω) Set.univ (backbone 0) (backbone n) := by
  induction n with
  | zero => exact OpenConnected.refl _ _ _
  | succ n ih =>
      obtain ⟨i, hi⟩ := hω n
      let r : Route := ⟨n, i⟩
      have h₁ : OpenConnected bundleGraph (graphConfig ω) Set.univ
          (backbone n) (middle r) := by
        apply OpenConnected.of_adj (show bundleGraph.Adj (backbone n) (middle r) from Or.inl rfl)
          (Set.mem_univ _)
        change graphConfig ω (routeEdge r) = true
        rw [graphConfig_routeEdge]
        exact hi
      have h₂ : OpenConnected bundleGraph (graphConfig ω) Set.univ
          (middle r) (backbone (n + 1)) := by
        apply OpenConnected.of_adj
          (show bundleGraph.Adj (middle r) (backbone (n + 1)) from Or.inr rfl)
          (Set.mem_univ _)
        exact graphConfig_stemEdge ω r
      exact ih.trans (h₁.trans h₂)

/-- Crossing every bundle puts the infinite backbone in the root's open cluster. -/
lemma allCrossed_rootPercolates {ω : RouteState} (hω : ω ∈ AllCrossed) :
    graphConfig ω ∈ RootPercolates := by
  change {x | OpenConnected bundleGraph (graphConfig ω) Set.univ (backbone 0) x}.Infinite
  apply (Set.infinite_range_of_injective backbone_injective).mono
  rintro x ⟨n, rfl⟩
  exact openConnected_backbone ω hω n

/-- If bundle `N` is shut, every open path from the root stays in one of the
first `N` bundles or on the first `N+1` backbone vertices. -/
lemma reachable_bounds_of_bundleClosed {ω : RouteState} {N : ℕ} {x : Vertex}
    (hclosed : ∀ i, ω N i = false)
    (hx : OpenConnected bundleGraph (graphConfig ω) Set.univ (backbone 0) x) :
    (∃ k ≤ N, x = backbone k) ∨ (∃ r : Route, r.1 < N ∧ x = middle r) := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
  | @tail a b hx hab ih =>
      rw [openGraph, SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨⟨e, he, hee⟩, -⟩ := hab
      have hG : bundleGraph.Adj a b := by
        have he' := e.property
        rw [hee] at he'
        exact he'
      have hω : graphConfig ω ⟨s(a, b), hG⟩ = true := by
        have heq : e = ⟨s(a, b), hG⟩ := Subtype.ext hee
        rw [← heq]
        exact he
      cases a with
      | inl n =>
          cases b with
          | inl m => exact (show False from hG).elim
          | inr r =>
              change n = r.1 ∨ n = r.1 + 1 at hG
              have hn : n ≤ N := by
                rcases ih with ⟨k, hk, hak⟩ | ⟨q, hq, haq⟩
                · have hnk : n = k := backbone_injective hak
                  omega
                · simp [backbone, middle] at haq
              rcases hG with hnr | hnr
              · subst n
                apply Or.inr
                refine ⟨r, ?_, rfl⟩
                have hrN : r.1 ≠ N := by
                  intro h
                  change graphConfig ω (routeEdge r) = true at hω
                  subst N
                  rw [graphConfig_routeEdge, hclosed r.2] at hω
                  contradiction
                omega
              · exact Or.inr ⟨r, by omega, rfl⟩
      | inr r =>
          cases b with
          | inl n =>
              change n = r.1 ∨ n = r.1 + 1 at hG
              have hrN : r.1 < N := by
                rcases ih with ⟨k, hk, hak⟩ | ⟨q, hq, haq⟩
                · simp [backbone, middle] at hak
                · have hrq : r = q := middle_injective haq
                  subst q
                  exact hq
              exact Or.inl ⟨n, by omega, rfl⟩
          | inr q => exact (show False from hG).elim

lemma root_cluster_finite_of_bundleClosed {ω : RouteState} {N : ℕ}
    (hclosed : ∀ i, ω N i = false) :
    {x | OpenConnected bundleGraph (graphConfig ω) Set.univ (backbone 0) x}.Finite := by
  let B : Set Vertex :=
    Set.range (fun k : Fin (N + 1) => backbone (k : ℕ)) ∪
      Set.range (fun r : Σ k : Fin N, Fin (width (k : ℕ)) => middle ⟨r.1.1, r.2⟩)
  have hB : B.Finite := (Set.finite_range _).union (Set.finite_range _)
  apply hB.subset
  intro x hx
  rcases reachable_bounds_of_bundleClosed hclosed hx with ⟨k, hk, rfl⟩ | ⟨r, hr, rfl⟩
  · exact Or.inl ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
  · exact Or.inr ⟨⟨⟨r.1, hr⟩, r.2⟩, rfl⟩

/-- Conversely, an infinite root cluster forces every bundle to be crossed. -/
lemma rootPercolates_allCrossed {ω : RouteState} (hω : graphConfig ω ∈ RootPercolates) :
    ω ∈ AllCrossed := by
  by_contra h
  change ¬ ∀ n, ∃ i, ω n i = true at h
  push_neg at h
  obtain ⟨N, hN⟩ := h
  have hclosed : ∀ i, ω N i = false := by
    intro i
    cases hi : ω N i with
    | false => rfl
    | true => exact (hN i hi).elim
  exact hω (root_cluster_finite_of_bundleClosed hclosed)

lemma graphConfig_preimage_rootPercolates :
    graphConfig ⁻¹' RootPercolates = AllCrossed := by
  ext ω
  exact ⟨rootPercolates_allCrossed, allCrossed_rootPercolates⟩

lemma measurableSet_allCrossed : MeasurableSet AllCrossed := by
  rw [← graphConfig_preimage_rootPercolates]
  exact measurable_graphConfig measurableSet_rootPercolates

/-! ### Independent single-edge activations and exact OR marginals -/

/-- Each route has an independent bond/activation pair. -/
abbrev JointRouteState := ∀ n : ℕ, (Fin (width n) → Bool × Bool)

/-- The independent paired law within one bundle. -/
noncomputable def pairedRouteLaw (p s : unitInterval) (n : ℕ) :
    Measure (Fin (width n) → Bool × Bool) :=
  Measure.infinitePi fun _ => (bernoulliMeasure true false p).prod (bernoulliMeasure true false s)

instance (p s : unitInterval) (n : ℕ) : IsProbabilityMeasure (pairedRouteLaw p s n) := by
  unfold pairedRouteLaw
  infer_instance

/-- The normalized independent bond/activation product over all routes. -/
noncomputable def jointRouteLaw (p s : unitInterval) : Measure JointRouteState :=
  Measure.infinitePi (pairedRouteLaw p s)

instance (p s : unitInterval) : IsProbabilityMeasure (jointRouteLaw p s) := by
  unfold jointRouteLaw
  infer_instance

/-- Apply the local OR independently at every random route edge. -/
def routeOr (χ : JointRouteState) : RouteState :=
  fun n i => (χ n i).1 || (χ n i).2

lemma measurable_routeOr : Measurable routeOr := by
  apply measurable_pi_iff.2
  intro n
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun χ : JointRouteState => (χ n i).1 || (χ n i).2)
  fun_prop

/-- Within a bundle, the local OR has exactly the normalized effective-rate law. -/
theorem pairedRouteLaw_map_routeOr (p s : unitInterval) (n : ℕ) :
    (pairedRouteLaw p s n).map (fun x i => (x i).1 || (x i).2) =
      routeLaw (orUnit p s) n := by
  unfold pairedRouteLaw routeLaw
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : Fin (width n) =>
      (bernoulliMeasure true false p).prod (bernoulliMeasure true false s))
    (f := fun _ (x : Bool × Bool) => x.1 || x.2) (fun _ => by fun_prop)]
  congr 1
  funext i
  exact AGGadget.prod_bernoulliMeasure_map_or p s

/-- The actual joint independent product has exactly the handoff's bond product
at `orUnit p s` as its OR marginal. -/
theorem jointRouteLaw_map_routeOr (p s : unitInterval) :
    (jointRouteLaw p s).map routeOr = bondLaw (orUnit p s) := by
  unfold jointRouteLaw routeOr bondLaw
  rw [Measure.infinitePi_map_pi (μ := pairedRouteLaw p s)
    (f := fun n (x : Fin (width n) → Bool × Bool) => fun i => (x i).1 || (x i).2)
    (fun n => by
      apply measurable_pi_iff.2
      intro i
      fun_prop)]
  congr 1
  funext n
  exact pairedRouteLaw_map_routeOr p s n

/-- The ordinary law on all graph edges: independent route bits and open stems. -/
noncomputable def graphBondLaw (p : unitInterval) : Measure (bundleGraph.edgeSet → Bool) :=
  (bondLaw p).map graphConfig

instance (p : unitInterval) : IsProbabilityMeasure (graphBondLaw p) where
  measure_univ := by
    rw [graphBondLaw, Measure.map_apply measurable_graphConfig MeasurableSet.univ]
    simp

/-- The enhanced law on graph edges induced by all local OR operations. -/
noncomputable def graphJointLaw (p s : unitInterval) : Measure (bundleGraph.edgeSet → Bool) :=
  (jointRouteLaw p s).map (graphConfig ∘ routeOr)

lemma measurable_graphConfig_comp_routeOr : Measurable (graphConfig ∘ routeOr) :=
  measurable_graphConfig.comp measurable_routeOr

instance (p s : unitInterval) : IsProbabilityMeasure (graphJointLaw p s) where
  measure_univ := by
    rw [graphJointLaw, Measure.map_apply measurable_graphConfig_comp_routeOr MeasurableSet.univ]
    simp

theorem graphBondLaw_rootPercolates (p : unitInterval) :
    graphBondLaw p RootPercolates = bondLaw p AllCrossed := by
  rw [graphBondLaw, Measure.map_apply measurable_graphConfig measurableSet_rootPercolates,
    graphConfig_preimage_rootPercolates]

theorem graphJointLaw_rootPercolates (p s : unitInterval) :
    graphJointLaw p s RootPercolates = bondLaw (orUnit p s) AllCrossed := by
  rw [graphJointLaw,
    Measure.map_apply measurable_graphConfig_comp_routeOr measurableSet_rootPercolates]
  change jointRouteLaw p s (routeOr ⁻¹' (graphConfig ⁻¹' RootPercolates)) = _
  rw [graphConfig_preimage_rootPercolates,
    ← Measure.map_apply measurable_routeOr measurableSet_allCrossed,
    jointRouteLaw_map_routeOr]

theorem base_rootPercolates_null_of_le_half {p : unitInterval} (hp : (p : ℝ) ≤ 1 / 2) :
    graphBondLaw p RootPercolates = 0 := by
  rw [graphBondLaw_rootPercolates]
  exact allCrossed_null_of_le_half p hp

theorem base_rootPercolates_pos_of_half_lt {p : unitInterval} (hp : 1 / 2 < (p : ℝ)) :
    graphBondLaw p RootPercolates ≠ 0 := by
  rw [graphBondLaw_rootPercolates]
  exact allCrossed_pos_of_half_lt hp

/-! ### Exact base and enhanced critical parameters -/

/-- Critical point of a real-valued family of percolation probabilities, using
the same `sSup` convention as the repository's `criticalProb`. -/
noncomputable def criticalParameter (θ : unitInterval → ℝ≥0∞) : ℝ :=
  sSup (Subtype.val '' {p : unitInterval | θ p = 0})

lemma criticalParameter_eq_of_threshold {θ : unitInterval → ℝ≥0∞} {c : unitInterval}
    (hzero : ∀ p : unitInterval, (p : ℝ) ≤ (c : ℝ) → θ p = 0)
    (hpos : ∀ p : unitInterval, (c : ℝ) < (p : ℝ) → θ p ≠ 0) :
    criticalParameter θ = (c : ℝ) := by
  apply le_antisymm
  · unfold criticalParameter
    apply Real.sSup_le
    rintro x ⟨p, hp, rfl⟩
    by_contra hpc
    exact hpos p (lt_of_not_ge hpc) hp
    exact c.property.1
  · unfold criticalParameter
    exact le_sSup_image_val (hzero c le_rfl)

noncomputable def half : unitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩
noncomputable def quarter : unitInterval := ⟨(1 / 4 : ℝ), by norm_num⟩
noncomputable def third : unitInterval := ⟨(1 / 3 : ℝ), by norm_num⟩

@[simp] lemma coe_half : (half : ℝ) = 1 / 2 := rfl
@[simp] lemma coe_quarter : (quarter : ℝ) = 1 / 4 := rfl
@[simp] lemma coe_third : (third : ℝ) = 1 / 3 := rfl

noncomputable def basePercolationProb (p : unitInterval) : ℝ≥0∞ :=
  graphBondLaw p RootPercolates

noncomputable def enhancedPercolationProb (s p : unitInterval) : ℝ≥0∞ :=
  graphJointLaw p s RootPercolates

noncomputable def baseCritical : ℝ := criticalParameter basePercolationProb

noncomputable def enhancedCritical (s : unitInterval) : ℝ :=
  criticalParameter (enhancedPercolationProb s)

theorem basePercolationProb_eq_bundle (p : unitInterval) :
    basePercolationProb p = bondLaw p AllCrossed := graphBondLaw_rootPercolates p

theorem enhancedPercolationProb_eq_bundle (p s : unitInterval) :
    enhancedPercolationProb s p = bondLaw (orUnit p s) AllCrossed :=
  graphJointLaw_rootPercolates p s

/-- The ordinary route graph has exact critical parameter `1/2`. -/
theorem baseCritical_eq_half : baseCritical = 1 / 2 := by
  unfold baseCritical
  apply criticalParameter_eq_of_threshold (c := half)
  · intro p hp
    rw [basePercolationProb_eq_bundle]
    exact allCrossed_null_of_le_half p (by simpa using hp)
  · intro p hp
    rw [basePercolationProb_eq_bundle]
    exact allCrossed_pos_of_half_lt (by simpa using hp)

/-- With independent activation rate `1/4` on every random route edge, the
enhanced critical parameter is exactly `1/3`. -/
theorem enhancedCritical_quarter_eq_third : enhancedCritical quarter = 1 / 3 := by
  unfold enhancedCritical
  apply criticalParameter_eq_of_threshold (c := third)
  · intro p hp
    change (p : ℝ) ≤ 1 / 3 at hp
    rw [enhancedPercolationProb_eq_bundle]
    apply allCrossed_null_of_le_half
    simp only [AGGadget.coe_orUnit, AGGadget.orRate, coe_quarter]
    nlinarith
  · intro p hp
    change 1 / 3 < (p : ℝ) at hp
    rw [enhancedPercolationProb_eq_bundle]
    apply allCrossed_pos_of_half_lt
    simp only [AGGadget.coe_orUnit, AGGadget.orRate, coe_quarter]
    nlinarith

/-- A normalized strict critical shift on the connected locally finite graph,
using only independent activations whose range is one edge. -/
theorem strict_critical_shift_quarter : enhancedCritical quarter < baseCritical := by
  rw [baseCritical_eq_half, enhancedCritical_quarter_eq_third]
  norm_num

end FK.AGBoundedRangeBundleShift

#print axioms FK.AGBoundedRangeBundleShift.allCrossed_null_of_le_half
#print axioms FK.AGBoundedRangeBundleShift.allCrossed_pos_of_half_lt
#print axioms FK.AGBoundedRangeBundleShift.bundleGraph_connected
#print axioms FK.AGBoundedRangeBundleShift.bundleGraphLocallyFinite
#print axioms FK.AGBoundedRangeBundleShift.graphConfig_preimage_rootPercolates
#print axioms FK.AGBoundedRangeBundleShift.pairedRouteLaw_map_routeOr
#print axioms FK.AGBoundedRangeBundleShift.jointRouteLaw_map_routeOr
#print axioms FK.AGBoundedRangeBundleShift.graphBondLaw_rootPercolates
#print axioms FK.AGBoundedRangeBundleShift.graphJointLaw_rootPercolates
#print axioms FK.AGBoundedRangeBundleShift.base_rootPercolates_null_of_le_half
#print axioms FK.AGBoundedRangeBundleShift.base_rootPercolates_pos_of_half_lt
#print axioms FK.AGBoundedRangeBundleShift.baseCritical_eq_half
#print axioms FK.AGBoundedRangeBundleShift.enhancedCritical_quarter_eq_third
#print axioms FK.AGBoundedRangeBundleShift.strict_critical_shift_quarter
