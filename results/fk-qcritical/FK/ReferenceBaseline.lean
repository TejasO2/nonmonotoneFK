/-
Worker m2 contribution, formalization of arXiv:2512.16486.

# The supercritical baseline for the Bernoulli reference model

The paper (Section 1.1) uses the following classical fact about the `q = 1`
reference model: *on any infinite graph `G` there is a critical parameter
`p_c(G) ∈ [0,1]` above which Bernoulli bond percolation has almost surely an
infinite cluster, and below which almost surely every cluster is finite.*

This file proves that fact, in the source's own convention
`p_c = criticalProb G o = sup {p : θ_o(p) = 0}`, for the actual ordinary
percolation event of the `q = 1` model on a connected locally finite graph `G`
(Mathlib `SimpleGraph`, open edges `ω : G.edgeSet → Bool` with `ω e = true`
meaning `e` is open), and discharges the supercritical/subcritical base
hypotheses of the AG machinery of `FK.AGDifferentialShift` for that event.

Main results, in increasing strength:

* `percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt` (no connectivity
  needed): `criticalProb G o < p → μ_p (HasInfiniteCluster) = 1`.  The positive
  direction, which no module of the repository previously supplied: `θ_o(p) > 0`
  comes straight from the supremum definition and the Kolmogorov zero–one law
  `FK.ClusterTail.percolation_hasInfiniteCluster_zero_one` upgrades it to `1`.
* `percolation_hasInfiniteCluster_eq_zero_of_lt_criticalProb` (connected locally
  finite `G`): `p < criticalProb G o → μ_p (HasInfiniteCluster) = 0`, hence
  `percolation_hasInfiniteCluster_eq_one_iff_of_ne`: away from `p_c`, the model
  percolates a.s. exactly above `p_c`.  The bridge from the root cluster to the
  event is `percolation_hasInfiniteCluster_eq_zero_iff_forall`
  (`μ_p = 0 ↔ ∀ x, θ_x(p) = 0`, a countable union) plus the single-coordinate
  Harris/FKG comparison `ofReal_mul_percolationProb_le` (`θ_x ≥ p·θ_y` for
  adjacent `x`, `y`), proved from the product structure without invoking FKG.
* `clusterCriticalProb` is the same critical parameter defined by the event,
  `sup {p : μ_p (HasInfiniteCluster) = 0}`; it satisfies
  `clusterCriticalProb_eq_criticalProb` on connected graphs, carries both halves
  of the dichotomy without any connectivity hypothesis, and
  `clusterCriticalProb_eq_sSup_forall` identifies it as `sup {p : ∀ x, θ_x(p) = 0}`.
* `incMass_hasInfiniteCluster_eq_one` / `_of_nonneg` and
  `mass_hasInfiniteCluster_eq_zero`: the base hypotheses `hbase` of
  `FK.AGDifferentialShift` (supercritical increment, subcritical decrement) for
  the actual percolation event and an arbitrary enhanced edge set, `ε = 0` and
  `ε > 0` alike.
* `lowerWindow_hasInfiniteCluster_q_lt_one` /
  `upperWindow_hasInfiniteCluster_q_lt_one`: the AG differential-trade windows
  with those base inputs removed at `pc = criticalProb G o`, leaving only the
  pivot-trade data `L`, `hderiv`, `htrade` and the convergence `hconv`.
* `ae_hasInfiniteCluster_*`: the source's "almost surely" phrasing.

Nothing outside `FK.ClusterTail`, `FK.AGDifferentialShift`, `FK.StrongUniqueness`
and `FK.SubcriticalPercolation` is imported, and no quasi-transitivity,
amenability or sharpness input is used anywhere.
-/
import FK.ClusterTail
import FK.AGDifferentialShift
import FK.StrongUniqueness
import FK.SubcriticalPercolation

open MeasureTheory ProbabilityTheory Filter
open Classical
open scoped ENNReal NNReal unitInterval Topology

set_option linter.unusedSectionVars false

namespace FK.ReferenceBaseline

open CurvatureVariance.Infra.Percolation FK.ClusterCover

variable {V : Type*} [Countable V]

/-! ### The percolation event above the root critical parameter -/

/-- Above `p_c` the root cluster is infinite with positive probability.  This is
the defining property of `p_c = sup {p : θ(p) = 0}`; no monotonicity in `p` is
involved. -/
theorem percolationProb_ne_zero_of_criticalProb_lt (G : SimpleGraph V) (o : V) {p : I}
    (hp : criticalProb G o < (p : ℝ)) : percolationProb G o p ≠ 0 := by
  intro h0
  have hmem : p ∈ {p : I | percolationProb G o p = 0} := h0
  have hle : (p : ℝ) ≤ criticalProb G o := le_sSup_image_val hmem
  linarith

/-- The same, in positive form. -/
theorem percolationProb_pos_of_criticalProb_lt (G : SimpleGraph V) (o : V) {p : I}
    (hp : criticalProb G o < (p : ℝ)) : 0 < percolationProb G o p :=
  pos_iff_ne_zero.mpr (percolationProb_ne_zero_of_criticalProb_lt G o hp)

/-- **Supercritical baseline.**  Above `p_c(G)` it is almost sure that some open
cluster is infinite. -/
theorem percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt (G : SimpleGraph V)
    (o : V) {p : I} (hp : criticalProb G o < (p : ℝ)) :
    percolation G p {ω | HasInfiniteCluster G ω} = 1 := by
  have hmono : percolation G p {ω | {x | OpenConnected G ω Set.univ o x}.Infinite} ≤
      percolation G p {ω | HasInfiniteCluster G ω} := by
    apply measure_mono
    intro ω hω
    exact ⟨o, by rwa [clusterAvoid_empty_eq]⟩
  have hpos : 0 < percolation G p {ω | HasInfiniteCluster G ω} := by
    refine lt_of_lt_of_le ?_ hmono
    rw [← percolationProb_eq]
    exact percolationProb_pos_of_criticalProb_lt G o hp
  rcases FK.ClusterTail.percolation_hasInfiniteCluster_zero_one G p with h | h
  · exact absurd h hpos.ne'
  · exact h

/-! ### The critical parameter of the percolation event -/

/-- The critical parameter of the reference model, defined by the a.s. existence
of an infinite cluster: `sup {p : P_p (HasInfiniteCluster) = 0}`.  This is the
convention of the source's Section 1.1 sentence. -/
noncomputable def clusterCriticalProb (G : SimpleGraph V) : ℝ :=
  sSup (Subtype.val '' {p : I | percolation G p {ω | HasInfiniteCluster G ω} = 0})

theorem clusterCriticalProb_nonneg (G : SimpleGraph V) : 0 ≤ clusterCriticalProb G :=
  sSup_image_val_nonneg _

theorem clusterCriticalProb_le_one (G : SimpleGraph V) : clusterCriticalProb G ≤ 1 :=
  sSup_image_val_le_one _

/-- The root convention lies above the percolation-event convention, since a
nonpercolating law has every root cluster finite. -/
theorem clusterCriticalProb_le_criticalProb (G : SimpleGraph V) (o : V) :
    clusterCriticalProb G ≤ criticalProb G o := by
  rw [clusterCriticalProb, criticalProb]
  by_cases hne : (Subtype.val '' {p : I | percolation G p {ω | HasInfiniteCluster G ω} = 0}).Nonempty
  · refine csSup_le hne ?_
    rintro x ⟨p, hp, rfl⟩
    have hθ : percolationProb G o p = 0 := by
      rw [percolationProb_eq]
      refine measure_mono_null ?_ hp
      intro ω hω
      exact ⟨o, by rwa [clusterAvoid_empty_eq]⟩
    exact le_sSup_image_val hθ
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact sSup_image_val_nonneg _

/-- Above `clusterCriticalProb` the event "some cluster is infinite" has positive
probability. -/
theorem percolation_hasInfiniteCluster_ne_zero_of_lt_clusterCriticalProb
    (G : SimpleGraph V) {p : I} (hp : clusterCriticalProb G < (p : ℝ)) :
    percolation G p {ω | HasInfiniteCluster G ω} ≠ 0 := by
  intro h0
  have hmem : p ∈ {p : I | percolation G p {ω | HasInfiniteCluster G ω} = 0} := h0
  have hle : (p : ℝ) ≤ clusterCriticalProb G := le_sSup_image_val hmem
  linarith

/-- **Supercritical half of the source dichotomy**, in the percolation-event
convention: above `clusterCriticalProb` there is almost surely an infinite
cluster. -/
theorem percolation_hasInfiniteCluster_eq_one_of_lt_clusterCriticalProb
    (G : SimpleGraph V) {p : I} (hp : clusterCriticalProb G < (p : ℝ)) :
    percolation G p {ω | HasInfiniteCluster G ω} = 1 := by
  have hne := percolation_hasInfiniteCluster_ne_zero_of_lt_clusterCriticalProb G hp
  rcases FK.ClusterTail.percolation_hasInfiniteCluster_zero_one G p with h | h
  · exact absurd h hne
  · exact h

/-- **Subcritical half of the source dichotomy**: below `clusterCriticalProb`
almost surely every open cluster is finite.  The proof is the monotone coupling
in the parameter (pointwise domination of the cylinder weights) together with
the definition of the critical parameter as a supremum. -/
theorem percolation_hasInfiniteCluster_eq_zero_of_lt_clusterCriticalProb
    (G : SimpleGraph V) {b : I} (hb : (b : ℝ) < clusterCriticalProb G) :
    percolation G b {ω | HasInfiniteCluster G ω} = 0 := by
  classical
  have hne : (Subtype.val '' {p : I | percolation G p {ω | HasInfiniteCluster G ω} = 0}).Nonempty := by
    rcases Set.eq_empty_or_nonempty
      (Subtype.val '' {p : I | percolation G p {ω | HasInfiniteCluster G ω} = 0}) with he | h
    · exfalso
      have hzero : clusterCriticalProb G = 0 := by
        rw [clusterCriticalProb, he, Real.sSup_empty]
      rw [hzero] at hb
      exact absurd hb (not_lt.mpr b.2.1)
    · exact h
  obtain ⟨x, ⟨q, hqS, rfl⟩, hbq⟩ :=
    exists_lt_of_lt_csSup hne (show (b : ℝ) < sSup (Subtype.val ''
      {p : I | percolation G p {ω | HasInfiniteCluster G ω} = 0}) from hb)
  have hbq' : b ≤ q := le_of_lt (Subtype.coe_lt_coe.mp hbq)
  have hq0 : (FKLimit.bernoulliProduct (fun _ : G.edgeSet => q) :
      Measure (G.edgeSet → Bool)) {ω | HasInfiniteCluster G ω} = 0 := hqS
  have hdom : FKLimit.StochasticallyDominates
      (FKLimit.bernoulliProduct (fun _ : G.edgeSet => q))
      (FKLimit.bernoulliProduct (fun _ : G.edgeSet => b)) :=
    FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
      (r := fun _ : G.edgeSet => b) (s := fun _ : G.edgeSet => q) (fun _ => hbq')
  have := FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates hdom
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G)
    (FK.ClusterTail.isUpperSet_hasInfiniteCluster G) hq0
  exact this

/-! ### The `hbase` inputs of `FK.AGDifferentialShift` -/

/-- The increment profile with decrement `0` is constant: the enhancement set is
invisible at `ε = 0`. -/
theorem decrementWeight_zero {E : Type*} (S : Set E) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    FK.AGDifferentialShift.decrementWeight S a 0 = fun _ : E => (⟨a, ha0, ha1⟩ : I) := by
  funext e
  apply Subtype.ext
  simp only [FK.AGDifferentialShift.decrementWeight, sub_zero]
  rw [ite_self, min_eq_right ha1, max_eq_right ha0]

/-- **The supercritical `hbase` of `FK.AGDifferentialShift`** for the actual
ordinary percolation event: at `ε = 0` the increment profile is the plain
Bernoulli law, so above `p_c` the event has full mass. -/
theorem incMass_hasInfiniteCluster_eq_one (G : SimpleGraph V) (o : V)
    (S : Set G.edgeSet) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hpc : criticalProb G o < a) :
    FK.AGDifferentialShift.incMass
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} S a 0 = 1 := by
  have hp : criticalProb G o < ((⟨a, ha0, ha1⟩ : I) : ℝ) := hpc
  have hfull := percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt G o hp
  rw [FK.AGDifferentialShift.incMass_zero, FK.AGDifferentialShift.mass,
    decrementWeight_zero S ha0 ha1]
  have hb : (FKLimit.bernoulliProduct (fun _ : G.edgeSet => (⟨a, ha0, ha1⟩ : I)) :
      Measure (G.edgeSet → Bool)) {ω | HasInfiniteCluster G ω} = 1 := hfull
  rw [hb]
  simp

/-- The same with the percolation-event convention for the critical parameter. -/
theorem incMass_hasInfiniteCluster_eq_one_of_clusterCriticalProb_lt (G : SimpleGraph V)
    (S : Set G.edgeSet) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hpc : clusterCriticalProb G < a) :
    FK.AGDifferentialShift.incMass
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} S a 0 = 1 := by
  have hp : clusterCriticalProb G < ((⟨a, ha0, ha1⟩ : I) : ℝ) := hpc
  have hfull := percolation_hasInfiniteCluster_eq_one_of_lt_clusterCriticalProb G hp
  rw [FK.AGDifferentialShift.incMass_zero, FK.AGDifferentialShift.mass,
    decrementWeight_zero S ha0 ha1]
  have hb : (FKLimit.bernoulliProduct (fun _ : G.edgeSet => (⟨a, ha0, ha1⟩ : I)) :
      Measure (G.edgeSet → Bool)) {ω | HasInfiniteCluster G ω} = 1 := hfull
  rw [hb]
  simp

/-! ### The complementary event `NonPercolating` -/

/-- The percolation event of `FK.ClusterTail` is the complement of the
non-percolation event `FK.NonPercolating` used elsewhere in the project. -/
theorem hasInfiniteCluster_iff_not_mem_nonPercolating (G : SimpleGraph V)
    (ω : G.edgeSet → Bool) :
    HasInfiniteCluster G ω ↔ ω ∉ FK.NonPercolating G := by
  constructor
  · rintro ⟨x, hx⟩ hx'
    rw [clusterAvoid_empty_eq] at hx
    exact hx (hx' x)
  · intro h
    by_contra hc
    refine h (fun o => ?_)
    rw [← clusterAvoid_empty_eq]
    exact Set.not_infinite.mp fun hinf => hc ⟨o, hinf⟩

/-- The supercritical baseline in the `NonPercolating` language. -/
theorem percolation_nonPercolating_eq_zero_of_criticalProb_lt (G : SimpleGraph V) (o : V)
    {p : I} (hp : criticalProb G o < (p : ℝ)) :
    percolation G p (FK.NonPercolating G) = 0 := by
  have hfull := percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt G o hp
  have hcompl : FK.NonPercolating G = {ω : G.edgeSet → Bool | HasInfiniteCluster G ω}ᶜ := by
    ext ω
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq, hasInfiniteCluster_iff_not_mem_nonPercolating]
    simp
  rw [hcompl, measure_compl (FK.ClusterTail.measurableSet_hasInfiniteCluster G)
    (measure_ne_top _ _), hfull]
  simp

/-! ### Pointwise comparisons of the AG profiles with the plain Bernoulli law -/

/-- The decrement profile is pointwise below the plain Bernoulli law at its base. -/
theorem decrementWeight_le_const {E : Type*} (S : Set E) {b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hε0 : 0 ≤ ε) :
    FK.AGDifferentialShift.decrementWeight S b ε ≤ fun _ : E => (⟨b, hb0, hb1⟩ : I) := by
  classical
  intro e
  show ((max 0 (min 1 (if e ∈ S then b - ε else b)) : ℝ)) ≤ b
  by_cases hmem : e ∈ S
  · simp only [hmem, ite_true]
    have h2 : min 1 (b - ε) ≤ b := le_trans (min_le_right _ _) (by linarith)
    calc max 0 (min 1 (b - ε)) ≤ max b b := max_le_max hb0 h2
      _ = b := max_self b
  · simp only [hmem, ite_false]
    calc max 0 (min 1 b) ≤ max b b := max_le_max hb0 (min_le_right _ _)
      _ = b := max_self b

/-- The plain Bernoulli law at the increment base is pointwise below the increment profile. -/
theorem const_le_incrementWeight {E : Type*} (S : Set E) {a ε : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hε0 : 0 ≤ ε) :
    (fun _ : E => (⟨a, ha0, ha1⟩ : I)) ≤ FK.AGDifferentialShift.incrementWeight S a ε := by
  classical
  intro e
  show a ≤ ((max 0 (min 1 (if e ∈ S then a + ε else a)) : ℝ))
  by_cases hmem : e ∈ S
  · simp only [hmem, ite_true]
    exact le_trans (le_min ha1 (by linarith)) (le_max_right 0 (min 1 (a + ε)))
  · simp only [hmem, ite_false, min_eq_right ha1, max_eq_right ha0]
    exact le_rfl

/-- **The supercritical AG input with the enhanced edges boosted.**  Above the
critical parameter the increment profile — weights `a + ε` on the enhanced set `S`
and `a` elsewhere — gives full mass to the ordinary percolation event. -/
theorem incMass_hasInfiniteCluster_eq_one_of_nonneg (G : SimpleGraph V) (o : V)
    (S : Set G.edgeSet) {a ε : ℝ} (ha0 : 0 ≤ a) (hε0 : 0 ≤ ε) (haε1 : a + ε ≤ 1)
    (hpc : criticalProb G o < a) :
    FK.AGDifferentialShift.incMass
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} S a ε = 1 := by
  have ha1 : a ≤ 1 := by linarith
  have h0 := incMass_hasInfiniteCluster_eq_one G o S ha0 ha1 hpc
  have hbase : (FKLimit.bernoulliProduct
      (FK.AGDifferentialShift.incrementWeight S a 0) : Measure (G.edgeSet → Bool))
      {ω | HasInfiniteCluster G ω} = 1 := by
    rw [← ENNReal.toReal_eq_one_iff]
    exact h0
  have hle : FK.AGDifferentialShift.incrementWeight S a 0 ≤
      FK.AGDifferentialShift.incrementWeight S a ε := by
    classical
    intro e
    change ((FK.AGDifferentialShift.incrementWeight S a 0 e : I) : ℝ) ≤
      ((FK.AGDifferentialShift.incrementWeight S a ε e : I) : ℝ)
    simp only [FK.AGDifferentialShift.incrementWeight, add_zero]
    by_cases hmem : e ∈ S
    · simp only [hmem, ite_true]
      exact max_le_max (le_refl (0:ℝ)) (min_le_min (le_refl (1:ℝ)) (by linarith))
    · simp only [hmem, ite_false, le_refl]
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
    (E := G.edgeSet) hle
  have hz := FK.EssentialWindow.measure_eq_one_of_stochasticallyDominates hdom
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G)
    (FK.ClusterTail.isUpperSet_hasInfiniteCluster G) hbase
  have hm : FK.AGDifferentialShift.incMass
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} S a ε =
      ((FKLimit.bernoulliProduct (FK.AGDifferentialShift.incrementWeight S a ε) :
        Measure (G.edgeSet → Bool)) {ω | HasInfiniteCluster G ω}).toReal := rfl
  rw [hm, ENNReal.toReal_eq_one_iff]
  exact hz

/-- **The subcritical AG input.**  Below the critical parameter the decrement
profile — weights `b - ε` on the enhanced set `S` and `b` elsewhere — gives zero
mass to the ordinary percolation event. -/
theorem mass_hasInfiniteCluster_eq_zero (G : SimpleGraph V) (S : Set G.edgeSet)
    {b ε : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hε0 : 0 ≤ ε) (hpc : b < clusterCriticalProb G) :
    FK.AGDifferentialShift.mass
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} S b ε = 0 := by
  have hb : ((⟨b, hb0, hb1⟩ : I) : ℝ) < clusterCriticalProb G := hpc
  have hbase : (FKLimit.bernoulliProduct (fun _ : G.edgeSet => (⟨b, hb0, hb1⟩ : I)) :
      Measure (G.edgeSet → Bool)) {ω | HasInfiniteCluster G ω} = 0 :=
    percolation_hasInfiniteCluster_eq_zero_of_lt_clusterCriticalProb G hb
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
    (r := FK.AGDifferentialShift.decrementWeight S b ε)
    (s := fun _ : G.edgeSet => (⟨b, hb0, hb1⟩ : I)) (decrementWeight_le_const S hb0 hb1 hε0)
  have hz := FK.EssentialWindow.measure_eq_zero_of_stochasticallyDominates hdom
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G)
    (FK.ClusterTail.isUpperSet_hasInfiniteCluster G) hbase
  have hm : FK.AGDifferentialShift.mass
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} S b ε =
      ((FKLimit.bernoulliProduct (FK.AGDifferentialShift.decrementWeight S b ε) :
        Measure (G.edgeSet → Bool)) {ω | HasInfiniteCluster G ω}).toReal := rfl
  rw [hm, hz]
  simp

/-! ### The event is the countable union of the root clusters

The step that separates "some open cluster is infinite" from "the cluster of this
root is infinite": on a countable vertex set the percolation event is the
countable union of the root-cluster events, so it is null exactly when every root
cluster is a.s. finite.  (No transitivity is needed for this; what a
quasi-transitivity argument adds is the independence of the zero set of `θ` from
the root.) -/

/-- The percolation event as the countable union of the root-cluster events. -/
theorem hasInfiniteCluster_eq_iUnion (G : SimpleGraph V) :
    {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} =
      ⋃ x : V, {ω : G.edgeSet → Bool | {y | OpenConnected G ω Set.univ x y}.Infinite} := by
  ext ω
  constructor
  · rintro ⟨x, hx⟩
    rw [clusterAvoid_empty_eq] at hx
    exact Set.mem_iUnion.mpr ⟨x, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    exact ⟨x, by rwa [clusterAvoid_empty_eq]⟩

/-- **The event convention versus the root convention.**  On a countable vertex
set the percolation event is null exactly when every root cluster is a.s.
finite.  Hence the only remaining difference between `clusterCriticalProb G` and
the root-based `criticalProb G o` is the (standard, quasi-transitivity) fact that
the zero set of `θ` does not depend on the root. -/
theorem percolation_hasInfiniteCluster_eq_zero_iff_forall (G : SimpleGraph V) (p : I) :
    percolation G p {ω | HasInfiniteCluster G ω} = 0 ↔
      ∀ x, percolationProb G x p = 0 := by
  constructor
  · intro h x
    rw [percolationProb_eq]
    refine measure_mono_null ?_ h
    intro ω hω
    exact ⟨x, by rwa [clusterAvoid_empty_eq]⟩
  · intro h
    rw [hasInfiniteCluster_eq_iUnion]
    refine measure_iUnion_null (fun x => ?_)
    rw [← percolationProb_eq]
    exact h x

/-- Below `clusterCriticalProb` every root cluster is a.s. finite. -/
theorem percolationProb_eq_zero_of_lt_clusterCriticalProb (G : SimpleGraph V) {b : I}
    (hb : (b : ℝ) < clusterCriticalProb G) :
    ∀ x, percolationProb G x b = 0 :=
  (percolation_hasInfiniteCluster_eq_zero_iff_forall G b).mp
    (percolation_hasInfiniteCluster_eq_zero_of_lt_clusterCriticalProb G hb)

/-- `clusterCriticalProb` is the supremum of the parameters at which every root
cluster is a.s. finite. -/
theorem clusterCriticalProb_eq_sSup_forall (G : SimpleGraph V) :
    clusterCriticalProb G = sSup (Subtype.val ''
      {p : I | ∀ x, percolationProb G x p = 0}) := by
  rw [clusterCriticalProb]
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (percolation_hasInfiniteCluster_eq_zero_iff_forall G p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (percolation_hasInfiniteCluster_eq_zero_iff_forall G p).mpr hp, rfl⟩

/-! ### The root convention: `p_c` as in the source

The source defines `p_c(G)` through the almost-sure existence or not of an
infinite cluster; the repository's `criticalProb G o = sup {p : θ_o(p) = 0}` uses
the root cluster.  For a connected graph the two agree.  The bridge is the
classical single-coordinate Harris/FKG comparison `θ_y ≥ p·θ_x` for adjacent
vertices, proved here from the product structure without invoking FKG: it
identifies `A ∩ {e open}` as `A` conditioned on `e`, and compares the mass of `A`
with the mass of the event obtained by forcing `e` open. -/


/-- Set the edge `e` open, leaving every other coordinate unchanged. -/
noncomputable def flipOpen (G : SimpleGraph V) (e : G.edgeSet) :
    (G.edgeSet → Bool) → (G.edgeSet → Bool) :=
  fun ω i => if i = e then true else ω i

theorem flipOpen_apply (G : SimpleGraph V) (e : G.edgeSet) (ω : G.edgeSet → Bool)
    (i : G.edgeSet) : flipOpen G e ω i = if i = e then true else ω i := rfl

theorem flipOpen_measurable (G : SimpleGraph V) (e : G.edgeSet) : Measurable (flipOpen G e) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i = e
  · have h1 : (fun ω : G.edgeSet → Bool => flipOpen G e ω i) = fun _ => true := by
      funext ω; rw [flipOpen_apply, ite_eq_left hi]
    rw [h1]; exact measurable_const
  · have h1 : (fun ω : G.edgeSet → Bool => flipOpen G e ω i) = fun ω => ω i := by
      funext ω; rw [flipOpen_apply]; simp [hi]
    rw [h1]
    exact measurable_pi_apply i

theorem le_flipOpen (G : SimpleGraph V) (e : G.edgeSet) (ω : G.edgeSet → Bool) :
    ω ≤ flipOpen G e ω := by
  intro i
  rw [flipOpen_apply]
  by_cases hi : i = e
  · simp [hi]
  · simp [hi]

theorem flipOpen_eq_self (G : SimpleGraph V) (e : G.edgeSet) {ω : G.edgeSet → Bool}
    (hω : ω e = true) : flipOpen G e ω = ω := by
  funext i
  rw [flipOpen_apply]
  by_cases hi : i = e
  · rw [ite_eq_left hi, hi]; exact hω.symm
  · rw [ite_eq_right hi]

/-- **Single-coordinate Harris inequality.**  For an increasing measurable event
`A` and an edge `e`, the mass of `A ∩ {e open}` is at least `p` times the mass
of `A`.-/
theorem ofReal_mul_measure_le_measure_inter (G : SimpleGraph V) (p : I)
    {A : Set (G.edgeSet → Bool)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (e : G.edgeSet) :
    (ENNReal.ofReal (p : ℝ)) * percolation G p A ≤
      percolation G p (A ∩ {ω | ω e = true}) := by
  classical
  set B : Set (G.edgeSet → Bool) := {ω | ω e = true} with hB
  have hgmeas : Measurable (flipOpen G e) := flipOpen_measurable G e
  have hpre : MeasurableSet (flipOpen G e ⁻¹' A) := hgmeas hA
  have hBmeas : MeasurableSet B := by
    have hBeq : B = (fun ω : G.edgeSet → Bool => ω e) ⁻¹' {true} := rfl
    rw [hBeq]
    exact (measurable_pi_apply e) (measurableSet_singleton true)
  have hdep : DependsOn (fun ω : G.edgeSet → Bool => ω ∈ flipOpen G e ⁻¹' A)
      ({e}ᶜ : Set G.edgeSet) := by
    intro ω η hωη
    have hgωη : flipOpen G e ω = flipOpen G e η := by
      funext i
      rw [flipOpen_apply, flipOpen_apply]
      by_cases hi : i = e
      · rw [ite_eq_left hi, ite_eq_left hi]
      · rw [ite_eq_right hi, ite_eq_right hi]
        exact hωη i (by simpa using hi)
    simp only [Set.mem_preimage, hgωη]
  have hBdep : DependsOn (fun ω : G.edgeSet → Bool => ω ∈ B) ({e} : Set G.edgeSet) := by
    intro ω η hωη
    have hωe : ω e = η e := hωη e (Set.mem_singleton e)
    simp only [hB, Set.mem_ofPred_eq, hωe]
  have hdisj : Disjoint ({e}ᶜ : Set G.edgeSet) {e} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (by simpa using hx')
  have hind : percolation G p (flipOpen G e ⁻¹' A ∩ B) =
      percolation G p (flipOpen G e ⁻¹' A) * percolation G p B := by
    have := measure_inter_eq_mul_of_dependsOn (ι := G.edgeSet) hpre hBmeas hdep hBdep hdisj p
    exact this
  have hBmass : percolation G p B = ENNReal.ofReal (p : ℝ) :=
    bernoulliProduct_coord_true (ι := G.edgeSet) p e
  have hset : flipOpen G e ⁻¹' A ∩ B = A ∩ B := by
    ext ω
    constructor
    · rintro ⟨hgA, hBω⟩
      refine ⟨?_, hBω⟩
      simp only [Set.mem_preimage] at hgA
      rwa [flipOpen_eq_self G e hBω] at hgA
    · rintro ⟨hAω, hBω⟩
      exact ⟨hAup (le_flipOpen G e ω) hAω, hBω⟩
  have hsub : A ⊆ flipOpen G e ⁻¹' A := fun ω hω => hAup (le_flipOpen G e ω) hω
  have hmono : percolation G p A ≤ percolation G p (flipOpen G e ⁻¹' A) := measure_mono hsub
  rw [hBmass, hset] at hind
  rw [hind, mul_comm]
  exact mul_le_mul_left hmono _

/-- Opening the edge `{x,y}` puts `y`'s cluster inside `x`'s cluster. -/
theorem cluster_subset_of_adj_open (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y)
    {ω : G.edgeSet → Bool} (hopen : ω ⟨s(x, y), hxy⟩ = true) :
    {z | OpenConnected G ω Set.univ y z} ⊆ {z | OpenConnected G ω Set.univ x z} := by
  intro z hz
  exact OpenConnected.trans (OpenConnected.of_adj hxy (Set.mem_univ _) hopen) hz

/-- **Neighbour comparison.**  `θ_x ≥ p · θ_y` for adjacent `x`, `y`. -/
theorem ofReal_mul_percolationProb_le (G : SimpleGraph V) (p : I) {x y : V} (hxy : G.Adj x y) :
    (ENNReal.ofReal (p : ℝ)) * percolationProb G y p ≤ percolationProb G x p := by
  classical
  rw [percolationProb_eq (G := G) (o := y), percolationProb_eq (G := G) (o := x)]
  have hAmeas : MeasurableSet
      {ω : G.edgeSet → Bool | {z | OpenConnected G ω Set.univ y z}.Infinite} :=
    MeasurableSet.setOfPred_infinite.preimage (FK.ClusterTail.measurable_openCluster (G := G) y)
  have hAup : IsUpperSet
      {ω : G.edgeSet → Bool | {z | OpenConnected G ω Set.univ y z}.Infinite} :=
    isUpperSet_infiniteOpenCluster (G := G) y
  have hharris := ofReal_mul_measure_le_measure_inter G p hAmeas hAup ⟨s(x, y), hxy⟩
  have hsub : {ω : G.edgeSet → Bool | {z | OpenConnected G ω Set.univ y z}.Infinite} ∩
        {ω | ω ⟨s(x, y), hxy⟩ = true} ⊆
      {ω : G.edgeSet → Bool | {z | OpenConnected G ω Set.univ x z}.Infinite} := by
    rintro ω ⟨hA, hopen⟩
    exact Set.Infinite.mono (cluster_subset_of_adj_open G hxy hopen) hA
  have hmono : percolation G p ({ω : G.edgeSet → Bool |
        {z | OpenConnected G ω Set.univ y z}.Infinite} ∩ {ω | ω ⟨s(x, y), hxy⟩ = true}) ≤
      percolation G p {ω : G.edgeSet → Bool |
        {z | OpenConnected G ω Set.univ x z}.Infinite} :=
    measure_mono hsub
  exact le_trans hharris hmono

/-- **Positivity of the root cluster is edge-invariant** at `p ≠ 0`. -/
theorem percolationProb_pos_iff_of_adj (G : SimpleGraph V) (p : I) (hp : (p : ℝ) ≠ 0)
    {x y : V} (hxy : G.Adj x y) :
    0 < percolationProb G x p ↔ 0 < percolationProb G y p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hp)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (p : ℝ) := ENNReal.ofReal_pos.mpr hp0
  constructor
  · intro hx
    refine lt_of_lt_of_le ?_ (ofReal_mul_percolationProb_le G p hxy.symm)
    exact ENNReal.mul_pos hpos.ne' hx.ne'
  · intro hy
    refine lt_of_lt_of_le ?_ (ofReal_mul_percolationProb_le G p hxy)
    exact ENNReal.mul_pos hpos.ne' hy.ne'

/-- Positivity of the root cluster is invariant along open-graph reachability. -/
theorem percolationProb_pos_iff_of_reachable (G : SimpleGraph V) (p : I) (hp : (p : ℝ) ≠ 0)
    {x y : V} (h : G.Reachable x y) :
    0 < percolationProb G x p ↔ 0 < percolationProb G y p := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Iff.rfl
  | cons hadj w ih => exact (percolationProb_pos_iff_of_adj G p hp hadj).trans ih

/-- The vanishing of the root cluster is invariant along reachability. -/
theorem percolationProb_eq_zero_iff_of_reachable (G : SimpleGraph V) (p : I) (hp : (p : ℝ) ≠ 0)
    {x y : V} (h : G.Reachable x y) :
    percolationProb G x p = 0 ↔ percolationProb G y p = 0 := by
  have H := percolationProb_pos_iff_of_reachable G p hp h
  constructor
  · intro hx
    by_contra hne
    exact absurd (H.mpr (pos_iff_ne_zero.mpr hne)) (by rw [hx]; exact lt_irrefl 0)
  · intro hy
    by_contra hne
    exact absurd (H.mp (pos_iff_ne_zero.mpr hne)) (by rw [hy]; exact lt_irrefl 0)

/-- **The subcritical half of the source dichotomy in the root convention.**
Below `criticalProb G o` the reference model is a.s. non-percolating. -/
theorem percolation_hasInfiniteCluster_eq_zero_of_lt_criticalProb (G : SimpleGraph V)
    [G.LocallyFinite] (hG : G.Connected) (o : V) {p : I}
    (hp : (p : ℝ) < criticalProb G o) :
    percolation G p {ω | HasInfiniteCluster G ω} = 0 := by
  classical
  obtain ⟨r, hpr, hrpc⟩ := exists_between hp
  have hr0 : (0 : ℝ) ≤ r := le_trans p.2.1 hpr.le
  have hr1 : r ≤ 1 := le_trans hrpc.le (criticalProb_mem_Icc G o).2
  set q : I := ⟨r, hr0, hr1⟩ with hq
  have hqval : (q : ℝ) = r := rfl
  have hqne : (q : ℝ) ≠ 0 := by
    rw [hqval]
    exact ne_of_gt (lt_of_le_of_lt p.2.1 hpr)
  have hall : ∀ x, percolationProb G x q = 0 := by
    intro x
    refine (percolationProb_eq_zero_iff_of_reachable G q hqne (hG.preconnected o x)).mp ?_
    exact percolationProb_eq_zero_of_lt_criticalProb hG (by rw [hqval]; exact hrpc)
  have hq0 : percolation G q {ω | HasInfiniteCluster G ω} = 0 :=
    (percolation_hasInfiniteCluster_eq_zero_iff_forall G q).mpr hall
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le
    (E := G.edgeSet) (r := fun _ : G.edgeSet => p) (s := fun _ : G.edgeSet => q)
    (fun _ => hpr.le)
  have hle := FK.EssentialWindow.measure_le_of_stochasticallyDominates hdom
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G)
    (FK.ClusterTail.isUpperSet_hasInfiniteCluster G)
  have hle' : percolation G p {ω | HasInfiniteCluster G ω} ≤
      percolation G q {ω | HasInfiniteCluster G ω} := hle
  rw [hq0] at hle'
  exact le_antisymm hle' bot_le

/-- **Exact criterion away from the critical parameter**, in the root convention
of the source: `p ≠ p_c` percolates a.s. exactly when `p > p_c`. -/
theorem percolation_hasInfiniteCluster_eq_one_iff_of_ne (G : SimpleGraph V) [G.LocallyFinite]
    (hG : G.Connected) (o : V) {p : I} (hne : (p : ℝ) ≠ criticalProb G o) :
    percolation G p {ω | HasInfiniteCluster G ω} = 1 ↔ criticalProb G o < (p : ℝ) := by
  constructor
  · intro hone
    by_contra hlt
    have hle : (p : ℝ) ≤ criticalProb G o := le_of_not_gt hlt
    have hlt' : (p : ℝ) < criticalProb G o := lt_of_le_of_ne hle hne
    rw [percolation_hasInfiniteCluster_eq_zero_of_lt_criticalProb G hG o hlt'] at hone
    exact zero_ne_one hone
  · intro hlt
    exact percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt G o hlt

/-- **The two critical-parameter conventions agree for connected graphs.** -/
theorem clusterCriticalProb_eq_criticalProb (G : SimpleGraph V) (hG : G.Connected) (o : V) :
    clusterCriticalProb G = criticalProb G o := by
  rw [clusterCriticalProb_eq_sSup_forall, criticalProb]
  apply le_antisymm
  · refine Real.sSup_le (fun y hy => ?_) (sSup_image_val_nonneg _)
    obtain ⟨p, hp, rfl⟩ := hy
    exact le_csSup (bddAbove_image_val _) ⟨p, hp o, rfl⟩
  · refine Real.sSup_le (fun y hy => ?_) (sSup_image_val_nonneg _)
    obtain ⟨p, hp, rfl⟩ := hy
    by_cases hp0 : (p : ℝ) = 0
    · rw [hp0]
      exact sSup_image_val_nonneg _
    · refine le_csSup (bddAbove_image_val _) ⟨p, fun x => ?_, rfl⟩
      exact (percolationProb_eq_zero_iff_of_reachable G p hp0 (hG.preconnected o x)).mp hp


/-! ### The AG windows with the base inputs discharged

The two theorems below are the existing differential-trade windows of
`FK.AGDifferentialShift` with the base hypothesis `hbase` replaced by the proved
dichotomy for the ordinary percolation event of the reference model.  What
remains is exactly the uniform geometric pivot trade bound (through the
derivative data `L`, `hderiv` and `htrade`) and the approximation convergence
`hconv`; no `incMass`/`mass` base input is left. -/

/-- **Lower (supercritical) window, `q < 1`, with the base input discharged.**
The critical parameter is the root convention `criticalProb G o`, so the only
extra hypotheses beyond `FK.AGDifferentialShift.lowerWindow_of_incrementTrade_q_lt_one`
are the non-degeneracy `0 < p_c < 1` of the reference model. -/
theorem lowerWindow_hasInfiniteCluster_q_lt_one (G : SimpleGraph V) (o : V)
    (An : ℕ → Set (G.edgeSet → Bool)) (Eb Ee : Set G.edgeSet) (n m : ℕ)
    {q c : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (k : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      HasFDerivAt (FK.AGDifferentialShift.incMassPair (An k) Eb) (L k a ε) (a, ε))
    (htrade : ∀ (k : ℕ) (a ε : ℝ), 0 ≤ a → 0 ≤ ε → a + ε ≤ 1 →
      0 ≤ (L k a ε) (-c, 1))
    (hconv : ∀ (a ε : ℝ), Tendsto
      (fun k => FK.AGDifferentialShift.incMass (An k) Eb a ε) atTop
      (𝓝 (FK.AGDifferentialShift.incMass
        {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} Eb a ε))) :
    FK.EssentialWindow.LowerWindow
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} (criticalProb G o)
      Eb Ee n m q hq :=
  FK.AGDifferentialShift.lowerWindow_of_incrementTrade_q_lt_one
    {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} An (criticalProb G o) Eb Ee n m q c
    hq hq1 hpc0 hpc1 hc0 hc1 L hderiv htrade hconv
    (fun _a hpa ha1 => incMass_hasInfiniteCluster_eq_one G o Eb (hpc0.trans hpa).le ha1 hpa)
    (FK.ClusterTail.isUpperSet_hasInfiniteCluster G)
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G)

/-- **Upper (subcritical) window, `q < 1`, with the base input discharged.**
Here the critical parameter is the percolation-event convention
`clusterCriticalProb G`; the non-degeneracy hypotheses `0 < p_c < 1` and the
trade data are the only remaining inputs. -/
theorem upperWindow_hasInfiniteCluster_q_lt_one (G : SimpleGraph V) [G.LocallyFinite]
    (hG : G.Connected) (o : V)
    (An : ℕ → Set (G.edgeSet → Bool)) (Eb Ee : Set G.edgeSet) (n m : ℕ)
    {q c : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (k : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (FK.AGDifferentialShift.massPair (An k) Ee) (L k b ε) (b, ε))
    (htrade : ∀ (k : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      (L k b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto
      (fun k => FK.AGDifferentialShift.mass (An k) Ee b ε) atTop
      (𝓝 (FK.AGDifferentialShift.mass
        {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} Ee b ε))) :
    FK.EssentialWindow.UpperWindow
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} (criticalProb G o)
      Eb Ee n m q hq :=
  FK.AGDifferentialShift.upperWindow_of_decrementTrade_q_lt_one
    {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} An (criticalProb G o) Eb Ee n m q c
    hq hq1 hpc0 hpc1 hc0 hc1 L hderiv htrade hconv
    (fun b hb0 hb =>
      mass_hasInfiniteCluster_eq_zero G Ee hb0 (hb.trans hpc1).le le_rfl
        (by rw [clusterCriticalProb_eq_criticalProb G hG o]; exact hb))
    (FK.ClusterTail.isUpperSet_hasInfiniteCluster G)
    (FK.ClusterTail.measurableSet_hasInfiniteCluster G)

/-! ### The source's "almost surely" phrasing -/

/-- The source's sentence "for `p` large enough there is almost surely an
infinite cluster", in the almost-everywhere form, above the root parameter. -/
theorem ae_hasInfiniteCluster_of_criticalProb_lt (G : SimpleGraph V) (o : V) {p : I}
    (hp : criticalProb G o < (p : ℝ)) :
    ∀ᵐ ω ∂(percolation G p), HasInfiniteCluster G ω := by
  rw [ae_iff]
  rw [show {ω : G.edgeSet → Bool | ¬ HasInfiniteCluster G ω} =
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω}ᶜ from rfl,
    measure_compl (FK.ClusterTail.measurableSet_hasInfiniteCluster G) (measure_ne_top _ _),
    percolation_hasInfiniteCluster_eq_one_of_criticalProb_lt G o hp]
  simp

/-- The same in the percolation-event convention for the critical parameter. -/
theorem ae_hasInfiniteCluster_of_lt_clusterCriticalProb (G : SimpleGraph V) {p : I}
    (hp : clusterCriticalProb G < (p : ℝ)) :
    ∀ᵐ ω ∂(percolation G p), HasInfiniteCluster G ω := by
  rw [ae_iff]
  rw [show {ω : G.edgeSet → Bool | ¬ HasInfiniteCluster G ω} =
      {ω : G.edgeSet → Bool | HasInfiniteCluster G ω}ᶜ from rfl,
    measure_compl (FK.ClusterTail.measurableSet_hasInfiniteCluster G) (measure_ne_top _ _),
    percolation_hasInfiniteCluster_eq_one_of_lt_clusterCriticalProb G hp]
  simp

end FK.ReferenceBaseline
