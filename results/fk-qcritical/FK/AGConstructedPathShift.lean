import FK.AGInfiniteLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A normalized synchronized-activation strict shift on a homogeneous path

The graph is the one-way path on `ℕ`, with exactly the bonds `(n,n+1)`.
Before enhancement these are independent Bernoulli(`p`) bonds.  There is one
additional Bernoulli(`s`) activation, independent of all the bonds, and the
enhanced configuration is `ω e || α`.  Thus every edge has the same bond law
and the same enhanced effective rate `p + (1-p)s`, while the enhanced edges
remain genuinely correlated through the one shared activation.

This gives an exact enhanced percolation curve
`θ_enh(p,s) = θ_base(p) + (1-θ_base(p))s`.  In particular the ordinary path
has critical parameter one, whereas every positive synchronized activation
has enhanced critical parameter zero.  The graph is connected and locally
finite, and no enhancement-only edges or zero-rate inhomogeneity are used.

**Scope.**  The single activation has unbounded range.  This is deliberately a
constructed normalized bond/activation example, not the missing bounded-range
Aizenman--Grimmett reference theorem and not a derivative/limit argument.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal Topology unitInterval Sym2 BigOperators

namespace FK.AGConstructedPathShift

open CurvatureVariance.Infra.Percolation

/-- The homogeneous one-way path on the natural numbers. -/
def rayGraph : SimpleGraph ℕ where
  Adj u v := u + 1 = v ∨ v + 1 = u
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro u h; omega⟩

/-- The bond joining `n` to `n+1`. -/
def rayEdge (n : ℕ) : rayGraph.edgeSet :=
  ⟨s(n, n + 1), Or.inl rfl⟩

@[simp] lemma rayEdge_apply (n : ℕ) : (rayEdge n : Sym2 ℕ) = s(n, n + 1) := rfl

lemma rayEdge_injective : Function.Injective rayEdge := by
  intro m n h
  have h' := congrArg Subtype.val h
  rw [rayEdge_apply, rayEdge_apply, Sym2.eq_iff] at h'
  omega

lemma rayGraph_reachable_zero (n : ℕ) : rayGraph.Reachable 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact ih.trans (show rayGraph.Adj n (n+1) from Or.inl rfl).reachable

lemma rayGraph_connected : rayGraph.Connected := by
  exact rayGraph.connected_iff_exists_forall_reachable.2 ⟨0, rayGraph_reachable_zero⟩

/-- Each vertex of the ray has at most two neighbours. -/
noncomputable instance rayGraphLocallyFinite : rayGraph.LocallyFinite := by
  intro v
  apply ((Set.finite_le_nat (v+1)).subset ?_).fintype
  intro w hw
  change w ≤ v+1
  change v + 1 = w ∨ w + 1 = v at hw
  omega

/-- The actual root-percolation event of the percolation library. -/
def RootPercolates : Set (rayGraph.edgeSet → Bool) :=
  {ω | {x | OpenConnected rayGraph ω Set.univ 0 x}.Infinite}

/-- Every path bond is open. -/
def AllOpen : Set (rayGraph.edgeSet → Bool) :=
  {ω | ∀ n, ω (rayEdge n) = true}

lemma reachable_le_of_closed {ω : rayGraph.edgeSet → Bool} {k x : ℕ}
    (hline : ω (rayEdge k) = false)
    (hx : OpenConnected rayGraph ω Set.univ 0 x) : x ≤ k := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact Nat.zero_le _
  | @tail a b hx hab ih =>
      rw [openGraph, SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨⟨e, he, hee⟩, -⟩ := hab
      have hG : rayGraph.Adj a b := by
        have he' := e.property
        rw [hee] at he'
        exact he'
      have hω : ω ⟨s(a, b), hG⟩ = true := by
        have heq : e = ⟨s(a, b), hG⟩ := Subtype.ext hee
        rw [← heq]
        exact he
      have hgeom : a + 1 = b ∨ b + 1 = a := hG
      rcases hgeom with hab | hab
      · by_contra hbk
        have hak : a = k := by omega
        have hbk' : b = k + 1 := by omega
        have heq : (⟨s(a, b), hG⟩ : rayGraph.edgeSet) = rayEdge k := by
          apply Subtype.ext
          simp [rayEdge_apply, hak, hbk']
        rw [heq, hline] at hω
        contradiction
      · omega

lemma rootPercolates_subset_allOpen {ω : rayGraph.edgeSet → Bool}
    (hω : ω ∈ RootPercolates) : ω ∈ AllOpen := by
  intro n
  by_contra hn
  have hline : ω (rayEdge n) = false := by
    cases h : ω (rayEdge n) with
    | false => rfl
    | true => exact (hn h).elim
  apply hω
  apply (Set.finite_le_nat n).subset
  intro x hx
  exact reachable_le_of_closed hline hx

lemma allOpen_rootConnected {ω : rayGraph.edgeSet → Bool}
    (hω : ω ∈ AllOpen) (n : ℕ) : OpenConnected rayGraph ω Set.univ 0 n := by
  induction n with
  | zero => exact OpenConnected.refl ω Set.univ 0
  | succ n ih =>
      exact ih.trans (OpenConnected.of_adj (rayEdge n).property (Set.mem_univ _) (hω n))

lemma allOpen_subset_rootPercolates : AllOpen ⊆ RootPercolates := by
  intro ω hω
  change {x | OpenConnected rayGraph ω Set.univ 0 x}.Infinite
  have heq : {x | OpenConnected rayGraph ω Set.univ 0 x} = Set.univ :=
    Set.eq_univ_of_forall (allOpen_rootConnected hω)
  rw [heq]
  exact Set.infinite_univ

lemma base_allOpen_le_pow (p : unitInterval) (N : ℕ) :
    percolation rayGraph p AllOpen ≤ (ENNReal.ofReal (p : ℝ)) ^ N := by
  classical
  let S : Finset rayGraph.edgeSet := (Finset.range N).image rayEdge
  let C : Set (rayGraph.edgeSet → Bool) :=
    Set.pi (↑S : Set rayGraph.edgeSet) (fun _ => {true})
  have hsub : AllOpen ⊆ C := by
    intro ω hω e he
    change ω e = true
    obtain ⟨n, hn⟩ := Finset.mem_image.1 he
    obtain ⟨hnN, rfl⟩ := hn
    exact hω n
  calc
    percolation rayGraph p AllOpen ≤ percolation rayGraph p C := measure_mono hsub
    _ = ∏ e ∈ S, bernoulliMeasure true false p {true} := by
      exact Measure.infinitePi_pi _ (fun e _ => measurableSet_singleton true)
    _ = ∏ e ∈ S, ENNReal.ofReal (p : ℝ) := by
      apply Finset.prod_congr rfl
      intro e _
      exact bernoulliMeasure_true _
    _ = ∏ _n ∈ Finset.range N, ENNReal.ofReal (p : ℝ) := by
      dsimp only [S]
      rw [Finset.prod_image rayEdge_injective.injOn]
    _ = (ENNReal.ofReal (p : ℝ)) ^ N := by simp

lemma base_allOpen_null {p : unitInterval} (hp : p < 1) :
    percolation rayGraph p AllOpen = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hp))
  exact Filter.Eventually.of_forall (base_allOpen_le_pow p)

/-- The serial path has zero root-percolation probability at every `p < 1`. -/
theorem base_rootPercolates_null {p : unitInterval} (hp : p < 1) :
    percolation rayGraph p RootPercolates = 0 := by
  exact measure_mono_null (fun _ => rootPercolates_subset_allOpen) (base_allOpen_null hp)

lemma base_allOpen_one : percolation rayGraph 1 AllOpen = 1 := by
  rw [measure_of_measure_compl_eq_zero, measure_univ]
  have hcompl : (AllOpen : Set (rayGraph.edgeSet → Bool))ᶜ =
      ⋃ n, {ω | ω (rayEdge n) = false} := by
    ext ω
    simp only [AllOpen, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
      Set.mem_iUnion]
    apply exists_congr
    intro n
    cases h : ω (rayEdge n) <;> simp_all
  rw [hcompl]
  apply measure_iUnion_null
  intro n
  exact bernoulliProduct_coord_false 1 (rayEdge n) |>.trans (by simp)

/-- At `p = 1` the root cluster is the whole infinite ray almost surely. -/
theorem base_rootPercolates_one :
    percolation rayGraph 1 RootPercolates = 1 := by
  apply le_antisymm prob_le_one
  rw [← base_allOpen_one]
  exact measure_mono allOpen_subset_rootPercolates

lemma measurableSet_rootPercolates : MeasurableSet RootPercolates := by
  rw [RootPercolates, setOf_infinite_eq_iInter_armEvent rayGraph_connected 0]
  exact MeasurableSet.iInter fun n => measurableSet_armEvent 0 n

/-- The independent bond state together with the one shared activation. -/
abbrev JointState := (rayGraph.edgeSet → Bool) × Bool

/-- The actual synchronized enhanced bond configuration. -/
def synchronizedConfig (χ : JointState) : rayGraph.edgeSet → Bool :=
  fun e => χ.1 e || χ.2

@[simp] lemma synchronizedConfig_apply (χ : JointState) (e : rayGraph.edgeSet) :
    synchronizedConfig χ e = (χ.1 e || χ.2) := rfl

@[simp] lemma synchronizedConfig_false (ω : rayGraph.edgeSet → Bool) :
    synchronizedConfig (ω, false) = ω := by
  funext e
  simp [synchronizedConfig]

lemma measurable_synchronizedConfig : Measurable synchronizedConfig := by
  apply measurable_pi_iff.2
  intro e
  change Measurable (fun χ : JointState => χ.1 e || χ.2)
  fun_prop

/-- Independent normalized product of the bond law and the activation law. -/
noncomputable def jointLaw (p s : unitInterval) : Measure JointState :=
  (percolation rayGraph p).prod (bernoulliMeasure true false s)

instance (p s : unitInterval) : IsProbabilityMeasure (jointLaw p s) := by
  unfold jointLaw
  infer_instance

/-- Pullback of the actual infinite-cluster event to the joint state. -/
def EnhancedPercolates : Set JointState := synchronizedConfig ⁻¹' RootPercolates

lemma rootPercolates_mono {ω ξ : rayGraph.edgeSet → Bool} (hωξ : ω ≤ ξ)
    (hω : ω ∈ RootPercolates) : ξ ∈ RootPercolates := by
  apply hω.mono
  intro x hx
  exact hx.mono_config hωξ

lemma base_le_synchronized (ω : rayGraph.edgeSet → Bool) (a : Bool) :
    ω ≤ synchronizedConfig (ω, a) := by
  intro e
  cases hω : ω e <;> cases a <;> simp [synchronizedConfig, hω]

/-- The enhanced percolation event is the disjoint union of ordinary
percolation (with either activation) and synchronized activation on an
ordinary nonpercolating bond configuration. -/
lemma enhancedPercolates_eq_union :
    EnhancedPercolates = (RootPercolates ×ˢ Set.univ) ∪
      (RootPercolatesᶜ ×ˢ ({true} : Set Bool)) := by
  ext χ
  rcases χ with ⟨ω, a⟩
  constructor
  · intro h
    by_cases hbase : ω ∈ RootPercolates
    · exact Or.inl ⟨hbase, Set.mem_univ _⟩
    · apply Or.inr
      refine ⟨hbase, ?_⟩
      cases a with
      | false =>
          exfalso
          apply hbase
          change synchronizedConfig (ω, false) ∈ RootPercolates at h
          rw [synchronizedConfig_false] at h
          exact h
      | true => rfl
  · intro h
    rcases h with h | h
    · exact rootPercolates_mono (base_le_synchronized ω a) h.1
    · have ha : a = true := h.2
      subst a
      change synchronizedConfig (ω, true) ∈ RootPercolates
      apply allOpen_subset_rootPercolates
      intro n
      simp [synchronizedConfig]

lemma disjoint_base_activation_union :
    Disjoint (RootPercolates ×ˢ (Set.univ : Set Bool))
      (RootPercolatesᶜ ×ˢ ({true} : Set Bool)) := by
  apply Set.disjoint_left.2
  rintro ⟨ω, a⟩ ⟨hω, ha⟩ ⟨hnω, ha'⟩
  exact hnω hω

lemma measurableSet_enhancedPercolates : MeasurableSet EnhancedPercolates :=
  measurable_synchronizedConfig measurableSet_rootPercolates

/-- **Exact normalized enhanced percolation curve.**  This is a direct product
measure calculation, not an identification of the synchronized law with an
independent bond product. -/
theorem jointLaw_enhancedPercolates (p s : unitInterval) :
    jointLaw p s EnhancedPercolates =
      percolation rayGraph p RootPercolates +
        (1 - percolation rayGraph p RootPercolates) * ENNReal.ofReal (s : ℝ) := by
  rw [enhancedPercolates_eq_union,
    measure_union disjoint_base_activation_union
      (measurableSet_rootPercolates.compl.prod (measurableSet_singleton true)),
    jointLaw, Measure.prod_prod, Measure.prod_prod, bernoulliMeasure_true,
    measure_compl measurableSet_rootPercolates (measure_ne_top _ _)]
  simp only [measure_univ, mul_one]

noncomputable def basePercolationProb (p : unitInterval) : ℝ≥0∞ :=
  percolation rayGraph p RootPercolates

/-- Enhanced probability as a function of the bond parameter, with the
activation parameter held fixed. -/
noncomputable def enhancedPercolationProb (s p : unitInterval) : ℝ≥0∞ :=
  jointLaw p s EnhancedPercolates

/-- Closed form for the actual enhanced curve. -/
theorem enhancedPercolationProb_curve (p s : unitInterval) :
    enhancedPercolationProb s p = basePercolationProb p +
      (1 - basePercolationProb p) * ENNReal.ofReal (s : ℝ) := by
  exact jointLaw_enhancedPercolates p s

/-- Before the endpoint, enhanced percolation is exactly the synchronized
activation event: ordinary serial-path percolation is null. -/
theorem enhancedPercolationProb_eq_s {p : unitInterval} (hp : p < 1)
    (s : unitInterval) : enhancedPercolationProb s p = ENNReal.ofReal (s : ℝ) := by
  rw [enhancedPercolationProb_curve, basePercolationProb,
    base_rootPercolates_null hp]
  simp

/-- At the endpoint the ordinary all-open path forces enhanced percolation. -/
theorem enhancedPercolationProb_one (s : unitInterval) :
    enhancedPercolationProb s 1 = 1 := by
  rw [enhancedPercolationProb_curve, basePercolationProb, base_rootPercolates_one]
  simp

/-- A direct lower bound, valid even without first calculating ordinary
percolation: synchronized activation itself makes the whole ray open. -/
theorem activation_le_enhancedPercolationProb (p s : unitInterval) :
    ENNReal.ofReal (s : ℝ) ≤ enhancedPercolationProb s p := by
  calc
    ENNReal.ofReal (s : ℝ) = jointLaw p s
        ((Set.univ : Set (rayGraph.edgeSet → Bool)) ×ˢ ({true} : Set Bool)) := by
      rw [jointLaw, Measure.prod_prod, bernoulliMeasure_true, measure_univ, one_mul]
    _ ≤ jointLaw p s EnhancedPercolates := by
      apply measure_mono
      rintro ⟨ω, a⟩ ⟨hω, ha⟩
      have ha' : a = true := ha
      subst a
      change synchronizedConfig (ω, true) ∈ RootPercolates
      apply allOpen_subset_rootPercolates
      intro n
      simp [synchronizedConfig]

lemma enhancedPercolationProb_ne_zero (p s : unitInterval) (hs : 0 < s) :
    enhancedPercolationProb s p ≠ 0 := by
  have hspos : 0 < ENNReal.ofReal (s : ℝ) :=
    ENNReal.ofReal_pos.2 (unitInterval.coe_pos.2 hs)
  exact ne_of_gt (lt_of_lt_of_le hspos (activation_le_enhancedPercolationProb p s))

/-- Critical point of a one-parameter family of percolation probabilities,
using the same `sSup` convention as `Percolation.criticalProb`. -/
noncomputable def criticalParameter (θ : unitInterval → ℝ≥0∞) : ℝ :=
  sSup (Subtype.val '' {p : unitInterval | θ p = 0})

noncomputable def baseCritical : ℝ := criticalParameter basePercolationProb

noncomputable def enhancedCritical (s : unitInterval) : ℝ :=
  criticalParameter (enhancedPercolationProb s)

lemma criticalParameter_nonneg (θ : unitInterval → ℝ≥0∞) : 0 ≤ criticalParameter θ :=
  CurvatureVariance.Infra.Percolation.sSup_image_val_nonneg _

lemma criticalParameter_le_one (θ : unitInterval → ℝ≥0∞) : criticalParameter θ ≤ 1 :=
  CurvatureVariance.Infra.Percolation.sSup_image_val_le_one _

lemma criticalParameter_eq_one_of_forall_lt_one {θ : unitInterval → ℝ≥0∞}
    (hθ : ∀ p : unitInterval, p < 1 → θ p = 0) : criticalParameter θ = 1 := by
  apply le_antisymm (criticalParameter_le_one θ)
  by_contra hnot
  have hlt : criticalParameter θ < 1 := lt_of_not_ge hnot
  let q : unitInterval := ⟨(criticalParameter θ + 1) / 2,
    ⟨by have := criticalParameter_nonneg θ; linarith, by linarith⟩⟩
  have hq1 : q < 1 := by
    change (criticalParameter θ + 1) / 2 < 1
    linarith
  have hq : (q : ℝ) ≤ criticalParameter θ := by
    unfold criticalParameter
    exact CurvatureVariance.Infra.Percolation.le_sSup_image_val (hθ q hq1)
  have hqgt : criticalParameter θ < (q : ℝ) := by
    change criticalParameter θ < (criticalParameter θ + 1) / 2
    linarith
  exact (not_lt_of_ge hq) hqgt

lemma criticalParameter_eq_zero_of_forall_ne_zero {θ : unitInterval → ℝ≥0∞}
    (hθ : ∀ p, θ p ≠ 0) : criticalParameter θ = 0 := by
  unfold criticalParameter
  have hempty : {p : unitInterval | θ p = 0} = ∅ := by
    ext p
    simp [hθ p]
  rw [hempty]
  simp

/-- The base critical parameter is the library's critical parameter on the
same actual root-percolation event, using its measure/set bridge. -/
theorem baseCritical_eq_library_criticalProb :
    baseCritical = criticalProb rayGraph 0 := by
  have h : basePercolationProb = percolationProb rayGraph 0 := by
    funext p
    exact (percolationProb_eq p).symm
  unfold baseCritical criticalParameter criticalProb
  rw [h]

theorem basePercolationProb_eq_percolationProb (p : unitInterval) :
    basePercolationProb p = percolationProb rayGraph 0 p := by
  exact (percolationProb_eq p).symm

/-- Ordinary homogeneous bond percolation on the ray has critical parameter
one. -/
theorem baseCritical_eq_one : baseCritical = 1 := by
  unfold baseCritical
  exact criticalParameter_eq_one_of_forall_lt_one
    (fun _ hp => base_rootPercolates_null hp)

/-- Every positive synchronized activation gives the enhanced critical
parameter zero, since the enhanced probability is strictly positive for every
bond parameter including zero. -/
theorem enhancedCritical_eq_zero (s : unitInterval) (hs : 0 < s) :
    enhancedCritical s = 0 := by
  unfold enhancedCritical
  exact criticalParameter_eq_zero_of_forall_ne_zero
    (fun p => enhancedPercolationProb_ne_zero p s hs)

/-- **Strict critical-parameter shift on a connected locally finite graph.**
All path bonds have the same ordinary parameter `p`; one independent shared
activation produces the exact continuous enhancement curve above. -/
theorem strict_critical_shift (s : unitInterval) (hs : 0 < s) :
    enhancedCritical s < baseCritical := by
  rw [baseCritical_eq_one, enhancedCritical_eq_zero s hs]
  norm_num

end FK.AGConstructedPathShift

#print axioms FK.AGConstructedPathShift.base_rootPercolates_null
#print axioms FK.AGConstructedPathShift.base_rootPercolates_one
#print axioms FK.AGConstructedPathShift.jointLaw_enhancedPercolates
#print axioms FK.AGConstructedPathShift.enhancedPercolationProb_curve
#print axioms FK.AGConstructedPathShift.enhancedPercolationProb_eq_s
#print axioms FK.AGConstructedPathShift.baseCritical_eq_one
#print axioms FK.AGConstructedPathShift.enhancedCritical_eq_zero
#print axioms FK.AGConstructedPathShift.strict_critical_shift
