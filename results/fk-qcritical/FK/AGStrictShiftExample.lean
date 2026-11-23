import FK.AGInfiniteLimit
import Mathlib.Probability.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A concrete strict critical-point shift for a path/star enhancement

The ordinary edges are the path edges `(n,n+1)` on `ℕ`.  The enhancement-only
edges join `0` to `n+2`.  Path bonds have parameter `p`; enhancement-only
bonds have parameter zero before enhancement and independent parameter `s`
after enhancement.  Thus the unenhanced root cluster is serial, whereas the
enhanced root cluster has infinitely many independent direct bypasses.

This is an inhomogeneous product model on a connected, non-locally-finite
simple graph, not the general homogeneous OR enhancement theorem.  The latter
cannot shift the critical point of a path away from one.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal Topology unitInterval Sym2

namespace FK.AGStrictShiftExample

open CurvatureVariance.Infra.Percolation

/-- Path edges together with direct star edges from the root. -/
def pathStarGraph : SimpleGraph ℕ where
  Adj u v := u + 1 = v ∨ v + 1 = u ∨ (u = 0 ∧ 2 ≤ v) ∨ (v = 0 ∧ 2 ≤ u)
  symm := ⟨by
    intro u v h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))⟩
  loopless := ⟨by
    intro u h
    change u + 1 = u ∨ u + 1 = u ∨ (u = 0 ∧ 2 ≤ u) ∨ (u = 0 ∧ 2 ≤ u) at h
    omega⟩

@[simp] lemma pathStarGraph_adj_root_one : pathStarGraph.Adj 0 1 := by
  left
  rfl

@[simp] lemma pathStarGraph_adj_root_star (n : ℕ) : pathStarGraph.Adj 0 (n + 2) := by
  exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))

lemma pathStarGraph_connected : pathStarGraph.Connected := by
  apply pathStarGraph.connected_iff_exists_forall_reachable.2
  refine ⟨0, fun n => ?_⟩
  by_cases h0 : n = 0
  · subst n
    rfl
  by_cases h1 : n = 1
  · subst n
    exact pathStarGraph_adj_root_one.reachable
  have hn : 2 ≤ n := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact (pathStarGraph_adj_root_star k).reachable

/-- The path edge joining `n` and `n+1`. -/
def lineEdge (n : ℕ) : pathStarGraph.edgeSet :=
  ⟨s(n, n + 1), by
    change pathStarGraph.Adj n (n + 1)
    exact Or.inl rfl⟩

/-- The enhancement-only edge joining the root to `n+2`. -/
def starEdge (n : ℕ) : pathStarGraph.edgeSet :=
  ⟨s(0, n + 2), pathStarGraph_adj_root_star n⟩

lemma lineEdge_apply (n : ℕ) : (lineEdge n : Sym2 ℕ) = s(n, n + 1) := rfl

lemma starEdge_apply (n : ℕ) : (starEdge n : Sym2 ℕ) = s(0, n + 2) := rfl

lemma lineEdge_injective : Function.Injective lineEdge := by
  intro m n h
  have h' := congrArg Subtype.val h
  rw [lineEdge_apply, lineEdge_apply, Sym2.eq_iff] at h'
  omega

lemma starEdge_injective : Function.Injective starEdge := by
  intro m n h
  have h' := congrArg Subtype.val h
  rw [starEdge_apply, starEdge_apply, Sym2.eq_iff] at h'
  omega

lemma lineEdge_ne_starEdge (m n : ℕ) : lineEdge m ≠ starEdge n := by
  intro h
  have h' := congrArg Subtype.val h
  rw [lineEdge_apply, starEdge_apply, Sym2.eq_iff] at h'
  omega

lemma edge_eq_line_or_star (e : pathStarGraph.edgeSet) :
    (∃ n, lineEdge n = e) ∨ (∃ n, starEdge n = e) := by
  obtain ⟨z, hz⟩ := e
  induction z using Sym2.inductionOn with
  | _ u v =>
      have hadj : pathStarGraph.Adj u v := hz
      rcases hadj with huv | huv | ⟨hu, hv⟩ | ⟨hv, hu⟩
      · apply Or.inl
        refine ⟨u, Subtype.ext ?_⟩
        rw [lineEdge_apply]
        exact Sym2.eq_iff.2 (Or.inl ⟨rfl, huv⟩)
      · apply Or.inl
        refine ⟨v, Subtype.ext ?_⟩
        rw [lineEdge_apply]
        exact Sym2.eq_iff.2 (Or.inr ⟨rfl, huv⟩)
      · apply Or.inr
        refine ⟨v - 2, Subtype.ext ?_⟩
        rw [starEdge_apply]
        exact Sym2.eq_iff.2 (Or.inl ⟨hu.symm, by omega⟩)
      · apply Or.inr
        refine ⟨u - 2, Subtype.ext ?_⟩
        rw [starEdge_apply]
        exact Sym2.eq_iff.2 (Or.inr ⟨hv.symm, by omega⟩)

/-- The actual root-percolation event from the percolation library. -/
def RootPercolates : Set (pathStarGraph.edgeSet → Bool) :=
  {ω | {x | OpenConnected pathStarGraph ω Set.univ 0 x}.Infinite}

/-- A zero-rate configuration space is inhomogeneous Bernoulli product measure. -/
noncomputable def productLaw (r : pathStarGraph.edgeSet → unitInterval) :
    Measure (pathStarGraph.edgeSet → Bool) :=
  Measure.infinitePi fun e => bernoulliMeasure true false (r e)

instance (r : pathStarGraph.edgeSet → unitInterval) : IsProbabilityMeasure (productLaw r) := by
  unfold productLaw
  infer_instance

/-- The base path/star parameters. -/
noncomputable def baseRate (p : unitInterval) (e : pathStarGraph.edgeSet) :
    unitInterval :=
  if ∃ n, lineEdge n = e then p else 0

/-- The enhanced path/star parameters. -/
noncomputable def enhancedRate (p s : unitInterval) (e : pathStarGraph.edgeSet) :
    unitInterval :=
  if ∃ n, lineEdge n = e then p else if ∃ n, starEdge n = e then s else 0

@[simp] lemma baseRate_line (p : unitInterval) (n : ℕ) : baseRate p (lineEdge n) = p := by
  simp [baseRate]

@[simp] lemma enhancedRate_line (p s : unitInterval) (n : ℕ) :
    enhancedRate p s (lineEdge n) = p := by
  simp [enhancedRate]

@[simp] lemma baseRate_star (p : unitInterval) (n : ℕ) : baseRate p (starEdge n) = 0 := by
  simp [baseRate, lineEdge_ne_starEdge]

@[simp] lemma enhancedRate_star (p s : unitInterval) (n : ℕ) :
    enhancedRate p s (starEdge n) = s := by
  simp [enhancedRate, lineEdge_ne_starEdge]

lemma enhancedRate_zero_activation (p : unitInterval) (e : pathStarGraph.edgeSet) :
    enhancedRate p 0 e = baseRate p e := by
  simp [enhancedRate, baseRate]

lemma enhancedLaw_zero_activation (p : unitInterval) :
    productLaw (enhancedRate p 0) = productLaw (baseRate p) := by
  unfold productLaw
  congr 1
  funext e
  rw [enhancedRate_zero_activation p e]

lemma productLaw_coord (r : pathStarGraph.edgeSet → unitInterval)
    (e : pathStarGraph.edgeSet) (b : Bool) :
    productLaw r {ω | ω e = b} = bernoulliMeasure true false (r e) {b} := by
  exact (measurePreserving_eval_infinitePi
    (fun e : pathStarGraph.edgeSet => bernoulliMeasure true false (r e)) e).measure_preimage
      (measurableSet_singleton b).nullMeasurableSet

lemma productLaw_coord_true (r : pathStarGraph.edgeSet → unitInterval)
    (e : pathStarGraph.edgeSet) :
    productLaw r {ω | ω e = true} = ENNReal.ofReal (r e) := by
  rw [productLaw_coord, bernoulliMeasure_true]

lemma productLaw_coord_false (r : pathStarGraph.edgeSet → unitInterval)
    (e : pathStarGraph.edgeSet) :
    productLaw r {ω | ω e = false} = ENNReal.ofReal (1 - (r e : ℝ)) := by
  rw [productLaw_coord, bernoulliMeasure_false]

lemma iIndepFun_coordinates (r : pathStarGraph.edgeSet → unitInterval) :
    iIndepFun (fun e (ω : pathStarGraph.edgeSet → Bool) => ω e) (productLaw r) := by
  exact iIndepFun_infinitePi
    (P := fun e : pathStarGraph.edgeSet => bernoulliMeasure true false (r e))
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id)

/-- Every path coordinate is open; this event is null below one. -/
def AllLineOpen : Set (pathStarGraph.edgeSet → Bool) :=
  {ω | ∀ n, ω (lineEdge n) = true}

/-- The event that the `n`-th direct root connection is open. -/
def StarOpen (n : ℕ) : Set (pathStarGraph.edgeSet → Bool) :=
  {ω | ω (starEdge n) = true}

lemma measurableSet_starOpen (n : ℕ) : MeasurableSet (StarOpen n) := by
  change MeasurableSet {ω : pathStarGraph.edgeSet → Bool | ω (starEdge n) = true}
  exact (measurable_pi_apply (X := fun _ : pathStarGraph.edgeSet => Bool) (starEdge n))
    (measurableSet_singleton true)

lemma root_connected_of_starOpen {ω : pathStarGraph.edgeSet → Bool} {n : ℕ}
    (h : ω ∈ StarOpen n) : OpenConnected pathStarGraph ω Set.univ 0 (n + 2) := by
  exact OpenConnected.of_adj (starEdge n).property (Set.mem_univ _) h

/-- If every direct root connection is closed and the path edge at `k` is
closed, then an open walk from the root cannot get beyond `k`. -/
lemma reachable_le_of_closed {ω : pathStarGraph.edgeSet → Bool} {k x : ℕ}
    (hstar : ∀ n, ω (starEdge n) = false) (hline : ω (lineEdge k) = false)
    (hx : OpenConnected pathStarGraph ω Set.univ 0 x) : x ≤ k := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact Nat.zero_le _
  | @tail a b hx hab ih =>
      rw [openGraph, SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨⟨e, he, hee⟩, -⟩ := hab
      have hG : pathStarGraph.Adj a b := by
        have he' := e.property
        rw [hee] at he'
        exact he'
      have hω : ω ⟨s(a, b), hG⟩ = true := by
        have heq : e = ⟨s(a, b), hG⟩ := Subtype.ext hee
        rw [← heq]
        exact he
      have hgeom : a + 1 = b ∨ b + 1 = a ∨ (a = 0 ∧ 2 ≤ b) ∨ (b = 0 ∧ 2 ≤ a) := hG
      rcases hgeom with hab | hab | ⟨ha, hb⟩ | ⟨hb, ha⟩
      · by_contra hbk
        have hak : a = k := by omega
        have hbk' : b = k + 1 := by omega
        have heq : (⟨s(a, b), hG⟩ : pathStarGraph.edgeSet) = lineEdge k := by
          apply Subtype.ext
          simp [lineEdge_apply, hak, hbk']
        rw [heq, hline] at hω
        contradiction
      · omega
      · have heq : (⟨s(a, b), hG⟩ : pathStarGraph.edgeSet) = starEdge (b - 2) := by
          apply Subtype.ext
          simp [starEdge_apply, ha, show b - 2 + 2 = b by omega]
        rw [heq, hstar (b - 2)] at hω
        contradiction
      · omega

/-- Geometric decomposition of unenhanced percolation into the all-line event
and a countable union of exceptional open zero-rate star coordinates. -/
lemma rootPercolates_subset_allLineOpen_union_starOpen {ω : pathStarGraph.edgeSet → Bool}
    (hω : ω ∈ RootPercolates) : ω ∈ AllLineOpen ∪ ⋃ n, StarOpen n := by
  by_cases hs : ∃ n, ω ∈ StarOpen n
  · exact Or.inr (Set.mem_iUnion.2 hs)
  apply Or.inl
  intro n
  by_contra hn
  have hline : ω (lineEdge n) = false := by
    cases h : ω (lineEdge n) with
    | false => rfl
    | true => exact (hn h).elim
  have hstar : ∀ m, ω (starEdge m) = false := by
    intro m
    cases h : ω (starEdge m) with
    | false => rfl
    | true => exact (hs ⟨m, h⟩).elim
  apply hω
  apply (Set.finite_le_nat n).subset
  intro x hx
  exact reachable_le_of_closed hstar hline hx

lemma base_allLineOpen_le_pow (p : unitInterval) (N : ℕ) :
    productLaw (baseRate p) AllLineOpen ≤ (ENNReal.ofReal (p : ℝ)) ^ N := by
  classical
  let S : Finset pathStarGraph.edgeSet := (Finset.range N).image lineEdge
  let C : Set (pathStarGraph.edgeSet → Bool) :=
    Set.pi (↑S : Set pathStarGraph.edgeSet) (fun _ => {true})
  have hsub : AllLineOpen ⊆ C := by
    intro ω hω e he
    change ω e = true
    obtain ⟨n, hn⟩ := Finset.mem_image.1 he
    obtain ⟨hnN, rfl⟩ := hn
    exact hω n
  calc
    productLaw (baseRate p) AllLineOpen ≤ productLaw (baseRate p) C := measure_mono hsub
    _ = ∏ e ∈ S, bernoulliMeasure true false (baseRate p e) {true} := by
      exact Measure.infinitePi_pi _ (fun e _ => measurableSet_singleton true)
    _ = ∏ e ∈ S, ENNReal.ofReal (baseRate p e : ℝ) := by
      apply Finset.prod_congr rfl
      intro e _
      exact bernoulliMeasure_true _
    _ = ∏ _n ∈ Finset.range N, ENNReal.ofReal (p : ℝ) := by
      dsimp only [S]
      rw [Finset.prod_image lineEdge_injective.injOn]
      simp
    _ = (ENNReal.ofReal (p : ℝ)) ^ N := by simp

lemma base_allLineOpen_null {p : unitInterval} (hp : p < 1) :
    productLaw (baseRate p) AllLineOpen = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hp))
  exact Filter.Eventually.of_forall (base_allLineOpen_le_pow p)

lemma base_starOpen_null (p : unitInterval) (n : ℕ) :
    productLaw (baseRate p) (StarOpen n) = 0 := by
  rw [show StarOpen n = {ω | ω (starEdge n) = true} from rfl,
    productLaw_coord_true, baseRate_star]
  simp

lemma base_rootPercolates_null {p : unitInterval} (hp : p < 1) :
    productLaw (baseRate p) RootPercolates = 0 := by
  apply measure_mono_null (fun _ => rootPercolates_subset_allLineOpen_union_starOpen)
  exact measure_union_null (base_allLineOpen_null hp)
    (measure_iUnion_null (base_starOpen_null p))

lemma iIndepSet_starOpen_enhanced (p s : unitInterval) :
    iIndepSet StarOpen (productLaw (enhancedRate p s)) := by
  apply (iIndepSet_iff_meas_biInter measurableSet_starOpen).2
  intro N
  have hindep := (iIndepFun_coordinates (enhancedRate p s)).precomp starEdge_injective
  have h := hindep.measure_inter_preimage_eq_mul N (sets := fun _ => {true})
    (fun _ _ => measurableSet_singleton true)
  simpa only [StarOpen, Set.preimage, Set.mem_singleton_iff, Set.ofPred_mem_eq] using h

lemma enhanced_starOpen_prob (p s : unitInterval) (n : ℕ) :
    productLaw (enhancedRate p s) (StarOpen n) = ENNReal.ofReal (s : ℝ) := by
  rw [show StarOpen n = {ω | ω (starEdge n) = true} from rfl,
    productLaw_coord_true, enhancedRate_star]

lemma enhanced_limsup_starOpen_one (p s : unitInterval) (hs : 0 < s) :
    productLaw (enhancedRate p s) (limsup StarOpen atTop) = 1 := by
  apply measure_limsup_eq_one measurableSet_starOpen (iIndepSet_starOpen_enhanced p s)
  simp_rw [enhanced_starOpen_prob]
  exact ENNReal.tsum_const_eq_top_of_ne_zero
    (ENNReal.ofReal_ne_zero_iff.2 (unitInterval.coe_pos.2 hs))

lemma limsup_starOpen_subset_rootPercolates :
    limsup StarOpen atTop ⊆ RootPercolates := by
  intro ω hω
  rw [mem_limsup_iff_frequently_mem, Filter.frequently_atTop] at hω
  change {x | OpenConnected pathStarGraph ω Set.univ 0 x}.Infinite
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro k
  obtain ⟨n, hkn, hn⟩ := hω k
  exact ⟨n + 2, root_connected_of_starOpen hn, by omega⟩

lemma enhanced_rootPercolates_one (p s : unitInterval) (hs : 0 < s) :
    productLaw (enhancedRate p s) RootPercolates = 1 := by
  apply le_antisymm prob_le_one
  rw [← enhanced_limsup_starOpen_one p s hs]
  exact measure_mono limsup_starOpen_subset_rootPercolates

lemma allLineOpen_rootConnected {ω : pathStarGraph.edgeSet → Bool}
    (hω : ω ∈ AllLineOpen) (n : ℕ) : OpenConnected pathStarGraph ω Set.univ 0 n := by
  induction n with
  | zero => exact OpenConnected.refl ω Set.univ 0
  | succ n ih =>
      have hedge : OpenConnected pathStarGraph ω Set.univ n (n + 1) :=
        OpenConnected.of_adj (lineEdge n).property (Set.mem_univ _) (hω n)
      exact ih.trans hedge

lemma allLineOpen_subset_rootPercolates : AllLineOpen ⊆ RootPercolates := by
  intro ω hω
  change {x | OpenConnected pathStarGraph ω Set.univ 0 x}.Infinite
  have heq : {x | OpenConnected pathStarGraph ω Set.univ 0 x} = Set.univ :=
    Set.eq_univ_of_forall (allLineOpen_rootConnected hω)
  rw [heq]
  exact Set.infinite_univ

lemma base_allLineOpen_one : productLaw (baseRate 1) AllLineOpen = 1 := by
  rw [measure_of_measure_compl_eq_zero, measure_univ]
  have hcompl : (AllLineOpen : Set (pathStarGraph.edgeSet → Bool))ᶜ =
      ⋃ n, {ω | ω (lineEdge n) = false} := by
    ext ω
    simp only [AllLineOpen, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
      Set.mem_iUnion]
    apply exists_congr
    intro n
    cases h : ω (lineEdge n) <;> simp_all
  rw [hcompl]
  apply measure_iUnion_null
  intro n
  rw [productLaw_coord_false, baseRate_line]
  simp

lemma base_rootPercolates_one : productLaw (baseRate 1) RootPercolates = 1 := by
  apply le_antisymm prob_le_one
  rw [← base_allLineOpen_one]
  exact measure_mono allLineOpen_subset_rootPercolates

/-- Critical point of a one-parameter family of percolation probabilities,
using the same `sSup` convention as `Percolation.criticalProb`. -/
noncomputable def criticalParameter (θ : unitInterval → ℝ≥0∞) : ℝ :=
  sSup (Subtype.val '' {p : unitInterval | θ p = 0})

noncomputable def basePercolationProb (p : unitInterval) : ℝ≥0∞ :=
  productLaw (baseRate p) RootPercolates

noncomputable def enhancedPercolationProb (s p : unitInterval) : ℝ≥0∞ :=
  productLaw (enhancedRate p s) RootPercolates

noncomputable def baseCritical : ℝ := criticalParameter basePercolationProb

noncomputable def enhancedCritical (s : unitInterval) : ℝ :=
  criticalParameter (enhancedPercolationProb s)

lemma base_percolationProb_eq_zero {p : unitInterval} (hp : p < 1) :
    basePercolationProb p = 0 := base_rootPercolates_null hp

lemma base_percolationProb_one : basePercolationProb 1 = 1 := base_rootPercolates_one

lemma enhanced_percolationProb_one (p s : unitInterval) (hs : 0 < s) :
    enhancedPercolationProb s p = 1 := enhanced_rootPercolates_one p s hs

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

lemma baseCritical_eq_one : baseCritical = 1 := by
  unfold baseCritical
  exact criticalParameter_eq_one_of_forall_lt_one (fun _ hp => base_rootPercolates_null hp)

lemma enhancedCritical_eq_zero (s : unitInterval) (hs : 0 < s) :
    enhancedCritical s = 0 := by
  unfold enhancedCritical criticalParameter
  have hempty : {p : unitInterval | enhancedPercolationProb s p = 0} = ∅ := by
    ext p
    simp [enhanced_percolationProb_one p s hs]
  rw [hempty]
  simp

/-- **An actual strict critical-point shift.**  The connected path/star graph
has ordinary critical parameter one, while every positive star activation
parameter produces percolation with probability one, hence enhanced critical
parameter zero. -/
theorem strict_critical_shift (s : unitInterval) (hs : 0 < s) :
    enhancedCritical s < baseCritical := by
  rw [baseCritical_eq_one, enhancedCritical_eq_zero s hs]
  norm_num

end FK.AGStrictShiftExample

#print axioms FK.AGStrictShiftExample.edge_eq_line_or_star
#print axioms FK.AGStrictShiftExample.base_rootPercolates_null
#print axioms FK.AGStrictShiftExample.base_rootPercolates_one
#print axioms FK.AGStrictShiftExample.enhanced_rootPercolates_one
#print axioms FK.AGStrictShiftExample.baseCritical_eq_one
#print axioms FK.AGStrictShiftExample.enhancedCritical_eq_zero
#print axioms FK.AGStrictShiftExample.strict_critical_shift
