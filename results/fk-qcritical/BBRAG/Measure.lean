import BBRAG.Defs
import BBRAG.Box

/-!
# The measure-theoretic link

Cylinder probabilities of the product Bernoulli measures, the crossing probability as the finite
weighted sum `tauF`, `θ(p, s) = lim_L P(R_L)` (continuity from above), and `θ(p) ≤ P_{p,0}(R_L)`.
-/

open MeasureTheory ProbabilityTheory unitInterval

namespace BBR

variable {d : ℕ}

/-! Only the percolation definitions from `BBR.Main` are needed for the Peierls
bound.  Keeping them here avoids importing the unrelated general rerouting proof. -/

noncomputable def sitePerc (d : ℕ) (p : I) : Measure (Set (Site d)) := setBer(Set.univ, p)

noncomputable def jointLaw (d : ℕ) (p s : I) : Measure (Set (Site d) × Set (Site d)) :=
  (sitePerc d p).prod (sitePerc d s)

def OriginInInfiniteCluster (A : Set (Site d)) : Prop := {x | ContainsPath A 0 x}.Infinite

noncomputable def theta (E0 : Set (Site d) → Set (Site d)) (p s : I) : ℝ :=
  (jointLaw d p s {ωα | OriginInInfiniteCluster (enhanced E0 ωα.1 ωα.2)}).toReal

noncomputable def theta0 (d : ℕ) (p : I) : ℝ :=
  (sitePerc d p {ω | OriginInInfiniteCluster ω}).toReal

noncomputable def pcSite (d : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ p : I, (p : ℝ) = x ∧ theta0 d p = 0}

/-! ### The laws are probability measures -/

private theorem isProbabilityMeasure_sitePerc (p : I) : IsProbabilityMeasure (sitePerc d p) := by
  unfold sitePerc; infer_instance

attribute [local instance] isProbabilityMeasure_sitePerc

private theorem isProbabilityMeasure_jointLaw (p s : I) :
    IsProbabilityMeasure (jointLaw d p s) := by
  unfold jointLaw; infer_instance

attribute [local instance] isProbabilityMeasure_jointLaw

/-! ### Cylinder sets of a finite box -/

/-- The cylinder `{ω : ω ∩ Λ = η}` is measurable. -/
private lemma measurableSet_cyl (Λ η : Finset (Site d)) :
    MeasurableSet {ω : Set (Site d) | ∀ x ∈ Λ, (x ∈ ω ↔ x ∈ η)} := by
  refine measurableSet_setOfPred.2 ?_
  fun_prop

private lemma ofReal_coe_I (p : I) : ENNReal.ofReal (p : ℝ) = (toNNReal p : ENNReal) := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg p.2.1]
  rfl

open Classical in
/-- **Cylinder probabilities.** For `η ⊆ Λ`, the probability that the open sites in `Λ` are
exactly those of `η` is `∏_{x ∈ Λ} (p or 1 - p)`. -/
theorem sitePerc_cyl (Λ η : Finset (Site d)) (hη : η ⊆ Λ) (p : I) :
    sitePerc d p {ω | ∀ x ∈ Λ, (x ∈ ω ↔ x ∈ η)} = ENNReal.ofReal (wt Λ (p : ℝ) η) := by
  rw [sitePerc, setBernoulli_eq_map,
    Measure.map_apply measurable_setOfPred (measurableSet_cyl Λ η)]
  -- the cylinder is a product set over `Λ` in `Site d → Prop`
  have : (fun P : Site d → Prop => {i | P i}) ⁻¹' {ω | ∀ x ∈ Λ, (x ∈ ω ↔ x ∈ η)} =
      Set.pi (Λ : Set (Site d)) (fun x => {q : Prop | q ↔ x ∈ η}) := by
    ext P; exact Iff.rfl
  rw [this, Measure.infinitePi_pi _ (fun _ _ => MeasurableSpace.measurableSet_top)]
  rw [wt, ENNReal.ofReal_prod_of_nonneg (fun x _ => by
    split_ifs
    · exact p.2.1
    · linarith [p.2.2])]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  by_cases h : x ∈ η
  · rw [bernoulliMeasure_apply_of_mem_of_notMem p MeasurableSpace.measurableSet_top
      (by exact ⟨fun _ => h, fun _ => Set.mem_univ x⟩) (by exact fun hf => hf.2 h)]
    simp only [h, ↓reduceIte]
    rw [ofReal_coe_I]
  · rw [bernoulliMeasure_apply_of_notMem_of_mem p MeasurableSpace.measurableSet_top
      (by exact fun hf => h (hf.1 (Set.mem_univ x))) (by exact ⟨False.elim, h⟩)]
    simp only [h, ↓reduceIte]
    rw [← coe_symm_eq, ofReal_coe_I]

private lemma wt_nonneg (Λ η : Finset (Site d)) (p : I) : 0 ≤ wt Λ (p : ℝ) η := by
  refine Finset.prod_nonneg (fun x _ => ?_)
  split_ifs
  · exact p.2.1
  · linarith [p.2.2]

open Classical in
/-- For `η ⊆ B`, the configuration `ω` agrees with `η` on `B` iff `B ∩ ω = η`. -/
private lemma mem_cyl_iff {B η : Finset (Site d)} (hη : η ⊆ B) (ω : Set (Site d)) :
    (∀ x ∈ B, (x ∈ ω ↔ x ∈ η)) ↔ B.filter (· ∈ ω) = η := by
  constructor
  · intro h
    ext x
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hxB, hxω⟩
      exact (h x hxB).1 hxω
    · intro hxη
      exact ⟨hη hxη, (h x (hη hxη)).2 hxη⟩
  · rintro h x hx
    rw [← h, Finset.mem_filter]
    exact (and_iff_right hx).symm

open Classical in
/-- The crossing event as a finite union of cylinders of the box `B_N(0)`. -/
private lemma crossing_eq_iUnion (E0 : Set (Site d) → Set (Site d)) (rE : ℕ)
    (hE : HasRange E0 rE) (L N : ℕ) (hN : L + 2 * rE ≤ N) :
    {ωα : Set (Site d) × Set (Site d) | Crosses L (enhanced E0 ωα.1 ωα.2)} =
      ⋃ q ∈ ((boxFin d N).powerset ×ˢ (boxFin d N).powerset).filter
          (fun q => RLind E0 L q.1 q.2 = 1),
        {ω : Set (Site d) | ∀ x ∈ boxFin d N, (x ∈ ω ↔ x ∈ q.1)} ×ˢ
          {α : Set (Site d) | ∀ x ∈ boxFin d N, (x ∈ α ↔ x ∈ q.2)} := by
  ext ⟨ω, α⟩
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset, exists_prop, Prod.exists]
  rw [crosses_iff_box E0 rE hE L N hN ω α]
  constructor
  · intro h
    refine ⟨(boxFin d N).filter (· ∈ ω), (boxFin d N).filter (· ∈ α),
      ⟨⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩, h⟩, ?_, ?_⟩
    · exact (mem_cyl_iff (Finset.filter_subset _ _) ω).2 rfl
    · exact (mem_cyl_iff (Finset.filter_subset _ _) α).2 rfl
  · rintro ⟨η, ζ, ⟨⟨hη, hζ⟩, h⟩, hω, hα⟩
    rw [(mem_cyl_iff hη ω).1 hω, (mem_cyl_iff hζ α).1 hα]
    exact h

/-- A property of configurations that depends only on finitely many sites is measurable. -/
private lemma measurable_of_local {φ : Set (Site d) → Prop} (F : Finset (Site d))
    (hφ : ∀ ω ω' : Set (Site d), (∀ x ∈ F, (x ∈ ω ↔ x ∈ ω')) → (φ ω ↔ φ ω')) :
    Measurable φ := by
  classical
  refine measurableSet_setOfPred.1 ?_
  have : {ω | φ ω} = ⋃ (S : Finset (Site d))
      (_ : S ∈ F.powerset.filter (fun S : Finset (Site d) => φ (S : Set (Site d)))),
        {ω : Set (Site d) | ∀ x ∈ F, (x ∈ ω ↔ x ∈ S)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro h
      refine ⟨F.filter (· ∈ ω), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · exact (hφ ω _ (fun x hx => by
          rw [Finset.mem_coe, Finset.mem_filter]; exact (and_iff_right hx).symm)).1 h
      · intro x hx
        rw [Finset.mem_filter]
        exact (and_iff_right hx).symm
    · rintro ⟨S, ⟨-, hφS⟩, hω⟩
      exact (hφ ω S (fun x hx => hω x hx)).2 hφS
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun S _ => measurableSet_cyl F S)

/-- Membership of a site in the enhanced configuration is measurable in `(ω, α)`. -/
private lemma measurable_mem_enhanced (E0 : Set (Site d) → Set (Site d)) (rE : ℕ)
    (hE : HasRange E0 rE) (z : Site d) :
    Measurable (fun ωα : Set (Site d) × Set (Site d) => z ∈ enhanced E0 ωα.1 ωα.2) := by
  -- the enhancement activated at `v` reads `ω` only in `B_{rE}(v)`
  have h1 : ∀ v : Site d,
      Measurable (fun ω : Set (Site d) => z ∈ translate (E0 (translate ω (-v))) v) := by
    intro v
    refine measurable_of_local (ball_finite v rE).toFinset (fun ω ω' hωω' => ?_)
    have : E0 (translate ω (-v)) = E0 (translate ω' (-v)) := by
      refine hE.1 _ _ (Set.ext fun y => ?_)
      simp only [Set.mem_inter_iff, mem_translate, sub_neg_eq_add]
      refine and_congr_left fun hy => hωω' (y + v) ?_
      have h2 := dist1_add_right y 0 v
      rw [zero_add] at h2
      rw [Set.Finite.mem_toFinset, mem_ball, h2]
      exact hy
    rw [this]
  simp only [enhanced, Set.mem_union, Set.mem_iUnion, exists_prop]
  refine Measurable.or ?_ (Measurable.exists fun v => Measurable.and ?_ ?_)
  · exact (measurable_set_mem z).comp measurable_fst
  · exact (measurable_set_mem v).comp measurable_snd
  · exact (h1 v).comp measurable_fst

/-- The crossing event `R_L` is measurable. -/
private lemma measurableSet_crossing (E0 : Set (Site d) → Set (Site d)) (rE : ℕ)
    (hE : HasRange E0 rE) (L : ℕ) :
    MeasurableSet {ωα : Set (Site d) × Set (Site d) | Crosses L (enhanced E0 ωα.1 ωα.2)} := by
  refine measurableSet_setOfPred.2 ?_
  unfold Crosses ContainsPath
  refine Measurable.exists fun y => Measurable.and measurable_const
    (Measurable.exists fun P => Measurable.and measurable_const
      (Measurable.and measurable_const (Measurable.and measurable_const ?_)))
  exact Measurable.forall fun z => Measurable.imp measurable_const
    (measurable_mem_enhanced E0 rE hE z)

/-- The crossing probability `τ_L(p, s)` is the finite weighted sum over the box `B_N(0)`,
`N ≥ L + 2 r_E`. -/
theorem jointLaw_crossing (E0 : Set (Site d) → Set (Site d)) (rE : ℕ) (hE : HasRange E0 rE)
    (L N : ℕ) (hN : L + 2 * rE ≤ N) (p s : I) :
    (jointLaw d p s {ωα | Crosses L (enhanced E0 ωα.1 ωα.2)}).toReal =
      tauF (boxFin d N) (RLind E0 L) p s := by
  classical
  rw [crossing_eq_iUnion E0 rE hE L N hN, measure_biUnion_finset]
  rotate_left
  · -- distinct restrictions to the box give disjoint cylinders
    intro q hq q' hq' hne
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_powerset,
      Set.mem_ofPred_eq] at hq hq'
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨ω, α⟩ ⟨hω, hα⟩ ⟨hω', hα'⟩
    apply hne
    have h1 := (mem_cyl_iff hq.1.1 ω).1 hω
    have h2 := (mem_cyl_iff hq.1.2 α).1 hα
    have h1' := (mem_cyl_iff hq'.1.1 ω).1 hω'
    have h2' := (mem_cyl_iff hq'.1.2 α).1 hα'
    exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')
  · intro q _
    exact (measurableSet_cyl _ _).prod (measurableSet_cyl _ _)
  have hterm : ∀ q ∈ ((boxFin d N).powerset ×ˢ (boxFin d N).powerset).filter
      (fun q => RLind E0 L q.1 q.2 = 1),
      jointLaw d p s ({ω : Set (Site d) | ∀ x ∈ boxFin d N, (x ∈ ω ↔ x ∈ q.1)} ×ˢ
          {α : Set (Site d) | ∀ x ∈ boxFin d N, (x ∈ α ↔ x ∈ q.2)}) =
        ENNReal.ofReal (wt (boxFin d N) (p : ℝ) q.1 * wt (boxFin d N) (s : ℝ) q.2) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hq
    rw [jointLaw, Measure.prod_prod, sitePerc_cyl _ _ hq.1.1, sitePerc_cyl _ _ hq.1.2,
      ENNReal.ofReal_mul (wt_nonneg _ _ _)]
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg
      (fun q _ => mul_nonneg (wt_nonneg _ _ _) (wt_nonneg _ _ _)),
    ENNReal.toReal_ofReal (Finset.sum_nonneg
      (fun q _ => mul_nonneg (wt_nonneg _ _ _) (wt_nonneg _ _ _))),
    Finset.sum_filter, Finset.sum_product, tauF]
  refine Finset.sum_congr rfl (fun η _ => Finset.sum_congr rfl (fun ζ _ => ?_))
  clear hterm
  unfold RLind
  split_ifs with h1 h2 <;> simp_all

/-! ### Crossings and infinite clusters -/

/-- A path from `0` to a site of norm at least `L` crosses `S_L`. -/
private lemma crosses_of_containsPath {A : Set (Site d)} {y : Site d} (h : ContainsPath A 0 y)
    (L : ℕ) (hL : (L : ℤ) ≤ norm1 y) : Crosses L A := by
  obtain ⟨P, hP, hx, hy, hA⟩ := h
  obtain ⟨z, hzP, hz⟩ := hP.1.exists_layer hx hy 0 (s := L) (by
    simp only [dist1_self, dist1_zero_right]
    exact ⟨le_trans (min_le_left _ _) (Int.natCast_nonneg L), le_trans hL (le_max_right _ _)⟩)
  refine ⟨z, hz, ?_⟩
  have h0 : (0 : Site d) ∈ P := List.mem_of_mem_head? hx
  exact (hP.1.siteConnected 0 h0 z hzP).mono (fun w hw => hA w hw)

/-- `R_L` is decreasing in `L`. -/
private lemma crosses_anti {A : Set (Site d)} {L L' : ℕ} (hLL : L ≤ L') (h : Crosses L' A) :
    Crosses L A := by
  obtain ⟨y, hy, hpath⟩ := h
  refine crosses_of_containsPath hpath L ?_
  rw [mem_sphere, dist1_zero_right] at hy
  rw [hy]
  exact_mod_cast hLL

/-- An infinite cluster at the origin reaches every sphere `S_L`. -/
private lemma crosses_of_infinite {A : Set (Site d)} (h : OriginInInfiniteCluster A) (L : ℕ) :
    Crosses L A := by
  by_contra hc
  apply h
  refine (ball_finite (0 : Site d) L).subset ?_
  intro y hy
  rw [mem_ball, dist1_zero_right]
  by_contra hlt
  exact hc (crosses_of_containsPath hy L (le_of_lt (not_le.mp hlt)))

/-- A cluster at the origin reaching every sphere `S_L` is infinite. -/
private lemma infinite_of_crosses {A : Set (Site d)} (h : ∀ L : ℕ, Crosses L A) :
    OriginInInfiniteCluster A := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image norm1).bddAbove
  obtain ⟨y, hy, hpath⟩ := h (M.toNat + 1)
  have h1 : norm1 y ≤ M := hM ⟨y, hpath, rfl⟩
  have h2 := Int.self_le_toNat M
  rw [mem_sphere, dist1_zero_right] at hy
  push_cast at hy
  omega

/-- **Continuity from above.** A lower bound for `τ_L(p, s)` valid for all large `L` is a lower
bound for `θ(p, s)`. -/
theorem theta_ge_of_crossing (E0 : Set (Site d) → Set (Site d)) (rE : ℕ) (hE : HasRange E0 rE)
    (p s : I) (c : ℝ) (L₀ : ℕ)
    (h : ∀ L : ℕ, L₀ ≤ L → c ≤ (jointLaw d p s {ωα | Crosses L (enhanced E0 ωα.1 ωα.2)}).toReal) :
    c ≤ theta E0 p s := by
  set A : ℕ → Set (Set (Site d) × Set (Site d)) :=
    fun L => {ωα | Crosses L (enhanced E0 ωα.1 ωα.2)} with hA
  -- `⋂_L R_L` is the event that the origin lies in an infinite cluster
  have hinter : (⋂ L, A L) = {ωα | OriginInInfiniteCluster (enhanced E0 ωα.1 ωα.2)} := by
    ext ωα
    simp only [Set.mem_iInter, hA, Set.mem_ofPred_eq]
    exact ⟨infinite_of_crosses, fun h L => crosses_of_infinite h L⟩
  have hanti : Antitone A := fun L L' hLL ωα hωα => crosses_anti hLL hωα
  have hlim := tendsto_measure_iInter_atTop (μ := jointLaw d p s)
    (fun L => (measurableSet_crossing E0 rE hE L).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hinter] at hlim
  rw [theta, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  refine ge_of_tendsto hlim ?_
  rw [Filter.eventually_atTop]
  exact ⟨L₀, fun L hL => (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (h L hL)⟩

private lemma enhanced_empty (E0 : Set (Site d) → Set (Site d)) (ω : Set (Site d)) :
    enhanced E0 ω ∅ = ω := by
  rw [enhanced, Set.biUnion_empty, Set.union_empty]

/-- `θ(p) ≤ τ_L(p, 0)`: with no activation the enhanced configuration is `ω`, and an infinite
cluster at the origin reaches `S_L`. -/
theorem theta0_le_crossing (E0 : Set (Site d) → Set (Site d)) (rE : ℕ) (hE : HasRange E0 rE)
    (L : ℕ) (p : I) :
    theta0 d p ≤ (jointLaw d p 0 {ωα | Crosses L (enhanced E0 ωα.1 ωα.2)}).toReal := by
  rw [theta0]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  have hj : jointLaw d p 0 = Measure.map (fun ω => (ω, (∅ : Set (Site d)))) (sitePerc d p) := by
    rw [jointLaw, show sitePerc d 0 = Measure.dirac ∅ from setBernoulli_zero _,
      Measure.prod_dirac]
  rw [hj]
  refine le_trans (measure_mono ?_) (Measure.le_map_apply (by fun_prop) _)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, enhanced_empty]
  exact crosses_of_infinite hω L

end BBR
