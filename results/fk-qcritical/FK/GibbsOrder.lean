import FK.WiredFKG
import FK.InfiniteVolume

/-!
# The free/wired sandwich and the order structure of the finite-volume FK measures

This module proves the boundary-wiring monotonicity of the finite random-cluster
(FK) measures on a finite labelled multigraph and derives the finite-volume and
weak-limit sandwich between the free and wired conventions: the finite form of the
monotonicity statement of arXiv:2512.16486v1, Section 1.4, equation (6).

## Main results

* `componentCount_diff_antitone`: for a finer boundary partition `ξ ≤ η` and
  configurations `x ≤ y`, the number of extra components produced by `ξ` is
  antitone in the configuration.
* `componentCount_wiring_mlr`: the two-point lattice ratio inequality for the
  wired component count.
* `fkWeightR_wiring_mlr`: the monotone likelihood ratio of the FK weight in the
  boundary partition at `q ≥ 1`.
* `fkPMF_expectation_mono_wiring`, `fkMeasure_mono_wiring`: coarsening the
  boundary partition increases the expectation of every increasing observable,
  resp. the probability of every increasing event (Holley's inequality).
* `fkMeasure_sandwich`: the finite free/wired sandwich.
* `FK.InfiniteVolume.FiniteBox.finiteVolumeLaw_sandwich`: the same sandwich for
  the actual finite-box laws on a countable ambient edge space.
* `FK.InfiniteVolume.fkLimit_sandwich`: every FK weak limit along a fixed box
  exhaustion is sandwiched between any free and any wired weak limit, i.e. the
  weak-limit form of equation (6) of arXiv:2512.16486v1, Section 1.4.
* `FK.InfiniteVolume.cylinder_eq_of_upT_eq`: for a finite coordinate set, masses
  of upper corners determine all cylinder masses (Boolean-lattice inversion by
  downward induction over the pattern lattice).
* `FK.InfiniteVolume.cylinder_eq_of_mutual_stochasticallyDominates`: two
  probability measures on the countable product that dominate each other
  stochastically have equal cylinder masses.
* `FK.InfiniteVolume.fkLimit_cylinder_eq_of_free_eq_wired`: if the free and the
  wired schedule converge to the same law `φ`, every FK limit has the same
  cylinder masses as `φ`.

Everything is stated for arbitrary labelled multigraphs with loops, parallel
labels and arbitrary boundary setoids, at `1 ≤ q` and `0 < p < 1`.
-/

open FK.Finite MeasureTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

namespace FK.Finite.LabelledMultigraph

open FinFKG

variable {G : LabelledMultigraph} [DecidableEq G.Vertex] [DecidableEq G.Edge]







/-- The augmented edge span of the labelled edges in `s` does not depend on the
boundary partition (the wiring edges are the `inr` coordinates). -/
lemma edgeSpan_augEnds_image_inl (ξ : G.BoundaryPartition) (s : Finset G.Edge) :
    FinFKG.edgeSpan (G.augEnds ξ) (s.image Sum.inl) =
      FinFKG.edgeSpan (G.augEnds (freeBoundary G)) (s.image Sum.inl) := by
  unfold FinFKG.edgeSpan
  congr 1
  ext v
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨Sum.inl e, ⟨e, he, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨Sum.inl e, ⟨e, he, rfl⟩, rfl⟩

/-- A generator of the span of a finer wiring lies in the span of a coarser one. -/
lemma csingle_add_blockRep_mem_edgeSpan {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η)
    (ω : G.Configuration) {v : G.Vertex} (hv : G.wireOpen ξ v = true) :
    FinFKG.csingle v + FinFKG.csingle (G.blockRep ξ (Quot.mk ξ v)) ∈
      FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η ω)) := by
  have hne : v ≠ G.blockRep ξ (Quot.mk ξ v) := G.wireOpen_eq_true_iff.mp hv
  have hrelξ : ξ.r v (G.blockRep ξ (Quot.mk ξ v)) :=
    ξ.symm (Quotient.exact (G.blockRep_spec ξ (Quot.mk ξ v)))
  have hrelη : η.r v (G.blockRep ξ (Quot.mk ξ v)) := Setoid.le_def.mp hξη hrelξ
  have hadj : (G.connectionGraph η ω).Adj v (G.blockRep ξ (Quot.mk ξ v)) :=
    ⟨hne, Or.inl hrelη⟩
  exact FinFKG.csingle_add_csingle_mem_edgeSpan_of_reachable
    (G.wiringSkeleton_reachable_of_connectionGraph hadj.reachable)

/-- **The wired edge span is monotone in the boundary partition**: a coarser
partition has a larger augmented span. -/
theorem edgeSpan_mono_wiring {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η)
    (ω : G.Configuration) :
    FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ ω))
      ≤ FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η ω)) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨y, hy, rfl⟩
  rw [Finset.mem_coe, FinFKG.mem_openSet] at hy
  rcases y with e | v
  · have hyη : Sum.inl e ∈ FinFKG.openSet (G.augConfig η ω) := by
      rw [FinFKG.mem_openSet]; exact hy
    exact Submodule.subset_span ⟨Sum.inl e, hyη, rfl⟩
  · have hmem := G.csingle_add_blockRep_mem_edgeSpan hξη ω hy
    show FinFKG.edgeVec (G.augEnds ξ) (Sum.inr v) ∈
      FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η ω))
    rw [FinFKG.edgeVec_eq_single]
    exact hmem





/-- **Diminishing returns of the rank**: for `A ≤ B` and any `U`, the rank gain
of `U` over `B` is at most its rank gain over `A`. -/
theorem finrank_sup_add_le {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {A B U : Submodule (ZMod 2) W} (hAB : A ≤ B) :
    Module.finrank (ZMod 2) ↥(B ⊔ U) + Module.finrank (ZMod 2) ↥A
      ≤ Module.finrank (ZMod 2) ↥(A ⊔ U) + Module.finrank (ZMod 2) ↥B := by
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ U) B
  have hsup : (A ⊔ U) ⊔ B = B ⊔ U := by
    refine le_antisymm ?_ ?_
    · refine sup_le (sup_le ?_ le_sup_right) le_sup_left
      exact le_trans hAB le_sup_left
    · refine sup_le le_sup_right ?_
      exact le_trans le_sup_right le_sup_left
  have hmono : Module.finrank (ZMod 2) ↥A ≤ Module.finrank (ZMod 2) ↥((A ⊔ U) ⊓ B) :=
    Submodule.finrank_mono (le_inf le_sup_left hAB)
  rw [hsup] at hmod
  omega




lemma augConfig_mono {ξ : G.BoundaryPartition} {x y : G.Configuration} (hxy : x ≤ y) :
    G.augConfig ξ x ≤ G.augConfig ξ y := by
  intro z
  rcases z with e | v
  · exact hxy e
  · exact le_rfl

lemma edgeSpan_mono_config {ξ : G.BoundaryPartition} {x y : G.Configuration} (hxy : x ≤ y) :
    FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ x))
      ≤ FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ y)) :=
  FinFKG.edgeSpan_mono (FinFKG.openSet_le (G.augConfig_mono hxy))

/-- The open set of the augmented configuration splits into the open set of a
smaller configuration and the newly opened labelled edges. -/
lemma openSet_augConfig_union {ξ : G.BoundaryPartition} {x y : G.Configuration} (hxy : x ≤ y) :
    FinFKG.openSet (G.augConfig ξ y) = FinFKG.openSet (G.augConfig ξ x) ∪
      (Finset.univ.filter (fun e : G.Edge => y e = true ∧ x e = false)).image Sum.inl := by
  ext z
  rcases z with e | v
  · have hb : y e = true ↔ (x e = true ∨ (y e = true ∧ x e = false)) := by
      constructor
      · intro hy
        by_cases hx : x e = true
        · exact Or.inl hx
        · exact Or.inr ⟨hy, by simpa using hx⟩
      · rintro (hx | ⟨hy, -⟩)
        · have hle : x e ≤ y e := hxy e
          rw [hx] at hle
          cases hy : y e
          · rw [hy] at hle
            exact absurd hle (by decide)
          · rfl
        · exact hy
    simp only [FinFKG.mem_openSet, augConfig, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Sum.inl.injEq, exists_eq_right]
    exact hb
  · simp only [FinFKG.mem_openSet, augConfig, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨e, -, he⟩)
      · exact h
      · exact absurd he (by simp)

/-- The augmented edge span turns finite unions into suprema. -/
lemma edgeSpan_union_eq (ends : G.Edge ⊕ G.Vertex → G.Vertex × G.Vertex)
    (s t : Finset (G.Edge ⊕ G.Vertex)) :
    FinFKG.edgeSpan ends (s ∪ t) = FinFKG.edgeSpan ends s ⊔ FinFKG.edgeSpan ends t := by
  refine le_antisymm (FinFKG.edgeSpan_union_le ends s t) ?_
  exact sup_le (FinFKG.edgeSpan_mono (Finset.subset_union_left ..))
    (FinFKG.edgeSpan_mono (Finset.subset_union_right ..))

/-- The rank of an augmented edge span is bounded by the number of vertices. -/
lemma edgeRank_le_card (ends : G.Edge ⊕ G.Vertex → G.Vertex × G.Vertex)
    (s : Finset (G.Edge ⊕ G.Vertex)) :
    FinFKG.edgeRank ends s ≤ Fintype.card G.Vertex := by
  unfold FinFKG.edgeRank
  refine le_trans (Submodule.finrank_le _) ?_
  rw [Module.finrank_fintype_fun_eq_card]

lemma componentCount_eq_card_sub_edgeRank (ζ : G.BoundaryPartition) (z : G.Configuration) :
    G.componentCount ζ z = Fintype.card G.Vertex -
      FinFKG.edgeRank (G.augEnds ζ) (FinFKG.openSet (G.augConfig ζ z)) := by
  rw [componentCount_eq_clusterCount]
  rfl

/-- **The component-count difference is antitone in the configuration**: for a
finer partition `ξ ≤ η` and `x ≤ y`, the number of extra components of `ξ` can
only decrease. -/
theorem componentCount_diff_antitone {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η)
    {x y : G.Configuration} (hxy : x ≤ y) :
    G.componentCount ξ y + G.componentCount η x ≤
      G.componentCount ξ x + G.componentCount η y := by
  classical
  set S : Finset G.Edge :=
    Finset.univ.filter (fun e : G.Edge => y e = true ∧ x e = false) with hS
  have hK : FinFKG.edgeSpan (G.augEnds ξ) (S.image Sum.inl) =
      FinFKG.edgeSpan (G.augEnds η) (S.image Sum.inl) := by
    rw [edgeSpan_augEnds_image_inl (G := G) ξ S, edgeSpan_augEnds_image_inl (G := G) η S]
  have hdecξ : FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ y))
      = FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ x)) ⊔
        FinFKG.edgeSpan (G.augEnds ξ) (S.image Sum.inl) := by
    rw [openSet_augConfig_union (G := G) (ξ := ξ) hxy, edgeSpan_union_eq]
  have hdecη : FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η y))
      = FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η x)) ⊔
        FinFKG.edgeSpan (G.augEnds η) (S.image Sum.inl) := by
    rw [openSet_augConfig_union (G := G) (ξ := η) hxy, edgeSpan_union_eq]
  have hdim := finrank_sup_add_le (W := G.Vertex → ZMod 2)
    (A := FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ x)))
    (B := FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η x)))
    (U := FinFKG.edgeSpan (G.augEnds ξ) (S.image Sum.inl))
    (edgeSpan_mono_wiring (G := G) hξη x)
  have hmain : Module.finrank (ZMod 2) ↥
        (FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η y))) +
        Module.finrank (ZMod 2) ↥
          (FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ x))) ≤
      Module.finrank (ZMod 2) ↥
        (FinFKG.edgeSpan (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ y))) +
        Module.finrank (ZMod 2) ↥
          (FinFKG.edgeSpan (G.augEnds η) (FinFKG.openSet (G.augConfig η x))) := by
    calc Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds η)
            (FinFKG.openSet (G.augConfig η y))) +
          Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds ξ)
            (FinFKG.openSet (G.augConfig ξ x)))
        = Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds η)
              (FinFKG.openSet (G.augConfig η x)) ⊔
              FinFKG.edgeSpan (G.augEnds η) (S.image Sum.inl)) +
          Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds ξ)
            (FinFKG.openSet (G.augConfig ξ x))) := by rw [hdecη]
      _ = Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds η)
              (FinFKG.openSet (G.augConfig η x)) ⊔
              FinFKG.edgeSpan (G.augEnds ξ) (S.image Sum.inl)) +
          Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds ξ)
            (FinFKG.openSet (G.augConfig ξ x))) := by rw [hK]
      _ ≤ Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds ξ)
              (FinFKG.openSet (G.augConfig ξ x)) ⊔
              FinFKG.edgeSpan (G.augEnds ξ) (S.image Sum.inl)) +
          Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds η)
            (FinFKG.openSet (G.augConfig η x))) := hdim
      _ = Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds ξ)
              (FinFKG.openSet (G.augConfig ξ y))) +
          Module.finrank (ZMod 2) ↥(FinFKG.edgeSpan (G.augEnds η)
            (FinFKG.openSet (G.augConfig η x))) := by rw [hdecξ]
  rw [componentCount_eq_card_sub_edgeRank, componentCount_eq_card_sub_edgeRank,
    componentCount_eq_card_sub_edgeRank, componentCount_eq_card_sub_edgeRank]
  have b1 := edgeRank_le_card (G := G) (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ x))
  have b2 := edgeRank_le_card (G := G) (G.augEnds η) (FinFKG.openSet (G.augConfig η x))
  have b3 := edgeRank_le_card (G := G) (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ y))
  have b4 := edgeRank_le_card (G := G) (G.augEnds η) (FinFKG.openSet (G.augConfig η y))
  have hrev : FinFKG.edgeRank (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ x)) +
      FinFKG.edgeRank (G.augEnds η) (FinFKG.openSet (G.augConfig η y)) ≤
      FinFKG.edgeRank (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ y)) +
        FinFKG.edgeRank (G.augEnds η) (FinFKG.openSet (G.augConfig η x)) := by
    have h := hmain
    simp only [FinFKG.edgeRank] at h ⊢
    omega
  omega








/-- **The component-count monotone likelihood ratio in the boundary partition.**
For a finer partition `ξ ≤ η`, the wired component count satisfies the two-point
lattice ratio inequality. -/
theorem componentCount_wiring_mlr {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η)
    (x y : G.Configuration) :
    G.componentCount ξ x + G.componentCount η y ≤
      G.componentCount η (x ⊔ y) + G.componentCount ξ (x ⊓ y) := by
  have h1 := componentCount_diff_antitone (G := G) hξη (inf_le_left : x ⊓ y ≤ x)
  have h2 := componentCount_supermodular (G := G) η x y
  omega

/-- The two-point Bernoulli factor identity for the lattice operations. -/
lemma bool_factor_sup_inf (p : ℝ) (a b : Bool) :
    (if a then p else 1 - p) * (if b then p else 1 - p) =
      (if (a ⊔ b) then p else 1 - p) * (if (a ⊓ b) then p else 1 - p) := by
  cases a <;> cases b <;> simp [mul_comm]

/-- The Bernoulli factors are exactly balanced by the lattice operations. -/
lemma prod_factor_sup_inf (p : NNReal) (x y : G.Configuration) :
    (∏ e, (if x e then (p : ℝ) else 1 - (p : ℝ))) *
        (∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ))) =
      (∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
        (∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ))) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [Pi.sup_apply, Pi.inf_apply]
  exact bool_factor_sup_inf _ (x e) (y e)

/-- **Monotone likelihood ratio of the FK weight in the boundary partition.**
A finer wiring makes the weight relatively smaller on configurations with more
open edges, for `q ≥ 1`. -/
theorem fkWeightR_wiring_mlr {q : NNReal} (hq : 1 ≤ q) {p : NNReal} (hp0 : 0 < p)
    (hp1 : p < 1) {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η) :
    ∀ x y : G.Configuration, G.fkWeightR q p ξ x * G.fkWeightR q p η y ≤
      G.fkWeightR q p η (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y) := by
  classical
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  intro x y
  have hκ : G.componentCount ξ x + G.componentCount η y ≤
      G.componentCount η (x ⊔ y) + G.componentCount ξ (x ⊓ y) :=
    componentCount_wiring_mlr hξη x y
  have hqpart : (q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount η y ≤
      (q : ℝ) ^ G.componentCount η (x ⊔ y) * (q : ℝ) ^ G.componentCount ξ (x ⊓ y) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hqR hκ
  have hprodf := prod_factor_sup_inf (G := G) p x y
  unfold fkWeightR
  calc (∏ e, (if x e then (p : ℝ) else 1 - (p : ℝ))) * (q : ℝ) ^ G.componentCount ξ x *
        ((∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ))) * (q : ℝ) ^ G.componentCount η y)
      = ((∏ e, (if x e then (p : ℝ) else 1 - (p : ℝ))) *
          (∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ)))) *
        ((q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount η y) := by ring
    _ ≤ ((∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          (∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ)))) *
        ((q : ℝ) ^ G.componentCount η (x ⊔ y) *
          (q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by
        rw [hprodf]
        refine mul_le_mul_of_nonneg_left hqpart (mul_nonneg ?_ ?_)
        · exact Finset.prod_nonneg (fun e _ => bern_factor_nonneg hp0R hp1R _)
        · exact Finset.prod_nonneg (fun e _ => bern_factor_nonneg hp0R hp1R _)
    _ = (∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          (q : ℝ) ^ G.componentCount η (x ⊔ y) *
        ((∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          (q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by ring








/-- `Finset.univ` does not depend on the chosen `Fintype` instance. -/
theorem univ_congr {α : Type*} (i₁ i₂ : Fintype α) :
    (@Finset.univ α i₁) = (@Finset.univ α i₂) :=
  congrArg (fun i : Fintype α => @Finset.univ α i) (Subsingleton.elim i₁ i₂)

/-- **Monotonicity in the boundary partition of every increasing observable.**
For `q ≥ 1` and `0 < p < 1`, a coarser boundary partition stochastically
increases the finite FK measure. -/
theorem fkPMF_expectation_mono_wiring {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η) (f : G.Configuration → ℝ)
    (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) :
    (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * f ω) ≤
      (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le η ω).toReal * f ω) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set Z₁ : ℝ := (G.partitionFunction q p ξ : ℝ) with hZ₁def
  set Z₂ : ℝ := (G.partitionFunction q p η : ℝ) with hZ₂def
  have hZ₁ : 0 < Z₁ := by
    rw [hZ₁def]; exact_mod_cast G.partitionFunction_pos hqpos hp1.le ξ
  have hZ₂ : 0 < Z₂ := by
    rw [hZ₂def]; exact_mod_cast G.partitionFunction_pos hqpos hp1.le η
  have hH := FinFKG.holley (P := fun ω => G.fkWeightR q p ξ ω)
    (Q := fun ω => G.fkWeightR q p η ω)
    (fun ω => G.fkWeightR_pos hqpos hp0 hp1 ξ ω)
    (fun ω => le_of_lt (G.fkWeightR_pos hqpos hp0 hp1 η ω))
    (G.fkWeightR_lc hq hp0 hp1 ξ) (G.fkWeightR_wiring_mlr hq hp0 hp1 hξη) f hf hf0
  have hw₁ : ∀ ω : G.Configuration, G.fkWeightR q p ξ ω = (G.fkWeight q p ξ ω : ℝ) :=
    fun ω => G.fkWeightR_eq_coe q p hp1.le ξ ω
  have hw₂ : ∀ ω : G.Configuration, G.fkWeightR q p η ω = (G.fkWeight q p η ω : ℝ) :=
    fun ω => G.fkWeightR_eq_coe q p hp1.le η ω
  simp only [hw₁, hw₂] at hH
  have hconv₁ : ∀ (h : G.Configuration → ℝ),
      (∑ ω, (G.fkPMF hqpos hp1.le ξ ω).toReal * h ω) =
        (∑ ω, (G.fkWeight q p ξ ω : ℝ) * h ω) / Z₁ := by
    intro h
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [show (G.fkPMF hqpos hp1.le ξ ω).toReal = (G.fkWeight q p ξ ω : ℝ) / Z₁ from ?_]
    · ring
    · rw [G.fkPMF_apply hqpos hp1.le ξ ω]
      simp only [hZ₁def]
      rw [ENNReal.coe_toReal]
      rfl
  have hconv₂ : ∀ (h : G.Configuration → ℝ),
      (∑ ω, (G.fkPMF hqpos hp1.le η ω).toReal * h ω) =
        (∑ ω, (G.fkWeight q p η ω : ℝ) * h ω) / Z₂ := by
    intro h
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [show (G.fkPMF hqpos hp1.le η ω).toReal = (G.fkWeight q p η ω : ℝ) / Z₂ from ?_]
    · ring
    · rw [G.fkPMF_apply hqpos hp1.le η ω]
      simp only [hZ₂def]
      rw [ENNReal.coe_toReal]
      rfl
  have hsum₁ : (∑ ω, (G.fkWeight q p ξ ω : ℝ)) = Z₁ := by
    rw [hZ₁def]
    exact_mod_cast (rfl : G.partitionFunction q p ξ = ∑ ω, G.fkWeight q p ξ ω)
  have hsum₂ : (∑ ω, (G.fkWeight q p η ω : ℝ)) = Z₂ := by
    rw [hZ₂def]
    exact_mod_cast (rfl : G.partitionFunction q p η = ∑ ω, G.fkWeight q p η ω)
  rw [hconv₁ f, hconv₂ f, div_le_div_iff₀ hZ₁ hZ₂, ← hsum₁, ← hsum₂]
  calc (∑ ω, (G.fkWeight q p ξ ω : ℝ) * f ω) * (∑ ω, (G.fkWeight q p η ω : ℝ))
      ≤ (∑ ω, (G.fkWeight q p ξ ω : ℝ)) * (∑ ω, (G.fkWeight q p η ω : ℝ) * f ω) := by
        have hh := hH
        rw [univ_congr (α := G.Edge → Bool) Pi.instFintype (inferInstance)] at hh
        exact hh
    _ = (∑ ω, (G.fkWeight q p η ω : ℝ) * f ω) * (∑ ω, (G.fkWeight q p ξ ω : ℝ)) :=
        mul_comm _ _








/-- The real-valued mass of an event under the finite FK measure, as a sum over
configurations. -/
lemma fkMeasure_toReal_eq_sum {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) (A : Set G.Configuration) :
    (G.fkMeasure hq hp ξ A).toReal =
      ∑ ω, (G.fkPMF hq hp ξ ω).toReal * (A.indicator (fun _ => (1 : ℝ)) ω) := by
  classical
  rw [fkMeasure, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · intro ω _
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h]; exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-- **Measure-level wiring monotonicity.** For `q ≥ 1` and `0 < p < 1`, a coarser
boundary partition increases the probability of every increasing event. -/
theorem fkMeasure_mono_wiring {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    {ξ η : G.BoundaryPartition} (hξη : ξ ≤ η) {A : Set G.Configuration}
    (hA : IsUpperSet A) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ A ≤
      G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le η A := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmono : Monotone (A.indicator (fun _ => (1 : ℝ))) := by
    intro x y hxy
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hA hxy hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_apply]
      split_ifs <;> norm_num
  have h0 : ∀ x, 0 ≤ (A.indicator (fun _ => (1 : ℝ))) x := by
    intro x
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  have hreal := G.fkPMF_expectation_mono_wiring hq hp0 hp1 hξη
    (A.indicator (fun _ => (1 : ℝ))) hmono h0
  rw [← G.fkMeasure_toReal_eq_sum hqpos hp1.le ξ A,
    ← G.fkMeasure_toReal_eq_sum hqpos hp1.le η A] at hreal
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (measure_ne_top _ _)).mp hreal

/-- The free boundary partition is the finest one. -/
theorem freeBoundary_le (ξ : G.BoundaryPartition) : G.freeBoundary ≤ ξ := by
  refine Setoid.le_def.mpr ?_
  intro x y hxy
  exact hxy ▸ ξ.refl x

/-- The wired boundary partition is the coarsest one. -/
theorem le_wiredBoundary (ξ : G.BoundaryPartition) : ξ ≤ G.wiredBoundary :=
  Setoid.le_def.mpr (fun {_ _} _ => trivial)

/-- **Finite-volume free/wired sandwich**: for `q ≥ 1`, `0 < p < 1`, every
boundary partition lies stochastically between the free and the wired one. -/
theorem fkMeasure_sandwich {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) {A : Set G.Configuration} (hA : IsUpperSet A) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le G.freeBoundary A ≤
        G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ A ∧
      G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ A ≤
        G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le G.wiredBoundary A :=
  ⟨G.fkMeasure_mono_wiring hq hp0 hp1 (G.freeBoundary_le ξ) hA,
    G.fkMeasure_mono_wiring hq hp0 hp1 (G.le_wiredBoundary ξ) hA⟩


end FK.Finite.LabelledMultigraph



open FK.Finite MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace FK.InfiniteVolume

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For probability measures, the `ℝ≥0`-valued mass comparison is the
`ℝ≥0∞`-valued measure comparison. -/
lemma probMeasure_apply_le_iff (μ ν : ProbabilityMeasure Ω) (A : Set Ω) :
    μ A ≤ ν A ↔ (μ : Measure Ω) A ≤ (ν : Measure Ω) A := by
  have h1 : μ A = ((μ : Measure Ω) A).toNNReal := rfl
  have h2 : ν A = ((ν : Measure Ω) A).toNNReal := rfl
  rw [h1, h2, ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)]

namespace FiniteBox

variable {E : Type*} [Countable E]

/-- The glue map is monotone in the interior configuration. -/
lemma glue_mono (B : FiniteBox E) (η : B.Exterior) {x y : B.Interior} (hxy : x ≤ y) :
    B.glue (η, x) ≤ B.glue (η, y) := by
  intro e
  by_cases he : e ∈ B.edges
  · simpa [glue, he] using hxy ⟨e, he⟩
  · simp [glue, he]

/-- The finite-box law is the FK law of the box pushed through the glue map. -/
lemma finiteVolumeLaw_coe {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (B : FiniteBox E) (α : B.BoundaryPartition) :
    ((B.finiteVolumeLaw hq hp α : ProbabilityMeasure (Configuration E)) :
        Measure (Configuration E))
      = Measure.map (fun x : B.Interior => B.glue (B.closedExterior, x))
          (B.graph.fkMeasure hq hp α) := rfl

/-- The mass of an event under the finite-box law is the FK mass of its pullback. -/
lemma finiteVolumeLaw_apply_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (B : FiniteBox E) (α : B.BoundaryPartition) (A : Set (Configuration E))
    (hA : MeasurableSet A) :
    ((B.finiteVolumeLaw hq hp α : ProbabilityMeasure (Configuration E)) :
        Measure (Configuration E)) A
      = B.graph.fkMeasure hq hp α
          ((fun x : B.Interior => B.glue (B.closedExterior, x)) ⁻¹' A) := by
  rw [finiteVolumeLaw_coe, Measure.map_apply (B.measurable_glue_const_left B.closedExterior) hA]

/-- **Free/wired sandwich for the actual finite-box laws**: every boundary
partition lies between the free and the wired one. -/
theorem finiteVolumeLaw_sandwich {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (B : FiniteBox E) (α : B.BoundaryPartition) :
    FKLimit.StochasticallyDominates (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp1.le α)
        (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp1.le B.graph.freeBoundary) ∧
      FKLimit.StochasticallyDominates
        (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp1.le B.graph.wiredBoundary)
        (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp1.le α) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  constructor
  · intro A hA hAup
    have hupper : IsUpperSet
        ((fun x : B.Interior => B.glue (B.closedExterior, x)) ⁻¹' A) := by
      intro x y hxy hx
      exact hAup (B.glue_mono B.closedExterior hxy) hx
    have hENN : ((B.finiteVolumeLaw hqpos hp1.le B.graph.freeBoundary :
          ProbabilityMeasure (Configuration E)) : Measure (Configuration E)) A
        ≤ ((B.finiteVolumeLaw hqpos hp1.le α :
          ProbabilityMeasure (Configuration E)) : Measure (Configuration E)) A := by
      rw [B.finiteVolumeLaw_apply_eq hqpos hp1.le B.graph.freeBoundary A hA,
        B.finiteVolumeLaw_apply_eq hqpos hp1.le α A hA]
      exact B.graph.fkMeasure_mono_wiring hq hp0 hp1 (B.graph.freeBoundary_le α) hupper
    exact (probMeasure_apply_le_iff _ _ A).mpr hENN
  · intro A hA hAup
    have hupper : IsUpperSet
        ((fun x : B.Interior => B.glue (B.closedExterior, x)) ⁻¹' A) := by
      intro x y hxy hx
      exact hAup (B.glue_mono B.closedExterior hxy) hx
    have hENN : ((B.finiteVolumeLaw hqpos hp1.le α :
          ProbabilityMeasure (Configuration E)) : Measure (Configuration E)) A
        ≤ ((B.finiteVolumeLaw hqpos hp1.le B.graph.wiredBoundary :
          ProbabilityMeasure (Configuration E)) : Measure (Configuration E)) A := by
      rw [B.finiteVolumeLaw_apply_eq hqpos hp1.le α A hA,
        B.finiteVolumeLaw_apply_eq hqpos hp1.le B.graph.wiredBoundary A hA]
      exact B.graph.fkMeasure_mono_wiring hq hp0 hp1 (B.graph.le_wiredBoundary α) hupper
    exact (probMeasure_apply_le_iff _ _ A).mpr hENN

end FiniteBox

/-- **Free/wired sandwich for FK weak limits**: any FK limit along the exhaustion
is sandwiched between any free and any wired weak limit.  This is the weak-limit
form of equation (6) of arXiv:2512.16486v1, Section 1.4. -/
theorem fkLimit_sandwich {E : Type*} [Countable E] (exh : BoxExhaustion E) {q p : NNReal}
    (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (μfree μ μwired : ProbabilityMeasure (Configuration E))
    (hfree : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp1.le
      (fun n => (exh.box n).graph.freeBoundary) μfree)
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp1.le α μ)
    (hwired : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp1.le
      (fun n => (exh.box n).graph.wiredBoundary) μwired) :
    FKLimit.StochasticallyDominates μ μfree ∧ FKLimit.StochasticallyDominates μwired μ := by
  constructor
  · exact FKLimit.stochasticallyDominates_of_tendsto hfree hμ
      (fun n => (FiniteBox.finiteVolumeLaw_sandwich hq hp0 hp1 (exh.box n) (α n)).1)
  · exact FKLimit.stochasticallyDominates_of_tendsto hμ hwired
      (fun n => (FiniteBox.finiteVolumeLaw_sandwich hq hp0 hp1 (exh.box n) (α n)).2)


/-! ## Mutual domination forces cylinder equality

The final block records the Boolean-lattice inversion alluded to in the module
summary: mutual stochastic domination forces equality of every finite-dimensional
cylinder mass.

Note: the `attribute [local instance] Classical.propDecidable` below is a local
decidability device for the pattern `Finset {e // e ∈ S}`, not a soundness flag.
-/

open Set

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {E : Type*} [Countable E]






/-- The cylinder of the "true-set" pattern `T` on the finite coordinate set `S`. -/
def cyT (S : Finset E) (T : Finset ↥S) : Set (Configuration E) :=
  {ω | ∀ e : ↥S, (ω e.1 = true ↔ e ∈ T)}

/-- The upper corner of the "true-set" pattern `T` on `S`. -/
def upT (S : Finset E) (T : Finset ↥S) : Set (Configuration E) :=
  {ω | ∀ e : ↥S, e ∈ T → ω e.1 = true}

lemma dependsOn_cyT (S : Finset E) (T : Finset ↥S) : FKLimit.DependsOnCoordinates (cyT S T) S := by
  intro ω η h
  have hiff : ∀ e : ↥S, (ω e.1 = true) ↔ (η e.1 = true) := fun e => by rw [h e.1 e.2]
  simp only [cyT, Set.mem_ofPred_eq]
  exact forall_congr' (fun e => by rw [hiff e])

lemma dependsOn_upT (S : Finset E) (T : Finset ↥S) : FKLimit.DependsOnCoordinates (upT S T) S := by
  intro ω η h
  have hiff : ∀ e : ↥S, (ω e.1 = true) ↔ (η e.1 = true) := fun e => by rw [h e.1 e.2]
  simp only [upT, Set.mem_ofPred_eq]
  exact forall_congr' (fun e => by rw [hiff e])

lemma measurableSet_cyT (S : Finset E) (T : Finset ↥S) : MeasurableSet (cyT S T) :=
  (dependsOn_cyT S T).measurableSet

lemma measurableSet_upT (S : Finset E) (T : Finset ↥S) : MeasurableSet (upT S T) :=
  (dependsOn_upT S T).measurableSet

lemma isUpperSet_upT (S : Finset E) (T : Finset ↥S) : IsUpperSet (upT S T) := by
  intro ω η hωη hω e he
  exact hωη e.1 (hω e he)

lemma cyT_subset_upT {S : Finset E} {T U : Finset ↥S} (hTU : T ⊆ U) : cyT S U ⊆ upT S T := by
  intro ω hω e he
  rw [hω e]
  exact hTU he

/-- The upper corner is the disjoint union of the cylinders of the true-sets above it. -/
theorem upT_eq_biUnion (S : Finset E) (T : Finset ↥S) :
    upT S T = ⋃ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊆ U), cyT S U := by
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hω
    refine ⟨Finset.univ.filter (fun e : ↥S => ω e.1 = true), ?_, ?_⟩
    · intro e he
      simpa using hω e he
    · intro e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rintro ⟨U, hTU, hω⟩ e he
    rw [hω e]
    exact hTU he

lemma pairwiseDisjoint_cyT (S : Finset E) (T : Finset ↥S) :
    (↑(Finset.univ.filter (fun U : Finset ↥S => T ⊆ U)) : Set (Finset ↥S)).PairwiseDisjoint
      (cyT S) := by
  intro U _ V _ hUV
  refine Set.disjoint_left.mpr ?_
  intro ω hωU hωV
  exact hUV (by ext e; rw [← hωU e, ← hωV e])









/-- **Cylinder masses are determined by upper-corner masses.**  If two probability
measures on the configuration space agree on all upper corners of patterns on a
finite coordinate set `S`, they agree on every cylinder over `S`. -/
theorem cylinder_eq_of_upT_eq (S : Finset E) (μ ν : ProbabilityMeasure (Configuration E))
    (hdom : ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A →
      (μ : Measure (Configuration E)) A ≤ (ν : Measure (Configuration E)) A)
    (hdom' : ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A →
      (ν : Measure (Configuration E)) A ≤ (μ : Measure (Configuration E)) A)
    (T : Finset ↥S) : μ (cyT S T) = ν (cyT S T) := by
  classical
  have key : ∀ k : ℕ, ∀ W : Finset ↥S, (Finset.univ \ W).card = k →
      (μ : Measure (Configuration E)) (cyT S W) =
        (ν : Measure (Configuration E)) (cyT S W) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro W hk
      have hdecomp : Finset.univ.filter (fun U : Finset ↥S => W ⊆ U) =
          insert W (Finset.univ.filter (fun U : Finset ↥S => W ⊂ U)) := by
        ext U
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hWU
          by_cases h : U = W
          · exact Or.inl h
          · exact Or.inr ⟨hWU, fun hUW => h (Finset.Subset.antisymm hUW hWU)⟩
        · rintro (rfl | ⟨hWU, -⟩)
          · exact le_refl _
          · exact hWU
      have hnotmem : W ∉ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        exact h.2 (le_refl W)
      have hsum : ∀ ζ : ProbabilityMeasure (Configuration E),
          (ζ : Measure (Configuration E)) (upT S W) =
            (ζ : Measure (Configuration E)) (cyT S W) +
              ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
                (ζ : Measure (Configuration E)) (cyT S U) := by
        intro ζ
        rw [upT_eq_biUnion,
          measure_biUnion_finset (pairwiseDisjoint_cyT S W) (fun U _ => measurableSet_cyT S U),
          hdecomp, Finset.sum_insert hnotmem]
      have hupper : (μ : Measure (Configuration E)) (upT S W) =
          (ν : Measure (Configuration E)) (upT S W) :=
        le_antisymm (hdom _ (measurableSet_upT S W) (isUpperSet_upT S W))
          (hdom' _ (measurableSet_upT S W) (isUpperSet_upT S W))
      have hIH : ∀ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
          (μ : Measure (Configuration E)) (cyT S U) =
            (ν : Measure (Configuration E)) (cyT S U) := by
        intro U hU
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
        refine ih ((Finset.univ \ U).card) ?_ U rfl
        have hlt : (Finset.univ \ U).card < (Finset.univ \ W).card := by
          rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ]
          exact Nat.sub_lt_sub_left
            (lt_of_lt_of_le (Finset.card_lt_card hU) (Finset.card_le_univ U))
            (Finset.card_lt_card hU)
        rwa [hk] at hlt
      have hsumEq : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (μ : Measure (Configuration E)) (cyT S U)) =
          ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (ν : Measure (Configuration E)) (cyT S U) :=
        Finset.sum_congr rfl hIH
      have hle : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
          (μ : Measure (Configuration E)) (cyT S U)) ≤ 1 := by
        have h1 : (μ : Measure (Configuration E)) (cyT S W) +
            (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
              (μ : Measure (Configuration E)) (cyT S U)) =
            (μ : Measure (Configuration E)) (upT S W) := (hsum μ).symm
        have h2 : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
            (μ : Measure (Configuration E)) (cyT S U)) ≤
            (μ : Measure (Configuration E)) (cyT S W) +
              (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
                (μ : Measure (Configuration E)) (cyT S U)) := le_add_left le_rfl
        rw [h1] at h2
        refine h2.trans ?_
        calc (μ : Measure (Configuration E)) (upT S W)
            ≤ (μ : Measure (Configuration E)) Set.univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      have hfin : (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
          (μ : Measure (Configuration E)) (cyT S U)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top hle
      have hmain : (μ : Measure (Configuration E)) (cyT S W) +
            (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
              (μ : Measure (Configuration E)) (cyT S U)) =
          (ν : Measure (Configuration E)) (cyT S W) +
            (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => W ⊂ U),
              (μ : Measure (Configuration E)) (cyT S U)) := by
        rw [← hsum μ, hupper, hsum ν, hsumEq]
      exact (ENNReal.add_left_inj hfin).mp hmain
  have h := key (Finset.univ \ T).card T rfl
  have hcoeμ : ((μ (cyT S T) : ℝ≥0) : ℝ≥0∞) = (μ : Measure (Configuration E)) (cyT S T) := by
    rw [show μ (cyT S T) = ((μ : Measure (Configuration E)) (cyT S T)).toNNReal from rfl,
      ENNReal.coe_toNNReal (measure_ne_top _ _)]
  have hcoeν : ((ν (cyT S T) : ℝ≥0) : ℝ≥0∞) = (ν : Measure (Configuration E)) (cyT S T) := by
    rw [show ν (cyT S T) = ((ν : Measure (Configuration E)) (cyT S T)).toNNReal from rfl,
      ENNReal.coe_toNNReal (measure_ne_top _ _)]
  have hnn : ((μ (cyT S T) : ℝ≥0) : ℝ≥0∞) = ((ν (cyT S T) : ℝ≥0) : ℝ≥0∞) := by
    rw [hcoeμ, hcoeν, h]
  exact ENNReal.coe_injective hnn








/-- **Mutual stochastic domination forces equality of cylinder masses.**  On a
countable product of two-point spaces, two probability measures that dominate each
other in the stochastic order agree on every finite-dimensional cylinder. -/
theorem cylinder_eq_of_mutual_stochasticallyDominates
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμν : FKLimit.StochasticallyDominates ν μ)
    (hνμ : FKLimit.StochasticallyDominates μ ν) :
    ∀ (S : Finset E) (W : Finset ↥S), μ (cyT S W) = ν (cyT S W) := by
  have hdom : ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A →
      (μ : Measure (Configuration E)) A ≤ (ν : Measure (Configuration E)) A :=
    fun A hA hAup => (probMeasure_apply_le_iff μ ν A).mp (hμν A hA hAup)
  have hdom' : ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A →
      (ν : Measure (Configuration E)) A ≤ (μ : Measure (Configuration E)) A :=
    fun A hA hAup => (probMeasure_apply_le_iff ν μ A).mp (hνμ A hA hAup)
  intro S W
  exact cylinder_eq_of_upT_eq S μ ν hdom hdom' W

/-- **Consequence of the free/wired sandwich**: if the free and the wired schedule
converge to the same law `φ`, then every FK weak limit along the exhaustion has the
same cylinder masses as `φ`.  This is the usable form of equation (6) of
arXiv:2512.16486v1, Section 1.4. -/
theorem fkLimit_cylinder_eq_of_free_eq_wired (exh : BoxExhaustion E) {q p : NNReal}
    (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (α : ∀ n, (exh.box n).BoundaryPartition) (φ μ : ProbabilityMeasure (Configuration E))
    (hfree : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp1.le
      (fun n => (exh.box n).graph.freeBoundary) φ)
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp1.le α μ)
    (hwired : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp1.le
      (fun n => (exh.box n).graph.wiredBoundary) φ) :
    ∀ (S : Finset E) (W : Finset ↥S), μ (cyT S W) = φ (cyT S W) := by
  obtain ⟨hsand₁, hsand₂⟩ := fkLimit_sandwich exh hq hp0 hp1 α φ μ φ hfree hμ hwired
  exact cylinder_eq_of_mutual_stochasticallyDominates hsand₂ hsand₁


end FK.InfiniteVolume
