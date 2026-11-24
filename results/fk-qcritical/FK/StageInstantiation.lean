/-
Formalization of normalized FK monotonicity and no-escape on genuine finite-box stages.

# Genuine `finiteVolumeLaw` stages for the edge-domain no-escape reduction

This file discharges the two missing inputs of
`FK.InfiniteVolume.NoEscape.noEscape_of_stage_mono` for genuine finite-volume
laws on a fixed-vertex nested edge exhaustion:

* `PosAssoc` (the named positive-association input of
  `FK.EdgeDomainMonotonicity.fkMeasure_le_of_inj`) is **proved** from the
  normalized finite FKG theorem `fkPMF_association_events` of `FK.WiredFKG`,
  using the exact point-mass identity for `fkMeasure`;
* the stage-monotonicity hypothesis `hmono` is derived from
  `fkMeasure_le_of_inj` for the actual `FiniteBox.finiteVolumeLaw` stages with
  `interiorRestriction` cylinder events and the edge injection of a nested
  exhaustion.

Neither `PosAssoc` nor stage monotonicity is assumed; both are conclusions
here.
-/
import FK.EdgeDomainMonotonicity
import FK.WiredFKG
import FK.InfiniteVolume
import FK.QOneLine

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite

/-! ## Part 1: point masses of the real-valued finite FK measure -/

/-- Real indicator of an event, in a form that needs no decidable predicate
instance in statements. -/
def indR {α : Type*} (B : Set α) : α → ℝ := by
  classical
  exact fun a => if a ∈ B then 1 else 0

lemma indR_of_mem {α : Type*} {B : Set α} {a : α} (h : a ∈ B) : indR B a = 1 := by
  classical
  simp [indR, h]

lemma indR_of_notMem {α : Type*} {B : Set α} {a : α} (h : a ∉ B) : indR B a = 0 := by
  classical
  simp [indR, h]

lemma indR_union_of_disjoint {α : Type*} {B C : Set α} (h : Disjoint B C) (a : α) :
    indR (B ∪ C) a = indR B a + indR C a := by
  classical
  by_cases hb : a ∈ B
  · have hbc : a ∈ B ∪ C := Or.inl hb
    have hc : a ∉ C := fun hc => Set.disjoint_left.mp h hb hc
    rw [indR_of_mem hbc, indR_of_mem hb, indR_of_notMem hc]; ring
  · by_cases hc : a ∈ C
    · have hbc : a ∈ B ∪ C := Or.inr hc
      rw [indR_of_mem hbc, indR_of_notMem hb, indR_of_mem hc]; ring
    · have hnot : a ∉ B ∪ C := by
        rintro (h' | h')
        · exact hb h'
        · exact hc h'
      rw [indR_of_notMem hnot, indR_of_notMem hb, indR_of_notMem hc]; ring

lemma indR_inter {α : Type*} {B C : Set α} (a : α) :
    indR (B ∩ C) a = indR B a * indR C a := by
  classical
  by_cases hb : a ∈ B <;> by_cases hc : a ∈ C
  · rw [indR_of_mem (show a ∈ B ∩ C from ⟨hb, hc⟩), indR_of_mem hb, indR_of_mem hc]; ring
  · rw [indR_of_notMem (show a ∉ B ∩ C from fun h => hc h.2), indR_of_mem hb,
      indR_of_notMem hc]; ring
  · rw [indR_of_notMem (show a ∉ B ∩ C from fun h => hb h.1), indR_of_notMem hb]; ring
  · rw [indR_of_notMem (show a ∉ B ∩ C from fun h => hb h.1), indR_of_notMem hb]; ring

/-- Splitting a real point-mass sum over two disjoint events. -/
theorem sum_indR_union {α : Type*} [Fintype α] (P : α → ℝ) {B C : Set α}
    (hBC : Disjoint B C) :
    ∑ a, P a * indR (B ∪ C) a
      = ∑ a, P a * indR B a + ∑ a, P a * indR C a := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [indR_union_of_disjoint hBC a, mul_add]

/-- The real mass of an event under `fkMeasure` is the sum of its point masses. -/
theorem fkMeasure_toReal_eq_sum_indicator {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) (B : Set G.Configuration) :
    ((G.fkMeasure hq hp ξ) B).toReal
      = ∑ ω : G.Configuration, (G.fkPMF hq hp ξ ω).toReal * indR B ω := by
  classical
  have hsplit := measure_eq_sum_singleton' (G.fkMeasure hq hp ξ) B
  rw [hsplit, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : a ∈ B
  · rw [ite_eq_left h, indR_of_mem h, mul_one,
      FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
  · rw [ite_eq_right h, indR_of_notMem h, mul_zero]

/-- The real point masses of a finite FK law sum to one. -/
theorem fkPMF_toReal_sum_one {G : LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) :
    ∑ ω : G.Configuration, (G.fkPMF hq hp ξ ω).toReal = 1 := by
  classical
  have h := fkMeasure_toReal_eq_sum_indicator (G := G) hq hp ξ (Set.univ : Set G.Configuration)
  rw [measure_univ, ENNReal.toReal_one] at h
  rw [h]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [indR_of_mem (Set.mem_univ a), mul_one]

/-! ## Part 2: positive association in the shape required by `PosAssoc` -/

/-- Abstract splitting step: from the association inequality for an increasing
event and the complement of a decreasing event, derive the correlation
inequality for the increasing event and the decreasing event. -/
theorem real_association_split {α : Type*} [Fintype α] (P : α → ℝ) {A D : Set α}
    (hassoc :
      (∑ a, P a * indR A a) * (∑ a, P a * indR Dᶜ a)
        ≤ ∑ a, P a * indR (A ∩ Dᶜ) a)
    (hP : ∑ a, P a = 1) :
    ∑ a, P a * indR (A ∩ D) a
      ≤ (∑ a, P a * indR A a) * (∑ a, P a * indR D a) := by
  classical
  have hAdisj : Disjoint (A ∩ Dᶜ) (A ∩ D) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact ha.2 hb.2
  have hAunion : (A ∩ Dᶜ) ∪ (A ∩ D) = A := by
    ext a
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have hA : ∑ a, P a * indR A a
      = (∑ a, P a * indR (A ∩ Dᶜ) a) + ∑ a, P a * indR (A ∩ D) a := by
    rw [← sum_indR_union P hAdisj, hAunion]
  have hD : (∑ a, P a * indR D a) + (∑ a, P a * indR Dᶜ a) = 1 := by
    have h := sum_indR_union P (disjoint_compl_right (a := D))
    rw [Set.union_compl_self] at h
    have huniv : ∑ a, P a * indR (Set.univ : Set α) a = ∑ a, P a :=
      Finset.sum_congr rfl (fun a _ => by rw [indR_of_mem (Set.mem_univ a), mul_one])
    rw [← h, huniv]
    exact hP
  have step : (∑ a, P a * indR A a) * (1 - ∑ a, P a * indR D a)
      ≤ (∑ a, P a * indR A a) - ∑ a, P a * indR (A ∩ D) a := by
    have hDc : ∑ a, P a * indR Dᶜ a = 1 - ∑ a, P a * indR D a := by linarith [hD]
    have hAs : ∑ a, P a * indR (A ∩ Dᶜ) a
        = (∑ a, P a * indR A a) - ∑ a, P a * indR (A ∩ D) a := by linarith [hA]
    rw [← hDc, ← hAs]
    exact hassoc
  nlinarith [step]

/-- **Positive association of the actual normalized finite FK measures** in the
event shape used by `FK.InfiniteVolume.NoEscape.PosAssoc`: for `q ≥ 1` and
`0 < p < 1`, an increasing event and a decreasing event are nonnegatively
correlated.  This is a conversion of the accepted normalized finite FKG
theorem `fkPMF_association_events`, not a new association proof. -/
theorem posAssoc_of_fkPMF {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1) :
    PosAssoc q p (lt_of_lt_of_le zero_lt_one hq) hp1.le := by
  classical
  intro G ξ A D hA hD
  -- association for the increasing events `A` and `Dᶜ`
  have hAup : ∀ x y : G.Configuration, x ≤ y → (fun ω => ω ∈ A) x → (fun ω => ω ∈ A) y :=
    fun x y hxy hx => hA x hx y hxy
  have hDcup : ∀ x y : G.Configuration, x ≤ y → (fun ω => ω ∈ Dᶜ) x → (fun ω => ω ∈ Dᶜ) y := by
    intro x y hxy hx hy
    exact hx (hD y hy x hxy)
  have hassoc := G.fkPMF_association_events hq hp0 hp1 ξ hAup hDcup
  -- convert the `FinFKG.indicator` factor of an event into `indR`
  have key : ∀ (X : Set G.Configuration) (ω : G.Configuration),
      FinFKG.indicator (fun ω => ω ∈ X) ω = indR X ω := by
    intro X ω
    unfold FinFKG.indicator indR
    by_cases h : ω ∈ X <;> simp [h]
  have hsumA : (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal
        * FinFKG.indicator (fun ω => ω ∈ A) ω)
      = ∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR A ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold FinFKG.indicator indR
    by_cases h : ω ∈ A <;> simp [h]
  have hsumDc : (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal
        * FinFKG.indicator (fun ω => ω ∈ Dᶜ) ω)
      = ∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR Dᶜ ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold FinFKG.indicator indR
    by_cases h : ω ∈ Dᶜ <;> simp [h]
  have hprod : (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal
        * FinFKG.indicator (fun ω => ω ∈ A) ω * FinFKG.indicator (fun ω => ω ∈ Dᶜ) ω)
      = ∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal
          * indR (A ∩ Dᶜ) ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold FinFKG.indicator indR
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ Dᶜ <;> simp [h1, h2]
  have hassoc' :
      (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR A ω)
          * (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR Dᶜ ω)
        ≤ (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal)
          * (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal
              * indR (A ∩ Dᶜ) ω) := by
    simpa only [hsumA, hsumDc, hprod] using hassoc
  -- the real mass of an event is its point-mass sum
  have hmass : ∀ X : Set G.Configuration,
      ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) X).toReal
        = ∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR X ω :=
    fun X => fkMeasure_toReal_eq_sum_indicator _ hp1.le ξ X
  have hP : ∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal = 1 :=
    fkPMF_toReal_sum_one _ hp1.le ξ
  have hassoc'' : (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR A ω)
        * (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR Dᶜ ω)
      ≤ ∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * indR (A ∩ Dᶜ) ω := by
    simpa only [hP, one_mul] using hassoc'
  have hreal : ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) (A ∩ D)).toReal
      ≤ ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) A).toReal
        * ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) D).toReal := by
    rw [hmass (A ∩ D), hmass A, hmass D]
    exact real_association_split _ hassoc'' hP
  have hfin1 : ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) (A ∩ D)) ≠ ⊤ :=
    measure_ne_top _ _
  have hfinA : ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) A) ≠ ⊤ :=
    measure_ne_top _ _
  have hfinD : ((G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ) D) ≠ ⊤ :=
    measure_ne_top _ _
  refine (ENNReal.toReal_le_toReal hfin1 (ENNReal.mul_ne_top hfinA hfinD)).mp ?_
  rw [ENNReal.toReal_mul]
  exact hreal

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite

/-! ## Part 3: genuine `FiniteBox.finiteVolumeLaw` stages with `interiorRestriction` -/

/-- A nested family of genuine finite boxes sharing one finite vertex type: the
free-boundary and arbitrary-boundary edge exhaustion used below.  Every stage is
an actual `FiniteBox` with the same vertices, and the edge labels are nested. -/
structure FixedVertexFamily (E V : Type) [Fintype V] where
  /-- Edge labels used at stage `n`. -/
  edges : ℕ → Finset E
  /-- Source map of the ambient labelled multigraph. -/
  src : E → V
  /-- Target map of the ambient labelled multigraph. -/
  tgt : E → V
  /-- The stages are nested. -/
  monotone : Monotone edges

namespace FixedVertexFamily

variable {E V : Type} [Fintype V] (F : FixedVertexFamily E V)

/-- The genuine `FiniteBox` of stage `n`; loops and parallel labels are kept. -/
def box (n : ℕ) : FiniteBox E where
  Vertex := V
  edges := F.edges n
  source := fun e => F.src e.1
  target := fun e => F.tgt e.1

@[simp] lemma box_edges (n : ℕ) : (F.box n).edges = F.edges n := rfl

/-- The common boundary setoid read as a boundary partition of stage `n`. -/
def stageBoundary (n : ℕ) (ξ : Setoid V) : (F.box n).BoundaryPartition := ξ

/-- The `finiteVolumeLaw` mass of an `interiorRestriction` cylinder is the mass
of the interior event under the actual finite FK measure of the box graph. -/
theorem finiteVolumeLaw_apply_interiorRestriction {q p : NNReal} {E : Type}
    (B : FiniteBox E) (α : B.BoundaryPartition) (hq : 0 < q)
    (hp : p ≤ 1) (S : Set B.Interior) :
    (B.finiteVolumeLaw hq hp α : Measure (Configuration E)) (B.interiorRestriction ⁻¹' S)
      = B.graph.fkMeasure hq hp α S := by
  classical
  have hdep : FKLimit.DependsOnCoordinates (B.interiorRestriction ⁻¹' S) B.edges := by
    intro ω η hωη
    have hfun : B.interiorRestriction ω = B.interiorRestriction η := by
      funext e
      exact hωη e.1 e.2
    rw [Set.mem_preimage, Set.mem_preimage, hfun]
  have hmeas : MeasurableSet (B.interiorRestriction ⁻¹' S) := hdep.measurableSet
  change (Measure.map (fun ω : B.Interior => B.glue (B.closedExterior, ω))
    (B.graph.fkMeasure hq hp α)) (B.interiorRestriction ⁻¹' S) = _
  rw [Measure.map_apply (B.measurable_glue_const_left B.closedExterior) hmeas]
  have hset : (fun ω : B.Interior => B.glue (B.closedExterior, ω)) ⁻¹'
      (B.interiorRestriction ⁻¹' S) = S := by
    ext ω
    simp
  rw [hset]

end FixedVertexFamily

namespace FixedVertexFamily

variable {E V : Type} [Fintype V] [DecidableEq V] [DecidableEq E] (F : FixedVertexFamily E V)

/-- The edge injection of a smaller stage into a larger stage of the family. -/
def stageIncl {m k : ℕ} (hmk : m ≤ k) : (F.box m).edges → (F.box k).edges :=
  fun e => ⟨e.1, F.monotone hmk e.2⟩

lemma stageIncl_injective {m k : ℕ} (hmk : m ≤ k) : Function.Injective (F.stageIncl hmk) := by
  intro a b hab
  have h : (a : E) = (b : E) := congrArg (fun x : (F.box k).edges => (x : E)) hab
  exact Subtype.ext h

lemma stageIncl_source {m k : ℕ} (hmk : m ≤ k) (e : (F.box m).edges) :
    (F.box k).source (F.stageIncl hmk e) = (F.box m).source e := rfl

lemma stageIncl_target {m k : ℕ} (hmk : m ≤ k) (e : (F.box m).edges) :
    (F.box k).target (F.stageIncl hmk e) = (F.box m).target e := rfl

/-- The interior readout of a `k`-stage cylinder over stage `m` is exactly the
restriction of the `k`-interior configuration to the embedded edge labels. -/
lemma interiorRestriction_eq_res {m k : ℕ} (hmk : m ≤ k) (ω : Configuration E) :
    (F.box m).interiorRestriction ω
      = res (F.stageIncl hmk) ((F.box k).interiorRestriction ω) := rfl

lemma preimage_interiorRestriction_stage {m k : ℕ} (hmk : m ≤ k)
    (A : Set (F.box m).Interior) :
    ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box k).interiorRestriction ⁻¹' (res (F.stageIncl hmk) ⁻¹' A) := by
  ext ω
  show (F.box m).interiorRestriction ω ∈ A ↔
    res (F.stageIncl hmk) ((F.box k).interiorRestriction ω) ∈ A
  rw [interiorRestriction_eq_res]

/-- **Stage monotonicity of the genuine finite-volume laws.**  For nested stages
of one fixed-vertex labelled multigraph and any increasing interior event, the
stage mass at the smaller box is at most the larger box's mass of the lifted
event.  This is `fkMeasure_le_of_inj` at the level of the actual
`FiniteBox.finiteVolumeLaw` pushforwards. -/
theorem finiteVolumeLaw_stage_mono {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hp1 : p < 1) (hPA : PosAssoc q p hq hp) (ξ : Setoid V)
    {m k : ℕ} (hmk : m ≤ k) {A : Set (F.box m).Interior} (hA : IsUp A) :
    (((F.box m).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
        ((F.box m).interiorRestriction ⁻¹' A))
      ≤ (((F.box k).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
        ((F.box m).interiorRestriction ⁻¹' A)) := by
  classical
  have hcomp := fkMeasure_le_of_inj (V := V) (E₁ := (F.box m).edges) (E₂ := (F.box k).edges)
    (src₁ := (F.box m).source) (tgt₁ := (F.box m).target)
    (src₂ := (F.box k).source) (tgt₂ := (F.box k).target)
    (ι := F.stageIncl hmk) (F.stageIncl_injective hmk) (fun e => rfl) (fun e => rfl)
    hq hp hp1 (ξ := ξ) hPA (A := A) hA
  have hL : ((F.box m).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
      ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box m).graph.fkMeasure hq hp ξ A :=
    finiteVolumeLaw_apply_interiorRestriction (B := F.box m) ξ hq hp A
  have hR : ((F.box k).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
      ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box k).graph.fkMeasure hq hp ξ (res (F.stageIncl hmk) ⁻¹' A) := by
    rw [preimage_interiorRestriction_stage]
    exact finiteVolumeLaw_apply_interiorRestriction (B := F.box k) ξ hq hp _
  calc ((F.box m).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
        ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box m).graph.fkMeasure hq hp ξ A := hL
    _ ≤ (F.box k).graph.fkMeasure hq hp ξ (res (F.stageIncl hmk) ⁻¹' A) := hcomp
    _ = ((F.box k).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
        ((F.box m).interiorRestriction ⁻¹' A) := hR.symm

end FixedVertexFamily

/-! ## Part 4: instantiated no-mass-escape for genuine stages -/

open FixedVertexFamily

/-- The stage cylinder of a nested family is a finitely supported event, hence
clopen in the product topology. -/
theorem isClopen_stageCylinder {E V : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (F : FixedVertexFamily E V) (A : (n : ℕ) → Set (F.box n).Interior) (k : ℕ) :
    IsClopen ((F.box k).interiorRestriction ⁻¹' A k) := by
  have hdep : FKLimit.DependsOnCoordinates ((F.box k).interiorRestriction ⁻¹' A k)
      (F.box k).edges := by
    intro ω η hωη
    have hfun : (F.box k).interiorRestriction ω = (F.box k).interiorRestriction η := by
      funext e
      exact hωη e.1 e.2
    rw [Set.mem_preimage, Set.mem_preimage, hfun]
  exact hdep.isClopen

/-- **No mass escape for the genuine finite-volume stages.**  On a nested
fixed-vertex edge exhaustion, with `PosAssoc` proved in Part 2 and stage
monotonicity proved in Part 3, the analytic no-escape reduction
`FK.InfiniteVolume.NoEscape.noEscape_of_stage_mono` is instantiated at the
actual `FiniteBox.finiteVolumeLaw` stages.  No stage monotonicity hypothesis is
assumed: it is derived from the edge injection. -/
theorem noEscape_of_finiteVolumeLaw_stage {E V : Type} [Fintype V] [DecidableEq V]
    [DecidableEq E] [Countable E] (F : FixedVertexFamily E V)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (hp1 : p < 1)
    (hPA : PosAssoc q p hq hp) (ξ : Setoid V)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto (fun n => (F.box n).finiteVolumeLaw hq hp ξ) atTop (𝓝 μ))
    (A : (n : ℕ) → Set (F.box n).Interior)
    (hAup : ∀ n, IsUp (A n))
    (hCmono : Monotone (fun k => (F.box k).interiorRestriction ⁻¹' A k))
    {Cinf : Set (Configuration E)}
    (hCunion : ∀ ω, (∃ k, ω ∈ (F.box k).interiorRestriction ⁻¹' A k) ↔ ω ∈ Cinf) :
    Filter.limsup (fun k => (((F.box k).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
        ((F.box k).interiorRestriction ⁻¹' A k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
  have hCcl : ∀ k, IsClopen ((F.box k).interiorRestriction ⁻¹' A k) :=
    fun k => isClopen_stageCylinder F A k
  have hmono : ∀ m k, m ≤ k →
      (((F.box m).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
          ((F.box m).interiorRestriction ⁻¹' A m))
        ≤ (((F.box k).finiteVolumeLaw hq hp ξ : Measure (Configuration E))
          ((F.box m).interiorRestriction ⁻¹' A m)) :=
    fun m k hmk => finiteVolumeLaw_stage_mono (F := F) hq hp hp1 hPA ξ hmk (hAup m)
  exact noEscape_of_stage_mono (fun n => (F.box n).finiteVolumeLaw hq hp ξ) μ hμ
    (C := fun k => (F.box k).interiorRestriction ⁻¹' A k) hCcl hCmono hCunion hmono

/-! ## Part 5: a concrete genuine instance (one vertex, all labels loops) -/

/-- The one-vertex family with loop labels `0, 1, …, n` at stage `n`.  Loops are
kept: every label joins the single vertex to itself, so the boundary setoid is
free and no label is lost. -/
def loopFamily : FixedVertexFamily ℕ PUnit where
  edges n := Finset.range (n + 1)
  src _ := PUnit.unit
  tgt _ := PUnit.unit
  monotone := by
    intro m k hmk e he
    simp only [Finset.mem_range] at he ⊢
    omega

/-- Membership in the stage edge set of `loopFamily`. -/
@[simp] lemma loopFamily_mem_edges {n j : ℕ} : j ∈ (loopFamily.box n).edges ↔ j < n + 1 := by
  simp [loopFamily, FixedVertexFamily.box]

/-- At stage `n`, some loop label in `{1, …, n}` is open. -/
def loopEvent (n : ℕ) : Set (loopFamily.box n).Interior :=
  {β | ∃ j : (loopFamily.box n).edges, 1 ≤ (j : ℕ) ∧ β j = true}

theorem loopEvent_isUp (n : ℕ) : IsUp (loopEvent n) := by
  rintro β ⟨j, hj, hβ⟩ γ hβγ
  refine ⟨j, hj, ?_⟩
  have := hβγ j
  rw [Bool.le_iff_imp] at this
  exact this hβ

theorem loopEvent_mono : Monotone (fun k => (loopFamily.box k).interiorRestriction ⁻¹'
    loopEvent k) := by
  intro m k hmk ω hω
  obtain ⟨j, hj, hβ⟩ := hω
  have hjm : (j : ℕ) < m + 1 := loopFamily_mem_edges.mp j.2
  have hjk : (j : ℕ) < k + 1 := by omega
  exact ⟨⟨j.1, loopFamily_mem_edges.mpr hjk⟩, hj, hβ⟩

theorem loopEvent_union :
    ∀ ω : Configuration ℕ,
      (∃ k, ω ∈ (loopFamily.box k).interiorRestriction ⁻¹' loopEvent k) ↔
        ω ∈ {ω | ∃ j : ℕ, 1 ≤ j ∧ ω j = true} := by
  intro ω
  constructor
  · rintro ⟨k, j, hj, hβ⟩
    exact ⟨j.1, hj, hβ⟩
  · rintro ⟨j, hj, hω⟩
    exact ⟨j, ⟨⟨j, loopFamily_mem_edges.mpr (by omega)⟩, hj, hω⟩⟩

/-- **Concrete no-escape conclusion on a genuine FK stage family.**  For the
one-vertex loop exhaustion with free boundary (`ξ = freeBoundary`) and any
`q ≥ 1`, `0 < p < 1`, every limit point of the actual `finiteVolumeLaw` stages
satisfies `limsup_k stage_k(C_k) ≤ μ(C_∞)` for the increasing clopen events
`C_k = {some loop in 1..k is open}`.  The association input is the proved
`posAssoc_of_fkPMF`, not a hypothesis. -/
theorem loopFamily_noEscape {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (μ : ProbabilityMeasure (Configuration ℕ))
    (hμ : Tendsto (fun n => (loopFamily.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp1.le
      (FK.Finite.LabelledMultigraph.freeBoundary (loopFamily.box 0).graph)) atTop (𝓝 μ)) :
    Filter.limsup (fun k => (((loopFamily.box k).finiteVolumeLaw
        (lt_of_lt_of_le zero_lt_one hq) hp1.le
        (FK.Finite.LabelledMultigraph.freeBoundary (loopFamily.box 0).graph) :
          Measure (Configuration ℕ))
        ((loopFamily.box k).interiorRestriction ⁻¹' loopEvent k)).toReal) atTop
      ≤ ((μ : Measure (Configuration ℕ))
        {ω : Configuration ℕ | ∃ j : ℕ, 1 ≤ j ∧ ω j = true}).toReal := by
  refine noEscape_of_finiteVolumeLaw_stage (F := loopFamily)
    (lt_of_lt_of_le zero_lt_one hq) hp1.le hp1 (posAssoc_of_fkPMF hq hp0 hp1) _ μ ?_
    loopEvent loopEvent_isUp loopEvent_mono loopEvent_union
  exact hμ

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite
open FixedVertexFamily

variable {E V : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {F : FixedVertexFamily E V}

/-! ## Part 6: the endpoint parameters `p = 0` and `p = 1` -/

/-- At `p = 1` the finite FK measure is the Dirac mass at the all-open
configuration. -/
theorem fkMeasure_one_eq_dirac {G : LabelledMultigraph} {q : NNReal} (hq : 0 < q)
    (ξ : G.BoundaryPartition) :
    G.fkMeasure hq (le_rfl : (1 : NNReal) ≤ 1) ξ = Measure.dirac G.allOpen := by
  unfold LabelledMultigraph.fkMeasure
  rw [LabelledMultigraph.fkPMF_one G hq ξ]
  exact PMF.toMeasure_pure G.allOpen

/-- At `p = 0` the finite FK measure is the Dirac mass at the all-closed
configuration. -/
theorem fkMeasure_zero_eq_dirac {G : LabelledMultigraph} {q : NNReal} (hq : 0 < q)
    (ξ : G.BoundaryPartition) :
    G.fkMeasure hq (zero_le : (0 : NNReal) ≤ 1) ξ = Measure.dirac G.allClosed := by
  unfold LabelledMultigraph.fkMeasure
  rw [LabelledMultigraph.fkPMF_zero G hq ξ]
  exact PMF.toMeasure_pure G.allClosed

/-- A Dirac measure gives mass zero to any set avoiding its atom. -/
theorem dirac_apply_of_notMem' {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a : α} {s : Set α} (h : a ∉ s) : Measure.dirac a s = 0 := by
  rw [Measure.dirac_apply]
  simp [Set.indicator, h]

/-- A Dirac mass at `f a` on `S` is dominated by the Dirac mass at `a` on the
preimage of `S`. -/
theorem dirac_preimage_le_dirac {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (a : α) (S : Set β) :
    Measure.dirac (f a) S ≤ Measure.dirac a (f ⁻¹' S) := by
  by_cases h : f a ∈ S
  · rw [Measure.dirac_apply_of_mem h, Measure.dirac_apply_of_mem (Set.mem_preimage.mpr h)]
  · rw [dirac_apply_of_notMem' h]
    exact zero_le

/-- **Positive association at `p = 0`**: the law is the Dirac mass at the
all-closed configuration, so every correlation inequality is trivial. -/
theorem posAssoc_zero {q : NNReal} (hq : 0 < q) : PosAssoc q 0 hq zero_le := by
  intro G ξ A D hA hD
  rw [fkMeasure_zero_eq_dirac hq ξ]
  by_cases h : G.allClosed ∈ A ∩ D
  · have h1 : G.allClosed ∈ A := h.1
    have h2 : G.allClosed ∈ D := h.2
    rw [Measure.dirac_apply_of_mem h, Measure.dirac_apply_of_mem h1,
      Measure.dirac_apply_of_mem h2]
    simp
  · rw [dirac_apply_of_notMem' h]
    exact zero_le

/-- **Positive association at `p = 1`**: the law is the Dirac mass at the
all-open configuration. -/
theorem posAssoc_one {q : NNReal} (hq : 0 < q) :
    PosAssoc q 1 hq (le_rfl : (1 : NNReal) ≤ 1) := by
  intro G ξ A D hA hD
  rw [fkMeasure_one_eq_dirac hq ξ]
  by_cases h : G.allOpen ∈ A ∩ D
  · have h1 : G.allOpen ∈ A := h.1
    have h2 : G.allOpen ∈ D := h.2
    rw [Measure.dirac_apply_of_mem h, Measure.dirac_apply_of_mem h1,
      Measure.dirac_apply_of_mem h2]
    simp
  · rw [dirac_apply_of_notMem' h]
    exact zero_le

/-- Stage monotonicity at `p = 1` for the genuine finite-volume laws: the
`p = 1` law is a Dirac mass at the all-open configuration of each box, and
restriction of the all-open stage configuration is the all-open configuration of
the smaller stage. -/
theorem finiteVolumeLaw_stage_mono_one {q : NNReal} (hq : 0 < q) (ξ : Setoid V)
    {m k : ℕ} (hmk : m ≤ k) (A : Set (F.box m).Interior) :
    (((F.box m).finiteVolumeLaw hq (le_rfl : (1 : NNReal) ≤ 1) (F.stageBoundary m ξ) :
        Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A))
      ≤ (((F.box k).finiteVolumeLaw hq (le_rfl : (1 : NNReal) ≤ 1) (F.stageBoundary k ξ) :
        Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)) := by
  have hL : ((F.box m).finiteVolumeLaw hq (le_rfl : (1 : NNReal) ≤ 1) (F.stageBoundary m ξ) :
      Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box m).graph.fkMeasure hq (le_rfl : (1 : NNReal) ≤ 1) (F.stageBoundary m ξ) A :=
    finiteVolumeLaw_apply_interiorRestriction (B := F.box m) (F.stageBoundary m ξ) hq le_rfl A
  have hR : ((F.box k).finiteVolumeLaw hq (le_rfl : (1 : NNReal) ≤ 1) (F.stageBoundary k ξ) :
      Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box k).graph.fkMeasure hq (le_rfl : (1 : NNReal) ≤ 1) (F.stageBoundary k ξ)
          (res (F.stageIncl hmk) ⁻¹' A) := by
    rw [preimage_interiorRestriction_stage]
    exact finiteVolumeLaw_apply_interiorRestriction (B := F.box k) (F.stageBoundary k ξ) hq le_rfl _
  rw [hL, hR,
    fkMeasure_one_eq_dirac hq (F.stageBoundary m ξ),
    fkMeasure_one_eq_dirac hq (F.stageBoundary k ξ)]
  have hres : res (F.stageIncl hmk) (F.box k).graph.allOpen = (F.box m).graph.allOpen := rfl
  rw [← hres]
  exact dirac_preimage_le_dirac (res (F.stageIncl hmk)) (F.box k).graph.allOpen A

/-- **Stage monotonicity at `p = 0`**: the law is a Dirac mass at the all-closed
configuration, and restriction of the all-closed stage configuration is the
all-closed configuration of the smaller stage. -/
theorem finiteVolumeLaw_stage_mono_zero {q : NNReal} (hq : 0 < q) (ξ : Setoid V)
    {m k : ℕ} (hmk : m ≤ k) (A : Set (F.box m).Interior) :
    (((F.box m).finiteVolumeLaw hq (zero_le : (0 : NNReal) ≤ 1) (F.stageBoundary m ξ) :
        Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A))
      ≤ (((F.box k).finiteVolumeLaw hq (zero_le : (0 : NNReal) ≤ 1) (F.stageBoundary k ξ) :
        Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)) := by
  have hL : ((F.box m).finiteVolumeLaw hq (zero_le : (0 : NNReal) ≤ 1) (F.stageBoundary m ξ) :
      Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box m).graph.fkMeasure hq (zero_le : (0 : NNReal) ≤ 1) (F.stageBoundary m ξ) A :=
    finiteVolumeLaw_apply_interiorRestriction (B := F.box m) (F.stageBoundary m ξ) hq zero_le A
  have hR : ((F.box k).finiteVolumeLaw hq (zero_le : (0 : NNReal) ≤ 1) (F.stageBoundary k ξ) :
      Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)
      = (F.box k).graph.fkMeasure hq (zero_le : (0 : NNReal) ≤ 1) (F.stageBoundary k ξ)
          (res (F.stageIncl hmk) ⁻¹' A) := by
    rw [preimage_interiorRestriction_stage]
    exact finiteVolumeLaw_apply_interiorRestriction (B := F.box k) (F.stageBoundary k ξ) hq zero_le _
  rw [hL, hR,
    fkMeasure_zero_eq_dirac hq (F.stageBoundary m ξ),
    fkMeasure_zero_eq_dirac hq (F.stageBoundary k ξ)]
  have hres : res (F.stageIncl hmk) (F.box k).graph.allClosed = (F.box m).graph.allClosed := rfl
  rw [← hres]
  exact dirac_preimage_le_dirac (res (F.stageIncl hmk)) (F.box k).graph.allClosed A

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite
open FixedVertexFamily

variable {E V : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {F : FixedVertexFamily E V}

/-! ## Part 7: unconditional `q ≥ 1` statement on the genuine family -/

/-- **Unconditional positive association for `q ≥ 1` and `0 < p ≤ 1`** in the
`PosAssoc` shape, assembled from the normalized finite FKG theorem (interior
case) and the two Dirac endpoints. -/
theorem posAssoc_of_one_le {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp : p ≤ 1) :
    PosAssoc q p (lt_of_lt_of_le zero_lt_one hq) hp := by
  rcases eq_or_lt_of_le hp with h1 | hlt
  · subst h1
    exact posAssoc_one _
  · exact posAssoc_of_fkPMF hq hp0 hlt

/-- **Unconditional stage monotonicity for `q ≥ 1`, `0 < p ≤ 1`.**  Both the
association input and the monotonicity itself are theorems here. -/
theorem finiteVolumeLaw_stage_mono_q_ge_one {q p : NNReal} (hq : 1 ≤ q)
    (hp0 : 0 < p) (hp : p ≤ 1) (ξ : Setoid V) {m k : ℕ} (hmk : m ≤ k)
    {A : Set (F.box m).Interior} (hA : IsUp A) :
    (((F.box m).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ :
        Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A))
      ≤ (((F.box k).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ :
        Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A)) := by
  rcases eq_or_lt_of_le hp with h1 | hlt
  · subst h1
    exact finiteVolumeLaw_stage_mono_one (F := F) (lt_of_lt_of_le zero_lt_one hq) ξ hmk A
  · exact finiteVolumeLaw_stage_mono (F := F) (lt_of_lt_of_le zero_lt_one hq) hp hlt
      (posAssoc_of_fkPMF hq hp0 hlt) ξ hmk hA

/-- **No mass escape for genuine finite-volume stages at `q ≥ 1`, `0 < p ≤ 1`,
with arbitrary boundary setoid.**  Nothing is assumed beyond the existence of the
limit point `μ`: `PosAssoc` and stage monotonicity are both theorems, including
the endpoint `p = 1`. -/
theorem noEscape_of_finiteVolumeLaw_stage_q_ge_one [Countable E]
    (F : FixedVertexFamily E V) {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp : p ≤ 1) (ξ : Setoid V)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto (fun n => (F.box n).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ)
      atTop (𝓝 μ))
    (A : (n : ℕ) → Set (F.box n).Interior)
    (hAup : ∀ n, IsUp (A n))
    (hCmono : Monotone (fun k => (F.box k).interiorRestriction ⁻¹' A k))
    {Cinf : Set (Configuration E)}
    (hCunion : ∀ ω, (∃ k, ω ∈ (F.box k).interiorRestriction ⁻¹' A k) ↔ ω ∈ Cinf) :
    Filter.limsup (fun k => (((F.box k).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ :
        Measure (Configuration E))
        ((F.box k).interiorRestriction ⁻¹' A k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
  have hCcl : ∀ k, IsClopen ((F.box k).interiorRestriction ⁻¹' A k) :=
    fun k => isClopen_stageCylinder F A k
  have hmono : ∀ m k, m ≤ k →
      (((F.box m).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ :
          Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A m))
        ≤ (((F.box k).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ :
          Measure (Configuration E)) ((F.box m).interiorRestriction ⁻¹' A m)) :=
    fun m k hmk => finiteVolumeLaw_stage_mono_q_ge_one (F := F) hq hp0 hp ξ hmk (hAup m)
  exact noEscape_of_stage_mono
    (fun n => (F.box n).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp ξ) μ hμ
    (C := fun k => (F.box k).interiorRestriction ⁻¹' A k) hCcl hCmono hCunion hmono

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite
open FixedVertexFamily

/-! ## Part 8: the concrete loop instance at `q ≥ 1` -/

/-- **Concrete unconditional instance.**  On the one-vertex loop exhaustion with
free boundary, for `q ≥ 1` and `0 < p ≤ 1`, every limit point `μ` of the genuine
`finiteVolumeLaw` stages satisfies `limsup_k stage_k(C_k) ≤ μ(C_∞)` for the
increasing clopen connection-type events `C_k = {some loop in 1..k is open}`.
Every input of the analytic reduction is discharged: `PosAssoc` by
`posAssoc_of_one_le`, stage monotonicity by `finiteVolumeLaw_stage_mono_q_ge_one`. -/
theorem loopFamily_noEscape_q_ge_one {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration ℕ))
    (hμ : Tendsto (fun n => (loopFamily.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp
      (loopFamily.stageBoundary n (FK.Finite.LabelledMultigraph.freeBoundary
        (loopFamily.box 0).graph))) atTop (𝓝 μ)) :
    Filter.limsup (fun k => (((loopFamily.box k).finiteVolumeLaw
        (lt_of_lt_of_le zero_lt_one hq) hp
        (loopFamily.stageBoundary k (FK.Finite.LabelledMultigraph.freeBoundary
          (loopFamily.box 0).graph)) : Measure (Configuration ℕ))
        ((loopFamily.box k).interiorRestriction ⁻¹' loopEvent k)).toReal) atTop
      ≤ ((μ : Measure (Configuration ℕ))
        {ω : Configuration ℕ | ∃ j : ℕ, 1 ≤ j ∧ ω j = true}).toReal :=
  noEscape_of_finiteVolumeLaw_stage_q_ge_one (F := loopFamily) hq hp0 hp
    (FK.Finite.LabelledMultigraph.freeBoundary (loopFamily.box 0).graph) μ hμ
    loopEvent loopEvent_isUp loopEvent_mono loopEvent_union

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite

/-! ## Part 9: the `openRate` identification of `onePoint_edge_of_noEscape` -/

/-- **The a.e. `openRate` identification is unconditional.**  For the genuine
box graph and any measure on global configurations, the two-valued rate of the
box connection event coincides a.e. with `Glauber.FKBridge.openRate` of the box
at the same edge.  This discharges the `hrate` input of
`FK.InfiniteVolume.OneEdgeNoEscape.onePoint_edge_of_noEscape` by the
definitional identity `openRate_eq_twoValuedRate`; only the finite-stage
one-point identity `hfin` and the geometric far-connection statement for the
events `C k` remain input there. -/
theorem openRate_identification {E : Type} [Countable E] (B : FiniteBox E) (e : B.edges)
    {q p : NNReal} (αspec : B.Exterior → B.BoundaryPartition)
    (ν : Measure (Configuration E)) :
    ∀ᵐ ω ∂ν, FK.InfiniteVolume.OneEdgeNoEscape.twoValuedRate (p : ℝ)
        (FK.prime (q : ℝ) (p : ℝ))
        {ω : Configuration E | FK.Finite.Conditional.endpointsConnectedWithout B.graph
          (αspec ((B.splitOff e ω).1)) e
          (Glauber.FKBridge.offConfiguration B.graph (αspec ((B.splitOff e ω).1)) e
            ((B.splitOff e ω).2))} ω
      = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2) :=
  Filter.Eventually.of_forall fun ω =>
    (congrFun (FK.InfiniteVolume.OneEdgeNoEscape.openRate_eq_twoValuedRate B e αspec) ω).symm

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite
open FixedVertexFamily

/-- The loop stages form a genuine `BoxExhaustion`: the edge sets are nested and
every label `j` belongs to stage `j`. -/
def loopExhaustion : FK.InfiniteVolume.BoxExhaustion ℕ where
  box n := loopFamily.box n
  monotone := loopFamily.monotone
  covers := by
    intro e
    exact ⟨e, loopFamily_mem_edges.mpr (by omega)⟩

/-- **Fully unconditional free-boundary instance at `q = 1`.**  On the one-vertex
loop exhaustion, for `0 < p ≤ 1`, the genuine stages converge (their `q = 1`
limit is the Bernoulli product, by
`FK.InfiniteVolume.QOne.isFKLimit_q_one`), and no mass escapes:
`limsup_k stage_k(C_k) ≤ μ(C_∞)` with the explicit limit `μ`.  No hypothesis on
the limit law remains. -/
theorem loopFamily_noEscape_unconditional {p : NNReal} (hp0 : 0 < p) (hp : p ≤ 1) :
    Filter.limsup (fun k => (((loopFamily.box k).finiteVolumeLaw zero_lt_one hp
        (loopFamily.stageBoundary k (FK.Finite.LabelledMultigraph.freeBoundary
          (loopFamily.box 0).graph)) : Measure (Configuration ℕ))
        ((loopFamily.box k).interiorRestriction ⁻¹' loopEvent k)).toReal) atTop
      ≤ ((FK.InfiniteVolume.QOne.bernoulliConst (E := ℕ) p hp : Measure (Configuration ℕ))
        {ω : Configuration ℕ | ∃ j : ℕ, 1 ≤ j ∧ ω j = true}).toReal := by
  have hμ : Tendsto (fun n => (loopFamily.box n).finiteVolumeLaw zero_lt_one hp
      (loopFamily.stageBoundary n (FK.Finite.LabelledMultigraph.freeBoundary
        (loopFamily.box 0).graph))) atTop
      (𝓝 (FK.InfiniteVolume.QOne.bernoulliConst (E := ℕ) p hp)) :=
    FK.InfiniteVolume.QOne.isFKLimit_q_one loopExhaustion hp
      (fun n => loopFamily.stageBoundary n (FK.Finite.LabelledMultigraph.freeBoundary
        (loopFamily.box 0).graph))
  exact noEscape_of_finiteVolumeLaw_stage_q_ge_one (F := loopFamily) (q := 1) (p := p)
    le_rfl hp0 hp _ _ hμ loopEvent loopEvent_isUp loopEvent_mono loopEvent_union

end

end FK.InfiniteVolume.NoEscape

namespace FK.InfiniteVolume.NoEscape

noncomputable section

open FK.Finite
open FixedVertexFamily

/-! ## Part 10: a parallel-edge instance with two distinct endpoints -/

/-- The family with edge labels `0, …, n` at stage `n` and arbitrary ambient
endpoint maps. -/
def rangeFamily (V : Type) [Fintype V] (src tgt : ℕ → V) : FixedVertexFamily ℕ V where
  edges n := Finset.range (n + 1)
  src := src
  tgt := tgt
  monotone := by
    intro m k hmk e he
    simp only [Finset.mem_range] at he ⊢
    omega

lemma rangeFamily_mem_edges {V : Type} [Fintype V] (src tgt : ℕ → V) {n j : ℕ} :
    j ∈ ((rangeFamily V src tgt).box n).edges ↔ j < n + 1 := by
  simp [rangeFamily, FixedVertexFamily.box]

/-- Two vertices joined by parallel labels `0, 1, 2, …` (no loops). -/
def parallelFamily : FixedVertexFamily ℕ (Fin 2) :=
  rangeFamily (Fin 2) (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))

/-- At stage `n`, some parallel label of the stage is open.  On this family this
is exactly the event that the two vertices are connected through the stage
labels (see `parallelEvent_iff_connected`). -/
def parallelEvent (n : ℕ) : Set (parallelFamily.box n).Interior :=
  {β | ∃ j : (parallelFamily.box n).edges, β j = true}

theorem parallelEvent_isUp (n : ℕ) : IsUp (parallelEvent n) := by
  rintro β ⟨j, hβ⟩ γ hβγ
  exact ⟨j, (by
    have := hβγ j
    rw [Bool.le_iff_imp] at this
    exact this hβ)⟩

theorem parallelEvent_mono : Monotone (fun k => (parallelFamily.box k).interiorRestriction ⁻¹'
    parallelEvent k) := by
  intro m k hmk ω hω
  obtain ⟨j, hβ⟩ := hω
  have hjm : (j : ℕ) < m + 1 := (rangeFamily_mem_edges (V := Fin 2) _ _).mp j.2
  have hjk : (j : ℕ) < k + 1 := by omega
  exact ⟨⟨j.1, (rangeFamily_mem_edges (V := Fin 2) _ _).mpr hjk⟩, hβ⟩

theorem parallelEvent_union :
    ∀ ω : Configuration ℕ,
      (∃ k, ω ∈ (parallelFamily.box k).interiorRestriction ⁻¹' parallelEvent k) ↔
        ω ∈ {ω | ∃ j : ℕ, ω j = true} := by
  intro ω
  constructor
  · rintro ⟨k, j, hβ⟩
    exact ⟨j.1, hβ⟩
  · rintro ⟨j, hω⟩
    exact ⟨j, ⟨⟨j, (rangeFamily_mem_edges (V := Fin 2) _ _).mpr (by omega)⟩, hω⟩⟩

/-- Any walk between two distinct vertices of the free-boundary parallel box uses
an open label. -/
theorem exists_open_of_walk {n : ℕ} {β : (parallelFamily.box n).Interior} {u v : Fin 2}
    (p : ((parallelFamily.box n).graph.connectionGraph
      (parallelFamily.box n).graph.freeBoundary β).Walk u v) (hne : u ≠ v) :
    ∃ e : (parallelFamily.box n).edges, β e = true := by
  induction p with
  | nil => exact absurd rfl hne
  | cons hadj rest ih =>
    obtain ⟨hne', hstep⟩ := hadj
    rcases hstep with hfree | ⟨e, he, hjoin⟩
    · exact absurd hfree hne'
    · exact ⟨e, he⟩

/-- **The stage events are genuine connection events.**  In the box graph of the
parallel family (two distinct vertices, all labels joining them), the two
vertices are connected in the open-edge graph after free-boundary wiring exactly
when some stage label is open. -/
theorem parallelEvent_iff_connected (n : ℕ) (β : (parallelFamily.box n).Interior) :
    β ∈ parallelEvent n ↔
      ((parallelFamily.box n).graph.connectionGraph
        (parallelFamily.box n).graph.freeBoundary β).Reachable
        (0 : Fin 2) (1 : Fin 2) := by
  constructor
  · rintro ⟨j, hβ⟩
    refine SimpleGraph.Adj.reachable ?_
    refine ⟨?_, Or.inr ⟨j, hβ, ?_⟩⟩
    · exact (by decide : (0 : Fin 2) ≠ 1)
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro ⟨p⟩
    exact exists_open_of_walk p (by decide : (0 : Fin 2) ≠ 1)

/-- **No mass escape on the parallel-edge family**, `q ≥ 1`, `0 < p ≤ 1`, any
boundary setoid.  The stages are genuine two-vertex random-cluster laws with
parallel labels and distinct endpoints, and the events `C n` are the actual
connection events of the stage graphs (`parallelEvent_iff_connected`). -/
theorem parallelFamily_noEscape {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp : p ≤ 1) (ξ : Setoid (Fin 2))
    (μ : ProbabilityMeasure (Configuration ℕ))
    (hμ : Tendsto (fun n => (parallelFamily.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (parallelFamily.stageBoundary n ξ)) atTop (𝓝 μ)) :
    Filter.limsup (fun k => (((parallelFamily.box k).finiteVolumeLaw
        (lt_of_lt_of_le zero_lt_one hq) hp (parallelFamily.stageBoundary k ξ) :
          Measure (Configuration ℕ))
        ((parallelFamily.box k).interiorRestriction ⁻¹' parallelEvent k)).toReal) atTop
      ≤ ((μ : Measure (Configuration ℕ))
        {ω : Configuration ℕ | ∃ j : ℕ, ω j = true}).toReal :=
  noEscape_of_finiteVolumeLaw_stage_q_ge_one (F := parallelFamily) hq hp0 hp ξ μ hμ
    parallelEvent parallelEvent_isUp parallelEvent_mono parallelEvent_union

end

end FK.InfiniteVolume.NoEscape
