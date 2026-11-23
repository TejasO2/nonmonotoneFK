import FK.GlobalFiniteEnergy
import FK.FiniteConditional

/-!
# Finite energy for unrelated finite-volume boundary conditions

The estimates in this file do not use a coherent `BoundaryConvention`.  Closing
edges in a fixed finite set changes only the corresponding Bernoulli factors
and component counts.  Together with the bounded fibres of the closing map,
this gives a uniform pushforward bound for every finite FK boundary setoid.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.NoncoherentFiniteEnergy

open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Conditional FK.FiniteFiber
open ConventionGeometry ConventionTransport

noncomputable section

/-- Closing one edge changes every finite FK weight by at least this factor. -/
def closeFactor (q p : NNReal) : NNReal :=
  min 1 (min q 1 * ((1 - p) / p))

lemma closeFactor_pos {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < closeFactor q p := by
  unfold closeFactor
  exact lt_min zero_lt_one (mul_pos (lt_min hq zero_lt_one)
    (div_pos (tsub_pos_of_lt hp₁) hp₀))

lemma closeFactor_le_one (q p : NNReal) : closeFactor q p ≤ 1 := min_le_left _ _

lemma closeFactor_le_closed_open_ratio (q p : NNReal) :
    closeFactor q p ≤ (1 - p) / p := by
  calc
    closeFactor q p ≤ min q 1 * ((1 - p) / p) := min_le_right _ _
    _ ≤ 1 * ((1 - p) / p) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = (1 - p) / p := one_mul _

lemma closeFactor_le_q_closed_open_ratio (q p : NNReal) :
    closeFactor q p ≤ q * (1 - p) / p := by
  calc
    closeFactor q p ≤ min q 1 * ((1 - p) / p) := min_le_right _ _
    _ ≤ q * ((1 - p) / p) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
    _ = q * (1 - p) / p := by ring

/-- One-sided FK weight ratio for closing one labelled edge. -/
theorem closeFactor_mul_fkWeight_le (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) (e : G.Edge) (ω : G.Configuration) :
    closeFactor q p * G.fkWeight q p ξ ω ≤
      G.fkWeight q p ξ (withEdge e false ω) := by
  classical
  by_cases he : ω e = true
  · have hω : withEdge e true ω = ω := by
      funext a
      by_cases hae : a = e
      · subst a
        simp [he]
      · exact withEdge_off hae true ω
    by_cases hconn : endpointsConnectedWithout G ξ e ω
    · have hopen := fkWeight_open_eq_of_connected G q p ξ e ω hconn
      have hclosed := fkWeight_closed_eq_of_connected G q p ξ e ω
      calc
        closeFactor q p * G.fkWeight q p ξ ω =
            closeFactor q p * G.fkWeight q p ξ (withEdge e true ω) := by rw [hω]
        _ ≤ ((1 - p) / p) * G.fkWeight q p ξ (withEdge e true ω) :=
          mul_le_mul_of_nonneg_right (closeFactor_le_closed_open_ratio q p) (by positivity)
        _ = (1 - p) *
            (offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e false ω)) := by
          rw [hopen]
          field_simp
          <;> ring
        _ = G.fkWeight q p ξ (withEdge e false ω) := hclosed.symm
    · have hopen := fkWeight_open_eq_of_not_connected G q p ξ e ω
      have hclosed := fkWeight_closed_eq_of_not_connected G q p ξ e ω hconn
      calc
        closeFactor q p * G.fkWeight q p ξ ω =
            closeFactor q p * G.fkWeight q p ξ (withEdge e true ω) := by rw [hω]
        _ ≤ (q * (1 - p) / p) * G.fkWeight q p ξ (withEdge e true ω) :=
          mul_le_mul_of_nonneg_right (closeFactor_le_q_closed_open_ratio q p) (by positivity)
        _ = q * (1 - p) *
            (offEdgeWeight G p e ω * q ^ G.componentCount ξ (withEdge e true ω)) := by
          rw [hopen]
          field_simp
          <;> ring
        _ = G.fkWeight q p ξ (withEdge e false ω) := hclosed.symm
  · have he' : ω e = false := Bool.eq_false_of_not_eq_true he
    have hclosed : withEdge e false ω = ω := by
      funext a
      by_cases hae : a = e
      · subst a
        simp [he']
      · exact withEdge_off hae false ω
    rw [hclosed]
    calc
      closeFactor q p * G.fkWeight q p ξ ω ≤ 1 * G.fkWeight q p ξ ω :=
        mul_le_mul_of_nonneg_right (closeFactor_le_one q p) (by positivity)
      _ = G.fkWeight q p ξ ω := one_mul _

/-- Close precisely the coordinates in a finite set of labelled edges. -/
def closeEdges {E : Type*} [DecidableEq E] (s : Finset E) (ω : E → Bool) : E → Bool :=
  fun e => if e ∈ s then false else ω e

@[simp] lemma closeEdges_empty {E : Type*} [DecidableEq E] (ω : E → Bool) :
    closeEdges ∅ ω = ω := rfl

lemma closeEdges_insert {E : Type*} [DecidableEq E] {e : E} {s : Finset E}
    (he : e ∉ s) (ω : E → Bool) :
    closeEdges (insert e s) ω = withEdge e false (closeEdges s ω) := by
  funext a
  by_cases hae : a = e
  · subst a
    simp [closeEdges, withEdge, he]
  · simp [closeEdges, withEdge_off hae, hae]

/-- Iterated closing has a uniform FK weight ratio for every boundary setoid. -/
theorem closeFactor_pow_mul_fkWeight_le (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) (s : Finset G.Edge) (ω : G.Configuration) :
    closeFactor q p ^ s.card * G.fkWeight q p ξ ω ≤
      G.fkWeight q p ξ (closeEdges s ω) := by
  classical
  induction s using Finset.induction generalizing ω with
  | empty => simp
  | @insert e s he ih =>
      rw [closeEdges_insert he]
      calc
        closeFactor q p ^ (insert e s).card * G.fkWeight q p ξ ω =
            closeFactor q p * (closeFactor q p ^ s.card * G.fkWeight q p ξ ω) := by
          simp only [Finset.card_insert_of_notMem he, pow_succ]
          ring
        _ ≤ closeFactor q p * G.fkWeight q p ξ (closeEdges s ω) :=
          mul_le_mul_of_nonneg_left (ih ω) (by positivity)
        _ ≤ G.fkWeight q p ξ (withEdge e false (closeEdges s ω)) :=
          closeFactor_mul_fkWeight_le G hq hp₀ hp₁ ξ e (closeEdges s ω)


/-- There are at most `2 ^ s.card` configurations with a given closing image. -/
lemma card_closeEdges_fiber_le {E : Type*} [Fintype E] [DecidableEq E] (s : Finset E)
    (η : E → Bool) :
    (Finset.univ.filter fun ω : E → Bool => η = closeEdges s ω).card ≤ 2 ^ s.card := by
  classical
  let F := Finset.univ.filter fun ω : E → Bool => η = closeEdges s ω
  let r : {ω // ω ∈ F} → (s → Bool) := fun ω e => ω.1 e.1
  have hr : Function.Injective r := by
    intro ω ζ hωζ
    apply Subtype.ext
    funext e
    by_cases he : e ∈ s
    · exact congrFun hωζ ⟨e, he⟩
    · have hω : η = closeEdges s ω.1 := (Finset.mem_filter.mp ω.2).2
      have hζ : η = closeEdges s ζ.1 := (Finset.mem_filter.mp ζ.2).2
      have hc : closeEdges s ω.1 = closeEdges s ζ.1 := hω.symm.trans hζ
      have heq := congrFun hc e
      simpa [closeEdges, he] using heq
  have hcard := Fintype.card_le_of_injective r hr
  change F.card ≤ 2 ^ s.card
  rw [← Fintype.card_coe F]
  calc
    Fintype.card {ω // ω ∈ F} ≤ Fintype.card (s → Bool) := hcard
    _ = 2 ^ s.card := by simp [Fintype.card_fun, Fintype.card_bool]

/-- The closing weight ratio remains valid after FK normalization. -/
theorem closeFactor_pow_mul_fkPMF_le (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) (s : Finset G.Edge) (ω : G.Configuration) :
    ((closeFactor q p ^ s.card : NNReal) : ℝ≥0∞) * G.fkPMF hq hp₁.le ξ ω ≤
      G.fkPMF hq hp₁.le ξ (closeEdges s ω) := by
  have hw := closeFactor_pow_mul_fkWeight_le G hq hp₀ hp₁ ξ s ω
  have hn : closeFactor q p ^ s.card *
      (G.fkWeight q p ξ ω / G.partitionFunction q p ξ) ≤
      G.fkWeight q p ξ (closeEdges s ω) / G.partitionFunction q p ξ := by
    calc
      closeFactor q p ^ s.card *
          (G.fkWeight q p ξ ω / G.partitionFunction q p ξ) =
          (closeFactor q p ^ s.card * G.fkWeight q p ξ ω) /
            G.partitionFunction q p ξ := by ring
      _ ≤ G.fkWeight q p ξ (closeEdges s ω) / G.partitionFunction q p ξ := by
        gcongr
  rw [G.fkPMF_apply hq hp₁.le, G.fkPMF_apply hq hp₁.le]
  exact_mod_cast hn

/-- Pointwise uniform bound for closing under an arbitrary finite FK law. -/
theorem map_closeEdges_fkPMF_apply_le (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) (s : Finset G.Edge) (η : G.Configuration) :
    PMF.map (closeEdges s) (G.fkPMF hq hp₁.le ξ) η ≤
      (2 ^ s.card : ℝ≥0∞) *
        (((closeFactor q p ^ s.card : NNReal) : ℝ≥0∞))⁻¹ *
          G.fkPMF hq hp₁.le ξ η := by
  classical
  let c : ℝ≥0∞ := ((closeFactor q p ^ s.card : NNReal) : ℝ≥0∞)
  have hcpos : 0 < closeFactor q p ^ s.card := pow_pos (closeFactor_pos hq hp₀ hp₁) _
  have hc₀ : c ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr hcpos.ne'
  have hctop : c ≠ ∞ := ENNReal.coe_ne_top
  let F := Finset.univ.filter fun ω : G.Configuration => η = closeEdges s ω
  have hmap : PMF.map (closeEdges s) (G.fkPMF hq hp₁.le ξ) η =
      ∑ ω ∈ F, G.fkPMF hq hp₁.le ξ ω := by
    rw [PMF.map_apply, tsum_fintype]
    simp only [F, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases h : η = closeEdges s ω <;> simp only [h, if_pos, if_neg]
  have hterm (ω : G.Configuration) (hω : ω ∈ F) :
      G.fkPMF hq hp₁.le ξ ω ≤ c⁻¹ * G.fkPMF hq hp₁.le ξ η := by
    have heq : η = closeEdges s ω := (Finset.mem_filter.mp hω).2
    have hn : c * G.fkPMF hq hp₁.le ξ ω ≤ G.fkPMF hq hp₁.le ξ η := by
      rw [heq]
      exact closeFactor_pow_mul_fkPMF_le G hq hp₀ hp₁ ξ s ω
    calc
      G.fkPMF hq hp₁.le ξ ω = c⁻¹ * (c * G.fkPMF hq hp₁.le ξ ω) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc₀ hctop, one_mul]
      _ ≤ c⁻¹ * G.fkPMF hq hp₁.le ξ η := by gcongr
  rw [hmap]
  calc
    (∑ ω ∈ F, G.fkPMF hq hp₁.le ξ ω) ≤
        ∑ _ω ∈ F, c⁻¹ * G.fkPMF hq hp₁.le ξ η := by
      exact Finset.sum_le_sum fun ω hω => hterm ω hω
    _ = (F.card : ℝ≥0∞) * (c⁻¹ * G.fkPMF hq hp₁.le ξ η) := by simp
    _ = (F.card : ℝ≥0∞) * c⁻¹ * G.fkPMF hq hp₁.le ξ η := by ring
    _ ≤ (2 ^ s.card : ℝ≥0∞) * c⁻¹ * G.fkPMF hq hp₁.le ξ η := by
      gcongr
      exact_mod_cast card_closeEdges_fiber_le s η

/-- Uniform close-set domination for a finite FK measure with any boundary setoid. -/
theorem measure_map_closeEdges_le (G : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) (s : Finset G.Edge) :
    Measure.map (closeEdges s) (G.fkMeasure hq hp₁.le ξ) ≤
      ((2 ^ s.card : ℝ≥0∞) *
        (((closeFactor q p ^ s.card : NNReal) : ℝ≥0∞))⁻¹) •
          G.fkMeasure hq hp₁.le ξ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul]
  change Measure.map (closeEdges s) (G.fkPMF hq hp₁.le ξ).toMeasure A ≤
    (2 ^ s.card : ℝ≥0∞) *
      (((closeFactor q p ^ s.card : NNReal) : ℝ≥0∞))⁻¹ *
        (G.fkPMF hq hp₁.le ξ).toMeasure A
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _), PMF.toMeasure_apply_fintype,
    PMF.toMeasure_apply_fintype, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro η _hη
  by_cases hη : η ∈ A
  · simp only [Set.indicator_of_mem hη]
    exact map_closeEdges_fkPMF_apply_le G hq hp₀ hp₁ ξ s η
  · simp [Set.indicator_of_notMem hη]


/-- The edges of `B`, viewed inside an ambient finite box. -/
def embeddedEdges {E : Type*} (B C : FiniteBox E) (hBC : B.edges ⊆ C.edges) :
    Finset C.edges :=
  B.edges.attach.map
    ⟨fun e => ⟨e.1, hBC e.2⟩, by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : C.edges => z.1) hab)⟩

@[simp] lemma mem_embeddedEdges {E : Type*} (B C : FiniteBox E)
    (hBC : B.edges ⊆ C.edges) (e : C.edges) :
    e ∈ embeddedEdges B C hBC ↔ e.1 ∈ B.edges := by
  constructor
  · intro he
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_map.mp he
    exact a.2
  · intro he
    apply Finset.mem_map.mpr
    exact ⟨⟨e.1, he⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

@[simp] lemma card_embeddedEdges {E : Type*} (B C : FiniteBox E)
    (hBC : B.edges ⊆ C.edges) : (embeddedEdges B C hBC).card = B.edges.card := by
  simp [embeddedEdges]

/-- The uniform finite-energy multiplier, depending only on the box being closed. -/
def closingMultiplier {E : Type*} (B : FiniteBox E) (q p : NNReal) : ℝ≥0∞ :=
  (2 ^ B.edges.card : ℝ≥0∞) *
    (((closeFactor q p ^ B.edges.card : NNReal) : ℝ≥0∞))⁻¹

lemma closingMultiplier_ne_top {E : Type*} (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) : closingMultiplier B q p ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · simp
  · exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr
      (pow_pos (closeFactor_pos hq hp₀ hp₁) _).ne')

/-- Closing a box inside an ambient conditional configuration is closing the
corresponding interior coordinates. -/
lemma closeBox_glue {E : Type*} (B C : FiniteBox E) (hBC : B.edges ⊆ C.edges)
    (η : C.Exterior) (ξ : C.Interior) :
    GlobalFiniteEnergy.closeBox B (C.glue (η, ξ)) =
      C.glue (η, closeEdges (embeddedEdges B C hBC) ξ) := by
  funext e
  by_cases heC : e ∈ C.edges
  · by_cases heB : e ∈ B.edges
    · simp [GlobalFiniteEnergy.closeBox, FiniteBox.glue, FiniteBox.split,
        closeEdges, mem_embeddedEdges, heB, heC]
    · simp [GlobalFiniteEnergy.closeBox, FiniteBox.glue, FiniteBox.split,
        closeEdges, mem_embeddedEdges, heB, heC]
  · have heB : e ∉ B.edges := fun h => heC (hBC h)
    simp [GlobalFiniteEnergy.closeBox, FiniteBox.glue, FiniteBox.split,
      closeEdges, mem_embeddedEdges, heB, heC]


/-- Uniform close-box domination for every conditional law in every containing
finite box.  The outer boundary setoid and exterior configuration are arbitrary. -/
theorem measure_map_closeBox_le_conditionalLaw {E : Type*} [Countable E]
    (B C : FiniteBox E) (hBC : B.edges ⊆ C.edges) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (β : C.BoundaryPartition) (η : C.Exterior) :
    Measure.map (GlobalFiniteEnergy.closeBox B)
        (C.conditionalLaw hq hp₁.le (fun _ => β) η :
          Measure (Configuration E)) ≤
      closingMultiplier B q p •
        (C.conditionalLaw hq hp₁.le (fun _ => β) η :
          Measure (Configuration E)) := by
  let f : C.Interior → Configuration E := fun ξ => C.glue (η, ξ)
  let T : C.Interior → C.Interior := closeEdges (embeddedEdges B C hBC)
  let ν : Measure C.Interior := C.graph.fkMeasure hq hp₁.le β
  have hf : Measurable f := C.measurable_glue_const_left η
  have hT : Measurable T := measurable_of_finite _
  have hc : Measurable (GlobalFiniteEnergy.closeBox B) :=
    GlobalFiniteEnergy.measurable_closeBox B
  have hcomp : GlobalFiniteEnergy.closeBox B ∘ f = f ∘ T := by
    funext ξ
    exact closeBox_glue B C hBC η ξ
  have hclose : T = @closeEdges C.edges (Classical.decEq C.edges)
      (embeddedEdges B C hBC) := by
    funext ξ e
    by_cases he : e.1 ∈ B.edges <;>
      simp [T, closeEdges, mem_embeddedEdges, he]
  have hbound : Measure.map T ν ≤ closingMultiplier B q p • ν := by
    rw [hclose]
    simpa only [ν, closingMultiplier, card_embeddedEdges] using
      measure_map_closeEdges_le C.graph hq hp₀ hp₁ β (embeddedEdges B C hBC)
  calc
    Measure.map (GlobalFiniteEnergy.closeBox B)
        (C.conditionalLaw hq hp₁.le (fun _ => β) η : Measure (Configuration E)) =
        Measure.map (GlobalFiniteEnergy.closeBox B) (Measure.map f ν) := rfl
    _ = Measure.map (GlobalFiniteEnergy.closeBox B ∘ f) ν := Measure.map_map hc hf
    _ = Measure.map (f ∘ T) ν := by rw [hcomp]
    _ = Measure.map f (Measure.map T ν) := (Measure.map_map hf hT).symm
    _ ≤ Measure.map f (closingMultiplier B q p • ν) := Measure.map_mono hbound hf
    _ = closingMultiplier B q p • Measure.map f ν :=
      Measure.map_smul (closingMultiplier B q p) hf.aemeasurable
    _ = closingMultiplier B q p •
        (C.conditionalLaw hq hp₁.le (fun _ => β) η : Measure (Configuration E)) := rfl

/-- Closed-exterior specialization for the actual finite-volume law. -/
theorem measure_map_closeBox_le_finiteVolumeLaw {E : Type*} [Countable E]
    (B C : FiniteBox E) (hBC : B.edges ⊆ C.edges) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (β : C.BoundaryPartition) :
    Measure.map (GlobalFiniteEnergy.closeBox B)
        (C.finiteVolumeLaw hq hp₁.le β : Measure (Configuration E)) ≤
      closingMultiplier B q p • (C.finiteVolumeLaw hq hp₁.le β : Measure (Configuration E)) := by
  simpa only [FiniteBox.finiteVolumeLaw] using
    measure_map_closeBox_le_conditionalLaw B C hBC hq hp₀ hp₁ β C.closedExterior

/-- The same constant passes to an arbitrary noncoherent FK weak limit.  No
nesting compatibility, DLR equation, or coherence of the boundary sequence is used. -/
theorem measure_map_closeBox_le_of_isFKLimit {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh hq hp₁.le α μ) :
    Measure.map (GlobalFiniteEnergy.closeBox B) (μ : Measure (Configuration E)) ≤
      closingMultiplier B q p • (μ : Measure (Configuration E)) := by
  apply GlobalFiniteEnergy.measure_map_le_smul_of_tendsto hμ
    (GlobalFiniteEnergy.closeBox B) (GlobalFiniteEnergy.continuous_closeBox B)
    (closingMultiplier_ne_top B hq hp₀ hp₁)
  filter_upwards [exh.eventually_subset B.edges] with n hn
  simpa only [ProbabilityMeasure.toMeasure_map] using
    measure_map_closeBox_le_finiteVolumeLaw B (exh.box n) hn hq hp₀ hp₁ (α n)

/-- Closing a fixed finite box preserves null events for an arbitrary FK limit. -/
theorem absolutelyContinuous_map_closeBox_of_isFKLimit {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh hq hp₁.le α μ) :
    Measure.map (GlobalFiniteEnergy.closeBox B) (μ : Measure (Configuration E)) ≪
      (μ : Measure (Configuration E)) :=
  Measure.absolutelyContinuous_of_le_smul
    (measure_map_closeBox_le_of_isFKLimit exh B hq hp₀ hp₁ α hμ)


/-- Global uniqueness survives closing a finite box for an arbitrary FK limit,
with no coherent source convention and no preliminary DLR law. -/
theorem ae_globalAtMostOne_closeInside_of_isFKLimit
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet) (B : FiniteBox G.edgeSet) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit exh hq hp₁.le α μ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      GlobalAtMostOne G (closeInside B η) := by
  have hac := absolutelyContinuous_map_closeBox_of_isFKLimit exh B hq hp₀ hp₁ α hμ
  have hclosed : ∀ᵐ ω ∂(Measure.map (GlobalFiniteEnergy.closeBox B)
      (μ : Measure (Configuration G.edgeSet))), GlobalAtMostOne G ω := hac.ae_le hglobal
  have hsplit : Measurable (fun ω : Configuration G.edgeSet => (B.splitEquiv ω).1) :=
    measurable_fst.comp B.splitEquiv.measurable
  have hmapeq : Measure.map (closeInside B) (B.exteriorMeasure μ : Measure B.Exterior) =
      Measure.map (GlobalFiniteEnergy.closeBox B) (μ : Measure (Configuration G.edgeSet)) := by
    change Measure.map (closeInside B)
      (Measure.map (fun ω : Configuration G.edgeSet => (B.splitEquiv ω).1)
        (μ : Measure (Configuration G.edgeSet))) = _
    rw [Measure.map_map (measurable_closeInside B) hsplit]
    rfl
  rw [← hmapeq] at hclosed
  exact (ae_map_iff (measurable_closeInside B).aemeasurable
    (measurableSet_globalAtMostOne G)).mp hclosed

/-- The pre-DLR global-to-exterior uniqueness theorem for arbitrary unrelated
finite-volume boundary setoids.  Interior parameters are needed for the uniform
local weight ratios; no coherent convention is present. -/
theorem aeAtMostOne_geometry_of_isFKLimit
    {V : Type*} {G : SimpleGraph V} [Countable V]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit exh hq hp₁.le α μ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    ConventionTransport.AEAtMostOne data.geometry μ := by
  intro m
  have hgood := ae_globalAtMostOne_closeInside_of_isFKLimit
    exh (exh.box m) hq hp₀ hp₁ α hμ hglobal
  filter_upwards [hgood] with ζ hζ
  intro x y hx hy
  exact hζ (data.vertex m x) (data.vertex m y) hx hy

end

end FK.InfiniteVolume.NoncoherentFiniteEnergy
