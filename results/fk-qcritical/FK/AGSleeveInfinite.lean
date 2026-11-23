import FK.AGSleeveDifferential
import FK.AGInfiniteLimit
import FK.NestedMetricGeometry

/-!
# Infinite-product limits for one finite annular sleeve

A fixed arm on a connected locally finite graph depends on finitely many bond
coordinates.  We put those coordinates, the complete selected sleeve and the
shared activation into one finite trace.  The finite pivot transport and
Margulis--Russo calculation on that trace are then identified with the actual
infinite product marginal.  Continuity from above gives the corresponding
infinite-cluster comparison; no derivative/limit interchange is used.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.AGImplant.Sleeve.Infinite

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation

universe u v w

/-- Extend a configuration on a finite trace by closed coordinates. -/
noncomputable def traceExtend {J : Type u} (K : Finset J) (ξ : K → Bool) : J → Bool :=
  CurvatureVariance.Infra.Percolation.extendFalse (K : Set J) ξ

/-- The trace of an event on the closed-extension section. -/
def traceEvent {J : Type u} (K : Finset J) (A : Set (J → Bool)) : Set (K → Bool) :=
  traceExtend K ⁻¹' A

/-- Coordinates of a full finite set, viewed inside a larger trace. -/
noncomputable def traceFinset {J : Type u} (R K : Finset J) (hRK : R ⊆ K) : Finset K :=
  R.attach.map (⟨fun x : R => (⟨x.1, hRK x.2⟩ : K), fun x y h =>
    Subtype.ext (congrArg (fun z : K => (z : J)) h)⟩ : R ↪ K)

@[simp] lemma mem_traceFinset {J : Type u} {R K : Finset J} {hRK : R ⊆ K}
    (x : K) : x ∈ traceFinset R K hRK ↔ (x : J) ∈ R := by
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact a.property
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨⟨x.1, hx⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

@[simp] lemma card_traceFinset {J : Type u} (R K : Finset J) (hRK : R ⊆ K) :
    (traceFinset R K hRK).card = R.card := by
  simp [traceFinset]

/-- Close full-trace coordinates in `R`. -/
noncomputable def traceClose {J : Type u} (R : Finset J) {K : Finset J}
    (ξ : K → Bool) : K → Bool := fun x => if (x : J) ∈ R then false else ξ x

@[simp] lemma traceExtend_apply_of_mem {J : Type u} {K : Finset J}
    (ξ : K → Bool) {x : J} (hx : x ∈ K) : traceExtend K ξ x = ξ ⟨x, hx⟩ := by
  simp [traceExtend, CurvatureVariance.Infra.Percolation.extendFalse, hx]

@[simp] lemma traceExtend_apply_of_notMem {J : Type u} {K : Finset J}
    (ξ : K → Bool) {x : J} (hx : x ∉ K) : traceExtend K ξ x = false := by
  simp [traceExtend, CurvatureVariance.Infra.Percolation.extendFalse, hx]

lemma traceExtend_forceEdge {J : Type u} (K : Finset J) (ξ : K → Bool)
    (x : K) (b : Bool) :
    traceExtend K (forceEdge ξ x b) = forceEdge (traceExtend K ξ) x.1 b := by
  classical
  ext y
  by_cases hyx : y = x.1
  · subst y
    simp [forceEdge]
  · by_cases hyK : y ∈ K
    · have hyx' : (⟨y, hyK⟩ : K) ≠ x := by
        intro h
        exact hyx (congrArg Subtype.val h)
      rw [traceExtend_apply_of_mem _ hyK]
      rw [forceEdge_of_ne _ hyx', forceEdge_of_ne _ hyx]
      exact (traceExtend_apply_of_mem ξ hyK).symm
    · simp [forceEdge, hyx, hyK]

lemma pivotal_traceEvent {J : Type u} (K : Finset J) (A : Set (J → Bool))
    (x : K) (ξ : K → Bool) :
    Pivotal (traceEvent K A) x ξ ↔ Pivotal A x.1 (traceExtend K ξ) := by
  simp only [Pivotal, traceEvent, Set.mem_preimage, traceExtend_forceEdge]

lemma traceExtend_traceClose {J : Type u} {R K : Finset J} (hRK : R ⊆ K)
    (ξ : K → Bool) :
    traceExtend K (traceClose R ξ) = fun y => if y ∈ R then false else traceExtend K ξ y := by
  classical
  ext y
  by_cases hyR : y ∈ R
  · have hyK := hRK hyR
    simp [traceClose, hyR, hyK]
  · by_cases hyK : y ∈ K
    · simp [traceClose, hyR, hyK]
    · simp [traceClose, hyR, hyK]

lemma traceClose_isLocalModification {J : Type u} {R K : Finset J} (hRK : R ⊆ K) :
    IsLocalModification (traceFinset R K hRK) (traceClose R) := by
  classical
  intro ξ x hx
  simp only [traceClose]
  rw [if_neg]
  simpa using hx


/-- The actual inhomogeneous independent product on all joint coordinates. -/
noncomputable def infiniteProductLaw {J : Type u} (r : J → unitInterval) : Measure (J → Bool) :=
  Measure.infinitePi fun x => bernoulliMeasure true false (r x)

instance {J : Type u} (r : J → unitInterval) : IsProbabilityMeasure (infiniteProductLaw r) := by
  unfold infiniteProductLaw
  infer_instance

/-- Finite-dimensional marginals of the actual infinite product. -/
lemma infiniteProductLaw_map_trace {J : Type u} (r : J → unitInterval)
    (K : Finset J) [Fintype K] :
    (infiniteProductLaw r).map (K : Set J).domRestrict =
      FKEnhancement.bernoulliProduct (fun x : K => r x.1) := by
  classical
  change Measure.map (K : Set J).domRestrict
    (Measure.infinitePi fun x => bernoulliMeasure true false (r x)) =
      Measure.pi (fun x : K => bernoulliMeasure true false (r x.1))
  rw [Measure.infinitePi_map_restrict']
  exact Measure.infinitePi_eq_pi _

/-- A finitely dependent event has exactly its finite-trace probability under
any inhomogeneous independent product. -/
lemma infiniteProductLaw_traceEvent {J : Type u} (r : J → unitInterval)
    (K : Finset J) [Fintype K] (A : Set (J → Bool))
    (hdep : DependsOn (fun χ => χ ∈ A) (K : Set J)) :
    (infiniteProductLaw r A).toReal =
      (FKEnhancement.bernoulliProduct (fun x : K => r x.1) (traceEvent K A)).toReal := by
  classical
  have hset : A = (K : Set J).domRestrict ⁻¹' traceEvent K A :=
    eq_preimage_restrict_of_dependsOn hdep
  calc
    (infiniteProductLaw r A).toReal =
        (infiniteProductLaw r ((K : Set J).domRestrict ⁻¹' traceEvent K A)).toReal :=
      congrArg (fun B => (infiniteProductLaw r B).toReal) hset
    _ = _ := by
      rw [← Measure.map_apply (by fun_prop) MeasurableSet.of_discrete,
        infiniteProductLaw_map_trace]

/-- The polynomial finite-trace event weight is therefore the actual
infinite-product probability, not a separate finite-volume surrogate. -/
lemma eventWeight_traceEvent {J : Type u} (r : J → unitInterval)
    (K : Finset J) [Fintype K] [DecidableEq K] (A : Set (J → Bool))
    (hdep : DependsOn (fun χ => χ ∈ A) (K : Set J)) :
    eventWeight (fun x : K => (r x.1 : ℝ)) (traceEvent K A) =
      (infiniteProductLaw r A).toReal := by
  rw [infiniteProductLaw_traceEvent r K A hdep]
  exact eventWeight_eq_bernoulliProduct_toReal (E := K)
    (fun x : K => r x.1) (traceEvent K A)

namespace SleeveTrace

variable {V : Type v} (H : SimpleGraph V) [H.LocallyFinite]
variable (hG : H.Connected) (S : Finset H.edgeSet)
variable (o : V ⊕ H.edgeSet) (n : ℕ)

/-- The finite trace used for one arm and one selected sleeve.  It contains
all bonds in the metric arm, the complete annulus and bypass support, and the
one shared activation. -/
noncomputable def coordinates : Finset ((graph H).edgeSet ⊕ Unit) :=
  ((FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n).map
      ⟨Sum.inl, Sum.inl_injective⟩) ∪
    ((edges H S).map ⟨Sum.inl, Sum.inl_injective⟩) ∪
      (bondCoordinates (F := Unit) (annulus H S)) ∪ {Sum.inr ()}

lemma activation_mem_coordinates :
    (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ coordinates H hG S o n := by
  simp [coordinates]

lemma metric_mem_coordinates {f : (graph H).edgeSet}
    (hf : f.1 ∈ innerEdges (graph H) o n) :
    (Sum.inl f : (graph H).edgeSet ⊕ Unit) ∈ coordinates H hG S o n := by
  have hf' : f ∈ FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n :=
    (FK.InfiniteVolume.NestedMetricGeometry.mem_metricEdges (graphConnected H hG) o n f).2 hf
  simp [coordinates, hf']

lemma annulus_subset_coordinates :
    bondCoordinates (F := Unit) (annulus H S) ⊆ coordinates H hG S o n := by
  intro x hx
  simp [coordinates, hx]

/-- The enhanced arm really does depend only on the explicit finite trace. -/
lemma dependsOn_deviceArmEvent :
    DependsOn (fun χ => χ ∈ deviceArmEvent (graph H) (support H S) o n)
      (coordinates H hG S o n : Set ((graph H).edgeSet ⊕ Unit)) := by
  classical
  intro χ ξ hagree
  apply dependsOn_armEvent (G := graph H) (graphConnected H hG) o n
  intro f hf
  have hbond : χ (Sum.inl f) = ξ (Sum.inl f) :=
    hagree _ (metric_mem_coordinates H hG S o n hf)
  have hact : χ (Sum.inr ()) = ξ (Sum.inr ()) :=
    hagree _ (activation_mem_coordinates H hG S o n)
  have hadd : AddsEdge (support H S) χ f ↔ AddsEdge (support H S) ξ f := by
    constructor
    · rintro ⟨z, hz, hfS⟩
      refine ⟨z, ?_, hfS⟩
      cases z
      rwa [← hact]
    · rintro ⟨z, hz, hfS⟩
      refine ⟨z, ?_, hfS⟩
      cases z
      rwa [hact]
  change (if AddsEdge (support H S) χ f then true else χ (Sum.inl f)) =
    (if AddsEdge (support H S) ξ f then true else ξ (Sum.inl f))
  simp only [hadd, hbond]

omit [H.LocallyFinite] in
/-- Closed extension commutes with closing the complete selected annulus. -/
lemma traceExtend_traceClose_annulus {K : Finset ((graph H).edgeSet ⊕ Unit)}
    (hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K)
    (ξ : K → Bool) :
    traceExtend K (traceClose (bondCoordinates (F := Unit) (annulus H S)) ξ) =
      annularClose (annulus H S) (traceExtend K ξ) := by
  classical
  rw [traceExtend_traceClose hRK]
  ext y
  cases y with
  | inl f =>
      by_cases hf : f ∈ annulus H S
      · have hb : (Sum.inl f : (graph H).edgeSet ⊕ Unit) ∈
            bondCoordinates (F := Unit) (annulus H S) := by simp [bondCoordinates, hf]
        simp only [hb, if_pos, annularClose, hf]
      · have hb : (Sum.inl f : (graph H).edgeSet ⊕ Unit) ∉
            bondCoordinates (F := Unit) (annulus H S) := by simp [bondCoordinates, hf]
        simp only [hb, if_neg, annularClose, hf]
  | inr z =>
      have hb : (Sum.inr z : (graph H).edgeSet ⊕ Unit) ∉
          bondCoordinates (F := Unit) (annulus H S) := by simp [bondCoordinates]
      simp [hb, annularClose]

end SleeveTrace


/-- One selected-annulus pivot on the finite trace is transported to the
shared activation with the original exact likelihood and fibre constants. -/
lemma sleeve_trace_pivot_event_mul_le
    {V : Type v} (H : SimpleGraph V) (S : Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ Unit)}
    (hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K)
    (haK : (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b)
    {x : K} (hx : x ∈ traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK) :
    δ ^ S.card * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ} ≤
      ((2 ^ S.card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n))
          ⟨Sum.inr (), haK⟩ ξ} := by
  classical
  let a : K := ⟨Sum.inr (), haK⟩
  have hmap : ∀ ξ : K → Bool,
      Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ →
      Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) a
        (traceClose (bondCoordinates (F := Unit) (annulus H S)) ξ) := by
    intro ξ hp
    have hxR := (mem_traceFinset (hRK := hRK) x).1 hx
    rcases Finset.mem_map.mp hxR with ⟨f, hf, hfx⟩
    obtain ⟨e, he, hfbase⟩ := (mem_annulus H (S := S) (f := f)).1 hf
    subst f
    have hxf : x.1 = Sum.inl (baseEdge H e) := hfx.symm
    have hpFull : EdgePivotal (deviceArmEvent (graph H) (support H S) o n)
        (baseEdge H e) (traceExtend K ξ) := by
      have hp' := (pivotal_traceEvent K _ x ξ).1 hp
      change Pivotal _ (Sum.inl (baseEdge H e)) _
      rw [← hxf]
      exact hp'
    have haFull := activationPivotal_deviceArmEvent_annulus H S he n hpFull
    apply (pivotal_traceEvent K _ a _).2
    change Pivotal _ (Sum.inr ()) _
    rw [SleeveTrace.traceExtend_traceClose_annulus H S hRK]
    exact haFull
  have h := local_pi_event_mul_le ν
    (traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK)
    δ hδ hν (traceClose (bondCoordinates (F := Unit) (annulus H S)))
    (traceClose_isLocalModification hRK)
    {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ}
    {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) a ξ}
    (by intro ξ hξ; exact hmap ξ hξ)
  simpa only [card_traceFinset, card_bondCoordinates, card_annulus, a] using h

/-- The exact summed pivot comparison on a finite trace.  The annulus image is
in `K`; no finiteness assumption on the graph's edge type is made. -/
lemma sleeve_trace_sum_pivot_event_mul_le
    {V : Type v} (H : SimpleGraph V) (S : Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ Unit)}
    (hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K)
    (haK : (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b) :
    δ ^ S.card * (∑ x ∈ traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK,
      (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ}) ≤
      ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ) * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n))
          ⟨Sum.inr (), haK⟩ ξ} := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK,
        δ ^ S.card * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ}) ≤
      ∑ _x ∈ traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK,
        ((2 ^ S.card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n))
            ⟨Sum.inr (), haK⟩ ξ} := by
      apply Finset.sum_le_sum
      intro x hx
      exact sleeve_trace_pivot_event_mul_le H S o n hRK haK ν δ hδ hν hx
    _ = ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ) * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n))
            ⟨Sum.inr (), haK⟩ ξ} := by
      simp only [Finset.sum_const, card_traceFinset, card_bondCoordinates,
        card_annulus, nsmul_eq_mul]
      ring

/-- The shared-activation differential has a nonnegative normalized slope on
the finite trace, with the same exact speed as in finite volume. -/
lemma sleeveTracePivotSlope_nonneg_of_box
    {V : Type v} (H : SimpleGraph V) (S : Finset H.edgeSet) (hS : S.Nonempty)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ Unit)}
    (hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K)
    (haK : (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ K)
    (p s a b t : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Icc a b)
    (hmove : p - sleeveComparisonSpeed a b S * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) :
    let c := sleeveComparisonSpeed a b S
    0 ≤ (-c) * (∑ x ∈ traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK,
        eventWeight (fun y : K => sleeveLine H S p s c t y.1)
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ}) +
      eventWeight (fun y : K => sleeveLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n))
          ⟨Sum.inr (), haK⟩ ξ} := by
  classical
  dsimp only
  let c := sleeveComparisonSpeed a b S
  let r : K → ℝ := fun y => sleeveLine H S p s c t y.1
  let Dp := ∑ x ∈ traceFinset (bondCoordinates (F := Unit) (annulus H S)) K hRK,
    eventWeight r {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (support H S) o n)) x ξ}
  let Pa := eventWeight r {ξ | Pivotal (traceEvent K
    (deviceArmEvent (graph H) (support H S) o n)) ⟨Sum.inr (), haK⟩ ξ}
  let den : ℝ := ((2 ^ S.card : ℕ) : ℝ) * (S.card : ℝ)
  have hrbox : ∀ x, r x ∈ Icc a b := by
    intro x
    exact sleeveLine_mem_box H S hp hmove hs x.1
  have hr : ∀ x, r x ∈ Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨ha.le.trans (hrbox x).1, (hrbox x).2.trans hb.le⟩
  let ν : K → OpenPath.FinProb Bool := fun x => boolLaw (r x) (hr x)
  have hminor : 0 < sleeveMinorant a b := sleeveMinorant_pos ha hb
  have hν : ∀ x bit, sleeveMinorant a b ≤ (ν x).mass bit := by
    intro x bit
    exact sleeveMinorant_le_boolLaw (hrbox x) (hr x) bit
  have hsum := sleeve_trace_sum_pivot_event_mul_le H S o n hRK haK ν
    (sleeveMinorant a b) hminor.le hν
  have hevent (C : Set (K → Bool)) :
      (OpenPath.FinProb.pi ν).event C = eventWeight r C := by
    simpa only [ν, boolProduct] using (eventWeight_eq_boolProduct_event r hr C).symm
  simp_rw [hevent] at hsum
  change (sleeveMinorant a b) ^ S.card * Dp ≤ den * Pa at hsum
  change 0 ≤ (-c) * Dp + Pa
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hden0 : den ≠ 0 := ne_of_gt hden
  have hcδ : c * den = (sleeveMinorant a b) ^ S.card := by
    change ((sleeveMinorant a b) ^ S.card / den) * den =
      (sleeveMinorant a b) ^ S.card
    exact div_mul_cancel₀ _ hden0
  have hmul : c * Dp ≤ Pa := by
    refine le_of_mul_le_mul_right (a := den) ?_ hden
    calc
      (c * Dp) * den = (c * den) * Dp := by ring
      _ = (sleeveMinorant a b) ^ S.card * Dp := by rw [hcδ]
      _ ≤ den * Pa := hsum
      _ = Pa * den := by ring
  linarith


lemma isUpperSet_traceEvent {J : Type u} (K : Finset J) {A : Set (J → Bool)}
    (hA : IsUpperSet A) : IsUpperSet (traceEvent K A) := by
  classical
  intro χ ξ hχξ hχ
  apply hA _ hχ
  intro y
  by_cases hy : y ∈ K
  · rw [traceExtend_apply_of_mem _ hy, traceExtend_apply_of_mem _ hy]
    exact hχξ ⟨y, hy⟩
  · simp [traceExtend_apply_of_notMem, hy]

/-- Restriction of the selected sleeve velocity to a finite trace. -/
noncomputable def sleeveTraceVelocity {E : Type u} {K : Finset (E ⊕ Unit)}
    (R : Finset E) (c : ℝ) : K → ℝ := fun x => selectedVelocity R c x.1

lemma sleeveTraceVelocity_of_mem {E : Type u} {K : Finset (E ⊕ Unit)}
    {R : Finset E} (hRK : bondCoordinates (F := Unit) R ⊆ K) (c : ℝ)
    {x : K} (hx : x ∈ traceFinset (bondCoordinates (F := Unit) R) K hRK) :
    sleeveTraceVelocity R c x = -c := by
  classical
  have hxR := (mem_traceFinset (hRK := hRK) x).1 hx
  rcases Finset.mem_map.mp hxR with ⟨f, hf, hfx⟩
  change selectedVelocity R c x.1 = -c
  rw [← hfx]
  simp [selectedVelocity, hf]

lemma sleeveTraceVelocity_activation {E : Type u} {K : Finset (E ⊕ Unit)}
    (R : Finset E) (c : ℝ)
    (haK : (Sum.inr () : E ⊕ Unit) ∈ K) :
    sleeveTraceVelocity R c (⟨Sum.inr (), haK⟩ : K) = 1 := by
  simp [sleeveTraceVelocity, selectedVelocity]

lemma sleeveTraceVelocity_eq_zero {E : Type u} {K : Finset (E ⊕ Unit)}
    {R : Finset E} (hRK : bondCoordinates (F := Unit) R ⊆ K) (c : ℝ)
    (haK : (Sum.inr () : E ⊕ Unit) ∈ K) {x : K}
    (hxR : x ∉ traceFinset (bondCoordinates (F := Unit) R) K hRK)
    (hxa : x ≠ ⟨Sum.inr (), haK⟩) :
    sleeveTraceVelocity R c x = 0 := by
  classical
  cases hx : x.1 with
  | inl f =>
      have hf : f ∉ R := by
        intro hf
        apply hxR
        apply (mem_traceFinset (hRK := hRK) x).2
        rw [hx]
        simp [bondCoordinates, hf]
      simp [sleeveTraceVelocity, selectedVelocity, hx, hf]
  | inr z =>
      cases z
      exfalso
      apply hxa
      apply Subtype.ext
      exact hx

/-- The only nonzero trace velocities are the activation and the exact finite
image of the annulus. -/
lemma sum_sleeveTraceVelocity_mul {E : Type u} {K : Finset (E ⊕ Unit)}
    {R : Finset E} (hRK : bondCoordinates (F := Unit) R ⊆ K) (c : ℝ)
    (haK : (Sum.inr () : E ⊕ Unit) ∈ K) (W : K → ℝ) :
    (∑ x, sleeveTraceVelocity R c x * W x) =
      (-c) * (∑ x ∈ traceFinset (bondCoordinates (F := Unit) R) K hRK, W x) +
        W ⟨Sum.inr (), haK⟩ := by
  classical
  let Rt := traceFinset (bondCoordinates (F := Unit) R) K hRK
  let a : K := ⟨Sum.inr (), haK⟩
  have haRt : a ∉ Rt := by
    intro ha
    have haR := (mem_traceFinset (hRK := hRK) a).1 ha
    simp [a, bondCoordinates] at haR
  calc
    (∑ x, sleeveTraceVelocity R c x * W x) =
        ∑ x ∈ insert a Rt, sleeveTraceVelocity R c x * W x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x hxuniv hx
      have hxR : x ∉ Rt := by
        intro hxR
        exact hx (Finset.mem_insert_of_mem hxR)
      have hxa : x ≠ a := by
        intro hxa
        subst x
        exact hx (Finset.mem_insert_self _ _)
      rw [sleeveTraceVelocity_eq_zero hRK c haK hxR hxa, zero_mul]
    _ = W a + ∑ x ∈ Rt, sleeveTraceVelocity R c x * W x := by
      rw [Finset.sum_insert haRt, sleeveTraceVelocity_activation R c haK, one_mul]
    _ = W a + ∑ x ∈ Rt, (-c) * W x := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [sleeveTraceVelocity_of_mem hRK c hx]
    _ = (-c) * (∑ x ∈ Rt, W x) + W a := by
      rw [Finset.mul_sum]
      ring

/-- Monotone finite-trace comparison curve for the actual enhanced arm on an
arbitrary, possibly infinite, sleeved graph. -/
lemma monotoneOn_traceEventWeight_sleeveLine
    {V : Type v} (H : SimpleGraph V) (S : Finset H.edgeSet) (hS : S.Nonempty)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ Unit)}
    (hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K)
    (haK : (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn (fun t => eventWeight (fun x : K => sleeveLine H S p s
      (sleeveComparisonSpeed a b S) t x.1)
      (traceEvent K (deviceArmEvent (graph H) (support H S) o n))) (Icc (0 : ℝ) T) := by
  classical
  let c := sleeveComparisonSpeed a b S
  let Dp : ℝ → ℝ := fun t => ∑ x ∈ traceFinset
    (bondCoordinates (F := Unit) (annulus H S)) K hRK,
    eventWeight (fun y : K => sleeveLine H S p s c t y.1)
      {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ}
  let Pa : ℝ → ℝ := fun t => eventWeight (fun y : K => sleeveLine H S p s c t y.1)
    {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n))
      ⟨Sum.inr (), haK⟩ ξ}
  have hc : 0 ≤ c := sleeveComparisonSpeed_nonneg ha.le hb.le
  have hupper : IsUpperSet (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) :=
    isUpperSet_traceEvent K (isUpperSet_deviceArmEvent (graph H) (support H S) o n)
  have hline (t : ℝ) : (fun x : K => sleeveLine H S p s c t x.1) =
      affineRates (fun x : K => sleeveLine H S p s c 0 x.1)
        (sleeveTraceVelocity (annulus H S) c) t := by
    funext x
    change sleeveLine H S p s c t x.1 = sleeveLine H S p s c 0 x.1 +
      t * sleeveTraceVelocity (annulus H S) c x
    calc
      sleeveLine H S p s c t x.1 = sleeveLine H S p s c 0 x.1 +
          t * selectedVelocity (annulus H S) c x.1 :=
        congrFun (sleeveLine_eq_affine H S p s c t) x.1
      _ = _ := by
        congr 1
        cases hx : x.1 with
        | inl f =>
            by_cases hf : f ∈ annulus H S <;>
              simp [sleeveTraceVelocity, selectedVelocity, hx, hf]
        | inr z => simp [sleeveTraceVelocity, selectedVelocity, hx]
  have hderiv (t : ℝ) : HasDerivAt
      (fun y => eventWeight (fun x : K => sleeveLine H S p s c y x.1)
        (traceEvent K (deviceArmEvent (graph H) (support H S) o n)))
      ((-c) * Dp t + Pa t) t := by
    have h := hasDerivAt_eventWeight_affine_pivotal
      (fun x : K => sleeveLine H S p s c 0 x.1)
      (sleeveTraceVelocity (annulus H S) c) hupper t
    simp_rw [← hline] at h
    convert h using 1
    simpa only [Dp, Pa] using (sum_sleeveTraceVelocity_mul hRK c haK (fun x =>
      eventWeight (fun y : K => sleeveLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) x ξ})).symm
  change MonotoneOn (fun t => eventWeight (fun x : K => sleeveLine H S p s c t x.1)
    (traceEvent K (deviceArmEvent (graph H) (support H S) o n))) (Icc (0 : ℝ) T)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T)
    (f' := fun t => (-c) * Dp t + Pa t)
  · intro t ht
    exact (hderiv t).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t).hasDerivWithinAt
  · intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := interior_subset ht
    have hbox := sleeveLine_parameters_mem_box hc htcc hp0 hs0 hpT hsT
    exact sleeveTracePivotSlope_nonneg_of_box H S hS o n hRK haK p s a b t
      ha hb hp0 hbox.1 hbox.2


/-- Endpoint comparison for the finite-trace polynomial. -/
lemma traceEventWeight_sleeveLine_le
    {V : Type v} (H : SimpleGraph V) (S : Finset H.edgeSet) (hS : S.Nonempty)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ Unit)}
    (hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K)
    (haK : (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (fun x : K => sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) ≤
      eventWeight (fun x : K => sleeveLine H S p s (sleeveComparisonSpeed a b S) T x.1)
        (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) := by
  have hmono := monotoneOn_traceEventWeight_sleeveLine H S hS o n hRK haK
    p s a b T ha hb hp0 hs0 hpT hsT
  exact hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

/-- Unit-interval parameters on one point of the sleeve comparison line. -/
noncomputable def unitSleeveLine {V : Type v} (H : SimpleGraph V)
    (S : Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, sleeveLine H S p s c t x ∈ Icc (0 : ℝ) 1) :
    (graph H).edgeSet ⊕ Unit → unitInterval := fun x =>
  ⟨sleeveLine H S p s c t x, (hr x).1, (hr x).2⟩

@[simp] lemma coe_unitSleeveLine {V : Type v} (H : SimpleGraph V)
    (S : Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, sleeveLine H S p s c t x ∈ Icc (0 : ℝ) 1)
    (x : (graph H).edgeSet ⊕ Unit) :
    (unitSleeveLine H S p s c t hr x : ℝ) = sleeveLine H S p s c t x := rfl

/-- **Infinite-product arm comparison for one actual annular sleeve.**  The
finite-window calculation is identified exactly with the infinite product on
the sleeved graph; the graph's edge type is not assumed finite. -/
theorem infiniteProductLaw_deviceArmEvent_sleeveLine_le
    {V : Type v} (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    (S : Finset H.edgeSet) (hS : S.Nonempty) (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, sleeveLine H S p s (sleeveComparisonSpeed a b S) T x ∈ Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) 0 hr0)
        (deviceArmEvent (graph H) (support H S) o n)).toReal ≤
      (infiniteProductLaw (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) T hrT)
        (deviceArmEvent (graph H) (support H S) o n)).toReal := by
  classical
  let K := SleeveTrace.coordinates H hG S o n
  have hRK : bondCoordinates (F := Unit) (annulus H S) ⊆ K :=
    SleeveTrace.annulus_subset_coordinates H hG S o n
  have haK : (Sum.inr () : (graph H).edgeSet ⊕ Unit) ∈ K :=
    SleeveTrace.activation_mem_coordinates H hG S o n
  have hdep : DependsOn (fun χ => χ ∈ deviceArmEvent (graph H) (support H S) o n)
      (K : Set ((graph H).edgeSet ⊕ Unit)) :=
    SleeveTrace.dependsOn_deviceArmEvent H hG S o n
  have h0 := eventWeight_traceEvent
    (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) 0 hr0) K
    (deviceArmEvent (graph H) (support H S) o n) hdep
  have hT' := eventWeight_traceEvent
    (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) T hrT) K
    (deviceArmEvent (graph H) (support H S) o n) hdep
  calc
    _ = eventWeight (fun x : K => sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) := h0.symm
    _ ≤ eventWeight (fun x : K => sleeveLine H S p s (sleeveComparisonSpeed a b S) T x.1)
        (traceEvent K (deviceArmEvent (graph H) (support H S) o n)) :=
      traceEventWeight_sleeveLine_le H S hS o n hRK haK p s a b T
        ha hb hT hp0 hs0 hpT hsT
    _ = _ := hT'


/-- The shared-sleeve enhanced configuration is measurable, with no
countability or finiteness assumption on the base edge type. -/
lemma measurable_deviceConfig_support {V : Type v} (H : SimpleGraph V)
    (S : Finset H.edgeSet) : Measurable (deviceConfig (support H S)) := by
  classical
  apply measurable_pi_iff.2
  intro f
  by_cases hf : f ∈ edges H S
  · have heq : (fun χ => deviceConfig (support H S) χ f) =
        (fun χ => if χ (Sum.inr ()) = true then true else χ (Sum.inl f)) := by
      funext χ
      by_cases ha : χ (Sum.inr ()) = true <;>
        simp [deviceConfig, AddsEdge, support, hf, ha]
    rw [heq]
    exact Measurable.ite
      (by measurability) measurable_const (measurable_pi_apply _)
  · have heq : (fun χ => deviceConfig (support H S) χ f) =
        (fun χ => χ (Sum.inl f)) := by
      funext χ
      simp [deviceConfig, AddsEdge, support, hf]
    rw [heq]
    exact measurable_pi_apply _

/-- The actual infinite-cluster event after applying the shared sleeve. -/
def sleevePercolationEvent {V : Type v} (H : SimpleGraph V)
    (S : Finset H.edgeSet) (o : V ⊕ H.edgeSet) :
    Set (JointConfig (graph H).edgeSet Unit) :=
  deviceConfig (support H S) ⁻¹'
    {ω | {x | OpenConnected (graph H) ω Set.univ o x}.Infinite}

/-- Enhanced percolation is exactly the decreasing intersection of the
finite-arm events on the explicitly constructed sleeved graph. -/
lemma sleevePercolationEvent_eq_iInter {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) (S : Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) :
    sleevePercolationEvent H S o = ⋂ n, deviceArmEvent (graph H) (support H S) o n := by
  rw [sleevePercolationEvent, setOf_infinite_eq_iInter_armEvent (graphConnected H hG) o]
  ext χ
  simp only [Set.mem_preimage, Set.mem_iInter, deviceArmEvent, deviceEvent]

/-- Continuity from above for the actual infinite-product arm probabilities.
No derivative is passed through this limit. -/
theorem tendsto_infiniteProductLaw_deviceArmEvent
    {V : Type v} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) (S : Finset H.edgeSet) (o : V ⊕ H.edgeSet)
    (r : (graph H).edgeSet ⊕ Unit → unitInterval) :
    Tendsto (fun n =>
      (infiniteProductLaw r (deviceArmEvent (graph H) (support H S) o n)).toReal)
      atTop (𝓝 ((infiniteProductLaw r (sleevePercolationEvent H S o)).toReal)) := by
  have hlim : Tendsto (fun n =>
      infiniteProductLaw r (deviceArmEvent (graph H) (support H S) o n)) atTop
      (𝓝 (infiniteProductLaw r (sleevePercolationEvent H S o))) := by
    rw [sleevePercolationEvent_eq_iInter H hG S o]
    exact tendsto_measure_iInter_atTop
      (fun n => ((measurable_deviceConfig_support H S)
        (measurableSet_armEvent o n)).nullMeasurableSet)
      (by
        intro m n hmn
        exact Set.preimage_mono (armEvent_antitone o hmn))
      ⟨0, measure_ne_top _ _⟩
  have hreal := (ENNReal.tendsto_toReal
    (a := infiniteProductLaw r (sleevePercolationEvent H S o))
    (measure_ne_top _ _)).comp hlim
  simpa only [Function.comp_def] using hreal

/-- **Infinite-cluster comparison for the explicitly constructed sleeved
graph.**  The exact finite-trace normalization is used at every arm radius;
continuity from above, rather than an asserted derivative/limit interchange,
finishes the argument.  This is a one-shared-sleeve comparison, not the full
multi-device reference critical-point theorem. -/
theorem infiniteProductLaw_sleevePercolation_sleeveLine_le
    {V : Type v} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) (S : Finset H.edgeSet) (hS : S.Nonempty)
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - sleeveComparisonSpeed a b S * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, sleeveLine H S p s (sleeveComparisonSpeed a b S) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, sleeveLine H S p s (sleeveComparisonSpeed a b S) T x ∈ Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) 0 hr0)
        (sleevePercolationEvent H S o)).toReal ≤
      (infiniteProductLaw (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) T hrT)
        (sleevePercolationEvent H S o)).toReal := by
  apply le_of_tendsto_of_tendsto
    (tendsto_infiniteProductLaw_deviceArmEvent H hG S o
      (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) 0 hr0))
    (tendsto_infiniteProductLaw_deviceArmEvent H hG S o
      (unitSleeveLine H S p s (sleeveComparisonSpeed a b S) T hrT))
  exact Filter.Eventually.of_forall fun n =>
    infiniteProductLaw_deviceArmEvent_sleeveLine_le H hG S hS o n p s a b T
      ha hb hT hp0 hs0 hpT hsT hr0 hrT

end FK.AGImplant.Sleeve.Infinite

#print axioms FK.AGImplant.Sleeve.Infinite.infiniteProductLaw_traceEvent
#print axioms FK.AGImplant.Sleeve.Infinite.SleeveTrace.dependsOn_deviceArmEvent
#print axioms FK.AGImplant.Sleeve.Infinite.sleeve_trace_sum_pivot_event_mul_le
#print axioms FK.AGImplant.Sleeve.Infinite.monotoneOn_traceEventWeight_sleeveLine
#print axioms FK.AGImplant.Sleeve.Infinite.infiniteProductLaw_deviceArmEvent_sleeveLine_le
#print axioms FK.AGImplant.Sleeve.Infinite.tendsto_infiniteProductLaw_deviceArmEvent
#print axioms FK.AGImplant.Sleeve.Infinite.infiniteProductLaw_sleevePercolation_sleeveLine_le
