import FK.AGSleeveInfinite
import FK.AGMultiDeviceIndependence

/-!
# Infinite product limits for finitely many independently activated sleeves

This module removes the finite-base-edge hypothesis from the indexed sleeve
comparison.  The index type of devices is finite, but the underlying graph and
its edge type may be infinite.  A finite trace contains a metric arm, every
selected annulus, every activated spoke and every indexed activation.

The finite-dimensional marginal is an actual finite Bernoulli product.  Pivot
transport and the affine derivative are performed on that trace, and continuity
from above passes the resulting endpoint comparison to infinite clusters.  No
limit of derivatives or identification of distinct activations is used.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.AGImplant.Sleeve.IndexedInfinite

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite

universe u v w

/-- The union of the selected annuli, with no finiteness assumption on the
ambient edge type. -/
noncomputable def baseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) :
    Finset (graph H).edgeSet := by
  classical
  exact Finset.univ.biUnion fun i => annulus H (S i)

@[simp] lemma mem_baseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] {S : ι → Finset H.edgeSet}
    {f : (graph H).edgeSet} :
    f ∈ baseSupport H S ↔ ∃ i, f ∈ annulus H (S i) := by
  classical
  simp [baseSupport]

/-- All spokes on which the finite indexed family can act. -/
noncomputable def sleeveSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) :
    Finset (graph H).edgeSet := by
  classical
  exact Finset.univ.biUnion fun i => edges H (S i)

@[simp] lemma mem_sleeveSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] {S : ι → Finset H.edgeSet}
    {f : (graph H).edgeSet} :
    f ∈ sleeveSupport H S ↔ ∃ i, f ∈ edges H (S i) := by
  classical
  simp [sleeveSupport]

/-- Every member of a finite activation family has its own trace coordinate. -/
noncomputable def activationCoordinates {E : Type u} {ι : Type v} [Fintype ι] :
    Finset (E ⊕ ι) := by
  classical
  exact Finset.univ.image Sum.inr

@[simp] lemma mem_activationCoordinates {E : Type u} {ι : Type v} [Fintype ι]
    (x : E ⊕ ι) : x ∈ activationCoordinates ↔ ∃ i, x = Sum.inr i := by
  classical
  cases x with
  | inl e => simp [activationCoordinates]
  | inr i => simp [activationCoordinates]

/-- Finite trace for one metric arm and a whole finite family of sleeves. -/
noncomputable def coordinates {V : Type u} (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) (n : ℕ) : Finset ((graph H).edgeSet ⊕ ι) :=
  ((FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n).map
      ⟨Sum.inl, Sum.inl_injective⟩) ∪
    (bondCoordinates (F := ι) (baseSupport H S)) ∪
      (bondCoordinates (F := ι) (sleeveSupport H S)) ∪ activationCoordinates

lemma activation_mem_coordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) (i : ι) :
    (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ coordinates H hG S o n := by
  simp [coordinates, activationCoordinates]

lemma metric_mem_coordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ)
    {f : (graph H).edgeSet} (hf : f.1 ∈ innerEdges (graph H) o n) :
    (Sum.inl f : (graph H).edgeSet ⊕ ι) ∈ coordinates H hG S o n := by
  have hf' : f ∈ FK.InfiniteVolume.NestedMetricGeometry.metricEdges
      (graphConnected H hG) o n :=
    (FK.InfiniteVolume.NestedMetricGeometry.mem_metricEdges
      (graphConnected H hG) o n f).2 hf
  simp [coordinates, hf']

lemma baseSupport_subset_coordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) :
    bondCoordinates (F := ι) (baseSupport H S) ⊆ coordinates H hG S o n := by
  intro x hx
  simp [coordinates, hx]

lemma annulus_subset_coordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) (i : ι) :
    bondCoordinates (F := ι) (annulus H (S i)) ⊆ coordinates H hG S o n := by
  intro x hx
  apply baseSupport_subset_coordinates H hG S o n
  simp only [bondCoordinates, Finset.mem_map] at hx ⊢
  rcases hx with ⟨f, hf, rfl⟩
  exact ⟨f, mem_baseSupport H |>.2 ⟨i, hf⟩, rfl⟩

/-- The enhanced arm depends only on the explicit finite indexed trace. -/
lemma dependsOn_deviceArmEvent {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) :
    DependsOn (fun χ => χ ∈ deviceArmEvent (graph H) (independentSupport H S) o n)
      (coordinates H hG S o n : Set ((graph H).edgeSet ⊕ ι)) := by
  classical
  intro χ ξ hagree
  apply dependsOn_armEvent (G := graph H) (graphConnected H hG) o n
  intro f hf
  have hbond : χ (Sum.inl f) = ξ (Sum.inl f) :=
    hagree _ (metric_mem_coordinates H hG S o n hf)
  have hadd : AddsEdge (independentSupport H S) χ f ↔
      AddsEdge (independentSupport H S) ξ f := by
    constructor
    · rintro ⟨z, hz, hfS⟩
      refine ⟨z, ?_, hfS⟩
      rwa [← hagree _ (activation_mem_coordinates H hG S o n z)]
    · rintro ⟨z, hz, hfS⟩
      refine ⟨z, ?_, hfS⟩
      rwa [hagree _ (activation_mem_coordinates H hG S o n z)]
  change (if AddsEdge (independentSupport H S) χ f then true else χ (Sum.inl f)) =
    (if AddsEdge (independentSupport H S) ξ f then true else ξ (Sum.inl f))
  simp only [hadd, hbond]

/-- Closing an annulus on a finite trace agrees with closing its closed
extension on the whole joint configuration space. -/
lemma traceExtend_traceClose_annular {E : Type u} {ι : Type v}
    {R : Finset E} {K : Finset (E ⊕ ι)}
    (hRK : bondCoordinates (F := ι) R ⊆ K) (ξ : K → Bool) :
    traceExtend K (traceClose (bondCoordinates (F := ι) R) ξ) =
      annularClose R (traceExtend K ξ) := by
  classical
  rw [traceExtend_traceClose hRK]
  ext x
  cases x with
  | inl e =>
      by_cases he : e ∈ R
      · have hb : (Sum.inl e : E ⊕ ι) ∈ bondCoordinates (F := ι) R := by
          simp [bondCoordinates, he]
        simp [annularClose, he, hb]
      · have hb : (Sum.inl e : E ⊕ ι) ∉ bondCoordinates (F := ι) R := by
          simp [bondCoordinates, he]
        simp [annularClose, he, hb]
  | inr i =>
      have hb : (Sum.inr i : E ⊕ ι) ∉ bondCoordinates (F := ι) R := by
        simp [bondCoordinates]
      simp [annularClose, hb]

/-- A selected-bond pivot on a finite trace is transported to the activation
of the same indexed sleeve, with the exact likelihood and fibre constants. -/
lemma trace_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (i : ι) {o : V ⊕ H.edgeSet} (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (annulus H (S i)) ⊆ K)
    (haK : (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b)
    {x : K} (hx : x ∈ traceFinset
      (bondCoordinates (F := ι) (annulus H (S i))) K hRK) :
    δ ^ (S i).card * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ} ≤
      ((2 ^ (S i).card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
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
        (traceClose (bondCoordinates (F := ι) (annulus H (S i))) ξ) := by
    intro ξ hp
    have hxR := (mem_traceFinset (hRK := hRK) x).1 hx
    rcases Finset.mem_map.mp hxR with ⟨f, hf, hfx⟩
    obtain ⟨e, he, hfbase⟩ := (mem_annulus H (S := S i) (f := f)).1 hf
    subst f
    have hxf : x.1 = Sum.inl (baseEdge H e) := hfx.symm
    have hpFull : EdgePivotal
        (deviceArmEvent (graph H) (independentSupport H S) o n)
        (baseEdge H e) (traceExtend K ξ) := by
      have hp' := (pivotal_traceEvent K _ x ξ).1 hp
      change Pivotal _ (Sum.inl (baseEdge H e)) _
      rw [← hxf]
      exact hp'
    have haFull := activationPivotal_deviceArmEvent_independent H S i he n hpFull
    apply (pivotal_traceEvent K _ a _).2
    change Pivotal _ (Sum.inr i) _
    rw [traceExtend_traceClose_annular hRK]
    exact haFull
  have h := local_pi_event_mul_le ν
    (traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K hRK)
    δ hδ hν (traceClose (bondCoordinates (F := ι) (annulus H (S i))))
    (traceClose_isLocalModification hRK)
    {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}
    {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) a ξ}
    (by intro ξ hξ; exact hmap ξ hξ)
  simpa only [card_traceFinset, card_bondCoordinates, card_annulus, a] using h

/-- Within one sleeve, the sum of all selected-bond pivots on an arbitrary
finite trace is bounded by that sleeve's activation pivot. -/
lemma trace_sum_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (i : ι) {o : V ⊕ H.edgeSet} (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (annulus H (S i)) ⊆ K)
    (haK : (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b) :
    δ ^ (S i).card * (∑ x ∈ traceFinset
      (bondCoordinates (F := ι) (annulus H (S i))) K hRK,
      (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}) ≤
      ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
        (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K
            (deviceArmEvent (graph H) (independentSupport H S) o n))
              ⟨Sum.inr i, haK⟩ ξ} := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K hRK,
        δ ^ (S i).card * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K
            (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}) ≤
      ∑ _x ∈ traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K hRK,
        ((2 ^ (S i).card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K
            (deviceArmEvent (graph H) (independentSupport H S) o n))
              ⟨Sum.inr i, haK⟩ ξ} := by
      apply Finset.sum_le_sum
      intro x hx
      exact trace_edgePivotal_event_mul_le H S i n hRK haK ν δ hδ hν hx
    _ = ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
          (OpenPath.FinProb.pi ν).event
            {ξ | Pivotal (traceEvent K
              (deviceArmEvent (graph H) (independentSupport H S) o n))
                ⟨Sum.inr i, haK⟩ ξ} := by
      simp only [Finset.sum_const, card_traceFinset, card_bondCoordinates,
        card_annulus, nsmul_eq_mul]
      ring

lemma annulus_subset_baseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (i : ι) :
    annulus H (S i) ⊆ baseSupport H S := by
  intro f hf
  exact (mem_baseSupport H).2 ⟨i, hf⟩

lemma bondCoordinates_mono {E : Type u} {ι : Type v} {R Q : Finset E}
    (hRQ : R ⊆ Q) : bondCoordinates (F := ι) R ⊆ bondCoordinates (F := ι) Q := by
  intro x hx
  simp only [bondCoordinates, Finset.mem_map] at hx ⊢
  obtain ⟨e, he, rfl⟩ := hx
  exact ⟨e, hRQ he, rfl⟩

/-- Disjoint annuli give an exact, duplicate-free decomposition of trace
sums over the moved base coordinates. -/
lemma sum_baseTrace_eq_sum_devices {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (W : K → ℝ) :
    (∑ x ∈ traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hBK, W x) =
      ∑ i, ∑ x ∈ traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K
        ((bondCoordinates_mono (annulus_subset_baseSupport H S i)).trans hBK), W x := by
  classical
  let hsub : ∀ i, bondCoordinates (F := ι) (annulus H (S i)) ⊆ K :=
    fun i => (bondCoordinates_mono (annulus_subset_baseSupport H S i)).trans hBK
  let Ri : ι → Finset K := fun i =>
    traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K (hsub i)
  have hEq : traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hBK =
      Finset.univ.biUnion Ri := by
    ext x
    constructor
    · intro hx
      obtain ⟨f, hf, hfx⟩ := Finset.mem_map.mp ((mem_traceFinset (hRK := hBK) x).1 hx)
      obtain ⟨i, hi⟩ := (mem_baseSupport H).1 hf
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, (mem_traceFinset (hRK := hsub i) x).2 ?_⟩
      exact Finset.mem_map.mpr ⟨f, hi, hfx⟩
    · intro hx
      obtain ⟨i, _hiuniv, hxi⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨f, hf, hfx⟩ :=
        Finset.mem_map.mp ((mem_traceFinset (hRK := hsub i) x).1 hxi)
      apply (mem_traceFinset (hRK := hBK) x).2
      exact Finset.mem_map.mpr ⟨f, (mem_baseSupport H).2 ⟨i, hf⟩, hfx⟩
  have hpair : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (Ri i) (Ri j) := by
    intro i _hi j _hj hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨fi, hfi, hfix⟩ := Finset.mem_map.mp
      ((mem_traceFinset (hRK := hsub i) x).1 hxi)
    obtain ⟨fj, hfj, hfjx⟩ := Finset.mem_map.mp
      ((mem_traceFinset (hRK := hsub j) x).1 hxj)
    have hf_eq : fi = fj :=
      Sum.inl_injective (hfix.trans hfjx.symm)
    subst fj
    exact (Finset.disjoint_left.mp (hdisj i j hij)) hfi hfj
  change (∑ x ∈ traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hBK, W x) =
    ∑ i, ∑ x ∈ Ri i, W x
  rw [hEq, Finset.sum_biUnion hpair]

/-- Exact cardinality of the moved base support for pairwise-disjoint annuli. -/
lemma card_baseSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j))) :
    (baseSupport H S).card = ∑ i, (S i).card := by
  classical
  rw [baseSupport, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _hi
    exact card_annulus H (S i)
  · intro i _hi j _hj hij
    exact hdisj i j hij

/-- The finite subfamily selected from the actual automorphism packing. -/
noncomputable def packedSleeves {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) (F : Finset (H ≃g H)) : {φ // φ ∈ F} → Finset H.edgeSet :=
  fun φ => S.map φ.1.mapEdgeSet.toEmbedding

/-- The actual uniform packing gives exact no-overlap support size on an
arbitrary, possibly infinite, sleeved graph. -/
lemma card_baseSupport_packed {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    (baseSupport H (packedSleeves H S F)).card = F.card * S.card := by
  classical
  unfold packedSleeves
  rw [card_baseSupport H _ (disjoint_packedIndependentAnnuli_fintype H S hM F hFM)]
  simp

/-- Ordinary-bond velocities for a finite family, defined on an arbitrary
ambient edge type. -/
noncomputable def indexedVelocity {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (c : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ baseSupport H S then -c else 0) (fun _ => 1)

/-- All selected annular bonds move down and every device's own activation
moves up along this affine comparison line. -/
noncomputable def indexedLine {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (p s c t : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ baseSupport H S then p - c * t else p)
    (fun _ => s + t)

lemma indexedLine_eq_affine {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (p s c t : ℝ) :
    indexedLine H S p s c t = affineRates (indexedLine H S p s c 0)
      (indexedVelocity H S c) t := by
  classical
  funext x
  cases x with
  | inl e =>
      by_cases he : e ∈ baseSupport H S <;>
        simp only [indexedLine, indexedVelocity, affineRates, Sum.elim_inl, he,
          ↓reduceIte] <;> ring
  | inr i =>
      simp [indexedLine, indexedVelocity, affineRates]

/-- Restriction of the indexed velocity to a finite trace. -/
noncomputable def traceVelocity {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    {K : Finset ((graph H).edgeSet ⊕ ι)} (c : ℝ) : K → ℝ :=
  fun x => indexedVelocity H S c x.1

lemma traceVelocity_of_mem_base {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    {hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K} {x : K}
    (hx : x ∈ traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hBK) :
    traceVelocity H S c x = -c := by
  have hxR := (mem_traceFinset (hRK := hBK) x).1 hx
  obtain ⟨f, hf, hfx⟩ := Finset.mem_map.mp hxR
  change indexedVelocity H S c x.1 = -c
  rw [← hfx]
  simp only [indexedVelocity, Function.Embedding.coeFn_mk, Sum.elim_inl, hf,
    ↓reduceIte]

lemma traceVelocity_activation {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K) (i : ι) :
    traceVelocity H S c (⟨Sum.inr i, haK i⟩ : K) = 1 := by
  simp [traceVelocity, indexedVelocity]

lemma traceVelocity_eq_zero {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (a : ι ↪ K) (ha : ∀ i, a i = ⟨Sum.inr i, haK i⟩) {x : K}
    (hxB : x ∉ traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hBK)
    (hxA : x ∉ Finset.univ.map a) :
    traceVelocity H S c x = 0 := by
  classical
  cases hx : x.1 with
  | inl f =>
      have hf : f ∉ baseSupport H S := by
        intro hf
        apply hxB
        apply (mem_traceFinset (hRK := hBK) x).2
        rw [hx]
        simp [bondCoordinates, hf]
      change indexedVelocity H S c x.1 = 0
      rw [hx]
      simp only [indexedVelocity, Sum.elim_inl, hf, ↓reduceIte]
  | inr i =>
      exfalso
      apply hxA
      apply Finset.mem_map.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [ha i]
      exact Subtype.ext hx.symm

/-- The derivative support decomposes exactly into the moved annuli and all
separate activation coordinates. -/
lemma sum_traceVelocity_mul {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (a : ι ↪ K) (ha : ∀ i, a i = ⟨Sum.inr i, haK i⟩) (W : K → ℝ) :
    (∑ x, traceVelocity H S c x * W x) =
      (-c) * (∑ x ∈ traceFinset
        (bondCoordinates (F := ι) (baseSupport H S)) K hBK, W x) +
        ∑ i, W (a i) := by
  classical
  let B := traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hBK
  let A := Finset.univ.map a
  have hdisj : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    obtain ⟨i, _hi, hix⟩ := Finset.mem_map.mp hxA
    have hx := (mem_traceFinset (hRK := hBK) x).1 hxB
    rw [← hix, ha i] at hx
    simp [bondCoordinates] at hx
  calc
    (∑ x, traceVelocity H S c x * W x) =
        ∑ x ∈ B ∪ A, traceVelocity H S c x * W x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _hxuniv hx
      have hxB : x ∉ B := fun h => hx (Finset.mem_union_left _ h)
      have hxA : x ∉ A := fun h => hx (Finset.mem_union_right _ h)
      rw [traceVelocity_eq_zero H S c hBK haK a ha hxB hxA, zero_mul]
    _ = (∑ x ∈ B, traceVelocity H S c x * W x) +
        ∑ x ∈ A, traceVelocity H S c x * W x := by
      rw [Finset.sum_union hdisj]
    _ = (∑ x ∈ B, (-c) * W x) + ∑ x ∈ A, W x := by
      congr 1
      · apply Finset.sum_congr rfl
        intro x hx
        rw [traceVelocity_of_mem_base H S c hx]
      · apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
        rw [ha i, traceVelocity_activation H S c haK i, one_mul]
    _ = (-c) * (∑ x ∈ B, W x) + ∑ i, W (a i) := by
      rw [Finset.mul_sum]
      simp [A]

/-- The canonical embedding of indexed activations into any trace that
contains them all. -/
noncomputable def traceActivationEmbedding {E : Type u} {ι : Type v}
    {K : Finset (E ⊕ ι)} (haK : ∀ i, (Sum.inr i : E ⊕ ι) ∈ K) : ι ↪ K where
  toFun i := ⟨Sum.inr i, haK i⟩
  inj' := by
    intro i j hij
    exact Sum.inr_injective (congrArg Subtype.val hij)

@[simp] lemma traceActivationEmbedding_apply {E : Type u} {ι : Type v}
    {K : Finset (E ⊕ ι)} (haK : ∀ i, (Sum.inr i : E ⊕ ι) ∈ K) (i : ι) :
    traceActivationEmbedding haK i = ⟨Sum.inr i, haK i⟩ := rfl

lemma indexedLine_mem_box {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    {p s c t a b : ℝ} (hp : p ∈ Icc a b) (hmove : p - c * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) (x : (graph H).edgeSet ⊕ ι) :
    indexedLine H S p s c t x ∈ Icc a b := by
  cases x with
  | inl e =>
      by_cases he : e ∈ baseSupport H S
      · change (if e ∈ baseSupport H S then p - c * t else p) ∈ Icc a b
        simp only [he, ↓reduceIte]
        exact hmove
      · change (if e ∈ baseSupport H S then p - c * t else p) ∈ Icc a b
        simp only [he, ↓reduceIte]
        exact hp
  | inr i => exact hs

/-- Common-speed normalized slope bound on a finite trace. -/
lemma tracePivotSlope_nonneg_of_box {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b t : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Icc a b)
    (hmove : p - independentComparisonSpeed a b R * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) :
    let c := independentComparisonSpeed a b R
    0 ≤ (-c) * (∑ i, ∑ x ∈ traceFinset
        (bondCoordinates (F := ι) (annulus H (S i))) K
          ((bondCoordinates_mono (annulus_subset_baseSupport H S i)).trans hBK),
        eventWeight (fun y : K => indexedLine H S p s c t y.1)
          {ξ | Pivotal (traceEvent K
            (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}) +
      ∑ i, eventWeight (fun y : K => indexedLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n))
            ⟨Sum.inr i, haK i⟩ ξ} := by
  classical
  dsimp only
  let c := independentComparisonSpeed a b R
  let r : K → ℝ := fun y => indexedLine H S p s c t y.1
  let hsub : ∀ i, bondCoordinates (F := ι) (annulus H (S i)) ⊆ K :=
    fun i => (bondCoordinates_mono (annulus_subset_baseSupport H S i)).trans hBK
  let Dp : ι → ℝ := fun i => ∑ x ∈ traceFinset
    (bondCoordinates (F := ι) (annulus H (S i))) K (hsub i),
    eventWeight r {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}
  let Pa : ι → ℝ := fun i => eventWeight r {ξ | Pivotal (traceEvent K
    (deviceArmEvent (graph H) (independentSupport H S) o n)) ⟨Sum.inr i, haK i⟩ ξ}
  let den : ℝ := ((2 ^ R : ℕ) : ℝ) * (R : ℝ)
  have hrbox : ∀ x, r x ∈ Icc a b := by
    intro x
    exact indexedLine_mem_box H S hp hmove hs x.1
  have hr : ∀ x, r x ∈ Icc (0 : ℝ) 1 := by
    intro x
    exact ⟨ha.le.trans (hrbox x).1, (hrbox x).2.trans hb.le⟩
  let ν : K → OpenPath.FinProb Bool := fun x => boolLaw (r x) (hr x)
  have hminor : 0 < sleeveMinorant a b := sleeveMinorant_pos ha hb
  have hν : ∀ x bit, sleeveMinorant a b ≤ (ν x).mass bit := by
    intro x bit
    exact sleeveMinorant_le_boolLaw (hrbox x) (hr x) bit
  have hevent (C : Set (K → Bool)) :
      (OpenPath.FinProb.pi ν).event C = eventWeight r C := by
    simpa only [ν, boolProduct] using (eventWeight_eq_boolProduct_event r hr C).symm
  have hsum (i : ι) : (sleeveMinorant a b) ^ R * Dp i ≤ den * Pa i := by
    have h := trace_sum_edgePivotal_event_mul_le H S i n (hsub i) (haK i) ν
      (sleeveMinorant a b) hminor.le hν (o := o)
    simp_rw [hevent] at h
    change (sleeveMinorant a b) ^ (S i).card * Dp i ≤
      (((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ)) * Pa i at h
    rw [hcard i] at h
    exact h
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hden0 : den ≠ 0 := ne_of_gt hden
  have hcδ : c * den = (sleeveMinorant a b) ^ R := by
    change ((sleeveMinorant a b) ^ R / den) * den = (sleeveMinorant a b) ^ R
    exact div_mul_cancel₀ _ hden0
  have hmul (i : ι) : c * Dp i ≤ Pa i := by
    refine le_of_mul_le_mul_right (a := den) ?_ hden
    calc
      (c * Dp i) * den = (c * den) * Dp i := by ring
      _ = (sleeveMinorant a b) ^ R * Dp i := by rw [hcδ]
      _ ≤ den * Pa i := hsum i
      _ = Pa i * den := by ring
  have htotal : c * (∑ i, Dp i) ≤ ∑ i, Pa i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _hi => hmul i
  change 0 ≤ (-c) * (∑ i, Dp i) + ∑ i, Pa i
  linarith

/-- Endpoint parameters bound every intermediate point of the indexed line. -/
lemma indexedLine_parameters_mem_box {p s c a b T t : ℝ}
    (hc : 0 ≤ c) (ht : t ∈ Icc (0 : ℝ) T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - c * T ∈ Icc a b) (hsT : s + T ∈ Icc a b) :
    p - c * t ∈ Icc a b ∧ s + t ∈ Icc a b :=
  FK.AGGadget.diagonal_parameters_mem_Icc hc ht hp0 hs0 hpT hsT

/-- Monotonicity of the actual finite-trace polynomial with all annuli moving
down and all independently indexed activations moving up. -/
theorem monotoneOn_traceEventWeight_indexedLine {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn (fun t => eventWeight (fun x : K => indexedLine H S p s
      (independentComparisonSpeed a b R) t x.1)
      (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)))
      (Icc (0 : ℝ) T) := by
  classical
  let c := independentComparisonSpeed a b R
  let hsub : ∀ i, bondCoordinates (F := ι) (annulus H (S i)) ⊆ K :=
    fun i => (bondCoordinates_mono (annulus_subset_baseSupport H S i)).trans hBK
  let Dp : ℝ → ℝ := fun t => ∑ i, ∑ x ∈ traceFinset
    (bondCoordinates (F := ι) (annulus H (S i))) K (hsub i),
    eventWeight (fun y : K => indexedLine H S p s c t y.1)
      {ξ | Pivotal (traceEvent K
        (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}
  let Pa : ℝ → ℝ := fun t => ∑ i,
    eventWeight (fun y : K => indexedLine H S p s c t y.1)
      {ξ | Pivotal (traceEvent K
        (deviceArmEvent (graph H) (independentSupport H S) o n))
          ⟨Sum.inr i, haK i⟩ ξ}
  let aemb := traceActivationEmbedding haK
  have hc : 0 ≤ c := independentComparisonSpeed_nonneg R ha.le hb.le
  have hupper : IsUpperSet (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
    isUpperSet_traceEvent K (isUpperSet_deviceArmEvent (graph H)
      (independentSupport H S) o n)
  have hline (t : ℝ) : (fun x : K => indexedLine H S p s c t x.1) =
      affineRates (fun x : K => indexedLine H S p s c 0 x.1)
        (traceVelocity H S c) t := by
    funext x
    exact congrFun (indexedLine_eq_affine H S p s c t) x.1
  have hderiv (t : ℝ) : HasDerivAt
      (fun y => eventWeight (fun x : K => indexedLine H S p s c y x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)))
      ((-c) * Dp t + Pa t) t := by
    have h := hasDerivAt_eventWeight_affine_pivotal
      (fun x : K => indexedLine H S p s c 0 x.1) (traceVelocity H S c) hupper t
    simp_rw [← hline] at h
    have hvel := sum_traceVelocity_mul H S c hBK haK aemb
      (fun _ => rfl) (fun x => eventWeight
        (fun y : K => indexedLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ})
    have hbase := sum_baseTrace_eq_sum_devices H S hBK hdisj
      (fun x => eventWeight (fun y : K => indexedLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ})
    rw [hvel, hbase] at h
    simpa only [Dp, Pa, aemb, traceActivationEmbedding_apply] using h
  change MonotoneOn (fun t => eventWeight (fun x : K => indexedLine H S p s c t x.1)
    (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)))
    (Icc (0 : ℝ) T)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T)
    (f' := fun t => (-c) * Dp t + Pa t)
  · intro t _ht
    exact (hderiv t).continuousAt.continuousWithinAt
  · intro t _ht
    exact (hderiv t).hasDerivWithinAt
  · intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := interior_subset ht
    have hbox := indexedLine_parameters_mem_box hc htcc hp0 hs0 hpT hsT
    exact tracePivotSlope_nonneg_of_box H S R hR hcard o n hBK haK
      p s a b t ha hb hp0 hbox.1 hbox.2

/-- Endpoint comparison for the finite-trace polynomial. -/
theorem traceEventWeight_indexedLine_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (fun x : K => indexedLine H S p s
        (independentComparisonSpeed a b R) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) ≤
      eventWeight (fun x : K => indexedLine H S p s
        (independentComparisonSpeed a b R) T x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) := by
  have hmono := monotoneOn_traceEventWeight_indexedLine H S hdisj R hR hcard o n
    hBK haK p s a b T ha hb hp0 hs0 hpT hsT
  exact hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

/-- The exact marginal on all activation coordinates is a finite product of
their own Bernoulli laws; no bond coordinate and no other device is collapsed
into a shared activation. -/
theorem infiniteProductLaw_map_activationCoordinates {E : Type u} {ι : Type v}
    [Fintype ι] (r : E ⊕ ι → unitInterval) :
    (infiniteProductLaw r).map
      ((activationCoordinates (E := E) (ι := ι) : Finset (E ⊕ ι)) : Set (E ⊕ ι)).domRestrict =
      FKEnhancement.bernoulliProduct
        (fun x : activationCoordinates (E := E) (ι := ι) => r x.1) := by
  exact infiniteProductLaw_map_trace r activationCoordinates

/-- Every event determined only by the finite family of activation coordinates
has exactly its finite-product probability in the actual infinite product. -/
theorem infiniteProductLaw_activation_traceEvent {E : Type u} {ι : Type v}
    [Fintype ι] (r : E ⊕ ι → unitInterval) (A : Set (JointConfig E ι))
    (hdep : DependsOn (fun χ => χ ∈ A)
      (activationCoordinates (E := E) (ι := ι) : Set (E ⊕ ι))) :
    (infiniteProductLaw r A).toReal =
      (FKEnhancement.bernoulliProduct
        (fun x : activationCoordinates (E := E) (ι := ι) => r x.1)
        (traceEvent activationCoordinates A)).toReal := by
  exact infiniteProductLaw_traceEvent r activationCoordinates A hdep

/-- Unit-interval parameters on one point of the indexed comparison line. -/
noncomputable def unitIndexedLine {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, indexedLine H S p s c t x ∈ Icc (0 : ℝ) 1) :
    (graph H).edgeSet ⊕ ι → unitInterval := fun x =>
  ⟨indexedLine H S p s c t x, (hr x).1, (hr x).2⟩

@[simp] lemma coe_unitIndexedLine {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, indexedLine H S p s c t x ∈ Icc (0 : ℝ) 1)
    (x : (graph H).edgeSet ⊕ ι) :
    (unitIndexedLine H S p s c t hr x : ℝ) = indexedLine H S p s c t x := rfl

/-- **Infinite-product arm comparison for a finite family of independently
activated sleeves.**  The graph may have infinitely many bonds.  Every finite
trace is the exact marginal of the displayed inhomogeneous product law. -/
theorem infiniteProductLaw_deviceArmEvent_indexedLine_le {V : Type u}
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, indexedLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Icc (0 : ℝ) 1)
    (hrT : ∀ x, indexedLine H S p s (independentComparisonSpeed a b R) T x ∈
      Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitIndexedLine H S p s
        (independentComparisonSpeed a b R) 0 hr0)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal ≤
      (infiniteProductLaw (unitIndexedLine H S p s
        (independentComparisonSpeed a b R) T hrT)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal := by
  classical
  let K := coordinates H hG S o n
  have hBK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K :=
    baseSupport_subset_coordinates H hG S o n
  have haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K :=
    activation_mem_coordinates H hG S o n
  have hdep : DependsOn (fun χ => χ ∈ deviceArmEvent (graph H)
      (independentSupport H S) o n) (K : Set ((graph H).edgeSet ⊕ ι)) :=
    dependsOn_deviceArmEvent H hG S o n
  have h0 := eventWeight_traceEvent
    (unitIndexedLine H S p s (independentComparisonSpeed a b R) 0 hr0) K
    (deviceArmEvent (graph H) (independentSupport H S) o n) hdep
  have hT' := eventWeight_traceEvent
    (unitIndexedLine H S p s (independentComparisonSpeed a b R) T hrT) K
    (deviceArmEvent (graph H) (independentSupport H S) o n) hdep
  calc
    _ = eventWeight (fun x : K => indexedLine H S p s
        (independentComparisonSpeed a b R) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) := h0.symm
    _ ≤ eventWeight (fun x : K => indexedLine H S p s
        (independentComparisonSpeed a b R) T x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      traceEventWeight_indexedLine_le H S hdisj R hR hcard o n hBK haK
        p s a b T ha hb hT hp0 hs0 hpT hsT
    _ = _ := hT'

/-- The indexed device configuration is measurable on an arbitrary joint
product space.  The existential over devices is finite. -/
lemma measurable_deviceConfig_independentSupport {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) :
    Measurable (deviceConfig (independentSupport H S)) := by
  classical
  apply measurable_pi_iff.2
  intro f
  change Measurable (fun χ => if AddsEdge (independentSupport H S) χ f then true
    else χ (Sum.inl f))
  apply Measurable.ite
  · have hset : {χ : JointConfig (graph H).edgeSet ι |
        AddsEdge (independentSupport H S) χ f} =
        ⋃ i ∈ {i : ι | f ∈ edges H (S i)},
          (fun χ : JointConfig (graph H).edgeSet ι => χ (Sum.inr i)) ⁻¹' {true} := by
      ext χ
      simp only [AddsEdge, mem_independentSupport, Set.mem_ofPred_eq, Set.mem_iUnion,
        Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, hfS⟩
        exact ⟨z, hfS, hz⟩
      · rintro ⟨z, hfS, hz⟩
        exact ⟨z, hz, hfS⟩
    rw [hset]
    exact MeasurableSet.biUnion (Set.to_countable _)
      (fun i _hi => (measurable_pi_apply (Sum.inr i)) (measurableSet_singleton true))
  · fun_prop
  · exact measurable_pi_apply _

/-- Actual infinite-cluster event for the full finite family of independently
activated sleeves. -/
def indexedPercolationEvent {V : Type u} (H : SimpleGraph V)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) :
    Set (JointConfig (graph H).edgeSet ι) :=
  deviceConfig (independentSupport H S) ⁻¹'
    {ω | {x | OpenConnected (graph H) ω Set.univ o x}.Infinite}

lemma indexedPercolationEvent_eq_iInter {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) :
    indexedPercolationEvent H S o =
      ⋂ n, deviceArmEvent (graph H) (independentSupport H S) o n := by
  rw [indexedPercolationEvent, setOf_infinite_eq_iInter_armEvent (graphConnected H hG) o]
  ext χ
  simp only [Set.mem_preimage, Set.mem_iInter, deviceArmEvent, deviceEvent]

/-- Continuity from above for the actual indexed infinite-product arm laws. -/
theorem tendsto_infiniteProductLaw_deviceArmEvent {V : Type u} [Countable V]
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) (r : (graph H).edgeSet ⊕ ι → unitInterval) :
    Tendsto (fun n =>
      (infiniteProductLaw r (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal)
      atTop (𝓝 ((infiniteProductLaw r (indexedPercolationEvent H S o)).toReal)) := by
  have hlim : Tendsto (fun n =>
      infiniteProductLaw r (deviceArmEvent (graph H) (independentSupport H S) o n)) atTop
      (𝓝 (infiniteProductLaw r (indexedPercolationEvent H S o))) := by
    rw [indexedPercolationEvent_eq_iInter H hG S o]
    exact tendsto_measure_iInter_atTop
      (fun n => ((measurable_deviceConfig_independentSupport H S)
        (measurableSet_armEvent o n)).nullMeasurableSet)
      (by
        intro m n hmn
        exact Set.preimage_mono (armEvent_antitone o hmn))
      ⟨0, measure_ne_top _ _⟩
  have hreal := (ENNReal.tendsto_toReal
    (a := infiniteProductLaw r (indexedPercolationEvent H S o))
    (measure_ne_top _ _)).comp hlim
  simpa only [Function.comp_def] using hreal

/-- **Infinite-cluster comparison for finitely many independently activated
sleeves on an infinite connected locally finite graph.**  The inequality is
first proved for every finite arm radius and then passed through continuity
from above; no derivative is passed through the limit. -/
theorem infiniteProductLaw_indexedPercolation_indexedLine_le {V : Type u}
    [Countable V] (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} [Fintype ι] (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (annulus H (S i)) (annulus H (S j)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, indexedLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Icc (0 : ℝ) 1)
    (hrT : ∀ x, indexedLine H S p s (independentComparisonSpeed a b R) T x ∈
      Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitIndexedLine H S p s
        (independentComparisonSpeed a b R) 0 hr0)
        (indexedPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw (unitIndexedLine H S p s
        (independentComparisonSpeed a b R) T hrT)
        (indexedPercolationEvent H S o)).toReal := by
  apply le_of_tendsto_of_tendsto
    (tendsto_infiniteProductLaw_deviceArmEvent H hG S o
      (unitIndexedLine H S p s (independentComparisonSpeed a b R) 0 hr0))
    (tendsto_infiniteProductLaw_deviceArmEvent H hG S o
      (unitIndexedLine H S p s (independentComparisonSpeed a b R) T hrT))
  exact Filter.Eventually.of_forall fun n =>
    infiniteProductLaw_deviceArmEvent_indexedLine_le H hG S hdisj R hR hcard o n
      p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT

/-- The preceding infinite-cluster comparison instantiated to a finite part of
the repository's actual uniform whole-template packing.  Disjoint annuli and
uniform annulus size are proved from the packing, not assumed again. -/
theorem infiniteProductLaw_packedPercolation_indexedLine_le {V : Type u}
    [Countable V] (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    (S : Finset H.edgeSet) (hS : S.Nonempty) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M)
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b S.card * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, indexedLine H (packedSleeves H S F) p s
      (independentComparisonSpeed a b S.card) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, indexedLine H (packedSleeves H S F) p s
      (independentComparisonSpeed a b S.card) T x ∈ Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitIndexedLine H (packedSleeves H S F) p s
        (independentComparisonSpeed a b S.card) 0 hr0)
        (indexedPercolationEvent H (packedSleeves H S F) o)).toReal ≤
      (infiniteProductLaw (unitIndexedLine H (packedSleeves H S F) p s
        (independentComparisonSpeed a b S.card) T hrT)
        (indexedPercolationEvent H (packedSleeves H S F) o)).toReal := by
  classical
  have hdisj : ∀ φ ψ : {φ // φ ∈ F}, φ ≠ ψ →
      Disjoint (annulus H ((packedSleeves H S F) φ))
        (annulus H ((packedSleeves H S F) ψ)) := by
    intro φ ψ hne
    exact disjoint_packedIndependentAnnuli_fintype H S hM F hFM φ ψ hne
  have hcard : ∀ φ, ((packedSleeves H S F) φ).card = S.card := by
    intro φ
    exact card_map_mapEdgeSet H φ.1 S
  exact infiniteProductLaw_indexedPercolation_indexedLine_le H hG
    (packedSleeves H S F) hdisj S.card (Finset.card_pos.mpr hS) hcard o
      p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT

end FK.AGImplant.Sleeve.IndexedInfinite

#print axioms FK.AGImplant.Sleeve.IndexedInfinite.infiniteProductLaw_map_activationCoordinates
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.dependsOn_deviceArmEvent
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.trace_sum_edgePivotal_event_mul_le
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.sum_baseTrace_eq_sum_devices
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.card_baseSupport_packed
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.tracePivotSlope_nonneg_of_box
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.monotoneOn_traceEventWeight_indexedLine
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.infiniteProductLaw_deviceArmEvent_indexedLine_le
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.measurable_deviceConfig_independentSupport
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.tendsto_infiniteProductLaw_deviceArmEvent
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.infiniteProductLaw_indexedPercolation_indexedLine_le
#print axioms FK.AGImplant.Sleeve.IndexedInfinite.infiniteProductLaw_packedPercolation_indexedLine_le
