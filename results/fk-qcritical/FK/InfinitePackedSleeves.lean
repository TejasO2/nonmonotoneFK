import FK.IndexedSleeveInfinite

/-!
# Infinite packed families of independent sleeves

A fixed metric arm sees only finitely many devices in a pairwise-disjoint
packing.  This file proves the corresponding finite-trace differential on the
original global coordinate type and uses it for genuinely infinite device
families.  No infinite sum of derivatives is formed: the omitted-device tail
of every fixed-arm polynomial is exactly zero.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.AGImplant.Sleeve.GlobalInfinite

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.IndexedInfinite

universe u v w

/-- Devices whose complete template meets a given finite edge set. -/
def incidentDevices {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (L : Finset (graph H).edgeSet) : Set ι :=
  {i | ∃ f ∈ L, f ∈ template H (S i)}

/-- At most one packed template contains any prescribed edge. -/
def EdgeUnique {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) : Prop :=
  ∀ f : (graph H).edgeSet, {i | f ∈ template H (S i)}.Subsingleton

lemma incidentDevices_eq_iUnion {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (L : Finset (graph H).edgeSet) :
    incidentDevices H S L = ⋃ f ∈ (L : Set (graph H).edgeSet),
      {i | f ∈ template H (S i)} := by
  ext i
  simp [incidentDevices]

lemma finite_incidentDevices {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (L : Finset (graph H).edgeSet) : (incidentDevices H S L).Finite := by
  rw [incidentDevices_eq_iUnion]
  exact L.finite_toSet.biUnion fun f _hf => (hunique f).finite

/-- The finite set of devices incident to a finite edge trace. -/
noncomputable def incidentFinset {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (L : Finset (graph H).edgeSet) : Finset ι :=
  (finite_incidentDevices H S hunique L).toFinset

@[simp] lemma mem_incidentFinset {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    {L : Finset (graph H).edgeSet} {i : ι} :
    i ∈ incidentFinset H S hunique L ↔ i ∈ incidentDevices H S L := by
  exact Set.Finite.mem_toFinset _

/-- Pairwise-disjoint templates imply edge uniqueness. -/
lemma edgeUnique_of_pairwiseDisjoint {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → Disjoint (template H (S i)) (template H (S j))) :
    EdgeUnique H S := by
  intro f i hi j hj
  by_contra hne
  exact (Finset.disjoint_left.1 (hdisj i j hne)) hi hj

/-- Moved original bonds in the finite incident family. -/
noncomputable def baseSupportOn {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) : Finset (graph H).edgeSet := by
  classical
  exact J.biUnion fun i => annulus H (S i)

@[simp] lemma mem_baseSupportOn {V : Type u} (H : SimpleGraph V) {ι : Type v}
    {S : ι → Finset H.edgeSet} {J : Finset ι} {f : (graph H).edgeSet} :
    f ∈ baseSupportOn H S J ↔ ∃ i ∈ J, f ∈ annulus H (S i) := by
  classical simp [baseSupportOn]

/-- Activated spokes in the finite incident family. -/
noncomputable def sleeveSupportOn {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) : Finset (graph H).edgeSet := by
  classical
  exact J.biUnion fun i => edges H (S i)

/-- Finite incident activation coordinates on the original global index type. -/
noncomputable def activationCoordinatesOn {E : Type u} {ι : Type v} (J : Finset ι) :
    Finset (E ⊕ ι) := by
  classical exact J.image Sum.inr

/-- Global affine line: every packed annular bond moves down and every device
activation moves up.  The family need not be finite. -/
noncomputable def globalLine {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (p s c t : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if ∃ i, e ∈ annulus H (S i) then p - c * t else p)
    (fun _ => s + t)

/-- The same line with all devices outside `J` frozen. -/
noncomputable def localLine {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (p s c t : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ baseSupportOn H S J then p - c * t else p)
    (fun i => if i ∈ J then s + t else s)

/-- Velocity of the localized affine line. -/
noncomputable def localVelocity {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (c : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ baseSupportOn H S J then -c else 0)
    (fun i => if i ∈ J then 1 else 0)

lemma localLine_eq_affine {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (p s c t : ℝ) :
    localLine H S J p s c t = affineRates (localLine H S J p s c 0)
      (localVelocity H S J c) t := by
  classical
  funext x
  cases x with
  | inl e => by_cases he : e ∈ baseSupportOn H S J <;>
      simp only [localLine, localVelocity, affineRates, Sum.elim_inl, he,
        ↓reduceIte] <;> ring
  | inr i => by_cases hi : i ∈ J <;>
      simp only [localLine, localVelocity, affineRates, Sum.elim_inr, hi,
        ↓reduceIte] <;> ring

/-- Finite trace for a full infinite family, localized to the devices in `J`. -/
noncomputable def localCoordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (o : V ⊕ H.edgeSet) (n : ℕ) :
    Finset ((graph H).edgeSet ⊕ ι) :=
  ((FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n).map
      ⟨Sum.inl, Sum.inl_injective⟩) ∪
    (bondCoordinates (F := ι) (baseSupportOn H S J)) ∪
      (bondCoordinates (F := ι) (sleeveSupportOn H S J)) ∪ activationCoordinatesOn J

lemma metric_mem_localCoordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (o : V ⊕ H.edgeSet) (n : ℕ)
    {f : (graph H).edgeSet} (hf : f.1 ∈ innerEdges (graph H) o n) :
    (Sum.inl f : (graph H).edgeSet ⊕ ι) ∈ localCoordinates H hG S J o n := by
  have hf' : f ∈ FK.InfiniteVolume.NestedMetricGeometry.metricEdges
      (graphConnected H hG) o n :=
    (FK.InfiniteVolume.NestedMetricGeometry.mem_metricEdges
      (graphConnected H hG) o n f).2 hf
  simp [localCoordinates, hf']

lemma activation_mem_localCoordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) {J : Finset ι} (o : V ⊕ H.edgeSet) (n : ℕ)
    {i : ι} (hi : i ∈ J) :
    (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ localCoordinates H hG S J o n := by
  simp [localCoordinates, activationCoordinatesOn, hi]

lemma baseSupportOn_subset_localCoordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (o : V ⊕ H.edgeSet) (n : ℕ) :
    bondCoordinates (F := ι) (baseSupportOn H S J) ⊆
      localCoordinates H hG S J o n := by
  intro x hx
  simp [localCoordinates, hx]

lemma annulus_subset_baseSupportOn {V : Type u} (H : SimpleGraph V) {ι : Type v}
    {S : ι → Finset H.edgeSet} {J : Finset ι} {i : ι} (hi : i ∈ J) :
    annulus H (S i) ⊆ baseSupportOn H S J := by
  intro f hf
  exact mem_baseSupportOn H |>.2 ⟨i, hi, hf⟩

/-- On the localized trace, a full infinite-family arm depends only on the
incident activations.  No outside-device activation coordinate is needed. -/
lemma dependsOn_deviceArmEvent_local {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) {J : Finset ι}
    (o : V ⊕ H.edgeSet) (n : ℕ)
    (hJ : incidentDevices H S
      (FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n) ⊆ J) :
    DependsOn (fun χ => χ ∈ deviceArmEvent (graph H) (independentSupport H S) o n)
      (localCoordinates H hG S J o n : Set ((graph H).edgeSet ⊕ ι)) := by
  classical
  intro χ ξ hagree
  apply dependsOn_armEvent (G := graph H) (graphConnected H hG) o n
  intro f hf
  have hbond : χ (Sum.inl f) = ξ (Sum.inl f) :=
    hagree _ (metric_mem_localCoordinates H hG S J o n hf)
  have hadd : AddsEdge (independentSupport H S) χ f ↔
      AddsEdge (independentSupport H S) ξ f := by
    constructor
    · rintro ⟨i, hi, hfS⟩
      have hiJ : i ∈ J := by
        apply hJ
        refine ⟨f, ?_, ?_⟩
        · exact (FK.InfiniteVolume.NestedMetricGeometry.mem_metricEdges
            (graphConnected H hG) o n f).2 hf
        · exact (mem_template H).2 (Or.inr hfS)
      refine ⟨i, ?_, hfS⟩
      rwa [← hagree _ (activation_mem_localCoordinates H hG S o n hiJ)]
    · rintro ⟨i, hi, hfS⟩
      have hiJ : i ∈ J := by
        apply hJ
        refine ⟨f, ?_, (mem_template H).2 (Or.inr hfS)⟩
        exact (FK.InfiniteVolume.NestedMetricGeometry.mem_metricEdges
          (graphConnected H hG) o n f).2 hf
      refine ⟨i, ?_, hfS⟩
      rwa [hagree _ (activation_mem_localCoordinates H hG S o n hiJ)]
  change (if AddsEdge (independentSupport H S) χ f then true else χ (Sum.inl f)) =
    (if AddsEdge (independentSupport H S) ξ f then true else ξ (Sum.inl f))
  simp only [hadd, hbond]

/-- Pivot transport on a finite trace of an arbitrarily indexed family. -/
lemma globalTrace_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet)
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
lemma globalTrace_sum_edgePivotal_event_mul_le {V : Type u}
    (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet)
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
      exact globalTrace_edgePivotal_event_mul_le H S i n hRK haK ν δ hδ hν hx
    _ = ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
          (OpenPath.FinProb.pi ν).event
            {ξ | Pivotal (traceEvent K
              (deviceArmEvent (graph H) (independentSupport H S) o n))
                ⟨Sum.inr i, haK⟩ ξ} := by
      simp only [Finset.sum_const, card_traceFinset, card_bondCoordinates,
        card_annulus, nsmul_eq_mul]
      ring


/-- Exact cardinality of a disjoint finite moved-base support. -/
lemma card_baseSupportOn {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (annulus H (S i)) (annulus H (S j))) :
    (baseSupportOn H S J).card = ∑ i ∈ J, (S i).card := by
  classical
  rw [baseSupportOn, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _hi
    exact card_annulus H (S i)
  · exact hdisj

/-- Disjoint annuli give a duplicate-free decomposition of moved-base trace
sums over the finite incident subtype. -/
lemma sum_localBaseTrace_eq_sum_devices {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (J : Finset ι)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K)
    (hdisj : ∀ (i j : J), i ≠ j →
      Disjoint (annulus H (S i.1)) (annulus H (S j.1)))
    (W : K → ℝ) :
    (∑ x ∈ traceFinset (bondCoordinates (F := ι) (baseSupportOn H S J)) K hBK,
      W x) = ∑ i : J, ∑ x ∈ traceFinset
        (bondCoordinates (F := ι) (annulus H (S i.1))) K
        ((bondCoordinates_mono (annulus_subset_baseSupportOn H i.2)).trans hBK), W x := by
  classical
  let hsub : ∀ i : J, bondCoordinates (F := ι) (annulus H (S i.1)) ⊆ K :=
    fun i => (bondCoordinates_mono (annulus_subset_baseSupportOn H i.2)).trans hBK
  let Ri : J → Finset K := fun i =>
    traceFinset (bondCoordinates (F := ι) (annulus H (S i.1))) K (hsub i)
  have hEq : traceFinset (bondCoordinates (F := ι) (baseSupportOn H S J)) K hBK =
      Finset.univ.biUnion Ri := by
    ext x
    constructor
    · intro hx
      obtain ⟨f, hf, hfx⟩ := Finset.mem_map.mp ((mem_traceFinset (hRK := hBK) x).1 hx)
      obtain ⟨i, hiJ, hi⟩ := (mem_baseSupportOn H).1 hf
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨i, hiJ⟩, Finset.mem_univ _, (mem_traceFinset (hRK := hsub _) x).2 ?_⟩
      exact Finset.mem_map.mpr ⟨f, hi, hfx⟩
    · intro hx
      obtain ⟨i, _hiuniv, hxi⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨f, hf, hfx⟩ :=
        Finset.mem_map.mp ((mem_traceFinset (hRK := hsub i) x).1 hxi)
      apply (mem_traceFinset (hRK := hBK) x).2
      exact Finset.mem_map.mpr ⟨f, (mem_baseSupportOn H).2 ⟨i.1, i.2, hf⟩, hfx⟩
  have hpair : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (Ri i) (Ri j) := by
    intro i _hi j _hj hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨fi, hfi, hfix⟩ := Finset.mem_map.mp
      ((mem_traceFinset (hRK := hsub i) x).1 hxi)
    obtain ⟨fj, hfj, hfjx⟩ := Finset.mem_map.mp
      ((mem_traceFinset (hRK := hsub j) x).1 hxj)
    have hf_eq : fi = fj := Sum.inl_injective (hfix.trans hfjx.symm)
    subst fj
    exact (Finset.disjoint_left.mp (hdisj i j hij)) hfi hfj
  change (∑ x ∈ traceFinset (bondCoordinates (F := ι) (baseSupportOn H S J)) K hBK,
    W x) = ∑ i : J, ∑ x ∈ Ri i, W x
  rw [hEq, Finset.sum_biUnion hpair]

/-- Restriction of localized velocity to a finite trace. -/
noncomputable def localTraceVelocity {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι)
    {K : Finset ((graph H).edgeSet ⊕ ι)} (c : ℝ) : K → ℝ :=
  fun x => localVelocity H S J c x.1

lemma localTraceVelocity_of_mem_base {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    {hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K} {x : K}
    (hx : x ∈ traceFinset (bondCoordinates (F := ι) (baseSupportOn H S J)) K hBK) :
    localTraceVelocity H S J c x = -c := by
  have hxR := (mem_traceFinset (hRK := hBK) x).1 hx
  obtain ⟨f, hf, hfx⟩ := Finset.mem_map.mp hxR
  change localVelocity H S J c x.1 = -c
  rw [← hfx]
  simp only [localVelocity, Function.Embedding.coeFn_mk, Sum.elim_inl, hf,
    ↓reduceIte]

lemma localTraceVelocity_activation {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K) (i : J) :
    localTraceVelocity H S J c (⟨Sum.inr i.1, haK i.1 i.2⟩ : K) = 1 := by
  simp [localTraceVelocity, localVelocity, i.2]

/-- Canonical embedding of the finite incident activation subtype. -/
noncomputable def localTraceActivationEmbedding {E : Type u} {ι : Type v}
    {J : Finset ι} {K : Finset (E ⊕ ι)}
    (haK : ∀ i ∈ J, (Sum.inr i : E ⊕ ι) ∈ K) : J ↪ K where
  toFun i := ⟨Sum.inr i.1, haK i.1 i.2⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact Sum.inr_injective (congrArg Subtype.val hij)

@[simp] lemma localTraceActivationEmbedding_apply {E : Type u} {ι : Type v}
    {J : Finset ι} {K : Finset (E ⊕ ι)}
    (haK : ∀ i ∈ J, (Sum.inr i : E ⊕ ι) ∈ K) (i : J) :
    localTraceActivationEmbedding haK i = ⟨Sum.inr i.1, haK i.1 i.2⟩ := rfl

/-- The localized derivative support splits into moved annuli and incident
activations.  Every other global coordinate has zero velocity on the trace. -/
lemma sum_localTraceVelocity_mul {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (c : ℝ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K)
    (haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (a : J ↪ K) (ha : ∀ i, a i = ⟨Sum.inr i.1, haK i.1 i.2⟩) (W : K → ℝ) :
    (∑ x, localTraceVelocity H S J c x * W x) =
      (-c) * (∑ x ∈ traceFinset
        (bondCoordinates (F := ι) (baseSupportOn H S J)) K hBK, W x) +
        ∑ i : J, W (a i) := by
  classical
  let B := traceFinset (bondCoordinates (F := ι) (baseSupportOn H S J)) K hBK
  let A := Finset.univ.map a
  have hdisj : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    obtain ⟨i, _hi, hix⟩ := Finset.mem_map.mp hxA
    have hx := (mem_traceFinset (hRK := hBK) x).1 hxB
    rw [← hix, ha i] at hx
    simp [bondCoordinates] at hx
  have hzero {x : K} (hxB : x ∉ B) (hxA : x ∉ A) :
      localTraceVelocity H S J c x = 0 := by
    cases hx : x.1 with
    | inl f =>
        have hf : f ∉ baseSupportOn H S J := by
          intro hf
          apply hxB
          apply (mem_traceFinset (hRK := hBK) x).2
          rw [hx]
          simp [bondCoordinates, hf]
        change localVelocity H S J c x.1 = 0
        rw [hx]
        simp only [localVelocity, Sum.elim_inl, hf, ↓reduceIte]
    | inr i =>
        by_cases hi : i ∈ J
        · exfalso
          apply hxA
          apply Finset.mem_map.mpr
          refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
          rw [ha]
          exact Subtype.ext hx.symm
        · change localVelocity H S J c x.1 = 0
          rw [hx]
          simp only [localVelocity, Sum.elim_inr, hi, ↓reduceIte]
  calc
    (∑ x, localTraceVelocity H S J c x * W x) =
        ∑ x ∈ B ∪ A, localTraceVelocity H S J c x * W x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _hxuniv hx
      have hxB : x ∉ B := fun h => hx (Finset.mem_union_left _ h)
      have hxA : x ∉ A := fun h => hx (Finset.mem_union_right _ h)
      rw [hzero hxB hxA, zero_mul]
    _ = (∑ x ∈ B, localTraceVelocity H S J c x * W x) +
        ∑ x ∈ A, localTraceVelocity H S J c x * W x := by
      rw [Finset.sum_union hdisj]
    _ = (∑ x ∈ B, (-c) * W x) + ∑ x ∈ A, W x := by
      congr 1
      · apply Finset.sum_congr rfl
        intro x hx
        rw [localTraceVelocity_of_mem_base H S J c hx]
      · apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
        rw [ha i, localTraceVelocity_activation H S J c haK i, one_mul]
    _ = (-c) * (∑ x ∈ B, W x) + ∑ i : J, W (a i) := by
      rw [Finset.mul_sum]
      simp [A]

lemma localLine_mem_box {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) {p s c t a b : ℝ}
    (hp : p ∈ Icc a b) (hmove : p - c * t ∈ Icc a b)
    (hs0 : s ∈ Icc a b) (hs : s + t ∈ Icc a b) (x : (graph H).edgeSet ⊕ ι) :
    localLine H S J p s c t x ∈ Icc a b := by
  cases x with
  | inl e =>
      by_cases he : e ∈ baseSupportOn H S J
      · simpa only [localLine, Sum.elim_inl, he, ↓reduceIte] using hmove
      · simpa only [localLine, Sum.elim_inl, he, ↓reduceIte] using hp
  | inr i =>
      by_cases hi : i ∈ J
      · simpa only [localLine, Sum.elim_inr, hi, ↓reduceIte] using hs
      · simpa only [localLine, Sum.elim_inr, hi, ↓reduceIte] using hs0

/-- Common normalized slope bound for the finite incident derivative. -/
lemma localTracePivotSlope_nonneg_of_box {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (J : Finset ι)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i ∈ J, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K)
    (haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b t : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hmove : p - independentComparisonSpeed a b R * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) :
    let c := independentComparisonSpeed a b R
    0 ≤ (-c) * (∑ i : J, ∑ x ∈ traceFinset
        (bondCoordinates (F := ι) (annulus H (S i.1))) K
          ((bondCoordinates_mono (annulus_subset_baseSupportOn H i.2)).trans hBK),
        eventWeight (fun y : K => localLine H S J p s c t y.1)
          {ξ | Pivotal (traceEvent K
            (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}) +
      ∑ i : J, eventWeight (fun y : K => localLine H S J p s c t y.1)
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n))
            ⟨Sum.inr i.1, haK i.1 i.2⟩ ξ} := by
  classical
  dsimp only
  let c := independentComparisonSpeed a b R
  let r : K → ℝ := fun y => localLine H S J p s c t y.1
  let hsub : ∀ i : J, bondCoordinates (F := ι) (annulus H (S i.1)) ⊆ K :=
    fun i => (bondCoordinates_mono (annulus_subset_baseSupportOn H i.2)).trans hBK
  let Dp : J → ℝ := fun i => ∑ x ∈ traceFinset
    (bondCoordinates (F := ι) (annulus H (S i.1))) K (hsub i),
    eventWeight r {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}
  let Pa : J → ℝ := fun i => eventWeight r {ξ | Pivotal (traceEvent K
    (deviceArmEvent (graph H) (independentSupport H S) o n))
      ⟨Sum.inr i.1, haK i.1 i.2⟩ ξ}
  let den : ℝ := ((2 ^ R : ℕ) : ℝ) * (R : ℝ)
  have hrbox : ∀ x, r x ∈ Icc a b := by
    intro x
    exact localLine_mem_box H S J hp hmove hs0 hs x.1
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
  have hsum (i : J) : (sleeveMinorant a b) ^ R * Dp i ≤ den * Pa i := by
    have h := globalTrace_sum_edgePivotal_event_mul_le H S i.1 n (hsub i)
      (haK i.1 i.2) ν (sleeveMinorant a b) hminor.le hν (o := o)
    simp_rw [hevent] at h
    change (sleeveMinorant a b) ^ (S i.1).card * Dp i ≤
      (((2 ^ (S i.1).card : ℕ) : ℝ) * ((S i.1).card : ℝ)) * Pa i at h
    rw [hcard i.1 i.2] at h
    exact h
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hden : 0 < den := by dsimp [den]; positivity
  have hden0 : den ≠ 0 := ne_of_gt hden
  have hcδ : c * den = (sleeveMinorant a b) ^ R := by
    change ((sleeveMinorant a b) ^ R / den) * den = (sleeveMinorant a b) ^ R
    exact div_mul_cancel₀ _ hden0
  have hmul (i : J) : c * Dp i ≤ Pa i := by
    refine le_of_mul_le_mul_right (a := den) ?_ hden
    calc
      (c * Dp i) * den = (c * den) * Dp i := by ring
      _ = (sleeveMinorant a b) ^ R * Dp i := by rw [hcδ]
      _ ≤ den * Pa i := hsum i
      _ = Pa i * den := by ring
  have htotal : c * (∑ i : J, Dp i) ≤ ∑ i : J, Pa i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _hi => hmul i
  change 0 ≤ (-c) * (∑ i : J, Dp i) + ∑ i : J, Pa i
  linarith

/-- Monotonicity of the finite incident trace polynomial along the localized
line.  All constants are exactly those of the finite-family theorem. -/
theorem monotoneOn_localTraceEventWeight {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (J : Finset ι)
    (hdisj : ∀ (i j : J), i ≠ j →
      Disjoint (annulus H (S i.1)) (annulus H (S j.1)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i ∈ J, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K)
    (haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn (fun t => eventWeight (fun x : K => localLine H S J p s
      (independentComparisonSpeed a b R) t x.1)
      (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)))
      (Icc (0 : ℝ) T) := by
  classical
  let c := independentComparisonSpeed a b R
  let hsub : ∀ i : J, bondCoordinates (F := ι) (annulus H (S i.1)) ⊆ K :=
    fun i => (bondCoordinates_mono (annulus_subset_baseSupportOn H i.2)).trans hBK
  let Dp : ℝ → ℝ := fun t => ∑ i : J, ∑ x ∈ traceFinset
    (bondCoordinates (F := ι) (annulus H (S i.1))) K (hsub i),
    eventWeight (fun y : K => localLine H S J p s c t y.1)
      {ξ | Pivotal (traceEvent K
        (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}
  let Pa : ℝ → ℝ := fun t => ∑ i : J,
    eventWeight (fun y : K => localLine H S J p s c t y.1)
      {ξ | Pivotal (traceEvent K
        (deviceArmEvent (graph H) (independentSupport H S) o n))
          ⟨Sum.inr i.1, haK i.1 i.2⟩ ξ}
  let aemb := localTraceActivationEmbedding haK
  have hc : 0 ≤ c := independentComparisonSpeed_nonneg R ha.le hb.le
  have hupper : IsUpperSet (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
    isUpperSet_traceEvent K (isUpperSet_deviceArmEvent (graph H)
      (independentSupport H S) o n)
  have hline (t : ℝ) : (fun x : K => localLine H S J p s c t x.1) =
      affineRates (fun x : K => localLine H S J p s c 0 x.1)
        (localTraceVelocity H S J c) t := by
    funext x
    exact congrFun (localLine_eq_affine H S J p s c t) x.1
  have hderiv (t : ℝ) : HasDerivAt
      (fun y => eventWeight (fun x : K => localLine H S J p s c y x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)))
      ((-c) * Dp t + Pa t) t := by
    have h := hasDerivAt_eventWeight_affine_pivotal
      (fun x : K => localLine H S J p s c 0 x.1) (localTraceVelocity H S J c) hupper t
    simp_rw [← hline] at h
    have hvel := sum_localTraceVelocity_mul H S J c hBK haK aemb
      (fun _ => rfl) (fun x => eventWeight
        (fun y : K => localLine H S J p s c t y.1)
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ})
    have hbase := sum_localBaseTrace_eq_sum_devices H S J hBK hdisj
      (fun x => eventWeight (fun y : K => localLine H S J p s c t y.1)
        {ξ | Pivotal (traceEvent K
          (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ})
    rw [hvel, hbase] at h
    simpa only [Dp, Pa, aemb, localTraceActivationEmbedding_apply] using h
  change MonotoneOn (fun t => eventWeight (fun x : K => localLine H S J p s c t x.1)
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
    exact localTracePivotSlope_nonneg_of_box H S J R hR hcard o n hBK haK
      p s a b t ha hb hp0 hs0 hbox.1 hbox.2

/-- Endpoint comparison of the actual global-event finite trace. -/
theorem localTraceEventWeight_le {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (J : Finset ι)
    (hdisj : ∀ (i j : J), i ≠ j →
      Disjoint (annulus H (S i.1)) (annulus H (S j.1)))
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i ∈ J, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K)
    (haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (fun x : K => localLine H S J p s
        (independentComparisonSpeed a b R) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) ≤
      eventWeight (fun x : K => localLine H S J p s
        (independentComparisonSpeed a b R) T x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) := by
  have hmono := monotoneOn_localTraceEventWeight H S J hdisj R hR hcard o n hBK haK
    p s a b T ha hb hp0 hs0 hpT hsT
  exact hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

@[simp] lemma mem_sleeveSupportOn {V : Type u} (H : SimpleGraph V) {ι : Type v}
    {S : ι → Finset H.edgeSet} {J : Finset ι} {f : (graph H).edgeSet} :
    f ∈ sleeveSupportOn H S J ↔ ∃ i ∈ J, f ∈ edges H (S i) := by
  classical simp [sleeveSupportOn]

lemma edge_mem_of_inl_mem_localCoordinates {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) (J : Finset ι) (o : V ⊕ H.edgeSet) (n : ℕ)
    {f : (graph H).edgeSet}
    (hf : (Sum.inl f : (graph H).edgeSet ⊕ ι) ∈ localCoordinates H hG S J o n) :
    f ∈ FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n ∨
      f ∈ baseSupportOn H S J ∨ f ∈ sleeveSupportOn H S J := by
  simpa only [localCoordinates, Finset.mem_union, bondCoordinates, Finset.mem_map,
    Function.Embedding.coeFn_mk, Sum.inl.injEq, exists_eq_right,
    activationCoordinatesOn, Finset.mem_image, reduceCtorEq, false_and, and_false,
    exists_false, or_false, or_assoc] using hf

/-- Global rates equal localized rates on the whole finite incident trace. -/
lemma globalLine_eq_localLine_on_trace {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S) {J : Finset ι}
    (o : V ⊕ H.edgeSet) (n : ℕ)
    (hJ : incidentDevices H S
      (FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n) ⊆ J)
    (p s c t : ℝ) {x : (graph H).edgeSet ⊕ ι}
    (hx : x ∈ localCoordinates H hG S J o n) :
    globalLine H S p s c t x = localLine H S J p s c t x := by
  classical
  cases x with
  | inl f =>
      have hf := edge_mem_of_inl_mem_localCoordinates H hG S J o n hx
      have hiff : (∃ i, f ∈ annulus H (S i)) ↔
          (∃ i ∈ J, f ∈ annulus H (S i)) := by
        constructor
        · rintro ⟨i, hi⟩
          have hiJ : i ∈ J := by
            rcases hf with hmetric | hbase | hsleeve
            · apply hJ
              exact ⟨f, hmetric, (mem_template H).2 (Or.inl hi)⟩
            · obtain ⟨j, hjJ, hj⟩ := (mem_baseSupportOn H).1 hbase
              have hij : i = j := hunique f (mem_template H |>.2 (Or.inl hi))
                (mem_template H |>.2 (Or.inl hj))
              simpa [hij] using hjJ
            · obtain ⟨j, hjJ, hj⟩ := (mem_sleeveSupportOn H).1 hsleeve
              have hij : i = j := hunique f (mem_template H |>.2 (Or.inl hi))
                (mem_template H |>.2 (Or.inr hj))
              simpa [hij] using hjJ
          exact ⟨i, hiJ, hi⟩
        · rintro ⟨i, _hiJ, hi⟩
          exact ⟨i, hi⟩
      simp only [globalLine, localLine, Sum.elim_inl, mem_baseSupportOn H, hiff]
  | inr i =>
      have hi : i ∈ J := by
        simpa only [localCoordinates, Finset.mem_union, bondCoordinates,
          activationCoordinatesOn, Finset.mem_map, Finset.mem_image,
          Function.Embedding.coeFn_mk, Sum.inr.injEq, exists_eq_right,
          reduceCtorEq, false_and, and_false, exists_false, or_false, false_or] using hx
      simp [globalLine, localLine, hi]

/-- Unit-interval parameters on the full infinite comparison line. -/
noncomputable def unitGlobalLine {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, globalLine H S p s c t x ∈ Icc (0 : ℝ) 1) :
    (graph H).edgeSet ⊕ ι → unitInterval := fun x =>
  ⟨globalLine H S p s c t x, (hr x).1, (hr x).2⟩

@[simp] lemma coe_unitGlobalLine {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (p s c t : ℝ)
    (hr : ∀ x, globalLine H S p s c t x ∈ Icc (0 : ℝ) 1)
    (x : (graph H).edgeSet ⊕ ι) :
    (unitGlobalLine H S p s c t hr x : ℝ) = globalLine H S p s c t x := rfl

lemma disjoint_annuli_of_edgeUnique {V : Type u} (H : SimpleGraph V) {ι : Type v}
    (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    {J : Finset ι} (i j : J) (hij : i ≠ j) :
    Disjoint (annulus H (S i.1)) (annulus H (S j.1)) := by
  rw [Finset.disjoint_left]
  intro f hfi hfj
  apply hij
  apply Subtype.ext
  exact hunique f (mem_template H |>.2 (Or.inl hfi))
    (mem_template H |>.2 (Or.inl hfj))

/-- **Infinite-family arm comparison.**  The ambient device index is arbitrary:
the proof uses only the finite set of devices incident to each fixed arm. -/
theorem infiniteProductLaw_deviceArmEvent_globalLine_le {V : Type u}
    (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Icc (0 : ℝ) 1)
    (hrT : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) T x ∈
      Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitGlobalLine H S p s
        (independentComparisonSpeed a b R) 0 hr0)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal ≤
      (infiniteProductLaw (unitGlobalLine H S p s
        (independentComparisonSpeed a b R) T hrT)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal := by
  classical
  let L := FK.InfiniteVolume.NestedMetricGeometry.metricEdges (graphConnected H hG) o n
  let J := incidentFinset H S hunique L
  let K := localCoordinates H hG S J o n
  let c := independentComparisonSpeed a b R
  have hJ : incidentDevices H S L ⊆ J := by
    intro i hi
    exact (mem_incidentFinset H S hunique).2 hi
  have hdep : DependsOn (fun χ => χ ∈ deviceArmEvent (graph H)
      (independentSupport H S) o n) (K : Set ((graph H).edgeSet ⊕ ι)) :=
    dependsOn_deviceArmEvent_local H hG S o n hJ
  have hBK : bondCoordinates (F := ι) (baseSupportOn H S J) ⊆ K :=
    baseSupportOn_subset_localCoordinates H hG S J o n
  have haK : ∀ i ∈ J, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K := by
    intro i hi
    exact activation_mem_localCoordinates H hG S o n hi
  have hdisj : ∀ (i j : J), i ≠ j →
      Disjoint (annulus H (S i.1)) (annulus H (S j.1)) := by
    intro i j hij
    exact disjoint_annuli_of_edgeUnique H S hunique i j hij
  have hline (t : ℝ) {x : (graph H).edgeSet ⊕ ι} (hx : x ∈ K) :
      globalLine H S p s c t x = localLine H S J p s c t x :=
    globalLine_eq_localLine_on_trace H hG S hunique o n hJ p s c t hx
  have hweight (t : ℝ) : eventWeight (fun x : K => globalLine H S p s c t x.1)
      (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) =
      eventWeight (fun x : K => localLine H S J p s c t x.1)
      (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) := by
    congr 2
    funext x
    exact hline t x.2
  calc
    _ = eventWeight (fun x : K => globalLine H S p s c 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      (eventWeight_traceEvent (unitGlobalLine H S p s c 0 hr0) K _ hdep).symm
    _ = eventWeight (fun x : K => localLine H S J p s c 0 x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      hweight 0
    _ ≤ eventWeight (fun x : K => localLine H S J p s c T x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      localTraceEventWeight_le H S J hdisj R hR (fun i hi => hcard i) o n hBK haK
        p s a b T ha hb hT hp0 hs0 hpT hsT
    _ = eventWeight (fun x : K => globalLine H S p s c T x.1)
        (traceEvent K (deviceArmEvent (graph H) (independentSupport H S) o n)) :=
      (hweight T).symm
    _ = _ := eventWeight_traceEvent (unitGlobalLine H S p s c T hrT) K _ hdep

end FK.AGImplant.Sleeve.GlobalInfinite


namespace FK.AGImplant.Sleeve.GlobalInfinite

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology
open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite
open FK.AGImplant.Sleeve.IndexedInfinite

universe u v

/-- On an edge-unique packing, every activated witness for a fixed bypass
spoke is the same device.  Thus an arbitrary (even uncountable) existential
over devices reduces to one activation coordinate whenever the spoke occurs. -/
lemma addsEdge_independentSupport_iff_of_mem {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    {f : (graph H).edgeSet} {i : ι} (hi : f ∈ edges H (S i))
    (χ : JointConfig (graph H).edgeSet ι) :
    AddsEdge (independentSupport H S) χ f ↔ χ (Sum.inr i) = true := by
  constructor
  · rintro ⟨j, hj, hfj⟩
    have hji : j = i := hunique f
      ((mem_template H).2 (Or.inr hfj)) ((mem_template H).2 (Or.inr hi))
    simpa [hji] using hj
  · intro hiact
    exact ⟨i, hiact, hi⟩

/-- The enhanced bond configuration of an arbitrary edge-unique family is
measurable.  No countability or finiteness is imposed on the device index:
at each bond, either no template uses it, or edge uniqueness selects its only
possible activation coordinate. -/
lemma measurable_deviceConfig_independentSupport_of_edgeUnique
    {V : Type u} (H : SimpleGraph V) {ι : Type v} (S : ι → Finset H.edgeSet)
    (hunique : EdgeUnique H S) :
    Measurable (deviceConfig (independentSupport H S)) := by
  classical
  apply measurable_pi_iff.2
  intro f
  by_cases hf : ∃ i, f ∈ edges H (S i)
  · obtain ⟨i, hi⟩ := hf
    have heq : (fun χ : JointConfig (graph H).edgeSet ι =>
        deviceConfig (independentSupport H S) χ f) =
        (fun χ => if χ (Sum.inr i) = true then true else χ (Sum.inl f)) := by
      funext χ
      by_cases ha : χ (Sum.inr i) = true
      · have hadd := (addsEdge_independentSupport_iff_of_mem H S hunique hi χ).2 ha
        simp [deviceConfig, hadd, ha]
      · have hadd : ¬ AddsEdge (independentSupport H S) χ f := by
          intro h
          exact ha ((addsEdge_independentSupport_iff_of_mem H S hunique hi χ).1 h)
        simp [deviceConfig, hadd, ha]
    rw [heq]
    exact Measurable.ite (by measurability) measurable_const (measurable_pi_apply _)
  · have heq : (fun χ : JointConfig (graph H).edgeSet ι =>
        deviceConfig (independentSupport H S) χ f) = (fun χ => χ (Sum.inl f)) := by
      funext χ
      have hadd : ¬ AddsEdge (independentSupport H S) χ f := by
        rintro ⟨i, _hiact, hi⟩
        exact hf ⟨i, hi⟩
      simp [deviceConfig, hadd]
    rw [heq]
    exact measurable_pi_apply _

/-- The actual infinite-cluster event after applying an arbitrary edge-unique
family of independently indexed devices. -/
def globalPercolationEvent {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) :
    Set (JointConfig (graph H).edgeSet ι) :=
  deviceConfig (independentSupport H S) ⁻¹'
    {ω | {x | OpenConnected (graph H) ω Set.univ o x}.Infinite}

/-- Enhanced percolation is exactly the decreasing intersection of finite
arms, for an arbitrary device index and with no finite-family assumption. -/
lemma globalPercolationEvent_eq_iInter {V : Type u} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type v}
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) :
    globalPercolationEvent H S o =
      ⋂ n, deviceArmEvent (graph H) (independentSupport H S) o n := by
  rw [globalPercolationEvent,
    setOf_infinite_eq_iInter_armEvent (graphConnected H hG) o]
  ext χ
  simp only [Set.mem_preimage, Set.mem_iInter, deviceArmEvent, deviceEvent]

/-- Continuity from above for the actual infinite-product arm probabilities.
The measurable majorant is the probability measure itself; no derivatives or
infinite sums are passed through the limit. -/
theorem tendsto_infiniteProductLaw_deviceArmEvent_global
    {V : Type u} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) {ι : Type v} (S : ι → Finset H.edgeSet)
    (hunique : EdgeUnique H S) (o : V ⊕ H.edgeSet)
    (r : (graph H).edgeSet ⊕ ι → unitInterval) :
    Tendsto (fun n =>
      (infiniteProductLaw r (deviceArmEvent (graph H)
        (independentSupport H S) o n)).toReal) atTop
      (𝓝 ((infiniteProductLaw r (globalPercolationEvent H S o)).toReal)) := by
  have hlim : Tendsto (fun n =>
      infiniteProductLaw r (deviceArmEvent (graph H) (independentSupport H S) o n))
      atTop (𝓝 (infiniteProductLaw r (globalPercolationEvent H S o))) := by
    rw [globalPercolationEvent_eq_iInter H hG S o]
    exact tendsto_measure_iInter_atTop
      (fun n => ((measurable_deviceConfig_independentSupport_of_edgeUnique H S hunique)
        (measurableSet_armEvent o n)).nullMeasurableSet)
      (by
        intro m n hmn
        exact Set.preimage_mono (armEvent_antitone o hmn))
      ⟨0, measure_ne_top _ _⟩
  have hreal := (ENNReal.tendsto_toReal
    (a := infiniteProductLaw r (globalPercolationEvent H S o))
    (measure_ne_top _ _)).comp hlim
  simpa only [Function.comp_def] using hreal

/-- **Infinite-cluster comparison for an arbitrary edge-unique family.**
Every arm inequality is evaluated on its finite incident trace, so the omitted
infinite device tail makes exactly zero contribution to that arm polynomial.
Only probabilities, not derivatives, are then passed to the decreasing arm
limit.  This is a scoped comparison, not a reference-law or strict-shift claim. -/
theorem infiniteProductLaw_globalPercolation_globalLine_le
    {V : Type u} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) {ι : Type v} (S : ι → Finset H.edgeSet)
    (hunique : EdgeUnique H S) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) 0 x ∈
      Icc (0 : ℝ) 1)
    (hrT : ∀ x, globalLine H S p s (independentComparisonSpeed a b R) T x ∈
      Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitGlobalLine H S p s
        (independentComparisonSpeed a b R) 0 hr0)
        (globalPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw (unitGlobalLine H S p s
        (independentComparisonSpeed a b R) T hrT)
        (globalPercolationEvent H S o)).toReal := by
  apply le_of_tendsto_of_tendsto
    (tendsto_infiniteProductLaw_deviceArmEvent_global H hG S hunique o
      (unitGlobalLine H S p s (independentComparisonSpeed a b R) 0 hr0))
    (tendsto_infiniteProductLaw_deviceArmEvent_global H hG S hunique o
      (unitGlobalLine H S p s (independentComparisonSpeed a b R) T hrT))
  exact Filter.Eventually.of_forall fun n =>
    infiniteProductLaw_deviceArmEvent_globalLine_le H hG S hunique R hR hcard o n
      p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT

end FK.AGImplant.Sleeve.GlobalInfinite

#print axioms FK.AGImplant.Sleeve.GlobalInfinite.infiniteProductLaw_deviceArmEvent_globalLine_le
#print axioms FK.AGImplant.Sleeve.GlobalInfinite.measurable_deviceConfig_independentSupport_of_edgeUnique
#print axioms FK.AGImplant.Sleeve.GlobalInfinite.globalPercolationEvent_eq_iInter
#print axioms FK.AGImplant.Sleeve.GlobalInfinite.tendsto_infiniteProductLaw_deviceArmEvent_global
#print axioms FK.AGImplant.Sleeve.GlobalInfinite.infiniteProductLaw_globalPercolation_globalLine_le


namespace FK.AGImplant.Sleeve.GlobalInfinite

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology
open FK.EssentialEnhancement FK.AGPeeling
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite

universe u

/-- The whole (not necessarily finite) selected part of the repository's
uniform translated-template packing. -/
noncomputable def packedSleevesSet {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) (M : Set (H ≃g H)) : M → Finset H.edgeSet :=
  fun φ => S.map φ.1.mapEdgeSet.toEmbedding

/-- Pairwise-disjoint whole translated templates imply the edge-uniqueness
input of the arbitrary-index comparison on the actual packing. -/
lemma edgeUnique_packedSleevesSet {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet))) :
    EdgeUnique H (packedSleevesSet H S M) := by
  classical
  apply edgeUnique_of_pairwiseDisjoint
  intro φ ψ hne
  have hne' : φ.1 ≠ ψ.1 := fun h => hne (Subtype.ext h)
  simpa [packedSleevesSet] using
    (pairwiseDisjoint_packedTemplates H S hM φ.2 ψ.2 hne')

@[simp] lemma card_packedSleevesSet {V : Type u} (H : SimpleGraph V)
    (S : Finset H.edgeSet) {M : Set (H ≃g H)} (φ : M) :
    (packedSleevesSet H S M φ).card = S.card := by
  exact card_map_mapEdgeSet H φ.1 S

/-- **Percolation comparison on the actual full uniform packing.**  The selected
automorphism set need not be finite or countable.  Pairwise-disjoint complete
templates give both the measurable arbitrary-index device configuration and
the disjoint finite incident traces used at every arm radius. -/
theorem infiniteProductLaw_packedSetPercolation_globalLine_le
    {V : Type u} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) (S : Finset H.edgeSet) (hS : S.Nonempty)
    {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (o : V ⊕ H.edgeSet) (p s a b T : ℝ)
    (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b S.card * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, globalLine H (packedSleevesSet H S M) p s
      (independentComparisonSpeed a b S.card) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, globalLine H (packedSleevesSet H S M) p s
      (independentComparisonSpeed a b S.card) T x ∈ Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitGlobalLine H (packedSleevesSet H S M) p s
        (independentComparisonSpeed a b S.card) 0 hr0)
        (globalPercolationEvent H (packedSleevesSet H S M) o)).toReal ≤
      (infiniteProductLaw (unitGlobalLine H (packedSleevesSet H S M) p s
        (independentComparisonSpeed a b S.card) T hrT)
        (globalPercolationEvent H (packedSleevesSet H S M) o)).toReal := by
  exact infiniteProductLaw_globalPercolation_globalLine_le H hG
    (packedSleevesSet H S M) (edgeUnique_packedSleevesSet H S hM)
    S.card (Finset.card_pos.mpr hS) (fun φ => card_packedSleevesSet H S φ) o
      p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT

end FK.AGImplant.Sleeve.GlobalInfinite

#print axioms FK.AGImplant.Sleeve.GlobalInfinite.edgeUnique_packedSleevesSet
#print axioms FK.AGImplant.Sleeve.GlobalInfinite.infiniteProductLaw_packedSetPercolation_globalLine_le


namespace FK.AGImplant.Sleeve.GlobalInfinite

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology
open FK.EssentialEnhancement FK.AGPeeling

universe u v

/-- **Explicit finite domination of the omitted-device tail.**  A finite edge
trace meets at most `L.card` devices of an edge-unique family.  Equivalently,
after the finite incident set of cardinal at most `L.card`, the trace has no
remaining device dependence at all. -/
theorem card_incidentFinset_le {V : Type u} (H : SimpleGraph V)
    {ι : Type v} (S : ι → Finset H.edgeSet) (hunique : EdgeUnique H S)
    (L : Finset (graph H).edgeSet) :
    (incidentFinset H S hunique L).card ≤ L.card := by
  classical
  let J := incidentFinset H S hunique L
  let pick : ∀ i, i ∈ J → (graph H).edgeSet := fun i hi =>
    Classical.choose ((mem_incidentFinset H S hunique (L := L)).1 hi :
      ∃ f ∈ L, f ∈ template H (S i))
  have hpickL : ∀ i (hi : i ∈ J), pick i hi ∈ L := by
    intro i hi
    exact (Classical.choose_spec ((mem_incidentFinset H S hunique (L := L)).1 hi :
      ∃ f ∈ L, f ∈ template H (S i))).1
  have hpickT : ∀ i (hi : i ∈ J), pick i hi ∈ template H (S i) := by
    intro i hi
    exact (Classical.choose_spec ((mem_incidentFinset H S hunique (L := L)).1 hi :
      ∃ f ∈ L, f ∈ template H (S i))).2
  let e : J ↪ L :=
    { toFun := fun i => ⟨pick i.1 i.2, hpickL i.1 i.2⟩
      inj' := by
        intro i j hij
        apply Subtype.ext
        apply hunique (pick i.1 i.2) (hpickT i.1 i.2)
        have heq : pick i.1 i.2 = pick j.1 j.2 := congrArg Subtype.val hij
        rw [heq]
        exact hpickT j.1 j.2 }
  simpa [J] using Fintype.card_le_of_embedding e

end FK.AGImplant.Sleeve.GlobalInfinite

#print axioms FK.AGImplant.Sleeve.GlobalInfinite.card_incidentFinset_le
