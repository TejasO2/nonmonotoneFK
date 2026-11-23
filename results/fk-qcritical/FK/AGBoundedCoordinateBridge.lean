import FK.AGMultiDeviceIndependence
import FK.AGSleeveInfinite

/-!
# Bounded-coordinate differential bridge on infinite sleeved graphs

For a finite family of independently activated finite sleeves on an arbitrary
connected locally finite graph, each fixed arm has a finite coordinate trace.
We transport the exact annular pivot estimate to that trace and sum over the
family.  The base-pivot sum over the *union* of moved coordinates is bounded
by the indexed double sum even when annuli overlap.  Consequently the
normalized comparison speed needs no disjointness or overlap correction.

The endpoint arm inequality is an inequality for the actual inhomogeneous
infinite product.  Continuity from above then gives the corresponding
infinite-cluster comparison.  No derivative is exchanged with an infinite
volume limit and no infinite indexed family is asserted.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.AGImplant.Sleeve.BoundedCoordinate

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite

universe u v w

/-- The finite union of the base annuli moved by a finite indexed family. -/
noncomputable def baseSupport {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet) :
    Finset (graph H).edgeSet := by
  classical
  exact Finset.univ.biUnion fun i => annulus H (S i)

@[simp] lemma mem_baseSupport {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] {S : ι → Finset H.edgeSet}
    {f : (graph H).edgeSet} :
    f ∈ baseSupport H S ↔ ∃ i, f ∈ annulus H (S i) := by
  classical
  simp [baseSupport]

/-- The finite union of all activation edge supports. -/
noncomputable def activationSupport {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet) :
    Finset (graph H).edgeSet := by
  classical
  exact Finset.univ.biUnion fun i => edges H (S i)

@[simp] lemma mem_activationSupport {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] {S : ι → Finset H.edgeSet}
    {f : (graph H).edgeSet} :
    f ∈ activationSupport H S ↔ ∃ i, f ∈ edges H (S i) := by
  classical
  simp [activationSupport]

/-- Base probabilities decrease on the union of annuli and every indexed
activation increases independently.  Unmentioned base bonds stay fixed. -/
noncomputable def independentLine {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (p s c t : ℝ) : (graph H).edgeSet ⊕ ι → ℝ :=
  Sum.elim (fun e => if e ∈ baseSupport H S then p - c * t else p)
    (fun _ => s + t)

lemma independentLine_mem_box {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    {p s c t a b : ℝ} (hp : p ∈ Icc a b)
    (hmove : p - c * t ∈ Icc a b) (hs : s + t ∈ Icc a b)
    (x : (graph H).edgeSet ⊕ ι) : independentLine H S p s c t x ∈ Icc a b := by
  cases x with
  | inl e =>
      by_cases he : e ∈ baseSupport H S
      · simpa only [independentLine, Sum.elim_inl, he, ↓reduceIte] using hmove
      · simpa only [independentLine, Sum.elim_inl, he, ↓reduceIte] using hp
  | inr i => exact hs

lemma independentLine_parameters_mem_box {p s c a b T t : ℝ}
    (hc : 0 ≤ c) (ht : t ∈ Icc (0 : ℝ) T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - c * T ∈ Icc a b) (hsT : s + T ∈ Icc a b) :
    p - c * t ∈ Icc a b ∧ s + t ∈ Icc a b :=
  FK.AGGadget.diagonal_parameters_mem_Icc hc ht hp0 hs0 hpT hsT

/-- A generic indexed velocity, shared by the global line and every trace. -/
noncomputable def indexedVelocity {E : Type w} {ι : Type u}
    (R : Finset E) (c : ℝ) : E ⊕ ι → ℝ
  | Sum.inl e => if e ∈ R then -c else 0
  | Sum.inr _ => 1

/-- Velocity of the indexed line on an arbitrary, possibly infinite, graph. -/
noncomputable def independentVelocity {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet) (c : ℝ) :
    (graph H).edgeSet ⊕ ι → ℝ :=
  indexedVelocity (baseSupport H S) c

lemma independentLine_eq_affine {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (p s c t : ℝ) :
    independentLine H S p s c t =
      affineRates (independentLine H S p s c 0)
        (independentVelocity H S c) t := by
  funext x
  cases x with
  | inl e =>
      simp only [independentLine, independentVelocity, affineRates, indexedVelocity,
        Sum.elim_inl]
      by_cases he : e ∈ baseSupport H S
      · simp only [he, ↓reduceIte]
        ring
      · simp only [he, ↓reduceIte]
        ring
  | inr i => simp [independentLine, independentVelocity, affineRates, indexedVelocity]

/-- A finite trace sufficient for one arm and the whole finite indexed
family: all metric bonds, all moved annuli and every activation coordinate. -/
noncomputable def coordinates {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) :
    Finset ((graph H).edgeSet ⊕ ι) :=
  ((FK.InfiniteVolume.NestedMetricGeometry.metricEdges
      (graphConnected H hG) o n).map ⟨Sum.inl, Sum.inl_injective⟩) ∪
    (bondCoordinates (F := ι) (baseSupport H S)) ∪
    (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)

lemma activation_mem_coordinates {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) (i : ι) :
    (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ coordinates H hG S o n := by
  simp [coordinates]

lemma metric_mem_coordinates {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ)
    {f : (graph H).edgeSet} (hf : f.1 ∈ innerEdges (graph H) o n) :
    (Sum.inl f : (graph H).edgeSet ⊕ ι) ∈ coordinates H hG S o n := by
  have hf' : f ∈ FK.InfiniteVolume.NestedMetricGeometry.metricEdges
      (graphConnected H hG) o n :=
    (FK.InfiniteVolume.NestedMetricGeometry.mem_metricEdges
      (graphConnected H hG) o n f).2 hf
  simp [coordinates, hf']

lemma baseSupport_subset_coordinates {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) :
    bondCoordinates (F := ι) (baseSupport H S) ⊆ coordinates H hG S o n := by
  intro x hx
  simp [coordinates, hx]

lemma annulus_subset_coordinates {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) (i : ι) :
    bondCoordinates (F := ι) (annulus H (S i)) ⊆ coordinates H hG S o n := by
  intro x hx
  apply baseSupport_subset_coordinates H hG S o n
  rcases Finset.mem_map.mp hx with ⟨f, hf, rfl⟩
  exact Finset.mem_map.mpr ⟨f, (mem_baseSupport H).2 ⟨i, hf⟩, rfl⟩

/-- The enhanced arm depends only on its explicit finite coordinate trace. -/
lemma dependsOn_deviceArmEvent {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) (n : ℕ) :
    DependsOn (fun χ => χ ∈ deviceArmEvent (graph H)
      (independentSupport H S) o n) (coordinates H hG S o n :
        Set ((graph H).edgeSet ⊕ ι)) := by
  classical
  intro χ ξ hagree
  apply dependsOn_armEvent (G := graph H) (graphConnected H hG) o n
  intro f hf
  have hbond : χ (Sum.inl f) = ξ (Sum.inl f) :=
    hagree _ (metric_mem_coordinates H hG S o n hf)
  have hact (i : ι) : χ (Sum.inr i) = ξ (Sum.inr i) :=
    hagree _ (activation_mem_coordinates H hG S o n i)
  have hadd : AddsEdge (independentSupport H S) χ f ↔
      AddsEdge (independentSupport H S) ξ f := by
    constructor
    · rintro ⟨i, hi, hfS⟩
      exact ⟨i, by rwa [← hact i], hfS⟩
    · rintro ⟨i, hi, hfS⟩
      exact ⟨i, by rwa [hact i], hfS⟩
  change (if AddsEdge (independentSupport H S) χ f then true else χ (Sum.inl f)) =
    (if AddsEdge (independentSupport H S) ξ f then true else ξ (Sum.inl f))
  simp only [hadd, hbond]

/-- Closed-extension traces commute with closing any selected annulus. -/
lemma traceExtend_traceClose_annulus {E : Type w} {ι : Type u}
    (R : Finset E) {K : Finset (E ⊕ ι)}
    (hRK : bondCoordinates (F := ι) R ⊆ K) (ξ : K → Bool) :
    traceExtend K (traceClose (bondCoordinates (F := ι) R) ξ) =
      annularClose R (traceExtend K ξ) := by
  classical
  rw [traceExtend_traceClose hRK]
  ext y
  cases y with
  | inl f =>
      by_cases hf : f ∈ R
      · have hb : (Sum.inl f : E ⊕ ι) ∈ bondCoordinates (F := ι) R := by
          simp [bondCoordinates, hf]
        simp [hb, annularClose, hf]
      · have hb : (Sum.inl f : E ⊕ ι) ∉ bondCoordinates (F := ι) R := by
          simp [bondCoordinates, hf]
        simp [hb, annularClose, hf]
  | inr i =>
      have hb : (Sum.inr i : E ⊕ ι) ∉ bondCoordinates (F := ι) R := by
        simp [bondCoordinates]
      simp [hb, annularClose]

/-- One selected base pivot in one member of an indexed family is dominated
by that member's activation pivot on any sufficiently large finite trace. -/
lemma trace_pivot_event_mul_le {V : Type v} (H : SimpleGraph V)
    {ι : Type u} (S : ι → Finset H.edgeSet) (i : ι)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (annulus H (S i)) ⊆ K)
    (haK : (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b)
    {x : K} (hx : x ∈ traceFinset
      (bondCoordinates (F := ι) (annulus H (S i))) K hRK) :
    δ ^ (S i).card * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) x ξ} ≤
      ((2 ^ (S i).card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) ⟨Sum.inr i, haK⟩ ξ} := by
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
    have hpFull : EdgePivotal (deviceArmEvent (graph H)
        (independentSupport H S) o n) (baseEdge H e) (traceExtend K ξ) := by
      have hp' := (pivotal_traceEvent K _ x ξ).1 hp
      change Pivotal _ (Sum.inl (baseEdge H e)) _
      rw [← hxf]
      exact hp'
    have haFull := activationPivotal_deviceArmEvent_independent H S i he n hpFull
    apply (pivotal_traceEvent K _ a _).2
    change Pivotal _ (Sum.inr i) _
    rw [traceExtend_traceClose_annulus (annulus H (S i)) hRK]
    exact haFull
  have h := local_pi_event_mul_le ν
    (traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K hRK)
    δ hδ hν (traceClose (bondCoordinates (F := ι) (annulus H (S i))))
    (traceClose_isLocalModification hRK)
    {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n)) x ξ}
    {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n)) a ξ}
    (by intro ξ hξ; exact hmap ξ hξ)
  simpa only [card_traceFinset, card_bondCoordinates, card_annulus, a] using h

/-- Exact per-device summed pivot comparison on a finite trace. -/
lemma trace_sum_pivot_event_mul_le {V : Type v} (H : SimpleGraph V)
    {ι : Type u} (S : ι → Finset H.edgeSet) (i : ι)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (annulus H (S i)) ⊆ K)
    (haK : (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (ν : K → OpenPath.FinProb Bool) (δ : ℝ) (hδ : 0 ≤ δ)
    (hν : ∀ x b, δ ≤ (ν x).mass b) :
    δ ^ (S i).card * (∑ x ∈ traceFinset
      (bondCoordinates (F := ι) (annulus H (S i))) K hRK,
      (OpenPath.FinProb.pi ν).event
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) x ξ}) ≤
      ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
        (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
            (independentSupport H S) o n)) ⟨Sum.inr i, haK⟩ ξ} := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K hRK,
        δ ^ (S i).card * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
            (independentSupport H S) o n)) x ξ}) ≤
      ∑ _x ∈ traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K hRK,
        ((2 ^ (S i).card : ℕ) : ℝ) * (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
            (independentSupport H S) o n)) ⟨Sum.inr i, haK⟩ ξ} := by
      apply Finset.sum_le_sum
      intro x hx
      exact trace_pivot_event_mul_le H S i o n hRK haK ν δ hδ hν hx
    _ = ((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ) *
        (OpenPath.FinProb.pi ν).event
          {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
            (independentSupport H S) o n)) ⟨Sum.inr i, haK⟩ ξ} := by
      simp only [Finset.sum_const, card_traceFinset, card_bondCoordinates,
        card_annulus, nsmul_eq_mul]
      ring

end FK.AGImplant.Sleeve.BoundedCoordinate

namespace FK.AGImplant.Sleeve.BoundedCoordinate

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite

/-- Nonnegative union sums are bounded by the corresponding indexed double
sums, with no disjointness assumption. -/
lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (B : α → Finset β) (W : β → ℝ) (hW : ∀ b, 0 ≤ W b) :
    (∑ b ∈ s.biUnion B, W b) ≤ ∑ i ∈ s, ∑ b ∈ B i, W b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      have hInter : 0 ≤ ∑ b ∈ B i ∩ s.biUnion B, W b := by
        exact Finset.sum_nonneg fun b _ => hW b
      have hUnion : (∑ b ∈ B i ∪ s.biUnion B, W b) ≤
          (∑ b ∈ B i, W b) + ∑ b ∈ s.biUnion B, W b := by
        have h := Finset.sum_union_inter (s₁ := B i) (s₂ := s.biUnion B) (f := W)
        linarith
      exact hUnion.trans (add_le_add_right ih _)

/-- Restriction of the global indexed velocity to a finite trace. -/
noncomputable def traceVelocity {E : Type w} {ι : Type u}
    (R : Finset E) (c : ℝ) {K : Finset (E ⊕ ι)} : K → ℝ := fun x =>
  indexedVelocity R c x.1

lemma traceVelocity_of_mem {E : Type w} {ι : Type u}
    {R : Finset E} {K : Finset (E ⊕ ι)}
    (hRK : bondCoordinates (F := ι) R ⊆ K) (c : ℝ)
    {x : K} (hx : x ∈ traceFinset (bondCoordinates (F := ι) R) K hRK) :
    traceVelocity R c x = -c := by
  classical
  have hxR := (mem_traceFinset (hRK := hRK) x).1 hx
  rcases Finset.mem_map.mp hxR with ⟨f, hf, hfx⟩
  change (match x.1 with
    | Sum.inl e => if e ∈ R then -c else 0
    | Sum.inr _ => 1) = -c
  rw [← hfx]
  simp [hf]

lemma traceVelocity_activation {E : Type w} {ι : Type u}
    (R : Finset E) (c : ℝ) {K : Finset (E ⊕ ι)}
    {i : ι} (haK : (Sum.inr i : E ⊕ ι) ∈ K) :
    traceVelocity R c (⟨Sum.inr i, haK⟩ : K) = 1 := rfl

/-- Sum the trace velocity as one union base-pivot term and all independent
activation-pivot terms. -/
lemma sum_traceVelocity_mul {E : Type w} {ι : Type u} [Fintype ι]
    {R : Finset E} {K : Finset (E ⊕ ι)}
    (hRK : bondCoordinates (F := ι) R ⊆ K) (c : ℝ)
    (haK : ∀ i, (Sum.inr i : E ⊕ ι) ∈ K) (W : K → ℝ) :
    (∑ x, traceVelocity R c x * W x) =
      (-c) * (∑ x ∈ traceFinset (bondCoordinates (F := ι) R) K hRK, W x) +
        ∑ i, W ⟨Sum.inr i, haK i⟩ := by
  classical
  let B := traceFinset (bondCoordinates (F := ι) R) K hRK
  let emb : ι ↪ K :=
    ⟨fun i => ⟨Sum.inr i, haK i⟩, by
      intro i j h
      exact Sum.inr_injective (congrArg Subtype.val h)⟩
  let A : Finset K := Finset.univ.map emb
  have hBA : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    have hxbase := (mem_traceFinset (hRK := hRK) x).1 hxB
    obtain ⟨i, _, hxi⟩ := Finset.mem_map.mp hxA
    have hval : x.1 = Sum.inr i := congrArg Subtype.val hxi.symm
    rw [hval] at hxbase
    simp [bondCoordinates] at hxbase
  have hsum : (∑ x, traceVelocity R c x * W x) =
      ∑ x ∈ B ∪ A, traceVelocity R c x * W x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hxB : x ∉ B := fun h => hx (Finset.mem_union_left _ h)
    have hxA : x ∉ A := fun h => hx (Finset.mem_union_right _ h)
    have hv : traceVelocity R c x = 0 := by
      cases hxval : x.1 with
      | inl f =>
          by_cases hf : f ∈ R
          · exfalso
            apply hxB
            apply (mem_traceFinset (hRK := hRK) x).2
            rw [hxval]
            simp [bondCoordinates, hf]
          · change (match x.1 with
              | Sum.inl e => if e ∈ R then -c else 0
              | Sum.inr _ => 1) = 0
            rw [hxval]
            simp [hf]
      | inr i =>
          exfalso
          apply hxA
          apply Finset.mem_map.mpr
          refine ⟨i, Finset.mem_univ _, ?_⟩
          apply Subtype.ext
          exact hxval.symm
    rw [hv, zero_mul]
  rw [hsum, Finset.sum_union hBA]
  have hA : (∑ x ∈ A, traceVelocity R c x * W x) = ∑ i, W ⟨Sum.inr i, haK i⟩ := by
    change (∑ x ∈ Finset.univ.map emb, traceVelocity R c x * W x) = _
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    change traceVelocity R c (emb i) * W (emb i) = W ⟨Sum.inr i, haK i⟩
    have hemb : emb i = ⟨Sum.inr i, haK i⟩ := by
      apply Subtype.ext
      rfl
    rw [hemb, traceVelocity_activation R c (haK i), one_mul]
  rw [hA]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [traceVelocity_of_mem hRK c hx]

lemma bondCoordinates_mono {E : Type w} {ι : Type u}
    {R T : Finset E} (hRT : R ⊆ T) :
    bondCoordinates (F := ι) R ⊆ bondCoordinates (F := ι) T := by
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨f, hf, rfl⟩
  exact Finset.mem_map.mpr ⟨f, hRT hf, rfl⟩

/-- The trace image of the union of annuli is the union of the individual
trace images, including all repetitions on the right-hand side. -/
lemma traceFinset_baseSupport_eq_biUnion {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (hRi : ∀ i, bondCoordinates (F := ι) (annulus H (S i)) ⊆ K) :
    traceFinset (bondCoordinates (F := ι) (baseSupport H S)) K hRK =
      Finset.univ.biUnion (fun i =>
        traceFinset (bondCoordinates (F := ι) (annulus H (S i))) K (hRi i)) := by
  classical
  ext x
  simp only [mem_traceFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨f, hf, hfx⟩
    obtain ⟨i, hi⟩ := (mem_baseSupport H).1 hf
    refine ⟨i, Finset.mem_map.mpr ⟨f, hi, hfx⟩⟩
  · rintro ⟨i, hx⟩
    rcases Finset.mem_map.mp hx with ⟨f, hf, hfx⟩
    exact Finset.mem_map.mpr ⟨f, (mem_baseSupport H).2 ⟨i, hf⟩, hfx⟩

/-- Nonnegative normalized derivative on an arbitrary finite trace.  The base
sum is over the union of annuli; no disjointness premise is used. -/
lemma tracePivotSlope_nonneg_of_box {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b t : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp : p ∈ Icc a b)
    (hmove : p - independentComparisonSpeed a b R * t ∈ Icc a b)
    (hs : s + t ∈ Icc a b) :
    let c := independentComparisonSpeed a b R
    0 ≤ (-c) * (∑ x ∈ traceFinset (bondCoordinates (F := ι)
        (baseSupport H S)) K hRK,
      eventWeight (fun y : K => independentLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) x ξ}) +
      ∑ i, eventWeight (fun y : K => independentLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) ⟨Sum.inr i, haK i⟩ ξ} := by
  classical
  dsimp only
  let c := independentComparisonSpeed a b R
  let r : K → ℝ := fun y => independentLine H S p s c t y.1
  have hRi : ∀ i, bondCoordinates (F := ι) (annulus H (S i)) ⊆ K := fun i =>
    (bondCoordinates_mono (show annulus H (S i) ⊆ baseSupport H S from by
      intro f hf
      exact (mem_baseSupport H).2 ⟨i, hf⟩)).trans hRK
  let Dp : ι → ℝ := fun i => ∑ x ∈ traceFinset
    (bondCoordinates (F := ι) (annulus H (S i))) K (hRi i),
    eventWeight r {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n)) x ξ}
  let U : ℝ := ∑ x ∈ traceFinset (bondCoordinates (F := ι)
    (baseSupport H S)) K hRK,
    eventWeight r {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n)) x ξ}
  let Pa : ι → ℝ := fun i => eventWeight r
    {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n)) ⟨Sum.inr i, haK i⟩ ξ}
  let den : ℝ := ((2 ^ R : ℕ) : ℝ) * (R : ℝ)
  have hrbox : ∀ x, r x ∈ Icc a b := by
    intro x
    exact independentLine_mem_box H S hp hmove hs x.1
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
    have h := trace_sum_pivot_event_mul_le H S i o n (hRi i) (haK i) ν
      (sleeveMinorant a b) hminor.le hν
    simp_rw [hevent] at h
    change (sleeveMinorant a b) ^ (S i).card * Dp i ≤
      (((2 ^ (S i).card : ℕ) : ℝ) * ((S i).card : ℝ)) * Pa i at h
    rwa [hcard i] at h
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hden : 0 < den := by dsimp [den]; positivity
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
    exact Finset.sum_le_sum fun i _ => hmul i
  have hW (x : K) : 0 ≤ eventWeight r {ξ | Pivotal (traceEvent K
      (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ} := by
    rw [← hevent]
    exact OpenPath.FinProb.event_nonneg _ _
  have hoverlap : U ≤ ∑ i, Dp i := by
    change (∑ x ∈ traceFinset (bondCoordinates (F := ι)
      (baseSupport H S)) K hRK, eventWeight r {ξ | Pivotal (traceEvent K
        (deviceArmEvent (graph H) (independentSupport H S) o n)) x ξ}) ≤ _
    rw [traceFinset_baseSupport_eq_biUnion H S hRK hRi]
    exact sum_biUnion_le_of_nonneg Finset.univ _ _ hW
  have hc : 0 ≤ c := independentComparisonSpeed_nonneg R ha.le hb.le
  have hcOverlap : c * U ≤ c * ∑ i, Dp i := mul_le_mul_of_nonneg_left hoverlap hc
  change 0 ≤ (-c) * U + ∑ i, Pa i
  linarith

/-- Monotone finite-trace comparison curve for an independently activated
finite family on an arbitrary graph. -/
lemma monotoneOn_traceEventWeight_independentLine {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    MonotoneOn (fun t => eventWeight
      (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) t x.1)
      (traceEvent K (deviceArmEvent (graph H)
        (independentSupport H S) o n))) (Icc (0 : ℝ) T) := by
  classical
  let c := independentComparisonSpeed a b R
  have hRi : ∀ i, bondCoordinates (F := ι) (annulus H (S i)) ⊆ K := fun i =>
    (bondCoordinates_mono (show annulus H (S i) ⊆ baseSupport H S from by
      intro f hf
      exact (mem_baseSupport H).2 ⟨i, hf⟩)).trans hRK
  let U : ℝ → ℝ := fun t => ∑ x ∈ traceFinset
    (bondCoordinates (F := ι) (baseSupport H S)) K hRK,
    eventWeight (fun y : K => independentLine H S p s c t y.1)
      {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
        (independentSupport H S) o n)) x ξ}
  let Pa : ℝ → ℝ := fun t => ∑ i,
    eventWeight (fun y : K => independentLine H S p s c t y.1)
      {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
        (independentSupport H S) o n)) ⟨Sum.inr i, haK i⟩ ξ}
  have hc : 0 ≤ c := independentComparisonSpeed_nonneg R ha.le hb.le
  have hupper : IsUpperSet (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n)) :=
    isUpperSet_traceEvent K (isUpperSet_deviceArmEvent (graph H)
      (independentSupport H S) o n)
  have hline (t : ℝ) : (fun x : K => independentLine H S p s c t x.1) =
      affineRates (fun x : K => independentLine H S p s c 0 x.1)
        (fun x => traceVelocity (baseSupport H S) c x) t := by
    funext x
    cases hx : x.1 with
    | inl e =>
        simpa only [affineRates, traceVelocity, independentVelocity, hx,
          indexedVelocity] using congrFun (independentLine_eq_affine H S p s c t) x.1
    | inr i =>
        simpa only [affineRates, traceVelocity, independentVelocity, hx,
          indexedVelocity] using congrFun (independentLine_eq_affine H S p s c t) x.1
  have hderiv (t : ℝ) : HasDerivAt
      (fun y => eventWeight (fun x : K => independentLine H S p s c y x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n))) ((-c) * U t + Pa t) t := by
    have h := hasDerivAt_eventWeight_affine_pivotal
      (fun x : K => independentLine H S p s c 0 x.1)
      (fun x => traceVelocity (baseSupport H S) c x) hupper t
    simp_rw [← hline] at h
    convert h using 1
    simpa only [U, Pa] using (sum_traceVelocity_mul hRK c haK (fun x =>
      eventWeight (fun y : K => independentLine H S p s c t y.1)
        {ξ | Pivotal (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) x ξ})).symm
  change MonotoneOn (fun t => eventWeight
    (fun x : K => independentLine H S p s c t x.1)
    (traceEvent K (deviceArmEvent (graph H)
      (independentSupport H S) o n))) (Icc (0 : ℝ) T)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) T)
    (f' := fun t => (-c) * U t + Pa t)
  · intro t ht
    exact (hderiv t).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t).hasDerivWithinAt
  · intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := interior_subset ht
    have hbox := independentLine_parameters_mem_box hc htcc hp0 hs0 hpT hsT
    exact tracePivotSlope_nonneg_of_box H S R hR hcard o n hRK haK
      p s a b t ha hb hp0 hbox.1 hbox.2

/-- Endpoint comparison for the finite-trace polynomial. -/
lemma traceEventWeight_independentLine_le {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    {K : Finset ((graph H).edgeSet ⊕ ι)}
    (hRK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K)
    (haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b) :
    eventWeight (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) ≤
      eventWeight (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) T x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) := by
  have hmono := monotoneOn_traceEventWeight_independentLine H S R hR hcard o n
    hRK haK p s a b T ha hb hp0 hs0 hpT hsT
  exact hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT

end FK.AGImplant.Sleeve.BoundedCoordinate

namespace FK.AGImplant.Sleeve.BoundedCoordinate

open FK.EssentialEnhancement FK.AGPeeling
open FK.Finite.Comparison FK.MargulisRussoFinite
open CurvatureVariance.Infra.Percolation
open FK.AGImplant.Sleeve.Infinite

/-- Unit-interval rates on one point of the indexed comparison line. -/
noncomputable def unitIndependentLine {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (p s c t : ℝ) (hr : ∀ x, independentLine H S p s c t x ∈ Icc (0 : ℝ) 1) :
    (graph H).edgeSet ⊕ ι → unitInterval := fun x =>
  ⟨independentLine H S p s c t x, (hr x).1, (hr x).2⟩

@[simp] lemma coe_unitIndependentLine {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (p s c t : ℝ) (hr : ∀ x, independentLine H S p s c t x ∈ Icc (0 : ℝ) 1)
    (x : (graph H).edgeSet ⊕ ι) :
    (unitIndependentLine H S p s c t hr x : ℝ) = independentLine H S p s c t x := rfl

/-- **Infinite-product arm comparison for a finite indexed family on an actual
infinite locally finite graph.**  Overlapping annuli are allowed. -/
theorem infiniteProductLaw_deviceArmEvent_independentLine_le
    {V : Type v} (H : SimpleGraph V) [H.LocallyFinite] (hG : H.Connected)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (R : ℕ) (hR : 0 < R) (hcard : ∀ i, (S i).card = R)
    (o : V ⊕ H.edgeSet) (n : ℕ)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, independentLine H S p s
      (independentComparisonSpeed a b R) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, independentLine H S p s
      (independentComparisonSpeed a b R) T x ∈ Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitIndependentLine H S p s
        (independentComparisonSpeed a b R) 0 hr0)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal ≤
      (infiniteProductLaw (unitIndependentLine H S p s
        (independentComparisonSpeed a b R) T hrT)
        (deviceArmEvent (graph H) (independentSupport H S) o n)).toReal := by
  classical
  let K := coordinates H hG S o n
  have hRK : bondCoordinates (F := ι) (baseSupport H S) ⊆ K :=
    baseSupport_subset_coordinates H hG S o n
  have haK : ∀ i, (Sum.inr i : (graph H).edgeSet ⊕ ι) ∈ K :=
    activation_mem_coordinates H hG S o n
  have hdep : DependsOn (fun χ => χ ∈ deviceArmEvent (graph H)
      (independentSupport H S) o n) (K : Set ((graph H).edgeSet ⊕ ι)) :=
    dependsOn_deviceArmEvent H hG S o n
  have h0 := eventWeight_traceEvent
    (unitIndependentLine H S p s (independentComparisonSpeed a b R) 0 hr0) K
    (deviceArmEvent (graph H) (independentSupport H S) o n) hdep
  have hT' := eventWeight_traceEvent
    (unitIndependentLine H S p s (independentComparisonSpeed a b R) T hrT) K
    (deviceArmEvent (graph H) (independentSupport H S) o n) hdep
  calc
    _ = eventWeight (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) 0 x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) := h0.symm
    _ ≤ eventWeight (fun x : K => independentLine H S p s
        (independentComparisonSpeed a b R) T x.1)
        (traceEvent K (deviceArmEvent (graph H)
          (independentSupport H S) o n)) :=
      traceEventWeight_independentLine_le H S R hR hcard o n hRK haK
        p s a b T ha hb hT hp0 hs0 hpT hsT
    _ = _ := hT'

/-- The independently activated device map is measurable.  Only the finite
union of activation supports needs special treatment. -/
lemma measurable_deviceConfig_independentSupport {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet) :
    Measurable (deviceConfig (independentSupport H S)) := by
  classical
  apply measurable_pi_iff.2
  intro f
  change Measurable (fun χ => if AddsEdge (independentSupport H S) χ f then true
    else χ (Sum.inl f))
  by_cases hf : f ∈ activationSupport H S
  · apply Measurable.ite _ measurable_const (measurable_pi_apply _)
    have hset : {χ : JointConfig (graph H).edgeSet ι |
        AddsEdge (independentSupport H S) χ f} =
        ⋃ i, {χ : JointConfig (graph H).edgeSet ι |
          χ (Sum.inr i) = true ∧ f ∈ edges H (S i)} := by
      ext χ
      simp [AddsEdge, independentSupport]
    rw [hset]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : f ∈ edges H (S i)
    · have hm : MeasurableSet {χ : JointConfig (graph H).edgeSet ι |
          χ (Sum.inr i) = true} :=
        measurableSet_eq_fun (measurable_pi_apply _) measurable_const
      simpa [hi] using hm
    · simp [hi]
  · have hnot : ∀ χ : JointConfig (graph H).edgeSet ι,
        ¬ AddsEdge (independentSupport H S) χ f := by
      intro χ hadd
      obtain ⟨i, _, hi⟩ := hadd
      exact hf ((mem_activationSupport H).2 ⟨i, hi⟩)
    simpa [hnot] using (measurable_pi_apply (Sum.inl f) :
      Measurable (fun χ : JointConfig (graph H).edgeSet ι => χ (Sum.inl f)))

/-- The actual infinite-cluster event after applying all indexed devices. -/
def independentPercolationEvent {V : Type v} (H : SimpleGraph V)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet)
    (o : V ⊕ H.edgeSet) : Set (JointConfig (graph H).edgeSet ι) :=
  deviceConfig (independentSupport H S) ⁻¹'
    {ω | {x | OpenConnected (graph H) ω Set.univ o x}.Infinite}

/-- Enhanced percolation is the decreasing intersection of enhanced arms. -/
lemma independentPercolationEvent_eq_iInter {V : Type v} (H : SimpleGraph V)
    [H.LocallyFinite] (hG : H.Connected)
    {ι : Type u} [Fintype ι] (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet) :
    independentPercolationEvent H S o =
      ⋂ n, deviceArmEvent (graph H) (independentSupport H S) o n := by
  rw [independentPercolationEvent,
    setOf_infinite_eq_iInter_armEvent (graphConnected H hG) o]
  ext χ
  simp only [Set.mem_preimage, Set.mem_iInter, deviceArmEvent, deviceEvent]

/-- Continuity from above for the actual independent infinite product. -/
theorem tendsto_infiniteProductLaw_deviceArmEvent_independent
    {V : Type v} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (o : V ⊕ H.edgeSet)
    (r : (graph H).edgeSet ⊕ ι → unitInterval) :
    Tendsto (fun n =>
      (infiniteProductLaw r (deviceArmEvent (graph H)
        (independentSupport H S) o n)).toReal) atTop
      (𝓝 ((infiniteProductLaw r (independentPercolationEvent H S o)).toReal)) := by
  have hlim : Tendsto (fun n =>
      infiniteProductLaw r (deviceArmEvent (graph H)
        (independentSupport H S) o n)) atTop
      (𝓝 (infiniteProductLaw r (independentPercolationEvent H S o))) := by
    rw [independentPercolationEvent_eq_iInter H hG S o]
    exact tendsto_measure_iInter_atTop
      (fun n => ((measurable_deviceConfig_independentSupport H S)
        (measurableSet_armEvent o n)).nullMeasurableSet)
      (by
        intro m n hmn
        exact Set.preimage_mono (armEvent_antitone o hmn))
      ⟨0, measure_ne_top _ _⟩
  have hreal := (ENNReal.tendsto_toReal
    (a := infiniteProductLaw r (independentPercolationEvent H S o))
    (measure_ne_top _ _)).comp hlim
  simpa only [Function.comp_def] using hreal

/-- **Infinite-cluster comparison on the actual infinite sleeved graph.**
The activation coordinates remain genuinely indexed and no disjointness is
required.  The finite-index assumption and uniform positive annulus size are
the precise remaining scope restrictions; no strict critical shift is claimed. -/
theorem infiniteProductLaw_independentPercolation_independentLine_le
    {V : Type v} [Countable V] (H : SimpleGraph V) [H.LocallyFinite]
    (hG : H.Connected) {ι : Type u} [Fintype ι]
    (S : ι → Finset H.edgeSet) (R : ℕ) (hR : 0 < R)
    (hcard : ∀ i, (S i).card = R) (o : V ⊕ H.edgeSet)
    (p s a b T : ℝ) (ha : 0 < a) (hb : b < 1) (hT : 0 ≤ T)
    (hp0 : p ∈ Icc a b) (hs0 : s ∈ Icc a b)
    (hpT : p - independentComparisonSpeed a b R * T ∈ Icc a b)
    (hsT : s + T ∈ Icc a b)
    (hr0 : ∀ x, independentLine H S p s
      (independentComparisonSpeed a b R) 0 x ∈ Icc (0 : ℝ) 1)
    (hrT : ∀ x, independentLine H S p s
      (independentComparisonSpeed a b R) T x ∈ Icc (0 : ℝ) 1) :
    (infiniteProductLaw (unitIndependentLine H S p s
        (independentComparisonSpeed a b R) 0 hr0)
        (independentPercolationEvent H S o)).toReal ≤
      (infiniteProductLaw (unitIndependentLine H S p s
        (independentComparisonSpeed a b R) T hrT)
        (independentPercolationEvent H S o)).toReal := by
  apply le_of_tendsto_of_tendsto
    (tendsto_infiniteProductLaw_deviceArmEvent_independent H hG S o
      (unitIndependentLine H S p s (independentComparisonSpeed a b R) 0 hr0))
    (tendsto_infiniteProductLaw_deviceArmEvent_independent H hG S o
      (unitIndependentLine H S p s (independentComparisonSpeed a b R) T hrT))
  exact Filter.Eventually.of_forall fun n =>
    infiniteProductLaw_deviceArmEvent_independentLine_le H hG S R hR hcard o n
      p s a b T ha hb hT hp0 hs0 hpT hsT hr0 hrT

#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.sum_biUnion_le_of_nonneg
#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.trace_sum_pivot_event_mul_le
#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.tracePivotSlope_nonneg_of_box
#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.monotoneOn_traceEventWeight_independentLine
#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.infiniteProductLaw_deviceArmEvent_independentLine_le
#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.tendsto_infiniteProductLaw_deviceArmEvent_independent
#print axioms FK.AGImplant.Sleeve.BoundedCoordinate.infiniteProductLaw_independentPercolation_independentLine_le

end FK.AGImplant.Sleeve.BoundedCoordinate
