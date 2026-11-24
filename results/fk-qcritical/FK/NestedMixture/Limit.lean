import FK.NestedMixture.Compare

/-!
# Genuine growing-vertex free finite-volume limits at `q ≥ 1`

A growing family of finite boxes (`GrowingFamily`) is a sequence of finite boxes
in a common labelled edge space whose edge sets increase, cover every edge, and
are related by the vertex/edge nesting data of `NestedBox` for every pair of
indices.  Its `upT` masses are eventually monotone (`upT_mass_mono`), because the
larger box's free law is a mixture of sub-box laws over the exterior-induced
partitions, each dominating the small box's free law.  Feeding this into the
cylinder/upper-corner compactness theorem of `FK.MonotoneLimitExistence` yields a
genuine full-sequence weak limit of the free finite-volume laws — a
growing-vertex limit, not merely a fixed-vertex one.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.SpecificationNesting

namespace FK.NestedMixture

open FK.InfiniteVolume

universe u v

variable {E : Type u} [Countable E]

/-- A growing family of finite boxes with genuine vertex/edge nesting data. -/
structure GrowingFamily (E : Type u) where
  box : ℕ → FK.InfiniteVolume.FiniteBox.{u, v} E
  edges_mono : ∀ n m : ℕ, n ≤ m → ∀ e ∈ (box n).edges, e ∈ (box m).edges
  covers : ∀ e : E, ∃ n, e ∈ (box n).edges
  nest : ∀ n m : ℕ, n ≤ m → NestedBox (box n) (box m)

namespace GrowingFamily

variable (F : GrowingFamily E)

/-- The underlying box exhaustion (edge sets only, with the induced nesting). -/
def exh : FK.InfiniteVolume.BoxExhaustion E where
  box := F.box
  monotone := fun n m hnm => F.edges_mono n m hnm
  covers := F.covers

/-- The interior event of a box cut out by the upper-corner pattern `(S,T)`. -/
def boxEvent (B : FK.InfiniteVolume.FiniteBox E) (S : Finset E)
    (hSB : ∀ e ∈ S, e ∈ B.edges) (T : Finset ↥S) : Set B.Interior :=
  {x | ∀ e : ↥S, e ∈ T → x ⟨e.1, hSB e.1 e.2⟩ = true}

theorem boxEvent_isUpperSet (B : FK.InfiniteVolume.FiniteBox E) (S : Finset E)
    (hSB : ∀ e ∈ S, e ∈ B.edges) (T : Finset ↥S) : IsUpperSet (boxEvent B S hSB T) := by
  intro x y hxy hx e he
  have h := hxy ⟨e.1, hSB e.1 e.2⟩
  rw [Bool.le_iff_imp] at h
  exact h (hx e he)

theorem glue_preimage_upT (B : FK.InfiniteVolume.FiniteBox E) (S : Finset E)
    (hSB : ∀ e ∈ S, e ∈ B.edges) (T : Finset ↥S) :
    (fun x : B.Interior => B.glue (B.closedExterior, x)) ⁻¹' FK.InfiniteVolume.upT S T
      = boxEvent B S hSB T := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, FK.InfiniteVolume.upT, boxEvent]
  constructor
  · intro h e he
    have h1 := h e he
    rw [FK.InfiniteVolume.FiniteBox.glue, dif_pos (hSB e.1 e.2)] at h1
    exact h1
  · intro h e he
    rw [FK.InfiniteVolume.FiniteBox.glue, dif_pos (hSB e.1 e.2)]
    exact h e he

/-- The `upT` mass of a box is the FK mass of the corresponding interior event. -/
theorem mass_upT_eq (B : FK.InfiniteVolume.FiniteBox E) {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (α : B.BoundaryPartition) (S : Finset E) (hSB : ∀ e ∈ S, e ∈ B.edges)
    (T : Finset ↥S) :
    ((B.finiteVolumeLaw hq hp α : ProbabilityMeasure (Configuration E)) :
        Measure (Configuration E)) (FK.InfiniteVolume.upT S T)
      = B.graph.fkMeasure hq hp α (boxEvent B S hSB T) := by
  rw [FK.InfiniteVolume.FiniteBox.finiteVolumeLaw_apply_eq hq hp B α _
    (FK.InfiniteVolume.measurableSet_upT S T), glue_preimage_upT B S hSB T]

/-- The region reading of the small box's event is the large box's event. -/
theorem cylOf_boxEvent_eq {B C : FK.InfiniteVolume.FiniteBox E} (N : NestedBox B C)
    (S : Finset E) (hSB : ∀ e ∈ S, e ∈ B.edges) (hSC : ∀ e ∈ S, e ∈ C.edges)
    (T : Finset ↥S) :
    {x : C.Interior | (fun a : ↥N.ide => x a.1) ∈ N.cylOf (boxEvent B S hSB T)}
      = boxEvent C S hSC T := by
  ext x
  simp only [Set.mem_ofPred_eq, NestedBox.cylOf, boxEvent]
  constructor
  · intro h e he
    have h1 : x (((N.edgeEquiv.symm ⟨e.1, hSB e.1 e.2⟩ : ↥N.ide)) : C.graph.Edge) = true :=
      h e he
    have hidx : (((N.edgeEquiv.symm ⟨e.1, hSB e.1 e.2⟩ : ↥N.ide)) : C.graph.Edge)
        = (⟨e.1, hSC e.1 e.2⟩ : C.graph.Edge) := Subtype.ext rfl
    rw [hidx] at h1
    exact h1
  · intro h e he
    have h1 := h e he
    have hidx : (((N.edgeEquiv.symm ⟨e.1, hSB e.1 e.2⟩ : ↥N.ide)) : C.graph.Edge)
        = (⟨e.1, hSC e.1 e.2⟩ : C.graph.Edge) := Subtype.ext rfl
    rw [hidx]
    exact h1

/-- **Eventual monotonicity of upper-corner masses** for the free growing family. -/
theorem upT_mass_mono {q p : NNReal} (hq1 : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (S : Finset E) (T : Finset ↥S) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
      FK.InfiniteVolume.mreal
          (((F.box n).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq1) hp1.le
            (F.box n).graph.freeBoundary : ProbabilityMeasure (Configuration E)) :
            Measure (Configuration E)) (FK.InfiniteVolume.upT S T)
        ≤ FK.InfiniteVolume.mreal
          (((F.box m).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq1) hp1.le
            (F.box m).graph.freeBoundary : ProbabilityMeasure (Configuration E)) :
            Measure (Configuration E)) (FK.InfiniteVolume.upT S T) := by
  classical
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (F.exh.eventually_subset S)
  refine ⟨N, fun n m hn hnm => ?_⟩
  have hSn : ∀ e ∈ S, e ∈ (F.box n).edges := fun e he => hN n hn he
  have hSm : ∀ e ∈ S, e ∈ (F.box m).edges := fun e he => hN m (le_trans hn hnm) he
  have hmassn := mass_upT_eq (F.box n) hq hp1.le (F.box n).graph.freeBoundary S hSn T
  have hmassm := mass_upT_eq (F.box m) hq hp1.le (F.box m).graph.freeBoundary S hSm T
  have hcmp : (F.box n).graph.fkMeasure hq hp1.le (F.box n).graph.freeBoundary
        (boxEvent (F.box n) S hSn T)
      ≤ (F.box m).graph.fkMeasure hq hp1.le (F.box m).graph.freeBoundary
          (boxEvent (F.box m) S hSm T) := by
    have hmain := NestedBox.nested_free_mass_le (N := F.nest n m hnm) (q := q) (p := p)
      hq1 hp0 hp1 (A := boxEvent (F.box n) S hSn T)
      (boxEvent_isUpperSet (F.box n) S hSn T)
    rwa [cylOf_boxEvent_eq (F.nest n m hnm) S hSn hSm T] at hmain
  have h1 : ((F.box n).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq1) hp1.le
      (F.box n).graph.freeBoundary : Measure (Configuration E)) (FK.InfiniteVolume.upT S T)
      ≤ ((F.box m).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq1) hp1.le
        (F.box m).graph.freeBoundary : Measure (Configuration E))
        (FK.InfiniteVolume.upT S T) := by
    rw [hmassn, hmassm]
    exact hcmp
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr h1

/-- **Genuine growing-vertex free finite-volume limits.**  At `q ≥ 1` and
`0 < p < 1`, the free finite-volume laws along a growing family of finite boxes
converge weakly to an actual probability measure on the full configuration
space. -/
theorem exists_free_limit {q p : NNReal} (hq1 : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ φ : ProbabilityMeasure (Configuration E),
      FK.InfiniteVolume.IsFKLimit F.exh (lt_of_lt_of_le zero_lt_one hq1) hp1.le
        (fun n => (F.box n).graph.freeBoundary) φ :=
  FK.InfiniteVolume.exists_isFKLimit_of_eventually_mono_upT F.exh
    (lt_of_lt_of_le zero_lt_one hq1) hp1.le (fun n => (F.box n).graph.freeBoundary)
    (fun S T => F.upT_mass_mono hq1 hp0 hp1 S T)

end GrowingFamily

end FK.NestedMixture

#print axioms FK.NestedMixture.GrowingFamily.exists_free_limit
#print axioms FK.NestedMixture.GrowingFamily.upT_mass_mono
