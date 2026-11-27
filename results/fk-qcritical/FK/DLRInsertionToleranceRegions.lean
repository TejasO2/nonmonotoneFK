import FK.DLRInsertionToleranceCore
import FK.ComparableNonpercolating
import FK.EncounterProbability

/-!
# Insertion tolerance for canonical and source FK specifications

Every finite edge set is interior to the induced box of the finite set of its
endpoints.  Thus the fixed-box DLR finite-energy theorem applies to every patch
in the all-finite-region canonical and source specifications.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical

local instance regionSetoidMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance regionFiniteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FK.InsertionTolerance

open FK.InfiniteVolume
open FK.RandomClosedBoundary
open FK.RandomRegionKernel
open FK.SourceRegions
open FK.ComparableNonpercolating
open FK.BurtonKeane
open CurvatureVariance.Infra.Percolation

noncomputable section

universe u

/-- Every finite set of labelled edges is contained in the induced box of a
finite vertex region, namely its finite endpoint set. -/
theorem exists_boxOf_edges {V : Type u} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (F : Finset G.edgeSet) :
    ∃ s : Finset V, F ⊆ (boxOf (G := G) s).edges := by
  classical
  let T : Set V := {x : V | ∃ e ∈ F, x ∈ (e.1 : Sym2 V)}
  have hTfin : T.Finite := by
    refine Set.Finite.subset
      (F.finite_toSet.biUnion fun e _ => FK.M3.finite_mem_sym2 (V := V) e.1) ?_
    rintro x ⟨e, he, hx⟩
    exact Set.mem_biUnion he hx
  refine ⟨hTfin.toFinset, ?_⟩
  intro e he
  rw [FK.RandomClosedBoundary.mem_regionBox_edges_iff,
    FK.RandomClosedBoundary.mem_interiorEdgeSet_iff]
  intro x hx
  exact hTfin.mem_toFinset.mpr ⟨e, he, hx⟩

/-- Canonical all-finite-region FK-DLR laws have finite-pattern insertion
tolerance at interior parameters.  No nonpercolation or comparison premise is
used: the DLR equation itself and finite FK positivity suffice. -/
theorem finitePatternInsertionTolerance_of_canonicalRegionDLR
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp₁.le μ) :
    FinitePatternInsertionTolerance (μ : Measure (Configuration G.edgeSet)) := by
  intro j A hA hAdep hApos
  obtain ⟨s, hs⟩ := exists_boxOf_edges (G := G) j.1
  exact measure_pos_inter_forcedPattern_of_isDLR (boxOf (G := G) s) hq hp₀ hp₁
    (exteriorPartition (G := G) (s : Set V) s.finite_toSet)
    (measurable_exteriorPartition (G := G) (s : Set V) s.finite_toSet)
    μ (hμ s) j hs A hA hAdep hApos

/-- Every law in the all-finite-region DLR class of an actual source
convention has finite-pattern insertion tolerance at interior parameters.
The geometric validity predicate `IsSourceGeometry` is not needed for this
measure-theoretic statement. -/
theorem finitePatternInsertionTolerance_of_sourceDLR
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : SourceConvention G hq hp₁.le)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) :
    FinitePatternInsertionTolerance (μ : Measure (Configuration G.edgeSet)) := by
  intro j A hA hAdep hApos
  obtain ⟨s, hs⟩ := exists_boxOf_edges (G := G) j.1
  exact measure_pos_inter_forcedPattern_of_isDLR (boxOf (G := G) s) hq hp₀ hp₁
    (Φ.partition s) (Φ.measurable_partition s) μ (hμ s) j hs A hA hAdep hApos

/-- Positive-probability encounters for a canonical all-region FK-DLR law.
The three-infinite-cluster premise is retained exactly; no claim that this
premise holds is made here. -/
theorem measure_pos_encounterEvent_of_canonicalRegionDLR
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp₁.le μ)
    (hS : 0 < (μ : Measure (Configuration G.edgeSet))
      {ω | ThreeInfiniteClusters G ω}) :
    0 < (μ : Measure (Configuration G.edgeSet)) (EncounterEvent G) := by
  exact measure_pos_encounterEvent_of_three_infinite_of_insertionTolerant hG
    (μ : Measure (Configuration G.edgeSet))
    (finitePatternInsertionTolerance_of_canonicalRegionDLR hq hp₀ hp₁ μ hμ) hS

/-- Positive-probability encounters for an actual source-convention DLR law,
again conditionally only on the stated positive three-infinite-cluster mass. -/
theorem measure_pos_encounterEvent_of_sourceDLR
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : SourceConvention G hq hp₁.le)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ)
    (hS : 0 < (μ : Measure (Configuration G.edgeSet))
      {ω | ThreeInfiniteClusters G ω}) :
    0 < (μ : Measure (Configuration G.edgeSet)) (EncounterEvent G) := by
  exact measure_pos_encounterEvent_of_three_infinite_of_insertionTolerant hG
    (μ : Measure (Configuration G.edgeSet))
    (finitePatternInsertionTolerance_of_sourceDLR hq hp₀ hp₁ Φ μ hμ) hS

end

end FK.InsertionTolerance
