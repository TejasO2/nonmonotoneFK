import FK.RandomClosedBoundary
import FK.NonlocalGeometry

/-!
# From the random region to a finite box with closed frontier

`RandomClosedBoundary.lean` constructs the paper's random regions
`S_n(ω) = region G ω (base n)` and proves they are measurable, finite,
connected, closed-boundary and exhaustive almost surely.

This file adds the box-level layer of Theorem 5.1 for the actual labelled edge
labels of the configuration:

* `interiorEdgeSet R` is the labelled finite box of a vertex region: all
  labelled edges both of whose endpoints lie in `R`.  Under local finiteness it
  is finite, so the region really induces a finite box;
* `frontier_closed`: every labelled edge of `R` that is incident with `R` but
  not interior is closed in `ω`.  This is the literal statement
  `ω|∂S_n(ω) = 0`;
* `exists_interiorEdgeSet_contains` / `ae_region_box`: every fixed finite edge
  set (in particular the edge set of a fixed cylindrical event) is eventually
  interior to the boxes, and the boxes are finite with closed frontier almost
  surely, off the single non-percolation null set;
* `freeBoundary_eq_bot`: the free boundary partition of the finite FK model is
  the bottom (equality) setoid, so the boundary step proved in
  `exteriorOpenSetoid_eq_bot` says exactly that a closed-boundary region
  induces the free finite-volume FK law.

Residual: the vertex re-indexing that turns `interiorEdgeSet R` into a
`FK.InfiniteVolume.FiniteBox` with `Vertex = ↥R` (choosing an orientation of
each labelled edge) and the resulting identification of the exterior
conditional law are not built here; see the notes file for the precise
remaining obligation.
-/

open MeasureTheory Set
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V}

/-! ## The interior labelled box of a region -/

/-- The labelled edges whose two endpoints lie in `R`. -/
def interiorEdgeSet (G : SimpleGraph V) (R : Set V) : Set G.edgeSet :=
  {e | ∀ x ∈ (e.1 : Sym2 V), x ∈ R}

theorem mem_interiorEdgeSet_iff {R : Set V} {e : G.edgeSet} :
    e ∈ interiorEdgeSet G R ↔ ∀ x ∈ (e.1 : Sym2 V), x ∈ R := Iff.rfl

theorem interiorEdgeSet_mono {R R' : Set V} (h : R ⊆ R') :
    interiorEdgeSet G R ⊆ interiorEdgeSet G R' := by
  intro e he x hx
  exact h (he x hx)

/-- Every labelled edge of the ambient graph has two adjacent endpoints. -/
theorem exists_adj_of_mem_edgeSet {e : G.edgeSet} :
    ∃ a b : V, G.Adj a b ∧ s(a, b) = (e.1 : Sym2 V) := by
  obtain ⟨a, b, hSab⟩ := Sym2.exists.mp (⟨e.1, rfl⟩ : ∃ p : Sym2 V, p = (e.1 : Sym2 V))
  refine ⟨a, b, (SimpleGraph.mem_edgeSet (G := G)).mp ?_, hSab⟩
  rw [hSab]
  exact e.2

/-- The interior box is contained in the incident edge set of `R`. -/
theorem interiorEdgeSet_subset_clusterSupport {R : Set V} :
    interiorEdgeSet G R ⊆ FK.InfiniteVolume.NonlocalInterior.clusterSupport (G := G) R := by
  intro e he
  obtain ⟨a, b, _hab, hSab⟩ := exists_adj_of_mem_edgeSet (G := G) (e := e)
  have ha : a ∈ (e.1 : Sym2 V) := by rw [← hSab]; exact Sym2.mem_mk_left a b
  exact ⟨a, he a ha, ha⟩

/-- On a locally finite graph the interior box of a finite region is finite. -/
theorem finite_interiorEdgeSet [G.LocallyFinite] {R : Set V} (hR : R.Finite) :
    (interiorEdgeSet G R).Finite :=
  (FK.InfiniteVolume.NonlocalInterior.finite_clusterSupport (G := G) hR).subset
    interiorEdgeSet_subset_clusterSupport

/-- **`ω|∂R = 0` for labelled edges.**  A labelled edge incident with the region
that is not interior crosses the frontier, hence is closed. -/
theorem frontier_closed {ω : G.edgeSet → Bool} {R : Set V}
    (hR : ClosedBoundary G (openSubgraph G ω) R) {e : G.edgeSet}
    (hin : ∃ x ∈ (e.1 : Sym2 V), x ∈ R) (hout : ∃ x ∈ (e.1 : Sym2 V), x ∉ R) :
    ω e = false := by
  classical
  obtain ⟨a, b, hab, hSab⟩ := exists_adj_of_mem_edgeSet (G := G) (e := e)
  have hmem : ∀ x : V, x ∈ (e.1 : Sym2 V) ↔ x = a ∨ x = b := by
    intro x
    rw [← hSab, Sym2.mem_iff]
  by_contra hne
  have hopen : ω e = true := by
    cases hv : ω e
    · exact absurd hv hne
    · rfl
  have hadj : (openSubgraph G ω).Adj a b := by
    rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨e, hopen, hSab.symm⟩, G.ne_of_adj hab⟩
  have hadj' : (openSubgraph G ω).Adj b a := hadj.symm
  by_cases ha : a ∈ R
  · have hb : b ∉ R := by
      rintro hbR
      obtain ⟨x, hx, hxR⟩ := hout
      rcases (hmem x).mp hx with rfl | rfl
      · exact hxR ha
      · exact hxR hbR
    exact absurd hadj (hR ha hb hab)
  · obtain ⟨x, hx, hxR⟩ := hin
    rcases (hmem x).mp hx with rfl | rfl
    · exact absurd hxR ha
    · exact absurd hadj' (hR hxR ha hab.symm)

/-- Any fixed finite labelled edge set is eventually interior to the boxes of
the random exhaustion. -/
theorem exists_interiorEdgeSet_contains (ω : G.edgeSet → Bool) (T : ℕ → Set V)
    (hTmono : Monotone T) (hTcov : ⋃ n, T n = Set.univ) {F : Set G.edgeSet}
    (hF : F.Finite) :
    ∃ N, ∀ n ≥ N, F ⊆ interiorEdgeSet G (region G ω (T n)) := by
  obtain ⟨N, hN⟩ := exists_edges_inside (G := G) (ω := ω) T hTmono hTcov hF
  exact ⟨N, fun n hn e he x hx => hN n hn e he x hx⟩

/-- Almost surely the box of every stage is a finite labelled edge box whose
frontier edges are closed, and a fixed finite edge set is eventually inside. -/
theorem ae_region_box [Countable V] [G.LocallyFinite]
    {μ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure μ]
    (T : ℕ → Set V) (hTfin : ∀ n, (T n).Finite)
    (hfin : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    ∀ᵐ ω ∂μ, (∀ n, (interiorEdgeSet G (region G ω (T n))).Finite) ∧
      (∀ n, ClosedBoundary G (openSubgraph G ω) (region G ω (T n))) ∧
      (∀ n (e : G.edgeSet), (∃ x ∈ (e.1 : Sym2 V), x ∈ region G ω (T n)) →
        (∃ x ∈ (e.1 : Sym2 V), x ∉ region G ω (T n)) → ω e = false) := by
  filter_upwards [hfin] with ω hω
  have hfinc : FiniteOpenClusters (openSubgraph G ω) :=
    finiteOpenClusters_of_nonPercolating G ω hω
  refine ⟨fun n => finite_interiorEdgeSet (region_finite (hTfin n) hfinc),
    fun n => region_closedBoundary (T n), ?_⟩
  intro n e hin hout
  exact frontier_closed (region_closedBoundary (T n)) hin hout

/-! ## The free boundary of the finite model -/

/-- The free boundary partition of the finite FK model is the bottom setoid, so
`exteriorOpenSetoid_eq_bot` identifies a closed-boundary region's induced
boundary condition with the free finite-volume FK law. -/
theorem freeBoundary_eq_bot (H : FK.Finite.LabelledMultigraph) :
    FK.Finite.LabelledMultigraph.freeBoundary H = ⊥ := by
  apply Setoid.ext
  intro x y
  exact Iff.rfl

end FK.RandomClosedBoundary

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.exists_adj_of_mem_edgeSet
#print axioms FK.RandomClosedBoundary.interiorEdgeSet_subset_clusterSupport
#print axioms FK.RandomClosedBoundary.finite_interiorEdgeSet
#print axioms FK.RandomClosedBoundary.frontier_closed
#print axioms FK.RandomClosedBoundary.exists_interiorEdgeSet_contains
#print axioms FK.RandomClosedBoundary.ae_region_box
#print axioms FK.RandomClosedBoundary.freeBoundary_eq_bot
