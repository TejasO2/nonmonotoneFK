import FK.RegionEdgeBox

/-!
# The finite FK box of a closed-boundary region is free

`RandomClosedBoundary.lean` proves that a region whose outgoing ambient edges
are closed in `ω` induces the discrete (free) boundary partition, and
`RegionEdgeBox.lean` supplies the finite labelled edge box
`interiorEdgeSet R`.

This file performs the vertex re-indexing `V ⊇ R → ↥R` that turns that edge box
into an actual `FK.InfiniteVolume.FiniteBox`, and then proves the finite-volume
statement used in the proof of Theorem 5.1: on the closed-boundary event the
exterior-induced boundary partition of the box is the free one, so the interior
FK law *is* the free FK law.

Results:

* `regionBox R hR`: the finite box with vertex type `↥R` and edge labels
  `interiorEdgeSet R`;
* `closedBoundary_of_forall_frontier_false`: all labelled frontier edges closed
  ⇒ `ClosedBoundary`;
* `exteriorPartition`: the boundary partition induced by an exterior
  configuration, defined through `exteriorOpenSetoid` on the actual open walks;
* `exteriorPartition_eq_bot`: on the closed-frontier event it is `⊥`;
* `interiorFKMeasure_eq_free`: consequently the box's interior FK measure with
  the exterior-induced partition is the free FK measure
  `fkMeasure hq hp freeBoundary` — the paper's step "the conditional law is the
  free random-cluster measure in the interior", with no convention slip: the
  identification is a definitional equality of the finite model plus the
  setoid identity.
-/

open MeasureTheory Set
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V}

/-! ## A chosen orientation of a labelled edge -/

/-- The first endpoint of the chosen representative of a labelled edge. -/
noncomputable def edgeFst (e : G.edgeSet) : V :=
  (exists_adj_of_mem_edgeSet (G := G) (e := e)).choose

/-- The second endpoint of the chosen representative of a labelled edge. -/
noncomputable def edgeSnd (e : G.edgeSet) : V :=
  (exists_adj_of_mem_edgeSet (G := G) (e := e)).choose_spec.choose

theorem edgeFst_adj_edgeSnd (e : G.edgeSet) : G.Adj (edgeFst e) (edgeSnd e) :=
  (exists_adj_of_mem_edgeSet (G := G) (e := e)).choose_spec.choose_spec.1

theorem edgeFst_edgeSnd_eq (e : G.edgeSet) :
    s(edgeFst e, edgeSnd e) = (e.1 : Sym2 V) :=
  (exists_adj_of_mem_edgeSet (G := G) (e := e)).choose_spec.choose_spec.2

theorem edgeFst_mem (e : G.edgeSet) : edgeFst e ∈ (e.1 : Sym2 V) := by
  rw [← edgeFst_edgeSnd_eq e]
  exact Sym2.mem_mk_left _ _

theorem edgeSnd_mem (e : G.edgeSet) : edgeSnd e ∈ (e.1 : Sym2 V) := by
  rw [← edgeFst_edgeSnd_eq e]
  exact Sym2.mem_mk_right _ _

/-! ## The finite box of a region -/

/-- The finite labelled box of a finite vertex region: vertex type `↥R`, edge
labels the interior edges of `R`, with the chosen orientation. -/
noncomputable def regionBox (R : Set V) (hR : R.Finite) [G.LocallyFinite] :
    FK.InfiniteVolume.FiniteBox G.edgeSet :=
  letI : Fintype ↥R := hR.fintype
  {
  Vertex := ↥R
  edges := (finite_interiorEdgeSet (G := G) hR).toFinset
  source e :=
    ⟨edgeFst (e : G.edgeSet), by
      have hmem : (e : G.edgeSet) ∈ interiorEdgeSet G R :=
        (finite_interiorEdgeSet (G := G) hR).mem_toFinset.mp e.2
      exact hmem _ (edgeFst_mem _)⟩
  target e :=
    ⟨edgeSnd (e : G.edgeSet), by
      have hmem : (e : G.edgeSet) ∈ interiorEdgeSet G R :=
        (finite_interiorEdgeSet (G := G) hR).mem_toFinset.mp e.2
      exact hmem _ (edgeSnd_mem _)⟩ }

/-! ## Closedness from labelled frontier data -/

theorem mem_edgeSet_of_adj {x y : V} (h : G.Adj x y) : s(x, y) ∈ G.edgeSet :=
  (SimpleGraph.mem_edgeSet (G := G)).mpr h

/-- If every labelled edge crossing the frontier is closed, the region has
closed boundary for the open subgraph. -/
theorem closedBoundary_of_forall_frontier_false {ω : G.edgeSet → Bool} {R : Set V}
    (h : ∀ e : G.edgeSet, (∃ x ∈ (e.1 : Sym2 V), x ∈ R) →
      (∃ x ∈ (e.1 : Sym2 V), x ∉ R) → ω e = false) :
    ClosedBoundary G (openSubgraph G ω) R := by
  intro x y hx hy hxy hadj
  have hcontr := h ⟨s(x, y), mem_edgeSet_of_adj hxy⟩ ⟨x, Sym2.mem_mk_left _ _, hx⟩
    ⟨y, Sym2.mem_mk_right _ _, hy⟩
  rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj] at hadj
  obtain ⟨⟨e, hopen, hee⟩, -⟩ := hadj
  have hfalse : ω e = false := by
    apply h
    · refine ⟨x, ?_, hx⟩
      rw [hee]
      exact Sym2.mem_mk_left _ _
    · refine ⟨y, ?_, hy⟩
      rw [hee]
      exact Sym2.mem_mk_right _ _
  have hopen' : ω e = true := hopen
  rw [hopen'] at hfalse
  exact absurd hfalse (by simp)


/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.edgeFst_adj_edgeSnd
#print axioms FK.RandomClosedBoundary.regionBox
#print axioms FK.RandomClosedBoundary.closedBoundary_of_forall_frontier_false

/-! ## The exterior-induced partition and the free interior law -/


variable [G.LocallyFinite] (R : Set V) (hR : R.Finite)

/-- The finite labelled box of the region. -/
noncomputable abbrev regionBoxOf : FK.InfiniteVolume.FiniteBox G.edgeSet :=
  regionBox R hR

/-- The ambient configuration extending an exterior configuration by closing
all box edges.  Only the exterior values are used below. -/
noncomputable def extendExterior (η : (regionBoxOf (G := G) R hR).Exterior) :
    G.edgeSet → Bool := by
  classical
  exact fun e => if h : e ∈ (regionBoxOf (G := G) R hR).edges then false else η ⟨e, h⟩

/-- The boundary partition induced by an exterior configuration: two vertices
of the region are wired when they are joined by an open walk that avoids the
interior box and uses the exterior values. -/
noncomputable def exteriorPartition (η : (regionBoxOf (G := G) R hR).Exterior) :
    (regionBoxOf (G := G) R hR).BoundaryPartition :=
  FK.InfiniteVolume.ConventionGeometry.exteriorOpenSetoid (S := R) G
    (extendExterior (G := G) R hR η) (nonInteriorEdges R)

/-- A box edge is an interior edge, hence has both endpoints in `R`. -/
theorem mem_interiorEdgeSet_of_mem_box {e : G.edgeSet}
    (he : e ∈ (regionBoxOf (G := G) R hR).edges) : e ∈ interiorEdgeSet G R :=
  (finite_interiorEdgeSet (G := G) hR).mem_toFinset.mp he

/-- **Induced boundary partitions are free on the closed-frontier event.** -/
theorem exteriorPartition_eq_bot {η : (regionBoxOf (G := G) R hR).Exterior}
    (hclose : ∀ (e : G.edgeSet) (hne : e ∉ (regionBoxOf (G := G) R hR).edges),
      (∃ x ∈ (e.1 : Sym2 V), x ∈ R) → (∃ x ∈ (e.1 : Sym2 V), x ∉ R) →
        η ⟨e, hne⟩ = false) :
    exteriorPartition (G := G) R hR η = ⊥ := by
  classical
  apply exteriorOpenSetoid_eq_bot
  apply closedBoundary_of_forall_frontier_false
  intro e hin hout
  by_cases he : e ∈ (regionBoxOf (G := G) R hR).edges
  · obtain ⟨x, hx, hxout⟩ := hout
    exact absurd (mem_interiorEdgeSet_of_mem_box (G := G) R hR he x hx) hxout
  · rw [show extendExterior (G := G) R hR η e =
        (if h : e ∈ (regionBoxOf (G := G) R hR).edges then false
          else η ⟨e, h⟩) from rfl, dif_neg he]
    exact hclose e he hin hout

/-- The exterior restriction of an ambient configuration. -/
noncomputable def restrictExterior (ω : G.edgeSet → Bool) :
    (regionBoxOf (G := G) R hR).Exterior :=
  fun e => ω e.1

/-- If the ambient configuration has closed boundary at the region, the
partition induced by its exterior restriction is free. -/
theorem exteriorPartition_restrict_eq_bot {ω : G.edgeSet → Bool}
    (hcl : ClosedBoundary G (openSubgraph G ω) R) :
    exteriorPartition (G := G) R hR (restrictExterior (G := G) R hR ω) = ⊥ := by
  classical
  apply exteriorPartition_eq_bot
  intro e hne hin hout
  show ω e = false
  exact frontier_closed hcl hin hout

/-- **The paper's conditional step at the finite level.**  The interior FK law
of the region box with the exterior-induced boundary partition is the *free*
FK law on the box. -/
theorem interiorFKMeasure_eq_free {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (η : (regionBoxOf (G := G) R hR).Exterior)
    (hclose : ∀ (e : G.edgeSet) (hne : e ∉ (regionBoxOf (G := G) R hR).edges),
      (∃ x ∈ (e.1 : Sym2 V), x ∈ R) → (∃ x ∈ (e.1 : Sym2 V), x ∉ R) →
        η ⟨e, hne⟩ = false) :
    (regionBoxOf (G := G) R hR).interiorFKMeasure hq hp
        (fun η => exteriorPartition (G := G) R hR η) η =
      (regionBoxOf (G := G) R hR).graph.fkMeasure hq hp
        (regionBoxOf (G := G) R hR).graph.freeBoundary := by
  simp only [FK.InfiniteVolume.FiniteBox.interiorFKMeasure]
  rw [exteriorPartition_eq_bot (G := G) R hR hclose,
    freeBoundary_eq_bot (regionBoxOf (G := G) R hR).graph]

end FK.RandomClosedBoundary

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.exteriorPartition
#print axioms FK.RandomClosedBoundary.exteriorPartition_eq_bot
#print axioms FK.RandomClosedBoundary.exteriorPartition_restrict_eq_bot
#print axioms FK.RandomClosedBoundary.interiorFKMeasure_eq_free
