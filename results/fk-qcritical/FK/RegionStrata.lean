/-
# The random closed region as a product stratum

Geometric core of the random-region DLR fibre identity: for a finite region `R`
containing the exploring base `T`, the stratum `{ω | region G ω T = R}` of the
random closed region factors, under `splitEquiv`, as a product of

* an *exterior* condition (every labelled edge crossing the frontier of `R` is
  closed), and
* an *interior* condition on the region box (every vertex of `R` is
  open-connected to the base `T` inside `R`).

Both factors are measurable in their own coordinates, so the stratum is a
measurable rectangle.  That is what makes the conditional interior law at the
random box computable from the finite specification.
-/

import FK.RegionFiniteBox

open MeasureTheory Set
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V}

/-! ## The interior extension of a box configuration -/

/-- The ambient configuration extending an interior configuration of the region
box by closing every edge outside the box. -/
noncomputable def extendInterior [G.LocallyFinite] (R : Set V) (hR : R.Finite)
    (i : (regionBoxOf (G := G) R hR).Interior) : G.edgeSet → Bool := by
  classical
  exact fun e => if h : e ∈ (regionBoxOf (G := G) R hR).edges then i ⟨e, h⟩ else false

variable [G.LocallyFinite] (R : Set V) (hR : R.Finite)

theorem extendInterior_apply_of_mem {i : (regionBoxOf (G := G) R hR).Interior}
    {e : G.edgeSet} (he : e ∈ (regionBoxOf (G := G) R hR).edges) :
    extendInterior (G := G) R hR i e = i ⟨e, he⟩ := by
  classical
  show (if h : e ∈ (regionBoxOf (G := G) R hR).edges then i ⟨e, h⟩ else false) = i ⟨e, he⟩
  rw [dif_pos he]

theorem extendExterior_apply_of_notMem {η : (regionBoxOf (G := G) R hR).Exterior}
    {e : G.edgeSet} (he : e ∉ (regionBoxOf (G := G) R hR).edges) :
    extendExterior (G := G) R hR η e = η ⟨e, he⟩ := by
  classical
  show (if h : e ∈ (regionBoxOf (G := G) R hR).edges then false else η ⟨e, h⟩) = η ⟨e, he⟩
  rw [dif_neg he]

/-- The box edges are exactly the interior labelled edges of the region. -/
theorem mem_regionBox_edges_iff {e : G.edgeSet} :
    e ∈ (regionBoxOf (G := G) R hR).edges ↔ e ∈ interiorEdgeSet G R := by
  constructor
  · exact mem_interiorEdgeSet_of_mem_box (G := G) R hR
  · intro h
    exact (finite_interiorEdgeSet (G := G) hR).mem_toFinset.mpr h

/-- A labelled edge crossing the frontier of `R` is never a box edge. -/
theorem not_mem_regionBox_edges_of_crossing {e : G.edgeSet}
    (hout : ∃ x ∈ (e.1 : Sym2 V), x ∉ R) :
    e ∉ (regionBoxOf (G := G) R hR).edges := by
  intro he
  obtain ⟨x, hx, hxR⟩ := hout
  exact hxR (mem_interiorEdgeSet_of_mem_box (G := G) R hR he x hx)

/-- Membership of the underlying pair in the coerced interior edge set. -/
theorem mem_coe_interiorEdgeSet {e : G.edgeSet} :
    ((e.1 : Sym2 V)) ∈ (interiorEdgeSet G R : Set (Sym2 V)) ↔ e ∈ interiorEdgeSet G R := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have hxe' : x = e := Subtype.ext hxe
    rwa [hxe'] at hx
  · exact fun h => ⟨e, h, rfl⟩

/-- The glued configuration agrees with the interior extension on box edges. -/
theorem glue_eq_extendInterior
    (z : (regionBoxOf (G := G) R hR).Exterior × (regionBoxOf (G := G) R hR).Interior)
    {e : G.edgeSet} (he : e ∈ (regionBoxOf (G := G) R hR).edges) :
    (regionBoxOf (G := G) R hR).glue z e = extendInterior (G := G) R hR z.2 e := by
  rw [show (regionBoxOf (G := G) R hR).glue z e = z.2 ⟨e, he⟩ from by
    simp only [FK.InfiniteVolume.FiniteBox.glue]
    exact dif_pos he]
  exact (extendInterior_apply_of_mem (G := G) R hR he).symm

/-- The glued configuration agrees with the exterior extension off the box. -/
theorem glue_eq_extendExterior
    (z : (regionBoxOf (G := G) R hR).Exterior × (regionBoxOf (G := G) R hR).Interior)
    {e : G.edgeSet} (he : e ∉ (regionBoxOf (G := G) R hR).edges) :
    (regionBoxOf (G := G) R hR).glue z e = extendExterior (G := G) R hR z.1 e := by
  rw [show (regionBoxOf (G := G) R hR).glue z e = z.1 ⟨e, he⟩ from by
    simp only [FK.InfiniteVolume.FiniteBox.glue]
    exact dif_neg he]
  exact (extendExterior_apply_of_notMem (G := G) R hR he).symm

/-! ## Open walks inside the region box -/

/-- An open walk inside the ambient open graph that starts and ends in a
closed-boundary region stays inside the labelled interior box: every edge it
crosses is an interior edge of the region. -/
theorem isOpenIn_interiorEdgeSet {ω : G.edgeSet → Bool} {R : Set V}
    (hcl : ClosedBoundary G (openSubgraph G ω) R) :
    ∀ {a b : V} {p : G.Walk a b}, IsOpenIn ω Set.univ p → a ∈ R → b ∈ R →
      IsOpenIn ω (interiorEdgeSet G R : Set (Sym2 V)) p := by
  intro a b p
  induction p with
  | nil => intro _ _ _; exact isOpenIn_nil
  | @cons a b c hab q ih =>
      intro hp ha hb
      rw [isOpenIn_cons] at hp ⊢
      have hbR : b ∈ R := by
        by_contra hb'
        exact hcl ha hb' hab (by
          rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj]
          exact ⟨⟨⟨s(a, b), hab⟩, hp.1.2, rfl⟩, G.ne_of_adj hab⟩)
      have hedge : s(a, b) ∈ (interiorEdgeSet G R : Set (Sym2 V)) := by
        refine ⟨⟨s(a, b), hab⟩, ?_, rfl⟩
        intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hbR
      exact ⟨⟨hedge, hp.1.2⟩, ih hp.2 hbR hb⟩

/-! ## The two factors of the stratum -/

/-- The exterior condition: every labelled edge crossing the frontier of `R` is
closed.  This is the paper's `ω|∂R = 0`, read in the exterior coordinate. -/
def frontierSet (η : (regionBoxOf (G := G) R hR).Exterior) : Prop :=
  ∀ e : G.edgeSet, (∃ x ∈ (e.1 : Sym2 V), x ∈ R) →
    (∃ x ∈ (e.1 : Sym2 V), x ∉ R) → extendExterior (G := G) R hR η e = false

/-- The interior condition: every vertex of `R` is open-connected to the base
`T` using only interior edges of `R`. -/
def interiorConnects (T : Set V) (i : (regionBoxOf (G := G) R hR).Interior) : Prop :=
  ∀ x ∈ R, ∃ t ∈ T,
    OpenConnected G (extendInterior (G := G) R hR i) (interiorEdgeSet G R : Set (Sym2 V)) x t

theorem frontierSet_iff_glue
    (z : (regionBoxOf (G := G) R hR).Exterior × (regionBoxOf (G := G) R hR).Interior) :
    frontierSet (G := G) R hR z.1 ↔
      ∀ e : G.edgeSet, (∃ x ∈ (e.1 : Sym2 V), x ∈ R) →
        (∃ x ∈ (e.1 : Sym2 V), x ∉ R) → (regionBoxOf (G := G) R hR).glue z e = false := by
  constructor
  · intro h e hin hout
    have he := not_mem_regionBox_edges_of_crossing (G := G) R hR hout
    rw [glue_eq_extendExterior (G := G) R hR z he]
    exact h e hin hout
  · intro h e hin hout
    have he := not_mem_regionBox_edges_of_crossing (G := G) R hR hout
    rw [← glue_eq_extendExterior (G := G) R hR z he]
    exact h e hin hout

theorem interiorConnects_iff_glue (T : Set V)
    (z : (regionBoxOf (G := G) R hR).Exterior × (regionBoxOf (G := G) R hR).Interior) :
    interiorConnects (G := G) R hR T z.2 ↔
      ∀ x ∈ R, ∃ t ∈ T, OpenConnected G ((regionBoxOf (G := G) R hR).glue z)
        (interiorEdgeSet G R : Set (Sym2 V)) x t := by
  have hagree : ∀ (e : G.edgeSet), e ∈ interiorEdgeSet G R →
      (regionBoxOf (G := G) R hR).glue z e = extendInterior (G := G) R hR z.2 e :=
    fun e he => glue_eq_extendInterior (G := G) R hR z
      ((mem_regionBox_edges_iff (G := G) R hR).mpr he)
  constructor
  · intro h x hx
    obtain ⟨t, ht, hxt⟩ := h x hx
    exact ⟨t, ht, hxt.congr (fun e he => (hagree e
      ((mem_coe_interiorEdgeSet (G := G) R).mp he)).symm)⟩
  · intro h x hx
    obtain ⟨t, ht, hxt⟩ := h x hx
    exact ⟨t, ht, hxt.congr (fun e he => hagree e
      ((mem_coe_interiorEdgeSet (G := G) R).mp he))⟩

variable {R hR}

/-- **Stratum factorisation.**  For a finite region `R` containing the base `T`,
the glued configuration has closed region exactly `R` iff the exterior has all
frontier edges closed and the interior connects every vertex of `R` to `T`. -/
theorem region_eq_iff {T : Set V}
    (z : (regionBoxOf (G := G) R hR).Exterior × (regionBoxOf (G := G) R hR).Interior)
    (hTR : T ⊆ R) :
    region G ((regionBoxOf (G := G) R hR).glue z) T = R ↔
      frontierSet (G := G) R hR z.1 ∧ interiorConnects (G := G) R hR T z.2 := by
  have hfront := frontierSet_iff_glue (G := G) R hR z
  have hconn := interiorConnects_iff_glue (G := G) R hR T z
  constructor
  · intro hreg
    have hcl : ClosedBoundary G (openSubgraph G ((regionBoxOf (G := G) R hR).glue z)) R := by
      have h := region_closedBoundary (G := G) (ω := (regionBoxOf (G := G) R hR).glue z) T
      rwa [hreg] at h
    refine ⟨hfront.mpr ?_, hconn.mpr ?_⟩
    · -- frontier closed
      intro e hin hout
      exact frontier_closed hcl hin hout
    · -- interior connections
      intro x hx
      have hxreg : x ∈ region G ((regionBoxOf (G := G) R hR).glue z) T := by
        rw [hreg]; exact hx
      rw [mem_region_iff] at hxreg
      obtain ⟨t, ht, htx⟩ := hxreg
      obtain ⟨p, hp⟩ := openConnected_symm htx
      have htR : t ∈ R := by
        have h := subset_region (G := G) (ω := (regionBoxOf (G := G) R hR).glue z) T ht
        rwa [hreg] at h
      exact ⟨t, ht, ⟨p, isOpenIn_interiorEdgeSet (G := G) (R := R) hcl hp hx htR⟩⟩
  · rintro ⟨hf, hc⟩
    apply Set.Subset.antisymm
    · exact region_minimal hTR
        (closedBoundary_of_forall_frontier_false (hfront.mp hf))
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := (hconn.mp hc) x hx
      rw [mem_region_iff]
      exact ⟨t, ht, openConnected_symm (hxt.mono_edges (Set.subset_univ _))⟩

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.extendInterior
#print axioms FK.RandomClosedBoundary.extendInterior_apply_of_mem
#print axioms FK.RandomClosedBoundary.extendExterior_apply_of_notMem
#print axioms FK.RandomClosedBoundary.mem_regionBox_edges_iff
#print axioms FK.RandomClosedBoundary.not_mem_regionBox_edges_of_crossing
#print axioms FK.RandomClosedBoundary.mem_coe_interiorEdgeSet
#print axioms FK.RandomClosedBoundary.glue_eq_extendInterior
#print axioms FK.RandomClosedBoundary.glue_eq_extendExterior
#print axioms FK.RandomClosedBoundary.isOpenIn_interiorEdgeSet
#print axioms FK.RandomClosedBoundary.frontierSet
#print axioms FK.RandomClosedBoundary.interiorConnects
#print axioms FK.RandomClosedBoundary.frontierSet_iff_glue
#print axioms FK.RandomClosedBoundary.interiorConnects_iff_glue
#print axioms FK.RandomClosedBoundary.region_eq_iff

end FK.RandomClosedBoundary
