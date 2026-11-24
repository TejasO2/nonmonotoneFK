/-
# The free-interior correction is necessary

The paper's step "on a closed-boundary region the conditional law in the interior
is the free FK measure" cannot be read as: *conditioning on the value of the random
closed region*, the interior is free FK.  Conditioning on the region stratum also
forces the interior connection event — every vertex of the region must be
open-connected to the base inside the region — and that event has free FK mass
strictly below one as soon as the region has a vertex outside the base.

This file makes that obstruction exact: for a region `R` with a vertex `x ∉ T`,
the all-closed interior configuration has positive free FK mass but lies outside
the connection event, so its stratum probability is exactly `0` while the naive
"free FK on the stratum" prediction is strictly positive.
-/

import FK.RegionFibreIdentity

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (R : Set V) (hR : R.Finite)

/-- The interior configuration with every interior edge closed. -/
def allClosedInterior : (regionBoxOf (G := G) R hR).Interior := fun _ => false

variable [Countable V]

/-- Closing all interior edges closes the whole ambient configuration restricted
to the box. -/
theorem extendInterior_allClosedInterior :
    extendInterior (G := G) R hR (allClosedInterior (G := G) R hR) = fun _ => false := by
  classical
  funext e
  by_cases he : e ∈ (regionBoxOf (G := G) R hR).edges
  · rw [extendInterior_apply_of_mem (G := G) R hR he]
    rfl
  · show (if h : e ∈ (regionBoxOf (G := G) R hR).edges then
      (fun _ => false : (regionBoxOf (G := G) R hR).Interior) ⟨e, h⟩ else false) = false
    rw [dif_neg he]

/-- The all-closed interior configuration does not connect a vertex outside the
base to the base. -/
theorem not_interiorConnects_allClosedInterior {T : Set V} (hT : T.Nonempty)
    {x : V} (hxR : x ∈ R) (hxT : x ∉ T) :
    ¬ interiorConnects (G := G) R hR T (allClosedInterior (G := G) R hR) := by
  intro h
  obtain ⟨t, ht, ⟨p, hp⟩⟩ := h x hxR
  rw [extendInterior_allClosedInterior (G := G) R hR] at hp
  cases p with
  | nil => exact hxT ht
  | cons hab q =>
      rw [isOpenIn_cons] at hp
      simp at hp

/-- The free FK mass of the all-closed interior configuration is positive for
interior parameters. -/
theorem regionFreeMeasure_allClosedInterior_ne_zero {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    regionFreeMeasure (G := G) R hR hq hp
        {allClosedInterior (G := G) R hR} ≠ 0 := by
  have h := FK.Finite.LabelledMultigraph.fkPMF_apply
    (G := (regionBoxOf (G := G) R hR).graph) (q := q) (p := p)
    (ξ := (regionBoxOf (G := G) R hR).graph.freeBoundary) hq hp
    (allClosedInterior (G := G) R hR)
  rw [regionFreeMeasure, FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
  rw [h, ENNReal.coe_ne_zero]
  exact div_ne_zero
    (FK.Finite.LabelledMultigraph.fkWeight_pos
      (G := (regionBoxOf (G := G) R hR).graph) (q := q) (p := p)
      (ξ := (regionBoxOf (G := G) R hR).graph.freeBoundary) hq hp0 hp1
      (allClosedInterior (G := G) R hR)).ne'
    (FK.Finite.LabelledMultigraph.partitionFunction_pos
      (G := (regionBoxOf (G := G) R hR).graph) (q := q) (p := p)
      (ξ := (regionBoxOf (G := G) R hR).graph.freeBoundary) hq hp).ne'

/-- The connection event is disjoint from the all-closed interior configuration. -/
theorem interiorConnectSet_inter_allClosedInterior {T : Set V} (hT : T.Nonempty)
    {x : V} (hxR : x ∈ R) (hxT : x ∉ T) :
    interiorConnectSet (G := G) R hR T ∩
        {allClosedInterior (G := G) R hR} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro i ⟨hiI, hiS⟩
  rw [Set.mem_singleton_iff] at hiS
  rw [hiS] at hiI
  exact not_interiorConnects_allClosedInterior (G := G) R hR hT hxR hxT hiI

/-- **The correction is necessary.**  For a region with a vertex outside the
base, and an exterior event of positive stratum mass, the stratum probability of
the all-closed interior configuration is exactly zero, while the naive
"free FK measure on the region stratum" prediction is strictly positive. -/
theorem free_stratum_naive_false {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R) (hT : T.Nonempty) {x : V} (hxR : x ∈ R) (hxT : x ∉ T)
    {U : Set (regionBoxOf (G := G) R hR).Exterior} (hU : MeasurableSet U)
    (hUpos : ((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
      (regionBoxOf (G := G) R hR).Exterior) (U ∩ frontierExterior (G := G) R hR) ≠ 0) :
    (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹'
          (U ×ˢ {allClosedInterior (G := G) R hR})) = 0 ∧
      ((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
          (regionBoxOf (G := G) R hR).Exterior) (U ∩ frontierExterior (G := G) R hR) *
        regionFreeMeasure (G := G) R hR hq hp
          {allClosedInterior (G := G) R hR} ≠ 0 := by
  have hzero : regionFreeMeasure (G := G) R hR hq hp
      ({allClosedInterior (G := G) R hR} ∩
        interiorConnectSet (G := G) R hR T) = 0 := by
    rw [Set.inter_comm, interiorConnectSet_inter_allClosedInterior (G := G) R hR hT hxR hxT,
      measure_empty]
  refine ⟨?_, ?_⟩
  · rw [region_stratum_rect (G := G) R hR hq hp μ hμ hTR hU (MeasurableSet.singleton _), hzero,
      mul_zero]
  · exact (ENNReal.mul_pos hUpos
      (regionFreeMeasure_allClosedInterior_ne_zero (G := G) R hR
        (q := q) (p := p) hq hp hp0 hp1)).ne'

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.extendInterior_allClosedInterior
#print axioms FK.RandomClosedBoundary.not_interiorConnects_allClosedInterior
#print axioms FK.RandomClosedBoundary.regionFreeMeasure_allClosedInterior_ne_zero
#print axioms FK.RandomClosedBoundary.interiorConnectSet_inter_allClosedInterior
#print axioms FK.RandomClosedBoundary.free_stratum_naive_false

end FK.RandomClosedBoundary
