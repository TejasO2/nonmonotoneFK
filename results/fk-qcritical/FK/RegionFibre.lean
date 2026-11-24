/-
# Measurability of the random-region stratum and of its exterior partition

Second piece of the random-region DLR fibre identity.  The actual exterior-induced
boundary partition `exteriorPartition` is measurable, so the finite FK kernel is
genuinely defined with it; the two factors of the region stratum are measurable in
their own coordinates; and on the frontier-closed factor the FK kernel *is* the free
FK measure on the region box.
-/

import FK.RegionStrata

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V}

/-- Boundary partitions carry the discrete measurable structure (local copy of
the instance in `FK.InfiniteVolume`). -/
local instance boundaryPartitionMeasurableSpaceLocal (X : Type*) :
    MeasurableSpace (Setoid X) := ⊤

/-- There are finitely many setoids on a finite type (local copy of the instance
used in `FK.InfiniteVolume`). -/
local instance finiteSetoidLocal (X : Type*) [Finite X] : Finite (Setoid X) := by
  classical
  apply Finite.of_injective (fun α : Setoid X ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

variable [G.LocallyFinite] (R : Set V) (hR : R.Finite)

/-! ## Measurability of the two extensions -/

theorem extendExterior_apply_of_mem {η : (regionBoxOf (G := G) R hR).Exterior}
    {e : G.edgeSet} (he : e ∈ (regionBoxOf (G := G) R hR).edges) :
    extendExterior (G := G) R hR η e = false := by
  classical
  show (if h : e ∈ (regionBoxOf (G := G) R hR).edges then false else η ⟨e, h⟩) = false
  rw [dif_pos he]

theorem measurable_extendExterior : Measurable (extendExterior (G := G) R hR) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ (regionBoxOf (G := G) R hR).edges
  · have h : (fun η : (regionBoxOf (G := G) R hR).Exterior =>
        extendExterior (G := G) R hR η e) = fun _ => false := by
      funext η
      exact extendExterior_apply_of_mem (G := G) R hR he
    rw [h]
    exact measurable_const
  · have h : (fun η : (regionBoxOf (G := G) R hR).Exterior =>
        extendExterior (G := G) R hR η e) = fun η => η ⟨e, he⟩ := by
      funext η
      exact extendExterior_apply_of_notMem (G := G) R hR he
    rw [h]
    exact measurable_pi_apply _

theorem measurable_extendInterior : Measurable (extendInterior (G := G) R hR) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ (regionBoxOf (G := G) R hR).edges
  · have h : (fun i : (regionBoxOf (G := G) R hR).Interior =>
        extendInterior (G := G) R hR i e) = fun i => i ⟨e, he⟩ := by
      funext i
      exact extendInterior_apply_of_mem (G := G) R hR he
    rw [h]
    exact measurable_pi_apply _
  · have h : (fun i : (regionBoxOf (G := G) R hR).Interior =>
        extendInterior (G := G) R hR i e) = fun _ => false := by
      funext i
      show (if h : e ∈ (regionBoxOf (G := G) R hR).edges then i ⟨e, h⟩ else false) = false
      rw [dif_neg he]
    rw [h]
    exact measurable_const

/-! ## Measurability of the frontier-closed factor -/

theorem measurableSet_frontierSet [Countable V] :
    MeasurableSet {η : (regionBoxOf (G := G) R hR).Exterior |
      frontierSet (G := G) R hR η} := by
  classical
  have hset : {η : (regionBoxOf (G := G) R hR).Exterior | frontierSet (G := G) R hR η} =
      ⋂ (e : G.edgeSet), {η | (∃ x ∈ (e.1 : Sym2 V), x ∈ R) →
        (∃ x ∈ (e.1 : Sym2 V), x ∉ R) →
          extendExterior (G := G) R hR η e = false} := by
    ext η
    simp only [frontierSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  apply MeasurableSet.iInter
  intro e
  by_cases hin : ∃ x ∈ (e.1 : Sym2 V), x ∈ R
  · by_cases hout : ∃ x ∈ (e.1 : Sym2 V), x ∉ R
    · have h : {η : (regionBoxOf (G := G) R hR).Exterior |
          (∃ x ∈ (e.1 : Sym2 V), x ∈ R) → (∃ x ∈ (e.1 : Sym2 V), x ∉ R) →
            extendExterior (G := G) R hR η e = false} =
          {η | extendExterior (G := G) R hR η e = false} := by
        ext η
        simp only [Set.mem_setOf_eq, hin, hout, true_implies]
      rw [h]
      exact measurable_extendExterior (G := G) R hR
        (measurable_pi_apply e (measurableSet_singleton false))
    · have h : {η : (regionBoxOf (G := G) R hR).Exterior |
          (∃ x ∈ (e.1 : Sym2 V), x ∈ R) → (∃ x ∈ (e.1 : Sym2 V), x ∉ R) →
            extendExterior (G := G) R hR η e = false} = univ := by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro _ hc
        exact absurd hc hout
      rw [h]
      exact MeasurableSet.univ
  · have h : {η : (regionBoxOf (G := G) R hR).Exterior |
        (∃ x ∈ (e.1 : Sym2 V), x ∈ R) → (∃ x ∈ (e.1 : Sym2 V), x ∉ R) →
          extendExterior (G := G) R hR η e = false} = univ := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro hc _
      exact absurd hc hin
    rw [h]
    exact MeasurableSet.univ

/-! ## Measurability of the interior-connection factor -/

theorem measurableSet_interiorConnects (T : Set V) :
    MeasurableSet {i : (regionBoxOf (G := G) R hR).Interior |
      interiorConnects (G := G) R hR T i} :=
  Set.Finite.measurableSet (Set.toFinite _)

/-! ## Measurability of the actual exterior-induced boundary partition -/

theorem measurableSet_exteriorPartition_fibre [Countable V]
    (α : (regionBoxOf (G := G) R hR).BoundaryPartition) :
    MeasurableSet {η : (regionBoxOf (G := G) R hR).Exterior |
      exteriorPartition (G := G) R hR η = α} := by
  classical
  have hset : {η : (regionBoxOf (G := G) R hR).Exterior |
        exteriorPartition (G := G) R hR η = α} =
      ⋂ (x : ↥R) (y : ↥R),
        {η | OpenConnected G (extendExterior (G := G) R hR η) (nonInteriorEdges R)
          (x : V) (y : V) ↔ α.r x y} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro rfl x y
      exact Iff.rfl
    · intro h
      exact Setoid.ext fun x y => h x y
  rw [hset]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  by_cases hxy : α.r x y
  · have h : {η : (regionBoxOf (G := G) R hR).Exterior |
        OpenConnected G (extendExterior (G := G) R hR η) (nonInteriorEdges R)
          (x : V) (y : V) ↔ α.r x y} =
        {η | OpenConnected G (extendExterior (G := G) R hR η) (nonInteriorEdges R)
          (x : V) (y : V)} := by
      ext η
      simp only [Set.mem_setOf_eq, hxy, iff_true]
    rw [h]
    exact measurable_extendExterior (G := G) R hR
      (measurableSet_openConnected (nonInteriorEdges R) (x : V) (y : V))
  · have h : {η : (regionBoxOf (G := G) R hR).Exterior |
        OpenConnected G (extendExterior (G := G) R hR η) (nonInteriorEdges R)
          (x : V) (y : V) ↔ α.r x y} =
        {η | OpenConnected G (extendExterior (G := G) R hR η) (nonInteriorEdges R)
          (x : V) (y : V)}ᶜ := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, hxy, iff_false]
    rw [h]
    exact (measurable_extendExterior (G := G) R hR
      (measurableSet_openConnected (nonInteriorEdges R) (x : V) (y : V))).compl

/-- **The exterior-induced boundary partition is measurable.**  This is the
regularity input that `FK.InfiniteVolume.FiniteBox.IsDLR` requires, and it is
what allows the finite FK kernel to be instantiated with the *actual* boundary
condition of the random closed region. -/
theorem measurable_exteriorPartition [Countable V] :
    Measurable (exteriorPartition (G := G) R hR) := by
  intro s _
  rw [show exteriorPartition (G := G) R hR ⁻¹' s =
      ⋃ α ∈ s, {η | exteriorPartition (G := G) R hR η = α} from by
    ext η
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨i, hi, he⟩ => he ▸ hi⟩]
  exact MeasurableSet.biUnion (Set.to_countable s)
    (fun α _ => measurableSet_exteriorPartition_fibre (G := G) R hR α)

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.extendExterior_apply_of_mem
#print axioms FK.RandomClosedBoundary.measurable_extendExterior
#print axioms FK.RandomClosedBoundary.measurable_extendInterior
#print axioms FK.RandomClosedBoundary.measurableSet_frontierSet
#print axioms FK.RandomClosedBoundary.measurableSet_interiorConnects
#print axioms FK.RandomClosedBoundary.measurableSet_exteriorPartition_fibre
#print axioms FK.RandomClosedBoundary.measurable_exteriorPartition

end FK.RandomClosedBoundary
