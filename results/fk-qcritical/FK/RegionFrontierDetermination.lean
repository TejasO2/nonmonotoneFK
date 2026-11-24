import FK.RegionFibreIdentity
import FK.RandomRegionKernel
import FK.SpecificationDeviation

/-!
# Determination of a random-region DLR law by its frontier-closed masses

Worker package of member `m3`, swarm `smwv2h7r6`, for arXiv:2512.16486v1
(Beffara--Faipeur--Oke), Theorem 5.1.

## Mathematical content

Let `G` be a connected locally finite graph and let `μ` be a probability law on
`{0,1}^{E(G)}` satisfying the DLR equation at the *region box* of every finite
vertex region `R ⊆ V`, with the boundary partition induced by the exterior
configuration (`exteriorPartition`).  Assume moreover that the random closed
region `region G ω T` is `μ`-almost surely finite (which holds as soon as `μ`
is non-percolating).

Then:

* `region_stratum_mass` — the mass of the stratum
  `{ω | region G ω T = R}` is the product of

    - `μ(∂R closed)` (the exterior mass of the frontier-closed event), and
    - the free finite-volume FK mass of "every vertex of `R` is connected to
      the base `T` inside `R`";

* `apply_eq_tsum_stratum` — for every event `A` supported in a finite edge set
  and every base `T` containing its endpoints,

    `μ(A) = ∑_R free_R(A ∩ connect_R) · μ(∂R closed)`;

* `eq_of_forall_frontier_mass_eq` — consequently `μ` is **determined** by the
  single numerical family `R ↦ μ(∂R closed)`.

This isolates the exact remaining obligation of Theorem 5.1 in the random-region
route: two Gibbs laws for the same specification coincide as soon as they give
the same mass to the decreasing events "the boundary of `R` is closed", for every
finite region `R`.  The `tsum` formula also shows why the route cannot give
uniqueness by itself: the frontier-closed masses are law-dependent (see
`REPORT.md`, §2.2).
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace FK.M3

variable {V : Type*} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- **Stratum mass identity.**  On the stratum of the random closed region `R`,
the exterior is the frontier-restricted exterior marginal and the interior is the
free FK measure cut down to the interior connection event; taking both factors
whole gives the mass of the stratum. -/
theorem region_stratum_mass {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (R : Set V) (hR : R.Finite)
    (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet))
    (hμ : (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).IsDLR hq hp
      (FK.RandomClosedBoundary.exteriorPartition (G := G) R hR)
      (FK.RandomClosedBoundary.measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R) :
    (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
        {ω | FK.RandomClosedBoundary.region G ω T = R} =
      ((FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).exteriorMeasure μ :
          Measure (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).Exterior)
          (FK.RandomClosedBoundary.frontierExterior (G := G) R hR) *
        (FK.RandomClosedBoundary.regionFreeMeasure (G := G) R hR hq hp)
          (FK.RandomClosedBoundary.interiorConnectSet (G := G) R hR T) := by
  have h := FK.RandomClosedBoundary.region_stratum_rect (G := G) R hR hq hp μ hμ hTR
    (U := Set.univ) (W := Set.univ) MeasurableSet.univ MeasurableSet.univ
  simpa only [Set.univ_prod_univ, Set.preimage_univ, Set.inter_univ, Set.univ_inter] using h

/-- The strata of the random closed region are pairwise disjoint and, on the
almost-sure finiteness event, cover the space.  Hence the mass of any measurable
event is the sum of its masses on the strata. -/
theorem apply_eq_tsum_stratum {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V)
    (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet))
    (hfin : ∀ᵐ ω ∂(μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)),
      (FK.RandomClosedBoundary.region G ω T).Finite)
    {A : Set (FK.InfiniteVolume.Configuration G.edgeSet)} (hA : MeasurableSet A) :
    (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)) A =
      ∑' s : Finset V, (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
        (A ∩ {ω | FK.RandomClosedBoundary.region G ω T = (s : Set V)}) := by
  classical
  have hnull : (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
      {ω | (FK.RandomClosedBoundary.region G ω T).Finite}ᶜ = 0 :=
    MeasureTheory.mem_ae_iff.mp hfin
  have hstep : (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)) A =
      (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
        (A ∩ {ω | (FK.RandomClosedBoundary.region G ω T).Finite}) := by
    refine le_antisymm ?_ (measure_mono Set.inter_subset_left)
    calc (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)) A
        ≤ (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
            ((A ∩ {ω | (FK.RandomClosedBoundary.region G ω T).Finite}) ∪
              {ω | (FK.RandomClosedBoundary.region G ω T).Finite}ᶜ) :=
          measure_mono (by
            intro x hx
            by_cases h : x ∈ {ω | (FK.RandomClosedBoundary.region G ω T).Finite}
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr h)
      _ ≤ (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
            (A ∩ {ω | (FK.RandomClosedBoundary.region G ω T).Finite}) +
          (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
            {ω | (FK.RandomClosedBoundary.region G ω T).Finite}ᶜ :=
          measure_union_le _ _
      _ = (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
            (A ∩ {ω | (FK.RandomClosedBoundary.region G ω T).Finite}) := by
          rw [hnull, add_zero]
  rw [hstep]
  have hset : A ∩ {ω | (FK.RandomClosedBoundary.region G ω T).Finite} =
      ⋃ s : Finset V, (A ∩ {ω | FK.RandomClosedBoundary.region G ω T = (s : Set V)}) := by
    rw [FK.RandomRegionKernel.region_finite_eq_iUnion (G := G) T, Set.inter_iUnion]
  rw [hset, MeasureTheory.measure_iUnion]
  · -- pairwise disjointness of the strata
    intro s t hst
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨-, hx⟩ ⟨-, hy⟩
    exact hst (Finset.coe_injective (by rw [← hx, ← hy]))
  · intro s
    exact hA.inter (FK.RandomClosedBoundary.measurableSet_region_eq (G := G) T (s : Set V))

/-- On a single stratum, an event supported in the interior of the region box has
the product mass of the frontier-restricted exterior marginal and the free FK
mass of its interior readout intersected with the interior connection event. -/
theorem stratum_apply_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (s : Finset V) {T : Set V} (hTs : T ⊆ (s : Set V))
    (μ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet))
    (hμ : (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).IsDLR
      hq hp (FK.RandomClosedBoundary.exteriorPartition (G := G) (s : Set V) s.finite_toSet)
      (FK.RandomClosedBoundary.measurable_exteriorPartition (G := G) (s : Set V) s.finite_toSet) μ)
    {A : Set (FK.InfiniteVolume.Configuration G.edgeSet)}
    (hA : FKLimit.DependsOnCoordinates A
      (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).edges) :
    (μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet))
        (A ∩ {ω | FK.RandomClosedBoundary.region G ω T = (s : Set V)}) =
      ((FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
          Measure (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
          (FK.RandomClosedBoundary.frontierExterior (G := G) (s : Set V) s.finite_toSet) *
        (FK.RandomClosedBoundary.regionFreeMeasure (G := G) (s : Set V) s.finite_toSet hq hp)
          ((FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).interiorRestriction '' A ∩
            FK.RandomClosedBoundary.interiorConnectSet (G := G) (s : Set V) s.finite_toSet T) := by
  classical
  set Aint : Set (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).Interior :=
    (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).interiorRestriction '' A
    with hAint
  have hAeq : A = (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).splitEquiv ⁻¹'
      (Set.univ ×ˢ Aint) := by
    rw [hAint]
    conv_lhs => rw [(FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).eq_preimage_interiorRestriction_image hA]
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rfl
  have h := FK.RandomClosedBoundary.region_stratum_rect (G := G) ((s : Set V)) s.finite_toSet hq hp μ hμ hTs
    (U := Set.univ) (W := Aint) MeasurableSet.univ MeasurableSet.of_discrete
  have hset : A ∩ {ω | FK.RandomClosedBoundary.region G ω T = (s : Set V)} =
      {ω | FK.RandomClosedBoundary.region G ω T = (s : Set V)} ∩
        (FK.RandomClosedBoundary.regionBoxOf (G := G) (s : Set V) s.finite_toSet).splitEquiv ⁻¹'
          (Set.univ ×ˢ Aint) := by
    rw [hAeq, Set.inter_comm]
  rw [hset]
  simpa only [Set.univ_inter] using h

/-- The two-element vertex set of a labelled edge is finite. -/
theorem finite_mem_sym2 (s : Sym2 V) : {x : V | x ∈ s}.Finite := by
  induction s using Sym2.ind with
  | h a b =>
    have hset : {x : V | x ∈ s(a, b)} = ({a, b} : Set V) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [Sym2.mem_iff]
    rw [hset]
    exact (Set.toFinite _)

/-- **Determination by frontier-closed masses.**

Let `μ` and `ν` be two probability laws that satisfy the DLR equation at the
region box of *every* finite vertex region with the exterior-induced boundary
partition (the paper's equation (5) for the geometric convention), and assume
the random closed region based at any finite vertex set is almost surely finite
for both.  If `μ` and `ν` give the same mass to the decreasing event "the
frontier of `R` is closed" for every finite region `R`, then `μ = ν`.

The proof sums the exact stratum identities over the countable family of finite
regions: on the stratum `{region = R}` an event supported in the region's
interior has mass `φ⁰_R(A ∩ connect_R) · μ(∂R closed)`, and the free factor does
not depend on the law. -/
theorem eq_of_forall_frontier_mass_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet))
    (hμ : ∀ (R : Set V) (hR : R.Finite),
      (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).IsDLR hq hp
        (FK.RandomClosedBoundary.exteriorPartition (G := G) R hR)
        (FK.RandomClosedBoundary.measurable_exteriorPartition (G := G) R hR) μ)
    (hν : ∀ (R : Set V) (hR : R.Finite),
      (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).IsDLR hq hp
        (FK.RandomClosedBoundary.exteriorPartition (G := G) R hR)
        (FK.RandomClosedBoundary.measurable_exteriorPartition (G := G) R hR) ν)
    (hμfin : ∀ T : Set V, ∀ᵐ ω ∂(μ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)),
      (FK.RandomClosedBoundary.region G ω T).Finite)
    (hνfin : ∀ T : Set V, ∀ᵐ ω ∂(ν : Measure (FK.InfiniteVolume.Configuration G.edgeSet)),
      (FK.RandomClosedBoundary.region G ω T).Finite)
    (hmass : ∀ (R : Set V) (hR : R.Finite),
      ((FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).exteriorMeasure μ :
          Measure (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).Exterior)
          (FK.RandomClosedBoundary.frontierExterior (G := G) R hR) =
        ((FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).exteriorMeasure ν :
          Measure (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).Exterior)
          (FK.RandomClosedBoundary.frontierExterior (G := G) R hR)) :
    μ = ν := by
  classical
  refine ProbabilityMeasure.toMeasure_injective
    (FK.InfiniteVolume.measure_eq_of_forall_dependsOn (fun F A hA => ?_))
  -- the finite vertex set spanned by the support of `A`
  set T : Set V := {x : V | ∃ e ∈ F, x ∈ (e.1 : Sym2 V)} with hTdef
  have hTfin : T.Finite := by
    refine Set.Finite.subset (F.finite_toSet.biUnion fun e _ => finite_mem_sym2 (V := V) e.1) ?_
    rintro x ⟨e, he, hx⟩
    exact Set.mem_biUnion he hx
  have hFsub : ∀ e ∈ F, e ∈ FK.RandomClosedBoundary.interiorEdgeSet G T := by
    intro e he
    rw [FK.RandomClosedBoundary.mem_interiorEdgeSet_iff]
    exact fun x hx => ⟨e, he, hx⟩
  -- the law-dependent summand
  let term : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet) → Finset V → ℝ≥0∞ :=
    fun κ s =>
      if h : T ⊆ (s : Set V) then
        ((FK.RandomClosedBoundary.regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).exteriorMeasure κ :
            Measure (FK.RandomClosedBoundary.regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).Exterior)
            (FK.RandomClosedBoundary.frontierExterior (G := G) ((s : Set V)) s.finite_toSet) *
          (FK.RandomClosedBoundary.regionFreeMeasure (G := G) ((s : Set V)) s.finite_toSet hq hp)
            ((FK.RandomClosedBoundary.regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).interiorRestriction '' A ∩
              FK.RandomClosedBoundary.interiorConnectSet (G := G) ((s : Set V)) s.finite_toSet T)
      else 0
  have hterm : ∀ (κ : ProbabilityMeasure (FK.InfiniteVolume.Configuration G.edgeSet)),
      (∀ (R : Set V) (hR : R.Finite),
        (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).IsDLR hq hp
          (FK.RandomClosedBoundary.exteriorPartition (G := G) R hR)
          (FK.RandomClosedBoundary.measurable_exteriorPartition (G := G) R hR) κ) →
      (∀ᵐ ω ∂(κ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)),
        (FK.RandomClosedBoundary.region G ω T).Finite) →
      (κ : Measure (FK.InfiniteVolume.Configuration G.edgeSet)) A = ∑' s, term κ s := by
    intro κ hκ hκfin
    rw [apply_eq_tsum_stratum hq hp T κ hκfin hA.measurableSet]
    refine tsum_congr fun s => ?_
    by_cases h : T ⊆ (s : Set V)
    · have hFs : F ⊆ (FK.RandomClosedBoundary.regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).edges := by
        intro e he
        rw [FK.RandomClosedBoundary.mem_regionBox_edges_iff,
          FK.RandomClosedBoundary.mem_interiorEdgeSet_iff]
        exact fun x hx => h (hFsub e he x hx)
      simp only [term, dif_pos h]
      exact stratum_apply_eq hq hp s h κ (hκ _ _) (hA.mono hFs)
    · have hempty : {ω | FK.RandomClosedBoundary.region G ω T = (s : Set V)} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hreg
        exact h (hreg ▸ FK.RandomClosedBoundary.subset_region T)
      simp only [term, dif_neg h]
      rw [hempty, Set.inter_empty, measure_empty]
  rw [hterm μ hμ (hμfin T), hterm ν hν (hνfin T)]
  congr 1
  funext s
  by_cases h : T ⊆ (s : Set V)
  · simp only [term, dif_pos h]
    rw [hmass]
  · simp only [term, dif_neg h]

end FK.M3

/-! ## Axiom audit -/

#print axioms FK.M3.region_stratum_mass
#print axioms FK.M3.apply_eq_tsum_stratum
#print axioms FK.M3.stratum_apply_eq
#print axioms FK.M3.stratum_apply_eq
#print axioms FK.M3.finite_mem_sym2
#print axioms FK.M3.eq_of_forall_frontier_mass_eq
