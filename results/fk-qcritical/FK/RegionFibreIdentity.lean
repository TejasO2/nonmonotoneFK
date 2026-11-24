/-
# The random-region DLR fibre identity

Main theorem of direction 2.  Let `μ` be a probability measure on the ambient
configurations that satisfies the DLR equations at the finite box of *every*
finite vertex region `R` with the actual exterior-induced boundary partition
`exteriorPartition R hR`.  Then, for every finite region `R` containing the
exploring base `T`, the law of `μ` on the stratum `{ω | region G ω T = R}` of the
random closed region factors, under `splitEquiv`, into

* the exterior marginal restricted to the frontier-closed configurations, and
* the **free** finite-volume FK measure on the region box, restricted to the
  interior configurations that connect every vertex of `R` to the base.

So the interior law on the random region is the free FK measure, independently of
the exterior configuration, with the only extra conditioning being the interior
connection event forced by the stratum itself.
-/

import FK.RegionFibre

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (R : Set V) (hR : R.Finite)

/-! ## Abstract conditioning computation -/

/-- **The technical core.**  If a Markov kernel `κ` is constantly `ρ` on a
measurable set `F` of the first coordinate, then restricting the composition
product to the rectangle `F ×ˢ I` is the same as replacing `κ` by the constant
kernel built from `ρ` and restricting the first marginal to `F`. -/
theorem compProd_inter_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : ProbabilityTheory.Kernel α β) (ρ : Measure β)
    [SFinite μ] [SFinite ρ] [ProbabilityTheory.IsSFiniteKernel κ]
    (F : Set α) (I : Set β) (hF : MeasurableSet F) (hI : MeasurableSet I)
    (hκ : ∀ a ∈ F, κ a = ρ) {S : Set (α × β)} (hS : MeasurableSet S) :
    (μ ⊗ₘ κ) (S ∩ (F ×ˢ I)) = ((μ.restrict F) ⊗ₘ ProbabilityTheory.Kernel.const α (ρ.restrict I)) S := by
  rw [Measure.compProd_apply (hS.inter (hF.prod hI)), Measure.compProd_apply hS]
  simp only [ProbabilityTheory.Kernel.const_apply]
  rw [← lintegral_indicator hF]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ F
  · rw [Set.indicator_of_mem ha, hκ a ha,
      Measure.restrict_apply (hS.preimage measurable_prodMk_left)]
    congr 1
    ext b
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod]
    constructor
    · rintro ⟨hb, -, hbI⟩
      exact ⟨hb, hbI⟩
    · intro hb
      exact ⟨hb.1, ha, hb.2⟩
  · rw [Set.indicator_of_notMem ha]
    have hempty : Prod.mk a ⁻¹' (S ∩ (F ×ˢ I)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro b ⟨-, hbF, -⟩
      exact ha hbF
    rw [hempty, measure_empty]

/-! ## The FK kernel on the frontier-closed factor is the free measure -/

/-- On the frontier-closed factor, the actual exterior-induced boundary partition
is the free one. -/
theorem exteriorPartition_eq_bot_of_frontierSet {η : (regionBoxOf (G := G) R hR).Exterior}
    (h : frontierSet (G := G) R hR η) :
    exteriorPartition (G := G) R hR η = ⊥ := by
  apply exteriorPartition_eq_bot
  intro e hne hin hout
  rw [← extendExterior_apply_of_notMem (G := G) (R := R) (hR := hR) (η := η) hne]
  exact h e hin hout

/-- On the frontier-closed factor, the DLR kernel at the region box **is** the
free finite-volume FK measure. -/
theorem fkKernel_eq_free_of_frontierSet [Countable V] {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {η : (regionBoxOf (G := G) R hR).Exterior} (h : frontierSet (G := G) R hR η) :
    (regionBoxOf (G := G) R hR).fkKernel hq hp (exteriorPartition (G := G) R hR)
        (measurable_exteriorPartition (G := G) R hR) η =
      (regionBoxOf (G := G) R hR).graph.fkMeasure hq hp
        (regionBoxOf (G := G) R hR).graph.freeBoundary := by
  rw [FK.InfiniteVolume.FiniteBox.fkKernel_apply,
    exteriorPartition_eq_bot_of_frontierSet (G := G) R hR h,
    freeBoundary_eq_bot]

/-! ## The stratum as a product -/

theorem glue_preimage_region_eq {T : Set V} (hTR : T ⊆ R) :
    (regionBoxOf (G := G) R hR).glue ⁻¹' {ω | region G ω T = R} =
      {η : (regionBoxOf (G := G) R hR).Exterior | frontierSet (G := G) R hR η} ×ˢ
        {i : (regionBoxOf (G := G) R hR).Interior | interiorConnects (G := G) R hR T i} := by
  ext z
  rw [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  exact region_eq_iff (G := G) (R := R) (hR := hR) (T := T) z hTR

/-! ## The fibre identity -/

/-- **Random-region DLR fibre identity.**  For a law `μ` satisfying the DLR
equations at every finite region box with the actual exterior-induced boundary
partition, the law of `μ` restricted to the stratum of the random closed region
is the product of the frontier-restricted exterior marginal with the (constant
kernel built from the) *free* finite-volume FK measure, cut down to the interior
connection event of the stratum. -/
theorem map_splitEquiv_restrict_region_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R) :
    Measure.map (regionBoxOf (G := G) R hR).splitEquiv
        ((μ : Measure (FKLimit.Configuration G.edgeSet)).restrict {ω | region G ω T = R})
      = ((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
            (regionBoxOf (G := G) R hR).Exterior).restrict
          {η : (regionBoxOf (G := G) R hR).Exterior | frontierSet (G := G) R hR η}
        ⊗ₘ ProbabilityTheory.Kernel.const _
            (((regionBoxOf (G := G) R hR).graph.fkMeasure hq hp
              (regionBoxOf (G := G) R hR).graph.freeBoundary).restrict
              {i : (regionBoxOf (G := G) R hR).Interior |
                interiorConnects (G := G) R hR T i}) := by
  classical
  have hstr : MeasurableSet {ω : FKLimit.Configuration G.edgeSet | region G ω T = R} :=
    measurableSet_region_eq (G := G) T R
  have hF : MeasurableSet {η : (regionBoxOf (G := G) R hR).Exterior |
      frontierSet (G := G) R hR η} := measurableSet_frontierSet (G := G) R hR
  have hI : MeasurableSet {i : (regionBoxOf (G := G) R hR).Interior |
      interiorConnects (G := G) R hR T i} := measurableSet_interiorConnects (G := G) R hR T
  ext S hS
  rw [Measure.map_apply (regionBoxOf (G := G) R hR).splitEquiv.measurable hS,
    Measure.restrict_apply ((regionBoxOf (G := G) R hR).splitEquiv.measurable hS)]
  rw [FK.InfiniteVolume.FiniteBox.measure_eq_map_glue_compProd (B := regionBoxOf (G := G) R hR) hq hp
    (exteriorPartition (G := G) R hR) (measurable_exteriorPartition (G := G) R hR) μ hμ,
    Measure.map_apply (f := (regionBoxOf (G := G) R hR).glue)
      (regionBoxOf (G := G) R hR).splitEquiv.symm.measurable
      (((regionBoxOf (G := G) R hR).splitEquiv.measurable hS).inter hstr)]
  have hpre : (regionBoxOf (G := G) R hR).glue ⁻¹'
      ((regionBoxOf (G := G) R hR).splitEquiv ⁻¹' S ∩
        {ω : FKLimit.Configuration G.edgeSet | region G ω T = R}) =
      S ∩ ({η : (regionBoxOf (G := G) R hR).Exterior | frontierSet (G := G) R hR η} ×ˢ
        {i : (regionBoxOf (G := G) R hR).Interior | interiorConnects (G := G) R hR T i}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod,
      FK.InfiniteVolume.FiniteBox.splitEquiv_apply, FK.InfiniteVolume.FiniteBox.split_glue]
    rw [region_eq_iff (G := G) (R := R) (hR := hR) (T := T) z hTR]
  rw [hpre]
  exact compProd_inter_prod ((regionBoxOf (G := G) R hR).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) R hR).Exterior)
    ((regionBoxOf (G := G) R hR).fkKernel hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR))
    ((regionBoxOf (G := G) R hR).graph.fkMeasure hq hp
      (regionBoxOf (G := G) R hR).graph.freeBoundary)
    _ _ hF hI (fun η hη => fkKernel_eq_free_of_frontierSet (G := G) R hR hq hp hη) hS


/-! ## Product form of the fibre identity -/

/-- The free interior measure of the region box. -/
noncomputable abbrev regionFreeMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    Measure (regionBoxOf (G := G) R hR).Interior :=
  ((regionBoxOf (G := G) R hR).graph.fkMeasure hq hp
    (regionBoxOf (G := G) R hR).graph.freeBoundary)

/-- The frontier-closed exterior set. -/
def frontierExterior : Set (regionBoxOf (G := G) R hR).Exterior :=
  {η | frontierSet (G := G) R hR η}

/-- The interior connection set. -/
def interiorConnectSet (T : Set V) : Set (regionBoxOf (G := G) R hR).Interior :=
  {i | interiorConnects (G := G) R hR T i}

/-- **Product form.**  On the stratum of the random closed region, the exterior
and the interior configurations are *independent*, the exterior is the exterior
marginal cut down to the frontier-closed configurations, and the interior is the
free finite-volume FK measure cut down to the interior connection event. -/
theorem map_splitEquiv_restrict_region_eq_prod {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R) :
    Measure.map (regionBoxOf (G := G) R hR).splitEquiv
        ((μ : Measure (FKLimit.Configuration G.edgeSet)).restrict {ω | region G ω T = R})
      = (((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
            (regionBoxOf (G := G) R hR).Exterior).restrict (frontierExterior (G := G) R hR)).prod
          ((regionFreeMeasure (G := G) R hR hq hp).restrict
            (interiorConnectSet (G := G) R hR T)) := by
  rw [map_splitEquiv_restrict_region_eq (G := G) R hR hq hp μ hμ hTR,
    Measure.compProd_const]
  rfl

/-- **Rectangle form.**  On the region stratum, the joint probability of an
exterior event `G` and an interior event `A` is the product of the
frontier-restricted exterior mass and the free FK mass of `A` intersected with
the interior connection event. -/
theorem region_stratum_rect {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R)
    {U : Set (regionBoxOf (G := G) R hR).Exterior}
    {W : Set (regionBoxOf (G := G) R hR).Interior}
    (hU : MeasurableSet U) (hW : MeasurableSet W) :
    (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W))
      = ((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
            (regionBoxOf (G := G) R hR).Exterior) (U ∩ frontierExterior (G := G) R hR) *
          (regionFreeMeasure (G := G) R hR hq hp) (W ∩ interiorConnectSet (G := G) R hR T) := by
  classical
  have hmeas := (regionBoxOf (G := G) R hR).splitEquiv.measurable
  have hstr : MeasurableSet {ω : FKLimit.Configuration G.edgeSet | region G ω T = R} :=
    measurableSet_region_eq (G := G) T R
  rw [show {ω : FKLimit.Configuration G.edgeSet | region G ω T = R} ∩
        (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W)
      = (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W) ∩
        {ω : FKLimit.Configuration G.edgeSet | region G ω T = R} from Set.inter_comm _ _,
    ← Measure.restrict_apply (hmeas (hU.prod hW)), ← Measure.map_apply hmeas (hU.prod hW),
    map_splitEquiv_restrict_region_eq_prod (G := G) R hR hq hp μ hμ hTR,
    Measure.prod_prod U W, Measure.restrict_apply hU, Measure.restrict_apply hW]

/-! ## The unconditional free-interior statement -/

/-- **Free interior on the frontier-closed exterior event.**  Regardless of the
random region, conditionally on the exterior configuration being frontier-closed
at `R` the interior configuration of the region box is *free* FK and independent
of the exterior.  This is the paper's step `ω|∂R = 0 ⇒ free random-cluster law in
the interior`, at the level of the infinite-body law. -/
theorem map_splitEquiv_restrict_frontierSet_prod {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ) :
    Measure.map (regionBoxOf (G := G) R hR).splitEquiv
        ((μ : Measure (FKLimit.Configuration G.edgeSet)).restrict
          ((regionBoxOf (G := G) R hR).splitEquiv ⁻¹'
            (frontierExterior (G := G) R hR ×ˢ Set.univ)))
      = (((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
            (regionBoxOf (G := G) R hR).Exterior).restrict (frontierExterior (G := G) R hR)).prod
          (regionFreeMeasure (G := G) R hR hq hp) := by
  classical
  have hmeas := (regionBoxOf (G := G) R hR).splitEquiv.measurable
  have hF : MeasurableSet (frontierExterior (G := G) R hR) :=
    measurableSet_frontierSet (G := G) R hR
  ext S hS
  rw [Measure.map_apply hmeas hS, Measure.restrict_apply (hmeas hS)]
  rw [FK.InfiniteVolume.FiniteBox.measure_eq_map_glue_compProd (B := regionBoxOf (G := G) R hR)
    hq hp (exteriorPartition (G := G) R hR) (measurable_exteriorPartition (G := G) R hR) μ hμ,
    Measure.map_apply (f := (regionBoxOf (G := G) R hR).glue)
      (regionBoxOf (G := G) R hR).splitEquiv.symm.measurable
      ((hmeas hS).inter (hmeas (hF.prod MeasurableSet.univ)))]
  have hpre : (regionBoxOf (G := G) R hR).glue ⁻¹'
      ((regionBoxOf (G := G) R hR).splitEquiv ⁻¹' S ∩
        (regionBoxOf (G := G) R hR).splitEquiv ⁻¹'
          (frontierExterior (G := G) R hR ×ˢ Set.univ)) =
      S ∩ (frontierExterior (G := G) R hR ×ˢ Set.univ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      FK.InfiniteVolume.FiniteBox.splitEquiv_apply, FK.InfiniteVolume.FiniteBox.split_glue,
      Set.mem_prod, Set.mem_univ, and_true]
  rw [hpre, compProd_inter_prod
    ((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
      (regionBoxOf (G := G) R hR).Exterior)
    ((regionBoxOf (G := G) R hR).fkKernel hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR))
    (regionFreeMeasure (G := G) R hR hq hp) _ Set.univ hF MeasurableSet.univ
    (fun η hη => fkKernel_eq_free_of_frontierSet (G := G) R hR hq hp hη) hS,
    Measure.restrict_univ, Measure.compProd_const]


/-! ## The conditional interior kernel does not depend on the law -/

/-- **Conditional form, multiplicatively.**  The conditional probability of an
interior event `W` on the region stratum, given an exterior event `U`, times the
free mass of the connection event `I`, equals the unconditional stratum
probability times the free mass of `W ∩ I`.  No positivity hypothesis is
needed. -/
theorem region_stratum_cond_mul {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R)
    {U : Set (regionBoxOf (G := G) R hR).Exterior}
    {W : Set (regionBoxOf (G := G) R hR).Interior}
    (hU : MeasurableSet U) (hW : MeasurableSet W) :
    (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W)) *
      (regionFreeMeasure (G := G) R hR hq hp) (interiorConnectSet (G := G) R hR T) =
    (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩
          (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ Set.univ)) *
      (regionFreeMeasure (G := G) R hR hq hp) (W ∩ interiorConnectSet (G := G) R hR T) := by
  rw [region_stratum_rect (G := G) R hR hq hp μ hμ hTR hU hW,
    region_stratum_rect (G := G) R hR hq hp μ hμ hTR hU MeasurableSet.univ,
    Set.univ_inter]
  ring

/-- **Conditional form with division.**  When the free mass of the connection
event is a positive real number, the conditional interior probability on the
region stratum is exactly the free FK ratio `free(W ∩ I) / free(I)`, a quantity
independent of the law `μ`. -/
theorem region_stratum_cond {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    {T : Set V} (hTR : T ⊆ R)
    {U : Set (regionBoxOf (G := G) R hR).Exterior}
    {W : Set (regionBoxOf (G := G) R hR).Interior}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hI : (regionFreeMeasure (G := G) R hR hq hp) (interiorConnectSet (G := G) R hR T) ≠ 0)
    (hIt : (regionFreeMeasure (G := G) R hR hq hp)
      (interiorConnectSet (G := G) R hR T) ≠ ⊤) :
    (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W))
      = (μ : Measure (FKLimit.Configuration G.edgeSet))
          ({ω | region G ω T = R} ∩
            (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ Set.univ)) *
        ((regionFreeMeasure (G := G) R hR hq hp)
            (W ∩ interiorConnectSet (G := G) R hR T) *
          ((regionFreeMeasure (G := G) R hR hq hp)
            (interiorConnectSet (G := G) R hR T))⁻¹) := by
  have hmul := region_stratum_cond_mul (G := G) R hR hq hp μ hμ hTR hU hW
  calc (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W))
      = ((μ : Measure (FKLimit.Configuration G.edgeSet))
          ({ω | region G ω T = R} ∩
            (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W)) *
          (regionFreeMeasure (G := G) R hR hq hp)
            (interiorConnectSet (G := G) R hR T)) *
          ((regionFreeMeasure (G := G) R hR hq hp)
            (interiorConnectSet (G := G) R hR T))⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hI hIt, mul_one]
    _ = ((μ : Measure (FKLimit.Configuration G.edgeSet))
          ({ω | region G ω T = R} ∩
            (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ Set.univ)) *
          (regionFreeMeasure (G := G) R hR hq hp)
            (W ∩ interiorConnectSet (G := G) R hR T)) *
          ((regionFreeMeasure (G := G) R hR hq hp)
            (interiorConnectSet (G := G) R hR T))⁻¹ := by
        rw [hmul]
    _ = _ := by rw [mul_assoc]

/-- **Kernel independence.**  Two laws satisfying the region-box DLR equations at
the same parameters induce the *same* conditional interior kernel on the stratum
of the random closed region: cross-multiplying removes the exterior marginal. -/
theorem region_stratum_kernel_independent {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    [Countable V]
    (μ₁ μ₂ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (h₁ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ₁)
    (h₂ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ₂)
    {T : Set V} (hTR : T ⊆ R)
    {U : Set (regionBoxOf (G := G) R hR).Exterior}
    {W : Set (regionBoxOf (G := G) R hR).Interior}
    (hU : MeasurableSet U) (hW : MeasurableSet W) :
    (μ₁ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W)) *
      (μ₂ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩
          (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ Set.univ)) =
    (μ₂ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩ (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W)) *
      (μ₁ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω T = R} ∩
          (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ Set.univ)) := by
  rw [region_stratum_rect (G := G) R hR hq hp μ₁ h₁ hTR hU hW,
    region_stratum_rect (G := G) R hR hq hp μ₁ h₁ hTR hU MeasurableSet.univ,
    region_stratum_rect (G := G) R hR hq hp μ₂ h₂ hTR hU hW,
    region_stratum_rect (G := G) R hR hq hp μ₂ h₂ hTR hU MeasurableSet.univ,
    Set.univ_inter]
  ring

/-! ## Stage form -/

/-- The stage-`n` instance of the rectangle formula: the base is `base n`. -/
theorem region_stratum_rect_stage {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    [Countable V]
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : (regionBoxOf (G := G) R hR).IsDLR hq hp (exteriorPartition (G := G) R hR)
      (measurable_exteriorPartition (G := G) R hR) μ)
    (base : ℕ → Set V) (n : ℕ) (hbase : base n ⊆ R)
    {U : Set (regionBoxOf (G := G) R hR).Exterior}
    {W : Set (regionBoxOf (G := G) R hR).Interior}
    (hU : MeasurableSet U) (hW : MeasurableSet W) :
    (μ : Measure (FKLimit.Configuration G.edgeSet))
        ({ω | region G ω (base n) = R} ∩
          (regionBoxOf (G := G) R hR).splitEquiv ⁻¹' (U ×ˢ W))
      = ((regionBoxOf (G := G) R hR).exteriorMeasure μ : Measure
            (regionBoxOf (G := G) R hR).Exterior) (U ∩ frontierExterior (G := G) R hR) *
          (regionFreeMeasure (G := G) R hR hq hp)
            (W ∩ interiorConnectSet (G := G) R hR (base n)) :=
  region_stratum_rect (G := G) R hR hq hp μ hμ hbase hU hW

/-! ## The dominating configuration's region has a closed labelled frontier -/

/-- Every configuration dominated by `ω'` has all labelled frontier edges of the
random region of `ω'` closed.  This is the labelled form of the source condition
`ωᵢ|∂S_n(ω₃) = 0` in exactly the shape that the fibre identity consumes: it
produces `frontierSet` for the exterior restriction of the dominated coordinate. -/
theorem frontierSet_restrictExterior_of_le {ω ω' : G.edgeSet → Bool} (hω : ω ≤ ω')
    {T : Set V} (hfin : (region G ω' T).Finite) :
    frontierSet (G := G) (region G ω' T) hfin
      (restrictExterior (G := G) (region G ω' T) hfin ω) := by
  intro e hin hout
  have he := not_mem_regionBox_edges_of_crossing (G := G) (region G ω' T) hfin hout
  rw [extendExterior_apply_of_notMem (G := G) (R := region G ω' T) (hR := hfin) he]
  exact frontier_closed (region_closedBoundary_of_le hω T) hin hout

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.compProd_inter_prod
#print axioms FK.RandomClosedBoundary.exteriorPartition_eq_bot_of_frontierSet
#print axioms FK.RandomClosedBoundary.fkKernel_eq_free_of_frontierSet
#print axioms FK.RandomClosedBoundary.glue_preimage_region_eq
#print axioms FK.RandomClosedBoundary.map_splitEquiv_restrict_region_eq
#print axioms FK.RandomClosedBoundary.map_splitEquiv_restrict_region_eq_prod
#print axioms FK.RandomClosedBoundary.region_stratum_rect
#print axioms FK.RandomClosedBoundary.region_stratum_rect_stage
#print axioms FK.RandomClosedBoundary.map_splitEquiv_restrict_frontierSet_prod
#print axioms FK.RandomClosedBoundary.region_stratum_cond_mul
#print axioms FK.RandomClosedBoundary.region_stratum_cond
#print axioms FK.RandomClosedBoundary.region_stratum_kernel_independent
#print axioms FK.RandomClosedBoundary.frontierSet_restrictExterior_of_le

end FK.RandomClosedBoundary
