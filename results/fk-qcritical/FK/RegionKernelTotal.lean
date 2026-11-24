/-
# The total random-region conditional kernel

`FK/RandomRegionKernel.lean` proves the random-region disintegration identity for
events `C` that are *interior-supported* (they only see the configuration inside
the region box) and whose test set is a global cylinder contained in the box.
The source (arXiv:2512.16486v1, proof of Theorem 5.1) needs one conditional law
for the random region valid for an **arbitrary** global measurable event `C`, so
that the conditioning is a genuine regular conditional distribution of `μ` given
`σ(regionField)`.

This file supplies that:

* `predictKernel` is the predicted law of the region box `s` given the exterior
  field `η`: the free FK measure of the box conditioned on the forced interior
  connectivity, pushed to global configurations by the exterior field.  It is a
  genuine Markov kernel in `η`.
* `sliceVal` is its mass on `C`; `mul_sliceVal_eq_freeMass` identifies
  `freeMass (conn) * sliceVal` with the free FK mass of `C`'s interior readout
  intersected with the forced connectivity, and `measurable_sliceVal` is the
  Fubini measurability of `η ↦ sliceVal η`.
* `stratum_lhs` and `stratum_rhs` compute the two sides of the identity on one
  stratum of the random closed region as exterior integrals, and
  `region_kernel_disintegration_total` glues the countably many strata: for every
  measurable `C` and every region-field cylinder `⋃ s, stratumPiece T s (Y s)`,
  the mass of `C` on that set is the integral of the predicted probability.

So, after the fact, `regionFieldKernel T ω = regionKernelFun T (regionField T ω)`
is a version of the conditional law of `μ` given the random region field, for
*every* measurable global event.  Nothing is assumed about the interior of `ω` on
a stratum: the identity says precisely that, given `regionField T ω`, the
interior is distributed as the free FK measure of the region box conditioned on
the forced connectivity.  The infinite-region fibre `regionIdx = none` is absent
from the test sets, and `region_kernel_total_univ` removes that restriction when
the random region is almost surely finite.
-/

import FK.RandomRegionKernel
import FK.Theorem110Assembly

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

open CurvatureVariance.Infra.Percolation
open FK.RandomClosedBoundary

namespace FK.RandomRegionKernel

variable {V : Type*} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-! ## A tool lemma on the conditional probability measure -/

/-- The mass of `s` times the `cond μ s`-integral of `h` is the integral of `h`
over `s`.  This is the algebraic form of "the conditional measure is the
restriction, normalised", in extended nonnegative reals so that no positivity of
`μ s` is needed. -/
theorem mul_lintegral_cond {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (s : Set α) (h : α → ℝ≥0∞) :
    μ s * ∫⁻ x, h x ∂(μ[|s]) = ∫⁻ x in s, h x ∂μ := by
  have hrew : ∫⁻ x, h x ∂(μ[|s]) = (μ s)⁻¹ * ∫⁻ x in s, h x ∂μ := by
    unfold ProbabilityTheory.cond
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [hrew, ← mul_assoc]
  rcases eq_or_ne (μ s) 0 with h0 | h0
  · have hzero : μ.restrict s = 0 := Measure.restrict_eq_zero.mpr h0
    rw [h0, zero_mul]
    simp [hzero]
  · rw [ENNReal.mul_inv_cancel h0 (measure_lt_top μ s).ne, one_mul]

/-- Restricting an integral to a subset of a measurable set. -/
theorem lintegral_of_subset {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P St : Set α} (hP : MeasurableSet P) (hSt : MeasurableSet St) (hsub : P ⊆ St)
    (f : α → ℝ≥0∞) :
    ∫⁻ ω in P, f ω ∂μ = ∫⁻ ω in St, P.indicator f ω ∂μ := by
  rw [← lintegral_indicator hP, ← lintegral_indicator hSt]
  refine lintegral_congr (fun ω => ?_)
  by_cases hω : ω ∈ St
  · rw [Set.indicator_of_mem hω]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (hsub h))]

/-- An indicator integral over a measure restricted to a superset is unchanged. -/
theorem lintegral_indicator_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : Set α} (hA : MeasurableSet A) (hAB : A ⊆ B) (G : α → ℝ≥0∞) :
    ∫⁻ x, A.indicator G x ∂(μ.restrict B) = ∫⁻ x, A.indicator G x ∂μ := by
  rw [lintegral_indicator hA, lintegral_indicator hA]
  have h1 : (μ.restrict B).restrict A = μ.restrict A := by
    rw [Measure.restrict_restrict hA, Set.inter_eq_left.mpr hAB]
  rw [h1]

/-! ## The predicted kernel of a region box -/

/-- **The predicted law of the region box given its exterior field.**  A genuine
Markov kernel: sample the exterior field, sample the interior from the free FK
measure of the box conditioned on the forced interior connectivity, and glue. -/
noncomputable def predictKernel {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (s : Finset V) :
    ProbabilityTheory.Kernel (boxOf (G := G) s).Exterior (G.edgeSet → Bool) :=
  ((ProbabilityTheory.Kernel.deterministic (fun η : (boxOf (G := G) s).Exterior => η)
      measurable_id).prod
    (ProbabilityTheory.Kernel.const (boxOf (G := G) s).Exterior
      ((freeMass (G := G) hq hp s)[|connSet (G := G) T s]))).map
    (fun z : (boxOf (G := G) s).Exterior × (boxOf (G := G) s).Interior =>
      (boxOf (G := G) s).glue z)

/-- The predicted kernel is Markov as soon as the forced connectivity has
positive free mass; on a stratum where it does not, the stratum itself is
`μ`-null and the predicted law is the zero measure. -/
theorem predictKernel_isMarkovKernel {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (s : Finset V)
    (hpos : freeMass (G := G) hq hp s (connSet (G := G) T s) ≠ 0) :
    IsMarkovKernel (predictKernel (G := G) hq hp T s) := by
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI : IsProbabilityMeasure ((freeMass (G := G) hq hp s)[|connSet (G := G) T s]) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  let κ : ProbabilityTheory.Kernel (boxOf (G := G) s).Exterior
      ((boxOf (G := G) s).Exterior × (boxOf (G := G) s).Interior) :=
    (ProbabilityTheory.Kernel.deterministic (fun η : (boxOf (G := G) s).Exterior => η)
      measurable_id).prod
    (ProbabilityTheory.Kernel.const (boxOf (G := G) s).Exterior
      ((freeMass (G := G) hq hp s)[|connSet (G := G) T s]))
  haveI hκ : IsMarkovKernel κ := by
    unfold κ
    infer_instance
  have hmark := ProbabilityTheory.Kernel.IsMarkovKernel.map κ (f := fun z :
    (boxOf (G := G) s).Exterior × (boxOf (G := G) s).Interior => (boxOf (G := G) s).glue z)
    (boxOf (G := G) s).splitEquiv.symm.measurable
  exact hmark

/-- The predicted probability of a global event, written as an integral over the
interior of the box. -/
theorem predictKernel_apply {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (s : Finset V) (η : (boxOf (G := G) s).Exterior) {C : Set (G.edgeSet → Bool)}
    (hC : MeasurableSet C) :
    predictKernel (G := G) hq hp T s η C =
      ∫⁻ i, ({i : (boxOf (G := G) s).Interior |
        (boxOf (G := G) s).glue (η, i) ∈ C}.indicator (1 : (boxOf (G := G) s).Interior → ℝ≥0∞)) i
        ∂((freeMass (G := G) hq hp s)[|connSet (G := G) T s]) := by
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI hfin : IsFiniteMeasure (freeMass (G := G) hq hp s) :=
    ⟨lt_of_le_of_lt (freeMass_le_one (G := G) hq hp s Set.univ) ENNReal.one_lt_top⟩
  have hglue : Measurable (fun z : (boxOf (G := G) s).Exterior × (boxOf (G := G) s).Interior =>
      (boxOf (G := G) s).glue z) := (boxOf (G := G) s).splitEquiv.symm.measurable
  have hX : MeasurableSet {i : (boxOf (G := G) s).Interior |
      (boxOf (G := G) s).glue (η, i) ∈ C} :=
    hC.preimage ((boxOf (G := G) s).measurable_glue_const_left η)
  rw [predictKernel, ProbabilityTheory.Kernel.map_apply _ hglue,
    ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.deterministic_apply,
    ProbabilityTheory.Kernel.const_apply, Measure.map_apply hglue hC, Measure.prod_apply
      (hC.preimage hglue), lintegral_dirac]
  have hset : Prod.mk η ⁻¹' (fun z : (boxOf (G := G) s).Exterior × (boxOf (G := G) s).Interior =>
      (boxOf (G := G) s).glue z) ⁻¹' C = {i : (boxOf (G := G) s).Interior |
        (boxOf (G := G) s).glue (η, i) ∈ C} := rfl
  rw [hset, ← lintegral_indicator_one hX]

/-! ## The predicted probability of an arbitrary global event -/

/-- The predicted probability of the global event `C` in the region box `s` with
exterior field `η`.  Unlike `kernelValue`, this does not require `C` to be
interior-supported. -/
noncomputable def sliceVal {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (C : Set (G.edgeSet → Bool)) (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) : ℝ≥0∞ :=
  ∫⁻ i, ({i : (boxOf (G := G) s).Interior |
      (boxOf (G := G) s).glue (η, i) ∈ C}.indicator (1 : (boxOf (G := G) s).Interior → ℝ≥0∞)) i
    ∂((freeMass (G := G) hq hp s)[|connSet (G := G) T s])

/-- `sliceVal` is the value of the predicted kernel. -/
theorem sliceVal_eq_predictKernel {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) :
    sliceVal (G := G) hq hp T C s η = predictKernel (G := G) hq hp T s η C :=
  (predictKernel_apply (G := G) hq hp T s η hC).symm

/-- The predicted probability is a measurable function of the exterior field. -/
theorem measurable_sliceVal {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) (s : Finset V) :
    Measurable (sliceVal (G := G) hq hp T C s) := by
  have h := ProbabilityTheory.Kernel.measurable_coe (predictKernel (G := G) hq hp T s) hC
  have hfun : sliceVal (G := G) hq hp T C s =
      fun η => predictKernel (G := G) hq hp T s η C :=
    funext (fun η => sliceVal_eq_predictKernel (G := G) hq hp T hC s η)
  rw [hfun]
  exact h

/-- The predicted probability is the free FK mass of `C`'s interior readout
intersected with the forced connectivity, normalised by the free connectivity
mass. -/
theorem mul_sliceVal_eq_freeMass {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) {T : Set V}
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) (s : Finset V)
    (η : (boxOf (G := G) s).Exterior) :
    freeMass (G := G) hq hp s (connSet (G := G) T s) *
        sliceVal (G := G) hq hp T C s η =
      freeMass (G := G) hq hp s
        ({i | (boxOf (G := G) s).glue (η, i) ∈ C} ∩ connSet (G := G) T s) := by
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI hfin : IsFiniteMeasure (freeMass (G := G) hq hp s) :=
    ⟨lt_of_le_of_lt (freeMass_le_one (G := G) hq hp s Set.univ) ENNReal.one_lt_top⟩
  have hX : MeasurableSet {i : (boxOf (G := G) s).Interior |
      (boxOf (G := G) s).glue (η, i) ∈ C} :=
    hC.preimage ((boxOf (G := G) s).measurable_glue_const_left η)
  have hK : MeasurableSet (connSet (G := G) T s) := measurableSet_connSet (G := G) T s
  rw [sliceVal, mul_lintegral_cond, ← lintegral_indicator_one (hX.inter hK),
    ← lintegral_indicator hK]
  refine lintegral_congr (fun i => ?_)
  by_cases hi : i ∈ connSet (G := G) T s <;>
    by_cases hxi : i ∈ {i : (boxOf (G := G) s).Interior | (boxOf (G := G) s).glue (η, i) ∈ C} <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hxi]

/-! ## The two sides of the identity on one stratum -/

/-- **The exterior form of the unconditional mass on one stratum.** -/
theorem stratum_lhs {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    {s : Finset V} (hT : T ⊆ (s : Set V))
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) =
      ∫⁻ η, ((frontSet (G := G) s ∩ extPreimage (G := G) s Y).indicator
          (fun η => freeMass (G := G) hq hp s
            ({i | (boxOf (G := G) s).glue (η, i) ∈ C} ∩ connSet (G := G) T s))) η
        ∂((boxOf (G := G) s).exteriorMeasure μ : Measure (boxOf (G := G) s).Exterior) := by
  classical
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI hfin : IsFiniteMeasure (freeMass (G := G) hq hp s) :=
    ⟨lt_of_le_of_lt (freeMass_le_one (G := G) hq hp s Set.univ) ENNReal.one_lt_top⟩
  set B := boxOf (G := G) s with hB
  set A : Set (G.edgeSet → Bool) := C ∩ stratumPiece (G := G) T s Y with hA
  set A₀ : Set B.Exterior := frontSet (G := G) s ∩ extPreimage (G := G) s Y with hA₀
  set K : Set B.Interior := connSet (G := G) T s with hK
  have hA₀meas : MeasurableSet A₀ :=
    (measurableSet_frontSet (G := G) s).inter (measurableSet_extPreimage (G := G) s hY)
  have hKmeas : MeasurableSet K := measurableSet_connSet (G := G) T s
  have hAmeas : MeasurableSet A := hC.inter (measurableSet_stratumPiece (G := G) T s hY)
  have hP : stratumPiece (G := G) T s Y = B.splitEquiv ⁻¹' (A₀ ×ˢ K) :=
    stratumPiece_eq_split_rect (G := G) T s Y hT
  have hSt : A ⊆ {ω : G.edgeSet → Bool | region G ω T = (s : Set V)} := by
    rintro ω ⟨-, hω⟩
    exact hω.1
  have hmap : Measure.map B.splitEquiv
      ((μ : Measure (G.edgeSet → Bool)).restrict
        {ω : G.edgeSet → Bool | region G ω T = (s : Set V)}) =
      ((B.exteriorMeasure μ : Measure B.Exterior).restrict (frontSet (G := G) s)).prod
        ((freeMass (G := G) hq hp s).restrict K) := by
    rw [show (frontSet (G := G) s) = frontierExterior (G := G) ((s : Set V)) s.finite_toSet from rfl,
      show K = interiorConnectSet (G := G) ((s : Set V)) s.finite_toSet T from rfl,
      show ((freeMass (G := G) hq hp s) : Measure B.Interior) =
        regionFreeMeasure (G := G) ((s : Set V)) s.finite_toSet hq hp from rfl]
    exact map_splitEquiv_restrict_region_eq_prod (G := G) ((s : Set V)) s.finite_toSet hq hp μ hμ hT
  have hstep : (μ : Measure (G.edgeSet → Bool)) A =
      (((B.exteriorMeasure μ : Measure B.Exterior).restrict (frontSet (G := G) s)).prod
        ((freeMass (G := G) hq hp s).restrict K)) (B.splitEquiv '' A) := by
    have hIm : MeasurableSet (B.splitEquiv '' A) :=
      B.splitEquiv.measurableEmbedding.measurableSet_image.mpr hAmeas
    rw [← hmap, Measure.map_apply B.splitEquiv.measurable hIm]
    rw [Set.preimage_image_eq A B.splitEquiv.injective, Measure.restrict_apply hAmeas,
      Set.inter_eq_left.mpr hSt]
  have himage : B.splitEquiv '' A = (A₀ ×ˢ K) ∩ {z : B.Exterior × B.Interior | B.glue z ∈ C} := by
    ext z
    constructor
    · rintro ⟨ω, ⟨hCω, hPω⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have h2 : ω ∈ B.splitEquiv ⁻¹' (A₀ ×ˢ K) := by rw [← hP]; exact hPω
        exact Set.mem_preimage.mp h2
      · show B.glue (B.splitEquiv ω) ∈ C
        rwa [B.splitEquiv_apply, B.glue_split]
    · rintro ⟨hz, hCz⟩
      refine ⟨B.glue z, ⟨hCz, ?_⟩, B.split_glue z⟩
      have h2 : B.splitEquiv (B.glue z) ∈ A₀ ×ˢ K := by
        rw [B.splitEquiv_apply, B.split_glue]
        exact hz
      have hgoal : B.glue z ∈ stratumPiece (G := G) T s Y ↔ B.splitEquiv (B.glue z) ∈ (A₀ ×ˢ K) := by
        rw [hP]
        rfl
      exact hgoal.mpr h2
  rw [hstep, himage,
    Measure.prod_apply (s := (A₀ ×ˢ K) ∩ {z : B.Exterior × B.Interior | B.glue z ∈ C})
      (hA₀meas.prod hKmeas |>.inter (hC.preimage B.splitEquiv.symm.measurable))]
  rw [← lintegral_indicator (measurableSet_frontSet (G := G) s)]
  refine lintegral_congr (fun η => ?_)
  by_cases hfront : η ∈ frontSet (G := G) s
  · rw [Set.indicator_of_mem hfront]
    by_cases hη : η ∈ A₀
    · rw [Set.indicator_of_mem hη, Measure.restrict_apply]
      · congr 1
        ext i
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_prod, Prod.mk.eta, hη,
          true_and]
        tauto
      · exact ((hA₀meas.prod hKmeas).inter
          (hC.preimage B.splitEquiv.symm.measurable)).preimage measurable_prodMk_left
    · rw [Set.indicator_of_notMem hη]
      have hempty : Prod.mk η ⁻¹' ((A₀ ×ˢ K) ∩ {z : B.Exterior × B.Interior | B.glue z ∈ C}) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro i ⟨h1, -⟩
        exact hη (Set.mem_prod.mp h1).1
      rw [hempty]
      simp
  · rw [Set.indicator_of_notMem hfront, Set.indicator_of_notMem
      (fun h => hfront (Set.mem_of_mem_inter_left h))]

/-! ## The kernel side of the identity on one stratum -/

/-- On a stratum of the random closed region, the random-region kernel value is
the predicted probability `sliceVal` of the exterior field. -/
theorem sliceVal_split_eq_regionKernelFun {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {s : Finset V} {ω : G.edgeSet → Bool}
    (hreg : region G ω T = (s : Set V)) {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) :
    sliceVal (G := G) hq hp T C s (restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω) =
      regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C := by
  rw [regionField_eq_of_region_eq (G := G) hreg, regionKernelFun, sliceVal,
    Measure.map_apply (f := fun i : (boxOf (G := G) s).Interior =>
      (boxOf (G := G) s).glue (((boxOf (G := G) s).splitEquiv
        (cutAt (G := G) ((s : Set V)) ω)).1, i))
      ((boxOf (G := G) s).measurable_glue_const_left _) hC,
    splitEquiv_cutAt_fst]
  have hX : MeasurableSet ((fun i : (boxOf (G := G) s).Interior =>
      (boxOf (G := G) s).glue (restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω, i))
      ⁻¹' C) :=
    hC.preimage ((boxOf (G := G) s).measurable_glue_const_left _)
  rw [← lintegral_indicator_one hX]
  rfl

/-- **The interior integral of a slice, computed.** -/
theorem lintegral_prod_slice {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) (s : Finset V)
    (μ₁ : Measure (boxOf (G := G) s).Exterior) {A₀ : Set (boxOf (G := G) s).Exterior}
    (hA₀ : MeasurableSet A₀) :
    ∫⁻ z, ((A₀ ×ˢ connSet (G := G) T s).indicator
        (fun z => sliceVal (G := G) hq hp T C s z.1)) z
        ∂(μ₁.prod ((freeMass (G := G) hq hp s).restrict (connSet (G := G) T s))) =
      ∫⁻ η in A₀, freeMass (G := G) hq hp s
        ({i | (boxOf (G := G) s).glue (η, i) ∈ C} ∩ connSet (G := G) T s) ∂μ₁ := by
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI hfin : IsFiniteMeasure (freeMass (G := G) hq hp s) :=
    ⟨lt_of_le_of_lt (freeMass_le_one (G := G) hq hp s Set.univ) ENNReal.one_lt_top⟩
  have hKmeas : MeasurableSet (connSet (G := G) T s) := measurableSet_connSet (G := G) T s
  have hmeas : Measurable (fun z : (boxOf (G := G) s).Exterior × (boxOf (G := G) s).Interior =>
      ((A₀ ×ˢ connSet (G := G) T s).indicator
        (fun z => sliceVal (G := G) hq hp T C s z.1)) z) :=
    Measurable.indicator ((measurable_sliceVal (G := G) hq hp T hC s).comp measurable_fst)
      (hA₀.prod hKmeas)
  rw [lintegral_prod _ hmeas.aemeasurable]
  have hinner : ∀ η : (boxOf (G := G) s).Exterior,
      ∫⁻ i, ((A₀ ×ˢ connSet (G := G) T s).indicator
          (fun z => sliceVal (G := G) hq hp T C s z.1)) (η, i)
          ∂((freeMass (G := G) hq hp s).restrict (connSet (G := G) T s)) =
        (A₀.indicator (fun η => freeMass (G := G) hq hp s
          ({i | (boxOf (G := G) s).glue (η, i) ∈ C} ∩ connSet (G := G) T s))) η := by
    intro η
    by_cases hη : η ∈ A₀
    · rw [Set.indicator_of_mem hη]
      have hstep : ∀ i : (boxOf (G := G) s).Interior,
          ((A₀ ×ˢ connSet (G := G) T s).indicator
            (fun z => sliceVal (G := G) hq hp T C s z.1)) (η, i) =
          (connSet (G := G) T s).indicator
            (fun _ => sliceVal (G := G) hq hp T C s η) i := by
        intro i
        by_cases hi : i ∈ connSet (G := G) T s <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hη, hi]
      rw [lintegral_congr hstep, lintegral_indicator_const hKmeas,
        Measure.restrict_apply hKmeas, Set.inter_self, mul_comm]
      exact mul_sliceVal_eq_freeMass (G := G) hq hp hC s η
    · rw [Set.indicator_of_notMem hη]
      have hstep : ∀ i : (boxOf (G := G) s).Interior,
          ((A₀ ×ˢ connSet (G := G) T s).indicator
            (fun z => sliceVal (G := G) hq hp T C s z.1)) (η, i) = 0 := by
        intro i
        simp [Set.indicator_of_notMem, hη]
      rw [lintegral_congr hstep]
      simp
  rw [lintegral_congr hinner, ← lintegral_indicator hA₀]

/-- **The exterior form of the kernel side on one stratum.** -/
theorem stratum_rhs {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    {s : Finset V} (hT : T ⊆ (s : Set V))
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    ∫⁻ ω in stratumPiece (G := G) T s Y,
        regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C
        ∂(μ : Measure (G.edgeSet → Bool)) =
      ∫⁻ η, ((frontSet (G := G) s ∩ extPreimage (G := G) s Y).indicator
          (fun η => freeMass (G := G) hq hp s
            ({i | (boxOf (G := G) s).glue (η, i) ∈ C} ∩ connSet (G := G) T s))) η
        ∂((boxOf (G := G) s).exteriorMeasure μ : Measure (boxOf (G := G) s).Exterior) := by
  classical
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI hfin : IsFiniteMeasure (freeMass (G := G) hq hp s) :=
    ⟨lt_of_le_of_lt (freeMass_le_one (G := G) hq hp s Set.univ) ENNReal.one_lt_top⟩
  set B := boxOf (G := G) s with hB
  set A₀ : Set B.Exterior := frontSet (G := G) s ∩ extPreimage (G := G) s Y with hA₀
  set K : Set B.Interior := connSet (G := G) T s with hK
  set St : Set (G.edgeSet → Bool) := {ω : G.edgeSet → Bool | region G ω T = (s : Set V)} with hStdef
  set P : Set (G.edgeSet → Bool) := stratumPiece (G := G) T s Y with hPdef
  have hA₀meas : MeasurableSet A₀ :=
    (measurableSet_frontSet (G := G) s).inter (measurableSet_extPreimage (G := G) s hY)
  have hKmeas : MeasurableSet K := measurableSet_connSet (G := G) T s
  have hPmeas : MeasurableSet P := measurableSet_stratumPiece (G := G) T s hY
  have hStmeas : MeasurableSet St := measurableSet_region_eq (G := G) T (s : Set V)
  have hPsub : P ⊆ St := fun ω hω => hω.1
  have hP : P = B.splitEquiv ⁻¹' (A₀ ×ˢ K) := stratumPiece_eq_split_rect (G := G) T s Y hT
  have hmap : Measure.map B.splitEquiv
      ((μ : Measure (G.edgeSet → Bool)).restrict St) =
      ((B.exteriorMeasure μ : Measure B.Exterior).restrict (frontSet (G := G) s)).prod
        ((freeMass (G := G) hq hp s).restrict K) := by
    rw [show (frontSet (G := G) s) = frontierExterior (G := G) ((s : Set V)) s.finite_toSet from rfl,
      show K = interiorConnectSet (G := G) ((s : Set V)) s.finite_toSet T from rfl,
      show ((freeMass (G := G) hq hp s) : Measure B.Interior) =
        regionFreeMeasure (G := G) ((s : Set V)) s.finite_toSet hq hp from rfl]
    exact map_splitEquiv_restrict_region_eq_prod (G := G) ((s : Set V)) s.finite_toSet hq hp μ hμ hT
  -- the ω-side equals the z-side
  have hpoint : ∀ z : B.Exterior × B.Interior,
      P.indicator (fun ω => regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C)
          (B.glue z) =
        ((A₀ ×ˢ K).indicator (fun z => sliceVal (G := G) hq hp T C s z.1)) z := by
    intro z
    by_cases hz : B.glue z ∈ P
    · have hzE : z ∈ A₀ ×ˢ K := by
        have h2 : B.splitEquiv (B.glue z) ∈ A₀ ×ˢ K := by
          rw [hP] at hz
          exact Set.mem_preimage.mp hz
        rwa [B.splitEquiv_apply, B.split_glue] at h2
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hzE]
      have hreg : region G (B.glue z) T = (s : Set V) := hz.1
      rw [← sliceVal_split_eq_regionKernelFun (G := G) hq hp hreg hC]
      congr 1
      exact congrArg Prod.fst (B.split_glue z)
    · have hzE : z ∉ A₀ ×ˢ K := by
        intro h2
        have h2' : B.splitEquiv (B.glue z) ∈ A₀ ×ˢ K := by
          rwa [B.splitEquiv_apply, B.split_glue]
        exact hz (by rw [hP]; exact Set.mem_preimage.mpr h2')
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hzE]
  have hstep : ∫⁻ ω in St, P.indicator (fun ω => regionKernelFun (G := G) hq hp T
        (regionField (G := G) T ω) C) ω ∂(μ : Measure (G.edgeSet → Bool)) =
      ∫⁻ z, ((A₀ ×ˢ K).indicator (fun z => sliceVal (G := G) hq hp T C s z.1)) z
        ∂(((B.exteriorMeasure μ : Measure B.Exterior).restrict (frontSet (G := G) s)).prod
          ((freeMass (G := G) hq hp s).restrict K)) := by
    rw [← hmap]
    rw [show ∫⁻ z, ((A₀ ×ˢ K).indicator (fun z => sliceVal (G := G) hq hp T C s z.1)) z
        ∂(Measure.map B.splitEquiv ((μ : Measure (G.edgeSet → Bool)).restrict St)) =
        ∫⁻ ω, ((A₀ ×ˢ K).indicator (fun z => sliceVal (G := G) hq hp T C s z.1))
          (B.splitEquiv ω) ∂((μ : Measure (G.edgeSet → Bool)).restrict St) from
      lintegral_map (Measurable.indicator
        ((measurable_sliceVal (G := G) hq hp T hC s).comp measurable_fst)
        (hA₀meas.prod hKmeas)) B.splitEquiv.measurable]
    refine lintegral_congr (fun ω => ?_)
    rw [← hpoint]
    congr 1
    rw [B.splitEquiv_apply]
    exact (B.glue_split ω).symm
  rw [lintegral_of_subset hPmeas hStmeas hPsub
    (fun ω => regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C)]
  rw [hstep, lintegral_prod_slice (G := G) hq hp T hC s
    ((B.exteriorMeasure μ : Measure B.Exterior).restrict (frontSet (G := G) s)) hA₀meas,
    ← lintegral_indicator hA₀meas]
  exact lintegral_indicator_restrict (μ := (B.exteriorMeasure μ : Measure B.Exterior))
    hA₀meas Set.inter_subset_left _


/-! ## The total identity: all strata at once -/

/-- **The random-region conditional law for arbitrary measurable events.**

For a law `μ` satisfying the DLR equations at the box of *every* finite vertex set
(with the actual exterior-induced boundary partition), every finite event
sequence `Y s` and every measurable global event `C`:

  `μ(C ∩ ⋃ s {region = s, exterior ∈ Y s})`
  `= ∫_{⋃ s {region = s, exterior ∈ Y s}} κ_T(ω)(C) dμ(ω)`,

where `κ_T(ω) = regionKernelFun T (regionField T ω)` is the free FK law of the
random region box conditioned on the forced connectivity, glued onto the exterior
field.  No interior support of `C` and no containment of `C` in a box is
required, and there is no null set to remove: the identity is between the two
explicit integrals. -/
theorem region_kernel_disintegration_total {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V) (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    (Y : Finset V → Set (G.edgeSet → Bool)) (hY : ∀ s, MeasurableSet (Y s)) :
    (μ : Measure (G.edgeSet → Bool))
        (C ∩ ⋃ s : Finset V, stratumPiece (G := G) T s (Y s)) =
      ∫⁻ ω in (⋃ s : Finset V, stratumPiece (G := G) T s (Y s)),
        regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C
        ∂(μ : Measure (G.edgeSet → Bool)) := by
  classical
  have hpiece_meas : ∀ s : Finset V,
      MeasurableSet (stratumPiece (G := G) T s (Y s)) :=
    fun s => measurableSet_stratumPiece (G := G) T s (hY s)
  have hpiece_disj : Pairwise (Function.onFun Disjoint
      (fun s : Finset V => stratumPiece (G := G) T s (Y s))) := by
    intro s s' hne
    exact stratumPiece_disjoint (G := G) hne (Y s) (Y s')
  have hdisjC : Pairwise (Function.onFun Disjoint
      (fun s : Finset V => C ∩ stratumPiece (G := G) T s (Y s))) := by
    intro s s' hne
    exact (hpiece_disj hne).mono Set.inter_subset_right Set.inter_subset_right
  have hInter : C ∩ ⋃ s : Finset V, stratumPiece (G := G) T s (Y s) =
      ⋃ s : Finset V, (C ∩ stratumPiece (G := G) T s (Y s)) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  rw [hInter, measure_iUnion hdisjC (fun s => hC.inter (hpiece_meas s)),
    lintegral_iUnion hpiece_meas hpiece_disj]
  refine tsum_congr (fun s => ?_)
  by_cases hTsub : T ⊆ (s : Set V)
  · exact (stratum_lhs (G := G) hq hp T hTsub μ (hμ s) hC (hY s)).trans
      (stratum_rhs (G := G) hq hp T hTsub μ (hμ s) hC (hY s)).symm
  · have hempty : stratumPiece (G := G) T s (Y s) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ω hω
      have hreg : region G ω T = (s : Set V) := hω.1
      have hsub : T ⊆ (s : Set V) := by
        rw [← hreg]
        exact subset_region (G := G) (ω := ω) T
      exact hTsub hsub
    rw [hempty, Set.inter_empty, measure_empty]
    simp

/-- **The unconditional prediction identity.**  When the random region is almost
surely finite -- in the source this is what domination by a subcritical
percolation supplies -- the infinite-region fibre is null and the conditional law
of the whole configuration is the random-region kernel. -/
theorem region_kernel_total_univ {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    (hfin : ∀ᵐ ω ∂(μ : Measure (G.edgeSet → Bool)), (region G ω T).Finite)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) :
    (μ : Measure (G.edgeSet → Bool)) C =
      ∫⁻ ω, regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C
        ∂(μ : Measure (G.edgeSet → Bool)) := by
  classical
  let U : Set (G.edgeSet → Bool) :=
    ⋃ s : Finset V, stratumPiece (G := G) T s (Set.univ : Set (G.edgeSet → Bool))
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion (fun s => measurableSet_stratumPiece (G := G) T s MeasurableSet.univ)
  have hstr : ∀ᵐ ω ∂(μ : Measure (G.edgeSet → Bool)), ω ∈ U := by
    filter_upwards [hfin] with ω hω
    exact Set.mem_iUnion.mpr ⟨hω.toFinset, by
      simp only [stratumPiece, Set.preimage_univ, Set.inter_univ, Set.mem_setOf_eq]
      exact hω.coe_toFinset.symm⟩
  have hrestrict : (μ : Measure (G.edgeSet → Bool)).restrict U =
      (μ : Measure (G.edgeSet → Bool)) := Measure.restrict_eq_self_of_ae_mem hstr
  have hnull : (μ : Measure (G.edgeSet → Bool)) Uᶜ = 0 := by
    rw [ae_iff] at hstr
    exact hstr
  have h1 : (μ : Measure (G.edgeSet → Bool)) C =
      (μ : Measure (G.edgeSet → Bool)) (C ∩ U) := by
    have hsd : (μ : Measure (G.edgeSet → Bool)) (C \ U) = 0 :=
      measure_mono_null (fun x hx => hx.2) hnull
    have h := measure_inter_add_sdiff (μ := (μ : Measure (G.edgeSet → Bool))) (t := U) C hUmeas
    rw [hsd, add_zero] at h
    exact h.symm
  have hmain := region_kernel_disintegration_total (G := G) hq hp T μ hμ hC
    (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hUm : (⋃ s : Finset V, stratumPiece (G := G) T s
      ((fun _ : Finset V => (Set.univ : Set (G.edgeSet → Bool))) s)) = U := rfl
  rw [hUm] at hmain
  rw [h1, hmain, hrestrict]

/-! ## The free-boundary conditional law on a closed box (Theorem 5.1, step 2)

The source uses the sentence "`μ_i(| F_{S_n(ω_3)^c})(ω_i)` is the free boundary
random cluster measure in the interior of `S_n(ω_3)`", where `S_n(ω_3)` is the
random closed region explored from the dominating configuration.  This section
proves the deterministic content of that sentence for a fixed finite box. -/

/-- **The free-boundary conditional law on a closed box.**

Let `μ` satisfy the DLR equations at the box of the finite vertex set `s` with the
exterior-induced boundary partition, let `J` be a finite set of edges of that box
and `S` a measurable set of `J`-configurations.  Then `μ`-almost everywhere, at
every configuration whose exterior field on `s` is frontier-closed, the
conditional probability of the cylinder `cylinder J S` given the exterior of the
box is the free FK mass of its interior readout. -/
theorem condExp_cylinder_eq_freeMass_of_frontierSet {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) {s : Finset V}
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {J : Finset G.edgeSet} (hJ : J ⊆ (boxOf (G := G) s).edges)
    {S : Set (J → Bool)} (hS : MeasurableSet S) :
    ∀ᵐ ω ∂(μ : Measure (G.edgeSet → Bool)),
      restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω ∈ frontSet (G := G) s →
        ((μ : Measure (G.edgeSet → Bool))⟦MeasureTheory.cylinder J S |
            FKLimit.outsideSigma (boxOf (G := G) s).edges⟧) ω =
          (freeMass (G := G) hq hp s).real ((boxOf (G := G) s).boxCylinder J S hJ) := by
  have hA : FKLimit.DependsOnCoordinates (MeasureTheory.cylinder J S)
      (boxOf (G := G) s).edges :=
    (FK.InfiniteVolume.dependsOnCoordinates_cylinder J S).mono hJ
  have hcond := (boxOf (G := G) s).condExp_of_dependsOn_edges_of_isDLR hq hp
    (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
    (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ hμ hA
  filter_upwards [hcond] with ω hω hfront
  rw [hω]
  rw [show MeasureTheory.cylinder J S = (boxOf (G := G) s).interiorRestriction ⁻¹'
      ((boxOf (G := G) s).boxCylinder J S hJ) from
    ((boxOf (G := G) s).preimage_interiorRestriction_boxCylinder J S hJ).symm]
  rw [FK.InfiniteVolume.FiniteBox.conditionalLaw_real_interior_preimage
    (B := boxOf (G := G) s) (C := (boxOf (G := G) s).boxCylinder J S hJ)
    (hC := Set.Finite.measurableSet (Set.toFinite _))]
  rw [show ((boxOf (G := G) s).graph.fkMeasure hq hp
        (exteriorPartition (G := G) ((s : Set V)) s.finite_toSet
          (FKLimit.exteriorRestriction (boxOf (G := G) s).edges ω)))
      = (boxOf (G := G) s).fkKernel hq hp
        (exteriorPartition (G := G) ((s : Set V)) s.finite_toSet)
        (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet)
        (restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω) from rfl]
  rw [fkKernel_eq_free_of_frontierSet (G := G) ((s : Set V)) s.finite_toSet hq hp hfront]

/-- **The unconditional prediction identity under a dominating subcritical law.**

This is the shape in which the source's Theorem 5.1 hypothesis enters: `μ` is
coupled below a non-percolating law `ρ`, which forces `μ`-a.e. non-percolation
(`FK.ae_nonPercolating_of_orderedCoupling`), hence makes the random region based
at any *finite* set almost surely finite, so that the infinite-region fibre
vanishes.  No no-percolation hypothesis is assumed on `μ` itself. -/
theorem region_kernel_total_univ_of_dominated {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hG : G.Connected) (T : Set V) (hT : T.Finite)
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {ρ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure ρ]
    {γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool))}
    (hγfst : γ.map Prod.fst = (μ : Measure (G.edgeSet → Bool)))
    (hγsnd : γ.map Prod.snd = ρ)
    (horder : ∀ᵐ z ∂γ, z.1 ≤ z.2)
    (hρ : ∀ᵐ ω ∂ρ, ω ∈ FK.NonPercolating G)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) :
    (μ : Measure (G.edgeSet → Bool)) C =
      ∫⁻ ω, regionKernelFun (G := G) hq hp T (regionField (G := G) T ω) C
        ∂(μ : Measure (G.edgeSet → Bool)) := by
  have hfinμ : ∀ᵐ ω ∂(μ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G :=
    FK.ae_nonPercolating_of_orderedCoupling G hG hγfst hγsnd horder hρ
  refine region_kernel_total_univ (G := G) hq hp T μ hμ ?_ hC
  filter_upwards [hfinμ] with ω hω
  exact region_finite (G := G) hT (finiteOpenClusters_of_nonPercolating G ω hω)

/-- **Closed boundary gives the frontier condition.**  A configuration whose
labelled frontier at `s` is closed induces a frontier-closed exterior field: the
form in which the source's `ωᵢ|∂S_n = 0` hypothesis is consumed. -/
theorem mem_frontSet_of_closedBoundary {s : Finset V} {ω : G.edgeSet → Bool}
    (h : ClosedBoundary G (openSubgraph G ω) ((s : Set V))) :
    restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω ∈ frontSet (G := G) s := by
  intro e hin hout
  have he := not_mem_regionBox_edges_of_crossing (G := G) ((s : Set V)) s.finite_toSet hout
  rw [extendExterior_apply_of_notMem (G := G) (R := (s : Set V)) (hR := s.finite_toSet) he]
  exact frontier_closed h hin hout

/-- **The free-boundary conditional law at a closed box, in configuration form.**

At every configuration whose labelled frontier at `s` is closed, the conditional
probability of a cylinder inside the box, given the exterior of the box, is the
free finite-volume FK mass of its interior readout. -/
theorem condExp_cylinder_eq_freeMass_of_closedBoundary {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) {s : Finset V}
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {J : Finset G.edgeSet} (hJ : J ⊆ (boxOf (G := G) s).edges)
    {S : Set (J → Bool)} (hS : MeasurableSet S) :
    ∀ᵐ ω ∂(μ : Measure (G.edgeSet → Bool)),
      ClosedBoundary G (openSubgraph G ω) ((s : Set V)) →
        ((μ : Measure (G.edgeSet → Bool))⟦MeasureTheory.cylinder J S |
            FKLimit.outsideSigma (boxOf (G := G) s).edges⟧) ω =
          (freeMass (G := G) hq hp s).real ((boxOf (G := G) s).boxCylinder J S hJ) := by
  filter_upwards [condExp_cylinder_eq_freeMass_of_frontierSet (G := G) hq hp μ hμ hJ hS]
    with ω hω hcl
  exact hω (mem_frontSet_of_closedBoundary (G := G) hcl)

end FK.RandomRegionKernel

/-! ## Axiom audit -/

#print axioms FK.RandomRegionKernel.mul_lintegral_cond
#print axioms FK.RandomRegionKernel.predictKernel_apply
#print axioms FK.RandomRegionKernel.measurable_sliceVal
#print axioms FK.RandomRegionKernel.mul_sliceVal_eq_freeMass
#print axioms FK.RandomRegionKernel.stratum_lhs
#print axioms FK.RandomRegionKernel.stratum_rhs
#print axioms FK.RandomRegionKernel.region_kernel_disintegration_total
#print axioms FK.RandomRegionKernel.region_kernel_total_univ
#print axioms FK.RandomRegionKernel.condExp_cylinder_eq_freeMass_of_frontierSet
#print axioms FK.RandomRegionKernel.region_kernel_total_univ_of_dominated
#print axioms FK.RandomRegionKernel.mem_frontSet_of_closedBoundary
#print axioms FK.RandomRegionKernel.condExp_cylinder_eq_freeMass_of_closedBoundary
