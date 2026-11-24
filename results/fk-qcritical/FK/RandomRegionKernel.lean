/-
# The conditional law of an FK-Gibbs measure given the random closed region

Direction 3: disintegration along the random box (arXiv:2512.16486v1, proof of
Theorem 5.1 / Proposition 1.8(2)).

The already-installed `FK/RegionFibreIdentity.lean` computes, for *each fixed*
finite vertex region `R`, the factorization of the law `μ` restricted to the
stratum `{ω | region G ω T = R}`.  What the source argument needs on top of that
is a *single* conditional law along the random region, valid simultaneously on
all strata and for all exterior tests, i.e. a regular conditional distribution
of `μ` given the random pair

  `ω ↦ (region G ω T, ω restricted to the complement of that region)`.

This file constructs the interior-supported and cylinder-level form of that
conditional identity. It does not yet package a full regular conditional kernel
on the whole product space or supply the reverse-martingale assembly.

* `cutAt R ω` closes every interior edge of `R` and keeps `ω` off the box: it is
  the exterior coordinate `ω|_{R^c}` written as an ambient configuration.
* `regionIdx T ω : Option (Finset V)` is the random region, encoded as an
  optional finite set with countably supported law: every fibre
  `{ω | regionIdx T ω = some s}` and the infinite-region fibre
  `{ω | regionIdx T ω = none}` is measurable (`measurableSet_regionIdx_eq_some`,
  `measurableSet_regionIdx_eq_none`).  No measurable structure on `Finset V`
  itself is needed anywhere.
* `regionField T ω = (regionIdx T ω, cutIdx (regionIdx T ω) ω)` is the random
  region together with its exterior field (equal to
  `(regionIdx T ω, cutAt (region G ω T) ω)` on the finite-region part).
* `kernelValue` is the interior FK mass
  `(free ∂R-mass of the forced connectivity event)⁻¹ * free-mass of the tested
  interior event ∩ forced connectivity`; `regionKernelFun` is the corresponding
  law on configurations, obtained by gluing the predicted interior to the
  exterior field.
* `stratum_cross_mul` is the per-stratum identity, cross-multiplied so that it
  needs no positivity of the connectivity mass.
* `region_kernel_disintegration` assembles all strata into one identity: on
  events that are `regionField`-measurable and meet only finitely many strata,
  the random-region kernel is a version of the conditional law of `μ`, for every
  event `C` that is read off from the interior of the region box.

The interior law is *not* the naive free box law: by
`RegionFibreCounterexample` the stratum forces the interior connection event, and
that conditioning is kept explicitly in `connSet`.
-/

import FK.RegionFibreIdentity
import FK.NestedFiniteAssembly

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

open CurvatureVariance.Infra.Percolation
open FK.RandomClosedBoundary

namespace FK.RandomRegionKernel

variable {V : Type*} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-! ## The exterior field of a vertex region -/

/-- The ambient configuration that closes every interior edge of `R` and keeps
the values of `ω` elsewhere.  This is the paper's `ω|_{R^c}` as a configuration. -/
noncomputable def cutAt (R : Set V) (ω : G.edgeSet → Bool) : G.edgeSet → Bool := by
  classical
  exact fun e => if e ∈ interiorEdgeSet G R then false else ω e

theorem cutAt_apply_of_mem {R : Set V} {ω : G.edgeSet → Bool} {e : G.edgeSet}
    (he : e ∈ interiorEdgeSet G R) : cutAt (G := G) R ω e = false := by
  classical
  show (if h : e ∈ interiorEdgeSet G R then false else ω e) = false
  rw [dif_pos he]

theorem cutAt_apply_of_notMem {R : Set V} {ω : G.edgeSet → Bool} {e : G.edgeSet}
    (he : e ∉ interiorEdgeSet G R) : cutAt (G := G) R ω e = ω e := by
  classical
  show (if h : e ∈ interiorEdgeSet G R then false else ω e) = ω e
  rw [dif_neg he]

/-- The cutoff map is the exterior extension of the exterior restriction. -/
theorem cutAt_eq_extendExterior (R : Set V) (hR : R.Finite) (ω : G.edgeSet → Bool) :
    cutAt (G := G) R ω =
      FK.RandomClosedBoundary.extendExterior (G := G) R hR
        (FK.RandomClosedBoundary.restrictExterior (G := G) R hR ω) := by
  classical
  funext e
  show (if h : e ∈ interiorEdgeSet G R then false else ω e) =
    (if h : e ∈ (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).edges then false
      else ω e)
  by_cases he : e ∈ (FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).edges
  · have hei : e ∈ interiorEdgeSet G R :=
      FK.RandomClosedBoundary.mem_interiorEdgeSet_of_mem_box (G := G) R hR he
    rw [dif_pos hei, dif_pos he]
  · have hei : e ∉ interiorEdgeSet G R := by
      intro hmem
      exact he ((FK.RandomClosedBoundary.mem_regionBox_edges_iff (G := G) R hR).mpr hmem)
    rw [dif_neg hei, dif_neg he]

/-- The exterior part of the cutoff is the exterior restriction of `ω`. -/
theorem splitEquiv_cutAt_fst (R : Set V) (hR : R.Finite) (ω : G.edgeSet → Bool) :
    ((FK.RandomClosedBoundary.regionBoxOf (G := G) R hR).splitEquiv
        (cutAt (G := G) R ω)).1 =
      FK.RandomClosedBoundary.restrictExterior (G := G) R hR ω := by
  classical
  funext e
  show cutAt (G := G) R ω e.1 = ω e.1
  apply cutAt_apply_of_notMem
  intro hmem
  exact e.2 ((FK.RandomClosedBoundary.mem_regionBox_edges_iff (G := G) R hR).mpr hmem)

/-- The cutoff map is measurable: each coordinate is either constant or a
coordinate projection. -/
theorem measurable_cutAt (R : Set V) :
    Measurable (cutAt (G := G) R) := by
  classical
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ interiorEdgeSet G R
  · have h : (fun ω : G.edgeSet → Bool => cutAt (G := G) R ω e) = fun _ => false := by
      funext ω
      exact cutAt_apply_of_mem (G := G) he
    rw [h]
    exact measurable_const
  · have h : (fun ω : G.edgeSet → Bool => cutAt (G := G) R ω e) = fun ω => ω e := by
      funext ω
      exact cutAt_apply_of_notMem (G := G) he
    rw [h]
    exact measurable_pi_apply e

/-! ## The random region as a random variable -/

/-- The random closed region of the base `T`, encoded as an optional finite set.
Nothing is claimed about the infinite-region event here; `Option.none` records
it. -/
noncomputable def regionIdx (T : Set V) (ω : G.edgeSet → Bool) : Option (Finset V) := by
  classical
  exact if h : (region G ω T).Finite then some h.toFinset else none

theorem regionIdx_eq_some_iff (T : Set V) (ω : G.edgeSet → Bool) (s : Finset V) :
    regionIdx (G := G) T ω = some s ↔ region G ω T = (s : Set V) := by
  classical
  unfold regionIdx
  by_cases h : (region G ω T).Finite
  · rw [dif_pos h]
    constructor
    · intro hs
      have hcoe : h.toFinset = s := Option.some.inj hs
      rw [← hcoe, h.coe_toFinset]
    · intro hs
      have hfs : h.toFinset = s := by
        apply Finset.coe_injective
        rw [h.coe_toFinset, hs]
      rw [hfs]
  · rw [dif_neg h]
    constructor
    · intro hc
      exact absurd hc (by simp)
    · intro hs
      exact absurd (hs ▸ s.finite_toSet) h

theorem regionIdx_eq_some_of_eq {T : Set V} {ω : G.edgeSet → Bool} {s : Finset V}
    (h : region G ω T = (s : Set V)) : regionIdx (G := G) T ω = some s :=
  (regionIdx_eq_some_iff T ω s).mpr h

theorem measurableSet_regionIdx_eq_some (T : Set V) (s : Finset V) :
    MeasurableSet {ω : G.edgeSet → Bool | regionIdx (G := G) T ω = some s} := by
  have h : {ω : G.edgeSet → Bool | regionIdx (G := G) T ω = some s} =
      {ω | region G ω T = (s : Set V)} := by
    ext ω
    exact regionIdx_eq_some_iff T ω s
  rw [h]
  exact measurableSet_region_eq (G := G) T (s : Set V)

theorem regionIdx_eq_none_iff (T : Set V) (ω : G.edgeSet → Bool) :
    regionIdx (G := G) T ω = none ↔ ¬ (region G ω T).Finite := by
  classical
  unfold regionIdx
  by_cases h : (region G ω T).Finite
  · rw [dif_pos h]
    exact ⟨fun hc => absurd hc (by simp), fun hc => absurd h hc⟩
  · rw [dif_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem region_finite_eq_iUnion (T : Set V) :
    {ω : G.edgeSet → Bool | (region G ω T).Finite} =
      ⋃ s : Finset V, {ω | region G ω T = (s : Set V)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro h
    exact ⟨h.toFinset, h.coe_toFinset.symm⟩
  · rintro ⟨s, hs⟩
    rw [hs]
    exact s.finite_toSet

theorem measurableSet_region_finite (T : Set V) :
    MeasurableSet {ω : G.edgeSet → Bool | (region G ω T).Finite} := by
  rw [region_finite_eq_iUnion]
  exact MeasurableSet.iUnion fun s => measurableSet_region_eq (G := G) T (s : Set V)

theorem measurableSet_regionIdx_eq_none (T : Set V) :
    MeasurableSet {ω : G.edgeSet → Bool | regionIdx (G := G) T ω = none} := by
  have h : {ω : G.edgeSet → Bool | regionIdx (G := G) T ω = none} =
      {ω | ¬ (region G ω T).Finite} := by
    ext ω
    exact regionIdx_eq_none_iff T ω
  rw [h]
  exact (measurableSet_region_finite T).compl

/-- The exterior field of the random region, as an ambient configuration. -/
noncomputable def cutIdx (i : Option (Finset V)) (ω : G.edgeSet → Bool) :
    G.edgeSet → Bool :=
  match i with
  | none => ω
  | some s => cutAt (G := G) ((s : Set V)) ω

/-- **The random region together with its exterior field.**  This is the random
variable the source conditions on in the proof of Theorem 5.1. -/
noncomputable def regionField (T : Set V) (ω : G.edgeSet → Bool) :
    Option (Finset V) × (G.edgeSet → Bool) :=
  (regionIdx (G := G) T ω, cutIdx (regionIdx (G := G) T ω) ω)

theorem regionField_eq_of_region_eq {T : Set V} {ω : G.edgeSet → Bool} {s : Finset V}
    (h : region G ω T = (s : Set V)) :
    regionField (G := G) T ω = (some s, cutAt (G := G) ((s : Set V)) ω) := by
  unfold regionField cutIdx
  rw [regionIdx_eq_some_of_eq h]

/-! ## The finite box of a region, its free mass and its forced connectivity -/

/-- The finite labelled box of a finite vertex region. -/
noncomputable abbrev boxOf (s : Finset V) : FK.InfiniteVolume.FiniteBox G.edgeSet :=
  regionBoxOf (G := G) ((s : Set V)) s.finite_toSet

/-- The forced interior connection event of the random-region stratum. -/
noncomputable abbrev connSet (T : Set V) (s : Finset V) : Set (boxOf (G := G) s).Interior :=
  interiorConnectSet (G := G) ((s : Set V)) s.finite_toSet T

/-- The free finite-volume FK measure of the region box. -/
noncomputable abbrev freeMass {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (s : Finset V) :
    Measure (boxOf (G := G) s).Interior :=
  regionFreeMeasure (G := G) ((s : Set V)) s.finite_toSet hq hp

/-- The interior readout of an event on the configurations of the region box. -/
noncomputable def intSet (C : Set (G.edgeSet → Bool)) (s : Finset V) :
    Set (boxOf (G := G) s).Interior :=
  {i | (boxOf (G := G) s).glue ((boxOf (G := G) s).closedExterior, i) ∈ C}

/-- The value of a probability measure on a set, as an extended nonnegative
real.  Kept as a rewrite rule because the coercion of `ProbabilityMeasure` to a
function is valued in `ℝ≥0`. -/
theorem probApply_eq {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α) (s : Set α) :
    (μ : Measure α) s = (↑(μ s) : ℝ≥0∞) := by simp

theorem measurableSet_connSet (T : Set V) (s : Finset V) :
    MeasurableSet (connSet (G := G) T s) :=
  measurableSet_interiorConnects (G := G) ((s : Set V)) s.finite_toSet T

theorem measurableSet_intSet {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    (s : Finset V) : MeasurableSet (intSet (G := G) C s) :=
  hC.preimage ((boxOf (G := G) s).measurable_glue_const_left
    (boxOf (G := G) s).closedExterior)

/-- **The value of the random-region kernel on an interior event.**  This is the
free FK mass of the tested interior event intersected with the forced
connectivity of the stratum, normalized by the free mass of that connectivity
event.  On the (null) strata where the connectivity event has zero free mass the
normalization returns `0`, matching the zero measure produced by `cond`. -/
noncomputable def kernelValue {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (C : Set (G.edgeSet → Bool)) : Option (Finset V) → ℝ≥0∞
  | none => 0
  | some s =>
      (freeMass (G := G) hq hp s (connSet (G := G) T s))⁻¹ *
        freeMass (G := G) hq hp s (intSet (G := G) C s ∩ connSet (G := G) T s)

/-- **The random-region conditional law.**  Given the random region (as a finite
vertex set) and the exterior field, the predicted interior law is the free FK
measure of the region box with the forced connectivity event imposed, glued onto
the exterior field. -/
noncomputable def regionKernelFun {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (T : Set V)
    (y : Option (Finset V) × (G.edgeSet → Bool)) : Measure (G.edgeSet → Bool) :=
  match y.1 with
  | none => Measure.dirac y.2
  | some s =>
      Measure.map
        (fun i : (boxOf (G := G) s).Interior =>
          (boxOf (G := G) s).glue (((boxOf (G := G) s).splitEquiv y.2).1, i))
        (ProbabilityTheory.cond (freeMass (G := G) hq hp s) (connSet (G := G) T s))

/-- The kernel's value on an interior-supported event is the explicit FK mass. -/
theorem regionKernelFun_apply_of_supported {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C) {s : Finset V}
    (ζ : G.edgeSet → Bool)
    (hsupp : ∀ (η : (boxOf (G := G) s).Exterior) (i : (boxOf (G := G) s).Interior),
      (boxOf (G := G) s).glue (η, i) ∈ C ↔ i ∈ intSet (G := G) C s) :
    regionKernelFun (G := G) hq hp T (some s, ζ) C =
      kernelValue (G := G) hq hp T C (some s) := by
  unfold regionKernelFun kernelValue
  rw [Measure.map_apply ((boxOf (G := G) s).measurable_glue_const_left _) hC,
    ProbabilityTheory.cond_apply (measurableSet_connSet (G := G) T s)]
  have hpre : (fun i : (boxOf (G := G) s).Interior =>
        (boxOf (G := G) s).glue (((boxOf (G := G) s).splitEquiv ζ).1, i)) ⁻¹' C =
      intSet (G := G) C s := by
    ext i
    exact hsupp ((boxOf (G := G) s).splitEquiv ζ).1 i
  rw [hpre, Set.inter_comm]

/-! ## Stratum pieces of the random-region partition -/

/-- The stratum of the random closed region `s`, cut down by an exterior test
`Y` on the exterior field. -/
noncomputable def stratumPiece (T : Set V) (s : Finset V) (Y : Set (G.edgeSet → Bool)) :
    Set (G.edgeSet → Bool) :=
  {ω | region G ω T = (s : Set V)} ∩ cutAt (G := G) ((s : Set V)) ⁻¹' Y

theorem measurableSet_stratumPiece (T : Set V) (s : Finset V)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    MeasurableSet (stratumPiece (G := G) T s Y) :=
  (measurableSet_region_eq (G := G) T (s : Set V)).inter
    (hY.preimage (measurable_cutAt (G := G) ((s : Set V))))

theorem stratumPiece_mono_test {T : Set V} {s : Finset V} {Y Y' : Set (G.edgeSet → Bool)}
    (hYY' : Y ⊆ Y') : stratumPiece (G := G) T s Y ⊆ stratumPiece (G := G) T s Y' := by
  rintro ω ⟨hreg, hcut⟩
  exact ⟨hreg, hYY' hcut⟩

theorem stratumPiece_disjoint {T : Set V} {s s' : Finset V} (h : s ≠ s')
    (Y Y' : Set (G.edgeSet → Bool)) :
    Disjoint (stratumPiece (G := G) T s Y) (stratumPiece (G := G) T s' Y') := by
  rw [Set.disjoint_left]
  rintro ω ⟨hreg, -⟩ ⟨hreg', -⟩
  have hcoe : (s : Set V) = (s' : Set V) := by rw [← hreg, hreg']
  exact h (Finset.coe_injective hcoe)

/-- The stratum piece is exactly the product of the closed-frontier exterior
condition (cut down by the exterior test) and the forced interior connectivity,
under the box splitting. -/
theorem stratumPiece_eq_split {T : Set V} (s : Finset V) (Y : Set (G.edgeSet → Bool))
    (hT : T ⊆ (s : Set V)) :
    stratumPiece (G := G) T s Y =
      (boxOf (G := G) s).splitEquiv ⁻¹'
        (({η : (boxOf (G := G) s).Exterior |
            frontierSet (G := G) ((s : Set V)) s.finite_toSet η} ∩
          {η | extendExterior (G := G) ((s : Set V)) s.finite_toSet η ∈ Y}) ×ˢ
          connSet (G := G) T s) := by
  ext ω
  simp only [stratumPiece, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_ofPred_eq]
  have hglue : (boxOf (G := G) s).glue ((boxOf (G := G) s).splitEquiv ω) = ω :=
    (boxOf (G := G) s).glue_split ω
  have hsplit_fst : ((boxOf (G := G) s).splitEquiv ω).1 =
      restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω := rfl
  have hcut : cutAt (G := G) ((s : Set V)) ω =
      extendExterior (G := G) ((s : Set V)) s.finite_toSet
        (restrictExterior (G := G) ((s : Set V)) s.finite_toSet ω) :=
    cutAt_eq_extendExterior (G := G) ((s : Set V)) s.finite_toSet ω
  constructor
  · rintro ⟨hreg, hY⟩
    have hreg' : region G ((boxOf (G := G) s).glue ((boxOf (G := G) s).splitEquiv ω)) T =
        (s : Set V) := by rw [hglue]; exact hreg
    obtain ⟨hfront, hconn⟩ :=
      (region_eq_iff (G := G) (R := (s : Set V)) (hR := s.finite_toSet) (T := T)
        ((boxOf (G := G) s).splitEquiv ω) hT).mp hreg'
    refine ⟨⟨hfront, ?_⟩, hconn⟩
    rw [hsplit_fst, ← hcut]
    exact hY
  · rintro ⟨⟨hfront, hY⟩, hconn⟩
    refine ⟨?_, ?_⟩
    · have hreg' := (region_eq_iff (G := G) (R := (s : Set V)) (hR := s.finite_toSet) (T := T)
        ((boxOf (G := G) s).splitEquiv ω) hT).mpr ⟨hfront, hconn⟩
      rwa [hglue] at hreg'
    · rw [hcut, ← hsplit_fst]
      exact hY
/-! ## The per-stratum DLR identity -/

/-- The closed-frontier exterior condition. -/
noncomputable def frontSet (s : Finset V) : Set (boxOf (G := G) s).Exterior :=
  {η | frontierSet (G := G) ((s : Set V)) s.finite_toSet η}

/-- The exterior test read on the exterior configurations of a box. -/
noncomputable def extPreimage (s : Finset V) (Y : Set (G.edgeSet → Bool)) :
    Set (boxOf (G := G) s).Exterior :=
  {η | extendExterior (G := G) ((s : Set V)) s.finite_toSet η ∈ Y}

theorem measurableSet_extPreimage (s : Finset V) {Y : Set (G.edgeSet → Bool)}
    (hY : MeasurableSet Y) : MeasurableSet (extPreimage (G := G) s Y) :=
  hY.preimage (measurable_extendExterior (G := G) ((s : Set V)) s.finite_toSet)

theorem measurableSet_frontSet (s : Finset V) : MeasurableSet (frontSet (G := G) s) :=
  measurableSet_frontierSet (G := G) ((s : Set V)) s.finite_toSet

/-- The stratum is exactly the split preimage of the closed-frontier exterior and
the forced interior connectivity. -/
theorem region_stratum_eq_split (T : Set V) (s : Finset V) (hT : T ⊆ (s : Set V)) :
    {ω : G.edgeSet → Bool | region G ω T = (s : Set V)} =
      (boxOf (G := G) s).splitEquiv ⁻¹'
        (frontSet (G := G) s ×ˢ connSet (G := G) T s) := by
  have h := stratumPiece_eq_split (G := G) (T := T) s Set.univ hT
  rw [stratumPiece, Set.preimage_univ, Set.inter_univ] at h
  rw [h]
  congr 2
  ext η
  simp [frontSet, extPreimage]

/-- The stratum piece as a split preimage rectangle. -/
theorem stratumPiece_eq_split_rect (T : Set V) (s : Finset V)
    (Y : Set (G.edgeSet → Bool)) (hT : T ⊆ (s : Set V)) :
    stratumPiece (G := G) T s Y =
      (boxOf (G := G) s).splitEquiv ⁻¹'
        ((frontSet (G := G) s ∩ extPreimage (G := G) s Y) ×ˢ connSet (G := G) T s) := by
  rw [stratumPiece_eq_split (G := G) (T := T) s Y hT]
  rfl

/-- **The exact rectangle formula on a random-region stratum.**  For a fixed
finite vertex region `s`, the joint law of the exterior field in `U` and the
interior in `W` on the stratum `{region = s}` factorizes: the exterior marginal
restricted to closed-frontier configurations, times the free FK mass of the
interior event intersected with the forced connectivity of the stratum. -/
theorem stratum_rect {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V) (s : Finset V) (hT : T ⊆ (s : Set V))
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {U : Set (boxOf (G := G) s).Exterior} {W : Set (boxOf (G := G) s).Interior}
    (hU : MeasurableSet U) (hW : MeasurableSet W) :
    (μ : Measure (G.edgeSet → Bool))
        ({ω : G.edgeSet → Bool | region G ω T = (s : Set V)} ∩
          (boxOf (G := G) s).splitEquiv ⁻¹' (U ×ˢ W)) =
      ((boxOf (G := G) s).exteriorMeasure μ) (U ∩ frontSet (G := G) s) *
        freeMass (G := G) hq hp s (W ∩ connSet (G := G) T s) := by
  have h := region_stratum_rect (G := G) (R := (s : Set V)) (hR := s.finite_toSet)
    (q := q) (p := p) hq hp μ hμ (T := T) hT (U := U) (W := W) hU hW
  simpa [frontSet, freeMass, connSet, frontierExterior] using h

/-- On the closed-frontier exterior the FK kernel of the region box is the free
measure, so the stratum pieces are computed by the free interior mass. -/
theorem stratumPiece_measure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V) (s : Finset V) (hT : T ⊆ (s : Set V))
    (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) =
      ((boxOf (G := G) s).exteriorMeasure μ)
          (frontSet (G := G) s ∩ extPreimage (G := G) s Y) *
        freeMass (G := G) hq hp s (connSet (G := G) T s) := by
  have hU : MeasurableSet (frontSet (G := G) s ∩ extPreimage (G := G) s Y) :=
    (measurableSet_frontSet (G := G) s).inter (measurableSet_extPreimage (G := G) s hY)
  have hglueω : ∀ ω : G.edgeSet → Bool,
      (boxOf (G := G) s).glue (((boxOf (G := G) s).splitEquiv ω).1,
        ((boxOf (G := G) s).splitEquiv ω).2) = ω :=
    fun ω => (boxOf (G := G) s).glue_split ω
  have hpiece : stratumPiece (G := G) T s Y =
      {ω : G.edgeSet → Bool | region G ω T = (s : Set V)} ∩
        (boxOf (G := G) s).splitEquiv ⁻¹'
          ((frontSet (G := G) s ∩ extPreimage (G := G) s Y) ×ˢ Set.univ) := by
    rw [stratumPiece_eq_split_rect (G := G) (T := T) s Y hT,
      region_stratum_eq_split (G := G) T s hT]
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Set.mem_univ, and_true]
    tauto
  rw [hpiece,
    stratum_rect (G := G) hq hp T s hT μ hμ hU MeasurableSet.univ,
    Set.univ_inter, Set.inter_right_comm, Set.inter_self]
/-! ## The per-stratum conditional identity -/

theorem freeMass_le_one {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (s : Finset V)
    (A : Set (boxOf (G := G) s).Interior) :
    freeMass (G := G) hq hp s A ≤ 1 := by
  haveI : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  calc freeMass (G := G) hq hp s A ≤ freeMass (G := G) hq hp s Set.univ :=
        measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem freeMass_ne_top {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (s : Finset V)
    (A : Set (boxOf (G := G) s).Interior) :
    freeMass (G := G) hq hp s A ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (freeMass_le_one (G := G) hq hp s A)

/-- **The rectangle formula on the split of a region box.**  For a measurable
exterior set `U` inside the closed-frontier event and a measurable interior set
`W`, the probability of "exterior in `U` and interior in `W` and the forced
connectivity" is the exterior marginal of `U` times the free interior FK mass of
`W` intersected with the connectivity event. -/
theorem stratum_split_rect {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {s : Finset V} (hT : T ⊆ (s : Set V))
    {μ : ProbabilityMeasure (G.edgeSet → Bool)}
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {U : Set (boxOf (G := G) s).Exterior} {W : Set (boxOf (G := G) s).Interior}
    (hU : MeasurableSet U) (hUfront : U ⊆ frontSet (G := G) s) (hW : MeasurableSet W) :
    (μ : Measure (G.edgeSet → Bool)) ((boxOf (G := G) s).splitEquiv ⁻¹'
        (U ×ˢ (W ∩ connSet (G := G) T s))) =
      ((boxOf (G := G) s).exteriorMeasure μ) U *
        freeMass (G := G) hq hp s (W ∩ connSet (G := G) T s) := by
  have hSU : (boxOf (G := G) s).splitEquiv ⁻¹' (U ×ˢ (W ∩ connSet (G := G) T s)) =
      {ω : G.edgeSet → Bool | region G ω T = (s : Set V)} ∩
        (boxOf (G := G) s).splitEquiv ⁻¹' (U ×ˢ W) := by
    rw [region_stratum_eq_split (G := G) T s hT, ← Set.preimage_inter, Set.prod_inter_prod,
      Set.inter_eq_right.mpr hUfront, Set.inter_comm (connSet (G := G) T s) W]
  rw [hSU, stratum_rect (G := G) hq hp T s hT μ hμ hU hW,
    Set.inter_eq_left.mpr hUfront]

/-- **Per-stratum conditional identity, cross-multiplied.**  On the stratum of
the random region `s` cut down by an exterior test `Y`, the probability of an
interior-supported event `C` is proportional to the free FK mass of its interior
readout intersected with the forced connectivity; the proportionality is
cross-multiplied so that no positivity is needed. -/
theorem stratum_cross_mul {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {s : Finset V} (hT : T ⊆ (s : Set V))
    {μ : ProbabilityMeasure (G.edgeSet → Bool)}
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    (hsupp : ∀ (η : (boxOf (G := G) s).Exterior) (i : (boxOf (G := G) s).Interior),
      (boxOf (G := G) s).glue (η, i) ∈ C ↔ i ∈ intSet (G := G) C s)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) *
        freeMass (G := G) hq hp s (connSet (G := G) T s) =
      freeMass (G := G) hq hp s (intSet (G := G) C s ∩ connSet (G := G) T s) *
        (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) := by
  classical
  have hU : MeasurableSet (frontSet (G := G) s ∩ extPreimage (G := G) s Y) :=
    (measurableSet_frontSet (G := G) s).inter (measurableSet_extPreimage (G := G) s hY)
  have hUfront : frontSet (G := G) s ∩ extPreimage (G := G) s Y ⊆ frontSet (G := G) s :=
    Set.inter_subset_left
  have hWint : MeasurableSet (intSet (G := G) C s) := measurableSet_intSet (G := G) hC s
  have hglueω : ∀ ω : G.edgeSet → Bool,
      (boxOf (G := G) s).glue (((boxOf (G := G) s).splitEquiv ω).1,
        ((boxOf (G := G) s).splitEquiv ω).2) = ω :=
    fun ω => (boxOf (G := G) s).glue_split ω
  have hpiece : stratumPiece (G := G) T s Y =
      (boxOf (G := G) s).splitEquiv ⁻¹'
        ((frontSet (G := G) s ∩ extPreimage (G := G) s Y) ×ˢ
          (Set.univ ∩ connSet (G := G) T s)) := by
    rw [stratumPiece_eq_split_rect (G := G) (T := T) s Y hT, Set.univ_inter]
  have hpieceC : C ∩ stratumPiece (G := G) T s Y =
      (boxOf (G := G) s).splitEquiv ⁻¹'
        ((frontSet (G := G) s ∩ extPreimage (G := G) s Y) ×ˢ
          (intSet (G := G) C s ∩ connSet (G := G) T s)) := by
    rw [stratumPiece_eq_split_rect (G := G) (T := T) s Y hT]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨hCmem, hA, hconn⟩
      have hCmem' : (boxOf (G := G) s).glue
          (((boxOf (G := G) s).splitEquiv ω).1, ((boxOf (G := G) s).splitEquiv ω).2) ∈ C := by
        rwa [hglueω ω]
      have hInt : ((boxOf (G := G) s).splitEquiv ω).2 ∈ intSet (G := G) C s :=
        (hsupp _ _).mp hCmem'
      exact ⟨hA, hInt, hconn⟩
    · rintro ⟨hA, hInt, hconn⟩
      refine ⟨?_, hA, hconn⟩
      have h := (hsupp ((boxOf (G := G) s).splitEquiv ω).1
        ((boxOf (G := G) s).splitEquiv ω).2).mpr hInt
      rw [hglueω ω] at h
      exact h
  rw [hpieceC, hpiece,
    stratum_split_rect (G := G) hq hp hT hμ hU hUfront MeasurableSet.univ,
    stratum_split_rect (G := G) hq hp hT hμ hU hUfront hWint,
    Set.univ_inter]
  ring

/-- **Per-stratum conditional identity in kernel form.**  With the normalization
made explicit, the conditional probability of the interior-supported event `C`
on the stratum equals the kernel value times the stratum mass.  No positivity
hypothesis: when the forced connectivity has zero free mass the stratum is null
and both sides vanish. -/
theorem stratum_cond_eq {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {s : Finset V} (hT : T ⊆ (s : Set V))
    {μ : ProbabilityMeasure (G.edgeSet → Bool)}
    (hμ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    (hsupp : ∀ (η : (boxOf (G := G) s).Exterior) (i : (boxOf (G := G) s).Interior),
      (boxOf (G := G) s).glue (η, i) ∈ C ↔ i ∈ intSet (G := G) C s)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) =
      kernelValue (G := G) hq hp T C (some s) *
        (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) := by
  classical
  have hcross : (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) *
        freeMass (G := G) hq hp s (connSet (G := G) T s) =
      freeMass (G := G) hq hp s (intSet (G := G) C s ∩ connSet (G := G) T s) *
        (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) :=
    stratum_cross_mul (G := G) hq hp hT hμ hC hsupp hY
  have hmass : (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) =
      ((boxOf (G := G) s).exteriorMeasure μ)
          (frontSet (G := G) s ∩ extPreimage (G := G) s Y) *
        freeMass (G := G) hq hp s (connSet (G := G) T s) :=
    stratumPiece_measure (G := G) hq hp T s hT μ hμ hY
  have hmle : (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) ≤
      (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) :=
    measure_mono (Set.inter_subset_right)
  set m : ℝ≥0∞ := freeMass (G := G) hq hp s (connSet (G := G) T s) with hm
  set w : ℝ≥0∞ := freeMass (G := G) hq hp s
    (intSet (G := G) C s ∩ connSet (G := G) T s) with hw
  set A : ℝ≥0∞ := ↑(((boxOf (G := G) s).exteriorMeasure μ)
    (frontSet (G := G) s ∩ extPreimage (G := G) s Y)) with hA
  have hcross' : (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) * m =
      w * (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) := by
    simpa only [← hm, ← hw] using hcross
  have hmass' : (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) = A * m := by
    simpa only [← hm, ← hA, ← hw] using hmass
  have hval : kernelValue (G := G) hq hp T C (some s) = m⁻¹ * w := rfl
  rw [hval]
  by_cases hm0 : m = 0
  · have hpiece0 : (μ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) = 0 := by
      rw [hmass', hm0, mul_zero]
    have hC0 : (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) = 0 :=
      le_antisymm (le_trans hmle (le_of_eq hpiece0)) zero_le
    rw [hC0, hpiece0, mul_zero]
  · have hunit : m * m⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hm0 (freeMass_ne_top (G := G) hq hp s _)
    have hstep : (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) * m =
        w * (A * m) := by
      rw [← hmass']
      exact hcross'
    calc (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y)
        = (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) * 1 := by
          rw [mul_one]
      _ = (μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) *
            (m * m⁻¹) := by rw [hunit]
      _ = ((μ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) * m) *
            m⁻¹ := by ring
      _ = (w * (A * m)) * m⁻¹ := by rw [hstep]
      _ = (m⁻¹ * w) * (μ : Measure (G.edgeSet → Bool))
            (stratumPiece (G := G) T s Y) := by rw [hmass']; ring
/-! ## Disintegration along the random region -/

/-- **The conditional law of an FK-Gibbs measure given the random closed
region.**  Let `μ` satisfy the DLR equations at the finite box of every finite
vertex region, let `C` be an event which, on the strata indexed by `Good`, is
read off from the interior configuration of the region box, and let `Y s` be an
exterior test for the stratum `s`.  Then

  `μ(C ∩ ⋃_{s ∈ Good} {region = s, exterior ∈ Y s})`

equals the integral, over the same union of strata, of the kernel value
`kernelValue (some s) C` — the normalized free FK mass of the interior readout
of `C` intersected with the forced interior connectivity of the stratum.

This is one identity for the whole random region, not a family of per-box
statements: there is no null set to intersect and no measurability of a
region-indexed kernel is assumed. -/
theorem region_kernel_disintegration {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V) (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    (Good : Finset V → Prop)
    (hsupp : ∀ s, Good s →
      ∀ (η : (boxOf (G := G) s).Exterior) (i : (boxOf (G := G) s).Interior),
        (boxOf (G := G) s).glue (η, i) ∈ C ↔ i ∈ intSet (G := G) C s)
    (Y : Finset V → Set (G.edgeSet → Bool)) (hY : ∀ s, MeasurableSet (Y s)) :
    (μ : Measure (G.edgeSet → Bool))
        (C ∩ ⋃ s : {s : Finset V // Good s},
          stratumPiece (G := G) T (s : Finset V) (Y (s : Finset V))) =
      ∫⁻ ω in (⋃ s : {s : Finset V // Good s},
          stratumPiece (G := G) T (s : Finset V) (Y (s : Finset V))),
        kernelValue (G := G) hq hp T C (regionIdx (G := G) T ω)
          ∂(μ : Measure (G.edgeSet → Bool)) := by
  classical
  set piece : {s : Finset V // Good s} → Set (G.edgeSet → Bool) :=
    fun s => stratumPiece (G := G) T (s : Finset V) (Y (s : Finset V)) with hpiece_def
  have hpiece_meas : ∀ s : {s : Finset V // Good s}, MeasurableSet (piece s) :=
    fun s => measurableSet_stratumPiece (G := G) T (s : Finset V) (hY (s : Finset V))
  have hpiece_disj : Pairwise (Function.onFun Disjoint piece) := by
    intro s s' hne
    exact stratumPiece_disjoint (G := G)
      (fun h => hne (Subtype.ext h)) (Y (s : Finset V)) (Y (s' : Finset V))
  have hdisjC : Pairwise (Function.onFun Disjoint fun s : {s : Finset V // Good s} =>
      C ∩ piece s) := by
    intro s s' hne
    exact (hpiece_disj hne).mono Set.inter_subset_right Set.inter_subset_right
  have hInter : C ∩ ⋃ s : {s : Finset V // Good s}, piece s =
      ⋃ s : {s : Finset V // Good s}, (C ∩ piece s) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  rw [hInter,
    measure_iUnion hdisjC (fun s => hC.inter (hpiece_meas s)),
    lintegral_iUnion hpiece_meas hpiece_disj]
  refine tsum_congr (fun s => ?_)
  by_cases hTsub : T ⊆ ((s : Finset V) : Set V)
  · have hval := stratum_cond_eq (G := G) hq hp hTsub (hμ (s : Finset V)) hC
      (hsupp (s : Finset V) s.2) (hY (s : Finset V))
    rw [hval]
    have hconst : ∫⁻ ω in piece s,
        kernelValue (G := G) hq hp T C (regionIdx (G := G) T ω) ∂
          (μ : Measure (G.edgeSet → Bool)) =
        ∫⁻ ω in piece s, kernelValue (G := G) hq hp T C (some (s : Finset V)) ∂
          (μ : Measure (G.edgeSet → Bool)) := by
      refine setLIntegral_congr_fun (hpiece_meas s) (fun ω hω => ?_)
      rw [regionIdx_eq_some_of_eq hω.1]
    rw [hconst, lintegral_const, Measure.restrict_apply_univ, mul_comm]
  · have hempty : piece s = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ω hω
      have hreg : region G ω T = ((s : Finset V) : Set V) := hω.1
      have hsub : T ⊆ ((s : Finset V) : Set V) := by
        rw [← hreg]
        exact subset_region (G := G) (ω := ω) T
      exact hTsub hsub
    rw [hempty, Set.inter_empty, measure_empty]
    simp
/-! ## Consequences: the kernel is law-independent, and cylinders -/

/-- The random-region conditional probability of an interior-supported event is
the same for *every* law satisfying the DLR equations at every finite box.  This
is the paper's step "the conditional law is the free random-cluster measure in
the interior", in cross-multiplied form so that no positivity of a stratum mass
is needed. -/
theorem region_cond_agree {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {s : Finset V} (hT : T ⊆ (s : Set V))
    {μ₁ μ₂ : ProbabilityMeasure (G.edgeSet → Bool)}
    (hμ₁ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ₁)
    (hμ₂ : (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ₂)
    {C : Set (G.edgeSet → Bool)} (hC : MeasurableSet C)
    (hsupp : ∀ (η : (boxOf (G := G) s).Exterior) (i : (boxOf (G := G) s).Interior),
      (boxOf (G := G) s).glue (η, i) ∈ C ↔ i ∈ intSet (G := G) C s)
    {Y : Set (G.edgeSet → Bool)} (hY : MeasurableSet Y) :
    (μ₁ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) *
        (μ₂ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) =
      (μ₂ : Measure (G.edgeSet → Bool)) (C ∩ stratumPiece (G := G) T s Y) *
        (μ₁ : Measure (G.edgeSet → Bool)) (stratumPiece (G := G) T s Y) := by
  have h₁ := stratum_cond_eq (G := G) hq hp hT hμ₁ hC hsupp hY
  have h₂ := stratum_cond_eq (G := G) hq hp hT hμ₂ hC hsupp hY
  rw [h₁, h₂]
  ring

/-- The random-region kernel is a probability measure on every stratum whose
forced connectivity event has positive free FK mass. -/
theorem regionKernelFun_isProbabilityMeasure {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {T : Set V} {s : Finset V} (ζ : G.edgeSet → Bool)
    (hpos : freeMass (G := G) hq hp s (connSet (G := G) T s) ≠ 0) :
    IsProbabilityMeasure (regionKernelFun (G := G) hq hp T (some s, ζ)) := by
  unfold regionKernelFun
  haveI hprob : IsProbabilityMeasure (freeMass (G := G) hq hp s) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (boxOf (G := G) s).graph hq hp (boxOf (G := G) s).graph.freeBoundary
  haveI hfin : IsFiniteMeasure (freeMass (G := G) hq hp s) :=
    ⟨lt_of_le_of_lt (freeMass_le_one (G := G) hq hp s Set.univ) ENNReal.one_lt_top⟩
  haveI hcond : IsProbabilityMeasure
      (ProbabilityTheory.cond (freeMass (G := G) hq hp s) (connSet (G := G) T s)) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  exact (Measure.isProbabilityMeasure_map_iff
    ((boxOf (G := G) s).measurable_glue_const_left _).aemeasurable).mpr hcond

/-! ## Cylinder events inside the region box -/

/-- **The random-region conditional law of a cylinder event.**  For a genuine
global cylinder `cylinder J S` whose base `J` is contained in the box of every
stratum under test, the conditional probability on each stratum of the random
closed region is the free finite-volume FK mass of the cylinder readout,
intersected with the forced interior connectivity and normalized.  This is the
form in which the source uses the identity. -/
theorem region_kernel_disintegration_cylinder {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V) (μ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp
      (fun η => exteriorPartition (G := G) ((s : Set V)) s.finite_toSet η)
      (measurable_exteriorPartition (G := G) ((s : Set V)) s.finite_toSet) μ)
    (J : Finset G.edgeSet) (S : Set (J → Bool)) (hS : MeasurableSet S)
    (Y : Finset V → Set (G.edgeSet → Bool)) (hY : ∀ s, MeasurableSet (Y s)) :
    (μ : Measure (G.edgeSet → Bool))
        (MeasureTheory.cylinder J S ∩ ⋃ s : {s : Finset V // J ⊆ (boxOf (G := G) s).edges},
          stratumPiece (G := G) T (s : Finset V) (Y (s : Finset V))) =
      ∫⁻ ω in (⋃ s : {s : Finset V // J ⊆ (boxOf (G := G) s).edges},
          stratumPiece (G := G) T (s : Finset V) (Y (s : Finset V))),
        kernelValue (G := G) hq hp T (MeasureTheory.cylinder J S)
          (regionIdx (G := G) T ω) ∂(μ : Measure (G.edgeSet → Bool)) := by
  classical
  refine region_kernel_disintegration (G := G) hq hp T μ hμ ?_
    (fun s => J ⊆ (boxOf (G := G) s).edges) ?_ Y hY
  · exact hS.cylinder J
  · intro s hs η i
    have hpre := FK.InfiniteVolume.FiniteBox.preimage_glue_boxCylinder
      (boxOf (G := G) s) J S hs η
    have hpre' := FK.InfiniteVolume.FiniteBox.preimage_glue_boxCylinder
      (boxOf (G := G) s) J S hs (boxOf (G := G) s).closedExterior
    have hInt : intSet (G := G) (MeasureTheory.cylinder J S) s =
        (boxOf (G := G) s).boxCylinder J S hs := hpre'
    rw [hInt, ← hpre]
    exact Iff.rfl
/-! ## Positivity of the forced connectivity on nonempty strata -/

/-- The free FK mass of a single interior configuration is positive for interior
edge weight `0 < p < 1` and `0 < q`. -/
theorem freeMass_singleton_pos {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (s : Finset V) (i : (boxOf (G := G) s).Interior) :
    freeMass (G := G) hq (le_of_lt hp₁) s {i} ≠ 0 := by
  classical
  have hsingle : freeMass (G := G) hq (le_of_lt hp₁) s {i} =
      (↑(FK.Finite.LabelledMultigraph.fkPMF (boxOf (G := G) s).graph hq
        (le_of_lt hp₁) (boxOf (G := G) s).graph.freeBoundary i) : ℝ≥0∞) := by
    unfold freeMass regionFreeMeasure
    exact FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton
      (boxOf (G := G) s).graph hq (le_of_lt hp₁)
      (boxOf (G := G) s).graph.freeBoundary i
  have hpmf : (FK.Finite.LabelledMultigraph.fkPMF (boxOf (G := G) s).graph hq
      (le_of_lt hp₁) (boxOf (G := G) s).graph.freeBoundary i : ℝ≥0∞) ≠ 0 := by
    rw [FK.Finite.LabelledMultigraph.fkPMF_apply]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (div_pos
      (FK.Finite.LabelledMultigraph.fkWeight_pos (boxOf (G := G) s).graph hq hp₀ hp₁
        (boxOf (G := G) s).graph.freeBoundary i)
      (FK.Finite.LabelledMultigraph.partitionFunction_pos (boxOf (G := G) s).graph hq
        (le_of_lt hp₁) (boxOf (G := G) s).graph.freeBoundary)))
  rw [hsingle]
  exact hpmf

/-- On a stratum that is actually attained, the forced interior connectivity has
positive free FK mass.  Hence the random-region conditional law is a genuine
probability measure there, not merely a sub-probability measure. -/
theorem freeMass_conn_ne_zero_of_nonempty_stratum {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p)
    (hp₁ : p < 1) {T : Set V} {s : Finset V}
    (hne : ∃ ω : G.edgeSet → Bool, region G ω T = (s : Set V)) :
    freeMass (G := G) hq (le_of_lt hp₁) s (connSet (G := G) T s) ≠ 0 := by
  classical
  obtain ⟨ω, hω⟩ := hne
  have hT : T ⊆ (s : Set V) := by
    rw [← hω]
    exact subset_region (G := G) (ω := ω) T
  have hgl : (boxOf (G := G) s).glue (((boxOf (G := G) s).splitEquiv ω).1,
      ((boxOf (G := G) s).splitEquiv ω).2) = ω := (boxOf (G := G) s).glue_split ω
  have hreg : region G ((boxOf (G := G) s).glue ((boxOf (G := G) s).splitEquiv ω)) T =
      (s : Set V) := by
    rw [hgl]
    exact hω
  have hconn : ((boxOf (G := G) s).splitEquiv ω).2 ∈ connSet (G := G) T s :=
    ((region_eq_iff (G := G) (R := (s : Set V)) (hR := s.finite_toSet) (T := T) _ hT).mp
      hreg).2
  have hsingle := freeMass_singleton_pos (G := G) hq hp₀ hp₁ s
    ((boxOf (G := G) s).splitEquiv ω).2
  have hpos : 0 < freeMass (G := G) hq (le_of_lt hp₁) s
      (connSet (G := G) T s) :=
    lt_of_lt_of_le (pos_of_ne_zero hsingle)
      (measure_mono (Set.singleton_subset_iff.mpr hconn))
  exact ne_of_gt hpos

/-- Consequently the random-region kernel fibre is a probability measure on every
stratum that is actually attained. -/
theorem regionKernelFun_isProbabilityMeasure_of_nonempty {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) {T : Set V} {s : Finset V}
    (hne : ∃ ω : G.edgeSet → Bool, region G ω T = (s : Set V))
    (ζ : G.edgeSet → Bool) :
    IsProbabilityMeasure
      (regionKernelFun (G := G) hq (le_of_lt hp₁) T (some s, ζ)) :=
  regionKernelFun_isProbabilityMeasure (G := G) hq (le_of_lt hp₁) ζ
    (freeMass_conn_ne_zero_of_nonempty_stratum (G := G) hq hp₀ hp₁ hne)

/-- The random-region kernel value is a measurable function of the
configuration: it depends on `ω` only through the random region index.  This is
the version statement needed to read the disintegration as a conditional
expectation. -/
theorem measurable_kernelValue_regionIdx {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (T : Set V) (C : Set (G.edgeSet → Bool)) :
    Measurable (fun ω : G.edgeSet → Bool =>
      kernelValue (G := G) hq hp T C (regionIdx (G := G) T ω)) := by
  classical
  have hrep : (fun ω : G.edgeSet → Bool =>
        kernelValue (G := G) hq hp T C (regionIdx (G := G) T ω)) =
      fun ω => ∑' s : Finset V,
        if regionIdx (G := G) T ω = some s then
          kernelValue (G := G) hq hp T C (some s) else 0 := by
    funext ω
    by_cases h : (region G ω T).Finite
    · have hsome : regionIdx (G := G) T ω = some h.toFinset := by
        unfold regionIdx
        rw [dif_pos h]
      rw [hsome, tsum_eq_single h.toFinset]
      · simp
      · intro b hb
        have hne : (some h.toFinset : Option (Finset V)) ≠ some b := by
          intro hc
          exact hb (Option.some.inj hc).symm
        simp [hne]
    · have hnone : regionIdx (G := G) T ω = none := (regionIdx_eq_none_iff T ω).mpr h
      have hzero : ∀ s : Finset V,
          (if regionIdx (G := G) T ω = some s then
            kernelValue (G := G) hq hp T C (some s) else 0) = 0 := by
        intro s
        rw [if_neg]
        rw [hnone]
        simp
      rw [hnone]
      simp [kernelValue, hzero]
  rw [hrep]
  exact Measurable.tsum (fun s => Measurable.ite
    (measurableSet_regionIdx_eq_some (G := G) T s) measurable_const measurable_const)

/-! ## Axiom audit -/

#print axioms FK.RandomRegionKernel.cutAt_eq_extendExterior
#print axioms FK.RandomRegionKernel.splitEquiv_cutAt_fst
#print axioms FK.RandomRegionKernel.measurable_cutAt
#print axioms FK.RandomRegionKernel.regionIdx_eq_some_iff
#print axioms FK.RandomRegionKernel.measurableSet_regionIdx_eq_some
#print axioms FK.RandomRegionKernel.measurableSet_region_finite
#print axioms FK.RandomRegionKernel.measurableSet_regionIdx_eq_none
#print axioms FK.RandomRegionKernel.measurableSet_connSet
#print axioms FK.RandomRegionKernel.measurableSet_intSet
#print axioms FK.RandomRegionKernel.regionKernelFun_apply_of_supported
#print axioms FK.RandomRegionKernel.measurableSet_stratumPiece
#print axioms FK.RandomRegionKernel.stratumPiece_disjoint
#print axioms FK.RandomRegionKernel.stratumPiece_eq_split
#print axioms FK.RandomRegionKernel.region_stratum_eq_split
#print axioms FK.RandomRegionKernel.stratum_rect
#print axioms FK.RandomRegionKernel.stratumPiece_measure
#print axioms FK.RandomRegionKernel.freeMass_le_one
#print axioms FK.RandomRegionKernel.stratum_split_rect
#print axioms FK.RandomRegionKernel.stratum_cross_mul
#print axioms FK.RandomRegionKernel.stratum_cond_eq
#print axioms FK.RandomRegionKernel.region_kernel_disintegration
#print axioms FK.RandomRegionKernel.region_cond_agree
#print axioms FK.RandomRegionKernel.regionKernelFun_isProbabilityMeasure
#print axioms FK.RandomRegionKernel.region_kernel_disintegration_cylinder
#print axioms FK.RandomRegionKernel.measurable_kernelValue_regionIdx
#print axioms FK.RandomRegionKernel.freeMass_singleton_pos
#print axioms FK.RandomRegionKernel.freeMass_conn_ne_zero_of_nonempty_stratum
#print axioms FK.RandomRegionKernel.regionKernelFun_isProbabilityMeasure_of_nonempty

end FK.RandomRegionKernel
