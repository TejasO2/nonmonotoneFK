import FK.RegionFrontierDetermination
import FK.SourceRegions
import FK.Theorem110Assembly
import FK.StrassenCountable

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

noncomputable section

namespace FK.ComparableNonpercolating

/-- Two nonnegative series, the smaller having finite sum, that are pointwise
ordered and have the same sum are equal term by term. -/
theorem eq_of_le_of_tsum_eq_tsum_ne_top {ι : Type*} {f g : ι → ℝ≥0∞}
    (hf : ∑' i, f i ≠ ∞) (hle : ∀ i, f i ≤ g i)
    (hsum : ∑' i, f i = ∑' i, g i) (i : ι) : f i = g i := by
  apply le_antisymm (hle i)
  by_contra hne
  have hlt : f i < g i := lt_of_le_not_ge (hle i) hne
  exact (ne_of_lt (ENNReal.tsum_lt_tsum hf hle hlt)) hsum

end FK.ComparableNonpercolating

namespace FK.ComparableNonpercolating

open FK.InfiniteVolume FK.RandomClosedBoundary FK.SourceRegions

universe u

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The global configuration event that the frontier of a fixed finite region is
closed. -/
def ambientFrontier (R : Set V) (hR : R.Finite) : Set (FKLimit.Configuration G.edgeSet) :=
  {ω | ClosedBoundary G (openSubgraph G ω) R}

lemma isLowerSet_ambientFrontier (R : Set V) (hR : R.Finite) :
    IsLowerSet (ambientFrontier (G := G) R hR) := by
  intro ω η hωη hη
  apply closedBoundary_of_forall_frontier_false (G := G)
  intro e hin hout
  have hωe : ω e = false := frontier_closed (G := G) hη hin hout
  have hle : η e ≤ ω e := hωη e
  cases hηe : η e
  · rfl
  · have : ¬ (true ≤ false) := by decide
    rw [hηe, hωe] at hle
    exact (this hle).elim

lemma restrictExterior_preimage_frontierExterior (R : Set V) (hR : R.Finite) :
    restrictExterior (G := G) R hR ⁻¹' frontierExterior (G := G) R hR =
      ambientFrontier (G := G) R hR := by
  classical
  ext ω
  change frontierSet (G := G) R hR (restrictExterior (G := G) R hR ω) ↔
    ClosedBoundary G (openSubgraph G ω) R
  constructor
  · intro h
    apply closedBoundary_of_forall_frontier_false (G := G)
    intro e hin hout
    have he : e ∉ (regionBoxOf (G := G) R hR).edges :=
      not_mem_regionBox_edges_of_crossing (G := G) R hR hout
    have h0 := h e hin hout
    change extendExterior (G := G) R hR (restrictExterior (G := G) R hR ω) e = false at h0
    change (if h' : e ∈ (regionBoxOf (G := G) R hR).edges then false else ω e) = false at h0
    simpa only [dif_neg he] using h0
  · intro h e hin hout
    have he : e ∉ (regionBoxOf (G := G) R hR).edges :=
      not_mem_regionBox_edges_of_crossing (G := G) R hR hout
    change extendExterior (G := G) R hR (restrictExterior (G := G) R hR ω) e = false
    change (if h' : e ∈ (regionBoxOf (G := G) R hR).edges then false else ω e) = false
    rw [dif_neg he]
    exact frontier_closed (G := G) h hin hout

lemma measurable_restrictExterior (R : Set V) (hR : R.Finite) :
    Measurable (restrictExterior (G := G) R hR) := by
  apply measurable_pi_lambda
  intro e
  exact measurable_pi_apply e.1

lemma measurableSet_ambientFrontier (R : Set V) (hR : R.Finite) :
    MeasurableSet (ambientFrontier (G := G) R hR) := by
  rw [← restrictExterior_preimage_frontierExterior (G := G) R hR]
  exact (measurableSet_frontierSet (G := G) R hR).preimage
    (measurable_restrictExterior (G := G) R hR)

lemma exteriorMeasure_frontierExterior_apply
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)) (R : Set V) (hR : R.Finite) :
    ((regionBoxOf (G := G) R hR).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) R hR).Exterior) (frontierExterior (G := G) R hR) =
      (μ : Measure (FKLimit.Configuration G.edgeSet)) (ambientFrontier (G := G) R hR) := by
  change Measure.map (fun ω => ((regionBoxOf (G := G) R hR).splitEquiv ω).1)
      (μ : Measure (FKLimit.Configuration G.edgeSet)) (frontierExterior (G := G) R hR) = _
  rw [Measure.map_apply]
  · congr 1
    exact restrictExterior_preimage_frontierExterior (G := G) R hR
  · exact (regionBoxOf (G := G) R hR).splitEquiv.measurable.fst
  · exact measurableSet_frontierSet (G := G) R hR

/-- Domination reverses the inequality on any frontier-closed event. -/
theorem exterior_frontier_le_of_stochasticallyDominates
    {μ ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)}
    (hdom : FKLimit.StochasticallyDominates ρ μ) (R : Set V) (hR : R.Finite) :
    ((regionBoxOf (G := G) R hR).exteriorMeasure ρ :
      Measure (regionBoxOf (G := G) R hR).Exterior) (frontierExterior (G := G) R hR) ≤
    ((regionBoxOf (G := G) R hR).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) R hR).Exterior) (frontierExterior (G := G) R hR) := by
  rw [exteriorMeasure_frontierExterior_apply, exteriorMeasure_frontierExterior_apply]
  let B := ambientFrontier (G := G) R hR
  have hB : MeasurableSet B := measurableSet_ambientFrontier (G := G) R hR
  have hcompl : (μ : Measure (FKLimit.Configuration G.edgeSet)) Bᶜ ≤
      (ρ : Measure (FKLimit.Configuration G.edgeSet)) Bᶜ := by
    have h' : μ Bᶜ ≤ ρ Bᶜ := hdom Bᶜ hB.compl (by
      intro ω η hωη hη hω
      exact hη (isLowerSet_ambientFrontier (G := G) R hR hωη hω))
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact_mod_cast h'
  apply ENNReal.le_of_add_le_add_right (a := (μ : Measure _) Bᶜ) (measure_ne_top _ _)
  calc
    (ρ : Measure _) B + (μ : Measure _) Bᶜ ≤
        (ρ : Measure _) B + (ρ : Measure _) Bᶜ := add_le_add_right hcompl _
    _ = 1 := by simpa only [measure_univ] using
      (measure_add_measure_compl (μ := (ρ : Measure _)) hB)
    _ = (μ : Measure _) B + (μ : Measure _) Bᶜ := by
      simpa only [measure_univ] using
        (measure_add_measure_compl (μ := (μ : Measure _)) hB).symm

end FK.ComparableNonpercolating

namespace FK.ComparableNonpercolating

open FK.InfiniteVolume FK.RandomClosedBoundary FK.SourceRegions
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- Exact all-region DLR input used by the frontier-stratum identities. -/
def CanonicalRegionDLR {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)) : Prop :=
  ∀ s : Finset V,
    (regionBoxOf (G := G) (s : Set V) s.finite_toSet).IsDLR hq hp
      (exteriorPartition (G := G) (s : Set V) s.finite_toSet)
      (measurable_exteriorPartition (G := G) (s : Set V) s.finite_toSet) μ

/-- The random closed region based at every finite vertex set is almost surely
finite.  Infinite bases are deliberately not required. -/
def FiniteRegionOnFiniteBases (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)) : Prop :=
  ∀ T : Set V, T.Finite → ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
    (region G ω T).Finite

/-- Summand in the total-mass decomposition of a law over its random-region
strata. -/
def stratumTerm {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (T : Set V) (s : Finset V) : ℝ≥0∞ :=
  if h : T ⊆ (s : Set V) then
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) *
    regionFreeMeasure (G := G) (s : Set V) s.finite_toSet hq hp
      (interiorConnectSet (G := G) (s : Set V) s.finite_toSet T)
  else 0

/-- Total mass is one on every finite-base random-region stratum decomposition. -/
theorem tsum_stratumTerm_eq_one {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hfin : FiniteRegionOnFiniteBases (G := G) μ)
    {T : Set V} (hT : T.Finite) :
    ∑' s : Finset V, stratumTerm (G := G) hq hp μ T s = 1 := by
  classical
  have h := FK.M3.apply_eq_tsum_stratum (G := G) hq hp T μ (hfin T hT)
    (A := Set.univ) MeasurableSet.univ
  rw [measure_univ] at h
  refine (h.trans ?_).symm
  apply tsum_congr
  intro s
  by_cases hTs : T ⊆ (s : Set V)
  · rw [stratumTerm, dif_pos hTs, Set.univ_inter]
    exact FK.M3.region_stratum_mass (G := G) hq hp (s : Set V) s.finite_toSet μ
      (hμ s) hTs
  · rw [stratumTerm, dif_neg hTs]
    have hempty : (Set.univ ∩ {ω : FKLimit.Configuration G.edgeSet |
        region G ω T = (s : Set V)}) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      apply hTs
      rw [← hω.2]
      exact subset_region (G := G) (ω := ω) T
    rw [hempty, measure_empty]

lemma interiorConnectSet_base_eq_univ (s : Finset V) :
    interiorConnectSet (G := G) (s : Set V) s.finite_toSet (s : Set V) = Set.univ := by
  ext i
  simp only [interiorConnectSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro x hx
  exact ⟨x, hx, OpenConnected.refl _ _ x⟩

lemma stratumTerm_base_self {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)) (s : Finset V) :
    stratumTerm (G := G) hq hp μ (s : Set V) s =
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet) := by
  haveI : IsProbabilityMeasure
      (regionFreeMeasure (G := G) (s : Set V) s.finite_toSet hq hp) :=
    FK.Finite.LabelledMultigraph.fkMeasure_isProbabilityMeasure
      (regionBoxOf (G := G) (s : Set V) s.finite_toSet).graph hq hp
      (regionBoxOf (G := G) (s : Set V) s.finite_toSet).graph.freeBoundary
  rw [stratumTerm, dif_pos (Set.Subset.refl _), interiorConnectSet_base_eq_univ,
    measure_univ, mul_one]

/-- **Equality of comparable random-region laws at their frontier masses.**
If `ρ` stochastically dominates `μ`, both satisfy the canonical all-region DLR
identities and their finite-base regions are almost surely finite, then every
frontier-closed mass is the same under `μ` and `ρ`. -/
theorem frontier_mass_eq_of_stochasticallyDominates
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hρ : CanonicalRegionDLR (G := G) hq hp ρ)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hρfin : FiniteRegionOnFiniteBases (G := G) ρ)
    (hdom : FKLimit.StochasticallyDominates ρ μ) (s : Finset V) :
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) =
    ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure ρ :
      Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
      (frontierExterior (G := G) (s : Set V) s.finite_toSet) := by
  let f := stratumTerm (G := G) hq hp ρ (s : Set V)
  let g := stratumTerm (G := G) hq hp μ (s : Set V)
  have hle : ∀ t : Finset V, f t ≤ g t := by
    intro t
    by_cases hst : (s : Set V) ⊆ (t : Set V)
    · simp only [f, g, stratumTerm, dif_pos hst]
      exact mul_le_mul_of_nonneg_right
        (exterior_frontier_le_of_stochasticallyDominates (G := G) hdom
          (t : Set V) t.finite_toSet) (by simp)
    · simp only [f, g, stratumTerm, dif_neg hst, le_refl]
  have hsum : ∑' t : Finset V, f t = ∑' t : Finset V, g t := by
    rw [tsum_stratumTerm_eq_one (G := G) hq hp ρ hρ hρfin s.finite_toSet,
      tsum_stratumTerm_eq_one (G := G) hq hp μ hμ hμfin s.finite_toSet]
  have htop : ∑' t : Finset V, f t ≠ ∞ := by
    rw [tsum_stratumTerm_eq_one (G := G) hq hp ρ hρ hρfin s.finite_toSet]
    exact ENNReal.one_ne_top
  have hterm := eq_of_le_of_tsum_eq_tsum_ne_top htop hle hsum s
  dsimp [f, g] at hterm
  rw [stratumTerm_base_self, stratumTerm_base_self] at hterm
  exact hterm.symm

end FK.ComparableNonpercolating

namespace FK.ComparableNonpercolating

open FK.InfiniteVolume FK.RandomClosedBoundary FK.SourceRegions
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.propDecidable

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- Almost-sure nonpercolation is exactly the finite-base input needed by the
random-region decomposition. -/
theorem finiteRegionOnFiniteBases_of_ae_nonPercolating
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) : FiniteRegionOnFiniteBases (G := G) μ := by
  intro T hT
  filter_upwards [hμ] with ω hω
  exact region_finite (G := G) hT (finiteOpenClusters_of_nonPercolating G ω hω)

/-- Finite-base strengthening of frontier-mass determination.  In particular,
no finiteness premise is imposed on regions based at an infinite set. -/
theorem eq_of_canonicalRegionDLR_of_frontier_mass_eq
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hν : CanonicalRegionDLR (G := G) hq hp ν)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hνfin : FiniteRegionOnFiniteBases (G := G) ν)
    (hmass : ∀ s : Finset V,
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure μ :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet) =
      ((regionBoxOf (G := G) (s : Set V) s.finite_toSet).exteriorMeasure ν :
        Measure (regionBoxOf (G := G) (s : Set V) s.finite_toSet).Exterior)
        (frontierExterior (G := G) (s : Set V) s.finite_toSet)) : μ = ν := by
  classical
  refine ProbabilityMeasure.toMeasure_injective
    (FK.InfiniteVolume.measure_eq_of_forall_dependsOn (fun F A hA => ?_))
  set T : Set V := {x : V | ∃ e ∈ F, x ∈ (e.1 : Sym2 V)} with hTdef
  have hTfin : T.Finite := by
    refine Set.Finite.subset (F.finite_toSet.biUnion fun e _ => FK.M3.finite_mem_sym2 (V := V) e.1) ?_
    rintro x ⟨e, he, hx⟩
    exact Set.mem_biUnion he hx
  have hFsub : ∀ e ∈ F, e ∈ interiorEdgeSet G T := by
    intro e he
    rw [mem_interiorEdgeSet_iff]
    exact fun x hx => ⟨e, he, hx⟩
  let term : ProbabilityMeasure (FKLimit.Configuration G.edgeSet) → Finset V → ℝ≥0∞ :=
    fun κ s =>
      if h : T ⊆ (s : Set V) then
        ((regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).exteriorMeasure κ :
          Measure (regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).Exterior)
          (frontierExterior (G := G) ((s : Set V)) s.finite_toSet) *
        regionFreeMeasure (G := G) ((s : Set V)) s.finite_toSet hq hp
          ((regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).interiorRestriction '' A ∩
            interiorConnectSet (G := G) ((s : Set V)) s.finite_toSet T)
      else 0
  have hterm : ∀ (κ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet)),
      CanonicalRegionDLR (G := G) hq hp κ →
      FiniteRegionOnFiniteBases (G := G) κ →
      (κ : Measure (FKLimit.Configuration G.edgeSet)) A = ∑' s, term κ s := by
    intro κ hκ hκfin
    rw [FK.M3.apply_eq_tsum_stratum (G := G) hq hp T κ (hκfin T hTfin) hA.measurableSet]
    refine tsum_congr fun s => ?_
    by_cases h : T ⊆ (s : Set V)
    · have hFs : F ⊆ (regionBoxOf (G := G) ((s : Set V)) s.finite_toSet).edges := by
        intro e he
        rw [mem_regionBox_edges_iff, mem_interiorEdgeSet_iff]
        exact fun x hx => h (hFsub e he x hx)
      simp only [term, dif_pos h]
      exact FK.M3.stratum_apply_eq (G := G) hq hp s h κ (hκ s) (hA.mono hFs)
    · have hempty : A ∩ {ω : FKLimit.Configuration G.edgeSet |
        region G ω T = (s : Set V)} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        intro hreg
        exact h (hreg.2 ▸ subset_region (G := G) T)
      simp only [term, dif_neg h]
      rw [hempty, measure_empty]
  rw [hterm μ hμ hμfin, hterm ν hν hνfin]
  congr 1
  funext s
  by_cases h : T ⊆ (s : Set V)
  · simp only [term, dif_pos h]
    rw [hmass s]
  · simp only [term, dif_neg h]

/-- **Comparable nonpercolating canonical region-DLR laws are equal.** -/
theorem eq_of_stochasticallyDominates_of_canonicalRegionDLR
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : CanonicalRegionDLR (G := G) hq hp μ)
    (hρ : CanonicalRegionDLR (G := G) hq hp ρ)
    (hμfin : FiniteRegionOnFiniteBases (G := G) μ)
    (hρfin : FiniteRegionOnFiniteBases (G := G) ρ)
    (hdom : FKLimit.StochasticallyDominates ρ μ) : μ = ρ := by
  apply eq_of_canonicalRegionDLR_of_frontier_mass_eq (G := G) hq hp μ ρ hμ hρ hμfin hρfin
  intro s
  exact frontier_mass_eq_of_stochasticallyDominates (G := G) hq hp μ ρ hμ hρ hμfin hρfin hdom s

end FK.ComparableNonpercolating

namespace FK.ComparableNonpercolating

open FK.InfiniteVolume FK.RandomClosedBoundary FK.SourceRegions FK.RandomRegionKernel
open CurvatureVariance.Infra.Percolation

universe u

attribute [local instance] Classical.propDecidable

local instance sourceBoundaryMeasurableSpace (X : Type*) : MeasurableSpace (Setoid X) := ⊤

local instance sourceFiniteSetoid (X : Type*) [Finite X] : Finite (Setoid X) := by
  classical
  apply Finite.of_injective (fun α : Setoid X => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- Every exterior component of a nonpercolating ambient configuration has
finite source infinitude certificate. -/
theorem not_sourceInfinite_of_nonPercolating {s : Finset V}
    {ω : FKLimit.Configuration G.edgeSet} (hω : ω ∈ FK.NonPercolating G)
    (x : (boxOf (G := G) s).Vertex) :
    ¬ sourceInfinite (G := G) s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) x := by
  intro hinf
  apply hinf
  apply (hω x.1).subset
  intro z hz
  have hz' : OpenConnected G ω (nonInteriorEdges (s : Set V)) x.1 z := by
    obtain ⟨p, hp⟩ := hz
    exact ⟨p, isOpenIn_of_isOpenIn_extendExterior_restrict
      s.finite_toSet ω p hp⟩
  exact OpenConnected.mono_edges hz' (Set.subset_univ _)

/-- At a nonpercolating configuration, a geometric source convention has no
choice left: it is the actual exterior-component partition. -/
theorem sourcePartition_eq_sourceComponents_of_nonPercolating
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (s : Finset V) {ω : FKLimit.Configuration G.edgeSet}
    (hω : ω ∈ FK.NonPercolating G) :
    Φ.partition s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) =
      sourceComponents (G := G) s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) := by
  apply ConventionGeometry.eq_openComponents_of_finite_separation
    (sourceComponents (G := G) s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))
    (Φ.partition s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))
    (sourceInfinite (G := G) s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))
  · exact hΦ.1 s _
  · exact hΦ.2 s _
  · intro x y hx _hy
    exact (not_sourceInfinite_of_nonPercolating (G := G) hω x hx).elim

/-- Convert a general geometric source-DLR law into the canonical all-region
DLR form, using only its almost-sure nonpercolation. -/
theorem canonicalRegionDLR_of_sourceDLR_of_ae_nonPercolating
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ)
    (hμnp : ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G) : CanonicalRegionDLR (G := G) hq hp μ := by
  have hcanon : ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp
      (exteriorPartition (G := G) (s : Set V) s.finite_toSet)
      (measurable_exteriorPartition (G := G) (s : Set V) s.finite_toSet) μ := by
    intro s
    apply (boxOf (G := G) s).isDLR_of_ae_partition_eq hq hp
      (Φ.partition s) (exteriorPartition (G := G) (s : Set V) s.finite_toSet)
      (Φ.measurable_partition s)
      (measurable_exteriorPartition (G := G) (s : Set V) s.finite_toSet)
      μ (hμ s)
    change ∀ᵐ η ∂Measure.map (fun ω => ((boxOf (G := G) s).splitEquiv ω).1)
      (μ : Measure (FKLimit.Configuration G.edgeSet)),
      Φ.partition s η = exteriorPartition (G := G) (s : Set V) s.finite_toSet η
    have hset : MeasurableSet {η : (boxOf (G := G) s).Exterior |
        Φ.partition s η = exteriorPartition (G := G) (s : Set V) s.finite_toSet η} :=
      measurableSet_eq_fun (Φ.measurable_partition s)
        (measurable_exteriorPartition (G := G) (s : Set V) s.finite_toSet)
    apply (ae_map_iff (boxOf (G := G) s).splitEquiv.measurable.fst.aemeasurable hset).2
    filter_upwards [hμnp] with ω hω
    exact sourcePartition_eq_sourceComponents_of_nonPercolating Φ hΦ s hω
  exact hcanon

/-- **Comparable nonpercolating laws for any geometric source convention are
equal.** -/
theorem eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hμ : μ ∈ SourceDLRMeasures Φ) (hρ : ρ ∈ SourceDLRMeasures Φ)
    (hμnp : ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hρnp : ∀ᵐ ω ∂(ρ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hdom : FKLimit.StochasticallyDominates ρ μ) : μ = ρ := by
  apply eq_of_stochasticallyDominates_of_canonicalRegionDLR (G := G) hq hp μ ρ
  · exact canonicalRegionDLR_of_sourceDLR_of_ae_nonPercolating hq hp Φ hΦ μ hμ hμnp
  · exact canonicalRegionDLR_of_sourceDLR_of_ae_nonPercolating hq hp Φ hΦ ρ hρ hρnp
  · exact finiteRegionOnFiniteBases_of_ae_nonPercolating μ hμnp
  · exact finiteRegionOnFiniteBases_of_ae_nonPercolating ρ hρnp
  · exact hdom

/-- If a nonpercolating dominant itself belongs to a geometric source-DLR class
and dominates every member, that class is exactly the singleton containing the
dominant.  No product or Dirac structure is required of the dominant. -/
theorem sourceDlr_eq_singleton_of_mem_nonpercolating_dominant
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention G hq hp) (hΦ : IsSourceGeometry Φ) (hG : G.Connected)
    (ρ : ProbabilityMeasure (FKLimit.Configuration G.edgeSet))
    (hρ : ρ ∈ SourceDLRMeasures Φ)
    (hρnp : ∀ᵐ ω ∂(ρ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (hdom : ∀ μ ∈ SourceDLRMeasures Φ, FKLimit.StochasticallyDominates ρ μ) :
    SourceDLRMeasures Φ = {ρ} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hρ, fun μ hμ => ?_⟩
  have hμnp : ∀ᵐ ω ∂(μ : Measure (FKLimit.Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G := by
    obtain ⟨γ, hγμ, hγρ, hγord⟩ :=
      FKLimit.exists_orderedCoupling_of_stochasticallyDominates (hdom μ hμ)
    apply FK.ae_nonPercolating_of_orderedCoupling G hG (γ := (γ : Measure _))
      (μ := (μ : Measure _)) (ρ := (ρ : Measure _)) ?_ ?_ hγord hρnp
    · exact congrArg Subtype.val hγμ
    · exact congrArg Subtype.val hγρ
  exact eq_of_stochasticallyDominates_of_sourceDLR_of_ae_nonPercolating hq hp
    Φ hΦ μ ρ hμ hρ hμnp hρnp (hdom μ hμ)

end FK.ComparableNonpercolating

/-! ## Axiom audit -/
