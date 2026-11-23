import FK.NestedRadialCounterexample

/-!
# Bad-configuration root attachment for nested metric estimates

The fixed-root criterion in `NestedRadialCounterexample` asks for root attachment
in every configuration.  This module sharpens it in three ways.

* On an all-closed configuration, open connection implies equality.  Hence the
  original all-configurations hypothesis forces every left vertex of a fixed
  split to belong to the root set.
* The actual exceptional-set inclusion needs root attachment only on
  configurations outside the maximal split stratum.
* Fixed-root arm events have explicit finite metric support.  Thus the sharper
  inclusion can be used with the nonpercolating fixed-root arm limit.

These are scoped geometric/locality results.  No new `hgood` identity, random
stopping-region FK identity, or whole-paper uniqueness theorem is asserted.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal Topology unitInterval Sym2 SimpleGraph

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- An all-closed configuration has no open path between distinct vertices. -/
theorem eq_of_openConnected_all_closed {x y : V}
    (h : OpenConnected G (fun _ => false) Set.univ x y) : x = y := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail a b hx hab ih =>
      rw [CurvatureVariance.Infra.Percolation.openGraph, SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨⟨e, he, hee⟩, -⟩ := hab
      cases he

/-- **Exact obstruction to all-configurations attachment on a fixed split.**
If every configuration attaches every left vertex to a root, then already the
all-closed configuration forces the image of every left vertex to be a root.
A fixed small root set therefore cannot serve a fixed split with any additional
left vertex; a random/explored region or a bad-only hypothesis is necessary. -/
theorem mem_roots_of_rootAttached_all_configurations
    {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (f : U ⊕ K → V) (roots : Finset V)
    (hroot : ∀ z, ∀ u, ∃ a ∈ roots,
      OpenConnected G (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
        (f (Sum.inl u))) :
    ∀ u, f (Sum.inl u) ∈ roots := by
  intro u
  obtain ⟨a, ha, hau⟩ := hroot (fun _ => false) u
  have hconf : BS.glue (BS.closedExterior,
      BS.reindex jS (fun _ => false)) = (fun _ => false) := by
    funext e
    simp only [FiniteBox.glue]
    split_ifs <;> rfl
  have hay : a = f (Sum.inl u) := by
    apply eq_of_openConnected_all_closed
    rw [← hconf]
    exact hau
  rwa [← hay]

/-- The finite-root arm inclusion with attachment required **only on the bad
configuration**.  Unlike the preceding fixed-split premise, the all-closed
(maximal-stratum) configuration is not asked to attach its left vertices. -/
theorem bad_maximalSplit_subset_closedLocalEvent_finiteRootArms_of_bad
    (hG : G.Connected) {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1)
    (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hfar : ∀ k, n + L ≤ G.dist o (f (Sum.inr k)))
    (hroot : ∀ z, (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z ∘ d) ∉
      maximalSplitStratum si ti so xo → ∀ u, ∃ a ∈ roots,
      OpenConnected G (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
        (f (Sum.inl u))) :
    (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) ⁻¹'
      ((fun ρ : (BD.indexedGraph jD).Configuration => ρ ∘ d) ⁻¹'
        maximalSplitStratum si ti so xo))ᶜ ⊆
      BS.reindex jS ⁻¹' closedLocalEvent BS (finiteRootArms G roots n) := by
  intro z hz
  change (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z ∘ d) ∉
    maximalSplitStratum si ti so xo at hz
  change BS.glue (BS.closedExterior, BS.reindex jS z) ∈ finiteRootArms G roots n
  exact RegionSplit.RootAttached.mem_finiteRootArms_of_not_mem_maximalSplitStratum
    hG si ti so xo _ _
    (nestedOpenPathMap BS BD jS jD hBD si ti so xo d z f hend)
    roots o L n hA hfar (hroot z hz) hz

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.eq_of_openConnected_all_closed
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.mem_roots_of_rootAttached_all_configurations
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.bad_maximalSplit_subset_closedLocalEvent_finiteRootArms_of_bad

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.NestedAssembly

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The explicit finite edge support of all radius-`n` arms from `roots`. -/
noncomputable def finiteRootArmEdges [G.LocallyFinite]
    (hG : G.Connected) (roots : Finset V) (n : ℕ) : Finset G.edgeSet :=
  roots.biUnion fun a => NestedMetricGeometry.metricEdges hG a n

/-- The simultaneous finite-root arm event depends only on its displayed
finite edge support. -/
theorem finiteRootArms_dependsOnCoordinates [G.LocallyFinite]
    (hG : G.Connected) (roots : Finset V) (n : ℕ) :
    FKLimit.DependsOnCoordinates (finiteRootArms G roots n)
      (finiteRootArmEdges hG roots n) := by
  intro ω η hωη
  have harm (a : V) (ha : a ∈ roots) :
      (ω ∈ armEvent G a n ↔ η ∈ armEvent G a n) := by
    apply Iff.of_eq
    apply dependsOn_armEvent hG a n
    intro e he
    apply hωη
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, (NestedMetricGeometry.mem_metricEdges hG a n e).2 he⟩
  constructor
  · intro h
    obtain ⟨a, h⟩ := Set.mem_iUnion.1 h
    obtain ⟨ha, hωa⟩ := Set.mem_iUnion.1 h
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, (harm a ha).1 hωa⟩⟩
  · intro h
    obtain ⟨a, h⟩ := Set.mem_iUnion.1 h
    obtain ⟨ha, hηa⟩ := Set.mem_iUnion.1 h
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, (harm a ha).2 hηa⟩⟩

/-- If every root is within distance `L` of `o`, every radius-`n` arm
coordinate lies in the actual metric box of radius `n+L` about `o`. -/
theorem finiteRootArmEdges_subset_metricBox [G.LocallyFinite]
    (hG : G.Connected) (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L) :
    finiteRootArmEdges hG roots n ⊆
      (NestedMetricGeometry.metricBox hG o (n + L)).edges := by
  intro e he
  obtain ⟨a, ha, hea⟩ := Finset.mem_biUnion.1 he
  apply (NestedMetricGeometry.mem_metricEdges hG o (n + L) e).2
  obtain ⟨x, hx, hxn⟩ := (NestedMetricGeometry.mem_metricEdges hG a n e).1 hea
  refine ⟨x, hx, ?_⟩
  have htri := hG.dist_triangle (u := o) (v := a) (w := x)
  have hoa := hA a ha
  omega

/-- Metric finite-coordinate realization of the simultaneous fixed-root arm
event.  The box has the same center and radius `n+L` used by the geometric
root-attachment inclusion. -/
theorem finiteRootArms_dependsOnCoordinates_metricBox [G.LocallyFinite]
    (hG : G.Connected) (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L) :
    FKLimit.DependsOnCoordinates (finiteRootArms G roots n)
      (NestedMetricGeometry.metricBox hG o (n + L)).edges :=
  (finiteRootArms_dependsOnCoordinates hG roots n).mono
    (finiteRootArmEdges_subset_metricBox hG roots o L n hA)

/-- Closing the exterior of the displayed metric box realizes exactly the
fixed-root arm event, not merely a larger far-connection event. -/
theorem preimage_interiorRestriction_closedLocalEvent_finiteRootArms
    [G.LocallyFinite] (hG : G.Connected) (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L) :
    (NestedMetricGeometry.metricBox hG o (n + L)).interiorRestriction ⁻¹'
      NestedMetricGeometry.closedLocalEvent
        (NestedMetricGeometry.metricBox hG o (n + L)) (finiteRootArms G roots n) =
      finiteRootArms G roots n :=
  NestedMetricGeometry.preimage_interiorRestriction_closedLocalEvent _ _
    (finiteRootArms_dependsOnCoordinates_metricBox hG roots o L n hA)

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.finiteRootArms_dependsOnCoordinates
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.finiteRootArmEdges_subset_metricBox
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.finiteRootArms_dependsOnCoordinates_metricBox
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.preimage_interiorRestriction_closedLocalEvent_finiteRootArms

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- **Nested finite-volume estimate with a fixed-root arm error.**  The
exceptional-set inclusion is proved from bad-configuration root attachment,
not assumed.  Finite-coordinate realization is discharged by `hdep`.  The
only stochastic input is the explicitly displayed, unchanged `hgood`; this is
a conditional one-scale estimate, not a random-region FK identity or a
strong-uniqueness theorem. -/
theorem finiteBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad
    (hG : G.Connected) {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (α : BS.BoundaryPartition) (β : BD.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool))
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1)
    (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hfar : ∀ k, n + L ≤ G.dist o (f (Sum.inr k)))
    (hroot : ∀ z, (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z ∘ d) ∉
      maximalSplitStratum si ti so xo → ∀ u, ∃ a ∈ roots,
      OpenConnected G (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
        (f (Sum.inl u)))
    (hdep : FKLimit.DependsOnCoordinates (finiteRootArms G roots n) BS.edges)
    (hgood :
      let e := nestedEdgeEquiv BS BD jS jD hBD
      let C : Set (BD.indexedGraph jD).Configuration :=
        (fun ρ : (BD.indexedGraph jD).Configuration => ρ ∘ d) ⁻¹'
          maximalSplitStratum si ti so xo
      let t := fkNestedOrderedTriple
        (fun i => BS.source (jS i)) (fun i => BS.target (jS i))
        (fun i => BD.source (jD i)) (fun i => BD.target (jD i))
        (outsideGraph BS BD) e (BS.indexedBoundary jS α)
        (BD.indexedBoundary jD β) hq hp₀ hp₁
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹'
            (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹'
            (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C))) :
    |(BS.finiteVolumeLaw hq hp₁.le α : Measure (Configuration G.edgeSet)).real
          (cylinder J S) -
        (BD.finiteVolumeLaw hq hp₁.le β : Measure (Configuration G.edgeSet)).real
          (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (finiteRootArms G roots n) := by
  let e := nestedEdgeEquiv BS BD jS jD hBD
  let C : Set (BD.indexedGraph jD).Configuration :=
    (fun ρ : (BD.indexedGraph jD).Configuration => ρ ∘ d) ⁻¹'
      maximalSplitStratum si ti so xo
  have he : ∀ i : J,
      e (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) = jS.symm ⟨i.1, hJS i.2⟩ := by
    intro i
    exact nestedEdgeEquiv_inl BS BD jS jD hBD J hJS hJD i
  have hU : BS.interiorRestriction ⁻¹'
      closedLocalEvent BS (finiteRootArms G roots n) = finiteRootArms G roots n :=
    preimage_interiorRestriction_closedLocalEvent BS _ hdep
  have hD : (restrictΔ e ⁻¹' C)ᶜ ⊆
      BS.reindex jS ⁻¹' closedLocalEvent BS (finiteRootArms G roots n) :=
    bad_maximalSplit_subset_closedLocalEvent_finiteRootArms_of_bad
      hG BS BD jS jD hBD si ti so xo d f hend roots o L n hA hfar hroot
  have h := finiteBox_cylinder_abs_sub_le_interiorUpper_of_good
    BS BD jS jD (outsideGraph BS BD) e α β hq hp₀ hp₁ J S hJS hJD he C
    (closedLocalEvent BS (finiteRootArms G roots n))
    (finiteRootArms G roots n) hU hgood hD
  change |(BS.finiteVolumeLaw hq hp₁.le α : Measure (Configuration G.edgeSet)).real
      (cylinder J S) -
    (BD.finiteVolumeLaw hq hp₁.le β : Measure (Configuration G.edgeSet)).real
      (cylinder J S)| ≤
    (Measure.infinitePi (fun _ : G.edgeSet => bernoulliMeasure true false
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)))).real
      (finiteRootArms G roots n) at h
  exact h

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.finiteBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- With the usual right-endpoint condition, the all-closed nested
configuration is in the maximal stratum.  Hence it is outside the domain on
which `bad_maximalSplit_subset_closedLocalEvent_finiteRootArms_of_bad` asks for
root attachment. -/
theorem allClosed_mem_maximalSplitStratum_nested
    {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (hright : ExteriorHasRight so xo) :
    (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) (fun _ => false) ∘ d) ∈
      maximalSplitStratum si ti so xo := by
  change (fun _ : Fin m ⊕ Fin k => false) ∈ maximalSplitStratum si ti so xo
  apply (mem_maximalSplitStratum_iff si ti so xo _ hright).2
  intro i hi
  change false = true at hi
  contradiction

/-- Metric support can be transported to any larger actual observation box. -/
theorem finiteRootArms_dependsOnCoordinates_of_metricBox_subset
    [G.LocallyFinite] (hG : G.Connected) (BS : FiniteBox G.edgeSet)
    (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hsub : (NestedMetricGeometry.metricBox hG o (n + L)).edges ⊆ BS.edges) :
    FKLimit.DependsOnCoordinates (finiteRootArms G roots n) BS.edges :=
  (finiteRootArms_dependsOnCoordinates_metricBox hG roots o L n hA).mono hsub

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.allClosed_mem_maximalSplitStratum_nested
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.finiteRootArms_dependsOnCoordinates_of_metricBox_subset

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Actual centered metric-box specialization.  Here `r ≤ N` are the two FK
scales and `n+L ≤ N` makes the fixed-root arm event local in the larger box.
The right vertices of the supplied split lie beyond radius `n+L`; the roots
stay in the fixed ball of radius `L`. -/
theorem metricBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool)) {N r L n : ℕ}
    (hnN : n + L ≤ N) (hrN : r ≤ N)
    (α : (metricBox hG o N).BoundaryPartition)
    (β : (metricBox hG o r).BoundaryPartition)
    (hJD : J ⊆ (metricBox hG o r).edges)
    {m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin (Fintype.card (metricBox hG o r).edges))
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((edgeIndex (metricBox hG o r) (d a)).1).1)
    (roots : Finset V)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hfar : ∀ k, n + L ≤ G.dist o (f (Sum.inr k)))
    (hroot : ∀ z, (restrictΔ (metricNestedEquiv hG o hrN) z ∘ d) ∉
      maximalSplitStratum si ti so xo → ∀ u, ∃ a ∈ roots,
      OpenConnected G ((metricBox hG o N).glue
        ((metricBox hG o N).closedExterior,
          (metricBox hG o N).reindex (edgeIndex _) z)) Set.univ a
        (f (Sum.inl u)))
    (hgood :
      let C : Set (((metricBox hG o r).indexedGraph (edgeIndex _)).Configuration) :=
        (fun ρ : ((metricBox hG o r).indexedGraph (edgeIndex _)).Configuration =>
          ρ ∘ d) ⁻¹' maximalSplitStratum si ti so xo
      let t := metricNestedTriple hG o hrN α β hq hp₀ hp₁
      let BS := metricBox hG o N
      let e := metricNestedEquiv hG o hrN
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (hJD.trans (nested_metricBox_edges hG o hrN))) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (hJD.trans (nested_metricBox_edges hG o hrN))) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C))) :
    |((metricBox hG o N).finiteVolumeLaw hq hp₁.le α :
          Measure (Configuration G.edgeSet)).real (cylinder J S) -
        ((metricBox hG o r).finiteVolumeLaw hq hp₁.le β :
          Measure (Configuration G.edgeSet)).real (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (finiteRootArms G roots n) := by
  exact finiteBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad
    hG (metricBox hG o N) (metricBox hG o r) (edgeIndex _) (edgeIndex _)
    (nested_metricBox_edges hG o hrN) α β hq hp₀ hp₁ J S
    (hJD.trans (nested_metricBox_edges hG o hrN)) hJD si ti so xo d f hend
    roots o L n hA hfar hroot
    (finiteRootArms_dependsOnCoordinates_of_metricBox_subset hG
      (metricBox hG o N) roots o L n hA (nested_metricBox_edges hG o hnN)) hgood

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.BadRootAttached.metricBox_cylinder_abs_sub_le_finiteRootArms_of_good_of_bad
