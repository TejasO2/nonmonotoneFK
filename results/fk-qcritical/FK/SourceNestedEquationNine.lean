import FK.ArbitrarySourceNestedWindow
import FK.SourceNestedBounds

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2 Topology

namespace FK.Adaptive.NestedSumGeometry

open FK.Finite FK.Finite.LabelledMultigraph FK.Exploration.FKCoupling
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.SourceUniqueness
open FK.NestedMixture
open FK.Prop42Source

universe uV

/-- Large-box realization of the arbitrary-nesting upper arm. -/
noncomputable def arbitraryArmInterior {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (K : Finset G.edgeSet) (hK : K ⊆ (D.box (G := G) m).edges) :
    Set (E.box (G := G) n).Interior :=
  arbitrarySourceInterior D E m n N ''
    {ρ | upperArm (arbitrarySourceNestedGeometry D E m n N)
      (sourceBase (D.box (G := G) m) (edgeIndex _) K hK)
      (nestedSourceRoots D E m n N) ρ}

lemma arbitrary_armInterior_preimage_subset {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (K : Finset G.edgeSet) (hK : K ⊆ (D.box (G := G) m).edges) :
    (E.box (G := G) n).interiorRestriction ⁻¹' arbitraryArmInterior D E m n N K hK ⊆
      boundaryConnection G (edgeRoots G K) (D.region m) := by
  intro ω hω
  obtain ⟨ρ, hρ, hEq⟩ := hω
  apply arbitrary_upperArm_mem_boundaryConnection D E m n N K hK ρ ω
  · intro e
    exact (congrFun hEq e).symm
  · exact hρ

lemma arbitrary_upperArm_subset_preimage {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (K : Finset G.edgeSet) (hK : K ⊆ (D.box (G := G) m).edges) :
    {ρ | upperArm (arbitrarySourceNestedGeometry D E m n N)
      (sourceBase (D.box (G := G) m) (edgeIndex _) K hK)
      (nestedSourceRoots D E m n N) ρ} ⊆
      arbitrarySourceInterior D E m n N ⁻¹' arbitraryArmInterior D E m n N K hK := by
  intro ρ hρ
  exact ⟨ρ, hρ, rfl⟩

/-- Global finite-volume equation (9) for every abstract `NestedBox`. -/
theorem arbitrarySource_abs_sub_le_boundary {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (α : (E.box (G := G) n).BoundaryPartition) (β : (D.box (G := G) m).BoundaryPartition)
    (hα : HasSourceBoundaryClass (E.data (G := G)) α)
    (hβ : HasSourceBoundaryClass (D.data (G := G)) β)
    (ξO : (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (e₀ : ((D.box (G := G) m).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).Edge)
    (K : Finset G.edgeSet) (S : Set (K → Bool)) (hK : K ⊆ (D.box (G := G) m).edges) :
    |(((E.box (G := G) n).finiteVolumeLaw hq hp₁.le α) :
        Measure (Configuration G.edgeSet)).real (cylinder K S) -
      (((D.box (G := G) m).finiteVolumeLaw hq hp₁.le β) :
        Measure (Configuration G.edgeSet)).real (cylinder K S)| ≤
    (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le :
      Measure (Configuration G.edgeSet)).real
      (boundaryConnection G (edgeRoots G K) (D.region m)) := by
  let BS := E.box (G := G) n
  let BD := D.box (G := G) m
  let jS := edgeIndex BS
  let jD := edgeIndex BD
  let X := arbitrarySourceNestedGeometry D E m n N
  let J := sourceBase BD jD K hK
  let T := sourceObservation BD jD K hK S
  let hr := (upperRateNN_lt_one hq hp₀ hp₁).le
  let U := arbitraryArmInterior D E m n N K hK
  have hfin := arbitraryNested_abs_sub_le_arm D E m n N α β hα hβ ξO
    hq hp₀ hp₁ e₀ J T
  have hmapBig := map_splitToInterior_fkPMF BS BD jS jD N.edge_sub α hq hp₀ hp₁
  have hfirst : (X.graph.fkPMF hq hp₁.le (BS.indexedBoundary jS α)).toMeasure.real
      {ω | baseCylinder J T (fun d : (BD.indexedGraph jD).Edge => ω (Sum.inl d))} =
      (BS.graph.fkPMF hq hp₁.le α).toMeasure.real
        (BS.boxCylinder K S (hK.trans N.edge_sub)) := by
    have h := FiniteBox.pmf_toMeasure_real_preimage_of_map
      (splitToInterior BS BD jS jD N.edge_sub)
      (X.graph.fkPMF hq hp₁.le (BS.indexedBoundary jS α))
      (BS.graph.fkPMF hq hp₁.le α) hmapBig (BS.boxCylinder K S (hK.trans N.edge_sub))
    change (X.graph.fkPMF hq hp₁.le (BS.indexedBoundary jS α)).toMeasure.real
      (splitToInterior BS BD jS jD N.edge_sub ⁻¹'
        BS.boxCylinder K S (hK.trans N.edge_sub)) = _ at h
    have hset := large_split_preimage_boxCylinder BS BD jS jD N.edge_sub K S hK
    exact (congrArg (fun A : Set ((BD.indexedGraph jD).Edge ⊕
      (outsideGraph BS BD).Edge → Bool) =>
        (X.graph.fkPMF hq hp₁.le (BS.indexedBoundary jS α)).toMeasure.real A) hset.symm).trans h
  have hsecond : (((BD.indexedGraph jD).fkPMF hq hp₁.le
      (BD.indexedBoundary jD β)).toMeasure.real (baseCylinder J T)) =
      (BD.graph.fkPMF hq hp₁.le β).toMeasure.real (BD.boxCylinder K S hK) := by
    have h := FiniteBox.pmf_toMeasure_real_preimage_of_map (BD.reindex jD)
      ((BD.indexedGraph jD).fkPMF hq hp₁.le (BD.indexedBoundary jD β))
      (BD.graph.fkPMF hq hp₁.le β) (BD.map_reindex_fkPMF jD β hq hp₀ hp₁)
      (BD.boxCylinder K S hK)
    rw [small_reindex_preimage_boxCylinder BD jD K S hK] at h
    exact h
  have hmapUpper := map_splitToInterior_bernoulliProductPMF BS BD jS jD N.edge_sub hr
  have hlocal := FiniteBox.pmf_toMeasure_real_preimage_of_map
    (splitToInterior BS BD jS jD N.edge_sub) (X.graph.bernoulliProductPMF hr)
    (BS.graph.bernoulliProductPMF hr) hmapUpper U
  have hg := bernoulliProduct_real_interior_preimage BS hr U
  have harm : (X.graph.bernoulliProductPMF hr).toMeasure.real
      (upperArm X J (nestedSourceRoots D E m n N)) ≤
      (globalBernoulli G.edgeSet hr : Measure (Configuration G.edgeSet)).real
        (boundaryConnection G (edgeRoots G K) (D.region m)) := by
    calc
      (X.graph.bernoulliProductPMF hr).toMeasure.real
          (upperArm X J (nestedSourceRoots D E m n N)) ≤
          (X.graph.bernoulliProductPMF hr).toMeasure.real
            (arbitrarySourceInterior D E m n N ⁻¹' U) :=
        measureReal_mono (arbitrary_upperArm_subset_preimage D E m n N K hK)
      _ = (BS.graph.bernoulliProductPMF hr).toMeasure.real U := hlocal
      _ = (globalBernoulli G.edgeSet hr : Measure (Configuration G.edgeSet)).real
          (BS.interiorRestriction ⁻¹' U) := hg.symm
      _ ≤ (globalBernoulli G.edgeSet hr : Measure (Configuration G.edgeSet)).real
          (boundaryConnection G (edgeRoots G K) (D.region m)) :=
        measureReal_mono (arbitrary_armInterior_preimage_subset D E m n N K hK)
  rw [BS.finiteVolumeLaw_real_boxCylinder hq hp₁.le α K S (hK.trans N.edge_sub),
    BD.finiteVolumeLaw_real_boxCylinder hq hp₁.le β K S hK, ← hfirst, ← hsecond]
  exact hfin.trans harm

/-- The literal `SourceUniqueness.NestedEquationNine`, with fixed endpoint roots
and the actual global upper Bernoulli product, for every interior `0 < p < 1`. -/
theorem sourceNestedEquationNine {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    NestedEquationNine (G := G) hq hp₁.le
      (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le) (edgeRoots G) := by
  intro D E α β hα hβ K S m n hK hN
  by_cases hKe : K = ∅
  · subst K
    exact empty_base_abs_sub_le_boundary
      ((E.box (G := G) n).finiteVolumeLaw hq hp₁.le (α n))
      ((D.box (G := G) m).finiteVolumeLaw hq hp₁.le (β m))
      (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le)
      (D.region m) S
  · let N : NestedBox (D.box (G := G) m) (E.box (G := G) n) := Classical.choice hN
    have hK0 : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKe
    let e : (D.box (G := G) m).edges := ⟨hK0.choose, hK hK0.choose_spec⟩
    let e₀ : ((D.box (G := G) m).indexedGraph (edgeIndex _)).Edge ⊕
        (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).Edge :=
      Sum.inl ((edgeIndex (D.box (G := G) m)).symm e)
    exact arbitrarySource_abs_sub_le_boundary D E m n N (α n) (β m) (hα n) (hβ m)
      (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).freeBoundary
      hq hp₀ hp₁ e₀ K S hK

/-- Nonpercolation makes the exact endpoint-root boundary errors vanish along
an arbitrary cofinal vertex exhaustion. -/
theorem source_tendsto_measureReal_boundaryConnection {V : Type uV}
    [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hρ : ∀ᵐ ω ∂(globalBernoulli G.edgeSet
      (upperRateNN_lt_one hq hp₀ hp₁).le : Measure (Configuration G.edgeSet)),
      ω ∈ FK.NonPercolating G)
    (K : Finset G.edgeSet) (D : VertexExhaustion V) :
    Tendsto (fun m => (globalBernoulli G.edgeSet
      (upperRateNN_lt_one hq hp₀ hp₁).le : Measure (Configuration G.edgeSet)).real
      (boundaryConnection G (edgeRoots G K) (D.region m))) atTop (𝓝 0) := by
  exact tendsto_measureReal_boundaryConnection
    (globalBernoulli G.edgeSet (upperRateNN_lt_one hq hp₀ hp₁).le :
      Measure (Configuration G.edgeSet)) (edgeRoots G K) D hρ

end FK.Adaptive.NestedSumGeometry
