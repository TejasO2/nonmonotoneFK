import FK.SourceNestedWindow

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.Adaptive.NestedSumGeometry

open FK.Finite FK.Finite.LabelledMultigraph FK.Exploration.FKCoupling
open FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.SourceUniqueness
open FK.NestedMixture
open FK.Prop42Source
open FK.RandomClosedBoundary

universe uV uE

/-- Index exactly those small-box edges occurring in a global observation base. -/
noncomputable def sourceBaseEmbedding {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (hI : K ⊆ BD.edges) :
    K ↪ (BD.indexedGraph jD).Edge where
  toFun i := jD.symm ⟨i.1, hI i.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun e : BD.edges => (e : E)) (jD.symm.injective hab)

/-- The observation base in the canonical finite edge indexing. -/
noncomputable def sourceBase {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (hI : K ⊆ BD.edges) :
    Finset (BD.indexedGraph jD).Edge :=
  K.attach.map (sourceBaseEmbedding BD jD K hI)

/-- Canonical identification of the indexed observation base with the global one. -/
noncomputable def sourceBaseEquiv {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (hI : K ⊆ BD.edges) :
    sourceBase BD jD K hI ≃ K :=
  (Finset.equivMap (sourceBaseEmbedding BD jD K hI) K.attach).symm.trans
    (Equiv.subtypeUnivEquiv (fun i : K => Finset.mem_attach K i))

@[simp] lemma sourceBaseEquiv_embedding {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (hI : K ⊆ BD.edges)
    (j : sourceBase BD jD K hI) :
    sourceBaseEmbedding BD jD K hI (sourceBaseEquiv BD jD K hI j) = j.1 := by
  let f := sourceBaseEmbedding BD jD K hI
  let b := (Finset.equivMap f K.attach).symm j
  have h := congrArg Subtype.val ((Finset.equivMap f K.attach).apply_symm_apply j)
  change f b.1 = j.1 at h
  exact h

/-- Transport an observation set to the canonical indexed base. -/
def sourceObservation {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (hI : K ⊆ BD.edges)
    (S : Set (K → Bool)) : Set (sourceBase BD jD K hI → Bool) :=
  {f | (fun i : K => f ((sourceBaseEquiv BD jD K hI).symm i)) ∈ S}

lemma sourceBaseEquiv_symm_embedding {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (hI : K ⊆ BD.edges) (i : K) :
    sourceBaseEmbedding BD jD K hI i =
      ((sourceBaseEquiv BD jD K hI).symm i).1 := by
  have h := sourceBaseEquiv_embedding BD jD K hI ((sourceBaseEquiv BD jD K hI).symm i)
  simpa only [Equiv.apply_symm_apply] using h

lemma small_reindex_preimage_boxCylinder {E : Type uE} (BD : FiniteBox E) {nD : ℕ}
    (jD : Fin nD ≃ BD.edges) (K : Finset E) (S : Set (K → Bool))
    (hI : K ⊆ BD.edges) :
    BD.reindex jD ⁻¹' BD.boxCylinder K S hI =
      baseCylinder (sourceBase BD jD K hI) (sourceObservation BD jD K hI S) := by
  ext ω
  change (fun i : K => ω (jD.symm ⟨i.1, hI i.2⟩)) ∈ S ↔
    (fun i : K => ω (((sourceBaseEquiv BD jD K hI).symm i).1)) ∈ S
  have hfun : (fun i : K => ω (jD.symm ⟨i.1, hI i.2⟩)) =
      (fun i : K => ω (((sourceBaseEquiv BD jD K hI).symm i).1)) := by
    funext i
    exact congrArg ω (sourceBaseEquiv_symm_embedding BD jD K hI i)
  rw [hfun]

/-- Transport a nested configuration to the original large indexed box. -/
noncomputable def splitToIndexed {E : Type uE} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (ω : (BD.indexedGraph jD).Edge ⊕ (outsideGraph BS BD).Edge → Bool) :
    (BS.indexedGraph jS).Configuration :=
  (BS.indexedGraph jS).transportConfig (Equiv.refl _)
    (nestedSplitEdgeEquiv BS BD jS jD hBD) ω

/-- Read a nested configuration in the original large finite-box coordinates. -/
noncomputable def splitToInterior {E : Type uE} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (ω : (BD.indexedGraph jD).Edge ⊕ (outsideGraph BS BD).Edge → Bool) : BS.Interior :=
  BS.reindex jS (splitToIndexed BS BD jS jD hBD ω)

@[simp] lemma splitToInterior_apply_split {E : Type uE}
    (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (ω : (BD.indexedGraph jD).Edge ⊕ (outsideGraph BS BD).Edge → Bool)
    (a : (BD.indexedGraph jD).Edge ⊕ (outsideGraph BS BD).Edge) :
    splitToInterior BS BD jS jD hBD ω (jS (nestedSplitEdgeEquiv BS BD jS jD hBD a)) = ω a := by
  let e := nestedSplitEdgeEquiv BS BD jS jD hBD
  change ω (e.symm (jS.symm (jS (e a)))) = ω a
  exact (congrArg (fun x => ω (e.symm x)) (Equiv.symm_apply_apply jS (e a))).trans
    (congrArg ω (Equiv.symm_apply_apply e a))

lemma splitToIndexed_restrict {E : Type uE} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (ω : (BD.indexedGraph jD).Edge ⊕ (outsideGraph BS BD).Edge → Bool) :
    restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) (splitToIndexed BS BD jS jD hBD ω) =
      (fun d : (BD.indexedGraph jD).Edge => ω (Sum.inl d)) := by
  funext d
  exact congrArg ω ((nestedEdgeEquiv BS BD jS jD hBD).symm_apply_apply (Sum.inl d))

lemma large_split_preimage_boxCylinder {E : Type uE} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (K : Finset E) (S : Set (K → Bool)) (hJD : K ⊆ BD.edges) :
    splitToInterior BS BD jS jD hBD ⁻¹'
        BS.boxCylinder K S (hJD.trans hBD) =
      {ω | baseCylinder (sourceBase BD jD K hJD) (sourceObservation BD jD K hJD S)
        (fun d : (BD.indexedGraph jD).Edge => ω (Sum.inl d))} := by
  let e := nestedEdgeEquiv BS BD jS jD hBD
  have he : ∀ i : K,
      e (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) =
        jS.symm ⟨i.1, (hJD.trans hBD) i.2⟩ := by
    intro i
    exact nestedEdgeEquiv_inl BS BD jS jD hBD K (hJD.trans hBD) hJD i
  have hlarge := reindex_preimage_boxCylinder_of_edge_compat BS BD jS jD
    (outsideGraph BS BD) e K S (hJD.trans hBD) hJD he
  have hsmall := small_reindex_preimage_boxCylinder BD jD K S hJD
  ext ω
  change splitToIndexed BS BD jS jD hBD ω ∈
      BS.reindex jS ⁻¹' BS.boxCylinder K S (hJD.trans hBD) ↔ _
  rw [hlarge]
  change restrictΔ e (splitToIndexed BS BD jS jD hBD ω) ∈
      BD.reindex jD ⁻¹' BD.boxCylinder K S hJD ↔ _
  rw [hsmall, splitToIndexed_restrict]
  rfl

/-- Original large-box FK marginal of the canonical nested law. -/
theorem map_splitToInterior_fkPMF {E : Type uE} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (α : BS.BoundaryPartition) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (splitToInterior BS BD jS jD hBD)
        ((nestedBig (G := BS.indexedGraph jS) (eV := Equiv.refl _)
      (nestedSplitEdgeEquiv BS BD jS jD hBD)).fkPMF hq hp₁.le (BS.indexedBoundary jS α)) =
      BS.graph.fkPMF hq hp₁.le α := by
  let e := nestedSplitEdgeEquiv BS BD jS jD hBD
  have htr : PMF.map (splitToIndexed BS BD jS jD hBD)
      ((nestedBig (G := BS.indexedGraph jS) (eV := Equiv.refl _)
      (nestedSplitEdgeEquiv BS BD jS jD hBD)).fkPMF hq hp₁.le (BS.indexedBoundary jS α)) =
      (BS.indexedGraph jS).fkPMF hq hp₁.le (BS.indexedBoundary jS α) := by
    exact (BS.indexedGraph jS).map_transport_fkPMF (Equiv.refl _) e
      (BS.indexedBoundary jS α) hq hp₀ hp₁
  have hre := BS.map_reindex_fkPMF jS α hq hp₀ hp₁
  calc
    PMF.map (splitToInterior BS BD jS jD hBD) _ =
        PMF.map (BS.reindex jS) (PMF.map (splitToIndexed BS BD jS jD hBD) _) := by
      exact (PMF.map_comp (splitToIndexed BS BD jS jD hBD) _ (BS.reindex jS)).symm
    _ = PMF.map (BS.reindex jS)
        ((BS.indexedGraph jS).fkPMF hq hp₁.le (BS.indexedBoundary jS α)) := by rw [htr]
    _ = _ := hre

/-- Original large-box Bernoulli marginal of the canonical nested upper law. -/
theorem map_splitToInterior_bernoulliProductPMF {E : Type uE}
    (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    {r : NNReal} (hr : r ≤ 1) :
    PMF.map (splitToInterior BS BD jS jD hBD)
        ((nestedBig (G := BS.indexedGraph jS) (eV := Equiv.refl _)
      (nestedSplitEdgeEquiv BS BD jS jD hBD)).bernoulliProductPMF hr) =
      BS.graph.bernoulliProductPMF hr := by
  have htr : PMF.map (splitToIndexed BS BD jS jD hBD)
      ((nestedBig (G := BS.indexedGraph jS) (eV := Equiv.refl _)
      (nestedSplitEdgeEquiv BS BD jS jD hBD)).bernoulliProductPMF hr) =
      (BS.indexedGraph jS).bernoulliProductPMF hr := by
    exact map_nested_bernoulli (G := BS.indexedGraph jS) (eV := Equiv.refl _)
      (nestedSplitEdgeEquiv BS BD jS jD hBD) hr
  have hre := BS.map_reindex_bernoulliProductPMF jS hr
  calc
    PMF.map (splitToInterior BS BD jS jD hBD) _ =
        PMF.map (BS.reindex jS) (PMF.map (splitToIndexed BS BD jS jD hBD) _) := by
      exact (PMF.map_comp (splitToIndexed BS BD jS jD hBD) _ (BS.reindex jS)).symm
    _ = PMF.map (BS.reindex jS) ((BS.indexedGraph jS).bernoulliProductPMF hr) := by rw [htr]
    _ = _ := hre

/-- Constant-rate global upper Bernoulli law. -/
noncomputable def globalBernoulli (E : Type uE) {r : NNReal} (hr : r ≤ 1) :
    ProbabilityMeasure (Configuration E) :=
  FKLimit.bernoulliProduct (fun _ : E => unitOfNN r hr)

@[simp] lemma globalBernoulli_coe (E : Type uE) {r : NNReal} (hr : r ≤ 1) :
    (globalBernoulli E hr : Measure (Configuration E)) =
      FKLimit.bernoulliProduct (fun _ : E => unitOfNN r hr) := rfl

/-- The finite set of global endpoints of an observation base. -/
noncomputable def edgeRoots {V : Type uV} (G : SimpleGraph V) (K : Finset G.edgeSet) : Finset V :=
  K.biUnion fun e => e.1.toFinset

lemma mem_region_of_mem_edgeRoots {V : Type uV} {G : SimpleGraph V} [G.LocallyFinite]
    (D : VertexExhaustion V) (m : ℕ) (K : Finset G.edgeSet)
    (hK : K ⊆ (D.box (G := G) m).edges) {x : V}
    (hx : x ∈ edgeRoots G K) : x ∈ D.region m := by
  obtain ⟨e, heK, hxe⟩ := Finset.mem_biUnion.mp hx
  exact (D.mem_box_edges_iff m e).mp (hK heK) x (Sym2.mem_toFinset.mp hxe)

/-- The canonical split of two induced source boxes. -/
noncomputable def canonicalSourceSplit {V : Type uV} {G : SimpleGraph V} [G.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ) (hn : D.region m ⊆ E.region n) :=
  nestedSplitEdgeEquiv (E.box (G := G) n) (D.box (G := G) m)
    (edgeIndex _) (edgeIndex _) (E.nest D m n hn).edge_sub

/-- The canonical nested configuration read in large-box coordinates. -/
noncomputable def canonicalSourceInterior {V : Type uV} {G : SimpleGraph V} [G.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ) (hn : D.region m ⊆ E.region n)
    (ω : ((D.box (G := G) m).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (E.box (G := G) n) (D.box (G := G) m)).Edge → Bool) :
    (E.box (G := G) n).Interior :=
  splitToInterior (E.box (G := G) n) (D.box (G := G) m)
    (edgeIndex _) (edgeIndex _) (E.nest D m n hn).edge_sub ω

/-- Actual global open-path realization of the canonical nested graph. -/
noncomputable def canonicalSourceOpenPathMap {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n)
    (ρ : (sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl)).graph.Configuration)
    (ω : G.edgeSet → Bool)
    (hagree : ∀ e : (E.box (G := G) n).edges,
      ω e.1 = canonicalSourceInterior D E m n hn ρ e) :
    OpenPathGeometry.LabelledOpenPathMap
      (sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl)).graph G ρ ω where
  vertex v := (E.data (G := G)).vertex n v
  edge a := (((edgeIndex (E.box (G := G) n)) (canonicalSourceSplit D E m n hn a) :
    (E.box (G := G) n).edges) : G.edgeSet)
  endpoint a := by
    exact (E.data (G := G)).endpoint n
      ((edgeIndex (E.box (G := G) n)) (canonicalSourceSplit D E m n hn a))
  isOpen a ha := by
    rw [hagree ((edgeIndex (E.box (G := G) n)) (canonicalSourceSplit D E m n hn a))]
    exact (splitToInterior_apply_split (E.box (G := G) n) (D.box (G := G) m)
      (edgeIndex _) (edgeIndex _) (E.nest D m n hn).edge_sub ρ a).trans ha

lemma canonical_source_mem_edgeRoots {V : Type uV} {G : SimpleGraph V} [G.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ) (hn : D.region m ⊆ E.region n)
    (K : Finset G.edgeSet) (hK : K ⊆ (D.box (G := G) m).edges)
    (j : sourceBase (D.box (G := G) m) (edgeIndex _) K hK) :
    (E.data (G := G)).vertex n
      ((sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl)).vertex
        (((D.box (G := G) m).indexedGraph (edgeIndex _)).source j.1)) ∈ edgeRoots G K := by
  let jD := edgeIndex (D.box (G := G) m)
  have hlabel : ((sourceBaseEquiv (D.box (G := G) m) jD K hK j : K) : G.edgeSet) =
      ((jD j.1 : (D.box (G := G) m).edges) : G.edgeSet) := by
    have h := congrArg (fun a : (D.box (G := G) m).indexedGraph jD |>.Edge =>
      ((jD a : (D.box (G := G) m).edges) : G.edgeSet))
      (sourceBaseEquiv_embedding (D.box (G := G) m) jD K hK j)
    change ((jD (jD.symm (⟨(sourceBaseEquiv (D.box (G := G) m) jD K hK j).1,
      hK (sourceBaseEquiv (D.box (G := G) m) jD K hK j).2⟩ :
      (D.box (G := G) m).edges)) : (D.box (G := G) m).edges) : G.edgeSet) = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  change ((D.box (G := G) m).source ((edgeIndex (D.box (G := G) m)) j.1)).1 ∈ edgeRoots G K
  refine Finset.mem_biUnion.mpr ⟨((jD j.1 : (D.box (G := G) m).edges) : G.edgeSet), ?_, ?_⟩
  · rw [← hlabel]
    exact (sourceBaseEquiv (D.box (G := G) m) jD K hK j).2
  · change (D.data (G := G)).vertex m ((D.box (G := G) m).source ((edgeIndex (D.box (G := G) m)) j.1)) ∈ _
    rw [Sym2.mem_toFinset, ← (D.data (G := G)).endpoint m ((edgeIndex (D.box (G := G) m)) j.1)]
    exact Sym2.mem_mk_left _ _

lemma canonical_target_mem_edgeRoots {V : Type uV} {G : SimpleGraph V} [G.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ) (hn : D.region m ⊆ E.region n)
    (K : Finset G.edgeSet) (hK : K ⊆ (D.box (G := G) m).edges)
    (j : sourceBase (D.box (G := G) m) (edgeIndex _) K hK) :
    (E.data (G := G)).vertex n
      ((sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl)).vertex
        (((D.box (G := G) m).indexedGraph (edgeIndex _)).target j.1)) ∈ edgeRoots G K := by
  let jD := edgeIndex (D.box (G := G) m)
  have hlabel : ((sourceBaseEquiv (D.box (G := G) m) jD K hK j : K) : G.edgeSet) =
      ((jD j.1 : (D.box (G := G) m).edges) : G.edgeSet) := by
    have h := congrArg (fun a : (D.box (G := G) m).indexedGraph jD |>.Edge =>
      ((jD a : (D.box (G := G) m).edges) : G.edgeSet))
      (sourceBaseEquiv_embedding (D.box (G := G) m) jD K hK j)
    change ((jD (jD.symm (⟨(sourceBaseEquiv (D.box (G := G) m) jD K hK j).1,
      hK (sourceBaseEquiv (D.box (G := G) m) jD K hK j).2⟩ :
      (D.box (G := G) m).edges)) : (D.box (G := G) m).edges) : G.edgeSet) = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  change ((D.box (G := G) m).target ((edgeIndex (D.box (G := G) m)) j.1)).1 ∈ edgeRoots G K
  refine Finset.mem_biUnion.mpr ⟨((jD j.1 : (D.box (G := G) m).edges) : G.edgeSet), ?_, ?_⟩
  · rw [← hlabel]
    exact (sourceBaseEquiv (D.box (G := G) m) jD K hK j).2
  · change (D.data (G := G)).vertex m ((D.box (G := G) m).target ((edgeIndex (D.box (G := G) m)) j.1)) ∈ _
    rw [Sym2.mem_toFinset, ← (D.data (G := G)).endpoint m ((edgeIndex (D.box (G := G) m)) j.1)]
    exact Sym2.mem_mk_right _ _

lemma canonical_nonCore_isRegionBoundary {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n) (c : (D.box (G := G) m).Vertex)
    (hc : c ∈ (sourceCore (Gph := G) D m)ᶜ) :
    IsRegionBoundary G (D.region m)
      ((E.data (G := G)).vertex n ((E.nest D m n hn).vert c)) := by
  have hc' : ¬ (D.data (G := G)).StarContained m c := hc
  unfold InfiniteVolume.ConventionTransport.SimpleGraphBoxData.StarContained at hc'
  push Not at hc'
  obtain ⟨f, hcf, hfn⟩ := hc'
  have hex : ∃ x, x ∈ (f.1 : Sym2 V) ∧ x ∉ D.region m := by
    by_contra hn'
    push Not at hn'
    apply hfn
    apply (D.mem_box_edges_iff m f).mpr
    intro x hx
    exact hn' x hx
  obtain ⟨x, hxf, hx⟩ := hex
  obtain ⟨a, b, hab, hfab⟩ := exists_adj_of_mem_edgeSet (G := G) (e := f)
  have hca : c.1 = a ∨ c.1 = b := by
    rw [← hfab] at hcf
    exact Sym2.mem_iff.mp hcf
  have hxa : x = a ∨ x = b := by
    rw [← hfab] at hxf
    exact Sym2.mem_iff.mp hxf
  change IsRegionBoundary G (D.region m) c.1
  refine ⟨c.2, x, hx, ?_⟩
  rcases hca with rfl | rfl <;> rcases hxa with rfl | rfl
  · exact (hx c.2).elim
  · exact hab
  · exact hab.symm
  · exact (hx c.2).elim

/-- Canonical upper arms are genuine global connections from the fixed
observation roots to the small region's vertex boundary. -/
theorem canonical_upperArm_mem_boundaryConnection {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n) (K : Finset G.edgeSet)
    (hK : K ⊆ (D.box (G := G) m).edges)
    (ρ : (sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl)).graph.Configuration)
    (ω : G.edgeSet → Bool)
    (hagree : ∀ e : (E.box (G := G) n).edges,
      ω e.1 = canonicalSourceInterior D E m n hn ρ e)
    (hρ : upperArm (sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl))
      (sourceBase (D.box (G := G) m) (edgeIndex _) K hK)
      (sourceRoots D E m n (E.nest D m n hn)) ρ) :
    ω ∈ boundaryConnection G (edgeRoots G K) (D.region m) := by
  let N := E.nest (G := G) D m n hn
  let X := sourceNestedGeometry D E m n N (fun _ => rfl)
  let M := canonicalSourceOpenPathMap D E m n hn ρ ω hagree
  obtain ⟨j, b, hb, hpath⟩ := hρ
  have finish (x : (D.box (G := G) m).Vertex)
      (hx : M.vertex (X.vertex x) ∈ edgeRoots G K)
      (hxb : (X.graph.openGraph X.graph.freeBoundary ρ).Reachable (X.vertex x) b) :
      ω ∈ boundaryConnection G (edgeRoots G K) (D.region m) := by
    have hconn : CurvatureVariance.Infra.Percolation.OpenConnected G ω Set.univ
        (M.vertex (X.vertex x)) (M.vertex b) := M.openConnected_of_reachable hxb
    change b ∈ {v | v ∉ Set.range N.vert} ∪ N.vert '' (sourceCore D m)ᶜ at hb
    rcases hb with hb | ⟨c, hc, rfl⟩
    · have hnmem : M.vertex b ∉ D.region m := by
        intro hbD
        apply hb
        let c : (D.box (G := G) m).Vertex := ⟨M.vertex b, hbD⟩
        refine ⟨c, ?_⟩
        apply Subtype.ext
        rfl
      obtain ⟨p, hp⟩ := hconn
      rcases inside_or_boundary_of_isOpenIn
          (mem_region_of_mem_edgeRoots D m K hK hx) p hp with h | h
      · exact (hnmem h.1).elim
      · obtain ⟨w, hw, hxw⟩ := h
        exact ⟨M.vertex (X.vertex x), hx, w, hw, hxw⟩
    · exact ⟨M.vertex (X.vertex x), hx, M.vertex (N.vert c),
        canonical_nonCore_isRegionBoundary D E m n hn c hc, hconn⟩
  rcases hpath with h | h
  · exact finish (((D.box (G := G) m).indexedGraph (edgeIndex _)).source j.1)
      (canonical_source_mem_edgeRoots D E m n hn K hK j) h
  · exact finish (((D.box (G := G) m).indexedGraph (edgeIndex _)).target j.1)
      (canonical_target_mem_edgeRoots D E m n hn K hK j) h

/-- The finite large-box realization of the canonical upper arm. -/
noncomputable def canonicalArmInterior {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n) (K : Finset G.edgeSet)
    (hK : K ⊆ (D.box (G := G) m).edges) : Set (E.box (G := G) n).Interior :=
  canonicalSourceInterior D E m n hn ''
    {ρ | upperArm (sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl))
      (sourceBase (D.box (G := G) m) (edgeIndex _) K hK)
      (sourceRoots D E m n (E.nest D m n hn)) ρ}

lemma canonical_armInterior_preimage_subset {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n) (K : Finset G.edgeSet)
    (hK : K ⊆ (D.box (G := G) m).edges) :
    (E.box (G := G) n).interiorRestriction ⁻¹' canonicalArmInterior D E m n hn K hK ⊆
      boundaryConnection G (edgeRoots G K) (D.region m) := by
  intro ω hω
  obtain ⟨ρ, hρ, hEq⟩ := hω
  apply canonical_upperArm_mem_boundaryConnection D E m n hn K hK ρ ω
  · intro e
    exact (congrFun hEq e).symm
  · exact hρ

lemma canonical_upperArm_subset_preimage {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n) (K : Finset G.edgeSet)
    (hK : K ⊆ (D.box (G := G) m).edges) :
    {ρ | upperArm (sourceNestedGeometry D E m n (E.nest D m n hn) (fun _ => rfl))
      (sourceBase (D.box (G := G) m) (edgeIndex _) K hK)
      (sourceRoots D E m n (E.nest D m n hn)) ρ} ⊆
      canonicalSourceInterior D E m n hn ⁻¹' canonicalArmInterior D E m n hn K hK := by
  intro ρ hρ
  exact ⟨ρ, hρ, rfl⟩

/-- Canonical induced nesting: actual global finite-volume cylinder estimate,
with the literal source boundary-connection error and fixed observation roots. -/
theorem canonicalSource_abs_sub_le_boundary {V : Type uV} {G : SimpleGraph V}
    [G.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n)
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
  let N := E.nest (G := G) D m n hn
  let X := sourceNestedGeometry D E m n N (fun _ => rfl)
  let J := sourceBase BD jD K hK
  let T := sourceObservation BD jD K hK S
  let hr := (upperRateNN_lt_one hq hp₀ hp₁).le
  let U := canonicalArmInterior D E m n hn K hK
  have hfin := sourceNested_abs_sub_le_arm_of_nest D E m n hn α β hα hβ ξO
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
      (upperArm X J (sourceRoots D E m n N)) ≤
      (globalBernoulli G.edgeSet hr : Measure (Configuration G.edgeSet)).real
        (boundaryConnection G (edgeRoots G K) (D.region m)) := by
    calc
      (X.graph.bernoulliProductPMF hr).toMeasure.real
          (upperArm X J (sourceRoots D E m n N)) ≤
          (X.graph.bernoulliProductPMF hr).toMeasure.real
            (canonicalSourceInterior D E m n hn ⁻¹' U) :=
        measureReal_mono (canonical_upperArm_subset_preimage D E m n hn K hK)
      _ = (BS.graph.bernoulliProductPMF hr).toMeasure.real U := hlocal
      _ = (globalBernoulli G.edgeSet hr : Measure (Configuration G.edgeSet)).real
          (BS.interiorRestriction ⁻¹' U) := hg.symm
      _ ≤ (globalBernoulli G.edgeSet hr : Measure (Configuration G.edgeSet)).real
          (boundaryConnection G (edgeRoots G K) (D.region m)) :=
        measureReal_mono (canonical_armInterior_preimage_subset D E m n hn K hK)
  rw [BS.finiteVolumeLaw_real_boxCylinder hq hp₁.le α K S (hK.trans N.edge_sub),
    BD.finiteVolumeLaw_real_boxCylinder hq hp₁.le β K S hK, ← hfirst, ← hsecond]
  exact hfin.trans harm

end FK.Adaptive.NestedSumGeometry
