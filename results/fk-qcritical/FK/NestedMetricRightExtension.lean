import FK.NestedCommonUpperGood
import FK.NestedMetricRegionSplit

/-!
# Right-disjoint two-sided presentations of metric finite boxes

This module makes the graph presentation needed by the proved common-upper
`hgood` theorem explicit.  A small indexed box and a fresh right graph are
assigned disjoint global labels.  The large box is enumerated by the same
`rightExtendedIndex` as `hgood`; no equality with the canonical
`outsideGraph` on shared box vertices is asserted.

The finite observation cylinders are arbitrary cylinders on the left/internal
`Fin m` coordinates.  An explicit equivalence with the global observation
base and a pointwise label identity transport them exactly.

The geometric arm inclusion is proved for the actual right-extended edge
split, not by silently replacing it with `nestedEdgeEquiv`.

Scope: the added graph and its global labels are supplied independently; no
endpoint model for those added labels in the ambient infinite graph is
asserted.  In particular, the large box is not identified with a standard
larger metric box, and no arbitrary-boundary DLR uniqueness claim is made.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.InfiniteVolume.NestedMetricGeometry.RightExtension

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.Exploration.NestedCoupledGood
open FK.Exploration.Sequential
open FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Finite.MarkovFactorization
open FK.InfiniteVolume.NestedFiniteAssembly

universe u v w x

variable {E : Type u} {U : Type v} {K : Type w}
variable [Fintype U] [Fintype K] {m k : ℕ}
variable (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
variable (GO : LabelledMultigraph)

/-- The small box, with the exterior-first transported split as its graph. -/
noncomputable abbrev smallBox (D : Finset E) (jD : Fin (k + m) ≃ D) : FiniteBox E where
  Vertex := (transportedAmbient si ti so xo).Vertex
  edges := D
  source e := (transportedAmbient si ti so xo).source (jD.symm e)
  target e := (transportedAmbient si ti so xo).target (jD.symm e)

/-- The right-extended large graph used by the accepted two-sided `hgood`. -/
noncomputable abbrev largeGraph : LabelledMultigraph :=
  rightExtendedGraph (transportedAmbient si ti so xo).source
    (transportedAmbient si ti so xo).target GO
/-- Enumerate the disjoint union by exterior-first small edges followed by the
fresh right graph.  This is deliberately `rightExtendedIndex`, not the
canonical nested-box difference equivalence. -/
noncomputable def largeIndex {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) :
    Fin (k + m + Fintype.card GO.Edge) ≃ (D ∪ O : Finset E) :=
  (rightExtendedIndex GO).trans <|
    (Equiv.sumCongr jD jO).trans <| (Equiv.Set.union hDO).symm.trans
      (Set.equivOfEq (Finset.coe_union D O).symm)

/-- The large box, with exactly the accepted right-extended graph. -/
noncomputable abbrev largeBox {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) : FiniteBox E where
  Vertex := (largeGraph si ti so xo GO).Vertex
  edges := D ∪ O
  source e := (largeGraph si ti so xo GO).source ((largeIndex GO hDO jD jO).symm e)
  target e := (largeGraph si ti so xo GO).target ((largeIndex GO hDO jD jO).symm e)

/-- The nested edge equivalence is literally the one in the accepted `hgood`
statement. -/
noncomputable abbrev edgeEquiv :
    Fin (k + m) ⊕ GO.Edge ≃ Fin (k + m + Fintype.card GO.Edge) :=
  (rightExtendedIndex GO).symm

lemma smallBox_source {D : Finset E} (jD : Fin (k + m) ≃ D) (i : Fin (k + m)) :
    (smallBox si ti so xo D jD).source (jD i) =
      (transportedAmbient si ti so xo).source i := by
  simp [smallBox]

lemma smallBox_target {D : Finset E} (jD : Fin (k + m) ≃ D) (i : Fin (k + m)) :
    (smallBox si ti so xo D jD).target (jD i) =
      (transportedAmbient si ti so xo).target i := by
  simp [smallBox]

lemma largeBox_source {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (i : Fin (k + m + Fintype.card GO.Edge)) :
    (largeBox si ti so xo GO hDO jD jO).source (largeIndex GO hDO jD jO i) =
      (largeGraph si ti so xo GO).source i := by
  simp [largeBox]

lemma largeBox_target {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (i : Fin (k + m + Fintype.card GO.Edge)) :
    (largeBox si ti so xo GO hDO jD jO).target (largeIndex GO hDO jD jO i) =
      (largeGraph si ti so xo GO).target i := by
  simp [largeBox]

lemma largeIndex_apply {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) (a : Fin (k + m) ⊕ GO.Edge) :
    largeIndex GO hDO jD jO ((rightExtendedIndex GO).symm a) =
      (Set.equivOfEq (Finset.coe_union D O).symm)
        ((Equiv.Set.union hDO).symm ((Equiv.sumCongr jD jO) a)) := by
  simp [largeIndex]

lemma largeIndex_inl {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) (a : Fin (k + m)) :
    ((largeIndex GO hDO jD jO ((edgeEquiv GO) (Sum.inl a)) : (D ∪ O : Finset E)) : E) =
      (jD a : E) := by
  rw [largeIndex_apply]
  rfl

/-- Global label of one left/internal coordinate. -/
noncomputable def internalLabel {D : Finset E} (jD : Fin (k + m) ≃ D) (i : Fin m) : E :=
  (jD (exteriorFirst.symm (Sum.inl i)) : E)

/-- The small-coordinate readout on the large box agrees with the first factor
of `splitRightExtendedConfig`. -/
lemma largeBox_reindex_small {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (z : (largeGraph si ti so xo GO).Configuration) (a : Fin (k + m))
    (ha : (jD a : E) ∈ (largeBox si ti so xo GO hDO jD jO).edges) :
    (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z
        ⟨jD a, ha⟩ =
      (splitRightExtendedConfig (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target GO z).1 a := by
  change z ((largeIndex GO hDO jD jO).symm ⟨jD a, ha⟩) =
    z ((rightExtendedIndex GO).symm (Sum.inl a))
  congr 2
  apply (largeIndex GO hDO jD jO).injective
  apply Subtype.ext
  simpa only [Equiv.apply_symm_apply] using (largeIndex_inl GO hDO jD jO a).symm

/-- The demonstrated small FK source law: arbitrary shared left wiring and an
independent right setoid. -/
@[instance_reducible]
noncomputable def smallSourceLaw {D : Finset E} (jD : Fin (k + m) ≃ D)
    (θ : Setoid U) (ζ : Setoid K) : (smallBox si ti so xo D jD).BoundaryPartition :=
  (ambientOfSum (splitSource si so) (splitTarget ti xo)).transportBoundaryOf
    (Equiv.refl (U ⊕ K)) (eE := exteriorFirst) (twoSidedBoundary si ti so xo θ ζ)

/-- The demonstrated large FK source law: the second right setoid, with an
arbitrary boundary setoid on the fresh right graph. -/
@[instance_reducible]
noncomputable def largeSourceLaw {D O : Finset E}
    (hDO : Disjoint (D : Set E) (O : Set E)) (jD : Fin (k + m) ≃ D)
    (jO : GO.Edge ≃ O) (θ : Setoid U) (ζ : Setoid K) (χ : GO.BoundaryPartition) :
    (largeBox si ti so xo GO hDO jD jO).BoundaryPartition :=
  (disjointSum
    (finIndexedGraph (U ⊕ K) (k + m) (transportedAmbient si ti so xo).source
      (transportedAmbient si ti so xo).target) GO).transportBoundaryOf
      (Equiv.refl _) (eE := rightExtendedIndex GO)
      (sumBoundary (smallSourceLaw si ti so xo jD θ ζ) χ)

lemma smallBox_indexedBoundary {D : Finset E} (jD : Fin (k + m) ≃ D)
    (θ : Setoid U) (ζ : Setoid K) :
    (smallBox si ti so xo D jD).indexedBoundary jD (smallSourceLaw si ti so xo jD θ ζ) =
      smallSourceLaw si ti so xo jD θ ζ := by
  rfl

lemma largeBox_indexedBoundary {D O : Finset E}
    (hDO : Disjoint (D : Set E) (O : Set E)) (jD : Fin (k + m) ≃ D)
    (jO : GO.Edge ≃ O) (θ : Setoid U) (ζ : Setoid K) (χ : GO.BoundaryPartition) :
    (largeBox si ti so xo GO hDO jD jO).indexedBoundary
      (largeIndex GO hDO jD jO) (largeSourceLaw si ti so xo GO hDO jD jO θ ζ χ) =
      largeSourceLaw si ti so xo GO hDO jD jO θ ζ χ := by
  rfl

/-- Transport an arbitrary global cylinder to the `Fin m` interior coordinates
by the specified observation equivalence. -/
def observationSet {J : Finset E} (jI : Fin m ≃ J) (S : Set (J → Bool)) :
    Set (Fin m → Bool) :=
  {a | (fun x : J => a (jI.symm x)) ∈ S}

/-- The actual maximal-stratum event on the small box. -/
def smallStratum {D : Finset E} (jD : Fin (k + m) ≃ D) :
    Set ((smallBox si ti so xo D jD).indexedGraph jD).Configuration :=
  {ω | toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}

/-- The large box's global observation cylinder is exactly the interior event
used by the two-sided common-upper theorem. -/
lemma large_preimage_boxCylinder {D O : Finset E} {J : Finset E}
    (hDO : Disjoint (D : Set E) (O : Set E)) (jD : Fin (k + m) ≃ D)
    (jO : GO.Edge ≃ O) (jI : Fin m ≃ J)
    (hlabel : ∀ i, ((jI i : J) : E) = internalLabel jD i)
    (S : Set (J → Bool)) (hJS : J ⊆ (largeBox si ti so xo GO hDO jD jO).edges) :
    (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) ⁻¹'
      (largeBox si ti so xo GO hDO jD jO).boxCylinder J S hJS =
    {ω | interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target GO ω).1)) ∈
        observationSet jI S} := by
  ext z
  change (fun x : J =>
      (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z
        ⟨x.1, hJS x.2⟩) ∈ S ↔
    (fun x : J => interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target GO z).1)) (jI.symm x)) ∈ S
  have hfun : (fun x : J =>
      (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z
        ⟨x.1, hJS x.2⟩) =
    (fun x : J => interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target GO z).1)) (jI.symm x)) := by
    funext x
    let i := jI.symm x
    have hxi : jI i = x := jI.apply_symm_apply x
    rw [← hxi]
    have hlabel' : ((jI i : J) : E) =
        (jD (exteriorFirst.symm (Sum.inl i)) : E) := by
      simpa only [internalLabel] using hlabel i
    have hread := largeBox_reindex_small si ti so xo GO hDO jD jO z
      (exteriorFirst.symm (Sum.inl i))
      (show (jD (exteriorFirst.symm (Sum.inl i)) : E) ∈ D ∪ O by
        rw [← hlabel']
        exact hJS (jI i).2)
    simp only [Equiv.symm_apply_apply]
    change (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z
        ⟨((jI i : J) : E), hJS (jI i).2⟩ =
      (splitRightExtendedConfig (transportedAmbient si ti so xo).source
        (transportedAmbient si ti so xo).target GO z).1
        (exteriorFirst.symm (Sum.inl i))
    have hsub : (⟨((jI i : J) : E), hJS (jI i).2⟩ :
        (largeBox si ti so xo GO hDO jD jO).edges) =
        ⟨jD (exteriorFirst.symm (Sum.inl i)),
          show (jD (exteriorFirst.symm (Sum.inl i)) : E) ∈ D ∪ O by
            rw [← hlabel']
            exact hJS (jI i).2⟩ := Subtype.ext hlabel'
    rw [hsub]
    exact hread
  rw [hfun]

/-- The small edge of the right-extended enumeration has exactly its
corresponding global small-box label. -/
lemma edgeCompat {D O : Finset E} (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) (a : Fin (k + m))
    (ha : (jD a : E) ∈ (largeBox si ti so xo GO hDO jD jO).edges) :
    (edgeEquiv GO) (Sum.inl a) =
      (largeIndex GO hDO jD jO).symm ⟨jD a, ha⟩ := by
  apply (largeIndex GO hDO jD jO).injective
  apply Subtype.ext
  simpa only [Equiv.apply_symm_apply] using (largeIndex_inl GO hDO jD jO a)

/-- **The actual common-upper `hgood` identity on the constructed finite
boxes.**  The small source law uses `θ, ζS`; the large one uses `θ, ζL, χ`.
The observation is an arbitrary global cylinder supported on the internal
`Fin m` coordinates by `jI` and `hlabel`. -/
theorem good_rightExtended_twoSided {D O J : Finset E}
    (hDO : Disjoint (D : Set E) (O : Set E)) (jD : Fin (k + m) ≃ D)
    (jO : GO.Edge ≃ O) (jI : Fin m ≃ J)
    (hlabel : ∀ i, ((jI i : J) : E) = internalLabel jD i)
    (hJS : J ⊆ (largeBox si ti so xo GO hDO jD jO).edges) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo) (S : Set (J → Bool)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξR : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζL)
    let L := rightExtendedGraph T.source T.target GO
    let DG := disjointSum (finIndexedGraph (U ⊕ K) (k + m) T.source T.target) GO
    let ξL : L.BoundaryPartition := DG.transportBoundaryOf (Equiv.refl _)
      (eE := rightExtendedIndex GO) (sumBoundary ξR χ)
    let B : Set L.Configuration :=
      (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) ⁻¹'
        (largeBox si ti so xo GO hDO jD jO).boxCylinder J S hJS
    let C : Set T.Configuration := smallStratum si ti so xo jD
    let t := fkNestedOrderedTriple L.source L.target T.source T.target GO
      (rightExtendedIndex GO).symm ξL ξS hq hp₀ hp₁
    t.dist.toMeasure
      ((fun z => z.1) ⁻¹' B ∩
        (fun z => z.2.2) ⁻¹' (restrictΔ (rightExtendedIndex GO).symm ⁻¹' C)) =
    t.dist.toMeasure
      ((fun z => z.2.1) ⁻¹' B ∩
        (fun z => z.2.2) ⁻¹' (restrictΔ (rightExtendedIndex GO).symm ⁻¹' C)) := by
  intro G T ξS ξR L DG ξL B C t
  have hB : B = {ω | interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig T.source T.target GO ω).1)) ∈ observationSet jI S} := by
    exact large_preimage_boxCylinder si ti so xo GO hDO jD jO jI hlabel S hJS
  rw [hB]
  have h := fkNestedOrderedTriple_good_rightExtended_twoSided
    si ti so xo GO hq hp₀ hp₁ θ ζS ζL χ hright (observationSet jI S)
  dsimp only at h
  with_unfolding_all exact h


/-- The left/internal labels as an embedding into the global label type. -/
noncomputable def internalLabelEmbedding {D : Finset E} (jD : Fin (k + m) ≃ D) : Fin m ↪ E where
  toFun := internalLabel jD
  inj' := by
    intro i j hij
    have hsub : jD (exteriorFirst.symm (Sum.inl i)) =
        jD (exteriorFirst.symm (Sum.inl j)) := Subtype.ext hij
    have he := jD.injective hsub
    exact Sum.inl_injective (exteriorFirst.symm.injective he)

/-- The canonical finite observation base consisting of every internal label. -/
noncomputable def internalLabels {D : Finset E} (jD : Fin (k + m) ≃ D) : Finset E :=
  Finset.univ.map (internalLabelEmbedding jD)

/-- Canonical indexing of the internal observation base. -/
noncomputable def internalObservationEquiv {D : Finset E} (jD : Fin (k + m) ≃ D) :
    Fin m ≃ internalLabels jD :=
  (internalLabelEmbedding jD).toEquivRange.trans <| Set.equivOfEq <| by
    simp only [internalLabels, Finset.coe_map, Finset.coe_univ, Set.image_univ]

lemma internalObservationEquiv_apply {D : Finset E} (jD : Fin (k + m) ≃ D) (i : Fin m) :
    ((internalObservationEquiv jD i : internalLabels jD) : E) = internalLabel jD i := by
  rfl

lemma internalLabels_subset {D : Finset E} (jD : Fin (k + m) ≃ D) :
    internalLabels jD ⊆ D := by
  intro e he
  simp only [internalLabels, Finset.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  exact (jD (exteriorFirst.symm (Sum.inl i))).2

lemma internalLabels_subset_largeBox {D O : Finset E}
    (hDO : Disjoint (D : Set E) (O : Set E)) (jD : Fin (k + m) ≃ D)
    (jO : GO.Edge ≃ O) : internalLabels jD ⊆
      (largeBox si ti so xo GO hDO jD jO).edges := by
  intro e he
  have hd := internalLabels_subset jD he
  simp only [Finset.mem_union]
  exact Or.inl hd

section Geometry

universe uV

variable {V : Type uV} {Gph : SimpleGraph V}

/-- The open-path map induced by the explicit right-extended box labels. -/
noncomputable def rightOpenPathMap {D O : Finset Gph.edgeSet}
    (hDO : Disjoint (D : Set Gph.edgeSet) (O : Set Gph.edgeSet))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (d : (ambientOfSum (splitSource si so) (splitTarget ti xo)).Edge ≃
      (transportedAmbient si ti so xo).Edge)
    (z : (largeGraph si ti so xo GO).Configuration) (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1) :
    OpenPathGeometry.LabelledOpenPathMap
      (ambientOfSum (splitSource si so) (splitTarget ti xo)) Gph
      ((restrictΔ (GS := largeGraph si ti so xo GO)
        (GD := transportedAmbient si ti so xo) (GO := GO) (edgeEquiv GO) z) ∘ d)
      ((largeBox si ti so xo GO hDO jD jO).glue
        ((largeBox si ti so xo GO hDO jD jO).closedExterior,
          (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z)) where
  vertex := f
  edge a := (jD (d a)).1
  endpoint := hend
  isOpen := by
    classical
    intro a ha
    change restrictΔ (GS := largeGraph si ti so xo GO)
      (GD := transportedAmbient si ti so xo) (GO := GO) (edgeEquiv GO) z (d a) = true at ha
    simp only [FiniteBox.glue]
    split_ifs with hbox
    · have hread := largeBox_reindex_small si ti so xo GO hDO jD jO z (d a) hbox
      change (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z
        ⟨jD (d a), hbox⟩ = true
      exact hread.trans ha
    · have hmem : ((jD (d a)).1 : Gph.edgeSet) ∈
          (largeBox si ti so xo GO hDO jD jO).edges := by
        simp only [Finset.mem_union]
        exact Or.inl (jD (d a)).2
      exact (hbox hmem).elim

/-- Failure of the right-extended maximal split stratum is contained in the
closed-exterior realization of `farConnection`. -/
theorem bad_rightExtended_subset_closedLocalEvent {D O : Finset Gph.edgeSet}
    (hDO : Disjoint (D : Set Gph.edgeSet) (O : Set Gph.edgeSet))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (d : (ambientOfSum (splitSource si so) (splitTarget ti xo)).Edge ≃
      (transportedAmbient si ti so xo).Edge) (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1)
    (roots : Finset V) (o : V) (r : ℕ)
    (hleft : ∀ u, f (Sum.inl u) ∈ roots)
    (hfar : ∀ κ, r ≤ Gph.dist o (f (Sum.inr κ))) :
    (restrictΔ (GS := largeGraph si ti so xo GO)
      (GD := transportedAmbient si ti so xo) (GO := GO) (edgeEquiv GO) ⁻¹'
      ((fun ρ : (transportedAmbient si ti so xo).Configuration => ρ ∘ d) ⁻¹'
        maximalSplitStratum si ti so xo))ᶜ ⊆
      (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) ⁻¹'
        closedLocalEvent (largeBox si ti so xo GO hDO jD jO)
          (NestedAssembly.farConnection Gph roots o r) := by
  intro z hz
  change (restrictΔ (GS := largeGraph si ti so xo GO)
    (GD := transportedAmbient si ti so xo) (GO := GO) (edgeEquiv GO) z ∘ d) ∉
    maximalSplitStratum si ti so xo at hz
  change (largeBox si ti so xo GO hDO jD jO).glue
    ((largeBox si ti so xo GO hDO jD jO).closedExterior,
      (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) z) ∈
    NestedAssembly.farConnection Gph roots o r
  exact OpenPathGeometry.mem_farConnection_of_not_mem_maximalSplitStratum
    si ti so xo _ _ (rightOpenPathMap si ti so xo GO hDO jD jO d z f hend)
    roots o r hleft hfar hz

/-- The same arm inclusion for the canonical `smallStratum`, whose sum
coordinates are read through `exteriorFirst`. -/
theorem bad_rightExtended_smallStratum_subset_closedLocalEvent
    {D O : Finset Gph.edgeSet}
    (hDO : Disjoint (D : Set Gph.edgeSet) (O : Set Gph.edgeSet))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (exteriorFirst.symm a)).1).1)
    (roots : Finset V) (o : V) (r : ℕ)
    (hleft : ∀ u, f (Sum.inl u) ∈ roots)
    (hfar : ∀ κ, r ≤ Gph.dist o (f (Sum.inr κ))) :
    (restrictΔ (edgeEquiv GO) ⁻¹' smallStratum si ti so xo jD)ᶜ ⊆
      (largeBox si ti so xo GO hDO jD jO).reindex (largeIndex GO hDO jD jO) ⁻¹'
        closedLocalEvent (largeBox si ti so xo GO hDO jD jO)
          (NestedAssembly.farConnection Gph roots o r) := by
  have h := bad_rightExtended_subset_closedLocalEvent si ti so xo GO hDO jD jO
    exteriorFirst.symm f hend roots o r hleft hfar
  exact h


/-- **Finite-volume cylinder/arm estimate for the right-disjoint metric
presentation.**  The good intersection is proved, not assumed.  The hypotheses
`hdep`, `hend`, `hleft`, and `hfar` are precisely the finite-coordinate and
geometric arm inputs. -/
theorem cylinder_abs_sub_le_rightExtended_farConnection {D O J : Finset Gph.edgeSet}
    (hDO : Disjoint (D : Set Gph.edgeSet) (O : Set Gph.edgeSet))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) (jI : Fin m ≃ J)
    (hlabel : ∀ i, ((jI i : J) : Gph.edgeSet) = internalLabel jD i)
    (hJS : J ⊆ (largeBox si ti so xo GO hDO jD jO).edges) (hJD : J ⊆ D) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo) (S : Set (J → Bool))
    (f : U ⊕ K → V) (roots : Finset V) (o : V) (r : ℕ)
    (hdep : FKLimit.DependsOnCoordinates (NestedAssembly.farConnection Gph roots o r)
      (largeBox si ti so xo GO hDO jD jO).edges)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (exteriorFirst.symm a)).1).1)
    (hleft : ∀ u, f (Sum.inl u) ∈ roots)
    (hfar : ∀ κ, r ≤ Gph.dist o (f (Sum.inr κ))) :
    |((largeBox si ti so xo GO hDO jD jO).finiteVolumeLaw hq hp₁.le
          (largeSourceLaw si ti so xo GO hDO jD jO θ ζL χ) :
        Measure (Configuration Gph.edgeSet)).real (cylinder J S) -
      ((smallBox si ti so xo D jD).finiteVolumeLaw hq hp₁.le
          (smallSourceLaw si ti so xo jD θ ζS) :
        Measure (Configuration Gph.edgeSet)).real (cylinder J S)| ≤
      (percolation Gph (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection Gph roots o r) := by
  have he : ∀ i : J, (edgeEquiv GO) (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) =
      (largeIndex GO hDO jD jO).symm ⟨i.1, hJS i.2⟩ := by
    intro i
    have hmem : (jD (jD.symm ⟨i.1, hJD i.2⟩) : Gph.edgeSet) ∈
        (largeBox si ti so xo GO hDO jD jO).edges := by
      simpa only [Equiv.apply_symm_apply] using hJS i.2
    simpa only [Equiv.apply_symm_apply] using
      (edgeCompat (si := si) (ti := ti) (so := so) (xo := xo) (GO := GO)
        hDO jD jO (jD.symm ⟨i.1, hJD i.2⟩) hmem)
  have hU : (largeBox si ti so xo GO hDO jD jO).interiorRestriction ⁻¹'
      closedLocalEvent (largeBox si ti so xo GO hDO jD jO)
        (NestedAssembly.farConnection Gph roots o r) =
        NestedAssembly.farConnection Gph roots o r :=
    preimage_interiorRestriction_closedLocalEvent
      (largeBox si ti so xo GO hDO jD jO) _ hdep
  apply finiteBox_cylinder_abs_sub_le_farConnection_of_good
    (largeBox si ti so xo GO hDO jD jO) (smallBox si ti so xo D jD)
    (largeIndex GO hDO jD jO) jD GO (edgeEquiv GO)
    (largeSourceLaw si ti so xo GO hDO jD jO θ ζL χ)
    (smallSourceLaw si ti so xo jD θ ζS) hq hp₀ hp₁ J S hJS hJD he
    (smallStratum si ti so xo jD)
    (closedLocalEvent (largeBox si ti so xo GO hDO jD jO)
      (NestedAssembly.farConnection Gph roots o r))
    roots o r hU
  · have hg := good_rightExtended_twoSided si ti so xo GO hDO jD jO
      jI hlabel hJS hq hp₀ hp₁ θ ζS ζL χ hright S
    have hs : (fun i => (largeBox si ti so xo GO hDO jD jO).source
        (largeIndex GO hDO jD jO i)) =
        (rightExtendedGraph (transportedAmbient si ti so xo).source
          (transportedAmbient si ti so xo).target GO).source := by
      funext i
      exact largeBox_source si ti so xo GO hDO jD jO i
    have ht : (fun i => (largeBox si ti so xo GO hDO jD jO).target
        (largeIndex GO hDO jD jO i)) =
        (rightExtendedGraph (transportedAmbient si ti so xo).source
          (transportedAmbient si ti so xo).target GO).target := by
      funext i
      exact largeBox_target si ti so xo GO hDO jD jO i
    have hsd : (fun i => (smallBox si ti so xo D jD).source (jD i)) =
        (transportedAmbient si ti so xo).source := by
      funext i
      exact smallBox_source si ti so xo jD i
    have htd : (fun i => (smallBox si ti so xo D jD).target (jD i)) =
        (transportedAmbient si ti so xo).target := by
      funext i
      exact smallBox_target si ti so xo jD i
    rw [hs, ht, hsd, htd, largeBox_indexedBoundary, smallBox_indexedBoundary]
    dsimp only at hg ⊢
    exact hg
  · exact bad_rightExtended_smallStratum_subset_closedLocalEvent
      si ti so xo GO hDO jD jO f hend roots o r hleft hfar


/-- Canonical-internal-cylinder form of `cylinder_abs_sub_le_rightExtended_farConnection`. -/
theorem cylinder_abs_sub_le_rightExtended_internal_farConnection
    {D O : Finset Gph.edgeSet}
    (hDO : Disjoint (D : Set Gph.edgeSet) (O : Set Gph.edgeSet))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo) (S : Set (internalLabels jD → Bool))
    (f : U ⊕ K → V) (roots : Finset V) (o : V) (r : ℕ)
    (hdep : FKLimit.DependsOnCoordinates (NestedAssembly.farConnection Gph roots o r)
      (largeBox si ti so xo GO hDO jD jO).edges)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (exteriorFirst.symm a)).1).1)
    (hleft : ∀ u, f (Sum.inl u) ∈ roots)
    (hfar : ∀ κ, r ≤ Gph.dist o (f (Sum.inr κ))) :
    |((largeBox si ti so xo GO hDO jD jO).finiteVolumeLaw hq hp₁.le
          (largeSourceLaw si ti so xo GO hDO jD jO θ ζL χ) :
        Measure (Configuration Gph.edgeSet)).real (cylinder (internalLabels jD) S) -
      ((smallBox si ti so xo D jD).finiteVolumeLaw hq hp₁.le
          (smallSourceLaw si ti so xo jD θ ζS) :
        Measure (Configuration Gph.edgeSet)).real (cylinder (internalLabels jD) S)| ≤
      (percolation Gph (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection Gph roots o r) := by
  exact cylinder_abs_sub_le_rightExtended_farConnection (J := internalLabels jD)
    si ti so xo GO hDO jD jO (internalObservationEquiv jD)
    (internalObservationEquiv_apply jD) (internalLabels_subset_largeBox si ti so xo GO hDO jD jO)
    (internalLabels_subset jD) hq hp₀ hp₁ θ ζS ζL χ hright S
    f roots o r hdep hend hleft hfar

end Geometry

end FK.InfiniteVolume.NestedMetricGeometry.RightExtension

namespace FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Radial

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling
open FK.Exploration.NestedCoupledGood
open FK.Exploration.Sequential
open FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Finite.MarkovFactorization
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial

universe u v w x

variable {V : Type u} {G : SimpleGraph V}

/-- Exterior-first presentation of the actual finite metric-box edges. -/
noncomputable def smallIndex [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :
    Fin (Fintype.card (ExternalEdge (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) +
      Fintype.card (InternalEdge (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r))) ≃ (metricBox hG o r).edges :=
  exteriorFirst.trans ((d hG o R r).trans (edgeIndex _))

/-- The radial small box after its canonical interior/exterior vertex split. -/
noncomputable abbrev smallMetricBox [G.LocallyFinite] (hG : G.Connected) (o : V)
    (R r : ℕ) : FiniteBox G.edgeSet :=
  smallBox (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)
    (metricBox hG o r).edges (smallIndex hG o R r)

/-- A fresh right-labelled extension of the radial split. -/
noncomputable abbrev largeMetricBox [G.LocallyFinite] (hG : G.Connected) (o : V)
    (R r : ℕ) (GO : LabelledMultigraph) {O : Finset G.edgeSet}
    (hDO : Disjoint ((metricBox hG o r).edges : Set G.edgeSet) (O : Set G.edgeSet))
    (jO : GO.Edge ≃ O) : FiniteBox G.edgeSet :=
  largeBox (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r) GO
    hDO (smallIndex hG o R r) jO

/-- Fully instantiated radial estimate.  `φΣ` is `largeSourceLaw θ ζL χ`,
`φΔ` is `smallSourceLaw θ ζS`; they are not arbitrary unrelated boundary
setoids.  The common-upper good identity, maximal-stratum arm inclusion, and
finite-coordinate dependence are all discharged. -/
theorem cylinder_abs_sub_le_radial_rightExtended_farConnection
    [G.LocallyFinite] (hG : G.Connected) (o : V) {R r : ℕ} (hRr : R ≤ r)
    (GO : LabelledMultigraph) {O : Finset G.edgeSet}
    (hDO : Disjoint ((metricBox hG o r).edges : Set G.edgeSet) (O : Set G.edgeSet))
    (jO : GO.Edge ≃ O) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid (LeftVertex (inBall hG o R r)))
    (ζS ζL : Setoid (RightVertex (inBall hG o R r)))
    (χ : GO.BoundaryPartition) (S : Set (internalLabels (smallIndex hG o R r) → Bool)) :
    |((largeMetricBox hG o R r GO hDO jO).finiteVolumeLaw hq hp₁.le
          (largeSourceLaw (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)
            GO hDO (smallIndex hG o R r) jO θ ζL χ) :
        Measure (Configuration G.edgeSet)).real (cylinder (internalLabels (smallIndex hG o R r)) S) -
      ((smallMetricBox hG o R r).finiteVolumeLaw hq hp₁.le
          (smallSourceLaw (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)
            (smallIndex hG o R r) θ ζS) :
        Measure (Configuration G.edgeSet)).real (cylinder (internalLabels (smallIndex hG o R r)) S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G (innerBall hG o R) o R) := by
  have hroots : ∀ a ∈ innerBall hG o R, G.dist o a < R := by
    intro a ha
    exact (mem_innerBall hG).1 ha
  have hsubD : (metricBox hG o r).edges ⊆ (largeMetricBox hG o R r GO hDO jO).edges := by
    intro e he
    simp only [Finset.mem_union]
    exact Or.inl he
  have hdep : FKLimit.DependsOnCoordinates
      (NestedAssembly.farConnection G (innerBall hG o R) o R)
      (largeMetricBox hG o R r GO hDO jO).edges :=
    (farConnection_dependsOnCoordinates_metricBox hG (innerBall hG o R) o R hroots).mono
      ((nested_metricBox_edges hG o hRr).trans hsubD)
  have hend : ∀ a, s(f hG o R r
      ((ambientOfSum (splitSource (si hG o R r) (so hG o R r))
        (splitTarget (ti hG o R r) (xo hG o R r))).source a),
      f hG o R r ((ambientOfSum (splitSource (si hG o R r) (so hG o R r))
        (splitTarget (ti hG o R r) (xo hG o R r))).target a)) =
      (((smallIndex hG o R r) (exteriorFirst.symm a)).1).1 := by
    intro a
    have hidx : (smallIndex hG o R r) (exteriorFirst.symm a) =
        (edgeIndex (metricBox hG o r)) (d hG o R r a) := by
      change (edgeIndex (metricBox hG o r))
        (d hG o R r (exteriorFirst (exteriorFirst.symm a))) = _
      exact congrArg (fun a' => (edgeIndex (metricBox hG o r)) (d hG o R r a'))
        (exteriorFirst.apply_symm_apply a)
    exact (hend hG o R r a).trans (congrArg
      (fun e : (metricBox hG o r).edges => (e.1).1) hidx.symm)
  exact cylinder_abs_sub_le_rightExtended_internal_farConnection
    (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r) GO hDO
    (smallIndex hG o R r) jO hq hp₀ hp₁ θ ζS ζL χ
    (exteriorHasRight hG o R r) S (f hG o R r) (innerBall hG o R) o R hdep hend
    (hleft hG o R r) (hfar hG o R r)

end FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Radial

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Radial.smallIndex
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Radial.cylinder_abs_sub_le_radial_rightExtended_farConnection

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.largeIndex
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.largeBox_reindex_small
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.large_preimage_boxCylinder
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.edgeCompat
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.internalObservationEquiv
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.internalObservationEquiv_apply
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.internalLabels_subset
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.internalLabels_subset_largeBox
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.good_rightExtended_twoSided
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.rightOpenPathMap
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.bad_rightExtended_subset_closedLocalEvent
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.bad_rightExtended_smallStratum_subset_closedLocalEvent
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.cylinder_abs_sub_le_rightExtended_farConnection
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.cylinder_abs_sub_le_rightExtended_internal_farConnection
