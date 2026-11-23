import FK.NestedMetricGeometry

/-!
# Finite region splits of indexed nested metric boxes

A decidable vertex region induces an exact split of every finite indexed graph
into edges internal to the region and edges in its complement.  Both vertex and
edge decompositions are canonical `Equiv.sumCompl` equivalences.  We then
instantiate the construction with an open metric ball on an actual metric box.
No stochastic good-intersection assertion is made here.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.InfiniteVolume.NestedFiniteAssembly

universe u v

variable {W : Type v} [Fintype W] {n : ℕ}
variable (s t : Fin n → W) (L : W → Prop) [DecidablePred L]

/-- Vertices of the selected region. -/
abbrev LeftVertex := {x : W // L x}

/-- Vertices outside the selected region. -/
abbrev RightVertex := {x : W // ¬ L x}

/-- The canonical equivalence between the two vertex summands and all vertices. -/
noncomputable def vertexEquiv : LeftVertex L ⊕ RightVertex L ≃ W :=
  Equiv.sumCompl L

/-- An edge is internal precisely when both endpoints are in the region. -/
def IsInternal (i : Fin n) : Prop := L (s i) ∧ L (t i)

/-- The finite type of internal labels. -/
abbrev InternalEdge := {i : Fin n // IsInternal s t L i}

/-- The finite type of labels not internal to the region. -/
abbrev ExternalEdge := {i : Fin n // ¬ IsInternal s t L i}

/-- The two finite summands indexing the split graph. -/
abbrev SplitIndex :=
  Fin (Fintype.card (InternalEdge s t L)) ⊕ Fin (Fintype.card (ExternalEdge s t L))

/-- Canonical finite index of the internal labels. -/
noncomputable def internalIndex :
    Fin (Fintype.card (InternalEdge s t L)) ≃ InternalEdge s t L :=
  (Fintype.equivFin _).symm

/-- Canonical finite index of the remaining labels. -/
noncomputable def externalIndex :
    Fin (Fintype.card (ExternalEdge s t L)) ≃ ExternalEdge s t L :=
  (Fintype.equivFin _).symm

/-- Exact disjoint-union presentation of all finite indexed edges. -/
noncomputable def edgeEquiv :
    Fin (Fintype.card (InternalEdge s t L)) ⊕
      Fin (Fintype.card (ExternalEdge s t L)) ≃ Fin n :=
  (Equiv.sumCongr (internalIndex s t L) (externalIndex s t L)).trans
    (Equiv.sumCompl (IsInternal s t L))

/-- Internal source in the left vertex type. -/
noncomputable def internalSource :
    Fin (Fintype.card (InternalEdge s t L)) → LeftVertex L :=
  fun i => ⟨s (internalIndex s t L i), (internalIndex s t L i).2.1⟩

/-- Internal target in the left vertex type. -/
noncomputable def internalTarget :
    Fin (Fintype.card (InternalEdge s t L)) → LeftVertex L :=
  fun i => ⟨t (internalIndex s t L i), (internalIndex s t L i).2.2⟩

/-- Source of a remaining edge, sent to its actual vertex summand. -/
noncomputable def externalSource :
    Fin (Fintype.card (ExternalEdge s t L)) → LeftVertex L ⊕ RightVertex L :=
  fun i => (vertexEquiv L).symm (s (externalIndex s t L i))

/-- Target of a remaining edge, sent to its actual vertex summand. -/
noncomputable def externalTarget :
    Fin (Fintype.card (ExternalEdge s t L)) → LeftVertex L ⊕ RightVertex L :=
  fun i => (vertexEquiv L).symm (t (externalIndex s t L i))

omit [Fintype W] [DecidablePred L] in
@[simp] lemma edgeEquiv_inl (i : Fin (Fintype.card (InternalEdge s t L))) :
    edgeEquiv s t L (Sum.inl i) = internalIndex s t L i := by
  rfl

omit [Fintype W] [DecidablePred L] in
@[simp] lemma edgeEquiv_inr (i : Fin (Fintype.card (ExternalEdge s t L))) :
    edgeEquiv s t L (Sum.inr i) = externalIndex s t L i := by
  rfl

omit [Fintype W] in
/-- The canonical vertex map sends a split internal source to the source of the
corresponding original edge. -/
theorem vertexEquiv_splitSource (a :
    Fin (Fintype.card (InternalEdge s t L)) ⊕
      Fin (Fintype.card (ExternalEdge s t L))) :
    vertexEquiv L
      (splitSource (internalSource s t L) (externalSource s t L) a) =
        s (edgeEquiv s t L a) := by
  cases a with
  | inl i => rfl
  | inr i => exact (vertexEquiv L).apply_symm_apply _

omit [Fintype W] in
/-- The corresponding identity for targets. -/
theorem vertexEquiv_splitTarget (a :
    Fin (Fintype.card (InternalEdge s t L)) ⊕
      Fin (Fintype.card (ExternalEdge s t L))) :
    vertexEquiv L
      (splitTarget (internalTarget s t L) (externalTarget s t L) a) =
        t (edgeEquiv s t L a) := by
  cases a with
  | inl i => rfl
  | inr i => exact (vertexEquiv L).apply_symm_apply _

omit [Fintype W] in
/-- Every remaining edge has at least one endpoint in the right summand. -/
theorem exteriorHasRight :
    ExteriorHasRight (externalSource s t L) (externalTarget s t L) := by
  intro i
  have hi : ¬ (L (s (externalIndex s t L i)) ∧
      L (t (externalIndex s t L i))) := (externalIndex s t L i).2
  by_cases hs : L (s (externalIndex s t L i))
  · have ht : ¬ L (t (externalIndex s t L i)) := fun ht => hi ⟨hs, ht⟩
    right
    exact ⟨⟨_, ht⟩, (Equiv.sumCompl_symm_apply_of_neg ht).symm⟩
  · left
    exact ⟨⟨_, hs⟩, (Equiv.sumCompl_symm_apply_of_neg hs).symm⟩

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit


namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling
open FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The actual metric-box source map on its canonical finite edge index. -/
noncomputable abbrev boxSource [G.LocallyFinite] (hG : G.Connected) (o : V) (r : ℕ) :
    Fin (Fintype.card (metricBox hG o r).edges) → (metricBox hG o r).Vertex :=
  fun i => (metricBox hG o r).source (edgeIndex _ i)

/-- The actual metric-box target map on its canonical finite edge index. -/
noncomputable abbrev boxTarget [G.LocallyFinite] (hG : G.Connected) (o : V) (r : ℕ) :
    Fin (Fintype.card (metricBox hG o r).edges) → (metricBox hG o r).Vertex :=
  fun i => (metricBox hG o r).target (edgeIndex _ i)

/-- Membership in the open ball of radius `R`, read on vertices of the actual
metric box at radius `r`. -/
def inBall [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ)
    (x : (metricBox hG o r).Vertex) : Prop :=
  G.dist o x.1 < R

/-- The finite edge equivalence induced by the ball/complement vertex split. -/
noncomputable def d [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :=
  edgeEquiv (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)

/-- Internal sources on the actual open-ball region. -/
noncomputable def si [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :=
  internalSource (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)

/-- Internal targets on the actual open-ball region. -/
noncomputable def ti [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :=
  internalTarget (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)

/-- Exterior sources in the ball/complement vertex sum. -/
noncomputable def so [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :=
  externalSource (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)

/-- Exterior targets in the ball/complement vertex sum. -/
noncomputable def xo [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :=
  externalTarget (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)

/-- The actual global embedding of the two metric vertex regions. -/
noncomputable def f [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :
    LeftVertex (inBall hG o R r) ⊕ RightVertex (inBall hG o R r) → V :=
  fun x => (vertexEquiv (inBall hG o R r) x).1

/-- The actual pulled-back maximal split stratum on the smaller indexed metric
box.  This is a definition of the event, not a hypothesis about its mass. -/
noncomputable def stratum [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :
    Set (((metricBox hG o r).indexedGraph (edgeIndex _)).Configuration) :=
  (fun ρ : ((metricBox hG o r).indexedGraph (edgeIndex _)).Configuration =>
    ρ ∘ d hG o R r) ⁻¹' maximalSplitStratum (si hG o R r) (ti hG o R r)
      (so hG o R r) (xo hG o R r)

/-- Metric endpoints agree exactly with the canonical ball/complement map. -/
theorem hend [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ)
    (a : SplitIndex (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)) :
    s(f hG o R r ((ambientOfSum (splitSource (si hG o R r) (so hG o R r))
      (splitTarget (ti hG o R r) (xo hG o R r))).source a),
      f hG o R r ((ambientOfSum (splitSource (si hG o R r) (so hG o R r))
      (splitTarget (ti hG o R r) (xo hG o R r))).target a)) =
        (((edgeIndex (metricBox hG o r)) (d hG o R r a)).1).1 := by
  have hs := congrArg Subtype.val
    (vertexEquiv_splitSource (boxSource hG o r) (boxTarget hG o r)
      (inBall hG o R r) a)
  have ht := congrArg Subtype.val
    (vertexEquiv_splitTarget (boxSource hG o r) (boxTarget hG o r)
      (inBall hG o R r) a)
  change s((vertexEquiv (inBall hG o R r)
      (splitSource (internalSource (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) (externalSource (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) a)).1,
    (vertexEquiv (inBall hG o R r)
      (splitTarget (internalTarget (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) (externalTarget (boxSource hG o r) (boxTarget hG o r)
        (inBall hG o R r)) a)).1) = _
  rw [hs, ht]
  exact (((edgeIndex (metricBox hG o r)) (d hG o R r a)).1).1.out_eq

/-- Every left vertex is one of the actual finite roots `innerBall hG o R`. -/
theorem hleft [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ)
    (u : LeftVertex (inBall hG o R r)) :
    f hG o R r (Sum.inl u) ∈ innerBall hG o R := by
  apply (mem_innerBall hG).2
  simpa [f, vertexEquiv, inBall] using u.2

/-- Every right vertex lies beyond the prescribed arm radius `R`. -/
theorem hfar [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ)
    (k : RightVertex (inBall hG o R r)) :
    R ≤ G.dist o (f hG o R r (Sum.inr k)) := by
  simpa [f, vertexEquiv, inBall] using Nat.le_of_not_gt k.2

/-- No remaining edge misses the right metric region completely. -/
theorem exteriorHasRight [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ) :
    ExteriorHasRight (so hG o R r) (xo hG o R r) := by
  exact RegionSplit.exteriorHasRight (boxSource hG o r) (boxTarget hG o r)
    (inBall hG o R r)

/-- Membership in the constructed maximal stratum is exactly separation of the
actual exterior bits from the open-ball vertex region. -/
theorem mem_stratum_iff [G.LocallyFinite] (hG : G.Connected) (o : V) (R r : ℕ)
    (ρ : ((metricBox hG o r).indexedGraph (edgeIndex _)).Configuration) :
    ρ ∈ stratum hG o R r ↔
      Separated (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)
        (exteriorConfig (ρ ∘ d hG o R r)) := by
  exact mem_maximalSplitStratum_iff (si hG o R r) (ti hG o R r)
    (so hG o R r) (xo hG o R r) (ρ ∘ d hG o R r) (exteriorHasRight hG o R r)

/-- The all-closed smaller-box configuration lies in the radial maximal
stratum.  In particular the constructed conditioning event is nonempty. -/
theorem allClosed_mem_stratum [G.LocallyFinite] (hG : G.Connected) (o : V)
    (R r : ℕ) :
    (fun _ : Fin (Fintype.card (metricBox hG o r).edges) => false) ∈
      stratum hG o R r := by
  apply (mem_stratum_iff hG o R r _).2
  intro i hi
  change false = true at hi
  contradiction

/-- **Exact radial exploration-region error inclusion.**  The finite maximal
split presentation, edge equivalence, global vertex map, endpoint identity,
left roots, and right radius are all constructed above.  The bound uses the
finite ball `innerBall hG o R` itself as its root set; it is not promoted to an
arm estimate from a smaller fixed root set. -/
theorem bad_stratum_subset_closedLocalEvent [G.LocallyFinite]
    (hG : G.Connected) (o : V) (R r : ℕ)
    (BS : FiniteBox G.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (hBD : (metricBox hG o r).edges ⊆ BS.edges) :
    (restrictΔ (nestedEdgeEquiv BS (metricBox hG o r) jS (edgeIndex _) hBD) ⁻¹'
      stratum hG o R r)ᶜ ⊆
      BS.reindex jS ⁻¹' closedLocalEvent BS
        (NestedAssembly.farConnection G (innerBall hG o R) o R) := by
  simpa only [stratum] using
    (OpenPathGeometry.bad_maximalSplit_subset_closedLocalEvent
    BS (metricBox hG o r) jS (edgeIndex _) hBD
    (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)
    (d hG o R r) (f hG o R r) (hend hG o R r)
    (innerBall hG o R) o R (hleft hG o R r) (hfar hG o R r))

/-- The finite-volume estimate with every geometric input discharged by the
radial construction.  The remaining `hgood` is the exact normalized measure
identity on the constructed maximal stratum, not a geometric assumption.
Here `R ≤ r ≤ n`: the arm uses the roots and radius `R`, while the two nested
FK boxes have scales `r` and `n`. -/
theorem cylinder_abs_sub_le_radial_farConnection_of_good [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) (J : Finset G.edgeSet) (S : Set (J → Bool))
    {R r n : ℕ} (hRr : R ≤ r) (hrn : r ≤ n)
    (α : (metricBox hG o n).BoundaryPartition)
    (β : (metricBox hG o r).BoundaryPartition)
    (hJD : J ⊆ (metricBox hG o r).edges)
    (hgood :
      let t := metricNestedTriple hG o hrn α β hq hp₀ hp₁
      let BS := metricBox hG o n
      let e := metricNestedEquiv hG o hrn
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (hJD.trans (nested_metricBox_edges hG o hrn))) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' stratum hG o R r)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex (edgeIndex BS) ⁻¹'
            BS.boxCylinder J S (hJD.trans (nested_metricBox_edges hG o hrn))) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' stratum hG o R r))) :
    |((metricBox hG o n).finiteVolumeLaw hq hp₁.le α :
          Measure (Configuration G.edgeSet)).real (cylinder J S) -
        ((metricBox hG o r).finiteVolumeLaw hq hp₁.le β :
          Measure (Configuration G.edgeSet)).real (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G (innerBall hG o R) o R) := by
  have hroots : ∀ a ∈ innerBall hG o R, G.dist o a < R := by
    intro a ha
    exact (mem_innerBall hG).1 ha
  have hdep : FKLimit.DependsOnCoordinates
      (NestedAssembly.farConnection G (innerBall hG o R) o R)
        (metricBox hG o n).edges :=
    (farConnection_dependsOnCoordinates_metricBox hG (innerBall hG o R) o R hroots).mono
      ((nested_metricBox_edges hG o hRr).trans (nested_metricBox_edges hG o hrn))
  apply finiteBox_cylinder_abs_sub_le_farConnection_canonical_of_good
    (metricBox hG o n) (metricBox hG o r) (nested_metricBox_edges hG o hrn)
    α β hq hp₀ hp₁ J S (hJD.trans (nested_metricBox_edges hG o hrn)) hJD
    (innerBall hG o R) o R hdep (stratum hG o R r) hgood
  simpa only [metricNestedEquiv] using
    (bad_stratum_subset_closedLocalEvent hG o R r (metricBox hG o n)
      (edgeIndex _) (nested_metricBox_edges hG o hrn))

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.edgeEquiv
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.vertexEquiv_splitSource
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.vertexEquiv_splitTarget
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.exteriorHasRight
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.d
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.f
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.hend
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.hleft
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.hfar
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.mem_stratum_iff
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.allClosed_mem_stratum
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.bad_stratum_subset_closedLocalEvent
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial.cylinder_abs_sub_le_radial_farConnection_of_good
