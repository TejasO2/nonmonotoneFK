import FK.NestedFiniteCoupling
import FK.NestedArmUniqueness
import FK.BernoulliFiniteBox
import FK.TransportBoundary

/-!
# Finite nested estimates on actual finite-box cylinders

This file supplies the finite-volume conversions needed after
`NestedFiniteCoupling`: a global finite-base cylinder supported in a box is an
explicit cylinder of that box's interior configuration, the closed-exterior
finite-volume law computes its mass by the actual finite FK PMF, and the
interior marginal of the upper global Bernoulli law is the actual finite
labelled-multigraph Bernoulli PMF.  No free-interior or `hgood` assertion is
made here.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.FiniteBox

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open CurvatureVariance.Infra.Percolation
open FK.Exploration.FKCoupling

universe u v

variable {E : Type u} (B : FiniteBox E)

/-- The interior readout of a global cylinder whose base lies in `B`. -/
def boxCylinder (J : Finset E) (S : Set (J → Bool)) (hJ : J ⊆ B.edges) :
    Set B.Interior :=
  {ω | (fun i : J => ω ⟨i.1, hJ i.2⟩) ∈ S}

@[simp] lemma mem_boxCylinder (J : Finset E) (S : Set (J → Bool))
    (hJ : J ⊆ B.edges) (ω : B.Interior) :
    ω ∈ B.boxCylinder J S hJ ↔ (fun i : J => ω ⟨i.1, hJ i.2⟩) ∈ S := Iff.rfl

/-- Gluing any exterior to a box interior computes exactly the box cylinder. -/
lemma preimage_glue_boxCylinder (J : Finset E) (S : Set (J → Bool))
    (hJ : J ⊆ B.edges) (η : B.Exterior) :
    (fun ω : B.Interior => B.glue (η, ω)) ⁻¹' cylinder J S =
      B.boxCylinder J S hJ := by
  ext ω
  simp only [Set.mem_preimage, cylinder, Finset.restrict, boxCylinder,
    Set.mem_setOf_eq]
  have h : J.restrict (B.glue (η, ω)) =
      (fun i : J => ω ⟨i.1, hJ i.2⟩) := by
    funext i
    simp [FiniteBox.glue, hJ i.2]
  rw [h]

/-- Restricting a global configuration to the box computes the same cylinder. -/
lemma preimage_interiorRestriction_boxCylinder (J : Finset E)
    (S : Set (J → Bool)) (hJ : J ⊆ B.edges) :
    B.interiorRestriction ⁻¹' B.boxCylinder J S hJ = cylinder J S := by
  ext ω
  simp only [Set.mem_preimage, cylinder, Finset.restrict, boxCylinder,
    Set.mem_setOf_eq]
  have h : (fun i : J => (B.interiorRestriction ω) ⟨i.1, hJ i.2⟩) =
      J.restrict ω := by
    funext i
    rfl
  rw [h]

/-- Exact finite-FK computation of a global cylinder in the closed-exterior
finite-volume representative. -/
theorem finiteVolumeLaw_real_boxCylinder {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (α : B.BoundaryPartition) (J : Finset E)
    (S : Set (J → Bool)) (hJ : J ⊆ B.edges) :
    (B.finiteVolumeLaw hq hp α : Measure (Configuration E)).real (cylinder J S) =
      (B.graph.fkPMF hq hp α).toMeasure.real (B.boxCylinder J S hJ) := by
  change (Measure.map (fun ω : B.Interior => B.glue (B.closedExterior, ω))
    (B.graph.fkMeasure hq hp α)).real (cylinder J S) = _
  rw [measureReal_def, measureReal_def, fkMeasure,
    Measure.map_apply (B.measurable_glue_const_left B.closedExterior)
      (dependsOnCoordinates_cylinder J S).measurableSet,
    B.preimage_glue_boxCylinder J S hJ B.closedExterior]

/-- The interior restriction of global constant-rate Bernoulli percolation is
the finite product on precisely the box edges. -/
lemma map_interiorRestriction_bernoulliProduct (r : unitInterval) :
    Measure.map B.interiorRestriction
        (FKLimit.bernoulliProduct (fun _ : E => r) : Measure (Configuration E)) =
      Measure.pi (fun _ : B.edges => bernoulliMeasure true false r) := by
  change Measure.map B.edges.restrict
    (Measure.infinitePi (fun _ : E => bernoulliMeasure true false r)) = _
  rw [Measure.infinitePi_map_restrict]

/-- The finite-indexed graph obtained from an edge reindexing of a box. -/
abbrev indexedGraph {n : ℕ} (j : Fin n ≃ B.edges) : LabelledMultigraph :=
  finIndexedGraph B.Vertex n (fun i => B.source (j i)) (fun i => B.target (j i))

/-- Read an indexed configuration in the original box coordinates. -/
def reindex {n : ℕ} (j : Fin n ≃ B.edges) :
    (B.indexedGraph j).Configuration → B.Interior :=
  B.graph.transportConfig (Equiv.refl _) j

/-- Boundary partitions are transported along the same reindexing. -/
def indexedBoundary {n : ℕ} (j : Fin n ≃ B.edges) (α : B.BoundaryPartition) :
    (B.indexedGraph j).BoundaryPartition :=
  B.graph.transportBoundaryOf (eE := j) (Equiv.refl _) α

/-- The transported box graph is definitionally the indexed graph used by the
nested coupling. -/
lemma transport_graph_eq_indexedGraph {n : ℕ} (j : Fin n ≃ B.edges) :
    B.graph.transport (Equiv.refl _) j = B.indexedGraph j := rfl

/-- Actual FK PMFs, with arbitrary boundary setoids, are unchanged by box edge
reindexing. -/
theorem map_reindex_fkPMF {n : ℕ} (j : Fin n ≃ B.edges)
    (α : B.BoundaryPartition) {q p : NNReal} (hq : 0 < q)
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (B.reindex j)
        ((B.indexedGraph j).fkPMF hq hp₁.le (B.indexedBoundary j α)) =
      B.graph.fkPMF hq hp₁.le α := by
  exact B.graph.map_transport_fkPMF (Equiv.refl _) j α hq hp₀ hp₁

/-- The same exact reindexing for the finite upper Bernoulli product. -/
theorem map_reindex_bernoulliProductPMF {n : ℕ} (j : Fin n ≃ B.edges)
    {p : NNReal} (hp : p ≤ 1) :
    PMF.map (B.reindex j) ((B.indexedGraph j).bernoulliProductPMF hp) =
      B.graph.bernoulliProductPMF hp := by
  change PMF.map (B.graph.transportConfig (Equiv.refl _) j)
    ((B.graph.transport (Equiv.refl _) j).bernoulliProductPMF hp) = _
  apply PMF.ext
  intro ω
  rw [map_equiv_apply]
  simp only [bernoulliProductPMF_apply]
  have h := B.graph.edgeWeight_transport (Equiv.refl _) j p
    ((B.graph.transportConfig (Equiv.refl _) j).symm ω)
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun x : NNReal => (x : ℝ≥0∞)) h.symm

/-- Real masses pull back along any exact PMF pushforward. -/
lemma pmf_toMeasure_real_preimage_of_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Finite α] [Finite β] (f : α → β) (μ : PMF α) (ν : PMF β)
    (h : μ.map f = ν) (A : Set β) :
    μ.toMeasure.real (f ⁻¹' A) = ν.toMeasure.real A := by
  have hf : Measurable f := measurable_of_finite f
  rw [measureReal_def, measureReal_def,
    ← Measure.map_apply hf (Set.toFinite A).measurableSet,
    PMF.toMeasure_map f μ hf, h]

end FK.InfiniteVolume.FiniteBox

namespace FK.InfiniteVolume.NestedFiniteAssembly

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open CurvatureVariance.Infra.Percolation
open FK.Exploration.FKCoupling

/-- Coerce a bounded `NNReal` rate to MathLib's unit interval. -/
def unitOfNN (p : NNReal) (hp : p ≤ 1) : unitInterval :=
  ⟨(p : ℝ), p.coe_nonneg, by exact_mod_cast hp⟩

@[simp] lemma toNNReal_unitOfNN {p : NNReal} (hp : p ≤ 1) :
    unitInterval.toNNReal (unitOfNN p hp) = p := by
  apply NNReal.eq
  rfl

@[simp] lemma toNNReal_symm_unitOfNN {p : NNReal} (hp : p ≤ 1) :
    unitInterval.toNNReal (unitInterval.symm (unitOfNN p hp)) = 1 - p := by
  apply NNReal.eq
  simp only [unitOfNN, unitInterval.coe_symm_eq]
  exact (NNReal.coe_sub hp).symm

/-- The one-edge `NNReal` Bernoulli PMF is Mathlib's unit-interval Bernoulli
measure, with the same `true = open` convention. -/
lemma bernoulliPMF_toMeasure {p : NNReal} (hp : p ≤ 1) :
    (FKModel.bernoulliPMF p hp).toMeasure =
      bernoulliMeasure true false (unitOfNN p hp) := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (by simp)]
  cases b <;>
    simp [FKModel.bernoulliPMF_apply, bernoulliMeasure_def]

/-- The explicit finite labelled-multigraph Bernoulli PMF induces exactly the
finite product measure used by the global finite-box restriction. -/
theorem bernoulliProductPMF_toMeasure (G : LabelledMultigraph)
    {p : NNReal} (hp : p ≤ 1) :
    (G.bernoulliProductPMF hp).toMeasure =
      Measure.pi (fun _ : G.Edge =>
        bernoulliMeasure true false (unitOfNN p hp)) := by
  apply Measure.ext_of_singleton
  intro ω
  rw [PMF.toMeasure_apply_singleton _ _ (by simp), Measure.pi_singleton]
  simp only [bernoulliProductPMF_apply, edgeWeight]
  rw [ENNReal.ofNNReal_finsetProd]
  apply Finset.prod_congr rfl
  intro e _
  cases h : ω e <;>
    simp [h, bernoulliMeasure_def, FKModel.bernoulliPMF_apply]

/-- The global upper Bernoulli law restricted to a box is literally its
labelled-multigraph `bernoulliProductPMF`. -/
lemma map_interiorRestriction_bernoulliProductPMF {E : Type u}
    (B : FiniteBox E) {p : NNReal} (hp : p ≤ 1) :
    Measure.map B.interiorRestriction
        (FKLimit.bernoulliProduct (fun _ : E => unitOfNN p hp) :
          Measure (Configuration E)) =
      (B.graph.bernoulliProductPMF hp).toMeasure := by
  rw [B.map_interiorRestriction_bernoulliProduct, bernoulliProductPMF_toMeasure]

/-- Real-mass form of the preceding exact marginal identity.  No measurability
condition is needed on the target event: the box configuration space is finite
and discrete. -/
lemma bernoulliProduct_real_interior_preimage {E : Type u}
    (B : FiniteBox E) {p : NNReal} (hp : p ≤ 1) (D : Set B.Interior) :
    (FKLimit.bernoulliProduct (fun _ : E => unitOfNN p hp) :
      Measure (Configuration E)).real (B.interiorRestriction ⁻¹' D) =
    (B.graph.bernoulliProductPMF hp).toMeasure.real D := by
  rw [measureReal_def, measureReal_def,
    ← Measure.map_apply B.measurable_interiorRestriction MeasurableSet.of_discrete,
    map_interiorRestriction_bernoulliProductPMF B hp]

/-- The accepted conditional nested estimate with its exceptional event
replaced by any proved larger event.  `hgood` is unchanged. -/
theorem fkNestedOrderedTriple_abs_sub_le_of_good_of_subset
    {VS VD : Type*} [Fintype VS] [Fintype VD] {nS nD : ℕ}
    (sS tS : Fin nS → VS) (sD tD : Fin nD → VD)
    (GO : LabelledMultigraph)
    (e : (finIndexedGraph VD nD sD tD).Edge ⊕ GO.Edge ≃
      (finIndexedGraph VS nS sS tS).Edge)
    (ξ : (finIndexedGraph VS nS sS tS).BoundaryPartition)
    (τ : (finIndexedGraph VD nD sD tD).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set (finIndexedGraph VS nS sS tS).Configuration)
    (A C : Set (finIndexedGraph VD nD sD tD).Configuration)
    (hBA : B = restrictΔ e ⁻¹' A)
    (hgood :
      (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.toMeasure
        ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      (fkNestedOrderedTriple sS tS sD tD GO e ξ τ hq hp₀ hp₁).dist.toMeasure
        ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (D : Set (finIndexedGraph VS nS sS tS).Configuration)
    (hD : (restrictΔ e ⁻¹' C)ᶜ ⊆ D) :
    |((finIndexedGraph VS nS sS tS).fkPMF hq hp₁.le ξ).toMeasure.real B -
        ((finIndexedGraph VD nD sD tD).fkPMF hq hp₁.le τ).toMeasure.real A| ≤
      ((finIndexedGraph VS nS sS tS).bernoulliProductPMF
        (upperRateNN_le_one hq hp₁.le)).toMeasure.real D := by
  exact (fkNestedOrderedTriple_abs_sub_le_of_good sS tS sD tD GO e ξ τ
    hq hp₀ hp₁ B A C hBA hgood).trans (measureReal_mono hD)

/-- Edge compatibility on the cylinder base proves the exact nested
observation compatibility, pointwise. -/
lemma reindex_preimage_boxCylinder_of_edge_compat {E : Type u}
    (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (GO : LabelledMultigraph)
    (e : (BD.indexedGraph jD).Edge ⊕ GO.Edge ≃ (BS.indexedGraph jS).Edge)
    (J : Finset E) (S : Set (J → Bool))
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges)
    (he : ∀ i : J,
      e (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) = jS.symm ⟨i.1, hJS i.2⟩) :
    BS.reindex jS ⁻¹' BS.boxCylinder J S hJS =
      restrictΔ e ⁻¹' (BD.reindex jD ⁻¹' BD.boxCylinder J S hJD) := by
  ext ω
  simp only [Set.mem_preimage, FiniteBox.mem_boxCylinder]
  have hfun : (fun i : J => BS.reindex jS ω ⟨i.1, hJS i.2⟩) =
      (fun i : J => BD.reindex jD (restrictΔ e ω) ⟨i.1, hJD i.2⟩) := by
    funext i
    change ω (jS.symm ⟨i.1, hJS i.2⟩) = (restrictΔ e ω) (jD.symm ⟨i.1, hJD i.2⟩)
    rw [← he i]
    rfl
  rw [hfun]

/-- **Finite nested cylinder/arm estimate on actual finite boxes.**  Both
left-hand probabilities are the actual closed-exterior `finiteVolumeLaw`s on
one and the same global cylinder.  The good-interior intersection equality is
still an explicit premise.  The only geometric prerequisites are edge
compatibility on the cylinder base and containment of the exceptional event
in `D`; the right-hand side is the exact global Bernoulli mass of the box
realization of `D`. -/
theorem finiteBox_cylinder_abs_sub_le_interiorUpper_of_good {E : Type u}
    (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (GO : LabelledMultigraph)
    (e : (BD.indexedGraph jD).Edge ⊕ GO.Edge ≃ (BS.indexedGraph jS).Edge)
    (α : BS.BoundaryPartition) (β : BD.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset E) (S : Set (J → Bool))
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges)
    (he : ∀ i : J,
      e (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) = jS.symm ⟨i.1, hJS i.2⟩)
    (C : Set (BD.indexedGraph jD).Configuration) (D : Set BS.Interior)
    (U : Set (Configuration E)) (hU : BS.interiorRestriction ⁻¹' D = U)
    (hgood :
      let t := fkNestedOrderedTriple
        (fun i => BS.source (jS i)) (fun i => BS.target (jS i))
        (fun i => BD.source (jD i)) (fun i => BD.target (jD i))
        GO e (BS.indexedBoundary jS α) (BD.indexedBoundary jD β) hq hp₀ hp₁
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (hD : (restrictΔ e ⁻¹' C)ᶜ ⊆ BS.reindex jS ⁻¹' D) :
    |(BS.finiteVolumeLaw hq hp₁.le α : Measure (Configuration E)).real
          (cylinder J S) -
        (BD.finiteVolumeLaw hq hp₁.le β : Measure (Configuration E)).real
          (cylinder J S)| ≤
      (FKLimit.bernoulliProduct
        (fun _ : E => unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)) :
        Measure (Configuration E)).real U := by
  let hr := upperRateNN_le_one hq hp₁.le
  have hBA := reindex_preimage_boxCylinder_of_edge_compat BS BD jS jD GO e
    J S hJS hJD he
  have hbase := fkNestedOrderedTriple_abs_sub_le_of_good_of_subset
    (fun i => BS.source (jS i)) (fun i => BS.target (jS i))
    (fun i => BD.source (jD i)) (fun i => BD.target (jD i))
    GO e (BS.indexedBoundary jS α) (BD.indexedBoundary jD β) hq hp₀ hp₁
    (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS)
    (BD.reindex jD ⁻¹' BD.boxCylinder J S hJD) C hBA hgood
    (BS.reindex jS ⁻¹' D) hD
  have hfirst := FiniteBox.pmf_toMeasure_real_preimage_of_map (BS.reindex jS)
    ((BS.indexedGraph jS).fkPMF hq hp₁.le (BS.indexedBoundary jS α))
    (BS.graph.fkPMF hq hp₁.le α) (BS.map_reindex_fkPMF jS α hq hp₀ hp₁)
    (BS.boxCylinder J S hJS)
  have hsecond := FiniteBox.pmf_toMeasure_real_preimage_of_map (BD.reindex jD)
    ((BD.indexedGraph jD).fkPMF hq hp₁.le (BD.indexedBoundary jD β))
    (BD.graph.fkPMF hq hp₁.le β) (BD.map_reindex_fkPMF jD β hq hp₀ hp₁)
    (BD.boxCylinder J S hJD)
  have hupper := FiniteBox.pmf_toMeasure_real_preimage_of_map (BS.reindex jS)
    ((BS.indexedGraph jS).bernoulliProductPMF hr)
    (BS.graph.bernoulliProductPMF hr) (BS.map_reindex_bernoulliProductPMF jS hr) D
  rw [hfirst, hsecond, hupper] at hbase
  rw [← hU, BS.finiteVolumeLaw_real_boxCylinder hq hp₁.le α J S hJS,
    BD.finiteVolumeLaw_real_boxCylinder hq hp₁.le β J S hJD,
    bernoulliProduct_real_interior_preimage BS hr D]
  exact hbase


/-- **Finite nested `farConnection` estimate on an actual graph.**  This is
`finiteBox_cylinder_abs_sub_le_interiorUpper_of_good` specialized to the exact
arm event used by `NestedArmUniqueness`, with arbitrary roots, center and
radius. `hU` makes the required local/global finite-box realization explicit. -/
theorem finiteBox_cylinder_abs_sub_le_farConnection_of_good
    {V : Type u} {G : SimpleGraph V} (BS BD : FiniteBox G.edgeSet) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (GO : LabelledMultigraph)
    (e : (BD.indexedGraph jD).Edge ⊕ GO.Edge ≃ (BS.indexedGraph jS).Edge)
    (α : BS.BoundaryPartition) (β : BD.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool))
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges)
    (he : ∀ i : J,
      e (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) = jS.symm ⟨i.1, hJS i.2⟩)
    (C : Set (BD.indexedGraph jD).Configuration) (D : Set BS.Interior)
    (roots : Finset V) (center : V) (r : ℕ)
    (hU : BS.interiorRestriction ⁻¹' D =
      NestedAssembly.farConnection G roots center r)
    (hgood :
      let t := fkNestedOrderedTriple
        (fun i => BS.source (jS i)) (fun i => BS.target (jS i))
        (fun i => BD.source (jD i)) (fun i => BD.target (jD i))
        GO e (BS.indexedBoundary jS α) (BD.indexedBoundary jD β) hq hp₀ hp₁
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (hD : (restrictΔ e ⁻¹' C)ᶜ ⊆ BS.reindex jS ⁻¹' D) :
    |(BS.finiteVolumeLaw hq hp₁.le α : Measure (Configuration G.edgeSet)).real
          (cylinder J S) -
        (BD.finiteVolumeLaw hq hp₁.le β : Measure (Configuration G.edgeSet)).real
          (cylinder J S)| ≤
      (percolation G (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G roots center r) := by
  have h := finiteBox_cylinder_abs_sub_le_interiorUpper_of_good BS BD jS jD GO e α β
    hq hp₀ hp₁ J S hJS hJD he C D
    (NestedAssembly.farConnection G roots center r) hU hgood hD
  change |(BS.finiteVolumeLaw hq hp₁.le α : Measure (Configuration G.edgeSet)).real
      (cylinder J S) -
    (BD.finiteVolumeLaw hq hp₁.le β : Measure (Configuration G.edgeSet)).real
      (cylinder J S)| ≤
    (Measure.infinitePi (fun _ : G.edgeSet => bernoulliMeasure true false
      (unitOfNN (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)))).real
      (NestedAssembly.farConnection G roots center r) at h
  exact h

end FK.InfiniteVolume.NestedFiniteAssembly
