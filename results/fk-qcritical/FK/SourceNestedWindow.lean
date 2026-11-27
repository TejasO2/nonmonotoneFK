import FK.NestedMetricWindow
import FK.SourceBoundary
import FK.NestedFiniteAssembly

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.Adaptive.NestedSumGeometry

open FK.Finite FK.Finite.LabelledMultigraph FK.Exploration.FKCoupling
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.OrdinaryGluing
open FK.SourceUniqueness
open FK.NestedMixture
open FK.Prop42Source

universe uV

variable {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]

noncomputable local instance : DecidableEq V := Classical.decEq _

/-- Small vertices with no globally incident edge leaving the small induced box. -/
def sourceCore (D : VertexExhaustion V) (m : ℕ) : Set (D.box (G := Gph) m).Vertex :=
  {c | (D.data (G := Gph)).StarContained m c}

/-- Joint exploration boundary outside the small source box and on its
non-core small vertices. -/
def sourceRoots (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n)) :
    Set (E.box (G := Gph) n).Vertex :=
  {x | x ∉ Set.range N.vert} ∪ N.vert '' (sourceCore D m)ᶜ

/-- The ordinary induced nested source boxes determine the adaptive geometry. -/
noncomputable def sourceNestedGeometry (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (hvert : ∀ c, (E.data (G := Gph)).vertex n (N.vert c) =
      (D.data (G := Gph)).vertex m c) :
    NestedSumGeometry (E.box (G := Gph) n).Vertex ((D.box (G := Gph) m).indexedGraph (edgeIndex _))
      (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)) := by
  let BS := E.box (G := Gph) n
  let BD := D.box (G := Gph) m
  let d := N.vert
  have hds : ∀ a, d (BD.source (edgeIndex _ a)) =
      BS.source ⟨(edgeIndex _ a).1, N.edge_sub (edgeIndex _ a).1 (edgeIndex _ a).2⟩ := by
    intro a
    exact (N.src _).symm
  have hdt : ∀ a, d (BD.target (edgeIndex _ a)) =
      BS.target ⟨(edgeIndex _ a).1, N.edge_sub (edgeIndex _ a).1 (edgeIndex _ a).2⟩ := by
    intro a
    exact (N.tgt _).symm
  have houtS : ∀ e : (outsideGraph BS BD).Edge,
      BS.source ⟨e.1, e.2.1⟩ ∉ d '' sourceCore D m := by
    rintro e ⟨c, hc, heq⟩
    apply e.2.2
    apply hc e.1
    change (D.data (G := Gph)).vertex m c ∈ (e.1 : Gph.edgeSet).1
    have heq0 := heq
    have heq' := (hvert c).symm.trans (congrArg
      (fun x : BS.Vertex => (E.data (G := Gph)).vertex n x) heq0)
    rw [heq']
    rw [← (E.data (G := Gph)).endpoint n ⟨e.1, e.2.1⟩]
    exact Sym2.mem_mk_left _ _
  have houtT : ∀ e : (outsideGraph BS BD).Edge,
      BS.target ⟨e.1, e.2.1⟩ ∉ d '' sourceCore D m := by
    rintro e ⟨c, hc, heq⟩
    apply e.2.2
    apply hc e.1
    change (D.data (G := Gph)).vertex m c ∈ (e.1 : Gph.edgeSet).1
    have heq0 := heq
    have heq' := (hvert c).symm.trans (congrArg
      (fun x : BS.Vertex => (E.data (G := Gph)).vertex n x) heq0)
    rw [heq']
    rw [← (E.data (G := Gph)).endpoint n ⟨e.1, e.2.1⟩]
    exact Sym2.mem_mk_right _ _
  exact nestedBoxGeometry BS BD (edgeIndex _) (edgeIndex _) N.edge_sub d N.vert_inj
    hds hdt (sourceCore D m) houtS houtT

lemma source_large_hstar_of_mem_interior (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (hvert : ∀ c, (E.data (G := Gph)).vertex n (N.vert c) =
      (D.data (G := Gph)).vertex m c)
    (k : Assignment (sourceNestedGeometry D E m n N hvert).graph.Edge)
    (v : (E.box (G := Gph) n).Vertex)
    (hv : v ∈ interior (G := (sourceNestedGeometry D E m n N hvert).graph)
      (sourceRoots D E m n N) k) :
    (E.data (G := Gph)).StarContained n v := by
  intro e he
  by_cases hvr : v ∈ Set.range N.vert
  · obtain ⟨c, rfl⟩ := hvr
    have hc : c ∈ sourceCore D m := by
      by_contra hn
      apply hv
      apply subset_closedRegion
      exact Or.inr ⟨c, hn, rfl⟩
    exact N.edge_sub e (hc e (by
      rw [← hvert c]
      exact he))
  · exact (hv (subset_closedRegion (Or.inl hvr))).elim

lemma source_small_mem_core_of_mem_interior (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (hvert : ∀ c, (E.data (G := Gph)).vertex n (N.vert c) =
      (D.data (G := Gph)).vertex m c)
    (k : Assignment (sourceNestedGeometry D E m n N hvert).graph.Edge)
    (c : (D.box (G := Gph) m).Vertex)
    (hc : (sourceNestedGeometry D E m n N hvert).vertex c ∈
      interior (G := (sourceNestedGeometry D E m n N hvert).graph)
        (sourceRoots D E m n N) k) :
    c ∈ (sourceNestedGeometry D E m n N hvert).core := by
  by_contra hn
  apply hc
  apply subset_closedRegion
  exact Or.inr ⟨c, hn, rfl⟩

lemma source_large_hwire (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (hvert : ∀ c, (E.data (G := Gph)).vertex n (N.vert c) =
      (D.data (G := Gph)).vertex m c)
    (α : (E.box (G := Gph) n).BoundaryPartition)
    (hα : HasSourceBoundaryClass (E.data (G := Gph)) α)
    (k : Assignment (sourceNestedGeometry D E m n N hvert).graph.Edge)
    (v : (E.box (G := Gph) n).Vertex)
    (hv : v ∈ interior (G := (sourceNestedGeometry D E m n N hvert).graph)
      (sourceRoots D E m n N) k) (w : (E.box (G := Gph) n).Vertex)
    (hvw : ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α).r v w) : v = w := by
  exact (hα v (source_large_hstar_of_mem_interior D E m n N hvert k v hv) w hvw).symm

lemma source_small_hwire (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (hvert : ∀ c, (E.data (G := Gph)).vertex n (N.vert c) =
      (D.data (G := Gph)).vertex m c)
    (β : (D.box (G := Gph) m).BoundaryPartition)
    (hβ : HasSourceBoundaryClass (D.data (G := Gph)) β)
    (k : Assignment (sourceNestedGeometry D E m n N hvert).graph.Edge)
    (c : (D.box (G := Gph) m).Vertex)
    (hc : (sourceNestedGeometry D E m n N hvert).vertex c ∈
      interior (G := (sourceNestedGeometry D E m n N hvert).graph)
        (sourceRoots D E m n N) k) (w : (D.box (G := Gph) m).Vertex)
    (hcw : ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β).r c w) : c = w := by
  have hcore := source_small_mem_core_of_mem_interior D E m n N hvert k c hc
  exact (hβ c hcore w hcw).symm

/-- Arbitrary induced nested source boxes: equation (9) with a direct arm to
outside-small/non-core vertices. -/
theorem sourceNested_abs_sub_le_arm (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (hvert : ∀ c, (E.data (G := Gph)).vertex n (N.vert c) =
      (D.data (G := Gph)).vertex m c)
    (α : (E.box (G := Gph) n).BoundaryPartition) (β : (D.box (G := Gph) m).BoundaryPartition)
    (hα : HasSourceBoundaryClass (E.data (G := Gph)) α)
    (hβ : HasSourceBoundaryClass (D.data (G := Gph)) β)
    (ξO : (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (e₀ : ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).Edge)
    (J : Finset ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge)
    (S : Set (J → Bool)) :
    let X := sourceNestedGeometry D E m n N hvert
    abs ((X.graph.fkPMF hq hp₁.le
        ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α)).toMeasure.real
        {ω | baseCylinder J S (fun d : ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge =>
          ω (Sum.inl d))} -
      (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).fkPMF hq hp₁.le
        ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β)).toMeasure.real
        (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (upperArm X J (sourceRoots D E m n N)) := by
  intro X
  exact X.windowCopyTriple_abs_sub_le_arm
    ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β) ξO
    ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α) hq hp₀ hp₁
    (sourceRoots D E m n N) e₀
    (source_small_mem_core_of_mem_interior D E m n N hvert)
    (source_large_hwire D E m n N hvert α hα)
    (source_small_hwire D E m n N hvert β hβ) J S


/-- Nested estimate specialized to the canonical induced nesting used by
`SourceUniqueness.NestedEquationNine`. -/
theorem sourceNested_abs_sub_le_arm_of_nest (D E : VertexExhaustion V) (m n : ℕ)
    (hn : D.region m ⊆ E.region n)
    (α : (E.box (G := Gph) n).BoundaryPartition)
    (β : (D.box (G := Gph) m).BoundaryPartition)
    (hα : HasSourceBoundaryClass (E.data (G := Gph)) α)
    (hβ : HasSourceBoundaryClass (D.data (G := Gph)) β)
    (ξO : (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (e₀ : ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).Edge)
    (J : Finset ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge)
    (S : Set (J → Bool)) :
    let N := E.nest D m n hn
    let X := sourceNestedGeometry D E m n N (fun _ => rfl)
    abs ((X.graph.fkPMF hq hp₁.le
        ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α)).toMeasure.real
        {ω | baseCylinder J S (fun d : ((D.box (G := Gph) m).indexedGraph
          (edgeIndex _)).Edge => ω (Sum.inl d))} -
      (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).fkPMF hq hp₁.le
        ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β)).toMeasure.real
        (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (upperArm X J (sourceRoots D E m n N)) := by
  intro N X
  exact sourceNested_abs_sub_le_arm D E m n N (fun _ => rfl) α β hα hβ ξO
    hq hp₀ hp₁ e₀ J S

end FK.Adaptive.NestedSumGeometry
