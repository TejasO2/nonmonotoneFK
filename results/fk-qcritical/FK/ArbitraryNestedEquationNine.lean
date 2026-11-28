import FK.SourceGlobalWindow
import FK.IsolatedBoundaryTransport
import FK.SourceUniqueness

/-!
# Literal nested equation (9) for arbitrary `NestedBox` witnesses

An arbitrary `NestedBox` need not preserve global labels on vertices which are
isolated in the inner box.  We therefore use the induced box on the intersection
of the two vertex regions.  Its edge set equals the inner edge set.  The exact
arbitrary-boundary deletion theorem identifies the two inner finite-volume
cylinders.  Every boundary vertex of the intersection is already a boundary
vertex of the original inner region, so the canonical global estimate applies
with the literal boundary event and upper Bernoulli law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.SourceUniqueness

open FK.Finite FK.Finite.LabelledMultigraph FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.NestedMixture
open FK.Adaptive.NestedSumGeometry
open FK.IsolatedBoundaryTransport
open FK.Exploration.FKCoupling

universe uV

variable {V : Type uV} {G : SimpleGraph V} [G.LocallyFinite]

/-- An exhaustion whose zero stage is the intersection of two prescribed
finite regions.  Later stages are only used to make it a genuine exhaustion. -/
noncomputable def intersectionExhaustion (D E : VertexExhaustion V) (m n : ℕ) :
    VertexExhaustion V where
  region
    | 0 => D.region m ∩ E.region n
    | k + 1 => D.region m ∩ E.region n ∪ E.region k
  monotone := by
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact Finset.Subset.rfl
      | succ j => exact Finset.subset_union_left
    | succ i =>
      cases j with
      | zero => exact (Nat.not_succ_le_zero i hij).elim
      | succ j =>
        change D.region m ∩ E.region n ∪ E.region i ⊆
          D.region m ∩ E.region n ∪ E.region j
        apply Finset.union_subset_union_right
        exact E.monotone (Nat.succ_le_succ_iff.mp hij)
  covers := by
    intro v
    obtain ⟨k, hk⟩ := E.covers v
    exact ⟨k + 1, Finset.mem_union_right _ hk⟩

@[simp] lemma intersectionExhaustion_region_zero (D E : VertexExhaustion V) (m n : ℕ) :
    (intersectionExhaustion D E m n).region 0 = D.region m ∩ E.region n := rfl

/-- Retain an intersection vertex in the original inner box. -/
noncomputable def retainVertex (D E : VertexExhaustion V) (m n : ℕ)
    (x : ((intersectionExhaustion D E m n).box (G := G) 0).Vertex) :
    (D.box (G := G) m).Vertex :=
  ⟨x.1, (Finset.mem_inter.mp (show x.1 ∈ D.region m ∩ E.region n from x.2)).1⟩

lemma retainVertex_injective (D E : VertexExhaustion V) (m n : ℕ) :
    Function.Injective (retainVertex (G := G) D E m n) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : (D.box (G := G) m).Vertex => z.1) hxy

/-- The intersection has exactly the inner box's edges. -/
lemma intersection_edges (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n)) :
    (D.box (G := G) m).edges = ((intersectionExhaustion D E m n).box (G := G) 0).edges := by
  ext e
  constructor
  · intro he
    rw [(intersectionExhaustion D E m n).mem_box_edges_iff]
    intro x hx
    have hxD : x ∈ D.region m := (D.mem_box_edges_iff m e).mp he x hx
    have hxE : x ∈ E.region n := (E.mem_box_edges_iff n e).mp (N.edge_sub e he) x hx
    exact Finset.mem_inter.mpr ⟨hxD, hxE⟩
  · intro he
    rw [D.mem_box_edges_iff]
    intro x hx
    have hxR := ((intersectionExhaustion D E m n).mem_box_edges_iff 0 e).mp he x hx
    exact (Finset.mem_inter.mp hxR).1

/-- The identity on global labels, viewed as an edge equivalence from the
intersection box to the original inner box. -/
noncomputable def intersectionEdgeEquiv (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n)) :
    ((intersectionExhaustion D E m n).box (G := G) 0).edges ≃ (D.box (G := G) m).edges where
  toFun e := ⟨e.1,
    (Finset.ext_iff.mp (intersection_edges D E m n N) e.1).mpr e.2⟩
  invFun e := ⟨e.1,
    (Finset.ext_iff.mp (intersection_edges D E m n N) e.1).mp e.2⟩
  left_inv e := Subtype.ext rfl
  right_inv e := Subtype.ext rfl

lemma intersection_source (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (e : ((intersectionExhaustion D E m n).box (G := G) 0).edges) :
    (D.box (G := G) m).source (intersectionEdgeEquiv D E m n N e) =
      retainVertex D E m n (((intersectionExhaustion D E m n).box (G := G) 0).source e) := by
  apply Subtype.ext
  rfl

lemma intersection_target (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (e : ((intersectionExhaustion D E m n).box (G := G) 0).edges) :
    (D.box (G := G) m).target (intersectionEdgeEquiv D E m n N e) =
      retainVertex D E m n (((intersectionExhaustion D E m n).box (G := G) 0).target e) := by
  apply Subtype.ext
  rfl

/-- Exact inner-cylinder identity after deletion of the vertices outside the
intersection, with the boundary partition pulled back. -/
lemma intersection_cylinder_real_eq (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (β : (D.box (G := G) m).BoundaryPartition)
    {q : NNReal} (hq : 0 < q) {p : NNReal} (hp : p ≤ 1)
    (K : Finset G.edgeSet) (S : Set (K → Bool))
    (hKD : K ⊆ (D.box (G := G) m).edges)
    (hKF : K ⊆ ((intersectionExhaustion D E m n).box (G := G) 0).edges) :
    (((D.box (G := G) m).finiteVolumeLaw hq hp β : Measure (Configuration G.edgeSet)).real
        (cylinder K S)) =
      (((intersectionExhaustion D E m n).box (G := G) 0).finiteVolumeLaw hq hp
        (Setoid.comap (retainVertex (G := G) D E m n) β) : Measure (Configuration G.edgeSet)).real
        (cylinder K S) := by
  let BD := D.box (G := G) m
  let F := intersectionExhaustion D E m n
  let eE : ((intersectionExhaustion D E m n).box (G := G) 0).edges ≃
      (D.box (G := G) m).edges := intersectionEdgeEquiv D E m n N
  have hmap := map_fkPMF_pullConfig
    (G := ((intersectionExhaustion D E m n).box (G := G) 0).graph)
    (H := (D.box (G := G) m).graph)
    (retainVertex (G := G) D E m n) (retainVertex_injective D E m n) eE
    (intersection_source D E m n N) (intersection_target D E m n N) β hq hp
  have hcyl : (pullConfig (G := (F.box (G := G) 0).graph) (H := BD.graph) eE) ⁻¹'
      ((F.box (G := G) 0).boxCylinder K S hKF) =
        (BD.boxCylinder K S hKD) := by
    ext ω
    change (fun i : K => ((pullConfig (G := (F.box (G := G) 0).graph) (H := BD.graph) eE) ω) ⟨i.1, hKF i.2⟩) ∈ S ↔
      (fun i : K => ω ⟨i.1, hKD i.2⟩) ∈ S
    have hfun : (fun i : K => ((pullConfig (G := (F.box (G := G) 0).graph) (H := BD.graph) eE) ω) ⟨i.1, hKF i.2⟩) =
        (fun i : K => ω ⟨i.1, hKD i.2⟩) := by
      funext i
      rfl
    rw [hfun]
  have hreal := FiniteBox.pmf_toMeasure_real_preimage_of_map (pullConfig eE)
    (BD.graph.fkPMF hq hp β)
    ((F.box (G := G) 0).graph.fkPMF hq hp
      (Setoid.comap (retainVertex (G := G) D E m n) β)) hmap
    ((F.box (G := G) 0).boxCylinder K S hKF)
  rw [hcyl] at hreal
  rw [BD.finiteVolumeLaw_real_boxCylinder hq hp β K S hKD,
    (F.box (G := G) 0).finiteVolumeLaw_real_boxCylinder hq hp
      (Setoid.comap (retainVertex (G := G) D E m n) β) K S hKF]
  exact hreal

/-- Star containment is preserved by retention in the original inner box. -/
lemma retain_starContained (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (c : ((intersectionExhaustion D E m n).box (G := G) 0).Vertex)
    (hc : ((intersectionExhaustion D E m n).data (G := G)).StarContained 0 c) :
    (D.data (G := G)).StarContained m (retainVertex D E m n c) := by
  intro e he
  have heF := hc e he
  exact (Finset.ext_iff.mp (intersection_edges D E m n N) e).mpr heF

/-- The pulled-back inner boundary partition remains a source boundary class. -/
lemma intersection_hasSourceBoundaryClass (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    (β : (D.box (G := G) m).BoundaryPartition)
    (hβ : Prop42Source.HasSourceBoundaryClass (D.data (G := G)) β) :
    Prop42Source.HasSourceBoundaryClass
      ((intersectionExhaustion D E m n).data (G := G))
      (Setoid.comap (retainVertex (G := G) D E m n) β) := by
  intro c hc w hcw
  apply retainVertex_injective D E m n
  exact hβ (retainVertex D E m n c) (retain_starContained D E m n N c hc)
    (retainVertex D E m n w) hcw

/-- No inner-region edge can join a retained vertex to an omitted vertex. -/
lemma intersection_isRegionBoundary (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    {w : V} (hw : IsRegionBoundary G
      ((intersectionExhaustion D E m n).region 0) w) :
    IsRegionBoundary G (D.region m) w := by
  rcases hw with ⟨hwR, x, hxR, hwx⟩
  have hwD : w ∈ D.region m := (Finset.mem_inter.mp hwR).1
  refine ⟨hwD, x, ?_, hwx⟩
  intro hxD
  apply hxR
  apply Finset.mem_inter.mpr
  refine ⟨hxD, ?_⟩
  let e : G.edgeSet := ⟨s(w, x), hwx⟩
  have heD : e ∈ (D.box (G := G) m).edges := by
    rw [D.mem_box_edges_iff]
    intro y hy
    change y ∈ s(w, x) at hy
    rw [Sym2.mem_iff] at hy
    rcases hy with rfl | rfl
    · exact hwD
    · exact hxD
  have heE := N.edge_sub e heD
  apply (E.mem_box_edges_iff n e).mp heE x
  change x ∈ s(w, x)
  exact Sym2.mem_mk_right _ _

lemma intersection_boundaryConnection_subset (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n)) (roots : Finset V) :
    boundaryConnection G roots ((intersectionExhaustion D E m n).region 0) ⊆
      boundaryConnection G roots (D.region m) := by
  intro ω hω
  rcases hω with ⟨a, ha, w, hw, haw⟩
  exact ⟨a, ha, w, intersection_isRegionBoundary D E m n N hw, haw⟩

/-- At zero rate every source finite-volume cylinder is the same all-closed
point-mass computation. -/
lemma finiteVolumeLaw_real_cylinder_zero (B C : FiniteBox G.edgeSet)
    {q : NNReal} (hq : 0 < q)
    (α : B.BoundaryPartition) (β : C.BoundaryPartition)
    (K : Finset G.edgeSet) (S : Set (K → Bool))
    (hB : K ⊆ B.edges) (hC : K ⊆ C.edges) :
    ((B.finiteVolumeLaw hq (p := 0) zero_le α : Measure (Configuration G.edgeSet)).real
      (cylinder K S)) =
    ((C.finiteVolumeLaw hq (p := 0) zero_le β : Measure (Configuration G.edgeSet)).real
      (cylinder K S)) := by
  rw [B.finiteVolumeLaw_real_boxCylinder hq zero_le α K S hB,
    C.finiteVolumeLaw_real_boxCylinder hq zero_le β K S hC,
    B.graph.fkPMF_zero hq α, C.graph.fkPMF_zero hq β]
  rw [measureReal_def, measureReal_def,
    PMF.toMeasure_pure_apply B.graph.allClosed _ MeasurableSet.of_discrete,
    PMF.toMeasure_pure_apply C.graph.allClosed _ MeasurableSet.of_discrete]
  rfl

/-- At unit rate the analogous all-open point-mass computation is independent
of the box and source boundary class. -/
lemma finiteVolumeLaw_real_cylinder_one (B C : FiniteBox G.edgeSet)
    {q : NNReal} (hq : 0 < q)
    (α : B.BoundaryPartition) (β : C.BoundaryPartition)
    (K : Finset G.edgeSet) (S : Set (K → Bool))
    (hB : K ⊆ B.edges) (hC : K ⊆ C.edges) :
    ((B.finiteVolumeLaw hq (p := 1) le_rfl α : Measure (Configuration G.edgeSet)).real
      (cylinder K S)) =
    ((C.finiteVolumeLaw hq (p := 1) le_rfl β : Measure (Configuration G.edgeSet)).real
      (cylinder K S)) := by
  rw [B.finiteVolumeLaw_real_boxCylinder hq le_rfl α K S hB,
    C.finiteVolumeLaw_real_boxCylinder hq le_rfl β K S hC,
    B.graph.fkPMF_one hq α, C.graph.fkPMF_one hq β]
  rw [measureReal_def, measureReal_def,
    PMF.toMeasure_pure_apply B.graph.allOpen _ MeasurableSet.of_discrete,
    PMF.toMeasure_pure_apply C.graph.allOpen _ MeasurableSet.of_discrete]
  rfl

/-- The unique observation on an empty base. -/
def emptyAssignment (E : Type*) : ((∅ : Finset E) → Bool) :=
  fun i => (List.not_mem_nil i.2).elim

/-- An empty-base cylinder is independent of the configuration. -/
lemma cylinder_empty_const {E : Type*} (S : Set ((∅ : Finset E) → Bool)) :
    cylinder (∅ : Finset E) S = {_ω : Configuration E | emptyAssignment E ∈ S} := by
  ext ω
  change (∅ : Finset E).restrict ω ∈ S ↔ _
  have hr : (∅ : Finset E).restrict ω = emptyAssignment E := Subsingleton.elim _ _
  rw [hr]
  rfl

/-- The arbitrary-`NestedBox` global estimate at interior edge rates. -/
lemma arbitraryNested_abs_sub_le_boundary_interior (D E : VertexExhaustion V) (m n : ℕ)
    (α : (E.box (G := G) n).BoundaryPartition) (β : (D.box (G := G) m).BoundaryPartition)
    (hα : Prop42Source.HasSourceBoundaryClass (E.data (G := G)) α)
    (hβ : Prop42Source.HasSourceBoundaryClass (D.data (G := G)) β)
    (N : NestedBox (D.box (G := G) m) (E.box (G := G) n))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (K : Finset G.edgeSet) (S : Set (K → Bool))
    (hKD : K ⊆ (D.box (G := G) m).edges)
    (hKF : K ⊆ ((intersectionExhaustion D E m n).box (G := G) 0).edges) :
    |(((E.box (G := G) n).finiteVolumeLaw hq hp₁.le α) :
        Measure (Configuration G.edgeSet)).real (cylinder K S) -
      (((D.box (G := G) m).finiteVolumeLaw hq hp₁.le β) :
        Measure (Configuration G.edgeSet)).real (cylinder K S)| ≤
    (globalBernoulli G.edgeSet (upperRateNN_le_one hq hp₁.le) :
      Measure (Configuration G.edgeSet)).real
      (boundaryConnection G (edgeRoots G K) (D.region m)) := by
  let F := intersectionExhaustion D E m n
  have hDE := intersection_cylinder_real_eq D E m n N β hq hp₁.le K S hKD hKF
  have hsub : boundaryConnection G (edgeRoots G K) (F.region 0) ⊆
      boundaryConnection G (edgeRoots G K) (D.region m) :=
    intersection_boundaryConnection_subset D E m n N (edgeRoots G K)
  have herror := measureReal_mono (μ := (globalBernoulli G.edgeSet
    (upperRateNN_le_one hq hp₁.le) : Measure (Configuration G.edgeSet))) hsub
    (measure_ne_top _ _)
  by_cases hK : K = ∅
  · subst K
    rw [cylinder_empty_const]
    by_cases hS : emptyAssignment G.edgeSet ∈ S <;> simp [hS]
  · have hKFne : (((F.box (G := G) 0)).edges).Nonempty := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hK
      exact ⟨i, hKF hi⟩
    have hKFne' : Nonempty ((F.box (G := G) 0).edges) := by
      obtain ⟨i, hi⟩ := hKFne
      exact ⟨⟨i, hi⟩⟩
    let e₀ : ((F.box (G := G) 0).indexedGraph (edgeIndex _)).Edge ⊕
        (outsideGraph (E.box (G := G) n) (F.box (G := G) 0)).Edge :=
      Sum.inl ⟨0, Fintype.card_pos_iff.mpr hKFne'⟩
    have hn : F.region 0 ⊆ E.region n := by
      intro x hx
      exact (Finset.mem_inter.mp hx).2
    have hγ : Prop42Source.HasSourceBoundaryClass (F.data (G := G))
        (Setoid.comap (retainVertex (G := G) D E m n) β) :=
      intersection_hasSourceBoundaryClass D E m n N β hβ
    have hcan := canonicalSource_abs_sub_le_boundary F E 0 n hn α
      (Setoid.comap (retainVertex (G := G) D E m n) β) hα hγ
      (outsideGraph (E.box (G := G) n) (F.box (G := G) 0)).freeBoundary
      hq hp₀ hp₁ e₀ K S hKF
    rw [hDE]
    exact hcan.trans herror

/-- **Literal `SourceUniqueness.NestedEquationNine`, with arbitrary
`NestedBox` witnesses, endpoint rates included, actual observation roots, and
the global upper Bernoulli law.** -/
theorem nestedEquationNine_upperBernoulli [Countable V]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    NestedEquationNine (G := G) hq hp
      (globalBernoulli G.edgeSet (upperRateNN_le_one hq hp)) (edgeRoots G) := by
  intro D E α β hα hβ K S m n hKD hN
  rcases hN with ⟨N⟩
  have hKE : K ⊆ (E.box (G := G) n).edges := hKD.trans N.edge_sub
  have hKF : K ⊆ ((intersectionExhaustion D E m n).box (G := G) 0).edges := by
    intro e he
    exact (Finset.ext_iff.mp (intersection_edges D E m n N) e).mp (hKD he)
  by_cases hp0 : p = 0
  · subst p
    have hm := finiteVolumeLaw_real_cylinder_zero (E.box (G := G) n)
      (D.box (G := G) m) hq (α n) (β m) K S hKE hKD
    rw [hm]
    simp
  · have hp₀ : 0 < p := lt_of_le_of_ne bot_le (Ne.symm hp0)
    by_cases hp1 : p = 1
    · subst p
      have hm := finiteVolumeLaw_real_cylinder_one (E.box (G := G) n)
        (D.box (G := G) m) hq (α n) (β m) K S hKE hKD
      rw [hm]
      simp
    · have hp₁ : p < 1 := lt_of_le_of_ne hp hp1
      exact arbitraryNested_abs_sub_le_boundary_interior D E m n (α n) (β m)
        (hα n) (hβ m) N hq hp₀ hp₁ K S hKD hKF

end FK.SourceUniqueness

#print axioms FK.SourceUniqueness.intersection_cylinder_real_eq
#print axioms FK.SourceUniqueness.arbitraryNested_abs_sub_le_boundary_interior
#print axioms FK.SourceUniqueness.nestedEquationNine_upperBernoulli
