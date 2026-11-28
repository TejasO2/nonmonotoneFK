import FK.SourceGlobalWindow

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
open FK.RandomClosedBoundary

universe uV

/-- Star-contained vertices incident to an actual small-box edge.  Every
abstract `NestedBox` fixes these vertices on their global labels. -/
def nestedStarEdgeCore {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]
    (D : VertexExhaustion V) (m : ℕ) : Set (D.box (G := Gph) m).Vertex :=
  {c | (D.data (G := Gph)).StarContained m c ∧
    ∃ e : (D.box (G := Gph) m).edges,
      (D.box (G := Gph) m).source e = c ∨ (D.box (G := Gph) m).target e = c}

lemma nested_vertex_eq_of_internal_endpoint {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    {c : (D.box (G := Gph) m).Vertex}
    (hc : ∃ e : (D.box (G := Gph) m).edges,
      (D.box (G := Gph) m).source e = c ∨ (D.box (G := Gph) m).target e = c) :
    (N.vert c).1 = c.1 := by
  obtain ⟨e, he | he⟩ := hc
  · rw [← he]
    exact congrArg (fun v : (E.box (G := Gph) n).Vertex => v.1) (N.src e).symm
  · rw [← he]
    exact congrArg (fun v : (E.box (G := Gph) n).Vertex => v.1) (N.tgt e).symm

lemma nested_vertex_eq_of_starEdgeCore {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    {c : (D.box (G := Gph) m).Vertex} (hc : c ∈ nestedStarEdgeCore D m) :
    (N.vert c).1 = c.1 :=
  nested_vertex_eq_of_internal_endpoint D E m n N hc.2

/-- Joint roots for the arbitrary-abstract-nesting core. -/
def nestedSourceRoots {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n)) :
    Set (E.box (G := Gph) n).Vertex :=
  {x | x ∉ Set.range N.vert} ∪ N.vert '' (nestedStarEdgeCore D m)ᶜ

/-- The star-edge geometry is defined for every abstract nested box. -/
noncomputable def arbitrarySourceNestedGeometry {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n)) :
    NestedSumGeometry (E.box (G := Gph) n).Vertex
      ((D.box (G := Gph) m).indexedGraph (edgeIndex _))
      (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)) := by
  let BS := E.box (G := Gph) n
  let BD := D.box (G := Gph) m
  have hds : ∀ a, N.vert (BD.source (edgeIndex _ a)) =
      BS.source ⟨(edgeIndex _ a).1, N.edge_sub (edgeIndex _ a).1 (edgeIndex _ a).2⟩ := by
    intro a
    exact (N.src _).symm
  have hdt : ∀ a, N.vert (BD.target (edgeIndex _ a)) =
      BS.target ⟨(edgeIndex _ a).1, N.edge_sub (edgeIndex _ a).1 (edgeIndex _ a).2⟩ := by
    intro a
    exact (N.tgt _).symm
  have houtS : ∀ e : (outsideGraph BS BD).Edge,
      BS.source ⟨e.1, e.2.1⟩ ∉ N.vert '' nestedStarEdgeCore D m := by
    rintro e ⟨c, hc, heq⟩
    have hcv := nested_vertex_eq_of_starEdgeCore D E m n N hc
    apply e.2.2
    apply hc.1 e.1
    change c.1 ∈ (e.1 : Gph.edgeSet).1
    rw [← hcv, heq]
    rw [← (E.data (G := Gph)).endpoint n ⟨e.1, e.2.1⟩]
    exact Sym2.mem_mk_left _ _
  have houtT : ∀ e : (outsideGraph BS BD).Edge,
      BS.target ⟨e.1, e.2.1⟩ ∉ N.vert '' nestedStarEdgeCore D m := by
    rintro e ⟨c, hc, heq⟩
    have hcv := nested_vertex_eq_of_starEdgeCore D E m n N hc
    apply e.2.2
    apply hc.1 e.1
    change c.1 ∈ (e.1 : Gph.edgeSet).1
    rw [← hcv, heq]
    rw [← (E.data (G := Gph)).endpoint n ⟨e.1, e.2.1⟩]
    exact Sym2.mem_mk_right _ _
  exact nestedBoxGeometry BS BD (edgeIndex _) (edgeIndex _) N.edge_sub N.vert N.vert_inj
    hds hdt (nestedStarEdgeCore D m) houtS houtT

lemma nested_large_hstar {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (k : Assignment (arbitrarySourceNestedGeometry D E m n N).graph.Edge)
    (v : (E.box (G := Gph) n).Vertex)
    (hv : v ∈ interior (G := (arbitrarySourceNestedGeometry D E m n N).graph)
      (nestedSourceRoots D E m n N) k) :
    (E.data (G := Gph)).StarContained n v := by
  intro e he
  by_cases hvr : v ∈ Set.range N.vert
  · obtain ⟨c, rfl⟩ := hvr
    have hc : c ∈ nestedStarEdgeCore D m := by
      by_contra hn
      apply hv
      apply subset_closedRegion
      exact Or.inr ⟨c, hn, rfl⟩
    have hcv := nested_vertex_eq_of_starEdgeCore D E m n N hc
    apply N.edge_sub
    apply hc.1 e
    change c.1 ∈ (e : Sym2 V)
    rwa [← hcv]
  · exact (hv (subset_closedRegion (Or.inl hvr))).elim

lemma nested_small_mem_core {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (k : Assignment (arbitrarySourceNestedGeometry D E m n N).graph.Edge)
    (c : (D.box (G := Gph) m).Vertex)
    (hc : (arbitrarySourceNestedGeometry D E m n N).vertex c ∈
      interior (G := (arbitrarySourceNestedGeometry D E m n N).graph)
        (nestedSourceRoots D E m n N) k) :
    c ∈ (arbitrarySourceNestedGeometry D E m n N).core := by
  by_contra hn
  apply hc
  apply subset_closedRegion
  exact Or.inr ⟨c, hn, rfl⟩

lemma nested_large_hwire {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (α : (E.box (G := Gph) n).BoundaryPartition)
    (hα : HasSourceBoundaryClass (E.data (G := Gph)) α)
    (k : Assignment (arbitrarySourceNestedGeometry D E m n N).graph.Edge)
    (v : (E.box (G := Gph) n).Vertex)
    (hv : v ∈ interior (G := (arbitrarySourceNestedGeometry D E m n N).graph)
      (nestedSourceRoots D E m n N) k) (w : (E.box (G := Gph) n).Vertex)
    (hvw : ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α).r v w) : v = w := by
  exact (hα v (nested_large_hstar D E m n N k v hv) w hvw).symm

lemma nested_small_hwire {V : Type uV} {Gph : SimpleGraph V} [Gph.LocallyFinite]
    (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (β : (D.box (G := Gph) m).BoundaryPartition)
    (hβ : HasSourceBoundaryClass (D.data (G := Gph)) β)
    (k : Assignment (arbitrarySourceNestedGeometry D E m n N).graph.Edge)
    (c : (D.box (G := Gph) m).Vertex)
    (hc : (arbitrarySourceNestedGeometry D E m n N).vertex c ∈
      interior (G := (arbitrarySourceNestedGeometry D E m n N).graph)
        (nestedSourceRoots D E m n N) k) (w : (D.box (G := Gph) m).Vertex)
    (hcw : ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β).r c w) : c = w := by
  have hcore := nested_small_mem_core D E m n N k c hc
  exact (hβ c hcore.1 w hcw).symm

/-- Literal finite arm estimate for every abstract nested box, including
nestings which do not induce inclusion of the underlying vertex regions. -/
theorem arbitraryNested_abs_sub_le_arm {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (α : (E.box (G := Gph) n).BoundaryPartition) (β : (D.box (G := Gph) m).BoundaryPartition)
    (hα : HasSourceBoundaryClass (E.data (G := Gph)) α)
    (hβ : HasSourceBoundaryClass (D.data (G := Gph)) β)
    (ξO : (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (e₀ : ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).Edge)
    (J : Finset ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge)
    (S : Set (J → Bool)) :
    let X := arbitrarySourceNestedGeometry D E m n N
    abs ((X.graph.fkPMF hq hp₁.le
        ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α)).toMeasure.real
        {ω | baseCylinder J S (fun d : ((D.box (G := Gph) m).indexedGraph
          (edgeIndex _)).Edge => ω (Sum.inl d))} -
      (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).fkPMF hq hp₁.le
        ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β)).toMeasure.real
        (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (upperArm X J (nestedSourceRoots D E m n N)) := by
  intro X
  exact X.windowCopyTriple_abs_sub_le_arm
    ((D.box (G := Gph) m).indexedBoundary (edgeIndex _) β) ξO
    ((E.box (G := Gph) n).indexedBoundary (edgeIndex _) α) hq hp₀ hp₁
    (nestedSourceRoots D E m n N) e₀
    (nested_small_mem_core D E m n N)
    (nested_large_hwire D E m n N α hα)
    (nested_small_hwire D E m n N β hβ) J S

/-- Every vertex incident to a small-box edge is globally fixed by an
abstract nesting, with both endpoint orientations allowed. -/
lemma exists_nested_vertex_of_mem_internal_edge {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (e : (D.box (G := Gph) m).edges) {v : V} (hv : v ∈ (e : Sym2 V)) :
    ∃ c : (D.box (G := Gph) m).Vertex, (N.vert c).1 = v ∧ c.1 = v := by
  have hend := (D.data (G := Gph)).endpoint m e
  rw [← hend] at hv
  rcases Sym2.mem_iff.mp hv with hs | ht
  · refine ⟨(D.box (G := Gph) m).source e, ?_, hs.symm⟩
    exact (nested_vertex_eq_of_internal_endpoint D E m n N
      ⟨e, Or.inl rfl⟩).trans hs.symm
  · refine ⟨(D.box (G := Gph) m).target e, ?_, ht.symm⟩
    exact (nested_vertex_eq_of_internal_endpoint D E m n N
      ⟨e, Or.inr rfl⟩).trans ht.symm

/-- A walk wholly supported in the small region tracks its endpoint through
an arbitrary `NestedBox`; no global region inclusion is needed. -/
lemma exists_nested_endpoint_of_walk {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    {a b : V} (x₀ : (D.box (G := Gph) m).Vertex)
    (p : Gph.Walk a b) (ha : a = (N.vert x₀).1) (hx₀ : x₀.1 = (N.vert x₀).1)
    (hp : ∀ v ∈ p.support, v ∈ D.region m) :
    ∃ c : (D.box (G := Gph) m).Vertex, (N.vert c).1 = b ∧ c.1 = b := by
  induction p generalizing x₀ with
  | nil => exact ⟨x₀, ha.symm, hx₀.trans ha.symm⟩
  | @cons a b c hab q ih =>
    have ha : a ∈ D.region m := hp a (by simp)
    have hb : b ∈ D.region m := hp b (by simp)
    let f : Gph.edgeSet := ⟨s(a, b), hab⟩
    have hf : f ∈ (D.box (G := Gph) m).edges := by
      apply (D.mem_box_edges_iff m f).mpr
      intro x hx
      change x ∈ s(a, b) at hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact ha
      · exact hb
    obtain ⟨d, hdN, hd⟩ := exists_nested_vertex_of_mem_internal_edge D E m n N
      (⟨f, hf⟩ : (D.box (G := Gph) m).edges) (v := b) (by
        change b ∈ s(a, b)
        exact Sym2.mem_mk_right _ _)
    have hdx : d.1 = (N.vert d).1 := hd.trans hdN.symm
    apply ih d hdN.symm hdx
    intro v hv
    apply hp v
    rw [SimpleGraph.Walk.support_cons, List.mem_cons]
    exact Or.inr hv

lemma notStar_isRegionBoundary {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D : VertexExhaustion V) (m : ℕ)
    (c : (D.box (G := Gph) m).Vertex)
    (hc : ¬ (D.data (G := Gph)).StarContained m c) :
    IsRegionBoundary Gph (D.region m) c.1 := by
  unfold InfiniteVolume.ConventionTransport.SimpleGraphBoxData.StarContained at hc
  push Not at hc
  obtain ⟨f, hcf, hfn⟩ := hc
  have hex : ∃ x, x ∈ (f.1 : Sym2 V) ∧ x ∉ D.region m := by
    by_contra hn'
    push Not at hn'
    apply hfn
    apply (D.mem_box_edges_iff m f).mpr
    intro x hx
    exact hn' x hx
  obtain ⟨x, hxf, hx⟩ := hex
  obtain ⟨a, b, hab, hfab⟩ := exists_adj_of_mem_edgeSet (G := Gph) (e := f)
  have hca : c.1 = a ∨ c.1 = b := by
    rw [← hfab] at hcf
    exact Sym2.mem_iff.mp hcf
  have hxa : x = a ∨ x = b := by
    rw [← hfab] at hxf
    exact Sym2.mem_iff.mp hxf
  refine ⟨c.2, x, hx, ?_⟩
  rcases hca with rfl | rfl <;> rcases hxa with rfl | rfl
  · exact (hx c.2).elim
  · exact hab
  · exact hab.symm
  · exact (hx c.2).elim

lemma notStarEdgeCore_cases {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D : VertexExhaustion V) (m : ℕ)
    (c : (D.box (G := Gph) m).Vertex) (hc : c ∈ (nestedStarEdgeCore D m)ᶜ) :
    (¬ (D.data (G := Gph)).StarContained m c) ∨
      ((∀ f : Gph.edgeSet, c.1 ∉ (f : Sym2 V)) ∧
        ¬ ∃ e : (D.box (G := Gph) m).edges,
          (D.box (G := Gph) m).source e = c ∨ (D.box (G := Gph) m).target e = c) := by
  by_cases hs : (D.data (G := Gph)).StarContained m c
  · right
    have hn : ¬ ∃ e : (D.box (G := Gph) m).edges,
        (D.box (G := Gph) m).source e = c ∨ (D.box (G := Gph) m).target e = c := by
      intro hi
      exact hc ⟨hs, hi⟩
    refine ⟨?_, hn⟩
    intro f hcf
    apply hn
    let e : (D.box (G := Gph) m).edges := ⟨f, hs f hcf⟩
    refine ⟨e, ?_⟩
    have hend := (D.data (G := Gph)).endpoint m e
    change c.1 ∈ (f : Sym2 V) at hcf
    rw [← hend] at hcf
    rcases Sym2.mem_iff.mp hcf with h | h
    · exact Or.inl (Subtype.ext h.symm)
    · exact Or.inr (Subtype.ext h.symm)
  · exact Or.inl hs

lemma eq_of_openConnected_of_no_incident {V : Type uV} {Gph : SimpleGraph V}
    {ω : Gph.edgeSet → Bool} {x c : V}
    (hc : ∀ f : Gph.edgeSet, c ∉ (f : Sym2 V))
    (h : CurvatureVariance.Infra.Percolation.OpenConnected Gph ω Set.univ x c) : x = c := by
  have hrev := ConventionGeometry.openConnected_symm h
  obtain ⟨p, hp⟩ := hrev
  cases p with
  | nil => rfl
  | cons hab q =>
    exact (hc ⟨s(c, _), hab⟩ (Sym2.mem_mk_left _ _)).elim

/-- Read an arbitrary source nesting in its large-box coordinates. -/
noncomputable def arbitrarySourceInterior {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (ω : ((D.box (G := Gph) m).indexedGraph (edgeIndex _)).Edge ⊕
      (outsideGraph (E.box (G := Gph) n) (D.box (G := Gph) m)).Edge → Bool) :
    (E.box (G := Gph) n).Interior :=
  splitToInterior (E.box (G := Gph) n) (D.box (G := Gph) m)
    (edgeIndex _) (edgeIndex _) N.edge_sub ω

/-- Actual global open-path map for an arbitrary abstract source nesting. -/
noncomputable def arbitrarySourceOpenPathMap {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (ρ : (arbitrarySourceNestedGeometry D E m n N).graph.Configuration)
    (ω : Gph.edgeSet → Bool)
    (hagree : ∀ e : (E.box (G := Gph) n).edges,
      ω e.1 = arbitrarySourceInterior D E m n N ρ e) :
    OpenPathGeometry.LabelledOpenPathMap
      (arbitrarySourceNestedGeometry D E m n N).graph Gph ρ ω where
  vertex v := (E.data (G := Gph)).vertex n v
  edge a := (((edgeIndex (E.box (G := Gph) n))
    (nestedSplitEdgeEquiv (E.box (G := Gph) n) (D.box (G := Gph) m)
      (edgeIndex _) (edgeIndex _) N.edge_sub a) :
    (E.box (G := Gph) n).edges) : Gph.edgeSet)
  endpoint a := by
    exact (E.data (G := Gph)).endpoint n
      ((edgeIndex (E.box (G := Gph) n))
        (nestedSplitEdgeEquiv (E.box (G := Gph) n) (D.box (G := Gph) m)
          (edgeIndex _) (edgeIndex _) N.edge_sub a))
  isOpen a ha := by
    rw [hagree ((edgeIndex (E.box (G := Gph) n))
      (nestedSplitEdgeEquiv (E.box (G := Gph) n) (D.box (G := Gph) m)
        (edgeIndex _) (edgeIndex _) N.edge_sub a))]
    exact (splitToInterior_apply_split (E.box (G := Gph) n) (D.box (G := Gph) m)
      (edgeIndex _) (edgeIndex _) N.edge_sub ρ a).trans ha

lemma arbitrary_source_mem_edgeRoots {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (K : Finset Gph.edgeSet) (hK : K ⊆ (D.box (G := Gph) m).edges)
    (j : sourceBase (D.box (G := Gph) m) (edgeIndex _) K hK) :
    (N.vert (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).source j.1)).1 ∈
      edgeRoots Gph K := by
  let BS := E.box (G := Gph) n
  let BD := D.box (G := Gph) m
  let jD := edgeIndex BD
  have hlabel : ((sourceBaseEquiv BD jD K hK j : K) : Gph.edgeSet) =
      ((jD j.1 : BD.edges) : Gph.edgeSet) := by
    have h := congrArg (fun a : (BD.indexedGraph jD).Edge =>
      ((jD a : BD.edges) : Gph.edgeSet)) (sourceBaseEquiv_embedding BD jD K hK j)
    change ((jD (jD.symm (⟨(sourceBaseEquiv BD jD K hK j).1,
      hK (sourceBaseEquiv BD jD K hK j).2⟩ : BD.edges)) : BD.edges) : Gph.edgeSet) = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  refine Finset.mem_biUnion.mpr ⟨((jD j.1 : BD.edges) : Gph.edgeSet), ?_, ?_⟩
  · rw [← hlabel]
    exact (sourceBaseEquiv BD jD K hK j).2
  · let big : BS.edges := ⟨(jD j.1).1, N.edge_sub (jD j.1).1 (jD j.1).2⟩
    have hs := congrArg (fun v : BS.Vertex => v.1) (N.src (jD j.1))
    change (N.vert (BD.source (jD j.1))).1 ∈ _
    rw [← hs, Sym2.mem_toFinset, ← (E.data (G := Gph)).endpoint n big]
    exact Sym2.mem_mk_left _ _

lemma arbitrary_target_mem_edgeRoots {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (K : Finset Gph.edgeSet) (hK : K ⊆ (D.box (G := Gph) m).edges)
    (j : sourceBase (D.box (G := Gph) m) (edgeIndex _) K hK) :
    (N.vert (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).target j.1)).1 ∈
      edgeRoots Gph K := by
  let BS := E.box (G := Gph) n
  let BD := D.box (G := Gph) m
  let jD := edgeIndex BD
  have hlabel : ((sourceBaseEquiv BD jD K hK j : K) : Gph.edgeSet) =
      ((jD j.1 : BD.edges) : Gph.edgeSet) := by
    have h := congrArg (fun a : (BD.indexedGraph jD).Edge =>
      ((jD a : BD.edges) : Gph.edgeSet)) (sourceBaseEquiv_embedding BD jD K hK j)
    change ((jD (jD.symm (⟨(sourceBaseEquiv BD jD K hK j).1,
      hK (sourceBaseEquiv BD jD K hK j).2⟩ : BD.edges)) : BD.edges) : Gph.edgeSet) = _ at h
    simpa only [Equiv.apply_symm_apply] using h
  refine Finset.mem_biUnion.mpr ⟨((jD j.1 : BD.edges) : Gph.edgeSet), ?_, ?_⟩
  · rw [← hlabel]
    exact (sourceBaseEquiv BD jD K hK j).2
  · let big : BS.edges := ⟨(jD j.1).1, N.edge_sub (jD j.1).1 (jD j.1).2⟩
    have ht := congrArg (fun v : BS.Vertex => v.1) (N.tgt (jD j.1))
    change (N.vert (BD.target (jD j.1))).1 ∈ _
    rw [← ht, Sym2.mem_toFinset, ← (E.data (G := Gph)).endpoint n big]
    exact Sym2.mem_mk_right _ _

/-- Arbitrary abstract-nesting arms factor through the true small region
boundary, including the globally isolated non-core case. -/
theorem arbitrary_upperArm_mem_boundaryConnection {V : Type uV} {Gph : SimpleGraph V}
    [Gph.LocallyFinite] (D E : VertexExhaustion V) (m n : ℕ)
    (N : NestedBox (D.box (G := Gph) m) (E.box (G := Gph) n))
    (K : Finset Gph.edgeSet) (hK : K ⊆ (D.box (G := Gph) m).edges)
    (ρ : (arbitrarySourceNestedGeometry D E m n N).graph.Configuration)
    (ω : Gph.edgeSet → Bool)
    (hagree : ∀ e : (E.box (G := Gph) n).edges,
      ω e.1 = arbitrarySourceInterior D E m n N ρ e)
    (hρ : upperArm (arbitrarySourceNestedGeometry D E m n N)
      (sourceBase (D.box (G := Gph) m) (edgeIndex _) K hK)
      (nestedSourceRoots D E m n N) ρ) :
    ω ∈ boundaryConnection Gph (edgeRoots Gph K) (D.region m) := by
  let X := arbitrarySourceNestedGeometry D E m n N
  let M := arbitrarySourceOpenPathMap D E m n N ρ ω hagree
  obtain ⟨j, b, hb, hpath⟩ := hρ
  have finish (x : (D.box (G := Gph) m).Vertex)
      (hx : (N.vert x).1 ∈ edgeRoots Gph K)
      (hxi : ∃ e : (D.box (G := Gph) m).edges,
        (D.box (G := Gph) m).source e = x ∨ (D.box (G := Gph) m).target e = x)
      (hxb : (X.graph.openGraph X.graph.freeBoundary ρ).Reachable (X.vertex x) b) :
      ω ∈ boundaryConnection Gph (edgeRoots Gph K) (D.region m) := by
    have hxN : (N.vert x).1 = x.1 := nested_vertex_eq_of_internal_endpoint D E m n N hxi
    have hx' : x.1 = (N.vert x).1 := hxN.symm
    have hconn : CurvatureVariance.Infra.Percolation.OpenConnected Gph ω Set.univ
        (N.vert x).1 (M.vertex b) := M.openConnected_of_reachable hxb
    change b ∈ {v | v ∉ Set.range N.vert} ∪ N.vert '' (nestedStarEdgeCore D m)ᶜ at hb
    obtain ⟨p, hp⟩ := hconn
    have hstart : (N.vert x).1 ∈ D.region m :=
      mem_region_of_mem_edgeRoots D m K hK hx
    rcases inside_or_boundary_of_isOpenIn hstart p hp with hstay | hout
    · obtain ⟨d, hdN, hd⟩ := exists_nested_endpoint_of_walk D E m n N x p rfl hx' hstay.2
      rcases hb with hb | ⟨c, hc, hcb⟩
      · exfalso
        apply hb
        refine ⟨d, ?_⟩
        apply Subtype.ext
        exact hdN
      · have hEq : d = c := by
          apply N.vert_inj
          apply Subtype.ext
          exact hdN.trans (congrArg (fun z : (E.box (G := Gph) n).Vertex => z.1) hcb.symm)
        have hdc : c.1 = M.vertex b := hEq ▸ hd
        have hconn0 : CurvatureVariance.Infra.Percolation.OpenConnected Gph ω Set.univ
            (N.vert x).1 (M.vertex b) := ⟨p, hp⟩
        have hconnC : CurvatureVariance.Infra.Percolation.OpenConnected Gph ω Set.univ
            (N.vert x).1 c.1 := hdc.symm ▸ hconn0
        rcases notStarEdgeCore_cases D m c hc with hn | ⟨hi, hn⟩
        · exact ⟨(N.vert x).1, hx, c.1, notStar_isRegionBoundary D m c hn, hconnC⟩
        · exfalso
          have heq : (N.vert x).1 = c.1 := eq_of_openConnected_of_no_incident hi hconnC
          have hxc : x = c := Subtype.ext (hxN.symm.trans heq)
          exact hn (hxc ▸ hxi)
    · obtain ⟨w, hw, hxw⟩ := hout
      exact ⟨(N.vert x).1, hx, w, hw, hxw⟩
  rcases hpath with h | h
  · exact finish (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).source j.1)
      (arbitrary_source_mem_edgeRoots D E m n N K hK j)
      ⟨((edgeIndex (D.box (G := Gph) m)) j.1), Or.inl rfl⟩ h
  · exact finish (((D.box (G := Gph) m).indexedGraph (edgeIndex _)).target j.1)
      (arbitrary_target_mem_edgeRoots D E m n N K hK j)
      ⟨((edgeIndex (D.box (G := Gph) m)) j.1), Or.inr rfl⟩ h

end FK.Adaptive.NestedSumGeometry
