import FK.NestedCommonUpperGood
import FK.NestedMetricRegionSplit
import FK.OrdinaryNestedGluing
import FK.NestedRadialCounterexample

/-!
# Metric nested boxes: region structure, the shell obstruction, and the
two-sided presentation of the smaller box
-/

open Set
open scoped Classical

namespace FK.MetricRegionGood

attribute [local instance] Classical.propDecidable

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial
open FK.Exploration.StoppedInterior
open FK.Exploration.FKCoupling
open FK.Exploration.TwoSidedInterior
open FK.FinitePlane.FreeInterior

variable {V : Type} {G : SimpleGraph V} [G.LocallyFinite]

/-! ## 1. Region structure of nested metric boxes -/

lemma mem_metricBox_edges_iff {o : V} {hG : G.Connected} {n : ℕ} {e : G.edgeSet} :
    e ∈ (metricBox hG o n).edges ↔ ∃ x : V, x ∈ e.1 ∧ G.dist o x < n := by
  show e ∈ metricEdges hG o n ↔ _
  rw [mem_metricEdges]
  rfl

lemma le_dist_of_not_mem_metricBox {o : V} {hG : G.Connected} {r : ℕ} {e : G.edgeSet}
    (he : e ∉ (metricBox hG o r).edges) {x : V} (hx : x ∈ e.1) : r ≤ G.dist o x := by
  by_contra h
  exact he ((mem_metricBox_edges_iff (hG := hG)).2 ⟨x, hx, Nat.lt_of_not_le h⟩)

lemma source_mem {o : V} {hG : G.Connected} {n : ℕ} (e : (metricBox hG o n).edges) :
    ((metricBox hG o n).source e).1 ∈ (e.1 : G.edgeSet).1 :=
  Sym2.out_fst_mem (e.1 : G.edgeSet).1

lemma target_mem {o : V} {hG : G.Connected} {n : ℕ} (e : (metricBox hG o n).edges) :
    ((metricBox hG o n).target e).1 ∈ (e.1 : G.edgeSet).1 :=
  Sym2.out_snd_mem (e.1 : G.edgeSet).1

/-- Every edge of the larger box that is not an edge of the smaller box misses the
open ball of radius `R ≤ r`. -/
theorem newEdge_avoids_region {o : V} {hG : G.Connected} {R r N : ℕ} (hRr : R ≤ r)
    {e : G.edgeSet} (hN : e ∈ (metricBox hG o N).edges)
    (hD : e ∉ (metricBox hG o r).edges) :
    ¬ G.dist o ((metricBox hG o N).source ⟨e, hN⟩).1 < R ∧
      ¬ G.dist o ((metricBox hG o N).target ⟨e, hN⟩).1 < R := by
  have hs : ((metricBox hG o N).source ⟨e, hN⟩).1 ∈ e.1 := source_mem ⟨e, hN⟩
  have ht : ((metricBox hG o N).target ⟨e, hN⟩).1 ∈ e.1 := target_mem ⟨e, hN⟩
  exact ⟨fun h => absurd (h.trans_le hRr) (not_lt.2 (le_dist_of_not_mem_metricBox hD hs)),
    fun h => absurd (h.trans_le hRr) (not_lt.2 (le_dist_of_not_mem_metricBox hD ht))⟩

/-! ## 2. The vertex complement of the smaller box -/

variable (hG : G.Connected) (o : V) (R r N : ℕ) (hRr : R ≤ r) (hrN : r ≤ N)

/-- The smaller metric box. -/
noncomputable abbrev small : FiniteBox G.edgeSet := metricBox hG o r
/-- The larger metric box. -/
noncomputable abbrev large : FiniteBox G.edgeSet := metricBox hG o N

/-- Inclusion of the smaller box into the larger one. -/
noncomputable def inc : (small hG o r).Vertex → (large hG o N).Vertex :=
  NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion hG o hrN

/-- The global vertex underlying a smaller-box vertex. -/
def smallVal (z : (small hG o r).Vertex) : V :=
  (show ↥(innerBall hG o (r+1)) from z).1

/-- The global vertex underlying a larger-box vertex. -/
def largeVal (z : (large hG o N).Vertex) : V :=
  (show ↥(innerBall hG o (N+1)) from z).1

@[simp] lemma inc_largeVal (x : (small hG o r).Vertex) :
    largeVal hG o N (inc hG o r N hrN x) = smallVal hG o r x := rfl

lemma inc_injective : Function.Injective (inc hG o r N hrN) := by
  intro x y h
  have h3 : (((show ↥(innerBall hG o (r+1)) from x)) : V) =
      (((show ↥(innerBall hG o (r+1)) from y)) : V) := by
    have h4 := congrArg (fun z : (large hG o N).Vertex =>
      (show ↥(innerBall hG o (N+1)) from z).1) h
    exact h4
  exact Subtype.ext h3

/-- Larger-box vertices that are images of smaller-box vertices. -/
abbrev InSmallV (x : (large hG o N).Vertex) : Prop := x ∈ Set.range (inc hG o r N hrN)

/-- The fresh vertex type of the added block. -/
noncomputable abbrev New := {x : (large hG o N).Vertex // ¬ InSmallV hG o r N hrN x}

/-- The vertex bijection `small ⊕ fresh ≃ large`. -/
noncomputable def vSmallSumNew :
    (small hG o r).Vertex ⊕ New hG o r N hrN ≃ (large hG o N).Vertex :=
  (Equiv.sumCongr (Equiv.ofInjective (inc hG o r N hrN) (inc_injective hG o r N hrN))
    (Equiv.refl _)).trans (Equiv.sumCompl (InSmallV hG o r N hrN))

@[simp] lemma vSmallSumNew_inl (x : (small hG o r).Vertex) :
    vSmallSumNew hG o r N hrN (Sum.inl x) = inc hG o r N hrN x := by
  show (Equiv.sumCompl (InSmallV hG o r N hrN))
    (Sum.inl ((Equiv.ofInjective (inc hG o r N hrN) (inc_injective hG o r N hrN)) x)) = _
  rw [Equiv.sumCompl_apply_inl, Equiv.ofInjective_apply]

@[simp] lemma vSmallSumNew_inr (y : New hG o r N hrN) :
    vSmallSumNew hG o r N hrN (Sum.inr y) = y.1 := by
  show (Equiv.sumCompl (InSmallV hG o r N hrN)) (Sum.inr ((Equiv.refl (New hG o r N hrN)) y)) = _
  rw [Equiv.sumCompl_apply_inr]
  rfl


/-!
# The shell obstruction for metric nested boxes
-/

open Set
open scoped Classical



attribute [local instance] Classical.propDecidable

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial
open FK.MetricRegionGood


/-- A larger-box vertex at distance exactly `r` is the image of a smaller-box
vertex under the canonical inclusion. -/
lemma mem_range_inc_of_dist_eq {o : V} {hG : G.Connected} {r N : ℕ} {hrN : r ≤ N}
    {y : V} (hy : G.dist o y = r) :
    (⟨y, (mem_innerBall hG).2 (by omega)⟩ : (metricBox hG o N).Vertex) ∈
      Set.range (NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion (Gph := G) hG o hrN) := by
  refine ⟨⟨y, (mem_innerBall hG).2 (by omega)⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Endpoints of a labelled edge are its two canonical representatives. -/
lemma eq_out_of_mem {V : Type} {e : Sym2 V} {x : V} (hx : x ∈ e) :
    x = e.out.1 ∨ x = e.out.2 := by
  have h := e.out_eq
  rw [← h] at hx
  rw [Sym2.mem_iff] at hx
  exact hx

/-- **Shell obstruction.**  A complementary edge of a nested metric pair with an
endpoint at distance exactly `r` has one endpoint among the smaller box's
vertices.  Hence the added block cannot be placed on the vertex complement. -/
theorem endpoint_inSmallV_of_dist_eq {o : V} {hG : G.Connected} {r N : ℕ} (hrN : r ≤ N)
    {e : G.edgeSet} (hN : e ∈ (metricBox hG o N).edges) {x : V} (hx : x ∈ e.1)
    (hxr : G.dist o x = r) :
    (∃ v : (metricBox hG o r).Vertex,
        (NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion (Gph := G) hG o hrN v)
          = (metricBox hG o N).source ⟨e, hN⟩) ∨
      (∃ v : (metricBox hG o r).Vertex,
        (NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion (Gph := G) hG o hrN v)
          = (metricBox hG o N).target ⟨e, hN⟩) := by
  rcases eq_out_of_mem hx with h | h
  · left
    refine ⟨⟨x, (mem_innerBall hG).2 (by omega)⟩, ?_⟩
    apply Subtype.ext
    show x = ((metricBox hG o N).source ⟨e, hN⟩).1
    rw [show ((metricBox hG o N).source ⟨e, hN⟩).1 = e.1.out.1 from rfl, ← h]
  · right
    refine ⟨⟨x, (mem_innerBall hG).2 (by omega)⟩, ?_⟩
    apply Subtype.ext
    show x = ((metricBox hG o N).target ⟨e, hN⟩).1
    rw [show ((metricBox hG o N).target ⟨e, hN⟩).1 = e.1.out.2 from rfl, ← h]


/-! ## 3. Concrete shell obstruction on the semi-infinite line -/

namespace LineInstance

open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample

/-- The edge `1-2` of the semi-infinite line is a radius-2 box edge. -/
lemma lineEdge_one_mem : lineEdge 1 ∈ (metricBox lineGraph_connected 0 2).edges := by
  rw [mem_metricBox_edges_iff]
  exact ⟨1, by rw [lineEdge_apply]; exact Sym2.mem_mk_left 1 2,
    by rw [lineGraph_dist_zero]; norm_num⟩

/-- The edge `1-2` is not a radius-1 box edge. -/
lemma lineEdge_one_not_mem : lineEdge 1 ∉ (metricBox lineGraph_connected 0 1).edges := by
  rw [mem_metricBox_edges_iff]
  rintro ⟨x, hx, hdist⟩
  rw [lineEdge_apply] at hx
  rw [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · rw [lineGraph_dist_zero] at hdist; omega
  · rw [lineGraph_dist_zero] at hdist; omega

/-- **The shell obstruction is non-vacuous**: in the semi-infinite line at
scales `r = 1 < N = 2`, the complementary edge `1-2` has an endpoint that is a
vertex of the smaller box.  The added block therefore cannot be placed on the
vertex complement of the smaller box. -/
theorem lineGraph_shell_obstruction :
    (∃ v : (metricBox lineGraph_connected 0 1).Vertex,
        NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion
            (Gph := lineGraph) lineGraph_connected 0 (by norm_num : 1 ≤ 2) v
          = (metricBox lineGraph_connected 0 2).source ⟨lineEdge 1, lineEdge_one_mem⟩) ∨
      (∃ v : (metricBox lineGraph_connected 0 1).Vertex,
        NestedMetricGeometry.OrdinaryGluing.metricVertexInclusion
            (Gph := lineGraph) lineGraph_connected 0 (by norm_num : 1 ≤ 2) v
          = (metricBox lineGraph_connected 0 2).target ⟨lineEdge 1, lineEdge_one_mem⟩) := by
  apply endpoint_inSmallV_of_dist_eq (hG := lineGraph_connected) (o := 0) (r := 1) (N := 2)
    (by norm_num) lineEdge_one_mem (x := 1)
  · rw [lineEdge_apply]; exact Sym2.mem_mk_left 1 2
  · rw [lineGraph_dist_zero]

end LineInstance


/-! ## 4. The smaller metric box as a two-sided ambient -/

/-- The number of region-internal edges of the radius-`r` box. -/
noncomputable abbrev mI : ℕ :=
  Fintype.card (InternalEdge (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r))

/-- The number of remaining edges of the radius-`r` box. -/
noncomputable abbrev kE : ℕ :=
  Fintype.card (ExternalEdge (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r))

/-- The exterior-first edge enumeration of the smaller box that is compatible
with `transportedAmbient`. -/
noncomputable def jD :
    Fin (kE hG o R r + mI hG o R r) ≃ (small hG o r).edges :=
  (exteriorFirst (m := mI hG o R r) (k := kE hG o R r)).trans
    ((d hG o R r).trans (edgeIndex (metricBox hG o r)))

/-- The two-sided ambient of the smaller box at the region split. -/
noncomputable abbrev amb : LabelledMultigraph :=
  transportedAmbient (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)

/-- Sources of the indexed smaller box expressed in the ambient edge order. -/
lemma small_source_eq (a : Fin (kE hG o R r + mI hG o R r)) :
    (vertexEquiv (inBall hG o R r)) (splitSource (si hG o R r) (so hG o R r)
        (exteriorFirst (m := mI hG o R r) (k := kE hG o R r) a))
      = (small hG o r).source (jD hG o R r a) := by
  simp only [jD, si, so, d, Equiv.trans_apply, vertexEquiv_splitSource]

/-- Targets of the indexed smaller box expressed in the ambient edge order. -/
lemma small_target_eq (a : Fin (kE hG o R r + mI hG o R r)) :
    (vertexEquiv (inBall hG o R r)) (splitTarget (ti hG o R r) (xo hG o R r)
        (exteriorFirst (m := mI hG o R r) (k := kE hG o R r) a))
      = (small hG o r).target (jD hG o R r a) := by
  simp only [jD, ti, xo, d, Equiv.trans_apply, vertexEquiv_splitTarget]



/-! ## 4b. Presentation of the smaller metric box as a two-sided ambient -/

/-- Structure extensionality for labelled multigraphs with fixed vertex and edge
types and subsingleton instance fields. -/
lemma graph_ext {V E : Type} [Fintype V] [Fintype E]
    (s t s' t' : E → V) (hs : s = s') (ht : t = t') :
    (@LabelledMultigraph.mk V E _ _ s t) = (@LabelledMultigraph.mk V E _ _ s' t') := by
  rw [LabelledMultigraph.mk.injEq]
  exact ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _), heq_of_eq (Subsingleton.elim _ _),
    heq_of_eq hs, heq_of_eq ht⟩

/-- **Two-sided presentation of the actual metric box.**  With the region-split
exterior-first enumeration, the radius-`r` box is the vertex transport of the
two-sided ambient along the region vertex equivalence. -/
theorem smallGraphEq :
    (transportedAmbient (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)).transport (vertexEquiv (inBall hG o R r)).symm
        (Equiv.refl (Fin (kE hG o R r + mI hG o R r)))
      = (metricBox hG o r).indexedGraph (jD hG o R r) := by
  have hs : (fun a => (vertexEquiv (inBall hG o R r)) ((transportedAmbient (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)).source (Equiv.refl _ a)))
      = (fun a => (metricBox hG o r).source (jD hG o R r a)) := by
    funext a; exact small_source_eq hG o R r a
  have ht : (fun a => (vertexEquiv (inBall hG o R r)) ((transportedAmbient (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)).target (Equiv.refl _ a)))
      = (fun a => (metricBox hG o r).target (jD hG o R r a)) := by
    funext a; exact small_target_eq hG o R r a
  show (@LabelledMultigraph.mk (metricBox hG o r).Vertex
      (Fin (kE hG o R r + mI hG o R r)) _ _
      (fun a => (vertexEquiv (inBall hG o R r)) ((transportedAmbient (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)).source a))
      (fun a => (vertexEquiv (inBall hG o R r)) ((transportedAmbient (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)).target a)))
    = (@LabelledMultigraph.mk (metricBox hG o r).Vertex
      (Fin (kE hG o R r + mI hG o R r)) _ _
      (fun a => (metricBox hG o r).source (jD hG o R r a))
      (fun a => (metricBox hG o r).target (jD hG o R r a)))
  exact graph_ext _ _ _ _ hs ht

/-! ## 5. The exact freshness condition for the added block -/

lemma dist_lt_of_inSmallV {x : (large hG o N).Vertex} (hx : InSmallV hG o r N hrN x) :
    G.dist o (largeVal hG o N x) < r + 1 := by
  obtain ⟨v, rfl⟩ := hx
  have h1 : (show ↥(innerBall hG o (r+1)) from v).1 ∈ innerBall hG o (r+1) :=
    (Finset.mem_coe).1 (show ↥(innerBall hG o (r+1)) from v).2
  have h2 : G.dist o (show ↥(innerBall hG o (r+1)) from v).1 < r + 1 := (mem_innerBall hG).1 h1
  simpa [smallVal] using h2

/-- **Freshness criterion.**  If every endpoint of every complementary edge has
distance at least `r + 1`, then added edges are supported on the vertex
complement, so the ordinary nested pair is a right extension of the smaller
box by a fresh graph on `New`.  This is the precise extra condition under which
the accepted two-sided common-upper `hgood` can be instantiated. -/
theorem newEdge_fresh_of_shell
    (hshell : ∀ (e : G.edgeSet), e ∈ (large hG o N).edges → e ∉ (small hG o r).edges →
      ∀ x : V, x ∈ e.1 → r < G.dist o x)
    {e : G.edgeSet} (hN : e ∈ (large hG o N).edges) (hD : e ∉ (small hG o r).edges) :
    ¬ InSmallV hG o r N hrN ((large hG o N).source ⟨e, hN⟩) ∧
      ¬ InSmallV hG o r N hrN ((large hG o N).target ⟨e, hN⟩) := by
  have hs : r < G.dist o ((large hG o N).source ⟨e, hN⟩).1 :=
    hshell e hN hD _ (source_mem ⟨e, hN⟩)
  have ht : r < G.dist o ((large hG o N).target ⟨e, hN⟩).1 :=
    hshell e hN hD _ (target_mem ⟨e, hN⟩)
  constructor
  · intro h
    have h2 : G.dist o ((large hG o N).source ⟨e, hN⟩).1 < r + 1 :=
      dist_lt_of_inSmallV hG o r N hrN h
    omega
  · intro h
    have h2 : G.dist o ((large hG o N).target ⟨e, hN⟩).1 < r + 1 :=
      dist_lt_of_inSmallV hG o r N hrN h
    omega

end FK.MetricRegionGood

/-! ## Axiom audit -/

#print axioms FK.MetricRegionGood.mem_metricBox_edges_iff
#print axioms FK.MetricRegionGood.le_dist_of_not_mem_metricBox
#print axioms FK.MetricRegionGood.source_mem
#print axioms FK.MetricRegionGood.target_mem
#print axioms FK.MetricRegionGood.newEdge_avoids_region
#print axioms FK.MetricRegionGood.inc_injective
#print axioms FK.MetricRegionGood.vSmallSumNew
#print axioms FK.MetricRegionGood.vSmallSumNew_inl
#print axioms FK.MetricRegionGood.vSmallSumNew_inr
#print axioms FK.MetricRegionGood.mem_range_inc_of_dist_eq
#print axioms FK.MetricRegionGood.eq_out_of_mem
#print axioms FK.MetricRegionGood.endpoint_inSmallV_of_dist_eq
#print axioms FK.MetricRegionGood.LineInstance.lineEdge_one_mem
#print axioms FK.MetricRegionGood.LineInstance.lineEdge_one_not_mem
#print axioms FK.MetricRegionGood.LineInstance.lineGraph_shell_obstruction
#print axioms FK.MetricRegionGood.jD
#print axioms FK.MetricRegionGood.small_source_eq
#print axioms FK.MetricRegionGood.small_target_eq
#print axioms FK.MetricRegionGood.graph_ext
#print axioms FK.MetricRegionGood.smallGraphEq
#print axioms FK.MetricRegionGood.dist_lt_of_inSmallV
#print axioms FK.MetricRegionGood.newEdge_fresh_of_shell
