import FK.CactusShift

/-!
# Source-faithful cycle devices on the triangle cactus
-/

namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation FK.AGImplant
open scoped ENNReal NNReal unitInterval Sym2 Topology
open FK.EssentialEnhancement

/-- Lift a double ray through the direct bonds of the cactus. -/
def liftDoubleRay (r : DoubleRay G) : DoubleRay graph where
  vertex n := Sum.inl (r.vertex n)
  vertex_injective := Sum.inl_injective.comp r.vertex_injective
  adj n := r.adj n

lemma liftDoubleRay_edge (r : DoubleRay G) (k : ℤ) :
    (liftDoubleRay r).edge k = baseEdge (r.edge k) := by
  apply Subtype.ext
  exact (baseEdge_val (r.edge k)).symm

/-- Every selected direct edge lies on an actual double ray of the cactus. -/
theorem onDoubleRay_baseEdge (e : G.edgeSet) : OnDoubleRay (baseEdge e) := by
  obtain ⟨r, k, hk⟩ := onDoubleRay_any_edge e
  refine ⟨liftDoubleRay r, k, ?_⟩
  rw [liftDoubleRay_edge, hk]

lemma out1_mem_base (e : G.edgeSet) :
    Sum.inl (e : Sym2 V).out.1 ∈ (baseEdge e : Sym2 Vertex) := by
  change Sum.inl (e : Sym2 V).out.1 ∈
    s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2)
  simp

lemma out2_mem_base (e : G.edgeSet) :
    Sum.inl (e : Sym2 V).out.2 ∈ (baseEdge e : Sym2 Vertex) := by
  change Sum.inl (e : Sym2 V).out.2 ∈
    s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2)
  simp

lemma out1_mem_leftSpoke (e : G.edgeSet) :
    Sum.inl (e : Sym2 V).out.1 ∈ (leftSpoke e : Sym2 Vertex) := by
  change Sum.inl (e : Sym2 V).out.1 ∈
    s(Sum.inl (e : Sym2 V).out.1, Sum.inr e)
  simp

lemma midpoint_mem_rightSpoke (e : G.edgeSet) :
    Sum.inr e ∈ (rightSpoke e : Sym2 Vertex) := by
  change Sum.inr e ∈ s(Sum.inr e, Sum.inl (e : Sym2 V).out.2)
  simp

lemma out2_mem_rightSpoke (e : G.edgeSet) :
    Sum.inl (e : Sym2 V).out.2 ∈ (rightSpoke e : Sym2 Vertex) := by
  change Sum.inl (e : Sym2 V).out.2 ∈
    s(Sum.inr e, Sum.inl (e : Sym2 V).out.2)
  simp

/-- Every bond is at line-graph distance at most one from the whole direct-bond family. -/
theorem direct_boundedDistance :
    FK.Theorem14.BoundedDistance graph.lineGraph.dist (Set.range baseEdge) := by
  refine ⟨1, fun f => ?_⟩
  obtain ⟨⟨e, k⟩, rfl⟩ := bond_surjective f
  fin_cases k
  · refine ⟨baseEdge e, ⟨e, rfl⟩, ?_⟩
    change graph.lineGraph.dist (baseEdge e) (baseEdge e) ≤ 1
    simp
  · refine ⟨baseEdge e, ⟨e, rfl⟩, ?_⟩
    change graph.lineGraph.dist (leftSpoke e) (baseEdge e) ≤ 1
    have hadj : graph.lineGraph.Adj (leftSpoke e) (baseEdge e) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr
        ⟨(baseEdge_ne_leftSpoke e e).symm,
          ⟨Sum.inl (e : Sym2 V).out.1, out1_mem_leftSpoke e, out1_mem_base e⟩⟩
    exact (graph.lineGraph.dist_le hadj.toWalk).trans (by simp [bond])
  · refine ⟨baseEdge e, ⟨e, rfl⟩, ?_⟩
    change graph.lineGraph.dist (rightSpoke e) (baseEdge e) ≤ 1
    have hadj : graph.lineGraph.Adj (rightSpoke e) (baseEdge e) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr
        ⟨(baseEdge_ne_rightSpoke e e).symm,
          ⟨Sum.inl (e : Sym2 V).out.2, out2_mem_rightSpoke e, out2_mem_base e⟩⟩
    exact (graph.lineGraph.dist_le hadj.toWalk).trans (by simp [bond])

/-- The three adjacency orientations used by the explicit triangle. -/
def baseAdj (e : G.edgeSet) :
    graph.Adj (Sum.inl (e : Sym2 V).out.1) (Sum.inl (e : Sym2 V).out.2) := by
  change graph.Adj (Sum.inl (e : Sym2 V).out.1) (Sum.inl (e : Sym2 V).out.2)
  exact (baseEdge e).property

def rightAdj (e : G.edgeSet) :
    graph.Adj (Sum.inl (e : Sym2 V).out.2) (Sum.inr e) := by
  change graph.Adj (Sum.inl (e : Sym2 V).out.2) (Sum.inr e)
  exact (rightSpoke e).property.symm

def leftAdj (e : G.edgeSet) :
    graph.Adj (Sum.inr e) (Sum.inl (e : Sym2 V).out.1) := by
  change graph.Adj (Sum.inr e) (Sum.inl (e : Sym2 V).out.1)
  exact (leftSpoke e).property.symm

/-- The triangle over `e`, traversed as direct edge, right spoke, left spoke. -/
noncomputable def triangle (e : G.edgeSet) :
    graph.Walk (Sum.inl (e : Sym2 V).out.1) (Sum.inl (e : Sym2 V).out.1) := by
  exact SimpleGraph.Walk.cons (baseAdj e) <|
    SimpleGraph.Walk.cons (rightAdj e) (SimpleGraph.Walk.cons (leftAdj e) SimpleGraph.Walk.nil)

lemma triangle_length (e : G.edgeSet) : (triangle e).length = 3 := by
  simp [triangle, SimpleGraph.Walk.length_cons]

lemma triangle_isCycle (e : G.edgeSet) : (triangle e).IsCycle := by
  rw [triangle, SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · apply SimpleGraph.Walk.IsPath.mk'
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
    exact (out_fst_ne_out_snd e).symm
  · intro hmem
    simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil] at hmem
    rcases hmem with hright | hleft | hfalse
    · apply baseEdge_ne_rightSpoke e e
      apply Subtype.ext
      exact hright.trans (Sym2.eq_swap :
        s(Sum.inl (e : Sym2 V).out.2, Sum.inr e) =
          s(Sum.inr e, Sum.inl (e : Sym2 V).out.2))
    · apply baseEdge_ne_leftSpoke e e
      apply Subtype.ext
      exact hleft.trans (Sym2.eq_swap :
        s(Sum.inr e, Sum.inl (e : Sym2 V).out.1) =
          s(Sum.inl (e : Sym2 V).out.1, Sum.inr e))
    · exact hfalse.elim

lemma baseEdge_mem_triangle_edges (e : G.edgeSet) :
    (baseEdge e : Sym2 Vertex) ∈ (triangle e).edges := by
  have hval : (baseEdge e : Sym2 Vertex) =
      s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) := rfl
  rw [hval]
  simp [triangle, SimpleGraph.Walk.edges_cons]

/-- Devices, indexed through the explicit bond equivalence. -/
noncomputable def triangleDevice (f : graph.edgeSet) : Finset graph.edgeSet :=
  FK.QuasiTransitive.walkDevice (triangle (bondEquiv.symm f).1)

lemma triangleDevice_baseEdge (e : G.edgeSet) :
    triangleDevice (baseEdge e) = FK.QuasiTransitive.walkDevice (triangle e) := by
  rw [triangleDevice, bondEquiv_symm_baseEdge]

/-- **Source separation.**  Each direct bond belongs to its own triangle, and
neither auxiliary spoke belongs to the direct enhanced family. -/
theorem direct_separatedDevices :
    FKLimit.IsSeparatedDeviceFamily (Set.range baseEdge) triangleDevice := by
  intro f hf
  obtain ⟨e, rfl⟩ := hf
  constructor
  · rw [triangleDevice_baseEdge, FK.QuasiTransitive.mem_walkDevice]
    exact baseEdge_mem_triangle_edges e
  · intro g hg hgne hgrange
    rw [triangleDevice_baseEdge, FK.QuasiTransitive.mem_walkDevice] at hg
    obtain ⟨e', rfl⟩ := hgrange
    simp only [triangle, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil] at hg
    rcases hg with hbase | hright | hleft | hfalse
    · exact hgne (Subtype.ext hbase)
    · apply baseEdge_ne_rightSpoke e' e
      apply Subtype.ext
      exact hright.trans (Sym2.eq_swap :
        s(Sum.inl (e : Sym2 V).out.2, Sum.inr e) =
          s(Sum.inr e, Sum.inl (e : Sym2 V).out.2))
    · apply baseEdge_ne_leftSpoke e' e
      apply Subtype.ext
      exact hleft.trans (Sym2.eq_swap :
        s(Sum.inr e, Sum.inl (e : Sym2 V).out.1) =
          s(Sum.inl (e : Sym2 V).out.1, Sum.inr e))
    · exact hfalse.elim

/-- Cycle and ray witnesses for every direct edge. -/
theorem direct_cycle_ray_geometry (e : G.edgeSet) :
    (triangle e).IsCycle ∧ (triangle e).length = 3 ∧ OnDoubleRay (baseEdge e) ∧
      baseEdge e ∈ FK.QuasiTransitive.walkDevice (triangle e) := by
  refine ⟨triangle_isCycle e, triangle_length e, onDoubleRay_baseEdge e, ?_⟩
  rw [FK.QuasiTransitive.mem_walkDevice]
  exact baseEdge_mem_triangle_edges e

end Ultra.TriangleCactus


namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation FK.AGImplant
open scoped ENNReal NNReal unitInterval Sym2 Topology
open FK.EssentialEnhancement

/-- Every device has at most the three edges of its defining triangle. -/
lemma card_triangleDevice_baseEdge (e : G.edgeSet) :
    (triangleDevice (baseEdge e)).card ≤ 3 := by
  rw [triangleDevice_baseEdge]
  exact (FK.QuasiTransitive.card_walkDevice_le_length (triangle e)).trans_eq (triangle_length e)

/-- A complete explicit model-faithful package.  The graph is the Husimi
triangle cactus over the five-regular junction tree; its criticality and
strict-window assertions use only
the independent Bernoulli laws on its actual bond subtype. -/
theorem triangle_cactus_model :
    graph.Connected ∧ (∀ v, Finite (graph.neighborSet v)) ∧
      FK.QuasiTransitive.IsQuasiTransitive graph ∧ Infinite Vertex ∧
      0 < (pc0 : ℝ) ∧ (pc0 : ℝ) < 1 ∧
      FK.Theorem14.BoundedDistance graph.lineGraph.dist (Set.range baseEdge) ∧
      FKLimit.IsSeparatedDeviceFamily (Set.range baseEdge) triangleDevice ∧
      (∀ e : G.edgeSet, (triangle e).IsCycle ∧ (triangle e).length = 3 ∧
        OnDoubleRay (baseEdge e) ∧
        baseEdge e ∈ FK.QuasiTransitive.walkDevice (triangle e)) ∧
      (∀ ε : unitInterval, 0 < (ε : ℝ) → (ε : ℝ) < (pc0 : ℝ) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ p : unitInterval, (pc0 : ℝ) ≤ (p : ℝ) →
          (p : ℝ) < (pc0 : ℝ) + δ →
            actualPr (penaltyRates p ε) {ω | ActualPerc ω} = 0) := by
  exact ⟨graph_connected, fun _ => Finite.of_fintype _, graph_quasiTransitive,
    inferInstance, pc0_pos, pc0_lt_one, direct_boundedDistance,
    direct_separatedDevices, direct_cycle_ray_geometry, strict_direct_penalty_window⟩

end Ultra.TriangleCactus
