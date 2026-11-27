import FK.TriangleCircuit

/-!
# The actual continuous embedding and spherical rotation of a triangle

The graph is the oriented 3-cycle.  Straight sides are proved noncrossing
from affine independence.  The six-dart rotation has two orientation classes.
-/

namespace FK.PlaneTopology.Continuous.Triangle

noncomputable section

open Set Metric Function
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology.Continuous
open FK.PlaneTopology.Continuous.OneSegment

def vertexSource (e : Fin 3) : Fin 3 := ![0, 1, 2] e
def vertexTarget (e : Fin 3) : Fin 3 := ![1, 2, 0] e

/-- The oriented three-cycle `0 → 1 → 2 → 0`. -/
def graph : LabelledMultigraph where
  Vertex := Fin 3
  Edge := Fin 3
  source := vertexSource
  target := vertexTarget

@[simp] lemma graph_source (e : Fin 3) : graph.source e = vertexSource e := rfl
@[simp] lemma graph_target (e : Fin 3) : graph.target e = vertexTarget e := rfl

lemma endpoint_ne (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3) :
    b (graph.source e) ≠ b (graph.target e) := by
  apply b.ind.injective.ne
  fin_cases e <;> simp [graph, vertexSource, vertexTarget]

/-- The straight Jordan arc for one labelled side. -/
def arc (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3) : JordanArc Plane :=
  straightArc (endpoint_ne b e)

@[simp] lemma arc_zero (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3) :
    arc b e 0 = b (graph.source e) := straightArc_zero _

@[simp] lemma arc_one (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3) :
    arc b e 1 = b (graph.target e) := straightArc_one _

lemma range_arc (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3) :
    Set.range (arc b e) = [b (graph.source e) -[ℝ] b (graph.target e)] :=
  range_straightArc _

/-- On a nondegenerate triangle, membership of a vertex in a side holds
exactly for the two endpoints. -/
lemma vertex_mem_segment_iff (b : AffineBasis (Fin 3) ℝ Plane)
    {i j v : Fin 3} (hij : i ≠ j) :
    b v ∈ [b i -[ℝ] b j] ↔ v = i ∨ v = j := by
  calc
    b v ∈ [b i -[ℝ] b j] ↔ Wbtw ℝ (b i) (b v) (b j) := mem_segment_iff_wbtw
    _ ↔ b v ∈ ((simplex b).face (Finset.card_pair hij)).closedInterior :=
      ((simplex b).mem_closedInterior_face_iff_wbtw hij).symm
    _ ↔ v ∈ ({i, j} : Finset (Fin 3)) :=
      (simplex b).point_mem_closedInterior_face_iff _
    _ ↔ v = i ∨ v = j := by simp

/-- Restriction of affine independence to two vectors based at a vertex. -/
lemma linearIndependent_pair_sub (b : AffineBasis (Fin 3) ℝ Plane)
    {i j k : Fin 3} (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) :
    LinearIndependent ℝ ![b j - b i, b k - b i] := by
  let J := {l : Fin 3 // l ≠ i}
  have hfull : LinearIndependent ℝ (fun l : J => b l.1 - b i) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ b i).mp b.ind
  let f : Fin 2 → J := fun n => ⟨![j, k] n, by fin_cases n <;> simp [hji, hki]⟩
  have hf : Function.Injective f := by
    intro m n hmn
    have h := congrArg Subtype.val hmn
    fin_cases m <;> fin_cases n <;> simp_all [f]
  have hcomp := hfull.comp f hf
  have heq : (fun l : J => b l.1 - b i) ∘ f = ![b j - b i, b k - b i] := by
    funext n
    fin_cases n <;> rfl
  rwa [heq] at hcomp

/-- Distinct graph vertices do not coincide geometrically. -/
lemma point_ne (b : AffineBasis (Fin 3) ℝ Plane) {i j : Fin 3} (hij : i ≠ j) :
    b i ≠ b j := b.ind.injective.ne hij

lemma arc_mem_segment (b : AffineBasis (Fin 3) ℝ Plane) (e : Fin 3) (t : I) :
    arc b e t ∈ [b (graph.source e) -[ℝ] b (graph.target e)] := by
  rw [← range_arc]
  exact ⟨t, rfl⟩

lemma arc_eq_vertex_endpoints (b : AffineBasis (Fin 3) ℝ Plane)
    {e v : Fin 3} {t : I} (h : arc b e t = b v) :
    (t = 0 ∧ graph.source e = v) ∨ (t = 1 ∧ graph.target e = v) := by
  have hv : b v ∈ [b (graph.source e) -[ℝ] b (graph.target e)] := h ▸ arc_mem_segment b e t
  have hst : graph.source e ≠ graph.target e := by
    exact fun h' => endpoint_ne b e (congrArg b h')
  rcases (vertex_mem_segment_iff b hst).1 hv with hvs | hvt
  · left
    have heq : t = (0 : I) := (arc b e).injective (by
      calc
        arc b e t = b v := h
        _ = b (graph.source e) := congrArg b hvs
        _ = arc b e 0 := (arc_zero b e).symm)
    exact ⟨heq, hvs.symm⟩
  · right
    have heq : t = (1 : I) := (arc b e).injective (by
      calc
        arc b e t = b v := h
        _ = b (graph.target e) := congrArg b hvt
        _ = arc b e 1 := (arc_one b e).symm)
    exact ⟨heq, hvt.symm⟩

/-- Two distinct sides meet only at a common triangle vertex. -/
lemma exists_common_vertex_of_arc_intersection (b : AffineBasis (Fin 3) ℝ Plane)
    {e f : Fin 3} (hef : e ≠ f) (s t : I) (h : arc b e s = arc b f t) :
    ∃ v : Fin 3, arc b e s = b v := by
  fin_cases e <;> fin_cases f
  all_goals try exact (hef rfl).elim
  · change arc b 0 s = arc b 1 t at h
    have hz : arc b 0 s ∈ [b 1 -[ℝ] b 0] ∩ [b 1 -[ℝ] b 2] := by
      constructor
      · rw [segment_symm ℝ (b 1) (b 0)]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 0 s
      · rw [h]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 1 t
    have hc := segment_inter_subset_endpoint_of_linearIndependent_sub ℝ
      (linearIndependent_pair_sub b (i := 1) (j := 0) (k := 2)
        (by decide) (by decide) (by decide)) hz
    exact ⟨1, by simpa using hc⟩
  · change arc b 0 s = arc b 2 t at h
    have hz : arc b 0 s ∈ [b 0 -[ℝ] b 1] ∩ [b 0 -[ℝ] b 2] := by
      constructor
      · simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 0 s
      · rw [h, segment_symm ℝ (b 0) (b 2)]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 2 t
    have hc := segment_inter_subset_endpoint_of_linearIndependent_sub ℝ
      (linearIndependent_pair_sub b (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) (by decide)) hz
    exact ⟨0, by simpa using hc⟩
  · change arc b 1 s = arc b 0 t at h
    have hz : arc b 1 s ∈ [b 1 -[ℝ] b 2] ∩ [b 1 -[ℝ] b 0] := by
      constructor
      · simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 1 s
      · rw [h, segment_symm ℝ (b 1) (b 0)]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 0 t
    have hc := segment_inter_subset_endpoint_of_linearIndependent_sub ℝ
      (linearIndependent_pair_sub b (i := 1) (j := 2) (k := 0)
        (by decide) (by decide) (by decide)) hz
    exact ⟨1, by simpa using hc⟩
  · change arc b 1 s = arc b 2 t at h
    have hz : arc b 1 s ∈ [b 2 -[ℝ] b 1] ∩ [b 2 -[ℝ] b 0] := by
      constructor
      · rw [segment_symm ℝ (b 2) (b 1)]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 1 s
      · rw [h]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 2 t
    have hc := segment_inter_subset_endpoint_of_linearIndependent_sub ℝ
      (linearIndependent_pair_sub b (i := 2) (j := 1) (k := 0)
        (by decide) (by decide) (by decide)) hz
    exact ⟨2, by simpa using hc⟩
  · change arc b 2 s = arc b 0 t at h
    have hz : arc b 2 s ∈ [b 0 -[ℝ] b 2] ∩ [b 0 -[ℝ] b 1] := by
      constructor
      · rw [segment_symm ℝ (b 0) (b 2)]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 2 s
      · rw [h]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 0 t
    have hc := segment_inter_subset_endpoint_of_linearIndependent_sub ℝ
      (linearIndependent_pair_sub b (i := 0) (j := 2) (k := 1)
        (by decide) (by decide) (by decide)) hz
    exact ⟨0, by simpa using hc⟩
  · change arc b 2 s = arc b 1 t at h
    have hz : arc b 2 s ∈ [b 2 -[ℝ] b 0] ∩ [b 2 -[ℝ] b 1] := by
      constructor
      · simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 2 s
      · rw [h, segment_symm ℝ (b 2) (b 1)]
        simpa [graph, vertexSource, vertexTarget] using arc_mem_segment b 1 t
    have hc := segment_inter_subset_endpoint_of_linearIndependent_sub ℝ
      (linearIndependent_pair_sub b (i := 2) (j := 0) (k := 1)
        (by decide) (by decide) (by decide)) hz
    exact ⟨2, by simpa using hc⟩

/-- The straight-segment embedding satisfies all actual continuous-carrier
noncrossing conditions. -/
def embedding (b : AffineBasis (Fin 3) ℝ Plane) : FiniteArcEmbedding graph where
  point := b
  arc := arc b
  point_injective := b.ind.injective
  source := arc_zero b
  target := arc_one b
  vertex_intersection := by
    intro v e t h
    change Fin 3 at v e
    exact arc_eq_vertex_endpoints b h.symm
  intersection := by
    intro e f hef s t h
    change Fin 3 at e f
    obtain ⟨v, hv⟩ := exists_common_vertex_of_arc_intersection b hef s t h
    exact ⟨v, hv, arc_eq_vertex_endpoints b hv,
      arc_eq_vertex_endpoints b (h.symm.trans hv)⟩

/-- The arcs cover exactly the three sides. -/
lemma iUnion_arc (b : AffineBasis (Fin 3) ℝ Plane) :
    (⋃ e, Set.range (arc b e)) = boundary b := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
    fin_cases e <;> rw [range_arc] at he <;>
      simp [boundary, graph, vertexSource, vertexTarget] at he ⊢ <;> tauto
  · intro hz
    rcases hz with (h01 | h12) | h20
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      rw [range_arc]
      simpa [graph, vertexSource, vertexTarget] using h01
    · apply Set.mem_iUnion.mpr
      refine ⟨1, ?_⟩
      rw [range_arc]
      simpa [graph, vertexSource, vertexTarget] using h12
    · apply Set.mem_iUnion.mpr
      refine ⟨2, ?_⟩
      rw [range_arc]
      simpa [graph, vertexSource, vertexTarget] using h20

/-- The actual compact closed carrier of the continuous embedding is the
three-segment polygonal boundary. -/
theorem carrier_embedding (b : AffineBasis (Fin 3) ℝ Plane) :
    (embedding b).carrier = boundary b := by
  have hv : Set.range b ⊆ boundary b := by
    rintro z ⟨v, rfl⟩
    fin_cases v
    · exact Or.inl (Or.inl (left_mem_segment ℝ (b 0) (b 1)))
    · exact Or.inl (Or.inl (right_mem_segment ℝ (b 0) (b 1)))
    · exact Or.inr (left_mem_segment ℝ (b 2) (b 0))
  change (Set.range b ∪ ⋃ e, Set.range (arc b e)) = boundary b
  rw [iUnion_arc]
  exact Set.union_eq_right.mpr hv

/-- The two regions, regarded as subsets of the actual complement subtype. -/
def regionSet (b : AffineBasis (Fin 3) ℝ Plane) : Bool → Set (embedding b).FacePoints
  | false => Subtype.val ⁻¹' outside b
  | true => Subtype.val ⁻¹' inside b

lemma mem_outside_of_not_inside (b : AffineBasis (Fin 3) ℝ Plane)
    (x : (embedding b).FacePoints) (hx : x.1 ∉ inside b) : x.1 ∈ outside b := by
  have hxc : x.1 ∈ (boundary b)ᶜ := by
    rw [← carrier_embedding]
    exact x.2
  have hu : x.1 ∈ inside b ∪ outside b := by
    rw [← compl_boundary]
    exact hxc
  exact hu.resolve_left hx

lemma regionSet_false_eq_compl (b : AffineBasis (Fin 3) ℝ Plane) :
    regionSet b false = (regionSet b true)ᶜ := by
  ext x
  constructor
  · intro hx hxi
    exact hx (interior_subset_closure hxi)
  · intro hx
    exact mem_outside_of_not_inside b x hx

lemma image_inside_region (b : AffineBasis (Fin 3) ℝ Plane) :
    Subtype.val '' regionSet b true = inside b := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    have hzc : z ∈ (embedding b).carrierᶜ := by
      rw [carrier_embedding, compl_boundary]
      exact Or.inl hz
    exact ⟨⟨z, hzc⟩, hz, rfl⟩

lemma image_outside_region (b : AffineBasis (Fin 3) ℝ Plane) :
    Subtype.val '' regionSet b false = outside b := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    have hzc : z ∈ (embedding b).carrierᶜ := by
      rw [carrier_embedding, compl_boundary]
      exact Or.inr hz
    exact ⟨⟨z, hzc⟩, hz, rfl⟩

lemma isPathConnected_inside_region (b : AffineBasis (Fin 3) ℝ Plane) :
    IsPathConnected (regionSet b true) := by
  rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, image_inside_region]
  exact isPathConnected_inside b

lemma isPathConnected_outside_region (b : AffineBasis (Fin 3) ℝ Plane) :
    IsPathConnected (regionSet b false) := by
  rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, image_outside_region]
  exact isPathConnected_outside b

/-- The actual connected-component face type of the continuous embedding is
canonically identified with the two labels `false` (outside) and `true`
(inside). -/
noncomputable def faceEquivBool (b : AffineBasis (Fin 3) ℝ Plane) :
    (embedding b).Face ≃ Bool := by
  have htrueOpen : IsOpen (regionSet b true) :=
    isOpen_interior.preimage continuous_subtype_val
  have hfalseOpen : IsOpen (regionSet b false) :=
    isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  have hfalseEq : regionSet b true = (regionSet b false)ᶜ := by
    rw [regionSet_false_eq_compl, compl_compl]
  have hclopen : ∀ i, IsClopen (regionSet b i) := by
    intro i
    cases i
    · exact ⟨(regionSet_false_eq_compl b).symm ▸ htrueOpen.isClosed_compl,
        hfalseOpen⟩
    · exact ⟨hfalseEq.symm ▸ hfalseOpen.isClosed_compl, htrueOpen⟩
  have hdisj : Pairwise (Disjoint on regionSet b) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · change Disjoint (regionSet b false) (regionSet b true)
      rw [regionSet_false_eq_compl]
      exact disjoint_compl_left
    · change Disjoint (regionSet b true) (regionSet b false)
      rw [regionSet_false_eq_compl]
      exact disjoint_compl_right
    · exact (hij rfl).elim
  have hunion : (⋃ i, regionSet b i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x.1 ∈ inside b
    · exact ⟨true, hx⟩
    · exact ⟨false, mem_outside_of_not_inside b x hx⟩
  have hconn : ∀ i, IsConnected (regionSet b i) := by
    intro i
    cases i
    · exact (isPathConnected_outside_region b).isConnected
    · exact (isPathConnected_inside_region b).isConnected
  exact ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn

end
end FK.PlaneTopology.Continuous.Triangle
