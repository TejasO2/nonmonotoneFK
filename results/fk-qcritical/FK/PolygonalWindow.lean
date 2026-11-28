import FK.ContinuousReparametrization

/-!
# An exact polygonal four-cycle with arbitrary continuous side parameters

This module constructs a new finite continuous window on the unit square.  The
straight carrier is proved to be the frontier of the closed square.  Its two
actual complementary connected components are the bounded open square and the
unbounded exterior.  Range-preserving reparametrization then permits arbitrary
continuous Jordan parametrizations of the four sides.

This is a scoped four-edge example.  No general simple-polygon Jordan theorem,
angular-order extraction, infinite window, or Theorem 1.11 conclusion is used.
-/

namespace FK.PlaneTopology.Continuous.Polygonal

noncomputable section

open Set Metric Function
open scoped Classical Convex unitInterval BigOperators
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology.Continuous
open FK.PlaneTopology.Continuous.OneSegment

namespace Square

/-- Counterclockwise vertices of the unit square. -/
def point : Fin 4 → Plane := ![(0, 0), (1, 0), (1, 1), (0, 1)]

def vertexSource (e : Fin 4) : Fin 4 := ![0, 1, 2, 3] e
def vertexTarget (e : Fin 4) : Fin 4 := ![1, 2, 3, 0] e

/-- The oriented four-cycle. -/
def graph : LabelledMultigraph where
  Vertex := Fin 4
  Edge := Fin 4
  source := vertexSource
  target := vertexTarget

@[simp] lemma graph_source (e : Fin 4) : graph.source e = vertexSource e := rfl
@[simp] lemma graph_target (e : Fin 4) : graph.target e = vertexTarget e := rfl

lemma point_injective : Function.Injective point := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [point, Prod.ext_iff]

lemma point_ne {i j : Fin 4} (hij : i ≠ j) : point i ≠ point j :=
  point_injective.ne hij

lemma endpoint_ne (e : Fin 4) : point (graph.source e) ≠ point (graph.target e) := by
  apply point_ne
  fin_cases e <;> simp [graph, vertexSource, vertexTarget]

/-- The four closed straight sides. -/
def sideSet (e : Fin 4) : Set Plane :=
  [point (graph.source e) -[ℝ] point (graph.target e)]

lemma mem_sideSet_zero {z : Plane} :
    z ∈ sideSet 0 ↔ z.2 = 0 ∧ z.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sideSet, segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hy : (AffineMap.lineMap (point (vertexSource 0))
        (point (vertexTarget 0)) t).2 = 0 := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    refine ⟨hy, ?_⟩
    have hx : (AffineMap.lineMap (point (vertexSource 0))
        (point (vertexTarget 0)) t).1 = (t : ℝ) := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    simp only [graph_source, graph_target, hx]
    exact ht
  · rintro ⟨hy, hx⟩
    refine ⟨z.1, hx, ?_⟩
    apply Prod.ext
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply, hy]

lemma mem_sideSet_one {z : Plane} :
    z ∈ sideSet 1 ↔ z.1 = 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sideSet, segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hx : (AffineMap.lineMap (point (vertexSource 1))
        (point (vertexTarget 1)) t).1 = 1 := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    refine ⟨hx, ?_⟩
    have hy : (AffineMap.lineMap (point (vertexSource 1))
        (point (vertexTarget 1)) t).2 = (t : ℝ) := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    simp only [graph_source, graph_target, hy]
    exact ht
  · rintro ⟨hx, hy⟩
    refine ⟨z.2, hy, ?_⟩
    apply Prod.ext
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply, hx]
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]

lemma mem_sideSet_two {z : Plane} :
    z ∈ sideSet 2 ↔ z.2 = 1 ∧ z.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sideSet, segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hy : (AffineMap.lineMap (point (vertexSource 2))
        (point (vertexTarget 2)) t).2 = 1 := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    refine ⟨hy, ?_⟩
    have hx : (AffineMap.lineMap (point (vertexSource 2))
        (point (vertexTarget 2)) t).1 = 1 - (t : ℝ) := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
      ring
    simp only [graph_source, graph_target, hx]
    exact ⟨sub_nonneg.mpr ht.2, by simpa using ht.1⟩
  · rintro ⟨hy, hx⟩
    refine ⟨1 - z.1, ⟨by simpa using hx.2, by simpa using hx.1⟩, ?_⟩
    apply Prod.ext
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply, hy]

lemma mem_sideSet_three {z : Plane} :
    z ∈ sideSet 3 ↔ z.1 = 0 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sideSet, segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hx : (AffineMap.lineMap (point (vertexSource 3))
        (point (vertexTarget 3)) t).1 = 0 := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
    refine ⟨hx, ?_⟩
    have hy : (AffineMap.lineMap (point (vertexSource 3))
        (point (vertexTarget 3)) t).2 = 1 - (t : ℝ) := by
      simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]
      ring
    simp only [graph_source, graph_target, hy]
    exact ⟨sub_nonneg.mpr ht.2, by simpa using ht.1⟩
  · rintro ⟨hx, hy⟩
    refine ⟨1 - z.2, ⟨by simpa using hy.2, by simpa using hy.1⟩, ?_⟩
    apply Prod.ext
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply, hx]
    · simp [point, vertexSource, vertexTarget, AffineMap.lineMap_apply]

/-- Coordinate membership data for the four sides, in the same cyclic order. -/
def sideData : Fin 4 → Set Plane := ![
  {z : Plane | z.2 = 0 ∧ z.1 ∈ Set.Icc (0 : ℝ) 1},
  {z : Plane | z.1 = 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1},
  {z : Plane | z.2 = 1 ∧ z.1 ∈ Set.Icc (0 : ℝ) 1},
  {z : Plane | z.1 = 0 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1}]

lemma sideSet_eq_data (e : Fin 4) : sideSet e = sideData e := by
  fin_cases e
  · change sideSet 0 = sideData 0
    ext z
    simpa [sideData] using (mem_sideSet_zero (z := z))
  · change sideSet 1 = sideData 1
    ext z
    simpa [sideData] using (mem_sideSet_one (z := z))
  · change sideSet 2 = sideData 2
    ext z
    simpa [sideData] using (mem_sideSet_two (z := z))
  · change sideSet 3 = sideData 3
    ext z
    simpa [sideData] using (mem_sideSet_three (z := z))

/-- The polygonal carrier, with no diagonal. -/
def boundary : Set Plane := sideSet 0 ∪ sideSet 1 ∪ sideSet 2 ∪ sideSet 3

/-- The closed square is described as a product of real intervals. -/
def solid : Set Plane := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- Its actual topological interior. -/
def inside : Set Plane := interior solid

/-- Its actual exterior, outside the closure. -/
def outside : Set Plane := (closure solid)ᶜ

lemma convex_solid : Convex ℝ solid := (convex_Icc 0 1).prod (convex_Icc 0 1)
lemma isCompact_solid : IsCompact solid := isCompact_Icc.prod isCompact_Icc
lemma isClosed_solid : IsClosed solid := isCompact_solid.isClosed
lemma closure_solid : closure solid = solid := isClosed_solid.closure_eq

lemma mem_solid_iff {z : Plane} :
    z ∈ solid ↔ z.1 ∈ Set.Icc (0 : ℝ) 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1 := Iff.rfl

lemma mem_inside_iff {z : Plane} :
    z ∈ inside ↔ z.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ z.2 ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [inside, solid, interior_prod_eq, interior_Icc]
  rfl

lemma mem_outside_iff {z : Plane} : z ∈ outside ↔ z ∉ solid := by
  rw [outside, closure_solid]
  rfl

/-- The four sides are exactly the topological frontier of the closed square. -/
lemma frontier_solid : frontier solid = boundary := by
  rw [frontier, closure_solid]
  ext z
  change (z ∈ solid ∧ z ∉ inside) ↔ z ∈ boundary
  constructor
  · rintro ⟨hs, hni⟩
    rw [mem_solid_iff] at hs
    have hside : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1 := by
      by_cases hx0 : z.1 = 0
      · exact Or.inl hx0
      by_cases hx1 : z.1 = 1
      · exact Or.inr (Or.inl hx1)
      by_cases hy0 : z.2 = 0
      · exact Or.inr (Or.inr (Or.inl hy0))
      by_cases hy1 : z.2 = 1
      · exact Or.inr (Or.inr (Or.inr hy1))
      exfalso
      apply hni
      rw [mem_inside_iff]
      exact ⟨⟨lt_of_le_of_ne hs.1.1 (Ne.symm hx0), lt_of_le_of_ne hs.1.2 hx1⟩,
        ⟨lt_of_le_of_ne hs.2.1 (Ne.symm hy0), lt_of_le_of_ne hs.2.2 hy1⟩⟩
    rcases hside with hx0 | hx1 | hy0 | hy1
    · exact Or.inr (mem_sideSet_three.mpr ⟨hx0, hs.2⟩)
    · exact Or.inl (Or.inl (Or.inr (mem_sideSet_one.mpr ⟨hx1, hs.2⟩)))
    · exact Or.inl (Or.inl (Or.inl (mem_sideSet_zero.mpr ⟨hy0, hs.1⟩)))
    · exact Or.inl (Or.inr (mem_sideSet_two.mpr ⟨hy1, hs.1⟩))
  · intro hz
    have hs : z ∈ solid := by
      rcases hz with (((h0 | h1) | h2) | h3)
      · rw [mem_sideSet_zero] at h0
        exact mem_solid_iff.mpr ⟨h0.2, by rw [h0.1]; exact ⟨le_rfl, zero_le_one⟩⟩
      · rw [mem_sideSet_one] at h1
        exact mem_solid_iff.mpr ⟨by rw [h1.1]; exact ⟨zero_le_one, le_rfl⟩, h1.2⟩
      · rw [mem_sideSet_two] at h2
        exact mem_solid_iff.mpr ⟨h2.2, by rw [h2.1]; exact ⟨zero_le_one, le_rfl⟩⟩
      · rw [mem_sideSet_three] at h3
        exact mem_solid_iff.mpr ⟨by rw [h3.1]; exact ⟨le_rfl, zero_le_one⟩, h3.2⟩
    refine ⟨hs, ?_⟩
    intro hi
    rw [mem_inside_iff] at hi
    rcases hz with (((h0 | h1) | h2) | h3)
    · rw [mem_sideSet_zero] at h0
      linarith [hi.2.1]
    · rw [mem_sideSet_one] at h1
      linarith [hi.1.2]
    · rw [mem_sideSet_two] at h2
      linarith [hi.2.2]
    · rw [mem_sideSet_three] at h3
      linarith [hi.1.1]

lemma compl_boundary : boundaryᶜ = inside ∪ outside := by
  rw [← frontier_solid]
  exact FK.PlaneTopology.compl_frontier_eq_interior_union_compl_closure solid

/-- The affine parametrization is used only to construct the carrier; it will
subsequently be transported to arbitrary continuous side parametrizations. -/
def arc (e : Fin 4) : JordanArc Plane := straightArc (endpoint_ne e)

@[simp] lemma arc_zero (e : Fin 4) : arc e 0 = point (graph.source e) :=
  straightArc_zero _

@[simp] lemma arc_one (e : Fin 4) : arc e 1 = point (graph.target e) :=
  straightArc_one _

lemma range_arc (e : Fin 4) : Set.range (arc e) = sideSet e :=
  range_straightArc _

lemma arc_mem_sideSet (e : Fin 4) (t : I) : arc e t ∈ sideSet e := by
  rw [← range_arc]
  exact ⟨t, rfl⟩

lemma vertex_mem_sideSet_iff {v e : Fin 4} :
    point v ∈ sideSet e ↔ v = graph.source e ∨ v = graph.target e := by
  rw [sideSet_eq_data]
  fin_cases e <;> fin_cases v <;>
    norm_num [sideData, point, vertexSource, vertexTarget, Prod.ext_iff]

lemma arc_eq_vertex_endpoints {e v : Fin 4} {t : I} (h : arc e t = point v) :
    (t = 0 ∧ graph.source e = v) ∨ (t = 1 ∧ graph.target e = v) := by
  have hv : point v ∈ sideSet e := h ▸ arc_mem_sideSet e t
  rcases (vertex_mem_sideSet_iff).1 hv with rfl | rfl
  · left
    exact ⟨(arc e).injective (h.trans (arc_zero e).symm), rfl⟩
  · right
    exact ⟨(arc e).injective (h.trans (arc_one e).symm), rfl⟩

/-- Two distinct sides of the square meet only at a vertex. -/
lemma exists_common_vertex_of_sideData_intersection {e f : Fin 4} (hef : e ≠ f)
    {z : Plane} (he : z ∈ sideData e) (hf : z ∈ sideData f) :
    ∃ v : Fin 4, z = point v := by
  fin_cases e <;> fin_cases f <;> simp [sideData] at he hf
  all_goals try exact (hef rfl).elim
  · exact ⟨1, Prod.ext hf.1 he.1⟩
  · exfalso; linarith [he.1, hf.1]
  · exact ⟨0, Prod.ext hf.1 he.1⟩
  · exact ⟨1, Prod.ext he.1 hf.1⟩
  · exact ⟨2, Prod.ext he.1 hf.1⟩
  · exfalso; linarith [he.1, hf.1]
  · exfalso; linarith [he.1, hf.1]
  · exact ⟨2, Prod.ext hf.1 he.1⟩
  · exact ⟨3, Prod.ext hf.1 he.1⟩
  · exact ⟨0, Prod.ext he.1 hf.1⟩
  · exfalso; linarith [he.1, hf.1]
  · exact ⟨3, Prod.ext he.1 hf.1⟩

/-- The straight square is a source-faithful finite continuous embedding. -/
def embedding : FiniteArcEmbedding graph where
  point := point
  arc := arc
  point_injective := point_injective
  source := arc_zero
  target := arc_one
  vertex_intersection := by
    intro v e t h
    exact arc_eq_vertex_endpoints h.symm
  intersection := by
    intro e f hef s t h
    change Fin 4 at e f
    have he : arc e s ∈ sideSet e := arc_mem_sideSet e s
    have hf : arc e s ∈ sideSet f := by
      rw [h]
      exact arc_mem_sideSet f t
    rw [sideSet_eq_data] at he hf
    obtain ⟨v, hv⟩ := exists_common_vertex_of_sideData_intersection hef he hf
    exact ⟨v, hv, arc_eq_vertex_endpoints hv,
      arc_eq_vertex_endpoints (h.symm.trans hv)⟩

lemma iUnion_arc : (⋃ e, Set.range (arc e)) = boundary := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
    rw [range_arc] at he
    fin_cases e
    · exact Or.inl (Or.inl (Or.inl he))
    · exact Or.inl (Or.inl (Or.inr he))
    · exact Or.inl (Or.inr he)
    · exact Or.inr he
  · intro hz
    rcases hz with (((h0 | h1) | h2) | h3)
    · exact Set.mem_iUnion.mpr ⟨0, by rwa [range_arc]⟩
    · exact Set.mem_iUnion.mpr ⟨1, by rwa [range_arc]⟩
    · exact Set.mem_iUnion.mpr ⟨2, by rwa [range_arc]⟩
    · exact Set.mem_iUnion.mpr ⟨3, by rwa [range_arc]⟩

/-- The actual compact continuous carrier is the four-sided boundary. -/
theorem carrier_embedding : embedding.carrier = boundary := by
  have hv : Set.range point ⊆ boundary := by
    rintro z ⟨v, rfl⟩
    fin_cases v
    · exact Or.inl (Or.inl (Or.inl (by
        rw [← range_arc 0]
        exact ⟨0, arc_zero 0⟩)))
    · exact Or.inl (Or.inl (Or.inr (by
        rw [← range_arc 1]
        exact ⟨0, arc_zero 1⟩)))
    · exact Or.inl (Or.inr (by
        rw [← range_arc 2]
        exact ⟨0, arc_zero 2⟩))
    · exact Or.inr (by
        rw [← range_arc 3]
        exact ⟨0, arc_zero 3⟩)
  change Set.range point ∪ (⋃ e, Set.range (arc e)) = boundary
  rw [iUnion_arc]
  exact Set.union_eq_right.mpr hv

/-- The bounded face is path connected. -/
lemma isPathConnected_inside : IsPathConnected inside := by
  apply convex_solid.interior.isPathConnected
  refine ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), ?_⟩
  exact mem_inside_iff.mpr ⟨by norm_num, by norm_num⟩

/-- The exterior is path connected by radial paths and a distant sphere. -/
lemma isPathConnected_outside : IsPathConnected outside := by
  exact Triangle.isPathConnected_compl_closure_of_bounded convex_solid
    (show ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ solid by norm_num [solid])
    isCompact_solid.isBounded Triangle.rank_plane

lemma isBounded_inside : Bornology.IsBounded inside :=
  isCompact_solid.isBounded.subset interior_subset

lemma not_isBounded_outside : ¬ Bornology.IsBounded outside := by
  exact Triangle.not_isBounded_compl_closure isCompact_solid.isBounded

/-- The two regions, regarded as subsets of the actual complement subtype. -/
def regionSet : Bool → Set embedding.FacePoints
  | false => Subtype.val ⁻¹' outside
  | true => Subtype.val ⁻¹' inside

lemma mem_outside_of_not_inside (x : embedding.FacePoints) (hx : x.1 ∉ inside) :
    x.1 ∈ outside := by
  have hxc : x.1 ∈ boundaryᶜ := by
    rw [← carrier_embedding]
    exact x.2
  have hu : x.1 ∈ inside ∪ outside := by
    rw [← compl_boundary]
    exact hxc
  exact hu.resolve_left hx

lemma regionSet_false_eq_compl : regionSet false = (regionSet true)ᶜ := by
  ext x
  constructor
  · intro hx hxi
    exact hx (interior_subset_closure hxi)
  · intro hx
    exact mem_outside_of_not_inside x hx

lemma image_inside_region : Subtype.val '' regionSet true = inside := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    have hzc : z ∈ embedding.carrierᶜ := by
      rw [carrier_embedding, compl_boundary]
      exact Or.inl hz
    exact ⟨⟨z, hzc⟩, hz, rfl⟩

lemma image_outside_region : Subtype.val '' regionSet false = outside := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    have hzc : z ∈ embedding.carrierᶜ := by
      rw [carrier_embedding, compl_boundary]
      exact Or.inr hz
    exact ⟨⟨z, hzc⟩, hz, rfl⟩

lemma isPathConnected_inside_region : IsPathConnected (regionSet true) := by
  rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, image_inside_region]
  exact isPathConnected_inside

lemma isPathConnected_outside_region : IsPathConnected (regionSet false) := by
  rw [Topology.IsInducing.subtypeVal.isPathConnected_iff, image_outside_region]
  exact isPathConnected_outside

/-- The actual connected-component face type is canonically `Bool`, with
`false` the unbounded exterior and `true` the bounded open square. -/
noncomputable def faceEquivBool : embedding.Face ≃ Bool := by
  have htrueOpen : IsOpen (regionSet true) :=
    isOpen_interior.preimage continuous_subtype_val
  have hfalseOpen : IsOpen (regionSet false) :=
    isClosed_closure.isOpen_compl.preimage continuous_subtype_val
  have hfalseEq : regionSet true = (regionSet false)ᶜ := by
    rw [regionSet_false_eq_compl, compl_compl]
  have hclopen : ∀ i, IsClopen (regionSet i) := by
    intro i
    cases i
    · exact ⟨(regionSet_false_eq_compl).symm ▸ htrueOpen.isClosed_compl,
        hfalseOpen⟩
    · exact ⟨hfalseEq.symm ▸ hfalseOpen.isClosed_compl, htrueOpen⟩
  have hdisj : Pairwise (Disjoint on regionSet) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · change Disjoint (regionSet false) (regionSet true)
      rw [regionSet_false_eq_compl]
      exact disjoint_compl_left
    · change Disjoint (regionSet true) (regionSet false)
      rw [regionSet_false_eq_compl]
      exact disjoint_compl_right
    · exact (hij rfl).elim
  have hunion : (⋃ i, regionSet i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x.1 ∈ inside
    · exact ⟨true, hx⟩
    · exact ⟨false, mem_outside_of_not_inside x hx⟩
  have hconn : ∀ i, IsConnected (regionSet i) := by
    intro i
    cases i
    · exact isPathConnected_outside_region.isConnected
    · exact isPathConnected_inside_region.isConnected
  exact ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn

/-! ## The spherical rotation of the four-cycle

At each degree-two vertex the planar rotation is forced up to global reversal:
it exchanges the incoming and outgoing darts.  We prove the resulting two face
cycles directly rather than claiming angular structure from edge enumeration. -/

def dt (e : Fin 4) (b : Bool) : Dart graph := (e, b)

/-- Incoming and outgoing darts are exchanged at their common vertex. -/
def dartMap : Dart graph → Dart graph := fun d =>
  cond d.2
    ((![dt 1 false, dt 2 false, dt 3 false, dt 0 false] : Fin 4 → Dart graph) d.1)
    ((![dt 3 true, dt 0 true, dt 1 true, dt 2 true] : Fin 4 → Dart graph) d.1)

lemma dartMap_dartMap (d : Dart graph) : dartMap (dartMap d) = d := by
  rcases d with ⟨e, b⟩
  change Fin 4 at e
  fin_cases e <;> cases b <;> rfl

def dartRotation : Equiv.Perm (Dart graph) where
  toFun := dartMap
  invFun := dartMap
  left_inv := dartMap_dartMap
  right_inv := dartMap_dartMap

@[simp] lemma dartRotation_apply (e : Fin 4) (b : Bool) :
    vertex graph (dartRotation (dt e b)) = vertex graph (dt e b) := by
  change vertex graph (dartMap (dt e b)) = vertex graph (dt e b)
  fin_cases e <;> cases b <;> rfl

lemma dart_eq_or_rotation_eq {d d' : Dart graph}
    (hd : vertex graph d = vertex graph d') : d = d' ∨ dartRotation d = d' := by
  rcases d with ⟨e, b⟩
  rcases d' with ⟨e', b'⟩
  fin_cases e <;> cases b <;> fin_cases e' <;> cases b' <;>
    simp [vertex, graph, vertexSource, vertexTarget] at hd <;>
    simp [dartRotation, dartMap, dt]

/-- The four-cycle with its exact local rotation. -/
def rotationSystem : RotationSystem graph where
  rotation := dartRotation
  vertex_rotation := by
    rintro ⟨e, b⟩
    exact dartRotation_apply e b
  sameCycle_rotation := by
    intro d d' hd
    rcases dart_eq_or_rotation_eq hd with rfl | h
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simpa using h⟩

@[simp] lemma facePerm_zero_false :
    rotationSystem.facePerm (dt 0 false) = dt 1 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_one_false :
    rotationSystem.facePerm (dt 1 false) = dt 2 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_two_false :
    rotationSystem.facePerm (dt 2 false) = dt 3 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_three_false :
    rotationSystem.facePerm (dt 3 false) = dt 0 false := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_zero_true :
    rotationSystem.facePerm (dt 0 true) = dt 3 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_one_true :
    rotationSystem.facePerm (dt 1 true) = dt 0 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_two_true :
    rotationSystem.facePerm (dt 2 true) = dt 1 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_three_true :
    rotationSystem.facePerm (dt 3 true) = dt 2 true := by
  simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

@[simp] lemma facePerm_snd (d : Dart graph) :
    (rotationSystem.facePerm d).2 = d.2 := by
  rcases d with ⟨e, b⟩
  change Fin 4 at e
  fin_cases e <;> cases b <;>
    simp [RotationSystem.facePerm, rotationSystem, dartRotation, dartMap, dt, reverse]

lemma facePerm_pow_snd (d : Dart graph) (n : ℕ) :
    ((rotationSystem.facePerm ^ n) d).2 = d.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, facePerm_snd]
      exact ih

/-- Every dart is in the face orbit of the zero-edge dart with the same
orientation. -/
lemma faceOf_base (e : Fin 4) (b : Bool) :
    rotationSystem.faceOf (dt e b) = rotationSystem.faceOf (dt 0 b) := by
  fin_cases e <;> cases b
  · rfl
  · rfl
  · apply (rotationSystem.faceOf_eq_iff).2
    have h₁ : rotationSystem.facePerm.SameCycle (dt 1 false) (dt 2 false) :=
      ⟨1, by simp⟩
    have h₂ : rotationSystem.facePerm.SameCycle (dt 2 false) (dt 3 false) :=
      ⟨1, by simp⟩
    have h₃ : rotationSystem.facePerm.SameCycle (dt 3 false) (dt 0 false) :=
      ⟨1, by simp⟩
    exact h₁.trans (h₂.trans h₃)
  · apply (rotationSystem.faceOf_eq_iff).2
    exact ⟨1, by simp⟩
  · apply (rotationSystem.faceOf_eq_iff).2
    have h₁ : rotationSystem.facePerm.SameCycle (dt 2 false) (dt 3 false) :=
      ⟨1, by simp⟩
    have h₂ : rotationSystem.facePerm.SameCycle (dt 3 false) (dt 0 false) :=
      ⟨1, by simp⟩
    exact h₁.trans h₂
  · apply (rotationSystem.faceOf_eq_iff).2
    have h₁ : rotationSystem.facePerm.SameCycle (dt 2 true) (dt 1 true) :=
      ⟨1, by simp⟩
    have h₂ : rotationSystem.facePerm.SameCycle (dt 1 true) (dt 0 true) :=
      ⟨1, by simp⟩
    exact h₁.trans h₂
  · apply (rotationSystem.faceOf_eq_iff).2
    exact ⟨1, by simp⟩
  · apply (rotationSystem.faceOf_eq_iff).2
    have h₁ : rotationSystem.facePerm.SameCycle (dt 3 true) (dt 2 true) :=
      ⟨1, by simp⟩
    have h₂ : rotationSystem.facePerm.SameCycle (dt 2 true) (dt 1 true) :=
      ⟨1, by simp⟩
    have h₃ : rotationSystem.facePerm.SameCycle (dt 1 true) (dt 0 true) :=
      ⟨1, by simp⟩
    exact h₁.trans (h₂.trans h₃)

lemma faceOf_eq_iff_snd {d d' : Dart graph} :
    rotationSystem.faceOf d = rotationSystem.faceOf d' ↔ d.2 = d'.2 := by
  constructor
  · intro heq
    obtain ⟨n, hn⟩ := ((rotationSystem.faceOf_eq_iff).1 heq).exists_nat_pow_eq
    have hn' := congrArg Prod.snd hn
    rwa [facePerm_pow_snd] at hn'
  · rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    change Fin 4 at e e'
    intro hb
    cases hb
    change rotationSystem.faceOf (dt e b) = rotationSystem.faceOf (dt e' b)
    rw [faceOf_base e b, faceOf_base e' b]

/-- The two face-traversal classes are the two dart orientations. -/
noncomputable def combFaceEquivBool : rotationSystem.Face ≃ Bool where
  toFun f := Quotient.liftOn f (fun d : Dart graph => d.2) (fun d d' h => by
    apply (faceOf_eq_iff_snd).1
    exact (rotationSystem.faceOf_eq_iff).2 h)
  invFun b := rotationSystem.faceOf (dt 0 b)
  left_inv f := by
    refine Quotient.inductionOn f ?_
    rintro ⟨e, b⟩
    change Fin 4 at e
    change rotationSystem.faceOf (dt 0 b) = rotationSystem.faceOf (dt e b)
    exact (faceOf_base e b).symm
  right_inv b := rfl

noncomputable instance fintypeFace : Fintype rotationSystem.Face :=
  rotationSystem.dualPair.fintypeFace

theorem card_face : Fintype.card rotationSystem.Face = 2 := by
  rw [Fintype.card_congr combFaceEquivBool]
  decide

lemma adj_source_target (e : Fin 4) :
    (graph.connectionGraph graph.freeBoundary graph.allOpen).Adj
      (graph.source e) (graph.target e) := by
  refine ⟨?_, Or.inr ⟨e, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  intro hst
  exact endpoint_ne e (congrArg point hst)

/-- The primal four-cycle is connected. -/
theorem graph_preconnected :
    (graph.connectionGraph graph.freeBoundary graph.allOpen).Preconnected := by
  have r01 : (graph.connectionGraph graph.freeBoundary graph.allOpen).Reachable (0 : Fin 4) (1 : Fin 4) := by
    apply SimpleGraph.Adj.reachable
    simpa [graph, vertexSource, vertexTarget] using adj_source_target (0 : Fin 4)
  have r12 : (graph.connectionGraph graph.freeBoundary graph.allOpen).Reachable (1 : Fin 4) (2 : Fin 4) := by
    apply SimpleGraph.Adj.reachable
    simpa [graph, vertexSource, vertexTarget] using adj_source_target (1 : Fin 4)
  have r23 : (graph.connectionGraph graph.freeBoundary graph.allOpen).Reachable (2 : Fin 4) (3 : Fin 4) := by
    apply SimpleGraph.Adj.reachable
    simpa [graph, vertexSource, vertexTarget] using adj_source_target (2 : Fin 4)
  have r30 : (graph.connectionGraph graph.freeBoundary graph.allOpen).Reachable (3 : Fin 4) (0 : Fin 4) := by
    apply SimpleGraph.Adj.reachable
    simpa [graph, vertexSource, vertexTarget] using adj_source_target (3 : Fin 4)
  intro u v
  change Fin 4 at u v
  fin_cases u <;> fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact r01
  · exact r01.trans r12
  · exact r30.symm
  · exact r01.symm
  · exact SimpleGraph.Reachable.refl _
  · exact r12
  · exact r12.trans r23
  · exact (r01.trans r12).symm
  · exact r12.symm
  · exact SimpleGraph.Reachable.refl _
  · exact r23
  · exact r30
  · exact r30.trans r01
  · exact r23.symm
  · exact SimpleGraph.Reachable.refl _

/-- The exact eight-dart spherical rotation system. -/
def sphere : RotationSphere graph where
  toRotationSystem := rotationSystem
  nonemptyVertex := ⟨(0 : Fin 4)⟩
  nonemptyDart := ⟨dt 0 false⟩
  primal_preconnected := graph_preconnected
  euler := by
    change Fintype.card rotationSystem.Face + Fintype.card (Fin 4) =
      Fintype.card (Fin 4) + 2
    rw [card_face]
    decide

/-- Geometric/combinatorial incidence for the straight square. -/
noncomputable def faceEquiv : sphere.toRotationSystem.Face ≃ embedding.Face :=
  combFaceEquivBool.trans faceEquivBool.symm

/-- Arbitrary continuous Jordan parametrizations of the four straight sides.
Their ranges are contained in the prescribed segments; continuity forces range
equality by `SegmentArc.range_eq_segment_of_continuous`. -/
structure SideArcs where
  arc : Fin 4 → JordanArc Plane
  zero : ∀ e, arc e 0 = point (graph.source e)
  one : ∀ e, arc e 1 = point (graph.target e)
  range_subset : ∀ e, Set.range (arc e) ⊆ sideSet e

/-- Package side parametrizations as a range-preserving reparametrization. -/
def arcReparametrization (γ : SideArcs) : ArcReparametrization embedding where
  arc := γ.arc
  zero e := (γ.zero e).trans (arc_zero e).symm
  one e := (γ.one e).trans (arc_one e).symm
  range e := by
    calc
      Set.range (γ.arc e) = sideSet e :=
        SegmentArc.range_eq_segment_of_continuous (γ.arc e)
          (γ.zero e) (γ.one e) (γ.range_subset e) (endpoint_ne e)
      _ = Set.range (arc e) := (range_arc e).symm

/-- The unit square with arbitrary continuous parameters on its four sides. -/
def continuousEmbedding (γ : SideArcs) : FiniteArcEmbedding graph :=
  embedding.reparametrize (arcReparametrization γ)

/-- The non-affine side presentation has exactly the same polygonal carrier. -/
theorem carrier_continuousEmbedding (γ : SideArcs) :
    (continuousEmbedding γ).carrier = boundary := by
  exact (FiniteArcEmbedding.carrier_reparametrize embedding
    (arcReparametrization γ)).trans carrier_embedding

/-- Exact eight-dart spherical-rotation/actual-face incidence for arbitrary
continuous side parameters. -/
noncomputable def continuousFaceEquiv (γ : SideArcs) :
    sphere.toRotationSystem.Face ≃ (continuousEmbedding γ).Face :=
  faceEquiv.trans
    (FiniteArcEmbedding.faceEquivReparametrize embedding (arcReparametrization γ))

/-! ## Canonical cellular incidence on the square's own simple graph -/

/-- The simple graph with exactly the four square sides, represented as the
all-open free connection graph. -/
def globalGraph : SimpleGraph (Fin 4) :=
  graph.connectionGraph graph.freeBoundary graph.allOpen

/-- One of the four canonical global edges. -/
def globalEdge (e : Fin 4) : globalGraph.edgeSet :=
  ⟨s(graph.source e, graph.target e), adj_source_target e⟩

open FK.PlaneTopology.CellularSealed

/-- Exact labelled primal incidence in the square's own simple graph. -/
def primalEmbedding : FK.PlaneTopology.LabelledSimpleGraphEmbedding graph globalGraph where
  vertex := id
  label := globalEdge
  endpoint _ := rfl

/-- Literal strict-interior coverage for every face region.  This statement is
for `globalGraph` only; it makes no completeness assertion for a larger ambient
graph. -/
theorem interiorEdgeCoverage (T : Set rotationSystem.Face) :
    LabelledSimpleGraphEmbedding.InteriorEdgeCoverage primalEmbedding rotationSystem T := by
  intro u _hu z hadj
  change (graph.connectionGraph graph.freeBoundary graph.allOpen).Adj u z at hadj
  rcases hadj.2 with hfree | ⟨e, _he, hjoin⟩
  · exact (hadj.1 hfree).elim
  · change Fin 4 at e
    rcases hjoin with hst | hts
    · refine ⟨e, graph.target e, Or.inl ⟨hst.1, rfl⟩, ?_, hst.2⟩
      apply Subtype.ext
      change s(graph.source e, graph.target e) = s(u, z)
      rw [hst.1, hst.2]
    · refine ⟨e, graph.source e, Or.inr ⟨rfl, hts.2⟩, ?_, hts.1⟩
      apply Subtype.ext
      change s(graph.source e, graph.target e) = s(u, z)
      rw [hts.1, hts.2]
      exact Sym2.eq_swap

/-! ## An explicitly non-affine side presentation -/

/-- The quadratic self-map of the unit parameter interval. -/
def quadraticParam : C(I, I) where
  toFun t := ⟨t.1 ^ 2, by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [t.2.1, t.2.2,
      mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2)]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

lemma quadraticParam_injective : Function.Injective quadraticParam := by
  intro s t h
  apply Subtype.ext
  have hs : (s.1 : ℝ) ^ 2 = (t.1 : ℝ) ^ 2 := congrArg Subtype.val h
  exact (sq_eq_sq₀ s.2.1 t.2.1).mp hs

/-- Each straight side reparametrized by `t ↦ t²`. -/
def quadraticArc (e : Fin 4) : JordanArc Plane where
  toMap := (arc e).toMap.comp quadraticParam
  injective := (arc e).injective.comp quadraticParam_injective

@[simp] lemma quadraticArc_apply (e : Fin 4) (t : I) :
    quadraticArc e t = arc e (quadraticParam t) := rfl

lemma quadraticParam_zero : quadraticParam 0 = 0 := by
  apply Subtype.ext
  norm_num [quadraticParam]

lemma quadraticParam_one : quadraticParam 1 = 1 := by
  apply Subtype.ext
  norm_num [quadraticParam]

/-- A concrete non-affine continuous polygonal side presentation. -/
def quadraticSideArcs : SideArcs where
  arc := quadraticArc
  zero e := by
    rw [quadraticArc_apply, quadraticParam_zero, arc_zero]
  one e := by
    rw [quadraticArc_apply, quadraticParam_one, arc_one]
  range_subset e := by
    rintro z ⟨t, rfl⟩
    change arc e (quadraticParam t) ∈ sideSet e
    exact arc_mem_sideSet e (quadraticParam t)

/-- The quadratic presentation is genuinely non-affine on the bottom side. -/
theorem quadraticSideArcs_arc_zero_ne_arc : quadraticSideArcs.arc 0 ≠ arc 0 := by
  intro h
  let t : I := ⟨1 / 2, by norm_num⟩
  have hv := congrArg (fun γ : JordanArc Plane => γ t) h
  change quadraticArc 0 t = arc 0 t at hv
  rw [quadraticArc_apply] at hv
  have hp : quadraticParam t = t := (arc 0).injective hv
  have hpval := congrArg Subtype.val hp
  norm_num [quadraticParam, t] at hpval

/-- The explicit non-affine presentation has the same actual two-face window. -/
noncomputable def quadraticFaceEquiv :
    sphere.toRotationSystem.Face ≃ (continuousEmbedding quadraticSideArcs).Face :=
  continuousFaceEquiv quadraticSideArcs

end Square
end
end FK.PlaneTopology.Continuous.Polygonal

/-! ## Fully qualified type and axiom audit -/

#check FK.PlaneTopology.Continuous.Polygonal.Square.frontier_solid
#check FK.PlaneTopology.Continuous.Polygonal.Square.embedding
#check FK.PlaneTopology.Continuous.Polygonal.Square.carrier_embedding
#check FK.PlaneTopology.Continuous.Polygonal.Square.faceEquivBool
#check FK.PlaneTopology.Continuous.Polygonal.Square.sphere
#check FK.PlaneTopology.Continuous.Polygonal.Square.faceEquiv
#check FK.PlaneTopology.Continuous.Polygonal.Square.carrier_continuousEmbedding
#check FK.PlaneTopology.Continuous.Polygonal.Square.continuousFaceEquiv
#check FK.PlaneTopology.Continuous.Polygonal.Square.interiorEdgeCoverage
#check FK.PlaneTopology.Continuous.Polygonal.Square.quadraticSideArcs
#check FK.PlaneTopology.Continuous.Polygonal.Square.quadraticSideArcs_arc_zero_ne_arc
#check FK.PlaneTopology.Continuous.Polygonal.Square.quadraticFaceEquiv

#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.frontier_solid
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.embedding
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.carrier_embedding
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.faceEquivBool
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.isPathConnected_inside
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.isPathConnected_outside
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.isBounded_inside
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.not_isBounded_outside
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.card_face
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.graph_preconnected
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.sphere
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.faceEquiv
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.arcReparametrization
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.carrier_continuousEmbedding
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.continuousFaceEquiv
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.interiorEdgeCoverage
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.quadraticParam_injective
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.quadraticSideArcs
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.quadraticSideArcs_arc_zero_ne_arc
#print axioms FK.PlaneTopology.Continuous.Polygonal.Square.quadraticFaceEquiv
