import FK.PrimalOpenBoundary
import FK.GlobalPrimalCompatibility
import FK.DualFiniteEnclosure
import FK.UnicyclicForest
import FK.SegmentSeparation

/-!
# Outer circuits in connected two-face unicyclic plane families

For a connected unicyclic labelled graph with its exact two-face dual, the
inside component of the dual configuration has a particularly rigid boundary.
If it does not contain the exterior face, its *whole* vertex cut is the unique
primal cycle.  In particular, that cycle is a primal-open matroid circuit.
The statement is for an arbitrary configuration; no openness of the graph is
assumed in advance.  Bridge labels are dual loops and do not enter the cut.

This is the combinatorial outer-boundary selection step.  Continuous arc and
radius data are added separately below; no general Jordan theorem is claimed.
-/

namespace FK.PlaneTopology.UnicyclicEnclosure

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid

variable {G : LabelledMultigraph} (hG : UniqueCycleCertificate G)
variable (bridgeFace : G.Edge → Bool)

/-- The labelled two-face pair associated with the unique-cycle certificate. -/
noncomputable abbrev pair : LabelledDualPair :=
  unicyclicDualPair G hG bridgeFace

/-- The component of the inside face in the actual complementary
configuration. -/
def insideComponent (ω : G.Configuration) : Set Bool :=
  (pair hG bridgeFace).faceDual.openVertexComponent
    (dualConfig (Equiv.refl G.Edge) ω) false

lemma false_mem_insideComponent (ω : G.Configuration) :
    false ∈ insideComponent hG bridgeFace ω := by
  exact SimpleGraph.Reachable.refl false

/-- The unique cycle is a matroid circuit, directly from the graph-theoretic
unique-cycle certificate. -/
theorem isCircuit_cycleEdges : G.cycleMatroid.IsCircuit hG.cycleEdges := by
  rw [Matroid.isCircuit_iff_forall_ssubset]
  constructor
  · constructor
    · rw [hG.indep_iff]
      simp
    · simp
  · intro I hI
    rw [hG.indep_iff]
    exact hI.not_subset

/-- Unicyclicity in circuit form: there are no other primal matroid circuits. -/
theorem eq_cycleEdges_of_isCircuit {C : Set G.Edge}
    (hC : G.cycleMatroid.IsCircuit C) : C = hG.cycleEdges := by
  have hsub : hG.cycleEdges ⊆ C := by
    by_contra hnot
    exact hC.not_indep ((hG.indep_iff C).mpr hnot)
  exact (hC.eq_of_dep_subset (isCircuit_cycleEdges hG).dep hsub).symm

/-- **Exact outer cut.**  Once the exterior face is excluded from the inside
component, its vertex cut is exactly the distinguished cycle.  Every bridge
is a dual loop and is excluded by the nonloop property of a vertex cut. -/
theorem vertexCut_insideComponent (ω : G.Configuration)
    (hout : true ∉ insideComponent hG bridgeFace ω) :
    (pair hG bridgeFace).faceDual.vertexCut (insideComponent hG bridgeFace ω) =
      hG.cycleEdges := by
  ext e
  change G.Edge at e
  constructor
  · intro he
    by_contra heC
    have hst : (pair hG bridgeFace).faceDual.source e =
        (pair hG bridgeFace).faceDual.target e := by
      change (if e ∈ hG.cycleEdges then false else bridgeFace e) =
        (if e ∈ hG.cycleEdges then true else bridgeFace e)
      split
      · rename_i h
        exact (heC h).elim
      · rfl
    exact (pair hG bridgeFace).faceDual.source_ne_target_of_mem_vertexCut he hst
  · intro heC
    have hfalse := false_mem_insideComponent hG bridgeFace ω
    change ((if e ∈ hG.cycleEdges then false else bridgeFace e) ∈
        insideComponent hG bridgeFace ω ∧
      (if e ∈ hG.cycleEdges then true else bridgeFace e) ∉
        insideComponent hG bridgeFace ω) ∨
      ((if e ∈ hG.cycleEdges then false else bridgeFace e) ∉
        insideComponent hG bridgeFace ω ∧
      (if e ∈ hG.cycleEdges then true else bridgeFace e) ∈
        insideComponent hG bridgeFace ω)
    split
    · exact Or.inl ⟨hfalse, hout⟩
    · rename_i h
      exact (h heC).elim

/-- Every label of the selected outer circuit is open in the original primal
configuration. -/
theorem cycleEdges_open (ω : G.Configuration)
    (hout : true ∉ insideComponent hG bridgeFace ω) :
    hG.cycleEdges ⊆ G.openEdgeSet ω := by
  intro e heC
  change ω e = true
  have hecut : e ∈ (pair hG bridgeFace).faceDual.vertexCut
      (insideComponent hG bridgeFace ω) := by
    rw [vertexCut_insideComponent hG bridgeFace ω hout]
    exact heC
  have hd := (pair hG bridgeFace).faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
    ((pair hG bridgeFace).faceDual.openComponentSaturated_openVertexComponent
      (dualConfig (Equiv.refl G.Edge) ω) false) hecut
  change (!ω e) = false at hd
  cases h : ω e <;> simp [h] at hd ⊢

/-- The selected cycle is connected by paths using only its own open labels. -/
theorem reachable_on_cycleEdges {ω : G.Configuration}
    (hout : true ∉ insideComponent hG bridgeFace ω)
    {u v : G.Vertex} (hu : G.VertexOnLabels hG.cycleEdges u)
    (hv : G.VertexOnLabels hG.cycleEdges v) :
    (G.connectionGraph G.freeBoundary ω).Reachable u v := by
  have hreach := G.reachable_of_cycleMatroid_isCircuit
    (isCircuit_cycleEdges hG) hu hv
  have hle : G.connectionGraph G.freeBoundary (G.setConfig hG.cycleEdges) ≤
      G.connectionGraph G.freeBoundary (G.setConfig (G.openEdgeSet ω)) :=
    G.connectionGraph_mono (G.setConfig_mono (cycleEdges_open hG bridgeFace ω hout))
  rw [G.setConfig_openEdgeSet] at hle
  exact hreach.mono hle

end FK.PlaneTopology.UnicyclicEnclosure

namespace FK.PlaneTopology.UnicyclicEnclosure

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : LabelledMultigraph} (hG : UniqueCycleCertificate G)
variable (bridgeFace : G.Edge → Bool)

/-- Constant-centre spherical geometry for a unicyclic family.  The only
crossing input concerns the actual unique cycle; every other circuit is then
handled by the proved circuit equality. -/
def sphericalGeometry {vertex : G.Vertex → X}
    (R : OpenPathRealization G.simpleGraph vertex)
    (hloop : ∀ e, G.source e ≠ G.target e) (c : X) {r : ℝ} (hr : 0 < r)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hcross : R.CrossingControlledBy (sphere c r)
      (G.simpleLabels hloop hG.cycleEdges)) :
    SphericalPrimalCircuitGeometry (pair hG bridgeFace) hloop R where
  centre _ := c
  radius _ := r
  radius_pos _ _ := hr
  vertex_off _ _ := hvertices
  crossing C hC := by
    change G.cycleMatroid.IsCircuit C at hC
    rw [eq_cycleEdges_of_isCircuit hG hC]
    exact hcross

omit [NormedSpace ℝ X] in
/-- **Spherical outer boundary.**  Excluding the exterior dual face gives the
unique cycle as an actual spherical primal-open circuit, not merely a matroid
circuit with an unspecified Jordan realization. -/
theorem sphericalOpenCircuit_insideComponent {vertex : G.Vertex → X}
    (R : OpenPathRealization G.simpleGraph vertex)
    (hloop : ∀ e, G.source e ≠ G.target e) (c : X) {r : ℝ} (hr : 0 < r)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hcross : R.CrossingControlledBy (sphere c r)
      (G.simpleLabels hloop hG.cycleEdges))
    (ω : G.Configuration) (hout : true ∉ insideComponent hG bridgeFace ω) :
    SphericalOpenCircuit R (G.simpleConfig hloop ω)
      (G.simpleLabels hloop hG.cycleEdges) c r := by
  let S := sphericalGeometry hG bridgeFace R hloop c hr hvertices hcross
  apply sphericalOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary
    S ω false
  · change hG.cycleEdges ⊆ (pair hG bridgeFace).faceDual.vertexCut
      (insideComponent hG bridgeFace ω)
    rw [vertexCut_insideComponent hG bridgeFace ω hout]
  · exact isCircuit_cycleEdges hG

end FK.PlaneTopology.UnicyclicEnclosure

/-!
## A concrete polygonal digon

We now discharge the geometric inputs for the two-edge cycle.  Its two
labelled arcs go around the upper and lower three sides of a square in the
sup-norm plane `ℝ × ℝ`.  At scale `a`, every point of either arc has distance
at least `a` from the origin.  Thus scale `4*r` avoids the sphere of radius
`r` and gives cofinal positive radius data.  This is an explicit two-face
example, not an assertion about arbitrary continuous embeddings.
-/
namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- A transparent straight path, used instead of unfolding a library path in
coordinate calculations. -/
noncomputable def straightPath (x y : ℝ × ℝ) : Path x y where
  toFun t := segmentArc x y (t : ℝ)
  continuous_toFun := (continuous_segmentArc x y).comp continuous_subtype_val
  source' := by simp
  target' := by simp

def west (a : ℝ) : ℝ × ℝ := (-a, 0)
def east (a : ℝ) : ℝ × ℝ := (a, 0)
def northWest (a : ℝ) : ℝ × ℝ := (-a, a)
def northEast (a : ℝ) : ℝ × ℝ := (a, a)
def southWest (a : ℝ) : ℝ × ℝ := (-a, -a)
def southEast (a : ℝ) : ℝ × ℝ := (a, -a)

/-- Upper three sides of the square, from the west to the east vertex. -/
noncomputable def upperArc (a : ℝ) : Path (west a) (east a) :=
  ((straightPath (west a) (northWest a)).trans
    (straightPath (northWest a) (northEast a))).trans
    (straightPath (northEast a) (east a))

/-- Lower three sides of the square, from the west to the east vertex. -/
noncomputable def lowerArc (a : ℝ) : Path (west a) (east a) :=
  ((straightPath (west a) (southWest a)).trans
    (straightPath (southWest a) (southEast a))).trans
    (straightPath (southEast a) (east a))

lemma le_dist_zero_of_abs_fst {z : ℝ × ℝ} {a : ℝ} (hz : |z.1| = a) :
    a ≤ dist z 0 := by
  rw [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, ← hz]
  exact le_max_left _ _

lemma le_dist_zero_of_abs_snd {z : ℝ × ℝ} {a : ℝ} (hz : |z.2| = a) :
    a ≤ dist z 0 := by
  rw [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, ← hz]
  exact le_max_right _ _

lemma fst_straightPath (a x y : ℝ) (t : I) :
    ((straightPath ((a, x) : ℝ × ℝ) (a, y)) t).1 = a := by
  simp [straightPath, segmentArc_apply]

lemma snd_straightPath (a x y : ℝ) (t : I) :
    ((straightPath ((x, a) : ℝ × ℝ) (y, a)) t).2 = a := by
  simp [straightPath, segmentArc_apply]

lemma abs_fst_le_dist_straightPath (a x y : ℝ) (t : I) :
    |a| ≤ dist ((straightPath ((a, x) : ℝ × ℝ) (a, y)) t) 0 := by
  apply le_dist_zero_of_abs_fst
  rw [fst_straightPath]

lemma abs_snd_le_dist_straightPath (a x y : ℝ) (t : I) :
    |a| ≤ dist ((straightPath ((x, a) : ℝ × ℝ) (y, a)) t) 0 := by
  apply le_dist_zero_of_abs_snd
  rw [snd_straightPath]

/-- Every point of the upper polygonal arc is at distance at least the outer
scale from the origin. -/
theorem upperArc_dist (a : ℝ) (ha : 0 ≤ a) (t : I) :
    a ≤ dist (upperArc a t) 0 := by
  have hmem : upperArc a t ∈ Set.range (upperArc a) := Set.mem_range_self t
  simp only [upperArc] at hmem ⊢
  rw [Path.trans_range, Path.trans_range] at hmem
  rcases hmem with (⟨u, hu⟩ | ⟨u, hu⟩) | ⟨u, hu⟩
  · rw [← hu]
    have hbound := abs_fst_le_dist_straightPath (-a) 0 a u
    rw [abs_neg, abs_of_nonneg ha] at hbound
    exact hbound
  · rw [← hu]
    have hbound := abs_snd_le_dist_straightPath a (-a) a u
    rw [abs_of_nonneg ha] at hbound
    exact hbound
  · rw [← hu]
    have hbound := abs_fst_le_dist_straightPath a a 0 u
    rw [abs_of_nonneg ha] at hbound
    exact hbound

/-- Every point of the lower polygonal arc is at distance at least the outer
scale from the origin. -/
theorem lowerArc_dist (a : ℝ) (ha : 0 ≤ a) (t : I) :
    a ≤ dist (lowerArc a t) 0 := by
  have hmem : lowerArc a t ∈ Set.range (lowerArc a) := Set.mem_range_self t
  simp only [lowerArc] at hmem ⊢
  rw [Path.trans_range, Path.trans_range] at hmem
  rcases hmem with (⟨u, hu⟩ | ⟨u, hu⟩) | ⟨u, hu⟩
  · rw [← hu]
    have hbound := abs_fst_le_dist_straightPath (-a) 0 (-a) u
    rw [abs_neg, abs_of_nonneg ha] at hbound
    exact hbound
  · rw [← hu]
    have hbound := abs_snd_le_dist_straightPath (-a) (-a) a u
    rw [abs_neg, abs_of_nonneg ha] at hbound
    exact hbound
  · rw [← hu]
    have hbound := abs_fst_le_dist_straightPath a (-a) 0 u
    rw [abs_of_nonneg ha] at hbound
    exact hbound

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- The graph-theoretic certificate of the two-edge cycle. -/
noncomputable def certificate : UniqueCycleCertificate twoEdgeCycle :=
  ofIsLabelledCycle _ isLabelledCycle_twoEdgeCycle

/-- The two-face pair used below; there are no bridge labels. -/
noncomputable abbrev dualPair : LabelledDualPair :=
  UnicyclicEnclosure.pair certificate (fun _ : twoEdgeCycle.Edge => false)

lemma certificate_cycleEdges : certificate.cycleEdges = (Set.univ : Set twoEdgeCycle.Edge) :=
  rfl

lemma source_ne_target (e : twoEdgeCycle.Edge) :
    twoEdgeCycle.source e ≠ twoEdgeCycle.target e :=
  Bool.false_ne_true

theorem graphicDualCertificate : dualPair.GraphicDualCertificate :=
  unicyclicDualPair_graphicDualCertificate _ certificate (fun _ => false)

/-- Geometric positions of the two primal vertices. -/
def embeddedVertex (a : ℝ) : twoEdgeCycle.Vertex → ℝ × ℝ
  | false => west a
  | true => east a

lemma dist_embeddedVertex (a : ℝ) (ha : 0 ≤ a) (v : twoEdgeCycle.Vertex) :
    dist (embeddedVertex a v) 0 = a := by
  cases v <;>
    simp [embeddedVertex, west, east, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, abs_of_nonneg ha, max_eq_left ha]

/-- Both labelled edges retain their own polygonal arc. -/
noncomputable def labelledRealization (a : ℝ) :
    LabelledPathRealization twoEdgeCycle (embeddedVertex a) where
  arc
    | false => upperArc a
    | true => lowerArc a

/-- The simple quotient has one bond, realized by the upper polygonal arc. -/
noncomputable def simpleRealization (a : ℝ) :
    OpenPathRealization twoEdgeCycle.simpleGraph (embeddedVertex a) where
  arc := by
    intro u v huv
    have hcases : (u = false ∧ v = true) ∨ (u = true ∧ v = false) := by
      rcases (twoEdgeCycle.simpleGraph_adj_iff).mp huv with ⟨_hne, e, he⟩
      rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨hs.symm, ht.symm⟩
      · exact Or.inr ⟨ht.symm, hs.symm⟩
    by_cases h : u = false ∧ v = true
    · rw [h.1, h.2]
      exact upperArc a
    · have h' := hcases.resolve_left h
      rw [h'.1, h'.2]
      exact (upperArc a).symm

lemma upperArc_off_sphere {r : ℝ} (hr : 0 < r) (t : I) :
    upperArc (4 * r) t ∈ (sphere (0 : ℝ × ℝ) r)ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  have hd := upperArc_dist (4 * r) (by positivity) t
  exact ne_of_gt (lt_of_lt_of_le (by linarith) hd)

lemma lowerArc_off_sphere {r : ℝ} (hr : 0 < r) (t : I) :
    lowerArc (4 * r) t ∈ (sphere (0 : ℝ × ℝ) r)ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  have hd := lowerArc_dist (4 * r) (by positivity) t
  exact ne_of_gt (lt_of_lt_of_le (by linarith) hd)

/-- Actual avoidance for each of the two labelled arcs at cofinal scale. -/
theorem labelledArc_off_sphere {r : ℝ} (hr : 0 < r) (e : twoEdgeCycle.Edge)
    (t : I) : (labelledRealization (4 * r)).arc e t ∈ (sphere (0 : ℝ × ℝ) r)ᶜ := by
  cases e
  · exact upperArc_off_sphere hr t
  · exact lowerArc_off_sphere hr t

lemma embeddedVertex_off_sphere {r : ℝ} (hr : 0 < r) (v : twoEdgeCycle.Vertex) :
    embeddedVertex (4 * r) v ∈ (sphere (0 : ℝ × ℝ) r)ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  rw [dist_embeddedVertex _ (by positivity : 0 ≤ 4 * r)]
  linarith

/-- Every simple edge is represented by a label of the distinguished cycle. -/
theorem simpleLabels_cycle_eq_univ :
    twoEdgeCycle.simpleLabels source_ne_target certificate.cycleEdges =
      (Set.univ : Set twoEdgeCycle.simpleGraph.edgeSet) := by
  apply Set.eq_univ_of_forall
  rintro ⟨z, hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro u v huv
  rcases (twoEdgeCycle.simpleGraph_adj_iff).mp huv with ⟨_hne, e, he⟩
  refine ⟨e, ?_, ?_⟩
  · rw [certificate_cycleEdges]
    exact Set.mem_univ e
  · apply Subtype.ext
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

/-- Crossing control is therefore exact on the simple quotient. -/
theorem crossing_cycle (r : ℝ) :
    (simpleRealization (4 * r)).CrossingControlledBy (sphere (0 : ℝ × ℝ) r)
      (twoEdgeCycle.simpleLabels source_ne_target certificate.cycleEdges) := by
  intro u v huv _hcross
  rw [simpleLabels_cycle_eq_univ]
  exact Set.mem_univ _

/-- If both primal labels are open, the complementary graph has no open edge,
so its inside component cannot reach the exterior face. -/
theorem exterior_not_mem_inside_allOpen :
    true ∉ UnicyclicEnclosure.insideComponent certificate (fun _ => false)
      twoEdgeCycle.allOpen := by
  intro htrue
  change (dualPair.faceDual.connectionGraph dualPair.faceDual.freeBoundary
    (dualConfig (Equiv.refl dualPair.faceDual.Edge) twoEdgeCycle.allOpen)).Reachable
      false true at htrue
  have hcfg : dualConfig (Equiv.refl dualPair.faceDual.Edge) twoEdgeCycle.allOpen =
      dualPair.faceDual.allClosed := by
    funext e
    rfl
  rw [hcfg, connectionGraph_free_allClosed] at htrue
  have heq := SimpleGraph.reachable_bot.mp htrue
  exact Bool.false_ne_true heq

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- The actual spherical open circuit of the all-open digon at scale `4*r`. -/
theorem sphericalOpenCircuit_allOpen {r : ℝ} (hr : 0 < r) :
    SphericalOpenCircuit (simpleRealization (4 * r))
      (twoEdgeCycle.simpleConfig source_ne_target twoEdgeCycle.allOpen)
      (twoEdgeCycle.simpleLabels source_ne_target certificate.cycleEdges) 0 r := by
  exact UnicyclicEnclosure.sphericalOpenCircuit_insideComponent certificate (fun _ => false)
    (simpleRealization (4 * r)) source_ne_target 0 hr (embeddedVertex_off_sphere hr)
    (crossing_cycle r) twoEdgeCycle.allOpen exterior_not_mem_inside_allOpen

/-- Cofinal positive-radius instances.  The realization scale varies with the
radius here; this is not yet an exhaustion of one fixed infinite graph. -/
theorem exists_sphericalOpenCircuit_gt (ρ : ℝ) :
    ∃ r : ℝ, ρ < r ∧
      SphericalOpenCircuit (simpleRealization (4 * r))
        (twoEdgeCycle.simpleConfig source_ne_target twoEdgeCycle.allOpen)
        (twoEdgeCycle.simpleLabels source_ne_target certificate.cycleEdges) 0 r := by
  let r := max (ρ + 1) 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hρ : ρ < r := lt_of_lt_of_le (lt_add_one ρ) (le_max_left _ _)
  exact ⟨r, hρ, sphericalOpenCircuit_allOpen hr⟩

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- Convexity gives the matching upper bound on a straight segment when both
endpoints lie in a closed ball. -/
lemma dist_straightPath_le {x y : ℝ × ℝ} {a : ℝ}
    (hx : dist x 0 ≤ a) (hy : dist y 0 ≤ a) (t : I) :
    dist (straightPath x y t) 0 ≤ a := by
  change dist (segmentArc x y (t : ℝ)) 0 ≤ a
  have hconv := (convexOn_univ_dist (0 : ℝ × ℝ)).2 (Set.mem_univ x) (Set.mem_univ y)
    (sub_nonneg.mpr t.2.2) t.2.1 (by ring)
  rw [segmentArc, AffineMap.lineMap_apply_module]
  calc
    dist ((1 - (t : ℝ)) • x + (t : ℝ) • y) 0 ≤
        (1 - (t : ℝ)) * dist x 0 + (t : ℝ) * dist y 0 := by
      simpa only [smul_eq_mul] using hconv
    _ ≤ (1 - (t : ℝ)) * a + (t : ℝ) * a := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr t.2.2)
      · exact mul_le_mul_of_nonneg_left hy t.2.1
    _ = a := by ring

lemma upperArc_dist_le (a : ℝ) (ha : 0 ≤ a) (t : I) :
    dist (upperArc a t) 0 ≤ a := by
  have hmem : upperArc a t ∈ Set.range (upperArc a) := Set.mem_range_self t
  simp only [upperArc] at hmem ⊢
  rw [Path.trans_range, Path.trans_range] at hmem
  rcases hmem with (⟨u, hu⟩ | ⟨u, hu⟩) | ⟨u, hu⟩
  · rw [← hu]
    apply dist_straightPath_le <;> simp [west, northWest, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg ha, max_eq_left ha]
  · rw [← hu]
    apply dist_straightPath_le <;> simp [northWest, northEast, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg ha]
  · rw [← hu]
    apply dist_straightPath_le <;> simp [northEast, east, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg ha, max_eq_left ha]

lemma lowerArc_dist_le (a : ℝ) (ha : 0 ≤ a) (t : I) :
    dist (lowerArc a t) 0 ≤ a := by
  have hmem : lowerArc a t ∈ Set.range (lowerArc a) := Set.mem_range_self t
  simp only [lowerArc] at hmem ⊢
  rw [Path.trans_range, Path.trans_range] at hmem
  rcases hmem with (⟨u, hu⟩ | ⟨u, hu⟩) | ⟨u, hu⟩
  · rw [← hu]
    apply dist_straightPath_le <;> simp [west, southWest, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg ha, max_eq_left ha]
  · rw [← hu]
    apply dist_straightPath_le <;> simp [southWest, southEast, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg ha]
  · rw [← hu]
    apply dist_straightPath_le <;> simp [southEast, east, dist_zero_right,
      Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg ha, max_eq_left ha]

/-- The upper digon arc lies exactly on the outer sup-norm sphere. -/
theorem upperArc_dist_eq (a : ℝ) (ha : 0 ≤ a) (t : I) :
    dist (upperArc a t) 0 = a :=
  le_antisymm (upperArc_dist_le a ha t) (upperArc_dist a ha t)

/-- The lower digon arc lies exactly on the outer sup-norm sphere. -/
theorem lowerArc_dist_eq (a : ℝ) (ha : 0 ≤ a) (t : I) :
    dist (lowerArc a t) 0 = a :=
  le_antisymm (lowerArc_dist_le a ha t) (lowerArc_dist a ha t)

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

/-!
## A fixed infinite scaled disjoint union

The preceding finite examples assemble into one fixed graph on
`ℕ × twoEdgeCycle.Vertex`.  Component `n` has outer scale `4*(n+1)` and the
circuit at radius `n+1/2` is selected from that component.  Since every arc lies
exactly on its own outer sphere, no arc meets the selected smaller sphere.
This gives a genuine `HasOpenCircuitExhaustion` for one fixed realization and
all-open configuration.  The graph is deliberately a disjoint union: no claim
is made for a general connected graph or from dual nonpercolation.
-/

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- Infinite disjoint union of the simple quotients of the digons. -/
def graph : SimpleGraph (ℕ × twoEdgeCycle.Vertex) where
  Adj x y := x.1 = y.1 ∧ twoEdgeCycle.simpleGraph.Adj x.2 y.2
  symm := ⟨by
    intro x y hxy
    exact ⟨hxy.1.symm, hxy.2.symm⟩⟩
  loopless := ⟨by
    intro x hxx
    exact hxx.2.ne rfl⟩

/-- Outer scale of component `n`. -/
def scale (n : ℕ) : ℝ := 4 * (n + 1)

lemma scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

lemma scale_nonneg (n : ℕ) : 0 ≤ scale n := (scale_pos n).le

/-- Fixed geometric embedding of all the components. -/
def vertex (x : ℕ × twoEdgeCycle.Vertex) : ℝ × ℝ :=
  embeddedVertex (scale x.1) x.2

lemma dist_vertex (x : ℕ × twoEdgeCycle.Vertex) : dist (vertex x) 0 = scale x.1 := by
  exact dist_embeddedVertex _ (scale_nonneg x.1) x.2

/-- Inclusion of component `n`. -/
def graphHom (n : ℕ) : twoEdgeCycle.simpleGraph →g graph where
  toFun := Prod.mk n
  map_rel' h := ⟨rfl, h⟩

/-- Fixed upper-arc realization.  Reverse adjacencies use the reversed upper
arc; all component and endpoint equalities are proved from graph adjacency. -/
noncomputable def realization : OpenPathRealization graph vertex where
  arc := by
    rintro ⟨n, u⟩ ⟨m, v⟩ hxy
    have hnm : n = m := hxy.1
    subst m
    cases u <;> cases v
    · exact (hxy.2.ne rfl).elim
    · exact upperArc (scale n)
    · exact (upperArc (scale n)).symm
    · exact (hxy.2.ne rfl).elim

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- Every global arc lies on the outer sphere of its source component. -/
theorem dist_realization_arc {x y : ℕ × twoEdgeCycle.Vertex} (hxy : graph.Adj x y)
    (t : I) : dist (realization.arc hxy t) 0 = scale x.1 := by
  rcases x with ⟨n, u⟩
  rcases y with ⟨m, v⟩
  have hnm : n = m := hxy.1
  subst m
  cases u <;> cases v
  · exact (hxy.2.ne rfl).elim
  · exact upperArc_dist_eq (scale n) (scale_nonneg n) t
  · change dist (upperArc (scale n) (unitInterval.symm t)) 0 = scale n
    exact upperArc_dist_eq (scale n) (scale_nonneg n) (unitInterval.symm t)
  · exact (hxy.2.ne rfl).elim

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- Half-integral selected radii avoid every integral multiple-of-four outer
scale. -/
noncomputable def radius (n : ℕ) : ℝ := n + 1 / 2

lemma radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

lemma scale_ne_radius (m n : ℕ) : scale m ≠ radius n := by
  intro h
  have heq : ((2 * n : ℕ) : ℝ) = ((8 * m + 7 : ℕ) : ℝ) := by
    push_cast
    dsimp [scale, radius] at h
    nlinarith [h]
  have heqnat : 2 * n = 8 * m + 7 := by exact_mod_cast heq
  omega

/-- Endpoint-preserving inclusion of the actual labelled digon in component
`n`; parallel-labelled collapse uses the graph homomorphism edge map. -/
def localEmbedding (n : ℕ) : LabelledSimpleGraphEmbedding twoEdgeCycle graph where
  vertex := Prod.mk n
  label e := (graphHom n).mapEdgeSet (twoEdgeCycle.simpleEdge source_ne_target e)
  endpoint _e := rfl

/-- The all-open configuration of the fixed global graph. -/
def allOpen : graph.edgeSet → Bool := fun _ => true

/-- Every global vertex is off the selected sphere. -/
theorem vertex_off (n : ℕ) (x : ℕ × twoEdgeCycle.Vertex) :
    vertex x ∈ (sphere (0 : ℝ × ℝ) (radius n))ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  rw [dist_vertex]
  exact scale_ne_radius x.1 n

/-- No realized arc at any component scale meets the selected half-integral
sphere, so crossing control is genuine rather than vacuous by assertion. -/
theorem crossing (n : ℕ) :
    realization.CrossingControlledBy (sphere (0 : ℝ × ℝ) (radius n))
      ((localEmbedding n).globalLabels certificate.cycleEdges) := by
  intro x y hxy hcross
  obtain ⟨t, ht⟩ := hcross
  have heq : scale x.1 = radius n := by
    rw [← dist_realization_arc hxy t]
    exact Metric.mem_sphere.mp ht
  exact (scale_ne_radius x.1 n heq).elim

/-- The selected globalized unique cycle is an actual spherical open circuit
of the fixed infinite graph and fixed all-open configuration. -/
theorem sphericalOpenCircuit (n : ℕ) :
    SphericalOpenCircuit realization allOpen
      ((localEmbedding n).globalLabels certificate.cycleEdges) 0 (radius n) := by
  apply (localEmbedding n).sphericalOpenCircuit_global_of_cycleMatroid_isCircuit
    (radius_pos n) (crossing n) (vertex_off n)
  · intro e _he
    rfl
  · exact UnicyclicEnclosure.isCircuit_cycleEdges certificate

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

/-- Half-integral radii are cofinal, so the fixed graph has an actual open
spherical circuit exhaustion. -/
theorem hasOpenCircuitExhaustion : HasOpenCircuitExhaustion realization allOpen 0 := by
  intro ρ
  obtain ⟨n, hn⟩ := exists_nat_gt ρ
  refine ⟨(localEmbedding n).globalLabels certificate.cycleEdges, radius n, ?_,
    sphericalOpenCircuit n⟩
  dsimp [radius]
  nlinarith [hn]

/-- The fixed embedding is proper on metric balls: if a vertex lies in the
ball of radius `r`, its integer component index is bounded by `⌈r⌉₊`, and each
component has only the two Boolean vertices. -/
theorem finite_vertex_preimage_ball (r : ℝ) : (vertex ⁻¹' ball 0 r).Finite := by
  let N := ⌈r⌉₊
  have hindices : {n : ℕ | scale n < r} ⊆ Iio N := by
    intro n hn
    have hnreal : (n : ℝ) < r := by
      have hlt : (n : ℝ) < scale n := by
        dsimp [scale]
        have hnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      exact hlt.trans hn
    exact Nat.lt_ceil.mpr hnreal
  have hfin : ({n : ℕ | scale n < r} ×ˢ
      (Set.univ : Set twoEdgeCycle.Vertex)).Finite :=
    ((Set.finite_Iio N).subset hindices).prod Set.finite_univ
  apply hfin.subset
  rintro ⟨n, v⟩ hx
  refine ⟨?_, Set.mem_univ v⟩
  change dist (vertex (n, v)) 0 < r at hx
  rw [dist_vertex] at hx
  exact hx

/-- The complete geometric uniqueness conclusion for this explicit fixed
all-open disjoint-union configuration. -/
theorem globalAtMostOne :
    FK.InfiniteVolume.ConventionTransport.GlobalAtMostOne graph allOpen := by
  exact globalAtMostOne_of_openCircuitExhaustion realization allOpen 0
    finite_vertex_preimage_ball hasOpenCircuitExhaustion

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily

#print axioms FK.PlaneTopology.UnicyclicEnclosure.isCircuit_cycleEdges
#print axioms FK.PlaneTopology.UnicyclicEnclosure.eq_cycleEdges_of_isCircuit
#print axioms FK.PlaneTopology.UnicyclicEnclosure.vertexCut_insideComponent
#print axioms FK.PlaneTopology.UnicyclicEnclosure.cycleEdges_open
#print axioms FK.PlaneTopology.UnicyclicEnclosure.reachable_on_cycleEdges
#print axioms FK.PlaneTopology.UnicyclicEnclosure.sphericalGeometry
#print axioms FK.PlaneTopology.UnicyclicEnclosure.sphericalOpenCircuit_insideComponent
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.upperArc_dist
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.lowerArc_dist
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.upperArc_dist_eq
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.lowerArc_dist_eq
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.graphicDualCertificate
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.labelledArc_off_sphere
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.exterior_not_mem_inside_allOpen
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.sphericalOpenCircuit_allOpen
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.dist_realization_arc
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.scale_ne_radius
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.localEmbedding
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.crossing
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.sphericalOpenCircuit
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.hasOpenCircuitExhaustion
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.finite_vertex_preimage_ball
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.ScaledFamily.globalAtMostOne

namespace FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open FK.PlaneTopology.DualExhaustion

/-- In the concrete two-face digon, whenever the exterior face is excluded,
the actual simple-graph `DualExhaustion.edgeCut` of the inside component is
all simple dual edges. -/
theorem edgeCut_insideComponent_eq_univ (ω : twoEdgeCycle.Configuration)
    (hout : true ∉ UnicyclicEnclosure.insideComponent certificate (fun _ => false) ω) :
    edgeCut dualPair.faceDual.simpleGraph
      (UnicyclicEnclosure.insideComponent certificate (fun _ => false) ω) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨z, hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro u v huv
  change Bool at u v
  have hfalse := UnicyclicEnclosure.false_mem_insideComponent certificate (fun _ => false) ω
  have hadj : dualPair.faceDual.simpleGraph.Adj u v := huv
  cases u <;> cases v
  · exact (hadj.ne rfl).elim
  · exact ⟨false, hfalse, true, hout, hadj, rfl⟩
  · exact ⟨false, hfalse, true, hout, hadj.symm, Sym2.eq_swap⟩
  · exact (hadj.ne rfl).elim

lemma dual_source_ne_target (e : dualPair.faceDual.Edge) :
    dualPair.faceDual.source e ≠ dualPair.faceDual.target e := by
  change twoEdgeCycle.Edge at e
  simp [dualPair, UnicyclicEnclosure.pair, unicyclicDualPair,
    LabelledDualPair.faceDual, certificate_cycleEdges]

/-- The same exact quotient representation on the face-dual graph. -/
theorem simpleLabels_faceDual_cycle_eq_univ :
    dualPair.faceDual.simpleLabels dual_source_ne_target certificate.cycleEdges =
      (Set.univ : Set dualPair.faceDual.simpleGraph.edgeSet) := by
  apply Set.eq_univ_of_forall
  rintro ⟨z, hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro u v huv
  rcases (dualPair.faceDual.simpleGraph_adj_iff).mp huv with ⟨_hne, e, he⟩
  refine ⟨e, ?_, ?_⟩
  · rw [certificate_cycleEdges]
    exact Set.mem_univ e
  · apply Subtype.ext
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

/-- The concrete primal-open circuit therefore lies exactly in the integrated
finite-enclosure cut, rather than only in a separately defined labelled cut. -/
theorem simpleLabels_cycle_eq_edgeCut (ω : twoEdgeCycle.Configuration)
    (hout : true ∉ UnicyclicEnclosure.insideComponent certificate (fun _ => false) ω) :
    dualPair.faceDual.simpleLabels dual_source_ne_target certificate.cycleEdges =
      edgeCut dualPair.faceDual.simpleGraph
        (UnicyclicEnclosure.insideComponent certificate (fun _ => false) ω) := by
  rw [edgeCut_insideComponent_eq_univ ω hout]
  exact simpleLabels_faceDual_cycle_eq_univ

end FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.edgeCut_insideComponent_eq_univ
#print axioms FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon.simpleLabels_cycle_eq_edgeCut
