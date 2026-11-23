import FK.JordanUnicyclicEnclosure

/-!
# Connected unicyclic windows with arbitrary bridge states

This file strengthens the concrete two-face enclosure step.  Exterior exclusion
needs only openness of the unique primal cycle; pendant/bridge labels may have
arbitrary states.  The geometric constructions below concern a connected
window, not the disjoint all-open scaled family.  They remain finite-window
results: the polygonal realization is rescaled with the radius, so no fixed
infinite connected graph, cofinal circuit exhaustion, dual nonpercolation
argument, or strong-uniqueness conclusion is claimed.  Arbitrary continuous
plane embeddings are also outside the scope; the realization and crossing
control used here are explicit.
-/

namespace FK.PlaneTopology.UnicyclicEnclosure

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

variable {G : LabelledMultigraph} (hG : UniqueCycleCertificate G)
variable (bridgeFace : G.Edge → Bool)

/-- If every label of the unique primal cycle is open, the inside dual component
cannot contain the exterior face.  Bridge labels, including their dual loops,
are completely unrestricted. -/
theorem exterior_not_mem_inside_of_cycleEdges_open (ω : G.Configuration)
    (hopen : hG.cycleEdges ⊆ G.openEdgeSet ω) :
    true ∉ insideComponent hG bridgeFace ω := by
  intro hreach
  let H : SimpleGraph Bool := (pair hG bridgeFace).faceDual.connectionGraph
    (pair hG bridgeFace).faceDual.freeBoundary
    (dualConfig (Equiv.refl G.Edge) ω)
  have hno : ¬ H.Adj false true := by
    intro hadj
    rcases hadj with ⟨hne, hfree | ⟨e, heopen, hejoin⟩⟩
    · exact (hne hfree).elim
    · by_cases heC : e ∈ hG.cycleEdges
      · have hetrue : ω e = true := hopen heC
        change (!ω e) = true at heopen
        simp [hetrue] at heopen
      · have hst : (pair hG bridgeFace).faceDual.source e =
            (pair hG bridgeFace).faceDual.target e := by
          change (if e ∈ hG.cycleEdges then false else bridgeFace e) =
            (if e ∈ hG.cycleEdges then true else bridgeFace e)
          simp [heC]
        rcases hejoin with ⟨hes, het⟩ | ⟨hes, het⟩ <;>
          rw [hes, het] at hst <;> simp at hst
  have hbot : H = ⊥ := by
    ext u v
    change Bool at u v
    cases u <;> cases v
    · simp only [SimpleGraph.bot_adj, iff_false]
      exact fun h => h.ne rfl
    · simp only [SimpleGraph.bot_adj, iff_false]
      exact hno
    · simp only [SimpleGraph.bot_adj, iff_false]
      exact fun h => hno h.symm
    · simp only [SimpleGraph.bot_adj, iff_false]
      exact fun h => h.ne rfl
  change H.Reachable false true at hreach
  rw [hbot] at hreach
  exact Bool.false_ne_true (SimpleGraph.reachable_bot.mp hreach)

/-- The exact outer-cut conclusion under cycle openness alone. -/
theorem vertexCut_insideComponent_of_cycleEdges_open (ω : G.Configuration)
    (hopen : hG.cycleEdges ⊆ G.openEdgeSet ω) :
    (pair hG bridgeFace).faceDual.vertexCut (insideComponent hG bridgeFace ω) =
      hG.cycleEdges :=
  vertexCut_insideComponent hG bridgeFace ω
    (exterior_not_mem_inside_of_cycleEdges_open hG bridgeFace ω hopen)

/-- Exterior exclusion is not merely sufficient for cycle openness: together
with the reverse implication from `JordanUnicyclicEnclosure`, it is exactly
equivalent to openness of the whole unique cycle.  Bridge states remain
arbitrary on both sides of the equivalence. -/
theorem cycleEdges_open_iff_exterior_not_mem (ω : G.Configuration) :
    hG.cycleEdges ⊆ G.openEdgeSet ω ↔
      true ∉ insideComponent hG bridgeFace ω := by
  constructor
  · exact exterior_not_mem_inside_of_cycleEdges_open hG bridgeFace ω
  · exact cycleEdges_open hG bridgeFace ω

/-- If the inside component's full vertex cut is already the distinguished
cycle, every label on that cycle is open.  This is the cut-level form of the
same saturated-component argument, and does not assume exterior exclusion. -/
theorem cycleEdges_open_of_vertexCut_eq (ω : G.Configuration)
    (hcut : (pair hG bridgeFace).faceDual.vertexCut
      (insideComponent hG bridgeFace ω) = hG.cycleEdges) :
    hG.cycleEdges ⊆ G.openEdgeSet ω := by
  intro e heC
  change ω e = true
  have hecut : e ∈ (pair hG bridgeFace).faceDual.vertexCut
      (insideComponent hG bridgeFace ω) := by
    rw [hcut]
    exact heC
  have hd := (pair hG bridgeFace).faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
    ((pair hG bridgeFace).faceDual.openComponentSaturated_openVertexComponent
      (dualConfig (Equiv.refl G.Edge) ω) false) hecut
  change (!ω e) = false at hd
  cases h : ω e <;> simp [h] at hd ⊢

/-- The exact outer-boundary alternative: the full inside vertex cut is the
unique cycle precisely when the exterior face is excluded.  In particular no
extra all-open hypothesis on pendant or bridge labels is hidden here. -/
theorem vertexCut_eq_cycleEdges_iff_exterior_not_mem (ω : G.Configuration) :
    (pair hG bridgeFace).faceDual.vertexCut
        (insideComponent hG bridgeFace ω) = hG.cycleEdges ↔
      true ∉ insideComponent hG bridgeFace ω := by
  constructor
  · intro hcut
    apply exterior_not_mem_inside_of_cycleEdges_open hG bridgeFace ω
    exact cycleEdges_open_of_vertexCut_eq hG bridgeFace ω hcut
  · exact vertexCut_insideComponent hG bridgeFace ω

/-- The spherical outer boundary is available for every configuration whose
unique cycle is open, with no hypothesis on bridge labels. -/
theorem sphericalOpenCircuit_of_cycleEdges_open
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {L : LabelledMultigraph.{0, u_2}} (hL : UniqueCycleCertificate L)
    {vertex : L.Vertex → X} (R : OpenPathRealization L.simpleGraph vertex)
    (hloop : ∀ e, L.source e ≠ L.target e) (c : X) {r : ℝ} (hr : 0 < r)
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hcross : R.CrossingControlledBy (sphere c r)
      (L.simpleLabels hloop hL.cycleEdges))
    (ω : L.Configuration) (hopen : hL.cycleEdges ⊆ L.openEdgeSet ω) :
    SphericalOpenCircuit R (L.simpleConfig hloop ω)
      (L.simpleLabels hloop hL.cycleEdges) c r :=
  sphericalOpenCircuit_insideComponent hL (fun _ => false) R hloop c hr
    hvertices hcross ω
    (exterior_not_mem_inside_of_cycleEdges_open hL (fun _ => false) ω hopen)

end FK.PlaneTopology.UnicyclicEnclosure

namespace FK.PlaneTopology.LabelledPathRealization

open Set Metric
open scoped Classical
open FK.Finite FK.Finite.LabelledMultigraph

variable {X : Type*} [TopologicalSpace X]
variable {G : LabelledMultigraph} {vertex : G.Vertex → X}

/-- A chosen simple arc with an exact labelled representative.  The
pointwise disjunction permits the reversed orientation without any dependent
path equality. -/
noncomputable def simpleArc (R : LabelledPathRealization G vertex)
    {u v : G.Vertex} (huv : G.simpleGraph.Adj u v) :
    {p : Path (vertex u) (vertex v) // ∃ e : G.Edge, G.Joins e u v ∧
      ∀ t : unitInterval, p t = R.arc e t ∨ p t = R.arc e (unitInterval.symm t)} :=
  Classical.choice (show Nonempty {p : Path (vertex u) (vertex v) // ∃ e : G.Edge,
      G.Joins e u v ∧ ∀ t : unitInterval,
        p t = R.arc e t ∨ p t = R.arc e (unitInterval.symm t)} from by
    obtain ⟨_hne, e, he⟩ := G.simpleGraph_adj_iff.mp huv
    rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · cases hs
      cases ht
      exact ⟨⟨R.arc e, ⟨e, Or.inl ⟨rfl, rfl⟩, fun _ => Or.inl rfl⟩⟩⟩
    · cases hs
      cases ht
      exact ⟨⟨(R.arc e).symm, ⟨e, Or.inr ⟨rfl, rfl⟩, fun _ => Or.inr rfl⟩⟩⟩)

/-- Forget parallel-label multiplicity in a path realization.  Every selected
arc remains an actual labelled arc, possibly reversed. -/
noncomputable def toSimple (R : LabelledPathRealization G vertex) :
    OpenPathRealization G.simpleGraph vertex where
  arc huv := (simpleArc R huv).1

/-- Every arc selected by `toSimple` stays in any locus containing all the
original labelled arcs. -/
theorem toSimple_arc_mem (R : LabelledPathRealization G vertex) (K : Set X)
    (hmem : ∀ e (t : unitInterval), R.arc e t ∈ K)
    {u v : G.Vertex} (huv : G.simpleGraph.Adj u v) (t : unitInterval) :
    R.toSimple.arc huv t ∈ K := by
  obtain ⟨e, _hejoin, he⟩ := (simpleArc R huv).2
  rcases he t with ht | ht
  · change (simpleArc R huv).1 t ∈ K
    rw [ht]
    exact hmem e t
  · change (simpleArc R huv).1 t ∈ K
    rw [ht]
    exact hmem e (unitInterval.symm t)

/-- Crossing control also descends to the simple quotient.  The image is a
label of the actual simple adjacency, not merely an edge value at one point. -/
theorem toSimple_crossingControlledBy (R : LabelledPathRealization G vertex)
    (K : Set X) (C : Set G.Edge) (hloop : ∀ e, G.source e ≠ G.target e)
    (hcross : R.CrossingControlledBy K C) :
    R.toSimple.CrossingControlledBy K (G.simpleLabels hloop C) := by
  intro u v huv hmeet
  obtain ⟨t, ht⟩ := hmeet
  obtain ⟨e, hejoin, he⟩ := (simpleArc R huv).2
  have heC : e ∈ C := by
    apply hcross e
    rcases he t with heq | heq
    · exact ⟨t, by rw [← heq]; exact ht⟩
    · exact ⟨unitInterval.symm t, by rw [← heq]; exact ht⟩
  refine ⟨e, heC, ?_⟩
  apply Subtype.ext
  rcases hejoin with ⟨hs, htgt⟩ | ⟨hs, htgt⟩
  · change s(G.source e, G.target e) = s(u, v)
    rw [hs, htgt]
  · change s(G.source e, G.target e) = s(u, v)
    rw [hs, htgt]
    exact Sym2.eq_swap

end FK.PlaneTopology.LabelledPathRealization

namespace FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon

open Set Metric unitInterval
open scoped Classical Topology
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation
open FK.PlaneTopology.UnicyclicEnclosure PolygonDigon

/-- A connected three-label window: the two-face digon with one pendant edge
attached to its east vertex. -/
abbrev oneLeafDigon : LabelledMultigraph := by
  exact attachMany twoEdgeCycle (fun _ : Fin 1 => true)

/-- The graph-theoretic unique-cycle certificate, inherited from the digon. -/
def certificate : UniqueCycleCertificate oneLeafDigon :=
  (ofIsLabelledCycle _ isLabelledCycle_twoEdgeCycle).attachMany_certificate
    (fun _ : Fin 1 => true)

/-- The underlying simple graph is connected, not a disjoint union. -/
theorem preconnected : oneLeafDigon.simpleGraph.Preconnected :=
  certificate.preconnected

/-- The old cycle labels, and no pendant label, form the distinguished cycle. -/
lemma mem_cycleEdges_iff (e : oneLeafDigon.Edge) :
    e ∈ certificate.cycleEdges ↔ ∃ c : twoEdgeCycle.Edge, e = Sum.inl c := by
  change e ∈ Sum.inl '' (Set.univ : Set twoEdgeCycle.Edge) ↔ _
  constructor
  · rintro ⟨c, _hc, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, Set.mem_univ c, rfl⟩

/-- Every labelled edge is a nonloop. -/
lemma source_ne_target (e : oneLeafDigon.Edge) :
    oneLeafDigon.source e ≠ oneLeafDigon.target e := by
  cases e with
  | inl e =>
      intro h
      exact PolygonDigon.source_ne_target e (Sum.inl.inj h)
  | inr i =>
      intro h
      have hi : (Sum.inr i : Bool ⊕ Fin 1) = Sum.inl true := h
      contradiction

/-- The original square-digon arcs stay fixed; the new pendant joins the east
core vertex to a leaf twice as far out on the horizontal axis. -/
def embeddedVertex (a : ℝ) : oneLeafDigon.Vertex → ℝ × ℝ
  | Sum.inl v => PolygonDigon.embeddedVertex a v
  | Sum.inr _ => (2 * a, 0)

/-- Actual continuous paths for every label. -/
noncomputable def labelledRealization (a : ℝ) :
    LabelledPathRealization oneLeafDigon (embeddedVertex a) where
  arc
    | Sum.inl e => (PolygonDigon.labelledRealization a).arc e
    | Sum.inr _ => straightPath (2 * a, 0) (east a)

/-- Coordinate formula for the horizontal pendant segment. -/
lemma fst_pendantArc (a : ℝ) (t : I) :
    ((straightPath (2 * a, 0) (east a) t).1) =
      (1 - (t : ℝ)) * (2 * a) + (t : ℝ) * a := by
  simp [straightPath, segmentArc_apply]
  simp [east]
  ring

/-- The pendant's first coordinate is uniformly at least its outer scale. -/
lemma le_fst_pendantArc (a : ℝ) (ha : 0 ≤ a) (t : I) :
    a ≤ ((straightPath (2 * a, 0) (east a) t).1) := by
  rw [fst_pendantArc]
  nlinarith [t.2.1, t.2.2]

/-- On the horizontal pendant segment, distance to the origin is at least the
outer scale `a`; this is a direct segment calculation. -/
lemma pendantArc_dist (a : ℝ) (ha : 0 ≤ a) (t : I) :
    a ≤ dist (straightPath (2 * a, 0) (east a) t) 0 := by
  have hx := le_fst_pendantArc a ha t
  have hx0 : 0 ≤ ((straightPath (2 * a, 0) (east a) t).1) := ha.trans hx
  rw [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hx0]
  exact hx.trans (le_max_left _ _)

/-- The pendant vertex is at distance `2*a` from the origin. -/
lemma dist_embeddedVertex_inr (a : ℝ) (ha : 0 ≤ a) (i : Fin 1) :
    dist (embeddedVertex a (Sum.inr i)) 0 = 2 * a := by
  simp [embeddedVertex, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
    abs_of_nonneg ha]
  exact ha

/-- The first coordinate is a 1-Lipschitz coordinate in the product norm. -/
lemma abs_fst_sub_le_dist (z c : ℝ × ℝ) : |z.1 - c.1| ≤ dist z c := by
  rw [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs]
  exact le_max_left _ _

/-- Exact lower distance between the two core vertices. -/
lemma two_mul_le_dist_east_west (a : ℝ) (ha : 0 ≤ a) :
    2 * a ≤ dist (east a) (west a) := by
  have h := abs_fst_sub_le_dist (east a) (west a)
  have h2 : 0 ≤ a + a := add_nonneg ha ha
  simpa [east, west, sub_neg_eq_add, abs_of_nonneg h2, two_mul] using h

/-- Exact lower distance between the pendant leaf and the west core vertex. -/
lemma three_mul_le_dist_leaf_west (a : ℝ) (ha : 0 ≤ a) (i : Fin 1) :
    3 * a ≤ dist (embeddedVertex a (Sum.inr i)) (west a) := by
  have h := abs_fst_sub_le_dist (embeddedVertex a (Sum.inr i)) (west a)
  have h3 : 0 ≤ 2 * a + a := by positivity
  simpa [embeddedVertex, west, sub_neg_eq_add, abs_of_nonneg h3,
    show 3 * a = 2 * a + a by ring] using h

/-- The entire pendant stays at distance at least `2*a` from the west core
vertex, so a sphere centred west and of radius below `2*a` misses it. -/
lemma pendantArc_dist_west (a : ℝ) (ha : 0 ≤ a) (t : I) :
    2 * a ≤ dist (straightPath (2 * a, 0) (east a) t) (west a) := by
  let z := straightPath (2 * a, 0) (east a) t
  have hx : a ≤ z.1 := le_fst_pendantArc a ha t
  have hd := abs_fst_sub_le_dist z (west a)
  have habs : |z.1 - (west a).1| = z.1 + a := by
    rw [show z.1 - (west a).1 = z.1 + a by simp [west, sub_neg_eq_add]]
    exact abs_of_nonneg (by linarith)
  rw [habs] at hd
  have htwo : 2 * a ≤ z.1 + a := by linarith
  exact htwo.trans hd

/-- Around the west core vertex, all three embedded vertices are off a sphere of
radius `r < 2*a`.  In particular the west vertex is strictly inside. -/
lemma embeddedVertex_off_west_sphere {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (har : r < 2 * a) (v : oneLeafDigon.Vertex) :
    embeddedVertex a v ∈ (sphere (west a) r)ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  cases v with
  | inl v =>
      cases v
      · change dist (west a) (west a) ≠ r
        simpa using hr.ne
      · change dist (east a) (west a) ≠ r
        have hd := two_mul_le_dist_east_west a ha
        exact ne_of_gt (lt_of_lt_of_le har hd)
  | inr i =>
      have hd := three_mul_le_dist_leaf_west a ha i
      have hra : r < 3 * a := by linarith
      exact ne_of_gt (lt_of_lt_of_le hra hd)

/-- The west core vertex is genuinely enclosed by the centred ball. -/
lemma west_mem_ball {a r : ℝ} (hr : 0 < r) :
    embeddedVertex a (Sum.inl false) ∈ ball (west a) r := by
  change dist (west a) (west a) < r
  simpa using hr

/-- Exact crossing control around west: old core labels already belong to the
cycle, and the pendant cannot meet the sphere. -/
lemma labelled_crossing_west {r : ℝ} (hr : 0 < r) :
    (labelledRealization (4 * r)).CrossingControlledBy
      (sphere (west (4 * r)) r) certificate.cycleEdges := by
  intro e he
  cases e with
  | inl c => exact (mem_cycleEdges_iff (Sum.inl c)).mpr ⟨c, rfl⟩
  | inr i =>
      exfalso
      obtain ⟨t, ht⟩ := he
      have hd := pendantArc_dist_west (4 * r) (by positivity) t
      have heq := Metric.mem_sphere.mp ht
      change dist (straightPath (2 * (4 * r), 0) (east (4 * r)) t)
        (west (4 * r)) = r at heq
      linarith

/-- Crossing control of the simple quotient around the actual enclosed west
vertex. -/
theorem crossing_west {r : ℝ} (hr : 0 < r) :
    (labelledRealization (4 * r)).toSimple.CrossingControlledBy
      (sphere (west (4 * r)) r)
      (oneLeafDigon.simpleLabels source_ne_target certificate.cycleEdges) :=
  LabelledPathRealization.toSimple_crossingControlledBy
    (labelledRealization (4 * r)) _ _ source_ne_target (labelled_crossing_west hr)

/-- At scale `4*r`, all core and pendant vertices avoid the inner sphere. -/
lemma embeddedVertex_off_sphere {r : ℝ} (hr : 0 < r)
    (v : oneLeafDigon.Vertex) :
    embeddedVertex (4 * r) v ∈ (sphere (0 : ℝ × ℝ) r)ᶜ := by
  cases v with
  | inl v => exact PolygonDigon.embeddedVertex_off_sphere hr v
  | inr i =>
      simp only [Set.mem_compl_iff, Metric.mem_sphere]
      rw [dist_embeddedVertex_inr _ (by positivity) i]
      linarith

/-- Every labelled arc avoids the inner sphere.  The two old arcs use the
square calculation; the new arc uses the horizontal-segment bound above. -/
lemma labelledArc_off_sphere {r : ℝ} (hr : 0 < r)
    (e : oneLeafDigon.Edge) (t : I) :
    (labelledRealization (4 * r)).arc e t ∈ (sphere (0 : ℝ × ℝ) r)ᶜ := by
  cases e with
  | inl e => exact PolygonDigon.labelledArc_off_sphere hr e t
  | inr i =>
      simp only [Set.mem_compl_iff, Metric.mem_sphere]
      change dist (straightPath (2 * (4 * r), 0) (east (4 * r)) t) 0 ≠ r
      have hd := pendantArc_dist (4 * r) (by positivity) t
      exact ne_of_gt (lt_of_lt_of_le (by linarith) hd)

/-- The simple-quotient realization is crossing-controlled by the selected
cycle: in fact none of its arcs meets the selected sphere at all. -/
theorem crossing {r : ℝ} (hr : 0 < r) :
    (labelledRealization (4 * r)).toSimple.CrossingControlledBy
      (sphere (0 : ℝ × ℝ) r)
      (oneLeafDigon.simpleLabels source_ne_target certificate.cycleEdges) := by
  intro u v huv hcross
  obtain ⟨t, ht⟩ := hcross
  have hoff := LabelledPathRealization.toSimple_arc_mem
    (labelledRealization (4 * r)) (sphere (0 : ℝ × ℝ) r)ᶜ
    (labelledArc_off_sphere hr) huv t
  exact (hoff ht).elim

/-- **Connected-window enclosure.**  For every configuration, openness of the
two original cycle labels enforces exterior exclusion and produces the actual
spherical primal-open circuit.  The pendant label may be open or closed. -/
theorem sphericalOpenCircuit_of_cycleEdges_open {r : ℝ} (hr : 0 < r)
    (ω : oneLeafDigon.Configuration)
    (hopen : certificate.cycleEdges ⊆ oneLeafDigon.openEdgeSet ω) :
    SphericalOpenCircuit (labelledRealization (4 * r)).toSimple
      (oneLeafDigon.simpleConfig source_ne_target ω)
      (oneLeafDigon.simpleLabels source_ne_target certificate.cycleEdges) 0 r :=
  UnicyclicEnclosure.sphericalOpenCircuit_of_cycleEdges_open certificate
    (labelledRealization (4 * r)).toSimple source_ne_target 0 hr
    (embeddedVertex_off_sphere hr) (crossing hr) ω hopen

/-- A genuinely non-all-open test configuration: both cycle labels are open,
but the unique pendant label is closed. -/
def coreOpenPendantClosed : oneLeafDigon.Configuration
  | Sum.inl _ => true
  | Sum.inr _ => false

lemma coreOpenPendantClosed_pendant (i : Fin 1) :
    coreOpenPendantClosed (Sum.inr i) = false := rfl

lemma coreOpenPendantClosed_cycle_open :
    certificate.cycleEdges ⊆ oneLeafDigon.openEdgeSet coreOpenPendantClosed := by
  intro e he
  obtain ⟨c, rfl⟩ := (mem_cycleEdges_iff e).mp he
  rfl

/-- Exterior exclusion is non-vacuous for the connected window even with the
pendant closed.  Its bridge face assignment is arbitrary. -/
theorem exterior_not_mem_inside_coreOpenPendantClosed
    (bridgeFace : oneLeafDigon.Edge → Bool) :
    true ∉ UnicyclicEnclosure.insideComponent certificate bridgeFace
      coreOpenPendantClosed :=
  UnicyclicEnclosure.exterior_not_mem_inside_of_cycleEdges_open certificate bridgeFace
    coreOpenPendantClosed coreOpenPendantClosed_cycle_open

/-- The exact vertex cut in the same mixed-state configuration. -/
theorem vertexCut_coreOpenPendantClosed
    (bridgeFace : oneLeafDigon.Edge → Bool) :
    (UnicyclicEnclosure.pair certificate bridgeFace).faceDual.vertexCut
      (UnicyclicEnclosure.insideComponent certificate bridgeFace
        coreOpenPendantClosed) = certificate.cycleEdges :=
  UnicyclicEnclosure.vertexCut_insideComponent_of_cycleEdges_open certificate bridgeFace
    coreOpenPendantClosed coreOpenPendantClosed_cycle_open

/-- The mixed-state connected window has the actual spherical circuit. -/
theorem sphericalOpenCircuit_coreOpenPendantClosed {r : ℝ} (hr : 0 < r) :
    SphericalOpenCircuit (labelledRealization (4 * r)).toSimple
      (oneLeafDigon.simpleConfig source_ne_target coreOpenPendantClosed)
      (oneLeafDigon.simpleLabels source_ne_target certificate.cycleEdges) 0 r :=
  sphericalOpenCircuit_of_cycleEdges_open hr coreOpenPendantClosed
    coreOpenPendantClosed_cycle_open

/-- The same cycle-open circuit can be centred at the west core vertex.  The
pendant is proved not to cross this sphere, and the centre itself is an
embedded graph vertex strictly inside the ball. -/
theorem sphericalOpenCircuit_west_coreOpenPendantClosed {r : ℝ} (hr : 0 < r) :
    SphericalOpenCircuit (labelledRealization (4 * r)).toSimple
      (oneLeafDigon.simpleConfig source_ne_target coreOpenPendantClosed)
      (oneLeafDigon.simpleLabels source_ne_target certificate.cycleEdges)
      (west (4 * r)) r :=
  UnicyclicEnclosure.sphericalOpenCircuit_of_cycleEdges_open certificate
    (labelledRealization (4 * r)).toSimple source_ne_target (west (4 * r)) hr
    (fun v => embeddedVertex_off_west_sphere (a := 4 * r) (r := r)
      (by positivity) hr (by linarith) v)
    (crossing_west hr) coreOpenPendantClosed coreOpenPendantClosed_cycle_open

/-- The west-centred circuit genuinely encloses the west core vertex. -/
theorem west_mem_circuit_ball {r : ℝ} (hr : 0 < r) :
    embeddedVertex (4 * r) (Sum.inl false) ∈ ball (west (4 * r)) r :=
  west_mem_ball hr

/-- The pendant leaf is strictly outside that west-centred ball. -/
theorem leaf_not_mem_west_circuit_ball {r : ℝ} (hr : 0 < r) (i : Fin 1) :
    embeddedVertex (4 * r) (Sum.inr i) ∉ ball (west (4 * r)) r := by
  change ¬ dist (embeddedVertex (4 * r) (Sum.inr i)) (west (4 * r)) < r
  have hd := three_mul_le_dist_leaf_west (4 * r) (by positivity) i
  exact not_lt_of_ge ((show r ≤ 3 * (4 * r) by linarith).trans hd)

/-- Properness on arbitrary metric balls for the connected finite window.
This is genuine finite-ball data; it is not promoted to a proper embedding of
an infinite graph. -/
theorem finite_vertex_preimage_ball {a : ℝ} (c : ℝ × ℝ) (r : ℝ) :
    (embeddedVertex a ⁻¹' ball c r).Finite :=
  Set.finite_univ.subset (Set.subset_univ _)

#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.preconnected
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.pendantArc_dist
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.labelledArc_off_sphere
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.crossing
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.sphericalOpenCircuit_of_cycleEdges_open
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.exterior_not_mem_inside_coreOpenPendantClosed
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.vertexCut_coreOpenPendantClosed
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.sphericalOpenCircuit_coreOpenPendantClosed
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.sphericalOpenCircuit_west_coreOpenPendantClosed
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.west_mem_circuit_ball
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.leaf_not_mem_west_circuit_ball
#print axioms FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon.finite_vertex_preimage_ball

end FK.PlaneTopology.UnicyclicEnclosure.ConnectedDigon

namespace FK.PlaneTopology.UnicyclicEnclosure

#print axioms FK.PlaneTopology.UnicyclicEnclosure.exterior_not_mem_inside_of_cycleEdges_open
#print axioms FK.PlaneTopology.UnicyclicEnclosure.vertexCut_insideComponent_of_cycleEdges_open
#print axioms FK.PlaneTopology.UnicyclicEnclosure.cycleEdges_open_iff_exterior_not_mem
#print axioms FK.PlaneTopology.UnicyclicEnclosure.cycleEdges_open_of_vertexCut_eq
#print axioms FK.PlaneTopology.UnicyclicEnclosure.vertexCut_eq_cycleEdges_iff_exterior_not_mem
#print axioms FK.PlaneTopology.UnicyclicEnclosure.sphericalOpenCircuit_of_cycleEdges_open
#print axioms FK.PlaneTopology.LabelledPathRealization.toSimple_arc_mem

end FK.PlaneTopology.UnicyclicEnclosure
