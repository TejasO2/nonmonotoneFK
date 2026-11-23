import FK.PrimalOpenBoundary

/-!
# Finite labelled circuits in a prescribed global plane-dual pair

The finite theorem in `FK.PrimalOpenBoundary` produces circuits on the simple
quotient of a finite labelled multigraph.  This file transports those circuits
to an already prescribed global simple graph and its prescribed dual edge
equivalence.  Local labels are mapped, rather than assumed to form a global
simple-edge subtype: distinct parallel labels may therefore have the same
image.  The local configuration is the restriction of the global one, so all
representatives of a collapsed edge have the same state.
-/

namespace FK.PlaneTopology

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

/-- An exact endpoint-preserving embedding of a finite labelled multigraph in
an arbitrary global simple graph.  Neither the vertex map nor the label map is
assumed injective.  In particular this includes quotienting parallel labels. -/
structure LabelledSimpleGraphEmbedding {V : Type*}
    (L : LabelledMultigraph) (G : SimpleGraph V) where
  vertex : L.Vertex → V
  label : L.Edge → G.edgeSet
  endpoint : ∀ e, s(vertex (L.source e), vertex (L.target e)) = (label e : Sym2 V)

namespace LabelledSimpleGraphEmbedding

variable {V : Type*} {L : LabelledMultigraph} {G : SimpleGraph V}
variable (B : LabelledSimpleGraphEmbedding L G)

/-- The local configuration induced by a global configuration. -/
def restriction (ω : G.edgeSet → Bool) : L.Configuration :=
  fun e => ω (B.label e)

/-- Global simple edges carrying a set of local labels. -/
def globalLabels (C : Set L.Edge) : Set G.edgeSet := B.label '' C

lemma adj_source_target (e : L.Edge) :
    G.Adj (B.vertex (L.source e)) (B.vertex (L.target e)) := by
  change s(B.vertex (L.source e), B.vertex (L.target e)) ∈ G.edgeSet
  rw [B.endpoint e]
  exact (B.label e).2

include B in
lemma source_ne_target (e : L.Edge) : L.source e ≠ L.target e := by
  intro hst
  have h := B.adj_source_target e
  rw [hst] at h
  exact h.ne rfl

lemma label_eq_canonical (e : L.Edge) :
    B.label e = ⟨s(B.vertex (L.source e), B.vertex (L.target e)),
      B.adj_source_target e⟩ := by
  apply Subtype.ext
  exact (B.endpoint e).symm

/-- Collapsing two local labels to the same quotient simple edge also
collapses their prescribed global labels.  No vertex injectivity is needed. -/
lemma label_eq_of_simpleEdge_eq {a b : L.Edge}
    (h : L.simpleEdge B.source_ne_target a = L.simpleEdge B.source_ne_target b) :
    B.label a = B.label b := by
  apply Subtype.ext
  rw [← B.endpoint a, ← B.endpoint b]
  have hmap := congrArg
    (fun ε : L.simpleGraph.edgeSet => Sym2.map B.vertex (ε : Sym2 L.Vertex)) h
  change s(B.vertex (L.source a), B.vertex (L.target a)) =
    s(B.vertex (L.source b), B.vertex (L.target b)) at hmap
  exact hmap

/-- With an injective vertex embedding, equality of global labels is exactly
parallel collapse in the finite labelled graph. -/
lemma simpleEdge_eq_of_label_eq (hinj : Function.Injective B.vertex)
    {a b : L.Edge} (h : B.label a = B.label b) :
    L.simpleEdge B.source_ne_target a = L.simpleEdge B.source_ne_target b := by
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  rw [← B.endpoint a, ← B.endpoint b] at h'
  rcases Sym2.eq_iff.mp h' with hst | hst
  · exact Sym2.eq_iff.mpr (Or.inl ⟨hinj hst.1, hinj hst.2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨hinj hst.1, hinj hst.2⟩)

/-- The quotient simple configuration at a represented edge agrees exactly
with the original global configuration.  This is the compatibility step that
makes the disjunction over parallel representatives harmless. -/
lemma simpleConfig_simpleEdge_eq_true_iff (ω : G.edgeSet → Bool) (e : L.Edge) :
    L.simpleConfig B.source_ne_target (B.restriction ω)
        (L.simpleEdge B.source_ne_target e) = true ↔
      ω (B.label e) = true := by
  rw [L.simpleConfig_eq_true_iff]
  constructor
  · rintro ⟨a, ha, hae⟩
    change ω (B.label a) = true at ha
    rwa [B.label_eq_of_simpleEdge_eq hae] at ha
  · intro he
    exact ⟨e, he, rfl⟩

lemma globalLabels_open {ω : G.edgeSet → Bool} {C : Set L.Edge}
    (hC : C ⊆ L.openEdgeSet (B.restriction ω)) :
    ∀ ε ∈ B.globalLabels C, ω ε = true := by
  rintro ε ⟨e, heC, rfl⟩
  exact hC heC

end LabelledSimpleGraphEmbedding

/-- Finite primal and face-dual embeddings compatible with a prescribed global
edge equivalence.  The dual label map is definitionally determined by the
primal one through `label_comm`, rather than by a second unrelated pairing. -/
structure LabelledDualPairEmbedding {V F : Type*}
    (P : LabelledDualPair) (G : SimpleGraph V) (GD : SimpleGraph F)
    (edge : G.edgeSet ≃ GD.edgeSet) where
  primal : LabelledSimpleGraphEmbedding P.primal G
  dual : LabelledSimpleGraphEmbedding P.faceDual GD
  label_comm : ∀ e, dual.label e = edge (primal.label e)

namespace LabelledDualPairEmbedding

variable {V F : Type*} {P : LabelledDualPair} {G : SimpleGraph V}
variable {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
variable (B : LabelledDualPairEmbedding P G GD edge)

/-- Restriction of the global primal configuration to local labels. -/
abbrev primalRestriction (ω : G.edgeSet → Bool) : P.primal.Configuration :=
  B.primal.restriction ω

/-- The local face-dual configuration used by the finite boundary theorem. -/
def dualRestriction (ω : G.edgeSet → Bool) : P.faceDual.Configuration :=
  dualConfig (Equiv.refl P.Edge) (B.primalRestriction ω)

/-- At every local label, the finite dual configuration is exactly the
restriction of the prescribed global dual configuration. -/
lemma dualRestriction_apply (ω : G.edgeSet → Bool) (e : P.Edge) :
    B.dualRestriction ω e = dualConfig edge ω (B.dual.label e) := by
  change (!ω (B.primal.label e)) = (!ω (edge.symm (B.dual.label e)))
  rw [B.label_comm e]
  simp


end LabelledDualPairEmbedding

/-- The existing global finite-box data is an embedding of its actual finite
labelled graph.  This constructor keeps the edge subtype and its endpoint
identity; it does not rebuild or relabel the box. -/
def SimpleGraphBoxData.toLabelledSimpleGraphEmbedding
    {V : Type*} {G : SimpleGraph V} {box : ℕ → FiniteBox G.edgeSet}
    (data : SimpleGraphBoxData G box) (n : ℕ) :
    LabelledSimpleGraphEmbedding (box n).graph G where
  vertex := data.vertex n
  label := fun e => e.1
  endpoint := data.endpoint n

namespace LabelledSimpleGraphEmbedding

variable {V : Type*} {L : LabelledMultigraph} {G : SimpleGraph V}
variable (B : LabelledSimpleGraphEmbedding L G)

/-- Map a path using only `C` to an open path in the prescribed global graph.
Every global edge of the resulting path lies in the image of `C`. -/
theorem openConnected_global_of_reachable_setConfig
    {ω : G.edgeSet → Bool} {C : Set L.Edge}
    (hCopen : C ⊆ L.openEdgeSet (B.restriction ω)) {u v : L.Vertex}
    (huv : (L.connectionGraph L.freeBoundary (L.setConfig C)).Reachable u v) :
    OpenConnected G ω (LabelCarrier (B.globalLabels C)) (B.vertex u) (B.vertex v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons a b c hab p ih =>
      rcases hab.2 with hfree | ⟨e, heC, hejoin⟩
      · exact (hab.1 hfree).elim
      · have heC' : e ∈ C := by simpa [setConfig] using heC
        have heq : s(B.vertex a, B.vertex b) = (B.label e : Sym2 V) := by
          rw [← B.endpoint e]
          rcases hejoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        have habSimple : G.Adj (B.vertex a) (B.vertex b) := by
          change s(B.vertex a, B.vertex b) ∈ G.edgeSet
          rw [heq]
          exact (B.label e).2
        have heqEdge : (⟨s(B.vertex a, B.vertex b), habSimple⟩ : G.edgeSet) =
            B.label e := Subtype.ext heq
        have hopen : ω (B.label e) = true := hCopen heC'
        have hmem : s(B.vertex a, B.vertex b) ∈
            LabelCarrier (B.globalLabels C) := by
          refine ⟨B.label e, ⟨e, heC', rfl⟩, heq.symm⟩
        exact (OpenConnected.of_adj habSimple hmem (by rwa [heqEdge])).trans ih

/-- Vertices incident to a globalized label are images of vertices incident to
the corresponding local label.  This uses the endpoint identity, not
surjectivity of the vertex embedding. -/
lemma exists_vertexOnLabels_of_global {C : Set L.Edge} {x : V}
    (hx : VertexOnLabels (B.globalLabels C) x) :
    ∃ u : L.Vertex, L.VertexOnLabels C u ∧ B.vertex u = x := by
  obtain ⟨y, hxy, hε⟩ := hx
  obtain ⟨e, heC, he⟩ := hε
  have hval : s(B.vertex (L.source e), B.vertex (L.target e)) = s(x, y) := by
    rw [B.endpoint e]
    exact congrArg Subtype.val he
  rcases Sym2.eq_iff.mp hval with hst | hst
  · exact ⟨L.source e, ⟨e, heC, Or.inl rfl⟩, hst.1⟩
  · exact ⟨L.target e, ⟨e, heC, Or.inr rfl⟩, hst.2⟩

end LabelledSimpleGraphEmbedding

end FK.PlaneTopology

namespace FK.PlaneTopology

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

namespace LabelledSimpleGraphEmbedding

variable {V : Type*} {L : LabelledMultigraph} {G : SimpleGraph V}
variable (B : LabelledSimpleGraphEmbedding L G)

/-- The connectedcarrier proof survives passage to the prescribed global
simple graph.  Open paths may use only global labels in the image of the
finite circuit; no ambient connectivity is substituted for it. -/
theorem openLabelConnected_global_of_cycleMatroid_isCircuit
    {ω : G.edgeSet → Bool} {C : Set L.Edge}
    (hCopen : C ⊆ L.openEdgeSet (B.restriction ω))
    (hC : L.cycleMatroid.IsCircuit C) :
    OpenLabelConnected G ω (B.globalLabels C) := by
  intro x y hx hy
  obtain ⟨u, hu, hux⟩ := B.exists_vertexOnLabels_of_global hx
  obtain ⟨v, hv, hvy⟩ := B.exists_vertexOnLabels_of_global hy
  have huv := L.reachable_of_cycleMatroid_isCircuit hC hu hv
  have hglobal := B.openConnected_global_of_reachable_setConfig hCopen huv
  rwa [hux, hvy] at hglobal

/-- A finite circuit and its independent spherical geometry become a spherical
open circuit of the actual global configuration. -/
theorem sphericalOpenCircuit_global_of_cycleMatroid_isCircuit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {vertex : V → X} {R : OpenPathRealization G vertex}
    {ω : G.edgeSet → Bool} {C : Set L.Edge} {c : X} {r : ℝ}
    (hr : 0 < r)
    (hcross : R.CrossingControlledBy (sphere c r) (B.globalLabels C))
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hCopen : C ⊆ L.openEdgeSet (B.restriction ω))
    (hC : L.cycleMatroid.IsCircuit C) :
    SphericalOpenCircuit R ω (B.globalLabels C) c r where
  radius_pos := hr
  crossing := hcross
  vertex_off := hvertices
  label_open := B.globalLabels_open hCopen
  openConnected := B.openLabelConnected_global_of_cycleMatroid_isCircuit hCopen hC

end LabelledSimpleGraphEmbedding

namespace LabelledDualPairEmbedding

variable {V F : Type*} {P : LabelledDualPair} {G : SimpleGraph V}
variable {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
variable (B : LabelledDualPairEmbedding P G GD edge)

/-- The boundary of a finite dual-open component consists of open primal
labels for the restricted global configuration.  The dual configuration here
is the one proved equal to the prescribed global dual restriction above. -/
lemma openEdgeSet_of_subset_dualOpenComponentBoundary
    (ω : G.edgeSet → Bool) (x : P.Face) {C : Set P.Edge}
    (hCcut : C ⊆ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (B.dualRestriction ω) x)) :
    C ⊆ P.primal.openEdgeSet (B.primalRestriction ω) := by
  intro f hf
  have hd := P.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
    (P.faceDual.openComponentSaturated_openVertexComponent
      (B.dualRestriction ω) x) (hCcut hf)
  change (dualConfig (Equiv.refl P.Edge) (B.primalRestriction ω) f) = false at hd
  change (!B.primalRestriction ω f) = false at hd
  change B.primalRestriction ω f = true
  cases h : B.primalRestriction ω f <;> simp [h] at hd ⊢

/-- Global spherical form of the reversed finite boundary circuit theorem.
Jordan/crossing data and vertex-off-sphere remain explicit; the combinatorial
openness and connectedcarrier parts are proved from the finite circuit. -/
theorem sphericalOpenCircuit_global_of_primalCircuit_subset_dualOpenComponentBoundary
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {vertex : V → X} {R : OpenPathRealization G vertex}
    (ω : G.edgeSet → Bool) (x : P.Face) {C : Set P.Edge} {c : X} {r : ℝ}
    (hr : 0 < r)
    (hcross : R.CrossingControlledBy (sphere c r) (B.primal.globalLabels C))
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hCcut : C ⊆ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (B.dualRestriction ω) x))
    (hC : P.primal.cycleMatroid.IsCircuit C) :
    SphericalOpenCircuit R ω (B.primal.globalLabels C) c r := by
  have hCopen := B.openEdgeSet_of_subset_dualOpenComponentBoundary ω x hCcut
  exact B.primal.sphericalOpenCircuit_global_of_cycleMatroid_isCircuit
    hr hcross hvertices hCopen hC

/-- The two descriptions of the restricted dual configuration are identical,
including the action of the prescribed global edge equivalence. -/
lemma dual_restriction_eq_dualRestriction (ω : G.edgeSet → Bool) :
    B.dual.restriction (dualConfig edge ω) = B.dualRestriction ω := by
  funext e
  exact (B.dualRestriction_apply ω e).symm

/-- A path in an actual finite dual-open component is a path in the prescribed
global dual-open component.  This is deliberately only the local-to-global
direction; selecting a box that contains an entire global component is the
separate enclosure/Jordan input. -/
theorem openConnected_globalDual_of_mem_openVertexComponent
    (ω : G.edgeSet → Bool) {x y : P.Face}
    (hy : y ∈ P.faceDual.openVertexComponent (B.dualRestriction ω) x) :
    OpenConnected GD (dualConfig edge ω) Set.univ
      (B.dual.vertex x) (B.dual.vertex y) := by
  have huv : (P.faceDual.connectionGraph P.faceDual.freeBoundary
      (P.faceDual.setConfig
        (P.faceDual.openEdgeSet (B.dualRestriction ω)))).Reachable x y := by
    rw [P.faceDual.setConfig_openEdgeSet]
    exact hy
  have hopen : P.faceDual.openEdgeSet (B.dualRestriction ω) ⊆
      P.faceDual.openEdgeSet (B.dual.restriction (dualConfig edge ω)) := by
    rw [B.dual_restriction_eq_dualRestriction]
  have hglobal := B.dual.openConnected_global_of_reachable_setConfig hopen huv
  exact hglobal.mono_edges (Set.subset_univ _)

end LabelledDualPairEmbedding

end FK.PlaneTopology

namespace FK.PlaneTopology

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

/-- Cofinally many finite dual-component boundary circuits, transported through
varying compatible finite boxes, give the exact global circuit exhaustion.
The fixed global graph, global configuration and prescribed edge equivalence
do not vary with the box. -/
theorem hasOpenCircuitExhaustion_of_cofinal_globalizedBoundaries
    {ι V F X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : SimpleGraph V} {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
    {P : ι → LabelledDualPair} {vertex : V → X}
    (B : ∀ i, LabelledDualPairEmbedding (P i) G GD edge)
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hcofinal : ∀ ρ : ℝ, ∃ (i : ι) (x : (P i).Face) (C : Set (P i).Edge) (r : ℝ),
      0 < r ∧ ρ < r ∧
      R.CrossingControlledBy (sphere c r) ((B i).primal.globalLabels C) ∧
      (∀ v, vertex v ∈ (sphere c r)ᶜ) ∧
      C ⊆ (P i).faceDual.vertexCut
        ((P i).faceDual.openVertexComponent ((B i).dualRestriction ω) x) ∧
      (P i).primal.cycleMatroid.IsCircuit C) :
    HasOpenCircuitExhaustion R ω c := by
  intro ρ
  obtain ⟨i, x, C, r, hr, hρ, hcross, hvertices, hCcut, hC⟩ := hcofinal ρ
  refine ⟨(B i).primal.globalLabels C, r, hρ, ?_⟩
  exact (B i).sphericalOpenCircuit_global_of_primalCircuit_subset_dualOpenComponentBoundary
    ω x hr hcross hvertices hCcut hC

/-- **Global finite-box compatibility for open-circuit uniqueness.**  Under an
explicit cofinal supply of compatible finite dual-boundary circuits and the
usual properness of the vertex realization, the prescribed global simple
graph configuration has at most one infinite open component. -/
theorem globalAtMostOne_of_cofinal_globalizedBoundaries
    {ι V F X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : SimpleGraph V} {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
    {P : ι → LabelledDualPair} {vertex : V → X}
    (B : ∀ i, LabelledDualPairEmbedding (P i) G GD edge)
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (hcofinal : ∀ ρ : ℝ, ∃ (i : ι) (x : (P i).Face) (C : Set (P i).Edge) (r : ℝ),
      0 < r ∧ ρ < r ∧
      R.CrossingControlledBy (sphere c r) ((B i).primal.globalLabels C) ∧
      (∀ v, vertex v ∈ (sphere c r)ᶜ) ∧
      C ⊆ (P i).faceDual.vertexCut
        ((P i).faceDual.openVertexComponent ((B i).dualRestriction ω) x) ∧
      (P i).primal.cycleMatroid.IsCircuit C) :
    GlobalAtMostOne G ω := by
  exact globalAtMostOne_of_openCircuitExhaustion R ω c hproper
    (hasOpenCircuitExhaustion_of_cofinal_globalizedBoundaries B R ω c hcofinal)

end FK.PlaneTopology

#print axioms FK.PlaneTopology.LabelledSimpleGraphEmbedding.label_eq_of_simpleEdge_eq
#print axioms FK.PlaneTopology.LabelledSimpleGraphEmbedding.simpleEdge_eq_of_label_eq
#print axioms FK.PlaneTopology.LabelledSimpleGraphEmbedding.simpleConfig_simpleEdge_eq_true_iff
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.dualRestriction_apply
#print axioms FK.PlaneTopology.SimpleGraphBoxData.toLabelledSimpleGraphEmbedding
#print axioms FK.PlaneTopology.LabelledSimpleGraphEmbedding.openConnected_global_of_reachable_setConfig
#print axioms FK.PlaneTopology.LabelledSimpleGraphEmbedding.openLabelConnected_global_of_cycleMatroid_isCircuit
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.sphericalOpenCircuit_global_of_primalCircuit_subset_dualOpenComponentBoundary
#print axioms FK.PlaneTopology.hasOpenCircuitExhaustion_of_cofinal_globalizedBoundaries
#print axioms FK.PlaneTopology.globalAtMostOne_of_cofinal_globalizedBoundaries
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.dual_restriction_eq_dualRestriction
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.openConnected_globalDual_of_mem_openVertexComponent
