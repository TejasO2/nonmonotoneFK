import FK.InfiniteOpenCircuitUniqueness

/-!
# Primal-open boundaries of finite dual-open components

This file reverses the cut/circuit argument in `FK.PlaneCutCircuit`.  A circuit
of a labelled cycle matroid is not merely an open set of labels: all its
incident vertices are connected using only those labels.  Applying this to the
boundary of an actual dual-open component gives a genuinely open-connected
primal circuit carrier.
-/

namespace FK.Finite.LabelledMultigraph

open scoped Classical
open Matroid
open FK.Finite.Conditional
open FK.Configuration

variable (G : LabelledMultigraph)

/-- A vertex incident to at least one member of a set of labelled edges. -/
def VertexOnLabels (C : Set G.Edge) (u : G.Vertex) : Prop :=
  ∃ e ∈ C, u = G.source e ∨ u = G.target e

lemma reachable_endpoints_of_mem (C : Set G.Edge) {e : G.Edge} (he : e ∈ C) :
    (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable
      (G.source e) (G.target e) := by
  by_cases hst : G.source e = G.target e
  · simp [hst]
  · apply SimpleGraph.Adj.reachable
    exact ⟨hst, Or.inr ⟨e, by simp [setConfig, he], Or.inl ⟨rfl, rfl⟩⟩⟩

/-- A walk using labels of `A ⊆ C` can be restricted to the labels whose
source lies in the `C`-component of its starting vertex. -/
lemma reachable_componentLabels_of_subset {A C : Set G.Edge} (hAC : A ⊆ C)
    {x u v : G.Vertex}
    (huv : (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable u v)
    (hxu : (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable x u) :
    (G.connectionGraph G.freeBoundary (G.setConfig
      {a ∈ A | (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable
        x (G.source a)})).Reachable u v := by
  obtain ⟨p⟩ := huv
  revert x
  induction p with
  | nil => intro x hxu; exact SimpleGraph.Reachable.refl _
  | @cons u w v huw p ih =>
      intro x hxu
      have huw' := huw
      rcases huw.2 with hfree | ⟨e, heA, hejoin⟩
      · exact (huw.1 hfree).elim
      · have heA' : e ∈ A := by simpa [setConfig] using heA
        have heC : e ∈ C := hAC heA'
        have heEnds := G.reachable_endpoints_of_mem C heC
        have hxe : (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable
            x (G.source e) := by
          rcases hejoin with ⟨hes, het⟩ | ⟨het, hes⟩
          · simpa [hes] using hxu
          · have hxt : (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable
                x (G.target e) := by simpa [hes] using hxu
            exact hxt.trans heEnds.symm
        have hxw : (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable x w := by
          rcases hejoin with ⟨hes, het⟩ | ⟨het, hes⟩
          · have hcs : (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable
                x (G.source e) := by simpa [hes] using hxu
            simpa [het] using hcs.trans heEnds
          · simpa [het] using hxe
        apply SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) (ih hxw)
        refine ⟨huw'.1, Or.inr ⟨e, ?_, hejoin⟩⟩
        simp [setConfig, heA', hxe]

/-- Every vertex incident to a cycle-matroid circuit is connected to every
other such vertex using only circuit labels.  This includes loops and parallel
labels; the proof uses minimal dependence rather than a simple-graph cycle
representation. -/
theorem reachable_of_cycleMatroid_isCircuit {C : Set G.Edge}
    (hC : G.cycleMatroid.IsCircuit C) {u v : G.Vertex}
    (hu : G.VertexOnLabels C u) (hv : G.VertexOnLabels C v) :
    (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable u v := by
  obtain ⟨f, hf⟩ := hC.nonempty
  let H := G.connectionGraph G.freeBoundary (G.setConfig C)
  let D := {e ∈ C | H.Reachable (G.source f) (G.source e)}
  have hDf : f ∈ D := ⟨hf, SimpleGraph.Reachable.refl _⟩
  have hpath := G.reachable_sdiff_singleton_of_cycleMatroid_isCircuit hC hf
  have hsub : C \ {f} ⊆ C := Set.sdiff_subset
  have hrestricted := G.reachable_componentLabels_of_subset hsub hpath
    (SimpleGraph.Reachable.refl (G.source f))
  have hset : {a ∈ C \ {f} | H.Reachable (G.source f) (G.source a)} = D \ {f} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨haC, haf⟩, ha⟩
      exact ⟨⟨haC, ha⟩, haf⟩
    · rintro ⟨⟨haC, ha⟩, haf⟩
      exact ⟨⟨haC, haf⟩, ha⟩
  rw [hset] at hrestricted
  have hdep : ¬ G.cycleMatroid.Indep D := by
    intro hInd
    have hforest := (G.cycleMatroid_indep D).mp hInd
    apply hforest f (by simp [setConfig, hDf])
    unfold endpointsConnectedWithout
    rw [G.withEdge_false_setConfig]
    exact hrestricted
  have hDC : D = C := hC.eq_of_not_indep_subset hdep (by
    intro e he
    exact he.1)
  have hsource : ∀ e ∈ C, H.Reachable (G.source f) (G.source e) := by
    intro e he
    have : e ∈ D := hDC.symm ▸ he
    exact this.2
  have hincident : ∀ {z : G.Vertex}, G.VertexOnLabels C z → H.Reachable (G.source f) z := by
    intro z hz
    obtain ⟨e, he, rfl | rfl⟩ := hz
    · exact hsource e he
    · exact (hsource e he).trans (G.reachable_endpoints_of_mem C he)
  exact (hincident hu).symm.trans (hincident hv)

end FK.Finite.LabelledMultigraph

namespace FK.Finite.PlaneMatroid.LabelledDualPair

open scoped Classical
open Matroid
open FK.Finite.LabelledMultigraph
open FK.Configuration

variable (P : LabelledDualPair)

/-- Exchange the two graphs in a labelled dual pair.  No duality certificate is
needed to form the combinatorial exchange. -/
def swap : LabelledDualPair where
  Vertex := P.Face
  Face := P.Vertex
  Edge := P.Edge
  source := P.dualSource
  target := P.dualTarget
  dualSource := P.source
  dualTarget := P.target

/-- A cocircuit of the face-dual cycle matroid is a circuit of the primal cycle
matroid, by the actual graphic-duality certificate and double duality. -/
lemma isCircuit_primal_of_isCocircuit_faceDual
    (hP : P.GraphicDualCertificate) {C : Set P.Edge}
    (hC : P.faceDual.cycleMatroid.IsCocircuit C) :
    P.primal.cycleMatroid.IsCircuit C := by
  change (P.faceDual.cycleMatroid)✶.IsCircuit C at hC
  have hC' : (P.primal.cycleMatroid)✶.IsCocircuit C := by
    change (P.primal.cycleMatroid)✶✶.IsCircuit C
    rw [hP.dual_cycleMatroid]
    exact hC
  exact Matroid.dual_isCocircuit_iff.mp hC'

/-- **Reversed finite boundary circuit.**  Every boundary label of an actual
finite dual-open component lies on a primal-open circuit contained in that
boundary.  Moreover all vertices incident to the circuit are connected in the
actual primal configuration using only circuit labels. -/
theorem exists_primalOpen_circuit_boundary_dualOpenComponent
    (hP : P.GraphicDualCertificate) (ω : P.primal.Configuration) (x : P.Face)
    {e : P.Edge}
    (he : e ∈ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x)) :
    ∃ C, C ⊆ P.faceDual.vertexCut
        (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x) ∧
      e ∈ C ∧ P.primal.cycleMatroid.IsCircuit C ∧
      C ⊆ P.primal.openEdgeSet ω ∧
      ∀ {u v : P.Vertex}, P.primal.VertexOnLabels C u →
        P.primal.VertexOnLabels C v →
          (P.primal.connectionGraph P.primal.freeBoundary ω).Reachable u v := by
  obtain ⟨C, hCcut, heC, hC⟩ := P.swap.exists_isCocircuit_subset_vertexCut he
  have hCc : P.primal.cycleMatroid.IsCircuit C :=
    P.isCircuit_primal_of_isCocircuit_faceDual hP hC
  have hCopen : C ⊆ P.primal.openEdgeSet ω := by
    intro f hf
    have hd := P.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
      (P.faceDual.openComponentSaturated_openVertexComponent
        (dualConfig (Equiv.refl P.Edge) ω) x) (hCcut hf)
    change (dualConfig (Equiv.refl P.Edge) ω f) = false at hd
    change (!ω f) = false at hd
    change ω f = true
    cases h : ω f <;> simp [h] at hd ⊢
  refine ⟨C, hCcut, heC, hCc, hCopen, ?_⟩
  intro u v hu hv
  have hreach := P.primal.reachable_of_cycleMatroid_isCircuit hCc hu hv
  have hle : P.primal.connectionGraph P.primal.freeBoundary (P.primal.setConfig C) ≤
      P.primal.connectionGraph P.primal.freeBoundary
        (P.primal.setConfig (P.primal.openEdgeSet ω)) :=
    P.primal.connectionGraph_mono (ξ := P.primal.freeBoundary)
      (P.primal.setConfig_mono hCopen)
  rw [P.primal.setConfig_openEdgeSet] at hle
  exact hreach.mono hle

end FK.Finite.PlaneMatroid.LabelledDualPair


namespace FK.Finite.LabelledMultigraph

open scoped Classical
open FK.Configuration
open CurvatureVariance.Infra.Percolation
open FK.PlaneTopology

variable (G : LabelledMultigraph)

/-- The simple graph obtained by forgetting orientations and parallel-label
multiplicity.  Loops disappear; the subsequent edge map assumes that the
labelled graph itself has none. -/
def simpleGraph : SimpleGraph G.Vertex :=
  G.connectionGraph G.freeBoundary G.allOpen

lemma simpleGraph_adj_iff {u v : G.Vertex} :
    G.simpleGraph.Adj u v ↔ u ≠ v ∧ ∃ e, G.Joins e u v := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rcases h.2 with hfree | ⟨e, he, hjoin⟩
    · exact (h.1 hfree).elim
    · exact ⟨e, hjoin⟩
  · rintro ⟨hne, e, hjoin⟩
    exact ⟨hne, Or.inr ⟨e, by simp [allOpen], hjoin⟩⟩

/-- The simple edge represented by a nonloop labelled edge. -/
def simpleEdge (hloop : ∀ e, G.source e ≠ G.target e) (e : G.Edge) :
    G.simpleGraph.edgeSet where
  val := s(G.source e, G.target e)
  property := (G.simpleGraph_adj_iff).2
    ⟨hloop e, e, Or.inl ⟨rfl, rfl⟩⟩

/-- Forget parallel multiplicity in the configuration: a simple edge is open
when at least one labelled representative is open. -/
noncomputable def simpleConfig (hloop : ∀ e, G.source e ≠ G.target e)
    (ω : G.Configuration) : G.simpleGraph.edgeSet → Bool :=
  fun ε => decide (∃ e, ω e = true ∧ G.simpleEdge hloop e = ε)

/-- Image of a set of labels under the simple-edge map. -/
def simpleLabels (hloop : ∀ e, G.source e ≠ G.target e) (C : Set G.Edge) :
    Set G.simpleGraph.edgeSet :=
  G.simpleEdge hloop '' C

lemma simpleConfig_eq_true_iff (hloop : ∀ e, G.source e ≠ G.target e)
    (ω : G.Configuration) (ε : G.simpleGraph.edgeSet) :
    G.simpleConfig hloop ω ε = true ↔
      ∃ e, ω e = true ∧ G.simpleEdge hloop e = ε := by
  simp [simpleConfig]

lemma simpleConfig_simpleEdge_of_mem_openEdgeSet
    (hloop : ∀ e, G.source e ≠ G.target e) {ω : G.Configuration}
    {C : Set G.Edge} (hCopen : C ⊆ G.openEdgeSet ω) {e : G.Edge} (he : e ∈ C) :
    G.simpleConfig hloop ω (G.simpleEdge hloop e) = true :=
  (G.simpleConfig_eq_true_iff hloop ω _).2 ⟨e, hCopen he, rfl⟩

/-- Transport a walk using only `C` to an open simple-graph walk whose allowed
underlying edges are precisely the image of `C`. -/
theorem openConnected_simple_of_reachable_setConfig
    (hloop : ∀ e, G.source e ≠ G.target e) {ω : G.Configuration}
    {C : Set G.Edge} (hCopen : C ⊆ G.openEdgeSet ω) {u v : G.Vertex}
    (huv : (G.connectionGraph G.freeBoundary (G.setConfig C)).Reachable u v) :
    OpenConnected G.simpleGraph (G.simpleConfig hloop ω)
      (LabelCarrier (G.simpleLabels hloop C)) u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact OpenConnected.refl _ _ _
  | @cons a b c hab p ih =>
      rcases hab.2 with hfree | ⟨e, heC, hejoin⟩
      · exact (hab.1 hfree).elim
      · have heC' : e ∈ C := by simpa [setConfig] using heC
        have habSimple : G.simpleGraph.Adj a b := (G.simpleGraph_adj_iff).2
          ⟨hab.1, e, hejoin⟩
        have heq : G.simpleEdge hloop e =
            (⟨s(a, b), habSimple⟩ : G.simpleGraph.edgeSet) := by
          apply Subtype.ext
          rcases hejoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        have hopen : G.simpleConfig hloop ω
            (⟨s(a, b), habSimple⟩ : G.simpleGraph.edgeSet) = true := by
          rw [← heq]
          exact G.simpleConfig_simpleEdge_of_mem_openEdgeSet hloop hCopen heC'
        have hmem : s(a, b) ∈ LabelCarrier (G.simpleLabels hloop C) := by
          refine ⟨G.simpleEdge hloop e, ⟨e, heC', rfl⟩, ?_⟩
          exact congrArg Subtype.val heq
        exact (OpenConnected.of_adj habSimple hmem hopen).trans ih

lemma labelled_vertexOnLabels_of_simple
    (hloop : ∀ e, G.source e ≠ G.target e) {C : Set G.Edge} {u : G.Vertex}
    (hu : FK.PlaneTopology.VertexOnLabels (G.simpleLabels hloop C) u) :
    G.VertexOnLabels C u := by
  obtain ⟨v, huv, hεC⟩ := hu
  obtain ⟨e, heC, hee⟩ := hεC
  have hval : s(G.source e, G.target e) = s(u, v) :=
    congrArg Subtype.val hee
  refine ⟨e, heC, ?_⟩
  rcases Sym2.eq_iff.mp hval with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact Or.inl hs.symm
  · exact Or.inr ht.symm

/-- A graphic-matroid circuit contained in the open labels becomes an
`OpenLabelConnected` set after forgetting parallel multiplicity. -/
theorem openLabelConnected_simple_of_cycleMatroid_isCircuit
    (hloop : ∀ e, G.source e ≠ G.target e) {ω : G.Configuration}
    {C : Set G.Edge} (hCopen : C ⊆ G.openEdgeSet ω)
    (hC : G.cycleMatroid.IsCircuit C) :
    OpenLabelConnected G.simpleGraph (G.simpleConfig hloop ω)
      (G.simpleLabels hloop C) := by
  intro u v hu hv
  have hu' := G.labelled_vertexOnLabels_of_simple hloop hu
  have hv' := G.labelled_vertexOnLabels_of_simple hloop hv
  exact G.openConnected_simple_of_reachable_setConfig hloop hCopen
    (G.reachable_of_cycleMatroid_isCircuit hC hu' hv')

end FK.Finite.LabelledMultigraph

namespace FK.PlaneTopology

open Set Metric
open scoped Classical
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open CurvatureVariance.Infra.Percolation

variable {X : Type*} [NormedAddCommGroup X]

/-- Geometric Jordan/crossing input for primal circuits on the actual simple
graph.  Unlike `SphericalDualCircuitGeometry`, this has the orientation needed
for open-circuit uniqueness: the crossing-controlled set consists of primal
circuit labels. -/
structure SphericalPrimalCircuitGeometry (P : LabelledDualPair)
    (hloop : ∀ e, P.primal.source e ≠ P.primal.target e)
    {vertex : P.Vertex → X} (R : OpenPathRealization P.primal.simpleGraph vertex) where
  centre : Set P.Edge → X
  radius : Set P.Edge → ℝ
  radius_pos : ∀ C, P.primal.cycleMatroid.IsCircuit C → 0 < radius C
  vertex_off : ∀ C, P.primal.cycleMatroid.IsCircuit C →
    ∀ v, vertex v ∈ (sphere (centre C) (radius C))ᶜ
  crossing : ∀ C, P.primal.cycleMatroid.IsCircuit C →
    R.CrossingControlledBy (sphere (centre C) (radius C))
      (P.primal.simpleLabels hloop C)

/-- Any primal circuit contained in the boundary of a finite dual-open
component is an actual spherical primal-open circuit with connected carrier. -/
theorem sphericalOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → X} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SphericalPrimalCircuitGeometry P hloop R)
    (ω : P.primal.Configuration) (x : P.Face) {C : Set P.Edge}
    (hCcut : C ⊆ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x))
    (hC : P.primal.cycleMatroid.IsCircuit C) :
    SphericalOpenCircuit R (P.primal.simpleConfig hloop ω)
      (P.primal.simpleLabels hloop C) (S.centre C) (S.radius C) := by
  have hCopen : C ⊆ P.primal.openEdgeSet ω := by
    intro f hf
    have hd := P.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
      (P.faceDual.openComponentSaturated_openVertexComponent
        (dualConfig (Equiv.refl P.Edge) ω) x) (hCcut hf)
    change (dualConfig (Equiv.refl P.Edge) ω f) = false at hd
    change (!ω f) = false at hd
    change ω f = true
    cases h : ω f <;> simp [h] at hd ⊢
  exact
    { radius_pos := S.radius_pos C hC
      crossing := S.crossing C hC
      vertex_off := S.vertex_off C hC
      label_open := by
        intro ε hε
        obtain ⟨e, heC, rfl⟩ := hε
        exact P.primal.simpleConfig_simpleEdge_of_mem_openEdgeSet hloop hCopen heC
      openConnected :=
        P.primal.openLabelConnected_simple_of_cycleMatroid_isCircuit hloop hCopen hC }

/-- The reversed finite boundary theorem specialized to the actual spherical
open-circuit interface. -/
theorem exists_sphericalOpenCircuit_boundary_dualOpenComponent
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → X} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SphericalPrimalCircuitGeometry P hloop R)
    (hP : P.GraphicDualCertificate) (ω : P.primal.Configuration) (x : P.Face)
    {e : P.Edge}
    (he : e ∈ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x)) :
    ∃ C : Set P.Edge, e ∈ C ∧
      SphericalOpenCircuit R (P.primal.simpleConfig hloop ω)
        (P.primal.simpleLabels hloop C) (S.centre C) (S.radius C) := by
  obtain ⟨C, hCcut, heC, hC, hCopen, hconn⟩ :=
    P.exists_primalOpen_circuit_boundary_dualOpenComponent hP ω x he
  exact ⟨C, heC,
    sphericalOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary
      S ω x hCcut hC⟩

/-- Cofinal spherical circuits cut out as primal boundaries of finite
dual-open components give the exact exhaustion consumed by
`InfiniteOpenCircuitUniqueness`. -/
theorem hasOpenCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → X} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SphericalPrimalCircuitGeometry P hloop R)
    (ω : P.primal.Configuration) (c : X)
    (hcofinal : ∀ ρ : ℝ, ∃ (x : P.Face) (C : Set P.Edge),
      C ⊆ P.faceDual.vertexCut
        (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x) ∧
      P.primal.cycleMatroid.IsCircuit C ∧
      c = S.centre C ∧ ρ < S.radius C) :
    HasOpenCircuitExhaustion R (P.primal.simpleConfig hloop ω) c := by
  intro ρ
  obtain ⟨x, C, hCcut, hC, rfl, hρ⟩ := hcofinal ρ
  exact ⟨P.primal.simpleLabels hloop C, S.radius C, hρ,
    sphericalOpenCircuit_of_primalCircuit_subset_dualOpenComponentBoundary
      S ω x hCcut hC⟩

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

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Composition check for the existing infinite geometric uniqueness step.
The hypothesis is the same explicit cofinal finite-dual-boundary supply used in
`hasOpenCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries`. -/
theorem globalAtMostOne_of_cofinal_dualOpenComponentBoundaries
    {P : LabelledDualPair} {hloop : ∀ e, P.primal.source e ≠ P.primal.target e}
    {vertex : P.Vertex → X} {R : OpenPathRealization P.primal.simpleGraph vertex}
    (S : SphericalPrimalCircuitGeometry P hloop R)
    (ω : P.primal.Configuration) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite)
    (hcofinal : ∀ ρ : ℝ, ∃ (x : P.Face) (C : Set P.Edge),
      C ⊆ P.faceDual.vertexCut
        (P.faceDual.openVertexComponent (dualConfig (Equiv.refl P.Edge) ω) x) ∧
      P.primal.cycleMatroid.IsCircuit C ∧
      c = S.centre C ∧ ρ < S.radius C) :
    GlobalAtMostOne P.primal.simpleGraph (P.primal.simpleConfig hloop ω) := by
  exact globalAtMostOne_of_openCircuitExhaustion R _ c hproper
    (hasOpenCircuitExhaustion_of_cofinal_dualOpenComponentBoundaries S ω c hcofinal)

end FK.PlaneTopology
