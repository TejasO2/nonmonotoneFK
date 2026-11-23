import FK.GlobalPrimalCompatibility
import FK.DualFiniteEnclosure
import FK.RotationSystemDuality

/-!
# Exact finite windows for a global dual-open component

A finite labelled plane-dual window can contain an entire component of the
prescribed global dual graph. This file proves the reverse (global-to-local)
path transport from explicit coverage of that component's vertices and
internal edges. It then identifies the labelled vertex cut with the actual
simple-graph edge cut on all labels represented in the window.

No component equality or path-lifting property is assumed. The geometric
construction of a Jordan circuit and the global rotation/box data remain
separate inputs.
-/

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

namespace LabelledDualPairEmbedding

variable {V F : Type*} {P : LabelledDualPair} {G : SimpleGraph V}
variable {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
variable (B : LabelledDualPairEmbedding P G GD edge)

/-- The component in the prescribed global simple dual graph, rather than in
an abstract global labelled graph. -/
def globalDualOpenComponent (ω : G.edgeSet → Bool) (x : P.Face) : Set F :=
  {z | OpenConnected GD (dualConfig edge ω) Set.univ (B.dual.vertex x) z}

/-- Every vertex of the selected global component is represented in the
finite window. -/
def CoversGlobalDualComponentVertices (ω : G.edgeSet → Bool) (x : P.Face) : Prop :=
  B.globalDualOpenComponent ω x ⊆ Set.range B.dual.vertex

/-- Every global edge internal to the selected component and joining two
represented vertices is represented by a local label. -/
def CoversGlobalDualComponentEdges (ω : G.edgeSet → Bool) (x : P.Face) : Prop :=
  ∀ {a b : P.Face} (hab : GD.Adj (B.dual.vertex a) (B.dual.vertex b)),
    B.dual.vertex a ∈ B.globalDualOpenComponent ω x →
    B.dual.vertex b ∈ B.globalDualOpenComponent ω x →
    ∃ e : P.Edge, B.dual.label e =
      (⟨s(B.dual.vertex a, B.dual.vertex b), hab⟩ : GD.edgeSet)

/-- Lift an open global walk with a generalized global start. This separate
induction form avoids identifying the finite-window vertices along the walk. -/
lemma exists_local_reachable_of_walk
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x)
    {a z : F} (p : GD.Walk a z)
    (hp : IsOpenIn (dualConfig edge ω) Set.univ p)
    {u : P.Face} (ha : a = B.dual.vertex u)
    (hu : B.dual.vertex u ∈ B.globalDualOpenComponent ω x) :
    ∃ v : P.Face, B.dual.vertex v = z ∧
      (P.faceDual.connectionGraph P.faceDual.freeBoundary
        (B.dualRestriction ω)).Reachable u v := by
  induction p generalizing u with
  | nil => exact ⟨u, ha.symm, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have hparts := isOpenIn_cons.mp hp
      have hab' : GD.Adj (B.dual.vertex u) b := by rwa [← ha]
      have hopen' : dualConfig edge ω
          (⟨s(B.dual.vertex u, b), hab'⟩ : GD.edgeSet) = true := by
        simpa only [← ha] using hparts.1.2
      have hb : b ∈ B.globalDualOpenComponent ω x := by
        exact hu.trans (OpenConnected.of_adj hab' (Set.mem_univ _) hopen')
      obtain ⟨w, hw⟩ := hvertex hb
      have huwAdj : GD.Adj (B.dual.vertex u) (B.dual.vertex w) := by
        rwa [hw]
      have hbw : B.dual.vertex w ∈ B.globalDualOpenComponent ω x := by
        rwa [hw]
      obtain ⟨e, he⟩ := hedge huwAdj hu hbw
      have hendpoints :
          s(B.dual.vertex (P.faceDual.source e), B.dual.vertex (P.faceDual.target e)) =
            s(B.dual.vertex u, B.dual.vertex w) := by
        rw [B.dual.endpoint e]
        exact congrArg Subtype.val he
      have hjoins : P.faceDual.Joins e u w := by
        rcases Sym2.eq_iff.mp hendpoints with hst | hst
        · exact Or.inl ⟨hinj hst.1, hinj hst.2⟩
        · exact Or.inr ⟨hinj hst.1, hinj hst.2⟩
      have hopenGlobal : dualConfig edge ω (B.dual.label e) = true := by
        rw [he]
        simpa [hw] using hopen'
      have hopenLocal : B.dualRestriction ω e = true := by
        rw [B.dualRestriction_apply]
        exact hopenGlobal
      have hlocalAdj : (P.faceDual.connectionGraph P.faceDual.freeBoundary
          (B.dualRestriction ω)).Adj u w := by
        refine ⟨?_, Or.inr ⟨e, hopenLocal, hjoins⟩⟩
        intro huwEq
        subst w
        exact huwAdj.ne rfl
      obtain ⟨v, hv, hwv⟩ := ih hparts.2 hw.symm hbw
      exact ⟨v, hv, (SimpleGraph.Adj.reachable hlocalAdj).trans hwv⟩

/-- Lift an open global connection starting at a represented vertex to a
local reachable vertex over the same global endpoint. Only component coverage
and injectivity of the vertex realization are used. -/
lemma exists_local_reachable_of_openConnected
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x)
    {u : P.Face} {z : F}
    (hu : B.dual.vertex u ∈ B.globalDualOpenComponent ω x)
    (huz : OpenConnected GD (dualConfig edge ω) Set.univ (B.dual.vertex u) z) :
    ∃ v : P.Face, B.dual.vertex v = z ∧
      (P.faceDual.connectionGraph P.faceDual.freeBoundary
        (B.dualRestriction ω)).Reachable u v := by
  obtain ⟨p, hp⟩ := huz
  exact B.exists_local_reachable_of_walk hinj ω x hvertex hedge p hp rfl hu

/-- Exact membership compatibility for represented vertices. The forward
implication is the existing local-to-global transport; the reverse one is
proved by lifting the global path using the finite-window coverage. -/
theorem mem_openVertexComponent_iff_global
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x y : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x) :
    y ∈ P.faceDual.openVertexComponent (B.dualRestriction ω) x ↔
      B.dual.vertex y ∈ B.globalDualOpenComponent ω x := by
  constructor
  · exact B.openConnected_globalDual_of_mem_openVertexComponent ω
  · intro hy
    obtain ⟨v, hv, hxv⟩ := B.exists_local_reachable_of_openConnected hinj ω x
      hvertex hedge (u := x) (z := B.dual.vertex y)
      (OpenConnected.refl _ _ _) hy
    have hvy : v = y := hinj hv
    change (P.faceDual.connectionGraph P.faceDual.freeBoundary
      (B.dualRestriction ω)).Reachable x y
    simpa only [hvy] using hxv

/-- Labelwise compatibility of the finite labelled component boundary with
the actual global simple-graph edge cut. -/
theorem label_mem_globalEdgeCut_iff_mem_vertexCut
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x) (e : P.Edge) :
    B.dual.label e ∈ DualExhaustion.edgeCut GD (B.globalDualOpenComponent ω x) ↔
      e ∈ P.faceDual.vertexCut
        (P.faceDual.openVertexComponent (B.dualRestriction ω) x) := by
  have hmem (y : P.Face) :
      y ∈ P.faceDual.openVertexComponent (B.dualRestriction ω) x ↔
        B.dual.vertex y ∈ B.globalDualOpenComponent ω x :=
    B.mem_openVertexComponent_iff_global hinj ω x y hvertex hedge
  constructor
  · rintro ⟨a, ha, b, hb, hab, he⟩
    have hval : s(B.dual.vertex (P.faceDual.source e),
        B.dual.vertex (P.faceDual.target e)) = s(a, b) := by
      rw [B.dual.endpoint e, he]
    rcases Sym2.eq_iff.mp hval with hst | hst
    · have hs : B.dual.vertex (P.faceDual.source e) ∈
          B.globalDualOpenComponent ω x := by rwa [hst.1]
      have ht : B.dual.vertex (P.faceDual.target e) ∉
          B.globalDualOpenComponent ω x := by rwa [hst.2]
      exact Or.inl ⟨(hmem _).mpr hs, fun h => ht ((hmem _).mp h)⟩
    · have hs : B.dual.vertex (P.faceDual.source e) ∉
          B.globalDualOpenComponent ω x := by rwa [hst.1]
      have ht : B.dual.vertex (P.faceDual.target e) ∈
          B.globalDualOpenComponent ω x := by rwa [hst.2]
      exact Or.inr ⟨fun h => hs ((hmem _).mp h), (hmem _).mpr ht⟩
  · intro he
    rcases he with he | he
    · refine ⟨B.dual.vertex (P.faceDual.source e), (hmem _).mp he.1,
        B.dual.vertex (P.faceDual.target e), ?_, B.dual.adj_source_target e, ?_⟩
      · intro ht
        exact he.2 ((hmem _).mpr ht)
      · exact (B.dual.endpoint e).symm
    · refine ⟨B.dual.vertex (P.faceDual.target e), (hmem _).mp he.2,
        B.dual.vertex (P.faceDual.source e), ?_, ?_, ?_⟩
      · intro hs
        exact he.1 ((hmem _).mpr hs)
      · exact (B.dual.adj_source_target e).symm
      · exact (B.dual.endpoint e).symm.trans Sym2.eq_swap

/-- Set-level form of the exact cut compatibility: represented labels of the
finite component cut are precisely represented labels of the global cut. -/
theorem globalLabels_vertexCut_eq_globalEdgeCut_inter_range
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x) :
    B.dual.globalLabels (P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (B.dualRestriction ω) x)) =
      DualExhaustion.edgeCut GD (B.globalDualOpenComponent ω x) ∩
        Set.range B.dual.label := by
  ext f
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨(B.label_mem_globalEdgeCut_iff_mem_vertexCut
      hinj ω x hvertex hedge e).mpr he, ⟨e, rfl⟩⟩
  · rintro ⟨hf, e, rfl⟩
    exact ⟨e, (B.label_mem_globalEdgeCut_iff_mem_vertexCut
      hinj ω x hvertex hedge e).mp hf, rfl⟩

/-- Primal circuit labels coming from the finite component boundary lie in
the `edge.symm` image of the actual global dual edge cut. -/
lemma primal_globalLabels_subset_globalDualEdgeCut
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x) {C : Set P.Edge}
    (hCcut : C ⊆ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (B.dualRestriction ω) x)) :
    B.primal.globalLabels C ⊆ edge.symm ''
      DualExhaustion.edgeCut GD (B.globalDualOpenComponent ω x) := by
  rintro f ⟨e, heC, rfl⟩
  refine ⟨B.dual.label e, (B.label_mem_globalEdgeCut_iff_mem_vertexCut
    hinj ω x hvertex hedge e).mpr (hCcut heC), ?_⟩
  calc
    edge.symm (B.dual.label e) = edge.symm (edge (B.primal.label e)) :=
      congrArg edge.symm (B.label_comm e)
    _ = B.primal.label e := edge.symm_apply_apply _

/-- A finite plane-dual embedding of a rotation-system dual. The global dual
label is definitionally the prescribed global edge image of the primal label,
so `label_comm` is not an additional compatibility assumption. -/
def ofRotationSystem {L : LabelledMultigraph}
    (R : FK.Finite.PlaneMatroid.Cellular.Rotation.RotationSystem L)
    (primalVertex : L.Vertex → V)
    (dualVertex : R.Face → F) (label : L.Edge → G.edgeSet)
    (primalEndpoint : ∀ e,
      s(primalVertex (L.source e), primalVertex (L.target e)) = (label e : Sym2 V))
    (dualEndpoint : ∀ e,
      s(dualVertex (R.faceOf (e, false)), dualVertex (R.faceOf (e, true))) =
        (edge (label e) : Sym2 F)) :
    LabelledDualPairEmbedding R.dualPair G GD edge where
  primal :=
    { vertex := primalVertex
      label := label
      endpoint := primalEndpoint }
  dual :=
    { vertex := dualVertex
      label := fun e => edge (label e)
      endpoint := dualEndpoint }
  label_comm := fun _ => rfl

/-- A primal circuit represented in the boundary of the actual global
simple-dual component becomes a spherical open circuit in the prescribed
global primal configuration. No finite-component cut membership is left in
the conclusion or the input. -/
theorem sphericalOpenCircuit_global_of_primalCircuit_subset_globalDualEdgeCut
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {vertex : V → X} {R : OpenPathRealization G vertex}
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x)
    {C : Set P.Edge} {c : X} {r : ℝ} (hr : 0 < r)
    (hcross : R.CrossingControlledBy (sphere c r) (B.primal.globalLabels C))
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (hCcut : ∀ e ∈ C, B.dual.label e ∈
      DualExhaustion.edgeCut GD (B.globalDualOpenComponent ω x))
    (hC : P.primal.cycleMatroid.IsCircuit C) :
    SphericalOpenCircuit R ω (B.primal.globalLabels C) c r := by
  apply B.sphericalOpenCircuit_global_of_primalCircuit_subset_dualOpenComponentBoundary
    ω x hr hcross hvertices ?_ hC
  intro e he
  exact (B.label_mem_globalEdgeCut_iff_mem_vertexCut hinj ω x hvertex hedge e).mp
    (hCcut e he)

/-- Existence of a global spherical primal circuit through any represented
label of the actual global dual-component cut. Graphic duality supplies the
finite circuit; the hypotheses above supply its exact global window. -/
theorem exists_sphericalOpenCircuit_global_of_mem_globalDualEdgeCut
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {vertex : V → X} {R : OpenPathRealization G vertex}
    (hP : P.GraphicDualCertificate)
    (hinj : Function.Injective B.dual.vertex) (ω : G.edgeSet → Bool) (x : P.Face)
    (hvertex : B.CoversGlobalDualComponentVertices ω x)
    (hedge : B.CoversGlobalDualComponentEdges ω x)
    {e : P.Edge} {c : X} {r : ℝ} (hr : 0 < r)
    (hcross : ∀ C : Set P.Edge, P.primal.cycleMatroid.IsCircuit C →
      R.CrossingControlledBy (sphere c r) (B.primal.globalLabels C))
    (hvertices : ∀ v, vertex v ∈ (sphere c r)ᶜ)
    (he : B.dual.label e ∈
      DualExhaustion.edgeCut GD (B.globalDualOpenComponent ω x)) :
    ∃ C : Set P.Edge, e ∈ C ∧
      SphericalOpenCircuit R ω (B.primal.globalLabels C) c r := by
  have heLocal : e ∈ P.faceDual.vertexCut
      (P.faceDual.openVertexComponent (B.dualRestriction ω) x) :=
    (B.label_mem_globalEdgeCut_iff_mem_vertexCut hinj ω x hvertex hedge e).mp he
  obtain ⟨C, hCcut, heC, hC, -, -⟩ :=
    P.exists_primalOpen_circuit_boundary_dualOpenComponent hP
      (B.primalRestriction ω) x heLocal
  refine ⟨C, heC, ?_⟩
  apply B.sphericalOpenCircuit_global_of_primalCircuit_subset_globalDualEdgeCut
    hinj ω x hvertex hedge hr (hcross C hC) hvertices ?_ hC
  intro f hf
  exact (B.label_mem_globalEdgeCut_iff_mem_vertexCut hinj ω x hvertex hedge f).mpr
    (hCcut hf)

end LabelledDualPairEmbedding

namespace DualExhaustion

open LabelledDualPairEmbedding

variable {V F : Type*} {P : LabelledDualPair} {G : SimpleGraph V}
variable {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}

/-- The constructed metric dual box discharges finite-window component
coverage once the window represents that box's vertices and all its internal
simple edges. The component containment itself comes from dual
nonpercolation and the closed-region exhaustion, not from the embedding. -/
theorem coversGlobalDualComponent_of_planarDualMetricExhaustion
    {X : Type*} [PseudoMetricSpace X] [Nonempty F]
    (B : LabelledDualPairEmbedding P G GD edge)
    (hGD : GD.Preconnected) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite)
    {n : ℕ} {x : P.Face}
    (hx : dualVertex (B.dual.vertex x) ∈ ball c (n : ℝ))
    (hboxVertices :
      (planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n ⊆
        Set.range B.dual.vertex)
    (hboxEdges : ∀ {a b : P.Face}
      (hab : GD.Adj (B.dual.vertex a) (B.dual.vertex b)),
      B.dual.vertex a ∈
        (planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n →
      B.dual.vertex b ∈
        (planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n →
      ∃ e : P.Edge, B.dual.label e =
        (⟨s(B.dual.vertex a, B.dual.vertex b), hab⟩ : GD.edgeSet)) :
    B.CoversGlobalDualComponentVertices ω x ∧
      B.CoversGlobalDualComponentEdges ω x := by
  let E := planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper
  have hsub : B.globalDualOpenComponent ω x ⊆ E.region n := by
    intro y hy
    exact dualComponent_subset_planarDualMetricExhaustion hGD edge ω hdual
      dualVertex c hproper hx hy
  constructor
  · exact hsub.trans hboxVertices
  · intro a b hab ha hb
    exact hboxEdges hab (hsub ha) (hsub hb)

end DualExhaustion

end FK.PlaneTopology

#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.ofRotationSystem
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.exists_local_reachable_of_walk
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.exists_local_reachable_of_openConnected
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.mem_openVertexComponent_iff_global
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.label_mem_globalEdgeCut_iff_mem_vertexCut
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.sphericalOpenCircuit_global_of_primalCircuit_subset_globalDualEdgeCut
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.exists_sphericalOpenCircuit_global_of_mem_globalDualEdgeCut
#print axioms FK.PlaneTopology.DualExhaustion.coversGlobalDualComponent_of_planarDualMetricExhaustion
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.globalLabels_vertexCut_eq_globalEdgeCut_inter_range
#print axioms FK.PlaneTopology.LabelledDualPairEmbedding.primal_globalLabels_subset_globalDualEdgeCut
