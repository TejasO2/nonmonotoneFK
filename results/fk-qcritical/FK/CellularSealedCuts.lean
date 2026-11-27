import FK.CombinatorialEnclosure
import FK.OpenCutSeparation

/-!
# Cofinal cellular sealed cuts

A cellular face potential gives a finite vertex region whose exit edges need
not be open: it is enough that each exit edge has an endpoint incident to one
open-connected circuit. This is the graph-theoretic form of vertex sealing.
It avoids both metric spheres and the false requirement that the whole
oriented cut be open.
-/

namespace FK.PlaneTopology.CellularSealed

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.CutSeparation

variable {V : Type*} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- A finite region sealed by an open-connected label set. Exit edges may be
closed, but each has an endpoint incident to the carrier. -/
structure SealedRegion (G : SimpleGraph V) (ω : G.edgeSet → Bool) where
  inside : Set V
  carrier : Set G.edgeSet
  finite_inside : inside.Finite
  carrier_open : ∀ e ∈ carrier, ω e = true
  carrier_connected : OpenLabelConnected G ω carrier
  sealed : ∀ {u v : V}, u ∈ inside → v ∉ inside → G.Adj u v →
    VertexOnLabels carrier u ∨ VertexOnLabels carrier v

namespace SealedRegion

/-- An open walk leaving a sealed finite region reaches the carrier by an
open prefix. -/
theorem exists_carrier_vertex_of_walk (S : SealedRegion G ω)
    {x z : V} (p : G.Walk x z) (hp : IsOpenIn ω Set.univ p)
    (hx : x ∈ S.inside) (hz : z ∉ S.inside) :
    ∃ u : V, VertexOnLabels S.carrier u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact (hz hx).elim
  | @cons a b c hab p ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      by_cases hb : b ∈ S.inside
      · obtain ⟨u, hu, hbu⟩ := ih hrest hb hz
        exact ⟨u, hu, (OpenConnected.of_adj hab (Set.mem_univ _) hopen).trans hbu⟩
      · rcases S.sealed hx hb hab with ha | hb'
        · exact ⟨a, ha, OpenConnected.refl _ _ _⟩
        · exact ⟨b, hb', OpenConnected.of_adj hab (Set.mem_univ _) hopen⟩

/-- Two infinite clusters rooted in one finite sealed region meet its common
open carrier and hence each other. -/
theorem openConnected_of_two_infinite (S : SealedRegion G ω)
    {x y : V} (hx : x ∈ S.inside) (hy : y ∈ S.inside)
    (hxinf : ExteriorInfiniteCluster G ω Set.univ x)
    (hyinf : ExteriorInfiniteCluster G ω Set.univ y) :
    OpenConnected G ω Set.univ x y := by
  have hex (a : V) (ha : a ∈ S.inside)
      (hainf : ExteriorInfiniteCluster G ω Set.univ a) :
      ∃ u : V, VertexOnLabels S.carrier u ∧ OpenConnected G ω Set.univ a u := by
    have hout : ∃ z : V, OpenConnected G ω Set.univ a z ∧ z ∉ S.inside := by
      by_contra! h
      exact hainf (S.finite_inside.subset fun z hz => h z hz)
    obtain ⟨z, haz, hz⟩ := hout
    obtain ⟨p, hp⟩ := haz
    exact S.exists_carrier_vertex_of_walk p hp ha hz
  obtain ⟨u, hu, hxu⟩ := hex x hx hxinf
  obtain ⟨v, hv, hyv⟩ := hex y hy hyinf
  exact hxu.trans ((S.carrier_connected hu hv).mono_edges (Set.subset_univ _) |>.trans
    (openConnected_symm hyv))

end SealedRegion

/-- Cofinal sealed regions imply at most one infinite open cluster. -/
theorem globalAtMostOne_of_cofinal_sealedRegions
    (h : ∀ x y : V, ∃ S : SealedRegion G ω, x ∈ S.inside ∧ y ∈ S.inside) :
    GlobalAtMostOne G ω := by
  intro x y hx hy
  obtain ⟨S, hxS, hyS⟩ := h x y
  exact S.openConnected_of_two_infinite hxS hyS hx hy

end FK.PlaneTopology.CellularSealed

namespace FK.Finite.PlaneMatroid.Cellular.Rotation

open scoped Classical
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph

variable {L : LabelledMultigraph} (R : RotationSystem L)

/-- One-step form of the cellular sealed-exit theorem. If an open adjacency
starts in a face-potential class and ends outside it, one endpoint is incident
to the potential's coboundary. -/
theorem vertexOnLabels_or_vertexOnLabels_of_adj_not_faceInterior
    {C : Set L.Edge} {q : R.Face → F2} {α : F2}
    (hpot : ∀ e : L.Edge, coboundary R.dualPair.faceDual q e ≠ 0 ↔ e ∈ C)
    {u v : L.Vertex}
    (w : (L.connectionGraph L.freeBoundary L.allOpen).Adj u v)
    (hu : FaceInterior R q α u) (hv : ¬ FaceInterior R q α v) :
    L.VertexOnLabels C u ∨ L.VertexOnLabels C v := by
  by_contra h
  push Not at h
  have huClear : ClearVertex C u := by
    by_contra hn
    exact h.1 (vertexOnLabels_of_not_clearVertex hn)
  have hvClear : ClearVertex C v := by
    by_contra hn
    exact h.2 (vertexOnLabels_of_not_clearVertex hn)
  have w' : (L.connectionGraph L.freeBoundary (L.setConfig Cᶜ)).Adj u v := by
    rcases w.2 with hfree | ⟨e, he, hjoin⟩
    · exact (w.1 hfree).elim
    · refine ⟨w.1, Or.inr ⟨e, ?_, hjoin⟩⟩
      have heC : e ∈ Cᶜ := by
        rcases hjoin with ⟨hs, -⟩ | ⟨-, ht⟩
        · exact huClear (e, false) hs
        · exact huClear (e, true) ht
      simp [LabelledMultigraph.setConfig, heC]
  exact hv (faceInterior_of_adj_compl R q α hpot w' huClear hvClear hu)

/-- Vertices all of whose incident faces belong to a prescribed face region. -/
def FacesInside (T : Set R.Face) : Set L.Vertex :=
  {v | ∀ d : Dart L, vertex L d = v → R.faceOf d ∈ T}

end FK.Finite.PlaneMatroid.Cellular.Rotation

namespace FK.PlaneTopology.CellularSealed

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology

namespace LabelledSimpleGraphEmbedding

variable {V : Type*} {L : LabelledMultigraph} {G : SimpleGraph V}
variable (B : LabelledSimpleGraphEmbedding L G)

/-- Exact incidence at the strict vertices of a face region: every global edge
at such a represented vertex, and its other endpoint, lift to the window. -/
def InteriorEdgeCoverage (R : RotationSystem L) (T : Set R.Face) : Prop :=
  ∀ {u : L.Vertex}, u ∈ FacesInside R T → ∀ {z : V} (h : G.Adj (B.vertex u) z),
    ∃ (e : L.Edge) (v : L.Vertex), L.Joins e u v ∧
      B.label e = (⟨s(B.vertex u, z), h⟩ : G.edgeSet) ∧ B.vertex v = z

/-- Mapping local circuit incidence to the prescribed global graph requires no
injectivity of either the vertex or label map. -/
theorem vertexOnLabels_global {C : Set L.Edge} {u : L.Vertex}
    (hu : L.VertexOnLabels C u) :
    VertexOnLabels (B.globalLabels C) (B.vertex u) := by
  obtain ⟨e, heC, hu⟩ := hu
  rcases hu with rfl | rfl
  · refine ⟨B.vertex (L.target e), B.adj_source_target e, ?_⟩
    rw [← B.label_eq_canonical e]
    exact ⟨e, heC, rfl⟩
  · refine ⟨B.vertex (L.source e), (B.adj_source_target e).symm, ?_⟩
    have heq : (⟨s(B.vertex (L.target e), B.vertex (L.source e)),
        (B.adj_source_target e).symm⟩ : G.edgeSet) = B.label e := by
      apply Subtype.ext
      rw [← B.endpoint e]
      exact Sym2.eq_swap
    rw [heq]
    exact ⟨e, heC, rfl⟩

/-- A circuit, a precisely identified face-potential class and exact strict
interior incidence produce a genuine global sealed region. -/
theorem exists_sealedRegion_of_facePotential
    {ω : G.edgeSet → Bool} (R : RotationSystem L)
    {C : Set L.Edge} {T : Set R.Face} {q : R.Face → F2} {α : F2}
    (hpot : ∀ e : L.Edge, coboundary R.dualPair.faceDual q e ≠ 0 ↔ e ∈ C)
    (hT : T = {z | q z = α})
    (hC : L.cycleMatroid.IsCircuit C)
    (hCopen : C ⊆ L.openEdgeSet (B.restriction ω))
    (hcover : InteriorEdgeCoverage B R T) :
    ∃ S : SealedRegion G ω,
      S.inside = B.vertex '' FacesInside R T ∧ S.carrier = B.globalLabels C := by
  refine ⟨{
    inside := B.vertex '' FacesInside R T
    carrier := B.globalLabels C
    finite_inside := Set.Finite.image B.vertex
      (Set.finite_univ.subset (Set.subset_univ _))
    carrier_open := B.globalLabels_open hCopen
    carrier_connected := B.openLabelConnected_global_of_cycleMatroid_isCircuit hCopen hC
    sealed := ?_ }, rfl, rfl⟩
  intro x y hx hy hxy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨e, v, hjoin, helabel, hvz⟩ := hcover hu hxy
  have hvInside : v ∉ FacesInside R T := by
    intro hv
    exact hy ⟨v, hv, hvz⟩
  have huInt : FaceInterior R q α u := by
    intro d hd
    have hdT := hu d hd
    rw [hT] at hdT
    exact hdT
  have hvInt : ¬ FaceInterior R q α v := by
    intro hv
    exact hvInside (fun d hd => by
      have hq := hv d hd
      rw [hT]
      exact hq)
  have huv : u ≠ v := by
    intro huv
    subst v
    exact hxy.ne hvz
  have wlocal : (L.connectionGraph L.freeBoundary L.allOpen).Adj u v := by
    refine ⟨huv, Or.inr ⟨e, by simp [LabelledMultigraph.allOpen], hjoin⟩⟩
  rcases vertexOnLabels_or_vertexOnLabels_of_adj_not_faceInterior R
      hpot wlocal huInt hvInt with huC | hvC
  · exact Or.inl (vertexOnLabels_global B huC)
  · rw [← hvz]
    exact Or.inr (vertexOnLabels_global B hvC)

end LabelledSimpleGraphEmbedding
end FK.PlaneTopology.CellularSealed

namespace FK.Finite.PlaneMatroid.Cellular.Rotation

open FK.Finite
open FK.Finite.LabelledMultigraph

variable {L : LabelledMultigraph} (R : RotationSystem L)

theorem facesInside_mono {S T : Set R.Face} (hST : S ⊆ T) :
    FacesInside R S ⊆ FacesInside R T := by
  intro v hv d hd
  exact hST (hv d hd)

end FK.Finite.PlaneMatroid.Cellular.Rotation

namespace FK.PlaneTopology.CellularSealed.LabelledSimpleGraphEmbedding

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology
open FK.PlaneTopology.CellularSealed

variable {V : Type*} {L : LabelledMultigraph} {G : SimpleGraph V}
variable (B : LabelledSimpleGraphEmbedding L G)

/-- **Global cellular enclosure, sealed form.** A finite spherical rotation
window and a dual box with closed open-component boundary yield a finite global
vertex region sealed by one open-connected primal circuit. The circuit is the
complete dual cut of its face region; both face regions are connected.

The only global geometric input is `hcover`: for each such circuit/face-region
pair, every global edge at a strict face-region vertex lifts, together with its
other endpoint, to the finite window. No spherical locus, all-open oriented cut,
or injectivity of the primal embedding is assumed. -/
theorem exists_sealedRegion_enclosing_dualBox
    (R : RotationSphere L) (ω : G.edgeSet → Bool)
    {D : Set R.Face} (hDne : D.Nonempty)
    (hDconn : (R.dualPair.faceDual.simpleGraph.induce D).Preconnected)
    (hDsat : R.dualPair.faceDual.OpenComponentSaturated
      (dualConfig (Equiv.refl L.Edge) (B.restriction ω)) D)
    {e : L.Edge} (he : e ∈ R.dualPair.faceDual.vertexCut D)
    (hcover : ∀ {C : Set L.Edge} {T : Set R.Face},
      C ⊆ R.dualPair.faceDual.vertexCut D →
      L.cycleMatroid.IsCircuit C →
      C = R.dualPair.faceDual.vertexCut T → InteriorEdgeCoverage B R.toRotationSystem T) :
    ∃ (S : SealedRegion G ω) (C : Set L.Edge) (T : Set R.Face),
      S.inside = B.vertex '' FacesInside R.toRotationSystem T ∧
      S.carrier = B.globalLabels C ∧
      C ⊆ R.dualPair.faceDual.vertexCut D ∧ e ∈ C ∧
      L.cycleMatroid.IsCircuit C ∧ D ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = R.dualPair.faceDual.vertexCut T ∧
      (R.dualPair.faceDual.simpleGraph.induce T).Preconnected ∧
      (R.dualPair.faceDual.simpleGraph.induce Tᶜ).Preconnected ∧
      B.vertex '' FacesInside R.toRotationSystem D ⊆ S.inside := by
  obtain ⟨C, _T₀, hCcut, heC, hC, _hDT₀, _hT₀fin, _hT₀proper, _hCeq₀⟩ :=
    Cellular.exists_primalCircuit_enclosing_dualBox R.dualPair R.cellularSphere
      hDne hDconn he
  obtain ⟨q, hpot⟩ := Cellular.exists_facePotential_of_primalCircuit
    R.dualPair R.cellularSphere hC
  obtain ⟨x, hxD⟩ := hDne
  have hqconst : ∀ y ∈ D, q y = q x := by
    intro y hy
    obtain ⟨w⟩ := hDconn ⟨x, hxD⟩ ⟨y, hy⟩
    exact (Cellular.potential_eq_of_induced_walk R.dualPair q hpot hCcut w).symm
  let _ : Fintype R.Face := R.dualPair.fintypeFace
  let T : Set R.Face := {z | q z = q x}
  have hDT : D ⊆ T := by
    intro y hy
    exact hqconst y hy
  have hCeq : C = R.dualPair.faceDual.vertexCut T := by
    change C = R.dualPair.faceDual.vertexCut {z | q z = q x}
    rw [Cellular.vertexCut_potentialClass R.dualPair q (q x)]
    ext f
    exact (hpot f).symm
  have hTfin : T.Finite := Set.toFinite T
  have hTproper : Tᶜ.Nonempty := by
    have heT : e ∈ R.dualPair.faceDual.vertexCut T := by rwa [← hCeq]
    rcases heT with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨R.dualPair.faceDual.target e, ht⟩
    · exact ⟨R.dualPair.faceDual.source e, hs⟩
  have hTconn : (R.dualPair.faceDual.simpleGraph.induce T).Preconnected :=
    Cellular.preconnected_region_of_primalCircuit_vertexCut
      R.dualPair R.cellularSphere hC hCeq
  have hCeqCompl : C = R.dualPair.faceDual.vertexCut Tᶜ := by
    rw [hCeq]
    exact (Cellular.vertexCut_compl R.dualPair.faceDual T).symm
  have hTcconn : (R.dualPair.faceDual.simpleGraph.induce Tᶜ).Preconnected :=
    Cellular.preconnected_region_of_primalCircuit_vertexCut
      R.dualPair R.cellularSphere hC hCeqCompl
  have hCopen : C ⊆ L.openEdgeSet (B.restriction ω) := by
    intro f hf
    have hd := R.dualPair.faceDual.closed_of_mem_vertexCut_of_openComponentSaturated
      hDsat (hCcut hf)
    change (!B.restriction ω f) = false at hd
    change B.restriction ω f = true
    cases h : B.restriction ω f <;> simp [h] at hd ⊢
  have hTdef : T = {z | q z = q x} := rfl
  obtain ⟨S, hSin, hScarrier⟩ := exists_sealedRegion_of_facePotential B
    R.toRotationSystem hpot hTdef hC hCopen (hcover hCcut hC hCeq)
  refine ⟨S, C, T, hSin, hScarrier, hCcut, heC, hC, hDT, hTfin, hTproper,
    hCeq, hTconn, hTcconn, ?_⟩
  rw [hSin]
  exact Set.image_mono (facesInside_mono R.toRotationSystem hDT)

end FK.PlaneTopology.CellularSealed.LabelledSimpleGraphEmbedding


namespace FK.PlaneTopology.CellularSealed.LabelledDualPairEmbedding

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.PlaneTopology

variable {V F : Type*} {P : LabelledDualPair} {G : SimpleGraph V}
variable {GD : SimpleGraph F} {edge : G.edgeSet ≃ GD.edgeSet}
variable (B : LabelledDualPairEmbedding P G GD edge)

/-- Exact representation of a global ambient dual box by the face vertices and
labels of a finite labelled plane-dual window. -/
structure DualRegionWindow (D : Set P.Face) (U : Set F) where
  injective : Function.Injective B.dual.vertex
  mem_iff : ∀ x, B.dual.vertex x ∈ U ↔ x ∈ D
  vertices : U ⊆ Set.range B.dual.vertex
  edges : ∀ {a b : P.Face} (hab : GD.Adj (B.dual.vertex a) (B.dual.vertex b)),
    B.dual.vertex a ∈ U → B.dual.vertex b ∈ U →
    ∃ e : P.Edge, B.dual.label e =
      (⟨s(B.dual.vertex a, B.dual.vertex b), hab⟩ : GD.edgeSet)

namespace DualRegionWindow

variable {D : Set P.Face} {U : Set F} (W : DualRegionWindow B D U)

/-- Lift a walk in an exactly represented global dual box to the local induced
face-dual graph. This is ambient-walk transport, not merely open-component
transport. -/
theorem exists_induced_reachable_of_walk
    (W : DualRegionWindow B D U) {a z : U} (p : (GD.induce U).Walk a z)
    (u : D) (ha : a.1 = B.dual.vertex u.1) :
    ∃ v : D, B.dual.vertex v.1 = z.1 ∧
      (P.faceDual.simpleGraph.induce D).Reachable u v := by
  induction p generalizing u with
  | nil => exact ⟨u, ha.symm, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hab p ih =>
      obtain ⟨v, hv⟩ := W.vertices b.2
      have hvD : v ∈ D := (W.mem_iff v).mp (by rw [hv]; exact b.2)
      let v' : D := ⟨v, hvD⟩
      have huvAdj : GD.Adj (B.dual.vertex u.1) (B.dual.vertex v'.1) := by
        change GD.Adj (B.dual.vertex u.1) (B.dual.vertex v)
        rw [← ha, hv]
        exact hab
      obtain ⟨e, he⟩ := W.edges huvAdj
        ((W.mem_iff u.1).mpr u.2) ((W.mem_iff v'.1).mpr v'.2)
      have hendpoints :
          s(B.dual.vertex (P.faceDual.source e), B.dual.vertex (P.faceDual.target e)) =
            s(B.dual.vertex u.1, B.dual.vertex v'.1) := by
        rw [B.dual.endpoint e, he]
      have hjoins : P.faceDual.Joins e u.1 v'.1 := by
        rcases Sym2.eq_iff.mp hendpoints with hst | hst
        · exact Or.inl ⟨W.injective hst.1, W.injective hst.2⟩
        · exact Or.inr ⟨W.injective hst.1, W.injective hst.2⟩
      have hne : u.1 ≠ v'.1 := by
        intro huv
        exact huvAdj.ne (congrArg B.dual.vertex huv)
      have hadj : (P.faceDual.simpleGraph.induce D).Adj u v' := by
        exact (P.faceDual.simpleGraph_adj_iff).2 ⟨hne, e, hjoins⟩
      obtain ⟨w, hw, hreach⟩ := ih v' hv.symm
      exact ⟨w, hw, (SimpleGraph.Adj.reachable hadj).trans hreach⟩

/-- Exact window transport of ambient preconnectedness. -/
theorem preconnected_induce (W : DualRegionWindow B D U)
    (hconn : (GD.induce U).Preconnected) :
    (P.faceDual.simpleGraph.induce D).Preconnected := by
  intro a b
  let a' : U := ⟨B.dual.vertex a.1, (W.mem_iff a.1).mpr a.2⟩
  let b' : U := ⟨B.dual.vertex b.1, (W.mem_iff b.1).mpr b.2⟩
  obtain ⟨p⟩ := hconn a' b'
  obtain ⟨v, hv, hpass⟩ := exists_induced_reachable_of_walk B W p a rfl
  have hvb : v = b := Subtype.ext (W.injective hv)
  simpa only [hvb] using hpass

/-- The global closed-frontier rule restricts to the exact labelled window. -/
theorem openComponentSaturated_of_closedBoundary (W : DualRegionWindow B D U)
    (ω : G.edgeSet → Bool)
    (hclosed : ClosedBoundary GD (openGraph GD (openSet (dualConfig edge ω))) U) :
    P.faceDual.OpenComponentSaturated (B.dualRestriction ω) D := by
  intro e he
  have heGlobal : dualConfig edge ω (B.dual.label e) = true := by
    rw [← B.dualRestriction_apply ω e]
    exact he
  have hG : GD.Adj (B.dual.vertex (P.faceDual.source e))
      (B.dual.vertex (P.faceDual.target e)) := B.dual.adj_source_target e
  have heCanon : B.dual.label e =
      (⟨s(B.dual.vertex (P.faceDual.source e),
        B.dual.vertex (P.faceDual.target e)), hG⟩ : GD.edgeSet) :=
    B.dual.label_eq_canonical e
  have hopen : (openGraph GD (openSet (dualConfig edge ω))).Adj
      (B.dual.vertex (P.faceDual.source e)) (B.dual.vertex (P.faceDual.target e)) := by
    rw [openGraph, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨⟨s(B.dual.vertex (P.faceDual.source e),
      B.dual.vertex (P.faceDual.target e)), hG⟩, ?_, rfl⟩, hG.ne⟩
    rw [← heCanon]
    exact heGlobal
  constructor
  · intro hs
    by_contra ht
    exact hclosed ((W.mem_iff _).mpr hs) (fun h => ht ((W.mem_iff _).mp h)) hG hopen
  · intro ht
    by_contra hs
    exact hclosed ((W.mem_iff _).mpr ht) (fun h => hs ((W.mem_iff _).mp h))
      hG.symm hopen.symm

end DualRegionWindow
end FK.PlaneTopology.CellularSealed.LabelledDualPairEmbedding

namespace FK.PlaneTopology.CellularSealed.LabelledDualPairEmbedding

open Set Metric
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.PlaneTopology
open FK.PlaneTopology.CellularSealed
open FK.PlaneTopology.CellularSealed.LabelledSimpleGraphEmbedding

variable {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F}
variable {edge : G.edgeSet ≃ GD.edgeSet}

/-- One metric dual box, exactly represented in a rotation-system window,
produces the global sealed enclosure. This theorem uses dual nonpercolation
through `planarDualMetricExhaustion`; it is not an assumed local closedness or
component-finiteness certificate. -/
theorem exists_sealedRegion_of_metricDualBox
    {X : Type*} [PseudoMetricSpace X] [Nonempty F] [GD.LocallyFinite]
    (hGD : GD.Preconnected) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite)
    {L : LabelledMultigraph} (R : RotationSphere L)
    (B : LabelledDualPairEmbedding R.dualPair G GD edge)
    (D : Set R.Face)
    (W : DualRegionWindow B D
      ((DualExhaustion.planarDualMetricExhaustion hGD edge ω hdual
        dualVertex c hproper).region n))
    {e : L.Edge} (he : e ∈ R.dualPair.faceDual.vertexCut D)
    (hcover : ∀ {C : Set L.Edge} {T : Set R.Face},
      C ⊆ R.dualPair.faceDual.vertexCut D →
      L.cycleMatroid.IsCircuit C →
      C = R.dualPair.faceDual.vertexCut T →
      LabelledSimpleGraphEmbedding.InteriorEdgeCoverage B.primal R.toRotationSystem T) :
    ∃ (S : SealedRegion G ω) (C : Set L.Edge) (T : Set R.Face),
      S.inside = B.primal.vertex '' FacesInside R.toRotationSystem T ∧
      S.carrier = B.primal.globalLabels C ∧
      C ⊆ R.dualPair.faceDual.vertexCut D ∧ e ∈ C ∧
      L.cycleMatroid.IsCircuit C ∧ D ⊆ T ∧ T.Finite ∧ Tᶜ.Nonempty ∧
      C = R.dualPair.faceDual.vertexCut T ∧
      (R.dualPair.faceDual.simpleGraph.induce T).Preconnected ∧
      (R.dualPair.faceDual.simpleGraph.induce Tᶜ).Preconnected ∧
      B.primal.vertex '' FacesInside R.toRotationSystem D ⊆ S.inside := by
  let E := DualExhaustion.planarDualMetricExhaustion hGD edge ω hdual
    dualVertex c hproper
  have hUne : (E.region n).Nonempty := by
    obtain ⟨z⟩ := (E.connected n).nonempty
    exact ⟨z.1, z.2⟩
  obtain ⟨z, hzU⟩ := hUne
  obtain ⟨x, hx⟩ := W.vertices hzU
  have hxU : B.dual.vertex x ∈ E.region n := by rw [hx]; exact hzU
  have hDne : D.Nonempty := ⟨x, (W.mem_iff x).mp hxU⟩
  have hDconn : (R.dualPair.faceDual.simpleGraph.induce D).Preconnected :=
    DualRegionWindow.preconnected_induce B W (E.connected n).preconnected
  have hDsat : R.dualPair.faceDual.OpenComponentSaturated
      (dualConfig (Equiv.refl L.Edge) (B.primalRestriction ω)) D := by
    exact DualRegionWindow.openComponentSaturated_of_closedBoundary B W ω (E.closed n)
  exact LabelledSimpleGraphEmbedding.exists_sealedRegion_enclosing_dualBox
    B.primal R ω hDne hDconn hDsat he hcover

end FK.PlaneTopology.CellularSealed.LabelledDualPairEmbedding

namespace FK.PlaneTopology.CellularSealed

open Set Metric
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.Finite.PlaneMatroid
open FK.Finite.PlaneMatroid.Cellular
open FK.Finite.PlaneMatroid.Cellular.Rotation
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.CellularSealed.LabelledSimpleGraphEmbedding
open FK.PlaneTopology.CellularSealed.LabelledDualPairEmbedding

/-- **Dual nonpercolation to primal at-most-one, through exact cellular
windows.** The metric dual exhaustion is constructed from `hdual` inside the
proof. Each finite window is a spherical rotation system with exact global
vertex/edge incidence on its dual box. For every circuit face region, global
edges at strict interior vertices lift with their other endpoint. The windows
are cofinal in the concrete sense that any two primal vertices occur as strict
face-interior vertices of one dual box.

Unlike the older spherical-cut criterion, closed exit edges are allowed: every
exit edge need only have an endpoint on the common open-connected circuit. -/
theorem globalAtMostOne_of_dualNonpercolation_of_cofinalCellularWindows
    {V F X : Type*} [PseudoMetricSpace X]
    {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F] [GD.LocallyFinite]
    {edge : G.edgeSet ≃ GD.edgeSet}
    (hGD : GD.Preconnected) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite)
    (L : ℕ → LabelledMultigraph) (R : ∀ n, RotationSphere (L n))
    (B : ∀ n, LabelledDualPairEmbedding (R n).dualPair G GD edge)
    (D : ∀ n, Set (R n).Face)
    (W : ∀ n, LabelledDualPairEmbedding.DualRegionWindow (B n) (D n)
      ((DualExhaustion.planarDualMetricExhaustion hGD edge ω hdual
        dualVertex c hproper).region n))
    (e : ∀ n, (L n).Edge)
    (he : ∀ n, e n ∈ (R n).dualPair.faceDual.vertexCut (D n))
    (hcover : ∀ (n : ℕ) {C : Set (L n).Edge} {T : Set (R n).Face},
      C ⊆ (R n).dualPair.faceDual.vertexCut (D n) →
      (L n).cycleMatroid.IsCircuit C →
      C = (R n).dualPair.faceDual.vertexCut T →
      InteriorEdgeCoverage (B n).primal (R n).toRotationSystem T)
    (hcofinal : ∀ x y : V, ∃ (n : ℕ) (u v : (L n).Vertex),
      (B n).primal.vertex u = x ∧ (B n).primal.vertex v = y ∧
      u ∈ FacesInside (R n).toRotationSystem (D n) ∧
      v ∈ FacesInside (R n).toRotationSystem (D n)) :
    GlobalAtMostOne G ω := by
  apply globalAtMostOne_of_cofinal_sealedRegions
  intro x y
  obtain ⟨n, u, v, hux, hvy, huD, hvD⟩ := hcofinal x y
  obtain ⟨S, C, T, hSin, hScarrier, hCcut, heC, hC, hDT, hTfin, hTproper,
    hCeq, hTconn, hTcconn, hDinside⟩ :=
    LabelledDualPairEmbedding.exists_sealedRegion_of_metricDualBox
      hGD ω hdual dualVertex c hproper (R n) (B n) (D n) (W n) (he n) (hcover n)
  exact ⟨S, hDinside ⟨u, huD, hux⟩, hDinside ⟨v, hvD, hvy⟩⟩

end FK.PlaneTopology.CellularSealed
