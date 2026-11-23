import FK.Proposition42Interior
import FK.ConventionTransport
import FK.FKQuasiTransitiveDevices

/-!
# Star cutsets and the finite-box boundary condition

This file isolates the geometric boundary hypothesis used in the proof of
Proposition 4.2.  A global incidence star does not by itself give a finite
`CutsetFamily` certificate when the boundary partition is allowed to identify
interior vertices.  The exact extra condition is that the star center have a
singleton boundary class.
-/

open Set
open scoped SimpleGraph Sym2 Classical

namespace FK.Finite.LabelledMultigraph

open FKEnhancement
open FK.FiniteFiber
open FK.Finite.Conditional
open FK.Finite.LabelledMultigraph

variable (G : FK.Finite.LabelledMultigraph)

/-- All labelled edges incident to a vertex, excluding no edge. -/
noncomputable def incidentEdges (c : G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter (fun a => G.source a = c ∨ G.target a = c)

@[simp] lemma mem_incidentEdges {c : G.Vertex} {a : G.Edge} :
    a ∈ G.incidentEdges c ↔ G.source a = c ∨ G.target a = c := by
  classical
  simp [incidentEdges]

/-- The other edges of the incidence star at `c`, with the pivot erased. -/
noncomputable def starCutset (c : G.Vertex) (e : G.Edge) : Finset G.Edge := by
  classical
  exact (G.incidentEdges c).erase e

@[simp] lemma mem_starCutset {c : G.Vertex} {e a : G.Edge} :
    a ∈ G.starCutset c e ↔ a ≠ e ∧ (G.source a = c ∨ G.target a = c) := by
  classical
  simp [starCutset]

/-- A boundary partition cannot use the vertex `c` to connect distinct points.
This is the finite-box replacement for saying that `c` is not on the geometric
boundary on which the source paper defines its boundary partition. -/
def HasSingletonBoundaryClass (ξ : G.BoundaryPartition) (c : G.Vertex) : Prop :=
  ∀ u, ξ.r c u → u = c

lemma hasSingletonBoundaryClass_free (c : G.Vertex) :
    G.HasSingletonBoundaryClass G.freeBoundary c := by
  intro u h
  exact h.symm


/-- Under fully wired boundary on all vertices, every non-loop pivot is already
connected without using itself. -/
lemma graphConnectionEvent_wiredBoundary (e : G.Edge) (ω : G.Configuration)
    (hne : G.source e ≠ G.target e) : graphConnectionEvent G G.wiredBoundary e ω := by
  change (G.connectionGraph G.wiredBoundary (withEdge e false ω)).Reachable
    (G.source e) (G.target e)
  exact SimpleGraph.Adj.reachable ⟨hne, Or.inl trivial⟩

/-- No set of closed edges can be a cutset at a non-loop under the unrestricted
fully wired boundary.  This records why the singleton-class hypothesis is not
redundant in the all-vertex `BoundaryPartition` model. -/
lemma not_isClosedCutset_wiredBoundary (e : G.Edge)
    (hne : G.source e ≠ G.target e) (χ : Set G.Edge) :
    ¬ IsClosedCutset (graphConnectionEvent G G.wiredBoundary) e χ := by
  intro hcut
  exact hcut (fun _ => false) (fun _ _ => rfl)
    (G.graphConnectionEvent_wiredBoundary e (fun _ => false) hne)

/-- Under the singleton-boundary-class condition, closing the other star edges
isolates `c` in the graph defining the FK connection event. -/
lemma not_adj_of_starCutset_closed
    (ξ : G.BoundaryPartition) (e : G.Edge) (c : G.Vertex)
    (hc : G.HasSingletonBoundaryClass ξ c) (ω : G.Configuration)
    (hclosed : ∀ a ∈ G.starCutset c e, ω a = false)
    {u : G.Vertex} :
    ¬ (G.connectionGraph ξ (withEdge e false ω)).Adj c u := by
  intro hadj
  rcases hadj.2 with hwire | ⟨a, haopen, hjoin⟩
  · exact hadj.1 (hc u hwire).symm
  · have hac : G.source a = c ∨ G.target a = c := by
      rcases hjoin with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    have hafalse : withEdge e false ω a = false := by
      by_cases hae : a = e
      · subst a
        simp
      · rw [withEdge_off hae]
        exact hclosed a (G.mem_starCutset.mpr ⟨hae, hac⟩)
    rw [hafalse] at haopen
    contradiction

/-- A vertex with all non-pivot star edges closed and with singleton boundary
class is not reachable from a distinct vertex in the off-pivot connection
graph. -/
lemma reachable_eq_of_starCutset_closed
    (ξ : G.BoundaryPartition) (e : G.Edge) (c : G.Vertex)
    (hc : G.HasSingletonBoundaryClass ξ c) (ω : G.Configuration)
    (hclosed : ∀ a ∈ G.starCutset c e, ω a = false)
    {u : G.Vertex} (hreach :
      (G.connectionGraph ξ (withEdge e false ω)).Reachable c u) : u = c := by
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => rfl
  | cons hadj p =>
      exact (G.not_adj_of_starCutset_closed ξ e c hc ω hclosed hadj).elim

/-- The erased incidence star is an actual closed cutset for the FK
endpoint-connection predicate.  The pivot must be incident to `c` and must not
be a loop. -/
lemma starCutset_isClosedCutset
    (ξ : G.BoundaryPartition) (e : G.Edge) (c : G.Vertex)
    (hsource : G.source e = c ∨ G.target e = c)
    (hne : G.source e ≠ G.target e)
    (hc : G.HasSingletonBoundaryClass ξ c) :
    IsClosedCutset (graphConnectionEvent G ξ) e (G.starCutset c e : Set G.Edge) := by
  intro ω hclosed hconn
  change (G.connectionGraph ξ (withEdge e false ω)).Reachable
    (G.source e) (G.target e) at hconn
  rcases hsource with hs | ht
  · rw [hs] at hconn hne
    exact hne (G.reachable_eq_of_starCutset_closed ξ e c hc ω hclosed hconn).symm
  · rw [ht] at hconn hne
    exact hne (G.reachable_eq_of_starCutset_closed ξ e c hc ω hclosed hconn.symm)

/-- Auxiliary membership for the erased star is exactly the condition needed
in addition to its cutset property. -/
lemma starCutset_isAuxiliary (enhanced : Set G.Edge) (e : G.Edge) (c : G.Vertex)
    (haux : ∀ a ∈ G.incidentEdges c, a ≠ e → a ∉ enhanced) :
    IsAuxiliary enhanced e (G.starCutset c e : Set G.Edge) := by
  intro a ha
  have ha' : a ≠ e ∧ (G.source a = c ∨ G.target a = c) :=
    G.mem_starCutset.mp ha
  exact ⟨haux a (G.mem_incidentEdges.mpr ha'.2) ha'.1, ha'.1⟩

/-- Corrected finite-box star certificate.  In particular, arbitrary boundary
setoids on all vertices require `HasSingletonBoundaryClass`; the global star
and its separation property do not imply this condition. -/
theorem starCutset_mem_cutsetFamily
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) (e : G.Edge) (c : G.Vertex)
    (hsource : G.source e = c ∨ G.target e = c)
    (hne : G.source e ≠ G.target e)
    (hc : G.HasSingletonBoundaryClass ξ c)
    (haux : ∀ a ∈ G.incidentEdges c, a ≠ e → a ∉ enhanced) :
    (G.starCutset c e : Set G.Edge) ∈
      CutsetFamily (graphConnectionEvent G ξ) enhanced e := by
  exact ⟨G.starCutset_isAuxiliary enhanced e c haux,
    G.starCutset_isClosedCutset ξ e c hsource hne hc⟩

lemma mem_incidentEdges_of_endpoint {e : G.Edge} {c : G.Vertex}
    (hc : G.source e = c ∨ G.target e = c) : e ∈ G.incidentEdges c :=
  G.mem_incidentEdges.mpr hc

lemma card_starCutset_le {Delta : ℕ} {e : G.Edge} {c : G.Vertex}
    (hc : G.source e = c ∨ G.target e = c)
    (hcard : (G.incidentEdges c).card ≤ Delta) :
    (G.starCutset c e).card ≤ Delta - 1 := by
  classical
  rw [starCutset, Finset.card_erase_of_mem (G.mem_incidentEdges_of_endpoint hc)]
  exact Nat.sub_le_sub_right hcard 1

end FK.Finite.LabelledMultigraph

namespace FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData

open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionGeometry
open FK.Finite.LabelledMultigraph

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FiniteBox G.edgeSet}

/-- Every global edge incident to the image of a box vertex belongs to the box.
This is the local content of containing an entire global incidence star. -/
def StarContained (data : SimpleGraphBoxData G box) (n : ℕ) (c : (box n).Vertex) : Prop :=
  ∀ f : G.edgeSet, data.vertex n c ∈ (f : Sym2 V) → f ∈ (box n).edges

/-- A box-contained star center has no nontrivial exterior-open path after all
box edges are closed. -/
lemma openConnected_eq_of_starContained (data : SimpleGraphBoxData G box)
    {n : ℕ} {c : (box n).Vertex} (hc : data.StarContained n c)
    (η : (box n).Exterior) {y : V}
    (hy : OpenConnected G (closeInside (box n) η) Set.univ (data.vertex n c) y) :
    y = data.vertex n c := by
  obtain ⟨p, hp⟩ := hy
  cases p with
  | nil => rfl
  | @cons _ z _ hadj p =>
      let f : G.edgeSet := ⟨s(data.vertex n c, z), hadj⟩
      have hcf : data.vertex n c ∈ (f : Sym2 V) := by simp [f]
      have hfbox : f ∈ (box n).edges := hc f hcf
      have hclosed : closeInside (box n) η f = false := by
        simp [closeInside, FiniteBox.glue, hfbox]
      rw [isOpenIn_cons] at hp
      have hopen := hp.1.2
      change closeInside (box n) η f = true at hopen
      rw [hclosed] at hopen
      contradiction

/-- In particular, a box-contained star center has a finite exterior cluster,
so wired-at-infinity cannot merge it with another component. -/
lemma not_infinite_of_starContained (data : SimpleGraphBoxData G box)
    {n : ℕ} {c : (box n).Vertex} (hc : data.StarContained n c)
    (η : (box n).Exterior)
    (hinf : ExteriorInfiniteCluster G (closeInside (box n) η) Set.univ
      (data.vertex n c)) : False := by
  have hset : {y | OpenConnected G (closeInside (box n) η) Set.univ
      (data.vertex n c) y} = {data.vertex n c} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (data.openConnected_eq_of_starContained hc η hy)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact OpenConnected.refl _ _ _
  change {y | OpenConnected G (closeInside (box n) η) Set.univ
    (data.vertex n c) y}.Infinite at hinf
  rw [hset] at hinf
  exact hinf (Set.finite_singleton _)

/-- Every geometrically valid convention separates the singleton exterior
component at a box-contained star center from every other component.  Together
with injectivity of the box vertex map, this gives the exact finite-box
boundary condition used by the source proof. -/
lemma hasSingletonBoundaryClass_of_isGeometric (data : SimpleGraphBoxData G box)
    [Countable V] (Φ : BoundaryAssignment box) (hΦ : IsGeometric data.geometry Φ)
    (n : ℕ) (c : (box n).Vertex) (hc : data.StarContained n c)
    (hinj : Function.Injective (data.vertex n)) (η : (box n).Exterior) :
    (box n).graph.HasSingletonBoundaryClass (Φ.partition n η) c := by
  intro u hcu
  have hcomp : (data.geometry.components n η).r c u := by
    by_contra hncomp
    have hninf : ¬ data.geometry.infinite n η c := by
      intro hinf
      exact data.not_infinite_of_starContained hc η hinf
    exact (hΦ.2 n η hncomp (Or.inl hninf)) hcu
  apply hinj
  exact data.openConnected_eq_of_starContained hc η hcomp

/-- For the canonical free convention, containment of a star and injectivity
of the box vertex map imply the exact singleton-class condition required by
the finite star cutset theorem. -/
lemma free_hasSingletonBoundaryClass (data : SimpleGraphBoxData G box)
    [Countable V] (n : ℕ) (c : (box n).Vertex) (hc : data.StarContained n c)
    (hinj : Function.Injective (data.vertex n)) (η : (box n).Exterior) :
    (box n).graph.HasSingletonBoundaryClass (data.free.partition n η) c := by
  intro u hcu
  apply hinj
  exact data.openConnected_eq_of_starContained hc η hcu

/-- The same correction holds for the canonical wired-at-infinity convention.
The free-component branch uses injectivity; the infinite-component branch is
ruled out by finiteness of the contained star center's exterior cluster. -/
lemma wired_hasSingletonBoundaryClass (data : SimpleGraphBoxData G box)
    [Countable V] (n : ℕ) (c : (box n).Vertex) (hc : data.StarContained n c)
    (hinj : Function.Injective (data.vertex n)) (η : (box n).Exterior) :
    (box n).graph.HasSingletonBoundaryClass (data.wired.partition n η) c := by
  intro u hcu
  change OpenConnected G (closeInside (box n) η) Set.univ (data.vertex n c)
      (data.vertex n u) ∨
    (ExteriorInfiniteCluster G (closeInside (box n) η) Set.univ (data.vertex n c) ∧
      ExteriorInfiniteCluster G (closeInside (box n) η) Set.univ (data.vertex n u)) at hcu
  rcases hcu with hcomp | ⟨hinf, _⟩
  · apply hinj
    exact data.openConnected_eq_of_starContained hc η hcomp
  · exact (data.not_infinite_of_starContained hc η hinf).elim

/-- Every locally incident edge maps into the global incidence star at the
corresponding vertex. -/
lemma mem_starDevice_of_incident (data : SimpleGraphBoxData G box)
    [G.LocallyFinite] (n : ℕ) (c : (box n).Vertex) (v : V)
    (hvc : data.vertex n c = v) {a : (box n).edges}
    (ha : (box n).source a = c ∨ (box n).target a = c) :
    a.1 ∈ FK.QuasiTransitive.starDevice G v := by
  apply (FK.QuasiTransitive.mem_starDevice G).mpr
  rw [← hvc, ← data.endpoint n a, Sym2.mem_iff]
  rcases ha with hs | ht
  · exact Or.inl (congrArg (data.vertex n) hs.symm)
  · exact Or.inr (congrArg (data.vertex n) ht.symm)

/-- The localized incidence star has at most as many edges as the compatible
global star.  The proof maps the labelled box edges injectively by their
underlying global labels. -/
lemma card_incidentEdges_le_starDevice (data : SimpleGraphBoxData G box)
    [G.LocallyFinite] (n : ℕ) (c : (box n).Vertex) (v : V)
    (hvc : data.vertex n c = v) :
    ((box n).graph.incidentEdges c).card ≤
      (FK.QuasiTransitive.starDevice G v).card := by
  classical
  let incl : (box n).edges ↪ G.edgeSet := Function.Embedding.subtype _
  let mapped := ((box n).graph.incidentEdges c).map incl
  have hsub : mapped ⊆ FK.QuasiTransitive.starDevice G v := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hf
    exact data.mem_starDevice_of_incident n c v hvc
      ((box n).graph.mem_incidentEdges.mp ha)
  have hcard := Finset.card_le_card hsub
  simpa [mapped, incl] using hcard

/-- The labelled endpoints of a box edge are distinct because its compatible
global edge belongs to a simple graph. -/
lemma source_ne_target (data : SimpleGraphBoxData G box) (n : ℕ)
    (e : (box n).edges) : (box n).source e ≠ (box n).target e := by
  intro hst
  apply G.not_isDiag_of_mem_edgeSet e.1.2
  rw [← data.endpoint n e, hst]
  simp

/-- Convert an actual separated global star into the finite cutset certificate
required by `Proposition42Interior`.  The extra boundary hypothesis is stated
exactly at the selected local center and uses box-containment of the full star.
For canonical free/wired boundaries it is proved by the two preceding
`hasSingletonBoundaryClass` lemmas under vertex-map injectivity. -/
theorem exists_starCutset_of_global_star (data : SimpleGraphBoxData G box)
    [G.LocallyFinite] {S : Set G.edgeSet} {D : G.edgeSet → Finset G.edgeSet}
    (hsep : FKLimit.IsSeparatedDeviceFamily S D) {n : ℕ} {e : (box n).edges}
    {v : V} (hv : v ∈ (e.1 : Sym2 V)) (hD : D e.1 = FK.QuasiTransitive.starDevice G v)
    (hsub : D e.1 ⊆ (box n).edges) (heS : e.1 ∈ S)
    (enhanced : Set (box n).edges) (henh : ∀ a ∈ enhanced, a.1 ∈ S)
    (ξ : (box n).graph.BoundaryPartition)
    (hξ : ∀ c : (box n).Vertex, data.vertex n c = v → data.StarContained n c →
      (box n).graph.HasSingletonBoundaryClass ξ c)
    {Delta : ℕ} (hcard : (D e.1).card ≤ Delta) :
    ∃ χ : Finset (box n).edges,
      (χ : Set (box n).edges) ∈
        FKEnhancement.CutsetFamily (FKEnhancement.graphConnectionEvent (box n).graph ξ)
          enhanced e ∧ χ.card ≤ Delta - 1 := by
  classical
  have hv' : v ∈ s(data.vertex n ((box n).source e),
      data.vertex n ((box n).target e)) := by
    rw [data.endpoint n e]
    exact hv
  rw [Sym2.mem_iff] at hv'
  obtain ⟨c, hvc, hce⟩ : ∃ c : (box n).Vertex, data.vertex n c = v ∧
      ((box n).source e = c ∨ (box n).target e = c) := by
    rcases hv' with hvs | hvt
    · exact ⟨(box n).source e, hvs.symm, Or.inl rfl⟩
    · exact ⟨(box n).target e, hvt.symm, Or.inr rfl⟩
  have hc : data.StarContained n c := by
    intro f hf
    apply hsub
    rw [hD]
    apply (FK.QuasiTransitive.mem_starDevice G).mpr
    rwa [← hvc]
  have haux : ∀ a ∈ (box n).graph.incidentEdges c, a ≠ e → a ∉ enhanced := by
    intro a ha hae haenh
    have hfa : a.1 ∈ D e.1 := by
      rw [hD]
      exact data.mem_starDevice_of_incident n c v hvc
        ((box n).graph.mem_incidentEdges.mp ha)
    have hgae : a.1 ≠ e.1 := by
      intro h
      exact hae (Subtype.ext h)
    exact (hsep e.1 heS).2 a.1 hfa hgae (henh a haenh)
  refine ⟨(box n).graph.starCutset c e, ?_, ?_⟩
  · exact (box n).graph.starCutset_mem_cutsetFamily ξ enhanced e c hce
      (data.source_ne_target n e) (hξ c hvc hc) haux
  · apply (box n).graph.card_starCutset_le hce
    calc
      ((box n).graph.incidentEdges c).card ≤
          (FK.QuasiTransitive.starDevice G v).card :=
        data.card_incidentEdges_le_starDevice n c v hvc
      _ = (D e.1).card := congrArg Finset.card hD.symm
      _ ≤ Delta := hcard

/-- Exact finite-box `hStarDevices` input for a separated family of actual
stars and any geometrically valid convention.  Admissibility remains an input;
this theorem supplies the cutset and its uniform `Delta - 1` cardinality bound. -/
theorem exists_starCutset_of_active_geometric {exh : BoxExhaustion G.edgeSet}
    (data : SimpleGraphBoxData G exh.box) [Countable V] [G.LocallyFinite]
    (Φ : BoundaryAssignment exh.box) (hΦ : IsGeometric data.geometry Φ)
    {S : Set G.edgeSet} {D : G.edgeSet → Finset G.edgeSet}
    (hsep : FKLimit.IsSeparatedDeviceFamily S D)
    {admissible : ℕ → G.edgeSet → Prop} {Delta : ℕ}
    (hstar : ∀ f ∈ S, ∃ v : V, D f = FK.QuasiTransitive.starDevice G v ∧
      v ∈ (f : Sym2 V))
    (hcard : ∀ f ∈ S, (D f).card ≤ Delta)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {n : ℕ} (η : (exh.box n).Exterior) (e : (exh.box n).edges)
    (he : e.1 ∈ FKLimit.activeEdges (FK.EnhancedTransport.edgeExhaustionOfBox exh)
      S D admissible n) :
    ∃ χ : Finset (exh.box n).edges,
      (χ : Set (exh.box n).edges) ∈ FKEnhancement.CutsetFamily
        (FKEnhancement.graphConnectionEvent (exh.box n).graph (Φ.partition n η))
        (↑(FK.EnhancedTransport.activeWithinFinset (exh.box n)
          (FKLimit.activeEdges (FK.EnhancedTransport.edgeExhaustionOfBox exh)
            S D admissible n)) : Set (exh.box n).edges) e ∧
      χ.card ≤ Delta - 1 := by
  classical
  have he' := FKLimit.mem_activeEdges.mp he
  obtain ⟨v, hD, hv⟩ := hstar e.1 he'.2.1
  apply data.exists_starCutset_of_global_star hsep hv hD he'.2.2.1 he'.2.1
      (ξ := Φ.partition n η) (hcard := hcard e.1 he'.2.1)
  · intro a ha
    have ha' : a.1 ∈ FKLimit.activeEdges (FK.EnhancedTransport.edgeExhaustionOfBox exh)
        S D admissible n :=
      FK.EnhancedTransport.mem_activeWithinFinset.mp ha
    exact (FKLimit.mem_activeEdges.mp ha').2.1
  · intro c _hvc hc
    exact data.hasSingletonBoundaryClass_of_isGeometric Φ hΦ n c hc (hinj n) η

end FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData

#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.exists_starCutset_of_active_geometric
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.exists_starCutset_of_global_star
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.hasSingletonBoundaryClass_of_isGeometric
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.free_hasSingletonBoundaryClass
#print axioms FK.InfiniteVolume.ConventionTransport.SimpleGraphBoxData.wired_hasSingletonBoundaryClass
#print axioms FK.Finite.LabelledMultigraph.not_isClosedCutset_wiredBoundary
#print axioms FK.Finite.LabelledMultigraph.starCutset_isClosedCutset
#print axioms FK.Finite.LabelledMultigraph.starCutset_mem_cutsetFamily
#print axioms FK.Finite.LabelledMultigraph.card_starCutset_le
