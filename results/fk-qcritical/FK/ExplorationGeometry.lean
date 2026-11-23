import FK.PlanarActual
import FK.ClosedBoundary
import FK.ClassicalCoupling

/-!
# Canonical outer exploration and maximal closed-cutset strata

The outer open region is the union of the open clusters based at the outer
boundary.  It is the smallest region containing the boundary whose outgoing
ambient edges are closed.  Consequently its complement is the maximal
interior separated from that boundary.  This is the deterministic geometry
used in Lemma 2.1; no edge ordering, chosen minimal cutset, decidability of
vertex equality, or exclusion of loops and parallel labelled edges is needed.
-/

namespace FK.Finite.Exploration

open Set
open scoped BigOperators ENNReal

open FK.Finite.LabelledMultigraph

variable {V : Type*}

/-- Membership in the outer explored region is precisely open reachability
from some outer-boundary vertex. -/
theorem mem_outerRegion_iff {H : SimpleGraph V} {B : Set V} {x : V} :
    x ∈ ClosedRegion H B ↔ ∃ b ∈ B, H.Reachable b x := by
  simp only [ClosedRegion, Set.mem_iUnion, FK.mem_openCluster_iff]
  constructor <;> rintro ⟨b, hb, hbx⟩ <;> exact ⟨b, hb, hbx⟩

/-- The outer explored region is the smallest closed-boundary region
containing `B`.  Thus the complementary interior is maximal. -/
theorem outerRegion_subset_of_closedBoundary {G H : SimpleGraph V}
    (hHG : H ≤ G) {B S : Set V} (hBS : B ⊆ S)
    (hS : ClosedBoundary G H S) : ClosedRegion H B ⊆ S := by
  intro x hx
  obtain ⟨b, hbB, hbx⟩ := mem_outerRegion_iff.mp hx
  clear hx
  rw [SimpleGraph.reachable_iff_reflTransGen] at hbx
  induction hbx with
  | refl => exact hBS hbB
  | tail hxy hyz ih =>
      by_contra hz
      exact hS ih hz (hHG hyz) hyz

/-- Absence of an open connection between two vertex sets is equivalent to
the first set lying in the maximal separated interior. -/
theorem no_open_connection_iff_subset_interior {H : SimpleGraph V}
    {A B : Set V} :
    (∀ a ∈ A, ∀ b ∈ B, ¬ H.Reachable a b) ↔
      A ⊆ (ClosedRegion H B)ᶜ := by
  constructor
  · intro hA a haA haOuter
    obtain ⟨b, hbB, hba⟩ := mem_outerRegion_iff.mp haOuter
    exact hA a haA b hbB hba.symm
  · intro hA a haA b hbB hab
    apply hA haA
    exact mem_outerRegion_iff.mpr ⟨b, hbB, hab.symm⟩

end FK.Finite.Exploration

namespace FK.Finite.LabelledMultigraph

open FK.Finite.Exploration

variable (G : FK.Finite.LabelledMultigraph)

/-- The open/wired graph used by outer exploration. -/
abbrev openGraph (ξ : G.BoundaryPartition) (ω : G.Configuration) : SimpleGraph G.Vertex :=
  G.connectionGraph ξ ω

/-- The ambient graph in which every labelled edge and every wiring
connection is available. -/
abbrev ambientGraph (ξ : G.BoundaryPartition) : SimpleGraph G.Vertex :=
  G.connectionGraph ξ G.allOpen

lemma openGraph_le_ambientGraph (ξ : G.BoundaryPartition) (ω : G.Configuration) :
    G.openGraph ξ ω ≤ G.ambientGraph ξ := by
  apply G.connectionGraph_mono
  intro e
  simp [LabelledMultigraph.allOpen]

/-- The canonical outer open region of a labelled configuration. -/
def outerRegion (ξ : G.BoundaryPartition) (B : Set G.Vertex)
    (ω : G.Configuration) : Set G.Vertex :=
  ClosedRegion (G.openGraph ξ ω) B

/-- Its complement is the maximal interior separated from the outer
boundary. -/
def interior (ξ : G.BoundaryPartition) (B : Set G.Vertex)
    (ω : G.Configuration) : Set G.Vertex :=
  (G.outerRegion ξ B ω)ᶜ

/-- An edge crosses the explored frontier when exactly one endpoint is in
 the outer region.  Both orientations are retained for labelled graphs. -/
def frontier (ξ : G.BoundaryPartition) (B : Set G.Vertex)
    (ω : G.Configuration) : Set G.Edge :=
  {e | (G.source e ∈ G.outerRegion ξ B ω ∧ G.target e ∉ G.outerRegion ξ B ω) ∨
    (G.target e ∈ G.outerRegion ξ B ω ∧ G.source e ∉ G.outerRegion ξ B ω)}

/-- Every canonical frontier edge is closed.  In particular loops cannot be
frontier edges, while distinct parallel labels are handled independently. -/
theorem frontier_isClosed (ξ : G.BoundaryPartition) (B : Set G.Vertex)
    (ω : G.Configuration) {e : G.Edge}
    (he : e ∈ G.frontier ξ B ω) : ω e = false := by
  apply Bool.eq_false_iff.mpr
  intro heOpen
  rcases he with he | he
  · have hne : G.source e ≠ G.target e := by
      intro hst
      exact he.2 (hst ▸ he.1)
    have hadjOpen : (G.openGraph ξ ω).Adj (G.source e) (G.target e) :=
      ⟨hne, Or.inr ⟨e, heOpen, Or.inl ⟨rfl, rfl⟩⟩⟩
    have hadjAmbient : (G.ambientGraph ξ).Adj (G.source e) (G.target e) :=
      G.openGraph_le_ambientGraph ξ ω hadjOpen
    exact closedRegion_closedBoundary he.1 he.2 hadjAmbient hadjOpen
  · have hne : G.target e ≠ G.source e := by
      intro hts
      exact he.2 (hts ▸ he.1)
    have hadjOpen : (G.openGraph ξ ω).Adj (G.target e) (G.source e) :=
      ⟨hne, Or.inr ⟨e, heOpen, Or.inr ⟨rfl, rfl⟩⟩⟩
    have hadjAmbient : (G.ambientGraph ξ).Adj (G.target e) (G.source e) :=
      G.openGraph_le_ambientGraph ξ ω hadjOpen
    exact closedRegion_closedBoundary he.1 he.2 hadjAmbient hadjOpen

/-- Every open path from a vertex of the maximal interior to the outer
boundary would cross an open frontier edge, hence cannot exist. -/
theorem not_reachable_of_mem_interior (ξ : G.BoundaryPartition) (B : Set G.Vertex)
    (ω : G.Configuration) {a : G.Vertex}
    (ha : a ∈ G.interior ξ B ω) {b : G.Vertex} (hb : b ∈ B) :
    ¬ (G.openGraph ξ ω).Reachable a b := by
  intro hab
  exact ha (mem_outerRegion_iff.mpr ⟨b, hb, hab.symm⟩)

/-- The canonical outer region is smallest among all regions containing `B`
whose outgoing ambient edges are closed. -/
theorem outerRegion_minimal (ξ : G.BoundaryPartition) (B : Set G.Vertex)
    (ω : G.Configuration) {S : Set G.Vertex} (hBS : B ⊆ S)
    (hS : ClosedBoundary (G.ambientGraph ξ) (G.openGraph ξ ω) S) :
    G.outerRegion ξ B ω ⊆ S := by
  exact outerRegion_subset_of_closedBoundary
    (G.openGraph_le_ambientGraph ξ ω) hBS hS

/-- The separated event used in Lemma 2.1, stated using the actual open graph
of the labelled configuration. -/
def separated (ξ : G.BoundaryPartition) (A B : Set G.Vertex) : Set G.Configuration :=
  {ω | ∀ a ∈ A, ∀ b ∈ B, ¬ (G.openGraph ξ ω).Reachable a b}

/-- On the separated event, `A` is contained in the canonical maximal
interior. -/
theorem separated_iff (ξ : G.BoundaryPartition) (A B : Set G.Vertex)
    (ω : G.Configuration) :
    ω ∈ G.separated ξ A B ↔ A ⊆ G.interior ξ B ω := by
  exact no_open_connection_iff_subset_interior

/-- A decomposition of the actual labelled configurations by the value of
 their canonical outer explored region. -/
def stratum (ξ : G.BoundaryPartition) (A B S : Set G.Vertex) : Set G.Configuration :=
  {ω | G.outerRegion ξ B ω = S ∧ A ⊆ Sᶜ}

/-- Canonical maximal-cutset strata are pairwise disjoint. -/
theorem stratum_pairwise_disjoint (ξ : G.BoundaryPartition) (A B : Set G.Vertex) :
    Pairwise (Function.onFun Disjoint (G.stratum ξ A B)) := by
  intro S T hST
  change Disjoint (G.stratum ξ A B S) (G.stratum ξ A B T)
  rw [Set.disjoint_left]
  intro ω hωS hωT
  exact hST (hωS.1.symm.trans hωT.1)

/-- The separated event is exhausted by its maximal-cutset strata. -/
theorem separated_eq_iUnion_stratum (ξ : G.BoundaryPartition) (A B : Set G.Vertex) :
    G.separated ξ A B = ⋃ S, G.stratum ξ A B S := by
  ext ω
  rw [Set.mem_iUnion]
  constructor
  · intro hω
    have hA : A ⊆ G.interior ξ B ω := (G.separated_iff ξ A B ω).mp hω
    exact ⟨G.outerRegion ξ B ω, rfl, hA⟩
  · rintro ⟨S, hS, hA⟩
    apply (G.separated_iff ξ A B ω).mpr
    change A ⊆ (G.outerRegion ξ B ω)ᶜ
    rwa [hS]

/-- Any exterior open edge incident with the maximal interior would have to
be a frontier edge.  This is the separation condition used when restricting
an exterior configuration to a maximal-cutset stratum. -/
theorem eq_false_of_open_of_endpoint_mem_interior
    (ξ : G.BoundaryPartition) (B : Set G.Vertex) (ω : G.Configuration)
    {e : G.Edge}
    (hs : G.source e ∈ G.interior ξ B ω ∨ G.target e ∈ G.interior ξ B ω)
    (hother : G.source e ∈ G.outerRegion ξ B ω ∨ G.target e ∈ G.outerRegion ξ B ω) :
    ω e = false := by
  apply G.frontier_isClosed ξ B ω
  rcases hs with hs | ht
  · rcases hother with hs' | ht'
    · exact (hs hs').elim
    · exact Or.inr ⟨ht', hs⟩
  · rcases hother with hs' | ht'
    · exact Or.inl ⟨hs', ht⟩
    · exact (ht ht').elim

/-- Open non-interior edges have no endpoint in the maximal interior.  When
interior labels are defined as those with both endpoints inside, this is
precisely the non-incidence condition required by
`FK.FinitePlane.exteriorBoundary_related_iff_of_no_open_incident`. -/
theorem source_and_target_not_mem_interior_of_open
    (ξ : G.BoundaryPartition) (B : Set G.Vertex) (ω : G.Configuration)
    {e : G.Edge} (heOpen : ω e = true)
    (he : ¬ (G.source e ∈ G.interior ξ B ω ∧ G.target e ∈ G.interior ξ B ω)) :
    G.source e ∉ G.interior ξ B ω ∧ G.target e ∉ G.interior ξ B ω := by
  constructor
  · intro hs
    have ht : G.target e ∈ G.outerRegion ξ B ω := by
      by_contra ht
      exact he ⟨hs, ht⟩
    have hc := G.eq_false_of_open_of_endpoint_mem_interior ξ B ω
      (e := e) (Or.inl hs) (Or.inr ht)
    simp [heOpen] at hc
  · intro ht
    have hs : G.source e ∈ G.outerRegion ξ B ω := by
      by_contra hs
      exact he ⟨hs, ht⟩
    have hc := G.eq_false_of_open_of_endpoint_mem_interior ξ B ω
      (e := e) (Or.inr ht) (Or.inl hs)
    simp [heOpen] at hc

/-- Measure equality on the separated event follows only from equality on
each canonical maximal-cutset stratum.  Disjointness, coverage and
measurability are discharged by the actual exploration geometry. -/
theorem measure_inter_eq_of_separated_stratification
    (ξ : G.BoundaryPartition) (A B : Set G.Vertex)
    (μ : MeasureTheory.Measure G.Configuration) {X Y : Set G.Configuration}
    (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hstratum : ∀ S, μ (X ∩ G.stratum ξ A B S) = μ (Y ∩ G.stratum ξ A B S)) :
    μ (X ∩ G.separated ξ A B) = μ (Y ∩ G.separated ξ A B) := by
  exact FKModel.measure_inter_eq_of_disjoint_stratification μ (G.stratum ξ A B)
    hX hY (G.separated_eq_iUnion_stratum ξ A B)
    (G.stratum_pairwise_disjoint ξ A B)
    (fun S => (Set.toFinite _).measurableSet) hstratum

end FK.Finite.LabelledMultigraph
