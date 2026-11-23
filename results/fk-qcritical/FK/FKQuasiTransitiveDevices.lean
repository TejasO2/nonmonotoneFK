import FK.AGEdgeGadget
import FK.Proposition42Interior

/-!
# Quasi-transitive graphs and geometric enhancement devices

This file constructs the geometric inputs to the device packing argument in
Theorem 1.4.  Quasi-transitivity means finitely many vertex orbits under the
full graph automorphism group.  We prove bounded degree, transport distances
and double rays, and bound line-graph distances using vertex walks.  Later
sections turn a finite device template into a uniformly local family and pack
it into the separated finite-device interface used by Proposition 4.2.
-/

open Set
open scoped SimpleGraph Sym2

namespace FK.QuasiTransitive

universe u

variable {V : Type u} {W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- A graph is quasi-transitive when its full automorphism group has finitely
many vertex orbits.  No bounded-degree or local-cycle conclusion is included. -/
def IsQuasiTransitive (G : SimpleGraph V) : Prop :=
  Finite (MulAction.orbitRel.Quotient (G ≃g G) V)

/-- Graph isomorphisms decrease extended distance along their forward map. -/
theorem iso_edist_le (φ : G ≃g G') (u v : V) :
    G'.edist (φ u) (φ v) ≤ G.edist u v := by
  by_cases h : G.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_edist
    rw [← hp]
    simpa using SimpleGraph.edist_le (p.map φ.toHom)
  · have h' : ¬ G'.Reachable (φ u) (φ v) := by
      intro h'
      exact h (φ.reachable_iff.mp h')
    rw [SimpleGraph.edist_eq_top_of_not_reachable h,
      SimpleGraph.edist_eq_top_of_not_reachable h']

/-- Graph isomorphisms preserve extended distance. -/
theorem iso_edist_eq (φ : G ≃g G') (u v : V) :
    G'.edist (φ u) (φ v) = G.edist u v := by
  apply le_antisymm
  · exact iso_edist_le φ u v
  · have h := iso_edist_le φ.symm (φ u) (φ v)
    simpa using h

/-- Graph isomorphisms preserve natural-valued graph distance. -/
theorem iso_dist_eq (φ : G ≃g G') (u v : V) :
    G'.dist (φ u) (φ v) = G.dist u v := by
  simp only [SimpleGraph.dist, iso_edist_eq]

/-- Every vertex is in the orbit of the representative of its orbit class. -/
lemma exists_iso_out_apply (v : V) :
    ∃ φ : G ≃g G, φ (Quotient.mk'' v : MulAction.orbitRel.Quotient (G ≃g G) V).out = v := by
  let q : MulAction.orbitRel.Quotient (G ≃g G) V := Quotient.mk'' v
  have hq : (Quotient.mk'' q.out : MulAction.orbitRel.Quotient (G ≃g G) V) =
      Quotient.mk'' v := q.out_eq'
  have hrel : (MulAction.orbitRel (G ≃g G) V) v q.out := Quotient.exact hq.symm
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨φ, hφ⟩ := hrel
  exact ⟨φ, hφ⟩

/-- A locally finite quasi-transitive graph has finite maximal degree. -/
theorem exists_degree_bound (G : SimpleGraph V) (hconn : G.Connected)
    (hqt : IsQuasiTransitive G) [G.LocallyFinite] :
    ∃ Δ : ℕ, ∀ v, G.degree v ≤ Δ := by
  letI : Nonempty V := hconn.nonempty
  letI : Finite (MulAction.orbitRel.Quotient (G ≃g G) V) := hqt
  letI : Nonempty (MulAction.orbitRel.Quotient (G ≃g G) V) :=
    ⟨Quotient.mk'' (Classical.choice hconn.nonempty)⟩
  obtain ⟨q, hq⟩ := Finite.exists_max
    (fun q : MulAction.orbitRel.Quotient (G ≃g G) V => G.degree q.out)
  refine ⟨G.degree q.out, fun v => ?_⟩
  obtain ⟨φ, hφ⟩ := exists_iso_out_apply (G := G) v
  rw [← hφ, φ.degree_eq]
  exact hq (Quotient.mk'' v)

namespace SimpleGraph

/-- Two incident edges are either equal or adjacent in the line graph. -/
lemma lineGraph_walk_one {e f : G.edgeSet} {v : V}
    (he : v ∈ (e : Sym2 V)) (hf : v ∈ (f : Sym2 V)) :
    ∃ p : G.lineGraph.Walk e f, p.length ≤ 1 := by
  by_cases h : e = f
  · subst f
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · have hadj : G.lineGraph.Adj e f :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨h, ⟨v, he, hf⟩⟩
    exact ⟨hadj.toWalk, by simp⟩

/-- A vertex walk joins any edge incident to its first vertex to any edge
incident to its last vertex, with at most one extra line-graph step. -/
lemma exists_lineGraph_walk_of_walk {u v : V} (p : G.Walk u v)
    {e f : G.edgeSet} (he : u ∈ (e : Sym2 V)) (hf : v ∈ (f : Sym2 V)) :
    ∃ P : G.lineGraph.Walk e f, P.length ≤ p.length + 1 := by
  induction p generalizing e with
  | nil => simpa using (lineGraph_walk_one (G := G) he hf)
  | @cons u w v h p ih =>
      let g : G.edgeSet := ⟨s(u, w), by simpa [SimpleGraph.mem_edgeSet] using h⟩
      have hug : u ∈ (g : Sym2 V) := by simp [g]
      have hwg : w ∈ (g : Sym2 V) := by simp [g]
      obtain ⟨P, hP⟩ := ih (e := g) hwg hf
      by_cases heq : e = g
      · subst e
        refine ⟨P, ?_⟩
        simp only [SimpleGraph.Walk.length_cons]
        omega
      · have hadj : G.lineGraph.Adj e g :=
          SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨heq, ⟨u, he, hug⟩⟩
        refine ⟨SimpleGraph.Walk.cons hadj P, ?_⟩
        simp only [SimpleGraph.Walk.length_cons]
        omega

/-- Line-graph distance is at most vertex distance plus one after choosing an
incident edge at each endpoint. -/
lemma lineGraph_dist_le_vertex_dist_add_one (hconn : G.Connected)
    {u v : V} {e f : G.edgeSet}
    (he : u ∈ (e : Sym2 V)) (hf : v ∈ (f : Sym2 V)) :
    G.lineGraph.dist e f ≤ G.dist u v + 1 := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨P, hP⟩ := exists_lineGraph_walk_of_walk p he hf
  exact (G.lineGraph.dist_le P).trans (hP.trans (by omega))

end SimpleGraph

@[simp] lemma iso_coe_mapEdgeSet (φ : G ≃g G') (e : G.edgeSet) :
    ((φ.mapEdgeSet e : G'.edgeSet) : Sym2 W) = Sym2.map φ (e : Sym2 V) := rfl

lemma iso_mem_mapEdgeSet (φ : G ≃g G') {v : V} {e : G.edgeSet}
    (hv : v ∈ (e : Sym2 V)) : φ v ∈ ((φ.mapEdgeSet e : G'.edgeSet) : Sym2 W) := by
  rw [iso_coe_mapEdgeSet, Sym2.mem_map]
  exact ⟨v, hv, rfl⟩

open FK.EssentialEnhancement

/-- Push a double ray forward through a graph isomorphism. -/
def doubleRayMap (r : DoubleRay G) (φ : G ≃g G') : DoubleRay G' where
  vertex n := φ (r.vertex n)
  vertex_injective := φ.injective.comp r.vertex_injective
  adj n := φ.toHom.map_adj (r.adj n)

@[simp] lemma doubleRayMap_edge (r : DoubleRay G) (φ : G ≃g G') (k : ℤ) :
    (doubleRayMap r φ).edge k = φ.mapEdgeSet (r.edge k) := by
  apply Subtype.ext
  rfl

/-- Being on a double ray is invariant under graph automorphisms. -/
theorem onDoubleRay_mapEdgeSet {e : G.edgeSet} (he : OnDoubleRay e) (φ : G ≃g G') :
    OnDoubleRay (G := G') (φ.mapEdgeSet e) := by
  obtain ⟨r, k, hk⟩ := he
  exact ⟨doubleRayMap r φ, k, by rw [doubleRayMap_edge, hk]⟩

/-- A connected graph with an edge has connected line graph. -/
theorem lineGraph_connected (G : SimpleGraph V) (hconn : G.Connected)
    [Nonempty G.edgeSet] : G.lineGraph.Connected := by
  constructor
  · intro e f
    let u : V := (e : Sym2 V).out.1
    let v : V := (f : Sym2 V).out.1
    have hu : u ∈ (e : Sym2 V) := Sym2.out_fst_mem _
    have hv : v ∈ (f : Sym2 V) := Sym2.out_fst_mem _
    obtain ⟨p⟩ := hconn u v
    obtain ⟨P, _⟩ := SimpleGraph.exists_lineGraph_walk_of_walk p hu hv
    exact ⟨P⟩

/-- The orbit of one edge is uniformly close to every edge in line-graph
distance.  The bound depends only on the orbit representatives and the seed. -/
theorem exists_orbitEdge_close (G : SimpleGraph V) (hconn : G.Connected)
    (hqt : IsQuasiTransitive G) (e₀ : G.edgeSet) :
    ∃ K : ℕ, ∀ e : G.edgeSet, ∃ φ : G ≃g G,
      G.lineGraph.dist e (φ.mapEdgeSet e₀) ≤ K := by
  letI : Nonempty V := hconn.nonempty
  letI : Finite (MulAction.orbitRel.Quotient (G ≃g G) V) := hqt
  letI : Nonempty (MulAction.orbitRel.Quotient (G ≃g G) V) :=
    ⟨Quotient.mk'' (Classical.choice hconn.nonempty)⟩
  let u₀ : V := (e₀ : Sym2 V).out.1
  have hu₀ : u₀ ∈ (e₀ : Sym2 V) := Sym2.out_fst_mem _
  obtain ⟨q, hq⟩ := Finite.exists_max
    (fun q : MulAction.orbitRel.Quotient (G ≃g G) V => G.dist q.out u₀)
  refine ⟨G.dist q.out u₀ + 1, fun e => ?_⟩
  let u : V := (e : Sym2 V).out.1
  have hu : u ∈ (e : Sym2 V) := Sym2.out_fst_mem _
  obtain ⟨φ, hφ⟩ := exists_iso_out_apply (G := G) u
  refine ⟨φ, ?_⟩
  have hu₀' : φ u₀ ∈ ((φ.mapEdgeSet e₀ : G.edgeSet) : Sym2 V) :=
    iso_mem_mapEdgeSet φ hu₀
  calc
    G.lineGraph.dist e (φ.mapEdgeSet e₀) ≤ G.dist u (φ u₀) + 1 :=
      SimpleGraph.lineGraph_dist_le_vertex_dist_add_one hconn hu hu₀'
    _ = G.dist (φ (Quotient.mk'' u : MulAction.orbitRel.Quotient (G ≃g G) V).out)
        (φ u₀) + 1 := by rw [hφ]
    _ = G.dist (Quotient.mk'' u : MulAction.orbitRel.Quotient (G ≃g G) V).out u₀ + 1 := by
      rw [iso_dist_eq]
    _ ≤ G.dist q.out u₀ + 1 := Nat.add_le_add_right (hq (Quotient.mk'' u)) 1

/-- The finite support obtained by translating a template. -/
noncomputable def translateSupport (φ : G ≃g G) (T : Finset G.edgeSet) :
    Finset G.edgeSet := T.map φ.mapEdgeSet.toEmbedding

/-- Support membership is just translation by the graph automorphism. -/@[simp] lemma mem_translateSupport_iff {φ : G ≃g G} {T : Finset G.edgeSet}
    {f : G.edgeSet} :
    f ∈ translateSupport φ T ↔ ∃ e ∈ T, φ.mapEdgeSet e = f := by
  change f ∈ T.map φ.mapEdgeSet.toEmbedding ↔ _
  constructor
  · intro hf
    obtain ⟨e, he, hef⟩ := Finset.mem_map.mp hf
    exact ⟨e, he, hef⟩
  · rintro ⟨e, he, rfl⟩
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩

@[simp] lemma card_translateSupport (φ : G ≃g G) (T : Finset G.edgeSet) :
    (translateSupport φ T).card = T.card := by
  simp [translateSupport]

/-- All translates of one finite template have the same diameter bound about
its distinguished edge. -/
lemma exists_translateSupport_diam (T : Finset G.edgeSet) {e₀ : G.edgeSet}
    (he₀ : e₀ ∈ T) :
    ∃ R : ℕ, ∀ (φ : G ≃g G) (f : G.edgeSet), f ∈ translateSupport φ T →
      G.lineGraph.dist f (φ.mapEdgeSet e₀) ≤ R := by
  classical
  obtain ⟨fmax, hfmaxmem, hfmax⟩ := Finset.exists_max_image T
    (fun f => G.lineGraph.dist f e₀) ⟨e₀, he₀⟩
  refine ⟨G.lineGraph.dist fmax e₀, fun φ f hf => ?_⟩
  obtain ⟨g, hg, rfl⟩ := mem_translateSupport_iff.mp hf
  have happ : φ.lineGraph g = φ.mapEdgeSet g := by
    apply Subtype.ext
    rfl
  have happ₀ : φ.lineGraph e₀ = φ.mapEdgeSet e₀ := by
    apply Subtype.ext
    rfl
  rw [← happ, ← happ₀, iso_dist_eq]
  exact hfmax g hg

/-- A quasi-transitive pivot orbit and a finite template give a uniform local
supply of whole devices. -/
lemma exists_translateSupport_localCover (G : SimpleGraph V) (hconn : G.Connected)
    (hqt : IsQuasiTransitive G) (T : Finset G.edgeSet) {e₀ : G.edgeSet}
    (he₀ : e₀ ∈ T) :
    ∃ K : ℕ, ∀ e : G.edgeSet, ∃ φ : G ≃g G, ∀ f ∈ translateSupport φ T,
      G.lineGraph.dist e f ≤ K := by
  obtain ⟨K, hK⟩ := exists_orbitEdge_close G hconn hqt e₀
  obtain ⟨R, hR⟩ := exists_translateSupport_diam T he₀
  letI : Nonempty G.edgeSet := ⟨e₀⟩
  have hLG : G.lineGraph.Connected := lineGraph_connected G hconn
  refine ⟨K + R, fun e => ?_⟩
  obtain ⟨φ, hφ⟩ := hK e
  refine ⟨φ, fun f hf => ?_⟩
  calc
    G.lineGraph.dist e f ≤ G.lineGraph.dist e (φ.mapEdgeSet e₀) +
        G.lineGraph.dist (φ.mapEdgeSet e₀) f := hLG.dist_triangle
    _ ≤ K + R := Nat.add_le_add hφ (by
      rw [SimpleGraph.dist_comm]
      exact hR φ f hf)

/-- The support selected for a pivot in a packed family.  Outside that family
it is empty, so no default device is needed. -/
noncomputable def selectedSupport {E Device : Type*} (support : Device → Finset E)
    (pivot : Device → E) (M : Set Device) (e : E) : Finset E := by
  classical
  exact if h : ∃ d, d ∈ M ∧ pivot d = e then support (Classical.choose h) else ∅

lemma selectedSupport_eq_of_mem {E Device : Type*} {support : Device → Finset E}
    {pivot : Device → E} {M : Set Device} {e : E}
    (h : ∃ d, d ∈ M ∧ pivot d = e) :
    selectedSupport support pivot M e = support (Classical.choose h) := by
  classical
  simp [selectedSupport, h]

lemma selectedSupport_spec {E Device : Type*} {support : Device → Finset E}
    {pivot : Device → E} {M : Set Device} {e : E}
    (h : ∃ d, d ∈ M ∧ pivot d = e) :
    Classical.choose h ∈ M ∧ pivot (Classical.choose h) = e ∧
      selectedSupport support pivot M e = support (Classical.choose h) :=
  ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2,
    selectedSupport_eq_of_mem h⟩

/-- The auxiliary-edge conclusion of maximal packing is exactly the separated
finite-device interface used in the infinite-volume comparisons. -/
lemma isSeparatedDeviceFamily_selectedSupport {E Device : Type*}
    (support : Device → Finset E) (pivot : Device → E) (M : Set Device)
    (hpivot : ∀ d, pivot d ∈ support d)
    (haux : ∀ d ∈ M, ∀ e ∈ (support d : Set E), e ≠ pivot d →
      e ∉ pivot '' M) :
    FKLimit.IsSeparatedDeviceFamily (pivot '' M) (selectedSupport support pivot M) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := he
  let h : ∃ d', d' ∈ M ∧ pivot d' = pivot d := ⟨d, hd, rfl⟩
  let d' := Classical.choose h
  have hd' : d' ∈ M ∧ pivot d' = pivot d := Classical.choose_spec h
  have hDe : selectedSupport support pivot M (pivot d) = support d' :=
    selectedSupport_eq_of_mem h
  constructor
  · rw [hDe, ← hd'.2]
    exact hpivot d'
  · intro f hf hne
    rw [hDe] at hf
    apply haux d' hd'.1 f hf
    intro hfe
    exact hne (hfe.trans hd'.2)

lemma exists_selectedSupport_spec {E Device : Type*} {support : Device → Finset E}
    {pivot : Device → E} {M : Set Device} {e : E} (he : e ∈ pivot '' M) :
    ∃ d ∈ M, pivot d = e ∧ selectedSupport support pivot M e = support d := by
  obtain ⟨d, hd, rfl⟩ := he
  let h : ∃ d', d' ∈ M ∧ pivot d' = pivot d := ⟨d, hd, rfl⟩
  let d' := Classical.choose h
  have hd' : d' ∈ M ∧ pivot d' = pivot d := Classical.choose_spec h
  exact ⟨d', hd'.1, hd'.2, selectedSupport_eq_of_mem h⟩

/-- **Uniform packed devices on a quasi-transitive graph.**  A finite template
containing a double-ray edge produces a bounded-distance, separated family of
finite devices.  Every selected support is an automorphic translate of the
original template and has the same cardinality. -/
theorem exists_separated_template_devices (G : SimpleGraph V) (hconn : G.Connected)
    (hqt : IsQuasiTransitive G) (T : Finset G.edgeSet) {e₀ : G.edgeSet}
    (he₀ : e₀ ∈ T) (hr₀ : OnDoubleRay e₀) :
    ∃ (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ T.card) ∧
      (∀ e ∈ S, ∃ φ : G ≃g G,
        D e = translateSupport φ T ∧ e = φ.mapEdgeSet e₀) := by
  classical
  obtain ⟨K, hK⟩ := exists_translateSupport_localCover G hconn hqt T he₀
  obtain ⟨R, hR⟩ := exists_translateSupport_diam T he₀
  letI : Nonempty G.edgeSet := ⟨e₀⟩
  have hLG : G.lineGraph.Connected := lineGraph_connected G hconn
  let support : (G ≃g G) → Finset G.edgeSet := fun φ => translateSupport φ T
  let pivot : (G ≃g G) → G.edgeSet := fun φ => φ.mapEdgeSet e₀
  have hpivot : ∀ φ, pivot φ ∈ support φ := by
    intro φ
    exact mem_translateSupport_iff.mpr ⟨e₀, he₀, rfl⟩
  obtain ⟨M, hMsub, hMpair, hMaux, hMmeet, hMdense⟩ :=
    FK.DevicePacking.exists_uniform_device_packing
      (fun φ : G ≃g G => (support φ : Set G.edgeSet)) Set.univ pivot hpivot
      G.lineGraph.dist (fun _ _ _ => hLG.dist_triangle) K R
      (fun e => by
        obtain ⟨φ, hφ⟩ := hK e
        exact ⟨φ, Set.mem_univ _, hφ⟩)
      (fun φ _ f hf => hR φ f hf)
  let S : Set G.edgeSet := pivot '' M
  let D : G.edgeSet → Finset G.edgeSet := selectedSupport support pivot M
  have hsep : FKLimit.IsSeparatedDeviceFamily S D := by
    exact isSeparatedDeviceFamily_selectedSupport support pivot M hpivot hMaux
  refine ⟨S, D, hsep, ⟨K + R, hMdense⟩, ?_, ?_, ?_⟩
  · rintro e ⟨φ, hφ, rfl⟩
    exact onDoubleRay_mapEdgeSet hr₀ φ
  · intro e he
    obtain ⟨φ, hφM, hpe, hDe⟩ := exists_selectedSupport_spec (support := support) he
    change (selectedSupport support pivot M e).card ≤ T.card
    rw [hDe]
    simpa [support] using (card_translateSupport φ T).le
  · intro e he
    obtain ⟨φ, hφM, hpe, hDe⟩ := exists_selectedSupport_spec (support := support) he
    exact ⟨φ, by simpa [D, support] using hDe, hpe.symm⟩

/-- The finite star consisting of every edge incident to `v`. -/
noncomputable def starDevice (G : SimpleGraph V) [G.LocallyFinite] (v : V) :
    Finset G.edgeSet := by
  classical
  exact (G.incidenceFinset v).attach.map
    { toFun := fun e => ⟨e.1, G.incidenceSet_subset v (by
        simpa only [SimpleGraph.mem_incidenceFinset] using e.2)⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        have h' := congrArg (fun z : G.edgeSet => (z : Sym2 V)) h
        simpa using h' }

@[simp] lemma mem_starDevice (G : SimpleGraph V) [G.LocallyFinite] {v : V}
    {e : G.edgeSet} : e ∈ starDevice G v ↔ v ∈ (e : Sym2 V) := by
  classical
  constructor
  · intro he
    change e ∈ (G.incidenceFinset v).attach.map _ at he
    obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp he
    have ha' : (a : Sym2 V) ∈ G.incidenceSet v :=
      SimpleGraph.mem_incidenceFinset.mp a.2
    have hval : (a : Sym2 V) = (e : Sym2 V) :=
      congrArg (fun z : G.edgeSet => (z : Sym2 V)) hae
    rw [← hval]
    exact ha'.2
  · intro he
    change e ∈ (G.incidenceFinset v).attach.map _
    let a : {x // x ∈ G.incidenceFinset v} := ⟨(e : Sym2 V),
      SimpleGraph.mem_incidenceFinset.mpr ((G.edge_mem_incidenceSet_iff).mpr he)⟩
    refine Finset.mem_map.mpr ⟨a, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

@[simp] lemma card_starDevice (G : SimpleGraph V) [G.LocallyFinite] (v : V) :
    (starDevice G v).card = G.degree v := by
  classical
  simp [starDevice]

/-- The finite edge support of a walk, without assuming finiteness of the
whole graph edge type. -/
noncomputable def walkDevice {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    Finset G.edgeSet := by
  classical
  exact (p.edges.attach.map
    (fun e => ⟨e.1, p.edges_subset_edgeSet e.2⟩)).toFinset

@[simp] lemma mem_walkDevice {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    {e : G.edgeSet} : e ∈ walkDevice p ↔ (e : Sym2 V) ∈ p.edges := by
  classical
  change e ∈ (p.edges.attach.map _).toFinset ↔ _
  rw [List.mem_toFinset]
  constructor
  · intro he
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp he
    have hval : (a : Sym2 V) = (e : Sym2 V) :=
      congrArg (fun z : G.edgeSet => (z : Sym2 V)) hae
    rw [← hval]
    exact a.2
  · intro he
    let a : {x // x ∈ p.edges} := ⟨(e : Sym2 V), he⟩
    apply List.mem_map.mpr
    exact ⟨a, List.mem_attach _ _, by apply Subtype.ext; rfl⟩

lemma card_walkDevice_le_length {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    (walkDevice p).card ≤ p.length := by
  classical
  change (p.edges.attach.map _).toFinset.card ≤ p.length
  calc
    _ ≤ (p.edges.attach.map _).length := List.toFinset_card_le _
    _ = p.edges.length := by simp
    _ = p.length := p.length_edges

@[simp] lemma iso_mapEdgeSet_symm_map (φ : G ≃g G') (e : G'.edgeSet) :
    φ.mapEdgeSet (φ.symm.mapEdgeSet e) = e := by
  apply Subtype.ext
  change Sym2.map φ (Sym2.map φ.symm (e : Sym2 W)) = (e : Sym2 W)
  simp [Sym2.map_map]

@[simp] lemma iso_symm_mapEdgeSet_map (φ : G ≃g G') (e : G.edgeSet) :
    φ.symm.mapEdgeSet (φ.mapEdgeSet e) = e := by
  apply Subtype.ext
  change Sym2.map φ.symm (Sym2.map φ (e : Sym2 V)) = (e : Sym2 V)
  simp [Sym2.map_map]

lemma mem_translateSupport_preimage_iff {φ : G ≃g G} {T : Finset G.edgeSet}
    {e : G.edgeSet} : φ.symm.mapEdgeSet e ∈ T ↔ e ∈ translateSupport φ T := by
  constructor
  · intro he
    exact mem_translateSupport_iff.mpr ⟨φ.symm.mapEdgeSet e, he,
      iso_mapEdgeSet_symm_map φ e⟩
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_translateSupport_iff.mp he
    simpa only [iso_symm_mapEdgeSet_map] using hf

/-- Automorphisms translate stars to stars. -/
lemma translateSupport_starDevice (G : SimpleGraph V) [G.LocallyFinite]
    (φ : G ≃g G) (v : V) :
    translateSupport φ (starDevice G v) = starDevice G (φ v) := by
  ext e
  rw [← mem_translateSupport_preimage_iff, mem_starDevice, mem_starDevice]
  constructor
  · intro he
    have h := iso_mem_mapEdgeSet φ he
    rw [iso_mapEdgeSet_symm_map] at h
    exact h
  · intro he
    have h := iso_mem_mapEdgeSet φ.symm he
    rw [show φ.symm (φ v) = v from φ.toEquiv.symm_apply_apply v] at h
    exact h

/-- Automorphisms translate walk supports to supports of mapped walks. -/
lemma translateSupport_walkDevice {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (φ : G ≃g G) :
    translateSupport φ (walkDevice p) = walkDevice (p.map φ.toHom) := by
  ext e
  rw [← mem_translateSupport_preimage_iff, mem_walkDevice, mem_walkDevice,
    SimpleGraph.Walk.edges_map]
  constructor
  · intro he
    apply List.mem_map.mpr
    refine ⟨(φ.symm.mapEdgeSet e : G.edgeSet), he, ?_⟩
    have hmap := congrArg (fun z : G.edgeSet => (z : Sym2 V))
      (iso_mapEdgeSet_symm_map φ e)
    change Sym2.map φ (Sym2.map φ.symm (e : Sym2 V)) = (e : Sym2 V)
    exact hmap
  · intro he
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp he
    have hraw : ((φ.symm.mapEdgeSet e : G.edgeSet) : Sym2 V) = a := by
      rw [iso_coe_mapEdgeSet, ← hae, Sym2.map_map]
      simp
    rw [hraw]
    exact ha

/-- **Separated star devices from quasi-transitivity.**  The same construction
also produces the uniform maximal-degree bound.  Each selected support is an
actual incidence star at a vertex incident to its double-ray pivot. -/
theorem exists_separated_star_devices (G : SimpleGraph V) (hconn : G.Connected)
    (hqt : IsQuasiTransitive G) [G.LocallyFinite] (u₀ : V) {e₀ : G.edgeSet}
    (hu₀ : u₀ ∈ (e₀ : Sym2 V)) (hr₀ : OnDoubleRay e₀) :
    ∃ (Delta : ℕ) (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      (∀ v, G.degree v ≤ Delta) ∧
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ Delta) ∧
      (∀ e ∈ S, ∃ v : V, D e = starDevice G v ∧ v ∈ (e : Sym2 V)) := by
  obtain ⟨Delta, hDelta⟩ := exists_degree_bound G hconn hqt
  obtain ⟨S, D, hsep, hbounded, hray, hcard, hwitness⟩ :=
    exists_separated_template_devices G hconn hqt (starDevice G u₀)
      ((mem_starDevice G).mpr hu₀) hr₀
  refine ⟨Delta, S, D, hDelta, hsep, hbounded, hray, ?_, ?_⟩
  · intro e he
    calc
      (D e).card ≤ (starDevice G u₀).card := hcard e he
      _ = G.degree u₀ := card_starDevice G u₀
      _ ≤ Delta := hDelta u₀
  · intro e he
    obtain ⟨φ, hDe, rfl⟩ := hwitness e he
    refine ⟨φ u₀, ?_, iso_mem_mapEdgeSet φ hu₀⟩
    rw [← translateSupport_starDevice G φ u₀]
    exact hDe

/-- **Separated cycle devices from quasi-transitivity.**  A single cycle
containing a double-ray edge yields a uniform finite cycle-length bound and a
bounded-distance separated family.  Every selected pivot lies on the cycle
support selected for it. -/
theorem exists_separated_cycle_devices (G : SimpleGraph V) (hconn : G.Connected)
    (hqt : IsQuasiTransitive G) {u₀ : V} (c₀ : G.Walk u₀ u₀)
    (hc₀ : c₀.IsCycle) {e₀ : G.edgeSet} (he₀ : (e₀ : Sym2 V) ∈ c₀.edges)
    (hr₀ : OnDoubleRay e₀) :
    ∃ (L : ℕ) (S : Set G.edgeSet) (D : G.edgeSet → Finset G.edgeSet),
      L = c₀.length ∧
      FKLimit.IsSeparatedDeviceFamily S D ∧
      FK.Theorem14.BoundedDistance G.lineGraph.dist S ∧
      (∀ e ∈ S, OnDoubleRay e) ∧
      (∀ e ∈ S, (D e).card ≤ L) ∧
      (∀ e ∈ S, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L ∧
        D e = walkDevice c ∧ (e : Sym2 V) ∈ c.edges) := by
  obtain ⟨S, D, hsep, hbounded, hray, hcard, hwitness⟩ :=
    exists_separated_template_devices G hconn hqt (walkDevice c₀)
      (mem_walkDevice.mpr he₀) hr₀
  refine ⟨c₀.length, S, D, rfl, hsep, hbounded, hray, ?_, ?_⟩
  · intro e he
    exact (hcard e he).trans (card_walkDevice_le_length c₀)
  · intro e he
    obtain ⟨φ, hDe, rfl⟩ := hwitness e he
    refine ⟨φ u₀, c₀.map φ.toHom, hc₀.map φ.injective, ?_, ?_, ?_⟩
    · exact SimpleGraph.Walk.length_map φ.toHom c₀
    · rw [← translateSupport_walkDevice c₀ φ]
      exact hDe
    · rw [iso_coe_mapEdgeSet, SimpleGraph.Walk.edges_map]
      exact List.mem_map.mpr ⟨(e₀ : Sym2 V), he₀, rfl⟩

/-- Removing the pivot from a bounded device leaves at most `L - 1`
auxiliary edges, matching both exponents in Proposition 4.2. -/
lemma card_auxiliary_le_pred {E : Type*} [DecidableEq E] {D : Finset E} {e : E} {L : ℕ}
    (he : e ∈ D) (hcard : D.card ≤ L) : (D.erase e).card ≤ L - 1 := by
  classical
  rw [Finset.card_erase_of_mem he]
  exact Nat.sub_le_sub_right hcard 1

end FK.QuasiTransitive

#print axioms FK.QuasiTransitive.exists_degree_bound
#print axioms FK.QuasiTransitive.iso_edist_eq
#print axioms FK.QuasiTransitive.iso_dist_eq
#print axioms FK.QuasiTransitive.SimpleGraph.exists_lineGraph_walk_of_walk
#print axioms FK.QuasiTransitive.lineGraph_connected
#print axioms FK.QuasiTransitive.onDoubleRay_mapEdgeSet
#print axioms FK.QuasiTransitive.exists_orbitEdge_close
#print axioms FK.QuasiTransitive.exists_separated_template_devices
#print axioms FK.QuasiTransitive.isSeparatedDeviceFamily_selectedSupport
#print axioms FK.QuasiTransitive.translateSupport_starDevice
#print axioms FK.QuasiTransitive.translateSupport_walkDevice
#print axioms FK.QuasiTransitive.exists_separated_star_devices
#print axioms FK.QuasiTransitive.exists_separated_cycle_devices
#print axioms FK.QuasiTransitive.card_auxiliary_le_pred
