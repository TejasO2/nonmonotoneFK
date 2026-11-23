import FK.PlanarMatroid

/-!
# Exact graphic matroid duality for connected unicyclic multigraphs

A graph-theoretic unique-cycle certificate is used, not matroid duality. The
plane dual has two face vertices. Cycle labels join them and a bridge label
is a loop at its prescribed incident face. The proof characterizes the primal
bases and the independent sets of the face-dual separately.
-/

namespace FK.Finite.PlaneMatroid

open scoped Classical
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.FinitePlane
open FK.FiniteFiber
open FK.Finite.Conditional

/-- Graph-theoretic data for a connected unicyclic labelled multigraph.
`cycleEdges` is dependent, and deleting any one of its labels leaves a forest.
No statement about a dual graph or a dual matroid occurs in this structure. -/
structure UniqueCycleCertificate (G : LabelledMultigraph) where
  cycleEdges : Set G.Edge
  nonempty_cycleEdges : cycleEdges.Nonempty
  preconnected : (G.connectionGraph G.freeBoundary G.allOpen).Preconnected
  forest_delete_cycleEdge (e : G.Edge) (he : e ∈ cycleEdges) :
    G.IsOpenForest G.freeBoundary (G.setConfig (Set.univ \ {e}))
  cycle_not_forest :
    ¬ G.IsOpenForest G.freeBoundary (G.setConfig cycleEdges)

namespace UniqueCycleCertificate

variable {G : LabelledMultigraph} (hG : UniqueCycleCertificate G)

/-- Independence in a unicyclic graph is precisely avoidance of its unique
cycle. -/
lemma indep_iff (A : Set G.Edge) :
    G.cycleMatroid.Indep A ↔ ¬ hG.cycleEdges ⊆ A := by
  rw [G.cycleMatroid_indep]
  constructor
  · intro hA hCA
    exact hG.cycle_not_forest
      (IsOpenForest.mono (G := G) (G.setConfig_mono hCA) hA)
  · intro hCA
    obtain ⟨e, heC, heA⟩ := Set.not_subset.mp hCA
    have hsub : A ⊆ Set.univ \ {e} := by
      intro a haA
      refine ⟨Set.mem_univ a, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hae
      exact heA (hae ▸ haA)
    exact IsOpenForest.mono (G := G) (G.setConfig_mono hsub)
      (hG.forest_delete_cycleEdge e heC)

lemma not_indep_univ (h : UniqueCycleCertificate G) :
    ¬ G.cycleMatroid.Indep Set.univ := by
  rw [h.indep_iff]
  simp

/-- Every primal basis deletes exactly one cycle label, and every such set is
a basis. -/
lemma isBase_iff (B : Set G.Edge) :
    G.cycleMatroid.IsBase B ↔ ∃ e ∈ hG.cycleEdges, B = Set.univ \ {e} := by
  constructor
  · intro hB
    have hnot : ¬ hG.cycleEdges ⊆ B := (hG.indep_iff B).mp hB.indep
    obtain ⟨e, heC, heB⟩ := Set.not_subset.mp hnot
    have hJ : G.cycleMatroid.Indep (Set.univ \ {e}) := by
      rw [hG.indep_iff]
      intro hsub
      have he := hsub heC
      simp at he
    refine ⟨e, heC, hB.eq_of_subset_indep hJ ?_⟩
    intro a haB
    refine ⟨Set.mem_univ a, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hae
    exact heB (hae ▸ haB)
  · rintro ⟨e, heC, rfl⟩
    have hI : G.cycleMatroid.Indep (Set.univ \ {e}) := by
      rw [hG.indep_iff]
      intro hsub
      have := hsub heC
      simp at this
    apply hI.isBase_of_forall_insert
    intro f hf
    simp only [G.cycleMatroid_ground, Set.mem_diff, Set.mem_univ, true_and,
      Set.mem_singleton_iff] at hf
    have hfe : f = e := by
      by_contra hfe
      exact hf hfe
    subst f
    simpa using not_indep_univ hG

/-- A two-face graph on the same labels. A cycle label joins the two faces;
a non-cycle label is a loop at the supplied incident face. -/
noncomputable abbrev dualGraph (bridgeFace : G.Edge → Bool) : LabelledMultigraph where
  Vertex := Bool
  Edge := G.Edge
  source e := if e ∈ hG.cycleEdges then false else bridgeFace e
  target e := if e ∈ hG.cycleEdges then true else bridgeFace e

/-- The face-dual forests are exactly the sets contained in a single cycle
label. In particular, every non-cycle label is a dual loop and two distinct
cycle labels form a dual cycle. -/
lemma dualGraph_forest_iff (bridgeFace : G.Edge → Bool) (A : Set G.Edge) :
    (hG.dualGraph bridgeFace).IsOpenForest (hG.dualGraph bridgeFace).freeBoundary
        ((hG.dualGraph bridgeFace).setConfig A) ↔
      ∃ e ∈ hG.cycleEdges, A ⊆ {e} := by
  constructor
  · intro hforest
    have hAC : A ⊆ hG.cycleEdges := by
      intro a haA
      by_contra haC
      have haopen : (hG.dualGraph bridgeFace).setConfig A a = true := by
        simp [LabelledMultigraph.setConfig, haA]
      apply hforest a haopen
      have hst : (hG.dualGraph bridgeFace).source a =
          (hG.dualGraph bridgeFace).target a := by
        simp [dualGraph, haC]
      unfold endpointsConnectedWithout
      rw [hst]
    have hAsub : A.Subsingleton := by
      intro a haA b hbA
      have haC := hAC haA
      by_contra hab
      have haopen : (hG.dualGraph bridgeFace).setConfig A a = true := by
        simp [LabelledMultigraph.setConfig, haA]
      apply hforest a haopen
      have hbne : b ≠ a := Ne.symm hab
      have hbopen : withEdge a false
          ((hG.dualGraph bridgeFace).setConfig A) b = true := by
        rw [withEdge_off hbne]
        simp [LabelledMultigraph.setConfig, hbA]
      have hadj : ((hG.dualGraph bridgeFace).connectionGraph
          (hG.dualGraph bridgeFace).freeBoundary
          (withEdge a false
            ((hG.dualGraph bridgeFace).setConfig A))).Adj false true := by
        refine ⟨Bool.false_ne_true, Or.inr ⟨b, hbopen, ?_⟩⟩
        simp [dualGraph, hAC hbA, LabelledMultigraph.Joins]
      unfold endpointsConnectedWithout
      simpa [dualGraph, haC] using hadj.reachable
    by_cases hne : A.Nonempty
    · obtain ⟨e, heA⟩ := hne
      refine ⟨e, hAC heA, ?_⟩
      intro a haA
      have hae : a = e := hAsub haA heA
      simpa [hae]
    · obtain ⟨e, heC⟩ := hG.nonempty_cycleEdges
      refine ⟨e, heC, ?_⟩
      intro a haA
      exact (hne ⟨a, haA⟩).elim
  · rintro ⟨e, heC, hAe⟩
    intro a haopen
    have haA : a ∈ A := by
      simpa [LabelledMultigraph.setConfig] using haopen
    have hae : a = e := by
      simpa only [Set.mem_singleton_iff] using hAe haA
    subst a
    have hoff : withEdge e false
        ((hG.dualGraph bridgeFace).setConfig A) =
        (hG.dualGraph bridgeFace).allClosed := by
      funext b
      by_cases hbe : b = e
      · subst b
        simp [LabelledMultigraph.allClosed]
      · rw [withEdge_off hbe]
        have hbA : b ∉ A := by
          intro hb
          have := hAe hb
          simp only [Set.mem_singleton_iff] at this
          exact hbe this
        simp [LabelledMultigraph.setConfig, hbA, LabelledMultigraph.allClosed]
    unfold endpointsConnectedWithout
    rw [hoff, LabelledMultigraph.connectionGraph_free_allClosed]
    intro hconn
    have heq := SimpleGraph.reachable_bot.mp hconn
    simp [dualGraph, heC] at heq

lemma dualGraph_indep_iff (bridgeFace : G.Edge → Bool) (A : Set G.Edge) :
    (hG.dualGraph bridgeFace).cycleMatroid.Indep A ↔
      ∃ e ∈ hG.cycleEdges, A ⊆ {e} :=
  ((hG.dualGraph bridgeFace).cycleMatroid_indep A).trans
    (hG.dualGraph_forest_iff bridgeFace A)

/-- The actual cycle-matroid dual equality for every connected unicyclic
labelled multigraph and every choice of incident faces for its bridges. -/
theorem dual_cycleMatroid (bridgeFace : G.Edge → Bool) :
    (G.cycleMatroid)✶ = (hG.dualGraph bridgeFace).cycleMatroid := by
  apply Matroid.ext_indep (by rfl)
  intro A hA
  rw [hG.dualGraph_indep_iff]
  rw [Matroid.dual_indep_iff_exists (by simp)]
  constructor
  · rintro ⟨B, hB, hdisj⟩
    obtain ⟨e, heC, rfl⟩ := (hG.isBase_iff B).mp hB
    refine ⟨e, heC, ?_⟩
    intro a haA
    simp only [Set.mem_singleton_iff]
    by_contra hae
    have haB : a ∈ Set.univ \ {e} := by
      exact ⟨Set.mem_univ a, by simpa [Set.mem_singleton_iff] using hae⟩
    exact Set.disjoint_left.mp hdisj haA haB
  · rintro ⟨e, heC, hAe⟩
    refine ⟨Set.univ \ {e}, (hG.isBase_iff _).mpr ⟨e, heC, rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    intro a haA haB
    have hae : a = e := by
      simpa only [Set.mem_singleton_iff] using hAe haA
    subst a
    simp at haB

end UniqueCycleCertificate

/-- The labelled primal/face-dual pair determined by a unique-cycle graph and
an assignment of every bridge to its incident face. -/
noncomputable abbrev unicyclicDualPair (G : LabelledMultigraph) (hG : UniqueCycleCertificate G)
    (bridgeFace : G.Edge → Bool) : LabelledDualPair where
  Vertex := G.Vertex
  Face := Bool
  Edge := G.Edge
  source := G.source
  target := G.target
  dualSource e := if e ∈ hG.cycleEdges then false else bridgeFace e
  dualTarget e := if e ∈ hG.cycleEdges then true else bridgeFace e

/-- The complete graphic-dual certificate is proved from the graph-theoretic
unique-cycle data. -/
theorem unicyclicDualPair_graphicDualCertificate (G : LabelledMultigraph)
    (hG : UniqueCycleCertificate G) (bridgeFace : G.Edge → Bool) :
    (unicyclicDualPair G hG bridgeFace).GraphicDualCertificate := by
  refine ⟨?_, ⟨false⟩, ?_⟩
  · change (G.cycleMatroid)✶ = (hG.dualGraph bridgeFace).cycleMatroid
    exact hG.dual_cycleMatroid bridgeFace
  · obtain ⟨e, heC⟩ := hG.nonempty_cycleEdges
    have hadj : ((unicyclicDualPair G hG bridgeFace).faceDual.connectionGraph
        (unicyclicDualPair G hG bridgeFace).faceDual.freeBoundary
        (unicyclicDualPair G hG bridgeFace).faceDual.allOpen).Adj false true := by
      refine ⟨Bool.false_ne_true, Or.inr ⟨e, ?_, ?_⟩⟩
      · simp [LabelledMultigraph.allOpen]
      · change ((if e ∈ hG.cycleEdges then false else bridgeFace e) = false ∧
            (if e ∈ hG.cycleEdges then true else bridgeFace e) = true) ∨
          ((if e ∈ hG.cycleEdges then false else bridgeFace e) = true ∧
            (if e ∈ hG.cycleEdges then true else bridgeFace e) = false)
        simp [heC]
    intro u v
    change Bool at u v
    cases u <;> cases v
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _

/-- Every previously defined connected labelled cycle gives the new
unique-cycle certificate. -/
def ofIsLabelledCycle (G : LabelledMultigraph) (hG : G.IsLabelledCycle) :
    UniqueCycleCertificate G where
  cycleEdges := Set.univ
  nonempty_cycleEdges := by
    haveI : Nonempty G.Edge := Fintype.card_pos_iff.mp (by
      rw [hG.card_edges]
      exact Fintype.card_pos_iff.mpr hG.nonemptyVertex)
    exact Set.univ_nonempty
  preconnected := hG.preconnected
  forest_delete_cycleEdge e he := by
    apply hG.isOpenForest_of_ne_allOpen
    intro hEq
    have hval := congrFun hEq e
    simp [LabelledMultigraph.setConfig, LabelledMultigraph.allOpen] at hval
  cycle_not_forest := by
    intro hforest
    have hconfig : G.setConfig (Set.univ : Set G.Edge) = G.allOpen := by
      funext e
      simp [LabelledMultigraph.setConfig, LabelledMultigraph.allOpen]
    rw [hconfig] at hforest
    have hcomp : G.componentCount G.freeBoundary G.allOpen = 1 :=
      componentCount_eq_one_of_preconnected G G.freeBoundary G.allOpen
        hG.nonemptyVertex.some hG.preconnected
    have hcard := (G.isOpenForest_iff_componentCount_add_openCard
      G.allOpen).mp hforest
    rw [hcomp, openCard_allOpen, hG.card_edges] at hcard
    omega

end FK.Finite.PlaneMatroid


/-!
## Simultaneous attachment of a finite star forest

The next construction attaches an arbitrary finite family of pendant edges to
prescribed vertices of a connected unicyclic graph.  The singleton family is
the ordinary leaf operation.  Since the output again has a unique-cycle
certificate, iterating the operation attaches any finite rooted forest to the
core.  Every new edge is a primal bridge and becomes a loop in its prescribed
face of the two-face dual.
-/

namespace FK.Finite.PlaneMatroid

open scoped Classical
open FK.Finite
open FK.Finite.LabelledMultigraph
open FK.FinitePlane
open FK.FiniteFiber
open FK.Finite.Conditional

/-- A walk can be transported along any relation on vertices which sends each
adjacency to reachability.  Unlike a graph homomorphism, this permits
collapsing an edge to two equal vertices. -/
lemma reachable_relMap {V W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (r : V → W) (hstep : ∀ {u v}, H.Adj u v → K.Reachable (r u) (r v))
    {u v : V} (h : H.Reachable u v) : K.Reachable (r u) (r v) := by
  rw [SimpleGraph.reachable_eq_reflTransGen] at h ⊢
  induction h with
  | refl => exact .refl
  | tail hxy hyz ih =>
      exact ih.trans ((SimpleGraph.reachable_iff_reflTransGen ..).mp (hstep hyz))

/-- Attach one new pendant vertex and one new labelled edge for every `i : ι`.
The new edge `Sum.inr i` joins `Sum.inr i` to `Sum.inl (attach i)`. -/
abbrev attachMany (G : LabelledMultigraph) {ι : Type*} [Fintype ι]
    (attach : ι → G.Vertex) : LabelledMultigraph where
  Vertex := G.Vertex ⊕ ι
  Edge := G.Edge ⊕ ι
  source
    | Sum.inl e => Sum.inl (G.source e)
    | Sum.inr i => Sum.inr i
  target
    | Sum.inl e => Sum.inl (G.target e)
    | Sum.inr i => Sum.inl (attach i)

namespace UniqueCycleCertificate

variable {G : LabelledMultigraph} (hG : UniqueCycleCertificate G)

/-- The embedded primal connection graph after simultaneous attachment. -/
def attachManyCoreHom {ι : Type*} [Fintype ι] (attach : ι → G.Vertex)
    (ω : G.Configuration) (η : (attachMany G attach).Configuration)
    (hη : ∀ e, η (Sum.inl e) = ω e) :
    G.connectionGraph G.freeBoundary ω →g
      (attachMany G attach).connectionGraph (attachMany G attach).freeBoundary η where
  toFun := Sum.inl
  map_rel' := by
    intro u v huv
    rcases huv.2 with hwire | ⟨e, heopen, hejoin⟩
    · change u = v at hwire
      subst v
      exact (huv.1 rfl).elim
    · refine ⟨fun heq => huv.1 (Sum.inl.inj heq), Or.inr ⟨Sum.inl e, ?_, ?_⟩⟩
      · simpa [hη] using heopen
      · simpa [attachMany, LabelledMultigraph.Joins] using hejoin

/-- Attachment preserves all-open connectivity. -/
lemma attachMany_preconnected (hG : UniqueCycleCertificate G)
    {ι : Type*} [Fintype ι] (attach : ι → G.Vertex) :
    ((attachMany G attach).connectionGraph (attachMany G attach).freeBoundary
      (attachMany G attach).allOpen).Preconnected := by
  let f := attachManyCoreHom attach G.allOpen (attachMany G attach).allOpen
    (fun _ => rfl)
  have hnew (i : ι) : ((attachMany G attach).connectionGraph
      (attachMany G attach).freeBoundary (attachMany G attach).allOpen).Adj
      (Sum.inr i) (Sum.inl (attach i)) := by
    refine ⟨by simp, Or.inr ⟨Sum.inr i, by simp [LabelledMultigraph.allOpen], ?_⟩⟩
    simp [attachMany, LabelledMultigraph.Joins]
  intro u v
  cases u with
  | inl u =>
      cases v with
      | inl v => exact (hG.preconnected u v).map f
      | inr j => exact ((hG.preconnected u (attach j)).map f).trans (hnew j).symm.reachable
  | inr i =>
      cases v with
      | inl v => exact (hnew i).reachable.trans ((hG.preconnected (attach i) v).map f)
      | inr j =>
          exact (hnew i).reachable.trans
            (((hG.preconnected (attach i) (attach j)).map f).trans (hnew j).symm.reachable)

/-- Collapse every new vertex to the old vertex at which its pendant edge is
attached. -/
def attachManyCollapse {ι : Type*} (attach : ι → G.Vertex) :
    G.Vertex ⊕ ι → G.Vertex
  | Sum.inl u => u
  | Sum.inr i => attach i

/-- After deleting a new pendant edge, its new endpoint is isolated. -/
lemma attachMany_no_adj_new {ι : Type*} [Fintype ι] (attach : ι → G.Vertex)
    (i : ι) (η : (attachMany G attach).Configuration)
    (v : (attachMany G attach).Vertex) :
    ¬ ((attachMany G attach).connectionGraph (attachMany G attach).freeBoundary
      (@withEdge _ (fun a b => Classical.propDecidable (a = b)) (Sum.inr i) false η)).Adj
      (Sum.inr i) v := by
  intro hadj
  rcases hadj.2 with hwire | ⟨e, heopen, hejoin⟩
  · change (Sum.inr i : G.Vertex ⊕ ι) = v at hwire
    subst v
    exact hadj.1 rfl
  · cases e with
    | inl e =>
        rcases hejoin with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [attachMany] at h₁ h₂
    | inr j =>
        rcases hejoin with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · have hji : j = i := Sum.inr.inj h₁
          subst j
          simp [withEdge] at heopen
        · simp [attachMany] at h₂

/-- Every simultaneously attached pendant edge is a bridge in every
configuration. -/
lemma attachMany_pendant_bridge {ι : Type*} [Fintype ι] (attach : ι → G.Vertex)
    (i : ι) (η : (attachMany G attach).Configuration) :
    ¬ endpointsConnectedWithout (attachMany G attach) (attachMany G attach).freeBoundary
      (Sum.inr i) η := by
  intro hconn
  unfold endpointsConnectedWithout at hconn
  apply hconn.elim
  intro p
  cases p with
  | cons hadj p => exact attachMany_no_adj_new attach i η _ hadj

/-- Collapsing the star forest sends every attached-graph adjacency to a
reachable relation in the old graph. -/
lemma attachMany_collapse_step {ι : Type*} [Fintype ι] (attach : ι → G.Vertex)
    (ω : G.Configuration) (η : (attachMany G attach).Configuration)
    (hη : ∀ e, η (Sum.inl e) = ω e) {u v : (attachMany G attach).Vertex}
    (hadj : ((attachMany G attach).connectionGraph
      (attachMany G attach).freeBoundary η).Adj u v) :
    (G.connectionGraph G.freeBoundary ω).Reachable
      (attachManyCollapse attach u) (attachManyCollapse attach v) := by
  rcases hadj.2 with hwire | ⟨e, heopen, hejoin⟩
  · change u = v at hwire
    subst v
    exact SimpleGraph.Reachable.refl _
  · cases e with
    | inr i =>
        rcases hejoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          exact SimpleGraph.Reachable.refl _
    | inl e =>
        have heopen' : ω e = true := by rw [← hη]; exact heopen
        rcases hejoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · apply SimpleGraph.Adj.reachable
          exact ⟨fun heq => hadj.1 (congrArg Sum.inl heq),
            Or.inr ⟨e, heopen', Or.inl ⟨rfl, rfl⟩⟩⟩
        · apply SimpleGraph.Adj.reachable
          exact ⟨fun heq => hadj.1 (congrArg Sum.inl heq),
            Or.inr ⟨e, heopen', Or.inr ⟨rfl, rfl⟩⟩⟩

@[simp] lemma attachMany_setConfig_image_inl {ι : Type*} [Fintype ι]
    (attach : ι → G.Vertex) (C : Set G.Edge) (e : G.Edge) :
    (attachMany G attach).setConfig (Sum.inl '' C) (Sum.inl e) = G.setConfig C e := by
  simp [LabelledMultigraph.setConfig]

@[simp] lemma attachMany_setConfig_delete_inl {ι : Type*} [Fintype ι]
    (attach : ι → G.Vertex) (e a : G.Edge) :
    (attachMany G attach).setConfig (Set.univ \ {Sum.inl e}) (Sum.inl a) =
      G.setConfig (Set.univ \ {e}) a := by
  simp [LabelledMultigraph.setConfig]

@[simp] lemma attachMany_withEdge_inl_classical {ι : Type*} [Fintype ι]
    (attach : ι → G.Vertex) (η : (attachMany G attach).Configuration)
    (a e : G.Edge) (b : Bool) :
    @withEdge (G.Edge ⊕ ι) (fun _ _ => Classical.propDecidable _)
      (Sum.inl a) b η (Sum.inl e) =
    @withEdge G.Edge (fun _ _ => Classical.propDecidable _)
      a b (fun x => η (Sum.inl x)) e := by
  by_cases h : e = a
  · subst e
    simp [withEdge]
  · have h' : (Sum.inl e : G.Edge ⊕ ι) ≠ Sum.inl a := by simpa [h]
    simp [withEdge, Function.update, h, h']


/-- Simultaneous pendant attachment preserves the unique-cycle graph
certificate.  The distinguished cycle contains exactly the old cycle labels. -/
def attachMany_certificate (hG : UniqueCycleCertificate G)
    {ι : Type*} [Fintype ι] (attach : ι → G.Vertex) :
    UniqueCycleCertificate (attachMany G attach) where
  cycleEdges := Sum.inl '' hG.cycleEdges
  nonempty_cycleEdges := hG.nonempty_cycleEdges.image Sum.inl
  preconnected := attachMany_preconnected hG attach
  forest_delete_cycleEdge q hq := by
    obtain ⟨e, heC, rfl⟩ := hq
    intro q hqopen
    cases q with
    | inr i => exact attachMany_pendant_bridge attach i _
    | inl a =>
        have haopen : G.setConfig (Set.univ \ {e}) a = true := by
          rw [← attachMany_setConfig_delete_inl attach e a]
          exact hqopen
        intro hconn
        apply hG.forest_delete_cycleEdge e heC a haopen
        unfold endpointsConnectedWithout at hconn ⊢
        have hstep : ∀ {u v : G.Vertex ⊕ ι},
            ((attachMany G attach).connectionGraph (attachMany G attach).freeBoundary
              (@withEdge (G.Edge ⊕ ι) (fun _ _ => Classical.propDecidable _)
                (Sum.inl a) false ((attachMany G attach).setConfig
                  (Set.univ \ {Sum.inl e})))).Adj u v →
            (G.connectionGraph G.freeBoundary
              (@withEdge G.Edge (fun _ _ => Classical.propDecidable _)
                a false (G.setConfig (Set.univ \ {e})))).Reachable
              (attachManyCollapse attach u) (attachManyCollapse attach v) := by
          intro u v hadj
          have hcfg : (fun x => (attachMany G attach).setConfig
              (Set.univ \ {Sum.inl e}) (Sum.inl x)) = G.setConfig (Set.univ \ {e}) := by
            funext x
            exact attachMany_setConfig_delete_inl attach e x
          exact attachMany_collapse_step attach _ _ (fun b => by
            rw [attachMany_withEdge_inl_classical]
            rw [hcfg]) hadj
        have hmap := reachable_relMap (attachManyCollapse attach) hstep hconn
        simpa [attachManyCollapse] using hmap
  cycle_not_forest := by
    intro hforest
    apply hG.cycle_not_forest
    intro a haopen hconn
    apply hforest (Sum.inl a) (by rw [attachMany_setConfig_image_inl]; exact haopen)
    unfold endpointsConnectedWithout at hconn ⊢
    let f := attachManyCoreHom attach
      (@withEdge G.Edge (fun _ _ => Classical.propDecidable _)
        a false (G.setConfig hG.cycleEdges))
      (@withEdge (G.Edge ⊕ ι) (fun _ _ => Classical.propDecidable _)
        (Sum.inl a) false ((attachMany G attach).setConfig (Sum.inl '' hG.cycleEdges)))
      (fun b => by
        rw [attachMany_withEdge_inl_classical]
        have hcfg : (fun x => (attachMany G attach).setConfig
            (Sum.inl '' hG.cycleEdges) (Sum.inl x)) = G.setConfig hG.cycleEdges := by
          funext x
          exact attachMany_setConfig_image_inl attach hG.cycleEdges x
        rw [hcfg])
    have hmap := hconn.map f
    simpa [f, attachManyCoreHom, attachMany] using hmap

end UniqueCycleCertificate

/-- Face assignment after simultaneous pendant attachment: old bridges retain
their face and each new bridge independently selects its incident face. -/
def attachManyBridgeFace {E ι : Type*} (bridgeFace : E → Bool) (newFace : ι → Bool) :
    E ⊕ ι → Bool
  | Sum.inl e => bridgeFace e
  | Sum.inr i => newFace i

/-- The exact graphic-dual certificate after an arbitrary finite star-forest
attachment.  No planar-duality premise occurs in the statement or proof. -/
theorem attachMany_graphicDualCertificate (G : LabelledMultigraph)
    (hG : UniqueCycleCertificate G) {ι : Type*} [Fintype ι]
    (attach : ι → G.Vertex) (bridgeFace : G.Edge → Bool) (newFace : ι → Bool) :
    (unicyclicDualPair (attachMany G attach) (hG.attachMany_certificate attach)
      (attachManyBridgeFace bridgeFace newFace)).GraphicDualCertificate :=
  unicyclicDualPair_graphicDualCertificate _ _ _

/-- An explicit unicyclic multigraph with three simultaneous pendant edges. -/
abbrev threeLeafDigon : FK.Finite.LabelledMultigraph := by
  exact attachMany FK.Finite.LabelledMultigraph.twoEdgeCycle (fun _ : Fin 3 => false)

/-- The graph-theoretic certificate for the three-leaf digon. -/
def threeLeafDigon_uniqueCycle : UniqueCycleCertificate threeLeafDigon :=
  (ofIsLabelledCycle _ FK.Finite.LabelledMultigraph.isLabelledCycle_twoEdgeCycle).attachMany_certificate
    (fun _ : Fin 3 => false)

/-- A completely explicit certificate whose primal has five labelled edges and
whose dual has two parallel edges and three loops. -/
theorem threeLeafDigon_graphicDualCertificate :
    (unicyclicDualPair threeLeafDigon threeLeafDigon_uniqueCycle
      (attachManyBridgeFace (fun _ => false) (fun _ : Fin 3 => false))).GraphicDualCertificate :=
  unicyclicDualPair_graphicDualCertificate _ _ _

end FK.Finite.PlaneMatroid
