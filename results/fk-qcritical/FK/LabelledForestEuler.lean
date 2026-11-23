import FK.FiniteComponentCounts

/-!
# Forest component counts on finite labelled multigraphs

An open labelled forest is defined by the bridge condition: after deleting any
open labelled edge, its endpoints are disconnected in the remaining open/wired
graph. This treats loops, pairs of parallel edges, and cycles through boundary
wiring uniformly. The component-count identity is proved directly from the
one-edge update, without collapsing labelled edges to a simple graph.
-/

namespace FK.Finite.LabelledMultigraph

open scoped BigOperators Classical
open FK.Finite.Conditional
open FK.FiniteFiber

variable (G : LabelledMultigraph)

/-- Every open labelled edge is a bridge in the open/wired configuration. -/
def IsOpenForest (ξ : G.BoundaryPartition) (ω : G.Configuration) : Prop :=
  ∀ e, ω e = true → ¬ endpointsConnectedWithout G ξ e ω

lemma isOpenForest_allClosed (ξ : G.BoundaryPartition) :
    G.IsOpenForest ξ G.allClosed := by
  intro e he
  simp [allClosed] at he

lemma isOpenForest_withEdge_false {ξ : G.BoundaryPartition} {ω : G.Configuration}
    (hω : G.IsOpenForest ξ ω) (e : G.Edge) (he : ω e = true) :
    G.IsOpenForest ξ (withEdge e false ω) := by
  intro f hf hconn
  have hfe : f ≠ e := by
    intro hfe
    subst f
    simp at hf
  have hfω : ω f = true := by
    rw [← withEdge_off hfe false ω]
    exact hf
  apply hω f hfω
  apply hconn.mono
  apply G.connectionGraph_mono
  intro a
  by_cases haf : a = f
  · subst a
    simp
  · rw [withEdge_off haf, withEdge_off haf]
    by_cases hae : a = e
    · subst a
      simp [he]
    · simp [withEdge, Function.update_of_ne hae]

lemma openCard_withEdge_false_add_one {ω : G.Configuration} {e : G.Edge}
    (he : ω e = true) :
    FK.FinitePlane.openCard (withEdge e false ω) + 1 = FK.FinitePlane.openCard ω := by
  classical
  let s := Finset.univ.filter fun a => ω a
  have hes : e ∈ s := by simp [s, he]
  have hset : Finset.univ.filter (fun a => withEdge e false ω a) = s.erase e := by
    ext a
    by_cases hae : a = e
    · subst a
      simp [s, he]
    · simp [s, hae]
  unfold FK.FinitePlane.openCard
  rw [hset, Finset.card_erase_of_mem hes]
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨e, hes⟩
  change s.card - 1 + 1 = s.card
  omega

lemma openCard_eq_zero_iff (ω : G.Configuration) :
    FK.FinitePlane.openCard ω = 0 ↔ ω = G.allClosed := by
  classical
  constructor
  · intro hω
    funext e
    cases he : ω e with
    | false => rfl
    | true =>
      have he' : e ∈ Finset.univ.filter fun a => ω a := by simp [he]
      have hpos : 0 < FK.FinitePlane.openCard ω :=
        Finset.card_pos.mpr ⟨e, he'⟩
      omega
  · intro hω
    subst ω
    simp [FK.FinitePlane.openCard, allClosed]

@[simp] lemma withEdge_true_eq_self [DecidableEq G.Edge]
    {ω : G.Configuration} {e : G.Edge} (he : ω e = true) :
    withEdge e true ω = ω := by
  funext a
  by_cases hae : a = e
  · subst a
    simp [he]
  · exact withEdge_off hae true ω

/-- **Labelled forest Euler identity with arbitrary wiring.** Every open edge
in an open forest is a bridge, so deleting all open edges one at a time lowers
both sides of the identity by one. -/
lemma componentCount_add_openCard_of_isOpenForest (ξ : G.BoundaryPartition)
    (ω : G.Configuration) (hω : G.IsOpenForest ξ ω) :
    G.componentCount ξ ω + FK.FinitePlane.openCard ω =
      G.componentCount ξ G.allClosed := by
  classical
  induction hcard : FK.FinitePlane.openCard ω generalizing ω with
  | zero =>
      have hclosed := (G.openCard_eq_zero_iff ω).mp hcard
      subst ω
      rfl
  | succ n ih =>
      have hnzero : FK.FinitePlane.openCard ω ≠ 0 := by omega
      have hne : ω ≠ G.allClosed := by
        intro hclosed
        exact hnzero ((G.openCard_eq_zero_iff ω).mpr hclosed)
      obtain ⟨e, he⟩ := G.exists_open_of_ne_allClosed hne
      let ω₀ := withEdge e false ω
      have hforest₀ : G.IsOpenForest ξ ω₀ :=
        G.isOpenForest_withEdge_false hω e he
      have hcard₀ : FK.FinitePlane.openCard ω₀ = n := by
        have h := G.openCard_withEdge_false_add_one he
        dsimp [ω₀]
        omega
      have hi := ih ω₀ hforest₀ hcard₀
      have hc := componentCount_open_add_one_of_not_connected G ξ e ω (hω e he)
      rw [G.withEdge_true_eq_self he] at hc
      dsimp [ω₀] at hi
      omega

/-- In the free boundary case, the labelled forest identity takes the familiar
form `components + open edges = vertices`, including isolated vertices. -/
lemma componentCount_add_openCard_of_free_isOpenForest (ω : G.Configuration)
    (hω : G.IsOpenForest G.freeBoundary ω) :
    G.componentCount G.freeBoundary ω + FK.FinitePlane.openCard ω =
      Fintype.card G.Vertex := by
  rw [G.componentCount_add_openCard_of_isOpenForest G.freeBoundary ω hω,
    G.componentCount_free_allClosed, Nat.card_eq_fintype_card]

end FK.Finite.LabelledMultigraph
