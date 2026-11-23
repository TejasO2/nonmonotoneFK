import FK.OpenPathEnhancement

/-!
# Cycle certificates for open-path enhancement

For a finite simple graph, a cycle supplies exactly the nonempty enhanced set
needed in the deduction of Theorem 1.2 from Proposition 3.2. This file does not
claim to encode loops, parallel edges, or the quotient graph `G ∪ α` used for a
wired boundary condition.
-/

open scoped BigOperators
open Set

namespace OpenPath

/-- The graph edges occurring in a walk, as a finset of the graph's edge type. -/
noncomputable def walkEdgeFinset {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {u v : V} (p : G.Walk u v) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => (e : Sym2 V) ∈ p.edges

/-- The first edge of a nonempty cycle, regarded as a graph edge. -/
def cycleHeadEdge {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) : G.edgeSet := ⟨s(u, v), h⟩

/-- The certificate collection assigning the remainder of the cycle to its
head edge and no certificates to every other edge. -/
def cyclePathCollection {V : Type*} {G : SimpleGraph V} [Fintype G.edgeSet]
    [DecidableEq V] {u v : V} (h : G.Adj u v) (p : G.Walk v u) : G.edgeSet → Set (Finset G.edgeSet) :=
  fun e => if e = cycleHeadEdge h then {walkEdgeFinset p} else ∅

lemma cycleHeadEdge_notMem_walkEdgeFinset {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {u v : V} (h : G.Adj u v) (p : G.Walk v u)
    (hc : (SimpleGraph.Walk.cons h p).IsCycle) :
    cycleHeadEdge h ∉ walkEdgeFinset p := by
  have hnot := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc |>.2
  intro hm
  have hm' : (cycleHeadEdge h : Sym2 V) ∈ p.edges := by
    have := (Finset.mem_filter.mp hm).2
    exact this
  exact hnot hm'

/-- A nonempty cycle gives a singleton enhanced set and an explicit auxiliary
alternate path. -/
theorem hasEnhancingPaths_cons_isCycle {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {u v : V} (h : G.Adj u v) (p : G.Walk v u)
    (hc : (SimpleGraph.Walk.cons h p).IsCycle) :
    HasEnhancingPaths {cycleHeadEdge h} (cyclePathCollection h p) := by
  refine { auxiliary := ?_, nonempty := ?_ }
  · intro e he
    have heq : e = cycleHeadEdge h := by simpa using he
    subst e
    intro γ hγ
    have hγeq : γ = walkEdgeFinset p := by
      simpa [cyclePathCollection] using hγ
    subst γ
    constructor
    · exact cycleHeadEdge_notMem_walkEdgeFinset h p hc
    · intro f hf
      simp only [Finset.mem_singleton]
      intro hfe
      subst f
      exact cycleHeadEdge_notMem_walkEdgeFinset h p hc hf
  · intro e he
    have heq : e = cycleHeadEdge h := by simpa using he
    subst e
    simp [cyclePathCollection]

/-- Every non-acyclic finite simple graph admits a nonempty enhanced set with
auxiliary path certificates. -/
theorem exists_hasEnhancingPaths_of_not_isAcyclic {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (hG : ¬ G.IsAcyclic) :
    ∃ enhanced : Finset G.edgeSet, enhanced.Nonempty ∧
      ∃ Γ : G.edgeSet → Set (Finset G.edgeSet), HasEnhancingPaths enhanced Γ := by
  rw [SimpleGraph.IsAcyclic] at hG
  push Not at hG
  obtain ⟨v, c, hc⟩ := hG
  cases c with
  | nil => exact (SimpleGraph.Walk.not_isCycle_nil hc).elim
  | cons h p =>
      exact ⟨{cycleHeadEdge h}, Finset.singleton_nonempty _,
        cyclePathCollection h p, hasEnhancingPaths_cons_isCycle h p hc⟩

end OpenPath

namespace OpenPath

/-- Every edge of a walk is open and differs from a distinguished edge `e`. -/
def OpenAvoiding {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    (e : G.edgeSet) (ω : Config G.edgeSet) {u v : V} (p : G.Walk u v) : Prop :=
  ∀ f : G.edgeSet, (f : Sym2 V) ∈ p.edges → f ≠ e ∧ ω f = 1

/-- The graph connection event `K_e` for a simple graph without wired boundary. -/
def OpenConnectedWithout {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    (e : G.edgeSet) (ω : Config G.edgeSet) (u v : V) : Prop :=
  ∃ p : G.Walk u v, OpenAvoiding e ω p

lemma OpenConnectedWithout.monotone {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {e : G.edgeSet} {ω ξ : Config G.edgeSet} (h : ω ≤ ξ) {u v : V}
    (hc : OpenConnectedWithout e ω u v) : OpenConnectedWithout e ξ u v := by
  obtain ⟨p, hp⟩ := hc
  refine ⟨p, ?_⟩
  intro f hf
  obtain ⟨hne, hopen⟩ := hp f hf
  refine ⟨hne, ?_⟩
  have hle := h f
  rw [hopen] at hle
  apply Fin.ext
  simp only [Fin.le_iff_val_le_val, Fin.val_one] at hle ⊢
  omega

/-- An open remainder of a cycle connects the endpoints of the enhanced head
edge without using that edge. -/
theorem openConnectedWithout_of_cyclePathOpen {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {u v : V} (h : G.Adj u v)
    (p : G.Walk v u) (hc : (SimpleGraph.Walk.cons h p).IsCycle)
    {ω : Config G.edgeSet}
    (hopen : SomePathOpen (cyclePathCollection h p (cycleHeadEdge h)) ω) :
    OpenConnectedWithout (cycleHeadEdge h) ω u v := by
  obtain ⟨γ, hγ, hγopen⟩ := hopen
  have hγeq : γ = walkEdgeFinset p := by
    simpa [cyclePathCollection] using hγ
  subst γ
  refine ⟨p.reverse, ?_⟩
  intro f hf
  have hf' : (f : Sym2 V) ∈ p.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using hf
  have hfγ : f ∈ walkEdgeFinset p := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf'⟩
  have hne : f ≠ cycleHeadEdge h := by
    intro hfe
    subst f
    exact cycleHeadEdge_notMem_walkEdgeFinset h p hc hfγ
  exact ⟨hne, hγopen f hfγ⟩

end OpenPath

namespace OpenPath

/-- Pathwise coupled update on an actual simple-graph cycle, with no wired
boundary. This is a concrete instance of Proposition 3.2's order-preservation
step, not the full stationary-law theorem. -/
theorem pathEnhancedUpdate_ordered_cycle {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] [DecidableEq V] {u v : V} (h : G.Adj u v)
    (p : G.Walk v u) (hc : (SimpleGraph.Walk.cons h p).IsCycle)
    {p' lo hi : ℝ} {pr : ℝ}
    (hlo : lo ≤ pr) (hlo' : lo ≤ p') (hhi : pr ≤ hi) (hhi' : p' ≤ hi)
    {y x z : Config G.edgeSet} (hyx : y ≤ x) (hxz : x ≤ z) (t : ℝ) :
    let c := pathEnhancedUpdate (cycleHeadEdge h) pr p' lo hi
      (fun ω => OpenConnectedWithout (cycleHeadEdge h) ω u v)
      (cyclePathCollection h p (cycleHeadEdge h)) y x z t
    c.1 ≤ c.2.1 ∧ c.2.1 ≤ c.2.2 := by
  apply pathEnhancedUpdate_ordered hlo hlo' hhi hhi'
  · intro ω ξ hωξ
    exact OpenConnectedWithout.monotone hωξ
  · intro ω hopen
    exact openConnectedWithout_of_cyclePathOpen h p hc hopen
  · exact hyx
  · exact hxz

end OpenPath
