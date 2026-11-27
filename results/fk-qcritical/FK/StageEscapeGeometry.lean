import FK.NestedStageConnection

/-! Correct non-reflexive wiring support and elementary path/configuration lemmas. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ClusterEscape

universe u v

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- Open paths are paths in every graph with additional boundary wiring. -/
theorem reachable_wiredGraph_of_openConnected {γ : Setoid V} {ω : G.edgeSet → Bool}
    {A : Set (Sym2 V)} {x y : V} (h : OpenConnected G ω A x y) :
    (wiredGraph G γ ω).Reachable x y := by
  rcases h with ⟨p, hp⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj p ih =>
      rw [isOpenIn_cons] at hp
      have hstep : (wiredGraph G γ ω).Adj u v := by
        refine ⟨hadj.ne, Or.inr
          ⟨(⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet), hp.1.2, rfl⟩⟩
      exact hstep.reachable.trans (ih hp.2)

/-- A wired walk staying in `K` is an open walk when every nonreflexive wiring
step is supported outside `K`. -/
theorem openConnected_of_walk_support_subset_ne {γ : Setoid V} {ω : G.edgeSet → Bool}
    {K : Finset V} (hγ : ∀ u v, u ≠ v → γ.r u v → u ∉ K ∧ v ∉ K) :
    ∀ {u v : V} (p : (wiredGraph G γ ω).Walk u v),
      (∀ w ∈ p.support, w ∈ K) → u ∈ K → OpenConnected G ω (innerEdges K) u v := by
  intro u v p
  induction p with
  | nil => intro _ _; exact OpenConnected.refl ω (innerEdges K) _
  | @cons a b c h p ih =>
      intro hsupp ha
      have hbK : b ∈ K := hsupp b (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem a p.start_mem_support)
      have hstep : OpenConnected G ω (innerEdges K) a b := by
        obtain ⟨hne, hcase⟩ := h
        rcases hcase with hr | ⟨e, he, heq⟩
        · exact absurd ha (hγ a b hne hr).1
        · have hadj : G.Adj a b := by
            rw [← SimpleGraph.mem_edgeSet, ← heq]
            exact e.2
          have hsub : (⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet) = e := by
            apply Subtype.ext
            exact heq.symm
          have hopen : ω ⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ = true := by
            rw [hsub]
            exact he
          exact OpenConnected.of_adj hadj (mem_innerEdges_iff.mpr ⟨ha, hbK⟩) hopen
      exact hstep.trans (ih (fun w hw => hsupp w (by
        rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem a hw)) hbK)

/-- A wired walk leaving `K` gives an ordinary open path from its start to the
complement of `K`, under the nonreflexive support hypothesis. -/
theorem exists_outside_of_walk_ne {γ : Setoid V} {ω : G.edgeSet → Bool}
    {K : Finset V} (hγ : ∀ u v, u ≠ v → γ.r u v → u ∉ K ∧ v ∉ K) :
    ∀ {u v : V} (p : (wiredGraph G γ ω).Walk u v), u ∈ K →
      (∃ w ∈ p.support, w ∉ K) → ∃ w : V, w ∉ K ∧ OpenConnected G ω Set.univ u w := by
  intro u v p
  induction p with
  | nil =>
      intro _ hex
      obtain ⟨w, hw, hwK⟩ := hex
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      subst hw
      exact absurd ‹_ ∈ K› hwK
  | @cons a b c h p ih =>
      intro ha hex
      rw [SimpleGraph.Walk.support_cons] at hex
      obtain ⟨w, hw, hwK⟩ := hex
      have hstep : OpenConnected G ω Set.univ a b := by
        obtain ⟨hne, hcase⟩ := h
        rcases hcase with hr | ⟨e, he, heq⟩
        · exact absurd ha (hγ a b hne hr).1
        · have hadj : G.Adj a b := by
            rw [← SimpleGraph.mem_edgeSet, ← heq]
            exact e.2
          have hsub : (⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet) = e := by
            apply Subtype.ext
            exact heq.symm
          have hopen : ω ⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ = true := by
            rw [hsub]
            exact he
          exact OpenConnected.of_adj hadj (Set.mem_univ _) hopen
      rcases List.mem_cons.mp hw with rfl | hwp
      · exact absurd ha hwK
      · by_cases hbK : b ∈ K
        · obtain ⟨w, hwK, hbw⟩ := ih hbK ⟨w, hwp, hwK⟩
          exact ⟨w, hwK, hstep.trans hbw⟩
        · exact ⟨b, hbK, hstep⟩

/-- Correct usable form of `ClusterEscape.escape_pair_of_wiredConn`: wiring
only needs to avoid `K` on pairs of distinct vertices.  The original hypothesis
also quantified over reflexive setoid pairs and was therefore impossible on a
nonempty `K`. -/
theorem escape_pair_of_wiredConn_ne {γ : Setoid V} {ω : G.edgeSet → Bool}
    {K : Finset V} (hγ : ∀ u v, u ≠ v → γ.r u v → u ∉ K ∧ v ∉ K) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (hconn : (wiredGraph G γ ω).Reachable x y)
    (hnotin : ¬ OpenConnected G ω (innerEdges K) x y) :
    ClusterMeetsOutside G ω x K ∧ ClusterMeetsOutside G ω y K := by
  obtain ⟨p⟩ := hconn
  have hex : ∃ w ∈ p.support, w ∉ K := by
    by_contra hcon
    refine hnotin (openConnected_of_walk_support_subset_ne hγ p (fun w hw => ?_) hx)
    by_contra hwK
    exact hcon ⟨w, hw, hwK⟩
  constructor
  · exact exists_outside_of_walk_ne hγ p hx hex
  · obtain ⟨w, hw, hwK⟩ := hex
    refine exists_outside_of_walk_ne hγ p.reverse hy ⟨w, ?_, hwK⟩
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hw

/-- Closing all coordinates outside a finite box decreases a configuration. -/
lemma closeOutside_le {B : FiniteBox G.edgeSet} (ω : G.edgeSet → Bool) :
    closeOutside B ω ≤ ω := by
  intro e
  by_cases he : e ∈ B.edges
  · simp [closeOutside, he]
  · simp [closeOutside, he]

/-- Closing one labelled global edge decreases a configuration. -/
lemma closeGlobalEdge_le (e : G.edgeSet) (ω : G.edgeSet → Bool) :
    closeGlobalEdge e ω ≤ ω := by
  intro f
  by_cases hf : f = e
  · subst f
    simp
  · simp [closeGlobalEdge_of_ne, hf]

end FK.NestedFinDLR
