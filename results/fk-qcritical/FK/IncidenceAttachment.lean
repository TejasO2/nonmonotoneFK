import FK.IncidenceGeometry

open scoped Classical
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane
open FK.ClusterCover

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- From an outside infinite incident-avoiding component and an original full
open path reaching it, construct a unique last-parent attachment and arms of
every metric radius from a prescribed centre. -/
theorem exists_incidence_attachment [G.LocallyFinite] (hG : G.Connected)
    {U : Set V} {r z : V} (p : G.Walk r z)
    (hp : IsOpenIn ω Set.univ p) (hr : r ∈ U) (hz : z ∉ U)
    (hinf : (clusterAvoid G ω (incidence G U) z).Infinite) (y : V) :
    ∃ a : V, a ∈ U ∧ ∃ b : V, b ∉ U ∧
      (clusterAvoid G ω (incidence G U) b).Infinite ∧ ∃ hab : G.Adj a b,
        ∃_ : OpenConnected G ω (Set.univ \ incidence G U) b z, ∀ n : ℕ, ∃ w : V, n ≤ G.dist y w ∧ ∃ arm : G.Walk b w,
          IsOpenIn ω (Set.univ \ incidence G U) arm ∧
          IsOpenIn ω Set.univ (SimpleGraph.Walk.cons hab arm) ∧
          ∀ x ∈ arm.support, x ∈ clusterAvoid G ω (incidence G U) b := by
  obtain ⟨a, haU, q, hq, htail⟩ := exists_lastIncidenceSuffix p hp hr hz
  have hnon : ¬ q.Nil := by
    intro hn
    have heq : a = z := SimpleGraph.Walk.Nil.eq hn
    exact hz (heq ▸ haU)
  have hqtailOpen : IsOpenIn ω Set.univ q.tail := by
    intro d hd
    rw [SimpleGraph.Walk.darts_tail] at hd
    exact hq d (List.mem_of_mem_tail hd)
  have hrootTail : q.snd ∉ U := htail q.snd (q.snd_mem_tail_support hnon)
  have hqtailAvoid : IsOpenIn ω (Set.univ \ incidence G U) q.tail := by
    apply isOpenIn_avoidIncidence_of_tail q.tail hqtailOpen hrootTail
    intro x hx
    rw [SimpleGraph.Walk.support_tail_of_not_nil q hnon] at hx
    exact htail x (List.mem_of_mem_tail hx)
  have hinfTail : (clusterAvoid G ω (incidence G U) q.snd).Infinite :=
    hinf.mono (clusterAvoid_subset_of_openConnected ⟨q.tail, hqtailAvoid⟩)
  have hlen : 0 < q.length := (SimpleGraph.Walk.not_nil_iff_lt_length).mp hnon
  have hab : G.Adj a q.snd := by
    have hadj := q.adj_getVert_succ (i := 0) hlen
    simpa using hadj
  refine ⟨a, haU, q.snd, hrootTail, hinfTail, hab, ⟨q.tail, hqtailAvoid⟩, ?_⟩
  intro n
  obtain ⟨w, hw, arm⟩ := exists_far_mem_of_infinite hG hinfTail y n
  obtain ⟨arm, harm⟩ := arm
  have hlenD : 0 < q.darts.length := by
    rw [SimpleGraph.Walk.length_darts]
    exact hlen
  have hd : q.darts[0] ∈ q.darts := List.getElem_mem hlenD
  have hfirst := hq q.darts[0] hd
  rw [q.darts_getElem_eq_getVert 0 hlenD] at hfirst
  have hfirst' : ω ⟨s(a, q.snd), hab⟩ = true := by
    simpa using hfirst.2
  have hcons : IsOpenIn ω Set.univ (SimpleGraph.Walk.cons hab arm) := by
    apply isOpenIn_cons.mpr
    exact ⟨⟨Set.mem_univ _, hfirst'⟩,
      harm.mono_edges (Set.subset_univ _)⟩
  refine ⟨w, hw, arm, harm, hcons, ?_⟩
  intro x hx
  exact mem_clusterAvoid_of_mem_support arm harm hx
