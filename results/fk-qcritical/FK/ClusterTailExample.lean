/-
# Sharpness: root-cluster events are not tail measurable

The existence of an infinite open cluster is invariant under finite edge
modifications, so by
`FK.ClusterTail.zero_one_hasInfiniteCluster_of_zeroOneOn_tail` its probability
is zero or one under any zero--one tail law.  This file records why the *root*
cluster cannot replace it: on the ray graph, opening or closing the single first
edge `{0,1}` changes the root cluster from all of `ℕ` to `{0}`, while an
infinite open cluster exists in both configurations.  Hence the event "the
cluster of `0` is infinite" is not invariant under finite modifications, is not
measurable for the tail sigma-algebra, and the percolation probability `θ` is
not a tail event.
-/
import FK.TailSigmaBridge

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

namespace FK.ClusterTail

open CurvatureVariance.Infra.Percolation
open FK.ClusterCover

/-- The ray graph on `ℕ`: `u` and `v` are adjacent when they differ by one. -/
def rayGraph : SimpleGraph ℕ := SimpleGraph.fromRel fun u v => v = u + 1

lemma rayGraph_adj_succ (n : ℕ) : rayGraph.Adj n (n + 1) :=
  ⟨by omega, Or.inl rfl⟩

lemma rayGraph_adj_zero {v : ℕ} (h : rayGraph.Adj 0 v) : v = 1 := by
  obtain ⟨-, h | h⟩ := h
  · exact h
  · omega

/-- The walk from `0` to `n` along the ray. -/
def rayWalk : (n : ℕ) → rayGraph.Walk 0 n
  | 0 => .nil
  | n + 1 => (rayWalk n).concat (rayGraph_adj_succ n)

/-- All edges open. -/
def rayAllOpen : rayGraph.edgeSet → Bool := fun _ => true

/-- All edges open except the first one `{0,1}`. -/
def rayCutFirst : rayGraph.edgeSet → Bool :=
  fun e => if (e : Sym2 ℕ) = s(0, 1) then false else true

lemma rayGraph_cluster_allOpen :
    {y : ℕ | OpenConnected rayGraph rayAllOpen Set.univ 0 y} = Set.univ := by
  ext y
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  exact ⟨rayWalk y, fun d _ => ⟨Set.mem_univ _, rfl⟩⟩

lemma rayGraph_root_infinite :
    {y : ℕ | OpenConnected rayGraph rayAllOpen Set.univ 0 y}.Infinite := by
  rw [rayGraph_cluster_allOpen]
  exact Set.infinite_univ

/-- With the first edge closed, the open cluster of `0` is the singleton `{0}`. -/
lemma rayGraph_cluster_cut :
    {y : ℕ | OpenConnected rayGraph rayCutFirst Set.univ 0 y} = {0} := by
  ext y
  constructor
  · rintro ⟨p, hp⟩
    match p with
    | .nil => rfl
    | .cons (v := v) hadj q =>
      obtain ⟨hhead, -⟩ := isOpenIn_cons.mp hp
      have hv : v = 1 := rayGraph_adj_zero hadj
      subst hv
      have hclosed : rayCutFirst (⟨s(0, 1), rayGraph_adj_succ 0⟩ : rayGraph.edgeSet) = true :=
        hhead.2
      simp [rayCutFirst] at hclosed
  · rintro rfl
    exact OpenConnected.refl _ _ _

lemma rayGraph_root_not_infinite :
    ¬ {y : ℕ | OpenConnected rayGraph rayCutFirst Set.univ 0 y}.Infinite := by
  rw [rayGraph_cluster_cut]
  exact (Set.finite_singleton 0).not_infinite

lemma rayGraph_exists_infinite_cluster_allOpen : HasInfiniteCluster rayGraph rayAllOpen :=
  ⟨0, by rw [clusterAvoid_empty_eq]; exact rayGraph_root_infinite⟩

/-- The single edge `{0,1}`, as a set of unordered pairs. -/
def rayFirstEdge : Set (Sym2 ℕ) := {s(0, 1)}

lemma rayFirstEdge_finite : rayFirstEdge.Finite := by
  have hsingle : rayFirstEdge = ({s(0, 1)} : Set (Sym2 ℕ)) := rfl
  rw [hsingle]
  exact Set.finite_singleton _

lemma rayFirstEdge_agrees : ∀ e : rayGraph.edgeSet, (e : Sym2 ℕ) ∉ rayFirstEdge →
    rayAllOpen e = rayCutFirst e := by
  intro e he
  simp only [rayFirstEdge, Set.mem_singleton_iff] at he
  simp [rayAllOpen, rayCutFirst, he]

/-- An infinite open cluster still exists after closing the first edge: this is
the invariance theorem applied to the two configurations. -/
lemma rayGraph_exists_infinite_cluster_cut : HasInfiniteCluster rayGraph rayCutFirst :=
  (hasInfiniteCluster_congr rayFirstEdge_finite rayFirstEdge_agrees).mp
    rayGraph_exists_infinite_cluster_allOpen

/-- **Sharpness.**  The event that the cluster of `0` is infinite is not
invariant under changing finitely many edges, hence is not measurable for the
tail sigma-algebra, although "an infinite open cluster exists" is. -/
theorem not_dependsOn_rootCluster :
    ¬ DependsOn (· ∈ {ω : rayGraph.edgeSet → Bool |
        {y : ℕ | OpenConnected rayGraph ω Set.univ 0 y}.Infinite})
      {e : rayGraph.edgeSet | (e : Sym2 ℕ) ∈ rayFirstEdge}ᶜ := by
  intro h
  have hdep : (rayAllOpen ∈ {ω : rayGraph.edgeSet → Bool |
      {y : ℕ | OpenConnected rayGraph ω Set.univ 0 y}.Infinite}) =
      (rayCutFirst ∈ {ω : rayGraph.edgeSet → Bool |
      {y : ℕ | OpenConnected rayGraph ω Set.univ 0 y}.Infinite}) :=
    h (fun e he => rayFirstEdge_agrees e (by simpa using he))
  have hdep' : ({y : ℕ | OpenConnected rayGraph rayAllOpen Set.univ 0 y}.Infinite) =
      ({y : ℕ | OpenConnected rayGraph rayCutFirst Set.univ 0 y}.Infinite) := hdep
  exact rayGraph_root_not_infinite (hdep' ▸ rayGraph_root_infinite)

end FK.ClusterTail
