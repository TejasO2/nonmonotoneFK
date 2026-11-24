/-
# Sharpness: "at least two infinite clusters" is not a tail event

The event that *some* infinite open cluster exists is invariant under finite edge
modifications.  The event that at least *two* infinite clusters exist is not: on
the bi-infinite line, closing the single edge `{0,1}` splits one infinite cluster
into two.  Consequently the number of infinite clusters is not a
finite-modification tail-measurable function, and its almost sure constancy for
i.i.d. laws must come from invariance under graph automorphisms (ergodicity),
not from a finite-modification zero--one argument.

All statements here concern the explicit line graph on `ℤ`.
-/
import FK.ClusterTailExample

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

namespace FK.ClusterTail

open CurvatureVariance.Infra.Percolation
open FK.ClusterCover

/-- The bi-infinite line graph on `ℤ`. -/
def lineGraph : SimpleGraph ℤ := SimpleGraph.fromRel fun u v => v = u + 1

lemma lineGraph_adj_succ (n : ℤ) : lineGraph.Adj n (n + 1) :=
  ⟨fun h => by omega, Or.inl rfl⟩

lemma lineGraph_adj_pred (n : ℤ) : lineGraph.Adj n (n - 1) :=
  ⟨fun h => by omega, Or.inr (by ring)⟩

/-- All edges open. -/
def lineAllOpen : lineGraph.edgeSet → Bool := fun _ => true

/-- All edges open except `{0,1}`. -/
def lineCut : lineGraph.edgeSet → Bool :=
  fun e => if (e : Sym2 ℤ) = s(0, 1) then false else true

lemma lineCut_ne_zero_one {e : lineGraph.edgeSet} (he : (e : Sym2 ℤ) ≠ s(0, 1)) :
    lineCut e = true := by
  simp [lineCut, he]

lemma lineCut_false : lineCut (⟨s(0, 1), lineGraph_adj_succ 0⟩ : lineGraph.edgeSet) = false := by
  simp [lineCut]

/-- A single open step in the cut configuration, away from `{0,1}`. -/
lemma lineCut_step {a b : ℤ} (hadj : lineGraph.Adj a b)
    (hne : (⟨s(a, b), hadj⟩ : lineGraph.edgeSet) ≠ ⟨s(0, 1), lineGraph_adj_succ 0⟩) :
    OpenConnected lineGraph lineCut Set.univ a b :=
  OpenConnected.of_adj hadj (Set.mem_univ _)
    (lineCut_ne_zero_one (fun h => hne (Subtype.ext h)))

/-- The edge of a step along the line differs from `{0,1}` unless the step
touches `0` from above. -/
lemma lineStep_edge_ne {a : ℤ} (h : a ≠ 0) :
    (⟨s(a, a + 1), lineGraph_adj_succ a⟩ : lineGraph.edgeSet) ≠
      ⟨s(0, 1), lineGraph_adj_succ 0⟩ := by
  intro hcontra
  have hval : (s(a, a + 1) : Sym2 ℤ) = s(0, 1) := congrArg Subtype.val hcontra
  rcases Sym2.eq_iff.mp hval with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h h1
  · omega

lemma lineStep_edge_ne' {a : ℤ} (h : a ≤ 0) :
    (⟨s(a, a - 1), lineGraph_adj_pred a⟩ : lineGraph.edgeSet) ≠
      ⟨s(0, 1), lineGraph_adj_succ 0⟩ := by
  intro hcontra
  have hval : (s(a, a - 1) : Sym2 ℤ) = s(0, 1) := congrArg Subtype.val hcontra
  rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Every vertex is reachable from `0` when all edges are open. -/
lemma line_reachable_all (y : ℤ) : OpenConnected lineGraph lineAllOpen Set.univ 0 y := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg y
  · subst hn
    induction n with
    | zero => exact OpenConnected.refl _ _ _
    | succ k ih =>
      have hcast : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      have hstep : OpenConnected lineGraph lineAllOpen Set.univ (k : ℤ) ((k : ℤ) + 1) :=
        OpenConnected.of_adj (lineGraph_adj_succ _) (Set.mem_univ _) rfl
      simpa only [hcast] using ih.trans hstep
  · subst hn
    induction n with
    | zero => exact OpenConnected.refl _ _ _
    | succ k ih =>
      have hcast : (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
      have hstep : OpenConnected lineGraph lineAllOpen Set.univ (-(k : ℤ)) (-(k : ℤ) - 1) :=
        OpenConnected.of_adj (lineGraph_adj_pred _) (Set.mem_univ _) rfl
      simpa only [hcast] using ih.trans hstep

lemma lineGraph_cluster_allOpen :
    {y : ℤ | OpenConnected lineGraph lineAllOpen Set.univ 0 y} = Set.univ := by
  ext y
  exact ⟨fun _ => Set.mem_univ _, fun _ => line_reachable_all y⟩

/-- Along a walk avoiding `{0,1}`, the vertex stays on the starting side of `0`. -/
lemma line_avoid_cut {x y : ℤ} (p : lineGraph.Walk x y) :
    IsOpenIn lineCut Set.univ p → x ≤ 0 → y ≤ 0 := by
  induction p with
  | nil => intro _ hx; exact hx
  | @cons u v w hadj q ih =>
    intro hp hx
    obtain ⟨hhead, htail⟩ := isOpenIn_cons.mp hp
    have hne : (⟨s(u, v), hadj⟩ : lineGraph.edgeSet) ≠ ⟨s(0, 1), lineGraph_adj_succ 0⟩ := by
      intro hcontra
      have hf : lineCut (⟨s(u, v), hadj⟩ : lineGraph.edgeSet) = false := by
        rw [hcontra, lineCut_false]
      rw [hf] at hhead
      exact Bool.false_ne_true hhead.2
    have hdecode : (s(u, v) : Sym2 ℤ) ≠ s(0, 1) := fun h => hne (Subtype.ext h)
    obtain ⟨-, hstep | hstep⟩ := hadj
    · -- v = u + 1, and `u ≠ 0`, so `u ≤ -1`
      have hu : u ≠ 0 := by
        intro hu
        subst hu
        subst hstep
        exact hdecode rfl
      have hv : v ≤ 0 := by omega
      exact ih htail hv
    · -- u = v + 1
      have hv : v ≤ 0 := by omega
      exact ih htail hv

/-- Non-positive integers are reachable from `0` in the cut configuration. -/
lemma line_reachable_cut_nonpos (n : ℕ) :
    OpenConnected lineGraph lineCut Set.univ 0 (-(n : ℤ)) := by
  induction n with
  | zero => exact OpenConnected.refl _ _ _
  | succ k ih =>
    have hk : (-(k : ℤ) - 1) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have hstep : OpenConnected lineGraph lineCut Set.univ (-(k : ℤ)) (-(k : ℤ) - 1) :=
      lineCut_step (lineGraph_adj_pred _) (lineStep_edge_ne' (by omega))
    rw [hk] at hstep
    exact ih.trans hstep

/-- Under the cut configuration the cluster of `0` is exactly the non-positive
integers. -/
lemma lineGraph_cluster_cut :
    {y : ℤ | OpenConnected lineGraph lineCut Set.univ 0 y} = {y : ℤ | y ≤ 0} := by
  ext y
  constructor
  · rintro ⟨p, hp⟩
    exact line_avoid_cut p hp (le_refl (0 : ℤ))
  · intro hy
    obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg y
    · subst hn
      have h0 : (n : ℤ) ≤ 0 := hy
      have hn0 : n = 0 := by omega
      subst hn0
      exact OpenConnected.refl _ _ _
    · subst hn
      exact line_reachable_cut_nonpos n

/-- The cluster of `1` is infinite under the cut configuration. -/
lemma lineGraph_one_infinite :
    {y : ℤ | OpenConnected lineGraph lineCut Set.univ 1 y}.Infinite := by
  refine Set.Infinite.mono (s := Set.range fun n : ℕ => 1 + (n : ℤ)) ?_ ?_
  · rintro y ⟨n, rfl⟩
    induction n with
    | zero => exact OpenConnected.refl _ _ _
    | succ k ih =>
      have hcast : (1 + (k : ℤ) + 1) = 1 + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      have hstep : OpenConnected lineGraph lineCut Set.univ (1 + (k : ℤ)) (1 + (k : ℤ) + 1) :=
        lineCut_step (lineGraph_adj_succ _) (lineStep_edge_ne (by omega))
      simpa only [hcast, Set.mem_ofPred_eq] using ih.trans hstep
  · exact Set.infinite_range_of_injective (f := fun n : ℕ => 1 + (n : ℤ)) (by
      intro a b hab
      have hab' : (1 : ℤ) + (a : ℤ) = 1 + (b : ℤ) := hab
      have h : (a : ℤ) = (b : ℤ) := by omega
      exact_mod_cast h)

/-- At least two infinite open clusters: two vertices with infinite clusters that
are not connected. -/
def TwoInfiniteClusters (G : SimpleGraph ℤ) (ω : G.edgeSet → Bool) : Prop :=
  ∃ a b : ℤ, {y : ℤ | OpenConnected G ω Set.univ a y}.Infinite ∧
    ¬ OpenConnected G ω Set.univ b a

lemma twoInfiniteClusters_cut : TwoInfiniteClusters lineGraph lineCut := by
  refine ⟨1, 0, lineGraph_one_infinite, ?_⟩
  intro hcon
  have hmem : (1 : ℤ) ∈ {y : ℤ | y ≤ 0} := by
    rw [← lineGraph_cluster_cut]
    exact hcon
  have hle : (1 : ℤ) ≤ 0 := hmem
  omega

lemma not_twoInfiniteClusters_allOpen : ¬ TwoInfiniteClusters lineGraph lineAllOpen := by
  rintro ⟨a, b, -, hnab⟩
  have hb : OpenConnected lineGraph lineAllOpen Set.univ 0 b := line_reachable_all b
  have ha : OpenConnected lineGraph lineAllOpen Set.univ 0 a := line_reachable_all a
  exact hnab ((FK.InfiniteVolume.ConventionGeometry.openConnected_symm hb).trans ha)

/-- The single edge `{0,1}`, as a set of unordered pairs. -/
def lineFirstEdge : Set (Sym2 ℤ) := {s(0, 1)}

lemma lineFirstEdge_finite : lineFirstEdge.Finite := by
  have hsingle : lineFirstEdge = ({s(0, 1)} : Set (Sym2 ℤ)) := rfl
  rw [hsingle]
  exact Set.finite_singleton _

lemma lineFirstEdge_agrees : ∀ e : lineGraph.edgeSet, (e : Sym2 ℤ) ∉ lineFirstEdge →
    lineAllOpen e = lineCut e := by
  intro e he
  simp only [lineFirstEdge, Set.mem_singleton_iff] at he
  simp [lineAllOpen, lineCut, he]

/-- **Sharpness.**  The event that at least two infinite open clusters exist is
not invariant under changing finitely many edges, hence is not measurable for
the tail sigma-algebra, although the existence of one infinite cluster is. -/
theorem not_dependsOn_twoInfiniteClusters :
    ¬ DependsOn (· ∈ {ω : lineGraph.edgeSet → Bool | TwoInfiniteClusters lineGraph ω})
      {e : lineGraph.edgeSet | (e : Sym2 ℤ) ∈ lineFirstEdge}ᶜ := by
  intro h
  have hdep : (lineAllOpen ∈ {ω : lineGraph.edgeSet → Bool |
      TwoInfiniteClusters lineGraph ω}) =
      (lineCut ∈ {ω : lineGraph.edgeSet → Bool | TwoInfiniteClusters lineGraph ω}) :=
    h (fun e he => lineFirstEdge_agrees e (by simpa using he))
  have hdep' : TwoInfiniteClusters lineGraph lineAllOpen = TwoInfiniteClusters lineGraph lineCut :=
    hdep
  exact not_twoInfiniteClusters_allOpen (Eq.mpr hdep' twoInfiniteClusters_cut)

end FK.ClusterTail
