import FK.ThetaDuality

/-!
# Generalized theta graphs and their bundled-cycle duals

For a finite type `ι`, `lengthTwoTheta ι` consists of two terminals joined by
one two-edge path for each `i : ι`.  Thus it is the complete bipartite graph
`K(2, |ι|)`, with every internal vertex retained.  If `G` is a labelled cycle
with edge type `ι`, its two-parallel-copy thickening is the facial dual of this
theta graph.  The proofs below compute both cycle matroids from their actual
connection graphs; no matroid-duality premise occurs.
-/

namespace FK.Finite.PlaneMatroid

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

namespace GeneralizedTheta

variable {ι : Type*} [Fintype ι]

/-- Two terminals, with one independent internal vertex per branch. -/
abbrev lengthTwoTheta (ι : Type*) [Fintype ι] : LabelledMultigraph where
  Vertex := Bool ⊕ ι
  Edge := ι × Bool
  source e := Sum.inl e.2
  target e := Sum.inr e.1

/-- The two edges of the terminal-to-terminal path indexed by `i`. -/
def branch (i : ι) : Set (lengthTwoTheta ι).Edge := {e | e.1 = i}

/-- A spanning tree: one complete branch and one selected edge in each other
branch.  The definition also selects one edge in the complete branch. -/
def spanningTree (full : ι) (sel : ι → Bool) : Set (lengthTwoTheta ι).Edge :=
  {e | e.1 = full ∨ e.2 = sel e.1}

lemma mem_branch_iff (i : ι) (e : (lengthTwoTheta ι).Edge) :
    e ∈ branch i ↔ e.1 = i := Iff.rfl

lemma selected_mem_spanningTree (full : ι) (sel : ι → Bool) (i : ι) :
    (i, sel i) ∈ spanningTree full sel := by
  exact Or.inr rfl

lemma full_mem_spanningTree (full : ι) (sel : ι → Bool) (b : Bool) :
    (full, b) ∈ spanningTree full sel := by
  exact Or.inl rfl

/-- The open terminal-to-internal adjacency contributed by one label. -/
lemma adj_terminal_internal (ω : (lengthTwoTheta ι).Configuration)
    (i : ι) (b : Bool) (he : ω (i, b) = true) :
    ((lengthTwoTheta ι).connectionGraph (lengthTwoTheta ι).freeBoundary ω).Adj
      (Sum.inl b) (Sum.inr i) := by
  have hne : (Sum.inl b : Bool ⊕ ι) ≠ Sum.inr i := by simp
  refine ⟨hne, Or.inr ⟨(i, b), he, ?_⟩⟩
  exact Or.inl ⟨rfl, rfl⟩

lemma adj_internal_terminal (ω : (lengthTwoTheta ι).Configuration)
    (i : ι) (b : Bool) (he : ω (i, b) = true) :
    ((lengthTwoTheta ι).connectionGraph (lengthTwoTheta ι).freeBoundary ω).Adj
      (Sum.inr i) (Sum.inl b) :=
  (adj_terminal_internal ω i b he).symm

lemma spanningTree_preconnected (full : ι) (sel : ι → Bool) :
    ((lengthTwoTheta ι).connectionGraph (lengthTwoTheta ι).freeBoundary
      ((lengthTwoTheta ι).setConfig (spanningTree full sel))).Preconnected := by
  have hopen (i : ι) : (lengthTwoTheta ι).setConfig (spanningTree full sel)
      (i, sel i) = true := by
    simp only [setConfig, decide_eq_true_eq]
    exact selected_mem_spanningTree full sel i
  have hfull (b : Bool) : (lengthTwoTheta ι).setConfig (spanningTree full sel)
      (full, b) = true := by
    simp only [setConfig, decide_eq_true_eq]
    exact full_mem_spanningTree full sel b
  have hroot : ∀ v, ((lengthTwoTheta ι).connectionGraph
      (lengthTwoTheta ι).freeBoundary
      ((lengthTwoTheta ι).setConfig (spanningTree full sel))).Reachable
        v (Sum.inl false) := by
    intro v
    cases v with
    | inl b =>
        cases b with
        | false => exact SimpleGraph.Reachable.refl _
        | true =>
            exact (adj_terminal_internal _ full true (hfull true)).reachable.trans
              (adj_internal_terminal _ full false (hfull false)).reachable
    | inr i =>
        exact (adj_internal_terminal _ i (sel i) (hopen i)).reachable.trans
          ((adj_terminal_internal _ full (sel i) (hfull (sel i))).reachable.trans
            (adj_internal_terminal _ full false (hfull false)).reachable)
  intro u v
  exact (hroot u).trans (hroot v).symm

/-- The selected edges plus the extra edge in the complete branch. -/
lemma spanningTree_eq_insert (full : ι) (sel : ι → Bool) :
    spanningTree full sel = insert (full, !sel full)
      (Set.range fun i => (i, sel i)) := by
  ext ⟨i, b⟩
  simp only [spanningTree, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_range,
    Prod.mk.injEq]
  constructor
  · intro h
    by_cases hi : i = full
    · subst i
      cases b <;> simp_all
    · right
      exact ⟨i, rfl, (h.resolve_left hi).symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩)
    · simp
    · simp

lemma spanningTree_ncard (full : ι) (sel : ι → Bool) :
    (spanningTree full sel).ncard = Fintype.card ι + 1 := by
  rw [spanningTree_eq_insert]
  have hnot : (full, !sel full) ∉ Set.range (fun i => (i, sel i)) := by
    rintro ⟨i, hi⟩
    have hif : i = full := congrArg Prod.fst hi
    subst i
    have hb : sel full = !sel full := congrArg Prod.snd hi
    cases h : sel full <;> simp [h] at hb
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_range_of_injective]
  · simp [Nat.card_eq_fintype_card, add_comm]
  · intro i j hij
    exact congrArg Prod.fst hij

/-- Every explicit candidate tree is independent in the actual labelled cycle
matroid.  This uses its connectivity and edge/component count. -/
lemma spanningTree_indep (full : ι) (sel : ι → Bool) :
    (lengthTwoTheta ι).cycleMatroid.Indep (spanningTree full sel) := by
  simp only [cycleMatroid_indep, isOpenForest_setConfig_iff]
  have hcomp : (lengthTwoTheta ι).componentCount (lengthTwoTheta ι).freeBoundary
      ((lengthTwoTheta ι).setConfig (spanningTree full sel)) = 1 :=
    componentCount_eq_one_of_preconnected _ _ _ (Sum.inl false)
      (spanningTree_preconnected full sel)
  rw [hcomp, spanningTree_ncard]
  change 1 + (Fintype.card ι + 1) = Fintype.card (Bool ⊕ ι)
  rw [Fintype.card_sum, Fintype.card_bool]
  omega

end GeneralizedTheta
end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid
namespace GeneralizedTheta

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane FK.Finite.Conditional
open FK.FiniteFiber

variable {ι : Type*} [Fintype ι]

lemma branch_subset_iff (A : Set (ι × Bool)) (i : ι) :
    branch i ⊆ A ↔ ∀ b, (i, b) ∈ A := by
  constructor
  · intro h b
    exact h rfl
  · intro h ⟨j, b⟩ hj
    change j = i at hj
    subst j
    exact h b

/-- Two complete terminal paths form a dependent set.  After deleting the
first edge of path `i`, a three-edge route through path `j` and the other edge
of path `i` still joins its endpoints. -/
lemma not_indep_of_branch_pair {A : Set (ι × Bool)} {i j : ι} (hij : i ≠ j)
    (hi : branch i ⊆ A) (hj : branch j ⊆ A) :
    ¬ (lengthTwoTheta ι).cycleMatroid.Indep A := by
  classical
  letI : DecidableEq (ι × Bool) := Classical.decEq _
  intro hA
  rw [(lengthTwoTheta ι).cycleMatroid_indep] at hA
  have hxA : (i, false) ∈ A := hi rfl
  apply hA (i, false) (by simp [setConfig, hxA])
  unfold endpointsConnectedWithout
  have hopen {e : ι × Bool} (heA : e ∈ A) (hex : e ≠ (i, false)) :
      withEdge (i, false) false ((lengthTwoTheta ι).setConfig A) e = true := by
    rw [withEdge_off hex]
    simp [setConfig, heA]
  have hne_j (b : Bool) : (j, b) ≠ (i, false) := by
    intro h
    apply hij
    exact (congrArg Prod.fst h).symm
  have hne_i : (i, true) ≠ (i, false) := by simp
  have h₁ := adj_terminal_internal
    (withEdge (i, false) false ((lengthTwoTheta ι).setConfig A)) j false
      (hopen (hj rfl) (hne_j false))
  have h₂ := adj_internal_terminal
    (withEdge (i, false) false ((lengthTwoTheta ι).setConfig A)) j true
      (hopen (hj rfl) (hne_j true))
  have h₃ := adj_terminal_internal
    (withEdge (i, false) false ((lengthTwoTheta ι).setConfig A)) i true
      (hopen (hi rfl) hne_i)
  exact h₁.reachable.trans (h₂.reachable.trans h₃.reachable)

lemma exists_selector_of_not_branch_subset {A : Set (ι × Bool)} {i : ι}
    (hi : ¬ branch i ⊆ A) :
    ∃ s : Bool, ∀ b, (i, b) ∈ A → b = s := by
  by_cases hf : (i, false) ∈ A
  · refine ⟨false, ?_⟩
    intro b hb
    cases b with
    | false => rfl
    | true =>
        exfalso
        apply hi
        intro ⟨j, b⟩ hj
        change j = i at hj
        subst j
        cases b
        · exact hf
        · exact hb
  · refine ⟨true, ?_⟩
    intro b hb
    cases b with
    | false => exact (hf hb).elim
    | true => rfl

/-- Any set with no complete branch except possibly the designated one is
contained in an explicit spanning tree. -/
lemma exists_spanningTree_superset (A : Set (ι × Bool)) (full : ι)
    (h : ∀ i, i ≠ full → ¬ branch i ⊆ A) :
    ∃ sel, A ⊆ spanningTree full sel := by
  have hs : ∀ i, ∃ s : Bool, i = full ∨ ∀ b, (i, b) ∈ A → b = s := by
    intro i
    by_cases hi : i = full
    · exact ⟨false, Or.inl hi⟩
    · obtain ⟨s, hs⟩ := exists_selector_of_not_branch_subset (h i hi)
      exact ⟨s, Or.inr hs⟩
  choose sel hs using hs
  refine ⟨sel, ?_⟩
  rintro ⟨i, b⟩ hb
  change i = full ∨ b = sel i
  rcases hs i with hi | hi
  · exact Or.inl hi
  · exact Or.inr (hi b hb)

/-- **Primal independence.**  A set of labels is a forest exactly when at
most one of its terminal-to-terminal branches is complete. -/
theorem indep_iff_atMostOne_branch [Nonempty ι] (A : Set (ι × Bool)) :
    (lengthTwoTheta ι).cycleMatroid.Indep A ↔
      ∀ i j, branch i ⊆ A → branch j ⊆ A → i = j := by
  constructor
  · intro hA i j hi hj
    by_contra hij
    exact not_indep_of_branch_pair hij hi hj hA
  · intro hA
    by_cases hf : ∃ i, branch i ⊆ A
    · obtain ⟨full, hfull⟩ := hf
      have hother : ∀ i, i ≠ full → ¬ branch i ⊆ A := by
        intro i hi hAi
        exact hi (hA i full hAi hfull)
      obtain ⟨sel, hsub⟩ := exists_spanningTree_superset A full hother
      exact (spanningTree_indep full sel).subset hsub
    · push_neg at hf
      let full : ι := Classical.choice inferInstance
      obtain ⟨sel, hsub⟩ := exists_spanningTree_superset A full
        (fun i _ => hf i)
      exact (spanningTree_indep full sel).subset hsub

end GeneralizedTheta

end FK.Finite.PlaneMatroid

namespace FK.Finite.PlaneMatroid.GeneralizedTheta

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane
open FK.FiniteFiber FK.Finite.Conditional

variable {ι : Type*} [Fintype ι]

/-- Bases retain one complete path and one edge from every remaining path. -/
theorem isBase_iff_spanningTree [Nonempty ι] (B : Set (ι × Bool)) :
    (lengthTwoTheta ι).cycleMatroid.IsBase B ↔
      ∃ full sel, B = spanningTree full sel := by
  constructor
  · intro hB
    have hno := (indep_iff_atMostOne_branch B).mp hB.indep
    by_cases hf : ∃ i, branch i ⊆ B
    · obtain ⟨full, hfull⟩ := hf
      have hother : ∀ i, i ≠ full → ¬ branch i ⊆ B := by
        intro i hi hAi
        exact hi (hno i full hAi hfull)
      obtain ⟨sel, hsub⟩ := exists_spanningTree_superset B full hother
      exact ⟨full, sel, hB.eq_of_subset_indep (spanningTree_indep full sel) hsub⟩
    · push_neg at hf
      let full : ι := Classical.choice inferInstance
      obtain ⟨sel, hsub⟩ := exists_spanningTree_superset B full
        (fun i _ => hf i)
      exact ⟨full, sel, hB.eq_of_subset_indep (spanningTree_indep full sel) hsub⟩
  · rintro ⟨full, sel, rfl⟩
    apply (spanningTree_indep full sel).isBase_of_forall_insert
    rintro ⟨i, b₀⟩ he
    have heB : (i, b₀) ∉ spanningTree full sel := by
      simpa using he.2
    have hi : i ≠ full := by
      intro hi
      apply heB
      exact Or.inl hi
    have hb₀ : b₀ ≠ sel i := by
      intro hb
      apply heB
      exact Or.inr hb
    intro hdep
    apply hi
    apply ((indep_iff_atMostOne_branch _).mp hdep) i full
    · rw [branch_subset_iff]
      intro b
      by_cases hb : b = b₀
      · subst b
        exact Set.mem_insert _ _
      · apply Set.mem_insert_of_mem
        have hsel : b = sel i := by
          cases b₀ <;> cases b <;> simp_all
        exact Or.inr hsel
    · exact (branch_subset_iff _ _).mpr (fun b =>
        Set.mem_insert_of_mem _ (full_mem_spanningTree full sel b))

end FK.Finite.PlaneMatroid.GeneralizedTheta

namespace FK.Finite.PlaneMatroid.GeneralizedTheta

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

variable {ι : Type*} [Fintype ι]

lemma branch_subset_union_iff {i j k : ι} :
    branch k ⊆ branch i ∪ branch j ↔ k = i ∨ k = j := by
  constructor
  · intro h
    have hk := h (show (k, false) ∈ branch k from rfl)
    simpa [branch] using hk
  · rintro (rfl | rfl)
    · exact Set.Subset.trans (Set.subset_union_left) (fun _ h => h)
    · exact Set.Subset.trans (Set.subset_union_right) (fun _ h => h)

lemma indep_twoBranches_delete [Nonempty ι] {i j : ι} (e : ι × Bool)
    (he : e ∈ branch i ∪ branch j) :
    (lengthTwoTheta ι).cycleMatroid.Indep ((branch i ∪ branch j) \ {e}) := by
  rw [indep_iff_atMostOne_branch]
  intro k l hk hl
  have hk' : branch k ⊆ branch i ∪ branch j := hk.trans Set.diff_subset
  have hl' : branch l ⊆ branch i ∪ branch j := hl.trans Set.diff_subset
  have hki := branch_subset_union_iff.mp hk'
  have hlj := branch_subset_union_iff.mp hl'
  rcases he with hei | hej
  · have hbroken : ¬ branch i ⊆ (branch i ∪ branch j) \ {e} := by
      intro hi
      exact (hi hei).2 (Set.mem_singleton e)
    rcases hki with rfl | rfl <;> rcases hlj with rfl | rfl
    · rfl
    · exact (hbroken hk).elim
    · exact (hbroken hl).elim
    · rfl
  · have hbroken : ¬ branch j ⊆ (branch i ∪ branch j) \ {e} := by
      intro hj
      exact (hj hej).2 (Set.mem_singleton e)
    rcases hki with rfl | rfl <;> rcases hlj with rfl | rfl
    · rfl
    · exact (hbroken hl).elim
    · exact (hbroken hk).elim
    · rfl

/-- **Exact circuit characterization.**  The matroid circuits are precisely
the completions of two distinct terminal paths, and no others. -/
theorem isCircuit_iff_two_branches [Nonempty ι] (C : Set (ι × Bool)) :
    (lengthTwoTheta ι).cycleMatroid.IsCircuit C ↔
      ∃ i j, i ≠ j ∧ C = branch i ∪ branch j := by
  constructor
  · intro hC
    have hex : ∃ i j, i ≠ j ∧ branch i ⊆ C ∧ branch j ⊆ C := by
      by_contra hn
      apply hC.not_indep
      rw [indep_iff_atMostOne_branch]
      intro i j hi hj
      by_contra hij
      exact hn ⟨i, j, hij, hi, hj⟩
    obtain ⟨i, j, hij, hi, hj⟩ := hex
    refine ⟨i, j, hij, ?_⟩
    have hsub : branch i ∪ branch j ⊆ C := Set.union_subset hi hj
    have hdep : (lengthTwoTheta ι).cycleMatroid.Dep (branch i ∪ branch j) := by
      refine ⟨?_, by simp⟩
      exact not_indep_of_branch_pair hij Set.subset_union_left Set.subset_union_right
    exact ((Matroid.isCircuit_iff.mp hC).2 hdep hsub).symm
  · rintro ⟨i, j, hij, rfl⟩
    rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, by simp⟩
      exact not_indep_of_branch_pair hij Set.subset_union_left Set.subset_union_right
    · intro e he
      exact indep_twoBranches_delete e he

end FK.Finite.PlaneMatroid.GeneralizedTheta

namespace FK.Finite.PlaneMatroid.GeneralizedTheta

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane
open FK.FiniteFiber FK.Finite.Conditional

/-- A generic open labelled edge joins its endpoints, even in the loop case. -/
lemma reachable_of_open (G : LabelledMultigraph) (ω : G.Configuration)
    (e : G.Edge) (he : ω e = true) :
    (G.connectionGraph G.freeBoundary ω).Reachable (G.source e) (G.target e) := by
  by_cases hst : G.source e = G.target e
  · rw [hst]
  · exact (show (G.connectionGraph G.freeBoundary ω).Adj (G.source e) (G.target e) from
      ⟨hst, Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩).reachable

variable (G : LabelledMultigraph)

/-- Two parallel copies of every label of `G`, on the same vertices. -/
abbrev bundledGraph : LabelledMultigraph where
  Vertex := G.Vertex
  Edge := G.Edge × Bool
  source e := G.source e.1
  target e := G.target e.1

/-- No two selected labels are parallel copies of the same base label. -/
def AtMostOneCopy (A : Set (G.Edge × Bool)) : Prop :=
  ∀ e b c, (e, b) ∈ A → (e, c) ∈ A → b = c

variable {G}

lemma connectionGraph_bundledGraph (A : Set (G.Edge × Bool)) :
    (bundledGraph G).connectionGraph (bundledGraph G).freeBoundary
        ((bundledGraph G).setConfig A) =
      G.connectionGraph G.freeBoundary (G.setConfig (Prod.fst '' A)) := by
  ext u v
  constructor
  · rintro ⟨huv, hwire | ⟨e, he, hjoin⟩⟩
    · exact ⟨huv, Or.inl hwire⟩
    · refine ⟨huv, Or.inr ⟨e.1, ?_, hjoin⟩⟩
      simp only [setConfig, decide_eq_true_eq] at he ⊢
      exact ⟨e, he, rfl⟩
  · rintro ⟨huv, hwire | ⟨f, hf, hjoin⟩⟩
    · exact ⟨huv, Or.inl hwire⟩
    · simp only [setConfig, decide_eq_true_eq] at hf
      obtain ⟨e, heA, rfl⟩ := hf
      refine ⟨huv, Or.inr ⟨e, ?_, hjoin⟩⟩
      simp [setConfig, heA]

lemma image_fst_diff_singleton_of_atMostOneCopy {A : Set (G.Edge × Bool)}
    (hA : AtMostOneCopy G A) (e : G.Edge) (b : Bool) (hb : (e, b) ∈ A) :
    Prod.fst '' (A \ {(e, b)}) = (Prod.fst '' A) \ {e} := by
  ext f
  constructor
  · rintro ⟨x, ⟨hxA, hxne⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    intro hfe
    subst e
    have hbc : x.2 = b := hA x.1 x.2 b hxA hb
    apply hxne
    apply Prod.ext
    · rfl
    · exact hbc
  · rintro ⟨⟨x, hxA, hfx⟩, hfe⟩
    refine ⟨x, ⟨hxA, ?_⟩, hfx⟩
    intro hxe
    apply hfe
    change f = e
    rw [← hfx]
    exact congrArg Prod.fst hxe

/-- With at most one copy per base label, forests in the bundled graph are
exactly forests of the projected support in the base graph. -/
lemma isOpenForest_bundledGraph_iff {A : Set (G.Edge × Bool)}
    (hA : AtMostOneCopy G A) :
    (bundledGraph G).IsOpenForest (bundledGraph G).freeBoundary
        ((bundledGraph G).setConfig A) ↔
      G.IsOpenForest G.freeBoundary (G.setConfig (Prod.fst '' A)) := by
  constructor
  · intro hf e he hconn
    simp only [setConfig, decide_eq_true_eq] at he
    obtain ⟨⟨f, b⟩, hfA, hef⟩ := he
    change f = e at hef
    subst f
    have hfopen : (bundledGraph G).setConfig A (e, b) = true := by
      simp [setConfig, hfA]
    apply hf (e, b) hfopen
    unfold endpointsConnectedWithout at hconn ⊢
    rw [G.withEdge_false_setConfig,
      ← image_fst_diff_singleton_of_atMostOneCopy hA e b hfA,
      ← connectionGraph_bundledGraph] at hconn
    rwa [(bundledGraph G).withEdge_false_setConfig]
  · intro hf ⟨e, b⟩ he hconn
    have heA : (e, b) ∈ A := by simpa [setConfig] using he
    have heopen : G.setConfig (Prod.fst '' A) e = true := by
      simp only [setConfig, decide_eq_true_eq]
      exact ⟨(e, b), heA, rfl⟩
    apply hf e heopen
    unfold endpointsConnectedWithout at hconn ⊢
    rw [(bundledGraph G).withEdge_false_setConfig] at hconn
    rw [G.withEdge_false_setConfig,
      ← image_fst_diff_singleton_of_atMostOneCopy hA e b heA,
      ← connectionGraph_bundledGraph]
    exact hconn

/-- Two distinct parallel labels already form a cycle. -/
lemma bundledGraph_not_indep_of_two_copies {A : Set (G.Edge × Bool)}
    {e : G.Edge} {b c : Bool} (hbc : b ≠ c) (hb : (e, b) ∈ A) (hc : (e, c) ∈ A) :
    ¬ (bundledGraph G).cycleMatroid.Indep A := by
  classical
  letI : DecidableEq (G.Edge × Bool) := Classical.decEq _
  intro hA
  rw [(bundledGraph G).cycleMatroid_indep] at hA
  apply hA (e, b) (by
    simp only [setConfig, decide_eq_true_eq]
    exact hb)
  unfold endpointsConnectedWithout
  apply reachable_of_open (bundledGraph G) _ (e, c)
  rw [withEdge_off]
  · simp only [setConfig, decide_eq_true_eq]
    exact hc
  · intro h
    exact hbc (congrArg Prod.snd h).symm

end FK.Finite.PlaneMatroid.GeneralizedTheta

namespace FK.Finite.PlaneMatroid.GeneralizedTheta

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

/-- Independence in a two-copy thickening of a labelled cycle. -/
theorem bundledGraph_indep_iff (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) (A : Set (G.Edge × Bool)) :
    (bundledGraph G).cycleMatroid.Indep A ↔
      AtMostOneCopy G A ∧ Prod.fst '' A ≠ Set.univ := by
  by_cases hcopy : AtMostOneCopy G A
  · rw [(bundledGraph G).cycleMatroid_indep,
      isOpenForest_bundledGraph_iff hcopy, ← G.cycleMatroid_indep,
      LabelledDualPair.cycle_indep_iff G hG]
    simp [hcopy]
  · constructor
    · intro hi
      have hc : AtMostOneCopy G A := by
        intro e b c hb hc
        by_contra hbc
        exact bundledGraph_not_indep_of_two_copies hbc hb hc hi
      exact (hcopy hc).elim
    · intro h
      exact (hcopy h.1).elim

end FK.Finite.PlaneMatroid.GeneralizedTheta

namespace FK.Finite.PlaneMatroid.GeneralizedTheta

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane

/-- The two-edge-path theta graph bundled with its facial thickening of `G`. -/
abbrev lengthTwoThetaPair (G : LabelledMultigraph) : LabelledDualPair where
  Vertex := Bool ⊕ G.Edge
  Face := G.Vertex
  Edge := G.Edge × Bool
  source e := Sum.inl e.2
  target e := Sum.inr e.1
  dualSource e := G.source e.1
  dualTarget e := G.target e.1

/-- Actual matroid duality for every length-two generalized theta graph over a
connected labelled cycle. -/
theorem lengthTwoTheta_dual_cycleMatroid (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) :
    ((lengthTwoTheta G.Edge).cycleMatroid)✶ = (bundledGraph G).cycleMatroid := by
  letI : Nonempty G.Edge := LabelledDualPair.cycle_nonempty_edge G hG
  apply Matroid.ext_indep (by rfl)
  intro A _
  rw [Matroid.dual_indep_iff_exists (by simp), bundledGraph_indep_iff G hG]
  constructor
  · rintro ⟨B, hB, hdisj⟩
    obtain ⟨full, sel, rfl⟩ := (isBase_iff_spanningTree B).mp hB
    refine ⟨?_, ?_⟩
    · intro e b c hb hc
      by_contra hbc
      have hor : b = sel e ∨ c = sel e := by
        cases b <;> cases c <;> cases hs : sel e <;> simp_all
      rcases hor with rfl | rfl
      · exact (Set.disjoint_left.mp hdisj hb (selected_mem_spanningTree full sel e)).elim
      · exact (Set.disjoint_left.mp hdisj hc (selected_mem_spanningTree full sel e)).elim
    · have hfull : full ∉ Prod.fst '' A := by
        rintro ⟨x, hxA, hx⟩
        have hxpair : x = (full, x.2) := Prod.ext hx rfl
        apply Set.disjoint_left.mp hdisj hxA
        rw [hxpair]
        exact full_mem_spanningTree full sel x.2
      intro heq
      apply hfull
      rw [heq]
      exact Set.mem_univ full
  · rintro ⟨hcopy, hproper⟩
    obtain ⟨full, hfull⟩ := (Set.ne_univ_iff_exists_notMem (Prod.fst '' A)).mp hproper
    let sel : G.Edge → Bool := fun e => if (e, false) ∈ A then true else false
    refine ⟨spanningTree full sel, (isBase_iff_spanningTree _).mpr ⟨full, sel, rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro ⟨e, b⟩ heA heB
    have hefull : e ≠ full := by
      intro he
      subst e
      exact hfull ⟨(full, b), heA, rfl⟩
    change e = full ∨ b = sel e at heB
    have hs : b = sel e := heB.resolve_left hefull
    cases b with
    | false => simp [sel, heA] at hs
    | true =>
        by_cases hf : (e, false) ∈ A
        · have htf := hcopy e true false heA hf
          contradiction
        · simp [sel, hf] at hs

lemma bundledGraph_allOpen_support (G : LabelledMultigraph) :
    Prod.fst '' (Set.univ : Set (G.Edge × Bool)) = Set.univ := by
  ext e
  simp only [Set.mem_image, Set.mem_univ, iff_true]
  exact ⟨(e, false), trivial, rfl⟩

lemma bundledGraph_allOpen_preconnected (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) :
    ((bundledGraph G).connectionGraph (bundledGraph G).freeBoundary
      (bundledGraph G).allOpen).Preconnected := by
  have hg := connectionGraph_bundledGraph (G := G) (A := Set.univ)
  rw [bundledGraph_allOpen_support, (bundledGraph G).setConfig_univ,
    G.setConfig_univ] at hg
  rw [hg]
  exact hG.preconnected

/-- The full bundled plane certificate for every connected labelled cycle.
No arbitrary embedding primitive is postulated for the new primal graph. -/
theorem lengthTwoThetaPair_graphicDualCertificate (G : LabelledMultigraph)
    (hG : G.IsLabelledCycle) :
    (lengthTwoThetaPair G).GraphicDualCertificate := by
  refine ⟨?_, hG.nonemptyVertex, ?_⟩
  · exact lengthTwoTheta_dual_cycleMatroid G hG
  · exact bundledGraph_allOpen_preconnected G hG

end FK.Finite.PlaneMatroid.GeneralizedTheta
