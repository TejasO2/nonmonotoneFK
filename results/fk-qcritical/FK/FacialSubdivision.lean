import FK.PlanarMatroid

/-!
# Facial subdivision and parallel extension

A plane edge subdivision leaves the face set unchanged and replaces the dual
edge by two parallel edges.  This file constructs that operation on arbitrary
finite labelled dual pairs.  Its proof uses the actual connection graphs and
component-form forest criterion, not an input matroid-duality assertion for
the enlarged graph.
-/

namespace FK.Finite.PlaneMatroid

open scoped BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.FinitePlane
open FK.Finite.Conditional

set_option backward.isDefEq.respectTransparency false

namespace LabelledDualPair

variable (P : LabelledDualPair) (e : P.Edge)

/-- Subdivide `e` at the new vertex `none`.  The old label is the first
segment and the new label `none` is the second segment.  On faces, `none` is
parallel to the old facial edge; the face type itself is unchanged. -/
noncomputable def subdivPair : LabelledDualPair where
  Vertex := Option P.Vertex
  Face := P.Face
  Edge := Option P.Edge
  source
    | some a => some (P.source a)
    | none => none
  target
    | some a => if a = e then none else some (P.target a)
    | none => some (P.target e)
  dualSource
    | some a => P.dualSource a
    | none => P.dualSource e
  dualTarget
    | some a => P.dualTarget a
    | none => P.dualTarget e

/-- The old configuration represented by a configuration on the two segments:
the old edge is open exactly when both segments are open. -/
noncomputable def projectConfig (σ : Option P.Edge → Bool) : P.Edge → Bool :=
  fun a => if a = e then σ (some a) && σ none else σ (some a)

/-- The corresponding projection of a set of segment labels. -/
noncomputable def projectSet (B : Set (Option P.Edge)) : Set P.Edge :=
  {a | if a = e then some a ∈ B ∧ none ∈ B else some a ∈ B}

/-- A facial parallel extension uses the complementary projection: the old
label is open exactly when at least one of its two copies is open. -/
noncomputable def parallelConfig (σ : Option P.Edge → Bool) : P.Edge → Bool :=
  fun a => if a = e then σ (some a) || σ none else σ (some a)

/-- The complementary set projection for the facial parallel graph. -/
noncomputable def parallelSet (B : Set (Option P.Edge)) : Set P.Edge :=
  {a | if a = e then some a ∈ B ∨ none ∈ B else some a ∈ B}

lemma decide_mem_projectSet (B : Set (Option P.Edge)) (a : P.Edge) :
    decide (a ∈ projectSet P e B) =
      if a = e then decide (some a ∈ B) && decide (none ∈ B) else decide (some a ∈ B) := by
  by_cases h : a = e
  · subst a
    simp only [ite_true]
    rw [← Bool.decide_and]
    apply Bool.decide_congr
    simp [projectSet]
  · simp only [h, ite_false]
    apply Bool.decide_congr
    simp [projectSet, h]

@[simp] lemma setConfig_projectSet (B : Set (Option P.Edge)) :
    P.primal.setConfig (projectSet P e B) =
      projectConfig P e ((subdivPair P e).primal.setConfig B) := by
  funext a
  exact decide_mem_projectSet P e B a

lemma decide_mem_parallelSet (B : Set (Option P.Edge)) (a : P.Edge) :
    decide (a ∈ parallelSet P e B) =
      if a = e then decide (some a ∈ B) || decide (none ∈ B) else decide (some a ∈ B) := by
  by_cases h : a = e
  · subst a
    simp only [ite_true]
    rw [← Bool.decide_or]
    apply Bool.decide_congr
    simp [parallelSet]
  · simp only [h, ite_false]
    apply Bool.decide_congr
    simp [parallelSet, h]

@[simp] lemma setConfig_parallelSet (B : Set (Option P.Edge)) :
    P.faceDual.setConfig (parallelSet P e B) =
      parallelConfig P e ((subdivPair P e).faceDual.setConfig B) := by
  funext a
  exact decide_mem_parallelSet P e B a

@[simp] lemma mem_projectSet_same (B : Set (Option P.Edge)) :
    e ∈ projectSet P e B ↔ some e ∈ B ∧ none ∈ B := by
  change (if e = e then some e ∈ B ∧ none ∈ B else some e ∈ B) ↔ _
  rw [ite_eq_left rfl]

lemma mem_projectSet_ne (B : Set (Option P.Edge)) {a : P.Edge} (hae : a ≠ e) :
    a ∈ projectSet P e B ↔ some a ∈ B := by
  change (if a = e then some a ∈ B ∧ none ∈ B else some a ∈ B) ↔ _
  rw [ite_eq_right hae]

@[simp] lemma mem_parallelSet_same (B : Set (Option P.Edge)) :
    e ∈ parallelSet P e B ↔ some e ∈ B ∨ none ∈ B := by
  change (if e = e then some e ∈ B ∨ none ∈ B else some e ∈ B) ↔ _
  rw [ite_eq_left rfl]

lemma mem_parallelSet_ne (B : Set (Option P.Edge)) {a : P.Edge} (hae : a ≠ e) :
    a ∈ parallelSet P e B ↔ some a ∈ B := by
  change (if a = e then some a ∈ B ∨ none ∈ B else some a ∈ B) ↔ _
  rw [ite_eq_right hae]

lemma parallelSet_compl (B : Set (Option P.Edge)) :
    parallelSet P e Bᶜ = (projectSet P e B)ᶜ := by
  ext a
  by_cases h : a = e
  · subst a
    by_cases h₁ : some e ∈ B <;> by_cases h₂ : none ∈ B <;>
      simp [parallelSet, projectSet, h₁, h₂]
  · simp [parallelSet, projectSet, h]

lemma parallelSet_eq_compl_projectSet (B : Set (Option P.Edge)) :
    parallelSet P e B = (projectSet P e (Set.univ \ B))ᶜ := by
  have h := parallelSet_compl P e (Set.univ \ B)
  have hc : (Set.univ \ B)ᶜ = B := by ext; simp
  rw [hc] at h
  exact h

lemma openCard_eq_sum {α : Type*} [Fintype α] (σ : α → Bool) :
    openCard σ = ∑ a, (if σ a = true then 1 else 0) := by
  classical
  unfold openCard
  rw [Finset.card_filter]

lemma openCard_projectConfig (σ : Option P.Edge → Bool) :
    openCard σ = openCard (projectConfig P e σ) +
      (if σ (some e) = true ∨ σ none = true then 1 else 0) := by
  classical
  rw [openCard_eq_sum, openCard_eq_sum]
  conv_lhs =>
    rw [Fintype.sum_option]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  conv_rhs =>
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  have hrest :
      (∑ a ∈ Finset.univ.erase e, if σ (some a) = true then 1 else 0) =
        ∑ a ∈ Finset.univ.erase e, if projectConfig P e σ a = true then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    have hae : a ≠ e := (Finset.mem_erase.mp ha).1
    simp [projectConfig, hae]
  rw [hrest]
  cases he : σ (some e) <;> cases hn : σ none <;>
    simp [projectConfig, he, hn] <;> omega

lemma openCard_parallelConfig (σ : Option P.Edge → Bool) :
    openCard σ = openCard (parallelConfig P e σ) +
      (if σ (some e) = true ∧ σ none = true then 1 else 0) := by
  classical
  rw [openCard_eq_sum, openCard_eq_sum]
  conv_lhs =>
    rw [Fintype.sum_option]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  conv_rhs =>
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  have hrest :
      (∑ a ∈ Finset.univ.erase e, if σ (some a) = true then 1 else 0) =
        ∑ a ∈ Finset.univ.erase e, if parallelConfig P e σ a = true then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    have hae : a ≠ e := (Finset.mem_erase.mp ha).1
    simp [parallelConfig, hae]
  rw [hrest]
  cases he : σ (some e) <;> cases hn : σ none <;>
    simp [parallelConfig, he, hn] <;> omega

/-- Opening either copy of an edge gives the same connection graph as opening
its facial parallel copy. -/
lemma faceDual_connectionGraph (σ : Option P.Edge → Bool) :
    (subdivPair P e).faceDual.connectionGraph (subdivPair P e).faceDual.freeBoundary σ =
      P.faceDual.connectionGraph P.faceDual.freeBoundary (parallelConfig P e σ) := by
  ext u v
  constructor
  · rintro ⟨hne, hfree | ⟨x, hx, hjoin⟩⟩
    · exact ⟨hne, Or.inl hfree⟩
    · refine ⟨hne, Or.inr ?_⟩
      cases x with
      | some a =>
          by_cases hae : a = e
          · subst a
            exact ⟨e, by simp [parallelConfig, hx], hjoin⟩
          · exact ⟨a, by simpa [parallelConfig, hae] using hx, hjoin⟩
      | none =>
          exact ⟨e, by simp [parallelConfig, hx], hjoin⟩
  · rintro ⟨hne, hfree | ⟨a, ha, hjoin⟩⟩
    · exact ⟨hne, Or.inl hfree⟩
    · refine ⟨hne, Or.inr ?_⟩
      by_cases he : σ (some a) = true
      · exact ⟨some a, he, hjoin⟩
      · by_cases hae : a = e
        · subst a
          rw [parallelConfig, ite_eq_left rfl] at ha
          have hn : σ none = true := by simpa [he] using ha
          exact ⟨none, hn, hjoin⟩
        · unfold parallelConfig at ha
          rw [ite_eq_right hae] at ha
          exact (he ha).elim

lemma faceDual_componentCount (σ : Option P.Edge → Bool) :
    (subdivPair P e).faceDual.componentCount (subdivPair P e).faceDual.freeBoundary σ =
      P.faceDual.componentCount P.faceDual.freeBoundary (parallelConfig P e σ) := by
  unfold LabelledMultigraph.componentCount
  rw [faceDual_connectionGraph]

lemma faceDual_isOpenForest_iff (σ : Option P.Edge → Bool) :
    (subdivPair P e).faceDual.IsOpenForest (subdivPair P e).faceDual.freeBoundary σ ↔
      ¬ (σ (some e) = true ∧ σ none = true) ∧
        P.faceDual.IsOpenForest P.faceDual.freeBoundary (parallelConfig P e σ) := by
  let H := (subdivPair P e).faceDual
  let G := P.faceDual
  let τ := parallelConfig P e σ
  have hcomp : H.componentCount H.freeBoundary σ = G.componentCount G.freeBoundary τ :=
    faceDual_componentCount P e σ
  have hcard : openCard σ = openCard τ +
      (if σ (some e) = true ∧ σ none = true then 1 else 0) :=
    openCard_parallelConfig P e σ
  constructor
  · intro hσ
    have heq := (H.isOpenForest_iff_componentCount_add_openCard σ).mp hσ
    by_cases hboth : σ (some e) = true ∧ σ none = true
    · rw [hcard] at heq
      simp only [hboth, true_and, ite_true] at heq
      have hle := G.card_vertices_le_componentCount_add_openCard τ
      rw [← hcomp] at hle
      change Fintype.card H.Vertex ≤ H.componentCount H.freeBoundary σ + openCard τ at hle
      omega
    · rw [hcomp, hcard] at heq
      simp only [hboth, ite_false] at heq
      exact ⟨hboth, (G.isOpenForest_iff_componentCount_add_openCard τ).mpr heq⟩
  · rintro ⟨hboth, hτ⟩
    apply (H.isOpenForest_iff_componentCount_add_openCard σ).mpr
    have heq := (G.isOpenForest_iff_componentCount_add_openCard τ).mp hτ
    rw [hcomp, hcard]
    simp only [hboth, ite_false]
    exact heq

/-- Collapse the subdivision vertex to the first endpoint when the first
segment is open, and to the second endpoint otherwise. -/
def collapse (σ : Option P.Edge → Bool) : Option P.Vertex → P.Vertex
  | some u => u
  | none => if σ (some e) = true then P.source e else P.target e

lemma reachable_relMap {V W : Type*} {K : SimpleGraph V} {L : SimpleGraph W}
    (r : V → W) (hstep : ∀ {u v}, K.Adj u v → L.Reachable (r u) (r v))
    {u v : V} (h : K.Reachable u v) : L.Reachable (r u) (r v) := by
  rw [SimpleGraph.reachable_eq_reflTransGen] at h ⊢
  induction h with
  | refl => exact .refl
  | tail hxy hyz ih =>
      exact ih.trans ((SimpleGraph.reachable_iff_reflTransGen ..).mp (hstep hyz))

lemma first_adj (σ : Option P.Edge → Bool) (he : σ (some e) = true) :
    ((subdivPair P e).primal.connectionGraph (subdivPair P e).primal.freeBoundary σ).Adj
      (some (P.source e)) none := by
  refine ⟨by simp, Or.inr ⟨some e, he, ?_⟩⟩
  simp [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins]

lemma second_adj (σ : Option P.Edge → Bool) (hn : σ none = true) :
    ((subdivPair P e).primal.connectionGraph (subdivPair P e).primal.freeBoundary σ).Adj
      none (some (P.target e)) := by
  refine ⟨by simp, Or.inr ⟨none, hn, ?_⟩⟩
  simp [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins]

lemma old_adj (σ : Option P.Edge → Bool) {a : P.Edge} (hae : a ≠ e)
    (ha : σ (some a) = true) {u v : P.Vertex} (hne : u ≠ v)
    (hjoin : P.primal.Joins a u v) :
    ((subdivPair P e).primal.connectionGraph (subdivPair P e).primal.freeBoundary σ).Adj
      (some u) (some v) := by
  refine ⟨fun h => hne (Option.some.inj h), Or.inr ⟨some a, ha, ?_⟩⟩
  simpa [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins, hae] using hjoin

lemma reachable_old_edge (σ : Option P.Edge → Bool)
    (he : σ (some e) = true) (hn : σ none = true) :
    (P.primal.connectionGraph P.primal.freeBoundary (projectConfig P e σ)).Reachable
      (P.source e) (P.target e) := by
  by_cases hst : P.source e = P.target e
  · rw [← hst]
  · apply SimpleGraph.Adj.reachable
    exact ⟨hst, Or.inr ⟨e, by simp [projectConfig, he, hn], Or.inl ⟨rfl, rfl⟩⟩⟩

/-- Reachability of old vertices in the projected graph lifts to the
subdivision graph. -/
lemma reachable_some_of_projected (σ : Option P.Edge → Bool) {u v : P.Vertex}
    (h : (P.primal.connectionGraph P.primal.freeBoundary (projectConfig P e σ)).Reachable u v) :
    ((subdivPair P e).primal.connectionGraph (subdivPair P e).primal.freeBoundary σ).Reachable
      (some u) (some v) := by
  apply reachable_relMap (fun u => some u) ?_ h
  intro x y hxy
  rcases hxy.2 with hfree | ⟨a, ha, hjoin⟩
  · exact (hxy.1 hfree).elim
  · by_cases hae : a = e
    · subst a
      have hboth : σ (some e) = true ∧ σ none = true := by
        have hopen : σ (some e) && σ none = true := by
          rw [projectConfig, ite_eq_left rfl] at ha
          exact ha
        exact Bool.and_eq_true_iff.mp hopen
      rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (first_adj P e σ hboth.1).reachable.trans
          (second_adj P e σ hboth.2).reachable
      · exact (second_adj P e σ hboth.2).symm.reachable.trans
          (first_adj P e σ hboth.1).symm.reachable
    · have ha' : σ (some a) = true := by
        unfold projectConfig at ha
        rw [ite_eq_right hae] at ha
        exact ha
      exact (old_adj P e σ hae ha' hxy.1 hjoin).reachable

lemma reachable_collapse_step (σ : Option P.Edge → Bool) {u v : Option P.Vertex}
    (hxy : ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).Adj u v) :
    (P.primal.connectionGraph P.primal.freeBoundary (projectConfig P e σ)).Reachable
      (collapse P e σ u) (collapse P e σ v) := by
  rcases hxy.2 with hfree | ⟨x, hx, hjoin⟩
  · exact (hxy.1 hfree).elim
  · cases x with
    | some a =>
        by_cases hae : a = e
        · subst a
          have hjoin' :
              (some (P.source e) = u ∧ none = v) ∨
                (some (P.source e) = v ∧ none = u) := by
            simpa [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins] using hjoin
          rcases hjoin' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [collapse, hx]
        · have hjoin' :
              (some (P.source a) = u ∧ some (P.target a) = v) ∨
                (some (P.source a) = v ∧ some (P.target a) = u) := by
            simpa [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins, hae] using hjoin
          have ha : projectConfig P e σ a = true := by
            simp [projectConfig, hae, hx]
          rcases hjoin' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · apply SimpleGraph.Adj.reachable
            exact ⟨fun h => hxy.1 (congrArg some h), Or.inr ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩⟩
          · apply SimpleGraph.Adj.reachable
            exact ⟨fun h => hxy.1 (congrArg some h), Or.inr ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩⟩
    | none =>
        have hjoin' :
            (none = u ∧ some (P.target e) = v) ∨
              (none = v ∧ some (P.target e) = u) := by
          simpa [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins] using hjoin
        rcases hjoin' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · by_cases he : σ (some e) = true
          · simpa [collapse, he] using reachable_old_edge P e σ he hx
          · simp [collapse, he]
        · by_cases he : σ (some e) = true
          · simpa [collapse, he] using (reachable_old_edge P e σ he hx).symm
          · simp [collapse, he]

lemma reachable_collapse (σ : Option P.Edge → Bool) {u v : Option P.Vertex}
    (h : ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).Reachable u v) :
    (P.primal.connectionGraph P.primal.freeBoundary (projectConfig P e σ)).Reachable
      (collapse P e σ u) (collapse P e σ v) := by
  exact reachable_relMap (collapse P e σ) (fun hxy => reachable_collapse_step P e σ hxy) h

lemma reachable_none_collapse (σ : Option P.Edge → Bool)
    (hopen : σ (some e) = true ∨ σ none = true) :
    ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).Reachable none (some (collapse P e σ none)) := by
  by_cases he : σ (some e) = true
  · simpa [collapse, he] using (first_adj P e σ he).symm.reachable
  · have hn : σ none = true := hopen.resolve_left he
    simpa [collapse, he] using (second_adj P e σ hn).reachable

/-- The connected components of a nontrivially open subdivision are exactly
those of the projected graph. -/
noncomputable def componentsEquivOfOpen (σ : Option P.Edge → Bool)
    (hopen : σ (some e) = true ∨ σ none = true) :
    ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).ConnectedComponent ≃
    (P.primal.connectionGraph P.primal.freeBoundary (projectConfig P e σ)).ConnectedComponent := by
  let f := Quot.map (collapse P e σ) (fun _ _ h => reachable_collapse P e σ h)
  let g := Quot.map (fun u : P.Vertex => some u)
    (fun _ _ h => reachable_some_of_projected P e σ h)
  refine ⟨f, g, ?_, ?_⟩
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x =>
        cases x with
        | some u => rfl
        | none =>
            apply SimpleGraph.ConnectedComponent.sound
            exact (reachable_none_collapse P e σ hopen).symm
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h u => rfl

lemma no_adj_none_of_closed (σ : Option P.Edge → Bool)
    (he : σ (some e) = false) (hn : σ none = false) {v : Option P.Vertex} :
    ¬ ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).Adj none v := by
  intro hadj
  rcases hadj.2 with hfree | ⟨x, hx, hjoin⟩
  · exact hadj.1 hfree
  · cases x with
    | some a =>
        by_cases hae : a = e
        · subst a
          simp [he] at hx
        · simp [subdivPair, LabelledDualPair.primal, LabelledMultigraph.Joins, hae] at hjoin
    | none => simp [hn] at hx

lemma eq_none_of_reachable_none (σ : Option P.Edge → Bool)
    (he : σ (some e) = false) (hn : σ none = false) {x : Option P.Vertex}
    (h : ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).Reachable none x) : x = none := by
  rcases h with ⟨p⟩
  cases p with
  | nil => rfl
  | cons hadj p => exact (no_adj_none_of_closed P e σ he hn hadj).elim

/-- With both segments closed, the subdivision vertex is one additional
isolated component. -/
noncomputable def componentsEquivOfClosed (σ : Option P.Edge → Bool)
    (he : σ (some e) = false) (hn : σ none = false) :
    ((subdivPair P e).primal.connectionGraph
      (subdivPair P e).primal.freeBoundary σ).ConnectedComponent ≃
    Option (P.primal.connectionGraph
      P.primal.freeBoundary (projectConfig P e σ)).ConnectedComponent := by
  let f := Quot.lift
    (fun x : Option P.Vertex => match x with
      | some u => some ((P.primal.connectionGraph P.primal.freeBoundary
          (projectConfig P e σ)).connectedComponentMk u)
      | none => none)
    (by
      intro x y hxy
      cases x with
      | some u =>
          cases y with
          | some v =>
              exact congrArg some (SimpleGraph.ConnectedComponent.sound
                (reachable_collapse P e σ hxy))
          | none =>
              have hfalse := eq_none_of_reachable_none P e σ he hn hxy.symm
              contradiction
      | none =>
          have hy : y = none := eq_none_of_reachable_none P e σ he hn hxy
          subst y
          rfl)
  let g₀ := Quot.map (fun u : P.Vertex => some u)
    (fun _ _ h => reachable_some_of_projected P e σ h)
  let g : Option (P.primal.connectionGraph P.primal.freeBoundary
      (projectConfig P e σ)).ConnectedComponent →
      ((subdivPair P e).primal.connectionGraph
        (subdivPair P e).primal.freeBoundary σ).ConnectedComponent
    | none => ((subdivPair P e).primal.connectionGraph
        (subdivPair P e).primal.freeBoundary σ).connectedComponentMk none
    | some C => g₀ C
  refine ⟨f, g, ?_, ?_⟩
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h x => cases x <;> rfl
  · intro C
    cases C with
    | none => rfl
    | some C =>
        induction C using SimpleGraph.ConnectedComponent.ind with
        | h u => rfl

lemma primal_componentCount (σ : Option P.Edge → Bool) :
    (subdivPair P e).primal.componentCount (subdivPair P e).primal.freeBoundary σ =
      P.primal.componentCount P.primal.freeBoundary (projectConfig P e σ) +
        (if σ (some e) = false ∧ σ none = false then 1 else 0) := by
  unfold LabelledMultigraph.componentCount
  by_cases he : σ (some e) = true
  · have hc := Nat.card_congr (componentsEquivOfOpen P e σ (Or.inl he))
    rw [show (if σ (some e) = false ∧ σ none = false then 1 else 0) = 0 by simp [he],
      Nat.add_zero]
    exact hc
  · have hefalse : σ (some e) = false := by cases h : σ (some e) <;> simp_all
    by_cases hn : σ none = true
    · have hc := Nat.card_congr (componentsEquivOfOpen P e σ (Or.inr hn))
      rw [show (if σ (some e) = false ∧ σ none = false then 1 else 0) = 0 by simp [he, hn],
        Nat.add_zero]
      exact hc
    · have hnfalse : σ none = false := by cases h : σ none <;> simp_all
      have hc := Nat.card_congr (componentsEquivOfClosed P e σ hefalse hnfalse)
      rw [show (if σ (some e) = false ∧ σ none = false then 1 else 0) = 1 by simp [he, hn]]
      exact hc.trans Finite.card_option

lemma primal_isOpenForest_iff (σ : Option P.Edge → Bool) :
    (subdivPair P e).primal.IsOpenForest (subdivPair P e).primal.freeBoundary σ ↔
      P.primal.IsOpenForest P.primal.freeBoundary (projectConfig P e σ) := by
  let H := (subdivPair P e).primal
  let G := P.primal
  let τ := projectConfig P e σ
  have hcomp : H.componentCount H.freeBoundary σ = G.componentCount G.freeBoundary τ +
      (if σ (some e) = false ∧ σ none = false then 1 else 0) := primal_componentCount P e σ
  have hcard : openCard σ = openCard τ +
      (if σ (some e) = true ∨ σ none = true then 1 else 0) := openCard_projectConfig P e σ
  rw [H.isOpenForest_iff_componentCount_add_openCard,
    G.isOpenForest_iff_componentCount_add_openCard, hcomp, hcard]
  have hv : Fintype.card H.Vertex = Fintype.card G.Vertex + 1 := by
    dsimp only [H, G]
    exact Fintype.card_option
  rw [hv]
  dsimp only [τ]
  cases he : σ (some e) <;> cases hn : σ none <;> simp [he, hn] <;> omega

lemma primal_indep_iff (B : Set (Option P.Edge)) :
    (subdivPair P e).primal.cycleMatroid.Indep B ↔
      P.primal.cycleMatroid.Indep (projectSet P e B) := by
  rw [LabelledMultigraph.cycleMatroid_indep, LabelledMultigraph.cycleMatroid_indep]
  have h := primal_isOpenForest_iff P e ((subdivPair P e).primal.setConfig B)
  rw [← setConfig_projectSet P e B] at h
  exact h

lemma faceDual_indep_iff (B : Set (Option P.Edge)) :
    (subdivPair P e).faceDual.cycleMatroid.Indep B ↔
      ¬ (some e ∈ B ∧ none ∈ B) ∧
        P.faceDual.cycleMatroid.Indep (parallelSet P e B) := by
  rw [LabelledMultigraph.cycleMatroid_indep, LabelledMultigraph.cycleMatroid_indep]
  have h := faceDual_isOpenForest_iff P e ((subdivPair P e).faceDual.setConfig B)
  rw [← setConfig_parallelSet P e B] at h
  simpa [LabelledMultigraph.setConfig] using h

lemma projectSet_insert_none (B : Set (Option P.Edge))
    (he : some e ∈ B) (hn : none ∉ B) :
    projectSet P e (insert none B) = insert e (projectSet P e B) := by
  ext a
  by_cases hae : a = e <;> by_cases h : some a ∈ B <;> simp_all [projectSet]

lemma projectSet_insert_none_of_notMem (B : Set (Option P.Edge)) (he : some e ∉ B) :
    projectSet P e (insert none B) = projectSet P e B := by
  ext a
  by_cases hae : a = e <;> by_cases hn : none ∈ B <;> simp_all [projectSet]

lemma projectSet_insert_some (B : Set (Option P.Edge)) (a : P.Edge)
    (ha : some a ∉ B) (hstatus : a = e → none ∈ B) :
    projectSet P e (insert (some a) B) = insert a (projectSet P e B) := by
  ext b
  by_cases hba : b = a <;> by_cases hbe : b = e <;> by_cases hn : none ∈ B <;>
    by_cases hae : a = e <;> simp_all [projectSet]

lemma parallelSet_insert_none (B : Set (Option P.Edge)) :
    parallelSet P e (insert none B) = insert e (parallelSet P e B) := by
  ext a
  by_cases hae : a = e <;> by_cases he : some e ∈ B <;> by_cases hn : none ∈ B <;>
    simp_all [parallelSet]

lemma parallelSet_insert_some (B : Set (Option P.Edge)) (a : P.Edge) :
    parallelSet P e (insert (some a) B) = insert a (parallelSet P e B) := by
  ext b
  by_cases hba : b = a <;> by_cases hbe : b = e <;> by_cases hn : none ∈ B <;>
    by_cases ha : some a ∈ B <;> simp_all [parallelSet]

lemma primal_isBase_iff (B : Set (Option P.Edge)) :
    (subdivPair P e).primal.cycleMatroid.IsBase B ↔
      P.primal.cycleMatroid.IsBase (projectSet P e B) ∧
        (some e ∈ B ∨ none ∈ B) := by
  let N := (subdivPair P e).primal.cycleMatroid
  let M := P.primal.cycleMatroid
  let C := projectSet P e B
  have hI (B' : Set (Option P.Edge)) :
      N.Indep B' ↔ M.Indep (projectSet P e B') := primal_indep_iff P e B'
  constructor
  · intro hB
    have hC : M.Indep C := (hI B).mp hB.indep
    have hstatus : some e ∈ B ∨ none ∈ B := by
      by_contra hn
      push Not at hn
      have hdep := hB.insert_dep (show none ∈ N.E \ B by simp [N, hn.2])
      apply hdep.not_indep
      apply (hI _).mpr
      rw [projectSet_insert_none_of_notMem P e B hn.1]
      exact hC
    refine ⟨?_, hstatus⟩
    apply hC.isBase_of_forall_insert
    intro a ha
    have haC : a ∉ C := ha.2
    intro hIns
    by_cases hae : a = e
    · subst a
      have hne : ¬ (some e ∈ B ∧ none ∈ B) := by
        intro hboth
        apply haC
        exact (mem_projectSet_same P e B).mpr hboth
      by_cases he : some e ∈ B
      · have hn : none ∉ B := fun hn => hne ⟨he, hn⟩
        have hdep := hB.insert_dep (show none ∈ N.E \ B by simp [N, hn])
        apply hdep.not_indep
        apply (hI _).mpr
        rw [projectSet_insert_none P e B he hn]
        exact hIns
      · have hn : none ∈ B := hstatus.resolve_left he
        have hdep := hB.insert_dep (show some e ∈ N.E \ B by simp [N, he])
        apply hdep.not_indep
        apply (hI _).mpr
        rw [projectSet_insert_some P e B e he (fun _ => hn)]
        exact hIns
    · have haB : some a ∉ B := by
        intro haB
        apply haC
        exact (mem_projectSet_ne P e B hae).mpr haB
      have hdep := hB.insert_dep (show some a ∈ N.E \ B by simp [N, haB])
      apply hdep.not_indep
      apply (hI _).mpr
      rw [projectSet_insert_some P e B a haB (fun h => (hae h).elim)]
      exact hIns
  · rintro ⟨hC, hstatus⟩
    apply ((hI B).mpr hC.indep).isBase_of_forall_insert
    intro x hx
    cases x with
    | some a =>
        have ha : some a ∉ B := hx.2
        have hs : a = e → none ∈ B := by
          intro hae
          subst a
          exact hstatus.resolve_left ha
        have haC : a ∉ C := by
          intro haC
          by_cases hae : a = e
          · subst a
            have hboth : some e ∈ B ∧ none ∈ B :=
              (mem_projectSet_same P e B).mp haC
            exact ha hboth.1
          · apply ha
            exact (mem_projectSet_ne P e B hae).mp haC
        intro hNi
        have hCi := (hI _).mp hNi
        rw [projectSet_insert_some P e B a ha hs] at hCi
        exact (hC.insert_dep (show a ∈ M.E \ C by simp [M, haC])).not_indep hCi
    | none =>
        have hn : none ∉ B := hx.2
        have he : some e ∈ B := hstatus.resolve_right hn
        have heC : e ∉ C := by
          intro heC
          exact hn ((mem_projectSet_same P e B).mp heC).2
        intro hNi
        have hCi := (hI _).mp hNi
        rw [projectSet_insert_none P e B he hn] at hCi
        exact (hC.insert_dep (show e ∈ M.E \ C by simp [M, heC])).not_indep hCi

lemma faceDual_isBase_iff (B : Set (Option P.Edge)) :
    (subdivPair P e).faceDual.cycleMatroid.IsBase B ↔
      ¬ (some e ∈ B ∧ none ∈ B) ∧
        P.faceDual.cycleMatroid.IsBase (parallelSet P e B) := by
  let Q := (subdivPair P e).faceDual.cycleMatroid
  let D := P.faceDual.cycleMatroid
  let C := parallelSet P e B
  have hI (B' : Set (Option P.Edge)) : Q.Indep B' ↔
      ¬ (some e ∈ B' ∧ none ∈ B') ∧ D.Indep (parallelSet P e B') :=
    faceDual_indep_iff P e B'
  constructor
  · intro hB
    have hi := (hI B).mp hB.indep
    refine ⟨hi.1, ?_⟩
    apply hi.2.isBase_of_forall_insert
    intro a ha
    have haC : a ∉ C := ha.2
    intro hIns
    by_cases hae : a = e
    · subst a
      have he : some e ∉ B := by
        intro he
        exact haC ((mem_parallelSet_same P e B).mpr (Or.inl he))
      have hn : none ∉ B := by
        intro hn
        exact haC ((mem_parallelSet_same P e B).mpr (Or.inr hn))
      have hdep := hB.insert_dep (show none ∈ Q.E \ B by simp [Q, hn])
      apply hdep.not_indep
      apply (hI _).mpr
      refine ⟨by simp [he], ?_⟩
      rw [parallelSet_insert_none]
      exact hIns
    · have haB : some a ∉ B := by
        intro haB
        exact haC ((mem_parallelSet_ne P e B hae).mpr haB)
      have hdep := hB.insert_dep (show some a ∈ Q.E \ B by simp [Q, haB])
      apply hdep.not_indep
      apply (hI _).mpr
      refine ⟨?_, ?_⟩
      · rintro ⟨he, hn⟩
        apply hi.1
        constructor
        · rcases Set.mem_insert_iff.mp he with heq | heB
          · exact (hae (Option.some.inj heq).symm).elim
          · exact heB
        · rcases Set.mem_insert_iff.mp hn with hnq | hnB
          · cases hnq
          · exact hnB
      · rw [parallelSet_insert_some]
        exact hIns
  · rintro ⟨hnot, hC⟩
    apply ((hI B).mpr ⟨hnot, hC.indep⟩).isBase_of_forall_insert
    intro x hx
    cases x with
    | some a =>
        have ha : some a ∉ B := hx.2
        intro hQi
        have hi := (hI _).mp hQi
        by_cases hae : a = e
        · subst a
          by_cases hn : none ∈ B
          · exact hi.1 ⟨by simp, by simp [hn]⟩
          · have heC : e ∉ C := by
              intro heC
              rcases (mem_parallelSet_same P e B).mp heC with he | hn'
              · exact ha he
              · exact hn hn'
            rw [parallelSet_insert_some] at hi
            exact (hC.insert_dep (show e ∈ D.E \ C by simp [D, heC])).not_indep hi.2
        · have haC : a ∉ C := by
            intro haC
            exact ha ((mem_parallelSet_ne P e B hae).mp haC)
          rw [parallelSet_insert_some] at hi
          exact (hC.insert_dep (show a ∈ D.E \ C by simp [D, haC])).not_indep hi.2
    | none =>
        have hn : none ∉ B := hx.2
        intro hQi
        have hi := (hI _).mp hQi
        by_cases he : some e ∈ B
        · exact hi.1 ⟨by simp [he], by simp⟩
        · have heC : e ∉ C := by
            intro heC
            rcases (mem_parallelSet_same P e B).mp heC with he' | hn'
            · exact he he'
            · exact hn hn'
          rw [parallelSet_insert_none] at hi
          exact (hC.insert_dep (show e ∈ D.E \ C by simp [D, heC])).not_indep hi.2

theorem dual_cycleMatroid_subdivPair (hP : P.GraphicDualCertificate) :
    ((subdivPair P e).primal.cycleMatroid)✶ = (subdivPair P e).faceDual.cycleMatroid := by
  apply Matroid.ext_isBase (by rfl)
  intro B hB
  rw [Matroid.dual_isBase_iff]
  change (subdivPair P e).primal.cycleMatroid.IsBase (Set.univ \ B) ↔
    (subdivPair P e).faceDual.cycleMatroid.IsBase B
  rw [primal_isBase_iff, faceDual_isBase_iff, ← hP.dual_cycleMatroid,
    Matroid.dual_isBase_iff]
  rw [parallelSet_eq_compl_projectSet]
  have hcompl : Set.univ \ (projectSet P e (Set.univ \ B))ᶜ =
      projectSet P e (Set.univ \ B) := by
    ext a
    simp
  rw [LabelledMultigraph.cycleMatroid_ground, hcompl]
  by_cases he : some e ∈ B <;> by_cases hn : none ∈ B <;> simp_all

/-- Plane edge subdivision preserves an actual graphic-duality certificate.
The facial graph visibly has the original faces and a parallel copy of the
subdivided edge; no new matroid-duality premise is introduced. -/
theorem graphicDualCertificate_subdivPair (hP : P.GraphicDualCertificate) :
    (subdivPair P e).GraphicDualCertificate where
  dual_cycleMatroid := dual_cycleMatroid_subdivPair P e hP
  nonemptyFace := hP.nonemptyFace
  allOpen_preconnected := by
    have hconfig : parallelConfig P e ((subdivPair P e).faceDual.allOpen) =
        P.faceDual.allOpen := by
      funext a
      by_cases hae : a = e <;> simp [parallelConfig, hae, LabelledMultigraph.allOpen]
    rw [faceDual_connectionGraph, hconfig]
    exact hP.allOpen_preconnected


end LabelledDualPair
end FK.Finite.PlaneMatroid
