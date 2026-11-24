import FK.AGTree.Reduced

/-!
# The two-class tree
-/

namespace Ultra

/-- Vertices of the tree: reduced words. -/
structure V where
  w : List A
  red : Reduced w

namespace V

lemma ext {v w : V} (h : v.w = w.w) : v = w := by cases v; cases w; simp_all

lemma ext_iff {v w : V} : v = w ↔ v.w = w.w := ⟨fun h => by rw [h], ext⟩

instance : DecidableEq V := fun v w =>
  decidable_of_iff (v.w = w.w) ⟨ext, fun h => by rw [h]⟩

/-- The empty vertex. -/
def root : V := ⟨[], reduced_nil⟩

/-- Append a letter (which must not repeat the last one). -/
def snoc (v : V) (a : A) (h : v.w = [] ∨ v.w.getLast? ≠ some a) : V :=
  ⟨v.w ++ [a], Reduced.snoc_of_ne v.red h⟩

@[simp] lemma snoc_w (v : V) (a : A) (h : _) : (snoc v a h).w = v.w ++ [a] := rfl

@[simp] lemma snoc_length (v : V) (a : A) (h : _) : (snoc v a h).w.length = v.w.length + 1 := by
  simp

lemma getLast?_snoc (v : V) (a : A) (h : _) : (snoc v a h).w.getLast? = some a := by
  simp

/-- `a` may be appended to `v`. -/
abbrev Valid (v : V) (a : A) : Prop := v.w = [] ∨ v.w.getLast? ≠ some a

instance (v : V) (a : A) : Decidable (v.Valid a) := by unfold Valid; infer_instance

lemma valid_of_append {v : V} {a : A} (h : Reduced (v.w ++ [a])) : v.Valid a := by
  rw [Valid]
  rcases Nat.eq_zero_or_pos v.w.length with h0 | hpos
  · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
  · exact Or.inr (Reduced.getLast?_ne h (List.ne_nil_of_length_pos hpos))

/-- The parent of a nonempty vertex. -/
def parent (v : V) (h : v.w ≠ []) : V :=
  ⟨v.w.dropLast, by
    have hv : v.w = v.w.dropLast ++ [v.w.getLast h] := (List.dropLast_append_getLast h).symm
    exact Reduced.of_snoc (l := v.w.dropLast) (a := v.w.getLast h) (by rw [← hv]; exact v.red)⟩

@[simp] lemma parent_w (v : V) (h : v.w ≠ []) : (parent v h).w = v.w.dropLast := rfl

end V

open V

/-- The two-class tree. -/
def G : SimpleGraph V where
  Adj v w := ∃ a : A, w.w = v.w ++ [a] ∨ v.w = w.w ++ [a]
  symm := ⟨fun v w h => by rcases h with ⟨a, h | h⟩; exacts [⟨a, Or.inr h⟩, ⟨a, Or.inl h⟩]⟩
  loopless := ⟨fun v h => by
    rcases h with ⟨a, h | h⟩ <;> (have := congrArg List.length h; simp at this)⟩

lemma adj_snoc {v : V} {a : A} (h : v.Valid a) : G.Adj v (v.snoc a h) :=
  ⟨a, Or.inl rfl⟩

lemma adj_parent {v : V} (h : v.w ≠ []) : G.Adj v (v.parent h) :=
  ⟨v.w.getLast h, Or.inr (List.dropLast_append_getLast h).symm⟩

/-- Every edge is either a step down to an appended letter or a step up to the parent. -/
lemma adj_iff {v w : V} :
    G.Adj v w ↔ (∃ (a : A) (h : v.Valid a), w = v.snoc a h) ∨
      (∃ (h : v.w ≠ []), w = v.parent h) := by
  constructor
  · rintro ⟨a, h | h⟩
    · have hred : Reduced (v.w ++ [a]) := by rw [← h]; exact w.red
      refine Or.inl ⟨a, valid_of_append hred, V.ext ?_⟩
      rw [V.snoc_w]; exact h
    · have hv : v.w ≠ [] := by rintro h0; rw [h0] at h; simp at h
      refine Or.inr ⟨hv, V.ext ?_⟩
      rw [V.parent_w, h, List.dropLast_concat]
  · rintro (⟨a, hv, rfl⟩ | ⟨h, rfl⟩)
    · exact adj_snoc hv
    · exact adj_parent h

/-- The tree is locally finite. -/
noncomputable instance : G.LocallyFinite := by
  intro v
  set S : Finset V :=
    ((Finset.univ : Finset A).biUnion (fun a =>
      (if h : v.Valid a then ({v.snoc a h} : Finset V) else ∅))) ∪
    (if h : v.w = [] then (∅ : Finset V) else {v.parent h}) with hS
  have hsub : G.neighborSet v ⊆ (S : Set V) := by
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    rcases (adj_iff (v := v) (w := w)).1 hw with ⟨a, hv, rfl⟩ | ⟨h, rfl⟩
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, ?_⟩)
      simp only [dif_pos hv, Finset.mem_singleton]
    · refine Finset.mem_union_right _ ?_
      rw [dif_neg h]
      simp
  exact (Set.Finite.subset (Finset.finite_toSet S) hsub).fintype

/-- Every vertex reaches the root by dropping letters. -/
theorem reachable_root (v : V) : G.Reachable v V.root := by
  rcases v with ⟨l, hl⟩
  revert hl
  induction l using List.reverseRecOn with
  | nil => intro hl; exact SimpleGraph.Reachable.refl _
  | append_singleton t a ih =>
    intro hl
    have ht : Reduced t := Reduced.of_snoc hl
    have hne : (t ++ [a]) ≠ [] := by simp
    have hpar : (⟨t ++ [a], hl⟩ : V).parent hne = (⟨t, ht⟩ : V) := by
      apply V.ext
      simp [V.parent_w, List.dropLast_concat]
    exact (SimpleGraph.Adj.reachable (adj_parent hne)).trans (by rw [hpar]; exact ih ht)

/-- The tree is connected. -/
theorem G_preconnected : G.Preconnected := fun v w =>
  (reachable_root v).trans (reachable_root w).symm

theorem G_connected : G.Connected :=
  (SimpleGraph.connected_iff G).2 ⟨G_preconnected, ⟨V.root⟩⟩

/-- Bounded degree: every vertex has at most six neighbours (in fact five). -/
theorem bounded_degree : ∃ K : ℕ, ∀ v : V, ∃ S : Finset V, S.card ≤ K ∧ G.neighborSet v ⊆ (S : Set V) := by
  refine ⟨6, fun v => ?_⟩
  let f : A → V := fun a => dite (v.Valid a) (fun h => v.snoc a h) (fun _ => v)
  let T : Finset V := (Finset.univ : Finset A).image f ∪
      (if h : v.w = [] then (∅ : Finset V) else {v.parent h})
  have hT : G.neighborSet v ⊆ (T : Set V) := by
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    rcases (adj_iff (v := v) (w := w)).1 hw with ⟨a, hv, rfl⟩ | ⟨h, rfl⟩
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ?_⟩)
      simp only [f, dif_pos hv]
    · refine Finset.mem_union_right _ ?_
      rw [dif_neg h]; simp
  have hcard : T.card ≤ 6 := by
    have h1 : ((Finset.univ : Finset A).image f).card ≤ 5 := by
      refine le_trans Finset.card_image_le ?_
      simp
    have h2 : (if h : v.w = [] then (∅ : Finset V) else {v.parent h}).card ≤ 1 := by
      split_ifs with h <;> simp
    calc T.card ≤ ((Finset.univ : Finset A).image f).card +
        (if h : v.w = [] then (∅ : Finset V) else {v.parent h}).card := Finset.card_union_le _ _
      _ ≤ 5 + 1 := by omega
  exact ⟨T, hcard, hT⟩

end Ultra
