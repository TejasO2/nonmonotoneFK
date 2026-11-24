import FK.AGTree.Edges

/-!
# Automorphisms of the two-class reduced-word tree

The vertices of `Ultra.G` are reduced words over the five-letter alphabet
`A = Sum (Fin 3) (Fin 2)`; adjacency appends one letter.  In group language
this is the Cayley graph of the free product of five copies of `Z/2` acting on
itself, so left multiplication by a generator is a graph automorphism.

This file constructs those automorphisms at the word level (with the explicit
cancellation rule `lpre`), proves that they are genuine `SimpleGraph.Iso`s of
`Ultra.G`, and derives vertex transitivity.
-/

namespace Ultra

open V

/-! ### Prepending a letter with cancellation -/

/-- Prepend the letter `a` to a word, cancelling a leading `a`.  Since every
letter is an involution this is left multiplication by `a` on reduced words. -/
def lpre (a : A) : List A → List A
  | [] => [a]
  | b :: t => if b = a then t else a :: b :: t

@[simp] lemma lpre_nil (a : A) : lpre a [] = [a] := rfl

lemma lpre_cons (a b : A) (t : List A) :
    lpre a (b :: t) = if b = a then t else a :: b :: t := rfl

lemma lpre_cons_self (a : A) (t : List A) : lpre a (a :: t) = t := by
  rw [lpre_cons, if_pos rfl]

lemma lpre_cons_of_ne {a b : A} (h : b ≠ a) (t : List A) :
    lpre a (b :: t) = a :: b :: t := by
  rw [lpre_cons, if_neg h]

/-- Prepending preserves reducedness. -/
lemma lpre_reduced {a : A} : ∀ {l : List A}, Reduced l → Reduced (lpre a l)
  | [], _ => reduced_singleton a
  | b :: t, h => by
    by_cases hb : b = a
    · rw [hb] at h ⊢
      rw [lpre_cons_self]
      cases t with
      | nil => exact reduced_nil
      | cons c u => exact h.2
    · rw [lpre_cons_of_ne hb]
      exact ⟨Ne.symm hb, h⟩

/-- Prepending twice is the identity on reduced words. -/
lemma lpre_lpre {a : A} : ∀ {l : List A}, Reduced l → lpre a (lpre a l) = l
  | [], _ => by rw [lpre_nil, lpre_cons_self]
  | b :: t, h => by
    by_cases hb : b = a
    · rw [hb, lpre_cons_self]
      cases t with
      | nil => rw [lpre_nil]
      | cons c u =>
        exact lpre_cons_of_ne (a := a) (b := c) (fun hca => h.1 (by rw [hb, hca])) u
    · rw [lpre_cons_of_ne hb, lpre_cons_self]

/-- Prepending commutes with appending a letter, as long as the word is
nonempty.  (At the empty word the `a`-edge is reversed by the cancellation.) -/
lemma lpre_append_singleton {a c : A} :
    ∀ {l : List A}, l ≠ [] → lpre a (l ++ [c]) = lpre a l ++ [c]
  | [], h => absurd rfl h
  | b :: t, _ => by
    by_cases hb : b = a
    · rw [hb, List.cons_append, lpre_cons_self, lpre_cons_self]
    · rw [List.cons_append, lpre_cons_of_ne hb, lpre_cons_of_ne hb]
      rfl

/-! ### Adjacency constructors -/

lemma adj_of_snoc {v w : V} {c : A} (h : w.w = v.w ++ [c]) : G.Adj v w := ⟨c, Or.inl h⟩

lemma adj_of_parent {v w : V} {c : A} (h : v.w = w.w ++ [c]) : G.Adj v w := ⟨c, Or.inr h⟩

/-! ### Left multiplication on vertices -/

/-- Left multiplication by a letter, as an operation on the tree. -/
def lmul (a : A) (v : V) : V := ⟨lpre a v.w, lpre_reduced v.red⟩

@[simp] lemma lmul_w (a : A) (v : V) : (lmul a v).w = lpre a v.w := rfl

/-- Every letter acts involutively. -/
lemma lmul_involutive (a : A) (v : V) : lmul a (lmul a v) = v := by
  apply V.ext
  simp only [lmul_w]
  exact lpre_lpre v.red

lemma lmul_injective (a : A) : Function.Injective (lmul a) :=
  Function.LeftInverse.injective (g := lmul a) (lmul_involutive a)

lemma lmul_surjective (a : A) : Function.Surjective (lmul a) :=
  Function.RightInverse.surjective (g := lmul a) (lmul_involutive a)

/-- Left multiplication by one letter maps adjacent vertices to adjacent
vertices. -/
lemma lmul_adj (a : A) {v w : V} (h : G.Adj v w) : G.Adj (lmul a v) (lmul a w) := by
  rcases h with ⟨c, hc | hc⟩
  · rcases eq_or_ne v.w [] with hv | hv
    · -- `v` is the root: cancellation may reverse the edge
      have hw : w.w = [c] := by rw [hc, hv, List.nil_append]
      have h1 : lpre a v.w = [a] := by rw [hv]; rfl
      have h2 : lpre a w.w = if c = a then [] else [a, c] := by rw [hw, lpre_cons]
      by_cases hca : c = a
      · rw [if_pos hca] at h2
        exact adj_of_parent (c := a) (by rw [lmul_w, lmul_w, h1, h2]; rfl)
      · rw [if_neg hca] at h2
        exact adj_of_snoc (c := c) (by rw [lmul_w, lmul_w, h1, h2]; rfl)
    · exact adj_of_snoc (c := c) (by rw [lmul_w, lmul_w, hc, lpre_append_singleton hv])
  · rcases eq_or_ne w.w [] with hw | hw
    · -- `w` is the root, so `v` is its child
      have hv : v.w = [c] := by rw [hc, hw, List.nil_append]
      have h1 : lpre a v.w = if c = a then [] else [a, c] := by rw [hv, lpre_cons]
      have h2 : lpre a w.w = [a] := by rw [hw]; rfl
      by_cases hca : c = a
      · rw [if_pos hca] at h1
        exact adj_of_snoc (c := a) (by rw [lmul_w, lmul_w, h1, h2]; rfl)
      · rw [if_neg hca] at h1
        exact adj_of_parent (c := c) (by rw [lmul_w, lmul_w, h1, h2]; rfl)
    · exact adj_of_parent (c := c) (by rw [lmul_w, lmul_w, hc, lpre_append_singleton hw])

/-- Left multiplication by a letter is a graph automorphism. -/
lemma lmul_adj_iff (a : A) {v w : V} : G.Adj (lmul a v) (lmul a w) ↔ G.Adj v w := by
  refine ⟨fun h => ?_, lmul_adj a⟩
  have h' := lmul_adj a h
  rwa [lmul_involutive, lmul_involutive] at h'

/-- Left multiplication by a letter as a graph automorphism. -/
def lmulIso (a : A) : G ≃g G where
  toEquiv :=
    { toFun := lmul a
      invFun := lmul a
      left_inv := lmul_involutive a
      right_inv := lmul_involutive a }
  map_rel_iff' := fun {v w} => lmul_adj_iff a

@[simp] lemma lmulIso_apply (a : A) (v : V) : lmulIso a v = lmul a v := rfl

@[simp] lemma lmulIso_apply_w (a : A) (v : V) : (lmulIso a v).w = lpre a v.w := rfl

end Ultra
