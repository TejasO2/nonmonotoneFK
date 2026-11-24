import FK.AGTree.Aut
import FK.FKQuasiTransitiveDevices

/-!
# Vertex transitivity and quasi-transitivity of the two-class tree

Iterating the single-letter automorphisms of `Ultra/Aut.lean` gives a graph
automorphism taking the root to any prescribed reduced word.  Consequently the
full automorphism group of `Ultra.G` acts transitively on vertices, the orbit
quotient is a subsingleton, and `Ultra.G` is quasi-transitive in the sense of
`FK.QuasiTransitive.IsQuasiTransitive`.  Because the graph is also regular of
degree five (`Ultra.degree_eq_five`), this is the bounded-degree
quasi-transitive setting of the enhancement/AG reference comparison.
-/

namespace Ultra

open V

/-! ### Left multiplication by a whole word -/

/-- Left multiplication by a word: apply the single-letter automorphisms from
the right.  For `l = [a₁, …, aₙ]` the root is sent to `[a₁, …, aₙ]`. -/
def lmulList : List A → V → V
  | [], v => v
  | a :: t, v => lmul a (lmulList t v)

@[simp] lemma lmulList_nil (v : V) : lmulList [] v = v := rfl

@[simp] lemma lmulList_cons (a : A) (t : List A) (v : V) :
    lmulList (a :: t) v = lmul a (lmulList t v) := rfl

lemma lmulList_adj_iff (l : List A) {v w : V} :
    G.Adj (lmulList l v) (lmulList l w) ↔ G.Adj v w := by
  induction l with
  | nil => exact Iff.rfl
  | cons a t ih => exact (lmul_adj_iff a).trans ih

lemma lmulList_append (l₁ l₂ : List A) (v : V) :
    lmulList (l₁ ++ l₂) v = lmulList l₁ (lmulList l₂ v) := by
  induction l₁ with
  | nil => rfl
  | cons a t ih => exact congrArg (lmul a) ih

/-- The reversed word gives the inverse operation. -/
lemma lmulList_reverse (l : List A) (v : V) : lmulList l.reverse (lmulList l v) = v := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons, lmulList_append]
    show lmulList t.reverse (lmul a (lmul a (lmulList t v))) = v
    rw [lmul_involutive, ih]

/-- The word-length automorphism as a graph automorphism. -/
def lmulListIso (l : List A) : G ≃g G where
  toEquiv :=
    { toFun := lmulList l
      invFun := lmulList l.reverse
      left_inv := lmulList_reverse l
      right_inv := fun v => by
        have := lmulList_reverse l.reverse v
        rwa [List.reverse_reverse] at this }
  map_rel_iff' := fun {v w} => lmulList_adj_iff l

@[simp] lemma lmulListIso_apply (l : List A) (v : V) :
    lmulListIso l v = lmulList l v := rfl

/-- The word automorphism sends the root to that word. -/
lemma lmulList_root : ∀ {l : List A} (h : Reduced l), lmulList l V.root = ⟨l, h⟩
  | [], _ => by apply V.ext; rfl
  | a :: t, h => by
      show lmul a (lmulList t V.root) = ⟨a :: t, h⟩
      rw [lmulList_root (Reduced.tail h)]
      apply V.ext
      show lpre a t = a :: t
      cases t with
      | nil => rfl
      | cons b u => exact lpre_cons_of_ne (a := a) (b := b) (fun hba => h.1 hba.symm) u

lemma lmulListIso_root {l : List A} (h : Reduced l) :
    lmulListIso l V.root = ⟨l, h⟩ := by
  rw [lmulListIso_apply, lmulList_root h]

/-! ### Transitivity -/

/-- The automorphism group acts transitively on vertices. -/
theorem vertex_transitive (v w : V) : ∃ φ : G ≃g G, φ v = w := by
  refine ⟨(lmulListIso v.w).symm.trans (lmulListIso w.w), ?_⟩
  have hφ : (lmulListIso v.w) V.root = v := lmulListIso_root v.red
  have hv : (lmulListIso v.w).symm v = V.root := by
    have h2 : (lmulListIso v.w).symm ((lmulListIso v.w) V.root) = V.root :=
      (lmulListIso v.w).symm_apply_apply V.root
    rw [hφ] at h2
    exact h2
  show lmulListIso w.w ((lmulListIso v.w).symm v) = w
  rw [hv, lmulListIso_root w.red]

/-- The orbit quotient is a subsingleton: there is exactly one vertex orbit. -/
theorem orbit_subsingleton :
    Subsingleton (MulAction.orbitRel.Quotient (G ≃g G) V) := by
  refine ⟨fun q₁ q₂ => ?_⟩
  refine Quotient.inductionOn₂ q₁ q₂ (fun v w => Quotient.sound ?_)
  show MulAction.orbitRel (G ≃g G) V v w
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨φ, hφ⟩ := vertex_transitive v w
  exact ⟨φ.symm, by rw [← hφ]; exact φ.symm_apply_apply v⟩

/-- **The two-class reduced-word tree is quasi-transitive**. -/
theorem isQuasiTransitive : FK.QuasiTransitive.IsQuasiTransitive G :=
  haveI := orbit_subsingleton
  Finite.of_subsingleton

end Ultra
