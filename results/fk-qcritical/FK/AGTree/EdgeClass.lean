import FK.AGTree.Degree

/-!
# The letter class of an edge is preserved by the word automorphisms

The two-rate law of `Ultra/Edges.lean` opens an edge with the rate attached to
the letter class `acls (letterOf e)`.  For the model to be homogeneous under the
automorphisms of the tree, those automorphisms must preserve `letterOf`.  This
file proves exactly that for the single-letter automorphisms `lmulIso a`.
-/

namespace Ultra

open V

/-! ### Last letters under prepending -/

/-- Prepending does not change the last letter, unless it cancels the whole
word. -/
lemma lpre_getLast? {a : A} {l : List A} (h : l ≠ []) (hl : lpre a l ≠ []) :
    (lpre a l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl h
  | cons b t =>
    cases t with
    | nil =>
      rw [lpre_cons]
      by_cases hb : b = a
      · exact absurd (by rw [lpre_cons, if_pos hb]) hl
      · rw [if_neg hb]; simp
    | cons d u =>
      rw [lpre_cons]
      by_cases hb : b = a
      · rw [if_pos hb]; simp
      · rw [if_neg hb]; simp

/-- Prepending a letter preserves validity at every non-root vertex. -/
lemma lmul_valid_of_ne_nil {a c : A} {u : V} (hu : u.w ≠ []) (h : u.Valid c) :
    (lmul a u).Valid c := by
  obtain hv | hv := h
  · exact absurd hv hu
  · by_cases hl : lpre a u.w = []
    · exact Or.inl (by rw [lmul_w]; exact hl)
    · refine Or.inr ?_
      rw [lmul_w, lpre_getLast? hu hl]
      exact hv

/-- Off the root, prepending commutes with appending a letter. -/
lemma lmul_snoc_of_ne_nil {a c : A} {u : V} (hu : u.w ≠ []) (h : u.Valid c) :
    lmul a (u.snoc c h) = (lmul a u).snoc c (lmul_valid_of_ne_nil hu h) := by
  apply V.ext
  simp only [lmul_w, V.snoc_w]
  exact lpre_append_singleton hu

/-! ### Prepending at the root -/

lemma root_snoc_eq (c : A) (h : V.root.Valid c) :
    V.root.snoc c h = ⟨[c], reduced_singleton c⟩ := by
  apply V.ext
  rw [V.snoc_w]
  rfl

lemma lmul_singleton_self (a : A) :
    lmul a ⟨[a], reduced_singleton a⟩ = V.root := by
  apply V.ext
  rw [lmul_w, lpre_cons, if_pos rfl]
  rfl

lemma lmul_singleton_of_ne {a c : A} (h : c ≠ a) (r : Reduced [c]) :
    lmul a ⟨[c], r⟩ = ⟨[a, c], ⟨fun hca => h hca.symm, trivial⟩⟩ := by
  apply V.ext
  rw [lmul_w, lpre_cons_of_ne (a := a) (b := c) h]

lemma root_valid_of_ne {c a : A} (h : c ≠ a) :
    ((⟨[a], reduced_singleton a⟩ : V)).Valid c := by
  refine Or.inr ?_
  simp [Ne.symm h]

/-! ### The image of a child edge -/

lemma mapEdgeSet_childE_sym2 (a : A) (u : V) (c : A) (h : u.Valid c) :
    (((lmulIso a).mapEdgeSet (childE ⟨(u, c), h⟩) : G.edgeSet) : Sym2 V)
      = s(lmul a u, lmul a (u.snoc c h)) := by
  rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
  rfl

/-- At the root the validity proof can be taken to be canonical. -/
lemma childE_root_congr (c : A) (h : V.root.Valid c) :
    childE ⟨(V.root, c), h⟩ =
      childE ⟨(V.root, c), (Or.inl rfl : V.root.Valid c)⟩ := by
  rw [show (⟨(V.root, c), h⟩ : Echild) = ⟨(V.root, c), (Or.inl rfl : V.root.Valid c)⟩
    from Subtype.ext rfl]

/-- A child edge is mapped to a child edge of the same letter. -/
lemma mapEdgeSet_childE (a : A) (u : V) (c : A) (h : u.Valid c) :
    ∃ (u' : V) (h' : u'.Valid c),
      (lmulIso a).mapEdgeSet (childE ⟨(u, c), h⟩) = childE ⟨(u', c), h'⟩ := by
  have hroot : lmul a V.root = (⟨[a], reduced_singleton a⟩ : V) := by
    apply V.ext; rfl
  rcases eq_or_ne u.w [] with hu | hu
  · obtain rfl : u = V.root := V.ext hu
    rw [childE_root_congr c h]
    rcases eq_or_ne c a with hca | hca
    · -- the `a`-edge at the root is reversed onto itself
      obtain rfl : a = c := hca.symm
      refine ⟨V.root, Or.inl rfl, ?_⟩
      apply Subtype.ext
      rw [mapEdgeSet_childE_sym2]
      have h2 : lmul a (V.root.snoc a (Or.inl rfl)) = V.root := by
        rw [root_snoc_eq a (Or.inl rfl), lmul_singleton_self]
      rw [hroot, h2]
      change s((⟨[a], reduced_singleton a⟩ : V), V.root) =
        s(V.root, ⟨[a], reduced_singleton a⟩)
      exact Sym2.eq_swap
    · -- otherwise the child edge is extended on the right
      refine ⟨⟨[a], reduced_singleton a⟩, root_valid_of_ne hca, ?_⟩
      apply Subtype.ext
      rw [mapEdgeSet_childE_sym2]
      have h2 : lmul a (V.root.snoc c (Or.inl rfl)) =
          ⟨[a, c], ⟨fun h' => hca h'.symm, trivial⟩⟩ := by
        rw [root_snoc_eq c (Or.inl rfl), lmul_singleton_of_ne hca (reduced_singleton c)]
      have h3 : ((⟨[a], reduced_singleton a⟩ : V).snoc c (root_valid_of_ne hca) : V) =
          ⟨[a, c], ⟨fun h' => hca h'.symm, trivial⟩⟩ := by
        apply V.ext
        rw [V.snoc_w]
        rfl
      rw [hroot, h2]
      change s((⟨[a], reduced_singleton a⟩ : V),
          ⟨[a, c], ⟨fun h' => hca h'.symm, trivial⟩⟩) =
        s((⟨[a], reduced_singleton a⟩ : V),
          (⟨[a], reduced_singleton a⟩ : V).snoc c (root_valid_of_ne hca))
      rw [h3]
  · refine ⟨lmul a u, lmul_valid_of_ne_nil hu h, ?_⟩
    apply Subtype.ext
    rw [mapEdgeSet_childE_sym2, lmul_snoc_of_ne_nil hu h]
    rfl

/-! ### The letter classes are preserved -/

/-- Every single-letter automorphism preserves the letter of every edge. -/
theorem letterOf_mapEdgeSet_lmulIso (a : A) (e : G.edgeSet) :
    letterOf ((lmulIso a).mapEdgeSet e) = letterOf e := by
  obtain ⟨x, rfl⟩ := childE_surj e
  obtain ⟨⟨u, c⟩, h⟩ := x
  obtain ⟨u', h', he⟩ := mapEdgeSet_childE a u c h
  rw [he, letterOf_childE, letterOf_childE]

/-- Hence the two-class rate of an edge is invariant under the single-letter
automorphisms. -/
theorem edgeRate_mapEdgeSet_lmulIso (r : Fin 2 → unitInterval) (a : A) (e : G.edgeSet) :
    edgeRate r ((lmulIso a).mapEdgeSet e) = edgeRate r e := by
  rw [edgeRate, edgeRate, letterOf_mapEdgeSet_lmulIso]

end Ultra
