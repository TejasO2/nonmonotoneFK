import FK.AGTree.Spine

/-!
# Edge transitivity of the reduced-word tree
-/

namespace Ultra

open V
open scoped Sym2

/-- Reducedness is preserved by an injective renaming of letters. -/
lemma Reduced.map_injective₂ {σ : A → A} (hσ : Function.Injective σ) :
    ∀ {l : List A}, Reduced l → Reduced (l.map σ)
  | [], _ => reduced_nil
  | [_], _ => reduced_singleton _
  | a :: b :: l, h => ⟨fun hab => h.1 (hσ hab), Reduced.map_injective₂ hσ h.2⟩

/-- Rename every letter in a reduced word. -/
def renameVertex (σ : A ≃ A) (v : V) : V :=
  ⟨v.w.map σ, Reduced.map_injective₂ σ.injective v.red⟩

@[simp] lemma renameVertex_w (σ : A ≃ A) (v : V) :
    (renameVertex σ v).w = v.w.map σ := rfl

@[simp] lemma renameVertex_root (σ : A ≃ A) : renameVertex σ V.root = V.root := by
  apply V.ext
  rfl

/-- A permutation of the alphabet induces a graph automorphism. -/
def renameIso (σ : A ≃ A) : G ≃g G where
  toEquiv :=
    { toFun := renameVertex σ
      invFun := renameVertex σ.symm
      left_inv := by
        intro v
        apply V.ext
        simp [renameVertex_w, List.map_map]
      right_inv := by
        intro v
        apply V.ext
        simp [renameVertex_w, List.map_map] }
  map_rel_iff' := by
    intro v w
    change G.Adj (renameVertex σ v) (renameVertex σ w) ↔ G.Adj v w
    constructor
    · rintro ⟨a, h | h⟩
      · refine ⟨σ.symm a, Or.inl ?_⟩
        have hc := congrArg (List.map σ.symm) h
        simpa [renameVertex_w, List.map_map] using hc
      · refine ⟨σ.symm a, Or.inr ?_⟩
        have hc := congrArg (List.map σ.symm) h
        simpa [renameVertex_w, List.map_map] using hc
    · rintro ⟨a, h | h⟩
      · exact ⟨σ a, Or.inl (by simpa [renameVertex_w] using congrArg (List.map σ) h)⟩
      · exact ⟨σ a, Or.inr (by simpa [renameVertex_w] using congrArg (List.map σ) h)⟩

@[simp] lemma renameIso_apply (σ : A ≃ A) (v : V) : renameIso σ v = renameVertex σ v := rfl

/-- The alphabet permutation sends a root child edge to the child edge with the
renamed letter. -/
lemma renameIso_mapEdgeSet_root_child (σ : A ≃ A) (a : A) (h : V.root.Valid a) :
    (renameIso σ).mapEdgeSet (childE ⟨(V.root, a), h⟩) =
      childE ⟨(V.root, σ a), (Or.inl rfl)⟩ := by
  apply Subtype.ext
  change s(renameVertex σ V.root, renameVertex σ (V.root.snoc a h)) =
    s(V.root, V.root.snoc (σ a) (Or.inl rfl))
  have hc : renameVertex σ (V.root.snoc a h) =
      V.root.snoc (σ a) (Or.inl rfl) := by
    apply V.ext
    change List.map σ (V.root.w ++ [a]) = V.root.w ++ [σ a]
    simp [V.root]
  rw [renameVertex_root, hc]

/-- Composition acts componentwise on edge subtypes. -/
lemma iso_trans_mapEdgeSet {H : SimpleGraph V} (φ ψ : H ≃g H) (e : H.edgeSet) :
    SimpleGraph.Iso.mapEdgeSet (φ.trans ψ) e = ψ.mapEdgeSet (φ.mapEdgeSet e) := by
  apply Subtype.ext
  change Sym2.map (ψ ∘ φ) (e : Sym2 V) = Sym2.map ψ (Sym2.map φ (e : Sym2 V))
  exact (Sym2.map_map (e : Sym2 V)).symm

/-- Every edge can be moved to the root edge on a prescribed letter. -/
lemma exists_iso_mapEdgeSet_root_child (e : G.edgeSet) (a : A) :
    ∃ φ : G ≃g G, φ.mapEdgeSet e = childE ⟨(V.root, a), (Or.inl rfl)⟩ := by
  obtain ⟨⟨⟨u, c⟩, h⟩, rfl⟩ := childE_surj e
  obtain ⟨φ, hφ⟩ := vertex_transitive u V.root
  have hadj : G.Adj V.root (φ (u.snoc c h)) := by
    rw [← hφ]
    exact φ.toHom.map_adj (adj_snoc h)
  rcases (adj_iff (v := V.root) (w := φ (u.snoc c h))).1 hadj with
    ⟨d, hd, hchild⟩ | ⟨hnil, _⟩
  · refine ⟨φ.trans (renameIso (Equiv.swap d a)), ?_⟩
    rw [iso_trans_mapEdgeSet]
    have hmap : φ.mapEdgeSet (childE ⟨(u, c), h⟩) =
        childE ⟨(V.root, d), hd⟩ := by
      apply Subtype.ext
      change s(φ u, φ (u.snoc c h)) = s(V.root, V.root.snoc d hd)
      rw [hφ, hchild]
    rw [hmap]
    exact renameIso_mapEdgeSet_root_child (Equiv.swap d a) d hd |>.trans (by
      rw [Equiv.swap_apply_left])
  · exact (hnil rfl).elim

/-- The reduced-word tree is edge-transitive. -/
theorem edge_transitive (e f : G.edgeSet) :
    ∃ φ : G ≃g G, φ.mapEdgeSet e = f := by
  obtain ⟨φe, hφe⟩ := exists_iso_mapEdgeSet_root_child e spineA
  obtain ⟨φf, hφf⟩ := exists_iso_mapEdgeSet_root_child f spineA
  refine ⟨φe.trans φf.symm, ?_⟩
  rw [iso_trans_mapEdgeSet, hφe, ← hφf]
  exact φf.mapEdgeSet.symm_apply_apply f

/-- Every tree edge lies on a double ray. -/
theorem onDoubleRay_any_edge (e : G.edgeSet) :
    FK.EssentialEnhancement.OnDoubleRay e := by
  obtain ⟨φ, hφ⟩ := exists_iso_mapEdgeSet_root_child e spineA
  have hr := FK.QuasiTransitive.onDoubleRay_mapEdgeSet
    (G := G) (G' := G) onDoubleRay_rootEdge φ.symm
  rw [← hφ] at hr
  have he : φ.symm.mapEdgeSet (φ.mapEdgeSet e) = e := by
    simpa using φ.mapEdgeSet.symm_apply_apply e
  rwa [he] at hr

end Ultra
