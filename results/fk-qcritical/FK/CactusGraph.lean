import FK.TreeEdgeTransitive
import FK.AGSleevedAnnulus

/-!
# The degree-five triangle cactus

Every edge of the reduced-word five-regular tree carries one triangle.  The
implementation retains the direct bond and adds a new midpoint with two spoke
bonds.  All statements below are about this graph itself, not about a surrogate
percolation measure on the tree.
-/

namespace Ultra.TriangleCactus

open Ultra V
open scoped Sym2

/-- Vertices are old tree junctions or the midpoint of one old tree edge. -/
abbrev Vertex := V ⊕ G.edgeSet

/-- The triangle expansion of `Ultra.G`. -/
def graph : SimpleGraph Vertex where
  Adj
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inl x, Sum.inr e => x ∈ (e : Sym2 V)
    | Sum.inr e, Sum.inl x => x ∈ (e : Sym2 V)
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro x y hxy
    cases x with
    | inl x => cases y with
      | inl y => exact hxy.symm
      | inr e => exact hxy
    | inr e => cases y with
      | inl y => exact hxy
      | inr f => exact hxy.elim⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl x => exact G.loopless.irrefl x
    | inr e => exact id⟩

lemma graph_eq_sleeve : graph = FK.AGImplant.Sleeve.graph G := by
  ext x y
  cases x with
  | inl x => cases y with
    | inl y => rfl
    | inr e => rfl
  | inr e => cases y with
    | inl y => rfl
    | inr f => rfl

/-- The midpoint of `e` is joined to its two canonical endpoints. -/
noncomputable def baseEdge (e : G.edgeSet) : graph.edgeSet :=
  ⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2), by
    change G.Adj (e : Sym2 V).out.1 (e : Sym2 V).out.2
    have he : s((e : Sym2 V).out.1, (e : Sym2 V).out.2) = (e : Sym2 V) :=
      Quot.out_eq _
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.property⟩

noncomputable def leftSpoke (e : G.edgeSet) : graph.edgeSet :=
  ⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inr e), Sym2.out_fst_mem (e : Sym2 V)⟩

noncomputable def rightSpoke (e : G.edgeSet) : graph.edgeSet :=
  ⟨s(Sum.inr e, Sum.inl (e : Sym2 V).out.2), Sym2.out_snd_mem (e : Sym2 V)⟩

lemma baseEdge_val (e : G.edgeSet) :
    (baseEdge e : Sym2 Vertex) = Sym2.map Sum.inl (e : Sym2 V) := by
  calc
    (baseEdge e : Sym2 Vertex) =
        Sym2.map Sum.inl s((e : Sym2 V).out.1, (e : Sym2 V).out.2) := rfl
    _ = Sym2.map Sum.inl (e : Sym2 V) := congrArg (Sym2.map Sum.inl) (Quot.out_eq _)

lemma baseEdge_injective : Function.Injective baseEdge := by
  intro e f hef
  apply Subtype.ext
  have hval := congrArg Subtype.val hef
  rw [baseEdge_val, baseEdge_val] at hval
  exact (Sym2.map.injective Sum.inl_injective) hval

lemma leftSpoke_injective : Function.Injective leftSpoke := by
  intro e f h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inr e) =
    s(Sum.inl (f : Sym2 V).out.1, Sum.inr f) at hval
  rcases Sym2.eq_iff.mp hval with ⟨_, hef⟩ | ⟨hne, _⟩
  · injection hef
  · exact (Sum.inl_ne_inr hne).elim

lemma rightSpoke_injective : Function.Injective rightSpoke := by
  intro e f h
  have hval := congrArg Subtype.val h
  change s(Sum.inr e, Sum.inl (e : Sym2 V).out.2) =
    s(Sum.inr f, Sum.inl (f : Sym2 V).out.2) at hval
  rcases Sym2.eq_iff.mp hval with ⟨hef, _⟩ | ⟨_, hne⟩
  · injection hef
  · exact (Sum.inl_ne_inr hne).elim

lemma baseEdge_ne_leftSpoke (e f : G.edgeSet) : baseEdge e ≠ leftSpoke f := by
  intro h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) =
    s(Sum.inl (f : Sym2 V).out.1, Sum.inr f) at hval
  rcases Sym2.eq_iff.mp hval with ⟨_, h⟩ | ⟨h, _⟩ <;> exact Sum.inl_ne_inr h

lemma baseEdge_ne_rightSpoke (e f : G.edgeSet) : baseEdge e ≠ rightSpoke f := by
  intro h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inl (e : Sym2 V).out.2) =
    s(Sum.inr f, Sum.inl (f : Sym2 V).out.2) at hval
  rcases Sym2.eq_iff.mp hval with ⟨h, _⟩ | ⟨_, h⟩ <;> exact Sum.inl_ne_inr h

lemma out_fst_ne_out_snd (e : G.edgeSet) :
    (e : Sym2 V).out.1 ≠ (e : Sym2 V).out.2 := by
  have hadj : G.Adj (e : Sym2 V).out.1 (e : Sym2 V).out.2 := by
    have he : s((e : Sym2 V).out.1, (e : Sym2 V).out.2) = (e : Sym2 V) :=
      Quot.out_eq _
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.property
  exact hadj.ne

lemma leftSpoke_ne_rightSpoke (e f : G.edgeSet) : leftSpoke e ≠ rightSpoke f := by
  intro h
  have hval := congrArg Subtype.val h
  change s(Sum.inl (e : Sym2 V).out.1, Sum.inr e) =
    s(Sum.inr f, Sum.inl (f : Sym2 V).out.2) at hval
  rcases Sym2.eq_iff.mp hval with ⟨h, _⟩ | ⟨hends, hef⟩
  · exact Sum.inl_ne_inr h
  · have he : e = f := by injection hef
    subst f
    exact out_fst_ne_out_snd e (Sum.inl_injective hends)

/-- The three original bonds in the triangle over `e`. -/
noncomputable def bond (x : G.edgeSet × Fin 3) : graph.edgeSet :=
  match x.2 with
  | 0 => baseEdge x.1
  | 1 => leftSpoke x.1
  | 2 => rightSpoke x.1

lemma bond_injective : Function.Injective bond := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  fin_cases i <;> fin_cases j <;> simp only [bond] at h ⊢
  all_goals try exact congrArg (fun x => (x, (0 : Fin 3))) (baseEdge_injective h)
  all_goals try exact congrArg (fun x => (x, (1 : Fin 3))) (leftSpoke_injective h)
  all_goals try exact congrArg (fun x => (x, (2 : Fin 3))) (rightSpoke_injective h)
  all_goals first
    | exact (baseEdge_ne_leftSpoke e f h).elim
    | exact (baseEdge_ne_rightSpoke e f h).elim
    | exact (leftSpoke_ne_rightSpoke e f h).elim
    | exact (baseEdge_ne_leftSpoke f e h.symm).elim
    | exact (baseEdge_ne_rightSpoke f e h.symm).elim
    | exact (leftSpoke_ne_rightSpoke f e h.symm).elim

lemma bond_surjective : Function.Surjective bond := by
  rintro ⟨z, hz⟩
  induction z using Sym2.ind with
  | _ x y =>
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        let e : G.edgeSet := ⟨s(x, y), hz⟩
        refine ⟨(e, 0), ?_⟩
        rw [show bond (e, 0) = baseEdge e from rfl]
        apply Subtype.ext
        exact baseEdge_val e
      | inr e =>
        change x ∈ (e : Sym2 V) at hz
        rw [← Quot.out_eq (e : Sym2 V), Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨(e, 1), rfl⟩
        · refine ⟨(e, 2), Subtype.ext ?_⟩
          exact Sym2.eq_swap
    | inr e =>
      cases y with
      | inl y =>
        change y ∈ (e : Sym2 V) at hz
        rw [← Quot.out_eq (e : Sym2 V), Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · refine ⟨(e, 1), Subtype.ext ?_⟩
          exact Sym2.eq_swap
        · exact ⟨(e, 2), rfl⟩
      | inr f => exact hz.elim

/-- An explicit equivalence between the original bond subtype and three bonds
per junction-tree adjacency. -/
noncomputable def bondEquiv : (G.edgeSet × Fin 3) ≃ graph.edgeSet :=
  Equiv.ofBijective bond ⟨bond_injective, bond_surjective⟩

@[simp] lemma bondEquiv_apply (x : G.edgeSet × Fin 3) : bondEquiv x = bond x := rfl

/-- Local finiteness on the expanded graph itself. -/
noncomputable instance : graph.LocallyFinite := by
  rw [graph_eq_sleeve]
  infer_instance

/-- Connectedness on the expanded graph itself. -/
theorem graph_connected : graph.Connected := by
  rw [graph_eq_sleeve]
  exact FK.AGImplant.Sleeve.graphConnected G G_connected

/-- The expanded graph is quasi-transitive. -/
theorem graph_quasiTransitive : FK.QuasiTransitive.IsQuasiTransitive graph := by
  letI : Nonempty V := ⟨V.root⟩
  letI : Nonempty G.edgeSet :=
    ⟨childE ⟨(V.root, spineA), (Or.inl rfl)⟩⟩
  rw [graph_eq_sleeve]
  exact FK.AGImplant.Sleeve.graphQuasiTransitive_of_vertex_edge_transitive G
    vertex_transitive edge_transitive

/-- The underlying tree has infinitely many vertices. -/
instance infiniteTreeVertex : Infinite V :=
  Infinite.of_injective
    (fun n : ℕ => (⟨altWord spineA spineB n, altWord_reduced spineA_ne_spineB n⟩ : V))
    (by
      intro n m h
      have hw := congrArg V.w h
      have hl := congrArg List.length hw
      simpa using hl)

instance : Infinite Vertex := Infinite.of_injective (fun v : V => Sum.inl v) Sum.inl_injective

end Ultra.TriangleCactus
