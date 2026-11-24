import FK.MonotoneLimitExistence
import FK.NestedMixture.Mixture
import FK.NestedMixture.Transport

/-!
# Nested finite boxes: the vertex/edge inclusion data and the region graph

A small `FiniteBox E` sitting inside a larger one is described by a vertex
injection preserving the endpoints of every small-box edge (`NestedBox`).  The
induced region of the large box is `dom = range vert`, `ide = {e | e ∈ B.edges}`;
`FK.SpecificationNesting` applies to the large box's graph on that region.

The small box's graph and the region sub-box are isomorphic as labelled
multigraphs (source and target agree on the nose after the vertex and edge
equivalences), so the free FK laws agree pointwise (`Transport`).
-/

open scoped Classical BigOperators ENNReal NNReal
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.SpecificationNesting

namespace FK.NestedMixture

variable {E : Type*}

/-- A finite box `B` sitting inside a finite box `C`, with an injective vertex map
preserving the endpoints of every `B`-edge. -/
structure NestedBox (B C : FK.InfiniteVolume.FiniteBox E) where
  edge_sub : ∀ e : E, e ∈ B.edges → e ∈ C.edges
  vert : B.Vertex → C.Vertex
  vert_inj : Function.Injective vert
  src : ∀ e : B.edges, C.source ⟨e.1, edge_sub e.1 e.2⟩ = vert (B.source e)
  tgt : ∀ e : B.edges, C.target ⟨e.1, edge_sub e.1 e.2⟩ = vert (B.target e)

namespace NestedBox

variable {B C : FK.InfiniteVolume.FiniteBox E} (N : NestedBox B C)

/-- The vertex region of the large box spanned by the small box. -/
def dom : Set C.Vertex := Set.range N.vert

/-- The edge region of the large box spanned by the small box. -/
def ide (N : NestedBox B C) : Set C.graph.Edge := {e | (e : E) ∈ B.edges}

lemma source_mem_dom (e : ↥N.ide) : C.source (e : C.graph.Edge) ∈ N.dom := by
  refine ⟨B.source ⟨(e : C.graph.Edge).1, e.2⟩, ?_⟩
  have he : (⟨(e : C.graph.Edge).1, N.edge_sub (e : C.graph.Edge).1 e.2⟩ : C.graph.Edge) =
      (e : C.graph.Edge) := Subtype.ext rfl
  exact (N.src ⟨(e : C.graph.Edge).1, e.2⟩).symm.trans (congrArg C.source he)

lemma target_mem_dom (e : ↥N.ide) : C.target (e : C.graph.Edge) ∈ N.dom := by
  refine ⟨B.target ⟨(e : C.graph.Edge).1, e.2⟩, ?_⟩
  have he : (⟨(e : C.graph.Edge).1, N.edge_sub (e : C.graph.Edge).1 e.2⟩ : C.graph.Edge) =
      (e : C.graph.Edge) := Subtype.ext rfl
  exact (N.tgt ⟨(e : C.graph.Edge).1, e.2⟩).symm.trans (congrArg C.target he)

/-- Both endpoints of every region edge lie in the vertex region. -/
theorem hdom : ∀ e : ↥N.ide,
    C.graph.source (e : C.graph.Edge) ∈ N.dom ∧ C.graph.target (e : C.graph.Edge) ∈ N.dom :=
  fun e => ⟨N.source_mem_dom e, N.target_mem_dom e⟩

/-- The vertex identification of the region with the small box. -/
noncomputable def vertEquiv : ↥N.dom ≃ B.Vertex :=
  (Equiv.ofInjective N.vert N.vert_inj).symm

/-- The edge identification of the region with the small box. -/
noncomputable def edgeEquiv : ↥N.ide ≃ B.edges where
  toFun e := ⟨(e : C.graph.Edge).1, e.2⟩
  invFun b := ⟨⟨b.1, N.edge_sub b.1 b.2⟩, b.2⟩
  left_inv e := by
    refine Subtype.ext ?_
    exact Subtype.ext rfl
  right_inv b := by
    refine Subtype.ext ?_
    rfl

@[simp] lemma edgeEquiv_apply (e : ↥N.ide) :
    ((N.edgeEquiv e : B.edges) : E) = (e : C.graph.Edge).1 := rfl

@[simp] lemma vertEquiv_symm_apply (v : B.Vertex) :
    ((N.vertEquiv.symm v : ↥N.dom) : C.Vertex) = N.vert v := rfl

/-- The source functions of the region sub-box and of the transported small box
agree. -/
theorem transport_source_eq :
    (fun a : ↥N.ide => N.vertEquiv.symm (B.graph.source (N.edgeEquiv a)))
      = (fun a : ↥N.ide =>
          (⟨C.graph.source (a : C.graph.Edge), (N.hdom a).1⟩ : ↥N.dom)) := by
  funext a
  refine Subtype.ext ?_
  rw [vertEquiv_symm_apply]
  exact (N.src ⟨(a : C.graph.Edge).1, a.2⟩).symm.trans
    (congrArg C.source (Subtype.ext rfl))

/-- The target functions of the region sub-box and of the transported small box
agree. -/
theorem transport_target_eq :
    (fun a : ↥N.ide => N.vertEquiv.symm (B.graph.target (N.edgeEquiv a)))
      = (fun a : ↥N.ide =>
          (⟨C.graph.target (a : C.graph.Edge), (N.hdom a).2⟩ : ↥N.dom)) := by
  funext a
  refine Subtype.ext ?_
  rw [vertEquiv_symm_apply]
  exact (N.tgt ⟨(a : C.graph.Edge).1, a.2⟩).symm.trans
    (congrArg C.target (Subtype.ext rfl))

/-- **The region sub-box is the transported small box.** -/
theorem subBox_eq_transport :
    subBox N.dom N.ide N.hdom
      = B.graph.transport N.vertEquiv N.edgeEquiv := by
  have h1 : subBox N.dom N.ide N.hdom
      = ({ Vertex := ↥N.dom, Edge := ↥N.ide,
            source := fun a => (⟨C.graph.source (a : C.graph.Edge), (N.hdom a).1⟩ : ↥N.dom),
            target := fun a => (⟨C.graph.target (a : C.graph.Edge), (N.hdom a).2⟩ : ↥N.dom) }
          : FK.Finite.LabelledMultigraph) := rfl
  have h2 : B.graph.transport N.vertEquiv N.edgeEquiv
      = ({ Vertex := ↥N.dom, Edge := ↥N.ide,
            source := fun a => N.vertEquiv.symm (B.graph.source (N.edgeEquiv a)),
            target := fun a => N.vertEquiv.symm (B.graph.target (N.edgeEquiv a)) }
          : FK.Finite.LabelledMultigraph) := rfl
  rw [h1, h2, N.transport_source_eq, N.transport_target_eq]

/-- **Pointwise identification of the region sub-box law with the small box law**
(in the region coordinates): the two graphs have the same vertex and edge types and
the same endpoint maps. -/
theorem subBox_fkPMF_eq_transport {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ω : ↥N.ide → Bool) :
    (subBox N.dom N.ide N.hdom).fkPMF hq hp
        (subBox N.dom N.ide N.hdom).freeBoundary ω
      = (B.graph.transport N.vertEquiv N.edgeEquiv).fkPMF hq hp
          (B.graph.transport N.vertEquiv N.edgeEquiv).freeBoundary ω := by
  exact fkPMF_eq_of_source_target_eq (V := ↥N.dom) (E := ↥N.ide)
    (fun a => (⟨C.graph.source (a : C.graph.Edge), (N.hdom a).1⟩ : ↥N.dom))
    (fun a => (⟨C.graph.target (a : C.graph.Edge), (N.hdom a).2⟩ : ↥N.dom))
    (fun a => N.vertEquiv.symm (B.graph.source (N.edgeEquiv a)))
    (fun a => N.vertEquiv.symm (B.graph.target (N.edgeEquiv a)))
    N.transport_source_eq.symm N.transport_target_eq.symm hq hp _ ω

end NestedBox

end FK.NestedMixture

#print axioms FK.NestedMixture.NestedBox.subBox_eq_transport
#print axioms FK.NestedMixture.NestedBox.subBox_fkPMF_eq_transport
