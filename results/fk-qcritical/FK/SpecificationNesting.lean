import FK.FiniteModel

/-!
# Splitting the component count of a finite graph along a vertex region

The paper's §1.3 uses one *standard computation*: for finite subgraphs
`Λ ⊆ Δ`, a boundary partition `α` of `Δ` and a configuration `η` on
`Δ ∖ Λ`, the conditional law of `ω|Λ` under `φ^α_Δ` is `φ^{α'}_Λ` where
`α' = π(α,η)` is the partition of `∂Λ` induced by `η` and `α`.

The mathematical content is a component-count splitting identity.  Let `A` be
the graph obtained from an ambient graph by *closing* every interior edge (it
keeps the exterior open edges and the boundary wiring), and `B` the ambient
graph with all edges.  Every `B`-edge whose endpoints are not both in the
region `R` is an `A`-edge.  Then

`#components B + #(A-reachability classes on R)`
  `= #components (region graph on R) + #components A`

where the region graph carries the `A`-reachability wiring on `R` plus the
`B`-edges inside `R`.  The extra term is exactly the information lost by
restricting to `R`; it does not depend on the interior configuration, which is
what makes the conditional law an FK law.

Everything here is finite graph theory; no measure theory is involved.
-/

open scoped Classical BigOperators

namespace FK.Finite.SpecificationNesting

universe u

/-- A chosen vertex of a connected component. -/
noncomputable def compRep {V : Type u} {G : SimpleGraph V} (C : G.ConnectedComponent) : V :=
  (SimpleGraph.ConnectedComponent.nonempty_supp C).some

lemma compRep_mem {V : Type u} {G : SimpleGraph V} (C : G.ConnectedComponent) :
    compRep C ∈ (C.supp : Set V) :=
  (SimpleGraph.ConnectedComponent.nonempty_supp C).some_mem

lemma mk_compRep {V : Type u} {G : SimpleGraph V} (C : G.ConnectedComponent) :
    G.connectedComponentMk (compRep C) = C :=
  (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp (compRep_mem C)

/-- Transport of reachability along a family of local reachability witnesses. -/
theorem reachable_of_adj_reachable {V W : Type u} {G : SimpleGraph W} {A : SimpleGraph V}
    (f : W → V) (h : ∀ x y, G.Adj x y → A.Reachable (f x) (f y)) {x y : W}
    (hxy : G.Reachable x y) : A.Reachable (f x) (f y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

/-! ## Region graphs and their reachability -/

section Graph

variable {V : Type u} [Fintype V]

/-- The wiring graph on a region `R`: two region vertices are adjacent when
they are already connected in the fixed ambient graph `A`. -/
def wiringGraph (A : SimpleGraph V) (R : Set V) : SimpleGraph ↥R where
  Adj x y := x ≠ y ∧ A.Reachable x.1 y.1
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- The region graph: the wiring plus the `B`-edges, restricted to `R`. -/
def regionGraph (A B : SimpleGraph V) (R : Set V) : SimpleGraph ↥R where
  Adj x y := x ≠ y ∧ (A.Reachable x.1 y.1 ∨ B.Adj x.1 y.1)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

variable {A B : SimpleGraph V} {R : Set V}

omit [Fintype V] in
/-- Reachability given by the wiring part alone. -/
theorem regionGraph_reachable_of_reachable (x y : ↥R) (h : A.Reachable x.1 y.1) :
    (regionGraph A B R).Reachable x y := by
  rcases eq_or_ne x y with rfl | hne
  · exact SimpleGraph.Reachable.refl x
  · exact SimpleGraph.Adj.reachable ⟨hne, Or.inl h⟩

omit [Fintype V] in
theorem wiringGraph_reachable_iff (x y : ↥R) :
    (wiringGraph A R).Reachable x y ↔ A.Reachable x.1 y.1 := by
  constructor
  · intro h
    exact reachable_of_adj_reachable (G := wiringGraph A R) (A := A) (fun z : ↥R => (z : V))
      (fun p q hpq => hpq.2) h
  · intro h
    rcases eq_or_ne x y with rfl | hne
    · exact SimpleGraph.Reachable.refl x
    · exact SimpleGraph.Adj.reachable ⟨hne, h⟩

omit [Fintype V] in
theorem regionGraph_reachable_iff {A B : SimpleGraph V} {R : Set V} (hAB : A ≤ B)
    (hR : ∀ u v, B.Adj u v → A.Adj u v ∨ (u ∈ R ∧ v ∈ R)) (x y : ↥R) :
    (regionGraph A B R).Reachable x y ↔ B.Reachable x.1 y.1 := by
  constructor
  · intro h
    exact reachable_of_adj_reachable (G := regionGraph A B R) (A := B) (fun z : ↥R => (z : V))
      (fun p q hpq => by
        rcases hpq.2 with h' | h'
        · exact h'.mono hAB
        · exact h'.reachable) h
  · intro h
    -- compression invariant: from `x ∈ R` we reach a region vertex by the
    -- region graph, staying `A`-connected to the ambient endpoint
    have key : ∀ {y : V}, B.Reachable x.1 y → ∃ z : ↥R,
        (regionGraph A B R).Reachable x z ∧ A.Reachable y z.1 := by
      intro y hy
      rw [SimpleGraph.reachable_iff_reflTransGen] at hy
      induction hy with
      | refl => exact ⟨x, SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl x.1⟩
      | tail _ hbc ih =>
          obtain ⟨z, hz, hAz⟩ := ih
          rcases hR _ _ hbc with hA | ⟨hbR, hcR⟩
          · exact ⟨z, hz, (SimpleGraph.Adj.reachable hA).symm.trans hAz⟩
          · refine ⟨⟨_, hcR⟩, ?_, SimpleGraph.Reachable.refl _⟩
            have h1 : (regionGraph A B R).Reachable z ⟨_, hbR⟩ :=
              regionGraph_reachable_of_reachable (A := A) (B := B) (R := R) z ⟨_, hbR⟩ hAz.symm
            have h2 : (regionGraph A B R).Reachable ⟨_, hbR⟩ ⟨_, hcR⟩ := by
              refine SimpleGraph.Adj.reachable ⟨?_, Or.inr hbc⟩
              intro h
              exact hbc.ne (congrArg Subtype.val h)
            exact hz.trans (h1.trans h2)
    obtain ⟨z, hz, hAz⟩ := key h
    exact hz.trans (regionGraph_reachable_of_reachable (A := A) (B := B) (R := R) z y hAz.symm)

end Graph

/-- Two simple graphs on the same vertex type with the same reachability
relation have the same number of connected components. -/
theorem card_components_eq_of_reachable_iff {W : Type u} {H₁ H₂ : SimpleGraph W}
    (h : ∀ x y : W, H₁.Reachable x y ↔ H₂.Reachable x y) :
    Nat.card H₁.ConnectedComponent = Nat.card H₂.ConnectedComponent := by
  classical
  refine Nat.card_congr (Equiv.ofBijective (fun C : H₁.ConnectedComponent =>
    H₂.connectedComponentMk (compRep C)) ?_)
  constructor
  · rintro C C' hCC'
    rw [← mk_compRep C, ← mk_compRep C']
    exact SimpleGraph.ConnectedComponent.sound
      ((h _ _).mpr (SimpleGraph.ConnectedComponent.exact hCC'))
  · intro D
    refine ⟨H₁.connectedComponentMk (compRep D), ?_⟩
    show H₂.connectedComponentMk (compRep (H₁.connectedComponentMk (compRep D))) = D
    have h1 : H₁.connectedComponentMk (compRep D) = H₁.connectedComponentMk
        (compRep (H₁.connectedComponentMk (compRep D))) := by
      rw [mk_compRep (H₁.connectedComponentMk (compRep D))]
    rw [← SimpleGraph.ConnectedComponent.sound ((h _ _).mp (SimpleGraph.ConnectedComponent.exact h1)),
      mk_compRep D]

/-! ## Splitting the component count -/

section Split

variable {V : Type u} [Fintype V]

/-- Components of `A` meeting `R` are the components of any graph on `R` with
the same reachability relation. -/
theorem card_components_meeting (A : SimpleGraph V) (R : Set V)
    (AR : SimpleGraph ↥R) (h : ∀ x y : ↥R, AR.Reachable x y ↔ A.Reachable x.1 y.1) :
    Nat.card {C : A.ConnectedComponent // ∃ x : ↥R, A.connectedComponentMk (x : V) = C} =
      Nat.card AR.ConnectedComponent := by
  classical
  refine (Nat.card_congr ?_).symm
  refine Equiv.ofBijective
    (fun D : AR.ConnectedComponent =>
      (⟨A.connectedComponentMk ((compRep D : ↥R) : V), ⟨compRep D, rfl⟩⟩ :
        {C : A.ConnectedComponent // ∃ x : ↥R, A.connectedComponentMk (x : V) = C})) ?_
  constructor
  · rintro D D' hDD'
    have hmem : D = AR.connectedComponentMk (compRep D) := (mk_compRep D).symm
    have hmem' : D' = AR.connectedComponentMk (compRep D') := (mk_compRep D').symm
    have hA : A.Reachable ((compRep D : ↥R) : V) ((compRep D' : ↥R) : V) :=
      SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hDD')
    rw [hmem, hmem']
    exact SimpleGraph.ConnectedComponent.sound ((h _ _).mpr hA)
  · rintro ⟨C, x, hx⟩
    refine ⟨AR.connectedComponentMk x, ?_⟩
    have h1 : AR.connectedComponentMk (compRep (AR.connectedComponentMk x)) =
        AR.connectedComponentMk x := mk_compRep _
    have hA : A.Reachable ((compRep (AR.connectedComponentMk x) : ↥R) : V) (x : V) :=
      (h _ _).mp (SimpleGraph.ConnectedComponent.exact h1)
    apply Subtype.ext
    show A.connectedComponentMk ((compRep (AR.connectedComponentMk x) : ↥R) : V) = C
    rw [SimpleGraph.ConnectedComponent.sound hA, hx]

/-- Membership in a component, read through the chosen representative. -/
lemma mem_supp_iff_reachable {G : SimpleGraph V} (D : G.ConnectedComponent) (v : V) :
    v ∈ (D.supp : Set V) ↔ G.Reachable (compRep D) v := by
  constructor
  · intro hv
    have h1 : G.connectedComponentMk v = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D v).mp hv
    have h2 : G.connectedComponentMk (compRep D) = G.connectedComponentMk v := by
      rw [mk_compRep D, h1]
    exact SimpleGraph.ConnectedComponent.exact h2
  · intro hv
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff D v).mpr
      ((SimpleGraph.ConnectedComponent.sound hv).symm.trans (mk_compRep D))

/-- Adding `B`-edges that touch `S` never changes the components contained in
`S`, provided all such edges are already `A`-edges. -/
theorem card_components_avoiding_of_le {A B : SimpleGraph V} {S : Set V} (hAB : A ≤ B)
    (h : ∀ u v, B.Adj u v → (u ∈ S ∨ v ∈ S) → A.Adj u v) :
    Nat.card {C : B.ConnectedComponent // ∀ v, v ∈ (C.supp : Set V) → v ∈ S} =
      Nat.card {C : A.ConnectedComponent // ∀ v, v ∈ (C.supp : Set V) → v ∈ S} := by
  classical
  -- a `B`-path started inside `S` stays `A`-reachable, hence inside `S`
  have key : ∀ {a : V}, (∀ v, A.Reachable a v → v ∈ S) → ∀ {b : V},
      B.Reachable a b → A.Reachable a b := by
    intro a ha b hab
    rw [SimpleGraph.reachable_iff_reflTransGen] at hab ⊢
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
        exact Relation.ReflTransGen.tail ih
          (h _ _ hbc (Or.inl (ha _ ((SimpleGraph.reachable_iff_reflTransGen a _).mpr ih))))
  refine Nat.card_congr ?_
  refine Equiv.ofBijective
    (fun C : {C : B.ConnectedComponent // ∀ v, v ∈ (C.supp : Set V) → v ∈ S} =>
      (⟨A.connectedComponentMk ((compRep C.1 : V)), ?_⟩ :
        {C : A.ConnectedComponent // ∀ v, v ∈ (C.supp : Set V) → v ∈ S})) ?_
  · intro v hv
    have hAreach : A.Reachable (compRep C.1 : V) v :=
      (SimpleGraph.ConnectedComponent.exact
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ v).mp hv)).symm
    exact C.2 v (mem_supp_iff_reachable C.1 v |>.mpr (hAreach.mono hAB))
  constructor
  · rintro C C' hEq
    have hmem : C.1 = B.connectedComponentMk (compRep C.1 : V) := (mk_compRep C.1).symm
    have hmem' : C'.1 = B.connectedComponentMk (compRep C'.1 : V) := (mk_compRep C'.1).symm
    have hA : A.Reachable (compRep C.1 : V) (compRep C'.1 : V) :=
      SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hEq)
    apply Subtype.ext
    rw [hmem, hmem']
    exact SimpleGraph.ConnectedComponent.sound (hA.mono hAB)
  · rintro ⟨D, hD⟩
    have hstep : ∀ v, B.Reachable (compRep D : V) v → A.Reachable (compRep D : V) v :=
      fun v hv => key (a := compRep D) (fun w hw => hD w (mem_supp_iff_reachable D w |>.mpr hw)) hv
    have hsub : ∀ v, v ∈ ((B.connectedComponentMk (compRep D : V)).supp : Set V) → v ∈ S := by
      intro v hv
      exact hD v (mem_supp_iff_reachable D v |>.mpr
        (hstep v ((SimpleGraph.ConnectedComponent.exact
            (mk_compRep (B.connectedComponentMk (compRep D : V)))).symm.trans
          ((mem_supp_iff_reachable (B.connectedComponentMk (compRep D : V)) v).mp hv))))
    refine ⟨⟨B.connectedComponentMk (compRep D : V), hsub⟩, ?_⟩
    apply Subtype.ext
    show A.connectedComponentMk
      ((compRep (B.connectedComponentMk (compRep D : V)) : V)) = D
    have h1 : A.Reachable (compRep (B.connectedComponentMk (compRep D : V)) : V) (compRep D : V) :=
      (hstep _ (SimpleGraph.ConnectedComponent.exact
        (mk_compRep (B.connectedComponentMk (compRep D : V)))).symm).symm
    rw [SimpleGraph.ConnectedComponent.sound h1]
    exact mk_compRep D

/-- Cardinality splitting of a finite type along a decidable predicate. -/
theorem natCard_subtype_add (α : Type u) [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card α = Nat.card {a : α // p a} + Nat.card {a : α // ¬p a} := by
  rw [← Nat.card_sum]
  exact (Nat.card_congr (Equiv.sumCompl p)).symm

/-- Cardinality of a subtype depends only on the proposition. -/
theorem natCard_subtype_congr {α : Type u} (p q : α → Prop) (h : ∀ a, p a ↔ q a) :
    Nat.card {a : α // p a} = Nat.card {a : α // q a} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, (h x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (h x.1).mpr x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

/-- **Component-count splitting.**  Adding edges whose endpoints are not both
in `R` cannot interact with the region part of the count. -/
theorem card_connectedComponent_split {A B : SimpleGraph V} {R : Set V} (hAB : A ≤ B)
    (hR : ∀ u v, B.Adj u v → A.Adj u v ∨ (u ∈ R ∧ v ∈ R)) :
    Nat.card B.ConnectedComponent + Nat.card (wiringGraph A R).ConnectedComponent =
      Nat.card (regionGraph A B R).ConnectedComponent + Nat.card A.ConnectedComponent := by
  classical
  have hmeet : ∀ (G : SimpleGraph V) (C : G.ConnectedComponent),
      (∃ x : ↥R, G.connectedComponentMk (x : V) = C) ↔
        ∃ v, v ∈ (C.supp : Set V) ∧ v ∈ R := by
    intro G C
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl, x.2⟩
    · rintro ⟨v, hv, hvR⟩
      exact ⟨⟨v, hvR⟩, (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mp hv⟩
  have hsplitB := natCard_subtype_add B.ConnectedComponent
    (fun C : B.ConnectedComponent => ∃ x : ↥R, B.connectedComponentMk (x : V) = C)
  have hsplitA := natCard_subtype_add A.ConnectedComponent
    (fun C : A.ConnectedComponent => ∃ x : ↥R, A.connectedComponentMk (x : V) = C)
  have hBmeet : Nat.card {C : B.ConnectedComponent //
      ∃ x : ↥R, B.connectedComponentMk (x : V) = C} =
      Nat.card (regionGraph A B R).ConnectedComponent :=
    card_components_meeting B R (regionGraph A B R) (regionGraph_reachable_iff hAB hR)
  have hAmeet : Nat.card {C : A.ConnectedComponent //
      ∃ x : ↥R, A.connectedComponentMk (x : V) = C} =
      Nat.card (wiringGraph A R).ConnectedComponent :=
    card_components_meeting A R (wiringGraph A R) (wiringGraph_reachable_iff)
  have havoid : Nat.card {C : B.ConnectedComponent //
      ¬∃ x : ↥R, B.connectedComponentMk (x : V) = C} =
      Nat.card {C : A.ConnectedComponent //
        ¬∃ x : ↥R, A.connectedComponentMk (x : V) = C} := by
    have hSR : ∀ u v, B.Adj u v → (u ∈ {w : V | w ∉ R} ∨ v ∈ {w : V | w ∉ R}) →
        A.Adj u v := by
      intro u v huv h
      rcases hR u v huv with h' | ⟨huR, hvR⟩
      · exact h'
      · rcases h with hu | hv
        · exact absurd (hu huR) (by simp)
        · exact absurd (hv hvR) (by simp)
    have hmain := card_components_avoiding_of_le (A := A) (B := B)
      (S := {w : V | w ∉ R}) hAB hSR
    have eB : Nat.card {C : B.ConnectedComponent //
        ¬∃ x : ↥R, B.connectedComponentMk (x : V) = C} =
        Nat.card {C : B.ConnectedComponent // ∀ v, v ∈ (C.supp : Set V) → v ∈ {w : V | w ∉ R}} :=
      natCard_subtype_congr _ _ (fun C => by
        constructor
        · intro h v hv hvR
          exact h ((hmeet B C).mpr ⟨v, hv, hvR⟩)
        · rintro h ⟨x, hx⟩
          exact h x.1 ((SimpleGraph.ConnectedComponent.mem_supp_iff C x.1).mpr hx) x.2)
    have eA : Nat.card {C : A.ConnectedComponent //
        ¬∃ x : ↥R, A.connectedComponentMk (x : V) = C} =
        Nat.card {C : A.ConnectedComponent // ∀ v, v ∈ (C.supp : Set V) → v ∈ {w : V | w ∉ R}} :=
      natCard_subtype_congr _ _ (fun C => by
        constructor
        · intro h v hv hvR
          exact h ((hmeet A C).mpr ⟨v, hv, hvR⟩)
        · rintro h ⟨x, hx⟩
          exact h x.1 ((SimpleGraph.ConnectedComponent.mem_supp_iff C x.1).mpr hx) x.2)
    rw [eB, eA, hmain]
  omega

end Split


/-! ## The FK sub-box of a finite labelled multigraph

Fix an ambient finite labelled multigraph `G`, a set `dom` of vertices and a set
`I` of edge labels with both endpoints in `dom`.  The *sub-box* has vertex type
`↥dom` and edge type `↥I`.  Closing all sub-box edges leaves the graph
`fixedGraph`; its reachability classes on `dom` are the boundary partition
`inducedPartition` carried by the exterior of the sub-box. -/

section FKBox

open FK.Finite FK.Finite.LabelledMultigraph

/-- The sub-box: region vertices and region edge labels. -/
@[reducible] noncomputable def subBox {G : LabelledMultigraph} (dom : Set G.Vertex)
    (I : Set G.Edge) (hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧
      G.target (e : G.Edge) ∈ dom) : LabelledMultigraph where
  Vertex := ↥dom
  Edge := ↥I
  source e := ⟨G.source (e : G.Edge), (hdom e).1⟩
  target e := ⟨G.target (e : G.Edge), (hdom e).2⟩

/-- Close every sub-box edge label.  The remaining configuration depends only
on the exterior of the sub-box. -/
noncomputable def interiorClosed {G : LabelledMultigraph} (I : Set G.Edge)
    (ω : G.Configuration) : G.Configuration :=
  fun e => if e ∈ I then false else ω e

lemma interiorClosed_le {G : LabelledMultigraph} (I : Set G.Edge)
    (ω : G.Configuration) : interiorClosed I ω ≤ ω := by
  classical
  intro e
  unfold interiorClosed
  split_ifs with h
  · exact bot_le
  · exact le_rfl

/-- The fixed graph: exterior open edges plus the boundary wiring, with all
sub-box edges closed. -/
noncomputable def fixedGraph {G : LabelledMultigraph} (I : Set G.Edge)
    (α : G.BoundaryPartition) (ω : G.Configuration) : SimpleGraph G.Vertex :=
  G.connectionGraph α (interiorClosed I ω)

/-- The boundary partition induced by an exterior configuration: two region
vertices are in the same block when they are connected in the fixed graph. -/
noncomputable def inducedPartition {G : LabelledMultigraph} (dom : Set G.Vertex)
    (I : Set G.Edge) (α : G.BoundaryPartition) (ω : G.Configuration) : Setoid ↥dom where
  r x y := (fixedGraph I α ω).Reachable x.1 y.1
  iseqv := ⟨fun x => SimpleGraph.Reachable.refl _,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The interior restriction of an ambient configuration. -/
def restrictI {G : LabelledMultigraph} (I : Set G.Edge)
    (ω : G.Configuration) : (↥I) → Bool :=
  fun e => ω (e : G.Edge)

end FKBox

section FKMain

open FK.Finite FK.Finite.LabelledMultigraph

variable {G : LabelledMultigraph}
variable {dom : Set G.Vertex}
variable {I : Set G.Edge}
variable {hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom}

/-- Region vertices: reachability in the region graph and in the sub-box
connection graph agree. -/
theorem regionGraph_reachable_iff_subBox (α : G.BoundaryPartition) (ω : G.Configuration)
    (x y : ↥dom) :
    (regionGraph (fixedGraph I α ω) (G.connectionGraph α ω) dom).Reachable x y ↔
      ((subBox dom I hdom).connectionGraph (inducedPartition dom I α ω)
        (restrictI I ω)).Reachable x y := by
  classical
  have step₁ : ∀ x y : ↥dom,
      (regionGraph (fixedGraph I α ω) (G.connectionGraph α ω) dom).Adj x y →
      ((subBox dom I hdom).connectionGraph (inducedPartition dom I α ω)
        (restrictI I ω)).Reachable x y := by
    intro x y hxy
    rcases hxy with ⟨hne, hcase⟩
    rcases hcase with hA | hB
    · exact SimpleGraph.Adj.reachable ⟨hne, Or.inl hA⟩
    · obtain ⟨-, hwire | ⟨e, he, hjoin⟩⟩ := hB
      · exact SimpleGraph.Adj.reachable ⟨hne, Or.inl
          (SimpleGraph.Adj.reachable ⟨hne ∘ Subtype.ext, Or.inl hwire⟩)⟩
      · by_cases heI : e ∈ I
        · refine SimpleGraph.Adj.reachable ⟨hne, Or.inr ⟨⟨e, heI⟩, he, ?_⟩⟩
          rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
        · have hA' : (fixedGraph I α ω).Adj x.1 y.1 :=
            ⟨hne ∘ Subtype.ext, Or.inr ⟨e, by simp [interiorClosed, heI, he], hjoin⟩⟩
          exact SimpleGraph.Adj.reachable ⟨hne, Or.inl hA'.reachable⟩
  have step₂ : ∀ x y : ↥dom,
      ((subBox dom I hdom).connectionGraph (inducedPartition dom I α ω)
        (restrictI I ω)).Adj x y →
      (regionGraph (fixedGraph I α ω) (G.connectionGraph α ω) dom).Reachable x y := by
    intro x y hxy
    rcases hxy with ⟨hne, hcase⟩
    rcases hcase with hA | ⟨e, he, hjoin⟩
    · exact regionGraph_reachable_of_reachable (A := fixedGraph I α ω)
        (B := G.connectionGraph α ω) (R := dom) x y hA
    · have hB : (G.connectionGraph α ω).Adj x.1 y.1 := by
        refine ⟨hne ∘ Subtype.ext, Or.inr ⟨(e : G.Edge), he, ?_⟩⟩
        rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
        · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
      exact SimpleGraph.Adj.reachable ⟨hne, Or.inr hB⟩
  constructor
  · intro h
    exact reachable_of_adj_reachable (G := regionGraph (fixedGraph I α ω)
      (G.connectionGraph α ω) dom)
      (A := (subBox dom I hdom).connectionGraph (inducedPartition dom I α ω) (restrictI I ω))
      id step₁ h
  · intro h
    exact reachable_of_adj_reachable (G := (subBox dom I hdom).connectionGraph
      (inducedPartition dom I α ω) (restrictI I ω))
      (A := regionGraph (fixedGraph I α ω) (G.connectionGraph α ω) dom) id step₂ h

/-- **The component count of the sub-box conditional law.**  The ambient
component count plus the number of boundary classes equals the sub-box
component count plus the fixed-graph component count. -/
theorem componentCount_split_subBox (α : G.BoundaryPartition) (ω : G.Configuration) :
    G.componentCount α ω +
        Nat.card (wiringGraph (fixedGraph I α ω) dom).ConnectedComponent =
      (subBox dom I hdom).componentCount (inducedPartition dom I α ω) (restrictI I ω) +
        G.componentCount α (interiorClosed I ω) := by
  classical
  have hAB : fixedGraph I α ω ≤ G.connectionGraph α ω :=
    G.connectionGraph_mono (interiorClosed_le I ω)
  have hR : ∀ u v, (G.connectionGraph α ω).Adj u v →
      (fixedGraph I α ω).Adj u v ∨ (u ∈ dom ∧ v ∈ dom) := by
    intro u v huv
    obtain ⟨hne, hwire | ⟨e, he, hjoin⟩⟩ := huv
    · exact Or.inl ⟨hne, Or.inl hwire⟩
    · by_cases heI : e ∈ I
      · refine Or.inr ⟨?_, ?_⟩
        · rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h1 ▸ (hdom ⟨e, heI⟩).1
          · exact h2 ▸ (hdom ⟨e, heI⟩).2
        · rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2 ▸ (hdom ⟨e, heI⟩).2
          · exact h1 ▸ (hdom ⟨e, heI⟩).1
      · exact Or.inl ⟨hne, Or.inr ⟨e, by simp [interiorClosed, heI, he], hjoin⟩⟩
  have h := card_connectedComponent_split hAB hR
  rw [card_components_eq_of_reachable_iff
    (fun x y => regionGraph_reachable_iff_subBox α ω x y)] at h
  exact h

/-- Rebuild an ambient configuration from an interior and an exterior part. -/
noncomputable def combine {G : LabelledMultigraph} (I : Set G.Edge) (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) : G.Configuration :=
  fun e => if h : e ∈ I then ζ ⟨e, h⟩ else ξ ⟨e, h⟩

@[simp] lemma combine_of_mem {G : LabelledMultigraph} (I : Set G.Edge) (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) (e : ↥I) :
    combine I ζ ξ (e : G.Edge) = ζ e := by
  simp only [combine, dif_pos e.2]

@[simp] lemma combine_of_not_mem {G : LabelledMultigraph} (I : Set G.Edge) (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) (e : {e : G.Edge // e ∉ I}) :
    combine I ζ ξ (e : G.Edge) = ξ e := by
  simp only [combine, dif_neg e.2]

@[simp] lemma restrictI_combine {G : LabelledMultigraph} (I : Set G.Edge) (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) : restrictI I (combine I ζ ξ) = ζ := by
  funext e
  exact combine_of_mem I ζ ξ e

lemma interiorClosed_combine {G : LabelledMultigraph} (I : Set G.Edge) (ζ ζ' : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) :
    interiorClosed I (combine I ζ ξ) = interiorClosed I (combine I ζ' ξ) := by
  funext e
  by_cases h : e ∈ I
  · rw [interiorClosed, if_pos h, interiorClosed, if_pos h]
  · rw [interiorClosed, if_neg h, interiorClosed, if_neg h]
    simp only [combine, dif_neg h]

lemma exterior_prod_congr {G : LabelledMultigraph} (I : Set G.Edge) (p : NNReal)
    (ζ ζ' : ↥I → Bool) (ξ : {e : G.Edge // e ∉ I} → Bool) :
    (∏ e : {e : G.Edge // e ∉ I}, (if combine I ζ ξ (e : G.Edge) then p else 1 - p)) =
      ∏ e : {e : G.Edge // e ∉ I}, (if combine I ζ' ξ (e : G.Edge) then p else 1 - p) := by
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [combine_of_not_mem, combine_of_not_mem]

/-- The Bernoulli edge weight splits into the sub-box part and the exterior. -/
theorem edgeWeight_split {G : LabelledMultigraph} {dom : Set G.Vertex} {I : Set G.Edge}
    (hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom)
    (p : NNReal) (ω : G.Configuration) :
    G.edgeWeight p ω = (subBox dom I hdom).edgeWeight p (restrictI I ω) *
      ∏ e : {e : G.Edge // e ∉ I}, (if ω (e : G.Edge) then p else 1 - p) := by
  classical
  rw [LabelledMultigraph.edgeWeight]
  have h : (∏ e : G.Edge, (if ω e then p else 1 - p)) =
      (∏ b : ↥I ⊕ {e : G.Edge // e ∉ I},
        (if ω (Sum.elim (fun a : ↥I => (a : G.Edge))
          (fun a : {e : G.Edge // e ∉ I} => (a : G.Edge)) b) then p else 1 - p)) :=
    (Equiv.prod_comp (Equiv.sumCompl (fun e : G.Edge => e ∈ I))
      (fun e => if ω e then p else 1 - p)).symm
  rw [h, Fintype.prod_sum_type]
  rfl

/-- **The FK weight factorization for a sub-box.**  The ambient weight times the
number of boundary classes is the sub-box weight with the exterior-induced
partition times a constant depending only on the exterior configuration. -/
theorem fkWeight_factorization {G : LabelledMultigraph} {dom : Set G.Vertex}
    {I : Set G.Edge}
    {hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom}
    {q p : NNReal} (α : G.BoundaryPartition) (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) :
    G.fkWeight q p α (combine I ζ ξ) *
        q ^ Nat.card (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent =
      (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ *
        (q ^ G.componentCount α (interiorClosed I (combine I ζ ξ)) *
          ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p)) := by
  classical
  have hcomp := componentCount_split_subBox (dom := dom) (I := I) (hdom := hdom) α
    (combine I ζ ξ)
  rw [restrictI_combine] at hcomp
  have hEW : (∏ e : {e : G.Edge // e ∉ I},
      (if combine I ζ ξ (e : G.Edge) then p else 1 - p)) =
      ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p) := by
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [combine_of_not_mem]
  rw [LabelledMultigraph.fkWeight, edgeWeight_split hdom p (combine I ζ ξ),
    restrictI_combine, hEW, LabelledMultigraph.fkWeight]
  have hk : q ^ G.componentCount α (combine I ζ ξ) *
      q ^ Nat.card (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent =
      q ^ ((subBox dom I hdom).componentCount (inducedPartition dom I α (combine I ζ ξ)) ζ +
        G.componentCount α (interiorClosed I (combine I ζ ξ))) := by
    rw [← pow_add, hcomp]
  have hk2 : q ^ G.componentCount α (combine I ζ ξ) *
      q ^ Nat.card (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent =
      q ^ ((subBox dom I hdom).componentCount (inducedPartition dom I α (combine I ζ ξ)) ζ +
        G.componentCount α (interiorClosed I (combine I ζ ξ))) := by
    rw [← pow_add, hcomp]
  calc ((subBox dom I hdom).edgeWeight p ζ *
        ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p)) *
        q ^ G.componentCount α (combine I ζ ξ) *
        q ^ Nat.card (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent
      = ((subBox dom I hdom).edgeWeight p ζ *
          ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p)) *
          (q ^ G.componentCount α (combine I ζ ξ) *
            q ^ Nat.card (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent) := by
        ring
    _ = ((subBox dom I hdom).edgeWeight p ζ *
          ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p)) *
          q ^ ((subBox dom I hdom).componentCount (inducedPartition dom I α (combine I ζ ξ)) ζ +
            G.componentCount α (interiorClosed I (combine I ζ ξ))) := by rw [hk2]
    _ = (subBox dom I hdom).edgeWeight p ζ *
          q ^ (subBox dom I hdom).componentCount (inducedPartition dom I α (combine I ζ ξ)) ζ *
          (q ^ G.componentCount α (interiorClosed I (combine I ζ ξ)) *
            ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p)) := by
        rw [pow_add]; ring

/-- The fixed graph only sees the closed interior. -/
lemma reachable_fixedGraph_congr {G : LabelledMultigraph} {I : Set G.Edge}
    {α : G.BoundaryPartition} {ω ω' : G.Configuration}
    (h : interiorClosed I ω = interiorClosed I ω') (x y : G.Vertex) :
    (fixedGraph I α ω).Reachable x y ↔ (fixedGraph I α ω').Reachable x y := by
  unfold fixedGraph
  rw [h]

/-- Hence the induced boundary partition only depends on the closed interior. -/
lemma inducedPartition_congr {G : LabelledMultigraph} {dom : Set G.Vertex} {I : Set G.Edge}
    {α : G.BoundaryPartition} {ω ω' : G.Configuration}
    (h : interiorClosed I ω = interiorClosed I ω') :
    inducedPartition dom I α ω = inducedPartition dom I α ω' := by
  apply Setoid.ext
  intro x y
  exact reachable_fixedGraph_congr h x.1 y.1

/-- **The source's §1.3 compatibility relation, in weight form.**  For a fixed
exterior configuration the ambient conditional weights are proportional to the
sub-box FK weights with the exterior-induced partition: the ratio of the two
interior weights is the ratio of the sub-box FK weights.  Since all weights are
strictly positive this is equivalent to the statement that the conditional law
of `ω|Λ` given `ω|(Δ∖Λ)` is `φ^{α'}_Λ`. -/
theorem fkWeight_conditional_ratio {G : LabelledMultigraph} {dom : Set G.Vertex}
    {I : Set G.Edge}
    {hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom}
    {q p : NNReal} (hq : 0 < q) (α : G.BoundaryPartition) (ζ ζ' : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) :
    G.fkWeight q p α (combine I ζ ξ) *
        (subBox dom I hdom).fkWeight q p
          (inducedPartition dom I α (combine I ζ ξ)) ζ' =
      G.fkWeight q p α (combine I ζ' ξ) *
        (subBox dom I hdom).fkWeight q p
          (inducedPartition dom I α (combine I ζ ξ)) ζ := by
  classical
  -- the two factorizations share the same boundary classes and the same constant
  have h2 := fkWeight_factorization (dom := dom) (I := I) (hdom := hdom) (q := q) (p := p)
    α ζ' ξ
  have hclose : interiorClosed I (combine I ζ' ξ) = interiorClosed I (combine I ζ ξ) :=
    interiorClosed_combine I ζ' ζ ξ
  have hπ : inducedPartition dom I α (combine I ζ' ξ) =
      inducedPartition dom I α (combine I ζ ξ) := inducedPartition_congr hclose
  have hc : G.componentCount α (interiorClosed I (combine I ζ' ξ)) =
      G.componentCount α (interiorClosed I (combine I ζ ξ)) := by rw [hclose]
  have hb : Nat.card (wiringGraph (fixedGraph I α (combine I ζ' ξ)) dom).ConnectedComponent =
      Nat.card (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent := by
    unfold fixedGraph
    rw [hclose]
  have he : (∏ e : {e : G.Edge // e ∉ I},
      (if combine I ζ' ξ (e : G.Edge) then p else 1 - p)) =
      ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p) := by
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [combine_of_not_mem]
  rw [hπ, hc, hb] at h2
  have h1 := fkWeight_factorization (dom := dom) (I := I) (hdom := hdom) (q := q) (p := p)
    α ζ ξ
  have hq0 : (q : NNReal) ^ Nat.card
      (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent ≠ 0 :=
    pow_ne_zero _ (ne_of_gt hq)
  refine mul_right_cancel₀ hq0 ?_
  calc G.fkWeight q p α (combine I ζ ξ) *
        (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ'
        * (q : NNReal) ^ Nat.card
          (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent
      = (G.fkWeight q p α (combine I ζ ξ) * (q : NNReal) ^ Nat.card
          (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent) *
          (subBox dom I hdom).fkWeight q p
            (inducedPartition dom I α (combine I ζ ξ)) ζ' := by ring
    _ = ((subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ *
          (q ^ G.componentCount α (interiorClosed I (combine I ζ ξ)) *
            ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p))) *
          (subBox dom I hdom).fkWeight q p
            (inducedPartition dom I α (combine I ζ ξ)) ζ' := by rw [h1]
    _ = ((subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ' *
          (q ^ G.componentCount α (interiorClosed I (combine I ζ ξ)) *
            ∏ e : {e : G.Edge // e ∉ I}, (if ξ e then p else 1 - p))) *
          (subBox dom I hdom).fkWeight q p
            (inducedPartition dom I α (combine I ζ ξ)) ζ := by ring
    _ = (G.fkWeight q p α (combine I ζ' ξ) * (q : NNReal) ^ Nat.card
          (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent) *
          (subBox dom I hdom).fkWeight q p
            (inducedPartition dom I α (combine I ζ ξ)) ζ := by rw [h2]
    _ = G.fkWeight q p α (combine I ζ' ξ) *
        (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ
        * (q : NNReal) ^ Nat.card
          (wiringGraph (fixedGraph I α (combine I ζ ξ)) dom).ConnectedComponent := by ring

/-- **The source's §1.3 compatibility relation.**  For every exterior
configuration `ξ`, the weighted conditional law of the interior given `ξ` is
exactly the sub-box FK law with the exterior-induced boundary partition: the
Bayes identity below says that the conditional weights and the sub-box weights
have the same total mass ratio.  All weights are strictly positive, so this is
equivalent to the conditional-law statement `φ^{α'}_Λ`. -/
theorem fkWeight_conditional_bayes {G : LabelledMultigraph} {dom : Set G.Vertex}
    {I : Set G.Edge}
    {hdom : ∀ e : ↥I, G.source (e : G.Edge) ∈ dom ∧ G.target (e : G.Edge) ∈ dom}
    {q p : NNReal} (hq : 0 < q) (α : G.BoundaryPartition) (ζ : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) :
    (∑ ζ' : ↥I → Bool, G.fkWeight q p α (combine I ζ' ξ)) *
        (subBox dom I hdom).fkWeight q p
          (inducedPartition dom I α (combine I ζ ξ)) ζ =
      G.fkWeight q p α (combine I ζ ξ) *
        ∑ ζ' : ↥I → Bool, (subBox dom I hdom).fkWeight q p
          (inducedPartition dom I α (combine I ζ ξ)) ζ' := by
  classical
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ζ' _ => (fkWeight_conditional_ratio hq α ζ ζ' ξ).symm)

/-- **The source's §1.3 conditional law at the level of the actual FK PMF.**
For every fixed exterior `ξ`, the ratio of the PMF masses of two glued
configurations equals the ratio of the sub-box FK masses of their interiors,
under the exterior-induced partition.  Since all masses are positive this is
exactly "the conditional law of `ω|Λ` given `ω|(Δ∖Λ) = η` is `φ^{α'}_Λ`". -/
theorem fkPMF_conditional_ratio {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p)
    (hp₁ : p < 1) (α : G.BoundaryPartition) (ζ ζ' : ↥I → Bool)
    (ξ : {e : G.Edge // e ∉ I} → Bool) :
    (G.fkPMF hq hp₁.le α) (combine I ζ ξ) *
        ((subBox dom I hdom).fkPMF hq hp₁.le
          (inducedPartition dom I α (combine I ζ ξ))) ζ' =
      (G.fkPMF hq hp₁.le α) (combine I ζ' ξ) *
        ((subBox dom I hdom).fkPMF hq hp₁.le
          (inducedPartition dom I α (combine I ζ ξ))) ζ := by
  classical
  have hZ : (G.partitionFunction q p α : NNReal) ≠ 0 :=
    (G.partitionFunction_pos hq hp₁.le α).ne'
  have hZs : ((subBox dom I hdom).partitionFunction q p
      (inducedPartition dom I α (combine I ζ ξ)) : NNReal) ≠ 0 :=
    ((subBox dom I hdom).partitionFunction_pos hq hp₁.le _).ne'
  have key : ((G.fkWeight q p α (combine I ζ ξ) / G.partitionFunction q p α) *
        ((subBox dom I hdom).fkWeight q p
          (inducedPartition dom I α (combine I ζ ξ)) ζ' /
          (subBox dom I hdom).partitionFunction q p
            (inducedPartition dom I α (combine I ζ ξ))) : NNReal) =
      (G.fkWeight q p α (combine I ζ' ξ) / G.partitionFunction q p α) *
        ((subBox dom I hdom).fkWeight q p
          (inducedPartition dom I α (combine I ζ ξ)) ζ /
          (subBox dom I hdom).partitionFunction q p
            (inducedPartition dom I α (combine I ζ ξ))) := by
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero hZ hZs) (mul_ne_zero hZ hZs)]
    calc G.fkWeight q p α (combine I ζ ξ) *
          (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ' *
          (G.partitionFunction q p α *
            (subBox dom I hdom).partitionFunction q p
              (inducedPartition dom I α (combine I ζ ξ)))
        = (G.fkWeight q p α (combine I ζ ξ) *
            (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ') *
            (G.partitionFunction q p α *
              (subBox dom I hdom).partitionFunction q p
                (inducedPartition dom I α (combine I ζ ξ))) := by ring
      _ = (G.fkWeight q p α (combine I ζ' ξ) *
            (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ) *
            (G.partitionFunction q p α *
              (subBox dom I hdom).partitionFunction q p
                (inducedPartition dom I α (combine I ζ ξ))) := by
          rw [fkWeight_conditional_ratio (dom := dom) (I := I) (hdom := hdom) hq α ζ ζ' ξ]
      _ = G.fkWeight q p α (combine I ζ' ξ) *
            (subBox dom I hdom).fkWeight q p (inducedPartition dom I α (combine I ζ ξ)) ζ *
            (G.partitionFunction q p α *
              (subBox dom I hdom).partitionFunction q p
                (inducedPartition dom I α (combine I ζ ξ))) := by ring
  simp only [LabelledMultigraph.fkPMF_apply, ← ENNReal.coe_mul]
  exact_mod_cast key

/-- **The induced partition respects open exterior paths.**  This is the
paper's first compatibility requirement on a convention: any two region
vertices connected by an open path outside the region are in the same block of
`π(α,η)`.  (`G.connectionGraph ⊥ (interiorClosed I ω)` is the exterior-open
connection graph: every interior edge is closed and no boundary wiring is
added.) -/
theorem exteriorReachable_inducedPartition {G : LabelledMultigraph} {dom : Set G.Vertex}
    {I : Set G.Edge} {α : G.BoundaryPartition} (ω : G.Configuration) {x y : ↥dom}
    (h : (G.connectionGraph (⊥ : G.BoundaryPartition)
      (interiorClosed I ω)).Reachable x.1 y.1) :
    (inducedPartition dom I α ω).r x y := by
  refine SimpleGraph.Reachable.mono ?_ h
  rintro u v ⟨hne, hcase | hcase⟩
  · subst hcase
    exact ⟨hne, Or.inl (α.iseqv.refl u)⟩
  · exact ⟨hne, Or.inr hcase⟩

end FKMain

/-- The induced partition is monotone in the exterior configuration. -/
theorem inducedPartition_mono {G : LabelledMultigraph} {dom : Set G.Vertex}
    {I : Set G.Edge} {α : G.BoundaryPartition} {ω ω' : G.Configuration}
    (h : interiorClosed I ω ≤ interiorClosed I ω') :
    inducedPartition dom I α ω ≤ inducedPartition dom I α ω' := by
  intro x y hxy
  exact SimpleGraph.Reachable.mono (G.connectionGraph_mono h) hxy

/-- **The induced partition depends only on the exterior configuration.**  The
interior bits are irrelevant: this is the exact content of `π(α,η)`, and it is
what makes the conditional law an FK law rather than an arbitrary kernel. -/
theorem inducedPartition_combine_eq {G : LabelledMultigraph} {dom : Set G.Vertex}
    {I : Set G.Edge} {α : G.BoundaryPartition} (ω : G.Configuration)
    (ζ : ↥I → Bool) :
    inducedPartition dom I α (combine I ζ (fun e => ω (e : G.Edge))) =
      inducedPartition dom I α ω := by
  apply inducedPartition_congr
  funext e
  by_cases h : e ∈ I
  · rw [interiorClosed, if_pos h, interiorClosed, if_pos h]
  · rw [interiorClosed, if_neg h, interiorClosed, if_neg h]
    simp only [combine, dif_neg h]

/-! ## Axiom audit -/

#print axioms FK.Finite.SpecificationNesting.card_components_eq_of_reachable_iff
#print axioms FK.Finite.SpecificationNesting.card_connectedComponent_split
#print axioms FK.Finite.SpecificationNesting.regionGraph_reachable_iff_subBox
#print axioms FK.Finite.SpecificationNesting.componentCount_split_subBox
#print axioms FK.Finite.SpecificationNesting.fkWeight_factorization
#print axioms FK.Finite.SpecificationNesting.fkWeight_conditional_ratio
#print axioms FK.Finite.SpecificationNesting.fkWeight_conditional_bayes
#print axioms FK.Finite.SpecificationNesting.inducedPartition_combine_eq
#print axioms FK.Finite.SpecificationNesting.fkPMF_conditional_ratio
#print axioms FK.Finite.SpecificationNesting.exteriorReachable_inducedPartition

end FK.Finite.SpecificationNesting