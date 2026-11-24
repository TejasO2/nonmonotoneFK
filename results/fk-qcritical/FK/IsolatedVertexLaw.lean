import FK.EdgeDomainMonotonicity
import FK.FiniteGraphTransport
import FK.InfiniteVolume

/-!
# Isolated-vertex invariance of the actual finite free FK law

Take a finite labelled multigraph on a vertex type `V` (loops and parallel
labels allowed, free boundary) and the graph on `V ⊕ X` with *exactly the same*
edge labels and endpoints carried into the left summand by `Sum.inl`.  The
configuration space is literally the same type `E → Bool`, and we prove:

* the free component counts differ by the constant `Nat.card X`;
* the FK weights differ by the constant factor `q ^ Nat.card X`;
* the partition functions differ by the same constant;
* the actual normalized PMFs and probability measures are **equal**.

The boundary result is stated for an arbitrary boundary setoid `ξ` on `V`
carried over to `V ⊕ X` with all new vertices free (`setoidSumInl`), which
specialises to free boundary on both sides.  A counterexample at the end shows
that a boundary setoid on `V ⊕ X` which relates a new vertex to an old one
breaks the constant component-count shift, hence the proportionality of
weights, so that hypothesis cannot be dropped.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

attribute [local instance] Classical.propDecidable Classical.decPred

namespace FK.InfiniteVolume.NoEscape

open FK.Finite

universe u

variable {V : Type*}

/-! ## The carried boundary setoid -/

/-- The boundary setoid on `V ⊕ X` that carries `ξ` on the old vertices and
leaves every vertex of `X` free: no relation touches the right summand. -/
def setoidSumInl (ξ : Setoid V) (X : Type) : Setoid (V ⊕ X) where
  r u v := u = v ∨ ∃ a b : V, u = Sum.inl a ∧ v = Sum.inl b ∧ ξ.r a b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro u; exact Or.inl rfl
    · rintro u v (h | ⟨a, b, ha, hb, h⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨b, a, hb, ha, ξ.iseqv.symm h⟩
    · rintro u v w (h₁ | ⟨a, b, ha, hb, h₁⟩) (h₂ | ⟨c, d, hc, hd, h₂⟩)
      · exact Or.inl (h₁.trans h₂)
      · exact Or.inr ⟨c, d, h₁.trans hc, hd, h₂⟩
      · exact Or.inr ⟨a, b, ha, h₂ ▸ hb, h₁⟩
      · have hbc : b = c := Sum.inl.inj (hb.symm.trans hc)
        subst hbc
        exact Or.inr ⟨a, d, ha, hd, ξ.iseqv.trans h₁ h₂⟩

@[simp] lemma setoidSumInl_r {ξ : Setoid V} {X : Type} {a b : V} :
    (setoidSumInl ξ X).r (Sum.inl a) (Sum.inl b) ↔ ξ.r a b := by
  constructor
  · rintro (h | ⟨a', b', ha, hb, h⟩)
    · simp only [Sum.inl.injEq] at h
      subst h; exact ξ.iseqv.refl a
    · simp only [Sum.inl.injEq] at ha hb
      subst ha; subst hb; exact h
  · intro h; exact Or.inr ⟨a, b, rfl, rfl, h⟩

/-- With `ξ = ⊥` the carried setoid is exactly free boundary. -/
lemma setoidSumInl_bot (X : Type) : setoidSumInl (⊥ : Setoid V) X = ⊥ := by
  refine Setoid.ext ?_
  intro u v
  constructor
  · rintro (h | ⟨a, b, rfl, rfl, hab⟩)
    · exact h
    · exact by simpa using hab
  · intro h
    exact Or.inl h

/-! ## The induced graph on the old vertex set is the old connection graph -/

/-- The canonical identification of the left summand `Set.range Sum.inl` with
`V`. -/
noncomputable def rangeInlEquiv (X : Type) :
    {w : V ⊕ X // w ∈ Set.range (Sum.inl : V → V ⊕ X)} ≃ V :=
  (Equiv.ofInjective (Sum.inl : V → V ⊕ X) Sum.inl_injective).symm

/-- The defining property of `rangeInlEquiv`. -/
lemma rangeInlEquiv_apply_coe (X : Type)
    (w : {w : V ⊕ X // w ∈ Set.range (Sum.inl : V → V ⊕ X)}) :
    Sum.inl (rangeInlEquiv X w) = w.1 := by
  have h : (Equiv.ofInjective (Sum.inl : V → V ⊕ X) Sum.inl_injective) (rangeInlEquiv X w) = w :=
    Equiv.apply_symm_apply _ w
  simpa using congrArg Subtype.val h

@[simp] lemma rangeInlEquiv_inl (X : Type) (a : V) :
    rangeInlEquiv X ⟨Sum.inl a, ⟨a, rfl⟩⟩ = a :=
  Equiv.ofInjective_symm_apply Sum.inl_injective a

variable [Fintype V]

/-! ## The vertex extension and the graph isomorphism -/

/-- The labelled multigraph on `V ⊕ X` whose edge labels and endpoints are
those of `fgOf E src tgt`, with every endpoint carried into the left summand. -/
@[reducible] def fgSumInl (X : Type) [Fintype X] (E : Type) [Fintype E]
    (src tgt : E → V) : FK.Finite.LabelledMultigraph where
  Vertex := V ⊕ X
  Edge := E
  source := fun e => Sum.inl (src e)
  target := fun e => Sum.inl (tgt e)

variable {E : Type} [Fintype E] {src tgt : E → V}

/-- The graph induced on the old vertices by the extended connection graph is
the old connection graph. -/
noncomputable def inducedConnectionIso (X : Type) [Fintype X] (ξ : Setoid V)
    (ω : E → Bool) :
    SimpleGraph.induce (Set.range (Sum.inl : V → V ⊕ X))
        ((fgSumInl X E src tgt).connectionGraph (setoidSumInl ξ X) ω) ≃g
      (fgOf E src tgt).connectionGraph ξ ω where
  toEquiv := rangeInlEquiv X
  map_rel_iff' := by
    intro u v
    rw [SimpleGraph.induce_adj]
    constructor
    · -- adjacency of the old graph gives adjacency of the extended graph
      rintro ⟨huv, hw⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply huv
        exact Sum.inl.inj (by
          rw [rangeInlEquiv_apply_coe X u, rangeInlEquiv_apply_coe X v, h])
      · rcases hw with hab | ⟨e, he, hjoin⟩
        · refine Or.inl (Or.inr ⟨rangeInlEquiv X u, rangeInlEquiv X v, ?_, ?_, hab⟩)
          · exact (rangeInlEquiv_apply_coe X u).symm
          · exact (rangeInlEquiv_apply_coe X v).symm
        · refine Or.inr ⟨e, he, ?_⟩
          rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine Or.inl ⟨?_, ?_⟩
            · show Sum.inl (src e) = u.1
              rw [show src e = rangeInlEquiv X u from h1, rangeInlEquiv_apply_coe X u]
            · show Sum.inl (tgt e) = v.1
              rw [show tgt e = rangeInlEquiv X v from h2, rangeInlEquiv_apply_coe X v]
          · refine Or.inr ⟨?_, ?_⟩
            · show Sum.inl (src e) = v.1
              rw [show src e = rangeInlEquiv X v from h1, rangeInlEquiv_apply_coe X v]
            · show Sum.inl (tgt e) = u.1
              rw [show tgt e = rangeInlEquiv X u from h2, rangeInlEquiv_apply_coe X u]
    · -- adjacency of the extended graph restricts to the old graph
      rintro ⟨huv, hw | ⟨e, he, hjoin⟩⟩
      · change u.1 = v.1 ∨ (∃ a b : V, u.1 = Sum.inl a ∧ v.1 = Sum.inl b ∧ ξ.r a b) at hw
        rcases hw with huv' | ⟨a, b, ha, hb, hab⟩
        · exact absurd huv' huv
        · have hua : rangeInlEquiv X u = a := Sum.inl.inj (by rw [rangeInlEquiv_apply_coe X u, ha])
          have hvb : rangeInlEquiv X v = b := Sum.inl.inj (by rw [rangeInlEquiv_apply_coe X v, hb])
          rw [hua, hvb]
          exact ⟨fun h => huv (by rw [ha, hb, h]), Or.inl hab⟩
      · refine ⟨?_, Or.inr ⟨e, he, ?_⟩⟩
        · intro h
          apply huv
          rw [← rangeInlEquiv_apply_coe X u, ← rangeInlEquiv_apply_coe X v, h]
        · rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Sum.inl.inj (h1.trans (rangeInlEquiv_apply_coe X u).symm),
              Sum.inl.inj (h2.trans (rangeInlEquiv_apply_coe X v).symm)⟩
          · exact Or.inr ⟨Sum.inl.inj (h1.trans (rangeInlEquiv_apply_coe X v).symm),
              Sum.inl.inj (h2.trans (rangeInlEquiv_apply_coe X u).symm)⟩


/-! ## Cardinality of the new vertex set and the component count -/

/-- The complement of the left summand is canonically the right summand. -/
noncomputable def complRangeInlEquiv (X : Type) :
    {v : V ⊕ X // v ∉ Set.range (Sum.inl : V → V ⊕ X)} ≃ X :=
  (Equiv.ofBijective
    (fun x : X => (⟨Sum.inr x, by simp⟩ :
      {v : V ⊕ X // v ∉ Set.range (Sum.inl : V → V ⊕ X)}))
    ⟨fun x y h => by simpa using h, by
      rintro ⟨v, hv⟩
      cases v with
      | inl a => exact absurd (Set.mem_range_self a) hv
      | inr x => exact ⟨x, Subtype.ext rfl⟩⟩).symm

omit [Fintype V] in
@[simp] lemma natCard_compl_range_inl (X : Type) [Fintype X] :
    Nat.card {v : V ⊕ X // v ∉ Set.range (Sum.inl : V → V ⊕ X)} = Nat.card X :=
  Nat.card_congr (complRangeInlEquiv X)

/-- The component count of the extended free (or carried-boundary) graph is the
old component count plus the number of new, isolated vertices. -/
theorem componentCount_sumInl (X : Type) [Fintype X] (ξ : Setoid V) (ω : E → Bool) :
    (fgSumInl X E src tgt).componentCount (setoidSumInl ξ X) ω
      = (fgOf E src tgt).componentCount ξ ω + Nat.card X := by
  classical
  have ht : ∀ u v : V ⊕ X,
      ((fgSumInl X E src tgt).connectionGraph (setoidSumInl ξ X) ω).Adj u v →
      u ∈ Set.range (Sum.inl : V → V ⊕ X) ∧ v ∈ Set.range (Sum.inl : V → V ⊕ X) := by
    intro u v huv
    constructor
    · rcases huv.2 with hw | ⟨e, he, hjoin⟩
      · change u = v ∨ (∃ a b : V, u = Sum.inl a ∧ v = Sum.inl b ∧ ξ.r a b) at hw
        rcases hw with h | ⟨a, b, ha, hb, -⟩
        · exact absurd h huv.1
        · exact ⟨a, ha.symm⟩
      · rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨src e, h1⟩
        · exact ⟨tgt e, h2⟩
    · rcases huv.2 with hw | ⟨e, he, hjoin⟩
      · change u = v ∨ (∃ a b : V, u = Sum.inl a ∧ v = Sum.inl b ∧ ξ.r a b) at hw
        rcases hw with h | ⟨a, b, ha, hb, -⟩
        · exact absurd h huv.1
        · exact ⟨b, hb.symm⟩
      · rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨tgt e, h2⟩
        · exact ⟨src e, h1⟩
  have hcard := card_connectedComponent_induce_add
    (H := (fgSumInl X E src tgt).connectionGraph (setoidSumInl ξ X) ω)
    (t := Set.range (Sum.inl : V → V ⊕ X)) ht
  unfold LabelledMultigraph.componentCount
  rw [hcard, Nat.card_congr (inducedConnectionIso (V := V) X ξ ω).connectedComponentEquiv,
    natCard_compl_range_inl]

/-! ## Weights, partition function and the normalized law -/

@[simp] theorem edgeWeight_sumInl (X : Type) [Fintype X] (p : NNReal) (ω : E → Bool) :
    (fgSumInl X E src tgt).edgeWeight p ω = (fgOf E src tgt).edgeWeight p ω := rfl

/-- The FK weight of the extended graph is the old weight times the constant
`q ^ Nat.card X`. -/
theorem fkWeight_sumInl (X : Type) [Fintype X] (ξ : Setoid V) (q p : NNReal)
    (ω : E → Bool) :
    (fgSumInl X E src tgt).fkWeight q p (setoidSumInl ξ X) ω
      = (fgOf E src tgt).fkWeight q p ξ ω * q ^ Nat.card X := by
  unfold LabelledMultigraph.fkWeight
  rw [componentCount_sumInl, edgeWeight_sumInl, pow_add]
  ring

/-- The partition function of the extended graph is the old partition function
times the same constant. -/
theorem partitionFunction_sumInl (X : Type) [Fintype X] (ξ : Setoid V) (q p : NNReal) :
    (fgSumInl X E src tgt).partitionFunction q p (setoidSumInl ξ X)
      = (fgOf E src tgt).partitionFunction q p ξ * q ^ Nat.card X := by
  classical
  unfold LabelledMultigraph.partitionFunction
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => fkWeight_sumInl X ξ q p ω)

/-- The actual normalized FK PMFs of the two graphs coincide. -/
theorem fkPMF_sumInl (X : Type) [Fintype X] (ξ : Setoid V) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) :
    (fgSumInl X E src tgt).fkPMF hq hp (setoidSumInl ξ X)
      = (fgOf E src tgt).fkPMF hq hp ξ := by
  classical
  ext ω
  rw [LabelledMultigraph.fkPMF_apply, LabelledMultigraph.fkPMF_apply,
    fkWeight_sumInl, partitionFunction_sumInl]
  have hc : q ^ Nat.card X ≠ 0 := pow_ne_zero _ hq.ne'
  rw [mul_div_mul_right _ _ hc]

/-- **The isolated-vertex invariance of the actual normalized finite FK law.**
Adding finitely many new, completely free vertices and keeping exactly the same
labelled edges (endpoints carried by `Sum.inl`) does not change the law on the
configuration space `E → Bool`. -/
theorem fkMeasure_sumInl (X : Type) [Fintype X] (ξ : Setoid V) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) :
    (fgSumInl X E src tgt).fkMeasure hq hp (setoidSumInl ξ X)
      = (fgOf E src tgt).fkMeasure hq hp ξ := by
  unfold LabelledMultigraph.fkMeasure
  rw [fkPMF_sumInl X ξ hq hp]

/-- Free boundary version: the free FK law is invariant under adding isolated
vertices. -/
theorem fkMeasure_sumInl_free (X : Type) [Fintype X] {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) :
    (fgSumInl X E src tgt).fkMeasure hq hp (⊥ : Setoid (V ⊕ X))
      = (fgOf E src tgt).fkMeasure hq hp (⊥ : Setoid V) := by
  rw [← setoidSumInl_bot (V := V) X]
  exact fkMeasure_sumInl X ⊥ hq hp

/-- Event-level form of the general (carried boundary) invariance. -/
theorem fkMeasure_sumInl_apply (X : Type) [Fintype X] (ξ : Setoid V) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (A : Set (E → Bool)) :
    (fgSumInl X E src tgt).fkMeasure hq hp (setoidSumInl ξ X) A
      = (fgOf E src tgt).fkMeasure hq hp ξ A := by
  rw [fkMeasure_sumInl X ξ hq hp]

/-- Event-level form of the free-boundary invariance. -/
theorem fkMeasure_sumInl_free_apply (X : Type) [Fintype X] {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (A : Set (E → Bool)) :
    (fgSumInl X E src tgt).fkMeasure hq hp (⊥ : Setoid (V ⊕ X)) A
      = (fgOf E src tgt).fkMeasure hq hp (⊥ : Setoid V) A := by
  rw [fkMeasure_sumInl_free X hq hp]


/-! ## The `FiniteBox`/`finiteVolumeLaw` form

The genuine `FiniteBox` of `FK.InfiniteVolume` keeps its boundary setoid on the
box's own vertex type.  Adding isolated vertices to a box therefore gives a box
with vertex type `B.Vertex ⊕ X`, the *same* `Finset` of global edge labels and
endpoints carried by `Sum.inl`; the interior configuration type is literally
unchanged, so the interior FK measures and the finite-volume laws agree. -/

section FiniteBox

variable {E : Type}

/-- Add finitely many new, isolated vertices to a finite box, keeping exactly
the same global edge labels. -/
abbrev _root_.FK.InfiniteVolume.FiniteBox.extendVertices (B : FiniteBox E) (X : Type) [Fintype X] :
    FiniteBox E where
  Vertex := B.Vertex ⊕ X
  edges := B.edges
  source := fun e => Sum.inl (B.source e)
  target := fun e => Sum.inl (B.target e)

variable (B : FiniteBox E) (X : Type) [Fintype X]

/-- The graph of the isolated-vertex extension is the `fgSumInl` graph. -/
lemma extendVertices_graph :
    (B.extendVertices X).graph = fgSumInl X ↥B.edges B.source B.target := rfl

/-- The interior FK measures agree: the interior configuration type is
unchanged and the free laws are equal by `fkMeasure_sumInl_free`. -/
theorem interiorFKMeasure_extendVertices {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (η : B.Exterior) :
    ((B.extendVertices X).interiorFKMeasure hq hp (fun _ => ⊥) η : Measure (↥B.edges → Bool))
      = (B.interiorFKMeasure hq hp (fun _ => ⊥) η : Measure (↥B.edges → Bool)) := by
  show (fgSumInl X ↥B.edges B.source B.target).fkMeasure hq hp (⊥ : Setoid (B.Vertex ⊕ X))
      = (fgOf ↥B.edges B.source B.target).fkMeasure hq hp (⊥ : Setoid B.Vertex)
  exact fkMeasure_sumInl_free (V := B.Vertex) (E := ↥B.edges) (src := B.source) (tgt := B.target)
    X hq hp

/-- The interior restriction map is the same function for the box and for its
isolated-vertex extension. -/
lemma interiorRestriction_extendVertices :
    (B.extendVertices X).interiorRestriction = B.interiorRestriction := rfl

/-- The actual finite-volume laws of a box and of its isolated-vertex
extension agree, as measures on the common global configuration space. -/
theorem finiteVolumeLaw_extendVertices {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    ((B.extendVertices X).finiteVolumeLaw hq hp ⊥ : Measure (Configuration E))
      = (B.finiteVolumeLaw hq hp ⊥ : Measure (Configuration E)) := by
  have hg : ((B.extendVertices X).graph.fkMeasure hq hp (⊥ : Setoid (B.Vertex ⊕ X)) :
        Measure (↥B.edges → Bool))
      = (B.graph.fkMeasure hq hp (⊥ : Setoid B.Vertex) : Measure (↥B.edges → Bool)) := by
    show (fgSumInl X ↥B.edges B.source B.target).fkMeasure hq hp (⊥ : Setoid (B.Vertex ⊕ X))
      = (fgOf ↥B.edges B.source B.target).fkMeasure hq hp (⊥ : Setoid B.Vertex)
    exact fkMeasure_sumInl_free (V := B.Vertex) (E := ↥B.edges) (src := B.source) (tgt := B.target)
      X hq hp
  have hglue : (fun ω => (B.extendVertices X).glue ((B.extendVertices X).closedExterior, ω))
      = (fun ω => B.glue (B.closedExterior, ω)) := rfl
  simp only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw]
  change Measure.map (fun ω => (B.extendVertices X).glue ((B.extendVertices X).closedExterior, ω))
      ((B.extendVertices X).graph.fkMeasure hq hp ⊥)
    = Measure.map (fun ω => B.glue (B.closedExterior, ω)) (B.graph.fkMeasure hq hp ⊥)
  rw [hg, hglue]

/-- Event-level form of `finiteVolumeLaw_extendVertices`. -/
theorem finiteVolumeLaw_extendVertices_apply {q p : NNReal} (hq : 0 < q)
    (hp : p ≤ 1) (A : Set (Configuration E)) :
    ((B.extendVertices X).finiteVolumeLaw hq hp ⊥ : Measure (Configuration E)) A
      = (B.finiteVolumeLaw hq hp ⊥ : Measure (Configuration E)) A := by
  rw [finiteVolumeLaw_extendVertices B X hq hp]


/-! ## The boundary hypothesis is needed: a wired counterexample

The theorem above requires the boundary setoid on `V ⊕ X` to leave the new
vertices free.  With a boundary setoid that merges new vertices into old
components the component-count shift is no longer constant, so the constant
proportionality of weights -- and hence the measure identity -- fails.  The
cheapest instance is the one-edge graph on two vertices with the *wired*
boundary on `V ⊕ X` versus the free boundary on `V`.
-/

section Counterexample

/-- The one-edge graph on two vertices. -/
abbrev ceSmall : LabelledMultigraph.{0, 0} := fgOf Unit (fun _ => (0 : Fin 2)) (fun _ => 1)

/-- The same edge on `Fin 2 ⊕ Unit`, all endpoints in the left summand. -/
abbrev ceBig : LabelledMultigraph.{0, 0} :=
  fgSumInl Unit Unit (fun _ => (0 : Fin 2)) (fun _ => 1)

/-- The wired boundary makes the extended graph a single component at every
configuration. -/
lemma ceBig_componentCount (ω : Unit → Bool) : ceBig.componentCount ceBig.wiredBoundary ω = 1 :=
  LabelledMultigraph.componentCount_wired ceBig ω

/-- With the free boundary the all-closed configuration has one component per
vertex. -/
lemma ceSmall_componentCount_closed :
    ceSmall.componentCount ceSmall.freeBoundary (fun _ => false) = 2 := by
  have h : ceSmall.componentCount ceSmall.freeBoundary (fun _ => false)
      = ceSmall.componentCount ceSmall.freeBoundary ceSmall.allClosed := rfl
  rw [h, LabelledMultigraph.componentCount_free_allClosed]
  simp

/-- The two-vertex one-edge graph is connected once its single edge is open. -/
lemma ceSmall_preconnected :
    (ceSmall.connectionGraph ceSmall.freeBoundary ceSmall.allOpen).Preconnected := by
  intro u v
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl u
  · refine SimpleGraph.Adj.reachable (show (ceSmall.connectionGraph ceSmall.freeBoundary
      ceSmall.allOpen).Adj u v from ⟨huv, Or.inr ⟨(), rfl, ?_⟩⟩)
    fin_cases u <;> fin_cases v <;>
      simp_all [ceSmall, fgOf, LabelledMultigraph.Joins]

lemma ceSmall_componentCount_open :
    ceSmall.componentCount ceSmall.freeBoundary (fun _ => true) = 1 := by
  have h : ceSmall.componentCount ceSmall.freeBoundary (fun _ => true)
      = ceSmall.componentCount ceSmall.freeBoundary ceSmall.allOpen := rfl
  rw [h]
  unfold LabelledMultigraph.componentCount
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨ceSmall_preconnected.subsingleton_connectedComponent, inferInstance⟩

/-- The component-count shift is not the constant `Nat.card X` for the wired
boundary. -/
theorem componentCount_shift_fails_wired :
    ceBig.componentCount ceBig.wiredBoundary ceBig.allClosed
      ≠ ceSmall.componentCount ceSmall.freeBoundary (fun _ => false) + Nat.card Unit := by
  have h : ceBig.componentCount ceBig.wiredBoundary ceBig.allClosed
      = ceBig.componentCount ceBig.wiredBoundary (fun _ => false) := rfl
  rw [h, ceBig_componentCount, ceSmall_componentCount_closed]
  simp

lemma one_sub_half : (1 : NNReal) - 2⁻¹ = 2⁻¹ := by
  rw [← NNReal.coe_inj]
  push_cast
  norm_num

lemma ceBig_edgeWeight_closed :
    ceBig.edgeWeight (1 / 2) (fun _ => false) = 1 / 2 := by
  unfold LabelledMultigraph.edgeWeight
  rw [Finset.univ_unique, Finset.prod_singleton]
  simp [one_sub_half]

lemma ceSmall_edgeWeight_closed :
    ceSmall.edgeWeight (1 / 2) (fun _ => false) = 1 / 2 := by
  unfold LabelledMultigraph.edgeWeight
  rw [Finset.univ_unique, Finset.prod_singleton]
  simp [one_sub_half]

lemma ceBig_edgeWeight_open :
    ceBig.edgeWeight (1 / 2) (fun _ => true) = 1 / 2 := by
  unfold LabelledMultigraph.edgeWeight
  rw [Finset.univ_unique, Finset.prod_singleton]
  norm_num

lemma ceSmall_edgeWeight_open :
    ceSmall.edgeWeight (1 / 2) (fun _ => true) = 1 / 2 := by
  unfold LabelledMultigraph.edgeWeight
  rw [Finset.univ_unique, Finset.prod_singleton]
  norm_num

lemma ceBig_fkWeight_closed :
    ceBig.fkWeight 2 (1 / 2) ceBig.wiredBoundary (fun _ => false) = 1 := by
  unfold LabelledMultigraph.fkWeight
  rw [ceBig_componentCount, ceBig_edgeWeight_closed]
  norm_num

lemma ceSmall_fkWeight_closed :
    ceSmall.fkWeight 2 (1 / 2) ceSmall.freeBoundary (fun _ => false) = 2 := by
  unfold LabelledMultigraph.fkWeight
  rw [ceSmall_componentCount_closed, ceSmall_edgeWeight_closed]
  norm_num

lemma ceBig_fkWeight_open :
    ceBig.fkWeight 2 (1 / 2) ceBig.wiredBoundary (fun _ => true) = 1 := by
  unfold LabelledMultigraph.fkWeight
  rw [ceBig_componentCount, ceBig_edgeWeight_open]
  norm_num

lemma ceSmall_fkWeight_open :
    ceSmall.fkWeight 2 (1 / 2) ceSmall.freeBoundary (fun _ => true) = 1 := by
  unfold LabelledMultigraph.fkWeight
  rw [ceSmall_componentCount_open, ceSmall_edgeWeight_open]
  norm_num

/-- The two configurations of `Unit → Bool`. -/
lemma univ_unit_bool : (Finset.univ : Finset (Unit → Bool)) = {fun _ => false, fun _ => true} := by
  ext f
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  by_cases h : f () = true
  · right
    funext x
    cases x
    simpa using h
  · left
    funext x
    cases x
    simp [h]

lemma univ_unit_bool_config :
    (@Finset.univ ceBig.Configuration (LabelledMultigraph.instFintypeConfiguration ceBig))
      = ({fun _ => false, fun _ => true} : Finset (Unit → Bool)) := by
  have h : (@Finset.univ ceBig.Configuration (LabelledMultigraph.instFintypeConfiguration ceBig))
      = @Finset.univ (Unit → Bool) Pi.instFintype :=
    univ_congr_fintype _ _
  rw [h]
  exact univ_unit_bool

lemma pair_ne : (fun _ => false : Unit → Bool) ≠ (fun _ => true) := by
  intro h
  have := congrFun h ()
  simp at this

lemma ceBig_partitionFunction :
    ceBig.partitionFunction 2 (1 / 2) ceBig.wiredBoundary = 2 := by
  unfold LabelledMultigraph.partitionFunction
  rw [univ_unit_bool_config, Finset.sum_pair pair_ne,
    ceBig_fkWeight_closed, ceBig_fkWeight_open]
  norm_num

lemma univ_unit_bool_config_small :
    (@Finset.univ ceSmall.Configuration (LabelledMultigraph.instFintypeConfiguration ceSmall))
      = ({fun _ => false, fun _ => true} : Finset (Unit → Bool)) := by
  have h : (@Finset.univ ceSmall.Configuration (LabelledMultigraph.instFintypeConfiguration ceSmall))
      = @Finset.univ (Unit → Bool) Pi.instFintype :=
    univ_congr_fintype _ _
  rw [h]
  exact univ_unit_bool

lemma ceSmall_partitionFunction :
    ceSmall.partitionFunction 2 (1 / 2) ceSmall.freeBoundary = 3 := by
  unfold LabelledMultigraph.partitionFunction
  rw [univ_unit_bool_config_small, Finset.sum_pair pair_ne,
    ceSmall_fkWeight_closed, ceSmall_fkWeight_open]
  norm_num

/-- **A non-free boundary breaks the measure identity.**  On the same
configuration space `Unit → Bool`, the wired law of the extended graph is not
the free law of the two-vertex graph: the singleton masses at the all-closed
configuration are `1/2` and `2/3`. -/
theorem fkMeasure_ne_of_wired :
    (ceBig.fkMeasure (by norm_num : (0 : NNReal) < 2) (by norm_num : (1 / 2 : NNReal) ≤ 1)
        ceBig.wiredBoundary : Measure (Unit → Bool))
      ≠ (ceSmall.fkMeasure (by norm_num : (0 : NNReal) < 2) (by norm_num : (1 / 2 : NNReal) ≤ 1)
        ceSmall.freeBoundary : Measure (Unit → Bool)) := by
  intro h
  have h1 := congrArg (fun ν : Measure (Unit → Bool) => ν {ceBig.allClosed}) h
  have hm := LabelledMultigraph.fkMeasure_apply_singleton
  have hw := LabelledMultigraph.fkPMF_apply
  rw [hm, hm, hw, hw] at h1
  rw [show ceBig.allClosed = (fun _ => false : Unit → Bool) from rfl] at h1
  rw [ceBig_fkWeight_closed, ceBig_partitionFunction, ceSmall_fkWeight_closed,
    ceSmall_partitionFunction] at h1
  rw [ENNReal.coe_inj] at h1
  norm_num at h1

end Counterexample


/-! ## Application: the vertex bookkeeping in the edge-injection comparison

`FK.InfiniteVolume.NoEscape.fkMeasure_le_of_inj` compares the laws of two
`fgOf` graphs on the *same* vertex type.  In a nested-box application the larger
stage graph lives on the enlarged vertex type of the next box.  The following
corollary composes that theorem with the isolated-vertex invariance, so that the
smaller law can be compared directly with the law of the augmented graph.  The
`PosAssoc` hypothesis of the underlying theorem is an input here as well: this
lemma discharges only the vertex bookkeeping, nothing analytic. -/

section StageInterface

variable {V₀ : Type} [Fintype V₀]
variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]
variable {src₁ : E₁ → V₀} {tgt₁ : E₁ → V₀} {src₂ : E₂ → V₀} {tgt₂ : E₂ → V₀}
variable {ι : E₁ → E₂}

/-- Edge-domain comparison against an isolated-vertex-augmented stage graph. -/
theorem fkMeasure_le_of_inj_sumInl (X : Type) [Fintype X]
    (hι : Function.Injective ι) (hsrc : ∀ e, src₂ (ι e) = src₁ e)
    (htgt : ∀ e, tgt₂ (ι e) = tgt₁ e)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (hp1 : p < 1)
    (hPA : PosAssoc q p hq hp) {A : Set (E₁ → Bool)} (hA : IsUp A) :
    (fgOf E₁ src₁ tgt₁).fkMeasure hq hp (⊥ : Setoid V₀) A
      ≤ (fgSumInl X E₂ src₂ tgt₂).fkMeasure hq hp (⊥ : Setoid (V₀ ⊕ X))
          (res ι ⁻¹' A) := by
  have hle : (fgSumInl X E₁ src₁ tgt₁).fkMeasure hq hp (⊥ : Setoid (V₀ ⊕ X)) A
      ≤ (fgSumInl X E₂ src₂ tgt₂).fkMeasure hq hp (⊥ : Setoid (V₀ ⊕ X))
          (res ι ⁻¹' A) :=
    fkMeasure_le_of_inj (V := V₀ ⊕ X) (E₁ := E₁) (E₂ := E₂)
      (src₁ := fun e => Sum.inl (src₁ e)) (tgt₁ := fun e => Sum.inl (tgt₁ e))
      (src₂ := fun e => Sum.inl (src₂ e)) (tgt₂ := fun e => Sum.inl (tgt₂ e))
      (ι := ι) hι (fun e => by rw [hsrc e]) (fun e => by rw [htgt e]) hq hp hp1 hPA hA
  have h₀ : (fgOf E₁ src₁ tgt₁).fkMeasure hq hp (⊥ : Setoid V₀)
      = (fgSumInl X E₁ src₁ tgt₁).fkMeasure hq hp (⊥ : Setoid (V₀ ⊕ X)) :=
    (fkMeasure_sumInl_free (V := V₀) X hq hp).symm
  rw [h₀]
  exact hle

end StageInterface

end FiniteBox

end FK.InfiniteVolume.NoEscape
