/-
# Sealed-region conditioning (the free-boundary Markov property) for finite FK

The paper (Beffara--Faipeur--Oke, arXiv:2512.16486v1) uses, in the proof of
Lemma 2.1 and again in the proof of Theorem 5.1, the *free-boundary Markov
property*: if a set of edges is closed and separates a region from the rest of
the graph, then the conditional law of the FK measure inside that region is the
FK measure with **free** boundary condition.  The paper states it as "Clearly,
this holds for all FK measures".

This file proves that statement in the generality needed by the paper's
arguments: for an arbitrary finite labelled multigraph (loops and parallel
labels allowed) with an **arbitrary boundary setoid**, an arbitrary vertex set
`U` carrying no boundary wiring, and an arbitrary exterior configuration whose
open edges avoid `U`.  No block decomposition (`Fin m ⊕ Fin k`), no metric and
no geometric data is assumed.

Main results:

* `FK.RegionSeal.componentCount_glue` : the FK component count of the ambient
  graph splits as the free region count plus a term depending only on the
  exterior configuration;
* `FK.RegionSeal.fkWeight_glue` : the same for the FK weights;
* `FK.RegionSeal.fiberPMF_eq_region` : the ambient FK law conditioned on a
  sealed exterior configuration is *exactly* the free FK law on the induced
  region graph.
-/
import FK.ExteriorMarkov

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionSeal

open FK.Finite FK.Finite.LabelledMultigraph

set_option linter.unusedSectionVars false

/-! ## Connected components of a graph that does not cross a vertex split -/

namespace SimpleGraph

variable {V : Type*} {H : SimpleGraph V} {U : Set V}

/-- If no adjacency of `H` crosses the vertex set `U`, then along a walk the
membership in `U` is constant. -/
theorem mem_of_reachable_of_no_cross
    (hcross : ∀ x y : V, H.Adj x y → (x ∈ U ↔ y ∈ U))
    {x y : V} (h : H.Reachable x y) : (x ∈ U ↔ y ∈ U) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Iff.rfl
  | cons hadj _ ih => exact (hcross _ _ hadj).trans ih

/-- Reachability in the induced subgraph implies reachability in the ambient
graph. -/
theorem reachable_of_induce {s : Set V} {x y : s}
    (h : (H.induce s).Reachable x y) : H.Reachable x.1 y.1 :=
  h.map (SimpleGraph.Embedding.induce s).toHom

/-- A walk in `H` between two vertices of `U` stays inside `U` and is therefore
a walk of the induced subgraph. -/
theorem induce_reachable_of_walk
    (hcross : ∀ x y : V, H.Adj x y → (x ∈ U ↔ y ∈ U)) :
    ∀ {x y : V}, H.Walk x y → ∀ (hx : x ∈ U) (hy : y ∈ U),
      (H.induce U).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, hx, _ => SimpleGraph.Reachable.refl _
  | _, _, .cons (v := y₀) h w', hx, hy => by
      have hy₀ : y₀ ∈ U := (hcross _ _ h).mp hx
      have hstep : (H.induce U).Adj ⟨_, hx⟩ ⟨_, hy₀⟩ := h
      exact (SimpleGraph.Adj.reachable hstep).trans
        (induce_reachable_of_walk hcross w' hy₀ hy)

theorem reachable_induce_iff
    (hcross : ∀ x y : V, H.Adj x y → (x ∈ U ↔ y ∈ U))
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    (H.induce U).Reachable ⟨x, hx⟩ ⟨y, hy⟩ ↔ H.Reachable x y :=
  ⟨reachable_of_induce, fun h => by
    obtain ⟨w⟩ := h
    exact induce_reachable_of_walk hcross w hx hy⟩

/-- A graph with no adjacency crossing `U` has exactly as many connected
components as the disjoint union of its two induced parts. -/
theorem natCard_connectedComponent_induce_split [Finite V]
    (hcross : ∀ x y : V, H.Adj x y → (x ∈ U ↔ y ∈ U)) :
    Nat.card H.ConnectedComponent =
      Nat.card (H.induce U).ConnectedComponent +
        Nat.card (H.induce Uᶜ).ConnectedComponent := by
  classical
  let φU : (H.induce U) →g H := (SimpleGraph.Embedding.induce U).toHom
  let φUc : (H.induce (Uᶜ : Set V)) →g H :=
    (SimpleGraph.Embedding.induce (Uᶜ : Set V)).toHom
  let g : (H.induce U).ConnectedComponent ⊕ (H.induce Uᶜ).ConnectedComponent →
      H.ConnectedComponent := Sum.elim (fun c => c.map φU) (fun d => d.map φUc)
  have hsurj : Function.Surjective g := by
    intro C
    obtain ⟨x, rfl⟩ := C.exists_rep
    by_cases hx : x ∈ U
    · exact ⟨Sum.inl ((H.induce U).connectedComponentMk (⟨x, hx⟩ : U)),
        by simp only [g, Sum.elim_inl, SimpleGraph.ConnectedComponent.map_mk]; rfl⟩
    · exact ⟨Sum.inr ((H.induce (Uᶜ : Set V)).connectedComponentMk
        (⟨x, by simpa using hx⟩ : (Uᶜ : Set V))),
        by simp only [g, Sum.elim_inr, SimpleGraph.ConnectedComponent.map_mk]; rfl⟩
  have hinjU : ∀ c d : (H.induce U).ConnectedComponent, c.map φU = d.map φU → c = d := by
    intro c d hcd
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨y, rfl⟩ := d.exists_rep
    have h' : H.connectedComponentMk x.1 = H.connectedComponentMk y.1 := hcd
    change (H.induce U).connectedComponentMk x = (H.induce U).connectedComponentMk y
    rw [SimpleGraph.ConnectedComponent.eq, reachable_induce_iff hcross x.2 y.2]
    exact SimpleGraph.ConnectedComponent.exact h'
  have hinjUc : ∀ c d : (H.induce (Uᶜ : Set V)).ConnectedComponent,
      c.map φUc = d.map φUc → c = d := by
    intro c d hcd
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨y, rfl⟩ := d.exists_rep
    have h' : H.connectedComponentMk x.1 = H.connectedComponentMk y.1 := hcd
    change (H.induce (Uᶜ : Set V)).connectedComponentMk x =
      (H.induce (Uᶜ : Set V)).connectedComponentMk y
    rw [SimpleGraph.ConnectedComponent.eq,
      reachable_induce_iff (U := (Uᶜ : Set V)) (fun a b hab => by
        simpa using not_congr (hcross a b hab)) x.2 y.2]
    exact SimpleGraph.ConnectedComponent.exact h'
  have hcross_false : ∀ (c : (H.induce U).ConnectedComponent)
      (d : (H.induce (Uᶜ : Set V)).ConnectedComponent), c.map φU ≠ d.map φUc := by
    intro c d hcd
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨y, rfl⟩ := d.exists_rep
    have h' : H.connectedComponentMk x.1 = H.connectedComponentMk y.1 := hcd
    have hmem := mem_of_reachable_of_no_cross hcross
      (SimpleGraph.ConnectedComponent.exact h')
    exact y.2 (hmem.mp x.2)
  have hinj : Function.Injective g := by
    intro c d hcd
    rcases c with c | c <;> rcases d with d | d
    · rw [hinjU c d hcd]
    · exact absurd hcd (hcross_false c d)
    · exact absurd hcd.symm (hcross_false d c)
    · rw [hinjUc c d hcd]
  rw [← Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩), Nat.card_sum]

end SimpleGraph

/-! ## Splitting the ambient graph along a vertex set -/

section Split

variable (G : LabelledMultigraph) (U : Set G.Vertex) [DecidablePred (· ∈ U)]

/-- An edge is *internal* to `U` when both endpoints lie in `U`. -/
abbrev IsInternal (e : G.Edge) : Prop := G.source e ∈ U ∧ G.target e ∈ U

/-- Internal labels. -/
abbrev Internal := {e : G.Edge // IsInternal G U e}

/-- External labels. -/
abbrev External := {e : G.Edge // ¬ IsInternal G U e}

/-- Restriction of a configuration to the internal labels. -/
def restrictI (ω : G.Configuration) : Internal G U → Bool := fun i => ω i.1

/-- Restriction of a configuration to the external labels. -/
def restrictO (ω : G.Configuration) : External G U → Bool := fun o => ω o.1

/-- Reassembly of a configuration from its internal and external parts. -/
def glueExt (ω : Internal G U → Bool) (ζ : External G U → Bool) :
    G.Configuration :=
  fun e => if h : IsInternal G U e then ω ⟨e, h⟩ else ζ ⟨e, h⟩

lemma glueExt_of_internal (ω : Internal G U → Bool) (ζ : External G U → Bool)
    (e : G.Edge) (h : IsInternal G U e) : glueExt G U ω ζ e = ω ⟨e, h⟩ := dif_pos h

lemma glueExt_of_external (ω : Internal G U → Bool) (ζ : External G U → Bool)
    (e : G.Edge) (h : ¬ IsInternal G U e) : glueExt G U ω ζ e = ζ ⟨e, h⟩ := dif_neg h

@[simp] lemma restrictI_glueExt (ω : Internal G U → Bool) (ζ : External G U → Bool) :
    restrictI G U (glueExt G U ω ζ) = ω := by
  funext i
  exact glueExt_of_internal G U ω ζ i.1 i.2

@[simp] lemma restrictO_glueExt (ω : Internal G U → Bool) (ζ : External G U → Bool) :
    restrictO G U (glueExt G U ω ζ) = ζ := by
  funext o
  exact glueExt_of_external G U ω ζ o.1 o.2

lemma glueExt_restrict (ρ : G.Configuration) :
    glueExt G U (restrictI G U ρ) (restrictO G U ρ) = ρ := by
  funext e
  by_cases h : IsInternal G U e
  · rw [glueExt_of_internal G U _ _ e h]; rfl
  · rw [glueExt_of_external G U _ _ e h]; rfl

lemma glueExt_injective (ζ : External G U → Bool) :
    Function.Injective (fun ω => glueExt G U ω ζ) := by
  intro ω η h
  have := congrArg (restrictI G U) h
  simpa using this

/-- Configurations whose external part is a prescribed `ζ`. -/
def extFiber (ζ : External G U → Bool) : Set G.Configuration :=
  {ρ | restrictO G U ρ = ζ}

lemma glueExt_mem_extFiber (ω : Internal G U → Bool) (ζ : External G U → Bool) :
    glueExt G U ω ζ ∈ extFiber G U ζ := restrictO_glueExt G U ω ζ

lemma eq_glueExt_of_mem_extFiber {ζ : External G U → Bool} {ρ : G.Configuration}
    (hρ : ρ ∈ extFiber G U ζ) : ρ = glueExt G U (restrictI G U ρ) ζ := by
  calc ρ = glueExt G U (restrictI G U ρ) (restrictO G U ρ) :=
        (glueExt_restrict G U ρ).symm
    _ = glueExt G U (restrictI G U ρ) ζ := by rw [hρ]

/-- The region graph: the induced subgraph on `U`, with free boundary. -/
def regionGraph : LabelledMultigraph where
  Vertex := U
  Edge := Internal G U
  source i := ⟨G.source i.1, i.2.1⟩
  target i := ⟨G.target i.1, i.2.2⟩

/-- The exterior graph on the vertices outside `U`; it depends only on the
exterior configuration `ζ` and on the boundary setoid. -/
def outGraph (α : G.BoundaryPartition) (ζ : External G U → Bool) :
    SimpleGraph (Uᶜ : Set G.Vertex) where
  Adj x y := x ≠ y ∧
    (α.r x.1 y.1 ∨ ∃ o : External G U, ζ o = true ∧ G.Joins o.1 x.1 y.1)
  symm := ⟨by
    rintro x y ⟨hne, h | ⟨o, ho, hj⟩⟩
    · exact ⟨hne.symm, Or.inl (α.symm h)⟩
    · exact ⟨hne.symm, Or.inr ⟨o, ho, hj.symm⟩⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

@[simp] lemma regionGraph_source (i : Internal G U) :
    (regionGraph G U).source i = ⟨G.source i.1, i.2.1⟩ := rfl

@[simp] lemma regionGraph_target (i : Internal G U) :
    (regionGraph G U).target i = ⟨G.target i.1, i.2.2⟩ := rfl

lemma regionGraph_joins (i : Internal G U) (x y : U) :
    (regionGraph G U).Joins i x y ↔ G.Joins i.1 x.1 y.1 := by
  unfold LabelledMultigraph.Joins
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
    · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩

/-- **No adjacency crosses the region.**  Under a boundary setoid with no
nontrivial relation on `U` and an exterior configuration whose open edges avoid
`U`, every adjacency of the ambient FK connection graph stays on one side. -/
theorem connectionGraph_noCross (α : G.BoundaryPartition) (ζ : External G U → Bool)
    (ω : Internal G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    {x y : G.Vertex} (h : (G.connectionGraph α (glueExt G U ω ζ)).Adj x y) :
    (x ∈ U ↔ y ∈ U) := by
  have key : ∀ a b : G.Vertex, (G.connectionGraph α (glueExt G U ω ζ)).Adj a b →
      a ∈ U → b ∈ U := by
    intro a b hab ha
    obtain ⟨hne, hw | ⟨e, he, hj⟩⟩ := hab
    · exact absurd (hwire a ha b hw) hne
    · by_cases hi : IsInternal G U e
      · rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hi.2
        · exact hi.1
      · have hg : ζ ⟨e, hi⟩ = true := by
          have := he; rw [glueExt_of_external G U ω ζ e hi] at this; exact this
        obtain ⟨hs, ht⟩ := hseal ⟨e, hi⟩ hg
        rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd ha hs
        · exact absurd ha ht
  constructor
  · intro hx; exact key x y h hx
  · intro hy; exact key y x h.symm hy

/-- The induced graph on the region is exactly the region FK connection graph
with free boundary. -/
theorem connectionGraph_induce_region (α : G.BoundaryPartition)
    (ζ : External G U → Bool) (ω : Internal G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U) :
    (G.connectionGraph α (glueExt G U ω ζ)).induce U =
      (regionGraph G U).connectionGraph (regionGraph G U).freeBoundary ω := by
  ext x y
  rw [SimpleGraph.induce_adj]
  constructor
  · rintro ⟨hne, hw | ⟨e, he, hj⟩⟩
    · exact absurd (hwire x.1 x.2 y.1 hw) hne
    · by_cases hi : IsInternal G U e
      · have hge : ω ⟨e, hi⟩ = true := by
          have := he; rw [glueExt_of_internal G U ω ζ e hi] at this; exact this
        exact ⟨fun h => hne (congrArg Subtype.val h),
          Or.inr ⟨⟨e, hi⟩, hge, (regionGraph_joins G U ⟨e, hi⟩ x y).mpr hj⟩⟩
      · have hg : ζ ⟨e, hi⟩ = true := by
          have := he; rw [glueExt_of_external G U ω ζ e hi] at this; exact this
        obtain ⟨hs, ht⟩ := hseal ⟨e, hi⟩ hg
        rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (h1 ▸ x.2) hs
        · exact absurd (h2 ▸ x.2) ht
  · rintro ⟨hne, hw | ⟨i, hi, hj⟩⟩
    · exact absurd hw hne
    · exact ⟨fun h => hne (Subtype.ext h),
        Or.inr ⟨i.1, by rw [glueExt_of_internal G U ω ζ i.1 i.2]; exact hi,
          (regionGraph_joins G U i x y).mp hj⟩⟩

/-- The induced graph outside the region is the exterior graph. -/
theorem connectionGraph_induce_outside (α : G.BoundaryPartition)
    (ζ : External G U → Bool) (ω : Internal G U → Bool) :
    (G.connectionGraph α (glueExt G U ω ζ)).induce (Uᶜ : Set G.Vertex) =
      outGraph G U α ζ := by
  ext x y
  rw [SimpleGraph.induce_adj]
  constructor
  · rintro ⟨hne, hw | ⟨e, he, hj⟩⟩
    · exact ⟨fun h => hne (congrArg Subtype.val h), Or.inl hw⟩
    · by_cases hi : IsInternal G U e
      · rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso; exact x.2 (h1.symm ▸ hi.1)
        · exfalso; exact x.2 (h2.symm ▸ hi.2)
      · have hg : ζ ⟨e, hi⟩ = true := by
          have := he; rw [glueExt_of_external G U ω ζ e hi] at this; exact this
        exact ⟨fun h => hne (congrArg Subtype.val h), Or.inr ⟨⟨e, hi⟩, hg, hj⟩⟩
  · rintro ⟨hne, hw | ⟨o, ho, hj⟩⟩
    · exact ⟨fun h => hne (Subtype.ext h), Or.inl hw⟩
    · exact ⟨fun h => hne (Subtype.ext h),
        Or.inr ⟨o.1, by rw [glueExt_of_external G U ω ζ o.1 o.2]; exact ho, hj⟩⟩

/-- **Component count of a sealed region.**  The ambient FK component count is
the free component count of the region plus a term depending only on the
exterior configuration. -/
theorem componentCount_glue (α : G.BoundaryPartition) (ζ : External G U → Bool)
    (ω : Internal G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U) :
    G.componentCount α (glueExt G U ω ζ) =
      (regionGraph G U).componentCount (regionGraph G U).freeBoundary ω +
        Nat.card (outGraph G U α ζ).ConnectedComponent := by
  have hnc : ∀ {x y : G.Vertex},
      (G.connectionGraph α (glueExt G U ω ζ)).Adj x y → (x ∈ U ↔ y ∈ U) :=
    fun {x y} h => connectionGraph_noCross G U α ζ ω hwire hseal h
  rw [LabelledMultigraph.componentCount,
    SimpleGraph.natCard_connectedComponent_induce_split (H := G.connectionGraph α
      (glueExt G U ω ζ)) (U := U) (fun x y h =>
        ⟨fun hx => (hnc (x := x) (y := y) h).mp hx,
         fun hy => (hnc (x := y) (y := x) h.symm).mp hy⟩),
    connectionGraph_induce_region G U α ζ ω hwire hseal,
    connectionGraph_induce_outside G U α ζ ω]
  rfl

/-- The exterior mass of a sealed exterior configuration. -/
noncomputable def outMass (α : G.BoundaryPartition) (ζ : External G U → Bool)
    (q p : NNReal) : NNReal :=
  FK.FinitePlane.edgeWeight p (1 - p) ζ *
    q ^ Nat.card (outGraph G U α ζ).ConnectedComponent

lemma edgeWeight_glue (p : NNReal) (ω : Internal G U → Bool)
    (ζ : External G U → Bool) :
    G.edgeWeight p (glueExt G U ω ζ) =
      (regionGraph G U).edgeWeight p ω *
        FK.FinitePlane.edgeWeight p (1 - p) ζ := by
  let f : G.Edge → NNReal := fun e => if glueExt G U ω ζ e then p else 1 - p
  let s : Finset G.Edge := Finset.univ.filter (IsInternal G U)
  have hs : ∀ x : G.Edge, x ∈ s ↔ IsInternal G U x := by
    intro x; simp [s]
  have hsc : ∀ x : G.Edge, x ∈ sᶜ ↔ ¬ IsInternal G U x := by
    intro x; simp [s]
  have hsplit : (∏ e ∈ s, f e) * (∏ e ∈ sᶜ, f e) = ∏ e, f e :=
    Finset.prod_mul_prod_compl s f
  have hleft : (∏ e ∈ s, f e) = ∏ i : Internal G U, f i.1 :=
    Finset.prod_subtype s hs f
  have hright : (∏ e ∈ sᶜ, f e) = ∏ o : External G U, f o.1 :=
    Finset.prod_subtype sᶜ hsc f
  unfold LabelledMultigraph.edgeWeight FK.FinitePlane.edgeWeight
  rw [← hsplit, hleft, hright]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro i _
    simp only [f, glueExt_of_internal G U ω ζ i.1 i.2]
  · refine Finset.prod_congr rfl ?_
    intro o _
    simp only [f, glueExt_of_external G U ω ζ o.1 o.2]

/-- **Weight factorization for a sealed region.** -/
theorem fkWeight_glue (α : G.BoundaryPartition) (ζ : External G U → Bool)
    (ω : Internal G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    (q p : NNReal) :
    G.fkWeight q p α (glueExt G U ω ζ) =
      (regionGraph G U).fkWeight q p (regionGraph G U).freeBoundary ω *
        outMass G U α ζ q p := by
  unfold LabelledMultigraph.fkWeight
  rw [edgeWeight_glue G U p ω ζ,
    componentCount_glue G U α ζ ω hwire hseal, outMass, pow_add]
  ring

/-! ## The conditional law on a sealed region -/

section Conditioning

variable (G : LabelledMultigraph) (U : Set G.Vertex) [DecidablePred (· ∈ U)]

/-- **The conditional law given a sealed exterior configuration.**  This is the
normalized restriction of the FK weights to the configurations whose external
part is `ζ`; since every weight is positive at interior parameters this is the
conditional law of the internal edges given the external ones. -/
noncomputable def fiberPMF (α : G.BoundaryPartition) (ζ : External G U → Bool)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF (Internal G U → Bool) :=
  FK.FinitePlane.normalizedPMF (fun ω => G.fkWeight q p α (glueExt G U ω ζ))
    (fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ (G.componentCount α) _)

lemma outMass_pos (α : G.BoundaryPartition) (ζ : External G U → Bool)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < outMass G U α ζ q p :=
  mul_pos (FK.FinitePlane.edgeWeight_pos' hp₀ hp₁ ζ) (pow_pos hq _)

/-- **The free-boundary Markov property.**  If the boundary setoid has no
nontrivial relation on the region `U` and the exterior configuration `ζ` has no
open edge touching `U`, then the FK law conditioned on the external part being
`ζ` is *exactly* the FK law of the induced region graph with free boundary. -/
theorem fiberPMF_eq_region (α : G.BoundaryPartition) (ζ : External G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    fiberPMF G U α ζ hq hp₀ hp₁ =
      (regionGraph G U).fkPMF hq hp₁.le (regionGraph G U).freeBoundary := by
  have hc := outMass_pos G U α ζ hq hp₀ hp₁
  have hprop : ∀ ω : Internal G U → Bool,
      G.fkWeight q p α (glueExt G U ω ζ) =
        outMass G U α ζ q p *
          (regionGraph G U).fkWeight q p (regionGraph G U).freeBoundary ω := by
    intro ω
    rw [fkWeight_glue G U α ζ ω hwire hseal q p, mul_comm]
  have h := FK.FinitePlane.normalizedPMF_map_eq_of_proportional
    (Equiv.refl (Internal G U → Bool))
    (fun ω => (regionGraph G U).fkWeight q p (regionGraph G U).freeBoundary ω)
    (fun ω => G.fkWeight q p α (glueExt G U ω ζ))
    (outMass G U α ζ q p) hc
    (fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    hprop
  simp only [Equiv.coe_refl, PMF.map_id] at h
  rw [← FK.FinitePlane.normalizedPMF_eq_actual_fkPMF (regionGraph G U)
    (regionGraph G U).freeBoundary hq hp₀ hp₁]
  exact h.symm

/-- The free-boundary Markov property in the geometric form used in the paper:
if every edge with exactly one endpoint in `U` is closed in the exterior
configuration (the region is surrounded by a closed cutset), then the
conditional law inside the region is free. -/
theorem fiberPMF_eq_region_of_closed_cut (α : G.BoundaryPartition)
    (ζ : External G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hcut : ∀ (e : G.Edge) (h : ¬ IsInternal G U e),
      (G.source e ∈ U ∨ G.target e ∈ U) → ζ ⟨e, h⟩ = false)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    fiberPMF G U α ζ hq hp₀ hp₁ =
      (regionGraph G U).fkPMF hq hp₁.le (regionGraph G U).freeBoundary := by
  refine fiberPMF_eq_region G U α ζ hwire ?_ hq hp₀ hp₁
  intro o ho
  have hcut' := hcut o.1 o.2
  by_cases hs : G.source o.1 ∈ U
  · exact absurd ho (by rw [hcut' (Or.inl hs)]; simp)
  · refine ⟨hs, ?_⟩
    by_cases ht : G.target o.1 ∈ U
    · exact absurd ho (by rw [hcut' (Or.inr ht)]; simp)
    · exact ht

/-- The free-boundary Markov property in the case that actually occurs in the
paper: the region carries the free boundary condition, so the wiring
hypothesis is automatic. -/
theorem fiberPMF_eq_region_free (ζ : External G U → Bool)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    fiberPMF G U G.freeBoundary ζ hq hp₀ hp₁ =
      (regionGraph G U).fkPMF hq hp₁.le (regionGraph G U).freeBoundary :=
  fiberPMF_eq_region G U G.freeBoundary ζ
    (fun _ _ _ h => h) hseal hq hp₀ hp₁

/-- Pointwise form: the conditional probability of a full configuration given
its sealed exterior is the free region probability of its interior part. -/
theorem fiberPMF_apply_eq_region (α : G.BoundaryPartition) (ζ : External G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ω : Internal G U → Bool) :
    fiberPMF G U α ζ hq hp₀ hp₁ ω =
      (regionGraph G U).fkPMF hq hp₁.le (regionGraph G U).freeBoundary ω :=
  congrArg (fun ν : PMF (Internal G U → Bool) => ν ω)
    (fiberPMF_eq_region G U α ζ hwire hseal hq hp₀ hp₁)

end Conditioning

end Split


/-! ## Two sealed coordinates agree

The ordered-triple arguments of the paper compare two FK coordinates through a
common upper configuration.  The following form is what is used there: if two
sealed exterior configurations are given (for possibly different graphs and
boundary setoids, both trivial on the same region), the corresponding
conditional laws on the region coincide, because both are the free region law.
-/

section TwoCoordinates

variable {G : LabelledMultigraph} {U : Set G.Vertex} [DecidablePred (· ∈ U)]

/-- **Two sealed coordinates have the same interior law.** -/
theorem fiberPMF_eq_of_sealed (α α' : G.BoundaryPartition)
    (ζ ζ' : External G U → Bool)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hwire' : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α'.r v w → v = w)
    (hseal : ∀ o : External G U, ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    (hseal' : ∀ o : External G U, ζ' o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    fiberPMF G U α ζ hq hp₀ hp₁ = fiberPMF G U α' ζ' hq hp₀ hp₁ := by
  rw [fiberPMF_eq_region G U α ζ hwire hseal hq hp₀ hp₁,
    fiberPMF_eq_region G U α' ζ' hwire' hseal' hq hp₀ hp₁]

end TwoCoordinates

/-! ## Conditioning only on the seal -/

section Sealed

variable (G : LabelledMultigraph) (U : Set G.Vertex) [DecidablePred (· ∈ U)]

/-- The conditional law of the internal coordinates given that the external
part lies in a finite set `SZ` of exterior configurations.  This is the
normalized restriction of the FK weights to that event. -/
noncomputable def sealedPMF (α : G.BoundaryPartition)
    (SZ : Finset (External G U → Bool))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hne : SZ.Nonempty) : PMF (Internal G U → Bool) :=
  FK.FinitePlane.normalizedPMF
    (fun ω => ∑ ζ ∈ SZ, G.fkWeight q p α (glueExt G U ω ζ))
    (fun _ => Finset.sum_pos
      (fun ζ _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _) hne)

/-- **Conditioning on a sealed exterior event gives the free region law.**
Only the seal has to be known: the exterior configuration is not fixed, merely
restricted to a finite set of configurations none of whose open edges touch the
region. -/
theorem sealedPMF_eq_region (α : G.BoundaryPartition)
    (SZ : Finset (External G U → Bool)) (hne : SZ.Nonempty)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, α.r v w → v = w)
    (hseal : ∀ ζ ∈ SZ, ∀ o : External G U,
      ζ o = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    sealedPMF G U α SZ hq hp₀ hp₁ hne =
      (regionGraph G U).fkPMF hq hp₁.le (regionGraph G U).freeBoundary := by
  have hc : 0 < ∑ ζ ∈ SZ, outMass G U α ζ q p :=
    Finset.sum_pos (fun ζ _ => outMass_pos G U α ζ hq hp₀ hp₁) hne
  have hprop : ∀ ω : Internal G U → Bool,
      (∑ ζ ∈ SZ, G.fkWeight q p α (glueExt G U ω ζ)) =
        (∑ ζ ∈ SZ, outMass G U α ζ q p) *
          (regionGraph G U).fkWeight q p (regionGraph G U).freeBoundary ω := by
    intro ω
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro ζ hζ
    rw [fkWeight_glue G U α ζ ω hwire (hseal ζ hζ) q p, mul_comm]
  have h := FK.FinitePlane.normalizedPMF_map_eq_of_proportional
    (Equiv.refl (Internal G U → Bool))
    (fun ω => (regionGraph G U).fkWeight q p (regionGraph G U).freeBoundary ω)
    (fun ω => ∑ ζ ∈ SZ, G.fkWeight q p α (glueExt G U ω ζ))
    (∑ ζ ∈ SZ, outMass G U α ζ q p) hc
    (fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun _ => Finset.sum_pos
      (fun ζ _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _) hne)
    hprop
  simp only [Equiv.coe_refl, PMF.map_id] at h
  rw [← FK.FinitePlane.normalizedPMF_eq_actual_fkPMF (regionGraph G U)
    (regionGraph G U).freeBoundary hq hp₀ hp₁]
  exact h.symm

end Sealed

/-! ## Non-vacuity witnesses -/

section Witnesses

variable (G : LabelledMultigraph)

/-- With `U` the whole vertex set there are no external labels, so the seal
holds vacuously and the theorem applies with the unique external
configuration.  This shows the hypotheses of `fiberPMF_eq_region_free` are
consistent in the extreme case. -/
theorem fiberPMF_eq_region_free_univ {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p)
    (hp₁ : p < 1) (ζ : External G Set.univ → Bool) :
    fiberPMF G Set.univ G.freeBoundary ζ hq hp₀ hp₁ =
      (regionGraph G Set.univ).fkPMF hq hp₁.le (regionGraph G Set.univ).freeBoundary :=
  fiberPMF_eq_region_free G Set.univ ζ
    (fun o => absurd ⟨trivial, trivial⟩ o.2) hq hp₀ hp₁

end Witnesses

section WitnessNonempty

/-- The two-vertex graph `true -- false` with a single label. -/
def witnessGraph : LabelledMultigraph where
  Vertex := Bool
  Edge := Unit
  source := fun _ => true
  target := fun _ => false

/-- A sealed external configuration exists for `witnessGraph` with
`U = {true}`: the single label has its target outside `U`, so it is external,
and no external label is open. -/
theorem exists_sealed_external :
    ∃ ζ : External witnessGraph {true} → Bool,
      ∀ o : External witnessGraph {true}, ζ o = true →
        witnessGraph.source o.1 ∉ ({true} : Set Bool) ∧
          witnessGraph.target o.1 ∉ ({true} : Set Bool) :=
  ⟨fun _ => false, fun _ ho => absurd ho (by simp)⟩

end WitnessNonempty
