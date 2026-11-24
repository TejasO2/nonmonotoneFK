/-
# Normalized FK/FKG bridge for labelled multigraphs with boundary wiring

# What is proved here

**The F2-corank is the connected-component count.**  For an arbitrary finite
endpoint map `ends : E → V × V` (loops and parallel labels allowed) and an
arbitrary finite set of open edges `s`, the corank `|V| - rank` of the `ZMod 2`
span of the endpoint vectors of `s` is exactly the number of connected components
of the simple graph joining the endpoints of the edges of `s`
(`FinFKG.clusterCount_eq_natCard_components`).  This closes the gap recorded for
`FKG.FKCluster` in `docs/MODULES.md` ("the general corank/component-count
identification is still open").

**Arbitrary boundary setoids.**  For a labelled multigraph `G` with boundary
setoid `ξ`, one artificial edge per vertex to a chosen representative of its block
turns `ξ` into a free boundary condition on the same vertex set:
`G.componentCount ξ ω` is the number of components of that augmented free
skeleton (`FK.Finite.LabelledMultigraph.componentCount_eq_card_components_wiringSkeleton`),
and therefore also the corank of its augmented edge span
(`...componentCount_eq_clusterCount`).  No quotient vertex type, no
`DecidableEq` on the external labels and no simple-graph quotient witness is
required.

**Supermodularity of the wired component count** in the lattice of
configurations (`...componentCount_supermodular`) follows by reducing
`openSet (augConfig ξ (ω ⊔ η))` to a union and applying the repo's
`FinFKG.clusterCount_supermodular`.  This is the hypothesis the FKG argument
actually needs, and it is now available for the *actual* model of
`FK.FiniteModel`, with loops, parallel edges and arbitrary wiring.

**Normalized FKG comparisons.**
* `...fkWeightR_lc`: the real unnormalized FK weight satisfies the lattice
  condition for `q ≥ 1`;
* `...fkPMF_association`: increasing nonnegative observables are positively
  correlated under the actual normalized `G.fkPMF` for `q ≥ 1`, `0 < p < 1`
  (`toReal` expectations, arbitrary boundary setoid);
* `...fkWeightR_mlr` and `...fkPMF_expectation_mono_p`: raising `p` at fixed
  `q ≥ 1` increases the expectation of increasing nonnegative observables,
  i.e. monotonicity of the finite-volume FK measures in `p`;
* `...fkPMF_association_events`: the same association inequality for pairs of
  increasing events;
* `...fkPMF_expectation_le_bernoulli` and `...fkPMF_event_le_bernoulli`: at
  `q ≥ 1` the FK measure is stochastically dominated by the product
  Bernoulli-`p` law at the same `p` (the correct orientation: `q > 1` favours
  clusters, hence closed edges).  The single-edge computation `q = 2`,
  `p = 1/2`, edge probability `1/3 < 1/2` shows the domination cannot be
  reversed;
* `...fkWeightR_lc_rev`: for `0 < q ≤ 1` the lattice condition reverses.  No
  association conclusion is drawn there, and `...fkWeightR_lc_fails_of_lt_one`
  plus the explicit two-vertex/two-parallel-edge example
  (`...parallelGraph_lattice_condition_fails`) show exactly where the FKG
  hypothesis fails for `q < 1`.

Everything is an ordinary Lean theorem: no `sorry`, no custom axiom, no
`unsafe`, no `native_decide`, no heartbeat override.  The file compiles without
errors and without warnings; the only `set_option` is the silence of a *style*
suggestion to write `let` instead of `letI` for the noncomputable `Fintype`
instances on connected-component quotient types that `Module.finrank` needs.

This file does not claim any of Theorem 1.4/1.9/1.10/1.11 itself: it supplies
the reusable finite positive-association and monotonicity machinery for the
genuine labelled-multigraph FK measures used elsewhere in the repository.
-/
import FK.FKG.FKApply
import FK.FiniteModel
import FK.ClassicalOne

set_option linter.unusedSectionVars false

-- `letI`/`haveI` here only install noncomputable `Fintype` instances on
-- connected-component quotient types (needed to speak about `Module.finrank`);
-- they carry no mathematical content.
set_option linter.style.haveILetI false

namespace FinFKG

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev csingle (u : V) : V → ZMod 2 := Pi.single u 1

lemma csingle_apply {u w : V} : csingle u w = if w = u then (1 : ZMod 2) else 0 :=
  Pi.single_apply ..

lemma csingle_add_self (u : V) : csingle u + csingle u = 0 := by
  funext w
  rw [Pi.add_apply, Pi.zero_apply]
  by_cases h : w = u
  · subst h
    rw [csingle_apply, ite_eq_left rfl]
    decide
  · rw [csingle_apply, ite_eq_right h, add_zero]

lemma add_add_cancel_mid (a b c : V → ZMod 2) (hb : b + b = 0) :
    (a + b) + (b + c) = a + c := by
  rw [add_assoc]
  nth_rewrite 1 [← add_assoc b b c]
  rw [hb, zero_add]

lemma csingle_eq_add_add (u r : V) : csingle u = (csingle u + csingle r) + csingle r := by
  have h := add_add_cancel_mid (csingle u) (csingle r) 0 (csingle_add_self r)
  simpa using h.symm

def skeleton (ends : E → V × V) (s : Finset E) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e ∈ s,
    (((ends e).1 = u ∧ (ends e).2 = v) ∨ ((ends e).1 = v ∧ (ends e).2 = u))
  symm := ⟨by
    rintro u v ⟨huv, e, he, h | h⟩
    · exact ⟨huv.symm, e, he, Or.inr h⟩
    · exact ⟨huv.symm, e, he, Or.inl h⟩⟩
  loopless := ⟨by rintro v ⟨h, -⟩; exact h rfl⟩

lemma skeleton_adj_iff {ends : E → V × V} {s : Finset E} {u v : V} :
    (skeleton ends s).Adj u v ↔ u ≠ v ∧ ∃ e ∈ s,
      (((ends e).1 = u ∧ (ends e).2 = v) ∨ ((ends e).1 = v ∧ (ends e).2 = u)) :=
  Iff.rfl

lemma edgeVec_eq_single (ends : E → V × V) (e : E) :
    edgeVec ends e = csingle (ends e).1 + csingle (ends e).2 := by
  funext w
  rw [Pi.add_apply, csingle_apply, csingle_apply]
  rfl

lemma csingle_add_csingle_mem_edgeSpan_of_adj {ends : E → V × V} {s : Finset E} {u v : V}
    (h : (skeleton ends s).Adj u v) :
    csingle u + csingle v ∈ edgeSpan ends s := by
  obtain ⟨-, e, he, hh | hh⟩ := h
  · rw [← hh.1, ← hh.2, ← edgeVec_eq_single]
    exact Submodule.subset_span ⟨e, by simpa using he, rfl⟩
  · rw [← hh.1, ← hh.2, add_comm, ← edgeVec_eq_single]
    exact Submodule.subset_span ⟨e, by simpa using he, rfl⟩

lemma csingle_add_csingle_mem_edgeSpan_of_reachable {ends : E → V × V} {s : Finset E} {u v : V}
    (h : (skeleton ends s).Reachable u v) :
    csingle u + csingle v ∈ edgeSpan ends s := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => csingle a + csingle v ∈ edgeSpan ends s) h ?_ ?_
  · rw [csingle_add_self]
    exact Submodule.zero_mem _
  · intro a c hac _ ih
    rw [← add_add_cancel_mid _ _ _ (csingle_add_self c)]
    exact Submodule.add_mem _ (csingle_add_csingle_mem_edgeSpan_of_adj hac) ih

/-! ### Component sums -/

/-- Sum of the coordinates of `f` over one fibre of `c`, as a linear map. -/
noncomputable def compSum {γ : Type*} [Fintype γ] [DecidableEq γ] (c : V → γ) :
    (V → ZMod 2) →ₗ[ZMod 2] (γ → ZMod 2) where
  toFun f C := ∑ v ∈ univ.filter (fun v => c v = C), f v
  map_add' f g := by
    funext C
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
  map_smul' a f := by
    funext C
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

lemma compSum_apply {γ : Type*} [Fintype γ] [DecidableEq γ] (c : V → γ)
    (f : V → ZMod 2) (C : γ) :
    compSum c f C = ∑ v ∈ univ.filter (fun v => c v = C), f v := rfl

lemma compSum_csingle {γ : Type*} [Fintype γ] [DecidableEq γ] (c : V → γ) (a : V) (C : γ) :
    compSum c (csingle a) C = if c a = C then (1 : ZMod 2) else 0 := by
  rw [compSum_apply]
  by_cases h : c a = C
  · rw [ite_eq_left h]
    rw [Finset.sum_eq_single a]
    · rw [csingle_apply, ite_eq_left rfl]
    · intro b _ hba
      rw [csingle_apply, ite_eq_right hba]
    · intro ha
      exact absurd (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ a, h⟩) ha
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero ?_
    intro b hb
    rw [Finset.mem_filter] at hb
    by_cases hba : b = a
    · subst hba; exact absurd hb.2 h
    · rw [csingle_apply, ite_eq_right hba]

/-- The edge span annihilates all sums over fibres of a map that is constant on
the edges of `s`. -/
lemma edgeSpan_le_ker {γ : Type*} [Fintype γ] [DecidableEq γ] {ends : E → V × V}
    {s : Finset E} (c : V → γ) (hc : ∀ u v : V, (skeleton ends s).Adj u v → c u = c v) :
    edgeSpan ends s ≤ (compSum c).ker := by
  classical
  unfold edgeSpan
  rw [Submodule.span_le]
  rintro _ ⟨e, he, rfl⟩
  change compSum c (edgeVec ends e) = 0
  funext C
  rw [edgeVec_eq_single, map_add, Pi.add_apply, compSum_csingle, compSum_csingle, Pi.zero_apply]
  set u := (ends e).1 with hu
  set v := (ends e).2 with hv
  have hcuv : c u = c v := by
    by_cases huv : u = v
    · rw [huv]
    · exact hc u v ⟨huv, e, he, Or.inl ⟨hu.symm, hv.symm⟩⟩
  rw [hcuv]
  by_cases hC : c v = C
  · rw [ite_eq_left hC]
    decide
  · rw [ite_eq_right hC]
    rfl

/-- Coordinate decomposition of a vector, for an arbitrary finite index type. -/
lemma sum_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ZMod 2) :
    ∑ i, f i • (Pi.single i (1 : ZMod 2) : ι → ZMod 2) = f := by
  funext w
  rw [Finset.sum_apply, Finset.sum_eq_single w]
  · rw [Pi.smul_apply, Pi.single_apply, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro b _ hbw
    rw [Pi.smul_apply, Pi.single_apply, ite_eq_right (Ne.symm hbw), smul_zero]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

/-- Coordinate decomposition of a vector. -/
lemma sum_smul_csingle (f : V → ZMod 2) : ∑ v, f v • csingle v = f :=
  sum_smul_single f

/-- If every `c`-fibre is contained in a skeleton component, then the kernel of
the sum map lies in the edge span. -/
lemma mem_edgeSpan_of_compSum_eq_zero {γ : Type*} [Fintype γ] [DecidableEq γ]
    {ends : E → V × V} {s : Finset E} {c : V → γ}
    (hcomp : ∀ u v : V, c u = c v → (skeleton ends s).Reachable u v)
    (hsurj : Function.Surjective c)
    {f : V → ZMod 2} (hf : compSum c f = 0) : f ∈ edgeSpan ends s := by
  classical
  set r : γ → V := fun C => Classical.choose (hsurj C) with hr
  have hrC : ∀ C : γ, c (r C) = C := fun C => Classical.choose_spec (hsurj C)
  have hdecomp : f = ∑ C : γ, ∑ v ∈ univ.filter (fun v => c v = C), f v • csingle v := by
    rw [Finset.sum_fiberwise (univ) c (fun v => f v • csingle v)]
    exact (sum_smul_csingle f).symm
  rw [hdecomp]
  refine Submodule.sum_mem _ fun C _ => ?_
  have hterm : ∀ v : V, f v • csingle v
      = f v • (csingle v + csingle (r C)) + f v • csingle (r C) := by
    intro v
    rw [← smul_add]
    exact congrArg (fun x => f v • x) (csingle_eq_add_add v (r C))
  have hsplit : ∑ v ∈ univ.filter (fun v => c v = C), f v • csingle v
      = (∑ v ∈ univ.filter (fun v => c v = C), f v • (csingle v + csingle (r C))) +
        (∑ v ∈ univ.filter (fun v => c v = C), f v • csingle (r C)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => hterm v
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.sum_mem _ fun v hv => ?_
    refine Submodule.smul_mem _ _ ?_
    refine csingle_add_csingle_mem_edgeSpan_of_reachable ?_
    rw [Finset.mem_filter] at hv
    exact hcomp v (r C) (by rw [hv.2, hrC C])
  · rw [← Finset.sum_smul]
    have hzero : ∑ v ∈ univ.filter (fun v => c v = C), f v = 0 := by
      have := congrFun hf C
      simpa [compSum_apply] using this
    rw [hzero, zero_smul]
    exact Submodule.zero_mem _


/-- The sum map for a surjective `c` is surjective. -/
lemma compSum_surjective {γ : Type*} [Fintype γ] [DecidableEq γ] {c : V → γ}
    (hsurj : Function.Surjective c) : Function.Surjective (compSum c) := by
  classical
  set r : γ → V := fun C => Classical.choose (hsurj C) with hr
  have hrC : ∀ C : γ, c (r C) = C := fun C => Classical.choose_spec (hsurj C)
  intro g
  refine ⟨∑ C : γ, g C • csingle (r C), ?_⟩
  have hterm : ∀ C : γ, compSum c (csingle (r C)) = Pi.single C (1 : ZMod 2) := by
    intro C
    funext C'
    rw [compSum_csingle, hrC]
    by_cases h : C = C'
    · subst h
      rw [ite_eq_left rfl, Pi.single_eq_same]
    · rw [ite_eq_right h, Pi.single_eq_of_ne (Ne.symm h)]
  calc compSum c (∑ C : γ, g C • csingle (r C))
      = ∑ C : γ, compSum c (g C • csingle (r C)) := map_sum ..
    _ = ∑ C : γ, g C • compSum c (csingle (r C)) := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [map_smul]
    _ = ∑ C : γ, g C • (Pi.single C (1 : ZMod 2) : γ → ZMod 2) := by
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [hterm]
    _ = g := sum_smul_single g

/-- Dimension count: when `c` is surjective the kernel of the sum map has
dimension `|V| - |γ|`. -/
lemma finrank_ker_compSum {γ : Type*} [Fintype γ] [DecidableEq γ] {c : V → γ}
    (hsurj : Function.Surjective c) :
    Module.finrank (ZMod 2) ↥(compSum c).ker = Fintype.card V - Fintype.card γ := by
  have hrange : (compSum c).range = ⊤ :=
    LinearMap.range_eq_top.mpr (compSum_surjective hsurj)
  have hrn := LinearMap.finrank_range_add_finrank_ker (compSum c)
  rw [hrange, finrank_top (ZMod 2) (γ → ZMod 2), Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hrn
  have hcard : Fintype.card γ ≤ Fintype.card V := Fintype.card_le_of_surjective c hsurj
  omega

/-- **The corank of the `ZMod 2` edge span is the number of connected components
of the underlying simple graph** (isolated vertices included). -/
theorem clusterCount_eq_natCard_components (ends : E → V × V) (s : Finset E) :
    clusterCount ends s = Nat.card (skeleton ends s).ConnectedComponent := by
  classical
  letI : Fintype (skeleton ends s).ConnectedComponent :=
    Fintype.ofFinite (skeleton ends s).ConnectedComponent
  let c : V → (skeleton ends s).ConnectedComponent := fun v =>
    (skeleton ends s).connectedComponentMk v
  have hsurj : Function.Surjective c := fun C => C.exists_rep
  have hconst : ∀ u v : V, (skeleton ends s).Adj u v → c u = c v :=
    fun u v h => SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h
  have hcomp : ∀ u v : V, c u = c v → (skeleton ends s).Reachable u v :=
    fun u v h => SimpleGraph.ConnectedComponent.exact h
  have hker : (compSum c).ker = edgeSpan ends s := by
    refine le_antisymm ?_ (edgeSpan_le_ker c hconst)
    intro f hf
    rw [LinearMap.mem_ker] at hf
    exact mem_edgeSpan_of_compSum_eq_zero hcomp hsurj hf
  have hrank : edgeRank ends s = Fintype.card V - Fintype.card (skeleton ends s).ConnectedComponent := by
    unfold edgeRank
    rw [← hker, finrank_ker_compSum hsurj]
  have hcard : Fintype.card (skeleton ends s).ConnectedComponent ≤ Fintype.card V :=
    Fintype.card_le_of_surjective c hsurj
  unfold clusterCount
  rw [hrank, Nat.card_eq_fintype_card]
  omega


/-! ### Comparing component counts across two graphs on the same vertex type -/

/-- Two simple graphs on the same vertex type with pointwise equivalent
reachability relations have the same number of connected components. -/
lemma card_components_eq_of_reachable_iff {W : Type*} {H₁ H₂ : SimpleGraph W}
    (h : ∀ u v : W, H₁.Reachable u v ↔ H₂.Reachable u v) :
    Nat.card H₁.ConnectedComponent = Nat.card H₂.ConnectedComponent := by
  classical
  let f : H₁.ConnectedComponent → H₂.ConnectedComponent :=
    Quot.lift (fun u => H₂.connectedComponentMk u)
      (fun u v huv => SimpleGraph.ConnectedComponent.sound ((h u v).mp huv))
  let g : H₂.ConnectedComponent → H₁.ConnectedComponent :=
    Quot.lift (fun u => H₁.connectedComponentMk u)
      (fun u v huv => SimpleGraph.ConnectedComponent.sound ((h u v).mpr huv))
  have hgf : ∀ C, g (f C) = C := fun C => Quot.inductionOn C (fun u => rfl)
  have hfg : ∀ C, f (g C) = C := fun C => Quot.inductionOn C (fun u => rfl)
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b hab
    have h' := congrArg g hab
    rwa [hgf a, hgf b] at h'
  · intro C
    exact ⟨g C, hfg C⟩

end FinFKG

/-! ### Boundary wiring as a free boundary condition on the block quotient -/

namespace FK.Finite.LabelledMultigraph

open FinFKG

variable (G : LabelledMultigraph)

/-- A chosen representative of every boundary block. -/
noncomputable def blockRep (ξ : G.BoundaryPartition) (q : Quotient ξ) : G.Vertex :=
  Classical.choose (Quot.exists_rep q)

lemma blockRep_spec (ξ : G.BoundaryPartition) (q : Quotient ξ) :
    Quot.mk ξ (blockRep G ξ q) = q :=
  Classical.choose_spec (Quot.exists_rep q)

/-- The endpoint map of the augmented free-boundary graph: the labelled edges of
`G` together with one artificial edge from each vertex to the representative of
its boundary block. -/
noncomputable def augEnds (ξ : G.BoundaryPartition) (x : G.Edge ⊕ G.Vertex) : G.Vertex × G.Vertex :=
  match x with
  | Sum.inl e => (G.source e, G.target e)
  | Sum.inr v => (v, blockRep G ξ (Quot.mk ξ v))

/-- The artificial edge is genuine unless the vertex is its own representative. -/
noncomputable def wireOpen (ξ : G.BoundaryPartition) (v : G.Vertex) : Bool := by
  classical
  exact if v = blockRep G ξ (Quot.mk ξ v) then false else true

lemma wireOpen_eq_false_iff {ξ : G.BoundaryPartition} {v : G.Vertex} :
    G.wireOpen ξ v = false ↔ v = blockRep G ξ (Quot.mk ξ v) := by
  classical
  constructor
  · intro hv
    unfold wireOpen at hv
    by_cases h : v = blockRep G ξ (Quot.mk ξ v)
    · exact h
    · rw [ite_eq_right h] at hv
      exact absurd hv (by decide)
  · intro h
    unfold wireOpen
    rw [ite_eq_left h]

lemma wireOpen_eq_true_iff {ξ : G.BoundaryPartition} {v : G.Vertex} :
    G.wireOpen ξ v = true ↔ v ≠ blockRep G ξ (Quot.mk ξ v) := by
  classical
  constructor
  · intro hv
    unfold wireOpen at hv
    by_cases h : v = blockRep G ξ (Quot.mk ξ v)
    · rw [ite_eq_left h] at hv
      exact absurd hv (by decide)
    · exact h
  · intro h
    unfold wireOpen
    rw [ite_eq_right h]

/-- The augmented open/closed configuration: labelled edges follow `ω`, and the
artificial wiring edge of a vertex is open exactly when it is not a loop. -/
noncomputable def augConfig (ξ : G.BoundaryPartition) (ω : G.Configuration)
    (x : G.Edge ⊕ G.Vertex) : Bool :=
  match x with
  | Sum.inl e => ω e
  | Sum.inr v => G.wireOpen ξ v


section Wiring

variable {G : LabelledMultigraph} {ξ : G.BoundaryPartition} {ω : G.Configuration}
variable [DecidableEq G.Vertex] [DecidableEq G.Edge]

/-- The skeleton of the augmented graph, whose open edges are the open labelled
edges together with the block-wiring edges. -/
noncomputable abbrev wiringSkeleton (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    (ω : G.Configuration) : SimpleGraph G.Vertex :=
  FinFKG.skeleton (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ ω))

lemma mem_openSet_augConfig_inl (e : G.Edge) :
    Sum.inl e ∈ FinFKG.openSet (G.augConfig ξ ω) ↔ ω e = true := by
  rw [FinFKG.mem_openSet]
  rfl

lemma mem_openSet_augConfig_inr (v : G.Vertex) :
    Sum.inr v ∈ FinFKG.openSet (G.augConfig ξ ω) ↔ v ≠ blockRep G ξ (Quot.mk ξ v) := by
  rw [FinFKG.mem_openSet]
  have h : G.augConfig ξ ω (Sum.inr v) = G.wireOpen ξ v := rfl
  rw [h, wireOpen_eq_true_iff]

/-- The wiring edge of a vertex is a genuine skeleton edge unless it is a loop. -/
lemma wiringSkeleton_adj_wire {v : G.Vertex} (hv : v ≠ blockRep G ξ (Quot.mk ξ v)) :
    (wiringSkeleton G ξ ω).Adj v (blockRep G ξ (Quot.mk ξ v)) := by
  refine ⟨hv, Sum.inr v, ?_, Or.inl ⟨rfl, rfl⟩⟩
  rw [mem_openSet_augConfig_inr]
  exact hv

/-- Every vertex reaches its block representative in the wiring skeleton. -/
lemma wiringSkeleton_reachable_rep (v : G.Vertex) :
    (wiringSkeleton G ξ ω).Reachable v (blockRep G ξ (Quot.mk ξ v)) := by
  by_cases hv : v = blockRep G ξ (Quot.mk ξ v)
  · rw [hv]
    have hspec : Quot.mk ξ (blockRep G ξ (Quot.mk ξ v)) = Quot.mk ξ v :=
      blockRep_spec G ξ (Quot.mk ξ v)
    rw [hspec]
  · exact (wiringSkeleton_adj_wire hv).reachable

/-- Every wired connection is a pair of vertices joined in the wiring skeleton. -/
lemma wiringSkeleton_reachable_of_wired {a c : G.Vertex} (h : ξ.r a c) :
    (wiringSkeleton G ξ ω).Reachable a c := by
  have hblock : Quot.mk ξ a = Quot.mk ξ c := Quot.sound h
  have hrep : blockRep G ξ (Quot.mk ξ a) = blockRep G ξ (Quot.mk ξ c) := by rw [hblock]
  refine (wiringSkeleton_reachable_rep a).trans ?_
  rw [hrep]
  exact (wiringSkeleton_reachable_rep c).symm

/-- Every open labelled edge joins its endpoints in the wiring skeleton. -/
lemma wiringSkeleton_reachable_of_open {a c : G.Vertex} (hne : a ≠ c) {e : G.Edge}
    (he : ω e = true) (hjoin : G.Joins e a c) :
    (wiringSkeleton G ξ ω).Reachable a c := by
  refine SimpleGraph.Adj.reachable ?_
  refine ⟨hne, Sum.inl e, ?_, ?_⟩
  · rw [mem_openSet_augConfig_inl]; exact he
  · exact hjoin

/-- Reachability in the wired connection graph implies reachability in the
wiring skeleton. -/
lemma wiringSkeleton_reachable_of_connectionGraph {u v : G.Vertex}
    (h : (G.connectionGraph ξ ω).Reachable u v) : (wiringSkeleton G ξ ω).Reachable u v := by
  have step : ∀ a c : G.Vertex, (G.connectionGraph ξ ω).Adj a c →
      (wiringSkeleton G ξ ω).Reachable a c := by
    rintro a c ⟨hne, hwire | ⟨e, he, hjoin⟩⟩
    · exact wiringSkeleton_reachable_of_wired hwire
    · exact wiringSkeleton_reachable_of_open hne he hjoin
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => (wiringSkeleton G ξ ω).Reachable a v) h ?_ ?_
  · exact SimpleGraph.Reachable.refl v
  · intro a c hac _ ih
    exact (step a c hac).trans ih

/-- Every wiring-skeleton edge is a wired connection. -/
lemma connectionGraph_reachable_of_wiringSkeleton_adj {a c : G.Vertex}
    (h : (wiringSkeleton G ξ ω).Adj a c) : (G.connectionGraph ξ ω).Reachable a c := by
  obtain ⟨hne, x, hx, horient⟩ := h
  rcases x with e | v
  · rw [mem_openSet_augConfig_inl] at hx
    refine SimpleGraph.Adj.reachable ⟨hne, Or.inr ⟨e, hx, ?_⟩⟩
    exact horient
  · rw [mem_openSet_augConfig_inr] at hx
    have hblock : Quot.mk ξ a = Quot.mk ξ c := by
      rcases horient with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h1' : v = a := h1
        have h2' : blockRep G ξ (Quot.mk ξ v) = c := h2
        calc Quot.mk ξ a = Quot.mk ξ v := by rw [← h1']
          _ = Quot.mk ξ (blockRep G ξ (Quot.mk ξ v)) :=
            (blockRep_spec G ξ (Quot.mk ξ v)).symm
          _ = Quot.mk ξ c := by rw [h2']
      · have h1' : v = c := h1
        have h2' : blockRep G ξ (Quot.mk ξ v) = a := h2
        calc Quot.mk ξ a = Quot.mk ξ (blockRep G ξ (Quot.mk ξ v)) := by rw [← h2']
          _ = Quot.mk ξ v := blockRep_spec G ξ (Quot.mk ξ v)
          _ = Quot.mk ξ c := by rw [← h1']
    refine SimpleGraph.Adj.reachable ⟨hne, Or.inl ?_⟩
    exact Quotient.exact hblock

/-- Reachability in the wiring skeleton implies reachability in the wired
connection graph. -/
lemma connectionGraph_reachable_of_wiringSkeleton {u v : G.Vertex}
    (h : (wiringSkeleton G ξ ω).Reachable u v) : (G.connectionGraph ξ ω).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => (G.connectionGraph ξ ω).Reachable a v) h ?_ ?_
  · exact SimpleGraph.Reachable.refl v
  · intro a c hac _ ih
    exact (connectionGraph_reachable_of_wiringSkeleton_adj hac).trans ih

end Wiring

section Main

variable {G : LabelledMultigraph}

/-- **Boundary wiring is a free boundary condition after adding one artificial
edge per vertex to its block representative**: the number of wired open
components of a configuration is the number of components of the augmented free
boundary skeleton. -/
theorem componentCount_eq_card_components_wiringSkeleton (ξ : G.BoundaryPartition)
    (ω : G.Configuration) :
    G.componentCount ξ ω = Nat.card (wiringSkeleton G ξ ω).ConnectedComponent := by
  classical
  unfold LabelledMultigraph.componentCount
  refine FinFKG.card_components_eq_of_reachable_iff ?_
  intro u v
  exact ⟨wiringSkeleton_reachable_of_connectionGraph,
    connectionGraph_reachable_of_wiringSkeleton⟩


/-- The augmented configuration of a supremum is the supremum of the augmented
configurations. -/
lemma augConfig_sup (ξ : G.BoundaryPartition) (ω η : G.Configuration) :
    G.augConfig ξ (ω ⊔ η) = G.augConfig ξ ω ⊔ G.augConfig ξ η := by
  funext x
  rcases x with e | v
  · rfl
  · show G.wireOpen ξ v = (G.wireOpen ξ v ⊔ G.wireOpen ξ v)
    cases G.wireOpen ξ v <;> rfl

/-- The augmented configuration of an infimum is the infimum of the augmented
configurations. -/
lemma augConfig_inf (ξ : G.BoundaryPartition) (ω η : G.Configuration) :
    G.augConfig ξ (ω ⊓ η) = G.augConfig ξ ω ⊓ G.augConfig ξ η := by
  funext x
  rcases x with e | v
  · rfl
  · show G.wireOpen ξ v = (G.wireOpen ξ v ⊓ G.wireOpen ξ v)
    cases G.wireOpen ξ v <;> rfl

/-- **The wired component count is the corank of the augmented free-boundary
edge span.** -/
theorem componentCount_eq_clusterCount [DecidableEq G.Vertex] [DecidableEq G.Edge]
    (ξ : G.BoundaryPartition) (ω : G.Configuration) :
    G.componentCount ξ ω =
      FinFKG.clusterCount (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ ω)) := by
  classical
  rw [componentCount_eq_card_components_wiringSkeleton]
  exact (FinFKG.clusterCount_eq_natCard_components (G.augEnds ξ)
    (FinFKG.openSet (G.augConfig ξ ω))).symm

/-- **Supermodularity of the wired component count**, for an arbitrary boundary
partition (setoid) and with loops and parallel labels allowed. -/
theorem componentCount_supermodular (ξ : G.BoundaryPartition) (ω η : G.Configuration) :
    G.componentCount ξ ω + G.componentCount ξ η ≤
      G.componentCount ξ (ω ⊔ η) + G.componentCount ξ (ω ⊓ η) := by
  classical
  have hcomp : ∀ ζ : G.Configuration, G.componentCount ξ ζ =
      FinFKG.clusterCount (G.augEnds ξ) (FinFKG.openSet (G.augConfig ξ ζ)) :=
    fun ζ => componentCount_eq_clusterCount ξ ζ
  have hsup : FinFKG.openSet (G.augConfig ξ (ω ⊔ η)) =
      FinFKG.openSet (G.augConfig ξ ω) ∪ FinFKG.openSet (G.augConfig ξ η) := by
    rw [augConfig_sup, FinFKG.openSet_sup]
  have hinf : FinFKG.openSet (G.augConfig ξ (ω ⊓ η)) =
      FinFKG.openSet (G.augConfig ξ ω) ∩ FinFKG.openSet (G.augConfig ξ η) := by
    rw [augConfig_inf, FinFKG.openSet_inf]
  rw [hcomp, hcomp, hcomp, hcomp, hsup, hinf]
  exact FinFKG.clusterCount_supermodular (G.augEnds ξ)
    (FinFKG.openSet (G.augConfig ξ ω)) (FinFKG.openSet (G.augConfig ξ η))

/-- The real-valued unnormalised FK weight of the labelled multigraph, with an
arbitrary boundary setoid. -/
noncomputable def fkWeightR (q p : NNReal) (ξ : G.BoundaryPartition)
    (ω : G.Configuration) : ℝ :=
  (∏ e, if ω e then (p : ℝ) else 1 - (p : ℝ)) * (q : ℝ) ^ G.componentCount ξ ω

lemma fkWeightR_eq_coe (q p : NNReal) (hp1 : p ≤ 1) (ξ : G.BoundaryPartition)
    (ω : G.Configuration) :
    G.fkWeightR q p ξ ω = (G.fkWeight q p ξ ω : ℝ) := by
  classical
  unfold fkWeightR LabelledMultigraph.fkWeight LabelledMultigraph.edgeWeight
  push_cast
  congr 1
  refine Finset.prod_congr rfl (fun e _ => ?_)
  by_cases h : ω e = true <;> simp [h, NNReal.coe_sub, hp1]

lemma fkWeightR_pos {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (ω : G.Configuration) : 0 < G.fkWeightR q p ξ ω := by
  rw [fkWeightR_eq_coe q p hp1.le]
  exact_mod_cast G.fkWeight_pos hq hp0 hp1 ξ ω

/-- Pointwise comparison of real products (Mathlib's `Finset.prod_le_prod` is
not available for `ℝ` in this toolchain). -/
lemma prod_le_prod_of_le_real {ι : Type*} [DecidableEq ι] (s : Finset ι) {f g : ι → ℝ}
    (h : ∀ i ∈ s, f i ≤ g i) (hf0 : ∀ i ∈ s, 0 ≤ f i) (h0 : ∀ i ∈ s, 0 ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : f a ≤ g a := h a (Finset.mem_insert_self a s)
      have hga : 0 ≤ g a := h0 a (Finset.mem_insert_self a s)
      have ih' : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      have hfprod : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
      exact mul_le_mul hfa ih' hfprod hga

/-- A single Bernoulli factor is nonnegative for `0 < p < 1`. -/
lemma bern_factor_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    (0 : ℝ) ≤ (if b then p else 1 - p) := by
  by_cases h : b = true
  · rw [ite_eq_left h]; exact le_of_lt hp0
  · rw [ite_eq_right h]; linarith

/-- Each single-edge Bernoulli factor is nonnegative for `0 < p < 1`. -/
lemma prod_factor_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (z : G.Configuration) :
    (0 : ℝ) ≤ ∏ e, if z e then p else 1 - p := by
  refine Finset.prod_nonneg (fun e _ => ?_)
  by_cases h : z e = true
  · rw [ite_eq_left h]; exact le_of_lt hp0
  · rw [ite_eq_right h]; linarith

/-- **The lattice condition (log-supermodularity) for the actual finite FK weight
at `q ≥ 1`**, with an arbitrary boundary setoid, loops and parallel labels. -/
theorem fkWeightR_lc {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) :
    ∀ x y : G.Configuration, G.fkWeightR q p ξ x * G.fkWeightR q p ξ y ≤
      G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y) := by
  classical
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  intro x y
  have hκ : G.componentCount ξ x + G.componentCount ξ y ≤
      G.componentCount ξ (x ⊔ y) + G.componentCount ξ (x ⊓ y) :=
    G.componentCount_supermodular ξ x y
  have hqpart : (q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y ≤
      (q : ℝ) ^ G.componentCount ξ (x ⊔ y) * (q : ℝ) ^ G.componentCount ξ (x ⊓ y) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hqR hκ
  have hφ : (∏ e, if x e then (p : ℝ) else 1 - (p : ℝ)) *
      (∏ e, if y e then (p : ℝ) else 1 - (p : ℝ)) =
      (∏ e, if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ)) *
        (∏ e, if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ)) :=
    FinFKG.bernoulli_lc (fun _ : G.Edge => (p : ℝ)) x y
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hfac : ∀ (z : G.Configuration),
      (0 : ℝ) ≤ ∏ e, if z e then (p : ℝ) else 1 - (p : ℝ) := by
    intro z
    refine Finset.prod_nonneg (fun e _ => ?_)
    by_cases h : z e = true
    · rw [ite_eq_left h]; exact le_of_lt hp0R
    · rw [ite_eq_right h]; linarith
  calc G.fkWeightR q p ξ x * G.fkWeightR q p ξ y
      = ((∏ e, if x e then (p : ℝ) else 1 - (p : ℝ)) *
          (∏ e, if y e then (p : ℝ) else 1 - (p : ℝ))) *
          ((q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y) := by
        unfold fkWeightR
        ring
    _ ≤ ((∏ e, if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ)) *
          (∏ e, if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          ((q : ℝ) ^ G.componentCount ξ (x ⊔ y) *
            (q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by
        rw [hφ]
        exact mul_le_mul_of_nonneg_left hqpart (mul_nonneg (hfac _) (hfac _))
    _ = G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y) := by
        unfold fkWeightR
        ring

/-- Monotone decrease of powers of a number in `[0,1]`. -/
lemma pow_le_pow_of_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    q ^ m ≤ q ^ n := by
  have h : q ^ m = q ^ n * q ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnm]
  rw [h]
  calc q ^ n * q ^ (m - n) ≤ q ^ n * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 n)
    _ = q ^ n := mul_one _

/-- **The reversed lattice condition for the actual FK weight at `0 < q ≤ 1`**,
with an arbitrary boundary setoid.  No association conclusion is drawn from it;
see `fkWeightR_lc_fails_of_lt_one` for the exact sense in which `q < 1` leaves the
FKG hypothesis. -/
theorem fkWeightR_lc_rev {q p : NNReal} (hq0 : 0 < q) (hq1 : q ≤ 1) (hp0 : 0 < p)
    (hp1 : p < 1) (ξ : G.BoundaryPartition) :
    ∀ x y : G.Configuration, G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y) ≤
      G.fkWeightR q p ξ x * G.fkWeightR q p ξ y := by
  classical
  have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hq0
  have hq1R : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  intro x y
  have hqpart : (q : ℝ) ^ G.componentCount ξ (x ⊔ y) * (q : ℝ) ^ G.componentCount ξ (x ⊓ y) ≤
      (q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_of_le_one hq0R hq1R (G.componentCount_supermodular ξ x y)
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hfac : ∀ (z : G.Configuration),
      (0 : ℝ) ≤ ∏ e, if z e then (p : ℝ) else 1 - (p : ℝ) := by
    intro z
    refine Finset.prod_nonneg (fun e _ => ?_)
    by_cases h : z e = true
    · rw [ite_eq_left h]; exact le_of_lt hp0R
    · rw [ite_eq_right h]; linarith
  have hφ : (∏ e, if x e then (p : ℝ) else 1 - (p : ℝ)) *
      (∏ e, if y e then (p : ℝ) else 1 - (p : ℝ)) =
      (∏ e, if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ)) *
        (∏ e, if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ)) :=
    FinFKG.bernoulli_lc (fun _ : G.Edge => (p : ℝ)) x y
  calc G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y)
      = ((∏ e, if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ)) *
          (∏ e, if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          ((q : ℝ) ^ G.componentCount ξ (x ⊔ y) *
            (q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by
        unfold fkWeightR
        ring
    _ ≤ ((∏ e, if x e then (p : ℝ) else 1 - (p : ℝ)) *
          (∏ e, if y e then (p : ℝ) else 1 - (p : ℝ))) *
          ((q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y) := by
        rw [← hφ]
        exact mul_le_mul_of_nonneg_left hqpart (mul_nonneg (hfac _) (hfac _))
    _ = G.fkWeightR q p ξ x * G.fkWeightR q p ξ y := by
        unfold fkWeightR
        ring

/-- Strict decrease of powers of a number in `(0,1)`. -/
lemma pow_lt_pow_of_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {n m : ℕ} (hnm : n < m) :
    q ^ m < q ^ n := by
  have h : q ^ m = q ^ n * q ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hnm)]
  have hpos : 0 < q ^ n := pow_pos hq0 n
  have hle : q ^ (m - n) ≤ q ^ 1 :=
    pow_le_pow_of_le_one (le_of_lt hq0) (le_of_lt hq1) (by omega)
  have hlt : q ^ (m - n) < 1 := lt_of_le_of_lt hle (by simpa using hq1)
  rw [h]
  calc q ^ n * q ^ (m - n) < q ^ n * 1 := mul_lt_mul_of_pos_left hlt hpos
    _ = q ^ n := mul_one _

/-- **The FKG lattice hypothesis genuinely fails for `0 < q < 1`.**  Wherever the
wired component count is *strictly* supermodular at a pair of configurations, the
FK weight violates the lattice condition.  Hence positive association at `q < 1`
is not available from this route, and no such conclusion is claimed. -/
theorem fkWeightR_lc_fails_of_lt_one {q p : NNReal} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (ξ : G.BoundaryPartition) {x y : G.Configuration}
    (hstrict : G.componentCount ξ x + G.componentCount ξ y <
      G.componentCount ξ (x ⊔ y) + G.componentCount ξ (x ⊓ y)) :
    ¬ (G.fkWeightR q p ξ x * G.fkWeightR q p ξ y ≤
        G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y)) := by
  classical
  intro hle
  set Φ : G.Configuration → ℝ := fun z => ∏ e, if z e then (p : ℝ) else 1 - (p : ℝ) with hΦ
  have hΦpos : ∀ z, 0 < Φ z := by
    intro z
    refine Finset.prod_pos (fun e _ => ?_)
    by_cases h : z e = true
    · rw [ite_eq_left h]; exact_mod_cast hp0
    · rw [ite_eq_right h]; linarith [show (p : ℝ) < 1 from by exact_mod_cast hp1]
  have hΦeq : Φ x * Φ y = Φ (x ⊔ y) * Φ (x ⊓ y) :=
    FinFKG.bernoulli_lc (fun _ : G.Edge => (p : ℝ)) x y
  rw [hΦ] at hΦeq
  have hexp : G.fkWeightR q p ξ x * G.fkWeightR q p ξ y =
      (Φ x * Φ y) * ((q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y) := by
    simp only [fkWeightR, hΦ]
    ring
  have hexp2 : G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y) =
      (Φ (x ⊔ y) * Φ (x ⊓ y)) *
        ((q : ℝ) ^ G.componentCount ξ (x ⊔ y) * (q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by
    simp only [fkWeightR, hΦ]
    ring
  rw [hexp, hexp2, hΦeq] at hle
  have hΦpos2 : (0 : ℝ) < Φ (x ⊔ y) * Φ (x ⊓ y) := mul_pos (hΦpos _) (hΦpos _)
  have hpow : (q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y ≤
      (q : ℝ) ^ G.componentCount ξ (x ⊔ y) * (q : ℝ) ^ G.componentCount ξ (x ⊓ y) :=
    le_of_mul_le_mul_left hle hΦpos2
  rw [← pow_add, ← pow_add] at hpow
  have hlt : (q : ℝ) ^ (G.componentCount ξ (x ⊔ y) + G.componentCount ξ (x ⊓ y)) <
      (q : ℝ) ^ (G.componentCount ξ x + G.componentCount ξ y) :=
    pow_lt_pow_of_lt_one (by exact_mod_cast hq0) (by exact_mod_cast hq1) hstrict
  linarith

/-- **Positive association (FKG) for the actual normalised finite FK measure at
`q ≥ 1`**: increasing nonnegative observables are positively correlated under
`FK.Finite.LabelledMultigraph.fkPMF`, for an arbitrary boundary setoid, with
loops and parallel labels allowed. -/
theorem fkPMF_association {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (f g : G.Configuration → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * f ω) *
        (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * g ω) ≤
      (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal) *
        (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * f ω * g ω) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set Z : ℝ := (G.partitionFunction q p ξ : ℝ) with hZdef
  have hZpos : 0 < Z := by
    rw [hZdef]
    exact_mod_cast G.partitionFunction_pos hqpos hp1.le ξ
  have htoReal : ∀ ω, (G.fkPMF hqpos hp1.le ξ ω).toReal =
      (G.fkWeight q p ξ ω : ℝ) / Z := by
    intro ω
    rw [G.fkPMF_apply hqpos hp1.le ξ ω]
    simp only [hZdef]
    rw [ENNReal.coe_toReal]
    rfl
  have hunnorm := FinFKG.fkg_of_lattice (P := fun ω => G.fkWeightR q p ξ ω)
    (fun ω => G.fkWeightR_pos hqpos hp0 hp1 ξ ω) (G.fkWeightR_lc hq hp0 hp1 ξ)
    f g hf hg hf0 hg0
  have hw : ∀ ω : G.Configuration, G.fkWeightR q p ξ ω = (G.fkWeight q p ξ ω : ℝ) :=
    fun ω => G.fkWeightR_eq_coe q p hp1.le ξ ω
  simp only [hw] at hunnorm
  have hconv : ∀ (h : G.Configuration → ℝ),
      (∑ ω, (G.fkPMF hqpos hp1.le ξ ω).toReal * h ω) =
        (∑ ω, (G.fkWeight q p ξ ω : ℝ) * h ω) / Z := by
    intro h
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [htoReal]
    ring
  have hone : (∑ ω, (G.fkPMF hqpos hp1.le ξ ω).toReal) = (∑ ω, (G.fkWeight q p ξ ω : ℝ)) / Z := by
    have h := hconv (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h]
  have hconv' : (∑ ω, (G.fkPMF hqpos hp1.le ξ ω).toReal * f ω * g ω) =
      (∑ ω, (G.fkWeight q p ξ ω : ℝ) * f ω * g ω) / Z := by
    have h := hconv (fun ω => f ω * g ω)
    simpa only [mul_assoc] using h
  rw [hconv f, hconv g, hone, hconv']
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right hunnorm (by positivity)

/-- The two-point monotone likelihood ratio behind `fkWeightR_mlr`. -/
lemma bool_factor_mlr {p₁ p₂ : ℝ} (hp12 : p₁ ≤ p₂) (a b : Bool) :
    (if a then p₁ else 1 - p₁) * (if b then p₂ else 1 - p₂) ≤
      (if (a ⊔ b) then p₂ else 1 - p₂) * (if (a ⊓ b) then p₁ else 1 - p₁) := by
  cases a <;> cases b <;> simp <;> linarith [hp12]

/-- **Monotone likelihood ratio in the edge probability**: raising `p` at fixed
`q ≥ 1` makes the FK weight more concentrated on configurations with more open
edges. -/
theorem fkWeightR_mlr {q : NNReal} (hq : 1 ≤ q) {p₁ p₂ : NNReal} (hp₁0 : 0 < p₁)
    (hp₂1 : p₂ < 1) (hp12 : p₁ ≤ p₂) (ξ : G.BoundaryPartition) :
    ∀ x y : G.Configuration, G.fkWeightR q p₁ ξ x * G.fkWeightR q p₂ ξ y ≤
      G.fkWeightR q p₂ ξ (x ⊔ y) * G.fkWeightR q p₁ ξ (x ⊓ y) := by
  classical
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp₁0R : (0 : ℝ) < p₁ := by exact_mod_cast hp₁0
  have hp₁1R : (p₁ : ℝ) < 1 := lt_of_le_of_lt (by exact_mod_cast hp12) (by exact_mod_cast hp₂1)
  have hp₂0R : (0 : ℝ) < p₂ := lt_of_lt_of_le hp₁0R (by exact_mod_cast hp12)
  have hp₂1R : (p₂ : ℝ) < 1 := by exact_mod_cast hp₂1
  have hp12R : (p₁ : ℝ) ≤ p₂ := by exact_mod_cast hp12
  intro x y
  have hκ : G.componentCount ξ x + G.componentCount ξ y ≤
      G.componentCount ξ (x ⊔ y) + G.componentCount ξ (x ⊓ y) :=
    G.componentCount_supermodular ξ x y
  have hqpart : (q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y ≤
      (q : ℝ) ^ G.componentCount ξ (x ⊔ y) * (q : ℝ) ^ G.componentCount ξ (x ⊓ y) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hqR hκ
  have hpt : ∀ e : G.Edge,
      (if x e then (p₁ : ℝ) else 1 - (p₁ : ℝ)) * (if y e then (p₂ : ℝ) else 1 - (p₂ : ℝ)) ≤
        (if (x ⊔ y) e then (p₂ : ℝ) else 1 - (p₂ : ℝ)) *
          (if (x ⊓ y) e then (p₁ : ℝ) else 1 - (p₁ : ℝ)) := by
    intro e
    rw [Pi.sup_apply, Pi.inf_apply]
    exact bool_factor_mlr hp12R (x e) (y e)

  have hφ : (∏ e, (if x e then (p₁ : ℝ) else 1 - (p₁ : ℝ)) *
        (if y e then (p₂ : ℝ) else 1 - (p₂ : ℝ))) ≤
      ∏ e, ((if (x ⊔ y) e then (p₂ : ℝ) else 1 - (p₂ : ℝ)) *
        (if (x ⊓ y) e then (p₁ : ℝ) else 1 - (p₁ : ℝ))) := by
    refine prod_le_prod_of_le_real Finset.univ (fun e _ => hpt e)
      (fun e _ => mul_nonneg (bern_factor_nonneg hp₁0R hp₁1R _)
        (bern_factor_nonneg hp₂0R hp₂1R _))
      (fun e _ => ?_)
    exact mul_nonneg (bern_factor_nonneg hp₂0R hp₂1R _) (bern_factor_nonneg hp₁0R hp₁1R _)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hφ
  calc G.fkWeightR q p₁ ξ x * G.fkWeightR q p₂ ξ y
      = ((∏ e, if x e then (p₁ : ℝ) else 1 - (p₁ : ℝ)) *
          (∏ e, if y e then (p₂ : ℝ) else 1 - (p₂ : ℝ))) *
          ((q : ℝ) ^ G.componentCount ξ x * (q : ℝ) ^ G.componentCount ξ y) := by
        unfold fkWeightR
        ring
    _ ≤ ((∏ e, if (x ⊔ y) e then (p₂ : ℝ) else 1 - (p₂ : ℝ)) *
          (∏ e, if (x ⊓ y) e then (p₁ : ℝ) else 1 - (p₁ : ℝ))) *
          ((q : ℝ) ^ G.componentCount ξ (x ⊔ y) *
            (q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by
        exact mul_le_mul hφ hqpart (by positivity)
          (mul_nonneg (prod_factor_nonneg hp₂0R hp₂1R _) (prod_factor_nonneg hp₁0R hp₁1R _))
    _ = G.fkWeightR q p₂ ξ (x ⊔ y) * G.fkWeightR q p₁ ξ (x ⊓ y) := by
        unfold fkWeightR
        ring

/-- **Monotonicity in the edge probability of the actual normalised FK measure at
`q ≥ 1`**: every increasing nonnegative observable has larger expectation at the
larger `p`.  With `f` the indicator of an increasing event this is stochastic
domination of the finite-volume FK measures. -/
theorem fkPMF_expectation_mono_p {q : NNReal} (hq : 1 ≤ q) {p₁ p₂ : NNReal}
    (hp₁0 : 0 < p₁) (hp₂1 : p₂ < 1) (hp12 : p₁ ≤ p₂) (ξ : G.BoundaryPartition)
    (f : G.Configuration → ℝ) (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) :
    (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) (le_trans hp12 hp₂1.le) ξ ω).toReal *
        f ω) ≤
      (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp₂1.le ξ ω).toReal * f ω) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp₁1 : p₁ < 1 := lt_of_le_of_lt hp12 hp₂1
  have hp₂0 : 0 < p₂ := lt_of_lt_of_le hp₁0 hp12
  set Z₁ : ℝ := (G.partitionFunction q p₁ ξ : ℝ) with hZ₁def
  set Z₂ : ℝ := (G.partitionFunction q p₂ ξ : ℝ) with hZ₂def
  have hZ₁ : 0 < Z₁ := by
    rw [hZ₁def]; exact_mod_cast G.partitionFunction_pos hqpos hp₁1.le ξ
  have hZ₂ : 0 < Z₂ := by
    rw [hZ₂def]; exact_mod_cast G.partitionFunction_pos hqpos hp₂1.le ξ
  have hH := FinFKG.holley (P := fun ω => G.fkWeightR q p₁ ξ ω)
    (Q := fun ω => G.fkWeightR q p₂ ξ ω)
    (fun ω => G.fkWeightR_pos hqpos hp₁0 hp₁1 ξ ω)
    (fun ω => le_of_lt (G.fkWeightR_pos hqpos hp₂0 hp₂1 ξ ω))
    (G.fkWeightR_lc hq hp₁0 hp₁1 ξ) (G.fkWeightR_mlr hq hp₁0 hp₂1 hp12 ξ) f hf hf0
  have hw₁ : ∀ ω : G.Configuration, G.fkWeightR q p₁ ξ ω = (G.fkWeight q p₁ ξ ω : ℝ) :=
    fun ω => G.fkWeightR_eq_coe q p₁ hp₁1.le ξ ω
  have hw₂ : ∀ ω : G.Configuration, G.fkWeightR q p₂ ξ ω = (G.fkWeight q p₂ ξ ω : ℝ) :=
    fun ω => G.fkWeightR_eq_coe q p₂ hp₂1.le ξ ω
  simp only [hw₁, hw₂] at hH
  have hconv₁ : ∀ (h : G.Configuration → ℝ),
      (∑ ω, (G.fkPMF hqpos hp₁1.le ξ ω).toReal * h ω) =
        (∑ ω, (G.fkWeight q p₁ ξ ω : ℝ) * h ω) / Z₁ := by
    intro h
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [show (G.fkPMF hqpos hp₁1.le ξ ω).toReal = (G.fkWeight q p₁ ξ ω : ℝ) / Z₁ from ?_]
    · ring
    · rw [G.fkPMF_apply hqpos hp₁1.le ξ ω]
      simp only [hZ₁def]
      rw [ENNReal.coe_toReal]
      rfl
  have hconv₂ : ∀ (h : G.Configuration → ℝ),
      (∑ ω, (G.fkPMF hqpos hp₂1.le ξ ω).toReal * h ω) =
        (∑ ω, (G.fkWeight q p₂ ξ ω : ℝ) * h ω) / Z₂ := by
    intro h
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [show (G.fkPMF hqpos hp₂1.le ξ ω).toReal = (G.fkWeight q p₂ ξ ω : ℝ) / Z₂ from ?_]
    · ring
    · rw [G.fkPMF_apply hqpos hp₂1.le ξ ω]
      simp only [hZ₂def]
      rw [ENNReal.coe_toReal]
      rfl
  have hsum₁ : (∑ ω, (G.fkWeight q p₁ ξ ω : ℝ)) = Z₁ := by
    rw [hZ₁def]
    exact_mod_cast (rfl : G.partitionFunction q p₁ ξ = ∑ ω, G.fkWeight q p₁ ξ ω)
  have hsum₂ : (∑ ω, (G.fkWeight q p₂ ξ ω : ℝ)) = Z₂ := by
    rw [hZ₂def]
    exact_mod_cast (rfl : G.partitionFunction q p₂ ξ = ∑ ω, G.fkWeight q p₂ ξ ω)
  rw [hconv₁ f, hconv₂ f, div_le_div_iff₀ hZ₁ hZ₂]
  simp only [hsum₁, hsum₂] at hH
  calc (∑ ω, (G.fkWeight q p₁ ξ ω : ℝ) * f ω) * Z₂
      ≤ Z₁ * (∑ ω, (G.fkWeight q p₂ ξ ω : ℝ) * f ω) := hH
    _ = (∑ ω, (G.fkWeight q p₂ ξ ω : ℝ) * f ω) * Z₁ := mul_comm _ _


/-! ### Event form and Bernoulli domination -/

/-- Event form of positive association: increasing events are positively
correlated under the actual finite FK measure at `q ≥ 1`. -/
theorem fkPMF_association_events {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) (ξ : G.BoundaryPartition)
    {A B : G.Configuration → Prop} [DecidablePred A] [DecidablePred B]
    (hA : ∀ x y : G.Configuration, x ≤ y → A x → A y)
    (hB : ∀ x y : G.Configuration, x ≤ y → B x → B y) :
    (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal *
        FinFKG.indicator A ω) *
        (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal *
          FinFKG.indicator B ω) ≤
      (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal) *
        (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal *
          FinFKG.indicator A ω * FinFKG.indicator B ω) := by
  classical
  refine G.fkPMF_association hq hp0 hp1 ξ (FinFKG.indicator A) (FinFKG.indicator B)
    ?_ ?_ ?_ ?_
  · intro x y hxy
    by_cases h : A x
    · have h' : A y := hA x y hxy h
      simp [FinFKG.indicator, h, h']
    · simp only [FinFKG.indicator, h]
      split_ifs <;> simp_all
  · intro x y hxy
    by_cases h : B x
    · have h' : B y := hB x y hxy h
      simp [FinFKG.indicator, h, h']
    · simp only [FinFKG.indicator, h]
      split_ifs <;> simp_all
  · intro x
    simp only [FinFKG.indicator]
    split_ifs <;> simp_all
  · intro x
    simp only [FinFKG.indicator]
    split_ifs <;> simp_all

/-- The real Bernoulli edge mass is the real product of its factors. -/
lemma edgeWeight_coe_eq {p : NNReal} (hp : p ≤ 1) (ω : G.Configuration) :
    (G.edgeWeight p ω : ℝ) = ∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ)) := by
  unfold LabelledMultigraph.edgeWeight
  rw [NNReal.coe_prod]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  by_cases h : ω e = true
  · simp [h]
  · simp [h, NNReal.coe_sub, hp]

/-- The product Bernoulli weight on the finite configuration space has total mass
one. -/
lemma bernoulli_partition_sum {p : NNReal} (hp : p ≤ 1) :
    (∑ ω : G.Configuration, ∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ))) = 1 := by
  classical
  have h1 : (∑ ω : G.Configuration, (G.edgeWeight p ω : ℝ)) = 1 := by
    have h := LabelledMultigraph.sum_edgeWeight G hp
    have h' := congrArg (fun x : NNReal => (x : ℝ)) h
    simpa using h'
  have h2 : (∑ ω : G.Configuration, ∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ)))
      = ∑ ω : G.Configuration, (G.edgeWeight p ω : ℝ) :=
    Finset.sum_congr rfl (fun ω _ => (G.edgeWeight_coe_eq hp ω).symm)
  rw [h2, h1]

/-- **The finite FK measure with `q ≥ 1` is stochastically dominated by the
product Bernoulli-`p` law at the same `p`.**  Every increasing nonnegative
observable has smaller expectation under `fkPMF` than under the independent
Bernoulli law, for every boundary setoid (so in particular for wired boundary
conditions).  This is the correct orientation: raising `q` above `1` favours
more clusters, hence fewer open edges (already visible on a single edge, where
`q = 2`, `p = 1/2` gives edge probability `1/3`). -/
theorem fkPMF_expectation_le_bernoulli {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) (ξ : G.BoundaryPartition) (f : G.Configuration → ℝ)
    (hf : Monotone f) (hf0 : ∀ x, 0 ≤ f x) :
    (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal * f ω) ≤
      ∑ ω, (∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ))) * f ω := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  set Z : ℝ := (G.partitionFunction q p ξ : ℝ) with hZdef
  have hZ : 0 < Z := by
    rw [hZdef]; exact_mod_cast G.partitionFunction_pos hqpos hp1.le ξ
  have hP : ∀ ω : G.Configuration, 0 < G.fkWeightR q p ξ ω :=
    fun ω => G.fkWeightR_pos hqpos hp0 hp1 ξ ω
  have hQ : ∀ ω : G.Configuration,
      0 ≤ ∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ)) := by
    intro ω
    refine Finset.prod_nonneg (fun e _ => ?_)
    by_cases h : ω e = true
    · rw [ite_eq_left h]; exact le_of_lt hp0R
    · rw [ite_eq_right h]; linarith
  have hlc : ∀ x y : G.Configuration,
      G.fkWeightR q p ξ x * G.fkWeightR q p ξ y ≤
        G.fkWeightR q p ξ (x ⊔ y) * G.fkWeightR q p ξ (x ⊓ y) :=
    G.fkWeightR_lc hq hp0 hp1 ξ
  have hmlr : ∀ x y : G.Configuration,
      G.fkWeightR q p ξ x * (∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ))) ≤
        (∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          G.fkWeightR q p ξ (x ⊓ y) := by
    intro x y
    have hle : x ⊓ y ≤ x := by
      intro e
      rw [Pi.inf_apply]
      exact inf_le_left
    have hκ : G.componentCount ξ x ≤ G.componentCount ξ (x ⊓ y) :=
      G.componentCount_anti (ξ := ξ) hle
    have hqpart : (q : ℝ) ^ G.componentCount ξ x ≤
        (q : ℝ) ^ G.componentCount ξ (x ⊓ y) := pow_le_pow_right₀ hqR hκ
    have hΦeq : (∏ e, (if x e then (p : ℝ) else 1 - (p : ℝ))) *
        (∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ))) =
        (∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
          (∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ))) :=
      FinFKG.bernoulli_lc (fun _ : G.Edge => (p : ℝ)) x y
    have hfacX : (0 : ℝ) ≤ ∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ)) :=
      hQ (x ⊔ y)
    have hfacY : (0 : ℝ) ≤ ∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ)) :=
      hQ (x ⊓ y)
    calc G.fkWeightR q p ξ x * (∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ)))
        = ((∏ e, (if x e then (p : ℝ) else 1 - (p : ℝ))) *
            (∏ e, (if y e then (p : ℝ) else 1 - (p : ℝ)))) *
            ((q : ℝ) ^ G.componentCount ξ x) := by
          unfold fkWeightR
          ring
      _ = ((∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
            (∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ)))) *
            ((q : ℝ) ^ G.componentCount ξ x) := by rw [hΦeq]
      _ ≤ ((∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
            (∏ e, (if (x ⊓ y) e then (p : ℝ) else 1 - (p : ℝ)))) *
            ((q : ℝ) ^ G.componentCount ξ (x ⊓ y)) := by
          refine mul_le_mul_of_nonneg_left hqpart (mul_nonneg hfacX hfacY)
      _ = (∏ e, (if (x ⊔ y) e then (p : ℝ) else 1 - (p : ℝ))) *
            G.fkWeightR q p ξ (x ⊓ y) := by
          unfold fkWeightR
          ring
  have h := FinFKG.holley (P := fun ω => G.fkWeightR q p ξ ω)
    (Q := fun ω : G.Configuration => ∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ)))
    hP hQ hlc hmlr f hf hf0
  have hw : ∀ ω : G.Configuration, G.fkWeightR q p ξ ω = (G.fkWeight q p ξ ω : ℝ) :=
    fun ω => G.fkWeightR_eq_coe q p hp1.le ξ ω
  simp only [hw] at h
  have hPsum : (∑ ω : G.Configuration, ∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ))) = 1 :=
    G.bernoulli_partition_sum hp1.le
  have hQsum : (∑ ω : G.Configuration, (G.fkWeight q p ξ ω : ℝ)) = Z := by
    rw [hZdef]
    exact_mod_cast (rfl : G.partitionFunction q p ξ = ∑ ω, G.fkWeight q p ξ ω)
  simp only [hPsum, hQsum, mul_one] at h
  have hconv : (∑ ω, (G.fkPMF hqpos hp1.le ξ ω).toReal * f ω) =
      (∑ ω, (G.fkWeight q p ξ ω : ℝ) * f ω) / Z := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [show (G.fkPMF hqpos hp1.le ξ ω).toReal = (G.fkWeight q p ξ ω : ℝ) / Z from ?_]
    · ring
    · rw [G.fkPMF_apply hqpos hp1.le ξ ω]
      simp only [hZdef]
      rw [ENNReal.coe_toReal]
      rfl
  rw [hconv, div_le_iff₀ hZ]
  calc (∑ ω, (G.fkWeight q p ξ ω : ℝ) * f ω)
      ≤ Z * (∑ ω, (∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ))) * f ω) := h
    _ = (∑ ω, (∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ))) * f ω) * Z := mul_comm _ _

/-- Event form of the Bernoulli domination: at `q ≥ 1` every increasing event has
FK probability at most its product Bernoulli-`p` probability, for every boundary
setoid.  In particular every single edge is open with probability at most `p`. -/
theorem fkPMF_event_le_bernoulli {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) (ξ : G.BoundaryPartition)
    {A : G.Configuration → Prop} [DecidablePred A]
    (hA : ∀ x y : G.Configuration, x ≤ y → A x → A y) :
    (∑ ω, (G.fkPMF (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ ω).toReal *
        FinFKG.indicator A ω) ≤
      ∑ ω, (∏ e, (if ω e then (p : ℝ) else 1 - (p : ℝ))) * FinFKG.indicator A ω := by
  classical
  refine G.fkPMF_expectation_le_bernoulli hq hp0 hp1 ξ (FinFKG.indicator A) ?_ ?_
  · intro x y hxy
    by_cases h : A x
    · have h' : A y := hA x y hxy h
      simp [FinFKG.indicator, h, h']
    · simp only [FinFKG.indicator, h]
      split_ifs <;> simp_all
  · intro x
    simp only [FinFKG.indicator]
    split_ifs <;> simp_all

end Main

/-! ### A concrete finite instance of strict supermodularity

The two-vertex graph with two parallel edges, with only one of the two edges open
in each of `x` and `y`: `κ x = κ y = κ (x ⊔ y) = 1` but `κ (x ⊓ y) = 2`. -/

section ParallelExample

/-- The two-vertex graph with two parallel edges. -/
abbrev parallelGraph : LabelledMultigraph where
  Vertex := Bool
  Edge := Bool
  fintypeVertex := inferInstance
  fintypeEdge := inferInstance
  source := fun _ => false
  target := fun _ => true

lemma parallelGraph_componentCount_of_open {ω : parallelGraph.Configuration}
    (h : ∃ e, ω e = true) : parallelGraph.componentCount parallelGraph.freeBoundary ω = 1 := by
  classical
  haveI : Nonempty parallelGraph.Vertex := ⟨false⟩
  have hpre : (parallelGraph.connectionGraph parallelGraph.freeBoundary ω).Preconnected := by
    intro u v
    obtain ⟨e, he⟩ := h
    have hadj : (parallelGraph.connectionGraph parallelGraph.freeBoundary ω).Adj false true := by
      unfold LabelledMultigraph.connectionGraph
      exact And.intro (fun h => by cases h) (Or.inr ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
    rcases u with _ | _ <;> rcases v with _ | _
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _
  unfold LabelledMultigraph.componentCount
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hpre.subsingleton_connectedComponent, inferInstance⟩

lemma parallelGraph_componentCount_of_allClosed :
    parallelGraph.componentCount parallelGraph.freeBoundary
      (parallelGraph.allClosed) = 2 := by
  rw [LabelledMultigraph.componentCount_free_allClosed]
  simp

/-- The pair of configurations on which the component count is strictly
supermodular. -/
noncomputable def parX : parallelGraph.Configuration := fun e => if e = false then true else false
noncomputable def parY : parallelGraph.Configuration := fun e => if e = true then true else false

lemma parX_false : parX false = true := by simp [parX]
lemma parX_true : parX true = false := by simp [parX]
lemma parY_false : parY false = false := by simp [parY]
lemma parY_true : parY true = true := by simp [parY]

lemma parX_sup_parY : parX ⊔ parY = parallelGraph.allOpen := by
  funext e
  rcases e with _ | _ <;> simp [parX, parY, LabelledMultigraph.allOpen]

lemma parX_inf_parY : parX ⊓ parY = parallelGraph.allClosed := by
  funext e
  rcases e with _ | _ <;> simp [parX, parY, LabelledMultigraph.allClosed]

theorem parallelGraph_strict_supermodular :
    parallelGraph.componentCount parallelGraph.freeBoundary parX +
        parallelGraph.componentCount parallelGraph.freeBoundary parY <
      parallelGraph.componentCount parallelGraph.freeBoundary (parX ⊔ parY) +
        parallelGraph.componentCount parallelGraph.freeBoundary (parX ⊓ parY) := by
  have hX : parallelGraph.componentCount parallelGraph.freeBoundary parX = 1 :=
    parallelGraph_componentCount_of_open ⟨false, parX_false⟩
  have hY : parallelGraph.componentCount parallelGraph.freeBoundary parY = 1 :=
    parallelGraph_componentCount_of_open ⟨true, parY_true⟩
  have hsup : parallelGraph.componentCount parallelGraph.freeBoundary (parX ⊔ parY) = 1 := by
    rw [parX_sup_parY]
    exact parallelGraph_componentCount_of_open ⟨false, parX_false⟩
  have hinf : parallelGraph.componentCount parallelGraph.freeBoundary (parX ⊓ parY) = 2 := by
    rw [parX_inf_parY]
    exact parallelGraph_componentCount_of_allClosed
  rw [hX, hY, hsup, hinf]
  norm_num

/-- **The FK weight of an explicit finite graph violates the FKG lattice
condition for every `0 < q < 1`** (two vertices, two parallel edges, free
boundary, any `0 < p < 1`). -/
theorem parallelGraph_lattice_condition_fails {q p : NNReal} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ (parallelGraph.fkWeightR q p parallelGraph.freeBoundary parX *
          parallelGraph.fkWeightR q p parallelGraph.freeBoundary parY ≤
        parallelGraph.fkWeightR q p parallelGraph.freeBoundary (parX ⊔ parY) *
          parallelGraph.fkWeightR q p parallelGraph.freeBoundary (parX ⊓ parY)) :=
  parallelGraph.fkWeightR_lc_fails_of_lt_one hq0 hq1 hp0 hp1 parallelGraph.freeBoundary
    parallelGraph_strict_supermodular

end ParallelExample

end FK.Finite.LabelledMultigraph

/-! ### Axiom audit

Every principal declaration below is printed with `#print axioms`; the expected
output is `['propext', 'Classical.choice', 'Quot.sound']` and in particular never
`sorryAx`, `Lean.ofReduceBool` or any user axiom. -/

#print axioms FinFKG.clusterCount_eq_natCard_components
#print axioms FinFKG.card_components_eq_of_reachable_iff
#print axioms FK.Finite.LabelledMultigraph.componentCount_eq_card_components_wiringSkeleton
#print axioms FK.Finite.LabelledMultigraph.componentCount_eq_clusterCount
#print axioms FK.Finite.LabelledMultigraph.componentCount_supermodular
#print axioms FK.Finite.LabelledMultigraph.fkWeightR_lc
#print axioms FK.Finite.LabelledMultigraph.fkWeightR_lc_rev
#print axioms FK.Finite.LabelledMultigraph.fkWeightR_mlr
#print axioms FK.Finite.LabelledMultigraph.fkWeightR_lc_fails_of_lt_one
#print axioms FK.Finite.LabelledMultigraph.fkPMF_association
#print axioms FK.Finite.LabelledMultigraph.fkPMF_expectation_mono_p
#print axioms FK.Finite.LabelledMultigraph.fkPMF_association_events
#print axioms FK.Finite.LabelledMultigraph.bernoulli_partition_sum
#print axioms FK.Finite.LabelledMultigraph.fkPMF_expectation_le_bernoulli
#print axioms FK.Finite.LabelledMultigraph.fkPMF_event_le_bernoulli
#print axioms FK.Finite.LabelledMultigraph.parallelGraph_strict_supermodular
#print axioms FK.Finite.LabelledMultigraph.parallelGraph_lattice_condition_fails
