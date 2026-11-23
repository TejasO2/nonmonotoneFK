import FK.AGSleevedAnnulus

/-!
# Uniform packing of genuine annular sleeves

We transport the simultaneous-sleeve templates through the lifted graph
automorphisms and apply the existing maximal whole-template packing.  The
selected templates are pairwise disjoint as *annulus and activation edges
together*, and every selected template is again an actual sleeve of a finite
set of base bonds.
-/

open Set
open scoped BigOperators Sym2

namespace FK.AGImplant
namespace Sleeve

open FK.EssentialEnhancement FK.AGPeeling
open CurvatureVariance.Infra.Percolation

universe u

variable {V : Type u} (H : SimpleGraph V)

/-- The lifted automorphism sends embedded base bonds to embedded base bonds. -/
@[simp] lemma automorphism_map_baseEdge (φ : H ≃g H) (e : H.edgeSet) :
    (automorphism H φ).mapEdgeSet (baseEdge H e) = baseEdge H (φ.mapEdgeSet e) := by
  apply Subtype.ext
  rw [FK.QuasiTransitive.iso_coe_mapEdgeSet, baseEdge_val, baseEdge_val,
    FK.QuasiTransitive.iso_coe_mapEdgeSet, Sym2.map_map, Sym2.map_map]
  rfl

/-- The endpoints of a mapped bond, in their canonical order, are either the
images of the old canonical endpoints or their reversals. -/
lemma mapped_out_endpoints (φ : H ≃g H) (e : H.edgeSet) :
    s(((φ.mapEdgeSet e : H.edgeSet) : Sym2 V).out.1,
        ((φ.mapEdgeSet e : H.edgeSet) : Sym2 V).out.2) =
      s(φ (e : Sym2 V).out.1, φ (e : Sym2 V).out.2) := by
  calc
    _ = ((φ.mapEdgeSet e : H.edgeSet) : Sym2 V) := Quot.out_eq _
    _ = Sym2.map φ (e : Sym2 V) := FK.QuasiTransitive.iso_coe_mapEdgeSet φ e
    _ = Sym2.map φ s((e : Sym2 V).out.1, (e : Sym2 V).out.2) :=
      congrArg (Sym2.map φ) (Quot.out_eq (e : Sym2 V)).symm
    _ = _ := Sym2.map_mk _ _ _

/-- A lifted automorphism either preserves the two spoke labels or exchanges
them.  This is the exact statement needed for invariance of the bypass edge
set; canonical `Sym2.out` orientation need not be preserved. -/
lemma automorphism_map_spokes (φ : H ≃g H) (e : H.edgeSet) :
    ((automorphism H φ).mapEdgeSet (leftSpoke H e) =
        leftSpoke H (φ.mapEdgeSet e) ∧
      (automorphism H φ).mapEdgeSet (rightSpoke H e) =
        rightSpoke H (φ.mapEdgeSet e)) ∨
    ((automorphism H φ).mapEdgeSet (leftSpoke H e) =
        rightSpoke H (φ.mapEdgeSet e) ∧
      (automorphism H φ).mapEdgeSet (rightSpoke H e) =
        leftSpoke H (φ.mapEdgeSet e)) := by
  have h := Sym2.eq_iff.mp (mapped_out_endpoints H φ e)
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    constructor <;> apply Subtype.ext
    · rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
      change Sym2.map (automorphism H φ)
        s(Sum.inl (e : Sym2 V).out.1, Sum.inr e) = _
      rw [Sym2.map_mk]
      change s(Sum.inl (φ (e : Sym2 V).out.1), Sum.inr (φ.mapEdgeSet e)) =
        s(Sum.inl ((φ.mapEdgeSet e : H.edgeSet) : Sym2 V).out.1,
          Sum.inr (φ.mapEdgeSet e))
      rw [← h₁]
    · rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
      change Sym2.map (automorphism H φ)
        s(Sum.inr e, Sum.inl (e : Sym2 V).out.2) = _
      rw [Sym2.map_mk]
      change s(Sum.inr (φ.mapEdgeSet e), Sum.inl (φ (e : Sym2 V).out.2)) =
        s(Sum.inr (φ.mapEdgeSet e),
          Sum.inl ((φ.mapEdgeSet e : H.edgeSet) : Sym2 V).out.2)
      rw [← h₂]
  · right
    constructor <;> apply Subtype.ext
    · rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
      change Sym2.map (automorphism H φ)
        s(Sum.inl (e : Sym2 V).out.1, Sum.inr e) = _
      rw [Sym2.map_mk]
      change s(Sum.inl (φ (e : Sym2 V).out.1), Sum.inr (φ.mapEdgeSet e)) =
        s(Sum.inr (φ.mapEdgeSet e),
          Sum.inl ((φ.mapEdgeSet e : H.edgeSet) : Sym2 V).out.2)
      rw [← h₂]
      exact Sym2.eq_swap
    · rw [FK.QuasiTransitive.iso_coe_mapEdgeSet]
      change Sym2.map (automorphism H φ)
        s(Sum.inr e, Sum.inl (e : Sym2 V).out.2) = _
      rw [Sym2.map_mk]
      change s(Sum.inr (φ.mapEdgeSet e), Sum.inl (φ (e : Sym2 V).out.2)) =
        s(Sum.inl ((φ.mapEdgeSet e : H.edgeSet) : Sym2 V).out.1,
          Sum.inr (φ.mapEdgeSet e))
      rw [← h₁]
      exact Sym2.eq_swap

/-- One complete finite sleeve template: its original-bond annulus together
with every activated bypass edge. -/
noncomputable def template (S : Finset H.edgeSet) : Finset (graph H).edgeSet := by
  classical
  exact annulus H S ∪ edges H S

@[simp] lemma mem_template {S : Finset H.edgeSet} {f : (graph H).edgeSet} :
    f ∈ template H S ↔ f ∈ annulus H S ∨ f ∈ edges H S := by
  simp [template]

lemma card_template (S : Finset H.edgeSet) :
    (template H S).card = S.card + (edges H S).card := by
  classical
  rw [template, Finset.card_union_of_disjoint (disjoint_annulus_edges H S),
    card_annulus]

lemma card_template_le (S : Finset H.edgeSet) :
    (template H S).card ≤ 3 * S.card := by
  rw [card_template]
  have h := card_edges_le H S
  omega

/-- The pair of bypass spokes is invariant under a lifted automorphism. -/
lemma automorphism_map_spokeEdges [DecidableEq (graph H).edgeSet]
    (φ : H ≃g H) (e : H.edgeSet) :
    FK.QuasiTransitive.translateSupport (automorphism H φ)
      ({leftSpoke H e, rightSpoke H e} : Finset (graph H).edgeSet) =
      {leftSpoke H (φ.mapEdgeSet e), rightSpoke H (φ.mapEdgeSet e)} := by
  classical
  rcases automorphism_map_spokes H φ e with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp [FK.QuasiTransitive.translateSupport, hl, hr]
  · simp [FK.QuasiTransitive.translateSupport, hl, hr]
    exact Finset.pair_comm _ _

/-- Annuli are exactly transported to annuli of the image bond set. -/
lemma automorphism_map_annulus (φ : H ≃g H) (S : Finset H.edgeSet) :
    FK.QuasiTransitive.translateSupport (automorphism H φ) (annulus H S) =
      annulus H (S.map φ.mapEdgeSet.toEmbedding) := by
  classical
  ext f
  simp only [FK.QuasiTransitive.mem_translateSupport_iff, mem_annulus]
  constructor
  · rintro ⟨g, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨φ.mapEdgeSet e, Finset.mem_map.mpr ⟨e, he, rfl⟩,
      (automorphism_map_baseEdge H φ e).symm⟩
  · rintro ⟨e', he', hf⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp he'
    exact ⟨baseEdge H e, ⟨e, he, rfl⟩,
      (automorphism_map_baseEdge H φ e).trans hf⟩

/-- All activation edges are exactly transported to those of the image bond
set, irrespective of the two possible canonical endpoint orientations. -/
lemma automorphism_map_edges (φ : H ≃g H) (S : Finset H.edgeSet) :
    FK.QuasiTransitive.translateSupport (automorphism H φ) (edges H S) =
      edges H (S.map φ.mapEdgeSet.toEmbedding) := by
  classical
  ext f
  rw [FK.QuasiTransitive.mem_translateSupport_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨e, he, hgp⟩ := Finset.mem_biUnion.mp hg
    have hmem : (automorphism H φ).mapEdgeSet g ∈
        FK.QuasiTransitive.translateSupport (automorphism H φ)
          ({leftSpoke H e, rightSpoke H e} : Finset (graph H).edgeSet) :=
      FK.QuasiTransitive.mem_translateSupport_iff.mpr ⟨g, hgp, rfl⟩
    rw [automorphism_map_spokeEdges] at hmem
    exact Finset.mem_biUnion.mpr
      ⟨φ.mapEdgeSet e, Finset.mem_map.mpr ⟨e, he, rfl⟩, hmem⟩
  · intro hf
    obtain ⟨e', he', hf'⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp he'
    have hmem : f ∈ FK.QuasiTransitive.translateSupport (automorphism H φ)
        ({leftSpoke H e, rightSpoke H e} : Finset (graph H).edgeSet) := by
      rwa [automorphism_map_spokeEdges]
    obtain ⟨g, hg, rfl⟩ := FK.QuasiTransitive.mem_translateSupport_iff.mp hmem
    exact ⟨g, Finset.mem_biUnion.mpr ⟨e, he, hg⟩, rfl⟩

/-- A complete template translates to the complete template of the image base
bonds. -/
lemma automorphism_map_template (φ : H ≃g H) (S : Finset H.edgeSet) :
    FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) =
      template H (S.map φ.mapEdgeSet.toEmbedding) := by
  classical
  simp only [template, FK.QuasiTransitive.translateSupport, Finset.map_union]
  exact congrArg₂ (· ∪ ·) (automorphism_map_annulus H φ S)
    (automorphism_map_edges H φ S)

@[simp] lemma card_map_mapEdgeSet (φ : H ≃g H) (S : Finset H.edgeSet) :
    (S.map φ.mapEdgeSet.toEmbedding).card = S.card := by
  classical
  simp

/-- Two edges sharing a vertex are at line-graph distance at most one. -/
lemma lineGraph_dist_le_one_of_common_vertex {W : Type*} {G : SimpleGraph W}
    {f g : G.edgeSet} {x : W} (hf : x ∈ (f : Sym2 W)) (hg : x ∈ (g : Sym2 W)) :
    G.lineGraph.dist f g ≤ 1 := by
  by_cases hfg : f = g
  · subst g
    simp
  · have hadj : G.lineGraph.Adj f g :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hfg, ⟨x, hf, hg⟩⟩
    simpa using G.lineGraph.dist_le hadj.toWalk

/-- An original vertex of a base bond belongs to its embedded base edge. -/
lemma inl_mem_baseEdge {e : H.edgeSet} {x : V} (hx : x ∈ (e : Sym2 V)) :
    Sum.inl x ∈ (baseEdge H e : Sym2 (V ⊕ H.edgeSet)) := by
  rw [baseEdge_val, Sym2.mem_map]
  exact ⟨x, hx, rfl⟩

/-- Every edge of the sleeved graph touches an embedded base edge in the line
graph.  The proof treats original bonds and both spoke orientations directly;
no finiteness is needed. -/
lemma exists_baseEdge_dist_le_one (f : (graph H).edgeSet) :
    ∃ e : H.edgeSet, (graph H).lineGraph.dist f (baseEdge H e) ≤ 1 := by
  generalize hx : (f : Sym2 (V ⊕ H.edgeSet)).out.1 = x
  generalize hy : (f : Sym2 (V ⊕ H.edgeSet)).out.2 = y
  have hxf : x ∈ (f : Sym2 (V ⊕ H.edgeSet)) := by
    rw [← hx]
    exact Sym2.out_fst_mem _
  have hyf : y ∈ (f : Sym2 (V ⊕ H.edgeSet)) := by
    rw [← hy]
    exact Sym2.out_snd_mem _
  have hxy : (graph H).Adj x y := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [show s(x, y) = (f : Sym2 (V ⊕ H.edgeSet)) by
      rw [← hx, ← hy]
      exact Quot.out_eq _]
    exact f.property
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          change Sum.inl x ∈ (f : Sym2 (V ⊕ H.edgeSet)) at hxf
          change H.Adj x y at hxy
          let e : H.edgeSet := ⟨s(x, y), by
            simpa [SimpleGraph.mem_edgeSet] using hxy⟩
          exact ⟨e, lineGraph_dist_le_one_of_common_vertex hxf
            (inl_mem_baseEdge H (e := e) (by simp [e]))⟩
      | inr e =>
          change Sum.inl x ∈ (f : Sym2 (V ⊕ H.edgeSet)) at hxf
          change x ∈ (e : Sym2 V) at hxy
          exact ⟨e, lineGraph_dist_le_one_of_common_vertex hxf
            (inl_mem_baseEdge H hxy)⟩
  | inr e =>
      cases y with
      | inl x =>
          change Sum.inl x ∈ (f : Sym2 (V ⊕ H.edgeSet)) at hyf
          change x ∈ (e : Sym2 V) at hxy
          exact ⟨e, lineGraph_dist_le_one_of_common_vertex hyf
            (inl_mem_baseEdge H hxy)⟩
      | inr f =>
          change False at hxy
          exact hxy.elim

/-- Edge-transitivity of the base graph gives a uniform local cover using
only lifted automorphisms.  This is stronger for the present construction than
a cover by arbitrary automorphisms of the sleeved graph. -/
lemma exists_lifted_template_localCover (hconn : H.Connected)
    (S : Finset H.edgeSet) {e₀ : H.edgeSet} (he₀ : e₀ ∈ S)
    (hedge : ∀ e f : H.edgeSet, ∃ φ : H ≃g H, φ.mapEdgeSet e = f) :
    ∃ K : ℕ, ∀ f : (graph H).edgeSet, ∃ φ : H ≃g H,
      ∀ g ∈ FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S),
        (graph H).lineGraph.dist f g ≤ K := by
  let e₀' : (graph H).edgeSet := baseEdge H e₀
  have he₀' : e₀' ∈ template H S := by
    apply (mem_template H).mpr
    exact Or.inl (baseEdge_mem_annulus H S he₀)
  obtain ⟨R, hR⟩ := FK.QuasiTransitive.exists_translateSupport_diam
    (template H S) he₀'
  letI : Nonempty (graph H).edgeSet := ⟨e₀'⟩
  have hLG : (graph H).lineGraph.Connected :=
    FK.QuasiTransitive.lineGraph_connected (graph H) (graphConnected H hconn)
  refine ⟨1 + R, fun f => ?_⟩
  obtain ⟨e, he⟩ := exists_baseEdge_dist_le_one H f
  obtain ⟨φ, hφ⟩ := hedge e₀ e
  refine ⟨φ, fun g hg => ?_⟩
  let ψ := automorphism H φ
  have hpivot : ψ.mapEdgeSet e₀' = baseEdge H e := by
    exact (automorphism_map_baseEdge H φ e₀).trans (congrArg (baseEdge H) hφ)
  calc
    (graph H).lineGraph.dist f g ≤
        (graph H).lineGraph.dist f (ψ.mapEdgeSet e₀') +
          (graph H).lineGraph.dist (ψ.mapEdgeSet e₀') g := hLG.dist_triangle
    _ ≤ 1 + R := Nat.add_le_add (by simpa [hpivot] using he) (by
      rw [SimpleGraph.dist_comm]
      exact hR ψ g hg)

/-- **Uniform separated packing of actual annular sleeves.**  The selected
whole templates are pairwise disjoint, their distinguished base pivots are at
bounded line-graph distance from every edge, and every template has at most
`3 * S.card` edges.  All indices are base automorphisms, so the exact transport
lemmas above identify each selected support as an actual sleeve. -/
theorem exists_uniform_sleeve_packing (hconn : H.Connected)
    (S : Finset H.edgeSet) {e₀ : H.edgeSet} (he₀ : e₀ ∈ S)
    (hr₀ : OnDoubleRay (baseEdge H e₀))
    (hedge : ∀ e f : H.edgeSet, ∃ φ : H ≃g H, φ.mapEdgeSet e = f) :
    ∃ M : Set (H ≃g H),
      M.PairwiseDisjoint (fun φ =>
        (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
          Set (graph H).edgeSet)) ∧
      FK.Theorem14.BoundedDistance (graph H).lineGraph.dist
        ((fun φ : H ≃g H => (automorphism H φ).mapEdgeSet (baseEdge H e₀)) '' M) ∧
      (∀ φ ∈ M, (FK.QuasiTransitive.translateSupport (automorphism H φ)
        (template H S)).card ≤ 3 * S.card) ∧
      (∀ p ∈ (fun φ : H ≃g H =>
        (automorphism H φ).mapEdgeSet (baseEdge H e₀)) '' M, OnDoubleRay p) := by
  classical
  let e₀' : (graph H).edgeSet := baseEdge H e₀
  have he₀' : e₀' ∈ template H S := by
    apply (mem_template H).mpr
    exact Or.inl (baseEdge_mem_annulus H S he₀)
  obtain ⟨R, hR⟩ := FK.QuasiTransitive.exists_translateSupport_diam
    (template H S) he₀'
  obtain ⟨K, hK⟩ := exists_lifted_template_localCover H hconn S he₀ hedge
  letI : Nonempty (graph H).edgeSet := ⟨e₀'⟩
  have hLG : (graph H).lineGraph.Connected :=
    FK.QuasiTransitive.lineGraph_connected (graph H) (graphConnected H hconn)
  let support : (H ≃g H) → Set (graph H).edgeSet := fun φ =>
    (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
      Set (graph H).edgeSet)
  let pivot : (H ≃g H) → (graph H).edgeSet := fun φ =>
    (automorphism H φ).mapEdgeSet e₀'
  have hpivot : ∀ φ, pivot φ ∈ support φ := by
    intro φ
    exact FK.QuasiTransitive.mem_translateSupport_iff.mpr ⟨e₀', he₀', rfl⟩
  obtain ⟨M, hMsub, hMpair, hMaux, hMmeet, hMdense⟩ :=
    FK.DevicePacking.exists_uniform_device_packing support Set.univ pivot hpivot
      (graph H).lineGraph.dist (fun _ _ _ => hLG.dist_triangle) K R
      (fun f => by
        obtain ⟨φ, hφ⟩ := hK f
        exact ⟨φ, Set.mem_univ _, hφ⟩)
      (fun φ _ f hf => hR (automorphism H φ) f hf)
  refine ⟨M, hMpair, ⟨K + R, hMdense⟩, ?_, ?_⟩
  · intro φ hφ
    rw [FK.QuasiTransitive.card_translateSupport]
    exact card_template_le H S
  · rintro p ⟨φ, hφ, rfl⟩
    exact FK.QuasiTransitive.onDoubleRay_mapEdgeSet hr₀ (automorphism H φ)

/-- The pairwise-disjoint packing can be rewritten entirely in terms of actual
annular-sleeve templates of transported base-bond sets. -/
lemma pairwiseDisjoint_packedTemplates (S : Finset H.edgeSet)
    {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet))) :
    M.PairwiseDisjoint (fun φ => template H (S.map φ.mapEdgeSet.toEmbedding)) := by
  classical
  intro φ hφ ψ hψ hne
  have hdSet := hM hφ hψ hne
  have hd : Disjoint
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S))
      (FK.QuasiTransitive.translateSupport (automorphism H ψ) (template H S)) :=
    Finset.disjoint_coe.mp hdSet
  rwa [automorphism_map_template, automorphism_map_template] at hd

/-- Distinct selected templates have distinct distinguished pivots. -/
lemma pivot_injOn_of_uniform_packing (S : Finset H.edgeSet)
    {e₀ : H.edgeSet} (he₀ : e₀ ∈ S) {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet))) :
    Set.InjOn (fun φ : H ≃g H => (automorphism H φ).mapEdgeSet (baseEdge H e₀)) M := by
  classical
  have he₀' : baseEdge H e₀ ∈ template H S :=
    (mem_template H).mpr (Or.inl (baseEdge_mem_annulus H S he₀))
  intro φ hφ ψ hψ hp
  by_contra hne
  have hd := hM hφ hψ hne
  have hpφ : (automorphism H φ).mapEdgeSet (baseEdge H e₀) ∈
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet) :=
    FK.QuasiTransitive.mem_translateSupport_iff.mpr ⟨baseEdge H e₀, he₀', rfl⟩
  change (automorphism H φ).mapEdgeSet (baseEdge H e₀) =
    (automorphism H ψ).mapEdgeSet (baseEdge H e₀) at hp
  have hpψ : (automorphism H φ).mapEdgeSet (baseEdge H e₀) ∈
      (FK.QuasiTransitive.translateSupport (automorphism H ψ) (template H S) :
        Set (graph H).edgeSet) := by
    rw [hp]
    exact FK.QuasiTransitive.mem_translateSupport_iff.mpr ⟨baseEdge H e₀, he₀', rfl⟩
  exact (disjoint_left.mp hd hpφ) hpψ

/-- Exact finite-overlap accounting: the cardinality of a union of selected
translated templates is the sum of the annulus and activation-edge counts.
There is no overlap correction. -/
theorem card_biUnion_packedTemplates [DecidableEq (graph H).edgeSet] (S : Finset H.edgeSet)
    {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    (F.biUnion fun φ => template H (S.map φ.mapEdgeSet.toEmbedding)).card =
      ∑ φ ∈ F, (S.card + (edges H (S.map φ.mapEdgeSet.toEmbedding)).card) := by
  classical
  have hpair := Set.Pairwise.mono hFM (pairwiseDisjoint_packedTemplates H S hM)
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [card_template, card_map_mapEdgeSet]

/-- The exact overlap count gives the uniform linear bound used when a finite
family of pivot comparisons is summed. -/
theorem card_biUnion_packedTemplates_le [DecidableEq (graph H).edgeSet] (S : Finset H.edgeSet)
    {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M) :
    (F.biUnion fun φ => template H (S.map φ.mapEdgeSet.toEmbedding)).card ≤
      F.card * (3 * S.card) := by
  classical
  rw [card_biUnion_packedTemplates H S hM F hFM]
  calc
    (∑ φ ∈ F, (S.card + (edges H (S.map φ.mapEdgeSet.toEmbedding)).card)) ≤
        ∑ _φ ∈ F, 3 * S.card := by
      apply Finset.sum_le_sum
      intro φ hφ
      have h := card_edges_le H (S.map φ.mapEdgeSet.toEmbedding)
      rw [card_map_mapEdgeSet] at h
      omega
    _ = F.card * (3 * S.card) := by simp

/-- Pointwise form of finite overlap: an edge occurs in at most one selected
translated template from any finite subfamily. -/
theorem card_filter_mem_packedTemplates_le_one [DecidableEq (graph H).edgeSet] (S : Finset H.edgeSet)
    {M : Set (H ≃g H)}
    (hM : M.PairwiseDisjoint (fun φ =>
      (FK.QuasiTransitive.translateSupport (automorphism H φ) (template H S) :
        Set (graph H).edgeSet)))
    (F : Finset (H ≃g H)) (hFM : (F : Set (H ≃g H)) ⊆ M)
    (f : (graph H).edgeSet) :
    (F.filter fun φ => f ∈ template H (S.map φ.mapEdgeSet.toEmbedding)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro φ hφ ψ hψ
  simp only [Finset.mem_filter] at hφ hψ
  by_contra hne
  have hd := Set.Pairwise.mono hFM (pairwiseDisjoint_packedTemplates H S hM) hφ.1 hψ.1 hne
  exact (Finset.disjoint_left.mp hd hφ.2) hψ.2

end Sleeve
end FK.AGImplant
