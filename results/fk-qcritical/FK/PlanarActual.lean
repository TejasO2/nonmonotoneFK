import FK.FiniteModel
import FK.PlanarConditioning

/-!
# Finite planar duality for the actual finite FK probability mass functions

This module identifies the normalized weights in `FK.FinitePlane` with the
finite labelled-multigraph model. It also proves that conditioning on exterior
edges induces the boundary setoid of exterior open-connected components, and
uses this to give actual-FK versions of conditioned planar duality and equation
(12).

No embedding theorem is asserted: ambient planar duality still requires
Euler's component relation for the two actual free-boundary connection graphs.
Loops, parallel labelled edges, isolated vertices, and arbitrary induced
boundary setoids are retained.
-/

namespace SimpleGraph

/-- If `H ≤ K` and every adjacency in `K` is spanned by an `H`-path, then
`H` and `K` have the same reachability relation. -/
lemma reachable_iff_of_le_of_adj_reachable {V : Type*} {H K : SimpleGraph V}
    (hHK : H ≤ K) (hreach : ∀ {u v : V}, K.Adj u v → H.Reachable u v)
    (u v : V) : H.Reachable u v ↔ K.Reachable u v := by
  constructor
  · exact fun h => h.mono hHK
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨SimpleGraph.Walk.nil⟩
    | cons h w ih => exact (hreach h).trans ih

/-- Connected components depend only on the reachability relation, not on the
particular simple-graph presentation of that relation. -/
noncomputable def connectedComponentEquivOfReachableIff {V : Type*}
    {H K : SimpleGraph V} (h : ∀ u v, H.Reachable u v ↔ K.Reachable u v) :
    H.ConnectedComponent ≃ K.ConnectedComponent := by
  let f : H.ConnectedComponent → K.ConnectedComponent :=
    Quot.map id (fun _ _ huv => (h _ _).mp huv)
  apply Equiv.ofBijective f
  constructor
  · intro C D hCD
    induction C using ConnectedComponent.ind with
    | h u =>
      induction D using ConnectedComponent.ind with
      | h v =>
        apply ConnectedComponent.sound
        apply (h u v).mpr
        exact ConnectedComponent.exact hCD
  · intro C
    induction C using ConnectedComponent.ind with
    | h v => exact ⟨H.connectedComponentMk v, rfl⟩

end SimpleGraph

namespace FK.FinitePlane

open scoped ENNReal BigOperators
open FK.Configuration
open FK.Finite
open FK.Finite.LabelledMultigraph

/-- The plane weight with an actual wired component count is definitionally
the finite-model FK weight, for every boundary setoid. -/
lemma plane_fkWeight_eq_actual (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) (q p : NNReal) (ω : G.Configuration) :
    fkWeight q p (G.componentCount ξ) ω = G.fkWeight q p ξ ω := rfl

/-- At interior parameters, the two normalizations of the same positive FK
weights are the same PMF, for an arbitrary boundary setoid. -/
lemma normalizedPMF_eq_actual_fkPMF (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    normalizedPMF (fkWeight q p (G.componentCount ξ))
        (fun ω => fkWeight_pos hq hp₀ hp₁ _ ω) =
      G.fkPMF hq hp₁.le ξ := by
  rfl

/-- Finite planar duality for the actual finite FK PMFs on two labelled
multigraphs.  The planar Euler relation remains a separate explicit geometric
hypothesis; loops and parallel labelled edges are retained in both models. -/
theorem actual_fkPMF_duality (G GD : LabelledMultigraph)
    (e : G.Edge ≃ GD.Edge) (q p : NNReal)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ω : G.Configuration,
      GD.componentCount GD.freeBoundary (dualConfig e ω) + Fintype.card G.Vertex =
        G.componentCount G.freeBoundary ω + 1 + openCard ω) :
    PMF.map (dualEquiv e) (G.fkPMF hq hp₁.le G.freeBoundary) =
      GD.fkPMF hq (dualParameter_le_one hq hp₁.le) GD.freeBoundary := by
  classical
  rw [← normalizedPMF_eq_actual_fkPMF G G.freeBoundary hq hp₀ hp₁,
    ← normalizedPMF_eq_actual_fkPMF GD GD.freeBoundary hq
      (dualParameter_pos hq hp₀ hp₁) (dualParameter_lt_one hq hp₀ hp₁.le)]
  exact finite_planar_fk_duality e q p _ _ hq hp₀ hp₁ heuler

/-- An ambient labelled multigraph whose edges are split into interior and
exterior labels. -/
def ambientOfSum {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) : LabelledMultigraph where
  Vertex := V
  Edge := I ⊕ O
  source := s
  target := t

/-- The interior induced graph retains all ambient vertices, including those
that become isolated after deleting exterior edges. -/
def interiorOfSum {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) : LabelledMultigraph where
  Vertex := V
  Edge := I
  source := s ∘ Sum.inl
  target := t ∘ Sum.inl

/-- The graph formed by the fixed exterior open edges alone. -/
def exteriorGraph {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) (ξ : O → Bool) : SimpleGraph V :=
  (ambientOfSum s t).connectionGraph (ambientOfSum s t).freeBoundary
    (glue (fun _ => false) ξ)

/-- Conditioning on exterior open edges wires together precisely their
connected components.  This is a setoid on all ambient vertices, with isolated
vertices retained. -/
def exteriorBoundary {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) (ξ : O → Bool) : Setoid V where
  r u v := (exteriorGraph s t ξ).Reachable u v
  iseqv := ⟨fun u => SimpleGraph.Reachable.refl u,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The full open graph after gluing an interior and exterior configuration. -/
def gluedGraph {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool) : SimpleGraph V :=
  (ambientOfSum s t).connectionGraph (ambientOfSum s t).freeBoundary (glue ω ξ)

/-- The open/wired graph of the induced interior FK measure. -/
def interiorGraph {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool) : SimpleGraph V :=
  (interiorOfSum s t).connectionGraph (exteriorBoundary s t ξ) ω

lemma exteriorGraph_le_gluedGraph {V I O : Type*} [Fintype V] [Fintype I]
    [Fintype O] (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool) :
    exteriorGraph s t ξ ≤ gluedGraph s t ω ξ := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hfree | ⟨a, ha, hjoin⟩
  · exact (huv.1 hfree).elim
  · refine Or.inr ⟨a, ?_, hjoin⟩
    cases a with
    | inl i => simp [glue] at ha
    | inr o => exact ha

lemma gluedGraph_le_interiorGraph {V I O : Type*} [Fintype V] [Fintype I]
    [Fintype O] (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool) :
    gluedGraph s t ω ξ ≤ interiorGraph s t ω ξ := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hfree | ⟨a, ha, hjoin⟩
  · exact (huv.1 hfree).elim
  · cases a with
    | inl i => exact Or.inr ⟨i, ha, hjoin⟩
    | inr o =>
      apply Or.inl
      apply SimpleGraph.Adj.reachable
      exact ⟨huv.1, Or.inr ⟨Sum.inr o, ha, hjoin⟩⟩

lemma interiorGraph_adj_reachable_gluedGraph {V I O : Type*} [Fintype V]
    [Fintype I] [Fintype O] (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool)
    {u v : V} (huv : (interiorGraph s t ω ξ).Adj u v) :
    (gluedGraph s t ω ξ).Reachable u v := by
  rcases huv.2 with hwire | ⟨i, hi, hjoin⟩
  · exact hwire.mono (exteriorGraph_le_gluedGraph s t ω ξ)
  · apply SimpleGraph.Adj.reachable
    exact ⟨huv.1, Or.inr ⟨Sum.inl i, hi, hjoin⟩⟩

/-- Replacing exterior paths by wiring preserves exactly the reachability
relation of the full glued graph. -/
lemma reachable_gluedGraph_iff {V I O : Type*} [Fintype V] [Fintype I]
    [Fintype O] (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool) (u v : V) :
    (gluedGraph s t ω ξ).Reachable u v ↔
      (interiorGraph s t ω ξ).Reachable u v :=
  SimpleGraph.reachable_iff_of_le_of_adj_reachable
    (gluedGraph_le_interiorGraph s t ω ξ)
    (fun h => interiorGraph_adj_reachable_gluedGraph s t ω ξ h) u v

/-- The ambient free component count after gluing equals the interior component
count with the exterior open components wired. -/
lemma componentCount_glue {V I O : Type*} [Fintype V] [Fintype I]
    [Fintype O] (s t : I ⊕ O → V) (ω : I → Bool) (ξ : O → Bool) :
    (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary (glue ω ξ) =
      (interiorOfSum s t).componentCount (exteriorBoundary s t ξ) ω := by
  exact Nat.card_congr (SimpleGraph.connectedComponentEquivOfReachableIff
    (reachable_gluedGraph_iff s t ω ξ))

/-- After gluing, the ambient FK weight is the fixed exterior Bernoulli weight
times the FK weight of the interior with exterior components wired. -/
lemma fkWeight_glue {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]
    (s t : I ⊕ O → V) (q p : NNReal) (ω : I → Bool) (ξ : O → Bool) :
    (ambientOfSum s t).fkWeight q p (ambientOfSum s t).freeBoundary (glue ω ξ) =
      edgeWeight p (1 - p) ξ *
        (interiorOfSum s t).fkWeight q p (exteriorBoundary s t ξ) ω := by
  classical
  simp only [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    FinitePlane.edgeWeight, componentCount_glue]
  change (∏ a : I ⊕ O, if glue ω ξ a then p else 1 - p) * _ = _
  rw [Fintype.prod_sum_type]
  simp only [glue_inl, glue_inr]
  ac_rfl

lemma edgeWeight_pos' {O : Type*} [Fintype O] {p : NNReal}
    (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    0 < edgeWeight p (1 - p) ξ := by
  classical
  unfold edgeWeight
  apply Finset.prod_pos
  intro o _
  split_ifs
  · exact hp₀
  · exact tsub_pos_of_lt hp₁

/-- Conditioning the actual ambient free-boundary FK PMF on an exterior
configuration gives the actual interior FK PMF with the exterior open
components wired. -/
lemma conditionedPMF_actual_fkPMF {V I O : Type*} [Fintype V] [Fintype I]
    [Fintype O] (s t : I ⊕ O → V) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    conditionedPMF (fkWeight q p ((ambientOfSum s t).componentCount
        (ambientOfSum s t).freeBoundary))
      (fun ρ => fkWeight_pos hq hp₀ hp₁ _ ρ) ξ =
      (interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ) := by
  classical
  rw [← normalizedPMF_eq_actual_fkPMF (interiorOfSum s t)
    (exteriorBoundary s t ξ) hq hp₀ hp₁]
  unfold conditionedPMF
  have h := normalizedPMF_map_eq_of_proportional (Equiv.refl (I → Bool))
    (fkWeight q p ((interiorOfSum s t).componentCount (exteriorBoundary s t ξ)))
    (fun ω => fkWeight q p ((ambientOfSum s t).componentCount
      (ambientOfSum s t).freeBoundary) (glue ω ξ))
    (edgeWeight p (1 - p) ξ) (edgeWeight_pos' hp₀ hp₁ ξ)
    (fun ω => fkWeight_pos hq hp₀ hp₁ _ ω)
    (fun ω => fkWeight_pos hq hp₀ hp₁ _ (glue ω ξ))
    (fun ω => fkWeight_glue s t q p ω ξ)
  simp only [Equiv.coe_refl, PMF.map_id] at h
  convert h.symm using 1
  rfl

/-- Conditioned planar duality for actual interior FK PMFs.  The interior
boundary conditions are computed from the exterior configurations, rather
than left as unrelated abstract component-count functions. -/
theorem actual_conditioned_fkPMF_duality {V VD I O ID OD : Type*}
    [Fintype V] [Fintype VD] [Fintype I] [Fintype O] [Fintype ID] [Fintype OD]
    (s t : I ⊕ O → V) (sD tD : ID ⊕ OD → VD)
    (eI : I ≃ ID) (eO : O ≃ OD) (q p : NNReal)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ : I ⊕ O → Bool,
      (ambientOfSum sD tD).componentCount (ambientOfSum sD tD).freeBoundary
          (dualConfig (eI.sumCongr eO) ρ) + Fintype.card V =
        (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary ρ +
          1 + openCard ρ) (ξ : O → Bool) :
    PMF.map (dualEquiv eI)
        ((interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ)) =
      (interiorOfSum sD tD).fkPMF hq (dualParameter_le_one hq hp₁.le)
        (exteriorBoundary sD tD (dualConfig eO ξ)) := by
  classical
  rw [← conditionedPMF_actual_fkPMF s t hq hp₀ hp₁ ξ,
    ← conditionedPMF_actual_fkPMF sD tD hq (dualParameter_pos hq hp₀ hp₁)
      (dualParameter_lt_one hq hp₀ hp₁.le) (dualConfig eO ξ)]
  exact map_conditioned_fkPMF eI eO q p _ _ hq hp₀ hp₁ heuler ξ

/-- Pointwise equation (12) for actual FK PMFs with the boundary setoids
induced by matching exterior configurations. -/
theorem equation_twelve_actual {V VD I O ID OD : Type*}
    [Fintype V] [Fintype VD] [Fintype I] [Fintype O] [Fintype ID] [Fintype OD]
    (s t : I ⊕ O → V) (sD tD : ID ⊕ OD → VD)
    (eI : I ≃ ID) (eO : O ≃ OD) (q p : NNReal)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ : I ⊕ O → Bool,
      (ambientOfSum sD tD).componentCount (ambientOfSum sD tD).freeBoundary
          (dualConfig (eI.sumCongr eO) ρ) + Fintype.card V =
        (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary ρ +
          1 + openCard ρ) (ξ : O → Bool) (ω : I → Bool) :
    (interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ) ω =
      (interiorOfSum sD tD).fkPMF hq (dualParameter_le_one hq hp₁.le)
        (exteriorBoundary sD tD (dualConfig eO ξ)) (dualConfig eI ω) := by
  classical
  have h := congrArg (fun P : PMF (ID → Bool) => P (dualConfig eI ω))
    (actual_conditioned_fkPMF_duality s t sD tD eI eO q p hq hp₀ hp₁ heuler ξ)
  calc
    _ = (interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ)
        ((dualEquiv eI).symm (dualConfig eI ω)) := by simp [dualEquiv]
    _ = (PMF.map (dualEquiv eI)
        ((interiorOfSum s t).fkPMF hq hp₁.le (exteriorBoundary s t ξ)))
        (dualConfig eI ω) := (pmf_map_equiv_apply _ _ _).symm
    _ = _ := h

end FK.FinitePlane
