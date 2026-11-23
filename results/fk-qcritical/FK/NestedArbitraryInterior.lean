import FK.ExteriorMarkov
import FK.WiredRightInterior

/-!
# Exterior conditioning with an arbitrary ambient boundary setoid

The fixed exterior graph contains both the prescribed ambient wiring and the
open exterior edges, with every interior edge closed. Its reachability
relation is the effective boundary of the interior FK law. This includes
left-left and left/right cross wiring directly; no sum-boundary or no-cross
restriction is imposed.

Copied imports: `FK.ExteriorMarkov` (the existing exact positive-weight
`PMF.filter` theorem) and `FK.WiredRightInterior` (the split-graph definitions,
actual maximal strata, and the earlier free-left/right-wired construction).
The arbitrary effective-boundary and two-sided factorizations below are new;
neither assumes equality of conditional good intersections.
-/

namespace FK.FinitePlane.ArbitraryBoundary

open scoped ENNReal BigOperators Classical
open FK.Configuration
open FK.Finite FK.Finite.LabelledMultigraph

variable {V I O : Type*} [Fintype V] [Fintype I] [Fintype O]

/-- The fixed graph used to condition an arbitrarily wired ambient FK law. -/
def fixedGraph (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ξ : O → Bool) : SimpleGraph V :=
  (ambientOfSum s t).connectionGraph ζ (glue (fun _ : I => false) ξ)

/-- Reachability in the fixed wired/exterior-open graph. Cross relations in
`ζ` are retained, rather than replaced by a sum of left and right setoids. -/
def effectiveBoundary (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ξ : O → Bool) : Setoid V where
  r u v := (fixedGraph s t ζ ξ).Reachable u v
  iseqv := ⟨fun u => SimpleGraph.Reachable.refl u,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The full graph after gluing arbitrary interior and exterior bits. -/
def wiredGluedGraph (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool) :
    SimpleGraph V :=
  (ambientOfSum s t).connectionGraph ζ (glue ω ξ)

/-- The interior graph whose boundary wires fixed exterior components and all
original ambient boundary relations. -/
def wiredInteriorGraph (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool) :
    SimpleGraph V :=
  (interiorOfSum s t).connectionGraph (effectiveBoundary s t ζ ξ) ω

lemma fixedGraph_le_wiredGluedGraph (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool) :
    fixedGraph s t ζ ξ ≤ wiredGluedGraph s t ζ ω ξ := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hwire | ⟨a, ha, hjoin⟩
  · exact Or.inl hwire
  · refine Or.inr ⟨a, ?_, hjoin⟩
    cases a with
    | inl i => simp [glue] at ha
    | inr o => exact ha

lemma wiredGluedGraph_le_wiredInteriorGraph (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool) :
    wiredGluedGraph s t ζ ω ξ ≤ wiredInteriorGraph s t ζ ω ξ := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hwire | ⟨a, ha, hjoin⟩
  · apply Or.inl
    apply SimpleGraph.Adj.reachable
    exact ⟨huv.1, Or.inl hwire⟩
  · cases a with
    | inl i => exact Or.inr ⟨i, ha, hjoin⟩
    | inr o =>
        apply Or.inl
        apply SimpleGraph.Adj.reachable
        exact ⟨huv.1, Or.inr ⟨Sum.inr o, ha, hjoin⟩⟩

lemma wiredInteriorGraph_adj_reachable_wiredGluedGraph (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool)
    {u v : V} (huv : (wiredInteriorGraph s t ζ ω ξ).Adj u v) :
    (wiredGluedGraph s t ζ ω ξ).Reachable u v := by
  rcases huv.2 with hwire | ⟨i, hi, hjoin⟩
  · exact hwire.mono (fixedGraph_le_wiredGluedGraph s t ζ ω ξ)
  · apply SimpleGraph.Adj.reachable
    exact ⟨huv.1, Or.inr ⟨Sum.inl i, hi, hjoin⟩⟩

/-- Replacing every fixed exterior/wired path by boundary wiring preserves
exactly the reachability relation. -/
theorem reachable_wiredGluedGraph_iff (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool)
    (u v : V) :
    (wiredGluedGraph s t ζ ω ξ).Reachable u v ↔
      (wiredInteriorGraph s t ζ ω ξ).Reachable u v :=
  SimpleGraph.reachable_iff_of_le_of_adj_reachable
    (wiredGluedGraph_le_wiredInteriorGraph s t ζ ω ξ)
    (fun h => wiredInteriorGraph_adj_reachable_wiredGluedGraph s t ζ ω ξ h) u v

/-- Exact component-count factorization for arbitrary boundary wiring. -/
theorem componentCount_glue (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (ω : I → Bool) (ξ : O → Bool) :
    (ambientOfSum s t).componentCount ζ (glue ω ξ) =
      (interiorOfSum s t).componentCount (effectiveBoundary s t ζ ξ) ω := by
  exact Nat.card_congr (SimpleGraph.connectedComponentEquivOfReachableIff
    (reachable_wiredGluedGraph_iff s t ζ ω ξ))

/-- The ambient weight is the fixed exterior Bernoulli product times the
interior FK weight with the effective boundary. -/
theorem fkWeight_glue (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) (q p : NNReal)
    (ω : I → Bool) (ξ : O → Bool) :
    (ambientOfSum s t).fkWeight q p ζ (glue ω ξ) =
      edgeWeight p (1 - p) ξ *
        (interiorOfSum s t).fkWeight q p (effectiveBoundary s t ζ ξ) ω := by
  classical
  simp only [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight,
    FinitePlane.edgeWeight, componentCount_glue]
  change (∏ a : I ⊕ O, if glue ω ξ a then p else 1 - p) * _ = _
  rw [Fintype.prod_sum_type]
  simp only [glue_inl, glue_inr]
  ac_rfl

/-- Positive-weight normalization on an exterior fiber gives the actual
interior FK law with the effective arbitrary boundary. -/
theorem conditionedPMF_fkPMF (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    conditionedPMF ((ambientOfSum s t).fkWeight q p ζ)
      (fun ρ => (ambientOfSum s t).fkWeight_pos hq hp₀ hp₁ ζ ρ) ξ =
    (interiorOfSum s t).fkPMF hq hp₁.le (effectiveBoundary s t ζ ξ) := by
  classical
  rw [← normalizedPMF_eq_actual_fkPMF (interiorOfSum s t)
    (effectiveBoundary s t ζ ξ) hq hp₀ hp₁]
  unfold conditionedPMF
  have h := normalizedPMF_map_eq_of_proportional (Equiv.refl (I → Bool))
    (fkWeight q p ((interiorOfSum s t).componentCount (effectiveBoundary s t ζ ξ)))
    (fun ω => (ambientOfSum s t).fkWeight q p ζ (glue ω ξ))
    (edgeWeight p (1 - p) ξ) (edgeWeight_pos' hp₀ hp₁ ξ)
    (fun ω => fkWeight_pos hq hp₀ hp₁ _ ω)
    (fun ω => (ambientOfSum s t).fkWeight_pos hq hp₀ hp₁ ζ (glue ω ξ))
    (fun ω => fkWeight_glue s t ζ q p ω ξ)
  simp only [Equiv.coe_refl, PMF.map_id] at h
  convert h.symm using 1
  rfl

/-- With free ambient wiring, the fixed graph is exactly the previously used
exterior-open graph. -/
lemma fixedGraph_free (s t : I ⊕ O → V) (ξ : O → Bool) :
    fixedGraph s t (ambientOfSum s t).freeBoundary ξ = exteriorGraph s t ξ := rfl

/-- The new effective boundary specializes definitionally to the integrated
exterior-component boundary at free ambient wiring. -/
lemma effectiveBoundary_free (s t : I ⊕ O → V) (ξ : O → Bool) :
    effectiveBoundary s t (ambientOfSum s t).freeBoundary ξ = exteriorBoundary s t ξ := by
  apply Setoid.ext
  intro u v
  rfl

/-- Every exterior fiber supports the actual arbitrarily wired FK PMF. -/
theorem exteriorFiber_support (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    ∃ ρ ∈ FinitePlane.exteriorFiber ξ,
      ρ ∈ ((ambientOfSum s t).fkPMF hq hp₁.le ζ).support := by
  rw [← normalizedPMF_eq_actual_fkPMF (ambientOfSum s t) ζ hq hp₀ hp₁]
  exact FinitePlane.exteriorFiber_support _
    (fun ρ => (ambientOfSum s t).fkWeight_pos hq hp₀ hp₁ ζ ρ) ξ

/-- Exact exterior-fiber conditioning of an actual FK law with arbitrary
left, right, and cross boundary setoid relations. -/
theorem filter_fkPMF_eq_map_glue (s t : I ⊕ O → V)
    (ζ : (ambientOfSum s t).BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : O → Bool) :
    PMF.map (fun ω : I → Bool => glue ω ξ)
      ((interiorOfSum s t).fkPMF hq hp₁.le (effectiveBoundary s t ζ ξ)) =
    ((ambientOfSum s t).fkPMF hq hp₁.le ζ).filter (FinitePlane.exteriorFiber ξ)
      (exteriorFiber_support s t ζ hq hp₀ hp₁ ξ) := by
  rw [← conditionedPMF_fkPMF s t ζ hq hp₀ hp₁ ξ]
  exact FinitePlane.map_glue_conditionedPMF _ _ ξ

/-- Equality of effective boundaries is sufficient for equality of the two
normalized interior laws on the same exterior fiber. Unlike an equality of
good intersections, this is an explicit graph-theoretic compatibility
condition that permits arbitrary cross wiring. -/
theorem filter_fkPMF_eq_of_effectiveBoundary_eq (s t : I ⊕ O → V)
    (ζ η : (ambientOfSum s t).BoundaryPartition) {q p : NNReal} (ξ : O → Bool)
    (h : effectiveBoundary s t ζ ξ = effectiveBoundary s t η ξ)
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ((ambientOfSum s t).fkPMF hq hp₁.le ζ).filter (FinitePlane.exteriorFiber ξ)
        (exteriorFiber_support s t ζ hq hp₀ hp₁ ξ) =
      ((ambientOfSum s t).fkPMF hq hp₁.le η).filter (FinitePlane.exteriorFiber ξ)
        (exteriorFiber_support s t η hq hp₀ hp₁ ξ) := by
  rw [← filter_fkPMF_eq_map_glue s t ζ hq hp₀ hp₁ ξ,
    ← filter_fkPMF_eq_map_glue s t η hq hp₀ hp₁ ξ]
  exact congrArg (fun τ : Setoid V =>
    PMF.map (fun ω : I → Bool => glue ω ξ)
      ((interiorOfSum s t).fkPMF hq hp₁.le τ)) h

end FK.FinitePlane.ArbitraryBoundary

#print axioms FK.FinitePlane.ArbitraryBoundary.componentCount_glue
#print axioms FK.FinitePlane.ArbitraryBoundary.fkWeight_glue
#print axioms FK.FinitePlane.ArbitraryBoundary.conditionedPMF_fkPMF
#print axioms FK.FinitePlane.ArbitraryBoundary.effectiveBoundary_free
#print axioms FK.FinitePlane.ArbitraryBoundary.filter_fkPMF_eq_map_glue
#print axioms FK.FinitePlane.ArbitraryBoundary.filter_fkPMF_eq_of_effectiveBoundary_eq


namespace FK.Exploration.TwoSidedInterior

open scoped ENNReal BigOperators Classical
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Arbitrary wiring on both summands, with the absence of cross-wiring made
by `sumBoundary` rather than silently treating an arbitrary cross setoid as a
sum. -/
@[instance_reducible] def twoSidedBoundary
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (θ : Setoid U) (ζ : Setoid K) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).BoundaryPartition :=
  FK.Finite.MarkovFactorization.sumBoundary
    (G := regionGraph si ti) (H := rightVertexGraph K) θ ζ

/-- The fixed right graph; it may depend on the arbitrary left setoid only
through proof irrelevance, and is retained explicitly in the factorization. -/
def twoSidedRightGraph
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (θ : Setoid U) (ζ : Setoid K) (ξ : Fin k → Bool) : SimpleGraph K where
  Adj x y := ((ambientOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
    (twoSidedBoundary si ti so xo θ ζ) (glue (fun _ : Fin m => false) ξ)).Adj
      (Sum.inr x) (Sum.inr y)
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- On a separated exterior, arbitrary left wiring gives the actual
`θ`-wired region law, while arbitrary right wiring contributes a fixed graph.
No open exterior edge can connect the two summands. -/
theorem connectionGraph_twoSided_eq_sum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (θ : Setoid U) (ζ : Setoid K) (ξ : Fin k → Bool) (ω : Fin m → Bool)
    (hsep : Separated si ti so xo ξ) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
      (twoSidedBoundary si ti so xo θ ζ) (glue ω ξ) =
    (regionGraph si ti).connectionGraph θ ω ⊕g
      twoSidedRightGraph si ti so xo θ ζ ξ := by
  ext x y
  rcases x with u | u <;> rcases y with v | v <;>
    simp [twoSidedRightGraph, LabelledMultigraph.connectionGraph,
      LabelledMultigraph.Joins, ambientOfSum, regionGraph, splitSource,
      splitTarget, glue]
  case inl.inl =>
    intro huv
    let P : Prop := ∃ a, ω a = true ∧
      (si a = u ∧ ti a = v ∨ si a = v ∧ ti a = u)
    let Q : Prop := ∃ b, ξ b = true ∧
      (so b = Sum.inl u ∧ xo b = Sum.inl v ∨ so b = Sum.inl v ∧ xo b = Sum.inl u)
    change (θ.r u v ∨ P ∨ Q) ↔ (θ.r u v ∨ P)
    have hQ : ¬ Q := by
      dsimp [Q]
      rintro ⟨b, hb, h | h⟩
      · exact (hsep b hb).1 ⟨u, h.1.symm⟩
      · exact (hsep b hb).1 ⟨v, h.1.symm⟩
    simp [hQ]
  case inl.inr =>
    constructor
    · intro h
      exact h.elim
    · intro o ho
      constructor
      · intro hso _
        exact ((hsep o ho).1 ⟨u, hso.symm⟩).elim
      · intro _ hxo
        exact (hsep o ho).2 ⟨u, hxo.symm⟩
  case inr.inl =>
    constructor
    · intro h
      exact h.elim
    · intro o ho
      constructor
      · intro _ hxo
        exact (hsep o ho).2 ⟨v, hxo.symm⟩
      · intro hso _
        exact ((hsep o ho).1 ⟨v, hso.symm⟩).elim

lemma componentCount_twoSided
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (θ : Setoid U) (ζ : Setoid K) (ξ : Fin k → Bool) (ω : Fin m → Bool)
    (hsep : Separated si ti so xo ξ) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).componentCount
      (twoSidedBoundary si ti so xo θ ζ) (glue ω ξ) =
    (regionGraph si ti).componentCount θ ω +
      Nat.card (twoSidedRightGraph si ti so xo θ ζ ξ).ConnectedComponent := by
  change Nat.card ((ambientOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
    (twoSidedBoundary si ti so xo θ ζ) (glue ω ξ)).ConnectedComponent = _
  rw [connectionGraph_twoSided_eq_sum si ti so xo θ ζ ξ ω hsep]
  exact SimpleGraph.natCard_connectedComponent_sum _ _

/-- Exact two-sided arbitrary-wiring FK weight factorization. -/
lemma fkWeight_glue_twoSided
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (q p : NNReal) (θ : Setoid U) (ζ : Setoid K) (ξ : Fin k → Bool)
    (ω : Fin m → Bool) (hsep : Separated si ti so xo ξ) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).fkWeight q p
      (twoSidedBoundary si ti so xo θ ζ) (glue ω ξ) =
    (q ^ Nat.card (twoSidedRightGraph si ti so xo θ ζ ξ).ConnectedComponent *
        FK.FinitePlane.edgeWeight p (1 - p) ξ) *
      (regionGraph si ti).fkWeight q p θ ω := by
  classical
  simp only [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight]
  change (∏ a : Fin m ⊕ Fin k, if glue ω ξ a then p else 1 - p) * _ = _
  rw [Fintype.prod_sum_type]
  simp only [glue_inl, glue_inr, componentCount_twoSided si ti so xo θ ζ ξ ω hsep,
    pow_add]
  unfold FK.FinitePlane.edgeWeight
  ac_rfl

lemma twoSided_constant_pos
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (ξ : Fin k → Bool) :
    0 < q ^ Nat.card (twoSidedRightGraph si ti so xo θ ζ ξ).ConnectedComponent *
      FK.FinitePlane.edgeWeight p (1 - p) ξ := by
  exact mul_pos (pow_pos hq _) (edgeWeight_pos' hp₀ hp₁ ξ)

/-- Conditioning an ambient FK law with arbitrary left and right wiring on a
separated exterior gives the actual interior FK law with the same arbitrary
left setoid. -/
theorem filter_fkPMF_eq_map_glue_region_twoSided
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (ξ : Fin k → Bool)
    (hsep : Separated si ti so xo ξ) :
    PMF.map (fun ω : Fin m → Bool => glue ω ξ)
      ((regionGraph si ti).fkPMF hq hp₁.le θ) =
    ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
      (twoSidedBoundary si ti so xo θ ζ)).filter (exteriorFiber ξ)
      (by
        let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
        rw [← normalizedPMF_eq_actual_fkPMF G (twoSidedBoundary si ti so xo θ ζ)
          hq hp₀ hp₁]
        exact FinitePlane.exteriorFiber_support _
          (fun ρ => G.fkWeight_pos hq hp₀ hp₁ _ ρ) ξ) := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let w : G.Configuration → NNReal := G.fkWeight q p (twoSidedBoundary si ti so xo θ ζ)
  have hw : ∀ ρ, 0 < w ρ := fun ρ => G.fkWeight_pos hq hp₀ hp₁ _ ρ
  have hcond : conditionedPMF w hw ξ = (regionGraph si ti).fkPMF hq hp₁.le θ := by
    rw [← normalizedPMF_eq_actual_fkPMF (regionGraph si ti) θ hq hp₀ hp₁]
    unfold conditionedPMF
    have h := normalizedPMF_map_eq_of_proportional (Equiv.refl (Fin m → Bool))
      ((regionGraph si ti).fkWeight q p θ) (fun ω => w (glue ω ξ))
      (q ^ Nat.card (twoSidedRightGraph si ti so xo θ ζ ξ).ConnectedComponent *
        FK.FinitePlane.edgeWeight p (1 - p) ξ)
      (twoSided_constant_pos si ti so xo hq hp₀ hp₁ θ ζ ξ)
      (fun ω => (regionGraph si ti).fkWeight_pos hq hp₀ hp₁ θ ω)
      (fun ω => hw (glue ω ξ))
      (fun ω => fkWeight_glue_twoSided si ti so xo q p θ ζ ξ ω hsep)
    simp only [Equiv.coe_refl, PMF.map_id] at h
    convert h.symm using 1
    rfl
  have hnorm : normalizedPMF w hw = G.fkPMF hq hp₁.le
      (twoSidedBoundary si ti so xo θ ζ) := by
    exact normalizedPMF_eq_actual_fkPMF G (twoSidedBoundary si ti so xo θ ζ)
      hq hp₀ hp₁
  have hfinal := FinitePlane.map_glue_conditionedPMF w hw ξ
  rw [hcond] at hfinal
  have hsupp : ∃ a ∈ exteriorFiber ξ,
      a ∈ (G.fkPMF hq hp₁.le (twoSidedBoundary si ti so xo θ ζ)).support := by
    rw [← hnorm]
    exact FinitePlane.exteriorFiber_support w hw ξ
  have heq := hfinal.trans (pmf_filter_congr hnorm (exteriorFiber ξ) _ hsupp)
  with_unfolding_all exact heq

/-- On the canonical maximal closed-cutset stratum, changing the arbitrary
right setoid does not change the normalized configuration law on the exterior
fiber. The shared left setoid remains arbitrary, not necessarily free. -/
theorem filter_twoSided_eq_of_mem_maximalSplitStratum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ η : Setoid K) (hright : ExteriorHasRight so xo)
    (ρ : Fin m ⊕ Fin k → Bool) (hρ : ρ ∈ maximalSplitStratum si ti so xo) :
    ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
      (twoSidedBoundary si ti so xo θ ζ)).filter
        (exteriorFiber (exteriorConfig ρ))
        (by
          let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
          rw [← normalizedPMF_eq_actual_fkPMF G (twoSidedBoundary si ti so xo θ ζ)
            hq hp₀ hp₁]
          exact FinitePlane.exteriorFiber_support _
            (fun σ => G.fkWeight_pos hq hp₀ hp₁ _ σ) (exteriorConfig ρ)) =
    ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
      (twoSidedBoundary si ti so xo θ η)).filter
        (exteriorFiber (exteriorConfig ρ))
        (by
          let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
          rw [← normalizedPMF_eq_actual_fkPMF G (twoSidedBoundary si ti so xo θ η)
            hq hp₀ hp₁]
          exact FinitePlane.exteriorFiber_support _
            (fun σ => G.fkWeight_pos hq hp₀ hp₁ _ σ) (exteriorConfig ρ)) := by
  have hsep : Separated si ti so xo (exteriorConfig ρ) :=
    (mem_maximalSplitStratum_iff si ti so xo ρ hright).mp hρ
  rw [← filter_fkPMF_eq_map_glue_region_twoSided si ti so xo hq hp₀ hp₁ θ ζ
      (exteriorConfig ρ) hsep,
    ← filter_fkPMF_eq_map_glue_region_twoSided si ti so xo hq hp₀ hp₁ θ η
      (exteriorConfig ρ) hsep]

end FK.Exploration.TwoSidedInterior

#print axioms FK.Exploration.TwoSidedInterior.connectionGraph_twoSided_eq_sum
#print axioms FK.Exploration.TwoSidedInterior.fkWeight_glue_twoSided
#print axioms FK.Exploration.TwoSidedInterior.filter_fkPMF_eq_map_glue_region_twoSided
#print axioms FK.Exploration.TwoSidedInterior.filter_twoSided_eq_of_mem_maximalSplitStratum
