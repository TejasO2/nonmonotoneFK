import FK.MaximalStrata

/-!
# Free interiors with arbitrary wiring supported on the right

A separated exterior splits the whole ambient open graph even when the right
vertices carry an arbitrary boundary setoid.  The left boundary remains free.
This gives genuinely different ambient FK laws with the same free interior.
-/

namespace FK.Exploration.WiredRightInterior

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- A vertex-only graph used to reuse the general disjoint-sum boundary
construction. -/
def rightVertexGraph (K : Type*) [Fintype K] : LabelledMultigraph where
  Vertex := K
  Edge := Fin 0
  source := Fin.elim0
  target := Fin.elim0

/-- Free wiring on the left summand, arbitrary wiring on the right, and no
cross-summand boundary edges. -/
@[instance_reducible] def rightWiredBoundary
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ζ : Setoid K) : (ambientOfSum (splitSource si so) (splitTarget ti xo)).BoundaryPartition :=
  FK.Finite.MarkovFactorization.sumBoundary
    (G := regionGraph si ti) (H := rightVertexGraph K)
      (regionGraph si ti).freeBoundary ζ

/-- The fixed right part of the wired ambient open graph. -/
def rightWiredGraph
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ζ : Setoid K) (ξ : Fin k → Bool) : SimpleGraph K where
  Adj x y := ((ambientOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
    (rightWiredBoundary si ti so xo ζ) (glue (fun _ : Fin m => false) ξ)).Adj
      (Sum.inr x) (Sum.inr y)
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- Exterior separation makes the whole wired ambient graph a disjoint sum
of the actual free interior graph and a fixed right graph. -/
theorem connectionGraph_rightWired_eq_sum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ζ : Setoid K) (ξ : Fin k → Bool) (ω : Fin m → Bool)
    (hsep : Separated si ti so xo ξ) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
      (rightWiredBoundary si ti so xo ζ) (glue ω ξ) =
    (regionGraph si ti).connectionGraph (regionGraph si ti).freeBoundary ω ⊕g
      rightWiredGraph si ti so xo ζ ξ := by
  ext x y
  rcases x with u | u <;> rcases y with v | v <;>
    simp [rightWiredGraph, rightWiredBoundary, FK.Finite.MarkovFactorization.sumBoundary,
      LabelledMultigraph.connectionGraph, LabelledMultigraph.freeBoundary,
      LabelledMultigraph.Joins, ambientOfSum, regionGraph, splitSource, splitTarget, glue]
  case inl.inl =>
    intro huv
    let P : Prop := ∃ a, ω a = true ∧ (si a = u ∧ ti a = v ∨ si a = v ∧ ti a = u)
    let Q : Prop := ∃ b, ξ b = true ∧
      (so b = Sum.inl u ∧ xo b = Sum.inl v ∨ so b = Sum.inl v ∧ xo b = Sum.inl u)
    change (u = v ∨ P ∨ Q) ↔ (u = v ∨ P)
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

end FK.Exploration.WiredRightInterior

namespace FK.Exploration.WiredRightInterior

open scoped ENNReal BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- The component count splits into the varying free-interior count and a
fixed right contribution. -/
lemma componentCount_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ζ : Setoid K) (ξ : Fin k → Bool) (ω : Fin m → Bool)
    (hsep : Separated si ti so xo ξ) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).componentCount
      (rightWiredBoundary si ti so xo ζ) (glue ω ξ) =
    (regionGraph si ti).componentCount (regionGraph si ti).freeBoundary ω +
      Nat.card (rightWiredGraph si ti so xo ζ ξ).ConnectedComponent := by
  change Nat.card ((ambientOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
    (rightWiredBoundary si ti so xo ζ) (glue ω ξ)).ConnectedComponent = _
  rw [connectionGraph_rightWired_eq_sum si ti so xo ζ ξ ω hsep]
  exact SimpleGraph.natCard_connectedComponent_sum _ _

/-- The whole ambient weight is a fixed exterior multiple of the actual free
interior-region FK weight. -/
lemma fkWeight_glue_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (q p : NNReal) (ζ : Setoid K) (ξ : Fin k → Bool) (ω : Fin m → Bool)
    (hsep : Separated si ti so xo ξ) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).fkWeight q p
      (rightWiredBoundary si ti so xo ζ) (glue ω ξ) =
    (q ^ Nat.card (rightWiredGraph si ti so xo ζ ξ).ConnectedComponent *
        FK.FinitePlane.edgeWeight p (1 - p) ξ) *
      (regionGraph si ti).fkWeight q p (regionGraph si ti).freeBoundary ω := by
  classical
  simp only [LabelledMultigraph.fkWeight, LabelledMultigraph.edgeWeight]
  change (∏ a : Fin m ⊕ Fin k, if glue ω ξ a then p else 1 - p) * _ = _
  rw [Fintype.prod_sum_type]
  simp only [glue_inl, glue_inr, componentCount_rightWired si ti so xo ζ ξ ω hsep,
    pow_add]
  unfold FK.FinitePlane.edgeWeight
  ac_rfl

/-- Positive normalization constant for the separated right-wired exterior. -/
lemma rightWired_constant_pos
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ξ : Fin k → Bool) :
    0 < q ^ Nat.card (rightWiredGraph si ti so xo ζ ξ).ConnectedComponent *
      FK.FinitePlane.edgeWeight p (1 - p) ξ := by
  exact mul_pos (pow_pos hq _) (edgeWeight_pos' hp₀ hp₁ ξ)

/-- Filtering respects equality of the underlying PMF; the two support
witnesses need not be syntactically identical. -/
lemma pmf_filter_congr {α : Type*} {p q : PMF α} (h : p = q) (E : Set α)
    (hp : ∃ a ∈ E, a ∈ p.support) (hq : ∃ a ∈ E, a ∈ q.support) :
    p.filter E hp = q.filter E hq := by
  subst q
  rfl

/-- The actual ambient FK law with free-left/right-supported wiring,
conditioned on a separated exterior fiber, is the actual free interior law.
The proof uses generic positive-weight conditioning, not a new Markov axiom. -/
theorem filter_ambient_fkPMF_eq_map_glue_region_free_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ξ : Fin k → Bool) (hsep : Separated si ti so xo ξ) :
    PMF.map (fun ω : Fin m → Bool => glue ω ξ)
        ((regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary) =
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
        (rightWiredBoundary si ti so xo ζ)).filter (exteriorFiber ξ)
          (by
            let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
            rw [← normalizedPMF_eq_actual_fkPMF G (rightWiredBoundary si ti so xo ζ)
              hq hp₀ hp₁]
            exact exteriorFiber_support _ (fun ρ => G.fkWeight_pos hq hp₀ hp₁ _ ρ) ξ) := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let w : G.Configuration → NNReal := G.fkWeight q p (rightWiredBoundary si ti so xo ζ)
  have hw : ∀ ρ, 0 < w ρ := fun ρ => G.fkWeight_pos hq hp₀ hp₁ _ ρ
  have hcond : conditionedPMF w hw ξ =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
    rw [← normalizedPMF_eq_actual_fkPMF (regionGraph si ti)
      (regionGraph si ti).freeBoundary hq hp₀ hp₁]
    unfold conditionedPMF
    have h := normalizedPMF_map_eq_of_proportional (Equiv.refl (Fin m → Bool))
      ((regionGraph si ti).fkWeight q p (regionGraph si ti).freeBoundary)
      (fun ω => w (glue ω ξ))
      (q ^ Nat.card (rightWiredGraph si ti so xo ζ ξ).ConnectedComponent *
        FK.FinitePlane.edgeWeight p (1 - p) ξ)
      (rightWired_constant_pos si ti so xo hq hp₀ hp₁ ζ ξ)
      (fun ω => (regionGraph si ti).fkWeight_pos hq hp₀ hp₁ _ ω)
      (fun ω => hw (glue ω ξ)) (fun ω => fkWeight_glue_rightWired si ti so xo q p ζ ξ ω hsep)
    simp only [Equiv.coe_refl, PMF.map_id] at h
    convert h.symm using 1 <;> rfl
  have hnorm : normalizedPMF w hw = G.fkPMF hq hp₁.le
      (rightWiredBoundary si ti so xo ζ) := by
    exact normalizedPMF_eq_actual_fkPMF G (rightWiredBoundary si ti so xo ζ) hq hp₀ hp₁
  have hfinal := map_glue_conditionedPMF w hw ξ
  rw [hcond] at hfinal
  have hsupp : ∃ a ∈ exteriorFiber ξ,
      a ∈ (G.fkPMF hq hp₁.le (rightWiredBoundary si ti so xo ζ)).support := by
    rw [← hnorm]
    exact exteriorFiber_support w hw ξ
  have heq := hfinal.trans (pmf_filter_congr hnorm (exteriorFiber ξ) _ hsupp)
  with_unfolding_all exact heq

end FK.Exploration.WiredRightInterior

namespace FK.Exploration.WiredRightInterior

open scoped ENNReal BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Positive-weight support on an exterior fiber for right-supported wiring. -/
lemma exteriorFiber_support_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ξ : Fin k → Bool) :
    ∃ ρ ∈ exteriorFiber ξ, ρ ∈
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
        (rightWiredBoundary si ti so xo ζ)).support := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  rw [← normalizedPMF_eq_actual_fkPMF G (rightWiredBoundary si ti so xo ζ) hq hp₀ hp₁]
  exact exteriorFiber_support _ (fun ρ => G.fkWeight_pos hq hp₀ hp₁ _ ρ) ξ

end FK.Exploration.WiredRightInterior
