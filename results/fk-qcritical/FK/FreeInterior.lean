import FK.ExteriorMarkov
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# The free interior law on a separated vertex split

When every interior edge has both endpoints on the left of a sum type and no
open exterior edge touches the left, the interior graph splits as a disjoint
sum.  Its left graph is the actual free interior graph and its right graph is
the fixed exterior wiring closure.  Component counting therefore identifies
the induced interior FK law with the actual free FK law on the left.
-/

namespace SimpleGraph

variable {U K : Type*} (G : SimpleGraph U) (H : SimpleGraph K)

lemma exists_left_of_sum_reachable_inl {u : U} {x : U ⊕ K}
    (h : (G ⊕g H).Reachable (Sum.inl u) x) :
    ∃ v, x = Sum.inl v ∧ G.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨u, rfl, SimpleGraph.Reachable.refl u⟩
  | @tail y z hxy hyz ih =>
      rcases ih with ⟨v, rfl, hv⟩
      cases z with
      | inl z =>
          have hyz' : G.Adj v z := by simpa using hyz
          exact ⟨z, rfl, hv.trans hyz'.reachable⟩
      | inr z => simp at hyz

lemma exists_right_of_sum_reachable_inr {w : K} {x : U ⊕ K}
    (h : (G ⊕g H).Reachable (Sum.inr w) x) :
    ∃ z, x = Sum.inr z ∧ H.Reachable w z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨w, rfl, SimpleGraph.Reachable.refl w⟩
  | @tail y z hxy hyz ih =>
      rcases ih with ⟨w', rfl, hw'⟩
      cases z with
      | inl z => simp at hyz
      | inr z =>
          have hyz' : H.Adj w' z := by simpa using hyz
          exact ⟨z, rfl, hw'.trans hyz'.reachable⟩

lemma sum_reachable_inl_inl_iff {u v : U} :
    (G ⊕g H).Reachable (Sum.inl u) (Sum.inl v) ↔ G.Reachable u v := by
  constructor
  · intro h
    obtain ⟨w, hw, huw⟩ := G.exists_left_of_sum_reachable_inl H h
    cases hw
    exact huw
  · intro h
    exact h.map SimpleGraph.Embedding.sumInl.toHom

lemma sum_reachable_inr_inr_iff {w z : K} :
    (G ⊕g H).Reachable (Sum.inr w) (Sum.inr z) ↔ H.Reachable w z := by
  constructor
  · intro h
    obtain ⟨x, hx, hwx⟩ := G.exists_right_of_sum_reachable_inr H h
    cases hx
    exact hwx
  · intro h
    exact h.map SimpleGraph.Embedding.sumInr.toHom

/-- Connected components of a disjoint sum are the sum of its component
types. -/
noncomputable def connectedComponentSumEquiv :
    (G ⊕g H).ConnectedComponent ≃ G.ConnectedComponent ⊕ H.ConnectedComponent where
  toFun c := Quot.lift
    (fun x : U ⊕ K => match x with
      | Sum.inl u => Sum.inl (G.connectedComponentMk u)
      | Sum.inr w => Sum.inr (H.connectedComponentMk w))
    (by
      intro x y hxy
      cases x with
      | inl u =>
          cases y with
          | inl v =>
              exact congrArg Sum.inl (SimpleGraph.ConnectedComponent.sound
                ((G.sum_reachable_inl_inl_iff H).mp hxy))
          | inr w => exact (not_reachable_sum_inl_inr u w hxy).elim
      | inr w =>
          cases y with
          | inl u => exact (not_reachable_sum_inl_inr u w hxy.symm).elim
          | inr z =>
              exact congrArg Sum.inr (SimpleGraph.ConnectedComponent.sound
                ((G.sum_reachable_inr_inr_iff H).mp hxy))) c
  invFun
    | Sum.inl c => c.map SimpleGraph.Embedding.sumInl.toHom
    | Sum.inr c => c.map SimpleGraph.Embedding.sumInr.toHom
  left_inv c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h x => cases x <;> rfl
  right_inv c := by
    cases c with
    | inl c =>
        induction c using SimpleGraph.ConnectedComponent.ind with
        | h u => rfl
    | inr c =>
        induction c using SimpleGraph.ConnectedComponent.ind with
        | h w => rfl

lemma natCard_connectedComponent_sum [Finite U] [Finite K] :
    Nat.card (G ⊕g H).ConnectedComponent =
      Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
  rw [Nat.card_congr (G.connectedComponentSumEquiv H), Nat.card_sum]

end SimpleGraph

namespace FK.FinitePlane.FreeInterior

open scoped ENNReal BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph

variable {U K I O : Type*} [Fintype U] [Fintype K] [Fintype I] [Fintype O]

/-- Interior endpoints are on the left; exterior endpoints are arbitrary
until the open-edge separation condition is imposed. -/
def splitSource (si : I → U) (so : O → U ⊕ K) : I ⊕ O → U ⊕ K
  | Sum.inl i => Sum.inl (si i)
  | Sum.inr o => so o

/-- Target analog of `splitSource`. -/
def splitTarget (ti : I → U) (xo : O → U ⊕ K) : I ⊕ O → U ⊕ K
  | Sum.inl i => Sum.inl (ti i)
  | Sum.inr o => xo o

/-- The actual graph on the interior vertex type alone, with free boundary. -/
def regionGraph (si ti : I → U) : LabelledMultigraph where
  Vertex := U
  Edge := I
  source := si
  target := ti

/-- The right summand is the closure of the exterior open-connected relation.
It is independent of the interior configuration. -/
def rightBoundaryGraph (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    (ξ : O → Bool) : SimpleGraph K where
  Adj x y := x ≠ y ∧
    (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ).r
      (Sum.inr x) (Sum.inr y)
  symm := ⟨by
    intro x y hxy
    exact ⟨hxy.1.symm, (exteriorBoundary _ _ _).symm hxy.2⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

/-- No open exterior edge touches an interior vertex. -/
def Separated (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    (ξ : O → Bool) : Prop :=
  ∀ o, ξ o = true →
    so o ∉ Set.range (Sum.inl : U → U ⊕ K) ∧
      xo o ∉ Set.range (Sum.inl : U → U ⊕ K)

/-- The exterior boundary is literally equality on left vertices. -/
lemma boundary_inl_related_iff (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    (ξ : O → Bool) (hsep : Separated si ti so xo ξ) (u : U) (x : U ⊕ K) :
    (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ).r
      (Sum.inl u) x ↔ Sum.inl u = x := by
  apply exteriorBoundary_related_iff_of_no_open_incident
    (U := Set.range (Sum.inl : U → U ⊕ K)) _ _ _ ?_ ⟨u, rfl⟩
  simpa [Separated, splitSource, splitTarget] using hsep

/-- The actual induced interior graph splits into the free region graph and
fixed exterior wiring closure. -/
theorem interiorGraph_eq_sum (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    (ξ : O → Bool) (ω : I → Bool) (hsep : Separated si ti so xo ξ) :
    interiorGraph (splitSource si so) (splitTarget ti xo) ω ξ =
      (regionGraph si ti).connectionGraph (regionGraph si ti).freeBoundary ω ⊕g
        rightBoundaryGraph si ti so xo ξ := by
  have hleft := boundary_inl_related_iff si ti so xo ξ hsep
  have hleft' : ∀ (u : U) (x : U ⊕ K),
      (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ).r
        x (Sum.inl u) ↔ x = Sum.inl u := by
    intro u x
    constructor
    · intro h
      exact ((hleft u x).mp ((exteriorBoundary _ _ _).symm h)).symm
    · intro h
      subst x
      exact (exteriorBoundary _ _ _).refl _
  ext x y
  cases x <;> cases y <;>
    simp [interiorGraph, interiorOfSum, LabelledMultigraph.connectionGraph,
      LabelledMultigraph.Joins, LabelledMultigraph.freeBoundary,
      regionGraph, rightBoundaryGraph, splitSource, splitTarget, hleft, hleft']
  case inl.inl u v =>
    intro huv
    have hn : ¬ (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ).r
        (Sum.inl u) (Sum.inl v) := by
      intro h
      have heq := (hleft u (Sum.inl v)).mp h
      exact huv (Sum.inl.inj heq)
    constructor
    · rintro (h | h)
      · exact (hn h).elim
      · exact Or.inr h
    · rintro (h | h)
      · exact (huv h).elim
      · exact Or.inr h
  case inl.inr u w =>
    intro h
    have heq := (hleft u (Sum.inr w)).mp h
    contradiction
  case inr.inl w u =>
    intro h
    have heq := (hleft' u (Sum.inr w)).mp h
    contradiction
  case inr.inr x y =>
    exact fun _ => Iff.rfl

/-- Component counts split with a fixed exterior contribution. -/
lemma componentCount_split (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    (ξ : O → Bool) (ω : I → Bool) (hsep : Separated si ti so xo ξ) :
    (interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
        (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ) ω =
      (regionGraph si ti).componentCount (regionGraph si ti).freeBoundary ω +
        Nat.card (rightBoundaryGraph si ti so xo ξ).ConnectedComponent := by
  change Nat.card (interiorGraph (splitSource si so) (splitTarget ti xo) ω ξ).ConnectedComponent =
    Nat.card ((regionGraph si ti).connectionGraph
      (regionGraph si ti).freeBoundary ω).ConnectedComponent + _
  rw [interiorGraph_eq_sum si ti so xo ξ ω hsep]
  exact SimpleGraph.natCard_connectedComponent_sum _ _

/-- The normalized interior law with exterior components wired is exactly the
actual free FK law on the interior vertex type. -/
theorem interior_fkPMF_eq_region_free (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : O → Bool) (hsep : Separated si ti so xo ξ) :
    (interiorOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
        (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  rw [← normalizedPMF_eq_actual_fkPMF
      (interiorOfSum (splitSource si so) (splitTarget ti xo))
      (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ) hq hp₀ hp₁,
    ← normalizedPMF_eq_actual_fkPMF (regionGraph si ti)
      (regionGraph si ti).freeBoundary hq hp₀ hp₁]
  let c : NNReal := q ^ Nat.card (rightBoundaryGraph si ti so xo ξ).ConnectedComponent
  have hc : 0 < c := pow_pos hq _
  have hprop : ∀ ω : I → Bool,
      FK.FinitePlane.fkWeight q p
        ((interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
          (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ)) ω =
        c * FK.FinitePlane.fkWeight q p
          ((regionGraph si ti).componentCount (regionGraph si ti).freeBoundary) ω := by
    intro ω
    simp only [FK.FinitePlane.fkWeight, c, componentCount_split si ti so xo ξ ω hsep,
      pow_add]
    ac_rfl
  let d : (regionGraph si ti).Configuration ≃
      (interiorOfSum (splitSource si so) (splitTarget ti xo)).Configuration :=
    Equiv.refl _
  have h := normalizedPMF_map_eq_of_proportional d
    (fun ω : (regionGraph si ti).Configuration => FK.FinitePlane.fkWeight q p
      ((regionGraph si ti).componentCount (regionGraph si ti).freeBoundary) ω)
    (fun ω : (interiorOfSum (splitSource si so) (splitTarget ti xo)).Configuration =>
      FK.FinitePlane.fkWeight q p
        ((interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
          (exteriorBoundary (splitSource si so) (splitTarget ti xo) ξ)) ω)
    c hc (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _) hprop
  rw [← h]
  change PMF.map (id : (regionGraph si ti).Configuration →
    (regionGraph si ti).Configuration) _ = _
  exact PMF.map_id _

/-- The actual ambient FK law conditioned on a separated exterior fiber is
the pushforward of the actual free interior-region law. -/
theorem filter_ambient_fkPMF_eq_map_glue_region_free
    (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : O → Bool) (hsep : Separated si ti so xo ξ) :
    PMF.map (fun ω : I → Bool => glue ω ξ)
        ((regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary) =
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
        (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary).filter
          (exteriorFiber ξ)
          (exteriorFiber_support_actual _ _ hq hp₀ hp₁ ξ) := by
  rw [← interior_fkPMF_eq_region_free si ti so xo hq hp₀ hp₁ ξ hsep]
  exact filter_ambient_fkPMF_eq_map_glue _ _ hq hp₀ hp₁ ξ

end FK.FinitePlane.FreeInterior
