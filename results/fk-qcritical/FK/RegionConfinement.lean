/-
# Region continuation with shell-touching added edges, under a confined boundary
-/

import FK.NestedCommonUpperGood

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary

attribute [local instance] Classical.propDecidable

variable {W K I O : Type*} [Fintype W] [Fintype K] [Fintype I] [Fintype O]

/-- The region vertex type, read inside the ambient vertex sum. -/
def InRegion (x : W ⊕ K) : Prop := ∃ a : W, x = Sum.inl a

lemma inRegion_inl (a : W) : InRegion (K := K) (Sum.inl a) := ⟨a, rfl⟩
lemma not_inRegion_inr (k : K) : ¬ InRegion (W := W) (Sum.inr k) := by
  rintro ⟨a, h⟩; exact absurd h (by simp)
lemma inRegion_iff {x : W ⊕ K} : InRegion x ↔ x ∈ Set.range (Sum.inl : W → W ⊕ K) := by
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩

/-- Region vertices are the left summand; every open exterior edge avoids them
and the boundary setoid does not leave that summand.  Then a fixed-graph path
starting at a region vertex never leaves the region, and inside the region it is
exactly the prescribed `θ`-wiring. -/
theorem boundary_confined_reachable
    (s t : I ⊕ O → W ⊕ K) (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξ : O → Bool)
    (hconf : ∀ (a : W) (y : W ⊕ K), ζ.r (Sum.inl a) y → ∃ a' : W, y = Sum.inl a')
    (hθ : ∀ (a a' : W), ζ.r (Sum.inl a) (Sum.inl a') ↔ θ.r a a')
    (hsep : ∀ o, ξ o = true → ¬ InRegion (K := K) (s (Sum.inr o)) ∧
      ¬ InRegion (K := K) (t (Sum.inr o)))
    (a a' : W) :
    (fixedGraph s t ζ ξ).Reachable (Sum.inl a) (Sum.inl a') ↔ θ.r a a' := by
  have hstep : ∀ {y z : W ⊕ K},
      (fixedGraph s t ζ ξ).Adj y z →
        ((∃ c c' : W, y = Sum.inl c ∧ z = Sum.inl c' ∧ θ.r c c') ∨
          (¬ InRegion (K := K) y ∧ ¬ InRegion (K := K) z)) := by
    intro y z hyz
    rcases hyz.2 with hwire | ⟨e, he, hjoin⟩
    · cases y with
      | inl c =>
          obtain ⟨c', rfl⟩ := hconf c _ hwire
          exact Or.inl ⟨c, c', rfl, rfl, (hθ c c').mp hwire⟩
      | inr kk =>
          cases z with
          | inl c' =>
              obtain ⟨b, hb⟩ := hconf c' (Sum.inr kk) (ζ.symm hwire)
              exact absurd hb (by simp)
          | inr kk' => exact Or.inr ⟨not_inRegion_inr kk, not_inRegion_inr kk'⟩
    · cases e with
      | inl i => simp [glue] at he
      | inr o =>
          have ho : ξ o = true := he
          obtain ⟨hso, hto⟩ := hsep o ho
          have hs : ¬ InRegion (K := K) ((ambientOfSum s t).source (Sum.inr o)) := hso
          have ht : ¬ InRegion (K := K) ((ambientOfSum s t).target (Sum.inr o)) := hto
          refine Or.inr ⟨?_, ?_⟩
          · rcases hjoin with h | h
            · rwa [← h.1]
            · rwa [← h.2]
          · rcases hjoin with h | h
            · rwa [← h.2]
            · rwa [← h.1]
  constructor
  · intro h
    have key : ∀ z, (fixedGraph s t ζ ξ).Reachable (Sum.inl a) z →
        ∃ b : W, z = Sum.inl b ∧ θ.r a b := by
      intro z hz
      rw [SimpleGraph.reachable_iff_reflTransGen] at hz
      induction hz with
      | refl => exact ⟨a, rfl, θ.refl a⟩
      | @tail y z hxy hyz ih =>
          obtain ⟨b, rfl, hb⟩ := ih
          rcases hstep hyz with ⟨c, c', hc, hc', hcc'⟩ | ⟨hyn, hzn⟩
          · have hbc : b = c := Sum.inl.inj hc
            exact ⟨c', hc', θ.trans hb (hbc.symm ▸ hcc')⟩
          · exact absurd (inRegion_inl (K := K) b) hyn
    obtain ⟨b, hb, hab⟩ := key (Sum.inl a') h
    have hba : b = a' := (Sum.inl.inj hb).symm
    exact hba ▸ hab
  · intro h
    by_cases haa' : a = a'
    · subst haa'; exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable
        ⟨fun hc => haa' (Sum.inl.inj hc), Or.inl ((hθ a a').mpr h)⟩


theorem fixedGraph_reachable_inRegion
    (s t : I ⊕ O → W ⊕ K) (ζ : Setoid (W ⊕ K)) (ξ : O → Bool)
    (hconf : ∀ (a : W) (y : W ⊕ K), ζ.r (Sum.inl a) y → ∃ a' : W, y = Sum.inl a')
    (hsep : ∀ o, ξ o = true → ¬ InRegion (K := K) (s (Sum.inr o)) ∧
      ¬ InRegion (K := K) (t (Sum.inr o)))
    (a : W) {z : W ⊕ K} (hz : (fixedGraph s t ζ ξ).Reachable (Sum.inl a) z) :
    InRegion (K := K) z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hz
  induction hz with
  | refl => exact inRegion_inl a
  | @tail y z hxy hyz ih =>
      rcases hyz.2 with hwire | ⟨e, he, hjoin⟩
      · cases y with
        | inl c => obtain ⟨c', rfl⟩ := hconf c _ hwire; exact inRegion_inl c'
        | inr kk => exact absurd ih (not_inRegion_inr kk)
      · cases e with
        | inl i => simp [glue] at he
        | inr o =>
            have ho : ξ o = true := he
            obtain ⟨hso, hto⟩ := hsep o ho
            have hs : ¬ InRegion (K := K) ((ambientOfSum s t).source (Sum.inr o)) := hso
            have ht : ¬ InRegion (K := K) ((ambientOfSum s t).target (Sum.inr o)) := hto
            exact absurd (hjoin.elim (fun h => hs (h.1.symm ▸ ih))
              (fun h => ht (h.2.symm ▸ ih))) id


/-- Mixed summands are never adjacent in a disjoint graph sum. -/
lemma not_sum_adj_inl_inr {α β : Type*} (A : SimpleGraph α) (B : SimpleGraph β)
    (a : α) (b : β) : ¬ (A ⊕g B).Adj (Sum.inl a) (Sum.inr b) := by simp

/-- Mixed summands are never adjacent in a disjoint graph sum. -/
lemma not_sum_adj_inr_inl {α β : Type*} (A : SimpleGraph α) (B : SimpleGraph β)
    (a : α) (b : β) : ¬ (A ⊕g B).Adj (Sum.inr b) (Sum.inl a) := by simp

/-- The complement block of the confined split: the right summand with its
induced exterior wiring only. -/
noncomputable def rightConfinedGraph (si : I → W) (ti : I → W)
    (so xo : O → W ⊕ K) (ζ : Setoid (W ⊕ K)) (ξ : O → Bool) : SimpleGraph K where
  Adj x y := x ≠ y ∧
    (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ).r
      (Sum.inr x) (Sum.inr y)
  symm := ⟨fun x y h => ⟨h.1.symm, (effectiveBoundary _ _ _ _).symm h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- **Confined region split.**  Under a region-confined boundary setoid and a
separated exterior configuration, the interior graph with the induced boundary
is the disjoint sum of the `θ`-wired region graph and the induced right graph.
Added labels may be incident with the right summand arbitrarily. -/
theorem interiorGraph_confined_eq_sum
    (si : I → W) (ti : I → W) (so xo : O → W ⊕ K) (θ : Setoid W)
    (ζ : Setoid (W ⊕ K)) (ξ : O → Bool) (ω : I → Bool)
    (hconf : ∀ (a : W) (y : W ⊕ K), ζ.r (Sum.inl a) y → ∃ a' : W, y = Sum.inl a')
    (hθ : ∀ (a a' : W), ζ.r (Sum.inl a) (Sum.inl a') ↔ θ.r a a')
    (hsep : ∀ o, ξ o = true →
      ¬ InRegion (K := K) (splitSource si so (Sum.inr o)) ∧
        ¬ InRegion (K := K) (splitTarget ti xo (Sum.inr o))) :
    (interiorOfSum (splitSource si so) (splitTarget ti xo)).connectionGraph
        (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ) ω =
      (regionGraph si ti).connectionGraph θ ω ⊕g
        rightConfinedGraph si ti so xo ζ ξ := by
  have hbd := boundary_confined_reachable (splitSource si so) (splitTarget ti xo)
    θ ζ ξ hconf hθ hsep
  have hcross : ∀ (a : W) (k : K),
      ¬ (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ).r
        (Sum.inl a) (Sum.inr k) := by
    intro a k hr
    exact not_inRegion_inr k
      (fixedGraph_reachable_inRegion (splitSource si so) (splitTarget ti xo) ζ ξ
        hconf hsep a hr)
  have hcross' : ∀ (k : K) (a : W),
      ¬ (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ).r
        (Sum.inr k) (Sum.inl a) := by
    intro k a hr
    exact hcross a k ((effectiveBoundary _ _ _ _).symm hr)
  -- every interior label joins two region vertices
  have hjregion : ∀ (i : I) (x y : W ⊕ K),
      (interiorOfSum (splitSource si so) (splitTarget ti xo)).Joins i x y →
        InRegion (K := K) x ∧ InRegion (K := K) y := by
    intro i x y h
    have hs : (interiorOfSum (splitSource si so) (splitTarget ti xo)).source i =
        Sum.inl (si i) := rfl
    have ht : (interiorOfSum (splitSource si so) (splitTarget ti xo)).target i =
        Sum.inl (ti i) := rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨?_, ?_⟩
      · rw [← h1, hs]; exact inRegion_inl (si i)
      · rw [← h2, ht]; exact inRegion_inl (ti i)
    · refine ⟨?_, ?_⟩
      · rw [← h2, ht]; exact inRegion_inl (ti i)
      · rw [← h1, hs]; exact inRegion_inl (si i)
  have hjoin : ∀ (i : I) (a a' : W),
      (interiorOfSum (splitSource si so) (splitTarget ti xo)).Joins i
          (Sum.inl a) (Sum.inl a') ↔ (regionGraph si ti).Joins i a a' := by
    intro i a a'
    constructor
    · intro h
      have hs : (interiorOfSum (splitSource si so) (splitTarget ti xo)).source i =
          Sum.inl (si i) := rfl
      have ht : (interiorOfSum (splitSource si so) (splitTarget ti xo)).target i =
          Sum.inl (ti i) := rfl
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hs] at h1; rw [ht] at h2
        exact Or.inl ⟨Sum.inl.inj h1, Sum.inl.inj h2⟩
      · rw [hs] at h1; rw [ht] at h2
        exact Or.inr ⟨Sum.inl.inj h1, Sum.inl.inj h2⟩
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg Sum.inl h1, congrArg Sum.inl h2⟩
      · exact Or.inr ⟨congrArg Sum.inl h1, congrArg Sum.inl h2⟩
  ext x y
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      show ((Sum.inl a : W ⊕ K) ≠ Sum.inl a' ∧
          ((effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ).r
              (Sum.inl a) (Sum.inl a') ∨
            ∃ i, ω i = true ∧ (interiorOfSum (splitSource si so)
              (splitTarget ti xo)).Joins i (Sum.inl a) (Sum.inl a')))
        ↔ (a ≠ a' ∧ (θ.r a a' ∨ ∃ i, ω i = true ∧ (regionGraph si ti).Joins i a a'))
      constructor
      · rintro ⟨hne, hb | ⟨i, hi, hj⟩⟩
        · exact ⟨fun hc => hne (by rw [hc]), Or.inl ((hbd a a').mp hb)⟩
        · exact ⟨fun hc => hne (by rw [hc]), Or.inr ⟨i, hi, (hjoin i a a').mp hj⟩⟩
      · rintro ⟨hne, hb | ⟨i, hi, hj⟩⟩
        · exact ⟨fun hc => hne (Sum.inl.inj hc), Or.inl ((hbd a a').mpr hb)⟩
        · exact ⟨fun hc => hne (Sum.inl.inj hc), Or.inr ⟨i, hi, (hjoin i a a').mpr hj⟩⟩
    | inr k =>
      constructor
      · rintro ⟨-, hb | ⟨i, hi, hj⟩⟩
        · exact absurd hb (hcross a k)
        · exact absurd (hjregion i _ _ hj).2 (not_inRegion_inr k)
      · intro h
        exact absurd h (not_sum_adj_inl_inr ((regionGraph si ti).connectionGraph θ ω)
          (rightConfinedGraph si ti so xo ζ ξ) a k)
  | inr k =>
    cases y with
    | inl a' =>
      constructor
      · rintro ⟨-, hb | ⟨i, hi, hj⟩⟩
        · exact absurd hb (hcross' k a')
        · exact absurd (hjregion i _ _ hj).1 (not_inRegion_inr k)
      · intro h
        exact absurd h (not_sum_adj_inr_inl ((regionGraph si ti).connectionGraph θ ω)
          (rightConfinedGraph si ti so xo ζ ξ) a' k)
    | inr k' =>
      have hno : ¬ (∃ i, ω i = true ∧ (interiorOfSum (splitSource si so)
          (splitTarget ti xo)).Joins i (Sum.inr k) (Sum.inr k')) := by
        rintro ⟨i, -, hj⟩
        exact not_inRegion_inr k (hjregion i _ _ hj).1
      show ((Sum.inr k : W ⊕ K) ≠ Sum.inr k' ∧
          ((effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ).r
              (Sum.inr k) (Sum.inr k') ∨ ∃ i, ω i = true ∧
            (interiorOfSum (splitSource si so) (splitTarget ti xo)).Joins i
              (Sum.inr k) (Sum.inr k')))
        ↔ (rightConfinedGraph si ti so xo ζ ξ).Adj k k'
      constructor
      · rintro ⟨hne, hb | hb⟩
        · exact ⟨fun hc => hne (by rw [hc]), hb⟩
        · exact absurd hb hno
      · rintro ⟨hne, hb⟩
        exact ⟨fun hc => hne (Sum.inr.inj hc), Or.inl hb⟩

/-- Component counts split with a fixed right contribution, for an arbitrary
region setoid `θ` and an arbitrary confined boundary. -/
theorem componentCount_split_confined
    (si : I → W) (ti : I → W) (so xo : O → W ⊕ K) (θ : Setoid W)
    (ζ : Setoid (W ⊕ K)) (ξ : O → Bool) (ω : I → Bool)
    (hconf : ∀ (a : W) (y : W ⊕ K), ζ.r (Sum.inl a) y → ∃ a' : W, y = Sum.inl a')
    (hθ : ∀ (a a' : W), ζ.r (Sum.inl a) (Sum.inl a') ↔ θ.r a a')
    (hsep : ∀ o, ξ o = true →
      ¬ InRegion (K := K) (splitSource si so (Sum.inr o)) ∧
        ¬ InRegion (K := K) (splitTarget ti xo (Sum.inr o))) :
    (interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
        (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ) ω =
      (regionGraph si ti).componentCount θ ω +
        Nat.card (rightConfinedGraph si ti so xo ζ ξ).ConnectedComponent := by
  change Nat.card ((interiorOfSum (splitSource si so)
    (splitTarget ti xo)).connectionGraph
      (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ) ω).ConnectedComponent = _
  rw [interiorGraph_confined_eq_sum si ti so xo θ ζ ξ ω hconf hθ hsep]
  exact SimpleGraph.natCard_connectedComponent_sum _ _

/-- **Region continuation at a fixed exterior configuration.**  For an arbitrary
region setoid `θ`, an arbitrary region-confined boundary, and a separated
exterior configuration, the induced interior FK law of the large graph is the
actual region FK law with boundary `θ` — whatever the added labels do to the
right summand. -/
theorem interior_fkPMF_eq_region_confined
    (si : I → W) (ti : I → W) (so xo : O → W ⊕ K) (θ : Setoid W)
    (ζ : Setoid (W ⊕ K)) (ξ : O → Bool)
    (hconf : ∀ (a : W) (y : W ⊕ K), ζ.r (Sum.inl a) y → ∃ a' : W, y = Sum.inl a')
    (hθ : ∀ (a a' : W), ζ.r (Sum.inl a) (Sum.inl a') ↔ θ.r a a')
    (hsep : ∀ o, ξ o = true →
      ¬ InRegion (K := K) (splitSource si so (Sum.inr o)) ∧
        ¬ InRegion (K := K) (splitTarget ti xo (Sum.inr o)))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (interiorOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
        (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  rw [← normalizedPMF_eq_actual_fkPMF
      (interiorOfSum (splitSource si so) (splitTarget ti xo))
      (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ) hq hp₀ hp₁,
    ← normalizedPMF_eq_actual_fkPMF (regionGraph si ti) θ hq hp₀ hp₁]
  let c : NNReal := q ^ Nat.card (rightConfinedGraph si ti so xo ζ ξ).ConnectedComponent
  have hc : 0 < c := pow_pos hq _
  have hprop : ∀ ω : I → Bool,
      FK.FinitePlane.fkWeight q p
        ((interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
          (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ)) ω =
        c * FK.FinitePlane.fkWeight q p
          ((regionGraph si ti).componentCount θ) ω := by
    intro ω
    simp only [FK.FinitePlane.fkWeight, c,
      componentCount_split_confined si ti so xo θ ζ ξ ω hconf hθ hsep, pow_add]
    ac_rfl
  let d : (regionGraph si ti).Configuration ≃
      (interiorOfSum (splitSource si so) (splitTarget ti xo)).Configuration :=
    Equiv.refl _
  have h := normalizedPMF_map_eq_of_proportional d
    (fun ω : (regionGraph si ti).Configuration => FK.FinitePlane.fkWeight q p
      ((regionGraph si ti).componentCount θ) ω)
    (fun ω : (interiorOfSum (splitSource si so) (splitTarget ti xo)).Configuration =>
      FK.FinitePlane.fkWeight q p
        ((interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
          (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ)) ω)
    c hc (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _)
    (fun _ => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ _) hprop
  rw [← h]
  change PMF.map (id : (regionGraph si ti).Configuration →
    (regionGraph si ti).Configuration) _ = _
  exact PMF.map_id _

/-- **Actual ambient region conditioning at a fixed exterior configuration.**
The ordinary FK law of the whole graph, conditioned on a separated exterior
configuration, pushes the region-event law of the actual region FK law with
boundary `θ` forward.  No freshness or disjointness of the exterior/added block
is assumed. -/
theorem filter_ambient_fkPMF_eq_map_glue_region_confined
    (si : I → W) (ti : I → W) (so xo : O → W ⊕ K) (θ : Setoid W)
    (ζ : Setoid (W ⊕ K)) (ξ : O → Bool)
    (hconf : ∀ (a : W) (y : W ⊕ K), ζ.r (Sum.inl a) y → ∃ a' : W, y = Sum.inl a')
    (hθ : ∀ (a a' : W), ζ.r (Sum.inl a) (Sum.inl a') ↔ θ.r a a')
    (hsep : ∀ o, ξ o = true →
      ¬ InRegion (K := K) (splitSource si so (Sum.inr o)) ∧
        ¬ InRegion (K := K) (splitTarget ti xo (Sum.inr o)))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (fun ω : I → Bool => glue ω ξ)
        ((regionGraph si ti).fkPMF hq hp₁.le θ) =
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le ζ).filter
        (exteriorFiber ξ)
        (exteriorFiber_support (splitSource si so) (splitTarget ti xo) ζ hq hp₀ hp₁ ξ) := by
  rw [← interior_fkPMF_eq_region_confined si ti so xo θ ζ ξ hconf hθ hsep hq hp₀ hp₁]
  exact filter_fkPMF_eq_map_glue (splitSource si so) (splitTarget ti xo) ζ hq hp₀ hp₁ ξ

/-! ## The prefix-only (marginal over the added block) continuation -/

variable {k a : ℕ}

/-- The event that the small box's exterior bits equal `ξS`. -/
def prefixEvent (ξS : Fin k → Bool) : Set (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
  {ρ | ∀ i : Fin k, ρ (Sum.inr (Sum.inl i)) = ξS i}

/-- The full exterior configuration built from the prescribed small bits and
the free added bits. -/
def bigExterior (ξS : Fin k → Bool) (γ : Fin a → Bool) : Fin k ⊕ Fin a → Bool :=
  Sum.elim ξS γ

/-- A configuration with the prescribed small exterior bits is determined by its
region bits and its added bits. -/
lemma eq_glue_of_mem_prefixEvent {ξS : Fin k → Bool}
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool} (hρ : ρ ∈ prefixEvent (I := I) (a := a) ξS) :
    ρ = glue (ρ ∘ Sum.inl) (bigExterior ξS (ρ ∘ Sum.inr ∘ Sum.inr)) := by
  funext x
  cases x with
  | inl i => rfl
  | inr l =>
      cases l with
      | inl j => exact hρ j
      | inr j => rfl

/-- Region and added bits of a configuration with prescribed small exterior bits. -/
def prefixToFun {ξS : Fin k → Bool}
    (ρ : {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool // ρ ∈ prefixEvent (I := I) (a := a) ξS}) :
    (I → Bool) × (Fin a → Bool) :=
  (ρ.1 ∘ Sum.inl, ρ.1 ∘ Sum.inr ∘ Sum.inr)

/-- Rebuild a configuration from region and added bits. -/
def prefixInvFun (ξS : Fin k → Bool) (z : (I → Bool) × (Fin a → Bool)) :
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool // ρ ∈ prefixEvent (I := I) (a := a) ξS} :=
  ⟨glue z.1 (bigExterior ξS z.2), fun _ => rfl⟩

/-- Configurations with fixed small exterior bits are exactly a region
configuration together with an added configuration. -/
noncomputable def prefixEquiv (ξS : Fin k → Bool) :
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool // ρ ∈ prefixEvent (I := I) (a := a) ξS} ≃
      (I → Bool) × (Fin a → Bool) where
  toFun := prefixToFun (I := I) (a := a)
  invFun := prefixInvFun ξS
  left_inv ρ := by
    refine Subtype.ext ?_
    exact (eq_glue_of_mem_prefixEvent (I := I) (a := a) ρ.2).symm
  right_inv z := by
    obtain ⟨ω, γ⟩ := z
    rfl

/-- Sums over the prefix event are sums over region and added configurations. -/
lemma tsum_prefix_fiber {F : (I ⊕ (Fin k ⊕ Fin a) → Bool) → ℝ≥0∞} (ξS : Fin k → Bool) :
    (∑' ρ, if ρ ∈ prefixEvent (I := I) (a := a) ξS then F ρ else 0)
      = ∑' ω : I → Bool, ∑' γ : Fin a → Bool, F (glue ω (bigExterior ξS γ)) := by
  have h1 : (∑' ρ : {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool //
        ρ ∈ prefixEvent (I := I) (a := a) ξS}, F ρ.1)
      = ∑' ρ, if ρ ∈ prefixEvent (I := I) (a := a) ξS then F ρ else 0 := by
    rw [tsum_subtype]
    simp [Set.indicator_apply]
  rw [← h1, ← ENNReal.tsum_prod, ← (prefixEquiv (I := I) (a := a) ξS).tsum_eq
    (fun z : (I → Bool) × (Fin a → Bool) => F (glue z.1 (bigExterior ξS z.2)))]
  apply tsum_congr
  intro ρ
  exact congrArg F (eq_glue_of_mem_prefixEvent (I := I) (a := a) ρ.2)

/-- The fibre of the prefix event over a fixed region configuration. -/
def prefixFiberSet (ξS : Fin k → Bool) (ω : I → Bool) :
    Set (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
  {ρ | ρ ∈ prefixEvent (I := I) (a := a) ξS ∧ ρ ∘ Sum.inl = ω}

/-- Region and added bits, with the region part fixed. -/
def prefixToFunFixed {ξS : Fin k → Bool} {ω : I → Bool}
    (ρ : {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool // ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω}) :
    Fin a → Bool :=
  ρ.1 ∘ Sum.inr ∘ Sum.inr

lemma mem_prefixFiberSet_iff {ξS : Fin k → Bool} {ω : I → Bool}
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool} :
    ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω ↔
      ρ ∈ prefixEvent (I := I) (a := a) ξS ∧ ρ ∘ Sum.inl = ω := Iff.rfl

/-- A configuration in one fibre of the prefix event is rebuilt from its region
and added bits. -/
lemma eq_glue_of_mem_prefixFiberSet {ξS : Fin k → Bool} {ω : I → Bool}
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool}
    (hρ : ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω) :
    ρ = glue ω (bigExterior ξS (ρ ∘ Sum.inr ∘ Sum.inr)) := by
  have h1 := eq_glue_of_mem_prefixEvent (I := I) (a := a) hρ.1
  rw [h1, hρ.2]
  simp only [bigExterior]
  rfl


/-- The fibre of the prefix event over a fixed region configuration is exactly
the added configurations. -/
noncomputable def prefixFiberEquiv (ξS : Fin k → Bool) (ω : I → Bool) :
    (Fin a → Bool) ≃ {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool //
      ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω} where
  toFun γ := ⟨glue ω (bigExterior ξS γ), fun i => rfl, rfl⟩
  invFun := prefixToFunFixed (I := I) (a := a) (ξS := ξS) (ω := ω)
  left_inv γ := by
    funext j
    rfl
  right_inv ρ := by
    refine Subtype.ext ?_
    simp only [prefixToFunFixed]
    exact (eq_glue_of_mem_prefixFiberSet (I := I) (a := a) ρ.2).symm

/-- Sums over one fibre of the prefix event are sums over the added
configurations. -/
lemma tsum_prefix_fiber_fixed {F : (I ⊕ (Fin k ⊕ Fin a) → Bool) → ℝ≥0∞}
    (ξS : Fin k → Bool) (ω : I → Bool) :
    (∑' ρ, if ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω then F ρ else 0)
      = ∑' γ : Fin a → Bool, F (glue ω (bigExterior ξS γ)) := by
  have h1 : (∑' ρ : {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool //
        ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω}, F ρ.1)
      = ∑' ρ, if ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω then F ρ else 0 := by
    rw [tsum_subtype]
    simp [Set.indicator_apply]
  have hE := (prefixFiberEquiv (I := I) (a := a) ξS ω).tsum_eq
    (fun ρ : {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool //
      ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω} => F ρ.1)
  rw [← h1]
  exact hE.symm

/-- The large graph's exterior source map: the small box's exterior labels
first, then the added labels. -/
def bigSo (so : Fin k → W ⊕ K) (ao : Fin a → W ⊕ K) : Fin k ⊕ Fin a → W ⊕ K :=
  Sum.elim so ao

/-- The large graph's exterior target map. -/
def bigXo (xo : Fin k → W ⊕ K) (bo : Fin a → W ⊕ K) : Fin k ⊕ Fin a → W ⊕ K :=
  Sum.elim xo bo

/-- Weight-level region factorization at a fixed exterior configuration. -/
theorem interiorWeight_confined_eq
    (si : I → W) (ti : I → W) (so xo : O → W ⊕ K) (θ : Setoid W)
    (ζ : Setoid (W ⊕ K)) (ξ : O → Bool) (ω : I → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c' : W, y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsep : ∀ o, ξ o = true →
      ¬ InRegion (K := K) (splitSource si so (Sum.inr o)) ∧
        ¬ InRegion (K := K) (splitTarget ti xo (Sum.inr o)))
    (q p : NNReal) :
    FK.FinitePlane.fkWeight q p
        ((interiorOfSum (splitSource si so) (splitTarget ti xo)).componentCount
          (effectiveBoundary (splitSource si so) (splitTarget ti xo) ζ ξ)) ω =
      q ^ Nat.card (rightConfinedGraph si ti so xo ζ ξ).ConnectedComponent *
        FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω := by
  simp only [FK.FinitePlane.fkWeight,
    componentCount_split_confined si ti so xo θ ζ ξ ω hconf hθ hsep, pow_add]
  ac_rfl

/-- The separatedness hypothesis for the full exterior configuration, from the
small exterior configuration and the region-avoidance of the added labels. -/
theorem separated_bigExterior
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (ξS : Fin k → Bool) (γ : Fin a → Bool)
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j)) :
    ∀ l : Fin k ⊕ Fin a, bigExterior ξS γ l = true →
      ¬ InRegion (K := K) (splitSource si (bigSo so ao) (Sum.inr l)) ∧
        ¬ InRegion (K := K) (splitTarget ti (bigXo xo bo) (Sum.inr l)) := by
  intro l h
  cases l with
  | inl i => exact hsepS i h
  | inr j => exact havoid j

/-- **Prefix weight sum.**  Summing the large graph's FK weights at a fixed
region configuration over all added configurations gives a constant (the
effective right-block weight) times the region FK weight at `θ`. -/
theorem ambientWeight_prefix_sum
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξS : Fin k → Bool) (ω : I → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c' : W, y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    (q p : NNReal) :
    (∑' γ : Fin a → Bool,
        (ambientOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo))).fkWeight
          q p ζ (glue ω (bigExterior ξS γ))) =
      (∑' γ : Fin a → Bool, FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) *
          q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ
            (bigExterior ξS γ)).ConnectedComponent) *
        FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω := by
  rw [← tsum_mul_right]
  refine tsum_congr ?_
  intro γ
  have h1 := FK.FinitePlane.ArbitraryBoundary.fkWeight_glue (s := splitSource si (bigSo so ao))
    (t := splitTarget ti (bigXo xo bo)) ζ q p ω (bigExterior ξS γ)
  have h2 := interiorWeight_confined_eq si ti (bigSo so ao) (bigXo xo bo) θ ζ
    (bigExterior ξS γ) ω hconf hθ (separated_bigExterior si ti so xo ao bo ξS γ
      hsepS havoid) q p
  have key : (ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkWeight q p ζ (glue ω (bigExterior ξS γ)) =
      FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) *
        (q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ
            (bigExterior ξS γ)).ConnectedComponent *
          FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω) :=
    h1.trans (congrArg (fun x => FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) * x) h2)
  exact key.trans (by ring)

/-- The prefix event is supported: the all-closed configuration with the
prescribed exterior bits has positive FK mass. -/
lemma prefixEvent_support (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K)) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ξS : Fin k → Bool) :
    ∃ ρ ∈ prefixEvent (I := I) (a := a) ξS,
      ρ ∈ ((ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).support := by
  refine ⟨glue (fun _ => false) (bigExterior ξS (fun _ => false)), fun i => rfl, ?_⟩
  exact (PMF.mem_support_iff (p := (ambientOfSum (splitSource si (bigSo so ao))
    (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) _).mpr
    (FK.Exploration.FKCoupling.fkPMF_ne_zero
      (ambientOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)))
      hq hp₀ hp₁ ζ _)

end FK.RegionConfinement
