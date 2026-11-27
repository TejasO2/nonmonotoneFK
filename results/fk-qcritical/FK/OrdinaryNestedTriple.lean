import FK.GenericNestedGood

/-!
# Lemma 2.1: common-upper identity on an ordinary confined nested split

This file lifts the shell-first free-interior pair identity to the actual
FK/FK/Bernoulli ordered triple.  It uses the original nested graph and its
confined boundary data, not a right-disjoint extension.  The third coordinate
is the same in both good intersections.
-/

open scoped ENNReal NNReal BigOperators Classical
open MeasureTheory

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary
open FK.RegionConfinement.ConfinedStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.Exploration.StoppedInterior FK.Exploration.TwoSidedInterior
open FK.Exploration.NestedCoupledGood

namespace FK.NestedRegionExploration

/-- The generic nested restriction along `nestedExploreEquiv` is the concrete
shell-plus-region restriction of the shell-first exploration theorem. -/
theorem restrictDelta_nestedExploreEquiv
    {VS VD : Type*} [Fintype VS] [Fintype VD] {m k a : ℕ}
    (sS tS : Fin (k + (m + a)) → VS) (sD tD : Fin (k + m) → VD)
    (ω : Fin (k + (m + a)) → Bool) :
    restrictΔ
      (GS := finIndexedGraph VS (k + (m + a)) sS tS)
      (GD := finIndexedGraph VD (k + m) sD tD)
      (GO := dummyGO a) (nestedExploreEquiv m k a) ω =
      restrictSmall k m a ω := by
  funext j
  exact nestedExploreEquiv_apply_inl ω j

/-- **Ordinary nested common-upper identity.**  For the actual nested
FK/FK/Bernoulli triple, the two FK coordinates have equal mass for every
region observation intersected with a separated shell stratum of their common
upper coordinate.  This is the finite free-boundary Markov identity used in
Lemma 2.1, in ordinary region-confined geometry. -/
theorem nestedOrderedTriple_good_annFirst
    {W K : Type*} [Fintype W] [Fintype K] {m k a : ℕ}
    (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS : Setoid K)
    (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo) (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    let T := transportedAmbient si ti so xo
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let L := finIndexedGraph (W ⊕ K) (k + (m + a))
      (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (W ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξB : L.BoundaryPartition := bigBoundary si ti so xo ao bo ζB
    let B : Set L.Configuration := {ω | regionOfAnn ω ∈ A}
    let C : Set T.Configuration :=
      {ρ | Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}
    let e : T.Edge ⊕ (dummyGO a).Edge ≃ L.Edge := nestedExploreEquiv m k a
    let ρO := (dummyGO a).bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)
    let cS : PMF.OrderedCoupling (L.fkPMF hq hp₁.le ξB)
        (splitLaw e (T.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)) ρO) := by
      rw [splitLaw_bernoulliProductPMF e (upperRateNN_le_one hq hp₁.le)]
      exact fkUpperOrderedCoupling
        (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
        ξB hq hp₀ hp₁
    let cΔ := fkUpperOrderedCoupling T.source T.target ξS hq hp₀ hp₁
    let t := nestedOrderedTriple (GS := L) (GD := T) (GO := dummyGO a) e cS cΔ
    t.dist.toMeasure
      ((fun z => z.1) ⁻¹' B ∩
        (fun z => z.2.2) ⁻¹' (restrictSmall k m a ⁻¹' C)) =
    t.dist.toMeasure
      ((fun z => z.2.1) ⁻¹' B ∩
        (fun z => z.2.2) ⁻¹' (restrictSmall k m a ⁻¹' C)) := by
  intro T G L ξS ξB B C e ρO cS cΔ t
  let AD : Set T.Configuration := {y | smallRegion y ∈ A}
  have hrestrict (ω : L.Configuration) :
      restrictΔ e ω = restrictSmall k m a ω := by
    funext j
    exact nestedExploreEquiv_apply_inl ω j
  have hfun : (restrictΔ e : L.Configuration → T.Configuration) =
      (restrictSmall k m a : L.Configuration → T.Configuration) := funext hrestrict
  have hC : restrictΔ e ⁻¹' C = restrictSmall k m a ⁻¹' C :=
    congrArg (fun f : L.Configuration → T.Configuration => f ⁻¹' C) hfun
  have hBA : B = restrictΔ e ⁻¹' AD := by
    ext ω
    change regionOfAnn ω ∈ A ↔ smallRegion (restrictΔ e ω) ∈ A
    rw [hrestrict]
    rfl
  have hcSdist : cS.dist = fkUpperPair
      (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
      ξB hq hp₀ hp₁ := by
    exact orderedCoupling_dist_of_eq_mp
      (splitLaw_bernoulliProductPMF e (upperRateNN_le_one hq hp₁.le))
      (fkUpperOrderedCoupling (bigPairSource si ti so xo ao bo)
        (bigPairTarget si ti so xo ao bo) ξB hq hp₀ hp₁)
  have hpairs : cS.dist.toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) =
      cΔ.dist.toMeasure (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
    have h := good_intersection_annFirstPairs si ti so xo ao bo θ ζS ζS ζB
      hconf hθ havoid hright hq hp₀ hp₁ A
    rw [hcSdist, hC]
    exact h
  have h := nestedOrderedTriple_good_of_pair_identity
    (GS := L) (GD := T) (GO := dummyGO a) e cS cΔ B AD C hBA hpairs
  change t.dist.toMeasure _ = t.dist.toMeasure _ at h
  rw [hC] at h
  exact h

/-- **Equation (9) for the ordinary confined nested split.**  The exceptional
set is the complement of the separated shell stratum, evaluated in the common
upper Bernoulli law. -/
theorem nested_annFirst_abs_sub_le
    {W K : Type*} [Fintype W] [Fintype K] {m k a : ℕ}
    (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS : Setoid K)
    (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : AddedAvoid ao bo) (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    let T := transportedAmbient si ti so xo
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let L := finIndexedGraph (W ⊕ K) (k + (m + a))
      (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (W ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξB : L.BoundaryPartition := bigBoundary si ti so xo ao bo ζB
    let B : Set L.Configuration := {ω | regionOfAnn ω ∈ A}
    let AD : Set T.Configuration := {y | smallRegion y ∈ A}
    let C : Set T.Configuration :=
      {ρ | Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}
    let e : T.Edge ⊕ (dummyGO a).Edge ≃ L.Edge := nestedExploreEquiv m k a
    let ρO := (dummyGO a).bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)
    |(L.fkPMF hq hp₁.le ξB).toMeasure.real B -
        (T.fkPMF hq hp₁.le ξS).toMeasure.real AD| ≤
      (splitLaw e (T.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)) ρO).toMeasure.real
        (restrictΔ e ⁻¹' C)ᶜ := by
  intro T G L ξS ξB B AD C e ρO
  let c0 := fkUpperOrderedCoupling
    (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
    ξB hq hp₀ hp₁
  let cS : PMF.OrderedCoupling (L.fkPMF hq hp₁.le ξB)
      (splitLaw e (T.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)) ρO) :=
    { dist := c0.dist
      map_fst := c0.map_fst
      map_snd := c0.map_snd.trans
        (splitLaw_bernoulliProductPMF (GS := L) (GD := T) (GO := dummyGO a)
          e (upperRateNN_le_one hq hp₁.le)).symm
      ordered := c0.ordered }
  let cΔ := fkUpperOrderedCoupling T.source T.target ξS hq hp₀ hp₁
  have hrestrict (ω : L.Configuration) :
      restrictΔ e ω = restrictSmall k m a ω := by
    funext j
    exact nestedExploreEquiv_apply_inl ω j
  have hfun : (restrictΔ e : L.Configuration → T.Configuration) =
      (restrictSmall k m a : L.Configuration → T.Configuration) := funext hrestrict
  have hC : restrictΔ e ⁻¹' C = restrictSmall k m a ⁻¹' C :=
    congrArg (fun f : L.Configuration → T.Configuration => f ⁻¹' C) hfun
  have hBA : B = restrictΔ e ⁻¹' AD := by
    ext ω
    change regionOfAnn ω ∈ A ↔ smallRegion (restrictΔ e ω) ∈ A
    rw [hrestrict]
    rfl
  have hcSdist : cS.dist = fkUpperPair
      (bigPairSource si ti so xo ao bo) (bigPairTarget si ti so xo ao bo)
      ξB hq hp₀ hp₁ := by
    rfl
  have hpairs : cS.dist.toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) =
      cΔ.dist.toMeasure (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
    have h := good_intersection_annFirstPairs si ti so xo ao bo θ ζS ζS ζB
      hconf hθ havoid hright hq hp₀ hp₁ A
    rw [hcSdist, hC]
    exact h
  exact nestedOrderedTriple_abs_sub_le_of_pair_identity
    (GS := L) (GD := T) (GO := dummyGO a) e cS cΔ B AD C hBA hpairs

end FK.NestedRegionExploration
