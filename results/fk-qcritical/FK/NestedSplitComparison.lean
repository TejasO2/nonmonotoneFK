import FK.NestedRegionExploration

open scoped ENNReal NNReal BigOperators Classical
open Set MeasureTheory

namespace FK.NestedSplitComparison

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.NestedCoupledGood
open FK.Exploration.RightWiredGood

variable {GS GD GO : LabelledMultigraph}

/-- Extending a pair by independent bits is invisible to events pulled back from
the smaller configuration pair. -/
theorem extendPairDist_toMeasure_restrictΔ (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μΔ ρΔ : PMF GD.Configuration} (c : PMF.OrderedCoupling μΔ ρΔ)
    (ρO : PMF GO.Configuration) (E F : Set GD.Configuration) :
    (extendPairDist e c ρO).toMeasure
        (Prod.fst ⁻¹' (restrictΔ e ⁻¹' E) ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' F)) =
      c.dist.toMeasure (Prod.fst ⁻¹' E ∩ Prod.snd ⁻¹' F) := by
  classical
  set S : Set (GS.Configuration × GS.Configuration) :=
    Prod.fst ⁻¹' (restrictΔ e ⁻¹' E) ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' F) with hS
  set EV : Set (GD.Configuration × GD.Configuration) := Prod.fst ⁻¹' E ∩ Prod.snd ⁻¹' F with hEV
  have hinner : ∀ z : GD.Configuration × GD.Configuration,
      (ρO.map (fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o)))).toMeasure S =
      if z ∈ EV then 1 else 0 := by
    intro z
    have hmf : Measurable
        (fun o : GO.Configuration => (configEquiv e (z.1, o), configEquiv e (z.2, o))) := by
      fun_prop
    have hmS : MeasurableSet S := MeasurableSet.of_discrete
    rw [PMF.toMeasure_map_apply (p := ρO) (f := fun o : GO.Configuration =>
      (configEquiv e (z.1, o), configEquiv e (z.2, o))) (s := S) hmf hmS]
    · have hset : ∀ o : GO.Configuration,
          ((fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))) o ∈ S) ↔ z ∈ EV := by
        intro o
        simp only [hS, hEV, mem_inter_iff, mem_preimage, mem_prod, restrictΔ_configEquiv]
      by_cases hz : z ∈ EV
      · have huniv : (fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))) ⁻¹' S = univ :=
          Set.eq_univ_of_forall (fun o => (hset o).mpr hz)
        rw [huniv, if_pos hz]
        simp
      · have hempty : (fun o => (configEquiv e (z.1, o), configEquiv e (z.2, o))) ⁻¹' S = ∅ :=
          Set.eq_empty_of_forall_notMem (fun o h => hz ((hset o).mp h))
        rw [hempty, if_neg hz]
        simp
  rw [extendPairDist, PMF.toMeasure_bind_apply _ _ _ MeasurableSet.of_discrete]
  rw [PMF.toMeasure_apply_eq_tsum (p := c.dist) (s := EV)]
  apply tsum_congr
  intro z
  rw [hinner z]
  by_cases hz : z ∈ EV
  · rw [if_pos hz, mul_one, indicator_of_mem hz]
  · rw [if_neg hz, mul_zero, indicator_of_notMem hz]


end FK.NestedSplitComparison

namespace FK.NestedSplitComparison

universe uW uK

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary
open FK.Exploration.Sequential FK.Exploration.StoppedInterior
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.Exploration.NestedCoupledGood FK.Exploration.MaximalStrata
open FK.Exploration.RightWiredGood FK.Exploration.TwoSidedInterior FK.NestedRegionExploration

variable {W : Type uW} {K : Type uK} [Fintype W] [Fintype K]

/-- The larger graph in exploration order. -/
noncomputable abbrev bigG {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) : LabelledMultigraph :=
  finIndexedGraph (W ⊕ K) (k + (m + a)) (bigPairSource si ti so xo ao bo)
    (bigPairTarget si ti so xo ao bo)

/-- The smaller graph in exterior-first order. -/
noncomputable abbrev smallG {m k : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) : LabelledMultigraph := transportedAmbient si ti so xo

/-- The boundary setoid of the larger exploration-order graph. -/
noncomputable abbrev xiB {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζB : Setoid (W ⊕ K)) :
    (bigG si ti so xo ao bo).BoundaryPartition :=
  bigBoundary si ti so xo ao bo ζB

/-- The two-sided boundary setoid of the smaller graph. -/
noncomputable abbrev xiS {m k : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (θ : Setoid W) (ζS : Setoid K) :
    (smallG si ti so xo).BoundaryPartition :=
  (ambientOfSum (splitSource si so) (splitTarget ti xo)).transportBoundaryOf
    (Equiv.refl (W ⊕ K)) (twoSidedBoundary si ti so xo θ ζS)

/-- A one-vertex graph carrying `a` added labels, with pinned universes. -/
def dG (a : ℕ) : LabelledMultigraph.{0, 0} where
  Vertex := PUnit
  Edge := Fin a
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit

/-- The exploration-order graph's Bernoulli product splits along the
shell/region/added decomposition. -/
lemma splitLaw_bernoulli_big {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) {r : NNReal} (hr : r ≤ 1) :
    splitLaw (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo) (GO := dG a)
        (nestedExploreEquiv m k a) ((smallG si ti so xo).bernoulliProductPMF hr)
        ((dG a).bernoulliProductPMF hr) =
      (bigG si ti so xo ao bo).bernoulliProductPMF hr :=
  @splitLaw_bernoulliProductPMF.{max uW uK, 0, max uW uK, 0, 0, 0}
    (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo) (GO := dG a)
    (e := nestedExploreEquiv m k a) (p := r) (hp := hr)

/-- The concrete shell-plus-region restriction is the exploration-order
restriction of the canonical nested edge equivalence. -/
lemma restrictSmall_eq_restrictDelta {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) :
    (restrictSmall k m a : (Fin (k + (m + a)) → Bool) → Fin (k + m) → Bool) =
      (fun z => restrictΔ (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) z) := by
  funext z j
  show z (nestedExploreEquiv m k a (Sum.inl j)) = z ⟨j.1, by omega⟩
  rw [nestedExploreEquiv_inl]


/-! ## The finite lemma 2.1 comparison at equation (9) -/

/-- The region coordinates of the exploration order equal the region coordinates
of the shell-plus-region restriction. -/
lemma regionOfAnn_eq_smallRegion (m k a : ℕ) (z : Fin (k + (m + a)) → Bool) :
    regionOfAnn z = smallRegion (restrictSmall k m a z) := by
  funext j
  show z ⟨k + j.1, by omega⟩ = z ⟨k + j.1, by omega⟩
  rfl

/-- **The shell-first finite comparison.**  For a shell-first split of a larger
finite graph over a smaller one, with an arbitrary region event, the difference
of the two FK laws on that event is bounded by the probability that the
dominating Bernoulli configuration is *not* separated on the shell. This error
is a fixed shell-touching event in the ordinary metric-box instantiation, not
the vanishing arm event of the paper's equation (9). -/
theorem split_equation_nine_region
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS ζL : Setoid K) (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : FK.RegionConfinement.ConfinedStrata.AddedAvoid ao bo)
    (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    |(bigPairLaw si ti so xo ao bo ζB hq hp₁).toMeasure.real
          {ω : Fin (k + (m + a)) → Bool | regionOfAnn ω ∈ A} -
        ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS)).toMeasure.real
          {ρ : Fin (k + m) → Bool | smallRegion ρ ∈ A}| ≤
      ((bigG si ti so xo ao bo).bernoulliProductPMF
        (upperRateNN_le_one hq hp₁.le)).toMeasure.real
        {z : Fin (k + (m + a)) → Bool |
          restrictSmall k m a z ∈
            {ρ : Fin (k + m) → Bool |
              Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}}ᶜ := by
  classical
  let hr := upperRateNN_le_one hq hp₁.le
  let μS : PMF (Fin (k + m) → Bool) :=
    (smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS)
  let smallBern : PMF (Fin (k + m) → Bool) := (smallG si ti so xo).bernoulliProductPMF hr
  let ρO : PMF (Fin a → Bool) := (dG a).bernoulliProductPMF hr
  let ν : PMF (Fin (k + (m + a)) → Bool) := (bigG si ti so xo ao bo).bernoulliProductPMF hr
  let B : Set (Fin (k + (m + a)) → Bool) := {ω | regionOfAnn ω ∈ A}
  let AD : Set (Fin (k + m) → Bool) := {ρ | smallRegion ρ ∈ A}
  let C : Set (Fin (k + m) → Bool) :=
    {ρ | Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}
  let Cbig : Set (Fin (k + (m + a)) → Bool) := {z | restrictSmall k m a z ∈ C}
  -- the smaller ordered FK/Bernoulli pair
  let cS : PMF.OrderedCoupling μS smallBern :=
    fkUpperOrderedCoupling (V := W ⊕ K) (smallG si ti so xo).source
      (smallG si ti so xo).target (xiS si ti so xo θ ζS) hq hp₀ hp₁
  -- splitting of the dominating Bernoulli product
  have hsplit : splitLaw (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
      (GO := dG a) (nestedExploreEquiv m k a) smallBern ρO = ν :=
    splitLaw_bernoulli_big (si := si) (ti := ti) (so := so) (xo := xo) (ao := ao) (bo := bo) hr
  -- the extended smaller pair, dominating upper marginal
  let SBig : PMF (Fin (k + (m + a)) → Bool) :=
    splitLaw (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo) (GO := dG a)
      (nestedExploreEquiv m k a) μS ρO
  let cE : PMF.Coupling SBig ν :=
    { dist := (extendOrderedCoupling (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) cS ρO).dist
      map_fst := (extendOrderedCoupling (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) cS ρO).map_fst
      map_snd := ((extendOrderedCoupling (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) cS ρO).map_snd).trans hsplit }
  -- the larger ordered pair
  let cB : PMF.OrderedCoupling (bigPairLaw si ti so xo ao bo ζB hq hp₁) ν :=
    fkUpperOrderedCoupling (V := W ⊕ K) (bigPairSource si ti so xo ao bo)
      (bigPairTarget si ti so xo ao bo) (bigBoundary si ti so xo ao bo ζB) hq hp₀ hp₁
  -- event conversions
  let ADbig : Set (Fin (k + (m + a)) → Bool) := {z | restrictSmall k m a z ∈ AD}
  have hB : (restrictSmall k m a : (Fin (k + (m + a)) → Bool) → Fin (k + m) → Bool) ⁻¹' AD = B := by
    ext z
    show (smallRegion (restrictSmall k m a z) ∈ A) ↔ (regionOfAnn z ∈ A)
    rw [regionOfAnn_eq_smallRegion m k a z]
  have hADbig : (ADbig : Set (Fin (k + (m + a)) → Bool)) =
      (restrictSmall k m a ⁻¹' AD) := rfl
  -- the exploration good intersection
  have hgood := good_intersection_annFirstPairs si ti so xo ao bo θ ζS ζL ζB hconf hθ
    havoid hright hq hp₀ hp₁ A
  -- equation (9) input
  have hpair : cB.dist.toMeasure (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' Cbig) =
      cE.dist.toMeasure (Prod.fst ⁻¹' ADbig ∩ Prod.snd ⁻¹' Cbig) := by
    have hL : cB.dist.toMeasure (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' Cbig) =
        (fkUpperPair (V := W ⊕ K) (bigPairSource si ti so xo ao bo)
          (bigPairTarget si ti so xo ao bo) (bigBoundary si ti so xo ao bo ζB)
          hq hp₀ hp₁).toMeasure
          (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictSmall k m a ⁻¹' C)) := rfl
    have hR : cE.dist.toMeasure (Prod.fst ⁻¹' ADbig ∩ Prod.snd ⁻¹' Cbig) =
        (fkUpperPair (V := W ⊕ K) (smallG si ti so xo).source (smallG si ti so xo).target
          (xiS si ti so xo θ ζS) hq hp₀ hp₁).toMeasure (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
      rw [show cE.dist = (extendOrderedCoupling (GS := bigG si ti so xo ao bo)
        (GD := smallG si ti so xo) (GO := dG a) (nestedExploreEquiv m k a) cS ρO).dist
        from rfl]
      rw [show (Cbig : Set (Fin (k + (m + a)) → Bool)) =
        ((fun z => restrictΔ (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
          (GO := dG a) (nestedExploreEquiv m k a) z) ⁻¹' C) from by
        dsimp only [Cbig]
        rw [restrictSmall_eq_restrictDelta si ti so xo ao bo]
        rfl]
      rw [show (ADbig : Set (Fin (k + (m + a)) → Bool)) =
        ((fun z => restrictΔ (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
          (GO := dG a) (nestedExploreEquiv m k a) z) ⁻¹' AD) from by
        dsimp only [ADbig]
        rw [restrictSmall_eq_restrictDelta si ti so xo ao bo]
        rfl]
      exact @extendPairDist_toMeasure_restrictΔ (bigG si ti so xo ao bo)
        (smallG si ti so xo) (dG a) (nestedExploreEquiv m k a) μS smallBern cS ρO AD C
    rw [hL, hR]
    exact hgood
  -- equation (9)
  have hnine := PMF.Coupling.equation_nine_abs_bound_of_pair_eq (α := Fin (k + (m + a)) → Bool)
    (β := Fin (k + (m + a)) → Bool) (γ := Fin (k + (m + a)) → Bool) cB.toCoupling cE
    (A := B) (B := ADbig) (C := Cbig) MeasurableSet.of_discrete MeasurableSet.of_discrete
    MeasurableSet.of_discrete hpair
  -- transfer the extended law's mass back to the smaller FK law
  have hmap : (SBig).map (restrictSmall k m a) = μS := by
    rw [restrictSmall_eq_restrictDelta si ti so xo ao bo]
    exact map_restrictΔ_splitLaw (GS := bigG si ti so xo ao bo)
      (GD := smallG si ti so xo) (GO := dG a) (nestedExploreEquiv m k a) μS ρO
  have hmass0 : (SBig.map (restrictSmall k m a)).toMeasure AD = SBig.toMeasure ADbig := by
    rw [PMF.toMeasure_map_apply (p := SBig) (f := restrictSmall k m a) (s := AD)
      (by fun_prop) MeasurableSet.of_discrete]
    rfl
  have hmass : (SBig.map (restrictSmall k m a)).toMeasure.real AD = SBig.toMeasure.real ADbig := by
    exact congrArg ENNReal.toReal hmass0
  rw [← hmass, hmap] at hnine
  exact hnine

/-! ## The ordered triple of Lemma 2.1 and its marginals -/

/-- Composing the second-coordinate projection with the shell-plus-region
restriction. -/
lemma map_snd_restrict {m k a : ℕ}
    (p : PMF ((Fin (k + (m + a)) → Bool) × (Fin (k + (m + a)) → Bool) ×
      (Fin (k + (m + a)) → Bool))) :
    p.map (fun z => restrictSmall k m a z.2.1) =
      (p.map (fun z => z.2.1)).map (restrictSmall k m a) := by
  rw [PMF.map_comp]
  rfl



/-- The smaller FK law extended by independent added labels, at the larger
configuration type. -/
noncomputable def SBigLaw
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS : Setoid K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF (Fin (k + (m + a)) → Bool) :=
  splitLaw (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo) (GO := dG a)
    (nestedExploreEquiv m k a)
    ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS))
    ((dG a).bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))

/-- **Lemma 2.1 triple.**  The exploration-order triple with the larger FK law,
the extended smaller FK law and the dominating Bernoulli configuration, whose
first and second coordinates are pointwise below the third. -/
noncomputable def leibnizTriple
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS : Setoid K) (ζB : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.RelativeTripleCoupling (bigPairLaw si ti so xo ao bo ζB hq hp₁)
      (SBigLaw si ti so xo ao bo θ ζS hq hp₀ hp₁)
      ((bigG si ti so xo ao bo).bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))
      (fun a c => a ≤ c) (fun b c => b ≤ c) := by
  let hr := upperRateNN_le_one hq hp₁.le
  let cS : PMF.OrderedCoupling
      ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS))
      ((smallG si ti so xo).bernoulliProductPMF hr) :=
    fkUpperOrderedCoupling (V := W ⊕ K) (smallG si ti so xo).source
      (smallG si ti so xo).target (xiS si ti so xo θ ζS) hq hp₀ hp₁
  have hsplit := splitLaw_bernoulli_big (si := si) (ti := ti) (so := so) (xo := xo)
    (ao := ao) (bo := bo) hr
  let cE : PMF.Coupling (SBigLaw si ti so xo ao bo θ ζS hq hp₀ hp₁)
      ((bigG si ti so xo ao bo).bernoulliProductPMF hr) :=
    { dist := (extendOrderedCoupling (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) cS ((dG a).bernoulliProductPMF hr)).dist
      map_fst := (extendOrderedCoupling (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) cS ((dG a).bernoulliProductPMF hr)).map_fst
      map_snd := ((extendOrderedCoupling (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo)
        (GO := dG a) (nestedExploreEquiv m k a) cS
        ((dG a).bernoulliProductPMF hr)).map_snd).trans hsplit }
  let cB : PMF.OrderedCoupling (bigPairLaw si ti so xo ao bo ζB hq hp₁)
      ((bigG si ti so xo ao bo).bernoulliProductPMF hr) :=
    fkUpperOrderedCoupling (V := W ⊕ K) (bigPairSource si ti so xo ao bo)
      (bigPairTarget si ti so xo ao bo) (bigBoundary si ti so xo ao bo ζB) hq hp₀ hp₁
  exact PMF.Coupling.glueRelative cB.toCoupling cE (fun a c => a ≤ c) (fun b c => b ≤ c)
    (fun x hx => cB.ordered x hx)
    (fun x hx => (extendPairDist_support (GS := bigG si ti so xo ao bo)
      (GD := smallG si ti so xo) (GO := dG a) (nestedExploreEquiv m k a) cS
      ((dG a).bernoulliProductPMF hr) hx).1)

/-! ## The ordered triple of Lemma 2.1 and its marginals -/

/-- The second coordinate of the Lemma 2.1 triple, restricted to the smaller
box's labels, is exactly the smaller FK law. -/
theorem leibnizTriple_snd_restrict
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS : Setoid K) (ζB : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).dist.map
        (fun z => restrictSmall k m a z.2.1) =
      (smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS) := by
  show ((leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).dist :
      PMF ((Fin (k + (m + a)) → Bool) × (Fin (k + (m + a)) → Bool) ×
        (Fin (k + (m + a)) → Bool))).map (fun z => restrictSmall k m a z.2.1) =
    (smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS)
  have key : ∀ (p : PMF ((Fin (k + (m + a)) → Bool) × (Fin (k + (m + a)) → Bool) ×
      (Fin (k + (m + a)) → Bool))),
      p.map (fun z => restrictSmall k m a z.2.1) =
        (p.map (fun z => z.2.1)).map (restrictSmall k m a) := by
    intro p
    rw [PMF.map_comp]
    rfl
  have hmap : (leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).dist.map
      (fun z : (Fin (k + (m + a)) → Bool) × (Fin (k + (m + a)) → Bool) ×
        (Fin (k + (m + a)) → Bool) => z.2.1) =
      SBigLaw si ti so xo ao bo θ ζS hq hp₀ hp₁ :=
    (leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).map_snd
  have step1 : (leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).dist.map
        (fun z => restrictSmall k m a z.2.1) =
      ((leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).dist.map
          (fun z => z.2.1)).map (restrictSmall k m a) := key _
  refine Eq.trans step1 ?_
  refine Eq.trans (congrArg (fun q => PMF.map (restrictSmall k m a) q) hmap) ?_
  show (splitLaw (GS := bigG si ti so xo ao bo) (GD := smallG si ti so xo) (GO := dG a)
    (nestedExploreEquiv m k a)
    ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS))
    ((dG a).bernoulliProductPMF (upperRateNN_le_one hq hp₁.le))).map
      (restrictSmall k m a) = _
  rw [restrictSmall_eq_restrictDelta si ti so xo ao bo]
  exact map_restrictΔ_splitLaw (GS := bigG si ti so xo ao bo)
    (GD := smallG si ti so xo) (GO := dG a) (nestedExploreEquiv m k a) _ _

/-- Both FK coordinates of the Lemma 2.1 triple stay below the dominating
Bernoulli configuration. -/
theorem leibnizTriple_ordered
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS : Setoid K) (ζB : Setoid (W ⊕ K))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    {z : (Fin (k + (m + a)) → Bool) × (Fin (k + (m + a)) → Bool) ×
      (Fin (k + (m + a)) → Bool)}
    (hz : z ∈ (leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).dist.support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 :=
  ⟨(leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).rel_fst z hz,
    (leibnizTriple si ti so xo ao bo θ ζS ζB hq hp₀ hp₁).rel_snd z hz⟩

/-- The preceding shell-first error bound expressed via the ordered triple. -/
theorem leibnizTriple_equation_nine
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS ζL : Setoid K) (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : FK.RegionConfinement.ConfinedStrata.AddedAvoid ao bo)
    (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    |(bigPairLaw si ti so xo ao bo ζB hq hp₁).toMeasure.real
          {ω : Fin (k + (m + a)) → Bool | regionOfAnn ω ∈ A} -
        ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS)).toMeasure.real
          {ρ : Fin (k + m) → Bool | smallRegion ρ ∈ A}| ≤
      ((bigG si ti so xo ao bo).bernoulliProductPMF
        (upperRateNN_le_one hq hp₁.le)).toMeasure.real
        {z : Fin (k + (m + a)) → Bool |
          restrictSmall k m a z ∈
            {ρ : Fin (k + m) → Bool |
              Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}}ᶜ :=
  split_equation_nine_region si ti so xo ao bo θ ζS ζL ζB hconf hθ havoid hright hq hp₀ hp₁ A

/-! ## Paper-shaped corollaries -/

/-- **Equation (9) with a smaller error event.**  If the domination event `E`
contains the shell-separation failure, the same bound holds with `E`. No
inclusion in a far-connection/arm event is asserted or proved. -/
theorem split_equation_nine_region_of_subset
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (θ : Setoid W) (ζS ζL : Setoid K) (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (havoid : FK.RegionConfinement.ConfinedStrata.AddedAvoid ao bo)
    (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) (E : Set (Fin (k + (m + a)) → Bool))
    (hE : {z : Fin (k + (m + a)) → Bool |
        restrictSmall k m a z ∈
          {ρ : Fin (k + m) → Bool |
            Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}}ᶜ ⊆ E) :
    |(bigPairLaw si ti so xo ao bo ζB hq hp₁).toMeasure.real
          {ω : Fin (k + (m + a)) → Bool | regionOfAnn ω ∈ A} -
        ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo θ ζS)).toMeasure.real
          {ρ : Fin (k + m) → Bool | smallRegion ρ ∈ A}| ≤
      ((bigG si ti so xo ao bo).bernoulliProductPMF
        (upperRateNN_le_one hq hp₁.le)).toMeasure.real E := by
  refine (split_equation_nine_region si ti so xo ao bo θ ζS ζL ζB hconf hθ havoid hright
    hq hp₀ hp₁ A).trans ?_
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hE)

/-- **Equation (9) for a free region.**  The paper's Lemma 2.1 has free boundary
inside the exploration region, which is the `θ = ⊥` case. -/
theorem split_equation_nine_region_free
    {m k a : ℕ} (si : Fin m → W) (ti : Fin m → W) (so xo : Fin k → W ⊕ K)
    (ao bo : Fin a → W ⊕ K) (ζS ζL : Setoid K) (ζB : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζB.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζB.r (Sum.inl c) (Sum.inl c') ↔ c = c')
    (havoid : FK.RegionConfinement.ConfinedStrata.AddedAvoid ao bo)
    (hright : ExteriorHasRight so xo)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (Fin m → Bool)) :
    |(bigPairLaw si ti so xo ao bo ζB hq hp₁).toMeasure.real
          {ω : Fin (k + (m + a)) → Bool | regionOfAnn ω ∈ A} -
        ((smallG si ti so xo).fkPMF hq hp₁.le (xiS si ti so xo (⊥ : Setoid W) ζS)).toMeasure.real
          {ρ : Fin (k + m) → Bool | smallRegion ρ ∈ A}| ≤
      ((bigG si ti so xo ao bo).bernoulliProductPMF
        (upperRateNN_le_one hq hp₁.le)).toMeasure.real
        {z : Fin (k + (m + a)) → Bool |
          restrictSmall k m a z ∈
            {ρ : Fin (k + m) → Bool |
              Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ))}}ᶜ :=
  split_equation_nine_region si ti so xo ao bo (⊥ : Setoid W) ζS ζL ζB hconf
    (fun c c' => by rw [hθ]; rfl) havoid hright hq hp₀ hp₁ A

end FK.NestedSplitComparison


#print axioms FK.NestedSplitComparison.split_equation_nine_region
#print axioms FK.NestedSplitComparison.splitLaw_bernoulli_big
#print axioms FK.NestedSplitComparison.restrictSmall_eq_restrictDelta
#print axioms FK.NestedSplitComparison.extendPairDist_toMeasure_restrictΔ
#print axioms FK.NestedSplitComparison.regionOfAnn_eq_smallRegion

#print axioms FK.NestedSplitComparison.leibnizTriple
#print axioms FK.NestedSplitComparison.leibnizTriple_snd_restrict
#print axioms FK.NestedSplitComparison.leibnizTriple_ordered
#print axioms FK.NestedSplitComparison.leibnizTriple_equation_nine
#print axioms FK.NestedSplitComparison.SBigLaw

#print axioms FK.NestedSplitComparison.split_equation_nine_region_of_subset
#print axioms FK.NestedSplitComparison.split_equation_nine_region_free
