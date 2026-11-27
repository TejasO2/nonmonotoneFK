import FK.IndependentProductFilter

/-! # The small FK/free-region law after a stopped nested product history -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling FK.FinitePlane FK.RegionSeal

/-- The small exterior configuration recorded by a joined partial history. -/
noncomputable def smallHistoryExterior {G H : LabelledMultigraph}
    (U : Set G.Vertex) [DecidablePred (· ∈ U)] (h : Assignment (G.Edge ⊕ H.Edge)) :
    RegionSeal.External G U → Bool :=
  fun o => decodeOption h (Sum.inl o.1)

lemma leftPartial_fiber_eq_smallExterior {G H : LabelledMultigraph}
    (U : Set G.Vertex) [DecidablePred (· ∈ U)] (h : Assignment (G.Edge ⊕ H.Edge))
    (hint : ∀ i : RegionSeal.Internal G U, h (Sum.inl i.1) = none)
    (hext : ∀ o : RegionSeal.External G U, h (Sum.inl o.1) ≠ none) :
    Fiber (leftPartial h) = extFiber G U (smallHistoryExterior U h) := by
  ext ω
  constructor
  · intro hω
    funext o
    have hh := hext o
    cases hv : h (Sum.inl o.1) with
    | none => exact (hh hv).elim
    | some b =>
        have hb := hω o.1 b hv
        change ω o.1 = decodeOption h (Sum.inl o.1)
        rw [hb]
        simp [decodeOption, hv]
  · intro hω a b hb
    change h (Sum.inl a) = some b at hb
    by_cases hi : IsInternal G U a
    · have hn := hint ⟨a, hi⟩
      rw [hn] at hb
      contradiction
    · have heq : restrictO G U ω = smallHistoryExterior U h := hω
      have hv := congrFun heq ⟨a, hi⟩
      change ω a = b
      change ω a = decodeOption h (Sum.inl a) at hv
      rw [hv]
      simp [decodeOption, hb]

/-- A stopped joined history whose small coordinates form a sealed exterior
fibre has exactly the small free-region FK law on those interior coordinates. -/
theorem cond_productJoinLaw_map_small_region {G H : LabelledMultigraph}
    (τ : G.BoundaryPartition) (ξO : H.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (h : Assignment (G.Edge ⊕ H.Edge))
    (U : Set G.Vertex) [DecidablePred (· ∈ U)]
    (hint : ∀ i : RegionSeal.Internal G U, h (Sum.inl i.1) = none)
    (hext : ∀ o : RegionSeal.External G U, h (Sum.inl o.1) ≠ none)
    (hwire : ∀ v : G.Vertex, v ∈ U → ∀ w : G.Vertex, τ.r v w → v = w)
    (hseal : ∀ o : RegionSeal.External G U,
      decodeOption h (Sum.inl o.1) = true → G.source o.1 ∉ U ∧ G.target o.1 ∉ U) :
    (cond (productJoinLaw (G.fkPMF hq hp₁.le τ)
      (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
      (productJoinLaw_ne_zero
        (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ τ ω)
        (bernoulliProductPMF_ne_zero H ξO (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁))) h).map
        (fun ω => restrictI G U (ω ∘ Sum.inl)) =
      (regionGraph G U).fkPMF hq hp₁.le (regionGraph G U).freeBoundary := by
  have hμ : ∀ ω, G.fkPMF hq hp₁.le τ ω ≠ 0 :=
    fun ω => fkPMF_ne_zero G hq hp₀ hp₁ τ ω
  have hν : ∀ ω, H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le ω ≠ 0 :=
    bernoulliProductPMF_ne_zero H ξO (upperRateNN_pos hp₀)
      (upperRateNN_lt_one hq hp₀ hp₁)
  have hfib : Fiber (leftPartial h) = extFiber G U (smallHistoryExterior U h) :=
    leftPartial_fiber_eq_smallExterior U h hint hext
  have hsupp : ∃ ω ∈ extFiber G U (smallHistoryExterior U h),
      ω ∈ (G.fkPMF hq hp₁.le τ).support := by
    rw [← hfib]
    exact fiber_support_of_positive _ hμ _
  have hcond : cond (G.fkPMF hq hp₁.le τ) hμ (leftPartial h) =
      (G.fkPMF hq hp₁.le τ).filter (extFiber G U (smallHistoryExterior U h)) hsupp := by
    exact filter_congr_set _ hfib (fiber_support_of_positive _ hμ _) hsupp
  have hmap := cond_productJoinLaw_map_left hμ hν h
  have hcomp : (cond (productJoinLaw (G.fkPMF hq hp₁.le τ)
      (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
      (productJoinLaw_ne_zero hμ hν) h).map
      (fun ω => restrictI G U (ω ∘ Sum.inl)) =
      ((cond (productJoinLaw (G.fkPMF hq hp₁.le τ)
        (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
        (productJoinLaw_ne_zero hμ hν) h).map (fun ω => ω ∘ Sum.inl)).map
        (restrictI G U) :=
    (PMF.map_comp (fun ω : G.Edge ⊕ H.Edge → Bool => ω ∘ Sum.inl)
      (cond (productJoinLaw (G.fkPMF hq hp₁.le τ)
        (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
        (productJoinLaw_ne_zero hμ hν) h) (restrictI G U)).symm
  have htail := (map_restrictI_filter_fkPMF U τ (smallHistoryExterior U h) hq hp₀ hp₁).trans
    (fiberPMF_eq_region G U τ (smallHistoryExterior U h) hwire hseal hq hp₀ hp₁)
  have hleft : ((cond (productJoinLaw (G.fkPMF hq hp₁.le τ)
      (H.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
      (productJoinLaw_ne_zero hμ hν) h).map (fun ω => ω ∘ Sum.inl)).map
      (restrictI G U) =
      ((G.fkPMF hq hp₁.le τ).filter (extFiber G U (smallHistoryExterior U h))
        hsupp).map (restrictI G U) :=
    (congrArg (PMF.map (restrictI G U)) hmap).trans
      (congrArg (PMF.map (restrictI G U)) hcond)
  exact hcomp.trans (hleft.trans htail)

end FK.Adaptive
