import FK.TransportBoundary

/-!
# Exterior-prefix continuations with right-supported ambient wiring

The canonical-prefix filter theorem is combined with arbitrary-boundary graph
transport and the right-wired free-interior Markov theorem.  The lower laws
can now differ through arbitrary setoids on the right/exterior vertices.
-/

namespace FK.Exploration.WiredStoppedInterior

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Exact free-interior continuation for any right-supported ambient boundary
setoid after an exterior-first exposed history. -/
theorem extendLower_exteriorHistory_eq_free_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ρ : Fin m ⊕ Fin k → Bool)
    (hsep : Separated si ti so xo (exteriorConfig ρ)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti so xo ζ)
    let μ := T.fkPMF hq hp₁.le ξ
    (extendLower (canonicalNext μ (fkPMF_ne_zero T hq hp₀ hp₁ ξ))
      (exteriorHistory ρ) m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let T := transportedAmbient si ti so xo
  let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
    (rightWiredBoundary si ti so xo ζ)
  let e : (Fin (k + m) → Bool) ≃ (Fin m ⊕ Fin k → Bool) :=
    toAmbientConfig si ti so xo
  let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ
  have hμ := fkPMF_ne_zero T hq hp₀ hp₁ ξ
  have hlen : (exteriorHistory ρ).length + m = k + m := by
    simp [exteriorHistory]
  dsimp only
  rw [extendLower_canonicalNext μ hμ (exteriorHistory ρ) m hlen]
  let P := prefixCylinder (n := k + m) (exteriorHistory ρ)
  have hP : P = e ⁻¹' exteriorFiber (exteriorConfig ρ) := by
    ext y
    exact exteriorHistory_prefix_iff si ti so xo ρ y
  have htransport : μ.map e = G.fkPMF hq hp₁.le (rightWiredBoundary si ti so xo ζ) := by
    exact G.map_transport_fkPMF (Equiv.refl (U ⊕ K)) exteriorFirst
      (rightWiredBoundary si ti so xo ζ) hq hp₀ hp₁
  have hBactual : ∃ a ∈ exteriorFiber (exteriorConfig ρ),
      a ∈ (G.fkPMF hq hp₁.le (rightWiredBoundary si ti so xo ζ)).support :=
    exteriorFiber_support_rightWired si ti so xo hq hp₀ hp₁ ζ (exteriorConfig ρ)
  have hB : ∃ a ∈ exteriorFiber (exteriorConfig ρ), a ∈ (μ.map e).support := by
    rw [htransport]
    exact hBactual
  have hfilter : (μ.filter P
      (prefixCylinder_support_of_positive μ hμ (exteriorHistory ρ) (by omega))).map e =
      (G.fkPMF hq hp₁.le (rightWiredBoundary si ti so xo ζ)).filter
        (exteriorFiber (exteriorConfig ρ)) hBactual := by
    simp only [hP]
    have hA : ∃ a ∈ e ⁻¹' exteriorFiber (exteriorConfig ρ), a ∈ μ.support := by
      rw [← hP]
      exact prefixCylinder_support_of_positive μ hμ (exteriorHistory ρ) (by omega)
    have h0 := map_filter_equiv e μ (exteriorFiber (exteriorConfig ρ)) hA hB
    simp only [htransport] at h0
    with_unfolding_all exact h0
  rw [PMF.map_comp]
  have hc : (fun y => interiorConfig ((toAmbientConfig si ti so xo)
      (toConfig (k + m) y))) ∘ List.ofFn = interiorConfig ∘ e := by
    funext ω
    change interiorConfig (e (toConfig (k + m) (List.ofFn ω))) = interiorConfig (e ω)
    rw [toConfig_ofFn]
  rw [hc, ← PMF.map_comp, hfilter]
  rw [← filter_ambient_fkPMF_eq_map_glue_region_free_rightWired si ti so xo
    hq hp₀ hp₁ ζ (exteriorConfig ρ) hsep]
  refine (PMF.map_comp _ _ _).trans ?_
  have hid : (interiorConfig (I := Fin m) (O := Fin k)) ∘
      (fun (ω : Fin m → Bool) => glue (I := Fin m) (O := Fin k) ω (exteriorConfig ρ)) = id := by
    funext ω
    rfl
  rw [hid]
  with_unfolding_all exact PMF.map_id _

/-- On an upper maximal stratum, every pointwise-lower exterior history also
has the exact free-interior continuation under either right boundary setoid. -/
theorem extendLower_exteriorHistory_eq_free_rightWired_of_le_outerRegion
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ρ π : Fin m ⊕ Fin k → Bool) (hπρ : π ≤ ρ)
    (hright : ExteriorHasRight so xo)
    (hR : ρ ∈ maximalSplitStratum si ti so xo) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti so xo ζ)
    let μ := T.fkPMF hq hp₁.le ξ
    (extendLower (canonicalNext μ (fkPMF_ne_zero T hq hp₀ hp₁ ξ))
      (exteriorHistory π) m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) =
      (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  apply extendLower_exteriorHistory_eq_free_rightWired si ti so xo hq hp₀ hp₁ ζ π
  exact separated_of_le_of_outerRegion si ti so xo ρ π hπρ hright hR

end FK.Exploration.WiredStoppedInterior
