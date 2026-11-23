import FK.FreeInterior
import FK.ExplorationGeometry

/-!
# Canonical exploration strata have free interior FK laws

This file joins canonical outer exploration to the separated split-graph
Markov theorem.  On a stratum where the outer region is the right summand,
the frontier-closedness theorem proves the nonincidence condition required by
`FreeInterior`.  Thus the ambient law conditioned on that exterior fiber is
literally the actual free interior FK law.
-/

namespace FK.FinitePlane.FreeInterior

open scoped ENNReal BigOperators Classical
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.Exploration

variable {U K I O : Type*} [Fintype U] [Fintype K] [Fintype I] [Fintype O]

/-- The exterior restriction of a configuration on a sum of labels. -/
def exteriorConfig (ρ : I ⊕ O → Bool) : O → Bool := ρ ∘ Sum.inr

/-- The interior restriction of a configuration on a sum of labels. -/
def interiorConfig (ρ : I ⊕ O → Bool) : I → Bool := ρ ∘ Sum.inl

/-- No exterior edge misses the right vertex summand.  Internal edges have
both endpoints on the left by `splitSource`/`splitTarget`, so an exterior edge
failing this condition would be an interior label. -/
def ExteriorHasRight (so xo : O → U ⊕ K) : Prop :=
  ∀ o, so o ∈ Set.range (Sum.inr : K → U ⊕ K) ∨
    xo o ∈ Set.range (Sum.inr : K → U ⊕ K)

/-- Canonical exploration proves the separated nonincidence condition on the
stratum whose outer region is exactly the right vertex summand. -/
theorem separated_of_outerRegion_eq_right
    (si : I → U) (ti : I → U) (so xo : O → U ⊕ K) (ρ : I ⊕ O → Bool)
    (hright : ExteriorHasRight so xo)
    (hR : (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr) :
    Separated si ti so xo (exteriorConfig ρ) := by
  let G : LabelledMultigraph := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let B : Set (U ⊕ K) := Set.range Sum.inr
  have hRG : G.outerRegion G.freeBoundary B ρ = B := hR
  have hinterior : G.interior G.freeBoundary B ρ = Set.range Sum.inl := by
    change (G.outerRegion G.freeBoundary B ρ)ᶜ = Set.range Sum.inl
    rw [hRG]
    ext x
    change x ∈ (Set.range (Sum.inr : K → U ⊕ K))ᶜ ↔
      x ∈ Set.range (Sum.inl : U → U ⊕ K)
    cases x <;> simp
  intro o ho
  have hopen : ρ (Sum.inr o) = true := ho
  have hor : G.source (Sum.inr o) ∈ G.outerRegion G.freeBoundary B ρ ∨
      G.target (Sum.inr o) ∈ G.outerRegion G.freeBoundary B ρ := by
    rw [hRG]
    exact hright o
  have he : ¬ (G.source (Sum.inr o) ∈ G.interior G.freeBoundary B ρ ∧
      G.target (Sum.inr o) ∈ G.interior G.freeBoundary B ρ) := by
    rintro ⟨hs, ht⟩
    rcases hor with hs' | ht'
    · exact hs hs'
    · exact ht ht'
  have hc := G.source_and_target_not_mem_interior_of_open G.freeBoundary B ρ hopen he
  constructor
  · change so o ∉ Set.range Sum.inl
    rw [← hinterior]
    exact hc.1
  · change xo o ∉ Set.range Sum.inl
    rw [← hinterior]
    exact hc.2

/-- On the canonical maximal-cutset stratum, the exact exterior-fiber
conditional law is the pushforward of the actual free interior-region FK law.
This discharges both the free-boundary and Markov inputs simultaneously. -/
theorem filter_ambient_fkPMF_eq_map_glue_free_of_outerRegion
    (si : I → U) (ti : I → U) (so xo : O → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ρ : I ⊕ O → Bool)
    (hright : ExteriorHasRight so xo)
    (hR : (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr) :
    PMF.map (fun ω : I → Bool => glue ω (exteriorConfig ρ))
        ((regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary) =
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).fkPMF hq hp₁.le
        (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary).filter
          (exteriorFiber (exteriorConfig ρ))
          (exteriorFiber_support_actual _ _ hq hp₀ hp₁ (exteriorConfig ρ)) := by
  apply filter_ambient_fkPMF_eq_map_glue_region_free si ti so xo hq hp₀ hp₁
  exact separated_of_outerRegion_eq_right si ti so xo ρ hright hR

end FK.FinitePlane.FreeInterior
