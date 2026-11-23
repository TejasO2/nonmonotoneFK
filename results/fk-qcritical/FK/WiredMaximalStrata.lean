import FK.WiredStoppedInterior

/-!
# Maximal-stratum interiors for two right-wired FK coordinates

The two lower sequential laws may use different arbitrary setoids on the
right/exterior vertices.  Their interiors nevertheless have the same actual
free FK law on every genuine maximal canonical stratum of the common upper
configuration.
-/

namespace FK.Exploration.WiredMaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- One supported continuation with right-supported ambient wiring has the
exact free-interior law on an upper maximal stratum. -/
theorem pair_interior_continuation_rightWired
    (si : Fin m → U) (ti : Fin m → U) (zo xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ : Setoid K) (ρ : Fin m ⊕ Fin k → Bool)
    (hright : ExteriorHasRight zo xo)
    (hR : ρ ∈ maximalSplitStratum si ti zo xo) :
    let G := ambientOfSum (splitSource si zo) (splitTarget ti xo)
    let T := transportedAmbient si ti zo xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti zo xo ζ)
    let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ
    let hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ
    let r := upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξ hq hp₀ hp₁ x
    let step := orderedUpperStep μ hμ r (upperRateNN_le_one hq hp₁.le) hbound
    ∀ {x y : List Bool}, (x, y) ∈ (extendPair step [] [] k).support →
      y = exteriorHistory ρ →
      (extendPair step x y m).map (fun z =>
        interiorConfig (toAmbientConfig si ti zo xo (toConfig (k + m) z.1))) =
          (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  intro G T ξ μ hμ r hbound step x y hxy hy
  have hfst : ∀ x y, (step x y).map Prod.fst = canonicalNext μ hμ x := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (upperRateNN_le_one hq hp₁.le) (hbound x)).map_fst
  have hordstep : ∀ x y z, z ∈ (step x y).support → z.1 ≤ z.2 := by
    intro x y w hw
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (upperRateNN_le_one hq hp₁.le) (hbound x)).ordered w hw
  have hlen := extendPair_length_support step [] [] k hxy
  have hord := extendPair_ordered step hordstep List.Forall₂.nil k hxy
  have hex : exteriorHistory (m := m) (ambientOfHistory x) = x :=
    exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.1)
  have hconf : toConfig k x ≤ exteriorConfig ρ := by
    have hc := toConfig_le_of_forall₂ (n := k) hord
    rw [hy] at hc
    simpa only [exteriorHistory, toConfig_ofFn, exteriorConfig, Function.comp_def] using hc
  have hmono : ambientOfHistory x ≤ ρ := by
    intro a
    cases a with
    | inl a => exact Bool.false_le _
    | inr a => exact hconf a
  calc
    (extendPair step x y m).map (fun z =>
        interiorConfig (toAmbientConfig si ti zo xo (toConfig (k + m) z.1))) =
        ((extendPair step x y m).map Prod.fst).map (fun z =>
          interiorConfig (toAmbientConfig si ti zo xo (toConfig (k + m) z))) := by
      rw [PMF.map_comp]
      rfl
    _ = (extendLower (canonicalNext μ hμ) x m).map (fun z =>
          interiorConfig (toAmbientConfig si ti zo xo (toConfig (k + m) z))) := by
      rw [extendPair_map_fst step (canonicalNext μ hμ) hfst]
    _ = (extendLower (canonicalNext μ hμ)
          (exteriorHistory (m := m) (ambientOfHistory x)) m).map (fun z =>
          interiorConfig (toAmbientConfig si ti zo xo (toConfig (k + m) z))) := by
      rw [hex]
    _ = _ := by
      apply extendLower_exteriorHistory_eq_free_rightWired_of_le_outerRegion
        si ti zo xo hq hp₀ hp₁ ζ ρ (ambientOfHistory x) hmono hright hR

end FK.Exploration.WiredMaximalStrata

namespace FK.Exploration.WiredMaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Both lower interiors are exactly free on the same normalized maximal
stratum, even with two different right/exterior boundary setoids. -/
theorem normalized_maximalStratum_interiors_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) (hright : ExteriorHasRight so xo) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ₁ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti so xo ζ₁)
    let ξ₂ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti so xo ζ₂)
    let μ₁ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ₁
    let μ₂ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ₂
    let hμ₁ : ∀ ω, μ₁ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ₁
    let hμ₂ : ∀ ω, μ₂ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ₂
    let r := upperRateNN q p
    let hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξ₁ hq hp₀ hp₁ x
    let hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξ₂ hq hp₀ hp₁ x
    let upperStep₁ := orderedUpperStep μ₁ hμ₁ r (upperRateNN_le_one hq hp₁.le) hb₁
    let upperStep₂ := orderedUpperStep μ₂ hμ₂ r (upperRateNN_le_one hq hp₁.le) hb₂
    let step := gluedUpperStep μ₁ μ₂ hμ₁ hμ₂ r
      (upperRateNN_le_one hq hp₁.le) hb₁ hb₂
    let pfx := extendTriple step [] [] [] k
    let M : Set (List Bool × List Bool × List Bool) :=
      {z | ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo}
    ∀ hU : ∃ z ∈ M, z ∈ pfx.support,
      ((pfx.filter M hU).bind fun z =>
        (extendTriple step z.1 z.2.1 z.2.2 m).map (fun w =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1)))) =
        (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary ∧
      ((pfx.filter M hU).bind fun z =>
        (extendTriple step z.1 z.2.1 z.2.2 m).map (fun w =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1)))) =
        (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  intro G T ξ₁ ξ₂ μ₁ μ₂ hμ₁ hμ₂ r hb₁ hb₂ upperStep₁ upperStep₂ step pfx M hU
  have hstep₁ : ∀ x₁ x₂ y, (step x₁ x₂ y).map (fun z => (z.1, z.2.2)) =
      upperStep₁ x₁ y := by
    intro x₁ x₂ y
    exact gluedUpperStep_map_fst_thd μ₁ μ₂ hμ₁ hμ₂ r
      (upperRateNN_le_one hq hp₁.le) hb₁ hb₂ x₁ x₂ y
  have hstep₂ : ∀ x₁ x₂ y, (step x₁ x₂ y).map (fun z => (z.2.1, z.2.2)) =
      upperStep₂ x₂ y := by
    intro x₁ x₂ y
    exact gluedUpperStep_map_snd_thd μ₁ μ₂ hμ₁ hμ₂ r
      (upperRateNN_le_one hq hp₁.le) hb₁ hb₂ x₁ x₂ y
  constructor
  · apply bind_eq_self_of_forall_support _ _ _
    intro z hz
    rw [PMF.mem_support_filter_iff] at hz
    obtain ⟨hzM, hz⟩ := hz
    have hlen := extendTriple_length_support step [] [] [] k hz
    have hM : ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo := hzM
    have hy : z.2.2 = exteriorHistory (m := m) (ambientOfHistory z.2.2) :=
      (exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.2.2)).symm
    have hzpair : (z.1, z.2.2) ∈ (extendPair upperStep₁ [] [] k).support := by
      rw [← extendTriple_map_fst_thd step upperStep₁ hstep₁ [] [] [] k]
      rw [PMF.mem_support_map_iff]
      exact ⟨z, hz, rfl⟩
    calc
      (extendTriple step z.1 z.2.1 z.2.2 m).map (fun w =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) =
          ((extendTriple step z.1 z.2.1 z.2.2 m).map (fun w => (w.1, w.2.2))).map
            (fun w => interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1))) := by
        rw [PMF.map_comp]
        rfl
      _ = (extendPair upperStep₁ z.1 z.2.2 m).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
        rw [extendTriple_map_fst_thd step upperStep₁ hstep₁]
      _ = _ := by
        exact pair_interior_continuation_rightWired si ti so xo hq hp₀ hp₁
          ζ₁ (ambientOfHistory z.2.2) hright hM hzpair hy
  · apply bind_eq_self_of_forall_support _ _ _
    intro z hz
    rw [PMF.mem_support_filter_iff] at hz
    obtain ⟨hzM, hz⟩ := hz
    have hlen := extendTriple_length_support step [] [] [] k hz
    have hM : ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo := hzM
    have hy : z.2.2 = exteriorHistory (m := m) (ambientOfHistory z.2.2) :=
      (exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.2.2)).symm
    have hzpair : (z.2.1, z.2.2) ∈ (extendPair upperStep₂ [] [] k).support := by
      rw [← extendTriple_map_snd_thd step upperStep₂ hstep₂ [] [] [] k]
      rw [PMF.mem_support_map_iff]
      exact ⟨z, hz, rfl⟩
    calc
      (extendTriple step z.1 z.2.1 z.2.2 m).map (fun w =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.2.1))) =
          ((extendTriple step z.1 z.2.1 z.2.2 m).map (fun w => (w.2.1, w.2.2))).map
            (fun w => interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1))) := by
        rw [PMF.map_comp]
        rfl
      _ = (extendPair upperStep₂ z.2.1 z.2.2 m).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
        rw [extendTriple_map_snd_thd step upperStep₂ hstep₂]
      _ = _ := by
        exact pair_interior_continuation_rightWired si ti so xo hq hp₀ hp₁
          ζ₂ (ambientOfHistory z.2.2) hright hM hzpair hy

end FK.Exploration.WiredMaximalStrata

namespace FK.Exploration.WiredMaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.WiredRightInterior
open FK.Exploration.WiredStoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- The all-closed exposed exterior supplies the conditioning witness for the
two-setoid theorem internally. -/
theorem maximalStratum_prefix_support_rightWired
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ζ₁ ζ₂ : Setoid K) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ₁ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti so xo ζ₁)
    let ξ₂ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (rightWiredBoundary si ti so xo ζ₂)
    let μ₁ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ₁
    let μ₂ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ₂
    let hμ₁ : ∀ ω, μ₁ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ₁
    let hμ₂ : ∀ ω, μ₂ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ₂
    let r := upperRateNN q p
    let hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξ₁ hq hp₀ hp₁ x
    let hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξ₂ hq hp₀ hp₁ x
    let upperStep₁ := orderedUpperStep μ₁ hμ₁ r (upperRateNN_le_one hq hp₁.le) hb₁
    let upperStep₂ := orderedUpperStep μ₂ hμ₂ r (upperRateNN_le_one hq hp₁.le) hb₂
    let step := gluedUpperStep μ₁ μ₂ hμ₁ hμ₂ r
      (upperRateNN_le_one hq hp₁.le) hb₁ hb₂
    let pfx := extendTriple step [] [] [] k
    let M : Set (List Bool × List Bool × List Bool) :=
      {z | ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo}
    ∃ z ∈ M, z ∈ pfx.support := by
  intro G T ξ₁ ξ₂ μ₁ μ₂ hμ₁ hμ₂ r hb₁ hb₂ upperStep₁ upperStep₂ step pfx M
  let z : List Bool × List Bool × List Bool :=
    (List.replicate k false, List.replicate k false, List.replicate k false)
  have hz : z ∈ pfx.support := by
    change (List.replicate k false, List.replicate k false, List.replicate k false) ∈
      (extendTriple step [] [] [] k).support
    have hs : ∀ x₁ x₂ y, (false, false, false) ∈ (step x₁ x₂ y).support := by
      intro x₁ x₂ y
      exact gluedUpperStep_false_support μ₁ μ₂ hμ₁ hμ₂ r
        (upperRateNN_le_one hq hp₁.le) (upperRateNN_lt_one hq hp₀ hp₁)
        hb₁ hb₂ x₁ x₂ y
    simpa using extendTriple_append_replicate_false_support step hs [] [] [] k
  refine ⟨z, ?_, hz⟩
  change ambientOfHistory (m := m) (List.replicate k false) ∈ maximalSplitStratum si ti so xo
  apply outerRegion_eq_right_of_separated
  intro o ho
  have hclosed : toConfig k (List.replicate k false) o = false := by
    exact List.getD_replicate false (y := false) o.isLt
  change toConfig k (List.replicate k false) o = true at ho
  rw [hclosed] at ho
  contradiction

end FK.Exploration.WiredMaximalStrata
