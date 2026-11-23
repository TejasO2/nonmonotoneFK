import FK.ExplorationTriple
import FK.StoppedInterior

/-!
# Genuine maximal exploration strata for sequential FK couplings

On the separated split graph, the canonical outer region is exactly the right
vertex summand iff no open exterior edge touches the left summand.  Hence the
maximal-stratum property is determined by the exposed exterior bits and is
unchanged by the hidden interior bits.  The sequential three-history process
then gives both lower interiors their common actual free FK law after
normalization on this maximal event.
-/

namespace FK.Exploration.MaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- The right summand has closed boundary whenever every open exterior edge
misses the left summand. -/
theorem closedBoundary_right_of_separated
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool)
    (hsep : Separated si ti so xo (exteriorConfig ρ)) :
    ClosedBoundary
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).ambientGraph
        (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary)
      ((ambientOfSum (splitSource si so) (splitTarget ti xo)).openGraph
        (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary ρ)
      (Set.range (Sum.inr : K → U ⊕ K)) := by
  intro x y hx hy _ hxy
  apply hy
  obtain ⟨x, rfl⟩ := hx
  rcases hxy.2 with hfree | ⟨e, he, hjoin⟩
  · change Sum.inr x = y at hfree
    exact (hxy.1 hfree).elim
  · cases e with
    | inl i =>
        change (Sum.inl (si i) = Sum.inr x ∧ Sum.inl (ti i) = y) ∨
          (Sum.inl (si i) = y ∧ Sum.inl (ti i) = Sum.inr x) at hjoin
        simp at hjoin
    | inr o =>
        cases y with
        | inl y =>
            exfalso
            change (so o = Sum.inr x ∧ xo o = Sum.inl y) ∨
              (so o = Sum.inl y ∧ xo o = Sum.inr x) at hjoin
            rcases hjoin with h | h
            · exact (hsep o he).2 ⟨y, h.2.symm⟩
            · exact (hsep o he).1 ⟨y, h.1.symm⟩
        | inr y => exact ⟨y, rfl⟩

/-- Converse of `separated_of_outerRegion_eq_right`: separation alone forces
the canonical outer open region to be exactly the right summand. -/
theorem outerRegion_eq_right_of_separated
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool)
    (hsep : Separated si ti so xo (exteriorConfig ρ)) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr := by
  apply Set.Subset.antisymm
  · apply (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion_minimal
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ (Set.Subset.rfl)
    exact closedBoundary_right_of_separated si ti so xo ρ hsep
  · exact subset_closedRegion

/-- The canonical maximal-stratum condition is exactly exterior separation. -/
theorem outerRegion_eq_right_iff_separated
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool) (hright : ExteriorHasRight so xo) :
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
      (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
        (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr ↔
      Separated si ti so xo (exteriorConfig ρ) := by
  constructor
  · intro hR
    exact separated_of_outerRegion_eq_right si ti so xo ρ hright hR
  · exact outerRegion_eq_right_of_separated si ti so xo ρ

/-- The maximal closed-cutset stratum of the split graph. -/
def maximalSplitStratum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K) :
    Set (Fin m ⊕ Fin k → Bool) :=
  {ρ | (ambientOfSum (splitSource si so) (splitTarget ti xo)).outerRegion
    (ambientOfSum (splitSource si so) (splitTarget ti xo)).freeBoundary
      (Set.range (Sum.inr : K → U ⊕ K)) ρ = Set.range Sum.inr}

theorem mem_maximalSplitStratum_iff
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool) (hright : ExteriorHasRight so xo) :
    ρ ∈ maximalSplitStratum si ti so xo ↔
      Separated si ti so xo (exteriorConfig ρ) :=
  outerRegion_eq_right_iff_separated si ti so xo ρ hright

/-- Hidden interior bits cannot change membership in the maximal stratum. -/
theorem mem_maximalSplitStratum_of_exterior_eq
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {ρ π : Fin m ⊕ Fin k → Bool} (hρ : ρ ∈ maximalSplitStratum si ti so xo)
    (hright : ExteriorHasRight so xo) (hext : exteriorConfig π = exteriorConfig ρ) :
    π ∈ maximalSplitStratum si ti so xo := by
  rw [mem_maximalSplitStratum_iff _ _ _ _ _ hright, hext]
  exact (mem_maximalSplitStratum_iff _ _ _ _ _ hright).mp hρ

end FK.Exploration.MaximalStrata

namespace FK.Exploration.MaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- One supported lower/upper continuation has the exact free interior law.
Unlike the earlier fixed-prefix aggregate theorem, this is a statement about
one branch and can therefore be used after filtering a joint triple on the
whole maximal exploration event. -/
theorem pair_interior_continuation_of_maximal
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ : Fin m ⊕ Fin k → Bool) (hright : ExteriorHasRight so xo)
    (hR : ρ ∈ maximalSplitStratum si ti so xo) :
    let T := transportedAmbient si ti so xo
    let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le T.freeBoundary
    let r := upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ
      (fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary) x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ T.freeBoundary hq hp₀ hp₁ x
    let step := orderedUpperStep μ
      (fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary) r
      (upperRateNN_le_one hq hp₁.le) hbound
    ∀ {x y : List Bool}, (x, y) ∈ (extendPair step [] [] k).support →
      y = exteriorHistory ρ →
      (extendPair step x y m).map (fun z =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z.1))) =
          (regionGraph si ti).fkPMF hq hp₁.le (regionGraph si ti).freeBoundary := by
  intro T μ r hbound step x y hxy hy
  have hμ := fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary
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
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z.1))) =
        ((extendPair step x y m).map Prod.fst).map (fun z =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z))) := by
      rw [PMF.map_comp]
      rfl
    _ = (extendLower (canonicalNext μ hμ) x m).map (fun z =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z))) := by
      rw [extendPair_map_fst step (canonicalNext μ hμ) hfst]
    _ = (extendLower (canonicalNext μ hμ)
          (exteriorHistory (m := m) (ambientOfHistory x)) m).map (fun z =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z))) := by
      rw [hex]
    _ = _ := by
      apply extendLower_exteriorHistory_eq_free_of_le_outerRegion si ti so xo hq hp₀ hp₁
        ρ (ambientOfHistory x) hmono hright hR

/-- The one-bit triple step obtained by gluing two ordered pairs through
their common fresh Bernoulli bit. -/
noncomputable def gluedUpperStep {n : ℕ} (μ₁ μ₂ : PMF (Fin n → Bool))
    (hμ₁ : ∀ ω, μ₁ ω ≠ 0) (hμ₂ : ∀ ω, μ₂ ω ≠ 0)
    (r : NNReal) (hr : r ≤ 1)
    (hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ))
    (hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ)) :
    List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool) :=
  fun x₁ x₂ _ => (PMF.OrderedCoupling.glue
    (boolOrderedCouplingOfLe (canonicalNext μ₁ hμ₁ x₁) r hr (hb₁ x₁))
    (boolOrderedCouplingOfLe (canonicalNext μ₂ hμ₂ x₂) r hr (hb₂ x₂))).dist

/-- First pair projection of the glued bit step. -/
lemma gluedUpperStep_map_fst_thd {n : ℕ} (μ₁ μ₂ : PMF (Fin n → Bool))
    (hμ₁ : ∀ ω, μ₁ ω ≠ 0) (hμ₂ : ∀ ω, μ₂ ω ≠ 0)
    (r : NNReal) (hr : r ≤ 1)
    (hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ))
    (hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ))
    (x₁ x₂ y : List Bool) :
    (gluedUpperStep μ₁ μ₂ hμ₁ hμ₂ r hr hb₁ hb₂ x₁ x₂ y).map
      (fun z => (z.1, z.2.2)) = orderedUpperStep μ₁ hμ₁ r hr hb₁ x₁ y := by
  exact PMF.Coupling.map_glueDist_fst_thd
    (boolOrderedCouplingOfLe (canonicalNext μ₁ hμ₁ x₁) r hr (hb₁ x₁)).toCoupling
    (boolOrderedCouplingOfLe (canonicalNext μ₂ hμ₂ x₂) r hr (hb₂ x₂)).toCoupling

/-- Second pair projection of the glued bit step. -/
lemma gluedUpperStep_map_snd_thd {n : ℕ} (μ₁ μ₂ : PMF (Fin n → Bool))
    (hμ₁ : ∀ ω, μ₁ ω ≠ 0) (hμ₂ : ∀ ω, μ₂ ω ≠ 0)
    (r : NNReal) (hr : r ≤ 1)
    (hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ))
    (hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ))
    (x₁ x₂ y : List Bool) :
    (gluedUpperStep μ₁ μ₂ hμ₁ hμ₂ r hr hb₁ hb₂ x₁ x₂ y).map
      (fun z => (z.2.1, z.2.2)) = orderedUpperStep μ₂ hμ₂ r hr hb₂ x₂ y := by
  exact PMF.Coupling.map_glueDist_snd_thd
    (boolOrderedCouplingOfLe (canonicalNext μ₁ hμ₁ x₁) r hr (hb₁ x₁)).toCoupling
    (boolOrderedCouplingOfLe (canonicalNext μ₂ hμ₂ x₂) r hr (hb₂ x₂)).toCoupling

/-- Both bit coordinates are below their common upper bit on support. -/
lemma gluedUpperStep_ordered {n : ℕ} (μ₁ μ₂ : PMF (Fin n → Bool))
    (hμ₁ : ∀ ω, μ₁ ω ≠ 0) (hμ₂ : ∀ ω, μ₂ ω ≠ 0)
    (r : NNReal) (hr : r ≤ 1)
    (hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ))
    (hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ))
    (x₁ x₂ y : List Bool) {z : Bool × Bool × Bool}
    (hz : z ∈ (gluedUpperStep μ₁ μ₂ hμ₁ hμ₂ r hr hb₁ hb₂ x₁ x₂ y).support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  exact ⟨(PMF.OrderedCoupling.glue
      (boolOrderedCouplingOfLe (canonicalNext μ₁ hμ₁ x₁) r hr (hb₁ x₁))
      (boolOrderedCouplingOfLe (canonicalNext μ₂ hμ₂ x₂) r hr (hb₂ x₂))).rel_fst z hz,
    (PMF.OrderedCoupling.glue
      (boolOrderedCouplingOfLe (canonicalNext μ₁ hμ₁ x₁) r hr (hb₁ x₁))
      (boolOrderedCouplingOfLe (canonicalNext μ₂ hμ₂ x₂) r hr (hb₂ x₂))).rel_snd z hz⟩

end FK.Exploration.MaximalStrata

namespace FK.Exploration.MaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- Normalized conditional free-interior laws of both FK coordinates on the
same genuine maximal closed-cutset stratum.  The event is evaluated on the
exposed upper history, completed only by closed interior coordinates.  By
`mem_maximalSplitStratum_of_exterior_eq`, its truth does not depend on that
completion.  `hU` is only the nondegenerate-conditioning support witness. -/
theorem normalized_maximalStratum_interiors
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hright : ExteriorHasRight so xo) :
    let T := transportedAmbient si ti so xo
    let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le T.freeBoundary
    let hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary
    let r := upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ T.freeBoundary hq hp₀ hp₁ x
    let upperStep := orderedUpperStep μ hμ r (upperRateNN_le_one hq hp₁.le) hbound
    let step := gluedUpperStep μ μ hμ hμ r (upperRateNN_le_one hq hp₁.le) hbound hbound
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
  intro T μ hμ r hbound upperStep step pfx M hU
  have hstep₁ : ∀ x₁ x₂ y, (step x₁ x₂ y).map (fun z => (z.1, z.2.2)) =
      upperStep x₁ y := by
    intro x₁ x₂ y
    exact gluedUpperStep_map_fst_thd μ μ hμ hμ r
      (upperRateNN_le_one hq hp₁.le) hbound hbound x₁ x₂ y
  have hstep₂ : ∀ x₁ x₂ y, (step x₁ x₂ y).map (fun z => (z.2.1, z.2.2)) =
      upperStep x₂ y := by
    intro x₁ x₂ y
    exact gluedUpperStep_map_snd_thd μ μ hμ hμ r
      (upperRateNN_le_one hq hp₁.le) hbound hbound x₁ x₂ y
  constructor
  · apply bind_eq_self_of_forall_support _ _ _
    intro z hz
    rw [PMF.mem_support_filter_iff] at hz
    obtain ⟨hzM, hz⟩ := hz
    have hlen := extendTriple_length_support step [] [] [] k hz
    have hM : ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo := hzM
    have hy : z.2.2 = exteriorHistory (m := m) (ambientOfHistory z.2.2) :=
      (exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.2.2)).symm
    have hzpair : (z.1, z.2.2) ∈ (extendPair upperStep [] [] k).support := by
      rw [← extendTriple_map_fst_thd step upperStep hstep₁ [] [] [] k]
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
      _ = (extendPair upperStep z.1 z.2.2 m).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
        rw [extendTriple_map_fst_thd step upperStep hstep₁]
      _ = _ := by
        exact pair_interior_continuation_of_maximal si ti so xo hq hp₀ hp₁
          (ambientOfHistory z.2.2) hright hM hzpair hy
  · apply bind_eq_self_of_forall_support _ _ _
    intro z hz
    rw [PMF.mem_support_filter_iff] at hz
    obtain ⟨hzM, hz⟩ := hz
    have hlen := extendTriple_length_support step [] [] [] k hz
    have hM : ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo := hzM
    have hy : z.2.2 = exteriorHistory (m := m) (ambientOfHistory z.2.2) :=
      (exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.2.2)).symm
    have hzpair : (z.2.1, z.2.2) ∈ (extendPair upperStep [] [] k).support := by
      rw [← extendTriple_map_snd_thd step upperStep hstep₂ [] [] [] k]
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
      _ = (extendPair upperStep z.2.1 z.2.2 m).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) w.1))) := by
        rw [extendTriple_map_snd_thd step upperStep hstep₂]
      _ = _ := by
        exact pair_interior_continuation_of_maximal si ti so xo hq hp₀ hp₁
          (ambientOfHistory z.2.2) hright hM hzpair hy

end FK.Exploration.MaximalStrata
namespace FK.Exploration.MaximalStrata

open scoped ENNReal BigOperators Classical
open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior

variable {U K : Type*} [Fintype U] [Fintype K]
variable {m k : ℕ}

/-- The all-closed triple bit is supported whenever the upper Bernoulli
closed mass is positive. -/
lemma gluedUpperStep_false_support {n : ℕ} (μ₁ μ₂ : PMF (Fin n → Bool))
    (hμ₁ : ∀ ω, μ₁ ω ≠ 0) (hμ₂ : ∀ ω, μ₂ ω ≠ 0)
    (r : NNReal) (hr : r ≤ 1) (hrlt : r < 1)
    (hb₁ : ∀ x, (canonicalNext μ₁ hμ₁ x true).toReal ≤ (r : ℝ))
    (hb₂ : ∀ x, (canonicalNext μ₂ hμ₂ x true).toReal ≤ (r : ℝ))
    (x₁ x₂ y : List Bool) :
    (false, false, false) ∈
      (gluedUpperStep μ₁ μ₂ hμ₁ hμ₂ r hr hb₁ hb₂ x₁ x₂ y).support := by
  let c₁ := boolOrderedCouplingOfLe (canonicalNext μ₁ hμ₁ x₁) r hr (hb₁ x₁)
  let c₂ := boolOrderedCouplingOfLe (canonicalNext μ₂ hμ₂ x₂) r hr (hb₂ x₂)
  let t := PMF.OrderedCoupling.glue c₁ c₂
  have hmap : t.dist.map (fun z => z.2.2) = FKModel.bernoulliPMF r hr := t.map_thd
  have hpos : false ∈ (FKModel.bernoulliPMF r hr).support := by
    rw [PMF.mem_support_iff, FKModel.bernoulliPMF_apply]
    simp only [Bool.cond_false, ne_eq, ENNReal.coe_eq_zero, tsub_eq_zero_iff_le]
    exact not_le_of_gt hrlt
  have hupper : false ∈ (t.dist.map (fun z => z.2.2)).support := by
    rw [hmap]
    exact hpos
  rw [PMF.mem_support_map_iff] at hupper
  obtain ⟨z, hz, hzfalse⟩ := hupper
  change z.2.2 = false at hzfalse
  rcases z with ⟨a, b, c⟩
  cases c with
  | false =>
      have h₁ := t.rel_fst (a, b, false) hz
      have h₂ := t.rel_snd (a, b, false) hz
      cases a <;> cases b
      · exact hz
      · exact ((by decide : ¬ (true : Bool) ≤ false) h₂).elim
      · exact ((by decide : ¬ (true : Bool) ≤ false) h₁).elim
      · exact ((by decide : ¬ (true : Bool) ≤ false) h₁).elim
  | true => simp at hzfalse

/-- Chronological closed extensions are supported if every one-bit closed
triple is supported. -/
theorem extendTriple_append_replicate_false_support
    (step : List Bool → List Bool → List Bool → PMF (Bool × Bool × Bool))
    (hstep : ∀ x₁ x₂ y, (false, false, false) ∈ (step x₁ x₂ y).support)
    (x₁ x₂ y : List Bool) (n : ℕ) :
    (x₁ ++ List.replicate n false, x₂ ++ List.replicate n false,
      y ++ List.replicate n false) ∈ (extendTriple step x₁ x₂ y n).support := by
  induction n generalizing x₁ x₂ y with
  | zero => simp [extendTriple]
  | succ n ih =>
      rw [extendTriple, PMF.mem_support_bind_iff]
      refine ⟨(false, false, false), hstep x₁ x₂ y, ?_⟩
      simpa only [Nat.add_comm n 1, List.replicate_add, List.replicate_one,
        List.singleton_append, List.nil_append, List.append_assoc] using
        ih (x₁ ++ [false]) (x₂ ++ [false]) (y ++ [false])

/-- The all-closed exposed exterior is a positive-probability point of the
maximal stratum.  This is exactly the conditioning witness `hU` required by
`normalized_maximalStratum_interiors`. -/
theorem maximalStratum_prefix_support
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    let T := transportedAmbient si ti so xo
    let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le T.freeBoundary
    let hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ T.freeBoundary
    let r := upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ T.freeBoundary hq hp₀ hp₁ x
    let upperStep := orderedUpperStep μ hμ r (upperRateNN_le_one hq hp₁.le) hbound
    let step := gluedUpperStep μ μ hμ hμ r (upperRateNN_le_one hq hp₁.le) hbound hbound
    let pfx := extendTriple step [] [] [] k
    let M : Set (List Bool × List Bool × List Bool) :=
      {z | ambientOfHistory (m := m) z.2.2 ∈ maximalSplitStratum si ti so xo}
    ∃ z ∈ M, z ∈ pfx.support := by
  intro T μ hμ r hbound upperStep step pfx M
  let z : List Bool × List Bool × List Bool :=
    (List.replicate k false, List.replicate k false, List.replicate k false)
  have hz : z ∈ pfx.support := by
    change (List.replicate k false, List.replicate k false, List.replicate k false) ∈
      (extendTriple step [] [] [] k).support
    have hs : ∀ x₁ x₂ y, (false, false, false) ∈ (step x₁ x₂ y).support := by
      intro x₁ x₂ y
      exact gluedUpperStep_false_support μ μ hμ hμ r
        (upperRateNN_le_one hq hp₁.le) (upperRateNN_lt_one hq hp₀ hp₁)
        hbound hbound x₁ x₂ y
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

end FK.Exploration.MaximalStrata
