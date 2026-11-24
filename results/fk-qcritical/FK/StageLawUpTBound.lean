import FK.StageInstantiation
import FK.GibbsOrder
open Filter MeasureTheory Set
set_option linter.unusedSectionVars false
namespace FK.InfiniteVolume
variable {E V : Type} [Countable E] [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The finite-volume law of a fixed-vertex stage with a fixed boundary partition. -/
noncomputable def stageLaw (F : FK.InfiniteVolume.NoEscape.FixedVertexFamily E V) (ξ : Setoid V)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (n : ℕ) : ProbabilityMeasure (Configuration E) :=
  (F.box n).finiteVolumeLaw hq hp ξ

/-- **One-step monotonicity of an upper-corner mass on a fixed-vertex family.** -/
theorem stageLaw_upT_le_of_le
    (F : FK.InfiniteVolume.NoEscape.FixedVertexFamily E V)
    {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1) (ξ : Setoid V)
    {S : Finset E} {T : Finset ↥S} {n m : ℕ} (hnm : n ≤ m) (hS : S ⊆ F.edges n) :
    ((stageLaw F ξ (lt_of_lt_of_le zero_lt_one hq) hp1.le n : Measure (Configuration E))
      (upT S T)).toReal
      ≤ ((stageLaw F ξ (lt_of_lt_of_le zero_lt_one hq) hp1.le m : Measure (Configuration E))
        (upT S T)).toReal := by
  classical
  set A : Set (F.box n).Interior := {β | ∀ e : ↥S, e ∈ T → β ⟨e.1, hS e.2⟩ = true} with hA
  have hAup : FK.InfiniteVolume.NoEscape.IsUp A := by
    intro β hβ γ hγ e he
    rw [← hγ ⟨e.1, hS e.2⟩]
    exact hβ e he
  have hev : upT S T = (F.box n).interiorRestriction ⁻¹' A := by
    ext ω
    show (∀ e : ↥S, e ∈ T → ω e.1 = true) ↔ ((F.box n).split ω).2 ∈ A
    rw [hA]
    simp only [FiniteBox.split, Set.mem_setOf_eq]
  rw [hev]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (FK.InfiniteVolume.NoEscape.FixedVertexFamily.finiteVolumeLaw_stage_mono
      (F := F) (hq := lt_of_lt_of_le zero_lt_one hq) (hp := hp1.le) hp1
      (FK.InfiniteVolume.NoEscape.posAssoc_of_one_le hq hp0 hp1.le) ξ hnm (A := A) hAup)


/-- **Stage monotonicity from the stage at which the corner coordinates exist.** -/
theorem fixedVertexFamily_eventually_mono_upT
    (F : FK.InfiniteVolume.NoEscape.FixedVertexFamily E V)
    (hcov : ∀ e : E, ∃ n, e ∈ F.edges n)
    {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p < 1) (ξ : Setoid V)
    (S : Finset E) (T : Finset ↥S) :
    ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
      ((stageLaw F ξ (lt_of_lt_of_le zero_lt_one hq) hp1.le n : Measure (Configuration E))
        (upT S T)).toReal
      ≤ ((stageLaw F ξ (lt_of_lt_of_le zero_lt_one hq) hp1.le m : Measure (Configuration E))
        (upT S T)).toReal := by
  classical
  have hcov' : ∀ e : E, ∃ n, e ∈ F.edges n := hcov
  choose st hst using hcov'
  refine ⟨Finset.sup S st, fun n m hn hm => ?_⟩
  exact stageLaw_upT_le_of_le F hq hp0 hp1 ξ hm
    (fun e he => F.monotone (le_trans (Finset.le_sup he) hn) (hst e))

#print axioms FK.InfiniteVolume.fixedVertexFamily_eventually_mono_upT

#print axioms FK.InfiniteVolume.stageLaw_upT_le_of_le
end FK.InfiniteVolume
