import FK.TripleAssembly
import FK.PatchLifting

/-!
# Positive probability of an all-scales encounter event

The deterministic three-cluster patch is expressed as a finite coordinate
update.  The target encounter event is measurable by expanding all its
countable geometric witnesses.  Countable finite-patch lifting then applies
to any law with the explicit finite-pattern insertion-tolerance property, and
in particular to Bernoulli bond percolation at interior rates.
-/

open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory unitInterval
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Configurations having three prescribed pairwise separated infinite open
clusters. -/
def ThreeInfiniteClusters (G : SimpleGraph V) (ω : G.edgeSet → Bool) : Prop :=
  ∃ r₀ r₁ r₂ : V,
    {z | OpenConnected G ω Set.univ r₀ z}.Infinite ∧
    {z | OpenConnected G ω Set.univ r₁ z}.Infinite ∧
    {z | OpenConnected G ω Set.univ r₂ z}.Infinite ∧
    (¬ OpenConnected G ω Set.univ r₀ r₁) ∧
    (¬ OpenConnected G ω Set.univ r₀ r₂) ∧
    (¬ OpenConnected G ω Set.univ r₁ r₂)

/-- A finite internal opening produces three disjoint arms at one centre at
all scales. -/
def EncounterEvent (G : SimpleGraph V) : Set (G.edgeSet → Bool) :=
  {η | ∃ U : Set V, U.Finite ∧ ∃ y : V,
    ∀ n : ℕ, ThreeWayArms G (openInternal U η) y n}

/-- The configuration-independent part of three-arm geometry. -/
def GoodThreeWayGeometry (G : SimpleGraph V) (y : V) (n : ℕ)
    {a b c : V} (pa : G.Walk y a) (pb : G.Walk y b) (pc : G.Walk y c) : Prop :=
  n ≤ G.dist y a ∧ n ≤ G.dist y b ∧ n ≤ G.dist y c ∧
    pa.IsPath ∧ pb.IsPath ∧ pc.IsPath ∧
    (∀ z ∈ pa.support, z ∈ pb.support → z = y) ∧
    (∀ z ∈ pa.support, z ∈ pc.support → z = y) ∧
    (∀ z ∈ pb.support, z ∈ pc.support → z = y)

lemma threeWayArms_iff {ω : G.edgeSet → Bool} {y : V} {n : ℕ} :
    ThreeWayArms G ω y n ↔ ∃ a b c : V, ∃ pa : G.Walk y a,
      ∃ pb : G.Walk y b, ∃ pc : G.Walk y c,
        GoodThreeWayGeometry G y n pa pb pc ∧
        IsOpenIn ω Set.univ pa ∧ IsOpenIn ω Set.univ pb ∧
          IsOpenIn ω Set.univ pc := by
  constructor
  · rintro ⟨a, b, c, pa, pb, pc, hna, hnb, hnc, hpatha, hpathb, hpathc,
      hopa, hopb, hopc, hab, hac, hbc⟩
    exact ⟨a, b, c, pa, pb, pc,
      ⟨hna, hnb, hnc, hpatha, hpathb, hpathc, hab, hac, hbc⟩, hopa, hopb, hopc⟩
  · rintro ⟨a, b, c, pa, pb, pc,
      ⟨hna, hnb, hnc, hpatha, hpathb, hpathc, hab, hac, hbc⟩, hopa, hopb, hopc⟩
    exact ⟨a, b, c, pa, pb, pc, hna, hnb, hnc, hpatha, hpathb, hpathc,
      hopa, hopb, hopc, hab, hac, hbc⟩

/-- Measurability of one fixed-scale three-arm event. -/
lemma measurableSet_threeWayArms [Countable V] (y : V) (n : ℕ) :
    MeasurableSet {ω : G.edgeSet → Bool | ThreeWayArms G ω y n} := by
  have heq : {ω : G.edgeSet → Bool | ThreeWayArms G ω y n} =
      ⋃ a : V, ⋃ b : V, ⋃ c : V, ⋃ pa : G.Walk y a, ⋃ pb : G.Walk y b,
        ⋃ pc : G.Walk y c, {ω : G.edgeSet → Bool |
          GoodThreeWayGeometry G y n pa pb pc ∧
          IsOpenIn ω Set.univ pa ∧ IsOpenIn ω Set.univ pb ∧
            IsOpenIn ω Set.univ pc} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact threeWayArms_iff
  rw [heq]
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun pa =>
      MeasurableSet.iUnion fun pb => MeasurableSet.iUnion fun pc => ?_
  by_cases hgeom : GoodThreeWayGeometry G y n pa pb pc
  · have hset : {ω : G.edgeSet → Bool |
        GoodThreeWayGeometry G y n pa pb pc ∧
        IsOpenIn ω Set.univ pa ∧ IsOpenIn ω Set.univ pb ∧
          IsOpenIn ω Set.univ pc} =
        {ω | IsOpenIn ω Set.univ pa} ∩ {ω | IsOpenIn ω Set.univ pb} ∩
          {ω | IsOpenIn ω Set.univ pc} := by
      ext ω
      simp only [hgeom, true_and, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset]
    exact ((measurableSet_isOpenIn Set.univ pa).inter
      (measurableSet_isOpenIn Set.univ pb)).inter (measurableSet_isOpenIn Set.univ pc)
  · have hset : {ω : G.edgeSet → Bool |
        GoodThreeWayGeometry G y n pa pb pc ∧
        IsOpenIn ω Set.univ pa ∧ IsOpenIn ω Set.univ pb ∧
          IsOpenIn ω Set.univ pc} = ∅ := by
      ext ω
      simp only [hgeom, false_and, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [hset]
    exact MeasurableSet.empty

/-- The all-scales encounter event is measurable on a countable graph. -/
lemma measurableSet_encounterEvent [Countable V] :
    MeasurableSet (EncounterEvent G) := by
  have heq : EncounterEvent G =
      ⋃ U ∈ {U : Set V | U.Finite}, ⋃ y : V, ⋂ n : ℕ,
        {η : G.edgeSet → Bool | ThreeWayArms G (openInternal U η) y n} := by
    ext η
    simp only [EncounterEvent, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨U, hU, y, hy⟩
      exact ⟨U, hU, y, hy⟩
    · rintro ⟨U, hU, y, hy⟩
      exact ⟨U, hU, y, hy⟩
  rw [heq]
  exact MeasurableSet.biUnion Set.Countable.ofPred_finite fun U _ =>
    MeasurableSet.iUnion fun y => MeasurableSet.iInter fun n => by
      have hmeas : Measurable fun η : G.edgeSet → Bool => openInternal U η := by
        apply measurable_pi_lambda
        intro e
        by_cases he : (e : Sym2 V) ∈ internal G U
        · simp only [openInternal, he, if_true]
          exact measurable_const
        · simp only [openInternal, he, if_false]
          exact measurable_pi_apply e
      exact (measurableSet_threeWayArms (G := G) y n).preimage hmeas

/-- The deterministic encounter patch, with an explicit finite coordinate
support.  Opening that support does not alter any exterior coordinate. -/
lemma exists_internalPatch_mem_encounterEvent [G.LocallyFinite]
    (hG : G.Connected) {ω : G.edgeSet → Bool}
    (hω : ThreeInfiniteClusters G ω) :
    ∃ j : PatchIndex G.edgeSet,
      @Function.updateFinset G.edgeSet (fun _ => Bool)
        (fun a b => Classical.propDecidable (a = b)) ω j.1 j.2 ∈ EncounterEvent G := by
  obtain ⟨r₀, r₁, r₂, hinf₀, hinf₁, hinf₂, h₀₁, h₀₂, h₁₂⟩ := hω
  obtain ⟨U, hU, y, hy⟩ := exists_threeWayArms_openInternal_of_three_infinite
    hG hinf₀ hinf₁ hinf₂ h₀₁ h₀₂ h₁₂
  refine ⟨⟨internalFinset (G := G) hU, fun _ => true⟩, ?_⟩
  dsimp only
  rw [← openInternal_eq_updateFinset (ω := ω) hU]
  exact ⟨U, hU, y, by simpa only [openInternal_idem] using hy⟩

/-- **Positive-probability encounter under insertion tolerance.**  If a law
on Boolean edges has finite-pattern insertion tolerance and gives positive
measure to three pairwise distinct infinite clusters, then it gives positive
measure to a finite patch producing three disjoint arms at every scale. -/
theorem measure_pos_encounterEvent_of_three_infinite_of_insertionTolerant
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) (hμ : FinitePatternInsertionTolerance μ)
    (hS : 0 < μ {ω | ThreeInfiniteClusters G ω}) :
    0 < μ (EncounterEvent G) := by
  refine measure_pos_of_forall_exists_patch_of_finitePatternInsertionTolerance
    μ hμ (measurableSet_encounterEvent (G := G)) hS ?_
  intro ω hω
  exact exists_internalPatch_mem_encounterEvent hG hω

/-- Bernoulli percolation at an interior rate has positive encounter
probability whenever three distinct infinite clusters have positive
probability. -/
theorem measure_pos_encounterEvent_of_three_infinite [Countable V]
    [G.LocallyFinite] (hG : G.Connected) (p : I)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hS : 0 < percolation G p {ω | ThreeInfiniteClusters G ω}) :
    0 < percolation G p (EncounterEvent G) := by
  exact measure_pos_encounterEvent_of_three_infinite_of_insertionTolerant
    hG (percolation G p) (finitePatternInsertionTolerance_bernoulliProduct p hp0 hp1) hS


end FK.BurtonKeane
