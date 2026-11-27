import FK.PcPos

/-!
# Positive probability after countable finite patching

A positive-measure set of configurations each admitting some finite patch into
a target event forces the target event to have positive measure under an
explicit finite-pattern insertion-tolerance hypothesis.  The patch may depend
on the configuration: countability extracts one fixed patch.  Independence
proves this hypothesis for a Bernoulli product with nondegenerate coordinate
laws.
-/

open MeasureTheory ProbabilityTheory unitInterval Set
open scoped Classical ENNReal

namespace FK.BurtonKeane

open CurvatureVariance.Infra.Percolation

universe u
variable {ι : Type u}

/-- A finite set and a Boolean pattern on it. -/
abbrev PatchIndex (ι : Type u) := Σ F : Finset ι, (∀ _ : F, Bool)

/-- Configurations whose prescribed finite patch lands in `T`. -/
def patchable (T : Set (ι → Bool)) (j : PatchIndex ι) : Set (ι → Bool) :=
  (fun ω => Function.updateFinset ω j.1 j.2) ⁻¹' T

/-- The cylinder imposing a prescribed pattern on a finite set. -/
def forcedPattern (j : PatchIndex ι) : Set (ι → Bool) :=
  j.1.restrict ⁻¹' {j.2}

lemma measurable_patchable {T : Set (ι → Bool)} (hT : MeasurableSet T)
    (j : PatchIndex ι) : MeasurableSet (patchable T j) := by
  exact (measurable_updateFinset_left (x := j.2) hT)

lemma measurable_forcedPattern (j : PatchIndex ι) : MeasurableSet (forcedPattern j) := by
  exact j.1.measurable_restrict (measurableSet_singleton j.2)

lemma dependsOn_patchable_compl {T : Set (ι → Bool)} (j : PatchIndex ι) :
    DependsOn (· ∈ patchable T j) (j.1 : Set ι)ᶜ := by
  simpa only [patchable, compl_eq_univ_sdiff, Set.mem_preimage] using
    (dependsOn_univ (fun ω : ι → Bool => ω ∈ T)).updateFinset j.2

lemma dependsOn_forcedPattern (j : PatchIndex ι) :
    DependsOn (· ∈ forcedPattern j) (j.1 : Set ι) := by
  intro x y hxy
  have hr : j.1.restrict x = j.1.restrict y := funext fun i => hxy i.1 i.2
  simp only [forcedPattern, Set.mem_preimage, Set.mem_singleton_iff, hr]

lemma patch_of_mem_forcedPattern (j : PatchIndex ι) {ω : ι → Bool}
    (hω : ω ∈ forcedPattern j) : Function.updateFinset ω j.1 j.2 = ω := by
  have hr : j.1.restrict ω = j.2 := hω
  calc
    Function.updateFinset ω j.1 j.2 = Function.updateFinset ω j.1 (j.1.restrict ω) := by rw [hr]
    _ = ω := Function.updateFinset_restrict (s := j.1) ω

lemma patchable_inter_forcedPattern_subset {T : Set (ι → Bool)} (j : PatchIndex ι) :
    patchable (T := T) j ∩ forcedPattern j ⊆ T := by
  rintro ω ⟨hω, hforced⟩
  have heq := patch_of_mem_forcedPattern j hforced
  rw [← heq]
  exact hω

/-- Finite-pattern insertion tolerance, phrased on arbitrary exterior events.
For each finite patch `j`, a positive-measure event depending only on the
complement of its support retains positive measure when `j` is forced.  This
is the measure-level consequence of finite energy needed by countable patch
lifting; no independence or group invariance is built into the definition. -/
def FinitePatternInsertionTolerance (μ : Measure (ι → Bool)) : Prop :=
  ∀ (j : PatchIndex ι) (A : Set (ι → Bool)), MeasurableSet A →
    DependsOn (· ∈ A) (j.1 : Set ι)ᶜ → 0 < μ A →
      0 < μ (A ∩ forcedPattern j)

/-- Every finite Boolean cylinder has positive mass at an interior rate. -/
theorem measure_forcedPattern_pos (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (j : PatchIndex ι) : 0 < bernoulliProduct ι p (forcedPattern j) := by
  classical
  let t : ι → Set Bool := fun i => if hi : i ∈ j.1 then {j.2 ⟨i, hi⟩} else Set.univ
  have heq : forcedPattern j = (j.1 : Set ι).pi t := by
    ext ω
    change j.1.restrict ω = j.2 ↔ ∀ i ∈ j.1, ω i ∈ t i
    constructor
    · intro h i hi
      have hi' : ω i = j.2 ⟨i, hi⟩ := congrFun h ⟨i, hi⟩
      rw [show t i = {j.2 ⟨i, hi⟩} from by simp [t, hi]]
      exact hi'
    · intro h
      funext i
      have hi := h i.1 i.2
      rw [show t i.1 = {j.2 i} from by simp [t, i.2]] at hi
      exact hi
  rw [heq]
  change 0 < Measure.infinitePi (fun _ : ι => bernoulliMeasure true false p) ((j.1 : Set ι).pi t)
  rw [Measure.infinitePi_pi _ (fun i hi => by by_cases h : i ∈ j.1 <;> simp [t, h])]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  cases hb : j.2 ⟨i, hi⟩
  · simp only [t, hi, dite_eq_left, hb]
    rw [bernoulliMeasure_false]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp1)).ne'
  · simp only [t, hi, dite_eq_left, hb]
    rw [bernoulliMeasure_true]
    exact (ENNReal.ofReal_pos.mpr hp0).ne'

/-- **Countable finite-patch lifting under insertion tolerance.** -/
theorem measure_pos_of_forall_exists_patch_of_finitePatternInsertionTolerance
    [Countable ι] (μ : Measure (ι → Bool))
    (hμ : FinitePatternInsertionTolerance μ)
    {S T : Set (ι → Bool)} (hTmeas : MeasurableSet T)
    (hS : 0 < μ S)
    (hpatch : ∀ ω ∈ S, ∃ j : PatchIndex ι, Function.updateFinset ω j.1 j.2 ∈ T) :
    0 < μ T := by
  classical
  have hcover : S ⊆ ⋃ j : PatchIndex ι, patchable (T := T) j := by
    intro ω hω
    obtain ⟨j, hj⟩ := hpatch ω hω
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hunion : μ (⋃ j : PatchIndex ι, patchable (T := T) j) ≠ 0 := by
    intro hz
    have hnull : μ S = 0 := measure_mono_null hcover hz
    exact (ne_of_gt hS) hnull
  obtain ⟨j, hj⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  have hposInter := hμ j (patchable (T := T) j)
    (measurable_patchable hTmeas j) (dependsOn_patchable_compl j) hj
  exact lt_of_lt_of_le hposInter (measure_mono (patchable_inter_forcedPattern_subset j))

/-- A nondegenerate Bernoulli product has finite-pattern insertion tolerance.
The exterior event and the forced finite cylinder are independent. -/
theorem finitePatternInsertionTolerance_bernoulliProduct
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    FinitePatternInsertionTolerance (bernoulliProduct ι p) := by
  intro j A hA hAdep hApos
  have hind := measure_inter_eq_mul_of_dependsOn
    hA (measurable_forcedPattern j) hAdep (dependsOn_forcedPattern j)
    (by simpa using (disjoint_compl_left : Disjoint (j.1 : Set ι)ᶜ j.1)) p
  rw [hind]
  exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hApos)
    (ne_of_gt (measure_forcedPattern_pos p hp0 hp1 j)))

/-- Countable finite-patch lifting for Bernoulli percolation. -/
theorem measure_pos_of_forall_exists_patch [Countable ι]
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {S T : Set (ι → Bool)} (hTmeas : MeasurableSet T)
    (hS : 0 < bernoulliProduct ι p S)
    (hpatch : ∀ ω ∈ S, ∃ j : PatchIndex ι, Function.updateFinset ω j.1 j.2 ∈ T) :
    0 < bernoulliProduct ι p T := by
  exact measure_pos_of_forall_exists_patch_of_finitePatternInsertionTolerance
    (bernoulliProduct ι p)
    (finitePatternInsertionTolerance_bernoulliProduct p hp0 hp1)
    hTmeas hS hpatch
