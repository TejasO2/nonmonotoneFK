import FK.GibbsOrder
import FK.StageInstantiation

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace FK.InfiniteVolume

variable {E : Type*} [Countable E]

attribute [local instance] Classical.propDecidable Classical.decPred

open Set

/-! ### Pattern cylinders and upper corners -/

/-- The mass of an upper corner is the sum of the masses of the pattern cylinders
above it. -/
theorem measure_upT_eq_sum (ζ : ProbabilityMeasure (Configuration E)) (S : Finset E)
    (T : Finset ↥S) :
    (ζ : Measure (Configuration E)) (upT S T) =
      ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊆ U),
        (ζ : Measure (Configuration E)) (cyT S U) := by
  rw [upT_eq_biUnion,
    measure_biUnion_finset (pairwiseDisjoint_cyT S T) (fun U _ => measurableSet_cyT S U)]

theorem filter_subset_eq_insert (S : Finset E) (T : Finset ↥S) :
    Finset.univ.filter (fun U : Finset ↥S => T ⊆ U) =
      insert T (Finset.univ.filter (fun U : Finset ↥S => T ⊂ U)) := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hWU
    by_cases h : U = T
    · exact Or.inl h
    · exact Or.inr ⟨hWU, fun hUW => h (Finset.Subset.antisymm hUW hWU)⟩
  · rintro (rfl | ⟨hWU, -⟩)
    · exact le_refl _
    · exact hWU

theorem self_not_mem_filter_ssubset (S : Finset E) (T : Finset ↥S) :
    T ∉ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro h
  exact h.2 (le_refl T)

/-- Real-valued version of the upper-corner decomposition. -/
theorem real_upT_eq_add_sum (ζ : ProbabilityMeasure (Configuration E)) (S : Finset E)
    (T : Finset ↥S) :
    ((ζ : Measure (Configuration E)) (upT S T)).toReal =
      ((ζ : Measure (Configuration E)) (cyT S T)).toReal +
        ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
          ((ζ : Measure (Configuration E)) (cyT S U)).toReal := by
  have hfin : ∀ A : Set (Configuration E), (ζ : Measure (Configuration E)) A ≠ ∞ :=
    fun A => measure_ne_top _ A
  rw [measure_upT_eq_sum, filter_subset_eq_insert S T,
    Finset.sum_insert (self_not_mem_filter_ssubset S T),
    ENNReal.toReal_add (hfin _) (ENNReal.sum_ne_top.mpr (fun U _ => hfin _)),
    ENNReal.toReal_sum (fun U _ => hfin _)]

/-- The mass of a pattern cylinder is the upper-corner mass minus the masses of the
strictly larger patterns. -/
theorem real_cyT_eq (ζ : ProbabilityMeasure (Configuration E)) (S : Finset E)
    (T : Finset ↥S) :
    ((ζ : Measure (Configuration E)) (cyT S T)).toReal =
      ((ζ : Measure (Configuration E)) (upT S T)).toReal -
        ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
          ((ζ : Measure (Configuration E)) (cyT S U)).toReal := by
  have h := real_upT_eq_add_sum ζ S T
  linarith

/-- **Pattern-cylinder masses converge when upper-corner masses do.**  The pattern
masses are recovered from the upper corners by downward induction over the Boolean
lattice of patterns on a fixed finite coordinate set. -/
theorem tendsto_cyT_of_tendsto_upT
    (μ : ℕ → ProbabilityMeasure (Configuration E)) (φ : ProbabilityMeasure (Configuration E))
    (S : Finset E)
    (hup : ∀ T : Finset ↥S, Tendsto
      (fun n => ((μ n : Measure (Configuration E)) (upT S T)).toReal)
      atTop (𝓝 (((φ : Measure (Configuration E)) (upT S T)).toReal))) :
    ∀ T : Finset ↥S, Tendsto
      (fun n => ((μ n : Measure (Configuration E)) (cyT S T)).toReal)
      atTop (𝓝 (((φ : Measure (Configuration E)) (cyT S T)).toReal)) := by
  classical
  have key : ∀ k : ℕ, ∀ T : Finset ↥S, (Finset.univ \ T).card = k →
      Tendsto (fun n => ((μ n : Measure (Configuration E)) (cyT S T)).toReal)
        atTop (𝓝 (((φ : Measure (Configuration E)) (cyT S T)).toReal)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro T hk
      have hsumlim : Tendsto
          (fun n => ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
            ((μ n : Measure (Configuration E)) (cyT S U)).toReal) atTop
          (𝓝 (∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
            ((φ : Measure (Configuration E)) (cyT S U)).toReal)) := by
        apply tendsto_finsetSum
        intro U hU
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
        refine ih ((Finset.univ \ U).card) ?_ U rfl
        have hlt : (Finset.univ \ U).card < (Finset.univ \ T).card := by
          rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ]
          exact Nat.sub_lt_sub_left
            (lt_of_lt_of_le (Finset.card_lt_card hU) (Finset.card_le_univ U))
            (Finset.card_lt_card hU)
        rwa [hk] at hlt
      have hmain : Tendsto
          (fun n => ((μ n : Measure (Configuration E)) (upT S T)).toReal -
            ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
              ((μ n : Measure (Configuration E)) (cyT S U)).toReal) atTop
          (𝓝 (((φ : Measure (Configuration E)) (upT S T)).toReal -
            ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
              ((φ : Measure (Configuration E)) (cyT S U)).toReal)) :=
        (hup T).sub hsumlim
      have hgoalval : ((φ : Measure (Configuration E)) (cyT S T)).toReal =
          ((φ : Measure (Configuration E)) (upT S T)).toReal -
            ∑ U ∈ Finset.univ.filter (fun U : Finset ↥S => T ⊂ U),
              ((φ : Measure (Configuration E)) (cyT S U)).toReal :=
        real_cyT_eq φ S T
      rw [hgoalval]
      exact hmain.congr (fun n => (real_cyT_eq (μ n) S T).symm)
  exact fun T => key (Finset.univ \ T).card T rfl

/-! ### Finite-coordinate cylinders -/

/-- The finite-coordinate cylinder cut out by `A` on the coordinates `S`. -/
def cyl (S : Finset E) (A : Set (↥S → Bool)) : Set (Configuration E) :=
  S.restrict ⁻¹' A

/-- The cylinder of one pattern on a finite coordinate set. -/
def pat (S : Finset E) (w : ↥S → Bool) : Set (Configuration E) := S.restrict ⁻¹' {w}

lemma pat_eq_cyT (S : Finset E) (w : ↥S → Bool) :
    pat S w = cyT S (Finset.univ.filter (fun i : ↥S => w i = true)) := by
  ext ω
  simp only [pat, cyT, Set.mem_preimage, Set.mem_singleton_iff, Finset.restrict,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, funext_iff]
  constructor
  · intro h e
    rw [h e]
  · intro h e
    have hh := h e
    revert hh
    cases ω e <;> cases w e <;> simp

lemma measurableSet_pat (S : Finset E) (w : ↥S → Bool) : MeasurableSet (pat S w) :=
  (measurableSet_singleton w).preimage S.measurable_restrict

lemma dependsOn_cyl (S : Finset E) (A : Set (↥S → Bool)) :
    FKLimit.DependsOnCoordinates (cyl S A) S := by
  intro ω η h
  have hres : S.restrict ω = S.restrict η := by
    funext i
    exact h i.1 i.2
  simp only [cyl, Set.mem_preimage]
  rw [hres]

theorem measure_cyl_eq_sum (ζ : ProbabilityMeasure (Configuration E)) (S : Finset E)
    (A : Set (↥S → Bool)) :
    (ζ : Measure (Configuration E)) (cyl S A) =
      ∑ w ∈ Finset.univ.filter (fun w : ↥S → Bool => w ∈ A),
        (ζ : Measure (Configuration E)) (pat S w) := by
  have hA : (↑(Finset.univ.filter (fun w : ↥S → Bool => w ∈ A)) : Set (↥S → Bool)) = A := by
    ext w
    simp
  have h := MeasureTheory.sum_measure_preimage_singleton (μ := (ζ : Measure (Configuration E)))
    (f := (fun ω : Configuration E => S.restrict ω))
    (s := Finset.univ.filter (fun w : ↥S → Bool => w ∈ A))
    (fun y _ => measurableSet_pat S y)
  rw [hA] at h
  exact h.symm

theorem real_cyl_eq_sum (ζ : ProbabilityMeasure (Configuration E)) (S : Finset E)
    (A : Set (↥S → Bool)) :
    ((ζ : Measure (Configuration E)) (cyl S A)).toReal =
      ∑ w ∈ Finset.univ.filter (fun w : ↥S → Bool => w ∈ A),
        ((ζ : Measure (Configuration E)) (pat S w)).toReal := by
  rw [measure_cyl_eq_sum,
    ENNReal.toReal_sum (fun w _ => measure_ne_top _ _)]

/-- Cylinder masses converge once pattern masses do. -/
theorem tendsto_real_cyl_of_tendsto_cyT
    (μ : ℕ → ProbabilityMeasure (Configuration E)) (φ : ProbabilityMeasure (Configuration E))
    (S : Finset E)
    (hcyT : ∀ T : Finset ↥S, Tendsto
      (fun n => ((μ n : Measure (Configuration E)) (cyT S T)).toReal)
      atTop (𝓝 (((φ : Measure (Configuration E)) (cyT S T)).toReal)))
    (A : Set (↥S → Bool)) :
    Tendsto (fun n => ((μ n : Measure (Configuration E)) (cyl S A)).toReal)
      atTop (𝓝 (((φ : Measure (Configuration E)) (cyl S A)).toReal)) := by
  have hpat : ∀ w : ↥S → Bool, Tendsto
      (fun n => ((μ n : Measure (Configuration E)) (pat S w)).toReal) atTop
      (𝓝 (((φ : Measure (Configuration E)) (pat S w)).toReal)) := by
    intro w
    have h := hcyT (Finset.univ.filter (fun i : ↥S => w i = true))
    rwa [← pat_eq_cyT] at h
  have hsum : Tendsto
      (fun n => ∑ w ∈ Finset.univ.filter (fun w : ↥S → Bool => w ∈ A),
        ((μ n : Measure (Configuration E)) (pat S w)).toReal) atTop
      (𝓝 (∑ w ∈ Finset.univ.filter (fun w : ↥S → Bool => w ∈ A),
        ((φ : Measure (Configuration E)) (pat S w)).toReal)) :=
    tendsto_finsetSum _ (fun w _ => hpat w)
  have hfun : (fun n => ((μ n : Measure (Configuration E)) (cyl S A)).toReal)
      = fun n => ∑ w ∈ Finset.univ.filter (fun w : ↥S → Bool => w ∈ A),
          ((μ n : Measure (Configuration E)) (pat S w)).toReal := by
    funext n
    exact real_cyl_eq_sum (μ n) S A
  rw [hfun, real_cyl_eq_sum φ S A]
  exact hsum

/-! ### Closed sets as intersections of cylinders -/

/-- Coordinate stages of a fixed enumeration of `E`. -/
noncomputable def coordStage {E : Type*} (e : ℕ → E) (k : ℕ) : Finset E :=
  (Finset.range (k + 1)).image e

lemma coordStage_mono {e : ℕ → E} : Monotone (coordStage e) := by
  intro m n hmn
  exact Finset.image_subset_image (Finset.range_subset_range.mpr (Nat.succ_le_succ hmn))

lemma coordStage_subset_of_finite {e : ℕ → E} (he : Function.Surjective e) (S : Finset E) :
    ∃ k, S ⊆ coordStage e k := by
  classical
  choose g hg using fun s : S => he s.1
  refine ⟨Finset.univ.sup g, ?_⟩
  intro s hs
  have hgs : g ⟨s, hs⟩ ≤ Finset.univ.sup g := Finset.le_sup (Finset.mem_univ _)
  exact Finset.mem_image.mpr
    ⟨g ⟨s, hs⟩, Finset.mem_range.mpr (Nat.lt_succ_of_le hgs), hg ⟨s, hs⟩⟩

/-- The finite-coordinate approximation of a set of configurations. -/
noncomputable def cylApprox {E : Type*} (e : ℕ → E) (F : Set (E → Bool)) (k : ℕ) :
    Set (E → Bool) :=
  cyl (coordStage e k) ((coordStage e k).restrict '' F)

lemma cylApprox_anti {e : ℕ → E} {F : Set (Configuration E)} : Antitone (cylApprox e F) := by
  intro m n hmn x hx
  simp only [cylApprox, Set.mem_preimage, Set.mem_image] at hx ⊢
  obtain ⟨y, hyF, hyx⟩ := hx
  refine ⟨y, hyF, ?_⟩
  funext i
  have h2 := congrFun hyx ⟨i.1, coordStage_mono hmn i.2⟩
  simpa using h2

lemma measurableSet_cylApprox {e : ℕ → E} {F : Set (Configuration E)} (k : ℕ) :
    MeasurableSet (cylApprox e F k) :=
  (dependsOn_cyl (coordStage e k) _).measurableSet

lemma subset_cylApprox {e : ℕ → E} {F : Set (Configuration E)} (k : ℕ) :
    F ⊆ cylApprox e F k := by
  intro x hx
  exact ⟨x, hx, rfl⟩

/-- A closed set is the intersection of the cylinders obtained by restricting to an
exhausting sequence of finite coordinate sets. -/
theorem isClosed_eq_iInter_cylApprox {e : ℕ → E} (he : Function.Surjective e)
    {F : Set (Configuration E)} (hF : IsClosed F) :
    F = ⋂ k, cylApprox e F k := by
  classical
  refine Set.Subset.antisymm (fun x hx => Set.mem_iInter.mpr fun k => subset_cylApprox k hx) ?_
  intro x hx
  by_contra hxF
  have hopen : IsOpen Fᶜ := hF.isOpen_compl
  have hmem : x ∈ Fᶜ := by simpa using hxF
  rw [isOpen_pi_iff] at hopen
  obtain ⟨I, u, hu, hsub⟩ := hopen x hmem
  obtain ⟨k, hk⟩ := coordStage_subset_of_finite he I
  have hxl : (coordStage e k).restrict x ∈ (coordStage e k).restrict '' F :=
    Set.mem_iInter.mp hx k
  obtain ⟨y, hyF, hyx⟩ := hxl
  have hy : y ∈ Set.pi (↑I) u := by
    rw [Set.mem_pi]
    intro a ha
    have hak : a ∈ coordStage e k := hk ha
    have hya : y a = x a := by
      have h2 := congrFun hyx ⟨a, hak⟩
      simpa using h2
    rw [hya]
    exact (hu a ha).2
  exact hsub hy hyF

/-! ### Real masses -/

/-- Real-valued mass of a finite measure, as an abbreviation to keep statements small. -/
noncomputable def mreal {α : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α) : ℝ :=
  (μ A).toReal

lemma mreal_def {α : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α) :
    mreal μ A = (μ A).toReal := rfl

/-! ### Portmanteau passage from cylinder convergence to weak convergence -/

/-- **Closed-set limsup bound from finite-coordinate cylinder convergence.** -/
theorem limsup_real_le_of_isClosed
    (μ : ℕ → ProbabilityMeasure (Configuration E)) (φ : ProbabilityMeasure (Configuration E))
    (e : ℕ → E) (he : Function.Surjective e)
    (hcyl : ∀ (S : Finset E) (A : Set (↥S → Bool)), Tendsto
      (fun n => mreal (μ n : Measure (Configuration E)) (cyl S A)) atTop
      (𝓝 (mreal (φ : Measure (Configuration E)) (cyl S A))))
    {F : Set (Configuration E)} (hF : IsClosed F) :
    limsup (fun n => mreal (μ n : Measure (Configuration E)) F) atTop ≤
      mreal (φ : Measure (Configuration E)) F := by
  classical
  have hcyl' : ∀ (S : Finset E) (A : Set (↥S → Bool)), Tendsto
      (fun n => mreal (μ n : Measure (Configuration E)) (cyl S A)) atTop
      (𝓝 (mreal (φ : Measure (Configuration E)) (cyl S A))) := hcyl
  have hInter : ⋂ k, cylApprox e F k = F := (isClosed_eq_iInter_cylApprox he hF).symm
  have htend : Tendsto
      (fun k => mreal (φ : Measure (Configuration E)) (cylApprox e F k)) atTop
      (𝓝 (mreal (φ : Measure (Configuration E)) F)) := by
    have h1 : Tendsto (fun k => (φ : Measure (Configuration E)) (cylApprox e F k)) atTop
        (𝓝 ((φ : Measure (Configuration E)) (⋂ k, cylApprox e F k))) :=
      tendsto_measure_iInter_atTop (fun k => (measurableSet_cylApprox k).nullMeasurableSet)
        cylApprox_anti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at h1
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1
  have hbound : ∀ k, limsup
      (fun n => mreal (μ n : Measure (Configuration E)) F) atTop ≤
      mreal (φ : Measure (Configuration E)) (cylApprox e F k) := by
    intro k
    have hle : ∀ n, mreal (μ n : Measure (Configuration E)) F ≤
        mreal (μ n : Measure (Configuration E)) (cylApprox e F k) := fun n =>
      MeasureTheory.measureReal_mono (subset_cylApprox k)
    have hlim : Tendsto
        (fun n => mreal (μ n : Measure (Configuration E)) (cylApprox e F k)) atTop
        (𝓝 (mreal (φ : Measure (Configuration E)) (cylApprox e F k))) := by
      have h := hcyl' (coordStage e k) ((coordStage e k).restrict '' F)
      exact h
    have hbdd : ∀ n, (μ n : Measure (Configuration E)).real (cylApprox e F k) ≤ 1 := by
      intro n
      simpa using MeasureTheory.measureReal_mono (μ := (μ n : Measure (Configuration E)))
        (Set.subset_univ (cylApprox e F k))
    calc limsup (fun n => mreal (μ n : Measure (Configuration E)) F) atTop
        ≤ limsup (fun n => mreal (μ n : Measure (Configuration E)) (cylApprox e F k)) atTop :=
          limsup_le_limsup (u := fun n => mreal (μ n : Measure (Configuration E)) F)
            (v := fun n => mreal (μ n : Measure (Configuration E)) (cylApprox e F k))
            (Eventually.of_forall hle)
            (by
              refine ⟨0, fun b hb => ?_⟩
              rw [Filter.eventually_map] at hb
              have h0 : ∀ᶠ n in atTop,
                  0 ≤ mreal (μ n : Measure (Configuration E)) F :=
                Eventually.of_forall fun n => MeasureTheory.measureReal_nonneg
              obtain ⟨n, hn0, hnb⟩ := (h0.and hb).exists
              exact hn0.trans hnb)
            (by
              refine ⟨1, ?_⟩
              rw [Filter.eventually_map]
              exact Eventually.of_forall hbdd)
      _ = mreal (φ : Measure (Configuration E)) (cylApprox e F k) := hlim.limsup_eq
  exact ge_of_tendsto htend (Eventually.of_forall hbound)

/-- **Convergence of all finite-coordinate cylinder masses forces weak convergence.** -/
theorem tendsto_of_tendsto_cyl
    (μ : ℕ → ProbabilityMeasure (Configuration E)) (φ : ProbabilityMeasure (Configuration E))
    (hcyl : ∀ (S : Finset E) (A : Set (↥S → Bool)), Tendsto
      (fun n => mreal (μ n : Measure (Configuration E)) (cyl S A)) atTop
      (𝓝 (mreal (φ : Measure (Configuration E)) (cyl S A)))) :
    Tendsto μ atTop (𝓝 φ) := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · have hE' : IsEmpty E := hE
    haveI : IsEmpty E := hE'
    haveI : Unique (Configuration E) := Pi.uniqueOfIsEmpty _
    haveI : Subsingleton (ProbabilityMeasure (Configuration E)) := by
      refine ⟨fun a b => ?_⟩
      apply ProbabilityMeasure.toMeasure_injective
      ext A _
      rcases Set.eq_empty_or_nonempty A with h | ⟨x, hx⟩
      · rw [h, measure_empty, measure_empty]
      · have hAuniv : A = Set.univ := by
          ext y
          exact ⟨fun _ => trivial, fun _ => by rwa [Subsingleton.elim y x]⟩
        rw [hAuniv, measure_univ, measure_univ]
    exact tendsto_const_nhds.congr fun n => Subsingleton.elim φ (μ n)
  · haveI : Nonempty E := hE
    obtain ⟨e, he⟩ := exists_surjective_nat E
    have hclosed : ∀ F : Set (Configuration E), IsClosed F →
        limsup (fun n => (μ n : Measure (Configuration E)).real F) atTop ≤
          (φ : Measure (Configuration E)).real F :=
      fun F hF => limsup_real_le_of_isClosed μ φ e he hcyl hF
    exact tendsto_of_forall_isClosed_limsup_real_le' hclosed

/-- **Monotone (or merely convergent) upper-corner masses force weak convergence.** -/
theorem tendsto_of_tendsto_upT
    (μ : ℕ → ProbabilityMeasure (Configuration E)) (φ : ProbabilityMeasure (Configuration E))
    (hup : ∀ (S : Finset E) (T : Finset ↥S), Tendsto
      (fun n => mreal (μ n : Measure (Configuration E)) (upT S T)) atTop
      (𝓝 (mreal (φ : Measure (Configuration E)) (upT S T)))) :
    Tendsto μ atTop (𝓝 φ) := by
  refine tendsto_of_tendsto_cyl μ φ fun S A => ?_
  exact tendsto_real_cyl_of_tendsto_cyT μ φ S
    (tendsto_cyT_of_tendsto_upT μ φ S (hup S)) A

/-! ### Application: existence of FK weak limits from convergent upper corners -/

/-- The `ℝ≥0`-valued mass of a probability measure and the `ℝ≥0∞`-valued mass of its
underlying measure have the same real value. -/
lemma coe_fn_eq_toReal {E : Type*} (ζ : ProbabilityMeasure (Configuration E))
    (A : Set (Configuration E)) :
    ((ζ A : ℝ≥0) : ℝ) = ((ζ : Measure (Configuration E)) A).toReal := by
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact (ENNReal.coe_toReal (ζ A)).symm

/-- **Existence of an FK weak limit from convergent upper-corner masses.**  A
subsequence converges by compactness of the probability measures on the compact
configuration space, and the assumed convergence of all upper-corner masses
identifies the subsequential limit with the full-sequence limit. -/
theorem exists_isFKLimit_of_tendsto_upT
    (exh : BoxExhaustion E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (hup : ∀ (S : Finset E) (T : Finset ↥S), ∃ a : ℝ, Tendsto
      (fun n => mreal ((exh.box n).finiteVolumeLaw hq hp (α n) : Measure (Configuration E))
        (upT S T)) atTop (𝓝 a)) :
    ∃ φ : ProbabilityMeasure (Configuration E), IsFKLimit exh hq hp α φ := by
  classical
  obtain ⟨a, u, hu, hsub⟩ := CompactSpace.tendsto_subseq
    (fun n => (exh.box n).finiteVolumeLaw hq hp (α n))
  refine ⟨a, ?_⟩
  have hconv : ∀ (S : Finset E) (T : Finset ↥S), Tendsto
      (fun n => mreal ((exh.box n).finiteVolumeLaw hq hp (α n) : Measure (Configuration E))
        (upT S T)) atTop (𝓝 (mreal (a : Measure (Configuration E)) (upT S T))) := by
    intro S T
    obtain ⟨b, hb⟩ := hup S T
    have hcl : IsClopen (upT S T) := (dependsOn_upT S T).isClopen
    have hnn := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hsub hcl
    have hcoe : Tendsto
        (fun j => ((exh.box (u j)).finiteVolumeLaw hq hp (α (u j)) (upT S T) : ℝ)) atTop
        (𝓝 ((a (upT S T) : ℝ≥0) : ℝ)) :=
      (NNReal.continuous_coe.tendsto (a (upT S T))).comp hnn
    have hsubreal : Tendsto
        (fun j => mreal ((exh.box (u j)).finiteVolumeLaw hq hp (α (u j)) :
          Measure (Configuration E)) (upT S T)) atTop
        (𝓝 (mreal (a : Measure (Configuration E)) (upT S T))) := by
      rw [show ((a (upT S T) : ℝ≥0) : ℝ) = mreal (a : Measure (Configuration E)) (upT S T)
        from coe_fn_eq_toReal a (upT S T)] at hcoe
      exact hcoe.congr fun j => coe_fn_eq_toReal _ _
    have hlim : mreal (a : Measure (Configuration E)) (upT S T) = b :=
      tendsto_nhds_unique hsubreal (hb.comp hu.tendsto_atTop)
    rw [hlim]
    exact hb
  exact tendsto_of_tendsto_upT _ a hconv

/-! ### Monotone upper-corner masses -/

/-- Real masses of probability measures are at most one. -/
lemma mreal_le_one {E : Type*} (ζ : ProbabilityMeasure (Configuration E))
    (A : Set (Configuration E)) : mreal (ζ : Measure (Configuration E)) A ≤ 1 := by
  have h : (ζ : Measure (Configuration E)).real A ≤ 1 := by
    simpa using MeasureTheory.measureReal_mono (μ := (ζ : Measure (Configuration E)))
      (Set.subset_univ A)
  exact h

/-- A sequence that is monotone from some point on and bounded above converges. -/
lemma exists_tendsto_of_eventually_mono (u : ℕ → ℝ) :
    (∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m → u n ≤ u m) → (∀ n, u n ≤ 1) →
      ∃ a : ℝ, Tendsto u atTop (𝓝 a) := by
  rintro ⟨N, hmono⟩ hbdd
  have hmono' : Monotone (fun k : ℕ => u (k + N)) := by
    intro i j hij
    exact hmono (i + N) (j + N) (Nat.le_add_left N i) (Nat.add_le_add_right hij N)
  refine ⟨⨆ k, u (k + N), ?_⟩
  have h := tendsto_atTop_ciSup hmono' ⟨1, by rintro _ ⟨k, rfl⟩; exact hbdd _⟩
  have hiff := tendsto_add_atTop_iff_nat (f := u) (k := N) (l := 𝓝 (⨆ k, u (k + N)))
  exact hiff.mp h

/-- **Existence of an FK weak limit from eventually monotone upper-corner masses.** -/
theorem exists_isFKLimit_of_eventually_mono_upT
    (exh : BoxExhaustion E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (hmono : ∀ (S : Finset E) (T : Finset ↥S), ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
      mreal ((exh.box n).finiteVolumeLaw hq hp (α n) : Measure (Configuration E))
        (upT S T) ≤
      mreal ((exh.box m).finiteVolumeLaw hq hp (α m) : Measure (Configuration E))
        (upT S T)) :
    ∃ φ : ProbabilityMeasure (Configuration E), IsFKLimit exh hq hp α φ := by
  refine exists_isFKLimit_of_tendsto_upT exh hq hp α fun S T => ?_
  exact exists_tendsto_of_eventually_mono
    (fun n => mreal ((exh.box n).finiteVolumeLaw hq hp (α n) : Measure (Configuration E))
      (upT S T)) (hmono S T) (fun n => mreal_le_one _ _)

/-- **A covering fixed-vertex family is a genuine box exhaustion.** -/
def fixedVertexExhaustion {E V : Type} [Fintype V]
    (F : FK.InfiniteVolume.NoEscape.FixedVertexFamily E V) (hcov : ∀ e : E, ∃ n, e ∈ F.edges n) :
    BoxExhaustion E where
  box := F.box
  monotone := F.monotone
  covers := hcov




/-- **Existence of an FK weak limit from monotone upper-corner masses** (convenience
form of `exists_isFKLimit_of_eventually_mono_upT`). -/
theorem exists_isFKLimit_of_mono_upT
    (exh : BoxExhaustion E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (hmono : ∀ (S : Finset E) (T : Finset ↥S), Monotone
      (fun n => mreal ((exh.box n).finiteVolumeLaw hq hp (α n) : Measure (Configuration E))
        (upT S T))) :
    ∃ φ : ProbabilityMeasure (Configuration E), IsFKLimit exh hq hp α φ :=
  exists_isFKLimit_of_eventually_mono_upT exh hq hp α
    (fun S T => ⟨0, fun n m _ hnm => hmono S T hnm⟩)
