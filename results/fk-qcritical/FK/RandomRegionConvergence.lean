import FK.BackwardConditional
import FK.ClassicalCoupling
import FK.ReverseMartingale

/-!
# A net-indexed comparison for configuration-dependent exterior regions

The source's Theorem 5.1 comparison uses regions depending on an auxiliary
configuration, so the linear filtration supplied by a fixed exhaustion is not
directly available at coupled points.

This module proves the region-indexed comparison **modulo a named analytic
input**. For a measurable event `A`,
`HasNetExteriorConvergence μ A` means that, off one μ-null set, every exterior
conditional of `A` converges to `μ.real A` along the net of finite edge sets.
The hypothesis is not proved here. For tail-trivial laws it would follow from a
net reverse-martingale/upcrossing theorem, which remains to be formalized.

## What is proved

* **Region-uniform tail remainder.** The tower property and conditional-expectation
  contraction give an `L¹` tail estimate depending only on a finite threshold,
  with a two-region corollary. No tail-triviality or martingale input is needed.
* **Comparison.** A pointwise net limit gives convergence along each monotone
  cofinal family. The convergence-exceptional set pushes forward along either
  coupled marginal, after which eventual agreement at the coupled points and
  the bool-cylinder extension lemma give equality of the two probability laws.
  There is also a tower-only common-region-value version and a deterministic
  consistency check using the installed reverse-martingale theorem.
* **Sharpness of two shortcuts.** Section-null exceptional sets do not pass to
  an arbitrary coupling: a normalized Lebesgue diagonal shows this in a genuine
  probability space. A finite atomic example with counting measure illustrates
  why the naive per-atom Markov bound cannot replace a genuine net analysis.

The last construction uses counting measure and specifically exhibits an atom
with conditional value `1/2` at every point. It is not presented as a formal
probability-normalized counterexample to a general theorem or a proof that every
conditional value in that finite example is exactly `1/2`.

No net upcrossing theorem, Theorem 5.1 or Proposition 1.8(2) endpoint is claimed.
-/


open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FK

namespace RandomRegion

/-! ## A cofinal monotone exhaustion of a countable edge type -/

/-- Every countable type carries a monotone cofinal family of finite subsets. -/
theorem exists_monotone_cofinal_finsets (E : Type*) [Countable E] :
    ∃ S : ℕ → Finset E, Monotone S ∧ ∀ T : Finset E, ∃ n, T ⊆ S n := by
  classical
  rcases isEmpty_or_nonempty E with hE | hE
  · refine ⟨fun _ => ∅, monotone_const, fun T => ⟨0, ?_⟩⟩
    have hT : T = ∅ := Finset.eq_empty_of_isEmpty T
    simp [hT]
  · obtain ⟨f, hf⟩ := Set.Countable.exists_eq_range
      (s := (univ : Set E)) Set.countable_univ (Set.univ_nonempty)
    refine ⟨fun n => (Finset.range n).image f, ?_, ?_⟩
    · intro m n hmn
      exact Finset.image_subset_image (Finset.range_mono hmn)
    · intro T
      have hsub : ∀ t ∈ T, ∃ k, f k = t := by
        intro t _
        have : t ∈ Set.range f := by rw [← hf]; exact Set.mem_univ t
        exact this
      choose g hg using hsub
      set G : T → ℕ := fun x => g x.1 x.2 with hG
      refine ⟨(T.attach).sup G + 1, ?_⟩
      intro t ht
      refine Finset.mem_coe.mpr ?_
      refine Finset.mem_image.mpr ⟨G ⟨t, ht⟩, ?_, ?_⟩
      · simp only [Finset.mem_range]
        have hle : G ⟨t, ht⟩ ≤ (T.attach).sup G :=
          Finset.le_sup (f := G) (Finset.mem_attach T ⟨t, ht⟩)
        omega
      · rw [hG]
        exact hg t ht

end RandomRegion

end FK

namespace FK

namespace RandomRegion

open FKLimit

variable {E : Type*} [Countable E]

/-! ## Region-uniform closeness of exterior conditionals to the tail

The reverse martingale for the exterior filtration is normally stated along one
fixed increasing sequence of edge sets.  Theorem 5.1 of the source instead uses
a family of regions that depends on the configuration of a dominating law, so
one needs a bound that is *uniform over the region*.  The two lemmas below give
it, with no martingale convergence involved: the tower property says that
shrinking the exterior sigma-algebra is a projection, and `L¹` contractivity of
conditional expectation then makes the distance to the tail conditional
expectation monotone.
-/

/-- **Region monotonicity.**  Enlarging the excluded edge set shrinks the
exterior sigma-algebra and can only increase the `L¹` distance between the
exterior conditional probability and the tail conditional probability.  This
is the tower property plus `L¹` contractivity; it is not a martingale
convergence statement. -/
theorem eLpNorm_condExp_outside_sub_le (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ] {A : Set (Configuration E)} (hA : MeasurableSet A)
    {K S : Finset E} (hKS : K ⊆ S) :
    eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) 1 μ ≤
      eLpNorm (μ⟦A | outsideSigma K⟧ - μ⟦A | tailSigma⟧) 1 μ := by
  have hmK : outsideSigma K ≤ (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    outsideSigma_le K
  have hmS : outsideSigma S ≤ (MeasurableSpace.pi : MeasurableSpace (Configuration E)) :=
    outsideSigma_le S
  have htailS : tailSigma (E := E) ≤ outsideSigma S := tailSigma_le_outsideSigma S
  have hle : outsideSigma S ≤ outsideSigma K := outsideSigma_anti hKS
  -- tower: the `S`-conditional probability is the `K`-conditional probability, re-projected
  have htower : μ⟦A | outsideSigma S⟧ =ᵐ[μ] μ[μ⟦A | outsideSigma K⟧ | outsideSigma S] :=
    (condExp_condExp_of_le (m₁ := outsideSigma S) (m₂ := outsideSigma K) hle hmK (f := A.indicator
      (fun _ => (1 : ℝ)))).symm
  -- the tail conditional is `S`-measurable, hence its own re-projection
  have htailfix : μ[μ⟦A | tailSigma⟧ | outsideSigma S] = μ⟦A | tailSigma⟧ :=
    condExp_of_stronglyMeasurable (m := outsideSigma S)
      (m₀ := (MeasurableSpace.pi : MeasurableSpace (Configuration E))) hmS
      ((stronglyMeasurable_condExp (m := tailSigma (E := E))
        (μ := μ) (f := A.indicator fun _ => (1 : ℝ))).mono htailS)
      (integrable_condExp (m := tailSigma (E := E)))
  have htailfix' : μ⟦A | tailSigma⟧ =ᵐ[μ]
      μ[μ⟦A | tailSigma⟧ | outsideSigma S] := Filter.EventuallyEq.of_eq htailfix.symm
  have hsub : (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) =ᵐ[μ]
      μ[(μ⟦A | outsideSigma K⟧ - μ⟦A | tailSigma⟧) | outsideSigma S] := by
    have h1 := condExp_sub (m := outsideSigma S)
      (f := μ⟦A | outsideSigma K⟧) (g := μ⟦A | tailSigma⟧)
      (integrable_condExp (m := outsideSigma K)) (integrable_condExp (m := tailSigma (E := E)))
    filter_upwards [htower, htailfix', h1] with ω hω1 hω2 hω3
    simp only [Pi.sub_apply]
    rw [hω1, hω2, hω3, Pi.sub_apply]
  calc eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) 1 μ
      = eLpNorm (μ[(μ⟦A | outsideSigma K⟧ - μ⟦A | tailSigma⟧) | outsideSigma S]) 1 μ :=
        eLpNorm_congr_ae hsub
    _ ≤ eLpNorm (μ⟦A | outsideSigma K⟧ - μ⟦A | tailSigma⟧) 1 μ :=
        eLpNorm_condExp_le_eLpNorm _ le_rfl

/-- **Region-uniform tail remainder.**  For every `ε > 0` there is a single
finite edge set `K` such that the exterior conditional probability of `A` is
within `ε` of its tail conditional probability in `L¹` for *every* finite edge
set containing `K`.  In particular the accuracy of the exterior conditional
probability is decided by the region once it exhausts `K`, uniformly in the
region — which is what the configuration-dependent regions of Theorem 5.1
require. -/
theorem exists_finset_eLpNorm_condExp_outside_to_tail_le
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    {A : Set (Configuration E)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
      eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) 1 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨Lam, hmono, hcof⟩ := exists_monotone_cofinal_finsets E
  have htend := tendsto_eLpNorm_one_condExp_indicator_outside_to_tail (μ := μ) Lam hmono hcof hA
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  obtain ⟨N, hN⟩ := (htend.eventually (Iio_mem_nhds hpos)).exists
  refine ⟨Lam N, fun S hS => ?_⟩
  exact (eLpNorm_condExp_outside_sub_le μ hA hS).trans hN.le

end RandomRegion

end FK

namespace FK

namespace RandomRegion

open FKLimit

variable {E : Type*} [Countable E]

/-! ## The final comparison step of Theorem 5.1

The two statements below are the deduction the source performs at the end of the
proof of Theorem 5.1: two laws whose exterior conditional probabilities agree
along the family of regions cut out by a typical configuration of the
dominating measure coincide.

The first form is the source's own: the two conditionals are compared at the
coupled points `X z`, `Y z` of a common auxiliary space, their limits are the
unconditional masses, and eventual agreement identifies the two limits.  This
is the part of the source's argument that needs *no* DLR, extremality,
tail-triviality or Choquet input: it is pure pointwise logic on a full-measure
set.

The second form is the consequence once the common limit is identified: if both
laws have the *deterministic* value `c n z` as their exterior conditional
almost everywhere at some region, the two masses agree outright.  This is the
form in which the source uses "`μᵢ(·|F_{Sₙ(ω₃)^c})(ωᵢ)` is the free random
cluster measure on `Sₙ(ω₃)`": the value depends on the region only.
-/

/-- **Agreement at coupled points identifies the masses.**  If two exterior
conditional probability sequences, evaluated at the coupled configurations and
along a common configuration-dependent region family, both converge to the
respective unconditional masses and agree eventually, then the masses agree. -/
theorem real_eq_real_of_eventual_regionAgreement
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {X Y : Θ → Configuration E}
    (S : ℕ → Θ → Finset E)
    {A : Set (Configuration E)}
    (hconvμ : ∀ᵐ z ∂ρ, Tendsto
      (fun n => (((μ : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (X z)))
      atTop (𝓝 ((μ : Measure (Configuration E)).real A)))
    (hconvν : ∀ᵐ z ∂ρ, Tendsto
      (fun n => (((ν : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (Y z)))
      atTop (𝓝 ((ν : Measure (Configuration E)).real A)))
    (hagree : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      (((μ : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (X z)) =
        (((ν : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (Y z))) :
    (μ : Measure (Configuration E)).real A = (ν : Measure (Configuration E)).real A := by
  obtain ⟨z, hzμ, hzν, hza⟩ := (hconvμ.and (hconvν.and hagree)).exists
  have hsym : (fun n => (((ν : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (Y z)))
      =ᶠ[atTop]
      (fun n => (((μ : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (X z))) := by
    filter_upwards [hza] with n hn
    exact hn.symm
  exact tendsto_nhds_unique hzμ (Tendsto.congr' hsym hzν)

/-- **A common deterministic exterior conditional value identifies the laws.**
If for almost every region of a configuration-dependent family both laws have
the same real number as their exterior conditional probability of `A` on a set
of full measure, then the two masses of `A` agree.  Only the tower property is
used: no convergence, extremality, tail triviality or Choquet input. -/
theorem real_eq_real_of_common_regionValue
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    (S : ℕ → Θ → Finset E) (c : ℕ → Θ → ℝ)
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hμ : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      ((μ : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) =ᵐ[(μ : Measure (Configuration E))]
        fun _ => c n z)
    (hν : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      ((ν : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) =ᵐ[(ν : Measure (Configuration E))]
        fun _ => c n z) :
    (μ : Measure (Configuration E)).real A = (ν : Measure (Configuration E)).real A := by
  obtain ⟨z, hzμ, hzν⟩ := (hμ.and hν).exists
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hzμ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hzν
  have hmass : ∀ (η : ProbabilityMeasure (Configuration E)) (m : ℕ),
      ((η : Measure (Configuration E))⟦A | outsideSigma (S m z)⟧) =ᵐ[(η : Measure (Configuration E))]
        (fun _ => c m z) →
      (η : Measure (Configuration E)).real A = c m z := by
    intro η m heq
    haveI : SigmaFinite ((η : Measure (Configuration E)).trim (outsideSigma_le (S m z))) :=
      inferInstance
    have htower := integral_condExp (μ := (η : Measure (Configuration E)))
      (m := outsideSigma (S m z)) (m₀ := (MeasurableSpace.pi : MeasurableSpace (Configuration E)))
      (outsideSigma_le (S m z)) (f := A.indicator fun _ => (1 : ℝ))
    have hconst : ∫ x, c m z ∂(η : Measure (Configuration E)) = c m z := by
      rw [integral_const, MeasureTheory.probReal_univ, one_smul]
    have hind : ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂(η : Measure (Configuration E)) =
        (η : Measure (Configuration E)).real A := by
      rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hind, ← htower, integral_congr_ae heq, hconst]
  refine (hmass μ (max N₁ N₂) (hN₁ (max N₁ N₂) (le_max_left _ _))).trans ?_
  exact (hmass ν (max N₁ N₂) (hN₂ (max N₁ N₂) (le_max_right _ _))).symm

end RandomRegion

end FK

namespace FK

namespace RandomRegion

open FKLimit

variable {E : Type*} [Countable E]

/-- Finite-base cylinders on Boolean configurations are measurable. -/
theorem cylinder_measurable {ι : Type*} (I : Finset ι)
    (S₀ : Set (↑I → Bool)) : MeasurableSet (cylinder (α := fun _ => Bool) I S₀) := by
  have hm : Measurable (fun (ω : ι → Bool) => (fun i : ↑I => ω i)) :=
    Measurable.of_eval (fun i => measurable_pi_apply (i : ι))
  exact hm ((Set.toFinite S₀).measurableSet)

/-- Masses are identified by their real values on a measurable set. -/
theorem measure_eq_of_real_eq {μ ν : ProbabilityMeasure (Configuration E)}
    {A : Set (Configuration E)}
    (h : (μ : Measure (Configuration E)).real A = (ν : Measure (Configuration E)).real A) :
    (μ : Measure (Configuration E)) A = (ν : Measure (Configuration E)) A := by
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ : Measure (Configuration E)) A)
    (measure_ne_top (ν : Measure (Configuration E)) A)]
  exact h

/-- **Theorem 5.1 final deduction, measure form.**  Two probability measures on
edge configurations agree as soon as, for every finite-base cylinder and along
one common configuration-dependent region family, their exterior conditional
probabilities agree eventually at the coupled points of a joint realisation and
converge to the respective unconditional masses.  No exhaustion, DLR equation,
extremality, tail triviality or Choquet decomposition is used. -/
theorem measure_eq_of_eventual_regionAgreement
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {X Y : Θ → Configuration E}
    (S : ℕ → Θ → Finset E)
    (hconvμ : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, Tendsto
      (fun n => (((μ : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀ | outsideSigma (S n z)⟧) (X z)))
      atTop (𝓝 ((μ : Measure (Configuration E)).real (cylinder (α := fun _ => Bool) I S₀))))
    (hconvν : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, Tendsto
      (fun n => (((ν : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀ | outsideSigma (S n z)⟧) (Y z)))
      atTop (𝓝 ((ν : Measure (Configuration E)).real (cylinder (α := fun _ => Bool) I S₀))))
    (hagree : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      (((μ : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀ | outsideSigma (S n z)⟧) (X z)) =
        (((ν : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀ | outsideSigma (S n z)⟧) (Y z))) :
    (μ : Measure (Configuration E)) = (ν : Measure (Configuration E)) := by
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S₀
  exact measure_eq_of_real_eq
    (real_eq_real_of_eventual_regionAgreement (E := E) μ ν S (A := cylinder (α := fun _ => Bool) I S₀)
      (hconvμ I S₀) (hconvν I S₀) (hagree I S₀))

/-- **Theorem 5.1 final deduction, common deterministic region value.**  Two
probability measures on edge configurations agree as soon as, for every
finite-base cylinder, both have the *same real number* as exterior conditional
probability at some region of one common configuration-dependent family, on a
set of full measure.  Only the tower property is used. -/
theorem measure_eq_of_common_regionValue
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    (S : ℕ → Θ → Finset E) (c : ℕ → Θ → ℝ)
    (hμ : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      ((μ : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀ | outsideSigma (S n z)⟧)
        =ᵐ[(μ : Measure (Configuration E))] fun _ => c n z)
    (hν : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      ((ν : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀ | outsideSigma (S n z)⟧)
        =ᵐ[(ν : Measure (Configuration E))] fun _ => c n z) :
    (μ : Measure (Configuration E)) = (ν : Measure (Configuration E)) := by
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S₀
  exact measure_eq_of_real_eq
    (real_eq_real_of_common_regionValue (E := E) μ ν S c (cylinder_measurable I S₀)
      (hμ I S₀) (hν I S₀))

end RandomRegion

end FK

namespace FK

namespace RandomRegion

open FKLimit

variable {E : Type*} [Countable E]

/-- **Consistency check: the deterministic exhaustion case.**  Along a fixed
cofinal family of edge sets the convergence hypothesis of
`real_eq_real_of_eventual_regionAgreement` is not an extra input: tail
triviality makes the exterior conditional probabilities converge to the
unconditional mass, by the reverse martingale of `FK.ReverseMartingale`.  So the
main comparison theorem has satisfiable hypotheses and strictly generalizes the
fixed-exhaustion comparison. -/
theorem real_eq_real_of_deterministic_regionAgreement
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {Λ : ℕ → Finset E} (hmono : Monotone Λ) (hcof : ∀ T : Finset E, ∃ n, T ⊆ Λ n)
    {X Y : Θ → FKLimit.Configuration E} (hX : Measurable X) (hY : Measurable Y)
    (hXμ : Measure.map X ρ = (μ : Measure (Configuration E)))
    (hYν : Measure.map Y ρ = (ν : Measure (Configuration E)))
    (htailμ : ZeroOneOn tailSigma (μ : Measure (Configuration E)))
    (htailν : ZeroOneOn tailSigma (ν : Measure (Configuration E)))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hagree : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      (((μ : Measure (Configuration E))⟦A | outsideSigma (Λ n)⟧) (X z)) =
        (((ν : Measure (Configuration E))⟦A | outsideSigma (Λ n)⟧) (Y z))) :
    (μ : Measure (Configuration E)).real A = (ν : Measure (Configuration E)).real A := by
  have hconv : ∀ (η : ProbabilityMeasure (Configuration E)), ZeroOneOn tailSigma
      (η : Measure (Configuration E)) →
      (Z : Θ → Configuration E) → Measurable Z →
      Measure.map Z ρ = (η : Measure (Configuration E)) →
      ∀ᵐ z ∂ρ, Tendsto
        (fun n => (((η : Measure (Configuration E))⟦A | outsideSigma (Λ n)⟧) (Z z)))
        atTop (𝓝 ((η : Measure (Configuration E)).real A)) := by
    intro η htail Z hZ hZη
    have hae := tendsto_ae_condExp_indicator_outside_to_real_of_zeroOneOn
      (μ := (η : Measure (Configuration E))) Λ hmono hcof hA htail
    exact (Measure.tendsto_ae_map (μ := ρ) hZ.aemeasurable).eventually (by rwa [hZη])
  exact real_eq_real_of_eventual_regionAgreement μ ν (fun n _ => Λ n)
    (hconv μ htailμ X hX hXμ) (hconv ν htailν Y hY hYν) hagree

end RandomRegion

end FK

namespace FK.RandomRegion

/-- **Consistency check at the level of measures.**  Along a fixed cofinal
family of edge sets, tail triviality supplies the convergence input, so the
comparison holds for every pair of tail-trivial laws whose exterior conditional
probabilities agree eventually at the coupled points of a common realisation.
This is the fixed-exhaustion form in which the source's Theorem 5.1 argument is
usually stated, recovered here as an instance of the configuration-dependent
comparison. -/
theorem measure_eq_of_deterministic_regionAgreement
    {E : Type*} [Countable E] {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (FKLimit.Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {Λ : ℕ → Finset E} (hmono : Monotone Λ) (hcof : ∀ T : Finset E, ∃ n, T ⊆ Λ n)
    {X Y : Θ → FKLimit.Configuration E} (hX : Measurable X) (hY : Measurable Y)
    (hXμ : Measure.map X ρ = (μ : Measure (FKLimit.Configuration E)))
    (hYν : Measure.map Y ρ = (ν : Measure (FKLimit.Configuration E)))
    (htailμ : FK.ZeroOneOn FKLimit.tailSigma (μ : Measure (FKLimit.Configuration E)))
    (htailν : FK.ZeroOneOn FKLimit.tailSigma (ν : Measure (FKLimit.Configuration E)))
    (hagree : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      (((μ : Measure (FKLimit.Configuration E))⟦cylinder (α := fun _ => Bool) I S₀
          | FKLimit.outsideSigma (Λ n)⟧) (X z)) =
        (((ν : Measure (FKLimit.Configuration E))⟦cylinder (α := fun _ => Bool) I S₀
          | FKLimit.outsideSigma (Λ n)⟧) (Y z))) :
    (μ : Measure (FKLimit.Configuration E)) = (ν : Measure (FKLimit.Configuration E)) := by
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S₀
  exact FK.RandomRegion.measure_eq_of_real_eq
    (FK.RandomRegion.real_eq_real_of_deterministic_regionAgreement (E := E) μ ν
      hmono hcof hX hY hXμ hYν htailμ htailν
      (FK.RandomRegion.cylinder_measurable I S₀) (hagree I S₀))

end FK.RandomRegion

#print axioms FK.RandomRegion.exists_monotone_cofinal_finsets
#print axioms FK.RandomRegion.eLpNorm_condExp_outside_sub_le
#print axioms FK.RandomRegion.exists_finset_eLpNorm_condExp_outside_to_tail_le
#print axioms FK.RandomRegion.real_eq_real_of_eventual_regionAgreement
#print axioms FK.RandomRegion.real_eq_real_of_common_regionValue
#print axioms FK.RandomRegion.cylinder_measurable
#print axioms FK.RandomRegion.measure_eq_of_real_eq
#print axioms FK.RandomRegion.measure_eq_of_eventual_regionAgreement
#print axioms FK.RandomRegion.measure_eq_of_common_regionValue
#print axioms FK.RandomRegion.real_eq_real_of_deterministic_regionAgreement

namespace FK

namespace RandomRegion

/-! ## A precise obstruction to one inference in the source argument

Theorem 5.1 of the source compares the two exterior conditional probabilities at
the *coupled* points `ω₁, ω₂` of an ordered triple coupling.  The convergence of
those conditionals along the exhaustion read off a typical `ω₃` is normally
justified by a backward martingale: for each fixed exhaustion the exceptional
set of configurations is null.  Passing from "every section is null" to
"the exceptional set is null under the coupling" is, however, *not* a
formal consequence of the marginals: a measurable set all of whose vertical
sections are null can still carry the whole mass of a coupling with those
marginals (the diagonal coupling below).  Any proof of Theorem 5.1 therefore
needs a genuine input at this point — measurability of the region selection
together with either absolute continuity of the conditional fibres or a maximal
inequality over the directed net of exterior sigma-algebras.

This is why the comparison theorems of this file take the coupled-point
convergence as an explicit hypothesis rather than deriving it from the
per-exhaustion martingale.
-/

/-- **Section-null does not imply coupling-null**, on a genuine probability space.
There are a probability measure `μ` on `ℝ` and a measurable set `E ⊆ ℝ × ℝ` whose
vertical sections are all `μ`-null — so `μ.prod μ E = 0` — while the diagonal
coupling `x ↦ (x, x)`, whose two marginals are both `μ`, puts mass `1` on `E`.

So a.e. statements about the sections of a jointly measurable exceptional set do
not transfer to the points of a coupling with the same marginals.  Any proof
which needs convergence at *coupled* points has to argue for it; it is not a
consequence of the marginals. -/
theorem exists_probability_nullSections_fullDiagonal :
    ∃ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ) (E : Set (ℝ × ℝ)),
      MeasurableSet E ∧
      (∀ x : ℝ, μ {y : ℝ | (x, y) ∈ E} = 0) ∧
      (μ.prod μ) E = 0 ∧
      (μ.map (fun x : ℝ => (x, x))) E = 1 := by
  classical
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun (f := Prod.fst) (g := Prod.snd) measurable_fst measurable_snd
  have hsing : ∀ x : ℝ, (volume.restrict (Set.Icc 0 1)) {x} = 0 := by
    intro x
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null (Set.inter_subset_left) Real.volume_singleton
  refine ⟨volume.restrict (Set.Icc 0 1), ⟨?_⟩, {p : ℝ × ℝ | p.1 = p.2}, hdiag, ?_, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  · intro x
    have hsub : {y : ℝ | (x, y) ∈ {p : ℝ × ℝ | p.1 = p.2}} ⊆ {x} := by
      intro y hy
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact hy.symm
    exact measure_mono_null hsub (hsing x)
  · have hsec : ∀ x : ℝ,
        (volume.restrict (Set.Icc 0 1)) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
      intro x
      have hsub : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} ⊆ {x} := by
        intro y hy
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hy ⊢
        exact hy.symm
      exact measure_mono_null hsub (hsing x)
    rw [Measure.prod_apply hdiag]
    simp only [hsec]
    simp
  · have hpre : (fun x : ℝ => (x, x)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = Set.univ := by
      ext x; simp
    have hmap := Measure.map_apply (μ := volume.restrict (Set.Icc 0 1))
      (f := fun x : ℝ => (x, x)) (measurable_id.prodMk measurable_id) hdiag
    rw [hmap, hpre]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num

#print axioms FK.RandomRegion.exists_probability_nullSections_fullDiagonal

end RandomRegion

end FK

namespace FK

namespace RandomRegion

open FKLimit

variable {E : Type*} [Countable E]

/-- **The choice of region does not matter once it contains `K`.**  Two finite
edge sets both containing the uniform threshold give exterior conditional
probabilities within `2ε` in `L¹`.  This is what licenses comparing two laws
along two *different* (in particular configuration-dependent) exhaustions of the
same configuration: the region only has to be large enough, uniformly. -/
theorem eLpNorm_condExp_outside_sub_le_two_regions (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ] {A : Set (Configuration E)} (hA : MeasurableSet A)
    {K : Finset E} {ε : ℝ} (hε : 0 ≤ ε)
    (hK : ∀ S : Finset E, K ⊆ S →
      eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) 1 μ ≤ ENNReal.ofReal ε)
    {S S' : Finset E} (hS : K ⊆ S) (hS' : K ⊆ S') :
    eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | outsideSigma S'⟧) 1 μ
      ≤ ENNReal.ofReal (2 * ε) := by
  have hsplit : (μ⟦A | outsideSigma S⟧ - μ⟦A | outsideSigma S'⟧) =ᵐ[μ]
      ((μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) +
        (μ⟦A | tailSigma⟧ - μ⟦A | outsideSigma S'⟧)) := by
    filter_upwards [] with ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  calc eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | outsideSigma S'⟧) 1 μ
      = eLpNorm ((μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) +
          (μ⟦A | tailSigma⟧ - μ⟦A | outsideSigma S'⟧)) 1 μ := eLpNorm_congr_ae hsplit
    _ ≤ eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) 1 μ +
          eLpNorm (μ⟦A | tailSigma⟧ - μ⟦A | outsideSigma S'⟧) 1 μ :=
        eLpNorm_add_le (by norm_num)
    _ = eLpNorm (μ⟦A | outsideSigma S⟧ - μ⟦A | tailSigma⟧) 1 μ +
          eLpNorm (μ⟦A | outsideSigma S'⟧ - μ⟦A | tailSigma⟧) 1 μ := by
        have hneg : (μ⟦A | tailSigma⟧ - μ⟦A | outsideSigma S'⟧)
            = -(μ⟦A | outsideSigma S'⟧ - μ⟦A | tailSigma⟧) := by
          funext ω
          simp only [Pi.sub_apply, Pi.neg_apply]
          ring
        rw [hneg, eLpNorm_neg]
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add (hK S hS) (hK S' hS')
    _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε hε]
        ring

end RandomRegion

end FK

#print axioms FK.RandomRegion.eLpNorm_condExp_outside_sub_le_two_regions

namespace FK

namespace RandomRegion

open FKLimit

variable {E : Type*} [Countable E]

/-! ## The comparison step at the level of the exterior net

The analytic input of the comparison is stated here in a form that mentions only
`μ` and the event `A`: off one null set, the exterior conditional probability
converges along the *net* of all finite edge sets.  This is exactly the
conclusion of the reverse-martingale theorem for the directed family of exterior
σ-algebras, and it is independent of whichever random exhaustion the coupling
happens to select. -/

/-- Off one `μ`-null set, the exterior conditional probability of `A` converges
along the net of finite edge sets to the unconditional mass.  Equivalently, one
null set serves every monotone cofinal family simultaneously (see
`tendsto_of_net_exterior`). -/
def HasNetExteriorConvergence (μ : Measure (Configuration E))
    (A : Set (Configuration E)) : Prop :=
  ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
    |(μ⟦A | outsideSigma S⟧) ω - μ.real A| ≤ ε

/-- A pointwise net limit gives convergence along every monotone cofinal family.
This is the only place where the random family is used: the net statement is a
property of the single configuration at which the conditional probability is
evaluated, so it serves all families at once. -/
theorem tendsto_of_net_exterior {g : Finset E → ℝ} {L : ℝ}
    (h : ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S → |g S - L| ≤ ε)
    (σ : ℕ → Finset E) (hmono : Monotone σ) (hcof : ∀ T : Finset E, ∃ n, T ⊆ σ n) :
    Tendsto (fun n => g (σ n)) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := hcof K
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have := hK (σ n) (Subset.trans hN (hmono hn))
  linarith

/-- **The comparison step with a null-set net hypothesis.**  Two probability
measures whose exterior conditional probabilities of `A` converge along the net
off their own null sets agree on `A`, provided the random region family is
almost surely monotone and cofinal and the coupled points eventually agree.
Neither the region family nor the coupling appears in the analytic hypothesis. -/
theorem real_eq_real_of_netExteriorConvergence
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {X Y : Θ → Configuration E} (hX : Measurable X) (hY : Measurable Y)
    (hXμ : Measure.map X ρ = (μ : Measure (Configuration E)))
    (hYν : Measure.map Y ρ = (ν : Measure (Configuration E)))
    (S : ℕ → Θ → Finset E)
    (hmono : ∀ᵐ z ∂ρ, Monotone fun n => S n z)
    (hcof : ∀ᵐ z ∂ρ, ∀ T : Finset E, ∃ n, T ⊆ S n z)
    {A : Set (Configuration E)}
    (hμnet : HasNetExteriorConvergence (μ : Measure (Configuration E)) A)
    (hνnet : HasNetExteriorConvergence (ν : Measure (Configuration E)) A)
    (hagree : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      (((μ : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (X z)) =
        (((ν : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (Y z))) :
    (μ : Measure (Configuration E)).real A = (ν : Measure (Configuration E)).real A := by
  have htrans : ∀ (η : ProbabilityMeasure (Configuration E)) (Z : Θ → Configuration E),
      Measurable Z → Measure.map Z ρ = (η : Measure (Configuration E)) →
      HasNetExteriorConvergence (η : Measure (Configuration E)) A →
      ∀ᵐ z ∂ρ, ∀ ε > 0, ∃ K : Finset E, ∀ S : Finset E, K ⊆ S →
        |((η : Measure (Configuration E))⟦A | outsideSigma S⟧) (Z z) -
          (η : Measure (Configuration E)).real A| ≤ ε := by
    intro η Z hZ hZη hnet
    exact (Measure.tendsto_ae_map (μ := ρ) hZ.aemeasurable).eventually (by rwa [hZη])
  have hconvμ : ∀ᵐ z ∂ρ, Tendsto
      (fun n => (((μ : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (X z)))
      atTop (𝓝 ((μ : Measure (Configuration E)).real A)) := by
    filter_upwards [htrans μ X hX hXμ hμnet, hmono, hcof] with z hz hm hc
    exact tendsto_of_net_exterior hz (fun n => S n z) hm hc
  have hconvν : ∀ᵐ z ∂ρ, Tendsto
      (fun n => (((ν : Measure (Configuration E))⟦A | outsideSigma (S n z)⟧) (Y z)))
      atTop (𝓝 ((ν : Measure (Configuration E)).real A)) := by
    filter_upwards [htrans ν Y hY hYν hνnet, hmono, hcof] with z hz hm hc
    exact tendsto_of_net_exterior hz (fun n => S n z) hm hc
  exact real_eq_real_of_eventual_regionAgreement μ ν S hconvμ hconvν hagree

/-- **Measure form** of the net comparison: it suffices to know the net
convergence of the exterior conditional probabilities of every finite-base
cylinder, for both laws. -/
theorem measure_eq_of_netExteriorConvergence
    {Θ : Type*} [MeasurableSpace Θ]
    (μ ν : ProbabilityMeasure (Configuration E))
    {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {X Y : Θ → Configuration E} (hX : Measurable X) (hY : Measurable Y)
    (hXμ : Measure.map X ρ = (μ : Measure (Configuration E)))
    (hYν : Measure.map Y ρ = (ν : Measure (Configuration E)))
    (S : ℕ → Θ → Finset E)
    (hmono : ∀ᵐ z ∂ρ, Monotone fun n => S n z)
    (hcof : ∀ᵐ z ∂ρ, ∀ T : Finset E, ∃ n, T ⊆ S n z)
    (hμnet : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)),
      HasNetExteriorConvergence (μ : Measure (Configuration E))
        (cylinder (α := fun _ => Bool) I S₀))
    (hνnet : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)),
      HasNetExteriorConvergence (ν : Measure (Configuration E))
        (cylinder (α := fun _ => Bool) I S₀))
    (hagree : ∀ (I : Finset E) (S₀ : Set (↑I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      (((μ : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀
          | outsideSigma (S n z)⟧) (X z)) =
        (((ν : Measure (Configuration E))⟦cylinder (α := fun _ => Bool) I S₀
          | outsideSigma (S n z)⟧) (Y z))) :
    (μ : Measure (Configuration E)) = (ν : Measure (Configuration E)) := by
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S₀
  exact measure_eq_of_real_eq
    (real_eq_real_of_netExteriorConvergence μ ν hX hY hXμ hYν S hmono hcof
      (hμnet I S₀) (hνnet I S₀) (hagree I S₀))

end RandomRegion

end FK

#print axioms FK.RandomRegion.HasNetExteriorConvergence
#print axioms FK.RandomRegion.tendsto_of_net_exterior
#print axioms FK.RandomRegion.real_eq_real_of_netExteriorConvergence
#print axioms FK.RandomRegion.measure_eq_of_netExteriorConvergence

namespace FK

namespace RandomRegion

/-! ## An atomic caution against the naive countable-Markov shortcut

One natural attempt to obtain net convergence from the region-uniform `L¹`
estimate thinks of each finite exterior σ-algebra as an atom-filter, bounds each
conditional value using Markov's inequality, and tries to intersect countably
many such statements. The following example is a caution against treating that
idea as a general directed maximal inequality.

On `Fin k → Bool` with counting measure, top is joined to a prescribed point by
a two-element atom. Conditional expectation of the singleton event on its own
atom is `1/2`, computed by two evaluations of its indicator integral. Every
point lies on some such atom. The formal counterexample is stated at that atomic
value level; computing a supremum over every sigma algebra is absent, and the
normalization to a probability measure is not formalized here.

This does not refute net martingale convergence, nor is it a counterexample to
the paper. It identifies separately why this heuristic is not an analytic proof.
-/

/-- The `Bool`-valued σ-algebra generated by one set has exactly four measurable
sets. -/
theorem measurableSet_comap_bool {Ω : Type*} [MeasurableSpace Ω] {g : Ω → Bool} {s : Set Ω}
    (hs : MeasurableSet[MeasurableSpace.comap g ⊤] s) :
    s = ∅ ∨ s = g ⁻¹' {true} ∨ s = g ⁻¹' {false} ∨ s = Set.univ := by
  obtain ⟨t, -, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  by_cases ht : true ∈ t <;> by_cases hf : false ∈ t
  · refine Or.inr (Or.inr (Or.inr ?_))
    ext x; cases hx : g x <;> simp [hx, ht, hf]
  · refine Or.inr (Or.inl ?_)
    ext x; cases hx : g x <;> simp [hx, ht, hf]
  · refine Or.inr (Or.inr (Or.inl ?_))
    ext x; cases hx : g x <;> simp [hx, ht, hf]
  · refine Or.inl ?_
    ext x; cases hx : g x <;> simp [hx, ht, hf]

/-- Conditional expectations given the σ-algebra generated by a `Bool`-valued map
are constant on the fibres of that map. -/
theorem eq_of_stronglyMeasurable_comap_bool {Ω : Type*} [MeasurableSpace Ω] {g : Ω → Bool}
    {φ : Ω → ℝ} (hφ : StronglyMeasurable[MeasurableSpace.comap g ⊤] φ)
    {ω ω' : Ω} (h : g ω = g ω') : φ ω = φ ω' := by
  have hset : MeasurableSet[MeasurableSpace.comap g ⊤] {x | φ x = φ ω} :=
    hφ.measurable (measurableSet_singleton (φ ω))
  have hmem : ω ∈ {x : Ω | φ x = φ ω} := rfl
  have key : ∀ x : Ω, x ∈ {x | φ x = φ ω} → g x = g ω → ω' ∈ {x | φ x = φ ω} := by
    intro x hx hgx
    rcases measurableSet_comap_bool hset with h0 | h1 | h2 | h3
    · rw [h0] at hx; exact absurd hx (Set.notMem_empty x)
    · rw [h1] at hx ⊢
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rw [← h, ← hgx]; exact hx
    · rw [h2] at hx ⊢
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rw [← h, ← hgx]; exact hx
    · rw [h3] at hx ⊢; exact Set.mem_univ ω'
  exact (key ω hmem rfl).symm

/-- A restricted integral of the indicator of a set is the mass of the
intersection. -/
theorem setIntegral_indicator_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫ x in s, t.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real (s ∩ t) := by
  classical
  have h1 : ∫ x in s, t.indicator (fun _ => (1 : ℝ)) x ∂μ
      = ∫ x, (s ∩ t).indicator (fun _ => (1 : ℝ)) x ∂μ := by
    rw [← integral_indicator hs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator_apply, Set.mem_inter_iff]
    by_cases h1 : x ∈ s <;> by_cases h2 : x ∈ t <;> simp [h1, h2]
  rw [h1, integral_indicator (hs.inter ht), setIntegral_const, smul_eq_mul, mul_one]

namespace NetMaximal

variable (k : ℕ)

/-- Counting measure on `Fin k → Bool`, with the product σ-algebra made explicit so
that no later elaboration can pick a smaller σ-algebra. -/
noncomputable abbrev cnt (k : ℕ) : Measure (Fin k → Bool) :=
  @Measure.count (Fin k → Bool) MeasurableSpace.pi

/-- The all-`true` configuration of `Fin k → Bool`. -/
def top (k : ℕ) : Fin k → Bool := fun _ => true

/-- The single-configuration event. -/
def evt (k : ℕ) : Set (Fin k → Bool) := {top k}

/-- The two-cell atom joining `top` to `y`. -/
def atomF (k : ℕ) (y : Fin k → Bool) : Finset (Fin k → Bool) := {top k, y}

/-- The σ-algebra generated by the atom through `top` and `y`. -/
noncomputable def sig (k : ℕ) (y : Fin k → Bool) : MeasurableSpace (Fin k → Bool) :=
  MeasurableSpace.comap (fun x => decide (x ∈ atomF k y)) ⊤

theorem measurable_sig (k : ℕ) (y : Fin k → Bool) :
    sig k y ≤ (MeasurableSpace.pi : MeasurableSpace (Fin k → Bool)) := by
  have hg : Measurable (fun x : Fin k → Bool => decide (x ∈ atomF k y)) :=
    measurable_of_finite _
  intro s hs
  rcases measurableSet_comap_bool hs with rfl | rfl | rfl | rfl
  · exact MeasurableSet.empty
  · exact hg (measurableSet_singleton true)
  · exact hg (measurableSet_singleton false)
  · exact MeasurableSet.univ

/-- **The value of the conditional expectation on its own atom.** -/
theorem count_condExp_evt (hk : 1 ≤ k) {y : Fin k → Bool} (hy : y ≠ top k)
    {ω : Fin k → Bool} (hω : ω ∈ atomF k y) :
    (cnt k⟦evt k | sig k y⟧) ω = 1 / 2 := by
  classical
  set φ : (Fin k → Bool) → ℝ := fun x =>
    (cnt k⟦evt k | sig k y⟧) x with hφ
  have hφsm : StronglyMeasurable[sig k y] φ := stronglyMeasurable_condExp
    (m := sig k y) (μ := cnt k)
    (f := (evt k).indicator fun _ => (1 : ℝ))
  have hconst : ∀ x ∈ atomF k y, φ x = φ ω := by
    intro x hx
    refine eq_of_stronglyMeasurable_comap_bool (g := fun x => decide (x ∈ atomF k y)) hφsm ?_
    have hx' : decide (x ∈ atomF k y) = true := by simpa using hx
    have hω' : decide (ω ∈ atomF k y) = true := by simpa using hω
    rw [hx', hω']
  have hHmeas : MeasurableSet (atomF k y : Set (Fin k → Bool)) :=
    (atomF k y).finite_toSet.measurableSet
  have hAmeas : MeasurableSet (evt k) := (Set.finite_singleton (top k)).measurableSet
  have hHmeasSig : MeasurableSet[sig k y] (atomF k y : Set (Fin k → Bool)) := by
    rw [show (atomF k y : Set (Fin k → Bool))
      = (fun x => decide (x ∈ atomF k y)) ⁻¹' {true} from by ext x; simp]
    exact MeasurableSpace.measurableSet_comap.mpr ⟨{true}, trivial, rfl⟩
  have hint : Integrable ((evt k).indicator fun _ => (1 : ℝ)) (cnt k) :=
    (integrable_const (1 : ℝ)).indicator hAmeas
  -- the two computations of the set integral over the atom
  have hstep1 : ∫ x in (atomF k y : Set (Fin k → Bool)), φ x
        ∂cnt k
      = φ ω * (cnt k).real (atomF k y : Set (Fin k → Bool)) := by
    rw [setIntegral_congr_fun (mX := (MeasurableSpace.pi : MeasurableSpace (Fin k → Bool)))
      (μ := cnt k) hHmeas (fun x hx => hconst x hx),
      setIntegral_const, smul_eq_mul, mul_comm]
  have hstep2 : ∫ x in (atomF k y : Set (Fin k → Bool)), φ x
        ∂cnt k
      = (cnt k).real (evt k ∩ (atomF k y : Set (Fin k → Bool))) := by
    have h := setIntegral_condExp (α := Fin k → Bool) (E := ℝ) (m := sig k y)
      (m₀ := (MeasurableSpace.pi : MeasurableSpace (Fin k → Bool))) (μ := cnt k)
      (f := (evt k).indicator fun _ => (1 : ℝ))
      (s := (atomF k y : Set (Fin k → Bool))) (measurable_sig k y) hint hHmeasSig
    rw [h, setIntegral_indicator_one hHmeas hAmeas, Set.inter_comm]

  have hcard : (atomF k y).card = 2 := by
    rw [atomF, Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact fun h => hy h.symm),
      Finset.card_singleton]
  have hreal2 : (cnt k).real (atomF k y : Set (Fin k → Bool)) = 2 := by
    rw [Measure.real, Measure.count_apply_finset, hcard]
    simp
  have hInter : (evt k ∩ (atomF k y : Set (Fin k → Bool))) = {top k} := by
    ext x
    simp only [Set.mem_inter_iff, evt, Set.mem_singleton_iff, atomF, Finset.coe_insert,
      Finset.coe_singleton, Set.mem_insert_iff]
    tauto
  have hreal1 : (cnt k).real
      (evt k ∩ (atomF k y : Set (Fin k → Bool))) = 1 := by
    rw [hInter, Measure.real, Measure.count_apply (measurableSet_singleton (top k))]
    simp
  have hmain : φ ω * 2 = 1 := by
    rw [← hreal2, ← hreal1, ← hstep1]
    exact hstep2
  linarith

/-- **Atom value with prescribed masses.**  For any finite measure, if the atom
`H` and the trace `A ∩ H` have masses `2 q` and `q` with `q ≠ 0`, then the
conditional expectation of `1_A` given the σ-algebra of the atom is `1/2`
everywhere on the atom. -/
theorem atom_condExp_eq_half {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A H : Set Ω} (hH : MeasurableSet H) (hA : MeasurableSet A)
    {q : ℝ} (hq : q ≠ 0) (hAq : μ.real (A ∩ H) = q) (hHq : μ.real H = 2 * q)
    {ω : Ω} (hω : ω ∈ H) :
    (μ⟦A | MeasurableSpace.comap (fun x => decide (x ∈ H)) ⊤⟧) ω = 1 / 2 := by
  classical
  set φ : Ω → ℝ := fun x => (μ⟦A | MeasurableSpace.comap (fun x => decide (x ∈ H)) ⊤⟧) x with hφ
  have hφsm : StronglyMeasurable[MeasurableSpace.comap (fun x => decide (x ∈ H)) ⊤] φ :=
    stronglyMeasurable_condExp (m := MeasurableSpace.comap (fun x => decide (x ∈ H)) ⊤)
      (μ := μ) (f := A.indicator fun _ => (1 : ℝ))
  have hconst : ∀ x ∈ H, φ x = φ ω := by
    intro x hx
    refine eq_of_stronglyMeasurable_comap_bool (g := fun x => decide (x ∈ H)) hφsm ?_
    have hx' : decide (x ∈ H) = true := by simpa using hx
    have hω' : decide (ω ∈ H) = true := by simpa using hω
    rw [hx', hω']
  have hle : MeasurableSpace.comap (fun x : Ω => decide (x ∈ H)) ⊤ ≤ ‹MeasurableSpace Ω› := by
    intro s hs
    rcases measurableSet_comap_bool hs with rfl | rfl | rfl | rfl
    · exact MeasurableSet.empty
    · have : (fun x : Ω => decide (x ∈ H)) ⁻¹' {true} = H := by ext x; simp
      rw [this]; exact hH
    · have : (fun x : Ω => decide (x ∈ H)) ⁻¹' {false} = Hᶜ := by ext x; simp
      rw [this]; exact hH.compl
    · exact MeasurableSet.univ
  have hint : Integrable (A.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hHmeasSig : MeasurableSet[MeasurableSpace.comap (fun x => decide (x ∈ H)) ⊤] H :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{true}, trivial, by ext x; simp⟩
  have hstep1 : ∫ x in H, φ x ∂μ = φ ω * μ.real H := by
    rw [setIntegral_congr_fun hH (fun x hx => hconst x hx), setIntegral_const,
      smul_eq_mul, mul_comm]
  have hstep2 : ∫ x in H, φ x ∂μ = μ.real (A ∩ H) := by
    have h := setIntegral_condExp (α := Ω) (E := ℝ)
      (m := MeasurableSpace.comap (fun x => decide (x ∈ H)) ⊤) (m₀ := ‹MeasurableSpace Ω›)
      (μ := μ) (f := A.indicator fun _ => (1 : ℝ)) (s := H) hle hint hHmeasSig
    rw [h, setIntegral_indicator_one hH hA, Set.inter_comm]
  have hmain : φ ω * (2 * q) = q := by
    rw [← hHq, ← hstep1, hstep2, hAq]
  have h2 : φ ω * 2 = 1 := by
    have hq2 : q * (φ ω * 2) = q * 1 := by linarith [hmain]
    exact mul_left_cancel₀ hq hq2
  linarith

/-- An explicit finite atomic value example. For each point of `Fin k → Bool`
there is a two-element atom whose conditional expectation of the singleton at
`top` is `1/2`, although the counting-measure mass of that singleton is `1`.
The theorem proves these atomic value and mass facts, not a complete theorem
about directed-net maximal inequalities. -/
theorem exists_directed_maximal_inequality_failure (k : ℕ) (hk : 1 ≤ k) :
    ∃ (A : Set (Fin k → Bool)) (G : (Fin k → Bool) → MeasurableSpace (Fin k → Bool)),
      (∀ ω : Fin k → Bool, ∃ y : Fin k → Bool, (1 / 2 : ℝ) ≤ ((cnt k)⟦A | G y⟧) ω) ∧
      (cnt k).real A = 1 := by
  classical
  have hne : (fun _ : Fin k => false) ≠ top k := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    simpa [top] using h0
  refine ⟨evt k, sig k, ?_, ?_⟩
  · intro ω
    by_cases hω : ω = top k
    · refine ⟨fun _ => false, ?_⟩
      rw [hω]
      exact le_of_eq (count_condExp_evt k hk hne (by simp [atomF])).symm
    · refine ⟨ω, ?_⟩
      have hmem : ω ∈ atomF k ω := by simp [atomF]
      exact le_of_eq (count_condExp_evt k hk hω hmem).symm
  · rw [evt, Measure.real, Measure.count_apply (measurableSet_singleton (top k))]
    simp

end NetMaximal

end RandomRegion

end FK

#print axioms FK.RandomRegion.NetMaximal.exists_directed_maximal_inequality_failure

#print axioms FK.RandomRegion.measurableSet_comap_bool
#print axioms FK.RandomRegion.eq_of_stronglyMeasurable_comap_bool
#print axioms FK.RandomRegion.NetMaximal.measurable_sig
#print axioms FK.RandomRegion.NetMaximal.count_condExp_evt
#print axioms FK.RandomRegion.setIntegral_indicator_one
#print axioms FK.RandomRegion.NetMaximal.atom_condExp_eq_half
