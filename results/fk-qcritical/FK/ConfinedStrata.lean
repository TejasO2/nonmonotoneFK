/-
# Arbitrary exterior strata in the confined region split

`FK/PrefixContinuation.lean` proves the ambient common-upper factorization

  `P(A x {xiS} x D) = regionFK(A) * P(univ x {xiS} x D)`

only for strata that are a *product* of one prescribed small-exterior
configuration `xiS` and a set `D` of added-block configurations.  The
good-intersection comparison of the nested-triple argument needs the same
identity for an arbitrary set `E` of exterior configurations, because the third
coordinate of the ordered triple is constrained by a stratum event, not by a
product event.

This file supplies that generalization.  The only hypothesis on `E` is the
pointwise one actually used by the weight computation: at every `e in E`, the
small-exterior bits of `e` that are *open* avoid the region, and the added
labels avoid the region.  Under it we prove

* the pointwise weight factorization at an arbitrary exterior configuration
  (`fkWeight_glue_stratum`), refining `fkWeight_glue_prefix_eq`;
* the weight-level stratification identity for an arbitrary stratum `E`
  (`stratum_weight_factorization`);
* its PMF-level form (`stratum_mass_factorization`), which is exactly the
  "same region law on every stratum" input of a common-upper comparison;
* the conditional region law on an arbitrary admissible stratum
  (`stratum_conditional_region_eq_region`);
* agreement of the conditional region law across two nested admissible
  strata (`nested_strata_conditional_eq`), i.e. the two-scale check.

The companion file `ConfinedStrataObstruction.lean` proves that the pointwise
separation hypothesis cannot be dropped, so the restriction to these strata is
not cosmetic.
-/
import FK.PrefixContinuation

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement.ConfinedStrata

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {W K I : Type*} [Fintype W] [Fintype K] [Fintype I]

/-! ## Separation predicates -/

/-- The small exterior configuration is separated: its open bits avoid the
region on both endpoints.  This is the hypothesis `hsepS` of
`FK.RegionConfinement.PrefixContinuation`, packaged as a predicate. -/
def SmallSep {k : ℕ} (so xo : Fin k → W ⊕ K) (ξS : Fin k → Bool) : Prop :=
  ∀ i : Fin k, ξS i = true → ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i)

/-- The added block never meets the region. -/
def AddedAvoid {a : ℕ} (ao bo : Fin a → W ⊕ K) : Prop :=
  ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j)

/-- Full pointwise separation of an exterior configuration. -/
def ExtSep {k a : ℕ} (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (e : Fin k ⊕ Fin a → Bool) : Prop :=
  ∀ l : Fin k ⊕ Fin a, e l = true →
    ¬ InRegion (K := K) (bigSo so ao l) ∧ ¬ InRegion (K := K) (bigXo xo bo l)

lemma extSep_of_small {k a : ℕ} {so xo : Fin k → W ⊕ K} {ao bo : Fin a → W ⊕ K}
    {ξS : Fin k → Bool} {γ : Fin a → Bool}
    (hsepS : SmallSep (K := K) so xo ξS) (havoid : AddedAvoid (K := K) ao bo) :
    ExtSep (K := K) so xo ao bo (bigExterior ξS γ) := by
  intro l h
  cases l with
  | inl i => exact hsepS i h
  | inr j => exact havoid j

/-- The small part of a separated exterior configuration is separated. -/
lemma smallSep_of_extSep {k a : ℕ} {so xo : Fin k → W ⊕ K} {ao bo : Fin a → W ⊕ K}
    {e : Fin k ⊕ Fin a → Bool} (h : ExtSep (K := K) so xo ao bo e) :
    SmallSep (K := K) so xo (e ∘ Sum.inl) := by
  intro i hi
  exact h (Sum.inl i) hi

/-! ## The exterior stratum events -/

/-- The stratum event: the exterior part of the configuration lies in `E`. -/
def extMask {k a : ℕ} (E : Set (Fin k ⊕ Fin a → Bool)) :
    Set (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
  {ρ | ρ ∘ Sum.inr ∈ E}

/-- The region event: the region part of the configuration lies in `A`. -/
def regionMask {k a : ℕ} (A : Set (I → Bool)) :
    Set (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
  {ρ | ρ ∘ Sum.inl ∈ A}

@[simp] lemma mem_extMask {k a : ℕ} {E : Set (Fin k ⊕ Fin a → Bool)}
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool} : ρ ∈ extMask (I := I) E ↔ ρ ∘ Sum.inr ∈ E :=
  Iff.rfl

@[simp] lemma mem_regionMask {k a : ℕ} {A : Set (I → Bool)}
    {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool} : ρ ∈ regionMask (I := I) A ↔ ρ ∘ Sum.inl ∈ A :=
  Iff.rfl

/-- Every configuration is the glue of its region and exterior parts. -/
lemma glue_eta {O : Type*} (ρ : I ⊕ O → Bool) :
    glue (ρ ∘ Sum.inl) (ρ ∘ Sum.inr) = ρ := by
  funext x
  cases x with
  | inl i => rfl
  | inr o => rfl

@[simp] lemma comp_glue_inl {O : Type*} (ω : I → Bool) (e : O → Bool) :
    glue ω e ∘ Sum.inl = ω := rfl

@[simp] lemma comp_glue_inr {O : Type*} (ω : I → Bool) (e : O → Bool) :
    glue ω e ∘ Sum.inr = e := rfl

/-- Splitting a sum-type configuration into its region and exterior halves. -/
def configEquiv (O : Type*) : (I ⊕ O → Bool) ≃ (I → Bool) × (O → Bool) :=
  Equiv.sumArrowEquivProdArrow I O Bool

@[simp] lemma configEquiv_apply (O : Type*) (ρ : I ⊕ O → Bool) :
    configEquiv (I := I) O ρ = (ρ ∘ Sum.inl, ρ ∘ Sum.inr) := rfl

@[simp] lemma configEquiv_symm_apply (O : Type*) (p : (I → Bool) × (O → Bool)) :
    (configEquiv (I := I) O).symm p = glue p.1 p.2 := by
  funext x
  cases x with
  | inl i => rfl
  | inr o => rfl

/-! ## The pointwise weight factorization at an arbitrary exterior configuration -/

/-- The effective exterior weight of the confined split at an exterior
configuration `e`: the Bernoulli weight of `e` times `q` to the number of
components of the confined exterior graph. -/
noncomputable def extWeight {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (ζ : Setoid (W ⊕ K)) (q p : NNReal) (e : Fin k ⊕ Fin a → Bool) : NNReal :=
  FK.FinitePlane.edgeWeight p (1 - p) e *
    q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ e).ConnectedComponent

/-- The region FK weight. -/
noncomputable def regionWeight (si : I → W) (ti : I → W) (θ : Setoid W)
    (q p : NNReal) (ω : I → Bool) : NNReal :=
  FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω

lemma regionWeight_pos {si : I → W} {ti : I → W} {θ : Setoid W} {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) (ω : I → Bool) :
    0 < regionWeight si ti θ q p ω :=
  FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ ω

lemma extWeight_pos {k a : ℕ} {si : I → W} {ti : I → W}
    {so xo : Fin k → W ⊕ K} {ao bo : Fin a → W ⊕ K} {ζ : Setoid (W ⊕ K)}
    {q p : NNReal} (hp₀ : 0 < p) (hp₁ : p < 1) (hq : 0 < q)
    (e : Fin k ⊕ Fin a → Bool) :
    0 < extWeight si ti so xo ao bo ζ q p e :=
  mul_pos (FK.FinitePlane.edgeWeight_pos' hp₀ hp₁ _) (pow_pos hq _)

/-- **Pointwise weight factorization at an arbitrary exterior configuration.**
This is `FK.RegionConfinement.PrefixContinuation.fkWeight_glue_prefix_eq` with
the positive-prefix configuration `bigExterior xiS gamma` replaced by an
arbitrary exterior configuration `e`, and the prefix-separation hypothesis
replaced by the pointwise separation of `e`. -/
theorem fkWeight_glue_stratum {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (e : Fin k ⊕ Fin a → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsep : ExtSep (K := K) so xo ao bo e)
    (q p : NNReal) (ω : I → Bool) :
    (ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkWeight q p ζ (glue ω e) =
      extWeight si ti so xo ao bo ζ q p e * regionWeight si ti θ q p ω := by
  have h1 := FK.FinitePlane.ArbitraryBoundary.fkWeight_glue
    (s := splitSource si (bigSo so ao)) (t := splitTarget ti (bigXo xo bo)) ζ q p ω e
  have h2 := FK.RegionConfinement.interiorWeight_confined_eq si ti (bigSo so ao)
    (bigXo xo bo) θ ζ e ω hconf hθ hsep q p
  have h2' : (interiorOfSum (splitSource si (bigSo so ao))
      (splitTarget ti (bigXo xo bo))).fkWeight q p
        (effectiveBoundary (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo)) ζ e) ω =
      q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ e).ConnectedComponent *
      FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω :=
    (FK.FinitePlane.plane_fkWeight_eq_actual
      (interiorOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)))
      (effectiveBoundary (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)) ζ e)
      q p ω).symm.trans h2
  exact h1.trans ((congrArg (fun t =>
      FK.FinitePlane.edgeWeight p (1 - p) e * t) h2').trans (mul_assoc _ _ _).symm)

/-! ## The stratification identity for an arbitrary admissible stratum -/

/-- **Weight-level stratification identity.**  For an arbitrary set `E` of
exterior configurations, all pointwise separated, the ambient FK weight mass of
the stratum `(region in A) x (exterior in E)` factors as the region weight mass
of `A` times the effective exterior weight mass of `E`.

This strictly generalizes
`FK.RegionConfinement.PrefixContinuation.ambientWeight_set_factorization`, whose
strata are products `{xiS} x D`. -/
theorem stratum_weight_factorization {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (q p : NNReal) (A : Set (I → Bool)) (E : Set (Fin k ⊕ Fin a → Bool))
    (hE : ∀ e ∈ E, ExtSep (K := K) so xo ao bo e) :
    (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
        (regionMask (I := I) A ∩ extMask (I := I) E).indicator
          (fun ρ => ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ) =
      (∑' ω : I → Bool, A.indicator
          (fun ω => (regionWeight si ti θ q p ω : ℝ≥0∞)) ω) *
        (∑' e : Fin k ⊕ Fin a → Bool, E.indicator
          (fun e => (extWeight si ti so xo ao bo ζ q p e : ℝ≥0∞)) e) := by
  classical
  set w : (I ⊕ (Fin k ⊕ Fin a) → Bool) → ℝ≥0∞ :=
    fun ρ => ((ambientOfSum (splitSource si (bigSo so ao))
      (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞) with hw
  set RW : (I → Bool) → ℝ≥0∞ := fun ω => (regionWeight si ti θ q p ω : ℝ≥0∞) with hRW
  set EW : (Fin k ⊕ Fin a → Bool) → ℝ≥0∞ :=
    fun e => (extWeight si ti so xo ao bo ζ q p e : ℝ≥0∞) with hEW
  have hpt : ∀ (ω : I → Bool) (e : Fin k ⊕ Fin a → Bool), e ∈ E →
      w (glue ω e) = EW e * RW ω := by
    intro ω e he
    have h := fkWeight_glue_stratum si ti so xo ao bo θ ζ e hconf hθ (hE e he) q p ω
    simp only [hw, hRW, hEW]
    rw [h]
    push_cast
    ring
  have hind : ∀ ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
      (regionMask (I := I) A ∩ extMask (I := I) E).indicator w ρ =
        (A.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inl)) *
          (E.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inr)) * w ρ := by
    intro ρ
    have hmem : ρ ∈ regionMask (I := I) A ∩ extMask (I := I) E ↔
        (ρ ∘ Sum.inl ∈ A ∧ ρ ∘ Sum.inr ∈ E) := Iff.rfl
    by_cases hA : ρ ∘ Sum.inl ∈ A
    · by_cases hE' : ρ ∘ Sum.inr ∈ E
      · rw [Set.indicator_of_mem (hmem.mpr ⟨hA, hE'⟩), Set.indicator_of_mem hA,
          Set.indicator_of_mem hE', one_mul, one_mul]
      · rw [Set.indicator_of_notMem (fun h => hE' (hmem.mp h).2),
          Set.indicator_of_notMem hE']
        simp
    · rw [Set.indicator_of_notMem (fun h => hA (hmem.mp h).1),
        Set.indicator_of_notMem hA]
      simp
  have hfib : ∀ ω : I → Bool,
      (∑' e : Fin k ⊕ Fin a → Bool,
          (E.indicator (fun _ => (1 : ℝ≥0∞)) e) * w (glue ω e)) =
        (∑' e : Fin k ⊕ Fin a → Bool,
          (E.indicator (fun _ => (1 : ℝ≥0∞)) e) * EW e) * RW ω := by
    intro ω
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr (fun e => ?_)
    by_cases he : e ∈ E
    · rw [hpt ω e he]; ring
    · rw [Set.indicator_of_notMem he, zero_mul, zero_mul, zero_mul]
  have hreindex : (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
      (regionMask (I := I) A ∩ extMask (I := I) E).indicator w ρ) =
      ∑' pe : (I → Bool) × (Fin k ⊕ Fin a → Bool),
        (regionMask (I := I) A ∩ extMask (I := I) E).indicator w (glue pe.1 pe.2) := by
    have h := Equiv.tsum_eq (configEquiv (I := I) (Fin k ⊕ Fin a)).symm
      (fun ρ => (regionMask (I := I) A ∩ extMask (I := I) E).indicator w ρ)
    rw [← h]
    exact tsum_congr (fun pe => by rw [configEquiv_symm_apply])
  rw [hreindex]
  simp only [hind, comp_glue_inl, comp_glue_inr]
  set C : ℝ≥0∞ := ∑' e : Fin k ⊕ Fin a → Bool, E.indicator (fun _ => (1 : ℝ≥0∞)) e * EW e
    with hC
  have hstep1 : (∑' pe : (I → Bool) × (Fin k ⊕ Fin a → Bool),
      A.indicator (fun _ => (1 : ℝ≥0∞)) pe.1 * E.indicator (fun _ => (1 : ℝ≥0∞)) pe.2 *
        w (glue pe.1 pe.2)) =
      ∑' ω : I → Bool, ∑' e : Fin k ⊕ Fin a → Bool,
        A.indicator (fun _ => (1 : ℝ≥0∞)) ω * E.indicator (fun _ => (1 : ℝ≥0∞)) e *
          w (glue ω e) :=
    ENNReal.tsum_prod (f := fun a b =>
      A.indicator (fun _ => (1 : ℝ≥0∞)) a * E.indicator (fun _ => (1 : ℝ≥0∞)) b * w (glue a b))
  have hinner : ∀ ω : I → Bool,
      (∑' e : Fin k ⊕ Fin a → Bool,
          A.indicator (fun _ => (1 : ℝ≥0∞)) ω * E.indicator (fun _ => (1 : ℝ≥0∞)) e *
            w (glue ω e)) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) ω * (C * RW ω) := by
    intro ω
    rw [show (∑' e : Fin k ⊕ Fin a → Bool,
          A.indicator (fun _ => (1 : ℝ≥0∞)) ω * E.indicator (fun _ => (1 : ℝ≥0∞)) e *
            w (glue ω e)) =
        ∑' e : Fin k ⊕ Fin a → Bool,
          A.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (E.indicator (fun _ => (1 : ℝ≥0∞)) e * w (glue ω e)) from
      tsum_congr (fun e => by ring)]
    rw [ENNReal.tsum_mul_left, hfib ω, hC]
  have hstep2 : (∑' ω : I → Bool, ∑' e : Fin k ⊕ Fin a → Bool,
        A.indicator (fun _ => (1 : ℝ≥0∞)) ω * E.indicator (fun _ => (1 : ℝ≥0∞)) e *
          w (glue ω e)) =
      ∑' ω : I → Bool, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * (C * RW ω) :=
    tsum_congr hinner
  have hstep3 : (∑' ω : I → Bool, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * (C * RW ω)) =
      (∑' ω : I → Bool, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * RW ω) * C := by
    rw [show (∑' ω : I → Bool, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * (C * RW ω)) =
        ∑' ω : I → Bool, (A.indicator (fun _ => (1 : ℝ≥0∞)) ω * RW ω) * C from
      tsum_congr (fun ω => by ring)]
    rw [ENNReal.tsum_mul_right]
  have hindA : ∀ ω : I → Bool, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * RW ω = A.indicator RW ω := by
    intro ω
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  have hindE : ∀ e : Fin k ⊕ Fin a → Bool,
      E.indicator (fun _ => (1 : ℝ≥0∞)) e * EW e = E.indicator EW e := by
    intro e
    by_cases h : e ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  rw [hstep1, hstep2, hstep3]
  simp only [hC, hindA, hindE]

/-! ## The PMF-level stratification identity -/

/-- The stratum event has a support point as soon as `E` is nonempty: the
all-closed region configuration over any exterior configuration in `E`. -/
theorem extMask_support {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (ζ : Setoid (W ⊕ K)) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (E : Set (Fin k ⊕ Fin a → Bool)) (hne : E.Nonempty) :
    ∃ ρ ∈ extMask (I := I) E,
      ρ ∈ ((ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).support := by
  obtain ⟨e, he⟩ := hne
  refine ⟨glue (fun _ => false) e, he, ?_⟩
  exact (PMF.mem_support_iff _ _).mpr
    (FK.Exploration.FKCoupling.fkPMF_ne_zero
      (ambientOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)))
      hq hp₀ hp₁ ζ _)

/-- The partition-function cancellation used by every mass factorization:
`C * (X * Y) * Z⁻¹ = (C * X⁻¹) * ((X * Y) * Z⁻¹)`. -/
lemma stratum_alg (C X Y Z : ℝ≥0∞) (hX0 : X ≠ 0) (hXt : X ≠ ∞) :
    C * Y * Z⁻¹ = (C * X⁻¹) * ((X * Y) * Z⁻¹) := by
  rw [show (C * X⁻¹) * ((X * Y) * Z⁻¹) = C * (X⁻¹ * X) * Y * Z⁻¹ from by ac_rfl]
  rw [ENNReal.inv_mul_cancel hX0 hXt, mul_one]

/-- **PMF-level stratification identity.**  For an arbitrary pointwise separated
exterior stratum `E`, the ambient FK mass of `(region in A) x (exterior in E)`
factors as the region FK mass of `A` times the ambient FK mass of the stratum.

This is the common-upper identity a good-intersection comparison consumes, for
strata that need not be product events. -/
theorem stratum_mass_factorization {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (I → Bool)) (E : Set (Fin k ⊕ Fin a → Bool))
    (hE : ∀ e ∈ E, ExtSep (K := K) so xo ao bo e) :
    (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
        (regionMask (I := I) A ∩ extMask (I := I) E).indicator
          (fun ρ => (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) ρ : ℝ≥0∞)) ρ) =
      (∑' ω : I → Bool, A.indicator
          (fun ω => (((regionGraph si ti).fkPMF hq hp₁.le θ) ω : ℝ≥0∞)) ω) *
        (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool, (extMask (I := I) E).indicator
          (fun ρ => (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) ρ : ℝ≥0∞)) ρ) := by
  classical
  have hA := stratum_weight_factorization si ti so xo ao bo θ ζ hconf hθ q p A E hE
  have hU := stratum_weight_factorization si ti so xo ao bo θ ζ hconf hθ q p Set.univ E hE
  have hU' : (∑' ω : I → Bool, Set.univ.indicator
        (fun ω => (regionWeight si ti θ q p ω : ℝ≥0∞)) ω) =
      ∑' ω : I → Bool, (regionWeight si ti θ q p ω : ℝ≥0∞) :=
    tsum_congr (fun ω => Set.indicator_of_mem (Set.mem_univ ω) _)
  rw [hU'] at hU
  have hUeq : regionMask (I := I) (Set.univ : Set (I → Bool)) ∩ extMask (I := I) E =
      extMask (I := I) E := by
    ext ρ
    simp
  have hregionmass : (∑' ω : I → Bool, A.indicator
        (fun ω => (((regionGraph si ti).fkPMF hq hp₁.le θ) ω : ℝ≥0∞)) ω) =
      (∑' ω : I → Bool, A.indicator (fun ω => (regionWeight si ti θ q p ω : ℝ≥0∞)) ω) *
        (∑' ω : I → Bool, (regionWeight si ti θ q p ω : ℝ≥0∞))⁻¹ := by
    rw [show (∑' ω : I → Bool, A.indicator
          (fun ω => (((regionGraph si ti).fkPMF hq hp₁.le θ) ω : ℝ≥0∞)) ω) =
        ∑' ω : I → Bool, A.indicator (fun ω => (regionWeight si ti θ q p ω : ℝ≥0∞)) ω *
          (∑' ω : I → Bool, (regionWeight si ti θ q p ω : ℝ≥0∞))⁻¹ from ?_]
    · exact ENNReal.tsum_mul_right
    refine tsum_congr (fun ω => ?_)
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      exact FK.FinitePlane.normalizedPMF_apply
        (fun ω => regionWeight si ti θ q p ω)
        (fun ω => regionWeight_pos hq hp₀ hp₁ ω) ω
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  have hRW0 : (∑' ω : I → Bool, (regionWeight si ti θ q p ω : ℝ≥0∞)) ≠ 0 :=
    FK.FinitePlane.tsum_coe_ne_zero_of_pos (fun ω => regionWeight si ti θ q p ω)
      (fun ω => regionWeight_pos hq hp₀ hp₁ ω)
  have hRWtop : (∑' ω : I → Bool, (regionWeight si ti θ q p ω : ℝ≥0∞)) ≠ ∞ :=
    FK.FinitePlane.tsum_coe_ne_top (fun ω => regionWeight si ti θ q p ω)
  rw [FK.RegionConfinement.PrefixContinuation.fkPMF_mass_eq si ti so xo ao bo ζ hq hp₀ hp₁
      (regionMask (I := I) A ∩ extMask (I := I) E),
    FK.RegionConfinement.PrefixContinuation.fkPMF_mass_eq si ti so xo ao bo ζ hq hp₀ hp₁
      (extMask (I := I) E),
    hA, hregionmass]
  rw [hUeq] at hU
  rw [hU]
  exact stratum_alg _ _ _ _ hRW0 hRWtop

/-! ## The conditional region law on an arbitrary admissible stratum -/

/-- **Conditional region law on an arbitrary admissible stratum.**  Conditioning
the actual ambient FK law on an arbitrary pointwise separated stratum `E` of
exterior configurations and reading off the region configuration gives exactly
the region FK law with boundary `θ`, independently of `E`.

This is the `hsepS`-restricted stratum statement: it is *not* claimed for
strata meeting the region with an open exterior label (see
`ConfinedStrataObstruction`). -/
theorem stratum_conditional_region_eq_region {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (E : Set (Fin k ⊕ Fin a → Bool)) (hE : ∀ e ∈ E, ExtSep (K := K) so xo ao bo e)
    (hne : E.Nonempty) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).filter
          (extMask (I := I) E) (extMask_support si ti so xo ao bo ζ hq hp₀ hp₁ E hne)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  refine FK.RegionConfinement.PrefixContinuation.map_filter_eq_of_mass_factorization
    (P := ((ambientOfSum (splitSource si (bigSo so ao))
      (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ))
    (f := fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
    (T := extMask (I := I) E)
    (hT := extMask_support si ti so xo ao bo ζ hq hp₀ hp₁ E hne)
    (TA := fun A => regionMask (I := I) A ∩ extMask (I := I) E)
    (c := (regionGraph si ti).fkPMF hq hp₁.le θ) ?_ ?_
  · intro A
    rfl
  · intro A
    exact stratum_mass_factorization si ti so xo ao bo θ ζ hconf hθ hq hp₀ hp₁ A E hE

/-- **Agreement across two nested admissible strata.**  For two nested strata of
exterior configurations, both pointwise separated and nonempty, the conditional
region laws coincide.  This is the two-scale check: changing the exterior box
does not change the region factor. -/
theorem nested_strata_conditional_eq {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K))
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (E₁ E₂ : Set (Fin k ⊕ Fin a → Bool))
    (hE₁ : ∀ e ∈ E₁, ExtSep (K := K) so xo ao bo e)
    (hE₂ : ∀ e ∈ E₂, ExtSep (K := K) so xo ao bo e)
    (hne₁ : E₁.Nonempty) (hne₂ : E₂.Nonempty) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).filter
          (extMask (I := I) E₁) (extMask_support si ti so xo ao bo ζ hq hp₀ hp₁ E₁ hne₁)) =
      PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).filter
          (extMask (I := I) E₂) (extMask_support si ti so xo ao bo ζ hq hp₀ hp₁ E₂ hne₂)) := by
  rw [stratum_conditional_region_eq_region si ti so xo ao bo θ ζ hconf hθ hq hp₀ hp₁
      E₁ hE₁ hne₁,
    stratum_conditional_region_eq_region si ti so xo ao bo θ ζ hconf hθ hq hp₀ hp₁
      E₂ hE₂ hne₂]

/-- The old product strata of `FK.PrefixContinuation` are the strata `E` of
exterior configurations whose small part is the prescribed prefix: the
generalization here strictly contains `prefixSet`. -/
theorem prefixSet_eq_regionMask_inter_extMask {k a : ℕ} (ξS : Fin k → Bool)
    (A : Set (I → Bool)) (D : Set (Fin a → Bool)) :
    FK.RegionConfinement.PrefixContinuation.prefixSet (I := I) (a := a) ξS A D =
      regionMask (I := I) A ∩
        extMask (I := I) (bigExterior ξS '' D) := by
  ext ρ
  constructor
  · rintro ⟨⟨hpre, hA⟩, hD⟩
    refine ⟨hA, ?_⟩
    exact ⟨ρ ∘ Sum.inr ∘ Sum.inr, hD, by
      funext l
      cases l with
      | inl i => exact (hpre i).symm
      | inr j => rfl⟩
  · rintro ⟨hA, γ, hD, hγ⟩
    refine ⟨⟨fun i => ?_, hA⟩, ?_⟩
    · have h1 := congrFun hγ (Sum.inl i)
      simp only [Function.comp_apply, FK.RegionConfinement.bigExterior, Sum.elim_inl] at h1
      exact h1.symm
    · have h2 : ρ ∘ Sum.inr ∘ Sum.inr = γ := by
        funext j
        have h1 := congrFun hγ (Sum.inr j)
        simp only [Function.comp_apply, FK.RegionConfinement.bigExterior, Sum.elim_inr] at h1
        exact h1.symm
      show ρ ∘ Sum.inr ∘ Sum.inr ∈ D
      rw [h2]
      exact hD
