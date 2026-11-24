/-
# Prefix continuation: the normalized PMF identity for confined region splits

`FK/RegionConfinement.lean` proves the weight-level prefix factorization
`ambientWeight_prefix_sum` and records the PMF statement

  `PMF.map (fun ρ => ρ ∘ Sum.inl) ((G_big.fkPMF ζ).filter (prefixEvent ξS))
     = regionGraph.fkPMF θ`

as the remaining residual.  This file proves that identity, in a form that
separates the purely probabilistic normalization step from the FK weight
factorization:

* `prefixEvent_support_normalizedPMF` : the prefix event meets the support of
  any positive finite normalized law, so `PMF.filter` is defined;
* `map_prefix_filter_normalizedPMF` : **general finite prefix fibre sum**.  For an
  arbitrary positive finite weight on `I ⊕ (Fin k ⊕ Fin a) → Bool`, the push
  forward of the normalized law conditioned on the prefix event is the
  normalized law of the fibre sums `ω ↦ ∑ γ, w (glue ω (bigExterior ξS γ))`.
  This is the general statement whose FK instance is the residual above; it is
  proved by an explicit `PMF.map_apply`/`PMF.filter_apply` computation in which
  the ambient partition function cancels against the conditioning mass;
* `ambientWeight_fibreSum_eq` : the fibre sums of the *big FK weight* are
  `c * regionWeight ω` with `c` the effective right-block weight (a restatement
  of `ambientWeight_prefix_sum` in the form consumed below);
* `prefix_filter_fkPMF_eq_region` : the residual PMF identity;
* `prefix_mass_factorization` : the mass of (region event) ∩ (small exterior
  prefix) ∩ (added-block event) factors as region mass times added mass.  This is
  the ambient "common upper" identity that a good-intersection comparison
  consumes: the region factor does not depend on the added block;
* `prefix_conditional_eq_of_boundary` : the conditional region law on a prefix is
  the same for every confined boundary matching `θ`;
* `prefix_filter_fkPMF_eq_region_twoSided` : the two-sided specialization.

No new axioms; the file imports `FK.RegionConfinement` only.
-/
import FK.RegionConfinement

open Set
open scoped ENNReal NNReal BigOperators Classical

namespace FK.RegionConfinement.PrefixContinuation

open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior FK.FinitePlane.ArbitraryBoundary

attribute [local instance] Classical.propDecidable

variable {W K I O : Type*} [Fintype W] [Fintype K] [Fintype I] [Fintype O]

/-! ## The prefix event meets the support -/

/-- The prefix event has positive mass for every positive finite weight: the
all-closed configuration carrying the prescribed small exterior bits lies in
it. -/
theorem prefixEvent_support_normalizedPMF {k a : ℕ}
    (w : (I ⊕ (Fin k ⊕ Fin a) → Bool) → NNReal) (hw : ∀ ρ, 0 < w ρ)
    (ξS : Fin k → Bool) :
    ∃ ρ ∈ prefixEvent (I := I) (a := a) ξS,
      ρ ∈ (FK.FinitePlane.normalizedPMF w hw).support :=
  ⟨glue (fun _ => false) (bigExterior ξS (fun _ => false)), fun _ => rfl,
    FK.FinitePlane.normalizedPMF_mem_support_of_pos w hw _⟩

/-! ## General prefix fibre sum -/

/-- **General finite prefix fibre sum.**  Conditioning the normalized law of a
positive finite weight on the event that the small exterior block equals `ξS` and
then reading off the region configuration is the normalized law of the fibre
sums over the added block.  No structure of `w` is used beyond positivity and
finiteness of the configuration type. -/
theorem map_prefix_filter_normalizedPMF {k a : ℕ}
    (w : (I ⊕ (Fin k ⊕ Fin a) → Bool) → NNReal) (hw : ∀ ρ, 0 < w ρ)
    (ξS : Fin k → Bool) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        ((FK.FinitePlane.normalizedPMF w hw).filter
          (prefixEvent (I := I) (a := a) ξS)
          (prefixEvent_support_normalizedPMF (I := I) (a := a) w hw ξS)) =
      FK.FinitePlane.normalizedPMF
        (fun ω : I → Bool => ∑ γ : Fin a → Bool,
          w (glue ω (bigExterior ξS γ)))
        (fun _ => Finset.sum_pos (fun _ _ => hw _) Finset.univ_nonempty) := by
  classical
  set P : PMF (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
    FK.FinitePlane.normalizedPMF w hw with hP
  set s : Set (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
    prefixEvent (I := I) (a := a) ξS with hs
  have hsupp : ∃ ρ ∈ s, ρ ∈ P.support :=
    prefixEvent_support_normalizedPMF (I := I) (a := a) w hw ξS
  set Z : ℝ≥0∞ := ∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool, (w ρ : ℝ≥0∞) with hZ
  set Y : (I → Bool) → ℝ≥0∞ :=
    fun ω => ∑' γ : Fin a → Bool, (w (glue ω (bigExterior ξS γ)) : ℝ≥0∞) with hY
  set ZS : ℝ≥0∞ := ∑' ω : I → Bool, Y ω with hZS
  have hYapp : ∀ ω : I → Bool, Y ω = ∑' γ : Fin a → Bool,
      (w (glue ω (bigExterior ξS γ)) : ℝ≥0∞) := fun ω => by rw [hY]
  have hZ0 : Z ≠ 0 := FK.FinitePlane.tsum_coe_ne_zero_of_pos w hw
  have hZtop : Z ≠ ∞ := FK.FinitePlane.tsum_coe_ne_top w
  have hYcoe : ∀ ω : I → Bool, Y ω =
      ((∑ γ : Fin a → Bool, w (glue ω (bigExterior ξS γ)) : NNReal) : ℝ≥0∞) :=
    fun ω => by rw [hYapp ω, tsum_fintype]; simp
  have hYpos : ∀ ω : I → Bool, 0 < Y ω := by
    intro ω
    rw [hYcoe ω]
    exact ENNReal.coe_pos.mpr
      (Finset.sum_pos (fun γ _ => hw _) Finset.univ_nonempty)
  have hZS0 : ZS ≠ 0 := by
    intro h
    have h0 : Y (fun _ => false) = 0 := by
      have : ZS = 0 := h
      rw [hZS, ENNReal.tsum_eq_zero] at this
      exact this _
    exact absurd h0 (hYpos _).ne'
  have hYtop : ∀ ω : I → Bool, Y ω ≠ ∞ := by
    intro ω
    rw [hYcoe ω]
    exact ENNReal.coe_ne_top
  have hZStop : ZS ≠ ∞ := by
    rw [hZS, tsum_fintype,
      show (∑ ω : I → Bool, Y ω : ℝ≥0∞) = ∑ ω ∈ Finset.univ, Y ω from by simp]
    exact (ENNReal.sum_ne_top).mpr (fun ω _ => hYtop ω)
  -- the conditioning mass
  have hdenom : (∑' ρ, s.indicator P ρ) = ZS * Z⁻¹ := by
    have h1 : (∑' ρ, s.indicator P ρ) =
        ∑' ω : I → Bool, ∑' γ : Fin a → Bool, P (glue ω (bigExterior ξS γ)) := by
      rw [show (∑' ρ, s.indicator P ρ) =
          ∑' ρ, if ρ ∈ s then P ρ else 0 from
        tsum_congr (fun ρ => by rw [Set.indicator_apply])]
      exact tsum_prefix_fiber (F := fun ρ => P ρ) ξS
    rw [h1]
    have hstep : ∀ ω : I → Bool,
        (∑' γ : Fin a → Bool, P (glue ω (bigExterior ξS γ))) = Y ω * Z⁻¹ := by
      intro ω
      rw [show (∑' γ : Fin a → Bool, P (glue ω (bigExterior ξS γ))) =
          ∑' γ : Fin a → Bool, (w (glue ω (bigExterior ξS γ)) : ℝ≥0∞) * Z⁻¹ from
        tsum_congr (fun γ => by rw [hP, FK.FinitePlane.normalizedPMF_apply])]
      rw [ENNReal.tsum_mul_right]
    rw [tsum_congr hstep, ENNReal.tsum_mul_right]
  have key : ∀ ω : I → Bool,
      (PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (P.filter s hsupp)) ω = Y ω * Z⁻¹ * (ZS * Z⁻¹)⁻¹ := by
    intro ω
    have hstep2 : (∑' γ : Fin a → Bool,
        (P.filter s hsupp) (glue ω (bigExterior ξS γ))) =
        (∑' γ : Fin a → Bool,
          (w (glue ω (bigExterior ξS γ)) : ℝ≥0∞) * Z⁻¹ * (ZS * Z⁻¹)⁻¹) :=
      tsum_congr (fun γ => by
        have hin : glue ω (bigExterior ξS γ) ∈ s := by
          rw [hs]
          intro i
          rfl
        rw [PMF.filter_apply, Set.indicator_of_mem hin, hdenom,
          hP, FK.FinitePlane.normalizedPMF_apply])
    have hstep3 : (∑' γ : Fin a → Bool,
          (w (glue ω (bigExterior ξS γ)) : ℝ≥0∞) * Z⁻¹ * (ZS * Z⁻¹)⁻¹)
        = Y ω * Z⁻¹ * (ZS * Z⁻¹)⁻¹ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hYapp]
    rw [PMF.map_apply]
    trans (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
      if ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω
        then (P.filter s hsupp) ρ else 0)
    · apply tsum_congr
      intro ρ
      by_cases hpre : ρ ∈ prefixEvent (I := I) (a := a) ξS
      · have hiff : (ω = ρ ∘ Sum.inl) ↔
            ρ ∈ prefixFiberSet (I := I) (a := a) ξS ω := by
          simp only [prefixFiberSet, Set.mem_ofPred_eq, hpre, true_and]
          exact eq_comm
        by_cases h : ω = ρ ∘ Sum.inl
        · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
        · rw [ite_eq_right h, ite_eq_right (fun hc => h (hiff.mpr hc))]
      · have hz : (P.filter s hsupp) ρ = 0 :=
          PMF.filter_apply_eq_zero_of_notMem hsupp (by rwa [hs])
        have hout : ρ ∉ prefixFiberSet (I := I) (a := a) ξS ω := fun hc => hpre hc.1
        rw [hz, ite_eq_right hout]
        exact ite_self 0
    · rw [tsum_prefix_fiber_fixed (F := fun ρ => (P.filter s hsupp) ρ) ξS ω]
      exact hstep2.trans hstep3
  apply PMF.ext
  intro ω
  rw [key ω, FK.FinitePlane.normalizedPMF_apply]
  have hcoe : ∀ ω : I → Bool,
      ((∑ γ : Fin a → Bool, w (glue ω (bigExterior ξS γ)) : NNReal) : ℝ≥0∞) = Y ω :=
    fun ω => (hYcoe ω).symm
  have hcoe2 : (∑' b : I → Bool,
      ((∑ γ : Fin a → Bool, w (glue b (bigExterior ξS γ)) : NNReal) : ℝ≥0∞)) = ZS := by
    rw [hZS]
    exact tsum_congr hcoe
  rw [hcoe, hcoe2]
  rw [ENNReal.mul_inv (Or.inl hZS0) (Or.inl hZStop), inv_inv]
  calc Y ω * Z⁻¹ * (ZS⁻¹ * Z) = Y ω * (Z⁻¹ * Z) * ZS⁻¹ := by ac_rfl
    _ = Y ω * 1 * ZS⁻¹ := by rw [ENNReal.inv_mul_cancel hZ0 hZtop]
    _ = Y ω * ZS⁻¹ := by rw [mul_one]

/-! ## The FK prefix identity -/

/-- **Residual of `docs/REGION-CONFINEMENT.md`.**  Under a region-confined
boundary matching `θ`, conditioning the actual FK law of the large ambient graph
on the event that the small exterior block equals `ξS`, and then reading off the
region configuration, gives exactly the actual region FK law with boundary `θ`.

All hypotheses are the ones already used by `ambientWeight_prefix_sum`:
confinement, matching on the region, separatedness of the *small* exterior bits
(the added labels are arbitrary and only required to avoid the region). -/
theorem prefix_filter_fkPMF_eq_region {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξS : Fin k → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).filter
          (prefixEvent (I := I) (a := a) ξS)
          (prefixEvent_support si ti so xo ao bo ζ hq hp₀ hp₁ ξS)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  classical
  set Gb : LabelledMultigraph :=
    ambientOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)) with hGb
  set w : (I ⊕ (Fin k ⊕ Fin a) → Bool) → NNReal := fun ρ => Gb.fkWeight q p ζ ρ with hwdef
  have hw : ∀ ρ, 0 < w ρ := fun ρ => Gb.fkWeight_pos hq hp₀ hp₁ ζ ρ
  set regionW : (I → Bool) → NNReal :=
    fun ω => FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω
    with hregionW
  have hregionWpos : ∀ ω, 0 < regionW ω :=
    fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ ω
  set cst : NNReal := ∑ γ : Fin a → Bool,
      FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) *
        q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ
          (bigExterior ξS γ)).ConnectedComponent with hcst
  -- the fibre sum is proportional to the region weight
  have hprop : ∀ ω : I → Bool,
      (∑ γ : Fin a → Bool, w (glue ω (bigExterior ξS γ))) = cst * regionW ω := by
    intro ω
    have h := ambientWeight_prefix_sum si ti so xo ao bo θ ζ ξS ω
      hconf hθ hsepS havoid q p
    simp only [tsum_fintype] at h
    exact h
  have hcstpos : 0 < cst := by
    rw [hcst]
    exact Finset.sum_pos (fun γ _ => mul_pos (FK.FinitePlane.edgeWeight_pos' hp₀ hp₁ _)
      (pow_pos hq _)) Finset.univ_nonempty
  -- normalization cancels the common factor
  have hpropn : FK.FinitePlane.normalizedPMF
        (fun ω : I → Bool => ∑ γ : Fin a → Bool, w (glue ω (bigExterior ξS γ)))
        (fun ω => Finset.sum_pos (fun γ _ => hw _) Finset.univ_nonempty) =
      FK.FinitePlane.normalizedPMF regionW hregionWpos := by
    have h := FK.FinitePlane.normalizedPMF_map_eq_of_proportional
      (Equiv.refl (I → Bool)) regionW
      (fun ω : I → Bool => ∑ γ : Fin a → Bool, w (glue ω (bigExterior ξS γ)))
      cst hcstpos hregionWpos
      (fun ω => Finset.sum_pos (fun γ _ => hw _) Finset.univ_nonempty)
      (fun ω => hprop ω)
    simp only [Equiv.coe_refl, PMF.map_id] at h
    exact h.symm
  -- the general prefix fibre-sum lemma, transported to the actual FK law
  have hmain := map_prefix_filter_normalizedPMF (I := I) (a := a) w hw ξS
  have hreg : FK.FinitePlane.normalizedPMF regionW hregionWpos =
      (regionGraph si ti).fkPMF hq hp₁.le θ := rfl
  refine hmain.trans ?_
  rw [hpropn, hreg]

/-! ## Pointwise weight factorization at a prefix configuration -/

/-- The ambient FK weight at a prefix configuration is the region FK weight times
the effective added-block weight `e γ`.  This is the pointwise form of the fibre
computation inside `ambientWeight_prefix_sum`. -/
theorem fkWeight_glue_prefix_eq {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξS : Fin k → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    (q p : NNReal) (ω : I → Bool) (γ : Fin a → Bool) :
    (ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkWeight q p ζ (glue ω (bigExterior ξS γ)) =
      FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) *
        q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ
          (bigExterior ξS γ)).ConnectedComponent *
      FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω := by
  have h1 := FK.FinitePlane.ArbitraryBoundary.fkWeight_glue
    (s := splitSource si (bigSo so ao)) (t := splitTarget ti (bigXo xo bo)) ζ q p ω
    (bigExterior ξS γ)
  have h2 := interiorWeight_confined_eq si ti (bigSo so ao) (bigXo xo bo) θ ζ
    (bigExterior ξS γ) ω hconf hθ
    (separated_bigExterior si ti so xo ao bo ξS γ hsepS havoid) q p
  have h2' : (interiorOfSum (splitSource si (bigSo so ao))
      (splitTarget ti (bigXo xo bo))).fkWeight q p
        (effectiveBoundary (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo)) ζ (bigExterior ξS γ)) ω =
      q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ
        (bigExterior ξS γ)).ConnectedComponent *
      FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω :=
    (FK.FinitePlane.plane_fkWeight_eq_actual
      (interiorOfSum (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)))
      (effectiveBoundary (splitSource si (bigSo so ao)) (splitTarget ti (bigXo xo bo)) ζ
        (bigExterior ξS γ)) q p ω).symm.trans h2
  exact h1.trans ((congrArg (fun t =>
    FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) * t) h2').trans
    (mul_assoc _ _ _).symm)

/-! ## The set-level factorization -/

/-- The product event: prescribed small exterior bits, region bits in `A`, added
bits in `D`. -/
def prefixSet {k a : ℕ} (ξS : Fin k → Bool) (A : Set (I → Bool))
    (D : Set (Fin a → Bool)) : Set (I ⊕ (Fin k ⊕ Fin a) → Bool) :=
  prefixEvent (I := I) (a := a) ξS ∩ (fun ρ => ρ ∘ Sum.inl) ⁻¹' A ∩
    (fun ρ => ρ ∘ Sum.inr ∘ Sum.inr) ⁻¹' D

omit [Fintype I] in
lemma prefixSet_subset {k a : ℕ} (ξS : Fin k → Bool) (A : Set (I → Bool))
    (D : Set (Fin a → Bool)) :
    prefixSet (I := I) (a := a) ξS A D ⊆ prefixEvent (I := I) (a := a) ξS :=
  fun _ h => h.1.1

omit [Fintype I] in
lemma prefixSet_subset_univ_left {k a : ℕ} (ξS : Fin k → Bool) (A : Set (I → Bool))
    (D : Set (Fin a → Bool)) :
    prefixSet (I := I) (a := a) ξS A D ⊆ prefixSet (I := I) (a := a) ξS Set.univ D := by
  intro x hx
  exact ⟨⟨hx.1.1, Set.mem_univ _⟩, hx.2⟩

omit [Fintype I] in
lemma mem_prefixSet_singleton {k a : ℕ} {ξS : Fin k → Bool} {D : Set (Fin a → Bool)}
    {ω : I → Bool} {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool}
    (hx : ρ ∈ prefixSet (I := I) (a := a) ξS Set.univ D) (he : ρ ∘ Sum.inl = ω) :
    ρ ∈ prefixSet (I := I) (a := a) ξS ({ω} : Set (I → Bool)) D := by
  refine ⟨⟨hx.1.1, ?_⟩, hx.2⟩
  show ρ ∘ Sum.inl ∈ ({ω} : Set (I → Bool))
  rw [Set.mem_singleton_iff]
  exact he

omit [Fintype I] in
lemma mem_prefixSet_singleton_fst {k a : ℕ} {ξS : Fin k → Bool} {D : Set (Fin a → Bool)}
    {ω : I → Bool} {ρ : I ⊕ (Fin k ⊕ Fin a) → Bool}
    (hx : ρ ∈ prefixSet (I := I) (a := a) ξS ({ω} : Set (I → Bool)) D) :
    ρ ∘ Sum.inl = ω := by
  simpa using hx.1.2

/-- The added-block weight of the confined split. -/
noncomputable def addedWeight {k a : ℕ} (si : I → W) (ti : I → W)
    (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K) (ζ : Setoid (W ⊕ K))
    (ξS : Fin k → Bool) (q p : NNReal) (γ : Fin a → Bool) : NNReal :=
  FK.FinitePlane.edgeWeight p (1 - p) (bigExterior ξS γ) *
    q ^ Nat.card (rightConfinedGraph si ti (bigSo so ao) (bigXo xo bo) ζ
      (bigExterior ξS γ)).ConnectedComponent

lemma addedWeight_pos {k a : ℕ} {si : I → W} {ti : I → W}
    {so xo : Fin k → W ⊕ K} {ao bo : Fin a → W ⊕ K} {ζ : Setoid (W ⊕ K)}
    {ξS : Fin k → Bool} {q p : NNReal} {γ : Fin a → Bool}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < addedWeight si ti so xo ao bo ζ ξS q p γ :=
  mul_pos (FK.FinitePlane.edgeWeight_pos' hp₀ hp₁ _) (pow_pos hq _)

/-- Transfer of a prefix-event sum to the region/added pair sum, for an
arbitrary nonnegative integrand.  Direct consequence of `tsum_prefix_fiber` and
`ENNReal.tsum_prod`. -/
theorem tsum_indicator_prefixEvent {k a : ℕ}
    {F : (I ⊕ (Fin k ⊕ Fin a) → Bool) → ℝ≥0∞} (ξS : Fin k → Bool) :
    (∑' ρ, (prefixEvent (I := I) (a := a) ξS).indicator F ρ) =
      ∑' z : (I → Bool) × (Fin a → Bool),
        F (glue z.1 (bigExterior ξS z.2)) := by
  rw [show (∑' ρ, (prefixEvent (I := I) (a := a) ξS).indicator F ρ) =
      ∑' ρ, if ρ ∈ prefixEvent (I := I) (a := a) ξS then F ρ else 0 from
    tsum_congr (fun ρ => by rw [Set.indicator_apply])]
  rw [tsum_prefix_fiber (F := F) ξS]
  exact (ENNReal.tsum_prod).symm

/-- **Weight-level set factorization.**  The ambient weight mass of the product
event (prescribed small exterior bits) × (region event `A`) × (added event `D`)
is the product of the region mass and the added mass. -/
theorem ambientWeight_set_factorization {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξS : Fin k → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    (q p : NNReal) (A : Set (I → Bool)) (D : Set (Fin a → Bool)) :
    (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
        (prefixSet (I := I) (a := a) ξS A D).indicator
          (fun ρ => ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ) =
      (∑' ω : I → Bool, A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) ω) *
        (∑' γ : Fin a → Bool, D.indicator (fun γ =>
          (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) γ) := by
  classical
  have hpt : ∀ ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
      (prefixSet (I := I) (a := a) ξS A D).indicator
          (fun ρ => ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ =
        (prefixEvent (I := I) (a := a) ξS).indicator (fun ρ =>
          A.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inl) *
            D.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inr ∘ Sum.inr) *
            ((ambientOfSum (splitSource si (bigSo so ao))
              (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ := by
    intro ρ
    by_cases hpre : ρ ∈ prefixEvent (I := I) (a := a) ξS
    · by_cases hA : (ρ ∘ Sum.inl) ∈ A
      · by_cases hD : (ρ ∘ Sum.inr ∘ Sum.inr) ∈ D
        · have hS : ρ ∈ prefixSet (I := I) (a := a) ξS A D := by
            simp only [prefixSet, Set.mem_inter_iff, Set.mem_preimage]
            exact ⟨⟨hpre, hA⟩, hD⟩
          rw [Set.indicator_of_mem hS, Set.indicator_of_mem hpre,
            Set.indicator_of_mem hA, Set.indicator_of_mem hD]
          simp
        · have hS : ρ ∉ prefixSet (I := I) (a := a) ξS A D := by
            intro hx
            simp only [prefixSet, Set.mem_inter_iff, Set.mem_preimage] at hx
            exact hD hx.2
          rw [Set.indicator_of_notMem hS, Set.indicator_of_mem hpre,
            Set.indicator_of_mem hA, Set.indicator_of_notMem hD]
          simp
      · have hS : ρ ∉ prefixSet (I := I) (a := a) ξS A D := by
          intro hx
          simp only [prefixSet, Set.mem_inter_iff, Set.mem_preimage] at hx
          exact hA hx.1.2
        rw [Set.indicator_of_notMem hS, Set.indicator_of_mem hpre,
          Set.indicator_of_notMem hA]
        simp
    · have hS : ρ ∉ prefixSet (I := I) (a := a) ξS A D :=
        fun hx => hpre (prefixSet_subset _ _ _ hx)
      rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hpre]
  rw [show (∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
        (prefixSet (I := I) (a := a) ξS A D).indicator
          (fun ρ => ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ) =
      ∑' ρ : I ⊕ (Fin k ⊕ Fin a) → Bool,
        (prefixEvent (I := I) (a := a) ξS).indicator (fun ρ =>
          A.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inl) *
            D.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inr ∘ Sum.inr) *
            ((ambientOfSum (splitSource si (bigSo so ao))
              (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ
      from tsum_congr hpt]
  rw [tsum_indicator_prefixEvent (I := I) (a := a)
    (F := fun ρ => A.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inl) *
      D.indicator (fun _ => (1 : ℝ≥0∞)) (ρ ∘ Sum.inr ∘ Sum.inr) *
      ((ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ξS]
  have hz : ∀ z : (I → Bool) × (Fin a → Bool),
      A.indicator (fun _ => (1 : ℝ≥0∞))
          ((glue z.1 (bigExterior ξS z.2)) ∘ Sum.inl) *
        D.indicator (fun _ => (1 : ℝ≥0∞))
          ((glue z.1 (bigExterior ξS z.2)) ∘ Sum.inr ∘ Sum.inr) *
        ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ
            (glue z.1 (bigExterior ξS z.2)) : ℝ≥0∞) =
      A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) z.1 *
        D.indicator (fun γ =>
          (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) z.2 := by
    intro z
    have h1 : A.indicator (fun _ => (1 : ℝ≥0∞))
        ((glue z.1 (bigExterior ξS z.2)) ∘ Sum.inl) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) z.1 := rfl
    have h2 : D.indicator (fun _ => (1 : ℝ≥0∞))
        ((glue z.1 (bigExterior ξS z.2)) ∘ Sum.inr ∘ Sum.inr) =
        D.indicator (fun _ => (1 : ℝ≥0∞)) z.2 := rfl
    rw [h1, h2, fkWeight_glue_prefix_eq si ti so xo ao bo θ ζ ξS hconf hθ hsepS havoid
      q p z.1 z.2]
    simp only [addedWeight]
    push_cast
    simp only [Set.indicator_apply]
    by_cases hA : z.1 ∈ A <;> by_cases hD : z.2 ∈ D
    · simp only [ite_eq_left hA, ite_eq_left hD]; ac_rfl
    · simp only [ite_eq_left hA, ite_eq_right hD]; simp
    · simp only [ite_eq_right hA, ite_eq_left hD]; simp
    · simp only [ite_eq_right hA, ite_eq_right hD]; simp
  trans ∑' z : (I → Bool) × (Fin a → Bool),
      A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) z.1 *
        D.indicator (fun γ =>
          (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) z.2
  · apply tsum_congr
    intro z
    exact hz z
  rw [tsum_fintype, tsum_fintype, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

/-! ## The PMF-level common-upper identity -/

/-- Mass of a set under the actual ambient FK law, in terms of the ambient
weight mass and the inverse partition function. -/
theorem fkPMF_mass_eq {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (ζ : Setoid (W ⊕ K)) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (S : Set (I ⊕ (Fin k ⊕ Fin a) → Bool)) :
    (∑' ρ, S.indicator (fun ρ =>
        ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) ρ) ρ) =
      (∑' ρ, S.indicator (fun ρ =>
          ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ) *
        (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹ := by
  classical
  rw [show (∑' ρ, S.indicator (fun ρ =>
        ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) ρ) ρ) =
      ∑' ρ, S.indicator (fun ρ =>
          ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞)) ρ *
        (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹ from ?_]
  · exact ENNReal.tsum_mul_right
  apply tsum_congr
  intro ρ
  by_cases h : ρ ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact FK.FinitePlane.normalizedPMF_apply
      (fun ρ => (ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ)
      (fun ρ => (ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkWeight_pos hq hp₀ hp₁ ζ ρ) ρ
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- **PMF-level common-upper identity (ambient form).**  For the actual FK law of
the large ambient graph with a region-confined boundary, the mass of the product
event "region bits in `A`, small exterior bits `ξS`, added bits in `D`" is the
product of the region FK mass of `A` and the mass of the partial event "small
exterior bits `ξS`, added bits in `D`".

Equivalently: conditionally on the small exterior prefix and any added-block
stratum, the region configuration has exactly the region FK law with boundary
`θ` — the region factor is independent of the added block.  This is the ambient
identity that a common-upper good-intersection comparison consumes. -/
theorem prefix_mass_factorization {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξS : Fin k → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (I → Bool)) (D : Set (Fin a → Bool)) :
    (∑' ρ, (prefixSet (I := I) (a := a) ξS A D).indicator (fun ρ =>
        ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) ρ) ρ) =
      (∑' ω, A.indicator (fun ω =>
          ((regionGraph si ti).fkPMF hq hp₁.le θ) ω) ω) *
        (∑' ρ, (prefixSet (I := I) (a := a) ξS Set.univ D).indicator (fun ρ =>
          ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ) ρ) ρ) := by
  classical
  -- the two ambient weight masses
  set Zinv : ℝ≥0∞ := (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
      (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹ with hZinv
  set RW : (I → Bool) → NNReal :=
    fun ω => FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω
    with hRW
  have hRWpos : ∀ ω, 0 < RW ω :=
    fun ω => FK.FinitePlane.fkWeight_pos hq hp₀ hp₁ _ ω
  have hregionmass : (∑' ω, A.indicator (fun ω =>
        ((regionGraph si ti).fkPMF hq hp₁.le θ) ω) ω) =
      (∑' ω, A.indicator (fun ω => (RW ω : ℝ≥0∞)) ω) *
        (∑' ω, (RW ω : ℝ≥0∞))⁻¹ := by
    rw [show (∑' ω, A.indicator (fun ω =>
          ((regionGraph si ti).fkPMF hq hp₁.le θ) ω) ω) =
        ∑' ω, A.indicator (fun ω => (RW ω : ℝ≥0∞)) ω *
          (∑' ω, (RW ω : ℝ≥0∞))⁻¹ from ?_]
    · exact ENNReal.tsum_mul_right
    apply tsum_congr
    intro ω
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      exact FK.FinitePlane.normalizedPMF_apply RW hRWpos ω
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  -- ambient weight masses of the two events
  have hAD := ambientWeight_set_factorization si ti so xo ao bo θ ζ ξS hconf hθ
    hsepS havoid q p A D
  have huD := ambientWeight_set_factorization si ti so xo ao bo θ ζ ξS hconf hθ
    hsepS havoid q p Set.univ D
  have huD' : (∑' ω : I → Bool, Set.univ.indicator (fun ω => (RW ω : ℝ≥0∞)) ω) =
      ∑' ω : I → Bool, (RW ω : ℝ≥0∞) := by
    apply tsum_congr
    intro ω
    exact Set.indicator_of_mem (Set.mem_univ ω) _
  rw [huD'] at huD
  -- region partition function facts
  have hRW0 : (∑' ω : I → Bool, (RW ω : ℝ≥0∞)) ≠ 0 :=
    FK.FinitePlane.tsum_coe_ne_zero_of_pos RW hRWpos
  have hRWtop : (∑' ω : I → Bool, (RW ω : ℝ≥0∞)) ≠ ∞ :=
    FK.FinitePlane.tsum_coe_ne_top RW
  -- assemble
  rw [fkPMF_mass_eq si ti so xo ao bo ζ hq hp₀ hp₁ (prefixSet (I := I) (a := a) ξS A D),
    fkPMF_mass_eq si ti so xo ao bo ζ hq hp₀ hp₁ (prefixSet (I := I) (a := a) ξS Set.univ D),
    hAD, huD, hregionmass]
  simp only [hRW]
  -- remaining: pure commutative-monoid algebra with `R⁻¹ * R = 1`
  have hcancel : (∑' ω : I → Bool,
      (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞))⁻¹ *
      (∑' ω : I → Bool,
        (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) = 1 :=
    ENNReal.inv_mul_cancel hRW0 hRWtop
  rw [show
      ((∑' ω : I → Bool, A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) ω) *
        (∑' γ : Fin a → Bool, D.indicator (fun γ =>
          (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) γ)) *
        (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹ =
      ((∑' ω : I → Bool, A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) ω) *
        (∑' ω : I → Bool,
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞))⁻¹) *
        (((∑' ω : I → Bool,
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) *
          (∑' γ : Fin a → Bool, D.indicator (fun γ =>
            (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) γ)) *
        (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹) from by
    rw [show
      ((∑' ω : I → Bool, A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) ω) *
        (∑' ω : I → Bool,
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞))⁻¹) *
        (((∑' ω : I → Bool,
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) *
          (∑' γ : Fin a → Bool, D.indicator (fun γ =>
            (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) γ)) *
        (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹) =
      ((∑' ω : I → Bool, A.indicator (fun ω =>
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞)) ω) *
        ((∑' ω : I → Bool,
          (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞))⁻¹ *
          (∑' ω : I → Bool,
            (FK.FinitePlane.fkWeight q p ((regionGraph si ti).componentCount θ) ω : ℝ≥0∞))) *
        (∑' γ : Fin a → Bool, D.indicator (fun γ =>
          (addedWeight si ti so xo ao bo ζ ξS q p γ : ℝ≥0∞)) γ)) *
        (∑' ρ, ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkWeight q p ζ ρ : ℝ≥0∞))⁻¹ from by
      ac_rfl]
    rw [hcancel, mul_one]]

/-! ## Two-sided boundary specializations (the project's standard convention) -/

/-- The `sumBoundary`-shaped two-sided boundary is region-confined and matches
`θ` on the region, so the whole prefix identity applies without any further
boundary hypothesis. -/
theorem prefix_filter_fkPMF_eq_region_twoSided {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid K) (ξS : Fin k → Bool)
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le
            (FK.Finite.MarkovFactorization.sumBoundary
              (G := regionGraph si ti)
              (H := FK.Exploration.WiredRightInterior.rightVertexGraph K) θ ζ)).filter
          (prefixEvent (I := I) (a := a) ξS)
          (prefixEvent_support si ti so xo ao bo _ hq hp₀ hp₁ ξS)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  refine prefix_filter_fkPMF_eq_region si ti so xo ao bo θ _ ξS ?_ ?_ hsepS havoid hq hp₀ hp₁
  · intro c y h
    cases y with
    | inl c' => exact ⟨c', rfl⟩
    | inr kk => exact h.elim
  · intro c c'
    exact Iff.rfl

/-- The common-upper mass identity for the standard two-sided boundary. -/
theorem prefix_mass_factorization_twoSided {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid K) (ξS : Fin k → Bool)
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (A : Set (I → Bool)) (D : Set (Fin a → Bool)) :
    (∑' ρ, (prefixSet (I := I) (a := a) ξS A D).indicator (fun ρ =>
        ((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le
          (FK.Finite.MarkovFactorization.sumBoundary
            (G := regionGraph si ti)
            (H := FK.Exploration.WiredRightInterior.rightVertexGraph K) θ ζ)) ρ) ρ) =
      (∑' ω, A.indicator (fun ω =>
          ((regionGraph si ti).fkPMF hq hp₁.le θ) ω) ω) *
        (∑' ρ, (prefixSet (I := I) (a := a) ξS Set.univ D).indicator (fun ρ =>
          ((ambientOfSum (splitSource si (bigSo so ao))
            (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le
            (FK.Finite.MarkovFactorization.sumBoundary
              (G := regionGraph si ti)
              (H := FK.Exploration.WiredRightInterior.rightVertexGraph K) θ ζ)) ρ) ρ) := by
  refine prefix_mass_factorization si ti so xo ao bo θ _ ξS ?_ ?_ hsepS havoid hq hp₀ hp₁ A D
  · intro c y h
    cases y with
    | inl c' => exact ⟨c', rfl⟩
    | inr kk => exact h.elim
  · intro c c'
    exact Iff.rfl

/-! ## The conditional region law on a prefix stratum -/

/-- **General conditional-law lemma.**  Let `P` be a finite PMF, `T ⊆ α` a set of
positive mass, `f : α → β` and `c : PMF β`.  If the family `TA A` is the trace of
`f ⁻¹' A` on `T` and the `P`-masses of `TA A` factor as `c(A)` times the mass of
`T`, then conditioning `P` on `T` and pushing forward along `f` gives `c`. -/
theorem map_filter_eq_of_mass_factorization {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (f : α → β) (T : Set α) (hT : ∃ a ∈ T, a ∈ P.support)
    (TA : Set β → Set α) (hTA : ∀ A, TA A = f ⁻¹' A ∩ T) (c : PMF β)
    (hmass : ∀ A : Set β, (∑' a, (TA A).indicator (fun a => P a) a) =
      (∑' b, A.indicator (fun b => c b) b) * (∑' a, T.indicator (fun a => P a) a)) :
    (P.filter T hT).map f = c := by
  classical
  have hmem : ∀ (A : Set β) (a : α), a ∈ TA A ↔ (f a ∈ A ∧ a ∈ T) := by
    intro A a
    rw [hTA A]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hQmass : ∀ A : Set β,
      (∑' a, (TA A).indicator (fun a => (P.filter T hT) a) a) =
        (∑' a, (TA A).indicator (fun a => P a) a) *
          (∑' a, T.indicator (fun a => P a) a)⁻¹ := by
    intro A
    rw [show (∑' a, (TA A).indicator (fun a => (P.filter T hT) a) a) =
        ∑' a, (TA A).indicator (fun a => P a) a *
          (∑' a, T.indicator (fun a => P a) a)⁻¹ from ?_]
    · exact ENNReal.tsum_mul_right
    apply tsum_congr
    intro a
    by_cases h : a ∈ TA A
    · have haT : a ∈ T := ((hmem A a).mp h).2
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h, PMF.filter_apply hT,
        Set.indicator_of_mem haT]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  have hM0 : (∑' a, T.indicator (fun a => P a) a) ≠ 0 := by
    obtain ⟨a₀, ha₀, hsupp₀⟩ := hT
    intro hzero
    rw [ENNReal.tsum_eq_zero] at hzero
    exact (PMF.mem_support_iff _ _).mp hsupp₀ (by
      have := hzero a₀
      rwa [Set.indicator_of_mem ha₀] at this)
  have hMtop : (∑' a, T.indicator (fun a => P a) a) ≠ ∞ := by
    rw [tsum_fintype,
      show (∑ a, T.indicator (fun a => P a) a) =
        ∑ a ∈ (Finset.univ : Finset α), T.indicator (fun a => P a) a from by simp]
    refine (ENNReal.sum_ne_top).mpr (fun a _ => ?_)
    by_cases h : a ∈ T
    · rw [Set.indicator_of_mem h]
      exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem h]
      exact ENNReal.zero_ne_top
  have hsingle : ∀ b : β, (∑' b', ({b} : Set β).indicator (fun b' => c b') b') = c b := by
    intro b
    rw [tsum_eq_single b]
    · exact Set.indicator_of_mem (Set.mem_singleton b) _
    · intro b' hb'
      exact Set.indicator_of_notMem (by simpa using hb') _
  apply PMF.ext
  intro b
  have hmap : ((P.filter T hT).map f) b =
      ∑' a, (TA {b}).indicator (fun a => (P.filter T hT) a) a := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro a
    by_cases h : a ∈ TA {b}
    · have hfb : f a = b := ((hmem {b} a).mp h).1
      rw [ite_eq_left hfb.symm, Set.indicator_of_mem h]
    · by_cases haT : a ∈ T
      · have hne : ¬ (b = f a) := fun he =>
          h ((hmem {b} a).mpr ⟨by rw [he]; simp, haT⟩)
        rw [ite_eq_right hne, Set.indicator_of_notMem h]
      · rw [Set.indicator_of_notMem h, PMF.filter_apply_eq_zero_of_notMem hT haT]
        by_cases he : b = f a <;> simp [he]
  rw [hmap, hQmass {b}, hmass {b}, hsingle, mul_assoc,
    ENNReal.mul_inv_cancel hM0 hMtop, mul_one]

/-- **Conditional region law on a prefix stratum.**  Conditioning the actual FK law
of the large ambient graph on the event "small exterior bits equal `ξS` **and**
added bits lie in `D`" and then reading off the region configuration gives
exactly the actual region FK law with boundary `θ`, for every added-block set `D`
whose stratum has positive ambient mass.

This is the conditional-law form of `prefix_mass_factorization`: the region
factor is independent of the added block, so restricting the added block cannot
change the region law. -/
theorem prefix_conditional_fkPMF_eq_region {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid (W ⊕ K)) (ξS : Fin k → Bool)
    (hconf : ∀ (c : W) (y : W ⊕ K), ζ.r (Sum.inl c) y → ∃ c', y = Sum.inl c')
    (hθ : ∀ (c c' : W), ζ.r (Sum.inl c) (Sum.inl c') ↔ θ.r c c')
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (D : Set (Fin a → Bool))
    (hsupp : ∃ ρ ∈ prefixSet (I := I) (a := a) ξS Set.univ D,
      ρ ∈ ((ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).support) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ).filter
            (prefixSet (I := I) (a := a) ξS Set.univ D) hsupp) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  refine map_filter_eq_of_mass_factorization
    (P := ((ambientOfSum (splitSource si (bigSo so ao))
      (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le ζ))
    (f := fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
    (T := prefixSet (I := I) (a := a) ξS Set.univ D) hsupp
    (TA := fun A => prefixSet (I := I) (a := a) ξS A D)
    (c := (regionGraph si ti).fkPMF hq hp₁.le θ) ?_ ?_
  · intro A
    show prefixSet (I := I) (a := a) ξS A D =
      (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl) ⁻¹' A ∩
        prefixSet (I := I) (a := a) ξS Set.univ D
    rw [prefixSet, prefixSet, Set.preimage_univ, Set.inter_univ,
      Set.inter_comm (prefixEvent (I := I) (a := a) ξS), Set.inter_assoc]
  · intro A
    exact prefix_mass_factorization si ti so xo ao bo θ ζ ξS hconf hθ hsepS havoid
      hq hp₀ hp₁ A D
/-! ## Non-vacuity of the hypotheses -/

section Nonvacuity

/-- The hypotheses of the two-sided common-upper identity are simultaneously
satisfiable on a concrete four-vertex, two-edge geometry: region `Fin 2` with one
internal edge `0–1`, outside block `Fin 2`, one small exterior label and one added
label, both with endpoints in the outside block.  (The identity itself is then a
statement about that actual graph, not a vacuous one.) -/
example : True := by
  have _ := prefix_mass_factorization_twoSided (W := Fin 2) (K := Fin 2) (I := Fin 1)
    (k := 1) (a := 1) (q := 1 / 2) (p := 1 / 2)
    (si := fun _ => 0) (ti := fun _ => 1)
    (so := fun _ => Sum.inr 0) (xo := fun _ => Sum.inr 1)
    (ao := fun _ => Sum.inr 1) (bo := fun _ => Sum.inr 0)
    (θ := ⊥) (ζ := ⊥) (ξS := fun _ => false)
    (fun _ h => absurd h (by simp))
    (fun _ => ⟨not_inRegion_inr _, not_inRegion_inr _⟩)
    (by norm_num) (by norm_num) (by norm_num)
    (A := Set.univ) (D := Set.univ)
  trivial

end Nonvacuity
/-- The conditional region law on a prefix stratum for the standard two-sided
boundary. -/
theorem prefix_conditional_fkPMF_eq_region_twoSided {k a : ℕ}
    (si : I → W) (ti : I → W) (so xo : Fin k → W ⊕ K) (ao bo : Fin a → W ⊕ K)
    (θ : Setoid W) (ζ : Setoid K) (ξS : Fin k → Bool)
    (hsepS : ∀ i : Fin k, ξS i = true →
      ¬ InRegion (K := K) (so i) ∧ ¬ InRegion (K := K) (xo i))
    (havoid : ∀ j : Fin a, ¬ InRegion (K := K) (ao j) ∧ ¬ InRegion (K := K) (bo j))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (D : Set (Fin a → Bool))
    (hsupp : ∃ ρ ∈ prefixSet (I := I) (a := a) ξS Set.univ D,
      ρ ∈ ((ambientOfSum (splitSource si (bigSo so ao))
        (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le
        (FK.Finite.MarkovFactorization.sumBoundary
          (G := regionGraph si ti)
          (H := FK.Exploration.WiredRightInterior.rightVertexGraph K) θ ζ)).support) :
    PMF.map (fun ρ : I ⊕ (Fin k ⊕ Fin a) → Bool => ρ ∘ Sum.inl)
        (((ambientOfSum (splitSource si (bigSo so ao))
          (splitTarget ti (bigXo xo bo))).fkPMF hq hp₁.le
          (FK.Finite.MarkovFactorization.sumBoundary
            (G := regionGraph si ti)
            (H := FK.Exploration.WiredRightInterior.rightVertexGraph K) θ ζ)).filter
            (prefixSet (I := I) (a := a) ξS Set.univ D) hsupp) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  refine prefix_conditional_fkPMF_eq_region si ti so xo ao bo θ _ ξS ?_ ?_ hsepS havoid
    hq hp₀ hp₁ D hsupp
  · intro c y h
    cases y with
    | inl c' => exact ⟨c', rfl⟩
    | inr kk => exact h.elim
  · intro c c'
    exact Iff.rfl

end FK.RegionConfinement.PrefixContinuation

#print axioms FK.RegionConfinement.PrefixContinuation.prefixEvent_support_normalizedPMF
#print axioms FK.RegionConfinement.PrefixContinuation.map_prefix_filter_normalizedPMF
#print axioms FK.RegionConfinement.PrefixContinuation.prefix_filter_fkPMF_eq_region
#print axioms FK.RegionConfinement.PrefixContinuation.fkWeight_glue_prefix_eq
#print axioms FK.RegionConfinement.PrefixContinuation.tsum_indicator_prefixEvent
#print axioms FK.RegionConfinement.PrefixContinuation.ambientWeight_set_factorization
#print axioms FK.RegionConfinement.PrefixContinuation.fkPMF_mass_eq
#print axioms FK.RegionConfinement.PrefixContinuation.prefix_mass_factorization
#print axioms FK.RegionConfinement.PrefixContinuation.prefix_filter_fkPMF_eq_region_twoSided
#print axioms FK.RegionConfinement.PrefixContinuation.prefix_mass_factorization_twoSided
#print axioms FK.RegionConfinement.PrefixContinuation.map_filter_eq_of_mass_factorization
#print axioms FK.RegionConfinement.PrefixContinuation.prefix_conditional_fkPMF_eq_region
#print axioms FK.RegionConfinement.PrefixContinuation.prefix_conditional_fkPMF_eq_region_twoSided
