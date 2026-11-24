/-
Worker m4 contribution, formalization of arXiv:2512.16486 (Beffara--Faipeur--Oke).

# Finite profile-mass derivatives, pivotal identification, and the AG trade reduction

`FK.AGDifferentialShift` reduces the Aizenman--Grimmett strict shift of the
critical point to two analytic inputs for the finite-volume profile masses of
`FK.EssentialWindow`: a Fréchet derivative `hderiv` for the clamped
decrement/increment profiles on the parameter plane, and a trade sign `htrade`.

This module

* identifies the clamped profile mass with the product polynomial
  `FK.MargulisRussoFinite.eventWeight` of `FK.MargulisRussoFinite` under the
  actual `FKLimit.bernoulliProduct` law (`mass_eq_eventWeight`,
  `incMass_eq_eventWeight`, using `Measure.infinitePi_eq_pi`);
* proves the interior Fréchet derivative of the *clamped* profile masses
  (`hasFDerivAt_massPair_of_interior`, `hasFDerivAt_incMassPair_of_interior`),
  which discharges the derivative binder wherever the unit-interval clamp is
  inactive, i.e. on `0 < b < 1`, `0 ≤ ε < b` (decrement) and `0 < a < 1`,
  `0 ≤ ε`, `a + ε < 1` (increment);
* identifies the trade directional derivative with expected pivotal masses
  (`massPair_deriv_decomp`, `incMassPair_deriv_decomp`): in direction `(p, q)`
  the derivative is `p · (total pivotal mass) - q · (pivotal mass on `S`)`,
  resp. `p · (total) + q · (on `S`)` for the increment plane;
* repairs the strict shift theorems so that only interior derivative data is
  required (`exists_subcritical_decrement_interior`,
  `exists_supercritical_increment_interior`).  The closed-region binder of the
  public `hderiv` is *not* satisfiable by the clamped profiles: on the collision
  line `ε = b` the clamped mass is `max 0 (b - ε)`, which is not differentiable
  (`not_hasFDerivAt_massPair_clamp`);
* packages the resulting `hAG` inputs
  (`decrement_AGInput_of_pivotTrade`, `increment_AGInput_of_pivotTrade`), whose
  only remaining finite-volume input is the pivot trade inequality
  `c · (total pivotal mass) ≤ (pivotal mass on the enhanced set)`.

Cylinder events (`FKLimit.DependsOnCoordinates`) extend all of this to an
arbitrary edge type, with the pivotal coefficients read on the finite support
(`mass_eq_mass_restrict`, `hasFDerivAt_massPair_of_interior_cylinder`,
`massPair_deriv_decomp_cylinder`).  Finally
`upperWindow_of_pivotTrade_q_lt_one` and its three companions produce the
`FK.EssentialWindow.UpperWindow`/`LowerWindow` predicates of `FK.AGWindow`
directly from the pivot trade inequality.

No percolation geometry and no critical-shift claim is made.  The pivot trade
inequality is exposed, not proved; `pivotTrade_obstruction_empty` shows it is not
a formal consequence of the product-polynomial algebra, and
`decrement_pivotTrade_consistent`/`increment_pivotTrade_consistent` show the
remaining hypothesis package is consistent.
-/
import FK.MargulisRussoFinite
import FK.AGDifferentialShift
import FK.AGWindow

open Set MeasureTheory Filter ProbabilityTheory
open scoped Classical BigOperators ENNReal unitInterval Topology

namespace FK.AGMassDerivative

open FK.AGDifferentialShift FK.MargulisRussoFinite

noncomputable section

variable {E : Type*}

/-- On a finite edge type the infinite product Bernoulli law is the finite
`Measure.pi` product. -/
theorem bernoulliProduct_eq_pi [Fintype E] (r : E → unitInterval) :
    (FKLimit.bernoulliProduct r : Measure (E → Bool)) = FKEnhancement.bernoulliProduct r := by
  change Measure.infinitePi (fun e => bernoulliMeasure true false (r e)) =
    Measure.pi (fun e => bernoulliMeasure true false (r e))
  rw [Measure.infinitePi_eq_pi]

/-- On a finite edge type the clamped decrement-profile mass is exactly the
product polynomial `eventWeight`. -/
theorem mass_eq_eventWeight [Fintype E] [DecidableEq E] (A : Set (E → Bool))
    (S : Set E) (b ε : ℝ) :
    FK.AGDifferentialShift.mass A S b ε =
      FK.MargulisRussoFinite.eventWeight
        (fun e => (FK.AGDifferentialShift.decrementWeight S b ε e : ℝ)) A := by
  rw [FK.AGDifferentialShift.mass, bernoulliProduct_eq_pi]
  exact (FK.MargulisRussoFinite.eventWeight_eq_bernoulliProduct_toReal
    (FK.AGDifferentialShift.decrementWeight S b ε) A).symm

/-- On a finite edge type the clamped increment-profile mass is exactly the
product polynomial `eventWeight`. -/
theorem incMass_eq_eventWeight [Fintype E] [DecidableEq E] (A : Set (E → Bool))
    (S : Set E) (a ε : ℝ) :
    FK.AGDifferentialShift.incMass A S a ε =
      FK.MargulisRussoFinite.eventWeight
        (fun e => (FK.AGDifferentialShift.incrementWeight S a ε e : ℝ)) A := by
  rw [FK.AGDifferentialShift.incMass, bernoulliProduct_eq_pi]
  exact (FK.MargulisRussoFinite.eventWeight_eq_bernoulliProduct_toReal
    (FK.AGDifferentialShift.incrementWeight S a ε) A).symm

/-- The real value of the clamped decrement weight at edge `e`. -/
def decWeight (S : Set E) (e : E) (u : ℝ × ℝ) : ℝ :=
  (FK.AGDifferentialShift.decrementWeight S u.1 u.2 e : ℝ)

/-- The real value of the clamped increment weight at edge `e`. -/
def incWeight (S : Set E) (e : E) (u : ℝ × ℝ) : ℝ :=
  (FK.AGDifferentialShift.incrementWeight S u.1 u.2 e : ℝ)

lemma decWeight_apply (S : Set E) (e : E) (u : ℝ × ℝ) :
    decWeight S e u = max 0 (min 1 (if e ∈ S then u.1 - u.2 else u.1)) := rfl

lemma incWeight_apply (S : Set E) (e : E) (u : ℝ × ℝ) :
    incWeight S e u = max 0 (min 1 (if e ∈ S then u.1 + u.2 else u.1)) := rfl

/-- The clamped decrement profile as a map of the parameter plane, on the
interior region, has the linear derivative `ḃ - ε̇` on `S` and `ḃ` outside. -/
def decCLM (S : Set E) (e : E) : (ℝ × ℝ) →L[ℝ] ℝ :=
  if e ∈ S then ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  else ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The same for the increment profile: `ȧ + ε̇` on `S` and `ȧ` outside. -/
def incCLM (S : Set E) (e : E) : (ℝ × ℝ) →L[ℝ] ℝ :=
  if e ∈ S then ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
  else ContinuousLinearMap.fst ℝ ℝ ℝ

lemma decCLM_apply (S : Set E) (e : E) (p : ℝ × ℝ) :
    decCLM S e p = if e ∈ S then p.1 - p.2 else p.1 := by
  by_cases h : e ∈ S <;> simp [decCLM, h]

lemma incCLM_apply (S : Set E) (e : E) (p : ℝ × ℝ) :
    incCLM S e p = if e ∈ S then p.1 + p.2 else p.1 := by
  by_cases h : e ∈ S <;> simp [incCLM, h]

private lemma decWeight_affine (S : Set E) (e : E) {b ε : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 ≤ ε) (hεb : ε < b) :
    (fun u : ℝ × ℝ => decWeight S e u) =ᶠ[𝓝 (b, ε)]
      (fun u : ℝ × ℝ => if e ∈ S then u.1 - u.2 else u.1) := by
  have hgap : 0 < b - ε := sub_pos.mpr hεb
  have hpos : 0 < 1 - b + ε := by linarith
  set δ : ℝ := min ((b - ε) / 4) ((1 - b) / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδg : δ ≤ (b - ε) / 4 := by rw [hδ]; exact min_le_left _ _
  have hδ1b : δ ≤ (1 - b) / 4 := by rw [hδ]; exact min_le_right _ _
  have hδp : δ ≤ (1 - b + ε) / 4 := by linarith
  filter_upwards [Metric.ball_mem_nhds (b, ε) hδ0] with u hu
  have hu' : max |u.1 - b| |u.2 - ε| < δ := by
    simpa [Prod.dist_eq, Real.dist_eq] using hu
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hu'
  have h1a : u.1 - b < δ := (abs_lt.mp h1).2
  have h1b : -(δ) < u.1 - b := (abs_lt.mp h1).1
  have h2a : u.2 - ε < δ := (abs_lt.mp h2).2
  have h2b : -(δ) < u.2 - ε := (abs_lt.mp h2).1
  have hup0 : 0 < u.1 := by linarith
  have hup1 : u.1 < 1 := by linarith
  have hs0 : 0 < u.1 - u.2 := by linarith
  have hs1 : u.1 - u.2 < 1 := by linarith
  rw [decWeight_apply]
  by_cases h : e ∈ S
  · simp only [h, ite_true]
    rw [min_eq_right hs1.le, max_eq_right hs0.le]
  · simp only [h, ite_false]
    rw [min_eq_right hup1.le, max_eq_right hup0.le]

private lemma incWeight_affine (S : Set E) (e : E) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε0 : 0 ≤ ε) (haε1 : a + ε < 1) :
    (fun u : ℝ × ℝ => incWeight S e u) =ᶠ[𝓝 (a, ε)]
      (fun u : ℝ × ℝ => if e ∈ S then u.1 + u.2 else u.1) := by
  have hpos : 0 < 1 - a - ε := by linarith
  have h1a0 : 0 < 1 - a := by linarith
  set δ : ℝ := min (a / 4) ((1 - a - ε) / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδa : δ ≤ a / 4 := by rw [hδ]; exact min_le_left _ _
  have hδp : δ ≤ (1 - a - ε) / 4 := by rw [hδ]; exact min_le_right _ _
  have hδ1a : δ ≤ (1 - a) / 4 := by linarith
  filter_upwards [Metric.ball_mem_nhds (a, ε) hδ0] with u hu
  have hu' : max |u.1 - a| |u.2 - ε| < δ := by
    simpa [Prod.dist_eq, Real.dist_eq] using hu
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hu'
  have h1a : u.1 - a < δ := (abs_lt.mp h1).2
  have h1b : -(δ) < u.1 - a := (abs_lt.mp h1).1
  have h2a : u.2 - ε < δ := (abs_lt.mp h2).2
  have h2b : -(δ) < u.2 - ε := (abs_lt.mp h2).1
  have hup0 : 0 < u.1 := by linarith
  have hup1 : u.1 < 1 := by linarith
  have hs0 : 0 < u.1 + u.2 := by linarith
  have hs1 : u.1 + u.2 < 1 := by linarith
  rw [incWeight_apply]
  by_cases h : e ∈ S
  · simp only [h, ite_true]
    rw [min_eq_right hs1.le, max_eq_right hs0.le]
  · simp only [h, ite_false]
    rw [min_eq_right hup1.le, max_eq_right hup0.le]

theorem hasFDerivAt_decWeight (S : Set E) (e : E) {b ε : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 ≤ ε) (hεb : ε < b) :
    HasFDerivAt (decWeight S e) (decCLM S e) (b, ε) := by
  have hder : HasFDerivAt (fun u : ℝ × ℝ => if e ∈ S then u.1 - u.2 else u.1)
      (decCLM S e) (b, ε) := by
    have hsub : HasFDerivAt (fun u : ℝ × ℝ => u.1 - u.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (b, ε) :=
      (hasFDerivAt_fst (p := (b, ε))).sub (hasFDerivAt_snd (p := (b, ε)))
    by_cases h : e ∈ S
    · simpa [decCLM, h] using hsub
    · simpa [decCLM, h] using (hasFDerivAt_fst (p := (b, ε)) :
        HasFDerivAt (fun u : ℝ × ℝ => u.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (b, ε))
  exact hder.congr_of_eventuallyEq (decWeight_affine S e hb0 hb1 hε0 hεb)

theorem hasFDerivAt_incWeight (S : Set E) (e : E) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε0 : 0 ≤ ε) (haε1 : a + ε < 1) :
    HasFDerivAt (incWeight S e) (incCLM S e) (a, ε) := by
  have hder : HasFDerivAt (fun u : ℝ × ℝ => if e ∈ S then u.1 + u.2 else u.1)
      (incCLM S e) (a, ε) := by
    have hadd : HasFDerivAt (fun u : ℝ × ℝ => u.1 + u.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) (a, ε) :=
      (hasFDerivAt_fst (p := (a, ε))).add (hasFDerivAt_snd (p := (a, ε)))
    by_cases h : e ∈ S
    · simpa [incCLM, h] using hadd
    · simpa [incCLM, h] using (hasFDerivAt_fst (p := (a, ε)) :
        HasFDerivAt (fun u : ℝ × ℝ => u.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (a, ε))
  exact hder.congr_of_eventuallyEq (incWeight_affine S e ha0 ha1 hε0 haε1)

/-- Inhomogeneous one-coordinate Margulis--Russo identity: the raw derivative of
the product polynomial in the parameter at `e`, summed over the event, is the
forced-open minus forced-closed difference.  This is the general-rate form of
`FK.MargulisRussoFinite.sum_configurationWeight_slope`. -/
theorem sum_configurationWeight_slope_profile [Fintype E] [DecidableEq E]
    (r : E → ℝ) (A : Set (E → Bool)) (e : E) :
    (∑ ω, if ω ∈ A then
        (∏ j ∈ Finset.univ.erase e, FK.MargulisRussoFinite.coordinateWeight (r j) (ω j)) *
          FK.MargulisRussoFinite.coordinateSlope (ω e) else 0) =
      FK.MargulisRussoFinite.offEventWeight r e A true -
        FK.MargulisRussoFinite.offEventWeight r e A false := by
  classical
  rw [← Equiv.sum_comp (Glauber.configSplit Bool e).symm, Fintype.sum_prod_type]
  rw [FK.MargulisRussoFinite.offEventWeight, FK.MargulisRussoFinite.offEventWeight,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro off _
  change (∑ b : Bool, if FK.MargulisRussoFinite.splice e off b ∈ A then
      (∏ j ∈ Finset.univ.erase e, FK.MargulisRussoFinite.coordinateWeight (r j)
        (FK.MargulisRussoFinite.splice e off b j)) *
        FK.MargulisRussoFinite.coordinateSlope (FK.MargulisRussoFinite.splice e off b e)
      else 0) =
    (if FK.MargulisRussoFinite.splice e off true ∈ A then
      FK.MargulisRussoFinite.offConfigurationWeight r e off else 0) -
    (if FK.MargulisRussoFinite.splice e off false ∈ A then
      FK.MargulisRussoFinite.offConfigurationWeight r e off else 0)
  simp_rw [← FK.MargulisRussoFinite.offConfigurationWeight_eq_prod_erase r e off]
  by_cases ht : FK.MargulisRussoFinite.splice e off true ∈ A <;>
    by_cases hf : FK.MargulisRussoFinite.splice e off false ∈ A <;>
    simp [ht, hf, FK.MargulisRussoFinite.coordinateSlope]

/-- Swapping the configuration sum and the edge sum for a finite edge type. -/
theorem sum_omega_sum_e_smul [Fintype E] [DecidableEq E] (A : Set (E → Bool)) (r : E → ℝ)
    (D : E → (ℝ × ℝ) →L[ℝ] ℝ) :
    (∑ ω, if ω ∈ A then ∑ e, ((∏ j ∈ Finset.univ.erase e,
        FK.MargulisRussoFinite.coordinateWeight (r j) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) • D e else 0)
      = ∑ e, (FK.MargulisRussoFinite.offEventWeight r e A true -
        FK.MargulisRussoFinite.offEventWeight r e A false) • D e := by
  classical
  have h1 : ∀ ω, (if ω ∈ A then ∑ e, ((∏ j ∈ Finset.univ.erase e,
        FK.MargulisRussoFinite.coordinateWeight (r j) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) • D e else 0)
      = ∑ e, (if ω ∈ A then ((∏ j ∈ Finset.univ.erase e,
        FK.MargulisRussoFinite.coordinateWeight (r j) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) else 0) • D e := by
    intro ω
    by_cases h : ω ∈ A
    · simp [h]
    · simp [h]
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_smul, sum_configurationWeight_slope_profile r A e]

/-- **Derivative of the product polynomial along a two-parameter profile.**
For a finite edge type, if every edge weight `w e` is differentiable at the
parameter `u₀`, the product polynomial of any event is differentiable there,
with the coordinate Margulis--Russo coefficients. -/
theorem hasFDerivAt_eventWeight_comp [Fintype E] [DecidableEq E]
    (w : E → ℝ × ℝ → ℝ) (D : E → (ℝ × ℝ) →L[ℝ] ℝ) (u₀ : ℝ × ℝ)
    (hw : ∀ e, HasFDerivAt (w e) (D e) u₀) (A : Set (E → Bool)) :
    HasFDerivAt (fun u => FK.MargulisRussoFinite.eventWeight (fun e => w e u) A)
      (∑ e, (FK.MargulisRussoFinite.offEventWeight (fun a => w a u₀) e A true -
        FK.MargulisRussoFinite.offEventWeight (fun a => w a u₀) e A false) • D e) u₀ := by
  classical
  have hcoord : ∀ (e : E) (ω : E → Bool), HasFDerivAt
      (fun u : ℝ × ℝ => FK.MargulisRussoFinite.coordinateWeight (w e u) (ω e))
      (FK.MargulisRussoFinite.coordinateSlope (ω e) • D e) u₀ := by
    intro e ω
    exact (FK.MargulisRussoFinite.hasDerivAt_coordinateWeight (ω e) (w e u₀)).comp_hasFDerivAt
      u₀ (hw e)
  have hprod : ∀ ω : E → Bool, HasFDerivAt
      (fun u : ℝ × ℝ => ∏ e, FK.MargulisRussoFinite.coordinateWeight (w e u) (ω e))
      (∑ e, ((∏ j ∈ (Finset.univ : Finset E).erase e,
          FK.MargulisRussoFinite.coordinateWeight (w j u₀) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) • D e) u₀ := by
    intro ω
    have h0 := HasFDerivAt.finsetProd (u := (Finset.univ : Finset E))
      (g := fun e (u : ℝ × ℝ) => FK.MargulisRussoFinite.coordinateWeight (w e u) (ω e))
      (g' := fun e => FK.MargulisRussoFinite.coordinateSlope (ω e) • D e)
      (x := u₀) (fun e _ => hcoord e ω)
    have h1 : (∑ e, (∏ j ∈ (Finset.univ : Finset E).erase e,
          FK.MargulisRussoFinite.coordinateWeight (w j u₀) (ω j)) •
        (FK.MargulisRussoFinite.coordinateSlope (ω e) • D e))
        = ∑ e, ((∏ j ∈ (Finset.univ : Finset E).erase e,
          FK.MargulisRussoFinite.coordinateWeight (w j u₀) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) • D e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [smul_smul]
    rw [h1] at h0
    simpa using h0
  have hmain : HasFDerivAt (fun u : ℝ × ℝ => ∑ ω, if ω ∈ A then
      ∏ e, FK.MargulisRussoFinite.coordinateWeight (w e u) (ω e) else 0)
      (∑ ω, if ω ∈ A then ∑ e, ((∏ j ∈ Finset.univ.erase e,
        FK.MargulisRussoFinite.coordinateWeight (w j u₀) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) • D e else 0) u₀ := by
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun ω _ => ?_)
    by_cases hω : ω ∈ A
    · simpa [hω] using hprod ω
    · simpa [hω] using hasFDerivAt_const (0 : ℝ) u₀
  have hfun : (fun u : ℝ × ℝ => FK.MargulisRussoFinite.eventWeight (fun e => w e u) A) =
      (fun u : ℝ × ℝ => ∑ ω, if ω ∈ A then
        ∏ e, FK.MargulisRussoFinite.coordinateWeight (w e u) (ω e) else 0) := by
    funext u
    simp [FK.MargulisRussoFinite.eventWeight, FK.MargulisRussoFinite.configurationWeight]
  have hCLM : (∑ ω, if ω ∈ A then ∑ e, ((∏ j ∈ Finset.univ.erase e,
        FK.MargulisRussoFinite.coordinateWeight (w j u₀) (ω j)) *
        FK.MargulisRussoFinite.coordinateSlope (ω e)) • D e else 0)
      = ∑ e, (FK.MargulisRussoFinite.offEventWeight (fun a => w a u₀) e A true -
        FK.MargulisRussoFinite.offEventWeight (fun a => w a u₀) e A false) • D e :=
    sum_omega_sum_e_smul A (fun a => w a u₀) D
  rw [hfun, ← hCLM]
  exact hmain

/-! ### Differentiability of the clamped profile masses -/

/-- **Interior Fréchet derivative of the clamped decrement-profile mass.**  On
the region where no coordinate clamp is active (`0 < b < 1` and `0 ≤ ε < b`),
the mass of any event has the derivative given by the one-coordinate
Margulis--Russo coefficients of the profile. -/
theorem hasFDerivAt_massPair_of_interior [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (S : Set E) {b ε : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 ≤ ε) (hεb : ε < b) :
    HasFDerivAt (massPair A S)
      (∑ e, (offEventWeight (fun a => decWeight S a (b, ε)) e A true -
        offEventWeight (fun a => decWeight S a (b, ε)) e A false) • decCLM S e) (b, ε) := by
  have hw : ∀ e, HasFDerivAt (decWeight S e) (decCLM S e) (b, ε) :=
    fun e => hasFDerivAt_decWeight S e hb0 hb1 hε0 hεb
  have h := hasFDerivAt_eventWeight_comp (w := decWeight S) (D := decCLM S)
    (u₀ := (b, ε)) hw A
  have hfun : massPair A S =
      fun u => eventWeight (fun e => decWeight S e u) A := by
    funext u
    exact mass_eq_eventWeight A S u.1 u.2
  rw [hfun]
  exact h

/-- Interior Fréchet derivative of the clamped increment-profile mass. -/
theorem hasFDerivAt_incMassPair_of_interior [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (S : Set E) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε0 : 0 ≤ ε) (haε1 : a + ε < 1) :
    HasFDerivAt (incMassPair A S)
      (∑ e, (offEventWeight (fun a' => incWeight S a' (a, ε)) e A true -
        offEventWeight (fun a' => incWeight S a' (a, ε)) e A false) • incCLM S e) (a, ε) := by
  have hw : ∀ e, HasFDerivAt (incWeight S e) (incCLM S e) (a, ε) :=
    fun e => hasFDerivAt_incWeight S e ha0 ha1 hε0 haε1
  have h := hasFDerivAt_eventWeight_comp (w := incWeight S) (D := incCLM S)
    (u₀ := (a, ε)) hw A
  have hfun : incMassPair A S =
      fun u => eventWeight (fun e => incWeight S e u) A := by
    funext u
    exact incMass_eq_eventWeight A S u.1 u.2
  rw [hfun]
  exact h

/-! ### Pivotal trade functionals -/

/-- The trade linear functional `T·p - P·q` on the parameter plane. -/
def tradeCLM (T P : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  T • ContinuousLinearMap.fst ℝ ℝ ℝ - P • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma tradeCLM_apply (T P : ℝ) (p : ℝ × ℝ) : tradeCLM T P p = T * p.1 - P * p.2 := by
  simp [tradeCLM]

/-- The increment-plane trade functional `T·p + P·q`. -/
def incTradeCLM (T P : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  T • ContinuousLinearMap.fst ℝ ℝ ℝ + P • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma incTradeCLM_apply (T P : ℝ) (p : ℝ × ℝ) : incTradeCLM T P p = T * p.1 + P * p.2 := by
  simp [incTradeCLM]

/-- The total pivotal mass of a profile. -/
def pivotTotal [Fintype E] [DecidableEq E] (r : E → ℝ) (A : Set (E → Bool)) : ℝ :=
  ∑ e, offPivotalWeight r e A

/-- The pivotal mass carried by the enhanced edge set. -/
def pivotOn [Fintype E] [DecidableEq E] (S : Set E) (r : E → ℝ) (A : Set (E → Bool)) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => e ∈ S), offPivotalWeight r e A

lemma sum_smul_decCLM_apply [Fintype E] [DecidableEq E] (S : Set E) (P : E → ℝ)
    (p : ℝ × ℝ) :
    (∑ e, P e • decCLM S e) p =
      (∑ e, P e) * p.1 - (∑ e ∈ Finset.univ.filter (fun e => e ∈ S), P e) * p.2 := by
  rw [sum_apply]
  have hsplit : ∀ e, P e • (decCLM S e) p = P e * p.1 - (if e ∈ S then P e * p.2 else 0) := by
    intro e
    rw [decCLM_apply]
    by_cases h : e ∈ S <;> simp only [h, ite_true, ite_false] <;> ring
  simp only [smul_apply, hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_mul]

lemma sum_smul_incCLM_apply [Fintype E] [DecidableEq E] (S : Set E) (P : E → ℝ)
    (p : ℝ × ℝ) :
    (∑ e, P e • incCLM S e) p =
      (∑ e, P e) * p.1 + (∑ e ∈ Finset.univ.filter (fun e => e ∈ S), P e) * p.2 := by
  rw [sum_apply]
  have hsplit : ∀ e, P e • (incCLM S e) p = P e * p.1 + (if e ∈ S then P e * p.2 else 0) := by
    intro e
    rw [incCLM_apply]
    by_cases h : e ∈ S <;> simp only [h, ite_true, ite_false] <;> ring
  simp only [smul_apply, hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_filter, ← Finset.sum_mul]

/-- **Trade derivative decomposition for the decrement profile.**  For an
increasing event the interior derivative of the mass in the direction `(p, q)`
is `p · (total pivotal mass) - q · (pivotal mass on the enhanced set)`. -/
theorem massPair_deriv_decomp [Fintype E] [DecidableEq E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (S : Set E) {b ε : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 ≤ ε) (hεb : ε < b) :
    HasFDerivAt (massPair A S)
      (tradeCLM (pivotTotal (fun a => decWeight S a (b, ε)) A)
        (pivotOn S (fun a => decWeight S a (b, ε)) A)) (b, ε) := by
  have h := hasFDerivAt_massPair_of_interior A S hb0 hb1 hε0 hεb
  have hcoef : (∑ e, (offEventWeight (fun a => decWeight S a (b, ε)) e A true -
        offEventWeight (fun a => decWeight S a (b, ε)) e A false) • decCLM S e)
      = tradeCLM (pivotTotal (fun a => decWeight S a (b, ε)) A)
          (pivotOn S (fun a => decWeight S a (b, ε)) A) := by
    have hdiff : ∀ e, (offEventWeight (fun a => decWeight S a (b, ε)) e A true -
        offEventWeight (fun a => decWeight S a (b, ε)) e A false)
        = offPivotalWeight (fun a => decWeight S a (b, ε)) e A :=
      fun e => offEventWeight_sub_eq_offPivotalWeight hA _ e
    simp only [hdiff]
    apply ContinuousLinearMap.ext
    intro p
    rw [sum_smul_decCLM_apply, tradeCLM_apply, pivotTotal, pivotOn]
  rw [hcoef] at h
  exact h

/-- **Trade derivative decomposition for the increment profile.** -/
theorem incMassPair_deriv_decomp [Fintype E] [DecidableEq E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (S : Set E) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε0 : 0 ≤ ε) (haε1 : a + ε < 1) :
    HasFDerivAt (incMassPair A S)
      (incTradeCLM (pivotTotal (fun a' => incWeight S a' (a, ε)) A)
        (pivotOn S (fun a' => incWeight S a' (a, ε)) A)) (a, ε) := by
  have h := hasFDerivAt_incMassPair_of_interior A S ha0 ha1 hε0 haε1
  have hcoef : (∑ e, (offEventWeight (fun a' => incWeight S a' (a, ε)) e A true -
        offEventWeight (fun a' => incWeight S a' (a, ε)) e A false) • incCLM S e)
      = incTradeCLM (pivotTotal (fun a' => incWeight S a' (a, ε)) A)
          (pivotOn S (fun a' => incWeight S a' (a, ε)) A) := by
    have hdiff : ∀ e, (offEventWeight (fun a' => incWeight S a' (a, ε)) e A true -
        offEventWeight (fun a' => incWeight S a' (a, ε)) e A false)
        = offPivotalWeight (fun a' => incWeight S a' (a, ε)) e A :=
      fun e => offEventWeight_sub_eq_offPivotalWeight hA _ e
    simp only [hdiff]
    apply ContinuousLinearMap.ext
    intro p
    rw [sum_smul_incCLM_apply, incTradeCLM_apply, pivotTotal, pivotOn]
  rw [hcoef] at h
  exact h

/-- Trade sign: the decrement trade derivative is non-positive as soon as the
enhanced pivotal mass dominates the total pivotal mass by the rate `c`. -/
lemma tradeCLM_trade_nonpos (T P c : ℝ) (h : c * T ≤ P) : tradeCLM T P (c, 1) ≤ 0 := by
  rw [tradeCLM_apply]
  nlinarith

/-- Trade sign for the increment plane in direction `(-c, 1)`. -/
lemma incTradeCLM_trade_nonneg (T P c : ℝ) (h : c * T ≤ P) :
    0 ≤ incTradeCLM T P (-c, 1) := by
  rw [incTradeCLM_apply]
  nlinarith

/-! ### Continuity of the profile masses -/

lemma continuous_coordinateWeight_comp {w : ℝ × ℝ → ℝ} (hw : Continuous w) (b : Bool) :
    Continuous (fun u => coordinateWeight (w u) b) := by
  have hfun : (fun u => coordinateWeight (w u) b) = fun u => if b then w u else 1 - w u := by
    funext u
    cases b <;> simp [coordinateWeight]
  rw [hfun]
  cases b
  · simp only [Bool.false_eq_true, reduceIte]
    exact continuous_const.sub hw
  · simp only [reduceIte]
    exact hw

theorem continuous_eventWeight_comp [Fintype E] [DecidableEq E]
    (w : E → ℝ × ℝ → ℝ) (hw : ∀ e, Continuous (w e)) (A : Set (E → Bool)) :
    Continuous (fun u => eventWeight (fun e => w e u) A) := by
  classical
  have hfun : (fun u => eventWeight (fun e => w e u) A) =
      fun u => ∑ ω, if ω ∈ A then ∏ e, coordinateWeight (w e u) (ω e) else 0 := by
    funext u
    simp [eventWeight, configurationWeight]
  rw [hfun]
  refine continuous_finsetSum _ (fun ω _ => ?_)
  by_cases hω : ω ∈ A
  · simp only [hω, ite_true]
    exact continuous_finsetProd _ (fun e _ => continuous_coordinateWeight_comp (hw e) (ω e))
  · simp only [hω, ite_false]
    exact continuous_const

lemma continuous_decWeight (S : Set E) (e : E) : Continuous (decWeight S e) := by
  have hfun : decWeight S e = fun u : ℝ × ℝ =>
      max 0 (min 1 (if e ∈ S then u.1 - u.2 else u.1)) := rfl
  rw [hfun]
  by_cases h : e ∈ S
  · simp only [h, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

lemma continuous_incWeight (S : Set E) (e : E) : Continuous (incWeight S e) := by
  have hfun : incWeight S e = fun u : ℝ × ℝ =>
      max 0 (min 1 (if e ∈ S then u.1 + u.2 else u.1)) := rfl
  rw [hfun]
  by_cases h : e ∈ S
  · simp only [h, ite_true]
    fun_prop
  · simp only [h, ite_false]
    fun_prop

theorem continuous_massPair [Fintype E] [DecidableEq E] (A : Set (E → Bool))
    (S : Set E) : Continuous (massPair A S) := by
  have hfun : massPair A S = fun u => eventWeight (fun e => decWeight S e u) A := by
    funext u
    exact mass_eq_eventWeight A S u.1 u.2
  rw [hfun]
  exact continuous_eventWeight_comp _ (fun e => continuous_decWeight S e) A

theorem continuous_incMassPair [Fintype E] [DecidableEq E] (A : Set (E → Bool))
    (S : Set E) : Continuous (incMassPair A S) := by
  have hfun : incMassPair A S = fun u => eventWeight (fun e => incWeight S e u) A := by
    funext u
    exact incMass_eq_eventWeight A S u.1 u.2
  rw [hfun]
  exact continuous_eventWeight_comp _ (fun e => continuous_incWeight S e) A

/-! ### The repaired strict shift theorems

The public binder of `FK.AGDifferentialShift.exists_subcritical_decrement`
requires a Fréchet derivative of the clamped mass on the *closed* region
`0 ≤ ε ≤ b ≤ 1`.  The clamped profile is not differentiable on the collision
line `ε = b` (see `not_hasFDerivAt_massPair_clamp`), so that binder cannot be
discharged by the actual profiles.  The two theorems below only require the
derivative and the trade sign on the open interior region actually used by the
mean value theorem, which is exactly where `hasFDerivAt_massPair_of_interior`
and `massPair_deriv_decomp` apply. -/

/-- **Strict decrement shift with the interior derivative data.** -/
theorem exists_subcritical_decrement_interior [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (b ε : ℝ), 0 < b → b < 1 → 0 ≤ ε → ε < b →
      HasFDerivAt (massPair (An n) S) (L n b ε) (b, ε))
    (htrade : ∀ (n : ℕ) (b ε : ℝ), 0 < b → b < 1 → 0 < ε → ε < b →
      (L n b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2) (hε1 : ε < (1 - pc) / 2) :
    ∃ b, pc < b ∧ b ≤ 1 ∧ ε ≤ b ∧ mass A S b ε = 0 := by
  set b₀ : ℝ := pc - c * ε / 2 with hb₀
  set b₁ : ℝ := pc + c * ε / 2 with hb₁
  have hcε : 0 < c * ε := mul_pos hc0 hε0
  have hb₀pc2 : pc / 2 ≤ b₀ := by rw [hb₀]; nlinarith
  have hb₀0 : 0 < b₀ := by rw [hb₀]; nlinarith
  have hb₀pc : b₀ < pc := by rw [hb₀]; nlinarith
  have hb₁pc : pc < b₁ := by rw [hb₁]; nlinarith
  have hb₁1 : b₁ ≤ 1 := by rw [hb₁]; nlinarith
  have hεb₁ : ε ≤ b₁ := by rw [hb₁]; nlinarith
  refine ⟨b₁, hb₁pc, hb₁1, hεb₁, ?_⟩
  have hb0t : ∀ t : ℝ, 0 < t → t ≤ ε → 0 < b₀ + c * t := by
    intro t ht0 _
    nlinarith [mul_pos hc0 ht0]
  have hb1t : ∀ t : ℝ, 0 < t → t ≤ ε → b₀ + c * t < 1 := by
    intro t _ htε
    have hct : c * t ≤ c * ε := by nlinarith
    have hb₀eq : b₀ + c * ε = b₁ := by rw [hb₀, hb₁]; ring
    nlinarith
  have hεt : ∀ t : ℝ, t ∈ Ioo (0:ℝ) ε → t < b₀ + c * t := by
    intro t ht
    have ht_pc : t < pc / 2 := lt_of_lt_of_le ht.2 hεpc.le
    have h1 : t < b₀ := by rw [hb₀]; nlinarith
    nlinarith [mul_pos hc0 ht.1]
  have hstep : ∀ n, mass (An n) S b₁ ε ≤ mass (An n) S b₀ 0 := by
    intro n
    have hcont : ContinuousOn
        ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) (Icc 0 ε) :=
      ((continuous_massPair (An n) S).comp (by fun_prop : Continuous
        fun s : ℝ => (b₀ + c * s, 0 + 1 * s))).continuousOn
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s))
          ((L n (b₀ + c * t) (0 + 1 * t)) (c, 1)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hbt0 : 0 < b₀ + c * t := hb0t t ht0 htε.le
      have hbt1 : b₀ + c * t < 1 := hb1t t ht0 htε.le
      have hεtt : 0 + 1 * t < b₀ + c * t := by simpa using hεt t ht
      have hle : (0:ℝ) ≤ 0 + 1 * t := by linarith
      have hF := hderiv n (b₀ + c * t) (0 + 1 * t) hbt0 hbt1 hle hεtt
      have hline : HasDerivAt (fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) (c, (1:ℝ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => b₀ + c * s) c t := by
          simpa using (hasDerivAt_const_mul (x := t) c).const_add b₀
        have h2 : HasDerivAt (fun s : ℝ => (0:ℝ) + 1 * s) 1 t := by
          simpa using (hasDerivAt_id (x := t)).const_add (0:ℝ)
        exact h1.prodMk h2
      exact hF.comp_hasDerivAt t hline
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        ((L n (b₀ + c * t) (0 + 1 * t)) (c, 1)) ≤ 0 := by
      intro t ht
      have hbt0 : 0 < b₀ + c * t := hb0t t ht.1 ht.2.le
      have hbt1 : b₀ + c * t < 1 := hb1t t ht.1 ht.2.le
      have hpos : (0:ℝ) < 0 + 1 * t := by linarith [ht.1]
      exact htrade n _ _ hbt0 hbt1 hpos (by simpa using hεt t ht)
    have hval := le_of_deriv_nonpos hε0 hderiv' hcont hbound
    have h₁ : ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) ε =
        mass (An n) S b₁ ε := by
      change mass (An n) S (b₀ + c * ε) (0 + 1 * ε) = mass (An n) S b₁ ε
      rw [show b₀ + c * ε = b₁ by rw [hb₀, hb₁]; ring,
        show 0 + 1 * ε = ε by ring]
    have h₀ : ((massPair (An n) S) ∘ fun s : ℝ => (b₀ + c * s, 0 + 1 * s)) 0 =
        mass (An n) S b₀ 0 := by
      change mass (An n) S (b₀ + c * 0) (0 + 1 * 0) = mass (An n) S b₀ 0
      norm_num
    rw [h₁, h₀] at hval
    exact hval
  have hub : mass A S b₁ ε ≤ mass A S b₀ 0 :=
    le_of_tendsto_of_tendsto (hconv b₁ ε) (hconv b₀ 0) (Eventually.of_forall hstep)
  rw [hbase b₀ hb₀0.le hb₀pc] at hub
  exact le_antisymm hub (mass_nonneg A S b₁ ε)

/-- **Strict increment shift with the interior derivative data.** -/
theorem exists_supercritical_increment_interior [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hderiv : ∀ (n : ℕ) (a ε : ℝ), 0 < a → a < 1 → 0 ≤ ε → a + ε < 1 →
      HasFDerivAt (incMassPair (An n) S) (L n a ε) (a, ε))
    (htrade : ∀ (n : ℕ) (a ε : ℝ), 0 < a → a < 1 → 0 < ε → a + ε < 1 →
      0 ≤ (L n a ε) (-c, 1))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1 - pc) / 2) (hεpc : ε < pc / 2) :
    ∃ a, 0 ≤ a ∧ a < pc ∧ a + ε ≤ 1 ∧ incMass A S a ε = 1 := by
  set a₀ : ℝ := pc + c * ε / 2 with ha₀
  set a₁ : ℝ := pc - c * ε / 2 with ha₁
  have hcε : 0 < c * ε := mul_pos hc0 hε0
  have ha₀pc : pc < a₀ := by rw [ha₀]; nlinarith
  have ha₀1 : a₀ < 1 := by rw [ha₀]; nlinarith
  have ha₁0 : 0 ≤ a₁ := by rw [ha₁]; nlinarith
  have ha₁pc : a₁ < pc := by rw [ha₁]; nlinarith
  have hεa₁ : a₁ + ε ≤ 1 := by rw [ha₁]; nlinarith
  refine ⟨a₁, ha₁0, ha₁pc, hεa₁, ?_⟩
  have ha0t : ∀ t : ℝ, 0 < t → t ≤ ε → 0 < a₀ + (-c) * t := by
    intro t _ _
    nlinarith [mul_pos hc0 (show (0:ℝ) < t by linarith)]
  have ha1t : ∀ t : ℝ, 0 < t → t ≤ ε → a₀ + (-c) * t < 1 := by
    intro t _ htε
    nlinarith
  have hsumt : ∀ t : ℝ, t ∈ Ioo (0:ℝ) ε → a₀ + (-c) * t + (0 + 1 * t) < 1 := by
    intro t ht
    have hct : (0:ℝ) < t := ht.1
    have htε : t < ε := ht.2
    nlinarith
  have hstep : ∀ n, incMass (An n) S a₁ ε ≥ incMass (An n) S a₀ 0 := by
    intro n
    have hcont : ContinuousOn
        ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) (Icc 0 ε) :=
      ((continuous_incMassPair (An n) S).comp (by fun_prop : Continuous
        fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))).continuousOn
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε,
        HasDerivAt ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s))
          ((L n (a₀ + (-c) * t) (0 + 1 * t)) (-c, 1)) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htε : t < ε := ht.2
      have hat0 : 0 < a₀ + (-c) * t := ha0t t ht0 htε.le
      have hat1 : a₀ + (-c) * t < 1 := ha1t t ht0 htε.le
      have hsum : a₀ + (-c) * t + (0 + 1 * t) < 1 := hsumt t ht
      have hle : (0:ℝ) ≤ 0 + 1 * t := by linarith
      have hF := hderiv n (a₀ + (-c) * t) (0 + 1 * t) hat0 hat1 hle hsum
      have hline : HasDerivAt (fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) ((-c), (1:ℝ)) t := by
        have h1 : HasDerivAt (fun s : ℝ => a₀ + (-c) * s) (-c) t := by
          simpa using (hasDerivAt_const_mul (x := t) (-c)).const_add a₀
        have h2 : HasDerivAt (fun s : ℝ => (0:ℝ) + 1 * s) 1 t := by
          simpa using (hasDerivAt_id (x := t)).const_add (0:ℝ)
        exact h1.prodMk h2
      exact hF.comp_hasDerivAt t hline
    have hbound : ∀ t ∈ Ioo (0:ℝ) ε,
        0 ≤ ((L n (a₀ + (-c) * t) (0 + 1 * t)) (-c, 1)) := by
      intro t ht
      have hat0 : 0 < a₀ + (-c) * t := ha0t t ht.1 ht.2.le
      have hat1 : a₀ + (-c) * t < 1 := ha1t t ht.1 ht.2.le
      have hsum : a₀ + (-c) * t + (0 + 1 * t) < 1 := hsumt t ht
      have hpos : (0:ℝ) < 0 + 1 * t := by linarith [ht.1]
      exact htrade n _ _ hat0 hat1 hpos hsum
    have hval := le_of_deriv_nonneg hε0 hderiv' hcont hbound
    have h₁ : ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) ε =
        incMass (An n) S a₁ ε := by
      change incMass (An n) S (a₀ + (-c) * ε) (0 + 1 * ε) = incMass (An n) S a₁ ε
      rw [show a₀ + (-c) * ε = a₁ by rw [ha₀, ha₁]; ring,
        show 0 + 1 * ε = ε by ring]
    have h₀ : ((incMassPair (An n) S) ∘ fun s : ℝ => (a₀ + (-c) * s, 0 + 1 * s)) 0 =
        incMass (An n) S a₀ 0 := by
      change incMass (An n) S (a₀ + (-c) * 0) (0 + 1 * 0) = incMass (An n) S a₀ 0
      norm_num
    rw [h₁, h₀] at hval
    exact hval
  have hlow : incMass A S a₀ 0 ≤ incMass A S a₁ ε :=
    le_of_tendsto_of_tendsto (hconv a₀ 0) (hconv a₁ ε) (Eventually.of_forall hstep)
  rw [hbase a₀ ha₀pc ha₀1.le] at hlow
  exact le_antisymm (incMass_le_one A S a₁ ε) hlow

/-- **The decrement `hAG` input from the finite pivot trade inequality.**  All
derivative data of `FK.AGDifferentialShift.decrement_AGInput` is discharged by
`massPair_deriv_decomp`; the sole remaining finite-volume input is the trade
inequality `c · (total pivotal mass) ≤ (pivotal mass on the enhanced set)`. -/
theorem decrement_AGInput_of_pivotTrade [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (hpivot : ∀ (n : ℕ) (b ε : ℝ), 0 < b → b < 1 → 0 < ε → ε < b →
      c * pivotTotal (fun a => decWeight S a (b, ε)) (An n) ≤
        pivotOn S (fun a => decWeight S a (b, ε)) (An n))
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => mass (An n) S b ε) atTop
      (𝓝 (mass A S b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A S b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < pc / 2 →
      ∃ b, ∃ hpcb : pc < b, ∃ hb1 : b ≤ 1, ∃ hεb : ε ≤ b,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
          (hpc0.le.trans hpcb.le) hb1 hε0.le hεb) : Measure (E → Bool)) A = 0 := by
  intro ε hε0 hεpc
  set ε' : ℝ := min ε ((1 - pc) / 4) with hε'
  have hε'0 : 0 < ε' := lt_min hε0 (by linarith)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'pc : ε' < pc / 2 := lt_of_le_of_lt hε'ε hεpc
  have hε'1 : ε' < (1 - pc) / 2 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨b, hpcb, hb1, hε'b, hmass⟩ :=
    exists_subcritical_decrement_interior A An S pc c hpc0 hpc1 hc0 hc1
      (fun n b ε => tradeCLM (pivotTotal (fun a => decWeight S a (b, ε)) (An n))
        (pivotOn S (fun a => decWeight S a (b, ε)) (An n)))
      (fun n b ε hb0 hb1 hε0 hεb => massPair_deriv_decomp (hAn n) S hb0 hb1 hε0 hεb)
      (fun n b ε hb0 hb1 hε0 hεb =>
        tradeCLM_trade_nonpos _ _ c (hpivot n b ε hb0 hb1 hε0 hεb))
      hconv hbase ε' hε'0 hε'pc hε'1
  have hb0 : 0 ≤ b := hpc0.le.trans hpcb.le
  have hεb : ε ≤ b := by linarith
  refine ⟨b, hpcb, hb1, hεb, ?_⟩
  have hmono : mass A S b ε ≤ mass A S b ε' := mass_anti_decrement hA hmeas S hε'ε
  have hzero : mass A S b ε = 0 :=
    le_antisymm (by rw [hmass] at hmono; exact hmono) (mass_nonneg A S b ε)
  have hm : ((FKLimit.bernoulliProduct (FK.EssentialWindow.decrementProfile S b ε
      hb0 hb1 hε0.le hεb) : Measure (E → Bool)) A) = 0 := by
    have h := hzero
    rw [mass_eq_decrementProfile A S hb0 hb1 hε0.le hεb] at h
    rcases (ENNReal.toReal_eq_zero_iff _).mp h with h' | h'
    · exact h'
    · exact absurd h' (measure_ne_top _ _)
  exact hm

/-- **The increment `hAG` input from the same finite pivot trade inequality.** -/
theorem increment_AGInput_of_pivotTrade [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (S : Set E)
    (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ n, IsUpperSet (An n))
    (hpivot : ∀ (n : ℕ) (a ε : ℝ), 0 < a → a < 1 → 0 < ε → a + ε < 1 →
      c * pivotTotal (fun a' => incWeight S a' (a, ε)) (An n) ≤
        pivotOn S (fun a' => incWeight S a' (a, ε)) (An n))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun n => incMass (An n) S a ε) atTop
      (𝓝 (incMass A S a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A S a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    ∀ (ε : ℝ) (hε0 : 0 < ε), ε < (1 - pc) / 2 →
      ∃ a, ∃ ha0 : 0 ≤ a, ∃ _hapc : a < pc, ∃ haε1 : a + ε ≤ 1,
        (FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
          ha0 hε0.le haε1) : Measure (E → Bool)) A = 1 := by
  intro ε hε0 hεpc
  set ε' : ℝ := min ε (min (pc / 4) ((1 - pc) / 4)) with hε'
  have hε'0 : 0 < ε' := lt_min hε0 (lt_min (by linarith) (by linarith))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'pc : ε' < pc / 2 := by
    have h1 : ε' ≤ pc / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hε'1 : ε' < (1 - pc) / 2 := by
    have h1 : ε' ≤ (1 - pc) / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  obtain ⟨a, ha0, _hapc, haε1, hmass⟩ :=
    exists_supercritical_increment_interior A An S pc c hpc0 hpc1 hc0 hc1
      (fun n a ε => incTradeCLM (pivotTotal (fun a' => incWeight S a' (a, ε)) (An n))
        (pivotOn S (fun a' => incWeight S a' (a, ε)) (An n)))
      (fun n a ε ha0 ha1 hε0 haε1 => incMassPair_deriv_decomp (hAn n) S ha0 ha1 hε0 haε1)
      (fun n a ε ha0 ha1 hε0 haε1 =>
        incTradeCLM_trade_nonneg _ _ c (hpivot n a ε ha0 ha1 hε0 haε1))
      hconv hbase ε' hε'0 hε'1 hε'pc
  have haε1' : a + ε ≤ 1 := by linarith
  refine ⟨a, ha0, _hapc, haε1', ?_⟩
  have hmono : incMass A S a ε' ≤ incMass A S a ε := incMass_mono_increment hA hmeas S hε'ε
  have hone : incMass A S a ε = 1 :=
    le_antisymm (incMass_le_one A S a ε) (by rw [hmass] at hmono; exact hmono)
  have hm : ((FKLimit.bernoulliProduct (FK.EssentialWindow.incrementProfile S a ε
      ha0 hε0.le haε1') : Measure (E → Bool)) A) = 1 := by
    have h := hone
    rw [incMass_eq_incrementProfile A S ha0 hε0.le haε1'] at h
    exact (ENNReal.toReal_eq_one_iff _).mp h
  exact hm

/-! ### The clamp collision: the closed-region binder is unsatisfiable -/

/-- The event that the unique `Unit` edge is open. -/
def unitOpenEvent : Set (Unit → Bool) := {ω | ω () = true}

/-- The clamped decrement mass of the single-edge open event is exactly the
clamped weight itself. -/
theorem mass_unitOpenEvent (b ε : ℝ) :
    mass unitOpenEvent Set.univ b ε = max 0 (min 1 (b - ε)) := by
  rw [mass_eq_eventWeight]
  rw [eventWeight_eq_coordinate (fun e => (decrementWeight Set.univ b ε e : ℝ))
    unitOpenEvent ()]
  have htrue : offEventWeight (fun e => (decrementWeight Set.univ b ε e : ℝ)) ()
      unitOpenEvent true = 1 := by
    rw [offEventWeight, ← sum_offConfigurationWeight
      (fun e => (decrementWeight Set.univ b ε e : ℝ)) ()]
    apply Finset.sum_congr rfl
    intro off _
    have hmem : splice () off true ∈ unitOpenEvent := by
      simp [unitOpenEvent, splice_same]
    simp only [hmem, ite_true]
  have hfalse : offEventWeight (fun e => (decrementWeight Set.univ b ε e : ℝ)) ()
      unitOpenEvent false = 0 := by
    rw [offEventWeight]
    apply Finset.sum_eq_zero
    intro off _
    have hmem : splice () off false ∉ unitOpenEvent := by
      simp [unitOpenEvent, splice_same]
    simp only [hmem, ite_false]
  rw [htrue, hfalse]
  have hw : ((decrementWeight Set.univ b ε () : unitInterval) : ℝ) = max 0 (min 1 (b - ε)) := by
    simp [FK.AGDifferentialShift.decrementWeight]
  rw [← hw]
  simp

/-- The clamped decrement mass along the collision direction at `(1/2, 1/2)` is
eventually `max 0 (2t)`, which is not differentiable at zero. -/
theorem not_hasFDerivAt_massPair_clamp :
    ¬ ∃ L : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt (massPair unitOpenEvent Set.univ) L ((1:ℝ)/2, (1:ℝ)/2) := by
  rintro ⟨L, hL⟩
  have hline : HasDerivAt (fun t : ℝ => ((1:ℝ)/2 + t, (1:ℝ)/2 - t)) ((1:ℝ), (-1:ℝ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (1:ℝ)/2 + t) 1 0 := by
      simpa using (hasDerivAt_id (x := (0:ℝ))).const_add ((1:ℝ)/2)
    have h2 : HasDerivAt (fun t : ℝ => (1:ℝ)/2 - t) (-1) 0 := by
      simpa using (hasDerivAt_id (x := (0:ℝ))).const_sub ((1:ℝ)/2)
    exact h1.prodMk h2
  have hL' : HasFDerivAt (massPair unitOpenEvent Set.univ) L
      ((1:ℝ)/2 + 0, (1:ℝ)/2 - 0) := by
    simpa using hL
  have hcomp := hL'.comp_hasDerivAt (0:ℝ) hline
  have hev : (massPair unitOpenEvent Set.univ ∘
      fun t : ℝ => ((1:ℝ)/2 + t, (1:ℝ)/2 - t)) =ᶠ[𝓝 (0:ℝ)] (fun t : ℝ => max 0 (2 * t)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1/2)] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have h := mass_unitOpenEvent ((1:ℝ)/2 + t) ((1:ℝ)/2 - t)
    rw [show (1:ℝ)/2 + t - ((1:ℝ)/2 - t) = 2 * t by ring,
      min_eq_right (by linarith [abs_lt.mp ht])] at h
    exact h
  have hdiff : DifferentiableAt ℝ (fun t : ℝ => max 0 (2 * t)) 0 :=
    hcomp.differentiableAt.congr_of_eventuallyEq hev.symm
  have hnot : ¬ DifferentiableAt ℝ (fun t : ℝ => max 0 (2 * t)) 0 := by
    intro hh
    have h2 : DifferentiableAt ℝ (fun t : ℝ => max 0 (2 * t) - t) 0 :=
      hh.sub differentiableAt_id
    have heq : (fun t : ℝ => max 0 (2 * t) - t) = (fun t : ℝ => |t|) := by
      funext t
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
      · rw [abs_of_nonpos h, max_eq_left (by linarith)]
        ring
    rw [heq] at h2
    exact not_differentiableAt_abs_zero h2
  exact hnot hdiff

/-! ### The trade inequality is not derivable from the definitions -/

lemma true_le_bool {b : Bool} (h : true ≤ b) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

lemma offEventWeight_unitOpenEvent_true (r : Unit → ℝ) :
    offEventWeight r () unitOpenEvent true = 1 := by
  rw [offEventWeight, ← sum_offConfigurationWeight r ()]
  apply Finset.sum_congr rfl
  intro off _
  have hmem : splice () off true ∈ unitOpenEvent := by
    simp [unitOpenEvent, splice_same]
  simp only [hmem, ite_true]

lemma offEventWeight_unitOpenEvent_false (r : Unit → ℝ) :
    offEventWeight r () unitOpenEvent false = 0 := by
  rw [offEventWeight]
  apply Finset.sum_eq_zero
  intro off _
  have hmem : splice () off false ∉ unitOpenEvent := by
    simp [unitOpenEvent, splice_same]
  simp only [hmem, ite_false]

lemma offPivotalWeight_unitOpenEvent (r : Unit → ℝ) :
    offPivotalWeight r () unitOpenEvent = 1 := by
  rw [← offEventWeight_sub_eq_offPivotalWeight (A := unitOpenEvent) ?_ r ()]
  · rw [offEventWeight_unitOpenEvent_true, offEventWeight_unitOpenEvent_false]; ring
  · intro ω η h hω
    simp only [unitOpenEvent, mem_ofPred_eq] at hω ⊢
    have h1 : ω () ≤ η () := h ()
    rw [hω] at h1
    exact true_le_bool h1

/-- **The pivot trade inequality has mathematical content.**  With no enhanced
edges (`S = ∅`) the enhanced pivotal mass vanishes, while the unique edge of the
singleton event is pivotal with mass one, so the trade inequality fails for
every `c > 0`.  Hence the remaining input of
`decrement_AGInput_of_pivotTrade` cannot be discharged by the product-polynomial
algebra alone: it needs the enhanced device geometry. -/
theorem pivotTrade_obstruction_empty :
    ¬ ((1/2 : ℝ) * pivotTotal (fun _ => (3:ℝ)/4) unitOpenEvent ≤
      pivotOn (∅ : Set Unit) (fun _ => (3:ℝ)/4) unitOpenEvent) := by
  have hT : pivotTotal (fun _ => (3:ℝ)/4) unitOpenEvent = 1 := by
    rw [pivotTotal]
    simp [offPivotalWeight_unitOpenEvent]
  have hP : pivotOn (∅ : Set Unit) (fun _ => (3:ℝ)/4) unitOpenEvent = 0 := by
    rw [pivotOn]
    simp
  rw [hT, hP]
  norm_num

/-- The mass of a finitely supported event under the clamped decrement profile
is the mass of its restriction to the support, on the finite coordinate type of
the support. -/
theorem mass_eq_mass_restrict [DecidableEq E] (A : Set (E → Bool)) (S : Set E)
    (T : Finset E) (hA : FKLimit.DependsOnCoordinates A T) (b ε : ℝ) :
    mass A S b ε = mass (E := T) (T.restrict '' A) {e : T | (e : E) ∈ S} b ε := by
  have hmap : Measure.map T.restrict
      (FKLimit.bernoulliProduct (decrementWeight S b ε) : Measure (E → Bool))
      = (FKLimit.bernoulliProduct (fun e : T => decrementWeight S b ε e.val) :
          Measure (T → Bool)) := by
    change Measure.map T.restrict
        (Measure.infinitePi
          (fun e => bernoulliMeasure true false (decrementWeight S b ε e))) =
      Measure.infinitePi
        (fun e : T => bernoulliMeasure true false (decrementWeight S b ε e.val))
    rw [Measure.infinitePi_map_restrict, Measure.infinitePi_eq_pi]
  have happly : (FKLimit.bernoulliProduct (decrementWeight S b ε) : Measure (E → Bool)) A
      = (Measure.map T.restrict
          (FKLimit.bernoulliProduct (decrementWeight S b ε) : Measure (E → Bool)))
          (T.restrict '' A) := by
    rw [Measure.map_apply T.measurable_restrict MeasurableSet.of_discrete]
    exact congrArg
      (fun B => (FKLimit.bernoulliProduct (decrementWeight S b ε) : Measure (E → Bool)) B)
      (FKLimit.eq_preimage_restrict_image hA)
  have hprof : (fun e : T => decrementWeight S b ε e.val)
      = decrementWeight {e : T | (e : E) ∈ S} b ε := by
    funext e
    apply Subtype.ext
    simp [FK.AGDifferentialShift.decrementWeight]
  rw [mass, mass, happly, hmap, hprof]

lemma decrementWeight_restrict_profile [DecidableEq E] (S : Set E) (T : Finset E)
    (b ε : ℝ) :
    (fun e : T => decrementWeight S b ε e.val)
      = decrementWeight {e : T | (e : E) ∈ S} b ε := by
  funext e
  apply Subtype.ext
  simp [FK.AGDifferentialShift.decrementWeight]

lemma incrementWeight_restrict_profile [DecidableEq E] (S : Set E) (T : Finset E)
    (a ε : ℝ) :
    (fun e : T => incrementWeight S a ε e.val)
      = incrementWeight {e : T | (e : E) ∈ S} a ε := by
  funext e
  apply Subtype.ext
  simp [FK.AGDifferentialShift.incrementWeight]

lemma decCLM_restrict [DecidableEq E] (S : Set E) (T : Finset E) (e : T) :
    decCLM {e : T | (e : E) ∈ S} e = decCLM S e.val := by
  apply ContinuousLinearMap.ext
  intro p
  simp [decCLM_apply]

lemma incCLM_restrict [DecidableEq E] (S : Set E) (T : Finset E) (e : T) :
    incCLM {e : T | (e : E) ∈ S} e = incCLM S e.val := by
  apply ContinuousLinearMap.ext
  intro p
  simp [incCLM_apply]

/-- The mass of a finitely supported event under the clamped increment profile
is the mass of its restriction to the support. -/
theorem incMass_eq_incMass_restrict [DecidableEq E] (A : Set (E → Bool)) (S : Set E)
    (T : Finset E) (hA : FKLimit.DependsOnCoordinates A T) (a ε : ℝ) :
    incMass A S a ε = incMass (E := T) (T.restrict '' A) {e : T | (e : E) ∈ S} a ε := by
  have hmap : Measure.map T.restrict
      (FKLimit.bernoulliProduct (incrementWeight S a ε) : Measure (E → Bool))
      = (FKLimit.bernoulliProduct (fun e : T => incrementWeight S a ε e.val) :
          Measure (T → Bool)) := by
    change Measure.map T.restrict
        (Measure.infinitePi
          (fun e => bernoulliMeasure true false (incrementWeight S a ε e))) =
      Measure.infinitePi
        (fun e : T => bernoulliMeasure true false (incrementWeight S a ε e.val))
    rw [Measure.infinitePi_map_restrict, Measure.infinitePi_eq_pi]
  have happly : (FKLimit.bernoulliProduct (incrementWeight S a ε) : Measure (E → Bool)) A
      = (Measure.map T.restrict
          (FKLimit.bernoulliProduct (incrementWeight S a ε) : Measure (E → Bool)))
          (T.restrict '' A) := by
    rw [Measure.map_apply T.measurable_restrict MeasurableSet.of_discrete]
    exact congrArg
      (fun B => (FKLimit.bernoulliProduct (incrementWeight S a ε) : Measure (E → Bool)) B)
      (FKLimit.eq_preimage_restrict_image hA)
  rw [incMass, incMass, happly, hmap, incrementWeight_restrict_profile]

/-- **Interior derivative of a cylinder event.**  For an event depending only on
the finite edge set `T`, the clamped decrement mass is differentiable on the
clamp-free region, with the pivotal coefficients read on `T`.  This covers
arbitrary edge types, not only finite ones. -/
theorem hasFDerivAt_massPair_of_interior_cylinder [DecidableEq E]
    (A : Set (E → Bool)) (S : Set E) (T : Finset E)
    (hA : FKLimit.DependsOnCoordinates A T) {b ε : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 ≤ ε) (hεb : ε < b) :
    HasFDerivAt (massPair A S)
      (∑ e : T, (offEventWeight (fun a : T => decWeight S a.val (b, ε)) e
          (T.restrict '' A) true -
        offEventWeight (fun a : T => decWeight S a.val (b, ε)) e
          (T.restrict '' A) false) • decCLM S e.val) (b, ε) := by
  have hfun : massPair A S =
      massPair (E := T) (T.restrict '' A) {e : T | (e : E) ∈ S} := by
    funext u
    exact mass_eq_mass_restrict A S T hA u.1 u.2
  rw [hfun]
  have h := hasFDerivAt_massPair_of_interior (E := T) (T.restrict '' A)
    {e : T | (e : E) ∈ S} hb0 hb1 hε0 hεb
  have hcoef : ∀ e : T,
      (offEventWeight (fun a : T => decWeight {x : T | (x : E) ∈ S} a (b, ε)) e
          (T.restrict '' A) true -
        offEventWeight (fun a : T => decWeight {x : T | (x : E) ∈ S} a (b, ε)) e
          (T.restrict '' A) false)
      = (offEventWeight (fun a : T => decWeight S a.val (b, ε)) e
          (T.restrict '' A) true -
        offEventWeight (fun a : T => decWeight S a.val (b, ε)) e
          (T.restrict '' A) false) := by
    intro e
    rw [show (fun a : T => decWeight {x : T | (x : E) ∈ S} a (b, ε))
        = (fun a : T => decWeight S a.val (b, ε)) from rfl]
  simp only [hcoef, decCLM_restrict] at h
  exact h

/-- The restriction to a finite support preserves increasing events. -/
lemma isUpperSet_restrict_image [DecidableEq E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (T : Finset E) : IsUpperSet (T.restrict '' A) := by
  intro x y hxy hx
  obtain ⟨ω, hω, rfl⟩ := hx
  refine ⟨fun e => if h : e ∈ T then y ⟨e, h⟩ else ω e, ?_, ?_⟩
  · refine hA (a := ω) (b := fun e => if h : e ∈ T then y ⟨e, h⟩ else ω e) ?_ hω
    intro e
    by_cases he : e ∈ T
    · simpa [he] using hxy ⟨e, he⟩
    · simp [he]
  · funext e
    simp [e.2]

/-- **Interior derivative of a cylinder event, increment profile.** -/
theorem hasFDerivAt_incMassPair_of_interior_cylinder [DecidableEq E]
    (A : Set (E → Bool)) (S : Set E) (T : Finset E)
    (hA : FKLimit.DependsOnCoordinates A T) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε0 : 0 ≤ ε) (haε1 : a + ε < 1) :
    HasFDerivAt (incMassPair A S)
      (∑ e : T, (offEventWeight (fun a' : T => incWeight S a'.val (a, ε)) e
          (T.restrict '' A) true -
        offEventWeight (fun a' : T => incWeight S a'.val (a, ε)) e
          (T.restrict '' A) false) • incCLM S e.val) (a, ε) := by
  have hfun : incMassPair A S =
      incMassPair (E := T) (T.restrict '' A) {e : T | (e : E) ∈ S} := by
    funext u
    exact incMass_eq_incMass_restrict A S T hA u.1 u.2
  rw [hfun]
  have h := hasFDerivAt_incMassPair_of_interior (E := T) (T.restrict '' A)
    {e : T | (e : E) ∈ S} ha0 ha1 hε0 haε1
  have hcoef : ∀ e : T,
      (offEventWeight (fun a' : T => incWeight {x : T | (x : E) ∈ S} a' (a, ε)) e
          (T.restrict '' A) true -
        offEventWeight (fun a' : T => incWeight {x : T | (x : E) ∈ S} a' (a, ε)) e
          (T.restrict '' A) false)
      = (offEventWeight (fun a' : T => incWeight S a'.val (a, ε)) e
          (T.restrict '' A) true -
        offEventWeight (fun a' : T => incWeight S a'.val (a, ε)) e
          (T.restrict '' A) false) := by
    intro e
    rw [show (fun a' : T => incWeight {x : T | (x : E) ∈ S} a' (a, ε))
        = (fun a' : T => incWeight S a'.val (a, ε)) from rfl]
  simp only [hcoef, incCLM_restrict] at h
  exact h

/-- **Pivotal trade derivative for a cylinder event.**  For an increasing event
depending on the finite set `T`, the interior derivative of the clamped
decrement mass is the trade functional built from the pivotal masses on `T`. -/
theorem massPair_deriv_decomp_cylinder [DecidableEq E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (S : Set E) (T : Finset E)
    (hdep : FKLimit.DependsOnCoordinates A T) {b ε : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) (hε0 : 0 ≤ ε) (hεb : ε < b) :
    HasFDerivAt (massPair A S)
      (tradeCLM (pivotTotal (fun a : T => decWeight S a.val (b, ε)) (T.restrict '' A))
        (pivotOn {e : T | (e : E) ∈ S} (fun a : T => decWeight S a.val (b, ε))
          (T.restrict '' A))) (b, ε) := by
  have hfun : massPair A S =
      massPair (E := T) (T.restrict '' A) {e : T | (e : E) ∈ S} := by
    funext u
    exact mass_eq_mass_restrict A S T hdep u.1 u.2
  rw [hfun]
  have h := massPair_deriv_decomp (E := T) (isUpperSet_restrict_image hA T)
    {e : T | (e : E) ∈ S} hb0 hb1 hε0 hεb
  have hprof : (fun a : T => decWeight {x : T | (x : E) ∈ S} a (b, ε))
      = (fun a : T => decWeight S a.val (b, ε)) := rfl
  rw [hprof] at h
  exact h

/-- **Pivotal trade derivative for a cylinder event, increment plane.** -/
theorem incMassPair_deriv_decomp_cylinder [DecidableEq E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (S : Set E) (T : Finset E)
    (hdep : FKLimit.DependsOnCoordinates A T) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε0 : 0 ≤ ε) (haε1 : a + ε < 1) :
    HasFDerivAt (incMassPair A S)
      (incTradeCLM (pivotTotal (fun a' : T => incWeight S a'.val (a, ε))
          (T.restrict '' A))
        (pivotOn {e : T | (e : E) ∈ S} (fun a' : T => incWeight S a'.val (a, ε))
          (T.restrict '' A))) (a, ε) := by
  have hfun : incMassPair A S =
      incMassPair (E := T) (T.restrict '' A) {e : T | (e : E) ∈ S} := by
    funext u
    exact incMass_eq_incMass_restrict A S T hdep u.1 u.2
  rw [hfun]
  have h := incMassPair_deriv_decomp (E := T) (isUpperSet_restrict_image hA T)
    {e : T | (e : E) ∈ S} ha0 ha1 hε0 haε1
  have hprof : (fun a' : T => incWeight {x : T | (x : E) ∈ S} a' (a, ε))
      = (fun a' : T => incWeight S a'.val (a, ε)) := rfl
  rw [hprof] at h
  exact h

/-! ### Non-vacuity of the pivot-trade hypothesis package -/


lemma offPivotalWeight_empty [Fintype E] [DecidableEq E] (r : E → ℝ) (e : E) :
    offPivotalWeight r e (∅ : Set (E → Bool)) = 0 := by
  rw [offPivotalWeight]
  apply Finset.sum_eq_zero
  intro off _
  simp [OffPivotal]

lemma offPivotalWeight_univ [Fintype E] [DecidableEq E] (r : E → ℝ) (e : E) :
    offPivotalWeight r e (Set.univ : Set (E → Bool)) = 0 := by
  rw [offPivotalWeight]
  apply Finset.sum_eq_zero
  intro off _
  simp [OffPivotal]

lemma pivotTotal_empty [Fintype E] [DecidableEq E] (r : E → ℝ) :
    pivotTotal r (∅ : Set (E → Bool)) = 0 := by
  rw [pivotTotal]
  exact Finset.sum_eq_zero (fun e _ => offPivotalWeight_empty r e)

lemma pivotOn_empty [Fintype E] [DecidableEq E] (S : Set E) (r : E → ℝ) :
    pivotOn S r (∅ : Set (E → Bool)) = 0 := by
  rw [pivotOn]
  exact Finset.sum_eq_zero (fun e _ => offPivotalWeight_empty r e)

lemma pivotTotal_univ [Fintype E] [DecidableEq E] (r : E → ℝ) :
    pivotTotal r (Set.univ : Set (E → Bool)) = 0 := by
  rw [pivotTotal]
  exact Finset.sum_eq_zero (fun e _ => offPivotalWeight_univ r e)

lemma pivotOn_univ [Fintype E] [DecidableEq E] (S : Set E) (r : E → ℝ) :
    pivotOn S r (Set.univ : Set (E → Bool)) = 0 := by
  rw [pivotOn]
  exact Finset.sum_eq_zero (fun e _ => offPivotalWeight_univ r e)

theorem mass_empty_event (S : Set E) (b ε : ℝ) :
    mass (∅ : Set (E → Bool)) S b ε = 0 := by
  rw [mass]
  simp

theorem incMass_univ_event (S : Set E) (a ε : ℝ) :
    incMass (Set.univ : Set (E → Bool)) S a ε = 1 := by
  rw [incMass]
  simp

/-- The decrement pivot-trade package is satisfiable: the empty event has zero
mass, no pivotal edge, and satisfies every hypothesis of
`decrement_AGInput_of_pivotTrade`. -/
theorem decrement_pivotTrade_consistent [Fintype E] [DecidableEq E]
    (S : Set E) (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < pc / 2) :
    ∃ b, pc < b ∧ b ≤ 1 ∧ ε ≤ b ∧ mass (∅ : Set (E → Bool)) S b ε = 0 := by
  have hmain := decrement_AGInput_of_pivotTrade (∅ : Set (E → Bool))
    (fun _ => (∅ : Set (E → Bool))) S pc c hpc0 hpc1 hc0 hc1
    (fun _ => isUpperSet_empty)
    (fun n b ε _ _ _ _ => by
      rw [pivotTotal_empty, pivotOn_empty]
      simp)
    (fun b ε => tendsto_const_nhds)
    (fun b _ _ => mass_empty_event S b 0)
    isUpperSet_empty MeasurableSet.empty ε hε0 hεpc
  obtain ⟨b, hpcb, hb1, hεb, -⟩ := hmain
  exact ⟨b, hpcb, hb1, hεb, mass_empty_event S b ε⟩

/-- The increment pivot-trade package is satisfiable: the full event has mass
one, no pivotal edge, and satisfies every hypothesis of
`increment_AGInput_of_pivotTrade`. -/
theorem increment_pivotTrade_consistent [Fintype E] [DecidableEq E]
    (S : Set E) (pc c : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1 - pc) / 2) :
    ∃ a, 0 ≤ a ∧ a < pc ∧ a + ε ≤ 1 ∧ incMass (Set.univ : Set (E → Bool)) S a ε = 1 := by
  have hmain := increment_AGInput_of_pivotTrade (Set.univ : Set (E → Bool))
    (fun _ => (Set.univ : Set (E → Bool))) S pc c hpc0 hpc1 hc0 hc1
    (fun _ => isUpperSet_univ)
    (fun n a ε _ _ _ _ => by
      rw [pivotTotal_univ, pivotOn_univ]
      simp)
    (fun a ε => tendsto_const_nhds)
    (fun a _ _ => incMass_univ_event S a 0)
    isUpperSet_univ MeasurableSet.univ ε hε0 hε1
  obtain ⟨a, ha0, hapc, haε1, -⟩ := hmain
  exact ⟨a, ha0, hapc, haε1, incMass_univ_event S a ε⟩

/-! ### The AG parameter windows from the pivot trade inequality

These four wrappers chain `decrement_AGInput_of_pivotTrade` /
`increment_AGInput_of_pivotTrade` with the public windows of `FK.AGWindow`.  They
are a *conditional* reduction: the pivot trade inequality and the baseline
percolation input stay explicit hypotheses. -/

/-- Upper window for `q < 1` from the decrement pivot trade inequality on the
enhanced edge set. -/
theorem upperWindow_of_pivotTrade_q_lt_one [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ k, IsUpperSet (An k))
    (hpivot : ∀ (k : ℕ) (b ε : ℝ), 0 < b → b < 1 → 0 < ε → ε < b →
      c * pivotTotal (fun a => decWeight Ee a (b, ε)) (An k) ≤
        pivotOn Ee (fun a => decWeight Ee a (b, ε)) (An k))
    (hconv : ∀ (b ε : ℝ), Tendsto (fun k => mass (An k) Ee b ε) atTop
      (𝓝 (mass A Ee b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A Ee b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.upperWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (decrement_AGInput_of_pivotTrade A An Ee pc c hpc0 hpc1 hc0 hc1 hAn hpivot
      hconv hbase hA hmeas)

/-- Lower window for `q < 1` from the increment pivot trade inequality on the
base edge set. -/
theorem lowerWindow_of_pivotTrade_q_lt_one [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ k, IsUpperSet (An k))
    (hpivot : ∀ (k : ℕ) (a ε : ℝ), 0 < a → a < 1 → 0 < ε → a + ε < 1 →
      c * pivotTotal (fun a' => incWeight Eb a' (a, ε)) (An k) ≤
        pivotOn Eb (fun a' => incWeight Eb a' (a, ε)) (An k))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun k => incMass (An k) Eb a ε) atTop
      (𝓝 (incMass A Eb a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A Eb a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.lowerWindow_of_AG_q_lt_one A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (increment_AGInput_of_pivotTrade A An Eb pc c hpc0 hpc1 hc0 hc1 hAn hpivot
      hconv hbase hA hmeas)

/-- Upper window for `1 < q` from the decrement pivot trade inequality on the
base edge set. -/
theorem upperWindow_of_pivotTrade_one_lt_q [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ k, IsUpperSet (An k))
    (hpivot : ∀ (k : ℕ) (b ε : ℝ), 0 < b → b < 1 → 0 < ε → ε < b →
      c * pivotTotal (fun a => decWeight Eb a (b, ε)) (An k) ≤
        pivotOn Eb (fun a => decWeight Eb a (b, ε)) (An k))
    (hconv : ∀ (b ε : ℝ), Tendsto (fun k => mass (An k) Eb b ε) atTop
      (𝓝 (mass A Eb b ε)))
    (hbase : ∀ b, 0 ≤ b → b < pc → mass A Eb b 0 = 0)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.UpperWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.upperWindow_of_AG_one_lt_q A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (decrement_AGInput_of_pivotTrade A An Eb pc c hpc0 hpc1 hc0 hc1 hAn hpivot
      hconv hbase hA hmeas)

/-- Lower window for `1 < q` from the increment pivot trade inequality on the
enhanced edge set. -/
theorem lowerWindow_of_pivotTrade_one_lt_q [Fintype E] [DecidableEq E]
    (A : Set (E → Bool)) (An : ℕ → Set (E → Bool)) (pc : ℝ) (Eb Ee : Set E)
    (n m : ℕ) (q c : ℝ) (hq : 0 < q) (hq1 : 1 < q)
    (hpc0 : 0 < pc) (hpc1 : pc < 1) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hAn : ∀ k, IsUpperSet (An k))
    (hpivot : ∀ (k : ℕ) (a ε : ℝ), 0 < a → a < 1 → 0 < ε → a + ε < 1 →
      c * pivotTotal (fun a' => incWeight Ee a' (a, ε)) (An k) ≤
        pivotOn Ee (fun a' => incWeight Ee a' (a, ε)) (An k))
    (hconv : ∀ (a ε : ℝ), Tendsto (fun k => incMass (An k) Ee a ε) atTop
      (𝓝 (incMass A Ee a ε)))
    (hbase : ∀ a, pc < a → a ≤ 1 → incMass A Ee a 0 = 1)
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) :
    FK.EssentialWindow.LowerWindow A pc Eb Ee n m q hq :=
  FK.EssentialWindow.lowerWindow_of_AG_one_lt_q A pc Eb Ee n m q hq hq1 hpc0 hpc1 hA hmeas
    (increment_AGInput_of_pivotTrade A An Ee pc c hpc0 hpc1 hc0 hc1 hAn hpivot
      hconv hbase hA hmeas)

end

end FK.AGMassDerivative
