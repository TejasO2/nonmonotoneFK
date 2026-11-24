/-
# Theorem 5.1 core: uniqueness from a cofinal free boundary

Source: Beffara--Faipeur--Oke, arXiv:2512.16486v1, Theorem 5.1 and its proof.

The paper's argument: take a coupling `(ω₁, ω₂, ω₃)` of two Gibbs measures with a
common dominating law `ρ`; almost surely the configuration `ω₃` admits cofinally
many finite boxes with *closed* boundary; on such a box the FK conditional law of
both `ω₁` and `ω₂` is the closed-exterior (free) one, so the two conditional
probabilities agree; each exterior conditional probability converges to the
unconditional mass by the reverse martingale; and agreement on an infinite
subsequence of a convergent sequence identifies the limits.

This file isolates that mechanism exactly.  The geometric input is reduced to
the single statement that `ρ`-almost every configuration has closed box
boundaries infinitely often; the boundary/free identity is a property of the
boundary convention, isolated as `IsFreeAtClosedBoundary`.
-/
import FK.NestedBoundaryUniqueness
import FK.ConditionallyIndependentOrderedCoupling

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option linter.unusedSectionVars false

namespace FK.InfiniteVolume

universe u v

variable {E : Type u} [Countable E]

/-! ## Closed boundaries and their cofinal occurrence -/

/-- All edges of `bdry n` are closed in `ω`. -/
def BoundaryClosed (bdry : ℕ → Set E) (n : ℕ) (ω : Configuration E) : Prop :=
  ∀ e ∈ bdry n, ω e = false

/-- The boundary of the `n`-th box is closed for infinitely many `n`. -/
def FrequentlyBoundaryClosed (bdry : ℕ → Set E) (ω : Configuration E) : Prop :=
  ∃ᶠ n in atTop, BoundaryClosed bdry n ω

lemma frequentlyBoundaryClosed_iff {bdry : ℕ → Set E} {ω : Configuration E} :
    FrequentlyBoundaryClosed bdry ω ↔ ∀ N, ∃ n ≥ N, BoundaryClosed bdry n ω :=
  Filter.frequently_atTop

/-- Closing more edges preserves closed boundaries. -/
lemma BoundaryClosed.mono {bdry : ℕ → Set E} {n : ℕ} {ω ω' : Configuration E}
    (hle : ω' ≤ ω) (h : BoundaryClosed bdry n ω) : BoundaryClosed bdry n ω' := by
  intro e he
  have h1 : ω' e ≤ ω e := hle e
  rw [h e he] at h1
  cases h2 : ω' e with
  | false => rfl
  | true => rw [h2] at h1; exact absurd h1 (by decide)

lemma FrequentlyBoundaryClosed.of_le {bdry : ℕ → Set E} {ω ω' : Configuration E}
    (hle : ω' ≤ ω) (h : FrequentlyBoundaryClosed bdry ω) :
    FrequentlyBoundaryClosed bdry ω' :=
  Filter.Frequently.mono h fun _ hn => BoundaryClosed.mono hle hn

/-! ## The free boundary convention at closed boundaries -/

section Convention

variable (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
  (bdry : ℕ → Set E)

/-- The convention is *free at closed boundaries*: whenever every boundary edge
of a box is closed in the exterior configuration, the induced boundary partition
is the closed-exterior reference partition.  This is the only property of the
source's free convention used by the uniqueness argument below. -/
def IsFreeAtClosedBoundary : Prop :=
  ∀ (n : ℕ) (ω : Configuration E), BoundaryClosed bdry n ω →
    Φ.partition n (FKLimit.exteriorRestriction (exh.box n).edges ω) =
      Φ.partition n (exh.box n).closedExterior

variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

end Convention

section Mass

variable {E : Type u}

/-- The conditional mass of a box-supported event depends on the exterior
configuration only through the induced boundary partition. -/
theorem finiteBox_conditionalLaw_real_eq_of_partition_eq
    (B : FiniteBox E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) {η η' : B.Exterior} (h : α η = α η')
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    (B.conditionalLaw hq hp α η : Measure (Configuration E)).real A =
      (B.conditionalLaw hq hp α η' : Measure (Configuration E)).real A := by
  have hC : MeasurableSet (B.interiorRestriction '' A) := MeasurableSet.of_discrete
  rw [B.eq_preimage_interiorRestriction_image hA,
    B.conditionalLaw_real_interior_preimage hq hp α η hC,
    B.conditionalLaw_real_interior_preimage hq hp α η' hC, h]

end Mass

section MassClosed

variable (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
  (bdry : ℕ → Set E)

variable {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- At a closed boundary the conditional FK mass of a box-supported event is its
reference (closed-exterior) mass, for *every* DLR law with this convention. -/
theorem conditionalLaw_real_eq_of_boundaryClosed
    (hfree : IsFreeAtClosedBoundary exh Φ bdry)
    (n : ℕ) {ω : Configuration E} (hω : BoundaryClosed bdry n ω)
    {A : Set (Configuration E)}
    (hA : FKLimit.DependsOnCoordinates A (exh.box n).edges) :
    ((exh.box n).conditionalLaw hq hp (Φ.partition n)
        (FKLimit.exteriorRestriction (exh.box n).edges ω) :
        Measure (Configuration E)).real A =
      ((exh.box n).conditionalLaw hq hp (Φ.partition n) (exh.box n).closedExterior :
        Measure (Configuration E)).real A :=
  finiteBox_conditionalLaw_real_eq_of_partition_eq (exh.box n) hq hp (Φ.partition n)
    (hfree n ω hω) hA

end MassClosed

/-! ## Reverse martingale convergence for an arbitrary DLR law -/

section ReverseMartingale

variable {E : Type u} [Countable E]

/-- Along any box exhaustion, the exterior conditional probability of a
box-supported event converges almost everywhere to its tail conditional
expectation.  This is reverse-martingale convergence for an arbitrary (not
necessarily extremal) DLR law, using only the exact exterior identification of
the DLR equation. -/
theorem tendsto_ae_exteriorConditionalLaw_of_dlr
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp)
    {A : Set (Configuration E)} {T : Finset E}
    (hAT : FKLimit.DependsOnCoordinates A T) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n => ((exh.box n).conditionalLaw hq hp (Φ.partition n)
        (FKLimit.exteriorRestriction (exh.box n).edges ω) :
        Measure (Configuration E)).real A) atTop
        (𝓝 (MeasureTheory.condExp (FKLimit.tailSigma (E := E))
          (μ : Measure (Configuration E)) (A.indicator (fun _ => 1)) ω)) := by
  classical
  have hcof : ∀ T : Finset E, ∃ n, T ⊆ (exh.box n).edges := by
    intro T
    induction T using Finset.induction with
    | empty => exact ⟨0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨n1, h1⟩ := ih
      obtain ⟨n2, h2⟩ := exh.covers a
      refine ⟨max n1 n2, fun e he => ?_⟩
      rcases Finset.mem_insert.mp he with rfl | hes
      · exact exh.monotone (le_max_right _ _) h2
      · exact exh.monotone (le_max_left _ _) (h1 hes)
  have hrev := FKLimit.tendsto_ae_condExp_indicator_outside_to_tail
    (μ := (μ : Measure (Configuration E))) (S := fun n => (exh.box n).edges)
    exh.monotone hcof (A := A) hAT.measurableSet
  have hident : ∀ᵐ ω ∂(μ : Measure (Configuration E)), ∀ n,
      T ⊆ (exh.box n).edges →
      MeasureTheory.condExp (FKLimit.outsideSigma (exh.box n).edges)
          (μ : Measure (Configuration E)) (A.indicator (fun _ => 1)) ω =
        ((exh.box n).conditionalLaw hq hp (Φ.partition n)
          (FKLimit.exteriorRestriction (exh.box n).edges ω) :
          Measure (Configuration E)).real A := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    by_cases hn : T ⊆ (exh.box n).edges
    · filter_upwards [(exh.box n).condExp_of_dependsOn_edges_of_isDLR hq hp (Φ.partition n)
        (Φ.measurable_partition n) μ (hμ n) (hAT.mono hn)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω hω => absurd hω hn
  filter_upwards [hrev, hident] with ω hrevω hidentω
  refine hrevω.congr' ?_
  filter_upwards [exh.eventually_subset T] with n hn
  exact hidentω n hn

/-! ## Extraction of a cofinal subsequence -/

/-- From a property that holds frequently at infinity, extract a strictly
increasing sequence of indices above a prescribed bound on which it holds. -/
lemma exists_strictMono_of_frequently {P : ℕ → Prop} (hfreq : ∃ᶠ n in atTop, P n)
    (N : ℕ) : ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ m, N ≤ k m) ∧ ∀ m, P (k m) := by
  have hStep : ∀ a : ℕ, ∃ b, a < b ∧ P b := by
    intro a
    obtain ⟨b, hb, hPb⟩ := (Filter.frequently_atTop.mp hfreq) (a + 1)
    exact ⟨b, Nat.lt_of_succ_le hb, hPb⟩
  choose f hf using hStep
  let k : ℕ → ℕ := fun m => Nat.iterate f (m + 1) N
  have hk_succ : ∀ m, k (m + 1) = f (k m) := by
    intro m
    show Nat.iterate f (m + 1 + 1) N = f (Nat.iterate f (m + 1) N)
    rw [Function.iterate_succ_apply']
  have hk_zero : k 0 = f N := by
    show Nat.iterate f 1 N = f N
    rw [Function.iterate_one]
  have hk_eq : ∀ m, k m = f (Nat.iterate f m N) := by
    intro m
    show Nat.iterate f (m + 1) N = f (Nat.iterate f m N)
    rw [Function.iterate_succ_apply']
  have hincr : ∀ j, k j ≤ k (j + 1) := by
    intro j
    rw [hk_succ j]
    exact le_of_lt (hf (k j)).1
  have hmono : ∀ j, k 0 ≤ k j := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ i ih => exact ih.trans (hincr i)
  refine ⟨k, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro m
    rw [hk_succ m]
    exact (hf (k m)).1
  · intro m
    have hbase : N ≤ k 0 := by
      rw [hk_zero]
      exact le_of_lt (hf N).1
    exact hbase.trans (hmono m)
  · intro m
    rw [hk_eq m]
    exact (hf (Nat.iterate f m N)).2

end ReverseMartingale

/-! ## The main uniqueness theorem -/

section Main

variable {E : Type u} [Countable E]

/-- **Theorem 5.1 core (coupled form).**  Let `μ₁, μ₂` be DLR laws for one
measurable boundary assignment at parameters `0 < q`, `p ≤ 1`, and let
`(ω₁, ω₂, ω₃)` be a coupling with `ω₁ ≤ ω₃`, `ω₂ ≤ ω₃` almost surely.  If the
convention is free at closed boundaries and `ω₃` has closed box boundaries
infinitely often almost surely, then `μ₁ = μ₂`.

This is the exact mechanism of the proof of Theorem 5.1: on a closed boundary of
a box containing the support of a cylinder event, both exterior conditional
probabilities equal the same reference value, and reverse-martingale convergence
identifies their limits. -/
theorem eq_of_orderedTriple_frequently_boundaryClosed
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (bdry : ℕ → Set E) (hfree : IsFreeAtClosedBoundary exh Φ bdry)
    {μ1 μ2 ρ : ProbabilityMeasure (Configuration E)}
    (hμ1 : μ1 ∈ DLRMeasures exh Φ hq hp) (hμ2 : μ2 ∈ DLRMeasures exh Φ hq hp)
    (hγ : FKLimit.HasOrderedTriple μ1 μ2 ρ)
    (hρ : ∀ᵐ η ∂(ρ : Measure (Configuration E)), FrequentlyBoundaryClosed bdry η) :
    μ1 = μ2 := by
  classical
  obtain ⟨γ, hm1, hm2, hm3, ho1, ho2⟩ := hγ
  refine ProbabilityMeasure.toMeasure_injective ?_
  refine FKModel.measure_ext_of_eq_on_boolCylinders (μ1 : Measure (Configuration E))
    (μ2 : Measure (Configuration E)) ?_
  intro I S
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, I ⊆ (exh.box n).edges := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (exh.eventually_subset I)
    exact ⟨N, hN⟩
  let A : Set (Configuration E) := cylinder I S
  have hAT : FKLimit.DependsOnCoordinates A I :=
    FK.InfiniteVolume.dependsOnCoordinates_cylinder I S
  have hAmeas : MeasurableSet A := hAT.measurableSet
  let val : ℕ → Configuration E → ℝ := fun n ω =>
    ((exh.box n).conditionalLaw hq hp (Φ.partition n)
      (FKLimit.exteriorRestriction (exh.box n).edges ω) : Measure (Configuration E)).real A
  let X : Configuration E → ℝ := fun ω =>
    MeasureTheory.condExp (FKLimit.tailSigma (E := E)) (μ1 : Measure (Configuration E))
      (A.indicator (fun _ => 1)) ω
  let Y : Configuration E → ℝ := fun ω =>
    MeasureTheory.condExp (FKLimit.tailSigma (E := E)) (μ2 : Measure (Configuration E))
      (A.indicator (fun _ => 1)) ω
  have hlim1 : ∀ᵐ ω ∂(μ1 : Measure (Configuration E)),
      Tendsto (fun n => val n ω) atTop (𝓝 (X ω)) :=
    tendsto_ae_exteriorConditionalLaw_of_dlr exh Φ hq hp μ1 hμ1 hAT
  have hlim2 : ∀ᵐ ω ∂(μ2 : Measure (Configuration E)),
      Tendsto (fun n => val n ω) atTop (𝓝 (Y ω)) :=
    tendsto_ae_exteriorConditionalLaw_of_dlr exh Φ hq hp μ2 hμ2 hAT
  -- measure level marginal identities of the triple
  have hm1' : (γ : Measure (Configuration E × Configuration E × Configuration E)).map
      (fun z => z.1) = (μ1 : Measure (Configuration E)) := by
    rw [← ProbabilityMeasure.toMeasure_map]
    exact congrArg Subtype.val hm1
  have hm2' : (γ : Measure (Configuration E × Configuration E × Configuration E)).map
      (fun z => z.2.1) = (μ2 : Measure (Configuration E)) := by
    rw [← ProbabilityMeasure.toMeasure_map]
    exact congrArg Subtype.val hm2
  have hm3' : (γ : Measure (Configuration E × Configuration E × Configuration E)).map
      (fun z => z.2.2) = (ρ : Measure (Configuration E)) := by
    rw [← ProbabilityMeasure.toMeasure_map]
    exact congrArg Subtype.val hm3
  have hqmp1 : QuasiMeasurePreserving
      (fun z : Configuration E × Configuration E × Configuration E => z.1)
      (γ : Measure (Configuration E × Configuration E × Configuration E))
      (μ1 : Measure (Configuration E)) :=
    ⟨by fun_prop, Measure.absolutelyContinuous_of_le (le_of_eq hm1')⟩
  have hqmp2 : QuasiMeasurePreserving
      (fun z : Configuration E × Configuration E × Configuration E => z.2.1)
      (γ : Measure (Configuration E × Configuration E × Configuration E))
      (μ2 : Measure (Configuration E)) :=
    ⟨by fun_prop, Measure.absolutelyContinuous_of_le (le_of_eq hm2')⟩
  have hqmp3 : QuasiMeasurePreserving
      (fun z : Configuration E × Configuration E × Configuration E => z.2.2)
      (γ : Measure (Configuration E × Configuration E × Configuration E))
      (ρ : Measure (Configuration E)) :=
    ⟨by fun_prop, Measure.absolutelyContinuous_of_le (le_of_eq hm3')⟩
  have hpush1 : ∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      Tendsto (fun n => val n z.1) atTop (𝓝 (X z.1)) :=
    hqmp1.tendsto_ae.eventually hlim1
  have hpush2 : ∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      Tendsto (fun n => val n z.2.1) atTop (𝓝 (Y z.2.1)) :=
    hqmp2.tendsto_ae.eventually hlim2
  have hpush3 : ∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      FrequentlyBoundaryClosed bdry z.2.2 :=
    hqmp3.tendsto_ae.eventually hρ
  have hkey : ∀ᵐ z ∂(γ : Measure (Configuration E × Configuration E × Configuration E)),
      X z.1 = Y z.2.1 := by
    filter_upwards [hpush1, hpush2, hpush3, ho1, ho2] with z hz1 hz2 hz3 hord1 hord2
    obtain ⟨k, hkmono, hkge, hkP⟩ := exists_strictMono_of_frequently hz3 N
    have hEqAt : ∀ m, val (k m) z.1 = val (k m) z.2.1 := by
      intro m
      have hkm : I ⊆ (exh.box (k m)).edges := fun e he => hN (k m) (hkge m) he
      have hA'm : FKLimit.DependsOnCoordinates A (exh.box (k m)).edges := hAT.mono hkm
      exact (conditionalLaw_real_eq_of_boundaryClosed exh Φ bdry hq hp hfree (k m)
          (BoundaryClosed.mono hord1 (hkP m)) hA'm).trans
        (conditionalLaw_real_eq_of_boundaryClosed exh Φ bdry hq hp hfree (k m)
          (BoundaryClosed.mono hord2 (hkP m)) hA'm).symm
    have hl1 : Tendsto (fun m => val (k m) z.1) atTop (𝓝 (X z.1)) :=
      hz1.comp hkmono.tendsto_atTop
    have hl2 : Tendsto (fun m => val (k m) z.2.1) atTop (𝓝 (Y z.2.1)) :=
      hz2.comp hkmono.tendsto_atTop
    have hl2' : Tendsto (fun m => val (k m) z.1) atTop (𝓝 (Y z.2.1)) :=
      hl2.congr' (Filter.Eventually.of_forall fun m => (hEqAt m).symm)
    exact tendsto_nhds_unique hl1 hl2'
  have hXint : MeasureTheory.Integrable X (μ1 : Measure (Configuration E)) :=
    MeasureTheory.integrable_condExp
  have hYint : MeasureTheory.Integrable Y (μ2 : Measure (Configuration E)) :=
    MeasureTheory.integrable_condExp
  have hIntEq : ∫ z, X z.1 ∂(γ : Measure (Configuration E × Configuration E × Configuration E)) =
      ∫ z, Y z.2.1 ∂(γ : Measure (Configuration E × Configuration E × Configuration E)) :=
    MeasureTheory.integral_congr_ae hkey
  have hXval : ∫ ω, X ω ∂(μ1 : Measure (Configuration E)) =
      (μ1 : Measure (Configuration E)).real A := by
    have h := MeasureTheory.integral_condExp (μ := (μ1 : Measure (Configuration E)))
      (m := FKLimit.tailSigma (E := E))
      (m₀ := (inferInstance : MeasurableSpace (Configuration E)))
      (f := A.indicator (fun _ => (1 : ℝ))) FKLimit.tailSigma_le
    rw [h, MeasureTheory.integral_indicator_const (1 : ℝ) hAmeas]
    simp
  have hYval : ∫ ω, Y ω ∂(μ2 : Measure (Configuration E)) =
      (μ2 : Measure (Configuration E)).real A := by
    have h := MeasureTheory.integral_condExp (μ := (μ2 : Measure (Configuration E)))
      (m := FKLimit.tailSigma (E := E))
      (m₀ := (inferInstance : MeasurableSpace (Configuration E)))
      (f := A.indicator (fun _ => (1 : ℝ))) FKLimit.tailSigma_le
    rw [h, MeasureTheory.integral_indicator_const (1 : ℝ) hAmeas]
    simp
  have hInt1 : ∫ z, X z.1 ∂(γ : Measure (Configuration E × Configuration E × Configuration E)) =
      (μ1 : Measure (Configuration E)).real A := by
    rw [← hXval, ← hm1']
    exact (MeasureTheory.integral_map (μ := (γ : Measure _))
      (φ := fun z : Configuration E × Configuration E × Configuration E => z.1)
      (f := X) (by fun_prop) (by rw [hm1']; exact hXint.aestronglyMeasurable)).symm
  have hInt2 : ∫ z, Y z.2.1 ∂(γ : Measure (Configuration E × Configuration E × Configuration E)) =
      (μ2 : Measure (Configuration E)).real A := by
    rw [← hYval, ← hm2']
    exact (MeasureTheory.integral_map (μ := (γ : Measure _))
      (φ := fun z : Configuration E × Configuration E × Configuration E => z.2.1)
      (f := Y) (by fun_prop) (by rw [hm2']; exact hYint.aestronglyMeasurable)).symm
  have hreal : (μ1 : Measure (Configuration E)).real A =
      (μ2 : Measure (Configuration E)).real A := by
    rw [← hInt1, ← hInt2, hIntEq]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ1 : Measure (Configuration E)) A)
    (measure_ne_top (μ2 : Measure (Configuration E)) A)).mp (by
      simpa only [Measure.real_def] using hreal)

end Main

/-! ## Inheriting closed boundaries from a dominating law -/

section Domination

variable {E : Type u} [Countable E] (bdry : ℕ → Set E)

lemma measurableSet_boundaryClosed (n : ℕ) :
    MeasurableSet {ω : Configuration E | BoundaryClosed bdry n ω} := by
  have h : {ω : Configuration E | BoundaryClosed bdry n ω}
      = ⋂ e : E, ⋂ (_ : e ∈ bdry n), {ω : Configuration E | ω e = false} := by
    ext ω
    simp [BoundaryClosed]
  rw [h]
  refine MeasurableSet.iInter fun e => ?_
  by_cases he : e ∈ bdry n
  · rw [show (⋂ (_ : e ∈ bdry n), {ω : Configuration E | ω e = false})
        = Set.pi ({e} : Set E) (fun _ => ({false} : Set Bool)) by
      ext ω; simp [he]]
    exact MeasurableSet.pi (Set.to_countable ({e} : Set E)) (fun i _ => MeasurableSet.singleton false)
  · rw [show (⋂ (_ : e ∈ bdry n), {ω : Configuration E | ω e = false}) = Set.univ by
      ext ω; simp [he]]
    exact MeasurableSet.univ

lemma measurableSet_frequentlyBoundaryClosed :
    MeasurableSet {ω : Configuration E | FrequentlyBoundaryClosed bdry ω} := by
  have h : {ω : Configuration E | FrequentlyBoundaryClosed bdry ω}
      = ⋂ N : ℕ, ⋃ n ∈ {n : ℕ | N ≤ n}, {ω : Configuration E | BoundaryClosed bdry n ω} := by
    ext ω
    simp [FrequentlyBoundaryClosed, Filter.frequently_atTop, Set.mem_iInter, Set.mem_iUnion]
  rw [h]
  exact MeasurableSet.iInter fun N =>
    MeasurableSet.biUnion (Set.to_countable _) fun n _ => measurableSet_boundaryClosed bdry n

lemma isLowerSet_frequentlyBoundaryClosed :
    IsLowerSet {ω : Configuration E | FrequentlyBoundaryClosed bdry ω} := by
  intro ω ω' hle hω
  exact FrequentlyBoundaryClosed.of_le hle hω

/-- A law dominated by a law with closed box boundaries almost surely has closed
box boundaries almost surely.  This is the step by which the paper transfers the
boundary property of `P` to every Gibbs measure it dominates. -/
theorem ae_frequentlyBoundaryClosed_of_stochasticallyDominates
    {ρ μ : ProbabilityMeasure (Configuration E)}
    (hdom : FKLimit.StochasticallyDominates ρ μ)
    (hρ : ∀ᵐ η ∂(ρ : Measure (Configuration E)), FrequentlyBoundaryClosed bdry η) :
    ∀ᵐ ω ∂(μ : Measure (Configuration E)), FrequentlyBoundaryClosed bdry ω := by
  have hcompl : (μ : Measure (Configuration E))
      {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} = 0 := by
    have hupper : IsUpperSet {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} := by
      intro a b hab hb ha
      exact hb (isLowerSet_frequentlyBoundaryClosed bdry hab ha)
    have hmeas : MeasurableSet {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} :=
      (measurableSet_frequentlyBoundaryClosed bdry).compl
    have hleNN : μ {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} ≤
        ρ {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} :=
      hdom _ hmeas hupper
    have hle : (μ : Measure (Configuration E))
        {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} ≤
        (ρ : Measure (Configuration E))
          {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} := by
      rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact ENNReal.coe_le_coe.mpr hleNN
    have hρzero : (ρ : Measure (Configuration E))
        {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} = 0 := by
      rw [MeasureTheory.ae_iff] at hρ
      exact hρ
    have hle0 : (μ : Measure (Configuration E))
        {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} ≤ 0 := by
      calc (μ : Measure (Configuration E))
            {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω}
          ≤ (ρ : Measure (Configuration E))
            {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω} := hle
        _ = 0 := hρzero
    exact eq_bot_iff.mpr hle0
  rw [MeasureTheory.ae_iff]
  exact hcompl

end Domination

/-! ## Theorem 5.1 at the level of the DLR class -/

section Class

variable {E : Type u} [Countable E]

/-- **Theorem 5.1 (domination form).**  Fix a convention `Φ` and parameters
`0 < q`, `p ≤ 1`.  Suppose the convention is free at closed boundaries, and that
there is a law `ρ` with closed box boundaries infinitely often almost surely that
stochastically dominates every DLR law.  Then the DLR class is a singleton. -/
theorem forall_eq_of_dominated_frequently_boundaryClosed
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (bdry : ℕ → Set E) (hfree : IsFreeAtClosedBoundary exh Φ bdry)
    (ρ : ProbabilityMeasure (Configuration E))
    (hρ : ∀ᵐ η ∂(ρ : Measure (Configuration E)), FrequentlyBoundaryClosed bdry η)
    (hdom : ∀ μ ∈ DLRMeasures exh Φ hq hp, FKLimit.StochasticallyDominates ρ μ) :
    ∀ μ ∈ DLRMeasures exh Φ hq hp, ∀ ν ∈ DLRMeasures exh Φ hq hp, μ = ν := by
  intro μ hμ ν hν
  exact eq_of_orderedTriple_frequently_boundaryClosed exh Φ hq hp bdry hfree hμ hν
    (FKLimit.hasOrderedTriple_iff.mpr ⟨hdom μ hμ, hdom ν hν⟩) hρ

/-- **Theorem 5.1 (source form).**  With the closed-boundary property of the
dominating law stated as a full-measure event, exactly as the paper's
`P(Ω̃) = 1`. -/
theorem forall_eq_of_dominated_fullMeasure_boundaryClosed
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (bdry : ℕ → Set E) (hfree : IsFreeAtClosedBoundary exh Φ bdry)
    (ρ : ProbabilityMeasure (Configuration E))
    (hρ : (ρ : Measure (Configuration E))
      {ω : Configuration E | FrequentlyBoundaryClosed bdry ω} = 1)
    (hdom : ∀ μ ∈ DLRMeasures exh Φ hq hp, FKLimit.StochasticallyDominates ρ μ) :
    ∀ μ ∈ DLRMeasures exh Φ hq hp, ∀ ν ∈ DLRMeasures exh Φ hq hp, μ = ν := by
  refine forall_eq_of_dominated_frequently_boundaryClosed exh Φ hq hp bdry hfree ρ ?_ hdom
  rw [MeasureTheory.ae_iff]
  rw [show {ω : Configuration E | ¬ FrequentlyBoundaryClosed bdry ω}
      = {ω : Configuration E | FrequentlyBoundaryClosed bdry ω}ᶜ from rfl,
    measure_compl (measurableSet_frequentlyBoundaryClosed bdry)
      (by rw [hρ]; exact ENNReal.one_ne_top)]
  simp [hρ]

/-- **Theorem 5.1 (coherent-convention form).**  The same conclusion for a
coherent boundary convention `Φ` and its Gibbs class `GibbsMeasures`, which is
the paper's `G^Φ_{p,q}`. -/
theorem forall_eq_gibbsMeasures_of_dominated_frequently_boundaryClosed
    (exh : BoxExhaustion.{u, v} E) {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : BoundaryConvention exh hq hp)
    (bdry : ℕ → Set E)
    (hfree : IsFreeAtClosedBoundary exh Φ.toBoundaryAssignment bdry)
    (ρ : ProbabilityMeasure (Configuration E))
    (hρ : ∀ᵐ η ∂(ρ : Measure (Configuration E)), FrequentlyBoundaryClosed bdry η)
    (hdom : ∀ μ ∈ GibbsMeasures exh Φ, FKLimit.StochasticallyDominates ρ μ) :
    ∀ μ ∈ GibbsMeasures exh Φ, ∀ ν ∈ GibbsMeasures exh Φ, μ = ν :=
  forall_eq_of_dominated_frequently_boundaryClosed exh Φ.toBoundaryAssignment hq hp
    bdry hfree ρ hρ hdom

/-- **Theorem 5.1, subsingleton form.** -/
theorem subsingleton_dlrMeasures_of_dominated_frequently_boundaryClosed
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (bdry : ℕ → Set E) (hfree : IsFreeAtClosedBoundary exh Φ bdry)
    (ρ : ProbabilityMeasure (Configuration E))
    (hρ : ∀ᵐ η ∂(ρ : Measure (Configuration E)), FrequentlyBoundaryClosed bdry η)
    (hdom : ∀ μ ∈ DLRMeasures exh Φ hq hp, FKLimit.StochasticallyDominates ρ μ) :
    Subsingleton (DLRMeasures exh Φ hq hp) :=
  ⟨fun μ ν => Subtype.ext
    (forall_eq_of_dominated_frequently_boundaryClosed exh Φ hq hp bdry hfree ρ hρ hdom
      μ μ.2 ν ν.2)⟩

end Class




/-! ## Non-vacuity of the hypotheses

The uniqueness theorem is only meaningful if its hypotheses can hold together.
Here are the two elementary facts that make the pair
`(bdry ≡ ∅, boundary-independent convention)` a genuine instance: the empty
boundary family is always closed, and the Dirac law at the all-open
configuration dominates every law.  Hence for any boundary-independent
convention the hypothesis set of
`forall_eq_of_dominated_frequently_boundaryClosed` is satisfied, and the theorem
concludes (correctly) uniqueness of its DLR class. -/

section NonVacuity

variable {E : Type u} [Countable E]

/-- With no boundary edges every configuration has a closed boundary, for every
box. -/
lemma frequentlyBoundaryClosed_empty (ω : Configuration E) :
    FrequentlyBoundaryClosed (fun _ : ℕ => (∅ : Set E)) ω :=
  Filter.Frequently.of_forall fun _ => by
    intro e he
    simp at he

/-- A boundary-independent convention is free at closed boundaries for the empty
boundary family. -/
lemma isFreeAtClosedBoundary_empty_of_const (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box)
    (hconst : ∀ (n : ℕ) (η : (exh.box n).Exterior),
      Φ.partition n η = Φ.partition n (exh.box n).closedExterior) :
    IsFreeAtClosedBoundary exh Φ (fun _ => (∅ : Set E)) :=
  fun n _ _ => hconst n _

/-- The Dirac law at the all-open configuration stochastically dominates every
law on configurations. -/
theorem stochasticallyDominates_dirac_allTrue
    (μ : ProbabilityMeasure (Configuration E)) :
    FKLimit.StochasticallyDominates
      ⟨Measure.dirac (fun _ : E => true), Measure.dirac.isProbabilityMeasure⟩ μ := by
  intro A hA hup
  change ((μ : Measure (Configuration E)) A).toNNReal ≤
    ((Measure.dirac (fun _ : E => true) : Measure (Configuration E)) A).toNNReal
  by_cases h : (fun _ : E => true) ∈ A
  · rw [Measure.dirac_apply_of_mem h]
    have hle : (μ : Measure (Configuration E)) A ≤ 1 := by
      have := measure_mono (μ := (μ : Measure (Configuration E))) (Set.subset_univ A)
      simpa using this
    rw [← ENNReal.coe_le_coe]
    simp [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top hle), hle]
  · have hAempty : A = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => h (hup ?_ hω)
      intro e
      cases ω e <;> simp
    rw [hAempty]
    simp


/-- **Non-vacuity, assembled.**  For any boundary-independent convention, the
empty boundary family and the Dirac law at the all-open configuration satisfy
*all* hypotheses of `forall_eq_of_dominated_frequently_boundaryClosed`, and its
conclusion holds.  So the hypothesis set is consistent and the theorem is not
vacuous. -/
theorem exists_satisfying_uniqueness_hypotheses (exh : BoxExhaustion.{u, v} E)
    (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hconst : ∀ (n : ℕ) (η : (exh.box n).Exterior),
      Φ.partition n η = Φ.partition n (exh.box n).closedExterior) :
    IsFreeAtClosedBoundary exh Φ (fun _ => (∅ : Set E)) ∧
      (∀ᵐ η ∂((⟨Measure.dirac (fun _ : E => true),
          Measure.dirac.isProbabilityMeasure⟩ : ProbabilityMeasure (Configuration E)) :
          Measure (Configuration E)),
        FrequentlyBoundaryClosed (fun _ => (∅ : Set E)) η) ∧
      (∀ μ ∈ DLRMeasures exh Φ hq hp,
        FKLimit.StochasticallyDominates ⟨Measure.dirac (fun _ : E => true),
          Measure.dirac.isProbabilityMeasure⟩ μ) ∧
      (∀ μ ∈ DLRMeasures exh Φ hq hp, ∀ ν ∈ DLRMeasures exh Φ hq hp, μ = ν) := by
  refine ⟨isFreeAtClosedBoundary_empty_of_const exh Φ hconst,
    Filter.Eventually.of_forall fun η => frequentlyBoundaryClosed_empty η, ?_, ?_⟩
  · intro μ _
    exact stochasticallyDominates_dirac_allTrue μ
  · exact forall_eq_of_dominated_frequently_boundaryClosed exh Φ hq hp
      (fun _ => (∅ : Set E)) (isFreeAtClosedBoundary_empty_of_const exh Φ hconst)
      ⟨Measure.dirac (fun _ : E => true), Measure.dirac.isProbabilityMeasure⟩
      (Filter.Eventually.of_forall fun η => frequentlyBoundaryClosed_empty η)
      (fun μ _ => stochasticallyDominates_dirac_allTrue μ)

end NonVacuity

end FK.InfiniteVolume

/-! ## Axiom audit -/

#print axioms FK.InfiniteVolume.measurableSet_boundaryClosed
#print axioms FK.InfiniteVolume.measurableSet_frequentlyBoundaryClosed
#print axioms FK.InfiniteVolume.isLowerSet_frequentlyBoundaryClosed
#print axioms FK.InfiniteVolume.ae_frequentlyBoundaryClosed_of_stochasticallyDominates
#print axioms FK.InfiniteVolume.finiteBox_conditionalLaw_real_eq_of_partition_eq
#print axioms FK.InfiniteVolume.conditionalLaw_real_eq_of_boundaryClosed
#print axioms FK.InfiniteVolume.tendsto_ae_exteriorConditionalLaw_of_dlr
#print axioms FK.InfiniteVolume.exists_strictMono_of_frequently
#print axioms FK.InfiniteVolume.eq_of_orderedTriple_frequently_boundaryClosed
#print axioms FK.InfiniteVolume.forall_eq_of_dominated_frequently_boundaryClosed
#print axioms FK.InfiniteVolume.forall_eq_of_dominated_fullMeasure_boundaryClosed
#print axioms FK.InfiniteVolume.forall_eq_gibbsMeasures_of_dominated_frequently_boundaryClosed
#print axioms FK.InfiniteVolume.subsingleton_dlrMeasures_of_dominated_frequently_boundaryClosed
#print axioms FK.InfiniteVolume.frequentlyBoundaryClosed_empty
#print axioms FK.InfiniteVolume.isFreeAtClosedBoundary_empty_of_const
#print axioms FK.InfiniteVolume.stochasticallyDominates_dirac_allTrue
#print axioms FK.InfiniteVolume.exists_satisfying_uniqueness_hypotheses
