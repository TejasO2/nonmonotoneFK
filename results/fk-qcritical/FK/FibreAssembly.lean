import FK.InfiniteVolume
import FK.OnePointDetermination

/-!
# Finite-box fibre assembly from one-edge conditional probabilities

This file proves the measure-theoretic residual of
`docs/ONE-POINT-DETERMINATION.md` (step 2, "fibre assembly"): if the global
one-edge conditional probability of every edge of a finite box agrees with the
box specification's equation-(2) open rate, then the law satisfies the actual
Dixon--Vere-Jones identity `B.IsDLR`.

The finite combinatorial content (a positive specification is determined by its
singleton part) is `Glauber.FinProb.eq_fkPMF_of_openRate_odds`.  The new content
here is the disintegration of `Measure.map B.splitEquiv μ` along the box split,
the identification of the exterior conditional fibre laws with the finite FK
specification, and the countable null-set bookkeeping over the finitely many
box edges and their off-edge fibres.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

noncomputable section

/-- Throughout this file every decidable equality is classical, matching the
convention of the finite random-cluster developments.  This makes the
`configSplit` equivalences used on both sides of the fibre-assembly argument
syntactically identical. -/
local instance (priority := 10000) classicalDecEqInstance (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace FKF

open FK FK.Finite FK.InfiniteVolume

attribute [local instance] Classical.decEq

/-! ## The finite core: a fibre whose one-edge odds are equation (2) is the FK law -/

section FiniteCore

variable {G : FK.Finite.LabelledMultigraph} {q p : NNReal}

/-- **Finite core.**  A nonnegative mass function on the configuration space of
a finite labelled multigraph which is normalised and whose one-edge odds are the
equation-(2) odds of the random-cluster specification is the random-cluster
mass.  The hypothesis is stated in the "fibre" form
`m(off, true) = r · (m(off, true) + m(off, false))`, which is what the
disintegration argument produces for an exterior conditional fibre law. -/
theorem eq_fkPMF_of_fibre_odds (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) {m : (G.Edge → Bool) → ℝ≥0∞}
    (hne : ∀ ω, m ω ≠ ∞) (hsum : ∑ ω, m ω = 1)
    (hodds : ∀ (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e),
      m ((Glauber.configSplit Bool e).symm (off, true)) =
        ENNReal.ofReal (Glauber.FKBridge.openRate G (q := q) (p := p) ξ e off) *
          (m ((Glauber.configSplit Bool e).symm (off, true)) +
            m ((Glauber.configSplit Bool e).symm (off, false)))) :
    ∀ ω, m ω = G.fkPMF hq hp₁.le ξ ω := by
  classical
  have hsumR : ∑ ω, (m ω).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => hne a), hsum]
    simp
  let μ : OpenPath.FinProb (G.Edge → Bool) :=
    { mass := fun ω => (m ω).toReal
      mass_nonneg := fun ω => ENNReal.toReal_nonneg
      sum_mass := hsumR }
  have hμ : ∀ ω, μ.mass ω = (m ω).toReal := fun ω => rfl
  have hreal : ∀ (e : G.Edge) (off : Glauber.OffConfig Bool G.Edge e),
      μ.mass ((Glauber.configSplit Bool e).symm (off, true)) *
          (1 - Glauber.FKBridge.openRate G (q := q) (p := p) ξ e off)
        = μ.mass ((Glauber.configSplit Bool e).symm (off, false)) *
          Glauber.FKBridge.openRate G (q := q) (p := p) ξ e off := by
    intro e off
    set r := Glauber.FKBridge.openRate G (q := q) (p := p) ξ e off with hr
    set A := m ((Glauber.configSplit Bool e).symm (off, true)) with hA
    set B := m ((Glauber.configSplit Bool e).symm (off, false)) with hB
    have hAne : A ≠ ∞ := hne _
    have hBne : B ≠ ∞ := hne _
    have hEq : A = ENNReal.ofReal r * (A + B) := hodds e off
    have hr0 : 0 ≤ r := hr ▸ (Glauber.FKBridge.openRate_mem_Icc G hq hp₁.le ξ e off).1
    have hAB : A.toReal = r * (A.toReal + B.toReal) := by
      have := congrArg ENNReal.toReal hEq
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add hAne hBne, ENNReal.toReal_ofReal hr0] at this
    have hgoal : A.toReal * (1 - r) = B.toReal * r := by nlinarith
    show μ.mass ((Glauber.configSplit Bool e).symm (off, true)) * (1 - r) =
      μ.mass ((Glauber.configSplit Bool e).symm (off, false)) * r
    rw [hμ, hμ, ← hA, ← hB]
    exact hgoal
  have heq : μ = Glauber.ofPMF (G.fkPMF hq hp₁.le ξ) :=
    Glauber.FinProb.eq_fkPMF_of_openRate_odds hq hp₀ hp₁ ξ hreal
  intro ω
  have h2 : (m ω).toReal = (G.fkPMF hq hp₁.le ξ ω).toReal := by
    rw [← hμ ω, heq, Glauber.ofPMF_mass]
  calc m ω = ENNReal.ofReal ((m ω).toReal) := (ENNReal.ofReal_toReal (hne ω)).symm
    _ = ENNReal.ofReal ((G.fkPMF hq hp₁.le ξ ω).toReal) := by rw [h2]
    _ = G.fkPMF hq hp₁.le ξ ω := ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

end FiniteCore

end FKF

namespace FKF

/-! ## Measurability on finite Boolean product spaces

Every subset of a finite type with measurable singletons is measurable; hence
every function whose domain is such a type is measurable. -/

section FiniteMeasurable

variable {α β : Type*}

lemma measurableSet_of_fintype [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Set α) : MeasurableSet s :=
  (Set.finite_univ.subset (subset_univ s)).measurableSet

lemma measurable_of_fintype_domain [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (f : α → β) : Measurable f :=
  fun _ _ => measurableSet_of_fintype _

end FiniteMeasurable

end FKF

namespace FK.InfiniteVolume

namespace FiniteBox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

variable {E : Type*} (B : FiniteBox E)

/-- The part of a global configuration outside one fixed box edge: the exterior
configuration together with the box configuration off that edge. -/
def splitOff (e : B.edges) : Configuration E → B.Exterior × OffConfig Bool B.edges e :=
  fun ω => ((B.splitEquiv ω).1, (configSplit Bool e (B.splitEquiv ω).2).1)

/-- The bit at one fixed box edge of a global configuration. -/
def splitBit (e : B.edges) : Configuration E → Bool :=
  fun ω => (configSplit Bool e (B.splitEquiv ω).2).2

@[simp] lemma splitOff_apply (e : B.edges) (ω : Configuration E) :
    B.splitOff e ω = ((B.splitEquiv ω).1, (configSplit Bool e (B.splitEquiv ω).2).1) := rfl

@[simp] lemma splitBit_apply (e : B.edges) (ω : Configuration E) :
    B.splitBit e ω = (configSplit Bool e (B.splitEquiv ω).2).2 := rfl

lemma measurable_splitOff (e : B.edges) : Measurable (B.splitOff e) := by
  have hg : Measurable (fun z : B.Exterior × B.Interior =>
      (z.1, (configSplit Bool e z.2).1)) :=
    measurable_fst.prodMk ((FKF.measurable_of_fintype_domain
      (fun ξ : B.Interior => (configSplit Bool e ξ).1)).comp measurable_snd)
  exact hg.comp B.splitEquiv.measurable

lemma measurable_splitBit (e : B.edges) : Measurable (B.splitBit e) := by
  have hg : Measurable (fun z : B.Exterior × B.Interior => (configSplit Bool e z.2).2) :=
    (FKF.measurable_of_fintype_domain
      (fun ξ : B.Interior => (configSplit Bool e ξ).2)).comp measurable_snd
  exact hg.comp B.splitEquiv.measurable

/-- The two interior configurations with off-edge value `o` and bit `b`. -/
def fibreConfig (e : B.edges) (o : OffConfig Bool B.edges e) (b : Bool) : B.Interior :=
  (configSplit Bool e).symm (o, b)

@[simp] lemma configSplit_fibreConfig (e : B.edges) (o : OffConfig Bool B.edges e) (b : Bool) :
    configSplit Bool e (B.fibreConfig e o b) = (o, b) := by
  simp [fibreConfig]

lemma fibreConfig_injective (e : B.edges) (o : OffConfig Bool B.edges e) :
    Function.Injective (B.fibreConfig e o) := by
  intro b b' h
  have h2 := congrArg (configSplit Bool e) h
  simpa using h2

lemma fibreConfig_true_ne_false (e : B.edges) (o : OffConfig Bool B.edges e) :
    B.fibreConfig e o true ≠ B.fibreConfig e o false := by
  intro h
  have h2 : true = false := B.fibreConfig_injective e o h
  exact Bool.noConfusion h2

/-- The interior configurations whose off-edge part equals a fixed value are
exactly the two configurations with that off-edge part. -/
lemma off_fibre_eq (e : B.edges) (o : OffConfig Bool B.edges e) :
    {ξ : B.Interior | (configSplit Bool e ξ).1 = o}
      = {B.fibreConfig e o true, B.fibreConfig e o false} := by
  ext ξ
  simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, fibreConfig]
  constructor
  · intro h
    have h2 : configSplit Bool e ξ = (o, (configSplit Bool e ξ).2) := Prod.ext h rfl
    have h3 : ξ = (configSplit Bool e).symm (o, (configSplit Bool e ξ).2) := by
      conv_lhs => rw [← Equiv.symm_apply_apply (configSplit Bool e) ξ, h2]
    cases hb : (configSplit Bool e ξ).2
    · exact Or.inr (by rw [h3, hb])
    · exact Or.inl (by rw [h3, hb])
  · rintro (h | h)
    · rw [h]; simp
    · rw [h]; simp

/-- Measure of an off-edge fibre as the sum of its two atoms. -/
lemma measure_off_fibre (κ : Measure B.Interior) (e : B.edges)
    (o : OffConfig Bool B.edges e) :
    κ {ξ : B.Interior | (configSplit Bool e ξ).1 = o} =
      κ {B.fibreConfig e o true} + κ {B.fibreConfig e o false} := by
  have hset2 : ({(B.fibreConfig e o true), B.fibreConfig e o false} : Set B.Interior)
      = {B.fibreConfig e o true} ∪ {B.fibreConfig e o false} := by
    ext x; simp [or_comm]
  rw [B.off_fibre_eq e o, hset2,
    measure_union (Set.disjoint_singleton_left.mpr (by
      simp [B.fibreConfig_true_ne_false e o])) (measurableSet_singleton _)]

end FiniteBox

end FK.InfiniteVolume

namespace FK.InfiniteVolume

namespace FiniteBox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

variable {E : Type*} (B : FiniteBox E)

/-! ## The joint law of the exterior configuration and the box configuration -/

/-- The joint law of the exterior configuration and the box configuration. -/
def boxMeasure (μ : ProbabilityMeasure (Configuration E)) : Measure (B.Exterior × B.Interior) :=
  Measure.map B.splitEquiv (μ : Measure (Configuration E))

instance boxMeasure_isProbabilityMeasure (μ : ProbabilityMeasure (Configuration E)) :
    IsProbabilityMeasure (B.boxMeasure μ) :=
  ⟨by rw [boxMeasure, Measure.map_apply B.splitEquiv.measurable MeasurableSet.univ,
    preimage_univ, measure_univ]⟩

/-- The exterior conditional law of the box interior. -/
def boxKernel (μ : ProbabilityMeasure (Configuration E)) : Kernel B.Exterior B.Interior :=
  (B.boxMeasure μ).condKernel

instance boxKernel_isMarkov (μ : ProbabilityMeasure (Configuration E)) :
    IsMarkovKernel (B.boxKernel μ) := by
  rw [boxKernel]; infer_instance

lemma boxMeasure_fst (μ : ProbabilityMeasure (Configuration E)) :
    (B.boxMeasure μ).fst = (B.exteriorMeasure μ : Measure B.Exterior) := by
  rw [boxMeasure, Measure.fst, Measure.map_map measurable_fst B.splitEquiv.measurable]
  rfl

/-- The interior configurations with prescribed off-edge part and bit. -/
lemma eq_fibreConfig_iff (e : B.edges) (o : OffConfig Bool B.edges e) (ξ : B.Interior) (b : Bool) :
    ξ = B.fibreConfig e o b ↔ ((configSplit Bool e ξ).1 = o ∧ (configSplit Bool e ξ).2 = b) := by
  constructor
  · intro h; rw [h, configSplit_fibreConfig]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have h3 : configSplit Bool e ξ = (o, b) := Prod.ext h1 h2
    show ξ = (configSplit Bool e).symm (o, b)
    rw [← h3, Equiv.symm_apply_apply]

lemma off_bit_eq_singleton (e : B.edges) (o : OffConfig Bool B.edges e) (b : Bool) :
    {ξ : B.Interior | (configSplit Bool e ξ).1 = o ∧ (configSplit Bool e ξ).2 = b}
      = {B.fibreConfig e o b} := by
  ext ξ
  rw [Set.mem_ofPred_eq, mem_singleton_iff, B.eq_fibreConfig_iff]

end FiniteBox

end FK.InfiniteVolume

namespace FK.InfiniteVolume

namespace FiniteBox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} (B : FiniteBox E)
variable {q p : NNReal} (hq : 0 < q) (hp₁ : p < 1)
variable (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)

include hα

/-- The equation-(2) open rate is a measurable function of the exterior
configuration, because the boundary-partition space is discrete. -/
lemma measurable_openRate (e : B.edges) (o : OffConfig Bool B.edges e) :
    Measurable (fun η : B.Exterior => FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) := by
  have hg : Measurable (fun ξ : B.BoundaryPartition =>
      FKBridge.openRate B.graph (q := q) (p := p) ξ e o) := fun s _ => trivial
  exact hg.comp hα

include hq hp₁

/-- **One-box odds identity.**  If the global one-edge conditional probability
of a box edge agrees with the box specification's equation-(2) open rate, then
the exterior conditional fibre law satisfies the off-edge odds identity
`lambda({true}) = r (lambda({true}) + lambda({false}))`, tested against every
measurable exterior set. -/
lemma key_identity (e : B.edges) (o : OffConfig Bool B.edges e)
    (μ : ProbabilityMeasure (Configuration E))
    (hpoint : ∀ (g : B.Exterior × OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
          ∂(μ : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
              (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
          ∂(μ : Measure (Configuration E)))
    {S : Set B.Exterior} (hS : MeasurableSet S) :
    ∫⁻ η in S, B.boxKernel μ η {B.fibreConfig e o true} ∂(B.boxMeasure μ).fst
      = ∫⁻ η in S, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (B.boxKernel μ η {B.fibreConfig e o true} +
            B.boxKernel μ η {B.fibreConfig e o false}) ∂(B.boxMeasure μ).fst := by
  classical
  -- the off-edge test function localising the exterior set and the off-value
  set g : B.Exterior × OffConfig Bool B.edges e → ℝ≥0∞ :=
    fun z => if z.1 ∈ S ∧ z.2 = o then 1 else 0 with hg
  have hgmeas : Measurable g := by
    have hset : MeasurableSet {z : B.Exterior × OffConfig Bool B.edges e | z.1 ∈ S ∧ z.2 = o} :=
      (hS.preimage measurable_fst).inter ((measurableSet_singleton o).preimage measurable_snd)
    exact Measurable.ite hset measurable_const measurable_const
  have hoffmeas : Measurable (fun z : B.Exterior × B.Interior =>
      (configSplit Bool e z.2).1) :=
    (FKF.measurable_of_fintype_domain
      (fun ξ : B.Interior => (configSplit Bool e ξ).1)).comp measurable_snd
  have hbitmeas : Measurable (fun z : B.Exterior × B.Interior =>
      (configSplit Bool e z.2).2) :=
    (FKF.measurable_of_fintype_domain
      (fun ξ : B.Interior => (configSplit Bool e ξ).2)).comp measurable_snd
  have hgcomp : Measurable (fun z : B.Exterior × B.Interior =>
      g (z.1, (configSplit Bool e z.2).1)) :=
    hgmeas.comp (measurable_fst.prodMk hoffmeas)
  have hratemeas : Measurable (fun z : B.Exterior × B.Interior =>
      ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α z.1) e o)) :=
    ENNReal.measurable_ofReal.comp ((measurable_openRate B α hα e o).comp measurable_fst)
  -- the two product integrands
  set H1 : B.Exterior × B.Interior → ℝ≥0∞ :=
    fun z => if (configSplit Bool e z.2).2 = true then g (z.1, (configSplit Bool e z.2).1) else 0
    with hH1
  set H2 : B.Exterior × B.Interior → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α z.1) e o) *
      g (z.1, (configSplit Bool e z.2).1) with hH2
  have hH1meas : Measurable H1 :=
    Measurable.ite (hbitmeas (measurableSet_singleton true)) hgcomp measurable_const
  have hH2meas : Measurable H2 := hratemeas.mul hgcomp
  -- the hypothesis, transported to the two product integrands
  have hleft : ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
        ∂(μ : Measure (Configuration E)) = ∫⁻ z, H1 z ∂(B.boxMeasure μ) := by
    rw [boxMeasure, lintegral_map hH1meas B.splitEquiv.measurable]
    rfl
  have hright : ∫⁻ ω, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
          (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) = ∫⁻ z, H2 z ∂(B.boxMeasure μ) := by
    rw [boxMeasure, lintegral_map hH2meas B.splitEquiv.measurable]
    refine lintegral_congr fun ω => ?_
    show ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
        (α ((B.splitEquiv ω).1)) e ((configSplit Bool e (B.splitEquiv ω).2).1)) *
        g ((B.splitEquiv ω).1, (configSplit Bool e (B.splitEquiv ω).2).1) = H2 (B.splitEquiv ω)
    simp only [hH2]
    by_cases h : (configSplit Bool e (B.splitEquiv ω).2).1 = o
    · rw [h]
    · simp only [hg, h, and_false, if_false, mul_zero]
  -- evaluation of the inner integrals
  have e1 : ∀ η : B.Exterior, ∫⁻ ξ, H1 (η, ξ) ∂(B.boxKernel μ η)
      = if η ∈ S then B.boxKernel μ η {B.fibreConfig e o true} else 0 := by
    intro η
    have hfun : (fun ξ : B.Interior => H1 (η, ξ)) =
        ({B.fibreConfig e o true} : Set B.Interior).indicator
          (fun _ => (if η ∈ S then (1 : ℝ≥0∞) else 0)) := by
      funext ξ
      have hmem : ξ ∈ ({B.fibreConfig e o true} : Set B.Interior) ↔
          ((configSplit Bool e ξ).1 = o ∧ (configSplit Bool e ξ).2 = true) := by
        rw [mem_singleton_iff, B.eq_fibreConfig_iff]
      simp only [hH1, hg]
      by_cases hξ : ξ ∈ ({B.fibreConfig e o true} : Set B.Interior)
      · obtain ⟨h1, h2⟩ := hmem.mp hξ
        rw [Set.indicator_of_mem hξ, if_pos h2]
        by_cases hη : η ∈ S
        · rw [if_pos ⟨hη, h1⟩, if_pos hη]
        · rw [if_neg (fun h => hη h.1), if_neg hη]
      · rw [Set.indicator_of_notMem hξ]
        by_cases hb : (configSplit Bool e ξ).2 = true
        · have h2 : ¬((configSplit Bool e ξ).1 = o) := fun hh => hξ (hmem.mpr ⟨hh, hb⟩)
          rw [if_pos hb]
          by_cases hη : η ∈ S
          · rw [if_neg (fun h => h2 h.2)]
          · rw [if_neg (fun h => hη h.1)]
        · rw [if_neg hb]
    rw [hfun, lintegral_indicator (measurableSet_singleton _), setLIntegral_const]
    by_cases hη : η ∈ S <;> simp [hη]
  have e2 : ∀ η : B.Exterior, ∫⁻ ξ, H2 (η, ξ) ∂(B.boxKernel μ η)
      = if η ∈ S then ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          B.boxKernel μ η {ξ : B.Interior | (configSplit Bool e ξ).1 = o} else 0 := by
    intro η
    have hfun : (fun ξ : B.Interior => H2 (η, ξ)) = fun ξ =>
        ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (({ξ : B.Interior | (configSplit Bool e ξ).1 = o} : Set B.Interior).indicator
            (fun _ => (if η ∈ S then (1 : ℝ≥0∞) else 0)) ξ) := by
      funext ξ
      simp only [hH2, hg]
      have hinner : (if η ∈ S ∧ (configSplit Bool e ξ).1 = o then (1 : ℝ≥0∞) else 0) =
          ({ξ : B.Interior | (configSplit Bool e ξ).1 = o} : Set B.Interior).indicator
            (fun _ => (if η ∈ S then (1 : ℝ≥0∞) else 0)) ξ := by
        by_cases hoff : (configSplit Bool e ξ).1 = o
        · rw [Set.indicator_of_mem (by simpa using hoff)]
          by_cases hη : η ∈ S
          · rw [if_pos ⟨hη, hoff⟩, if_pos hη]
          · rw [if_neg (fun h => hη h.1), if_neg hη]
        · rw [Set.indicator_of_notMem (by simpa using hoff)]
          by_cases hη : η ∈ S
          · rw [if_neg (fun h => hoff h.2)]
          · rw [if_neg (fun h => hη h.1)]
      rw [hinner]
    rw [hfun, lintegral_const_mul _ (Measurable.indicator measurable_const
      (FKF.measurableSet_of_fintype _)), lintegral_indicator (FKF.measurableSet_of_fintype _),
      setLIntegral_const]
    by_cases hη : η ∈ S <;> simp [hη]
  -- assemble both sides
  calc ∫⁻ η in S, B.boxKernel μ η {B.fibreConfig e o true} ∂(B.boxMeasure μ).fst
      = ∫⁻ η, (if η ∈ S then B.boxKernel μ η {B.fibreConfig e o true} else 0)
          ∂(B.boxMeasure μ).fst := by
        rw [← lintegral_indicator hS]
        exact lintegral_congr fun η => by simp [Set.indicator_apply]
    _ = ∫⁻ η, ∫⁻ ξ, H1 (η, ξ) ∂(B.boxKernel μ η) ∂(B.boxMeasure μ).fst :=
        lintegral_congr fun η => (e1 η).symm
    _ = ∫⁻ z, H1 z ∂(B.boxMeasure μ) := Measure.lintegral_condKernel hH1meas
    _ = ∫⁻ z, H2 z ∂(B.boxMeasure μ) := by
        rw [← hleft, ← hright]
        exact hpoint g hgmeas
    _ = ∫⁻ η, ∫⁻ ξ, H2 (η, ξ) ∂(B.boxKernel μ η) ∂(B.boxMeasure μ).fst :=
        (Measure.lintegral_condKernel hH2meas).symm
    _ = ∫⁻ η, (if η ∈ S then ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
            (α η) e o) * B.boxKernel μ η {ξ : B.Interior | (configSplit Bool e ξ).1 = o}
          else 0) ∂(B.boxMeasure μ).fst :=
        lintegral_congr fun η => e2 η
    _ = ∫⁻ η in S, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          B.boxKernel μ η {ξ : B.Interior | (configSplit Bool e ξ).1 = o}
          ∂(B.boxMeasure μ).fst := by
        rw [← lintegral_indicator hS]
        exact lintegral_congr fun η => by by_cases h : η ∈ S <;> simp [h, Set.indicator_apply]
    _ = ∫⁻ η in S, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (B.boxKernel μ η {B.fibreConfig e o true} +
            B.boxKernel μ η {B.fibreConfig e o false}) ∂(B.boxMeasure μ).fst := by
        refine setLIntegral_congr_fun hS fun η _ => ?_
        rw [B.measure_off_fibre]

end FiniteBox

end FK.InfiniteVolume

namespace FK.InfiniteVolume

namespace FiniteBox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

local instance boundaryPartitionMeasurableSpace' (V : Type*) : MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} (B : FiniteBox E)

/-- On a finite type with measurable singletons two measures agreeing on all
singletons coincide. -/
lemma measure_eq_of_singleton_eq {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ₁ μ₂ : Measure α} (h : ∀ a, μ₁ {a} = μ₂ {a}) :
    μ₁ = μ₂ := by
  classical
  ext s _
  rw [← Set.coe_toFinset s,
    ← sum_measure_singleton (μ := μ₁) (s := s.toFinset),
    ← sum_measure_singleton (μ := μ₂) (s := s.toFinset)]
  exact Finset.sum_congr rfl fun a _ => h a

/-- The fibre law mass of a singleton is finite (the kernel is Markov). -/
lemma boxKernel_singleton_ne_top (μ : ProbabilityMeasure (Configuration E)) (η : B.Exterior)
    (ξ : B.Interior) : B.boxKernel μ η {ξ} ≠ ∞ := by
  have hle : B.boxKernel μ η {ξ} ≤ 1 := by
    have h1 : B.boxKernel μ η {ξ} ≤ B.boxKernel μ η Set.univ :=
      measure_mono (subset_univ _)
    rwa [measure_univ] at h1
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

/-- The fibre law masses sum to one. -/
lemma boxKernel_sum_singleton (μ : ProbabilityMeasure (Configuration E)) (η : B.Exterior) :
    ∑ ξ, B.boxKernel μ η {ξ} = 1 := by
  classical
  have h : ∑ ξ, B.boxKernel μ η {ξ} = B.boxKernel μ η (Set.univ : Set B.Interior) := by
    simpa using sum_measure_singleton (μ := B.boxKernel μ η)
      (s := (Finset.univ : Finset B.Interior))
  rw [h, measure_univ]

end FiniteBox

end FK.InfiniteVolume

namespace FK.InfiniteVolume

namespace FiniteBox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

local instance boundaryPartitionMeasurableSpace'' (V : Type*) : MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} (B : FiniteBox E)
variable {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
variable (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
variable (μ : ProbabilityMeasure (Configuration E))

include hα hq hp₀ hp₁

/-- Almost-everywhere off-edge odds for the exterior conditional fibre law. -/
lemma ae_kernel_odds (e : B.edges) (o : OffConfig Bool B.edges e)
    (hpoint : ∀ (g : B.Exterior × OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
          ∂(μ : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
              (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
          ∂(μ : Measure (Configuration E))) :
    ∀ᵐ η ∂(B.boxMeasure μ).fst,
      B.boxKernel μ η {B.fibreConfig e o true} =
        ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (B.boxKernel μ η {B.fibreConfig e o true} +
            B.boxKernel μ η {B.fibreConfig e o false}) := by
  have hf : Measurable (fun η : B.Exterior => B.boxKernel μ η {B.fibreConfig e o true}) :=
    Kernel.measurable_coe _ (measurableSet_singleton _)
  have hg : Measurable (fun η : B.Exterior =>
      ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
        (B.boxKernel μ η {B.fibreConfig e o true} +
          B.boxKernel μ η {B.fibreConfig e o false})) :=
    (ENNReal.measurable_ofReal.comp (measurable_openRate B α hα e o)).mul
      ((Kernel.measurable_coe _ (measurableSet_singleton _)).add
        (Kernel.measurable_coe _ (measurableSet_singleton _)))
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hf hg (fun S hS _ => ?_)
  exact key_identity B hq hp₁ α hα e o μ hpoint hS

/-- **Fibre assembly.**  If the global one-edge conditional probability of every
edge of a finite box agrees with the box specification's equation-(2) open rate,
then the law satisfies the actual DLR/comp-product identity for that box. -/
lemma isDLR_of_ae_fibre_odds
    (hae : ∀ᵐ η ∂(B.boxMeasure μ).fst, ∀ (e : B.edges) (o : OffConfig Bool B.edges e),
      B.boxKernel μ η {B.fibreConfig e o true} =
        ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (B.boxKernel μ η {B.fibreConfig e o true} +
            B.boxKernel μ η {B.fibreConfig e o false})) :
    B.IsDLR hq hp₁.le α hα μ := by
  classical
  have hgood : ∀ᵐ η ∂(B.boxMeasure μ).fst, B.boxKernel μ η = B.fkKernel hq hp₁.le α hα η := by
    filter_upwards [hae] with η hodd
    letI : Fintype (B.graph.Edge → Bool) := B.graph.instFintypeConfiguration
    have hsum : ∑ ω, ((B.boxKernel μ) η) {ω} = 1 := by
      have h := sum_measure_singleton (μ := (B.boxKernel μ η))
        (s := (Finset.univ : Finset (B.graph.Edge → Bool)))
      rw [Finset.coe_univ, measure_univ] at h
      exact h
    have hfib := FKF.eq_fkPMF_of_fibre_odds (G := B.graph) (q := q) (p := p) hq hp₀ hp₁ (α η)
      (fun ω => boxKernel_singleton_ne_top B μ η ω) hsum
      (fun e off => by
        simpa [fibreConfig] using hodd e off)
    refine measure_eq_of_singleton_eq fun ξ => ?_
    rw [hfib ξ, fkKernel_apply, FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton]
  have h1 : B.boxMeasure μ = (B.boxMeasure μ).fst ⊗ₘ (B.boxMeasure μ).condKernel :=
    (Measure.disintegrate (B.boxMeasure μ) (B.boxMeasure μ).condKernel).symm
  have h2 : (B.boxMeasure μ).fst ⊗ₘ (B.boxMeasure μ).condKernel
      = (B.boxMeasure μ).fst ⊗ₘ B.fkKernel hq hp₁.le α hα :=
    Measure.compProd_congr hgood
  show B.boxMeasure μ = (B.exteriorMeasure μ : Measure B.Exterior) ⊗ₘ B.fkKernel hq hp₁.le α hα
  rw [← B.boxMeasure_fst μ, ← h2]
  exact h1

/-- **Fibre assembly.**  If the global one-edge conditional probability of every
edge of a finite box agrees with the box specification's equation-(2) open rate,
then the law satisfies the actual DLR/comp-product identity for that box. -/
theorem isDLR_of_onePointConditionals
    (hpoint : ∀ (e : B.edges) (g : B.Exterior × OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
      ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
          ∂(μ : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
              (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
          ∂(μ : Measure (Configuration E))) :
    B.IsDLR hq hp₁.le α hα μ := by
  classical
  have hall : ∀ (s : Finset ((e : B.edges) × OffConfig Bool B.edges e)),
      ∀ᵐ η ∂(B.boxMeasure μ).fst, ∀ pt ∈ s,
        B.boxKernel μ η {B.fibreConfig pt.1 pt.2 true} =
          ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) pt.1 pt.2) *
            (B.boxKernel μ η {B.fibreConfig pt.1 pt.2 true} +
              B.boxKernel μ η {B.fibreConfig pt.1 pt.2 false}) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        filter_upwards [ih, ae_kernel_odds (B := B) (q := q) (p := p) (hq := hq) (hp₀ := hp₀)
          (hp₁ := hp₁) (α := α) (hα := hα) (μ := μ) a.1 a.2 (hpoint a.1)] with η h1 h2
        intro pt hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact h2
        · exact h1 pt hp
  refine isDLR_of_ae_fibre_odds B hq hp₀ hp₁ α hα μ ?_
  filter_upwards [hall Finset.univ] with η hodd
  intro e o
  exact hodd ⟨e, o⟩ (Finset.mem_univ _)

/-- The one-point part tested against off-edge indicators is exactly the fibre
odds identity of the exterior conditional law. -/
theorem isDLR_of_fibreOdds
    (hfib : ∀ (e : B.edges) (o : OffConfig Bool B.edges e) {S : Set B.Exterior},
      MeasurableSet S →
      ∫⁻ η in S, B.boxKernel μ η {B.fibreConfig e o true} ∂(B.boxMeasure μ).fst
        = ∫⁻ η in S, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
            (B.boxKernel μ η {B.fibreConfig e o true} +
              B.boxKernel μ η {B.fibreConfig e o false}) ∂(B.boxMeasure μ).fst) :
    B.IsDLR hq hp₁.le α hα μ := by
  have hf : ∀ e o, Measurable (fun η : B.Exterior => B.boxKernel μ η {B.fibreConfig e o true}) :=
    fun e o => Kernel.measurable_coe _ (measurableSet_singleton _)
  have hg : ∀ e o, Measurable (fun η : B.Exterior =>
      ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
        (B.boxKernel μ η {B.fibreConfig e o true} +
          B.boxKernel μ η {B.fibreConfig e o false})) :=
    fun e o => (ENNReal.measurable_ofReal.comp (measurable_openRate B α hα e o)).mul
      ((Kernel.measurable_coe _ (measurableSet_singleton _)).add
        (Kernel.measurable_coe _ (measurableSet_singleton _)))
  have hall : ∀ (s : Finset ((e : B.edges) × OffConfig Bool B.edges e)),
      ∀ᵐ η ∂(B.boxMeasure μ).fst, ∀ pt ∈ s,
        B.boxKernel μ η {B.fibreConfig pt.1 pt.2 true} =
          ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) pt.1 pt.2) *
            (B.boxKernel μ η {B.fibreConfig pt.1 pt.2 true} +
              B.boxKernel μ η {B.fibreConfig pt.1 pt.2 false}) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        filter_upwards [ih, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
          (hf a.1 a.2) (hg a.1 a.2) (fun S hS _ => hfib a.1 a.2 hS)] with η h1 h2
        intro pt hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact h2
        · exact h1 pt hp
  refine isDLR_of_ae_fibre_odds B hq hp₀ hp₁ α hα μ ?_
  filter_upwards [hall Finset.univ] with η hodd
  intro e o
  exact hodd ⟨e, o⟩ (Finset.mem_univ _)

end FiniteBox

end FK.InfiniteVolume

namespace FKF

open MeasureTheory ProbabilityTheory Set Filter Glauber
open scoped ENNReal

/-- **The finite random-cluster law's own one-point odds.**  In the actual
finite FK law with an arbitrary boundary partition, the mass of the
configuration with a prescribed off-edge part and open bit `e` is the
equation-(2) open rate times the total mass of the two configurations with that
off-edge part.  This is the pointwise form of equation (2). -/
lemma fkMeasure_singleton_odds {G : FK.Finite.LabelledMultigraph} {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1) (ξ : G.BoundaryPartition) (e : G.Edge)
    (off : OffConfig Bool G.Edge e) :
    G.fkMeasure hq hp ξ {(configSplit Bool e).symm (off, true)} =
      ENNReal.ofReal (FKBridge.openRate G (q := q) (p := p) ξ e off) *
        (G.fkMeasure hq hp ξ {(configSplit Bool e).symm (off, true)} +
          G.fkMeasure hq hp ξ {(configSplit Bool e).symm (off, false)}) := by
  classical
  set μ := Glauber.ofPMF (G.fkPMF hq hp ξ) with hμ
  set A := μ.mass ((configSplit Bool e).symm (off, true)) with hA
  set B := μ.mass ((configSplit Bool e).symm (off, false)) with hB
  set r := FKBridge.openRate G (q := q) (p := p) ξ e off with hr
  have hc := Glauber.FKBridge.fk_hasEdgeConditional (G := G) hq hp ξ e
  unfold Glauber.HasEdgeConditional Glauber.HasConjConditional at hc
  have h1 : A = Glauber.outsideMassConj (configSplit Bool e) μ off *
      (FKBridge.edgeConditionals G hq hp ξ e off).mass true := hc off true
  have hout : Glauber.outsideMassConj (configSplit Bool e) μ off = A + B := by
    rw [Glauber.outsideMassConj, Fintype.sum_bool]
  have hrt : (FKBridge.edgeConditionals G hq hp ξ e off).mass true = r := by
    rw [hr]; exact FKBridge.boolLaw_true _ _
  have hAreal : A = (A + B) * r := by
    have h := h1
    rw [hout, hrt] at h
    exact h
  have hA0 : 0 ≤ A := μ.mass_nonneg _
  have hB0 : 0 ≤ B := μ.mass_nonneg _
  have hr0 : 0 ≤ r := by
    rw [hr]; exact (FKBridge.openRate_mem_Icc G hq hp ξ e off).1
  have hfk : ∀ x : G.Edge → Bool, G.fkMeasure hq hp ξ {x} = ENNReal.ofReal (μ.mass x) := by
    intro x
    rw [FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton, hμ, Glauber.ofPMF_mass,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  simp only [hfk]
  have hne : 0 ≤ r * (A + B) := by nlinarith
  rw [← hA, ← hB, ← ENNReal.ofReal_add hA0 hB0, ← ENNReal.ofReal_mul hr0,
    ENNReal.ofReal_eq_ofReal_iff hA0 hne, mul_comm]
  exact hAreal

end FKF

namespace FK.InfiniteVolume

namespace FiniteBox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

local instance boundaryPartitionMeasurableSpace''' (V : Type*) : MeasurableSpace (Setoid V) := ⊤

variable {E : Type*} (B : FiniteBox E)
variable {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
variable (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
variable (μ : ProbabilityMeasure (Configuration E))

include hα hp₀ hp₁

/-- The DLR identity identifies the exterior conditional fibre law with the
finite random-cluster specification almost everywhere. -/
lemma ae_fkKernel_eq_condKernel
    (h : B.IsDLR hq hp₁.le α hα μ) :
    ∀ᵐ η ∂(B.boxMeasure μ).fst,
      B.fkKernel hq hp₁.le α hα η = (B.boxMeasure μ).condKernel η := by
  haveI : IsFiniteMeasure (B.boxMeasure μ) := inferInstance
  refine ProbabilityTheory.eq_condKernel_of_measure_eq_compProd
    (B.fkKernel hq hp₁.le α hα) ?_
  show (B.boxMeasure μ) = (B.boxMeasure μ).fst ⊗ₘ B.fkKernel hq hp₁.le α hα
  rw [B.boxMeasure_fst μ]
  exact h

/-- **Converse.**  A DLR law satisfies the one-point fibre odds identity of the
box specification, hence the one-point part of equation (2) is not merely
sufficient but exactly the DLR condition for the box. -/
theorem fibreOdds_of_isDLR (h : B.IsDLR hq hp₁.le α hα μ)
    (e : B.edges) (o : OffConfig Bool B.edges e) {S : Set B.Exterior}
    (hS : MeasurableSet S) :
    ∫⁻ η in S, B.boxKernel μ η {B.fibreConfig e o true} ∂(B.boxMeasure μ).fst
      = ∫⁻ η in S, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (B.boxKernel μ η {B.fibreConfig e o true} +
            B.boxKernel μ η {B.fibreConfig e o false}) ∂(B.boxMeasure μ).fst := by
  classical
  have hpt : ∀ᵐ η ∂(B.boxMeasure μ).fst,
      B.boxKernel μ η {B.fibreConfig e o true} =
        ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
          (B.boxKernel μ η {B.fibreConfig e o true} +
            B.boxKernel μ η {B.fibreConfig e o false}) := by
    filter_upwards [ae_fkKernel_eq_condKernel (B := B) (q := q) (p := p) (hq := hq) (hp₀ := hp₀)
      (hp₁ := hp₁) (α := α) (hα := hα) (μ := μ) h] with η hη
    simp only [boxKernel]
    rw [← hη]
    simp only [fkKernel_apply]
    exact FKF.fkMeasure_singleton_odds (G := B.graph) hq hp₁.le (α η) e o
  rw [← lintegral_indicator hS, ← lintegral_indicator hS]
  refine lintegral_congr_ae ?_
  filter_upwards [hpt] with η hη
  by_cases hmem : η ∈ S
  · simp only [Set.indicator_of_mem hmem]
    exact hη
  · simp only [Set.indicator_of_notMem hmem]

/-- **Characterisation.**  For one finite box, the DLR identity holds exactly
when the box specification's one-point odds identity holds for the exterior
conditional law. -/
theorem isDLR_iff_fibreOdds :
    B.IsDLR hq hp₁.le α hα μ ↔
      ∀ (e : B.edges) (o : OffConfig Bool B.edges e) {S : Set B.Exterior},
        MeasurableSet S →
        ∫⁻ η in S, B.boxKernel μ η {B.fibreConfig e o true} ∂(B.boxMeasure μ).fst
          = ∫⁻ η in S, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p) (α η) e o) *
              (B.boxKernel μ η {B.fibreConfig e o true} +
                B.boxKernel μ η {B.fibreConfig e o false}) ∂(B.boxMeasure μ).fst :=
  ⟨fun h => fibreOdds_of_isDLR (B := B) (q := q) (p := p) (hq := hq) (hp₀ := hp₀) (hp₁ := hp₁)
      (α := α) (hα := hα) (μ := μ) h,
   fun h => isDLR_of_fibreOdds (B := B) (q := q) (p := p) (hq := hq) (hp₀ := hp₀) (hp₁ := hp₁)
      (α := α) (hα := hα) (μ := μ) h⟩

end FiniteBox

end FK.InfiniteVolume

namespace FK.InfiniteVolume

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

attribute [local instance] Classical.decEq

local instance boundaryPartitionMeasurableSpaceIV (V : Type*) : MeasurableSpace (Setoid V) := ⊤

namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- The equation-(2) one-point conditional hypothesis for one finite box and one
boundary assignment: the global conditional probability that a box edge is open,
given the whole off-edge configuration, is the box specification's open rate,
tested against every measurable function of the off-edge configuration. -/
def HasOnePointConditionals {q p : NNReal} (α : B.Exterior → B.BoundaryPartition)
    (μ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∀ (e : B.edges) (g : B.Exterior × OffConfig Bool B.edges e → ℝ≥0∞), Measurable g →
    ∫⁻ ω, (if B.splitBit e ω = true then g (B.splitOff e ω) else 0)
        ∂(μ : Measure (Configuration E))
      = ∫⁻ ω, ENNReal.ofReal (FKBridge.openRate B.graph (q := q) (p := p)
            (α ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E))

/-- The one-point conditionals of a box give its DLR identity. -/
theorem isDLR_of_hasOnePointConditionals {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p)
    (hp₁ : p < 1) (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (h : B.HasOnePointConditionals (q := q) (p := p) α μ) :
    B.IsDLR hq hp₁.le α hα μ :=
  isDLR_of_onePointConditionals B hq hp₀ hp₁ α hα μ h

end FiniteBox

end FK.InfiniteVolume

namespace FK.InfiniteVolume

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open Glauber

/-- **Countably many boxes.**  If every box of a genuine box exhaustion separately
has the equation-(2) one-point conditionals of its prescribed boundary
assignment, then the law belongs to the DLR class of that assignment.  No joint
null-set bookkeeping is needed: each `IsDLR` is a measure identity, so the boxes
are handled one at a time. -/
theorem mem_dlrMeasures_of_hasOnePointConditionals {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (μ : ProbabilityMeasure (Configuration E))
    (h : ∀ n, (exh.box n).HasOnePointConditionals (q := q) (p := p) (Φ.partition n) μ) :
    μ ∈ DLRMeasures exh Φ hq hp₁.le :=
  fun n => (exh.box n).isDLR_of_hasOnePointConditionals hq hp₀ hp₁
    (Φ.partition n) (Φ.measurable_partition n) μ (h n)
