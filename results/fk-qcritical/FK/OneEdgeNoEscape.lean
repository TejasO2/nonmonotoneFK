import FK.OneEdgeLimit

/-!
# No-mass-escape for the one-edge one-point limit passage

`FK/OneEdgeLimit.lean` reduces the one-point conditional identity of an
infinite-volume limit law to a single *scalar* mass identity

`∫ ρ dμ = μ {e open}`

for the limiting rate `ρ`.  The finite-stage identities together with monotone
continuous rates give one half; the other half is exactly the statement that no
mass escapes through increasingly distant boundary configurations.

This file

* records the two-valued shape of the random-cluster rate (`twoValuedRate`),
  its range, continuity and integral,
* proves the automatic half of the scalar identity in explicit-limit form,
* proves that the scalar identity is *equivalent* to the no-mass-escape
  inequality `limsup_k μ_k(C k) ≤ μ(C∞)` for the connection events `C k`, and
* conversely derives the convergence of the finite-stage connection masses
  from the scalar identity.

Everything is stated in the API of `FK.OneEdgeLimit`: the events live in
`Configuration E`, the box is an actual `FiniteBox E` and the open bit is
`B.splitBit e`.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace FK.InfiniteVolume

namespace OneEdgeNoEscape

attribute [local instance] Classical.propDecidable

variable {E : Type*} [Countable E]

/-! ## Part 1: the two-valued random-cluster rate -/

/-- The two-valued rate that takes the value `α` on the set `C` and `β` off it.
For the random-cluster specification this is the rate `p` on the connection
event and `p/(p + q(1-p))` off it (or the reverse, according to the value of
`q`); `Glauber.FKBridge.openRate` is definitionally of this shape. -/
def twoValuedRate {X : Type*} (α β : ℝ) (C : Set X) : X → ℝ :=
  fun ω => if ω ∈ C then α else β

omit [Countable E] in
lemma twoValuedRate_apply (α β : ℝ) (C : Set (Configuration E)) (ω : Configuration E) :
    twoValuedRate α β C ω = if ω ∈ C then α else β := rfl

omit [Countable E] in
lemma twoValuedRate_eq (α β : ℝ) (C : Set (Configuration E)) (ω : Configuration E) :
    twoValuedRate α β C ω = β - (β - α) * (if ω ∈ C then (1 : ℝ) else 0) := by
  by_cases h : ω ∈ C <;> simp [twoValuedRate, h]

omit [Countable E] in
lemma twoValuedRate_mem_Icc {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    (C : Set (Configuration E)) (ω : Configuration E) :
    twoValuedRate α β C ω ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : ω ∈ C
  · simp only [twoValuedRate, h, ite_true]
    exact ⟨hα, hαβ.trans hβ⟩
  · simp only [twoValuedRate, h, ite_false]
    exact ⟨hα.trans hαβ, hβ⟩

omit [Countable E] in
/-- A two-valued rate attached to a clopen set is continuous. -/
lemma continuous_twoValuedRate (α β : ℝ) {C : Set (Configuration E)} (hC : IsClopen C) :
    Continuous (twoValuedRate α β C) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hcongr : twoValuedRate α β C =ᶠ[𝓝 x] (fun _ => twoValuedRate α β C x) := by
    by_cases hx : x ∈ C
    · filter_upwards [hC.isOpen.mem_nhds hx] with y hy
      simp [twoValuedRate, hy, hx]
    · filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ C := by simpa using hy
      simp [twoValuedRate, hy', hx]
  exact Tendsto.congr' hcongr.symm tendsto_const_nhds

omit [Countable E] in
/-- The integral of a two-valued rate against a probability measure. -/
lemma integral_twoValuedRate (ν : ProbabilityMeasure (Configuration E))
    {C : Set (Configuration E)} (hC : MeasurableSet C) (α β : ℝ) :
    ∫ ω, twoValuedRate α β C ω ∂(ν : Measure (Configuration E))
      = β - (β - α) * ((ν : Measure (Configuration E)) C).toReal := by
  have hind : ∫ ω, C.indicator (fun _ => (1 : ℝ)) ω ∂(ν : Measure (Configuration E))
      = ((ν : Measure (Configuration E)) C).toReal := by
    rw [MeasureTheory.integral_indicator hC, MeasureTheory.setIntegral_const,
      Measure.real_def]
    simp
  have hfun : (fun ω => twoValuedRate α β C ω)
      = fun ω => β - (β - α) * C.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [twoValuedRate_eq]
    simp [Set.indicator_apply]
  rw [hfun]
  have hβ : ∫ ω, (β : ℝ) ∂(ν : Measure (Configuration E)) = β := by simp
  have hg : ∫ ω, (β - α) * C.indicator (fun _ => (1 : ℝ)) ω ∂(ν : Measure (Configuration E))
      = (β - α) * ((ν : Measure (Configuration E)) C).toReal := by
    rw [MeasureTheory.integral_const_mul, hind]
  rw [MeasureTheory.integral_sub (integrable_const β)
    ((integrable_const (1 : ℝ)).indicator hC |>.const_mul (β - α)), hβ, hg]

/-! ## Part 2: limsup/liminf of a convergent real sequence -/

lemma limsup_eq_of_tendsto {u : ℕ → ℝ} {L : ℝ} (h : Tendsto u atTop (𝓝 L)) :
    Filter.limsup u atTop = L := h.limsup_eq

lemma liminf_eq_of_tendsto {u : ℕ → ℝ} {L : ℝ} (h : Tendsto u atTop (𝓝 L)) :
    Filter.liminf u atTop = L := h.liminf_eq

/-! ## Part 3: the automatic half of the scalar mass identity -/

/-- **The automatic half.**  If the finite-stage masses of an increasing clopen
family converge to `L`, then the limit law's mass of the union is at most `L`.
Equivalently `μ(C∞) ≤ liminf_k μ_k(C k)`; this half needs no mass-escape
estimate. -/
theorem le_of_tendsto_measure_toReal_of_monotone_clopen
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hmono : Monotone C) (hclopen : ∀ k, IsClopen (C k))
    (hUnion : ∀ x, (∃ k, x ∈ C k) ↔ x ∈ Cinf) {L : ℝ}
    (hL : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop (𝓝 L)) :
    ((μ : Measure (Configuration E)) Cinf).toReal ≤ L := by
  have hunion : Cinf = ⋃ k, C k := by
    ext x
    rw [Set.mem_iUnion]
    exact (hUnion x).symm
  have htend : ∀ m, Tendsto (fun k => ((μs k : Measure (Configuration E)) (C m)).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) (C m)).toReal)) := by
    intro m
    have hfr : (μ : Measure (Configuration E)) (frontier (C m)) = 0 := by
      rw [isClopen_iff_frontier_eq_empty.mp (hclopen m)]; simp
    exact ENNReal.tendsto_toReal (by simp) |>.comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ (E := C m) hfr)
  have hlevel : ∀ m, ((μ : Measure (Configuration E)) (C m)).toReal ≤ L := by
    intro m
    refine le_of_tendsto_of_tendsto (htend m) hL ?_
    filter_upwards [eventually_ge_atTop m] with k hk
    exact ENNReal.toReal_mono (by simp) (measure_mono (hmono hk))
  have hfin : ∀ m, (μ : Measure (Configuration E)) (C m) ≠ ⊤ := by intro m; simp
  rw [hunion, hmono.measure_iUnion, ENNReal.toReal_iSup hfin]
  exact ciSup_le hlevel

/-! ## Part 4: the box open-bit event and the finite-stage scalar identity -/

section Box

variable (B : FiniteBox E) (e : B.edges)

/-- The open-bit event of the box edge `e` is clopen. -/
lemma isClopen_splitBit : IsClopen {ω : Configuration E | B.splitBit e ω = true} :=
  (isClopen_discrete {true}).preimage (B.continuous_splitBit e)

lemma measurableSet_splitBit : MeasurableSet {ω : Configuration E | B.splitBit e ω = true} :=
  (isClopen_splitBit B e).isOpen.measurableSet

/-- Weak convergence gives convergence of the open-bit masses. -/
theorem tendsto_measure_splitBit
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun k => ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal)
      atTop (𝓝 (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal)) := by
  have hfr : (μ : Measure (Configuration E)) (frontier {ω | B.splitBit e ω = true}) = 0 := by
    rw [isClopen_iff_frontier_eq_empty.mp (isClopen_splitBit B e)]; simp
  exact ENNReal.tendsto_toReal (by simp) |>.comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hfr)

/-- **The finite-stage scalar identity in real form.**  The constant test `1` in
the finite-stage one-point identity of `FK.OneEdgeLimit` yields the box
open-bit mass as the integral of the one-edge conditional rate. -/
theorem stage_eq_of_fin
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (ρs : ℕ → Configuration E → ℝ)
    (hcont : ∀ k, Continuous (ρs k))
    (hρ0 : ∀ k ω, 0 ≤ ρs k ω) (hρ1 : ∀ k ω, ρs k ω ≤ 1)
    (hfin : ∀ (k : ℕ) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (ρs k ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (k : ℕ) :
    ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, ρs k ω ∂(μs k : Measure (Configuration E)) := by
  classical
  have : IsFiniteMeasure (μs k : Measure (Configuration E)) := inferInstance
  obtain ⟨φ, hφ⟩ :
      ∃ φ : BoundedContinuousFunction (B.Exterior × Glauber.OffConfig Bool B.edges e) ℝ,
        ∀ y, φ y = 1 :=
    ⟨BoundedContinuousFunction.mkOfCompact ⟨fun _ => 1, continuous_const⟩, fun _ => rfl⟩
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => by rw [hφ y]; norm_num
  have hmain := FiniteBox.finiteStage_real (B := B) (e := e) μs ρs hcont hρ0 hρ1 hfin k φ hφ0
  have hleft : ∫ ω, FiniteBox.openBitTest B e φ ω ∂(μs k : Measure (Configuration E))
      = ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal := by
    have hpt : ∀ ω, FiniteBox.openBitTest B e φ ω
        = {ω : Configuration E | B.splitBit e ω = true}.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : B.splitBit e ω = true
      · have hmem : ω ∈ {ω : Configuration E | B.splitBit e ω = true} := h
        rw [FiniteBox.openBitTest, FiniteBox.offTest, ite_eq_left h, Set.indicator_of_mem hmem, hφ]
      · have hmem : ω ∉ {ω : Configuration E | B.splitBit e ω = true} := by simpa using h
        rw [FiniteBox.openBitTest, ite_eq_right (by simpa using h), Set.indicator_of_notMem hmem]
    rw [show ∫ ω, FiniteBox.openBitTest B e φ ω ∂(μs k : Measure (Configuration E))
        = ∫ ω, {ω : Configuration E | B.splitBit e ω = true}.indicator (fun _ => (1:ℝ)) ω
            ∂(μs k : Measure (Configuration E)) from integral_congr_ae
          (Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_indicator (measurableSet_splitBit B e),
      MeasureTheory.setIntegral_const, Measure.real_def]
    simp
  have hright : ∫ ω, ρs k ω * FiniteBox.offTest B e φ ω ∂(μs k : Measure (Configuration E))
      = ∫ ω, ρs k ω ∂(μs k : Measure (Configuration E)) := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [FiniteBox.offTest, hφ]
  rw [hleft, hright] at hmain
  exact hmain

end Box

/-! ## Part 5: the no-mass-escape criterion -/

section Criterion

variable (B : FiniteBox E) (e : B.edges)

/-- The finite-stage connection masses converge to the explicit scalar `L`
determined by the open-bit mass and the two rate values. -/
private lemma stage_limit
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hαβ : α < β)
    {C : ℕ → Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k))
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      (𝓝 ((((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
        / (α - β))) := by
  classical
  have htend : Tendsto
      (fun k => ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal)) :=
    tendsto_measure_splitBit B e hμ
  have hstage' : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = β - (β - α) * ((μs k : Measure (Configuration E)) (C k)).toReal := by
    intro k
    rw [hstage k]
    exact integral_twoValuedRate (μs k) ((hCcl k).isOpen.measurableSet) α β
  have h2 : Tendsto
      (fun k => (((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
        / (α - β)) atTop
      (𝓝 ((((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β) / (α - β))) :=
    (htend.sub_const β).div_const (α - β)
  refine Tendsto.congr' (Eventually.of_forall fun k => ?_) h2
  rw [hstage' k]
  have hne : α - β ≠ 0 := by linarith
  field_simp
  ring

/-- **No-mass-escape criterion.**  Suppose the finite-stage laws satisfy the
one-point identity with the two-valued connection rates of the increasing
clopen family `C k`, and suppose `μs k ⇀ μ`.  Then the scalar mass identity for
the limiting rate (the remaining input of `onePoint_edge_of_scalar`) is
*equivalent* to the no-mass-escape inequality

`limsup_k μ_k(C k) ≤ μ(C∞)`.

The other half `μ(C∞) ≤ liminf_k μ_k(C k)` is automatic (`Part 3`). -/
theorem scalar_iff_limsup_le
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    ((∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
        = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
      ↔ Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
          ≤ ((μ : Measure (Configuration E)) Cinf).toReal := by
  classical
  set u : ℝ := ((μ : Measure (Configuration E)) Cinf).toReal with hu
  set L : ℝ := (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
    / (α - β) with hL
  have hconv : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop (𝓝 L) :=
    stage_limit B e μs μ hαβ hCcl hstage hμ
  have hauto : u ≤ L :=
    le_of_tendsto_measure_toReal_of_monotone_clopen hμ hCmono hCcl hCunion hconv
  have hCinfmeas : MeasurableSet Cinf := by
    have hun : Cinf = ⋃ k, C k := by
      ext x
      rw [Set.mem_iUnion]
      exact (hCunion x).symm
    rw [hun]
    exact MeasurableSet.iUnion fun k => (hCcl k).isOpen.measurableSet
  have hInt : Integrable (twoValuedRate α β Cinf) (μ : Measure (Configuration E)) := by
    refine Integrable.of_bound
      ((Measurable.ite hCinfmeas measurable_const measurable_const :
        Measurable (twoValuedRate α β Cinf)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => ?_)
    have h1 := twoValuedRate_mem_Icc hα0 hαβ.le hβ1 Cinf ω
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hnonneg : ∀ᵐ ω ∂(μ : Measure (Configuration E)), 0 ≤ twoValuedRate α β Cinf ω :=
    Eventually.of_forall fun ω => (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 Cinf ω).1
  have hX0 : 0 ≤ ∫ ω, twoValuedRate α β Cinf ω ∂(μ : Measure (Configuration E)) :=
    integral_nonneg fun ω => (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 Cinf ω).1
  have hintegral : ∫ ω, twoValuedRate α β Cinf ω ∂(μ : Measure (Configuration E))
      = β - (β - α) * u := integral_twoValuedRate μ hCinfmeas α β
  have hscalar_iff :
      ((∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
          = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
        ↔ ∫ ω, twoValuedRate α β Cinf ω ∂(μ : Measure (Configuration E))
            = ((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal := by
    have key : ENNReal.ofReal (∫ ω, twoValuedRate α β Cinf ω ∂(μ : Measure (Configuration E)))
        = ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)) :=
      ofReal_integral_eq_lintegral_ofReal hInt hnonneg
    constructor
    · intro h
      have h' : ENNReal.ofReal (∫ ω, twoValuedRate α β Cinf ω ∂(μ : Measure (Configuration E)))
          = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true} := by rw [key, h]
      have h2 := congrArg ENNReal.toReal h'
      rwa [ENNReal.toReal_ofReal hX0] at h2
    · intro h
      rw [← key, h, ENNReal.ofReal_toReal (by simp)]
  have hTL : ((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = β - (β - α) * L := by
    rw [hL]
    have hne : α - β ≠ 0 := by linarith
    field_simp
    ring
  have hlimsup : Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      = L := limsup_eq_of_tendsto hconv
  rw [hscalar_iff, hintegral, hlimsup]
  constructor
  · intro h
    have hEq : u = L := by
      rw [hTL] at h
      nlinarith [h, hαβ]
    linarith [hEq]
  · intro h
    have hEq : L = u := le_antisymm h hauto
    rw [hTL, hEq]

/-- **No-mass-escape in `Tendsto` form.**  The finite-stage connection masses
converge to the limit law's mass of the union, and conversely. -/
theorem tendsto_measure_iff_scalar
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
        (𝓝 (((μ : Measure (Configuration E)) Cinf).toReal))
      ↔ (∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω)
          ∂(μ : Measure (Configuration E)))
          = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true} := by
  classical
  set u : ℝ := ((μ : Measure (Configuration E)) Cinf).toReal with hu
  set L : ℝ := (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
    / (α - β) with hL
  have hconv : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop (𝓝 L) :=
    stage_limit B e μs μ hαβ hCcl hstage hμ
  have hauto : u ≤ L :=
    le_of_tendsto_measure_toReal_of_monotone_clopen hμ hCmono hCcl hCunion hconv
  have hcrit := scalar_iff_limsup_le B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ
  have hlimsup : Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      = L := limsup_eq_of_tendsto hconv
  constructor
  · intro h
    have h' : u = L := tendsto_nhds_unique h hconv
    refine hcrit.mpr ?_
    rw [hlimsup]
    exact le_of_eq h'.symm
  · intro h
    have hle : L ≤ u := by
      rw [← hlimsup]
      exact hcrit.mp h
    have hLeq : L = u := le_antisymm hle hauto
    rw [← hLeq]
    exact hconv


/-! ## Part 6: clopen measure convergence -/

/-- Weak convergence gives convergence of the masses of every clopen set. -/
theorem tendsto_measure_toReal_of_isClopen {A : Set (Configuration E)} (hA : IsClopen A)
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun k => ((μs k : Measure (Configuration E)) A).toReal) atTop
      (𝓝 (((μ : Measure (Configuration E)) A).toReal)) := by
  have hfr : (μ : Measure (Configuration E)) (frontier A) = 0 := by
    rw [isClopen_iff_frontier_eq_empty.mp hA]; simp
  exact ENNReal.tendsto_toReal (by simp) |>.comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hfr)

/-! ## Part 7: the small-box (far-vanishing) form of no mass escape -/

section FarVanishing

variable (B : FiniteBox E) (e : B.edges)

/-- **Small-box form of no-mass-escape.**  If, for every `ε > 0`, the mass of
the finite-stage connection events that need a witness leaving a *fixed* box
`C m` is eventually at most `ε`, then the scalar mass identity holds.  This is
the version in which the escape of the connection mass to infinity is made
explicit: `μ_k(C k \ C m)` is exactly the mass whose connection witness leaves
the fixed box `m`. -/
theorem scalar_of_farVanishing
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
      ∀ᶠ k in atTop, ((μs k : Measure (Configuration E)) (C k \ C m)).toReal ≤ ε) :
    (∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true} := by
  classical
  set s : ℕ → ℝ := fun k => ((μs k : Measure (Configuration E)) (C k)).toReal with hs
  set u : ℝ := ((μ : Measure (Configuration E)) Cinf).toReal with hu
  set L : ℝ := (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
    / (α - β) with hL
  have hconv : Tendsto s atTop (𝓝 L) := stage_limit B e μs μ hαβ hCcl hstage hμ
  have hauto : u ≤ L :=
    le_of_tendsto_measure_toReal_of_monotone_clopen hμ hCmono hCcl hCunion hconv
  have hcrit := scalar_iff_limsup_le B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ
  refine hcrit.mpr ?_
  rw [limsup_eq_of_tendsto hconv]
  have hsub_inf : ∀ m, C m ⊆ Cinf := by
    intro m x hx
    exact (hCunion x).mp ⟨m, hx⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm⟩ := hfar ε hε
  have hsplit : ∀ᶠ k in atTop,
      s k ≤ ((μs k : Measure (Configuration E)) (C m)).toReal + ε := by
    filter_upwards [eventually_ge_atTop m, hm] with k hk hkε
    have hsub : C m ⊆ C k := hCmono hk
    have hun : C m ∪ (C k \ C m) = C k := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hsub hx
        · exact hx.1
      · intro hx
        by_cases hxm : x ∈ C m
        · exact Or.inl hxm
        · exact Or.inr ⟨hx, hxm⟩
    have hdisj : Disjoint (C m) (C k \ C m) := disjoint_sdiff_right
    have hmeas : MeasurableSet (C k \ C m) :=
      ((hCcl k).isOpen.measurableSet).diff (hCcl m).isOpen.measurableSet
    calc s k = ((μs k : Measure (Configuration E)) (C k)).toReal := rfl
      _ = ((μs k : Measure (Configuration E)) (C m ∪ (C k \ C m))).toReal := by rw [hun]
      _ = ((μs k : Measure (Configuration E)) (C m)
            + (μs k : Measure (Configuration E)) (C k \ C m)).toReal := by
          rw [measure_union hdisj hmeas]
      _ = ((μs k : Measure (Configuration E)) (C m)).toReal
            + ((μs k : Measure (Configuration E)) (C k \ C m)).toReal :=
          ENNReal.toReal_add (by simp) (by simp)
      _ ≤ ((μs k : Measure (Configuration E)) (C m)).toReal + ε := by linarith
  have hlevel : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C m)).toReal + ε) atTop
      (𝓝 (((μ : Measure (Configuration E)) (C m)).toReal + ε)) :=
    (tendsto_measure_toReal_of_isClopen (hCcl m) hμ).add_const ε
  have hlim := le_of_tendsto_of_tendsto hconv hlevel hsplit
  have hle : ((μ : Measure (Configuration E)) (C m)).toReal ≤ u :=
    ENNReal.toReal_mono (by simp) (measure_mono (hsub_inf m))
  linarith

/-- **Stabilisation implies no mass escape.**  If the connection events are
eventually constant (as they are for graphs in which the connection has a
unique finite witness, e.g. forests), the scalar mass identity holds. -/
theorem scalar_of_eventually_eq
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (K : ℕ) (hstab : ∀ k, K ≤ k → C k = C K) :
    (∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true} := by
  classical
  refine scalar_of_farVanishing B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ ?_
  intro ε hε
  refine ⟨K, ?_⟩
  filter_upwards [eventually_ge_atTop K] with k hk
  rw [hstab k hk, Set.sdiff_eq_empty.mpr (Set.Subset.refl _)]
  simp only [measure_empty, ENNReal.toReal_zero]
  exact hε.le

/-- **Domination by the limit implies no mass escape.**  If every finite-stage
mass of the union event is at most its limit mass, the scalar mass identity
holds. -/
theorem scalar_of_dominated
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hdom : ∀ k, (μs k : Measure (Configuration E)) Cinf
      ≤ (μ : Measure (Configuration E)) Cinf) :
    (∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true} := by
  classical
  set s : ℕ → ℝ := fun k => ((μs k : Measure (Configuration E)) (C k)).toReal with hs
  set u : ℝ := ((μ : Measure (Configuration E)) Cinf).toReal with hu
  set L : ℝ := (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
    / (α - β) with hL
  have hconv : Tendsto s atTop (𝓝 L) := stage_limit B e μs μ hαβ hCcl hstage hμ
  have hauto : u ≤ L :=
    le_of_tendsto_measure_toReal_of_monotone_clopen hμ hCmono hCcl hCunion hconv
  have hcrit := scalar_iff_limsup_le B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ
  refine hcrit.mpr ?_
  rw [limsup_eq_of_tendsto hconv]
  have hbound : ∀ k, s k ≤ u := by
    intro k
    have h1 : (μs k : Measure (Configuration E)) (C k)
        ≤ (μs k : Measure (Configuration E)) Cinf :=
      measure_mono fun x hx => (hCunion x).mp ⟨k, hx⟩
    calc s k = ((μs k : Measure (Configuration E)) (C k)).toReal := rfl
      _ ≤ ((μs k : Measure (Configuration E)) Cinf).toReal := ENNReal.toReal_mono (by simp) h1
      _ ≤ u := ENNReal.toReal_mono (by simp) (hdom k)
  exact le_of_tendsto_of_tendsto hconv tendsto_const_nhds (Eventually.of_forall hbound)

/-- **Cylinder agreement implies no mass escape.**  If every finite-stage law
agrees with the limit on the event `C k` itself, then the sequence of masses is
the restriction of the limit's own masses along an increasing family, and no
mass can escape.  This is the exact structural property that monotone
(Bernoulli / `q = 1`, or stabilising) models have and that the nonmonotone FK
exhaustions do not. -/
theorem scalar_of_agreesOnEvents
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hagree : ∀ k, (μs k : Measure (Configuration E)) (C k)
      = (μ : Measure (Configuration E)) (C k)) :
    (∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
      = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true} := by
  classical
  set s : ℕ → ℝ := fun k => ((μs k : Measure (Configuration E)) (C k)).toReal with hs
  set u : ℝ := ((μ : Measure (Configuration E)) Cinf).toReal with hu
  set L : ℝ := (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
    / (α - β) with hL
  have hconv : Tendsto s atTop (𝓝 L) := stage_limit B e μs μ hαβ hCcl hstage hμ
  have hun : Cinf = ⋃ k, C k := by
    ext x
    rw [Set.mem_iUnion]
    exact (hCunion x).symm
  have hlev : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop (𝓝 u) := by
    have h1 : Tendsto (fun m => (μ : Measure (Configuration E)) (C m)) atTop
        (𝓝 ((μ : Measure (Configuration E)) (⋃ m, C m))) :=
      MeasureTheory.tendsto_measure_iUnion_atTop hCmono
    have h2 : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop
        (𝓝 (((μ : Measure (Configuration E)) (⋃ m, C m))).toReal) :=
      (ENNReal.tendsto_toReal
        (by simp : (μ : Measure (Configuration E)) (⋃ m, C m) ≠ ⊤)).comp h1
    simpa [hu, hun] using h2
  have hs_eq : ∀ k, s k = ((μ : Measure (Configuration E)) (C k)).toReal := by
    intro k
    rw [show s k = ((μs k : Measure (Configuration E)) (C k)).toReal from rfl, hagree k]
  have hLu : L = u := tendsto_nhds_unique hconv
    (Tendsto.congr' (Eventually.of_forall fun k => (hs_eq k).symm) hlev)
  refine (scalar_iff_limsup_le B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ).mpr ?_
  rw [limsup_eq_of_tendsto hconv, hLu]

/-- **The small-box inequality is equivalent to the scalar mass identity.**
No mass escapes if and only if the mass of the finite-stage connection events
whose witness has to leave a fixed box `C m` is eventually arbitrarily small.
This makes the residual analytic input of the one-point determination route a
statement about a *fixed* finite box, uniformly in the exhaustion. -/
theorem scalar_iff_farVanishing
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    ((∫⁻ ω, ENNReal.ofReal (twoValuedRate α β Cinf ω) ∂(μ : Measure (Configuration E)))
        = (μ : Measure (Configuration E)) {ω | B.splitBit e ω = true})
      ↔ ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
          ∀ᶠ k in atTop, ((μs k : Measure (Configuration E)) (C k \ C m)).toReal ≤ ε := by
  classical
  constructor
  · intro hscalar
    set s : ℕ → ℝ := fun k => ((μs k : Measure (Configuration E)) (C k)).toReal with hs
    set u : ℝ := ((μ : Measure (Configuration E)) Cinf).toReal with hu
    set L : ℝ := (((μ : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal - β)
      / (α - β) with hL
    have hconv : Tendsto s atTop (𝓝 L) := stage_limit B e μs μ hαβ hCcl hstage hμ
    have hnoEscape : Filter.limsup s atTop ≤ u :=
      (scalar_iff_limsup_le B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ).mp hscalar
    have hLe : L ≤ u := by
      rw [← limsup_eq_of_tendsto hconv]; exact hnoEscape
    have hmono' : Monotone fun m => ((μ : Measure (Configuration E)) (C m)).toReal := by
      intro m n hmn
      exact ENNReal.toReal_mono (by simp) (measure_mono (hCmono hmn))
    have hun : Cinf = ⋃ k, C k := by
      ext x
      rw [Set.mem_iUnion]
      exact (hCunion x).symm
    have hlev : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop (𝓝 u) := by
      have h1 : Tendsto (fun m => (μ : Measure (Configuration E)) (C m)) atTop
          (𝓝 ((μ : Measure (Configuration E)) (⋃ m, C m))) :=
        MeasureTheory.tendsto_measure_iUnion_atTop hCmono
      have h2 : Tendsto (fun m => ((μ : Measure (Configuration E)) (C m)).toReal) atTop
          (𝓝 (((μ : Measure (Configuration E)) (⋃ m, C m))).toReal) :=
        (ENNReal.tendsto_toReal
          (by simp : (μ : Measure (Configuration E)) (⋃ m, C m) ≠ ⊤)).comp h1
      simpa [hu, hun] using h2
    intro ε hε
    have h0 : ∀ᶠ m in atTop, u - ((μ : Measure (Configuration E)) (C m)).toReal ≤ ε / 4 := by
      have hmono0 : Tendsto (fun m => u - ((μ : Measure (Configuration E)) (C m)).toReal) atTop
          (𝓝 (u - u)) := hlev.const_sub u
      have h0' : Tendsto (fun m => u - ((μ : Measure (Configuration E)) (C m)).toReal) atTop
          (𝓝 0) := by simpa using hmono0
      have hlt : ∀ᶠ m in atTop,
          u - ((μ : Measure (Configuration E)) (C m)).toReal < ε / 4 :=
        h0'.eventually (isOpen_Iio.mem_nhds (by linarith : (0:ℝ) < ε / 4))
      exact hlt.mono fun m hm => le_of_lt hm
    obtain ⟨m, hm⟩ := h0.exists
    refine ⟨m, ?_⟩
    have hse : ∀ᶠ k in atTop, s k ≤ u + ε / 4 := by
      have h1 : ∀ᶠ k in atTop, s k < u + ε / 4 :=
        hconv.eventually (isOpen_Iio.mem_nhds (by linarith : L < u + ε / 4))
      exact h1.mono fun k hk => le_of_lt hk
    have hlvl : ∀ᶠ k in atTop,
        ((μ : Measure (Configuration E)) (C m)).toReal - ε / 4
          ≤ ((μs k : Measure (Configuration E)) (C m)).toReal := by
      have h2tend : Tendsto (fun k => ((μs k : Measure (Configuration E)) (C m)).toReal) atTop
          (𝓝 (((μ : Measure (Configuration E)) (C m)).toReal)) :=
        tendsto_measure_toReal_of_isClopen (hCcl m) hμ
      have h2 : ∀ᶠ k in atTop,
          ((μ : Measure (Configuration E)) (C m)).toReal - ε / 4
            < ((μs k : Measure (Configuration E)) (C m)).toReal :=
        h2tend.eventually (isOpen_Ioi.mem_nhds
          (sub_lt_self _ (by linarith : (0:ℝ) < ε / 4)))
      exact h2.mono fun k hk => le_of_lt hk
    filter_upwards [eventually_ge_atTop m, hse, hlvl] with k hk hks hkl
    have hsub : C m ⊆ C k := hCmono hk
    have hunion : C m ∪ (C k \ C m) = C k := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact hsub hx
        · exact hx.1
      · intro hx
        by_cases hxm : x ∈ C m
        · exact Or.inl hxm
        · exact Or.inr ⟨hx, hxm⟩
    have hdisj : Disjoint (C m) (C k \ C m) := disjoint_sdiff_right
    have hmeas : MeasurableSet (C k \ C m) :=
      ((hCcl k).isOpen.measurableSet).diff (hCcl m).isOpen.measurableSet
    have hsum : (μs k : Measure (Configuration E)) (C k)
        = (μs k : Measure (Configuration E)) (C m)
          + (μs k : Measure (Configuration E)) (C k \ C m) := by
      calc (μs k : Measure (Configuration E)) (C k)
          = (μs k : Measure (Configuration E)) (C m ∪ (C k \ C m)) := by rw [hunion]
        _ = (μs k : Measure (Configuration E)) (C m)
              + (μs k : Measure (Configuration E)) (C k \ C m) := measure_union hdisj hmeas
    have hsplit : ((μs k : Measure (Configuration E)) (C k \ C m)).toReal
        = s k - ((μs k : Measure (Configuration E)) (C m)).toReal := by
      have hs' : s k = ((μs k : Measure (Configuration E)) (C k)).toReal := rfl
      rw [hs', hsum, ENNReal.toReal_add (by simp) (by simp)]
      ring
    rw [hsplit]
    linarith
  · exact scalar_of_farVanishing B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hstage hμ

end FarVanishing


/-! ## Part 8: sharpness -- no mass escape is not automatic -/

section Counterexample

/-- The configuration with a single open edge at `k`. -/
def pt (k : ℕ) : Configuration ℕ := fun j => decide (j = k)

/-- The all-closed configuration. -/
def zeroConfig : Configuration ℕ := fun _ => false

/-- The connection-type events: some edge among `1, …, k+1` is open. -/
def Cset (k : ℕ) : Set (Configuration ℕ) :=
  {ω | ∃ j ∈ Finset.Icc 1 (k + 1), ω j = true}

/-- The union of the events `Cset k`. -/
def CsetInf : Set (Configuration ℕ) := {ω | ∃ j, 1 ≤ j ∧ ω j = true}

lemma isClopen_Cset (k : ℕ) : IsClopen (Cset k) := by
  have h : Cset k = ⋃ j ∈ Finset.Icc 1 (k + 1), {ω : Configuration ℕ | ω j = true} := by
    ext ω
    simp [Cset]
  rw [h]
  exact isClopen_biUnion_finset
    (fun j _ => (isClopen_discrete {true}).preimage (continuous_apply j))

lemma measurableSet_CsetInf : MeasurableSet CsetInf := by
  have h : CsetInf = ⋃ j, {ω : Configuration ℕ | 1 ≤ j ∧ ω j = true} := by
    ext ω
    simp [CsetInf]
  rw [h]
  refine MeasurableSet.iUnion fun j => ?_
  by_cases hj : 1 ≤ j
  · have h1 : {ω : Configuration ℕ | 1 ≤ j ∧ ω j = true} = {ω : Configuration ℕ | ω j = true} := by
      ext ω
      simp [hj]
    rw [h1]
    exact ((isClopen_discrete {true}).preimage (continuous_apply j)).isOpen.measurableSet
  · have h1 : {ω : Configuration ℕ | 1 ≤ j ∧ ω j = true} = ∅ := by
      ext ω
      simp [hj]
    rw [h1]
    exact MeasurableSet.empty

lemma monotone_Cset : Monotone Cset := by
  intro k l hkl ω hω
  obtain ⟨j, hj, hw⟩ := hω
  exact ⟨j, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
    le_trans (Finset.mem_Icc.mp hj).2 (by omega)⟩, hw⟩

lemma union_Cset : ∀ ω : Configuration ℕ, (∃ k, ω ∈ Cset k) ↔ ω ∈ CsetInf := by
  intro ω
  constructor
  · rintro ⟨k, j, hj, hw⟩
    exact ⟨j, (Finset.mem_Icc.mp hj).1, hw⟩
  · rintro ⟨j, hj1, hw⟩
    exact ⟨j, j, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, hw⟩

lemma pt_mem_Cset (k : ℕ) : pt (k + 1) ∈ Cset k :=
  ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩, by simp [pt]⟩

lemma zeroConfig_notMem_CsetInf : zeroConfig ∉ CsetInf := by
  rintro ⟨j, -, hw⟩
  simp [zeroConfig] at hw

lemma tendsto_pt : Tendsto (fun k => pt (k + 1)) atTop (𝓝 zeroConfig) := by
  rw [tendsto_pi_nhds]
  intro j
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop j] with k hk
  have h : j ≠ k + 1 := by omega
  simp [pt, zeroConfig, h]

lemma tendsto_dirac_pt :
    Tendsto (fun k => diracProba (pt (k + 1))) atTop
      (𝓝 (diracProba zeroConfig)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hcomp : Tendsto (fun k => f (pt (k + 1))) atTop (𝓝 (f zeroConfig)) :=
    f.continuous.tendsto zeroConfig |>.comp tendsto_pt
  simpa only [MeasureTheory.diracProba, ProbabilityMeasure.coe_mk, integral_dirac] using hcomp

/-- **Sharpness.**  No mass escape is *not* a consequence of the remaining
measure-theoretic hypotheses: there are increasing clopen events `C k` with
union `Cinf` whose finite-stage masses are all `1` while the limit puts mass
`0` on the union.  (Concretely the witness of `C k` moves off to infinity, as
in the single-open-edge configuration `pt (k+1)`.) -/
theorem exists_massEscaping :
    ∃ (μs : ℕ → ProbabilityMeasure (Configuration ℕ))
      (μ : ProbabilityMeasure (Configuration ℕ))
      (C : ℕ → Set (Configuration ℕ)) (Cinf : Set (Configuration ℕ)),
      (∀ k, IsClopen (C k)) ∧ Monotone C ∧ (∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf) ∧
      Tendsto μs atTop (𝓝 μ) ∧
      ¬ (Filter.limsup (fun k => ((μs k : Measure (Configuration ℕ)) (C k)).toReal) atTop
          ≤ ((μ : Measure (Configuration ℕ)) Cinf).toReal) := by
  refine ⟨fun k => diracProba (pt (k + 1)), diracProba zeroConfig, Cset, CsetInf,
    isClopen_Cset, monotone_Cset, union_Cset, tendsto_dirac_pt, ?_⟩
  have h1 : ∀ k, ((diracProba (pt (k + 1)) : Measure (Configuration ℕ)) (Cset k)).toReal = 1 := by
    intro k
    rw [diracProba_toMeasure_apply_of_mem (pt_mem_Cset k)]
    simp
  have h0 : ((diracProba zeroConfig : Measure (Configuration ℕ)) CsetInf).toReal = 0 := by
    rw [diracProba_toMeasure_apply' zeroConfig measurableSet_CsetInf,
      Set.indicator_of_notMem zeroConfig_notMem_CsetInf]
    simp
  simp only [h1, h0]
  have hlimsup : Filter.limsup (fun _ : ℕ => (1 : ℝ)) atTop = 1 :=
    limsup_eq_of_tendsto tendsto_const_nhds
  rw [hlimsup]
  norm_num

end Counterexample

/-! ## Part 9: the per-edge one-point identity from no mass escape -/

section Assembly

variable (B : FiniteBox E) (e : B.edges)

/-- **Per-edge one-point identity from no mass escape.**  This is
`FiniteBox.onePoint_edge_of_scalar` with the scalar mass identity replaced by
the geometric no-mass-escape inequality for the connection events.  All the
remaining inputs (the two-valued stage rates, monotonicity, continuity and the
pointwise rate limit) are discharged from clopenness and monotonicity of the
events. -/
theorem onePoint_edge_of_noEscape
    {q p : NNReal}
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    {α β : ℝ} (hα0 : 0 ≤ α) (hαβ : α < β) (hβ1 : β ≤ 1)
    {C : ℕ → Set (Configuration E)} {Cinf : Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔ ω ∈ Cinf)
    (hfin : ∀ (k : ℕ) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (twoValuedRate α β (C k) ω) * g (B.splitOff e ω)
          ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hnoEscape : Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E)) Cinf).toReal)
    (αspec : B.Exterior → B.BoundaryPartition)
    (hrate : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      twoValuedRate α β Cinf ω = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
    (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0) ∂(μ : Measure (Configuration E))
      = ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) := by
  classical
  have hcont : ∀ k, Continuous (twoValuedRate α β (C k)) :=
    fun k => continuous_twoValuedRate α β (hCcl k)
  have hρ0 : ∀ k ω, 0 ≤ twoValuedRate α β (C k) ω := fun k ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (C k) ω).1
  have hρ1 : ∀ k ω, twoValuedRate α β (C k) ω ≤ 1 := fun k ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 (C k) ω).2
  have hρmono : ∀ k ω, twoValuedRate α β (C (k + 1)) ω ≤ twoValuedRate α β (C k) ω := by
    intro k ω
    by_cases h : ω ∈ C (k + 1)
    · have h' : twoValuedRate α β (C (k + 1)) ω = α := by simp [twoValuedRate, h]
      rw [h']
      by_cases h2 : ω ∈ C k
      · simp [twoValuedRate, h2]
      · have : twoValuedRate α β (C k) ω = β := by simp [twoValuedRate, h2]
        rw [this]
        exact hαβ.le
    · have h' : twoValuedRate α β (C (k + 1)) ω = β := by simp [twoValuedRate, h]
      rw [h']
      have h2 : ω ∉ C k := fun hc => h (hCmono (Nat.le_succ k) hc)
      simp [twoValuedRate, h2]
  have hlim : ∀ ω, Tendsto (fun k => twoValuedRate α β (C k) ω) atTop
      (𝓝 (twoValuedRate α β Cinf ω)) := by
    intro ω
    by_cases h : ω ∈ Cinf
    · obtain ⟨K, hK⟩ := (hCunion ω).mpr h
      have hev : ∀ᶠ k in atTop, twoValuedRate α β (C k) ω = α := by
        filter_upwards [eventually_ge_atTop K] with k hk
        simp [twoValuedRate, hCmono hk hK]
      have hlimα : twoValuedRate α β Cinf ω = α := by simp [twoValuedRate, h]
      rw [hlimα]
      exact Tendsto.congr' (hev.mono fun k hk => hk.symm) tendsto_const_nhds
    · have hk : ∀ k, ω ∉ C k := fun k hk => h ((hCunion ω).mp ⟨k, hk⟩)
      have hev : ∀ᶠ k in atTop, twoValuedRate α β (C k) ω = β :=
        Eventually.of_forall fun k => by simp [twoValuedRate, hk k]
      have hlimβ : twoValuedRate α β Cinf ω = β := by simp [twoValuedRate, h]
      rw [hlimβ]
      exact Tendsto.congr' (hev.mono fun k hk => hk.symm) tendsto_const_nhds
  have hCinfmeas : MeasurableSet Cinf := by
    have hun : Cinf = ⋃ k, C k := by
      ext x
      rw [Set.mem_iUnion]
      exact (hCunion x).symm
    rw [hun]
    exact MeasurableSet.iUnion fun k => (hCcl k).isOpen.measurableSet
  have hρmeas : Measurable (twoValuedRate α β Cinf) :=
    Measurable.ite hCinfmeas measurable_const measurable_const
  have hρ0' : ∀ ω, 0 ≤ twoValuedRate α β Cinf ω := fun ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 Cinf ω).1
  have hρ1' : ∀ ω, twoValuedRate α β Cinf ω ≤ 1 := fun ω =>
    (twoValuedRate_mem_Icc hα0 hαβ.le hβ1 Cinf ω).2
  have hstage : ∀ k, ((μs k : Measure (Configuration E)) {ω | B.splitBit e ω = true}).toReal
      = ∫ ω, twoValuedRate α β (C k) ω ∂(μs k : Measure (Configuration E)) :=
    fun k => stage_eq_of_fin B e μs (fun k => twoValuedRate α β (C k)) hcont hρ0 hρ1 hfin k
  have hscalar := (scalar_iff_limsup_le B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion
    hstage hμ).mpr hnoEscape
  exact FiniteBox.onePoint_edge_of_scalar (B := B) (e := e) μs μ
    (fun k => twoValuedRate α β (C k)) (twoValuedRate α β Cinf)
    hcont hρ0 hρ1 hρmono hlim hfin hμ hρmeas hρ0' hρ1' hscalar αspec hrate g hg


/-! ## Part 10: the random-cluster rate in two-valued normal form -/

omit [Countable E] in
/-- **The random-cluster one-edge rate is two-valued.**  Definitionally, the
one-edge FK rate equals `p` on the event that the endpoints of `e` are
connected (without `e`, in the off-configuration wired by the exterior
partition) and `FK.prime q p = p/(p + q(1-p))` off it.  Consequently the a.e.
rate identification `hrate` of `onePoint_edge_of_scalar` is automatic once the
connection event `Cinf` is *defined* as the connection event of the box graph,
and is not an extra input. -/
lemma openRate_eq_twoValuedRate {q p : NNReal}
    (αspec : B.Exterior → B.BoundaryPartition) :
    (fun ω : Configuration E => Glauber.FKBridge.openRate B.graph (q := q) (p := p)
        (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2))
      = twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
          {ω : Configuration E | FK.Finite.Conditional.endpointsConnectedWithout B.graph
            (αspec ((B.splitOff e ω).1)) e
            (Glauber.FKBridge.offConfiguration B.graph (αspec ((B.splitOff e ω).1)) e
              ((B.splitOff e ω).2))} := rfl

/-- For `q < 1` the connected rate `p` is *below* the disconnected rate
`p/(p+q(1-p))`, so increasing the connection event decreases the rate. -/
theorem lt_prime_iff {q p : ℝ} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    p < FK.prime q p ↔ q < 1 := by
  rw [FK.prime]
  have hD : (0:ℝ) < p + q * (1 - p) := by nlinarith
  have h1p : (0:ℝ) < 1 - p := by linarith
  rw [lt_div_iff₀ hD]
  constructor
  · intro h
    have h2 : p * (p + q * (1 - p)) < p * 1 := by simpa using h
    have h3 : p + q * (1 - p) < 1 := lt_of_mul_lt_mul_left h2 hp0.le
    nlinarith [h3, h1p]
  · intro h
    have h3 : p + q * (1 - p) < 1 := by nlinarith [h, h1p]
    calc p * (p + q * (1 - p)) < p * 1 := mul_lt_mul_of_pos_left h3 hp0
      _ = p := by ring

/-- For `q > 1` the connected rate `p` is *above* the disconnected rate, so
increasing the connection event increases the rate. -/
theorem prime_lt_iff {q p : ℝ} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) :
    FK.prime q p < p ↔ 1 < q := by
  rw [FK.prime]
  have hD : (0:ℝ) < p + q * (1 - p) := by nlinarith
  have h1p : (0:ℝ) < 1 - p := by linarith
  rw [div_lt_iff₀ hD]
  constructor
  · intro h
    have h2 : p * 1 < p * (p + q * (1 - p)) := by simpa using h
    have h3 : 1 < p + q * (1 - p) := lt_of_mul_lt_mul_left h2 hp0.le
    nlinarith [h3, h1p]
  · intro h
    have h3 : 1 < p + q * (1 - p) := by nlinarith [h, h1p]
    calc p = p * 1 := by ring
      _ < p * (p + q * (1 - p)) := mul_lt_mul_of_pos_left h3 hp0

/-- **Geometric form of the per-edge one-point identity.**  With the limiting
connection event `Cinf` taken to be the actual box-graph connection event of
the specification, the rate identification is automatic and the only remaining
input beyond the finite-stage identities is no mass escape. -/
theorem onePoint_edge_of_noEscape_geometric
    {q p : NNReal}
    (μs : ℕ → ProbabilityMeasure (Configuration E))
    (μ : ProbabilityMeasure (Configuration E))
    (αspec : B.Exterior → B.BoundaryPartition)
    {C : ℕ → Set (Configuration E)}
    (hCcl : ∀ k, IsClopen (C k)) (hCmono : Monotone C)
    (hCunion : ∀ ω, (∃ k, ω ∈ C k) ↔
      FK.Finite.Conditional.endpointsConnectedWithout B.graph
        (αspec ((B.splitOff e ω).1)) e
        (Glauber.FKBridge.offConfiguration B.graph (αspec ((B.splitOff e ω).1)) e
          ((B.splitOff e ω).2)))
    (hfin : ∀ (k : ℕ) (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0)
          ∂(μs k : Measure (Configuration E))
        = ∫⁻ ω, ENNReal.ofReal (twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) (C k) ω)
            * g (B.splitOff e ω) ∂(μs k : Measure (Configuration E)))
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hnoEscape : Filter.limsup (fun k => ((μs k : Measure (Configuration E)) (C k)).toReal) atTop
      ≤ ((μ : Measure (Configuration E))
          {ω : Configuration E | FK.Finite.Conditional.endpointsConnectedWithout B.graph
            (αspec ((B.splitOff e ω).1)) e
            (Glauber.FKBridge.offConfiguration B.graph (αspec ((B.splitOff e ω).1)) e
              ((B.splitOff e ω).2))}).toReal)
    (q₀ : 0 < q) (q₁ : q < 1) (p₀ : 0 < p) (p₁ : p < 1)
    (g : B.Exterior × Glauber.OffConfig Bool B.edges e → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, (bif B.splitBit e ω then g (B.splitOff e ω) else 0) ∂(μ : Measure (Configuration E))
      = ∫⁻ ω, ENNReal.ofReal (Glauber.FKBridge.openRate B.graph (q := q) (p := p)
          (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2)) * g (B.splitOff e ω)
        ∂(μ : Measure (Configuration E)) := by
  classical
  have hα0 : (0:ℝ) ≤ (p : ℝ) := by positivity
  have hβ1 : FK.prime (q : ℝ) (p : ℝ) ≤ 1 :=
    FK.prime_le_one (by exact_mod_cast q₀) (by positivity) (by exact_mod_cast p₁.le)
  have hαβ : (p : ℝ) < FK.prime (q : ℝ) (p : ℝ) := by
    rw [lt_prime_iff (by exact_mod_cast q₀) (by exact_mod_cast p₀) (by exact_mod_cast p₁)]
    exact_mod_cast q₁
  have hrate : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ))
          {ω : Configuration E | FK.Finite.Conditional.endpointsConnectedWithout B.graph
            (αspec ((B.splitOff e ω).1)) e
            (Glauber.FKBridge.offConfiguration B.graph (αspec ((B.splitOff e ω).1)) e
              ((B.splitOff e ω).2))} ω
        = Glauber.FKBridge.openRate B.graph (q := q) (p := p)
            (αspec ((B.splitOff e ω).1)) e ((B.splitOff e ω).2) := by
    filter_upwards with ω
    exact (congrFun (openRate_eq_twoValuedRate B e αspec) ω).symm
  exact onePoint_edge_of_noEscape B e μs μ hα0 hαβ hβ1 hCcl hCmono hCunion hfin hμ
    hnoEscape αspec hrate g hg

end Assembly

end Criterion

end OneEdgeNoEscape

end FK.InfiniteVolume
