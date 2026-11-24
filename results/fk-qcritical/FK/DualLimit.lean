import FK.DualParameterDuality
import FK.MonotoneLimitExistence
import FK.Theorem110Assembly

/-!
# Infinite-volume duality for FK measures

Beffara--Faipeur--Oke, arXiv:2512.16486v1, proof of Theorem 1.11 (Section 5.2):
"By applying the duality relation (12) to all finite subgraphs `Λ ⊂ G`, it
follows that `φ` is the (unique) dual measure of `φ*`."

The finite conditioned duality (12) at the paper's dual parameter `p*`
(`FK.FinitePlane.dualParameter`), its transport to the DLR equation, and the
per-box dual-uniqueness step are already proved in `FK.DualParameterDuality`.
What is missing for the theorem is the *infinite-volume* statement: the dual of
an FK **limit** measure is again an FK limit measure at the dual parameters
along the dual box sequence, and hence uniqueness of the dual class forces
uniqueness of the primal class.

This file supplies that.  The essential bookkeeping point is that the dual of a
closed-exterior finite-volume law is *not* a closed-exterior finite-volume law:
complementation turns the closed exterior into the open one, so the dual object
is a limit of genuine external-boundary conditional laws.  The external-boundary
form is the one the paper actually uses (`φ^{Φ_Λ(ξ)}_{Λ,p,q}` with an exterior
configuration `ξ`), and the project's
`tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw` converts it back to
`IsFKLimit` when needed.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical Topology

noncomputable section

namespace FK.InfiniteVolume

variable {E : Type*} [Countable E]

local instance boundaryPartitionMeasurableSpaceM1 (V : Type*) : MeasurableSpace (Setoid V) := ⊤

/-- The all-open exterior configuration of a box. -/
def openExterior (B : FiniteBox E) : B.Exterior := fun _ => true

/-- Complementation sends the closed exterior to the open one. -/
@[simp] lemma extDual_closedExterior (B : FiniteBox E) :
    extDual B B.closedExterior = openExterior B := by
  funext i
  rw [extDual_apply]
  rfl

/-- Complementation sends the open exterior back to the closed one. -/
@[simp] lemma extDual_openExterior (B : FiniteBox E) :
    extDual B (openExterior B) = B.closedExterior := by
  rw [← extDual_closedExterior B, extDual_invol]

/-- Complementation of a glued configuration flips both parts. -/
lemma cfgDual_glue (B : FiniteBox E) (η : B.Exterior) (ω : B.Interior) :
    cfgDual E (B.glue (η, ω)) = B.glue (extDual B η, intDual B ω) := by
  apply B.splitEquiv.injective
  rw [B.splitEquiv_apply, split_cfgDual, B.splitEquiv_apply, B.split_glue, B.split_glue]

/-- **Equation (12) for one box, exterior-parametrised form.**  If the primal box
FK PMF at `(q,p)` with the convention induced by an exterior configuration is
the dual box FK PMF at `(q,p*)` composed with complementation, then complementing
the primal conditional law at exterior `η` gives the dual box conditional law at
the complemented exterior.  This is the local statement used in the proof of
Theorem 1.11, with an *arbitrary* exterior configuration (no freedom at
infinity is assumed). -/
theorem map_conditionalLaw_cfgDual_dualParameter
    (B : FiniteBox E) (Vd : Type*) [Fintype Vd] (s t : B.edges → Vd)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp (α (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq (FK.FinitePlane.dualParameter_le_one hq hp)
          (αD η) (intDual B ω))
    (η : B.Exterior) :
    ProbabilityMeasure.map (B.conditionalLaw hq hp α η) (cfgDual E) =
      (dualBox B Vd s t).conditionalLaw hq (FK.FinitePlane.dualParameter_le_one hq hp)
        αD (extDual B η) := by
  have hk := kernel_dual_of_pmf_dual_dualParameter (B := B) (Vd := Vd) (s := s) (t := t)
    (q := q) (p := p) hq hp α hα αD hαD hpmf
  have hK : ((dualBox B Vd s t).graph.fkMeasure hq (FK.FinitePlane.dualParameter_le_one hq hp)
        (αD (extDual B η))) =
      Measure.map (intDual B) (B.graph.fkMeasure hq hp (α η)) := by
    have h := hk (extDual B η)
    rw [extDual_invol, FiniteBox.fkKernel_apply, FiniteBox.fkKernel_apply] at h
    exact h
  apply Subtype.ext
  show Measure.map (cfgDual E)
      (Measure.map (fun ω : B.Interior => B.glue (η, ω))
        (B.graph.fkMeasure hq hp (α η))) =
    Measure.map (fun ω : B.Interior => B.glue (extDual B η, ω))
      ((dualBox B Vd s t).graph.fkMeasure hq (FK.FinitePlane.dualParameter_le_one hq hp)
        (αD (extDual B η)))
  rw [hK,
    Measure.map_map (cfgDual E).measurable (B.measurable_glue_const_left η),
    Measure.map_map (B.measurable_glue_const_left (extDual B η)) (intDual B).measurable]
  congr 1
  funext ω
  rw [Function.comp_apply, Function.comp_apply, cfgDual_glue]

/-- The closed-exterior finite-volume law is the special case of the conditional
law at the closed exterior with a constant convention; its complement is the dual
box conditional law at the all-open exterior. -/
theorem map_finiteVolumeLaw_cfgDual_dualParameter
    (B : FiniteBox E) (Vd : Type*) [Fintype Vd] (s t : B.edges → Vd)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.BoundaryPartition)
    (αD : B.Exterior → (dualBox B Vd s t).BoundaryPartition) (hαD : Measurable αD)
    (hpmf : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp α ω =
        (dualBox B Vd s t).graph.fkPMF hq (FK.FinitePlane.dualParameter_le_one hq hp)
          (αD η) (intDual B ω)) :
    ProbabilityMeasure.map (B.finiteVolumeLaw hq hp α) (cfgDual E) =
      (dualBox B Vd s t).conditionalLaw hq (FK.FinitePlane.dualParameter_le_one hq hp)
        αD (openExterior B) := by
  have hpmf' : ∀ (η : B.Exterior) (ω : B.Interior),
      B.graph.fkPMF hq hp ((fun _ : B.Exterior => α) (extDual B η)) ω =
        (dualBox B Vd s t).graph.fkPMF hq (FK.FinitePlane.dualParameter_le_one hq hp)
          (αD η) (intDual B ω) := fun η ω => hpmf η ω
  have h := map_conditionalLaw_cfgDual_dualParameter (B := B) (Vd := Vd) (s := s) (t := t)
    (q := q) (p := p) hq hp (fun _ : B.Exterior => α) measurable_const αD hαD hpmf'
    B.closedExterior
  rw [extDual_closedExterior] at h
  exact h

/-! ## Cylinder bookkeeping and the infinite-volume limit -/

/-- Pointwise complement of a finite-coordinate pattern. -/
def flipPattern (J : Finset E) (A : Set (↥J → Bool)) : Set (↥J → Bool) :=
  {w | (fun i : ↥J => !(w i)) ∈ A}

lemma restrict_cfgDual (J : Finset E) (ω : Configuration E) :
    J.restrict (cfgDual E ω) = (fun i : ↥J => !(J.restrict ω i)) := by
  funext i
  rw [cfgDual_apply]
  rfl

/-- Complementation of a cylinder is the cylinder of the complemented pattern. -/
lemma cyl_preimage_cfgDual (J : Finset E) (A : Set (↥J → Bool)) :
    cfgDual E ⁻¹' cyl J A = cyl J (flipPattern J A) := by
  ext ω
  simp only [cyl, Set.mem_preimage, flipPattern, Set.mem_ofPred_eq, restrict_cfgDual]

/-- Real masses pull back along a measurable map. -/
lemma real_map_apply_cfg (μ : Measure (Configuration E)) (f : Configuration E → Configuration E)
    (hf : Measurable f) {A : Set (Configuration E)} (hA : MeasurableSet A) :
    (Measure.map f μ).real A = μ.real (f ⁻¹' A) := by
  rw [Measure.real_def, Measure.real_def, Measure.map_apply hf hA]

/-- **Infinite-volume duality (external-boundary limit form).**  If the primal
finite-volume laws with conventions `α n` at exterior configurations `η n`
converge to `μ`, and each box satisfies the finite conditioned duality (12) at
the dual parameters, then complementing the primal limit is the limit of the dual
boxes' conditional laws at the complemented exteriors. -/
theorem tendsto_conditionalLaw_cfgDual
    (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (hα : ∀ n, Measurable (α n))
    (αD : ∀ n, (exh.box n).Exterior →
      (dualBox (exh.box n) (Vd n) (s n) (t n)).BoundaryPartition)
    (hαD : ∀ n, Measurable (αD n))
    (hpmf : ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
      (exh.box n).graph.fkPMF hq hp (α n (extDual (exh.box n) η)) ω =
        (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η) (intDual (exh.box n) ω))
    (η : ∀ n, (exh.box n).Exterior)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp (α n) (η n))
      atTop (𝓝 μ)) :
    Tendsto (fun n => (dualBox (exh.box n) (Vd n) (s n) (t n)).conditionalLaw hq
      (FK.FinitePlane.dualParameter_le_one hq hp) (αD n)
        (extDual (exh.box n) (η n)))
      atTop (𝓝 (ProbabilityMeasure.map μ (cfgDual E))) := by
  rw [tendsto_probabilityMeasure_iff_cylinder_real_tendsto]
  intro J A
  have hprimal := (tendsto_probabilityMeasure_iff_cylinder_real_tendsto
    (fun n => (exh.box n).conditionalLaw hq hp (α n) (η n)) μ).1 hμ
  have hlim : Tendsto (fun n =>
      ((exh.box n).conditionalLaw hq hp (α n) (η n) : Measure (Configuration E)).real
        (cyl J (flipPattern J A))) atTop
      (𝓝 ((μ : Measure (Configuration E)).real (cyl J (flipPattern J A)))) :=
    hprimal J (flipPattern J A)
  have htarget : ((μ : Measure (Configuration E)).real (cyl J (flipPattern J A)))
      = (((ProbabilityMeasure.map μ (cfgDual E) :
            ProbabilityMeasure (Configuration E)) : Measure (Configuration E)).real (cyl J A)) := by
    rw [ProbabilityMeasure.toMeasure_map,
      real_map_apply_cfg _ _ (cfgDual E).measurable (dependsOn_cyl J A).measurableSet,
      cyl_preimage_cfgDual]
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [exh.eventually_subset J] with n _
  have hmap := map_conditionalLaw_cfgDual_dualParameter (exh.box n) (Vd n) (s n) (t n)
    hq hp (α n) (hα n) (αD n) (hαD n) (hpmf n) (η n)
  have hreal := congrArg (fun ν : ProbabilityMeasure (Configuration E) =>
    ((ν : Measure (Configuration E)).real (cyl J A))) hmap
  rw [ProbabilityMeasure.toMeasure_map,
    real_map_apply_cfg _ _ (cfgDual E).measurable (dependsOn_cyl J A).measurableSet,
    cyl_preimage_cfgDual] at hreal
  exact hreal

/-! ## The dual box exhaustion and the `IsFKLimit` form -/

/-- The dual box family of an exhaustion is again an exhaustion: the global edge
labels are unchanged by duality. -/
def dualExhaustion (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n) : BoxExhaustion E where
  box n := dualBox (exh.box n) (Vd n) (s n) (t n)
  monotone := exh.monotone
  covers := exh.covers

@[simp] lemma dualExhaustion_box (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n) (n : ℕ) :
    (dualExhaustion exh Vd s t).box n = dualBox (exh.box n) (Vd n) (s n) (t n) := rfl

/-- **The complement of every FK limit is an FK limit at the dual parameters.**
This is the infinite-volume form of equation (12): applied to all finite
subgraphs along the exhaustion.  The dual boundary sequence is the dual
convention evaluated at the all-open exterior, which is exactly the complement
of the closed exterior used by `finiteVolumeLaw`. -/
theorem isFKLimit_map_cfgDual
    (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (αD : ∀ n, (exh.box n).Exterior →
      (dualBox (exh.box n) (Vd n) (s n) (t n)).BoundaryPartition)
    (hαD : ∀ n, Measurable (αD n))
    (hpmf : ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
      (exh.box n).graph.fkPMF hq hp (α n) ω =
        (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η) (intDual (exh.box n) ω))
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : IsFKLimit exh hq hp α μ) :
    IsFKLimit (dualExhaustion exh Vd s t) hq (FK.FinitePlane.dualParameter_le_one hq hp)
      (fun n => αD n (openExterior (exh.box n)))
      (ProbabilityMeasure.map μ (cfgDual E)) := by
  have hpmf' : ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
      (exh.box n).graph.fkPMF hq hp ((fun _ : (exh.box n).Exterior => α n) (extDual (exh.box n) η)) ω =
        (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η) (intDual (exh.box n) ω) :=
    fun n η ω => hpmf n η ω
  have hcond : Tendsto (fun n => (exh.box n).conditionalLaw hq hp
      (fun _ : (exh.box n).Exterior => α n) (fun _ => false))
      atTop (𝓝 μ) :=
    (tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw exh hq hp
      (fun n (_ : (exh.box n).Exterior) => α n) (fun n => (exh.box n).closedExterior) μ).1 hμ
  have hdual := tendsto_conditionalLaw_cfgDual exh Vd s t hq hp
    (fun n (_ : (exh.box n).Exterior) => α n) (fun n => measurable_const) αD hαD hpmf'
    (fun n => (exh.box n).closedExterior) μ hcond
  refine (tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw (dualExhaustion exh Vd s t)
    hq (FK.FinitePlane.dualParameter_le_one hq hp) (fun n => αD n)
    (fun n => openExterior (exh.box n)) (ProbabilityMeasure.map μ (cfgDual E))).2 ?_
  exact hdual

/-- **Dual uniqueness forces primal uniqueness of the FK limit class.**  If the
dual box exhaustion has a unique FK limit measure `ν₀` at `(q,p*)`, then every
primal FK limit whose boundary sequence admits the finite duality (12) is the
complement of `ν₀`. -/
theorem eq_map_of_unique_dual_fkLimit
    (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    (αD : ∀ n, (exh.box n).Exterior →
      (dualBox (exh.box n) (Vd n) (s n) (t n)).BoundaryPartition)
    (hαD : ∀ n, Measurable (αD n))
    (hpmf : ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
      (exh.box n).graph.fkPMF hq hp (α n) ω =
        (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η) (intDual (exh.box n) ω))
    (ν₀ : ProbabilityMeasure (Configuration E))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKLimitMeasures (dualExhaustion exh Vd s t) hq
        (FK.FinitePlane.dualParameter_le_one hq hp) → ν = ν₀)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : IsFKLimit exh hq hp α μ) :
    μ = ProbabilityMeasure.map ν₀ (cfgDual E) := by
  have hkey : ProbabilityMeasure.map μ (cfgDual E) = ν₀ :=
    huniq _ ⟨_, isFKLimit_map_cfgDual exh Vd s t hq hp α αD hαD hpmf μ hμ⟩
  calc μ = ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual E)) (cfgDual E) :=
        (map_cfgDual_map_cfgDual μ).symm
    _ = ProbabilityMeasure.map ν₀ (cfgDual E) := by rw [hkey]


/-! ## Theorem 1.11 modulo dual uniqueness -/

/-- **Theorem 1.11 reduced to dual uniqueness and the finite duality (12).**

The two inputs are:

* `huniq` — strong uniqueness of the **dual-parameter** FK limit class on the
  dual box exhaustion, i.e. Theorem 1.10 applied to the dual graph `G*` at
  parameters `(q, p*)` (this is where the Aizenman--Grimmett window is used in
  the paper);
* `hdualizable` — for every primal boundary sequence there is a dual convention
  for which the finite conditioned duality (12) holds box by box (in the paper:
  equation (12) for the exterior configurations of the exhaustion, which is
  available whenever the primal has at most one infinite cluster).

Nothing here assumes the conclusion: the conclusion is uniqueness of the *total*
FK family `FK(p,q)`, including every boundary convention and every weak limit.
The proof routes through the limit-level duality above and the already proved
Proposition 1.8(1) + Choquet step `eq_of_unique_fkLimit`. -/
theorem theorem_1_11_modulo_dual_uniqueness
    (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ν₀ : ProbabilityMeasure (Configuration E))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKLimitMeasures (dualExhaustion exh Vd s t) hq
        (FK.FinitePlane.dualParameter_le_one hq hp) → ν = ν₀)
    (hdualizable : ∀ α : ∀ n, (exh.box n).BoundaryPartition,
      ∃ (αD : ∀ n, (exh.box n).Exterior →
          (dualBox (exh.box n) (Vd n) (s n) (t n)).BoundaryPartition)
        (hαD : ∀ n, Measurable (αD n)),
        ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
          (exh.box n).graph.fkPMF hq hp (α n) ω =
            (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
              (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η)
              (intDual (exh.box n) ω)) :
    ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKFamily exh hq hp → ν = ProbabilityMeasure.map ν₀ (cfgDual E) := by
  refine eq_of_unique_fkLimit hq hp exh (fun μ hμ => ?_)
  obtain ⟨α, hα⟩ := hμ
  obtain ⟨αD, hαD, hpmf⟩ := hdualizable α
  exact eq_map_of_unique_dual_fkLimit exh Vd s t hq hp α αD hαD hpmf ν₀ huniq μ hα

/-! ## Axiom audit -/

#print axioms FK.InfiniteVolume.map_conditionalLaw_cfgDual_dualParameter
#print axioms FK.InfiniteVolume.map_finiteVolumeLaw_cfgDual_dualParameter
#print axioms FK.InfiniteVolume.tendsto_conditionalLaw_cfgDual
#print axioms FK.InfiniteVolume.isFKLimit_map_cfgDual
#print axioms FK.InfiniteVolume.eq_map_of_unique_dual_fkLimit
#print axioms FK.InfiniteVolume.theorem_1_11_modulo_dual_uniqueness


/-! ## The paper's equation (12) discharges the duality hypothesis

The infinite-volume theorems above take the box-by-box conditioned duality as a
hypothesis.  In the paper's plane geometry that hypothesis is *proved*:
`FK.InfiniteVolume.planeBox_pmf_dualParameter` is equation (12) at the paper's
dual parameter `p*`, for the free (primal) convention and the source dual
convention, with an **arbitrary** exterior configuration.  Here we record that
it has exactly the shape required above, at the level of the actual conditional
laws. -/

open FK.FinitePlane FK.Configuration

universe w

variable {V VD Ib O OD : Type w} [Fintype V] [Fintype VD] [Fintype Ib] [Fintype O]
  [Fintype OD]

/-- **Equation (12) as a conditional-law identity.**  For every exterior
configuration, complementing the primal `(q,p)` conditional law of the plane box
with the free convention gives the dual box's `(q,p*)` conditional law with the
source dual convention, at the complemented exterior.  No assumption on the
number of infinite exterior clusters is needed: the identity is stated for every
exterior configuration. -/
theorem map_conditionalLaw_planeBox_cfgDual
    (s t : Ib ⊕ O → V) (sD tD : ↥(sumEdges Ib O) ⊕ OD → VD) (eO : O ≃ OD)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (heuler : ∀ ρ : Ib ⊕ O → Bool,
      (ambientOfSum sD tD).componentCount (ambientOfSum sD tD).freeBoundary
          (dualConfig ((sumEdgesEquiv Ib O).sumCongr eO) ρ) + Fintype.card V =
        (ambientOfSum s t).componentCount (ambientOfSum s t).freeBoundary ρ +
          1 + openCard ρ)
    (hα : Measurable (primalConvention (V := V) s t))
    (hαD : Measurable (dualConvention (V := V) s t sD tD eO))
    (η : (planeBox (V := V) s t).Exterior) :
    ProbabilityMeasure.map
        ((planeBox (V := V) s t).conditionalLaw hq hp₁.le
          (primalConvention (V := V) s t) η) (cfgDual (Ib ⊕ O)) =
      (dualBox (planeBox (V := V) s t) VD (fun e => sD (Sum.inl e))
          (fun e => tD (Sum.inl e))).conditionalLaw hq
        (FK.FinitePlane.dualParameter_le_one hq hp₁.le)
        (dualConvention (V := V) s t sD tD eO)
        (extDual (planeBox (V := V) s t) η) :=
  map_conditionalLaw_cfgDual_dualParameter (planeBox (V := V) s t) VD
    (fun e => sD (Sum.inl e)) (fun e => tD (Sum.inl e)) hq hp₁.le
    (primalConvention (V := V) s t) hα
    (dualConvention (V := V) s t sD tD eO) hαD
    (planeBox_pmf_dualParameter s t sD tD eO hq hp₀ hp₁ heuler) η

#print axioms FK.InfiniteVolume.map_conditionalLaw_planeBox_cfgDual



/-! ## Theorem 1.11 in the paper's own hypothesis shape -/

/-- **Theorem 1.11 modulo strong uniqueness at the dual parameters.**

`hdual` is exactly the *conclusion* of Theorem 1.10 (strong uniqueness in the
subcritical regime) applied to the dual plane graph `G*` at parameters `(q, p*)`;
`hdualizable` is the finite conditioned duality (12) for the primal boundary
sequences in play.  The conclusion is the paper's: strong uniqueness of the
total FK family at `(p,q)` on `G`, with the unique measure the complement of the
dual one.  Note that the primal side is quantified over *all* boundary
conventions and weak limits; no scoping reduction of `FK(p,q)` is made. -/
theorem theorem_1_11_modulo_dual_family_uniqueness
    (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (ν₀ : ProbabilityMeasure (Configuration E))
    (hdual : ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKFamily (dualExhaustion exh Vd s t) hq
        (FK.FinitePlane.dualParameter_le_one hq hp) → ν = ν₀)
    (hdualizable : ∀ α : ∀ n, (exh.box n).BoundaryPartition,
      ∃ (αD : ∀ n, (exh.box n).Exterior →
          (dualBox (exh.box n) (Vd n) (s n) (t n)).BoundaryPartition)
        (hαD : ∀ n, Measurable (αD n)),
        ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
          (exh.box n).graph.fkPMF hq hp (α n) ω =
            (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
              (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η)
              (intDual (exh.box n) ω)) :
    ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKFamily exh hq hp → ν = ProbabilityMeasure.map ν₀ (cfgDual E) :=
  theorem_1_11_modulo_dual_uniqueness exh Vd s t hq hp ν₀
    (fun ν hν => hdual ν (mem_fkFamily_of_mem_fkLimit hq
      (FK.FinitePlane.dualParameter_le_one hq hp) (dualExhaustion exh Vd s t) hν))
    hdualizable

#print axioms FK.InfiniteVolume.theorem_1_11_modulo_dual_family_uniqueness


/-! ## Class-level (all-box) dual transport and identification

`FK.DualParameterDuality.eq_map_of_unique_dual_dualParameter` identifies a primal
DLR law from a dual law that is unique **at one box**.  For Theorem 1.11 this is
too strong an input: Theorem 1.10 applied to `G*` gives uniqueness of the whole
dual DLR *class* (equivalently, by Proposition 1.8(1), of the exhaustion class),
not per-box uniqueness.  The two theorems below upgrade the per-box statement to
an arbitrary family of boxes — in particular to every box of an exhaustion —
which is exactly the form the paper's last step uses. -/

/-- **Class-level dual transport.**  If `μ` satisfies the `(q,p)` DLR equation for
every box of an arbitrary family (with exterior-induced primal conventions), then
its complement satisfies the `(q,p*)` DLR equation for the dual box of every box
of the family (with the dual conventions). -/
theorem isDLR_map_cfgDual_allBoxes
    {ι : Type*} (box : ι → FiniteBox E)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)] (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ i, (box i).Exterior → (box i).BoundaryPartition)
    (hα : ∀ i, Measurable (α i))
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (hpmf : ∀ i (η : (box i).Exterior) (ω : (box i).Interior),
      (box i).graph.fkPMF hq hp (α i (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD i η) (intDual (box i) ω))
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : ∀ i, (box i).IsDLR hq hp (α i) (hα i) μ) :
    ∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
      (FK.FinitePlane.dualParameter_le_one hq hp) (αD i) (hαD i)
      (ProbabilityMeasure.map μ (cfgDual E)) :=
  fun i => isDLR_map_cfgDual_dualParameter (box i) (Vd i) (s i) (t i) hq hp
    (α i) (hα i) (αD i) (hαD i) μ (hμ i) (hpmf i)

/-- **Class-level dual identification.**  If the dual `(q,p*)` DLR class of an
arbitrary box family is the singleton `{ν₀}`, then every `(q,p)` DLR law of the
primal family is the complement of `ν₀`.  This is the paper's final step of
Theorem 1.11 ("`φ` is the unique dual measure of `φ*`") in the form that
Theorem 1.10 on `G*` can supply. -/
theorem eq_map_of_allBoxes_unique_dual
    {ι : Type*} (box : ι → FiniteBox E)
    (Vd : ι → Type) [∀ i, Fintype (Vd i)] (s t : ∀ i, (box i).edges → Vd i)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ i, (box i).Exterior → (box i).BoundaryPartition)
    (hα : ∀ i, Measurable (α i))
    (αD : ∀ i, (box i).Exterior →
      (dualBox (box i) (Vd i) (s i) (t i)).BoundaryPartition)
    (hαD : ∀ i, Measurable (αD i))
    (hpmf : ∀ i (η : (box i).Exterior) (ω : (box i).Interior),
      (box i).graph.fkPMF hq hp (α i (extDual (box i) η)) ω =
        (dualBox (box i) (Vd i) (s i) (t i)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD i η) (intDual (box i) ω))
    (ν₀ : ProbabilityMeasure (Configuration E))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration E),
      (∀ i, (dualBox (box i) (Vd i) (s i) (t i)).IsDLR hq
        (FK.FinitePlane.dualParameter_le_one hq hp) (αD i) (hαD i) ν) → ν = ν₀)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : ∀ i, (box i).IsDLR hq hp (α i) (hα i) μ) :
    μ = ProbabilityMeasure.map ν₀ (cfgDual E) := by
  have hkey : ProbabilityMeasure.map μ (cfgDual E) = ν₀ :=
    huniq _ (isDLR_map_cfgDual_allBoxes box Vd s t hq hp α hα αD hαD hpmf μ hμ)
  calc μ = ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual E)) (cfgDual E) :=
        (map_cfgDual_map_cfgDual μ).symm
    _ = ProbabilityMeasure.map ν₀ (cfgDual E) := by rw [hkey]

#print axioms FK.InfiniteVolume.isDLR_map_cfgDual_allBoxes
#print axioms FK.InfiniteVolume.eq_map_of_allBoxes_unique_dual


/-! ## The paper's Theorem 1.11 parameter window at the genuine dual parameter

The dual-box DLR transport above carries the parameter `p* =
FK.FinitePlane.dualParameter q p` (a `NNReal`), while the paper's scalar
identities `FK.max_dual_prime_dual` and `FK.parameter_window_iff` are stated for
the real-valued `FK.dual`.  These two lemmas transfer them to the parameter that
the duality theorems actually use, so that the Aizenman–Grimmett window
`max(p*,p'*) < p_c(G*)+δ''` can be attached to `isFKLimit_map_cfgDual`
directly. -/

/-- **`max(p*, p'*) = 1 - min(p, p')` at the dual parameter `p*`** carried by the
dual-box DLR transport. -/
theorem max_dualParameter_prime_eq_one_sub_min {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) :
    max ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ)
        (FK.prime (q : ℝ) ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ))
      = 1 - min (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hp0R : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hden := FK.denominator_ne_zero hqR hp0R hp1R
  have hdual : FK.dual (q : ℝ) (p : ℝ) = 1 - FK.prime (q : ℝ) (p : ℝ) :=
    FK.dual_eq_one_sub_prime hden
  have hprime : FK.prime (q : ℝ) (1 - FK.prime (q : ℝ) (p : ℝ)) = 1 - (p : ℝ) := by
    rw [← hdual]
    exact FK.prime_dual hqR hp0R hp1R
  rw [FK.InfiniteVolume.coe_dualParameter_eq_one_sub_prime hq hp, hprime]
  exact (FK.max_one_sub_eq_one_sub_min (FK.prime (q : ℝ) (p : ℝ)) (p : ℝ)).trans
    (by rw [min_comm])

/-- **Theorem 1.11's parameter conversion**: `min(p,p') > 1-p_c(G*)-δ''` is
exactly the subcritical window `max(p*,p'*) < p_c(G*)+δ''` at the dual
parameter `p*` used by the dual-box transport. -/
theorem parameter_window_iff_dualParameter {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (c δ : ℝ) :
    (max ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ)
        (FK.prime (q : ℝ) ((FK.FinitePlane.dualParameter q p : NNReal) : ℝ)) < c + δ)
      ↔ min (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) > 1 - c - δ := by
  rw [max_dualParameter_prime_eq_one_sub_min hq hp]
  constructor <;> intro h <;> linarith

#print axioms FK.InfiniteVolume.max_dualParameter_prime_eq_one_sub_min
#print axioms FK.InfiniteVolume.parameter_window_iff_dualParameter


/-! ## The source's own limit form: typical exterior configurations

Proposition 1.8(1) of the paper represents an extremal DLR law as
`φ = lim_n φ^{Φ_{Λ_n}(ξ)}_{Λ_n,p,q}` for `φ`-a.e. `ξ`, i.e. as a limit of
conditional laws at *exterior configurations*, not at closed exteriors.  The
following form of the identification covers exactly that input; the dual limit
is then an FK limit measure in the `finiteVolumeLaw` sense, so class-level dual
uniqueness applies to it. -/

/-- **Dual uniqueness identifies every free-convention limit at typical exterior
configurations.**  If `μ` is a limit of primal conditional laws with conventions
`α n` at exteriors `η n`, and the dual exhaustion has a unique FK limit measure
`ν₀` at the dual parameters, then `μ` is the complement of `ν₀`. -/
theorem eq_map_of_unique_dual_generalExterior
    (exh : BoxExhaustion E) (Vd : ℕ → Type) [∀ n, Fintype (Vd n)]
    (s t : ∀ n, (exh.box n).edges → Vd n)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).Exterior → (exh.box n).BoundaryPartition)
    (hα : ∀ n, Measurable (α n))
    (αD : ∀ n, (exh.box n).Exterior →
      (dualBox (exh.box n) (Vd n) (s n) (t n)).BoundaryPartition)
    (hαD : ∀ n, Measurable (αD n))
    (hpmf : ∀ n (η : (exh.box n).Exterior) (ω : (exh.box n).Interior),
      (exh.box n).graph.fkPMF hq hp (α n (extDual (exh.box n) η)) ω =
        (dualBox (exh.box n) (Vd n) (s n) (t n)).graph.fkPMF hq
          (FK.FinitePlane.dualParameter_le_one hq hp) (αD n η) (intDual (exh.box n) ω))
    (η : ∀ n, (exh.box n).Exterior)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : Tendsto (fun n => (exh.box n).conditionalLaw hq hp (α n) (η n))
      atTop (𝓝 μ))
    (ν₀ : ProbabilityMeasure (Configuration E))
    (huniq : ∀ ν : ProbabilityMeasure (Configuration E),
      ν ∈ FKLimitMeasures (dualExhaustion exh Vd s t) hq
        (FK.FinitePlane.dualParameter_le_one hq hp) → ν = ν₀) :
    μ = ProbabilityMeasure.map ν₀ (cfgDual E) := by
  have hdual := tendsto_conditionalLaw_cfgDual exh Vd s t hq hp α hα αD hαD hpmf η μ hμ
  have hmem : ProbabilityMeasure.map μ (cfgDual E) ∈
      FKLimitMeasures (dualExhaustion exh Vd s t) hq
        (FK.FinitePlane.dualParameter_le_one hq hp) :=
    ⟨fun n => αD n (extDual (exh.box n) (η n)),
      (FK.InfiniteVolume.tendsto_finiteVolumeLaw_iff_tendsto_conditionalLaw (dualExhaustion exh Vd s t)
        hq (FK.FinitePlane.dualParameter_le_one hq hp) (fun n => αD n)
        (fun n => extDual (exh.box n) (η n)) (ProbabilityMeasure.map μ (cfgDual E))).2 hdual⟩
  have hkey : ProbabilityMeasure.map μ (cfgDual E) = ν₀ := huniq _ hmem
  calc μ = ProbabilityMeasure.map (ProbabilityMeasure.map μ (cfgDual E)) (cfgDual E) :=
        (map_cfgDual_map_cfgDual μ).symm
    _ = ProbabilityMeasure.map ν₀ (cfgDual E) := by rw [hkey]

#print axioms FK.InfiniteVolume.eq_map_of_unique_dual_generalExterior

end FK.InfiniteVolume
