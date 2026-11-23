import FK.BernoulliFiniteBox

/-!
# Cylinder-local comparison transport through the DLR equation

For a finitely supported event, the enhanced Bernoulli comparison product can
be evaluated on the supporting box alone. Thus the exterior marginal of a DLR
law need not be Bernoulli: the comparison-product fibre probability is constant
in the exterior configuration.
-/

namespace FK.InfiniteVolume

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

noncomputable section

local instance boundaryPartitionMeasurableSpaceCylinder (V : Type*) :
    MeasurableSpace (Setoid V) := ⊤
local instance finiteSetoidCylinder (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- On an event supported in `B`, changing the exterior does not change the
interior fibre of the event. -/
lemma glue_fiber_eq_of_dependsOn {A : Set (Configuration E)}
    (hA : FKLimit.DependsOnCoordinates A B.edges) (η ξ : B.Exterior) :
    (fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A =
      (fun ω : B.Interior ↦ B.glue (ξ, ω)) ⁻¹' A := by
  ext ω
  apply hA
  intro e he
  simp [glue, he]

/-- Lower comparison on one box, without any assumption on the exterior
marginal of the DLR law. -/
theorem apply_le_of_isDLR_local_lower
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    (r : E → unitInterval)
    (hlocal : ∀ η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1))
      (B.graph.fkMeasure hq hp (α η)))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hAupper : IsUpperSet A) (hdep : FKLimit.DependsOnCoordinates A B.edges) :
    (FKLimit.bernoulliProduct r) A ≤ μ A := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  let ρ : Measure B.Exterior := Measure.infinitePi
    (fun e : {e : E // e ∉ B.edges} => bernoulliMeasure true false (r e.1))
  let ν : Measure B.Interior :=
    FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1)
  have htarget : ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A) =
      ∫⁻ η, ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) ∂ρ := by
    dsimp only [ν, ρ]
    rw [B.bernoulliProduct_eq_map_glue_prod,
      Measure.map_apply hg hA, Measure.prod_apply (hg hA)]
    rfl
  have hconst : ∀ η : B.Exterior,
      ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) =
        ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A) := by
    intro η
    rw [B.glue_fiber_eq_of_dependsOn hdep η B.closedExterior]
  change ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A).toNNReal ≤
    ((μ : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [htarget, B.measure_eq_map_glue_compProd hq hp α hα μ hμ,
    Measure.map_apply hg hA, Measure.compProd_apply (hg hA)]
  calc
    (∫⁻ η, ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) ∂ρ) =
        ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A) := by
      simp_rw [hconst]
      simp
    _ = ∫⁻ _η, ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A)
        ∂(B.exteriorMeasure μ : Measure B.Exterior) := by simp
    _ ≤ ∫⁻ η, (B.graph.fkMeasure hq hp (α η))
        ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A)
        ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
      apply lintegral_mono
      intro η
      dsimp only
      rw [B.glue_fiber_eq_of_dependsOn hdep B.closedExterior η]
      exact hlocal η _ (B.measurable_glue_const_left η hA)
        (B.isUpperSet_glue_fiber hAupper η)

/-- Upper comparison on one box, again with an arbitrary DLR exterior
marginal. -/
theorem le_apply_of_isDLR_local_upper
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    (r : E → unitInterval)
    (hlocal : ∀ η, FKEnhancement.StochasticallyDominates
      (B.graph.fkMeasure hq hp (α η))
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1)))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hAupper : IsUpperSet A) (hdep : FKLimit.DependsOnCoordinates A B.edges) :
    μ A ≤ (FKLimit.bernoulliProduct r) A := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  let ρ : Measure B.Exterior := Measure.infinitePi
    (fun e : {e : E // e ∉ B.edges} => bernoulliMeasure true false (r e.1))
  let ν : Measure B.Interior :=
    FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1)
  have htarget : ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A) =
      ∫⁻ η, ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) ∂ρ := by
    dsimp only [ν, ρ]
    rw [B.bernoulliProduct_eq_map_glue_prod,
      Measure.map_apply hg hA, Measure.prod_apply (hg hA)]
    rfl
  have hconst : ∀ η : B.Exterior,
      ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) =
        ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A) := by
    intro η
    rw [B.glue_fiber_eq_of_dependsOn hdep η B.closedExterior]
  change ((μ : Measure (Configuration E)) A).toNNReal ≤
    ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [htarget, B.measure_eq_map_glue_compProd hq hp α hα μ hμ,
    Measure.map_apply hg hA, Measure.compProd_apply (hg hA)]
  calc
    (∫⁻ η, (B.graph.fkMeasure hq hp (α η))
        ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A)
        ∂(B.exteriorMeasure μ : Measure B.Exterior)) ≤
        ∫⁻ _η, ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A)
          ∂(B.exteriorMeasure μ : Measure B.Exterior) := by
      apply lintegral_mono
      intro η
      rw [B.glue_fiber_eq_of_dependsOn hdep B.closedExterior η]
      exact hlocal η _ (B.measurable_glue_const_left η hA)
        (B.isUpperSet_glue_fiber hAupper η)
    _ = ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A) := by simp
    _ = ∫⁻ η, ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) ∂ρ := by
      simp_rw [hconst]
      simp

/-- A box-supported Bernoulli probability is exactly the fibre probability at
the canonical closed exterior. -/
lemma bernoulliProduct_apply_eq_closed_fiber
    (r : E → unitInterval) {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hdep : FKLimit.DependsOnCoordinates A B.edges) :
    ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A) =
      FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1)
        ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A) := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  let ρ : Measure B.Exterior := Measure.infinitePi
    (fun e : {e : E // e ∉ B.edges} => bernoulliMeasure true false (r e.1))
  let ν : Measure B.Interior :=
    FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1)
  have htarget : ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A) =
      ∫⁻ η, ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) ∂ρ := by
    dsimp only [ν, ρ]
    rw [B.bernoulliProduct_eq_map_glue_prod,
      Measure.map_apply hg hA, Measure.prod_apply (hg hA)]
    rfl
  have hconst : ∀ η : B.Exterior,
      ν ((fun ω : B.Interior ↦ B.glue (η, ω)) ⁻¹' A) =
        ν ((fun ω : B.Interior ↦ B.glue (B.closedExterior, ω)) ⁻¹' A) := by
    intro η
    rw [B.glue_fiber_eq_of_dependsOn hdep η B.closedExterior]
  rw [htarget]
  simp_rw [hconst]
  simp
  rfl

/-- A lower interior comparison gives the corresponding box-local comparison
against a finite-volume law with its actual closed exterior. -/
theorem apply_le_finiteVolumeLaw_local_lower
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (α : B.BoundaryPartition)
    (r : E → unitInterval)
    (hlocal : FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1))
      (B.graph.fkMeasure hq hp α))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hAupper : IsUpperSet A) (hdep : FKLimit.DependsOnCoordinates A B.edges) :
    (FKLimit.bernoulliProduct r) A ≤ B.finiteVolumeLaw hq hp α A := by
  have hvol : ((B.finiteVolumeLaw hq hp α : Measure (Configuration E)) A) =
      B.graph.fkMeasure hq hp α ((fun ω : B.Interior ↦
        B.glue (B.closedExterior, ω)) ⁻¹' A) := by
    exact Measure.map_apply (B.measurable_glue_const_left B.closedExterior) hA
  change ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A).toNNReal ≤
    ((B.finiteVolumeLaw hq hp α : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [B.bernoulliProduct_apply_eq_closed_fiber r hA hdep, hvol]
  exact hlocal _ (B.measurable_glue_const_left B.closedExterior hA)
    (B.isUpperSet_glue_fiber hAupper B.closedExterior)

/-- The upper finite-volume companion. -/
theorem le_apply_finiteVolumeLaw_local_upper
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (α : B.BoundaryPartition)
    (r : E → unitInterval)
    (hlocal : FKEnhancement.StochasticallyDominates
      (B.graph.fkMeasure hq hp α)
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1)))
    {A : Set (Configuration E)} (hA : MeasurableSet A)
    (hAupper : IsUpperSet A) (hdep : FKLimit.DependsOnCoordinates A B.edges) :
    B.finiteVolumeLaw hq hp α A ≤ (FKLimit.bernoulliProduct r) A := by
  have hvol : ((B.finiteVolumeLaw hq hp α : Measure (Configuration E)) A) =
      B.graph.fkMeasure hq hp α ((fun ω : B.Interior ↦
        B.glue (B.closedExterior, ω)) ⁻¹' A) := by
    exact Measure.map_apply (B.measurable_glue_const_left B.closedExterior) hA
  change ((B.finiteVolumeLaw hq hp α : Measure (Configuration E)) A).toNNReal ≤
    ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [B.bernoulliProduct_apply_eq_closed_fiber r hA hdep, hvol]
  exact hlocal _ (B.measurable_glue_const_left B.closedExterior hA)
    (B.isUpperSet_glue_fiber hAupper B.closedExterior)

end FiniteBox

/-- Uniform interior lower comparisons on every box give cylinder domination
for every DLR law of the fixed convention. No exterior-product equality is
required. -/
theorem cylinderDominates_of_mem_dlrMeasures_local_lower
    {E : Type*} (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (r : E → unitInterval)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => r e.1))
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))) :
    FKLimit.CylinderDominates μ (FKLimit.bernoulliProduct r) := by
  intro A S hdep hAupper
  obtain ⟨n, hn⟩ : ∃ n, S ⊆ (exh.box n).edges := by
    have h : ∀ᶠ n in Filter.atTop, S ⊆ (exh.box n).edges := exh.eventually_subset S
    exact Filter.Eventually.exists h
  exact (exh.box n).apply_le_of_isDLR_local_lower hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ (hμ n) r (hlocal n) hdep.measurableSet hAupper
      (hdep.mono hn)

/-- The corresponding cylinder upper comparison for every DLR law. -/
theorem cylinderDominates_of_mem_dlrMeasures_local_upper
    {E : Type*} (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (r : E → unitInterval)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => r e.1))) :
    FKLimit.CylinderDominates (FKLimit.bernoulliProduct r) μ := by
  intro A S hdep hAupper
  obtain ⟨n, hn⟩ : ∃ n, S ⊆ (exh.box n).edges := by
    have h : ∀ᶠ n in Filter.atTop, S ⊆ (exh.box n).edges := exh.eventually_subset S
    exact Filter.Eventually.exists h
  exact (exh.box n).le_apply_of_isDLR_local_upper hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ (hμ n) r (hlocal n) hdep.measurableSet hAupper
      (hdep.mono hn)

/-- Full lower stochastic comparison for a countable labelled edge space. -/
theorem stochasticallyDominates_of_mem_dlrMeasures_local_lower
    {E : Type*} [Countable E] (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (r : E → unitInterval)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => r e.1))
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) :=
  FKLimit.stochasticallyDominates_of_cylinderDominates
    (cylinderDominates_of_mem_dlrMeasures_local_lower exh Φ hq hp hμ r hlocal)

/-- Full upper stochastic comparison for a countable labelled edge space. -/
theorem stochasticallyDominates_of_mem_dlrMeasures_local_upper
    {E : Type*} [Countable E] (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (r : E → unitInterval)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => r e.1))) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ :=
  FKLimit.stochasticallyDominates_of_cylinderDominates
    (cylinderDominates_of_mem_dlrMeasures_local_upper exh Φ hq hp hμ r hlocal)

/-- Two-sided local comparisons pass to an arbitrary DLR law without assuming
that its exterior marginal is a Bernoulli product. -/
theorem two_sided_stochasticallyDominates_of_mem_dlrMeasures_local
    {E : Type*} [Countable E] (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (lower upper : E → unitInterval)
    (hLower : ∀ n η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => lower e.1))
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η)))
    (hUpper : ∀ n η, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => upper e.1))) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct lower) ∧
      FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct upper) μ :=
  ⟨stochasticallyDominates_of_mem_dlrMeasures_local_lower exh Φ hq hp hμ lower hLower,
    stochasticallyDominates_of_mem_dlrMeasures_local_upper exh Φ hq hp hμ upper hUpper⟩

/-- Scale-dependent interior comparisons pass to every DLR law when the
comparison products eventually agree on each fixed cylinder. -/
theorem cylinderDominates_of_mem_dlrMeasures_eventually_lower
    {E : Type*} (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (rs : ℕ → E → unitInterval)
    (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in Filter.atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))) :
    FKLimit.CylinderDominates μ (FKLimit.bernoulliProduct r) := by
  intro A S hdep hAupper
  obtain ⟨n, hnS, hnr⟩ := ((exh.eventually_subset S).and (hrs A S hdep)).exists
  rw [← hnr]
  exact (exh.box n).apply_le_of_isDLR_local_lower hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ (hμ n) (rs n) (hlocal n) hdep.measurableSet hAupper
      (hdep.mono hnS)

/-- The upper companion of scale-dependent DLR cylinder transport. -/
theorem cylinderDominates_of_mem_dlrMeasures_eventually_upper
    {E : Type*} (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (rs : ℕ → E → unitInterval)
    (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in Filter.atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))) :
    FKLimit.CylinderDominates (FKLimit.bernoulliProduct r) μ := by
  intro A S hdep hAupper
  obtain ⟨n, hnS, hnr⟩ := ((exh.eventually_subset S).and (hrs A S hdep)).exists
  rw [← hnr]
  exact (exh.box n).le_apply_of_isDLR_local_upper hq hp (Φ.partition n)
    (Φ.measurable_partition n) μ (hμ n) (rs n) (hlocal n) hdep.measurableSet hAupper
      (hdep.mono hnS)

/-- Full stochastic lower comparison from scale-dependent local inputs. -/
theorem stochasticallyDominates_of_mem_dlrMeasures_eventually_lower
    {E : Type*} [Countable E] (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (rs : ℕ → E → unitInterval)
    (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in Filter.atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) :=
  FKLimit.stochasticallyDominates_of_cylinderDominates
    (cylinderDominates_of_mem_dlrMeasures_eventually_lower exh Φ hq hp hμ rs r hrs hlocal)

/-- Full stochastic upper comparison from scale-dependent local inputs. -/
theorem stochasticallyDominates_of_mem_dlrMeasures_eventually_upper
    {E : Type*} [Countable E] (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (rs : ℕ → E → unitInterval)
    (r : E → unitInterval)
    (hrs : ∀ A S, FKLimit.DependsOnCoordinates A S → ∀ᶠ n in Filter.atTop,
      FKLimit.bernoulliProduct (rs n) A = FKLimit.bernoulliProduct r A)
    (hlocal : ∀ n η, FKEnhancement.StochasticallyDominates
      ((exh.box n).graph.fkMeasure hq hp (Φ.partition n η))
      (FKEnhancement.bernoulliProduct (fun e : (exh.box n).edges => rs n e.1))) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ :=
  FKLimit.stochasticallyDominates_of_cylinderDominates
    (cylinderDominates_of_mem_dlrMeasures_eventually_upper exh Φ hq hp hμ rs r hrs hlocal)

end

end FK.InfiniteVolume

#print axioms FK.InfiniteVolume.FiniteBox.apply_le_of_isDLR_local_lower
#print axioms FK.InfiniteVolume.FiniteBox.le_apply_of_isDLR_local_upper
#print axioms FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_local_lower
#print axioms FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_local_upper
#print axioms FK.InfiniteVolume.two_sided_stochasticallyDominates_of_mem_dlrMeasures_local
#print axioms FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_eventually_lower
#print axioms FK.InfiniteVolume.stochasticallyDominates_of_mem_dlrMeasures_eventually_upper
