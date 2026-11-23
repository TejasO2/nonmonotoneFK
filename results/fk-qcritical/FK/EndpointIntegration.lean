import FK.InfiniteVolume
import FK.EssentialWindow
import FK.PhasesCoordinate

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.MainIntegration.Endpoint

open FK.InfiniteVolume

/-- The deterministic all-closed law on a configuration space. -/
noncomputable def closedLaw (E : Type*) : ProbabilityMeasure (E → Bool) :=
  ⟨Measure.dirac (fun _ ↦ false), inferInstance⟩

/-- The deterministic all-open law on a configuration space. -/
noncomputable def openLaw (E : Type*) : ProbabilityMeasure (E → Bool) :=
  ⟨Measure.dirac (fun _ ↦ true), inferInstance⟩

/-- One zero-rate finite-box conditional law is the point mass obtained by
keeping the exterior and closing every interior edge. -/
theorem conditionalLaw_zero {E : Type*} (B : FiniteBox E) {q : NNReal} (hq : 0 < q)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) :
    B.conditionalLaw hq (p := 0) bot_le α η =
      ⟨Measure.dirac (B.glue (η, fun _ ↦ false)), inferInstance⟩ := by
  apply Subtype.ext
  simp only [FiniteBox.conditionalLaw, FK.Finite.LabelledMultigraph.fkMeasure,
    FK.Finite.LabelledMultigraph.fkPMF_zero]
  rw [PMF.toMeasure_pure, Measure.map_dirac' (B.measurable_glue_const_left η)]
  rfl

/-- At zero rate, every finite-volume law in a finite-box exhaustion is the
all-closed point mass. -/
theorem finiteVolumeLaw_zero {E : Type*} (B : FiniteBox E) {q : NNReal} (hq : 0 < q)
    (ξ : B.BoundaryPartition) :
    B.finiteVolumeLaw hq (p := 0) bot_le ξ = closedLaw E := by
  rw [FiniteBox.finiteVolumeLaw, conditionalLaw_zero B hq]
  apply Subtype.ext
  change Measure.dirac (B.glue (B.closedExterior, fun _ ↦ false)) =
    Measure.dirac (fun _ : E ↦ false)
  congr 1
  funext e
  by_cases he : e ∈ B.edges <;> simp [FiniteBox.glue, he, FiniteBox.closedExterior]

/-- One unit-rate finite-box conditional law is the point mass obtained by
keeping the exterior and opening every interior edge. -/
theorem conditionalLaw_one {E : Type*} (B : FiniteBox E) {q : NNReal} (hq : 0 < q)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) :
    B.conditionalLaw hq (p := 1) le_rfl α η =
      ⟨Measure.dirac (B.glue (η, fun _ ↦ true)), inferInstance⟩ := by
  apply Subtype.ext
  simp only [FiniteBox.conditionalLaw, FK.Finite.LabelledMultigraph.fkMeasure,
    FK.Finite.LabelledMultigraph.fkPMF_one]
  rw [PMF.toMeasure_pure, Measure.map_dirac' (B.measurable_glue_const_left η)]
  rfl

lemma measurableSet_open {E : Type*} (e : E) :
    MeasurableSet {ω : E → Bool | ω e = true} :=
  (measurableSet_singleton true).preimage (measurable_pi_apply e)

lemma measurableSet_closed {E : Type*} (e : E) :
    MeasurableSet {ω : E → Bool | ω e = false} :=
  (measurableSet_singleton false).preimage (measurable_pi_apply e)

lemma closedLaw_apply_open {E : Type*} (e : E) :
    (closedLaw E : Measure (E → Bool)) {ω | ω e = true} = 0 := by
  have hm := measurableSet_open e
  simp [closedLaw, Measure.dirac_apply', hm]

lemma openLaw_apply_closed {E : Type*} (e : E) :
    (openLaw E : Measure (E → Bool)) {ω | ω e = false} = 0 := by
  have hm := measurableSet_closed e
  simp [openLaw, Measure.dirac_apply', hm]

/-- A zero-rate conditional law closes every coordinate in the box. -/
theorem conditionalLaw_zero_apply_open {E : Type*} (B : FiniteBox E)
    {q : NNReal} (hq : 0 < q) (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {e : E} (he : e ∈ B.edges) :
    (B.conditionalLaw hq (p := 0) bot_le α η : Measure (E → Bool)) {ω | ω e = true} = 0 := by
  have hm := measurableSet_open e
  rw [conditionalLaw_zero B hq]
  simp [Measure.dirac_apply', hm, FiniteBox.glue, he]

/-- A unit-rate conditional law opens every coordinate in the box. -/
theorem conditionalLaw_one_apply_closed {E : Type*} (B : FiniteBox E)
    {q : NNReal} (hq : 0 < q) (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {e : E} (he : e ∈ B.edges) :
    (B.conditionalLaw hq (p := 1) le_rfl α η : Measure (E → Bool)) {ω | ω e = false} = 0 := by
  have hm := measurableSet_closed e
  rw [conditionalLaw_one B hq]
  simp [Measure.dirac_apply', hm, FiniteBox.glue, he]

/-- A DLR law at zero rate has vanishing mass at every open coordinate. -/
theorem dlr_apply_open_zero {E : Type*} (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {q : NNReal} (hq : 0 < q)
    {μ : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ DLRMeasures exh Φ hq (p := 0) bot_le) (e : E) :
    (μ : Measure (E → Bool)) {ω | ω e = true} = 0 := by
  obtain ⟨n, hn⟩ := exh.covers e
  have hm := measurableSet_open e
  rw [(exh.box n).apply_of_isDLR hq bot_le (Φ.partition n) (Φ.measurable_partition n)
    μ (hμ n) hm]
  simp [conditionalLaw_zero_apply_open (exh.box n) hq (Φ.partition n) _ hn]

/-- A DLR law at unit rate has vanishing mass at every closed coordinate. -/
theorem dlr_apply_closed_one {E : Type*} (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {q : NNReal} (hq : 0 < q)
    {μ : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ DLRMeasures exh Φ hq (p := 1) le_rfl) (e : E) :
    (μ : Measure (E → Bool)) {ω | ω e = false} = 0 := by
  obtain ⟨n, hn⟩ := exh.covers e
  have hm := measurableSet_closed e
  rw [(exh.box n).apply_of_isDLR hq le_rfl (Φ.partition n) (Φ.measurable_partition n)
    μ (hμ n) hm]
  simp [conditionalLaw_one_apply_closed (exh.box n) hq (Φ.partition n) _ hn]

lemma isClopen_open {E : Type*} (e : E) : IsClopen {ω : E → Bool | ω e = true} :=
  (isClopen_discrete {true}).preimage (continuous_apply e)

lemma isClopen_closed {E : Type*} (e : E) : IsClopen {ω : E → Bool | ω e = false} :=
  (isClopen_discrete {false}).preimage (continuous_apply e)

/-- An FK weak limit at zero rate has vanishing mass at every open coordinate. -/
theorem fkLimit_apply_open_zero {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q : NNReal} (hq : 0 < q) (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (E → Bool)}
    (hμ : IsFKLimit exh hq (p := 0) bot_le α μ) (e : E) :
    (μ : Measure (E → Bool)) {ω | ω e = true} = 0 := by
  let A : Set (E → Bool) := {ω | ω e = true}
  let μs : ℕ → ProbabilityMeasure (E → Bool) := fun n ↦
    (exh.box n).finiteVolumeLaw hq (p := 0) bot_le (α n)
  change Tendsto μs atTop (𝓝 μ) at hμ
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (isClopen_open e)
  change Tendsto (fun n ↦ ENNReal.toNNReal (((μs n : ProbabilityMeasure (E → Bool)) :
    Measure (E → Bool)) A)) atTop (𝓝 (ENNReal.toNNReal (((μ : Measure (E → Bool)) A)))) at ht
  have hev : ∀ᶠ n in atTop, ENNReal.toNNReal (((μs n : ProbabilityMeasure (E → Bool)) :
      Measure (E → Bool)) A) = 0 := by
    apply Filter.Eventually.of_forall
    intro n
    dsimp [μs]
    rw [finiteVolumeLaw_zero (exh.box n) hq (α n)]
    rw [show A = {ω : E → Bool | ω e = true} from rfl, closedLaw_apply_open]
    rfl
  have hzero : ENNReal.toNNReal (((μ : Measure (E → Bool)) A)) = 0 :=
    tendsto_nhds_unique ht (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds)
  exact (((ENNReal.toNNReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _))

/-- An FK weak limit at unit rate has vanishing mass at every closed coordinate. -/
theorem fkLimit_apply_closed_one {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q : NNReal} (hq : 0 < q) (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (E → Bool)}
    (hμ : IsFKLimit exh hq (p := 1) le_rfl α μ) (e : E) :
    (μ : Measure (E → Bool)) {ω | ω e = false} = 0 := by
  let A : Set (E → Bool) := {ω | ω e = false}
  let μs : ℕ → ProbabilityMeasure (E → Bool) := fun n ↦
    (exh.box n).finiteVolumeLaw hq (p := 1) le_rfl (α n)
  change Tendsto μs atTop (𝓝 μ) at hμ
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ (isClopen_closed e)
  change Tendsto (fun n ↦ ENNReal.toNNReal (((μs n : ProbabilityMeasure (E → Bool)) :
    Measure (E → Bool)) A)) atTop (𝓝 (ENNReal.toNNReal (((μ : Measure (E → Bool)) A)))) at ht
  have hev : ∀ᶠ n in atTop, ENNReal.toNNReal (((μs n : ProbabilityMeasure (E → Bool)) :
      Measure (E → Bool)) A) = 0 := by
    filter_upwards [exh.eventually_mem e] with n hn
    dsimp [μs]
    change ENNReal.toNNReal ((((exh.box n).conditionalLaw hq (p := 1) le_rfl (fun _ ↦ α n)
      (exh.box n).closedExterior : ProbabilityMeasure (E → Bool)) : Measure (E → Bool)) A) = 0
    rw [show A = {ω : E → Bool | ω e = false} from rfl,
      conditionalLaw_one_apply_closed (exh.box n) hq _ _ hn]
    rfl
  have hzero : ENNReal.toNNReal (((μ : Measure (E → Bool)) A)) = 0 :=
    tendsto_nhds_unique ht (Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds)
  exact (((ENNReal.toNNReal_eq_zero_iff _).mp hzero).resolve_right (measure_ne_top _ _))

/-- A probability law whose coordinates are almost surely all closed is the
all-closed point mass. -/
theorem eq_closedLaw_of_ae_closed {E : Type*} {μ : ProbabilityMeasure (E → Bool)}
    (h : ∀ᵐ ω ∂(μ : Measure (E → Bool)), ∀ e, ω e = false) : μ = closedLaw E := by
  apply Subtype.ext
  refine Measure.ext ?_
  intro A hA
  change (μ : Measure (E → Bool)) A = Measure.dirac (fun _ ↦ false) A
  rw [Measure.dirac_apply' _ hA]
  by_cases h0 : (fun _ : E ↦ false) ∈ A
  · have h' : ∀ᵐ ω ∂(μ : Measure (E → Bool)), ω ∈ A := by
      filter_upwards [h] with ω hω
      have heq : ω = fun _ ↦ false := funext hω
      simpa only [heq] using h0
    have hm := (ae_mem_iff_measure_eq hA.nullMeasurableSet).mp h'
    rw [Set.indicator_of_mem h0]
    simpa using hm
  · have h' : ∀ᵐ ω ∂(μ : Measure (E → Bool)), ω ∉ A := by
      filter_upwards [h] with ω hω hωA
      have heq : ω = fun _ ↦ false := funext hω
      exact h0 (by simpa only [← heq] using hωA)
    have hm : (μ : Measure (E → Bool)) A = 0 := by
      simpa using (ae_iff.mp h')
    rw [Set.indicator_of_notMem h0, hm]

/-- A probability law whose coordinates are almost surely all open is the
all-open point mass. -/
theorem eq_openLaw_of_ae_open {E : Type*} {μ : ProbabilityMeasure (E → Bool)}
    (h : ∀ᵐ ω ∂(μ : Measure (E → Bool)), ∀ e, ω e = true) : μ = openLaw E := by
  apply Subtype.ext
  refine Measure.ext ?_
  intro A hA
  change (μ : Measure (E → Bool)) A = Measure.dirac (fun _ ↦ true) A
  rw [Measure.dirac_apply' _ hA]
  by_cases h0 : (fun _ : E ↦ true) ∈ A
  · have h' : ∀ᵐ ω ∂(μ : Measure (E → Bool)), ω ∈ A := by
      filter_upwards [h] with ω hω
      have heq : ω = fun _ ↦ true := funext hω
      simpa only [heq] using h0
    have hm := (ae_mem_iff_measure_eq hA.nullMeasurableSet).mp h'
    rw [Set.indicator_of_mem h0]
    simpa using hm
  · have h' : ∀ᵐ ω ∂(μ : Measure (E → Bool)), ω ∉ A := by
      filter_upwards [h] with ω hω hωA
      have heq : ω = fun _ ↦ true := funext hω
      exact h0 (by simpa only [← heq] using hωA)
    have hm : (μ : Measure (E → Bool)) A = 0 := by
      simpa using (ae_iff.mp h')
    rw [Set.indicator_of_notMem h0, hm]

/-- Every FK weak-limit or coherent-convention Gibbs law at zero rate is the
all-closed point mass. -/
theorem limitOrGibbs_eq_closedLaw_zero {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q) {μ : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ LimitOrGibbsMeasures exh hq (p := 0) bot_le) : μ = closedLaw E := by
  apply eq_closedLaw_of_ae_closed
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  rcases hμ with hμ | ⟨Φ, hμ⟩
  · obtain ⟨α, hα⟩ := hμ
    simpa using fkLimit_apply_open_zero exh hq α hα e
  · simpa using dlr_apply_open_zero exh Φ.toBoundaryAssignment hq hμ e

/-- Every FK weak-limit or coherent-convention Gibbs law at unit rate is the
all-open point mass. -/
theorem limitOrGibbs_eq_openLaw_one {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q : NNReal} (hq : 0 < q) {μ : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ LimitOrGibbsMeasures exh hq (p := 1) le_rfl) : μ = openLaw E := by
  apply eq_openLaw_of_ae_open
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  rcases hμ with hμ | ⟨Φ, hμ⟩
  · obtain ⟨α, hα⟩ := hμ
    simpa using fkLimit_apply_closed_one exh hq α hα e
  · simpa using dlr_apply_closed_one exh Φ.toBoundaryAssignment hq hμ e

/-- The zero-rate Bernoulli product is the all-closed point mass. -/
theorem bernoulliProduct_zero_eq_closedLaw {E : Type*} [Countable E] :
    FK.Phases.bernoulliProduct (fun _ : E ↦ (0 : unitInterval)) = closedLaw E := by
  apply eq_closedLaw_of_ae_closed
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  have h := FK.Phases.bernoulliProduct_apply_open (fun _ : E ↦ (0 : unitInterval)) e
  simpa using h

/-- The unit-rate Bernoulli product is the all-open point mass. -/
theorem bernoulliProduct_one_eq_openLaw {E : Type*} [Countable E] :
    FK.Phases.bernoulliProduct (fun _ : E ↦ (1 : unitInterval)) = openLaw E := by
  apply eq_openLaw_of_ae_open
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  have h := FK.Phases.bernoulliProduct_apply_closed (fun _ : E ↦ (1 : unitInterval)) e
  simpa using h

/-- Both phase profiles are identically zero at `p = 0`. -/
theorem lowerWeights_zero {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {q : ℝ} (hq : 0 < q) :
    FK.Phases.lowerWeights Eb Ee n m (p := (0 : ℝ)) le_rfl zero_le_one hq =
      fun _ ↦ (0 : unitInterval) := by
  funext e
  apply Subtype.ext
  simp [FK.Phases.lowerWeights, FK.Phases.lowerWeightsReal, FK.Enhancement.fkPrime,
    FK.Enhancement.cutsetEnhancement]

/-- Both phase profiles are identically zero at `p = 0`. -/
theorem upperWeights_zero {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {q : ℝ} (hq : 0 < q) :
    FK.Phases.upperWeights Eb Ee n m (p := (0 : ℝ)) le_rfl zero_le_one hq =
      fun _ ↦ (0 : unitInterval) := by
  funext e
  apply Subtype.ext
  simp [FK.Phases.upperWeights, FK.Phases.upperWeightsReal, FK.Enhancement.fkPrime,
    FK.Enhancement.pathEnhancement]

/-- Both phase profiles are identically one at `p = 1`. -/
theorem lowerWeights_one {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {q : ℝ} (hq : 0 < q) :
    FK.Phases.lowerWeights Eb Ee n m (p := (1 : ℝ)) zero_le_one le_rfl hq =
      fun _ ↦ (1 : unitInterval) := by
  funext e
  apply Subtype.ext
  simp [FK.Phases.lowerWeights, FK.Phases.lowerWeightsReal, FK.Enhancement.fkPrime,
    FK.Enhancement.cutsetEnhancement]

/-- Both phase profiles are identically one at `p = 1`. -/
theorem upperWeights_one {E : Type*} (Eb Ee : Set E) (n m : ℕ)
    {q : ℝ} (hq : 0 < q) :
    FK.Phases.upperWeights Eb Ee n m (p := (1 : ℝ)) zero_le_one le_rfl hq =
      fun _ ↦ (1 : unitInterval) := by
  funext e
  apply Subtype.ext
  simp [FK.Phases.upperWeights, FK.Phases.upperWeightsReal, FK.Enhancement.fkPrime,
    FK.Enhancement.pathEnhancement]

/-- The two enhanced stochastic comparisons are automatic at `p = 0`, for
arbitrary enhanced sets and for the full FK-limit/Gibbs union. -/
theorem comparison_zero_of_mem_limitOrGibbs {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Eb Ee : Set E) (n m : ℕ)
    {q : NNReal} (hq : 0 < q) (hqR : (0 : ℝ) < (q : ℝ))
    {μ : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ LimitOrGibbsMeasures exh hq (p := 0) bot_le) :
    FK.Phases.StochLe (FK.Phases.bernoulliProduct
      (FK.Phases.lowerWeights Eb Ee n m (p := (0 : ℝ)) le_rfl zero_le_one
        hqR)) μ ∧
    FK.Phases.StochLe μ (FK.Phases.bernoulliProduct
      (FK.Phases.upperWeights Eb Ee n m (p := (0 : ℝ)) le_rfl zero_le_one
        hqR)) := by
  have hl : FK.Phases.bernoulliProduct
      (FK.Phases.lowerWeights Eb Ee n m (p := (0 : ℝ)) le_rfl zero_le_one hqR) =
        closedLaw E := by
    rw [lowerWeights_zero Eb Ee n m hqR]
    exact bernoulliProduct_zero_eq_closedLaw
  have hu : FK.Phases.bernoulliProduct
      (FK.Phases.upperWeights Eb Ee n m (p := (0 : ℝ)) le_rfl zero_le_one hqR) =
        closedLaw E := by
    rw [upperWeights_zero Eb Ee n m hqR]
    exact bernoulliProduct_zero_eq_closedLaw
  rw [hl, hu, limitOrGibbs_eq_closedLaw_zero exh hq hμ]
  exact ⟨FK.Phases.StochLe.refl _, FK.Phases.StochLe.refl _⟩

/-- The two enhanced stochastic comparisons are automatic at `p = 1`, for
arbitrary enhanced sets and for the full FK-limit/Gibbs union. -/
theorem comparison_one_of_mem_limitOrGibbs {E : Type*} [Countable E]
    (exh : BoxExhaustion E) (Eb Ee : Set E) (n m : ℕ)
    {q : NNReal} (hq : 0 < q) (hqR : (0 : ℝ) < (q : ℝ))
    {μ : ProbabilityMeasure (E → Bool)}
    (hμ : μ ∈ LimitOrGibbsMeasures exh hq (p := 1) le_rfl) :
    FK.Phases.StochLe (FK.Phases.bernoulliProduct
      (FK.Phases.lowerWeights Eb Ee n m (p := (1 : ℝ)) zero_le_one le_rfl
        hqR)) μ ∧
    FK.Phases.StochLe μ (FK.Phases.bernoulliProduct
      (FK.Phases.upperWeights Eb Ee n m (p := (1 : ℝ)) zero_le_one le_rfl
        hqR)) := by
  have hl : FK.Phases.bernoulliProduct
      (FK.Phases.lowerWeights Eb Ee n m (p := (1 : ℝ)) zero_le_one le_rfl hqR) =
        openLaw E := by
    rw [lowerWeights_one Eb Ee n m hqR]
    exact bernoulliProduct_one_eq_openLaw
  have hu : FK.Phases.bernoulliProduct
      (FK.Phases.upperWeights Eb Ee n m (p := (1 : ℝ)) zero_le_one le_rfl hqR) =
        openLaw E := by
    rw [upperWeights_one Eb Ee n m hqR]
    exact bernoulliProduct_one_eq_openLaw
  rw [hl, hu, limitOrGibbs_eq_openLaw_one exh hq hμ]
  exact ⟨FK.Phases.StochLe.refl _, FK.Phases.StochLe.refl _⟩

end FK.MainIntegration.Endpoint
