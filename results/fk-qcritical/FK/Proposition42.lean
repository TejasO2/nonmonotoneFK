import Mathlib

/-!
# Infinite-volume limit infrastructure for enhanced FK comparisons

This file formalizes the measure-theoretic part of the passage to the limit in
Section 4 of arXiv:2512.16486.  Configurations use the pointwise order on
`E → Bool`; `true` denotes an open edge.  Bernoulli products are the actual
projective-limit product measures, not an axiomatized family.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FKLimit

/-- Edge configurations, ordered pointwise. -/
abbrev Configuration (E : Type*) := E → Bool

/-- The inhomogeneous Bernoulli bond-percolation measure with open-edge
probabilities `r`. -/
noncomputable def bernoulliProduct {E : Type*} (r : E → unitInterval) :
    ProbabilityMeasure (Configuration E) :=
  ⟨Measure.infinitePi (fun e ↦ bernoulliMeasure true false (r e)), inferInstance⟩

/-- An event depending only on the coordinates in the finite set `S`. -/
def DependsOnCoordinates {E : Type*} (A : Set (Configuration E)) (S : Finset E) : Prop :=
  ∀ ω η : Configuration E, (∀ e ∈ S, ω e = η e) → (ω ∈ A ↔ η ∈ A)

lemma DependsOnCoordinates.mono {E : Type*} {A : Set (Configuration E)}
    {S T : Finset E} (h : DependsOnCoordinates A S) (hST : S ⊆ T) :
    DependsOnCoordinates A T := by
  intro ω η he
  exact h ω η (fun e heS ↦ he e (hST heS))

lemma dependsOnCoordinates_empty {E : Type*} {A : Set (Configuration E)}
    (h : A = ∅ ∨ A = Set.univ) : DependsOnCoordinates A ∅ := by
  rcases h with rfl | rfl <;> simp [DependsOnCoordinates]

/-- A finitely supported event is the pullback of its restriction image. -/
lemma eq_preimage_restrict_image {E : Type*} {A : Set (Configuration E)} {S : Finset E}
    (hA : DependsOnCoordinates A S) :
    A = S.restrict ⁻¹' (S.restrict '' A) := by
  ext ω
  constructor
  · intro hω
    exact ⟨ω, hω, rfl⟩
  · rintro ⟨η, hηA, hηω⟩
    apply (hA ω η ?_).2 hηA
    intro e he
    exact (congrFun hηω ⟨e, he⟩).symm

lemma continuous_finsetRestrict {E : Type*} (S : Finset E) :
    Continuous (S.restrict (π := fun _ : E ↦ Bool)) := by
  exact continuous_pi (fun e ↦ continuous_apply e.1)

/-- Finite-dimensional events are clopen in the product topology. -/
lemma DependsOnCoordinates.isClopen {E : Type*} {A : Set (Configuration E)} {S : Finset E}
    (hA : DependsOnCoordinates A S) : IsClopen A := by
  rw [eq_preimage_restrict_image hA]
  exact (isClopen_discrete _).preimage (continuous_finsetRestrict S)

lemma DependsOnCoordinates.measurableSet {E : Type*} {A : Set (Configuration E)}
    {S : Finset E} (hA : DependsOnCoordinates A S) : MeasurableSet A := by
  rw [eq_preimage_restrict_image hA]
  exact MeasurableSet.of_discrete.preimage S.measurable_restrict

/-- The probability of a finitely supported event depends only on the
Bernoulli parameters at those coordinates. -/
lemma bernoulliProduct_apply_eq_of_dependsOn {E : Type*}
    {A : Set (Configuration E)} {S : Finset E} (hA : DependsOnCoordinates A S)
    {r s : E → unitInterval} (hrs : ∀ e ∈ S, r e = s e) :
    bernoulliProduct r A = bernoulliProduct s A := by
  have hmap :
      (bernoulliProduct r : Measure (Configuration E)).map S.restrict =
        (bernoulliProduct s : Measure (Configuration E)).map S.restrict := by
    change Measure.map S.restrict (Measure.infinitePi
      (fun e ↦ bernoulliMeasure true false (r e))) =
        Measure.map S.restrict (Measure.infinitePi
          (fun e ↦ bernoulliMeasure true false (s e)))
    rw [Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
    congr 1
    funext e
    rw [hrs e.1 e.2]
  have happly (t : E → unitInterval) :
      (bernoulliProduct t : Measure (Configuration E)) A =
        ((bernoulliProduct t : Measure (Configuration E)).map S.restrict)
          (S.restrict '' A) := by
    rw [Measure.map_apply S.measurable_restrict MeasurableSet.of_discrete]
    exact congrArg (fun B ↦ (bernoulliProduct t : Measure (Configuration E)) B)
      (eq_preimage_restrict_image hA)
  change ((bernoulliProduct r : Measure (Configuration E)) A).toNNReal =
    ((bernoulliProduct s : Measure (Configuration E)) A).toNNReal
  rw [happly r, happly s]
  exact congrArg (fun m : Measure ((e : ↥S) → Bool) ↦ (m (S.restrict '' A)).toNNReal) hmap

/-- Stochastic domination tested on all measurable increasing events. -/
def StochasticallyDominates {E : Type*} (ν μ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∀ A : Set (Configuration E), MeasurableSet A → IsUpperSet A → μ A ≤ ν A

/-- Stochastic domination tested on finite-dimensional increasing events. -/
def CylinderDominates {E : Type*} (ν μ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∀ (A : Set (Configuration E)) (S : Finset E), DependsOnCoordinates A S →
    IsUpperSet A → μ A ≤ ν A

lemma CylinderDominates.of_stochasticallyDominates {E : Type*}
    {ν μ : ProbabilityMeasure (Configuration E)} (h : StochasticallyDominates ν μ) :
    CylinderDominates ν μ := by
  intro A S hAS hA
  exact h A hAS.measurableSet hA

/-- Cylinder domination is preserved by weak convergence of both sides. -/
lemma cylinderDominates_of_tendsto {E : Type*} [Countable E]
    {μs νs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hdom : ∀ n, CylinderDominates (νs n) (μs n)) : CylinderDominates ν μ := by
  intro A S hAS hA
  apply le_of_tendsto_of_tendsto'
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAS.isClopen)
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hAS.isClopen)
  intro n
  exact hdom n A S hAS hA

/-- The right hand side may instead converge by being eventually constant on
the coordinates of each fixed test event. -/
lemma cylinderDominates_of_tendsto_left_of_eventually_eq {E : Type*} [Countable E]
    {μs : ℕ → ProbabilityMeasure (Configuration E)} {rs : ℕ → E → unitInterval}
    {r : E → unitInterval} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hrs : ∀ A : Set (Configuration E), ∀ S : Finset E, DependsOnCoordinates A S →
      ∀ᶠ n in atTop, bernoulliProduct (rs n) A = bernoulliProduct r A)
    (hdom : ∀ n, CylinderDominates (bernoulliProduct (rs n)) (μs n)) :
    CylinderDominates (bernoulliProduct r) μ := by
  intro A S hAS hA
  have hright : Tendsto (fun n ↦ bernoulliProduct (rs n) A) atTop
      (𝓝 (bernoulliProduct r A)) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm (hrs A S hAS)) tendsto_const_nhds
  apply le_of_tendsto_of_tendsto
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAS.isClopen) hright
  filter_upwards [hrs A S hAS] with n hn
  simpa only [hn] using hdom n A S hAS hA

/-- A probability measure represented by a Markov kernel and a mixing law. -/
noncomputable def kernelMixture {α E : Type*} [MeasurableSpace α]
    (ρ : ProbabilityMeasure α) (κ : ProbabilityTheory.Kernel α (Configuration E))
    [IsMarkovKernel κ] : ProbabilityMeasure (Configuration E) :=
  ⟨Measure.bind (ρ : Measure α) κ,
    isProbabilityMeasure_bind κ.aemeasurable
      (Filter.Eventually.of_forall (fun _ ↦ inferInstance))⟩

/-- The measure at one point of a Markov kernel, as a probability measure. -/
noncomputable def kernelAt {α E : Type*} [MeasurableSpace α]
    (κ : ProbabilityTheory.Kernel α (Configuration E))
    [IsMarkovKernel κ] (x : α) : ProbabilityMeasure (Configuration E) :=
  ⟨κ x, inferInstance⟩

lemma ennreal_le_of_probabilityMeasure_apply_le {E : Type*}
    {ν μ : ProbabilityMeasure (Configuration E)} {A B : Set (Configuration E)}
    (h : ν A ≤ μ B) :
    (ν : Measure (Configuration E)) A ≤ (μ : Measure (Configuration E)) B := by
  exact (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h

/-- A common upper stochastic bound passes through arbitrary Markov-kernel
mixtures. -/
theorem kernelMixture_upper_bound {α E : Type*} [MeasurableSpace α]
    (ρ : ProbabilityMeasure α) (κ : ProbabilityTheory.Kernel α (Configuration E))
    [IsMarkovKernel κ]
    {ν : ProbabilityMeasure (Configuration E)}
    (hdom : ∀ x, StochasticallyDominates ν (kernelAt κ x)) :
    StochasticallyDominates ν (kernelMixture ρ κ) := by
  intro A hA hAup
  change ((Measure.bind (ρ : Measure α) κ) A).toNNReal ≤
    ((ν : Measure (Configuration E)) A).toNNReal
  have htop : (Measure.bind (ρ : Measure α) κ) A ≠ ⊤ :=
    measure_ne_top (kernelMixture ρ κ : Measure (Configuration E)) A
  rw [Measure.bind_apply hA κ.aemeasurable] at htop ⊢
  apply (ENNReal.toNNReal_le_toNNReal htop (measure_ne_top _ _)).mpr
  calc
    (∫⁻ x, κ x A ∂(ρ : Measure α)) ≤
        ∫⁻ _x, (ν : Measure (Configuration E)) A ∂(ρ : Measure α) := by
      apply lintegral_mono
      intro x
      exact ennreal_le_of_probabilityMeasure_apply_le (hdom x A hA hAup)
    _ = (ν : Measure (Configuration E)) A := by simp

/-- A common lower stochastic bound passes through arbitrary Markov-kernel
mixtures.  This is the measure-theoretic content needed when an extremal Gibbs
measure is represented as a mixture of FK limits. -/
theorem kernelMixture_lower_bound {α E : Type*} [MeasurableSpace α]
    (ρ : ProbabilityMeasure α) (κ : ProbabilityTheory.Kernel α (Configuration E))
    [IsMarkovKernel κ]
    {ν : ProbabilityMeasure (Configuration E)}
    (hdom : ∀ x, StochasticallyDominates (kernelAt κ x) ν) :
    StochasticallyDominates (kernelMixture ρ κ) ν := by
  intro A hA hAup
  change ((ν : Measure (Configuration E)) A).toNNReal ≤
    ((Measure.bind (ρ : Measure α) κ) A).toNNReal
  have htop : (Measure.bind (ρ : Measure α) κ) A ≠ ⊤ :=
    measure_ne_top (kernelMixture ρ κ : Measure (Configuration E)) A
  rw [Measure.bind_apply hA κ.aemeasurable] at htop ⊢
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) htop).mpr
  calc
    (ν : Measure (Configuration E)) A =
        ∫⁻ _x, (ν : Measure (Configuration E)) A ∂(ρ : Measure α) := by simp
    _ ≤ ∫⁻ x, κ x A ∂(ρ : Measure α) := by
      apply lintegral_mono
      intro x
      exact ennreal_le_of_probabilityMeasure_apply_le (hdom x A hA hAup)

/-- An increasing exhaustion by finite edge sets. -/
structure EdgeExhaustion (E : Type*) where
  box : ℕ → Finset E
  monotone : Monotone box
  covers : ∀ e : E, ∃ n, e ∈ box n

namespace EdgeExhaustion

variable {E : Type*} (exh : EdgeExhaustion E)

lemma eventually_mem (e : E) : ∀ᶠ n in atTop, e ∈ exh.box n := by
  obtain ⟨N, hN⟩ := exh.covers e
  filter_upwards [eventually_ge_atTop N] with n hn
  exact exh.monotone hn hN

lemma eventually_subset (S : Finset E) : ∀ᶠ n in atTop, S ⊆ exh.box n := by
  change ∀ᶠ n in atTop, ∀ e ∈ S, e ∈ exh.box n
  rw [Finset.eventually_all]
  exact fun e _ ↦ exh.eventually_mem e

end EdgeExhaustion

/-- `D e` is the device selected for an enhanced edge `e`.  Separation is
exactly the requirement that every auxiliary edge avoid the enhanced set. -/
def IsSeparatedDeviceFamily {E : Type*} (S : Set E) (D : E → Finset E) : Prop :=
  ∀ e ∈ S, e ∈ D e ∧ ∀ f ∈ D e, f ≠ e → f ∉ S

/-- Enhanced edges activated at scale `n`: their whole device is present and
any additional finite-volume admissibility condition holds. -/
noncomputable def activeEdges {E : Type*} (exh : EdgeExhaustion E) (S : Set E)
    (D : E → Finset E) (admissible : ℕ → E → Prop) (n : ℕ) : Finset E := by
  classical
  exact (exh.box n).filter (fun e ↦ e ∈ S ∧ D e ⊆ exh.box n ∧ admissible n e)

lemma mem_activeEdges {E : Type*} {exh : EdgeExhaustion E} {S : Set E}
    {D : E → Finset E} {admissible : ℕ → E → Prop} {n : ℕ} {e : E} :
    e ∈ activeEdges exh S D admissible n ↔
      e ∈ exh.box n ∧ e ∈ S ∧ D e ⊆ exh.box n ∧ admissible n e := by
  simp [activeEdges]

lemma activeEdges_subset {E : Type*} {exh : EdgeExhaustion E} {S : Set E}
    {D : E → Finset E} {admissible : ℕ → E → Prop} {n : ℕ} :
    (activeEdges exh S D admissible n : Set E) ⊆ S := by
  intro e he
  exact (mem_activeEdges.mp he).2.1

/-- Select `step` exactly on `S`, leaving the remaining parameters at `base`. -/
noncomputable def selectParameters {E : Type*} (base step : E → unitInterval)
    (S : Set E) : E → unitInterval := by
  classical
  exact fun e ↦ if e ∈ S then step e else base e

/-- The finite-volume parameters obtained by activating complete devices. -/
noncomputable def activeParameters {E : Type*} (exh : EdgeExhaustion E) (S : Set E)
    (D : E → Finset E) (admissible : ℕ → E → Prop) (base step : E → unitInterval)
    (n : ℕ) : E → unitInterval :=
  selectParameters base step (activeEdges exh S D admissible n)

/-- Every coordinate of the activated parameters eventually agrees with the
final enhanced parameters. -/
lemma activeParameters_eventually_eq {E : Type*} (exh : EdgeExhaustion E)
    (S : Set E) (D : E → Finset E) (admissible : ℕ → E → Prop)
    (base step : E → unitInterval) (hD : ∀ e ∈ S, e ∈ D e)
    (hadm : ∀ e ∈ S, ∀ᶠ n in atTop, admissible n e) (e : E) :
    ∀ᶠ n in atTop, activeParameters exh S D admissible base step n e =
      selectParameters base step S e := by
  by_cases he : e ∈ S
  · filter_upwards [exh.eventually_subset (D e), hadm e he] with n hn hna
    have hactive : e ∈ activeEdges exh S D admissible n := by
      exact mem_activeEdges.mpr ⟨hn (hD e he), he, hn, hna⟩
    simp [activeParameters, selectParameters, hactive, he]
  · have hnot : ∀ n, e ∉ activeEdges exh S D admissible n := by
      intro n hactive
      exact he (activeEdges_subset hactive)
    simp [activeParameters, selectParameters, hnot, he]

/-- The eventual coordinatewise statement above is enough to identify every
finite-dimensional Bernoulli probability in the limit. -/
lemma eventually_bernoulliProduct_active {E : Type*} (exh : EdgeExhaustion E)
    (S : Set E) (D : E → Finset E) (admissible : ℕ → E → Prop)
    (base step : E → unitInterval) (hD : ∀ e ∈ S, e ∈ D e)
    (hadm : ∀ e ∈ S, ∀ᶠ n in atTop, admissible n e)
    (A : Set (Configuration E)) (T : Finset E) (hAT : DependsOnCoordinates A T) :
    ∀ᶠ n in atTop,
      bernoulliProduct (activeParameters exh S D admissible base step n) A =
        bernoulliProduct (selectParameters base step S) A := by
  have hcoord : ∀ᶠ n in atTop, ∀ e ∈ T,
      activeParameters exh S D admissible base step n e =
        selectParameters base step S e := by
    rw [Finset.eventually_all]
    exact fun e _ ↦ activeParameters_eventually_eq exh S D admissible base step hD hadm e
  filter_upwards [hcoord] with n hn
  exact bernoulliProduct_apply_eq_of_dependsOn hAT hn

/-- Pass a finite-volume lower comparison to a weak FK limit.  `hdom` is the
fact supplied by the relevant finite enhancement proposition. -/
theorem cylinder_lower_bound_of_finiteVolume {E : Type*} [Countable E]
    (exh : EdgeExhaustion E) (S : Set E) (D : E → Finset E)
    (admissible : ℕ → E → Prop) (base step : E → unitInterval)
    (hD : ∀ e ∈ S, e ∈ D e) (hadm : ∀ e ∈ S, ∀ᶠ n in atTop, admissible n e)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hdom : ∀ n, CylinderDominates
      (bernoulliProduct (activeParameters exh S D admissible base step n)) (μs n)) :
    CylinderDominates (bernoulliProduct (selectParameters base step S)) μ := by
  apply cylinderDominates_of_tendsto_left_of_eventually_eq hμ
    (fun A T hAT ↦ eventually_bernoulliProduct_active exh S D admissible base step hD hadm A T hAT)
  exact hdom

/-- The corresponding passage for a finite-volume upper comparison. -/
theorem cylinder_upper_bound_of_finiteVolume {E : Type*} [Countable E]
    (exh : EdgeExhaustion E) (S : Set E) (D : E → Finset E)
    (admissible : ℕ → E → Prop) (base step : E → unitInterval)
    (hD : ∀ e ∈ S, e ∈ D e) (hadm : ∀ e ∈ S, ∀ᶠ n in atTop, admissible n e)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hdom : ∀ n, CylinderDominates (μs n)
      (bernoulliProduct (activeParameters exh S D admissible base step n))) :
    CylinderDominates μ (bernoulliProduct (selectParameters base step S)) := by
  intro A T hAT hA
  have hlim : Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAT.isClopen
  apply ge_of_tendsto hlim
  filter_upwards [eventually_bernoulliProduct_active
    exh S D admissible base step hD hadm A T hAT] with n hn
  rw [← hn]
  exact hdom n A T hAT hA

/-- A canonical edge exhaustion for a countable edge type, using lists to
avoid imposing any extra enumeration hypothesis. -/
noncomputable def encodableEdgeExhaustion (E : Type*) [Countable E] : EdgeExhaustion E := by
  classical
  letI := Encodable.ofCountable E
  refine
    { box := fun n ↦ ((List.range n).filterMap
        (fun i ↦ Encodable.decode (α := E) i)).toFinset
      monotone := ?_
      covers := ?_ }
  · intro m n hmn e he
    simp only [List.mem_toFinset, List.mem_filterMap, List.mem_range] at he ⊢
    obtain ⟨i, hi, hie⟩ := he
    exact ⟨i, lt_of_lt_of_le hi hmn, hie⟩
  · intro e
    refine ⟨Encodable.encode e + 1, ?_⟩
    simp only [List.mem_toFinset, List.mem_filterMap, List.mem_range]
    exact ⟨Encodable.encode e, Nat.lt_succ_self _, Encodable.encodek e⟩

/-- The set of configurations having the same restriction to `S` as some
configuration of `K`. -/
def restrictionNeighborhood {E : Type*} (K : Set (Configuration E)) (S : Finset E) :
    Set (Configuration E) :=
  S.restrict ⁻¹' (S.restrict '' K)

lemma dependsOnCoordinates_restrictionNeighborhood {E : Type*}
    (K : Set (Configuration E)) (S : Finset E) :
    DependsOnCoordinates (restrictionNeighborhood K S) S := by
  intro ω η hωη
  have hrestr : S.restrict ω = S.restrict η := funext (fun e ↦ hωη e.1 e.2)
  simp only [restrictionNeighborhood, Set.mem_preimage, hrestr]

lemma restrictionNeighborhood_mono {E : Type*} (K : Set (Configuration E))
    {S T : Finset E} (hST : S ⊆ T) :
    restrictionNeighborhood K T ⊆ restrictionNeighborhood K S := by
  rintro ω ⟨k, hk, hkω⟩
  refine ⟨k, hk, ?_⟩
  funext e
  exact congrFun hkω ⟨e.1, hST e.2⟩

lemma restrictionNeighborhood_isUpperSet {E : Type*} {K : Set (Configuration E)}
    (hK : IsUpperSet K) (S : Finset E) : IsUpperSet (restrictionNeighborhood K S) := by
  intro ω η hωη hω
  rcases hω with ⟨k, hk, hkω⟩
  refine ⟨k ⊔ η, hK le_sup_left hk, ?_⟩
  funext e
  change k e ⊔ η e = η e
  apply sup_eq_right.mpr
  have hke : k e = ω e := congrFun hkω e
  exact hke ▸ hωη e.1

lemma subset_restrictionNeighborhood {E : Type*} (K : Set (Configuration E))
    (S : Finset E) : K ⊆ restrictionNeighborhood K S := by
  intro ω hω
  exact ⟨ω, hω, rfl⟩

lemma iInter_restrictionNeighborhood {E : Type*} (exh : EdgeExhaustion E)
    {K : Set (Configuration E)} (hK : IsClosed K) :
    (⋂ n, restrictionNeighborhood K (exh.box n)) = K := by
  apply Set.Subset.antisymm
  · intro ω hω
    have hmem : ∀ n, ∃ k ∈ K, (exh.box n).restrict k = (exh.box n).restrict ω := by
      intro n
      exact Set.mem_iInter.mp hω n
    choose k hkK hkeq using hmem
    apply hK.mem_of_tendsto (b := atTop) (f := k) ?_ (Filter.Eventually.of_forall hkK)
    rw [tendsto_pi_nhds]
    intro e
    rw [nhds_discrete]
    apply Filter.tendsto_pure.mpr
    filter_upwards [exh.eventually_mem e] with n hn
    exact congrFun (hkeq n) ⟨e, hn⟩
  · intro ω hω
    apply Set.mem_iInter.mpr
    exact fun n ↦ ⟨ω, hω, rfl⟩

lemma tendsto_restrictionNeighborhood_measure {E : Type*} (exh : EdgeExhaustion E)
    (μ : ProbabilityMeasure (Configuration E)) {K : Set (Configuration E)}
    (hK : IsClosed K) :
    Tendsto (fun n ↦ μ (restrictionNeighborhood K (exh.box n))) atTop (𝓝 (μ K)) := by
  have hanti : Antitone (fun n ↦ restrictionNeighborhood K (exh.box n)) := by
    intro m n hmn
    exact restrictionNeighborhood_mono K (exh.monotone hmn)
  have hlim := tendsto_measure_iInter_atTop (μ := (μ : Measure (Configuration E)))
    (fun n ↦ (dependsOnCoordinates_restrictionNeighborhood K (exh.box n)).measurableSet.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [iInter_restrictionNeighborhood exh hK] at hlim
  have ht := (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure (Configuration E)) K)).comp hlim
  change Tendsto
    (fun n ↦ (((μ : Measure (Configuration E)) (restrictionNeighborhood K (exh.box n))).toNNReal))
    atTop (𝓝 (((μ : Measure (Configuration E)) K).toNNReal))
  simpa only [Function.comp_def] using ht

/-- Upper closure maps compact sets to compact sets in the Boolean
configuration lattice. -/
lemma isCompact_upperClosure {E : Type*} {K : Set (Configuration E)}
    (hK : IsCompact K) : IsCompact (↑(upperClosure K) : Set (Configuration E)) := by
  have heq : (↑(upperClosure K) : Set (Configuration E)) =
      (fun p : Configuration E × Configuration E ↦ p.1 ⊔ p.2) '' (K ×ˢ Set.univ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hax⟩ := mem_upperClosure.mp hx
      exact ⟨(a, x), ⟨ha, Set.mem_univ _⟩, sup_eq_right.mpr hax⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, _⟩, rfl⟩
      exact mem_upperClosure.mpr ⟨a, ha, le_sup_left⟩
  rw [heq]
  have hcont : Continuous (fun p : Configuration E × Configuration E ↦ p.1 ⊔ p.2) := by
    letI : ContinuousSup Bool := ⟨continuous_of_discreteTopology⟩
    apply continuous_pi
    intro e
    exact ((continuous_apply e).comp continuous_fst).sup
      ((continuous_apply e).comp continuous_snd)
  exact (hK.prod isCompact_univ).image hcont

/-- Cylinder domination extends to compact upper events. -/
lemma cylinderDominates_on_isCompact_upperSet {E : Type*} [Countable E]
    {ν μ : ProbabilityMeasure (Configuration E)} (hdom : CylinderDominates ν μ)
    {K : Set (Configuration E)} (hK : IsCompact K) (hKup : IsUpperSet K) : μ K ≤ ν K := by
  let exh := encodableEdgeExhaustion E
  have hμ := tendsto_restrictionNeighborhood_measure exh μ hK.isClosed
  have hν := tendsto_restrictionNeighborhood_measure exh ν hK.isClosed
  apply le_of_tendsto_of_tendsto' hμ hν
  intro n
  exact hdom (restrictionNeighborhood K (exh.box n)) (exh.box n)
    (dependsOnCoordinates_restrictionNeighborhood _ _)
    (restrictionNeighborhood_isUpperSet hKup _)

/-- On countable Boolean configuration spaces, testing finite-dimensional
upper events is sufficient for stochastic domination on every measurable upper
event. -/
theorem stochasticallyDominates_of_cylinderDominates {E : Type*} [Countable E]
    {ν μ : ProbabilityMeasure (Configuration E)} (hdom : CylinderDominates ν μ) :
    StochasticallyDominates ν μ := by
  intro A hA hAup
  have hcompact : ∀ K : Set (Configuration E), K ⊆ A → IsCompact K → μ K ≤ ν A := by
    intro K hKA hKc
    let U : Set (Configuration E) := ↑(upperClosure K)
    have hUsub : U ⊆ A := upperClosure_min hKA hAup
    have hUc : IsCompact U := isCompact_upperClosure hKc
    calc
      μ K ≤ μ U := ProbabilityMeasure.apply_mono μ subset_upperClosure
      _ ≤ ν U := cylinderDominates_on_isCompact_upperSet hdom hUc (upperClosure K).upper
      _ ≤ ν A := ProbabilityMeasure.apply_mono ν hUsub
  change ((μ : Measure (Configuration E)) A).toNNReal ≤
    ((ν : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [MeasurableSet.measure_eq_iSup_isCompact hA (μ : Measure (Configuration E))]
  refine iSup_le (fun K ↦ iSup_le (fun hKA ↦ iSup_le (fun hKc ↦ ?_)))
  exact ennreal_le_of_probabilityMeasure_apply_le (hcompact K hKA hKc)

/-- Weak convergence preserves full stochastic domination on countable
configuration spaces. -/
theorem stochasticallyDominates_of_tendsto {E : Type*} [Countable E]
    {μs νs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ ν : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hdom : ∀ n, StochasticallyDominates (νs n) (μs n)) :
    StochasticallyDominates ν μ := by
  apply stochasticallyDominates_of_cylinderDominates
  exact cylinderDominates_of_tendsto hμ hν
    (fun n ↦ CylinderDominates.of_stochasticallyDominates (hdom n))

/-- Full lower comparison for a weak limit of finite-volume FK measures. -/
theorem lower_bound_of_finiteVolume {E : Type*} [Countable E]
    (exh : EdgeExhaustion E) (S : Set E) (D : E → Finset E)
    (admissible : ℕ → E → Prop) (base step : E → unitInterval)
    (hD : ∀ e ∈ S, e ∈ D e) (hadm : ∀ e ∈ S, ∀ᶠ n in atTop, admissible n e)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hdom : ∀ n, CylinderDominates
      (bernoulliProduct (activeParameters exh S D admissible base step n)) (μs n)) :
    StochasticallyDominates (bernoulliProduct (selectParameters base step S)) μ := by
  exact stochasticallyDominates_of_cylinderDominates
    (cylinder_lower_bound_of_finiteVolume exh S D admissible base step hD hadm hμ hdom)

/-- Full upper comparison for a weak limit of finite-volume FK measures. -/
theorem upper_bound_of_finiteVolume {E : Type*} [Countable E]
    (exh : EdgeExhaustion E) (S : Set E) (D : E → Finset E)
    (admissible : ℕ → E → Prop) (base step : E → unitInterval)
    (hD : ∀ e ∈ S, e ∈ D e) (hadm : ∀ e ∈ S, ∀ᶠ n in atTop, admissible n e)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hdom : ∀ n, CylinderDominates (μs n)
      (bernoulliProduct (activeParameters exh S D admissible base step n))) :
    StochasticallyDominates μ (bernoulliProduct (selectParameters base step S)) := by
  exact stochasticallyDominates_of_cylinderDominates
    (cylinder_upper_bound_of_finiteVolume exh S D admissible base step hD hadm hμ hdom)

end FKLimit



/-!
# The explicit parameters in Proposition 4.2

The paper writes `p' = p / (p + q * (1 - p))`, and uses the uniform lower
bounds `|p' - p| * (1 - max(p,p'))^(Δ-1)` and
`|p' - p| * min(p,p')^(L-1)` for star and cycle devices.  This file proves
their parameter ranges and the algebraic sign dichotomy.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FKLimit

/-- The singleton conditional parameter from equation (2) of the paper. -/
noncomputable def fkSingletonParameter (p q : ℝ) : ℝ := p / (p + q * (1 - p))

/-- The uniform enhancement attached to star devices. -/
noncomputable def starEpsilon (p q : ℝ) (Delta : ℕ) : ℝ :=
  |fkSingletonParameter p q - p| * (1 - max p (fkSingletonParameter p q)) ^ (Delta - 1)

/-- The uniform enhancement attached to cycle devices of length `L`. -/
noncomputable def cycleEpsilon (p q : ℝ) (L : ℕ) : ℝ :=
  |fkSingletonParameter p q - p| * min p (fkSingletonParameter p q) ^ (L - 1)

lemma fkSingletonDenominator_pos {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    0 < p + q * (1 - p) := by
  rcases hp with ⟨hp0, hp1⟩
  positivity

lemma fkSingletonParameter_pos {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    0 < fkSingletonParameter p q := by
  exact div_pos hp.1 (fkSingletonDenominator_pos hp hq)

lemma fkSingletonParameter_lt_one {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    fkSingletonParameter p q < 1 := by
  rw [fkSingletonParameter, div_lt_one (fkSingletonDenominator_pos hp hq)]
  nlinarith [mul_pos hq (sub_pos.mpr hp.2)]

lemma fkSingletonParameter_sub_self {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    fkSingletonParameter p q - p = p * (1 - p) * (1 - q) / (p + q * (1 - p)) := by
  have hd : p + q * (1 - p) ≠ 0 := (fkSingletonDenominator_pos hp hq).ne'
  rw [fkSingletonParameter]
  field_simp
  <;> ring

lemma fkSingletonParameter_lt_self_iff {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    fkSingletonParameter p q < p ↔ 1 < q := by
  have hd := fkSingletonDenominator_pos hp hq
  have hfactor : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  constructor
  · intro h
    have hneg : fkSingletonParameter p q - p < 0 := sub_neg_of_lt h
    rw [fkSingletonParameter_sub_self hp hq] at hneg
    have hnum : p * (1 - p) * (1 - q) < 0 := by
      rcases div_neg_iff.mp hneg with hcase | hcase
      · exact (not_lt_of_ge hd.le hcase.2).elim
      · exact hcase.1
    have : 1 - q < 0 := neg_of_mul_neg_right hnum hfactor.le
    linarith
  · intro hq1
    apply lt_of_sub_neg
    rw [fkSingletonParameter_sub_self hp hq]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg hfactor (by linarith)) hd

lemma self_lt_fkSingletonParameter_iff {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    p < fkSingletonParameter p q ↔ q < 1 := by
  have hd := fkSingletonDenominator_pos hp hq
  have hfactor : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  constructor
  · intro h
    have hpos : 0 < fkSingletonParameter p q - p := sub_pos.mpr h
    rw [fkSingletonParameter_sub_self hp hq] at hpos
    have hnum : 0 < p * (1 - p) * (1 - q) := by
      rcases div_pos_iff.mp hpos with hcase | hcase
      · exact hcase.1
      · exact (not_lt_of_ge hd.le hcase.2).elim
    have : 0 < 1 - q := (mul_pos_iff_of_pos_left hfactor).mp hnum
    linarith
  · intro hq1
    apply sub_pos.mp
    rw [fkSingletonParameter_sub_self hp hq]
    exact div_pos (mul_pos hfactor (by linarith)) hd

lemma fkSingletonParameter_ne_self {p q : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hq : 0 < q) (hq1 : q ≠ 1) : fkSingletonParameter p q ≠ p := by
  intro heq
  rcases lt_or_gt_of_ne hq1 with hq1 | hq1
  · have := (self_lt_fkSingletonParameter_iff hp hq).2 hq1
    exact (ne_of_lt this) heq.symm
  · have := (fkSingletonParameter_lt_self_iff hp hq).2 hq1
    exact (ne_of_lt this) heq

lemma min_fkSingletonParameter_pos {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    0 < min p (fkSingletonParameter p q) :=
  lt_min hp.1 (fkSingletonParameter_pos hp hq)

lemma max_fkSingletonParameter_lt_one {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) :
    max p (fkSingletonParameter p q) < 1 :=
  max_lt hp.2 (fkSingletonParameter_lt_one hp hq)

lemma starEpsilon_pos {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (hq1 : q ≠ 1) (Delta : ℕ) : 0 < starEpsilon p q Delta := by
  rw [starEpsilon]
  apply mul_pos (abs_pos.mpr (sub_ne_zero.mpr (fkSingletonParameter_ne_self hp hq hq1)))
  exact pow_pos (sub_pos.mpr (max_fkSingletonParameter_lt_one hp hq)) _

lemma cycleEpsilon_pos {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (hq1 : q ≠ 1) (L : ℕ) : 0 < cycleEpsilon p q L := by
  rw [cycleEpsilon]
  apply mul_pos (abs_pos.mpr (sub_ne_zero.mpr (fkSingletonParameter_ne_self hp hq hq1)))
  exact pow_pos (min_fkSingletonParameter_pos hp hq) _

lemma starEpsilon_le_abs {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (Delta : ℕ) : starEpsilon p q Delta ≤ |fkSingletonParameter p q - p| := by
  rw [starEpsilon]
  apply mul_le_of_le_one_right (abs_nonneg _)
  have h0 : 0 ≤ 1 - max p (fkSingletonParameter p q) :=
    sub_nonneg.mpr (max_fkSingletonParameter_lt_one hp hq).le
  have h1 : 1 - max p (fkSingletonParameter p q) ≤ 1 := by
    have : 0 ≤ max p (fkSingletonParameter p q) := le_max_of_le_left hp.1.le
    linarith
  exact pow_le_one₀ h0 h1

lemma cycleEpsilon_le_abs {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (L : ℕ) : cycleEpsilon p q L ≤ |fkSingletonParameter p q - p| := by
  rw [cycleEpsilon]
  apply mul_le_of_le_one_right (abs_nonneg _)
  have h0 : 0 ≤ min p (fkSingletonParameter p q) := (min_fkSingletonParameter_pos hp hq).le
  have h1 : min p (fkSingletonParameter p q) ≤ 1 := by
    exact (min_le_left _ _).trans hp.2.le
  exact pow_le_one₀ h0 h1

lemma starEpsilon_nonneg {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (Delta : ℕ) : 0 ≤ starEpsilon p q Delta := by
  apply mul_nonneg (abs_nonneg _)
  exact pow_nonneg (sub_nonneg.mpr (max_fkSingletonParameter_lt_one hp hq).le) _

lemma cycleEpsilon_nonneg {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (L : ℕ) : 0 ≤ cycleEpsilon p q L := by
  apply mul_nonneg (abs_nonneg _)
  exact pow_nonneg (min_fkSingletonParameter_pos hp hq).le _

/-- Raise the parameter by `eps` on `S`. -/
noncomputable def raisedOn {E : Type*} (base eps : ℝ) (S : Set E) : E → ℝ := by
  classical
  exact fun e ↦ if e ∈ S then base + eps else base

/-- Lower the parameter by `eps` on `S`. -/
noncomputable def loweredOn {E : Type*} (base eps : ℝ) (S : Set E) : E → ℝ := by
  classical
  exact fun e ↦ if e ∈ S then base - eps else base

lemma raisedOn_mem_Icc {E : Type*} {base upper eps : ℝ} {S : Set E}
    (hbase0 : 0 ≤ base) (hupper1 : upper ≤ 1) (hbu : base ≤ upper)
    (heps0 : 0 ≤ eps) (heps : eps ≤ upper - base) (e : E) :
    raisedOn base eps S e ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  rw [raisedOn]
  split_ifs
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨hbase0, hbu.trans hupper1⟩

lemma loweredOn_mem_Icc {E : Type*} {base lower eps : ℝ} {S : Set E}
    (hlower0 : 0 ≤ lower) (hbase1 : base ≤ 1) (hlb : lower ≤ base)
    (heps0 : 0 ≤ eps) (heps : eps ≤ base - lower) (e : E) :
    loweredOn base eps S e ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  rw [loweredOn]
  split_ifs
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨hlower0.trans hlb, hbase1⟩

/-- Package a real-valued family known to lie in `[0,1]` as Bernoulli
parameters. -/
noncomputable def unitParameters {E : Type*} (r : E → ℝ)
    (h0 : ∀ e, 0 ≤ r e) (h1 : ∀ e, r e ≤ 1) : E → unitInterval :=
  fun e ↦ ⟨r e, h0 e, h1 e⟩

@[simp] lemma coe_unitParameters {E : Type*} (r : E → ℝ)
    (h0 : ∀ e, 0 ≤ r e) (h1 : ∀ e, r e ≤ 1) (e : E) :
    (unitParameters r h0 h1 e : ℝ) = r e := rfl

lemma raisedOn_star_mem_Icc_of_lt {E : Type*} {p q : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : p < fkSingletonParameter p q)
    (Delta : ℕ) (S : Set E) (e : E) :
    raisedOn p (starEpsilon p q Delta) S e ∈ Set.Icc (0 : ℝ) 1 := by
  apply raisedOn_mem_Icc hp.1.le (fkSingletonParameter_lt_one hp hq).le hpp.le
    (starEpsilon_nonneg hp hq Delta)
  calc
    starEpsilon p q Delta ≤ |fkSingletonParameter p q - p| := starEpsilon_le_abs hp hq Delta
    _ = fkSingletonParameter p q - p := abs_of_pos (sub_pos.mpr hpp)

lemma loweredOn_cycle_mem_Icc_of_lt {E : Type*} {p q : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : p < fkSingletonParameter p q)
    (L : ℕ) (S : Set E) (e : E) :
    loweredOn (fkSingletonParameter p q) (cycleEpsilon p q L) S e ∈ Set.Icc (0 : ℝ) 1 := by
  apply loweredOn_mem_Icc hp.1.le (fkSingletonParameter_lt_one hp hq).le hpp.le
    (cycleEpsilon_nonneg hp hq L)
  calc
    cycleEpsilon p q L ≤ |fkSingletonParameter p q - p| := cycleEpsilon_le_abs hp hq L
    _ = fkSingletonParameter p q - p := abs_of_pos (sub_pos.mpr hpp)

lemma raisedOn_cycle_mem_Icc_of_gt {E : Type*} {p q : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : fkSingletonParameter p q < p)
    (L : ℕ) (S : Set E) (e : E) :
    raisedOn (fkSingletonParameter p q) (cycleEpsilon p q L) S e ∈ Set.Icc (0 : ℝ) 1 := by
  apply raisedOn_mem_Icc (fkSingletonParameter_pos hp hq).le hp.2.le hpp.le
    (cycleEpsilon_nonneg hp hq L)
  calc
    cycleEpsilon p q L ≤ |fkSingletonParameter p q - p| := cycleEpsilon_le_abs hp hq L
    _ = p - fkSingletonParameter p q := by
      simpa only [neg_sub] using abs_of_neg (sub_neg.mpr hpp)

lemma loweredOn_star_mem_Icc_of_gt {E : Type*} {p q : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : fkSingletonParameter p q < p)
    (Delta : ℕ) (S : Set E) (e : E) :
    loweredOn p (starEpsilon p q Delta) S e ∈ Set.Icc (0 : ℝ) 1 := by
  apply loweredOn_mem_Icc (fkSingletonParameter_pos hp hq).le hp.2.le hpp.le
    (starEpsilon_nonneg hp hq Delta)
  calc
    starEpsilon p q Delta ≤ |fkSingletonParameter p q - p| := starEpsilon_le_abs hp hq Delta
    _ = p - fkSingletonParameter p q := by
      simpa only [neg_sub] using abs_of_neg (sub_neg.mpr hpp)

end FKLimit


namespace FKLimit

/-- Lower product parameters in Proposition 4.2(1): `p + ε̂` on `S`. -/
noncomputable def ltLowerParameters {E : Type*} (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : p < fkSingletonParameter p q)
    (Delta : ℕ) (S : Set E) : E → unitInterval :=
  unitParameters (raisedOn p (starEpsilon p q Delta) S)
    (fun e ↦ (raisedOn_star_mem_Icc_of_lt hp hq hpp Delta S e).1)
    (fun e ↦ (raisedOn_star_mem_Icc_of_lt hp hq hpp Delta S e).2)

/-- Upper product parameters in Proposition 4.2(1): `p' - ε̃` on `S`. -/
noncomputable def ltUpperParameters {E : Type*} (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : p < fkSingletonParameter p q)
    (L : ℕ) (S : Set E) : E → unitInterval :=
  unitParameters (loweredOn (fkSingletonParameter p q) (cycleEpsilon p q L) S)
    (fun e ↦ (loweredOn_cycle_mem_Icc_of_lt hp hq hpp L S e).1)
    (fun e ↦ (loweredOn_cycle_mem_Icc_of_lt hp hq hpp L S e).2)

/-- Lower product parameters in Proposition 4.2(2): `p' + ε̃` on `S`. -/
noncomputable def gtLowerParameters {E : Type*} (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : fkSingletonParameter p q < p)
    (L : ℕ) (S : Set E) : E → unitInterval :=
  unitParameters (raisedOn (fkSingletonParameter p q) (cycleEpsilon p q L) S)
    (fun e ↦ (raisedOn_cycle_mem_Icc_of_gt hp hq hpp L S e).1)
    (fun e ↦ (raisedOn_cycle_mem_Icc_of_gt hp hq hpp L S e).2)

/-- Upper product parameters in Proposition 4.2(2): `p - ε̂` on `S`. -/
noncomputable def gtUpperParameters {E : Type*} (p q : ℝ)
    (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q) (hpp : fkSingletonParameter p q < p)
    (Delta : ℕ) (S : Set E) : E → unitInterval :=
  unitParameters (loweredOn p (starEpsilon p q Delta) S)
    (fun e ↦ (loweredOn_star_mem_Icc_of_gt hp hq hpp Delta S e).1)
    (fun e ↦ (loweredOn_star_mem_Icc_of_gt hp hq hpp Delta S e).2)

lemma selectParameters_raisedOn_unit {E : Type*} (base eps : ℝ) (S : Set E)
    (hb0 : ∀ _ : E, 0 ≤ base) (hb1 : ∀ _ : E, base ≤ 1)
    (hr0 : ∀ e, 0 ≤ raisedOn base eps S e) (hr1 : ∀ e, raisedOn base eps S e ≤ 1) :
    selectParameters (unitParameters (fun _ : E ↦ base) hb0 hb1)
      (unitParameters (raisedOn base eps S) hr0 hr1) S =
        unitParameters (raisedOn base eps S) hr0 hr1 := by
  funext e
  by_cases he : e ∈ S
  · simp [selectParameters, he]
  · apply Subtype.ext
    simp [selectParameters, unitParameters, raisedOn, he]

lemma selectParameters_loweredOn_unit {E : Type*} (base eps : ℝ) (S : Set E)
    (hb0 : ∀ _ : E, 0 ≤ base) (hb1 : ∀ _ : E, base ≤ 1)
    (hr0 : ∀ e, 0 ≤ loweredOn base eps S e) (hr1 : ∀ e, loweredOn base eps S e ≤ 1) :
    selectParameters (unitParameters (fun _ : E ↦ base) hb0 hb1)
      (unitParameters (loweredOn base eps S) hr0 hr1) S =
        unitParameters (loweredOn base eps S) hr0 hr1 := by
  funext e
  by_cases he : e ∈ S
  · simp [selectParameters, he]
  · apply Subtype.ext
    simp [selectParameters, unitParameters, loweredOn, he]

end FKLimit


namespace FKLimit

/-- **Legacy opposite-sandwich reduction.** This declaration is retained to
avoid breaking older code, but its hypotheses/conclusion are not the paper's
Proposition 4.2(1), because `StochasticallyDominates` has an orientation-sensitive
definition. The faithful weak-limit Proposition 4.2 sandwich is
`FK.MainIntegration.proposition_4_2_lt_of_oriented_finite_comparisons`, and its
phase-law form is `FK.MainIntegration.proposition_4_2_lt_phase_sandwich_of_oriented_limit`.
Do not use this older declaration as the intended finite-enhancement input. -/
theorem proposition_4_2_lt_of_finite_comparisons {E : Type*} [Countable E]
    (exh : EdgeExhaustion E) (Sstar Scycle : Set E) (Dstar Dcycle : E → Finset E)
    (starAdmissible cycleAdmissible : ℕ → E → Prop)
    {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (hpp : p < fkSingletonParameter p q) (Delta L : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hLower : ∀ n, CylinderDominates
      (bernoulliProduct (activeParameters exh Sstar Dstar starAdmissible
        (unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
        (ltLowerParameters p q hp hq hpp Delta Sstar) n)) (μs n))
    (hUpper : ∀ n, CylinderDominates (μs n)
      (bernoulliProduct (activeParameters exh Scycle Dcycle cycleAdmissible
        (unitParameters (fun _ : E ↦ fkSingletonParameter p q)
          (fun _ ↦ (fkSingletonParameter_pos hp hq).le)
          (fun _ ↦ (fkSingletonParameter_lt_one hp hq).le))
        (ltUpperParameters p q hp hq hpp L Scycle) n))) :
    StochasticallyDominates
      (bernoulliProduct (ltLowerParameters p q hp hq hpp Delta Sstar)) μ ∧
    StochasticallyDominates μ
      (bernoulliProduct (ltUpperParameters p q hp hq hpp L Scycle)) := by
  constructor
  · have hselect :
        selectParameters
          (unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
          (ltLowerParameters p q hp hq hpp Delta Sstar) Sstar =
            ltLowerParameters p q hp hq hpp Delta Sstar := by
      apply selectParameters_raisedOn_unit
    have h := lower_bound_of_finiteVolume exh Sstar Dstar starAdmissible
      (unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
      (ltLowerParameters p q hp hq hpp Delta Sstar)
      (fun e he ↦ (hStar e he).1) hstarAdm hμ hLower
    rwa [hselect] at h
  · have hselect :
        selectParameters
          (unitParameters (fun _ : E ↦ fkSingletonParameter p q)
            (fun _ ↦ (fkSingletonParameter_pos hp hq).le)
            (fun _ ↦ (fkSingletonParameter_lt_one hp hq).le))
          (ltUpperParameters p q hp hq hpp L Scycle) Scycle =
            ltUpperParameters p q hp hq hpp L Scycle := by
      apply selectParameters_loweredOn_unit
    have h := upper_bound_of_finiteVolume exh Scycle Dcycle cycleAdmissible
      (unitParameters (fun _ : E ↦ fkSingletonParameter p q)
        (fun _ ↦ (fkSingletonParameter_pos hp hq).le)
        (fun _ ↦ (fkSingletonParameter_lt_one hp hq).le))
      (ltUpperParameters p q hp hq hpp L Scycle)
      (fun e he ↦ (hCycle e he).1) hcycleAdm hμ hUpper
    rwa [hselect] at h

end FKLimit


namespace FKLimit

/-- **Legacy opposite-sandwich reduction** analogous to
`FKLimit.proposition_4_2_lt_of_finite_comparisons`. This is not the paper's
Proposition 4.2(2) because of orientation. Use
`FK.MainIntegration.proposition_4_2_gt_of_oriented_finite_comparisons` and
`FK.MainIntegration.proposition_4_2_gt_phase_sandwich_of_oriented_limit` instead. -/
theorem proposition_4_2_gt_of_finite_comparisons {E : Type*} [Countable E]
    (exh : EdgeExhaustion E) (Sstar Scycle : Set E) (Dstar Dcycle : E → Finset E)
    (starAdmissible cycleAdmissible : ℕ → E → Prop)
    {p q : ℝ} (hp : p ∈ Set.Ioo 0 1) (hq : 0 < q)
    (hpp : fkSingletonParameter p q < p) (Delta L : ℕ)
    (hStar : IsSeparatedDeviceFamily Sstar Dstar)
    (hCycle : IsSeparatedDeviceFamily Scycle Dcycle)
    (hstarAdm : ∀ e ∈ Sstar, ∀ᶠ n in atTop, starAdmissible n e)
    (hcycleAdm : ∀ e ∈ Scycle, ∀ᶠ n in atTop, cycleAdmissible n e)
    {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs atTop (𝓝 μ))
    (hLower : ∀ n, CylinderDominates
      (bernoulliProduct (activeParameters exh Scycle Dcycle cycleAdmissible
        (unitParameters (fun _ : E ↦ fkSingletonParameter p q)
          (fun _ ↦ (fkSingletonParameter_pos hp hq).le)
          (fun _ ↦ (fkSingletonParameter_lt_one hp hq).le))
        (gtLowerParameters p q hp hq hpp L Scycle) n)) (μs n))
    (hUpper : ∀ n, CylinderDominates (μs n)
      (bernoulliProduct (activeParameters exh Sstar Dstar starAdmissible
        (unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
        (gtUpperParameters p q hp hq hpp Delta Sstar) n))) :
    StochasticallyDominates
      (bernoulliProduct (gtLowerParameters p q hp hq hpp L Scycle)) μ ∧
    StochasticallyDominates μ
      (bernoulliProduct (gtUpperParameters p q hp hq hpp Delta Sstar)) := by
  constructor
  · have hselect :
        selectParameters
          (unitParameters (fun _ : E ↦ fkSingletonParameter p q)
            (fun _ ↦ (fkSingletonParameter_pos hp hq).le)
            (fun _ ↦ (fkSingletonParameter_lt_one hp hq).le))
          (gtLowerParameters p q hp hq hpp L Scycle) Scycle =
            gtLowerParameters p q hp hq hpp L Scycle := by
      apply selectParameters_raisedOn_unit
    have h := lower_bound_of_finiteVolume exh Scycle Dcycle cycleAdmissible
      (unitParameters (fun _ : E ↦ fkSingletonParameter p q)
        (fun _ ↦ (fkSingletonParameter_pos hp hq).le)
        (fun _ ↦ (fkSingletonParameter_lt_one hp hq).le))
      (gtLowerParameters p q hp hq hpp L Scycle)
      (fun e he ↦ (hCycle e he).1) hcycleAdm hμ hLower
    rwa [hselect] at h
  · have hselect :
        selectParameters
          (unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
          (gtUpperParameters p q hp hq hpp Delta Sstar) Sstar =
            gtUpperParameters p q hp hq hpp Delta Sstar := by
      apply selectParameters_loweredOn_unit
    have h := upper_bound_of_finiteVolume exh Sstar Dstar starAdmissible
      (unitParameters (fun _ : E ↦ p) (fun _ ↦ hp.1.le) (fun _ ↦ hp.2.le))
      (gtUpperParameters p q hp hq hpp Delta Sstar)
      (fun e he ↦ (hStar e he).1) hstarAdm hμ hUpper
    rwa [hselect] at h

end FKLimit


namespace FKLimit

/-- The two-sided comparison extends from every component of a Markov-kernel
mixture to the mixture itself.  With `kernelAt κ x` instantiated by FK limit
measures, this is the measure-theoretic Gibbs-mixture step of Proposition 4.2. -/
theorem two_sided_comparison_of_kernelMixture {α E : Type*} [MeasurableSpace α]
    (ρ : ProbabilityMeasure α) (κ : ProbabilityTheory.Kernel α (Configuration E))
    [IsMarkovKernel κ] (lower upper : ProbabilityMeasure (Configuration E))
    (hLower : ∀ x, StochasticallyDominates lower (kernelAt κ x))
    (hUpper : ∀ x, StochasticallyDominates (kernelAt κ x) upper) :
    StochasticallyDominates lower (kernelMixture ρ κ) ∧
      StochasticallyDominates (kernelMixture ρ κ) upper :=
  ⟨kernelMixture_upper_bound ρ κ hLower, kernelMixture_lower_bound ρ κ hUpper⟩

end FKLimit
