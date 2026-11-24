import FK.NestedFiniteAssembly
/-
Boundary-independence of the finite FK law and the q = 1 collapse of the FK family.

At `q = 1` the wired-component weight is identically one, so the finite FK law is
a Bernoulli edge product that does not see the boundary partition.  This file
turns that finite identity into infinite-volume statements: every conditional
global FK law of a box, every DLR law at `q = 1`, and every FK weak limit along a
fixed exhaustion is the same Bernoulli product.

Only the standard axioms are used.
-/
import FK.BernoulliFiniteBox
import FK.ClassicalOne
import FK.ExteriorIdentification
import FK.ReverseMartingale
import FK.Theorem110Assembly

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval

namespace FK.InfiniteVolume.QOne

noncomputable section

variable {E : Type*} [Countable E]

/-- At `q = 1`, on any event supported inside the box, the conditional global law
of the box does not depend on the boundary partition or on the exterior
configuration: it equals the Bernoulli product with rate `p`. -/
theorem conditionalLaw_q_one_real_eq_bernoulliProduct
    (B : FiniteBox E) {p : NNReal} (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {A : Set (Configuration E)} {T : Finset E}
    (hA : FKLimit.DependsOnCoordinates A T) (hT : T ⊆ B.edges) :
    (B.conditionalLaw (q := 1) zero_lt_one hp α η :
        Measure (Configuration E)).real A =
      (FKLimit.bernoulliProduct
        (fun _ : E => FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp) :
          Measure (Configuration E)).real A := by
  rw [B.eq_preimage_interiorRestriction_image (hA.mono hT)]
  rw [B.conditionalLaw_real_interior_preimage (q := 1) zero_lt_one hp α η
    MeasurableSet.of_discrete]
  rw [FK.Finite.LabelledMultigraph.fkMeasure_q_one B.graph hp (α η)]
  exact (FK.InfiniteVolume.NestedFiniteAssembly.bernoulliProduct_real_interior_preimage B hp
    (B.interiorRestriction '' A)).symm

/-- At `q = 1` the finite-volume law of a box is boundary-independent on
box-supported events. -/
theorem finiteVolumeLaw_q_one_real_eq_bernoulliProduct
    (B : FiniteBox E) {p : NNReal} (hp : p ≤ 1)
    (α : B.BoundaryPartition)
    {A : Set (Configuration E)} {T : Finset E}
    (hA : FKLimit.DependsOnCoordinates A T) (hT : T ⊆ B.edges) :
    (B.finiteVolumeLaw (q := 1) zero_lt_one hp α :
        Measure (Configuration E)).real A =
      (FKLimit.bernoulliProduct
        (fun _ : E => FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp) :
          Measure (Configuration E)).real A :=
  conditionalLaw_q_one_real_eq_bernoulliProduct B hp (fun _ => α)
    B.closedExterior hA hT

end

end FK.InfiniteVolume.QOne

namespace FK.InfiniteVolume.QOne

noncomputable section

open FK.InfiniteVolume
open Filter Topology

variable {E : Type*} [Countable E]

/-- The Bernoulli product with constant rate `p`, in `ProbabilityMeasure` form. -/
abbrev bernoulliConst (p : NNReal) (hp : p ≤ 1) : ProbabilityMeasure (Configuration E) :=
  FKLimit.bernoulliProduct (fun _ : E => FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp)

/-- **Every boundary schedule at `q = 1` gives the Bernoulli product as an FK
weak limit**, along any fixed exhaustion: the finite laws have eventually constant
cylinder masses. -/
theorem isFKLimit_q_one (exh : BoxExhaustion E) {p : NNReal} (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition) :
    IsFKLimit exh (q := 1) zero_lt_one hp α (bernoulliConst (E := E) p hp) := by
  rw [IsFKLimit]
  refine (tendsto_probabilityMeasure_iff_cylinder_real_tendsto _ _).mpr ?_
  intro J S
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [exh.eventually_subset J] with n hn
  exact (finiteVolumeLaw_q_one_real_eq_bernoulliProduct (exh.box n) hp (α n)
    (FK.InfiniteVolume.dependsOnCoordinates_cylinder J S) hn).symm

/-- **Uniqueness of the `q = 1` FK limit**: every limit along a fixed exhaustion
is the Bernoulli product, whatever the boundary partitions are. -/
theorem eq_bernoulliConst_of_isFKLimit_q_one (exh : BoxExhaustion E) {p : NNReal}
    (hp : p ≤ 1) (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh (q := 1) zero_lt_one hp α μ) :
    μ = bernoulliConst (E := E) p hp := by
  apply ProbabilityMeasure.toMeasure_injective
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro J S
  have hEq : (fun n =>
      (exh.box n).finiteVolumeLaw (q := 1) zero_lt_one hp (α n)
        (MeasureTheory.cylinder J S)) =ᶠ[atTop] fun _ =>
      (bernoulliConst (E := E) p hp) (MeasureTheory.cylinder J S) := by
    filter_upwards [exh.eventually_subset J] with n hn
    have hreal := finiteVolumeLaw_q_one_real_eq_bernoulliProduct (exh.box n) hp (α n)
      (FK.InfiniteVolume.dependsOnCoordinates_cylinder J S) hn
    have hreal' : ((exh.box n).finiteVolumeLaw (q := 1) zero_lt_one hp (α n)
        (MeasureTheory.cylinder J S) : ℝ) =
        ((bernoulliConst (E := E) p hp) (MeasureTheory.cylinder J S) : ℝ) := by
      simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hreal
    exact_mod_cast hreal'
  have hNN : ((μ : Measure (Configuration E)) (MeasureTheory.cylinder J S)).toNNReal =
      ((bernoulliConst (E := E) p hp : Measure (Configuration E))
        (MeasureTheory.cylinder J S)).toNNReal := by
    have hclop : Tendsto (fun n =>
        (exh.box n).finiteVolumeLaw (q := 1) zero_lt_one hp (α n)
          (MeasureTheory.cylinder J S)) atTop
        (𝓝 ((μ (MeasureTheory.cylinder J S) : ℝ≥0))) :=
      ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ
        (FK.InfiniteVolume.dependsOnCoordinates_cylinder J S).isClopen
    have hconst : Tendsto (fun _ =>
        (bernoulliConst (E := E) p hp) (MeasureTheory.cylinder J S)) atTop
        (𝓝 ((μ (MeasureTheory.cylinder J S) : ℝ≥0))) :=
      hclop.congr' hEq
    have heqNN : (bernoulliConst (E := E) p hp) (MeasureTheory.cylinder J S) =
        μ (MeasureTheory.cylinder J S) := tendsto_const_nhds_iff.mp hconst
    simpa only [ProbabilityMeasure.coeFn_def] using heqNN.symm
  calc (μ : Measure (Configuration E)) (MeasureTheory.cylinder J S)
      = (((μ : Measure (Configuration E)) (MeasureTheory.cylinder J S)).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm
    _ = ((((bernoulliConst (E := E) p hp : Measure (Configuration E))
          (MeasureTheory.cylinder J S)).toNNReal) : ℝ≥0∞) := by rw [hNN]
    _ = (bernoulliConst (E := E) p hp : Measure (Configuration E))
          (MeasureTheory.cylinder J S) := ENNReal.coe_toNNReal (measure_ne_top _ _)

/-- The `q = 1` FK limit class is the singleton Bernoulli product, for every
fixed exhaustion. -/
theorem fkLimitMeasures_q_one_eq_singleton (exh : BoxExhaustion E) {p : NNReal}
    (hp : p ≤ 1) :
    FKLimitMeasures exh (q := 1) zero_lt_one hp = {bernoulliConst (E := E) p hp} := by
  ext μ
  constructor
  · rintro ⟨α, hα⟩
    exact Set.mem_singleton_iff.mpr (eq_bernoulliConst_of_isFKLimit_q_one exh hp α hα)
  · intro hμ
    refine ⟨fun _ => ⊥, ?_⟩
    rw [Set.mem_singleton_iff] at hμ
    subst hμ
    exact isFKLimit_q_one exh hp _

/-- **Unconditional strong uniqueness at `q = 1`**: for every exhaustion, every
`p ∈ [0,1]` and every boundary convention, the total FK family is the single
Bernoulli product. -/
theorem fkFamily_q_one_eq_singleton (exh : BoxExhaustion E) {p : NNReal}
    (hp : p ≤ 1) :
    FKFamily exh (q := 1) zero_lt_one hp = {bernoulliConst (E := E) p hp} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro ν hν
    refine Set.mem_singleton_iff.mpr (eq_of_unique_fkLimit (q := 1) zero_lt_one hp exh
      (fun μ hμ => ?_) ν hν)
    obtain ⟨α, hα⟩ := hμ
    exact eq_bernoulliConst_of_isFKLimit_q_one exh hp α hα
  · intro ν hν
    rw [Set.mem_singleton_iff] at hν
    subst hν
    exact mem_fkFamily_of_mem_fkLimit zero_lt_one hp exh
      ⟨fun _ => ⊥, isFKLimit_q_one exh hp (fun _ => ⊥)⟩

end

end FK.InfiniteVolume.QOne

namespace FK.InfiniteVolume.QOne

noncomputable section

open FK.InfiniteVolume
open Filter Topology

variable {E : Type*} [Countable E]

/-- ENNReal form of the `q = 1` conditional identity: on box-supported events
the conditional global law is exactly the Bernoulli product measure. -/
theorem conditionalLaw_q_one_apply_eq_bernoulliProduct
    (B : FiniteBox E) {p : NNReal} (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior)
    {A : Set (Configuration E)} {T : Finset E}
    (hA : FKLimit.DependsOnCoordinates A T) (hT : T ⊆ B.edges) :
    (B.conditionalLaw (q := 1) zero_lt_one hp α η : Measure (Configuration E)) A =
      (FKLimit.bernoulliProduct
        (fun _ : E => FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp) :
          Measure (Configuration E)) A := by
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)]
  exact conditionalLaw_q_one_real_eq_bernoulliProduct B hp α η hA hT

/-- **Every DLR law at `q = 1` is the Bernoulli product**, for every measurable
boundary convention: the finite specification at `q = 1` does not see the
boundary, so every box-supported cylinder mass is the Bernoulli mass. -/
theorem eq_bernoulliConst_of_mem_dlrMeasures_q_one (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {p : NNReal} (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ (q := 1) zero_lt_one hp) :
    μ = bernoulliConst (E := E) p hp := by
  apply ProbabilityMeasure.toMeasure_injective
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro J S
  obtain ⟨n, hn⟩ := (exh.eventually_subset J).exists
  have hdlr := (exh.box n).apply_of_isDLR (q := 1) zero_lt_one hp
    (Φ.partition n) (Φ.measurable_partition n) μ (hμ n)
    (FK.InfiniteVolume.dependsOnCoordinates_cylinder J S).measurableSet
  rw [hdlr]
  have hconst : ∀ η, ((exh.box n).conditionalLaw (q := 1) zero_lt_one hp
      (Φ.partition n) η : Measure (Configuration E))
        (MeasureTheory.cylinder J S) =
      (bernoulliConst (E := E) p hp : Measure (Configuration E))
        (MeasureTheory.cylinder J S) :=
    fun η => conditionalLaw_q_one_apply_eq_bernoulliProduct (exh.box n) hp
      (Φ.partition n) η (FK.InfiniteVolume.dependsOnCoordinates_cylinder J S) hn
  simp only [hconst]
  simp

end

end FK.InfiniteVolume.QOne

namespace FK.InfiniteVolume.QOne

noncomputable section

open FK.InfiniteVolume
open Filter Topology

variable {E : Type*} [Countable E]

/-- The exterior marginal of the Bernoulli product across a box is the Bernoulli
product on the complementary edges. -/
theorem exteriorMeasure_bernoulliConst (B : FiniteBox E) {p : NNReal} (hp : p ≤ 1) :
    (B.exteriorMeasure (bernoulliConst (E := E) p hp) : Measure B.Exterior) =
      Measure.infinitePi (fun _ : {e : E // e ∉ B.edges} =>
        bernoulliMeasure true false
          (FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp)) := by
  have hcoe : (B.exteriorMeasure (bernoulliConst (E := E) p hp) : Measure B.Exterior) =
      Measure.map Prod.fst (Measure.map B.splitEquiv
        (bernoulliConst (E := E) p hp : Measure (Configuration E))) := by
    rw [FiniteBox.exteriorMeasure, ProbabilityMeasure.toMeasure_map, Measure.map_map]
    · rfl
    · exact measurable_fst
    · exact B.splitEquiv.measurable
  rw [hcoe, B.map_splitEquiv_bernoulliProduct, Measure.map_fst_prod]
  simp

/-- **The Bernoulli product is a DLR law at `q = 1`** for every measurable
boundary convention: at `q = 1` the box specification is the Bernoulli product
independent of the exterior, so the DLR equation is the product factorization. -/
theorem mem_dlrMeasures_q_one (exh : BoxExhaustion E) (Φ : BoundaryAssignment exh.box)
    {p : NNReal} (hp : p ≤ 1) :
    bernoulliConst (E := E) p hp ∈ DLRMeasures exh Φ (q := 1) zero_lt_one hp := by
  intro n
  set B := exh.box n with hB
  have hker : B.fkKernel (q := 1) zero_lt_one hp (Φ.partition n) (Φ.measurable_partition n) =
      ProbabilityTheory.Kernel.const B.Exterior
        (Measure.pi (fun e : B.edges => bernoulliMeasure true false
          (FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp))) := by
    apply ProbabilityTheory.Kernel.ext
    intro η
    rw [FiniteBox.fkKernel_apply]
    rw [FK.Finite.LabelledMultigraph.fkMeasure_q_one B.graph hp (Φ.partition n η)]
    rw [FK.InfiniteVolume.NestedFiniteAssembly.bernoulliProductPMF_toMeasure]
    rfl
  rw [FiniteBox.IsDLR, hker, Measure.compProd_const,
    B.map_splitEquiv_bernoulliProduct (fun _ : E =>
      FK.InfiniteVolume.NestedFiniteAssembly.unitOfNN p hp),
    exteriorMeasure_bernoulliConst B hp]

end

end FK.InfiniteVolume.QOne

namespace FK.InfiniteVolume.QOne

noncomputable section

open FK.InfiniteVolume

variable {E : Type*} [Countable E]

/-- **The DLR class at `q = 1` is the singleton Bernoulli product**, for every
measurable boundary convention and every exhaustion: every DLR law is the
Bernoulli product, and the Bernoulli product is DLR. -/
theorem dlrMeasures_q_one_eq_singleton (exh : BoxExhaustion E)
    (Φ : BoundaryAssignment exh.box) {p : NNReal} (hp : p ≤ 1) :
    DLRMeasures exh Φ (q := 1) zero_lt_one hp = {bernoulliConst (E := E) p hp} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro μ hμ
    exact Set.mem_singleton_iff.mpr (eq_bernoulliConst_of_mem_dlrMeasures_q_one exh Φ hp hμ)
  · intro μ hμ
    rw [Set.mem_singleton_iff] at hμ
    subst hμ
    exact mem_dlrMeasures_q_one exh Φ hp

end

end FK.InfiniteVolume.QOne

namespace FK.InfiniteVolume.QOne

noncomputable section

open FK.InfiniteVolume

variable {E : Type*} [Countable E]

/-- **Strong uniqueness at `q = 1`**, in `∃!` form: for every exhaustion and every
`p ∈ [0,1]` the total FK family is a single point, the Bernoulli product.  No
sub-exhaustion, no nonemptiness hypothesis and no boundary-convention hypothesis
is left open at this parameter line. -/
theorem existsUnique_fkFamily_q_one (exh : BoxExhaustion E) {p : NNReal} (hp : p ≤ 1) :
    ∃! μ : ProbabilityMeasure (Configuration E),
      μ ∈ FKFamily exh (q := 1) zero_lt_one hp := by
  refine ⟨bernoulliConst (E := E) p hp, ?_, ?_⟩
  · rw [fkFamily_q_one_eq_singleton exh hp]
    exact Set.mem_singleton _
  · intro μ hμ
    rw [fkFamily_q_one_eq_singleton exh hp] at hμ
    exact Set.mem_singleton_iff.mp hμ

end

end FK.InfiniteVolume.QOne
