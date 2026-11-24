/-
# Infinite-volume FKG (positive association) for FK limit laws

The finite bridge `FK.WiredFKG` gives positive association at `q ≥ 1` for the
normalized finite random-cluster measures.  This file passes it to an arbitrary
weak limit `μ` of finite-volume FK laws (`FK.InfiniteVolume.IsFKLimit`), along
any box exhaustion and for any boundary-setoid schedule.

## Main exports

* `fkMeasure_mul_le_inter` : two increasing events are positively correlated
  under the finite normalized FK measure at `q ≥ 1` and `0 ≤ p ≤ 1` (both
  endpoints included), for arbitrary boundary setoids;
* `finiteVolumeLaw_mul_le_inter` : the same for genuine finite-box laws on a
  countable edge space, for global events supported in the box;
* `cylinder_mul_le_inter_of_isFKLimit` : the same for finitely supported
  increasing events under an FK weak limit;
* `mul_le_inter_of_isFKLimit`, `mul_le_inter_of_mem_fkLimitMeasures`,
  `apply_mul_le_apply_inter_of_isFKLimit` : **the infinite-volume FKG
  inequality** `μ(A ∩ B) ≥ μ(A) μ(B)` for all measurable increasing `A, B` and
  every FK weak limit `μ` at `q ≥ 1`, `0 ≤ p ≤ 1`;
* `inter_le_mul_of_isFKLimit`, `apply_inter_le_mul_of_isFKLimit` : the up/down
  form `μ(A ∩ D) ≤ μ(A) μ(D)` for `A` increasing and `D` decreasing, the
  infinite-volume analogue of the finite `PosAssoc` shape;
* `fkMeasure_mono_p_of_lt_one`, `finiteVolumeLaw_mono_p`,
  `stochasticallyDominates_of_isFKLimit_p` : monotonicity in the edge parameter
  `p` (finite, box, and for two limits along a common schedule);
* `bernoulliConst_mul_le_inter` : the `q = 1` instance, showing that the limit
  hypothesis is not vacuous (`QOne.isFKLimit_q_one`).

## Method

* Cylinder events: the mass of a finitely supported event is continuous for the
  weak topology, and the finite FK laws along the exhaustion satisfy FKG at
  every stage, so the inequality survives the limit.
* All increasing measurable events: an increasing measurable event is
  approximated from inside by increasing compact sets, and for a compact
  increasing set `K` the cylinder approximation `restrictionNeighborhood K S`
  is increasing, finitely supported and decreases to `K`.

No construction of limits, no uniqueness, no DLR membership and no percolation
statement is claimed here; the only inputs are the finite FKG theorem, the
endpoint Dirac laws and the definition of an FK weak limit.
-/
import FK.Proposition42
import FK.StageInstantiation
import FK.WiredFKG
import FK.InfiniteVolume
import FK.GibbsOrder
import FK.QOneLine

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

namespace FK.InfiniteVolume

namespace InfiniteVolumeFKG

/-! ## Part 1: two increasing events are positively correlated at finite volume -/

section Finite

variable {G : FK.Finite.LabelledMultigraph}

/-- **FKG for two increasing events**, finite normalized FK measure, interior
rate.  This is the event form of `fkPMF_association` with the two indicators as
the increasing observables, expressed directly in the measure. -/
theorem fkMeasure_mul_le_inter_of_lt_one {q p : NNReal} (hq : 1 ≤ q) (hp0 : 0 < p)
    (hp1 : p < 1) (ξ : G.BoundaryPartition) {A B : Set G.Configuration}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ A *
        G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ B
      ≤ G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp1.le ξ (A ∩ B) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set P : G.Configuration → ℝ := fun ω ↦ (G.fkPMF hqpos hp1.le ξ ω).toReal with hP
  have hmonoA : Monotone (A.indicator (fun _ => (1 : ℝ))) := by
    intro x y hxy
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hA hxy hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_apply]
      split_ifs <;> norm_num
  have hmonoB : Monotone (B.indicator (fun _ => (1 : ℝ))) := by
    intro x y hxy
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hB hxy hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_apply]
      split_ifs <;> norm_num
  have h0A : ∀ x, 0 ≤ (A.indicator (fun _ => (1 : ℝ))) x := by
    intro x; rw [Set.indicator_apply]; split_ifs <;> norm_num
  have h0B : ∀ x, 0 ≤ (B.indicator (fun _ => (1 : ℝ))) x := by
    intro x; rw [Set.indicator_apply]; split_ifs <;> norm_num
  have hreal := G.fkPMF_association (q := q) (p := p) hq hp0 hp1 ξ
    (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℝ)))
    hmonoA hmonoB h0A h0B
  have hmass : ∀ S : Set G.Configuration,
      (∑ ω, P ω * S.indicator (fun _ => (1 : ℝ)) ω)
        = (G.fkMeasure hqpos hp1.le ξ S).toReal := by
    intro S
    rw [G.fkMeasure_toReal_eq_sum hqpos hp1.le ξ S]
  have hsum : (∑ ω, P ω) = 1 := by
    have h := hmass Set.univ
    simpa [P, Set.indicator_univ] using h
  have hprod : (∑ ω, P ω * A.indicator (fun _ => (1 : ℝ)) ω *
        B.indicator (fun _ => (1 : ℝ)) ω)
      = (G.fkMeasure hqpos hp1.le ξ (A ∩ B)).toReal := by
    rw [← hmass (A ∩ B)]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
  rw [hmass A, hmass B, hsum, hprod, one_mul] at hreal
  refine (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (measure_ne_top _ _)).mp ?_
  rw [ENNReal.toReal_mul]
  exact hreal

/-- A Dirac law satisfies FKG for two increasing events (trivially, and in fact
for any two sets). -/
theorem dirac_mul_le_inter {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (x : Ω) {A B : Set Ω} :
    (Measure.dirac x : Measure Ω) A * (Measure.dirac x : Measure Ω) B ≤
      (Measure.dirac x : Measure Ω) (A ∩ B) := by
  by_cases hxA : x ∈ A
  · by_cases hxB : x ∈ B
    · rw [Measure.dirac_apply_of_mem hxA, Measure.dirac_apply_of_mem hxB,
        Measure.dirac_apply_of_mem (Set.mem_inter hxA hxB), one_mul]
    · have hzero : (Measure.dirac x : Measure Ω) B = 0 := by
        rw [Measure.dirac_apply]
        simp [hxB]
      rw [hzero, mul_zero]
      exact bot_le
  · have hzero : (Measure.dirac x : Measure Ω) A = 0 := by
      rw [Measure.dirac_apply]
      simp [hxA]
    rw [hzero, zero_mul]
    exact bot_le

/-- **FKG for two increasing events** for the finite normalized FK measure at
`q ≥ 1` and `0 < p ≤ 1`, including the all-open endpoint. -/
theorem fkMeasure_mul_le_inter {q p : NNReal} (hq : 1 ≤ q)
    (hp : p ≤ 1) (ξ : G.BoundaryPartition) {A B : Set G.Configuration}
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp ξ A *
        G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp ξ B
      ≤ G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp ξ (A ∩ B) := by
  rcases eq_or_lt_of_le (zero_le : (0 : NNReal) ≤ p) with h0 | hpos
  · subst h0
    rw [FK.InfiniteVolume.NoEscape.fkMeasure_zero_eq_dirac
      (lt_of_lt_of_le zero_lt_one hq) ξ]
    exact dirac_mul_le_inter G.allClosed
  · rcases eq_or_lt_of_le hp with h1 | hlt
    · subst h1
      rw [FK.InfiniteVolume.NoEscape.fkMeasure_one_eq_dirac
        (lt_of_lt_of_le zero_lt_one hq) ξ]
      exact dirac_mul_le_inter G.allOpen
    · exact fkMeasure_mul_le_inter_of_lt_one hq hpos hlt ξ hA hB

/-- **Monotonicity in the edge parameter `p`**, finite normalized FK measure,
increasing event, interior `p₂ < 1`. -/
theorem fkMeasure_mono_p_of_lt_one {G : FK.Finite.LabelledMultigraph} {q : NNReal}
    (hq : 1 ≤ q) {p₁ p₂ : NNReal} (hp₁0 : 0 < p₁) (hp₂1 : p₂ < 1) (hp12 : p₁ ≤ p₂)
    (ξ : G.BoundaryPartition) {A : Set G.Configuration} (hA : IsUpperSet A) :
    G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) (le_trans hp12 hp₂1.le) ξ A ≤
      G.fkMeasure (lt_of_lt_of_le zero_lt_one hq) hp₂1.le ξ A := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmono : Monotone (A.indicator (fun _ => (1 : ℝ))) := by
    intro x y hxy
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hA hxy hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_apply]
      split_ifs <;> norm_num
  have h0 : ∀ x, 0 ≤ (A.indicator (fun _ => (1 : ℝ))) x := by
    intro x; rw [Set.indicator_apply]; split_ifs <;> norm_num
  have hreal := G.fkPMF_expectation_mono_p hq (p₁ := p₁) (p₂ := p₂) hp₁0 hp₂1 hp12 ξ
    (A.indicator (fun _ => (1 : ℝ))) hmono h0
  rw [← G.fkMeasure_toReal_eq_sum hqpos (le_trans hp12 hp₂1.le) ξ A,
    ← G.fkMeasure_toReal_eq_sum hqpos hp₂1.le ξ A] at hreal
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end Finite

/-! ## Part 2: the same for the actual finite-box laws on a global edge space -/

section Stage

variable {E : Type*}

/-- The `finiteVolumeLaw` mass of the interior preimage of an interior event is
the finite FK mass of the box graph. -/
theorem finiteVolumeLaw_apply_preimage (B : FK.InfiniteVolume.FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) (α : B.BoundaryPartition)
    (S : Set B.Interior) :
    (B.finiteVolumeLaw hq hp α : Measure (Configuration E))
        (B.interiorRestriction ⁻¹' S) = B.graph.fkMeasure hq hp α S := by
  classical
  have hdep : FKLimit.DependsOnCoordinates (B.interiorRestriction ⁻¹' S) B.edges := by
    intro ω η hωη
    have hfun : B.interiorRestriction ω = B.interiorRestriction η := by
      funext e
      exact hωη e.1 e.2
    rw [Set.mem_preimage, Set.mem_preimage, hfun]
  have hmeas : MeasurableSet (B.interiorRestriction ⁻¹' S) := hdep.measurableSet
  change (Measure.map (fun ω : B.Interior => B.glue (B.closedExterior, ω))
    (B.graph.fkMeasure hq hp α)) (B.interiorRestriction ⁻¹' S) = _
  rw [Measure.map_apply (B.measurable_glue_const_left B.closedExterior) hmeas]
  have hset : (fun ω : B.Interior => B.glue (B.closedExterior, ω)) ⁻¹'
      (B.interiorRestriction ⁻¹' S) = S := by
    ext ω
    simp
  rw [hset]

/-- The interior-restriction image of an increasing global event is increasing
for the pointwise order on the box interior. -/
theorem isUpperSet_interiorRestriction_image (B : FK.InfiniteVolume.FiniteBox E)
    {A : Set (Configuration E)} (hA : IsUpperSet A) :
    IsUpperSet (B.interiorRestriction '' A) := by
  classical
  intro i j hij hi
  obtain ⟨ω, hωA, hωi⟩ := hi
  subst hωi
  refine ⟨fun e => if he : e ∈ B.edges then j ⟨e, he⟩ else ω e, ?_, ?_⟩
  · refine hA ?_ hωA
    intro e
    by_cases he : e ∈ B.edges
    · have hb : (fun e => if he : e ∈ B.edges then j ⟨e, he⟩ else ω e) e
          = j ⟨e, he⟩ := by simp only [dite_eq_left he]
      rw [hb]
      have hωe : ω e = (B.interiorRestriction ω) ⟨e, he⟩ := rfl
      rw [hωe]
      exact hij ⟨e, he⟩
    · have hb : (fun e => if he : e ∈ B.edges then j ⟨e, he⟩ else ω e) e = ω e := by
        simp only [dite_eq_right he]
      rw [hb]
  · show B.interiorRestriction
      (fun e => if he : e ∈ B.edges then j ⟨e, he⟩ else ω e) = j
    funext e
    exact dite_eq_left e.2

/-- An event depending on the box edges is the preimage of its interior
restriction image. -/
theorem eq_preimage_interiorRestriction_image (B : FK.InfiniteVolume.FiniteBox E)
    {A : Set (Configuration E)} (hA : FKLimit.DependsOnCoordinates A B.edges) :
    A = B.interiorRestriction ⁻¹' (B.interiorRestriction '' A) := by
  ext ω
  constructor
  · intro hω
    exact ⟨ω, hω, rfl⟩
  · rintro ⟨η, hη, hηω⟩
    refine (hA η ω ?_).mp hη
    intro e he
    exact congrFun hηω ⟨e, he⟩

/-- **FKG for two increasing events** under a genuine finite-box FK law at
`q ≥ 1`, `0 < p ≤ 1` and an arbitrary boundary partition, for global events
that depend only on the box edges. -/
theorem finiteVolumeLaw_mul_le_inter (B : FK.InfiniteVolume.FiniteBox E)
    {q p : NNReal} (hq : 1 ≤ q) (hp : p ≤ 1)
    (α : B.BoundaryPartition) {A C : Set (Configuration E)}
    (hA : FKLimit.DependsOnCoordinates A B.edges)
    (hC : FKLimit.DependsOnCoordinates C B.edges)
    (hAup : IsUpperSet A) (hCup : IsUpperSet C) :
    (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp α :
        Measure (Configuration E)) A *
        (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp α :
          Measure (Configuration E)) C
      ≤ (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp α :
          Measure (Configuration E)) (A ∩ C) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set SA : Set B.Interior := B.interiorRestriction '' A with hSA
  set SC : Set B.Interior := B.interiorRestriction '' C with hSC
  have hAeq : A = B.interiorRestriction ⁻¹' SA :=
    eq_preimage_interiorRestriction_image B hA
  have hCeq : C = B.interiorRestriction ⁻¹' SC :=
    eq_preimage_interiorRestriction_image B hC
  rw [hAeq, hCeq, ← Set.preimage_inter,
    finiteVolumeLaw_apply_preimage B hq0 hp α SA,
    finiteVolumeLaw_apply_preimage B hq0 hp α SC,
    finiteVolumeLaw_apply_preimage B hq0 hp α (SA ∩ SC)]
  exact fkMeasure_mul_le_inter hq hp α
    (isUpperSet_interiorRestriction_image B hAup)
    (isUpperSet_interiorRestriction_image B hCup)

/-- **Monotonicity in `p` for the finite-box laws** on cylinder events. -/
theorem finiteVolumeLaw_mono_p (B : FK.InfiniteVolume.FiniteBox E) {q : NNReal}
    (hq : 1 ≤ q) {p₁ p₂ : NNReal} (hp₁0 : 0 < p₁) (hp₂1 : p₂ < 1)
    (hp12 : p₁ ≤ p₂) (α : B.BoundaryPartition) {A : Set (Configuration E)}
    (hA : FKLimit.DependsOnCoordinates A B.edges) (hAup : IsUpperSet A) :
    (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) (le_trans hp12 hp₂1.le) α :
        Measure (Configuration E)) A ≤
      (B.finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp₂1.le α :
        Measure (Configuration E)) A := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hAeq : A = B.interiorRestriction ⁻¹' (B.interiorRestriction '' A) :=
    eq_preimage_interiorRestriction_image B hA
  rw [hAeq, finiteVolumeLaw_apply_preimage B hq0 (le_trans hp12 hp₂1.le) α _,
    finiteVolumeLaw_apply_preimage B hq0 hp₂1.le α _]
  exact fkMeasure_mono_p_of_lt_one hq hp₁0 hp₂1 hp12 α
    (isUpperSet_interiorRestriction_image B hAup)

end Stage


/-- The mass of a set under a probability measure, read in `ℝ≥0∞`. -/
theorem coe_apply_probabilityMeasure (μ : ProbabilityMeasure (Configuration E)) (S : Set (Configuration E)) :
    ((μ S : NNReal) : ENNReal) = (μ : Measure (Configuration E)) S :=
  ENNReal.coe_toNNReal (measure_ne_top (μ : Measure (Configuration E)) S)

/-! ## Part 3: cylinder FKG for FK weak limits -/

section Limit

variable {E : Type*} [Countable E]

/-- **Cylinder FKG for an FK weak limit.**  Any weak limit of genuine finite-box
FK laws with arbitrary boundary setoids at `q ≥ 1` and `0 < p ≤ 1` satisfies
positive association on pairs of increasing events that depend on finitely many
edges. -/
theorem cylinder_mul_le_inter_of_isFKLimit {exh : BoxExhaustion E} {q p : NNReal}
    (hq : 1 ≤ q) (hp : p ≤ 1)
    {α : ∀ n, (exh.box n).BoundaryPartition} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp α μ)
    {A C : Set (Configuration E)} {S : Finset E}
    (hA : FKLimit.DependsOnCoordinates A S)
    (hC : FKLimit.DependsOnCoordinates C S)
    (hAup : IsUpperSet A) (hCup : IsUpperSet C) :
    μ A * μ C ≤ μ (A ∩ C) := by
  classical
  have hAC : FKLimit.DependsOnCoordinates (A ∩ C) S := by
    intro ω η hωη
    rw [Set.mem_inter_iff, Set.mem_inter_iff, hA ω η hωη, hC ω η hωη]
  have hAcl : IsClopen A := hA.isClopen
  have hCcl : IsClopen C := hC.isClopen
  have hACcl : IsClopen (A ∩ C) := hAC.isClopen
  have hAclim : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n) A) atTop (𝓝 (μ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAcl
  have hCclim : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n) C) atTop (𝓝 (μ C)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hCcl
  have hAClim : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n) (A ∩ C)) atTop (𝓝 (μ (A ∩ C))) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hACcl
  have hmullim : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n) A *
        (exh.box n).finiteVolumeLaw (lt_of_lt_of_le zero_lt_one hq) hp (α n) C)
      atTop (𝓝 (μ A * μ C)) := hAclim.mul hCclim
  refine le_of_tendsto_of_tendsto hmullim hAClim ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (exh.eventually_subset S)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul,
    coe_apply_probabilityMeasure ((exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n)) A,
    coe_apply_probabilityMeasure ((exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n)) C,
    coe_apply_probabilityMeasure ((exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp (α n)) (A ∩ C)]
  exact finiteVolumeLaw_mul_le_inter (exh.box n) hq hp (α n)
    (hA.mono (hN n hn)) (hC.mono (hN n hn)) hAup hCup

/-- **Monotonicity in `p` of FK weak limits along a common schedule.**  Two FK
limits along the same exhaustion and boundary schedule, at `p₁ ≤ p₂ < 1` and
`q ≥ 1`, are stochastically ordered: the larger rate stochastically dominates
the smaller. -/
theorem stochasticallyDominates_of_isFKLimit_p {exh : BoxExhaustion E} {q : NNReal}
    (hq : 1 ≤ q) {p₁ p₂ : NNReal} (hp₁0 : 0 < p₁) (hp₂1 : p₂ < 1) (hp12 : p₁ ≤ p₂)
    {α : ∀ n, (exh.box n).BoundaryPartition}
    {μ₁ μ₂ : ProbabilityMeasure (Configuration E)}
    (hμ₁ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) (le_trans hp12 hp₂1.le) α μ₁)
    (hμ₂ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp₂1.le α μ₂) :
    FKLimit.StochasticallyDominates μ₂ μ₁ := by
  apply FKLimit.stochasticallyDominates_of_cylinderDominates
  intro A S hAS hAup
  have h1 : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) (le_trans hp12 hp₂1.le) (α n) A)
      atTop (𝓝 (μ₁ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ₁ hAS.isClopen
  have h2 : Tendsto (fun n ↦ (exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp₂1.le (α n) A) atTop (𝓝 (μ₂ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ₂ hAS.isClopen
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (exh.eventually_subset S)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← ENNReal.coe_le_coe, coe_apply_probabilityMeasure ((exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) (le_trans hp12 hp₂1.le) (α n)) A,
    coe_apply_probabilityMeasure ((exh.box n).finiteVolumeLaw
      (lt_of_lt_of_le zero_lt_one hq) hp₂1.le (α n)) A]
  exact finiteVolumeLaw_mono_p (exh.box n) hq hp₁0 hp₂1 hp12 (α n)
    (hAS.mono (hN n hn)) hAup

end Limit

/-! ## Part 4: from cylinders to all increasing measurable events -/

section Approximation

variable {E : Type*} [Countable E] {μ : ProbabilityMeasure (Configuration E)}

/-- The masses of a decreasing sequence of measurable sets converge to the mass
of the intersection, in `ℝ≥0`, for a probability measure. -/
theorem tendsto_measure_iInter_nnreal {s : ℕ → Set (Configuration E)}
    (hmeas : ∀ n, MeasurableSet (s n)) (hanti : Antitone s) :
    Tendsto (fun n ↦ μ (s n)) atTop (𝓝 (μ (⋂ n, s n))) := by
  have hlim := tendsto_measure_iInter_atTop (μ := (μ : Measure (Configuration E)))
    (fun n ↦ (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have ht := (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure (Configuration E)) _)).comp
    hlim
  change Tendsto (fun n ↦ ((μ : Measure (Configuration E)) (s n)).toNNReal) atTop
    (𝓝 (((μ : Measure (Configuration E)) (⋂ n, s n)).toNNReal))
  simpa only [Function.comp_def] using ht

/-- **FKG on increasing compact sets.**  For a measure satisfying the FKG
inequality on finitely supported increasing events, the inequality holds for
pairs of compact increasing sets. -/
theorem mul_le_inter_of_isCompact_upper
    (hcyl : ∀ (A C : Set (Configuration E)) (S : Finset E),
      FKLimit.DependsOnCoordinates A S → FKLimit.DependsOnCoordinates C S →
      IsUpperSet A → IsUpperSet C →
      (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) C ≤
        (μ : Measure (Configuration E)) (A ∩ C))
    {K L : Set (Configuration E)} (hK : IsCompact K) (hKup : IsUpperSet K)
    (hL : IsCompact L) (hLup : IsUpperSet L) :
    (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) L ≤
      (μ : Measure (Configuration E)) (K ∩ L) := by
  classical
  let e := FKLimit.encodableEdgeExhaustion E
  have hKlim : Tendsto (fun n ↦ μ (FKLimit.restrictionNeighborhood K (e.box n)))
      atTop (𝓝 (μ K)) := by
    have hanti : Antitone (fun n ↦ FKLimit.restrictionNeighborhood K (e.box n)) :=
      fun m n hmn ↦ FKLimit.restrictionNeighborhood_mono K (e.monotone hmn)
    have hlim := tendsto_measure_iInter_nnreal (μ := μ)
      (s := fun n ↦ FKLimit.restrictionNeighborhood K (e.box n))
      (fun n ↦ (FKLimit.dependsOnCoordinates_restrictionNeighborhood K _).measurableSet)
      hanti
    rwa [FKLimit.iInter_restrictionNeighborhood e hK.isClosed] at hlim
  have hLlim : Tendsto (fun n ↦ μ (FKLimit.restrictionNeighborhood L (e.box n)))
      atTop (𝓝 (μ L)) := by
    have hanti : Antitone (fun n ↦ FKLimit.restrictionNeighborhood L (e.box n)) :=
      fun m n hmn ↦ FKLimit.restrictionNeighborhood_mono L (e.monotone hmn)
    have hlim := tendsto_measure_iInter_nnreal (μ := μ)
      (s := fun n ↦ FKLimit.restrictionNeighborhood L (e.box n))
      (fun n ↦ (FKLimit.dependsOnCoordinates_restrictionNeighborhood L _).measurableSet)
      hanti
    rwa [FKLimit.iInter_restrictionNeighborhood e hL.isClosed] at hlim
  have hmullim : Tendsto (fun n ↦ μ (FKLimit.restrictionNeighborhood K (e.box n)) *
      μ (FKLimit.restrictionNeighborhood L (e.box n))) atTop (𝓝 (μ K * μ L)) :=
    hKlim.mul hLlim
  have hKLlim : Tendsto (fun n ↦ μ (FKLimit.restrictionNeighborhood K (e.box n) ∩
      FKLimit.restrictionNeighborhood L (e.box n))) atTop (𝓝 (μ (K ∩ L))) := by
    have hanti : Antitone (fun n ↦ FKLimit.restrictionNeighborhood K (e.box n) ∩
        FKLimit.restrictionNeighborhood L (e.box n)) := fun m n hmn ↦
      Set.inter_subset_inter (FKLimit.restrictionNeighborhood_mono K (e.monotone hmn))
        (FKLimit.restrictionNeighborhood_mono L (e.monotone hmn))
    have hmeas : ∀ n, MeasurableSet (FKLimit.restrictionNeighborhood K (e.box n) ∩
        FKLimit.restrictionNeighborhood L (e.box n)) := fun n ↦
      (FKLimit.dependsOnCoordinates_restrictionNeighborhood K _).measurableSet.inter
        (FKLimit.dependsOnCoordinates_restrictionNeighborhood L _).measurableSet
    have hlim := tendsto_measure_iInter_nnreal (μ := μ)
      (s := fun n ↦ FKLimit.restrictionNeighborhood K (e.box n) ∩
        FKLimit.restrictionNeighborhood L (e.box n)) hmeas hanti
    have hKi : (⋂ n, FKLimit.restrictionNeighborhood K (e.box n)) = K :=
      FKLimit.iInter_restrictionNeighborhood e hK.isClosed
    have hLi : (⋂ n, FKLimit.restrictionNeighborhood L (e.box n)) = L :=
      FKLimit.iInter_restrictionNeighborhood e hL.isClosed
    have h3 : (⋂ n, (FKLimit.restrictionNeighborhood K (e.box n) ∩
        FKLimit.restrictionNeighborhood L (e.box n)))
        = (⋂ n, FKLimit.restrictionNeighborhood K (e.box n)) ∩
          (⋂ n, FKLimit.restrictionNeighborhood L (e.box n)) := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      exact ⟨fun h ↦ ⟨fun n ↦ (h n).1, fun n ↦ (h n).2⟩,
        fun h n ↦ ⟨h.1 n, h.2 n⟩⟩
    rw [h3, hKi, hLi] at hlim
    exact hlim
  have hmulcoe : Tendsto (fun n ↦ ((μ (FKLimit.restrictionNeighborhood K (e.box n)) *
      μ (FKLimit.restrictionNeighborhood L (e.box n)) : NNReal) : ENNReal)) atTop
      (𝓝 ((μ K * μ L : NNReal) : ENNReal)) := ENNReal.tendsto_coe.mpr hmullim
  have hKLcoe : Tendsto (fun n ↦ ((μ (FKLimit.restrictionNeighborhood K (e.box n) ∩
      FKLimit.restrictionNeighborhood L (e.box n)) : NNReal) : ENNReal)) atTop
      (𝓝 ((μ (K ∩ L) : NNReal) : ENNReal)) := ENNReal.tendsto_coe.mpr hKLlim
  rw [← coe_apply_probabilityMeasure μ K, ← coe_apply_probabilityMeasure μ L,
    ← coe_apply_probabilityMeasure μ (K ∩ L), ← ENNReal.coe_mul]
  refine le_of_tendsto_of_tendsto hmulcoe hKLcoe (Eventually.of_forall fun n ↦ ?_)
  beta_reduce
  rw [ENNReal.coe_mul, coe_apply_probabilityMeasure μ _,
    coe_apply_probabilityMeasure μ _, coe_apply_probabilityMeasure μ _]
  exact hcyl _ _ _ (FKLimit.dependsOnCoordinates_restrictionNeighborhood K _)
    (FKLimit.dependsOnCoordinates_restrictionNeighborhood L _)
    (FKLimit.restrictionNeighborhood_isUpperSet hKup _)
    (FKLimit.restrictionNeighborhood_isUpperSet hLup _)

/-- **FKG with one compact increasing and one measurable increasing event.** -/
theorem mul_le_inter_of_isCompact_upper_right
    (hcomp : ∀ {K L : Set (Configuration E)}, IsCompact K → IsUpperSet K →
      IsCompact L → IsUpperSet L →
      (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) L ≤
        (μ : Measure (Configuration E)) (K ∩ L))
    {K D : Set (Configuration E)} (hK : IsCompact K) (hKup : IsUpperSet K)
    (hD : MeasurableSet D) (hDup : IsUpperSet D) :
    (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) D ≤
      (μ : Measure (Configuration E)) (K ∩ D) := by
  have hreg := MeasurableSet.measure_eq_iSup_isCompact hD (μ : Measure (Configuration E))
  calc (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) D
      = (μ : Measure (Configuration E)) K *
          (⨆ (L : Set (Configuration E)), ⨆ (_ : L ⊆ D), ⨆ (_ : IsCompact L),
            (μ : Measure (Configuration E)) L) := by rw [hreg]
    _ = ⨆ (L : Set (Configuration E)), ⨆ (_ : L ⊆ D), ⨆ (_ : IsCompact L),
          (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) L := by
        rw [ENNReal.mul_iSup]
        simp only [ENNReal.mul_iSup]
    _ ≤ (μ : Measure (Configuration E)) (K ∩ D) := by
        refine iSup_le fun L ↦ iSup_le fun hLD ↦ iSup_le fun hLc ↦ ?_
        calc (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) L
            ≤ (μ : Measure (Configuration E)) K *
                (μ : Measure (Configuration E)) (↑(upperClosure L)) := by
              gcongr
              exact subset_upperClosure
          _ ≤ (μ : Measure (Configuration E)) (K ∩ ↑(upperClosure L)) :=
              hcomp hK hKup (FKLimit.isCompact_upperClosure hLc) (upperClosure L).upper
          _ ≤ (μ : Measure (Configuration E)) (K ∩ D) := by
              gcongr
              exact upperClosure_min hLD hDup


/-- **FKG for all pairs of increasing measurable events.** -/
theorem mul_le_inter_of_measurable_upper
    (hcomp : ∀ {K D : Set (Configuration E)}, IsCompact K → IsUpperSet K →
      MeasurableSet D → IsUpperSet D →
      (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) D ≤
        (μ : Measure (Configuration E)) (K ∩ D))
    {A B : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hB : MeasurableSet B) (hBup : IsUpperSet B) :
    (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) B ≤
      (μ : Measure (Configuration E)) (A ∩ B) := by
  have hreg := MeasurableSet.measure_eq_iSup_isCompact hA (μ : Measure (Configuration E))
  calc (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) B
      = (⨆ (K : Set (Configuration E)), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K),
            (μ : Measure (Configuration E)) K) *
          (μ : Measure (Configuration E)) B := by rw [hreg]
    _ = ⨆ (K : Set (Configuration E)), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K),
          (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) B := by
        rw [ENNReal.iSup_mul]
        simp only [ENNReal.iSup_mul]
    _ ≤ (μ : Measure (Configuration E)) (A ∩ B) := by
        refine iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hKc ↦ ?_
        calc (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) B
            ≤ (μ : Measure (Configuration E)) (↑(upperClosure K)) *
                (μ : Measure (Configuration E)) B := by
              gcongr
              exact subset_upperClosure
          _ ≤ (μ : Measure (Configuration E)) (↑(upperClosure K) ∩ B) :=
              hcomp (FKLimit.isCompact_upperClosure hKc) (upperClosure K).upper hB hBup
          _ ≤ (μ : Measure (Configuration E)) (A ∩ B) := by
              gcongr
              exact upperClosure_min hKA hAup


end Approximation

/-! ## Part 5: the infinite-volume FKG inequality for FK limits -/

section Main

variable {E : Type*} [Countable E]

/-- **Infinite-volume FKG (positive association) for an FK weak limit.**
Any weak limit of genuine finite-box FK laws along a box exhaustion, with
arbitrary boundary setoids, at `q ≥ 1` and `0 ≤ p ≤ 1`, satisfies the FKG
inequality for every pair of increasing measurable events. -/
theorem mul_le_inter_of_isFKLimit {exh : BoxExhaustion E} {q p : NNReal}
    (hq : 1 ≤ q) (hp : p ≤ 1)
    {α : ∀ n, (exh.box n).BoundaryPartition} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp α μ)
    {A B : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hB : MeasurableSet B) (hBup : IsUpperSet B) :
    (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) B ≤
      (μ : Measure (Configuration E)) (A ∩ B) := by
  have hcyl : ∀ (A C : Set (Configuration E)) (S : Finset E),
      FKLimit.DependsOnCoordinates A S → FKLimit.DependsOnCoordinates C S →
      IsUpperSet A → IsUpperSet C →
      (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) C ≤
        (μ : Measure (Configuration E)) (A ∩ C) := by
    intro A C S hAS hCS hAup' hCup'
    rw [← coe_apply_probabilityMeasure μ A, ← coe_apply_probabilityMeasure μ C,
      ← coe_apply_probabilityMeasure μ (A ∩ C), ← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr
      (cylinder_mul_le_inter_of_isFKLimit hq hp hμ hAS hCS hAup' hCup')
  have hcomp : ∀ {K L : Set (Configuration E)}, IsCompact K → IsUpperSet K →
      IsCompact L → IsUpperSet L →
      (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) L ≤
        (μ : Measure (Configuration E)) (K ∩ L) :=
    fun hK hKup hL hLup ↦ mul_le_inter_of_isCompact_upper hcyl hK hKup hL hLup
  have hcomp' : ∀ {K D : Set (Configuration E)}, IsCompact K → IsUpperSet K →
      MeasurableSet D → IsUpperSet D →
      (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) D ≤
        (μ : Measure (Configuration E)) (K ∩ D) :=
    fun hK hKup hD hDup ↦ mul_le_inter_of_isCompact_upper_right hcomp hK hKup hD hDup
  exact mul_le_inter_of_measurable_upper hcomp' hA hAup hB hBup

/-- **Infinite-volume FKG for the whole FK-limit class** at `q ≥ 1`. -/
theorem mul_le_inter_of_mem_fkLimitMeasures {exh : BoxExhaustion E} {q p : NNReal}
    (hq : 1 ≤ q) (hp : p ≤ 1)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ FKLimitMeasures exh (lt_of_lt_of_le zero_lt_one hq) hp)
    {A B : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hB : MeasurableSet B) (hBup : IsUpperSet B) :
    (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) B ≤
      (μ : Measure (Configuration E)) (A ∩ B) := by
  obtain ⟨α, hα⟩ := hμ
  exact mul_le_inter_of_isFKLimit hq hp hα hA hAup hB hBup

/-- The same infinite-volume FKG inequality in `ℝ≥0`-valued form. -/
theorem apply_mul_le_apply_inter_of_isFKLimit {exh : BoxExhaustion E} {q p : NNReal}
    (hq : 1 ≤ q) (hp : p ≤ 1)
    {α : ∀ n, (exh.box n).BoundaryPartition} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp α μ)
    {A B : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hB : MeasurableSet B) (hBup : IsUpperSet B) :
    μ A * μ B ≤ μ (A ∩ B) := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul,
    coe_apply_probabilityMeasure μ A, coe_apply_probabilityMeasure μ B,
    coe_apply_probabilityMeasure μ (A ∩ B)]
  exact mul_le_inter_of_isFKLimit hq hp hμ hA hAup hB hBup

/-- **Infinite-volume FKG, up/down form.**  Under an FK weak limit at `q ≥ 1`,
an increasing and a decreasing measurable event are negatively correlated.
This is the infinite-volume analogue of `FK.InfiniteVolume.NoEscape.PosAssoc`. -/
theorem inter_le_mul_of_isFKLimit {exh : BoxExhaustion E} {q p : NNReal}
    (hq : 1 ≤ q) (hp : p ≤ 1)
    {α : ∀ n, (exh.box n).BoundaryPartition} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp α μ)
    {A D : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hD : MeasurableSet D) (hDdown : IsLowerSet D) :
    (μ : Measure (Configuration E)) (A ∩ D) ≤
      (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) D := by
  have hDup : IsUpperSet Dᶜ := by
    intro x y hxy hx hy
    exact hx (hDdown hxy hy)
  have hcross := mul_le_inter_of_isFKLimit hq hp hμ hA hAup
    hD.compl hDup
  have hfA : (μ : Measure (Configuration E)) A ≠ ⊤ := measure_ne_top _ _
  have hfD : (μ : Measure (Configuration E)) D ≠ ⊤ := measure_ne_top _ _
  have hfDc : (μ : Measure (Configuration E)) Dᶜ ≠ ⊤ := measure_ne_top _ _
  have hfAD : (μ : Measure (Configuration E)) (A ∩ D) ≠ ⊤ := measure_ne_top _ _
  have hfADc : (μ : Measure (Configuration E)) (A ∩ Dᶜ) ≠ ⊤ := measure_ne_top _ _
  have hsplit : (μ : Measure (Configuration E)) A =
      (μ : Measure (Configuration E)) (A ∩ D) +
        (μ : Measure (Configuration E)) (A ∩ Dᶜ) := by
    have h := measure_inter_add_sdiff (μ := (μ : Measure (Configuration E))) A hD
    have hset : A \ D = A ∩ Dᶜ := by
      ext ω
      simp [Set.mem_sdiff, Set.mem_inter_iff]
    rw [hset] at h
    exact h.symm
  have hcompl : (μ : Measure (Configuration E)) D +
      (μ : Measure (Configuration E)) Dᶜ = 1 := by
    have h := measure_add_measure_compl (μ := (μ : Measure (Configuration E))) hD
    simpa using h
  have hreal : ((μ : Measure (Configuration E)) (A ∩ D)).toReal ≤
      ((μ : Measure (Configuration E)) A).toReal *
        ((μ : Measure (Configuration E)) D).toReal := by
    have h1 : ((μ : Measure (Configuration E)) A).toReal =
        ((μ : Measure (Configuration E)) (A ∩ D)).toReal +
          ((μ : Measure (Configuration E)) (A ∩ Dᶜ)).toReal := by
      rw [hsplit, ENNReal.toReal_add hfAD hfADc]
    have h2 : ((μ : Measure (Configuration E)) D).toReal +
        ((μ : Measure (Configuration E)) Dᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add hfD hfDc, hcompl, ENNReal.toReal_one]
    have h3 : ((μ : Measure (Configuration E)) A).toReal *
        ((μ : Measure (Configuration E)) Dᶜ).toReal ≤
          ((μ : Measure (Configuration E)) (A ∩ Dᶜ)).toReal := by
      rw [← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono hfADc hcross
    have hd : ((μ : Measure (Configuration E)) D).toReal =
        1 - ((μ : Measure (Configuration E)) Dᶜ).toReal := by linarith
    have hmul : ((μ : Measure (Configuration E)) A).toReal *
        ((μ : Measure (Configuration E)) D).toReal =
          ((μ : Measure (Configuration E)) A).toReal -
            ((μ : Measure (Configuration E)) A).toReal *
              ((μ : Measure (Configuration E)) Dᶜ).toReal := by
      rw [hd]; ring
    rw [hmul]
    linarith
  rw [← ENNReal.toReal_le_toReal hfAD (ENNReal.mul_ne_top hfA hfD),
    ENNReal.toReal_mul]
  exact hreal

/-- The up/down form of infinite-volume FKG in `ℝ≥0`-valued form, matching the
finite `PosAssoc` shape. -/
theorem apply_inter_le_mul_of_isFKLimit {exh : BoxExhaustion E} {q p : NNReal}
    (hq : 1 ≤ q) (hp : p ≤ 1)
    {α : ∀ n, (exh.box n).BoundaryPartition} {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh (lt_of_lt_of_le zero_lt_one hq) hp α μ)
    {A D : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hD : MeasurableSet D) (hDdown : IsLowerSet D) :
    μ (A ∩ D) ≤ μ A * μ D := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul,
    coe_apply_probabilityMeasure μ (A ∩ D), coe_apply_probabilityMeasure μ A,
    coe_apply_probabilityMeasure μ D]
  exact inter_le_mul_of_isFKLimit hq hp hμ hA hAup hD hDdown

section Nonvacuity

/-- **Non-vacuity of the limit hypothesis.**  At `q = 1`, every box exhaustion
and boundary schedule has the Bernoulli product as an FK weak limit
(`FK.InfiniteVolume.QOne.isFKLimit_q_one`), so the infinite-volume FKG theorem
applies to it. -/
theorem bernoulliConst_mul_le_inter (exh : BoxExhaustion E) {p : NNReal} (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {A B : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hB : MeasurableSet B) (hBup : IsUpperSet B) :
    ((QOne.bernoulliConst p hp : ProbabilityMeasure (Configuration E)) :
        Measure (Configuration E)) A *
        ((QOne.bernoulliConst p hp : ProbabilityMeasure (Configuration E)) :
          Measure (Configuration E)) B ≤
      ((QOne.bernoulliConst p hp : ProbabilityMeasure (Configuration E)) :
        Measure (Configuration E)) (A ∩ B) :=
  mul_le_inter_of_isFKLimit (exh := exh) (q := 1) (p := p) le_rfl hp
    (QOne.isFKLimit_q_one exh hp α) hA hAup hB hBup

end Nonvacuity

/-- **Weak-limit transfer principle.**  If a sequence of probability measures on
the countable Boolean product converges weakly to `μ`, and each member satisfies
the FKG inequality on finitely supported increasing events, then `μ` satisfies
the FKG inequality for **all** measurable increasing events.

This is the abstract form of the passage used for FK limits: hypotheses on
cylinders only, conclusion on the whole product `σ`-algebra. -/
theorem mul_le_inter_of_tendsto_of_cylinder {μs : ℕ → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hcyl : ∀ (n : ℕ) (A C : Set (Configuration E)) (S : Finset E),
      FKLimit.DependsOnCoordinates A S → FKLimit.DependsOnCoordinates C S →
      IsUpperSet A → IsUpperSet C →
      (μs n : Measure (Configuration E)) A * (μs n : Measure (Configuration E)) C ≤
        (μs n : Measure (Configuration E)) (A ∩ C))
    {A B : Set (Configuration E)} (hA : MeasurableSet A) (hAup : IsUpperSet A)
    (hB : MeasurableSet B) (hBup : IsUpperSet B) :
    (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) B ≤
      (μ : Measure (Configuration E)) (A ∩ B) := by
  have hlimcyl : ∀ (A C : Set (Configuration E)) (S : Finset E),
      FKLimit.DependsOnCoordinates A S → FKLimit.DependsOnCoordinates C S →
      IsUpperSet A → IsUpperSet C →
      (μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) C ≤
        (μ : Measure (Configuration E)) (A ∩ C) := by
    intro A C S hAS hCS hAup' hCup'
    have hAC : FKLimit.DependsOnCoordinates (A ∩ C) S := by
      intro ω η hωη
      rw [Set.mem_inter_iff, Set.mem_inter_iff, hAS ω η hωη, hCS ω η hωη]
    have h1 : Tendsto (fun n ↦ (μs n : Measure (Configuration E)) A) atTop
        (𝓝 ((μ : Measure (Configuration E)) A)) := by
      have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAS.isClopen
      have h2 := (ENNReal.tendsto_coe (f := atTop) (m := fun n ↦ μs n A) (a := μ A)).mpr h
      simpa only [coe_apply_probabilityMeasure] using h2
    have h3 : Tendsto (fun n ↦ (μs n : Measure (Configuration E)) C) atTop
        (𝓝 ((μ : Measure (Configuration E)) C)) := by
      have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hCS.isClopen
      have h2 := (ENNReal.tendsto_coe (f := atTop) (m := fun n ↦ μs n C) (a := μ C)).mpr h
      simpa only [coe_apply_probabilityMeasure] using h2
    have h4 : Tendsto (fun n ↦ (μs n : Measure (Configuration E)) (A ∩ C)) atTop
        (𝓝 ((μ : Measure (Configuration E)) (A ∩ C))) := by
      have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAC.isClopen
      have h2 := (ENNReal.tendsto_coe (f := atTop) (m := fun n ↦ μs n (A ∩ C)) (a := μ (A ∩ C))).mpr h
      simpa only [coe_apply_probabilityMeasure] using h2
    have h12 : Tendsto (fun n ↦ (μs n : Measure (Configuration E)) A *
        (μs n : Measure (Configuration E)) C) atTop
        (𝓝 ((μ : Measure (Configuration E)) A * (μ : Measure (Configuration E)) C)) := by
      have := (ENNReal.tendsto_coe (f := atTop) (m := fun n ↦ μs n A * μs n C) (a := μ A * μ C)).mpr
        (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hAS.isClopen
          |>.mul (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hμ hCS.isClopen))
      simpa only [coe_apply_probabilityMeasure, ENNReal.coe_mul] using this
    exact le_of_tendsto_of_tendsto h12 h4 (Eventually.of_forall fun n ↦
      hcyl n A C S hAS hCS hAup' hCup')
  have hcomp : ∀ {K L : Set (Configuration E)}, IsCompact K → IsUpperSet K →
      IsCompact L → IsUpperSet L →
      (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) L ≤
        (μ : Measure (Configuration E)) (K ∩ L) :=
    fun hK hKup hL hLup ↦ mul_le_inter_of_isCompact_upper hlimcyl hK hKup hL hLup
  have hcomp' : ∀ {K D : Set (Configuration E)}, IsCompact K → IsUpperSet K →
      MeasurableSet D → IsUpperSet D →
      (μ : Measure (Configuration E)) K * (μ : Measure (Configuration E)) D ≤
        (μ : Measure (Configuration E)) (K ∩ D) :=
    fun hK hKup hD hDup ↦ mul_le_inter_of_isCompact_upper_right hcomp hK hKup hD hDup
  exact mul_le_inter_of_measurable_upper hcomp' hA hAup hB hBup

end Main

/-! ## Axiom audit of the principal exports -/

#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.fkMeasure_mul_le_inter
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.fkMeasure_mono_p_of_lt_one
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.finiteVolumeLaw_apply_preimage
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.finiteVolumeLaw_mul_le_inter
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.finiteVolumeLaw_mono_p
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.coe_apply_probabilityMeasure
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.cylinder_mul_le_inter_of_isFKLimit
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.stochasticallyDominates_of_isFKLimit_p
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.tendsto_measure_iInter_nnreal
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.mul_le_inter_of_isCompact_upper
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.mul_le_inter_of_isCompact_upper_right
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.mul_le_inter_of_measurable_upper
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.mul_le_inter_of_tendsto_of_cylinder
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.mul_le_inter_of_isFKLimit
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.mul_le_inter_of_mem_fkLimitMeasures
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.apply_mul_le_apply_inter_of_isFKLimit
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.inter_le_mul_of_isFKLimit
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.apply_inter_le_mul_of_isFKLimit
#print axioms FK.InfiniteVolume.InfiniteVolumeFKG.bernoulliConst_mul_le_inter

end InfiniteVolumeFKG

end FK.InfiniteVolume
