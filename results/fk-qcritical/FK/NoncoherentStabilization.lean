import FK.NoncoherentFiniteEnergy

/-!
# Local stabilization for noncoherent FK specifications

This file isolates the analytic step needed when the boundary specification on a
fixed box changes with the approximating measure.  Pointwise convergence of
finite-valued boundary assignments is not enough for weak reconstruction.  The
hypothesis used below instead gives, almost everywhere under the limiting
exterior law, one neighbourhood on which all sufficiently late assignments
agree with the limiting assignment.

The first parts are topological and measure-theoretic.  The final definitions
specialize them to actual FK conditional laws.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.NoncoherentStabilization

open NonlocalInterior ConventionGeometry ConventionTransport

noncomputable section

/-- A sequence of specifications stabilizes locally in both the sequence index
and the exterior variable.  Crucially, `U` and the eventual-in-`l` statement
are uniform over `U`; pointwise convergence alone does not imply this. -/
def LocallyStabilizes {X J ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (l : Filter ι) (μ : Measure X) (α : ι → X → J) (β : X → J) : Prop :=
  ∀ᵐ x ∂μ, ∃ U ∈ 𝓝 x, ∀ᶠ i in l, Set.EqOn (α i) β U

/-- Two-sided additive errors which tend to zero identify the limit.  This
form avoids subtraction and is valid at every finite or infinite endpoint. -/
theorem tendsto_of_le_add_of_le_add {ι : Type*} {l : Filter ι} [l.NeBot]
    {a b c : ι → ℝ≥0∞} {d : ℝ≥0∞}
    (hb : Tendsto b l (𝓝 d)) (hc : Tendsto c l (𝓝 0))
    (hab : ∀ᶠ i in l, a i ≤ b i + c i)
    (hba : ∀ᶠ i in l, b i ≤ a i + c i) : Tendsto a l (𝓝 d) := by
  apply tendsto_of_le_liminf_of_limsup_le
    (h := ⟨⊤, by simp⟩) (h' := ⟨0, by simp⟩)
  · calc
      d = liminf b l := hb.liminf_eq.symm
      _ ≤ liminf (fun i => a i + c i) l := liminf_le_liminf hba
      _ = liminf a l := by
        exact ENNReal.liminf_add_of_right_tendsto_zero hc a
  · calc
      limsup a l ≤ limsup (fun i => b i + c i) l := limsup_le_limsup hab
      _ = limsup b l := ENNReal.limsup_add_of_right_tendsto_zero hc b
      _ = d := hb.limsup_eq

/-- Local stabilization makes the exceptional-measure sequence tend to zero.
The exceptional sets need not be measurable: all estimates bound them by a
closed set before applying Portmanteau. -/
theorem tendsto_measure_disagreement
    {X J ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X] [T2Space X]
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hμ : Tendsto μs l (𝓝 μ))
    {α : ι → X → J} {β : X → J}
    (hstab : LocallyStabilizes l (μ : Measure X) α β) :
    Tendsto (fun i => (μs i : Measure X) {x | α i x ≠ β x}) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  let G : Set X := {x | ∃ U ∈ 𝓝 x, ∀ᶠ i in l, Set.EqOn (α i) β U}
  have hG : G ∈ ae (μ : Measure X) := hstab
  obtain ⟨T, hGT, hTmeas, hTzero⟩ :=
    exists_measurable_superset_of_null (mem_ae_iff.mp hG)
  let S : Set X := Tᶜ
  have hSmeas : MeasurableSet S := hTmeas.compl
  have hSG : S ⊆ G := by
    intro x hxS
    by_contra hxG
    exact hxS (hGT hxG)
  have hSzero : (μ : Measure X) Sᶜ = 0 := by
    simpa only [S, compl_compl] using hTzero
  obtain ⟨K, hKS, hKcompact, hKsmall⟩ :=
    hSmeas.exists_isCompact_sdiff_lt (measure_ne_top (μ : Measure X) S) hε.ne'
  have hKcompl : (μ : Measure X) Kᶜ < ε := by
    have hKcompl' : Kᶜ = Sᶜ ∪ (S \ K) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_sdiff]
      constructor
      · intro hxK
        by_cases hxS : x ∈ S
        · exact Or.inr ⟨hxS, hxK⟩
        · exact Or.inl hxS
      · rintro (hxS | ⟨_hxS, hxK⟩)
        · exact fun hxK => hxS (hKS hxK)
        · exact hxK
    rw [hKcompl']
    calc
      (μ : Measure X) (Sᶜ ∪ (S \ K)) ≤
          (μ : Measure X) Sᶜ + (μ : Measure X) (S \ K) := measure_union_le _ _
      _ < ε := by simpa only [hSzero, zero_add] using hKsmall
  have hpoint : ∀ x : K, ∃ U : Set X, U ∈ 𝓝 (x : X) ∧
      ∀ᶠ i in l, Set.EqOn (α i) β U :=
    fun x => hSG (hKS x.2)
  choose U hUnhds hUtail using hpoint
  have hopen : ∀ x : K, ∃ V : Set X, V ⊆ U x ∧ IsOpen V ∧ (x : X) ∈ V :=
    fun x => mem_nhds_iff.mp (hUnhds x)
  choose V hVU hVopen hxV using hopen
  have hKcover : K ⊆ ⋃ x : K, V x := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover V hVopen hKcover
  let W : Set X := ⋃ x ∈ t, V x
  have hKW : K ⊆ W := by
    intro y hy
    apply ht hy
  have hWopen : IsOpen W := isOpen_biUnion fun x _ => hVopen x
  have hWtail : ∀ᶠ i in l, Set.EqOn (α i) β W := by
    have ht' : ∀ᶠ i in l, ∀ x ∈ t, Set.EqOn (α i) β (V x) := by
      rw [Finset.eventually_all]
      intro x hx
      filter_upwards [hUtail x] with i hi
      exact fun y hy => hi (hVU x hy)
    filter_upwards [ht'] with i hi y hy
    simp only [W, Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyV⟩ := hy
    exact hi x hx hyV
  have hWU : (μ : Measure X) Wᶜ < ε :=
    (measure_mono (compl_subset_compl.mpr hKW)).trans_lt hKcompl
  have hlimsup : l.limsup (fun i => (μs i : Measure X) Wᶜ) < ε :=
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ
      hWopen.isClosed_compl).trans_lt hWU
  filter_upwards [hWtail, eventually_lt_of_limsup_lt hlimsup] with i hi hWi
  have hsub : {x | α i x ≠ β x} ⊆ Wᶜ := by
    intro x hx hxW
    exact hx (hi hxW)
  exact (measure_mono hsub).trans hWi.le

/-- Lower integrals of a varying finite-index statistic converge when the
indices stabilize locally almost everywhere.  The fixed-index theorem is used
only for the reference index `β`; the mismatch is bounded by the disagreement
mass from the previous theorem. -/
theorem tendsto_lintegral_indexed_of_tendsto_of_locallyStabilizes
    {X J ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [SecondCountableTopology X]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace X] [T2Space X]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableEq J] [Finite J]
    {l : Filter ι} [l.NeBot] {μs : ι → ProbabilityMeasure X}
    {μ : ProbabilityMeasure X} (hμ : Tendsto μs l (𝓝 μ))
    (α : ι → X → J) (hα : ∀ i, Measurable (α i))
    (β : X → J) (hβ : Measurable β)
    (hstab : LocallyStabilizes l (μ : Measure X) α β)
    (hlocalβ : ∀ᵐ x ∂(μ : Measure X), ∀ᶠ y in 𝓝 x, β y = β x)
    (g : J → ℝ≥0∞) (hg : Measurable g)
    (C : ℝ≥0∞) (hCtop : C ≠ ∞) (hgC : ∀ a, g a ≤ C) :
    Tendsto (fun i => ∫⁻ x, g (α i x) ∂(μs i : Measure X)) l
      (𝓝 (∫⁻ x, g (β x) ∂(μ : Measure X))) := by
  have hb : Tendsto (fun i => ∫⁻ x, g (β x) ∂(μs i : Measure X)) l
      (𝓝 (∫⁻ x, g (β x) ∂(μ : Measure X))) :=
    NonlocalInterior.tendsto_lintegral_indexed_of_tendsto hμ β hβ hlocalβ g
      (fun a => ne_top_of_le_ne_top hCtop (hgC a))
  have hD (i : ι) : MeasurableSet {x | α i x ≠ β x} := by
    exact (measurableSet_eq_fun (hα i) hβ).compl
  have herr : Tendsto
      (fun i => C * (μs i : Measure X) {x | α i x ≠ β x}) l (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul
      (tendsto_measure_disagreement hμ hstab) (a := C) (Or.inr hCtop)
    simpa only [mul_zero] using h
  have hpoint (i : ι) (x : X) : g (α i x) ≤
      g (β x) + {y | α i y ≠ β y}.indicator (fun _ => C) x := by
    by_cases hx : α i x = β x
    · simp [hx]
    · rw [Set.indicator_of_mem hx]
      calc
        g (α i x) ≤ C := hgC _
        _ = 0 + C := (zero_add _).symm
        _ ≤ g (β x) + C := add_le_add (zero_le) le_rfl
  have hpoint' (i : ι) (x : X) : g (β x) ≤
      g (α i x) + {y | α i y ≠ β y}.indicator (fun _ => C) x := by
    by_cases hx : α i x = β x
    · simp [hx]
    · rw [Set.indicator_of_mem hx]
      calc
        g (β x) ≤ C := hgC _
        _ = 0 + C := (zero_add _).symm
        _ ≤ g (α i x) + C := add_le_add (zero_le) le_rfl
  have hab : ∀ i, (∫⁻ x, g (α i x) ∂(μs i : Measure X)) ≤
      (∫⁻ x, g (β x) ∂(μs i : Measure X)) +
        C * (μs i : Measure X) {x | α i x ≠ β x} := by
    intro i
    calc
      (∫⁻ x, g (α i x) ∂(μs i : Measure X)) ≤
          ∫⁻ x, (g (β x) + {y | α i y ≠ β y}.indicator (fun _ => C) x)
            ∂(μs i : Measure X) := lintegral_mono (hpoint i)
      _ = (∫⁻ x, g (β x) ∂(μs i : Measure X)) +
          C * (μs i : Measure X) {x | α i x ≠ β x} := by
        have hgβ : Measurable (fun x => g (β x)) := hg.comp hβ
        rw [lintegral_add_left hgβ, lintegral_indicator_const (hD i)]
  have hba : ∀ i, (∫⁻ x, g (β x) ∂(μs i : Measure X)) ≤
      (∫⁻ x, g (α i x) ∂(μs i : Measure X)) +
        C * (μs i : Measure X) {x | α i x ≠ β x} := by
    intro i
    calc
      (∫⁻ x, g (β x) ∂(μs i : Measure X)) ≤
          ∫⁻ x, (g (α i x) + {y | α i y ≠ β y}.indicator (fun _ => C) x)
            ∂(μs i : Measure X) := lintegral_mono (hpoint' i)
      _ = (∫⁻ x, g (α i x) ∂(μs i : Measure X)) +
          C * (μs i : Measure X) {x | α i x ≠ β x} := by
        have hgα : Measurable (fun x => g (α i x)) := hg.comp (hα i)
        rw [lintegral_add_left hgα, lintegral_indicator_const (hD i)]
  exact tendsto_of_le_add_of_le_add hb herr
    (Eventually.of_forall hab) (Eventually.of_forall hba)

local instance boundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- Weak closure for a genuinely varying FK boundary specification.  The
source laws need only satisfy DLR for their own specifications; no source
`BoundaryConvention` is required.  The eventual common neighbourhood is the
additional noncoherent stabilization input. -/
theorem isDLR_of_tendsto_of_locallyStabilizes
    {E ι : Type*} [Countable E] (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ι → B.Exterior → B.BoundaryPartition) (hα : ∀ i, Measurable (α i))
    (β : B.Exterior → B.BoundaryPartition) (hβ : Measurable β)
    {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ᶠ i in l, B.IsDLR hq hp (α i) (hα i) (μs i))
    (hstab : LocallyStabilizes l (B.exteriorMeasure μ : Measure B.Exterior) α β)
    (hlocalβ : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      ∀ᶠ ζ in 𝓝 η, β ζ = β η) : B.IsDLR hq hp β hβ μ := by
  apply InteriorWeakLimit.FiniteBox.isDLR_of_eq_reconstruct B hq hp β hβ μ
  apply ProbabilityMeasure.toMeasure_injective
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro T S
  let A : Set (Configuration E) := cylinder T S
  have hA : FKLimit.DependsOnCoordinates A T := dependsOnCoordinates_cylinder T S
  have hleft : Tendsto (fun i => (μs i : Measure (Configuration E)) A) l
      (𝓝 ((μ : Measure (Configuration E)) A)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (by simp [hA.isClopen])
  let idx : ι → B.Exterior → B.BoundaryPartition ×
      (NonlocalInterior.exteriorSupport B T → Bool) :=
    fun i η => (α i η, fun e => η e)
  let idx₀ : B.Exterior → B.BoundaryPartition ×
      (NonlocalInterior.exteriorSupport B T → Bool) :=
    fun η => (β η, fun e => η e)
  let g : B.BoundaryPartition ×
      (NonlocalInterior.exteriorSupport B T → Bool) → ℝ≥0∞ := fun z =>
    (B.conditionalLaw hq hp (fun _ => z.1) (NonlocalInterior.extendExterior B z.2) :
      Measure (Configuration E)) A
  have hidx (i : ι) : Measurable (idx i) := by
    apply Measurable.prodMk (hα i)
    exact Measurable.of_eval fun e => measurable_pi_apply e.1
  have hidx₀ : Measurable idx₀ := by
    apply Measurable.prodMk hβ
    exact Measurable.of_eval fun e => measurable_pi_apply e.1
  have hstabIdx : LocallyStabilizes l
      (B.exteriorMeasure μ : Measure B.Exterior) idx idx₀ := by
    filter_upwards [hstab] with η hη
    obtain ⟨U, hU, hi⟩ := hη
    let V : Set B.Exterior :=
      (↑(NonlocalInterior.exteriorSupport B T) : Set {e : E // e ∉ B.edges}).pi
        (fun e => {η e})
    have hV : V ∈ 𝓝 η :=
      set_pi_mem_nhds (NonlocalInterior.exteriorSupport B T).finite_toSet
        (fun _ _ => by simp)
    refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
    filter_upwards [hi] with i hi ζ hζ
    apply Prod.ext (hi hζ.1)
    rfl
  have hlocalIdx₀ : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      ∀ᶠ ζ in 𝓝 η, idx₀ ζ = idx₀ η := by
    filter_upwards [hlocalβ] with η hη
    let V : Set B.Exterior :=
      (↑(NonlocalInterior.exteriorSupport B T) : Set {e : E // e ∉ B.edges}).pi
        (fun e => {η e})
    have hV : V ∈ 𝓝 η :=
      set_pi_mem_nhds (NonlocalInterior.exteriorSupport B T).finite_toSet
        (fun _ _ => by simp)
    filter_upwards [hη, hV] with ζ hζα hζ
    apply Prod.ext hζα
    funext e
    exact hζ e.1 e.2
  have hfun (γ : B.Exterior → B.BoundaryPartition) (η : B.Exterior) :
      (B.conditionalLaw hq hp γ η : Measure (Configuration E)) A =
        g (γ η, fun e => η e) := by
    dsimp only [g]
    apply NonlocalInterior.conditionalLaw_apply_eq_of_agree B hq hp γ η
      (NonlocalInterior.extendExterior B (fun e => η e)) hA
    intro e he
    simp only [NonlocalInterior.extendExterior]
    split_ifs with hes
    · rfl
    · exact (hes (Finset.mem_subtype.mpr he)).elim
  have hint : Tendsto
      (fun i => ∫⁻ η, (B.conditionalLaw hq hp (α i) η :
        Measure (Configuration E)) A ∂(B.exteriorMeasure (μs i) : Measure B.Exterior)) l
      (𝓝 (∫⁻ η, (B.conditionalLaw hq hp β η : Measure (Configuration E)) A
        ∂(B.exteriorMeasure μ : Measure B.Exterior))) := by
    have h := tendsto_lintegral_indexed_of_tendsto_of_locallyStabilizes
      (InteriorWeakLimit.FiniteBox.tendsto_exteriorMeasure B hμ)
      idx hidx idx₀ hidx₀ hstabIdx hlocalIdx₀ g (measurable_of_finite _)
      1 ENNReal.one_ne_top (fun _ => prob_le_one)
    simpa only [idx, idx₀, ← hfun] using h
  have hright : Tendsto
      (fun i => (InteriorWeakLimit.FiniteBox.reconstruct B hq hp (α i) (hα i) (μs i) :
        Measure (Configuration E)) A) l
      (𝓝 ((InteriorWeakLimit.FiniteBox.reconstruct B hq hp β hβ μ :
        Measure (Configuration E)) A)) := by
    simpa only [NonlocalInterior.apply_reconstruct B hq hp, hA.measurableSet] using hint
  apply tendsto_nhds_unique (l := l)
    (f := fun i => (μs i : Measure (Configuration E)) A)
    (a := (μ : Measure (Configuration E)) A)
    (b := (InteriorWeakLimit.FiniteBox.reconstruct B hq hp β hβ μ :
      Measure (Configuration E)) A)
  · exact hleft
  · apply hright.congr'
    filter_upwards [hDLR] with i hi
    exact congrArg (fun ν : ProbabilityMeasure (Configuration E) =>
      (ν : Measure (Configuration E)) A)
      (InteriorWeakLimit.FiniteBox.eq_reconstruct_of_isDLR
        B hq hp (α i) (hα i) (μs i) hi).symm

/-- Full-exhaustion form of varying-source locally stabilized DLR closure. -/
theorem mem_dlrMeasures_of_tendsto_of_locallyStabilizes
    {E ι : Type*} [Countable E] (exh : BoxExhaustion E)
    (α : ι → BoundaryAssignment exh.box)
    (β : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration E)}
    {μ : ProbabilityMeasure (Configuration E)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ n, ∀ᶠ i in l, (exh.box n).IsDLR hq hp
      ((α i).partition n) ((α i).measurable_partition n) (μs i))
    (hstab : ∀ n, LocallyStabilizes l
      ((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior)
      (fun i => (α i).partition n) (β.partition n))
    (hlocalβ : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ :
      Measure (exh.box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, β.partition n ζ = β.partition n η) :
    μ ∈ DLRMeasures exh β hq hp := by
  intro n
  exact isDLR_of_tendsto_of_locallyStabilizes (exh.box n) hq hp
    (fun i => (α i).partition n) (fun _ => (α _).measurable_partition n)
    (β.partition n) (β.measurable_partition n) hμ
    (hDLR n) (hstab n) (hlocalβ n)

/-- Geometric reference assignments have the local-constancy input required by
varying-source closure on every at-most-one exterior marginal. -/
theorem ae_eventually_eq_of_geometric_atMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    {box : ℕ → FiniteBox G.edgeSet}
    (data : ConventionTransport.SimpleGraphBoxData G box)
    (β : BoundaryAssignment box)
    (hβ : ConventionTransport.IsGeometric data.geometry β)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hunique : ConventionTransport.AEAtMostOne data.geometry μ) :
    ∀ n, ∀ᵐ η ∂((box n).exteriorMeasure μ : Measure (box n).Exterior),
      ∀ᶠ ζ in 𝓝 η, β.partition n ζ = β.partition n η := by
  intro n
  filter_upwards [hunique n] with η hη
  exact NonlocalInterior.eventually_partition_eq_of_atMostOne data β hβ n η hη

/-- Varying-source DLR closure with a geometric reference and exterior
uniqueness.  Only local DLR compatibility and joint stabilization of the
varying source remain as analytic inputs; reference regularity is derived. -/
theorem mem_dlrMeasures_of_tendsto_of_locallyStabilizes_of_atMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {ι : Type*} (α : ι → BoundaryAssignment exh.box)
    (β : BoundaryAssignment exh.box)
    (hβ : ConventionTransport.IsGeometric data.geometry β)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    {l : Filter ι} [l.NeBot]
    {μs : ι → ProbabilityMeasure (Configuration G.edgeSet)}
    {μ : ProbabilityMeasure (Configuration G.edgeSet)} (hμ : Tendsto μs l (𝓝 μ))
    (hDLR : ∀ n, ∀ᶠ i in l, (exh.box n).IsDLR hq hp
      ((α i).partition n) ((α i).measurable_partition n) (μs i))
    (hstab : ∀ n, LocallyStabilizes l
      ((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior)
      (fun i => (α i).partition n) (β.partition n))
    (hunique : ConventionTransport.AEAtMostOne data.geometry μ) :
    μ ∈ DLRMeasures exh β hq hp :=
  mem_dlrMeasures_of_tendsto_of_locallyStabilizes exh α β hq hp hμ hDLR hstab
    (ae_eventually_eq_of_geometric_atMostOne data β hβ hunique)

/-- Exact scoped noncoherent weak-limit statement.  The source is an actual
arbitrary-boundary `IsFKLimit`; global uniqueness supplies exterior uniqueness
for the geometric reference.  The induced local DLR specifications and their
joint stabilization are explicit residual hypotheses, not silently inferred. -/
theorem mem_dlrMeasures_of_isFKLimit_of_locallyStabilizes_of_globalAtMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    (α : ℕ → BoundaryAssignment exh.box)
    (β : BoundaryAssignment exh.box)
    (hβ : ConventionTransport.IsGeometric data.geometry β)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit exh hq hp₁.le a μ)
    (hDLR : ∀ m, ∀ᶠ n in atTop, (exh.box m).IsDLR hq hp₁.le
      ((α n).partition m) ((α n).measurable_partition m)
      ((exh.box n).finiteVolumeLaw hq hp₁.le (a n)))
    (hstab : ∀ m, LocallyStabilizes atTop
      ((exh.box m).exteriorMeasure μ : Measure (exh.box m).Exterior)
      (fun n => (α n).partition m) (β.partition m))
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh β hq hp₁.le := by
  have hunique : ConventionTransport.AEAtMostOne data.geometry μ :=
    NoncoherentFiniteEnergy.aeAtMostOne_geometry_of_isFKLimit
      exh data hq hp₀ hp₁ a hμ hglobal
  exact mem_dlrMeasures_of_tendsto_of_locallyStabilizes_of_atMostOne
    exh data α β hβ hq hp₁.le hμ hDLR hstab hunique

/-- Simultaneous pointwise diagonalization for a countable family of finite
(discrete) outputs.  This is a genuine strict subsequence, not a subnet or a
finite-index-only compactness claim. -/
theorem exists_strictMono_tendsto_pi
    {X : Type*} [Countable X] (J : X → Type*) [∀ x, Finite (J x)]
    [∀ x, TopologicalSpace (J x)] [∀ x, DiscreteTopology (J x)]
    (a : ℕ → ∀ x, J x) :
    ∃ b : (∀ x, J x), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 b) := by
  exact CompactSpace.tendsto_subseq a

/-- Eventual exact form of simultaneous finite-valued diagonalization. -/
theorem exists_strictMono_eventually_eq_pi
    {X : Type*} [Countable X] (J : X → Type*) [∀ x, Finite (J x)]
    [∀ x, TopologicalSpace (J x)] [∀ x, DiscreteTopology (J x)]
    (a : ℕ → ∀ x, J x) :
    ∃ b : (∀ x, J x), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ x, ∀ᶠ n in atTop, a (φ n) x = b x := by
  obtain ⟨b, φ, hφ, hlim⟩ := exists_strictMono_tendsto_pi J a
  refine ⟨b, φ, hφ, fun x => ?_⟩
  have hx : Tendsto (fun n => a (φ n) x) atTop (𝓝 (b x)) := by
    exact (tendsto_pi_nhds.mp hlim) x
  have hev : ∀ᶠ y : J x in 𝓝 (b x), y = b x := by
    simp only [nhds_discrete, eventually_pure]
  exact hx.eventually hev

/-- A strict subsequence preserves convergence of the actual finite-volume
laws, with their boxes reindexed as well as their boundary setoids. -/
theorem tendsto_finiteVolumeLaw_subseq {E : Type*} [Countable E]
    (exh : BoxExhaustion E) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh hq hp α μ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun n => (exh.box (φ n)).finiteVolumeLaw hq hp (α (φ n)))
      atTop (𝓝 μ) :=
  hμ.comp hφ.tendsto_atTop

/-- Simultaneous pointwise stabilization at countable dense exterior probes in
all boxes.  The restriction to a countable probe family is essential: the full
uncountable product of finite-valued assignments need not be sequentially
compact.  Dense diagonalization alone supplies neither DLR compatibility nor
`LocallyStabilizes`. -/
theorem exists_boundary_denseProbe_subsequence {E : Type*} [Countable E]
    (exh : BoxExhaustion E)
    (a : ℕ → ∀ m, (exh.box m).Exterior → (exh.box m).BoundaryPartition) :
    ∃ b : (∀ m, ℕ → (exh.box m).BoundaryPartition),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ m k, ∀ᶠ n in atTop,
          a (φ n) m (TopologicalSpace.denseSeq (exh.box m).Exterior k) = b m k := by
  let X := Σ _m : ℕ, ℕ
  let J : X → Type _ := fun z => (exh.box z.1).BoundaryPartition
  let a' : ℕ → ∀ z, J z := fun n z =>
    a n z.1 (TopologicalSpace.denseSeq (exh.box z.1).Exterior z.2)
  letI (z : X) : TopologicalSpace (J z) := ⊥
  haveI (z : X) : DiscreteTopology (J z) := ⟨rfl⟩
  letI : TopologicalSpace (∀ z, J z) := Pi.topologicalSpace
  obtain ⟨b', φ, hφ, hlim⟩ := exists_strictMono_eventually_eq_pi J a'
  refine ⟨fun m k => b' ⟨m, k⟩, φ, hφ, fun m k => ?_⟩
  exact hlim ⟨m, k⟩

end

end FK.InfiniteVolume.NoncoherentStabilization
