import FK.NoncoherentCounterexample

/-!
# Closed-exception stabilization for varying coherent FK sources

The local-DLR equations below come from the actual `BoundaryConvention.compatible`
field of each source.  The stabilization input is supplied by eventual agreement
outside a closed null set.  We also record why mere almost-everywhere agreement
cannot replace that stronger input.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators

namespace FK.InfiniteVolume.NoncoherentStabilization

open NonlocalInterior ConventionGeometry ConventionTransport

noncomputable section

local instance closedExceptionBoundaryPartitionMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance closedExceptionFiniteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- For a constant specification sequence, local stabilization is exactly
nullity of the closure of the disagreement set.  In particular, nullity of the
disagreement set itself is not sufficient. -/
theorem locallyStabilizes_const_iff_measure_closure_disagreement_eq_zero
    {X J ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {l : Filter ι} [l.NeBot] (μ : Measure X) (α β : X → J) :
    LocallyStabilizes l μ (fun _ => α) β ↔
      μ (closure {x | α x ≠ β x}) = 0 := by
  constructor
  · intro h
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with x hx
    obtain ⟨U, hU, hev⟩ := hx
    obtain ⟨i, hi⟩ := hev.exists
    have hsub : U ⊆ {y | α y ≠ β y}ᶜ := by
      intro y hyU hy
      exact hy (hi hyU)
    have hxint : x ∈ interior {y | α y ≠ β y}ᶜ :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hU hsub)
    simpa only [interior_compl, mem_compl_iff] using hxint
  · intro h
    rw [measure_eq_zero_iff_ae_notMem] at h
    filter_upwards [h] with x hx
    refine ⟨(closure {y | α y ≠ β y})ᶜ,
      isOpen_compl_iff.mpr isClosed_closure |>.mem_nhds hx, ?_⟩
    filter_upwards [] with i
    intro y hy
    by_contra hne
    exact hy (subset_closure hne)

/-- Eventual agreement outside a closed null exceptional set gives genuine
joint local stabilization.  The functions need not agree globally at any
index, and no local constancy is assumed. -/
theorem locallyStabilizes_of_eventually_eqOn_compl_closed
    {X J ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {l : Filter ι} (μ : Measure X) (α : ι → X → J) (β : X → J)
    (K : Set X) (hK : IsClosed K) (hK0 : μ K = 0)
    (hαβ : ∀ᶠ i in l, Set.EqOn (α i) β Kᶜ) :
    LocallyStabilizes l μ α β := by
  rw [measure_eq_zero_iff_ae_notMem] at hK0
  filter_upwards [hK0] with x hx
  refine ⟨Kᶜ, hK.isOpen_compl.mem_nhds hx, ?_⟩
  filter_upwards [hαβ] with i hi
  exact fun y hy => hi hy

/-- Source laws built from varying coherent conventions automatically have
all induced smaller-box DLR equations. -/
theorem eventually_isDLR_finiteVolumeLaw_coherent
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : ℕ → BoundaryConvention exh hq hp) :
    ∀ m, ∀ᶠ n in atTop, (exh.box m).IsDLR hq hp
      ((Φ n).partition m) ((Φ n).measurable_partition m)
      ((exh.box n).finiteVolumeLaw hq hp
        ((Φ n).partition n (exh.box n).closedExterior)) := by
  intro m
  filter_upwards [eventually_ge_atTop m] with n hn
  simpa only [FiniteBox.finiteVolumeLaw, FiniteBox.conditionalLaw] using
    (Φ n).compatible m n (exh.monotone hn) (exh.box n).closedExterior

/-- Closed-exception closure theorem for genuinely varying coherent sources.
Each source supplies its own smaller-box DLR law; discrepancies between the
source and target assignments must eventually lie in a fixed closed null set
for each box.  The target need not itself be a coherent convention. -/
theorem mem_dlrMeasures_of_tendsto_coherent_of_eventually_eqOn_compl_closed
    {E : Type*} [Countable E] (exh : BoxExhaustion E)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : ℕ → BoundaryConvention exh hq hp) (β : BoundaryAssignment exh.box)
    {μ : ProbabilityMeasure (Configuration E)}
    (K : ∀ m, Set (exh.box m).Exterior)
    (hKclosed : ∀ m, IsClosed (K m))
    (hKnull : ∀ m, ((exh.box m).exteriorMeasure μ : Measure (exh.box m).Exterior)
      (K m) = 0)
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      ((Φ n).partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hαβ : ∀ m, ∀ᶠ n in atTop,
      Set.EqOn ((Φ n).partition m) (β.partition m) (K m)ᶜ)
    (hlocalβ : ∀ m, ∀ᵐ η ∂((exh.box m).exteriorMeasure μ :
      Measure (exh.box m).Exterior),
      ∀ᶠ ζ in 𝓝 η, β.partition m ζ = β.partition m η) :
    μ ∈ DLRMeasures exh β hq hp := by
  apply mem_dlrMeasures_of_tendsto_of_locallyStabilizes exh
    (fun n => (Φ n).toBoundaryAssignment) β hq hp hμ
    (eventually_isDLR_finiteVolumeLaw_coherent exh Φ)
  · intro m
    exact locallyStabilizes_of_eventually_eqOn_compl_closed
      ((exh.box m).exteriorMeasure μ : Measure (exh.box m).Exterior)
      (fun n => (Φ n).partition m) (β.partition m) (K m)
      (hKclosed m) (hKnull m) (hαβ m)
  · exact hlocalβ

/-- Geometric form of closed-exception closure.  Exterior uniqueness supplies
both local regularity of the geometric target and, in the next theorem, the
usual consequence of global at-most-one-cluster uniqueness. -/
theorem mem_dlrMeasures_of_tendsto_coherent_of_eventually_eqOn_compl_closed_of_atMostOne
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : ℕ → BoundaryConvention exh hq hp) (β : BoundaryAssignment exh.box)
    (hβ : ConventionTransport.IsGeometric data.geometry β)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (K : ∀ m, Set (exh.box m).Exterior)
    (hKclosed : ∀ m, IsClosed (K m))
    (hKnull : ∀ m, ((exh.box m).exteriorMeasure μ : Measure (exh.box m).Exterior)
      (K m) = 0)
    (hμ : Tendsto (fun n => (exh.box n).finiteVolumeLaw hq hp
      ((Φ n).partition n (exh.box n).closedExterior)) atTop (𝓝 μ))
    (hαβ : ∀ m, ∀ᶠ n in atTop,
      Set.EqOn ((Φ n).partition m) (β.partition m) (K m)ᶜ)
    (hunique : ConventionTransport.AEAtMostOne data.geometry μ) :
    μ ∈ DLRMeasures exh β hq hp := by
  exact mem_dlrMeasures_of_tendsto_coherent_of_eventually_eqOn_compl_closed
    exh Φ β K hKclosed hKnull hμ hαβ
    (ae_eventually_eq_of_geometric_atMostOne data β hβ hunique)

/-- Actual arbitrary-boundary `IsFKLimit` form.  The approximating setoids are
the closed-exterior evaluations of varying coherent conventions.  Global
uniqueness and the closed-exception agreement are the only geometric inputs;
no coherence of the target and no agreement on the exceptional sets is used. -/
theorem mem_dlrMeasures_of_isFKLimit_coherent_of_eventually_eqOn_compl_closed
    {V : Type*} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (exh : BoxExhaustion G.edgeSet)
    (data : ConventionTransport.SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : ℕ → BoundaryConvention exh hq hp₁.le)
    (β : BoundaryAssignment exh.box)
    (hβ : ConventionTransport.IsGeometric data.geometry β)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (K : ∀ m, Set (exh.box m).Exterior)
    (hKclosed : ∀ m, IsClosed (K m))
    (hKnull : ∀ m, ((exh.box m).exteriorMeasure μ : Measure (exh.box m).Exterior)
      (K m) = 0)
    (hμ : IsFKLimit exh hq hp₁.le
      (fun n => (Φ n).partition n (exh.box n).closedExterior) μ)
    (hαβ : ∀ m, ∀ᶠ n in atTop,
      Set.EqOn ((Φ n).partition m) (β.partition m) (K m)ᶜ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ConventionTransport.GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh β hq hp₁.le := by
  have hunique : ConventionTransport.AEAtMostOne data.geometry μ :=
    NoncoherentFiniteEnergy.aeAtMostOne_geometry_of_isFKLimit
      exh data hq hp₀ hp₁
      (fun n => (Φ n).partition n (exh.box n).closedExterior) hμ hglobal
  exact mem_dlrMeasures_of_tendsto_coherent_of_eventually_eqOn_compl_closed_of_atMostOne
    exh data Φ β hβ K hKclosed hKnull hμ hαβ hunique

/-! ## A compact-product obstruction to weakening the hypothesis -/

namespace ClosedExceptionCounterexample

/-- The ordinary compact product of Boolean configurations. -/
abbrev Cantor := ℕ → Bool

/-- The distinguished all-true configuration. -/
def apex : Cantor := fun _ => true

/-- Two finite-valued specifications which agree only at `apex`. -/
def varying : Cantor → Bool := fun x => if x = apex then true else false
def reference : Cantor → Bool := fun _ => true

lemma disagreement_eq_compl_singleton :
    {x | varying x ≠ reference x} = ({apex}ᶜ : Set Cantor) := by
  ext x
  simp [varying, reference]

/-- Flipping one coordinate of `apex` gives a sequence tending to `apex` in
the product topology, while every term lies in the disagreement set. -/
lemma tendsto_update_apex :
    Tendsto (fun n => Function.update apex n false) atTop (𝓝 apex) := by
  rw [tendsto_pi_nhds]
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with n hn
  symm
  simp [Function.update_apply, Nat.ne_of_lt hn]

lemma closure_disagreement_eq_univ :
    closure {x | varying x ≠ reference x} = Set.univ := by
  rw [disagreement_eq_compl_singleton]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = apex
  · subst x
    apply mem_closure_of_tendsto tendsto_update_apex
    filter_upwards [] with n
    intro hn
    have h := congrFun hn n
    simp [apex] at h
  · apply subset_closure
    simpa using hx

/-- The point mass at the unique agreement configuration. -/
noncomputable def pointMass : Measure Cantor := Measure.dirac apex

lemma pointMass_disagreement :
    pointMass {x | varying x ≠ reference x} = 0 := by
  rw [disagreement_eq_compl_singleton, pointMass,
    Measure.dirac_apply' _ isClosed_singleton.measurableSet.compl]
  simp

lemma pointMass_closure_disagreement :
    pointMass (closure {x | varying x ≠ reference x}) = 1 := by
  rw [closure_disagreement_eq_univ]
  simp [pointMass]

lemma ae_varying_eq_reference :
    ∀ᵐ x ∂pointMass, varying x = reference x := by
  rw [ae_iff]
  simpa only [not_not] using pointMass_disagreement

/-- On a compact configuration space, almost-everywhere equality of a fixed
pair of specifications does not imply joint local stabilization.  The
disagreement set here is null but dense. -/
theorem ae_agreement_not_locallyStabilizes :
    (∀ᵐ x ∂pointMass, varying x = reference x) ∧
      ¬ LocallyStabilizes atTop pointMass (fun _ : ℕ => varying) reference := by
  refine ⟨ae_varying_eq_reference, ?_⟩
  rw [locallyStabilizes_const_iff_measure_closure_disagreement_eq_zero,
    pointMass_closure_disagreement]
  exact one_ne_zero

end ClosedExceptionCounterexample

end

end FK.InfiniteVolume.NoncoherentStabilization
