import FK.InfiniteVolume

/-!
# Geometric convention transport for FK Gibbs measures

This module formalizes the Gibbs-to-Gibbs part of Proposition 1.8(2). The
`BoundaryAssignment` is separate from the geometric certificate saying that
it merges open exterior components and separates distinct components when at
least one is finite. No such certificate is inferred from measurability alone.
The weak-limit half of Proposition 1.8(2) is not asserted here.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

namespace FK.InfiniteVolume.ConventionTransport

noncomputable section

open CurvatureVariance.Infra.Percolation
open ConventionGeometry

universe u v w

local instance setoidMeasurableSpace (V : Type*) : MeasurableSpace (Setoid V) := ⊤

local instance finiteSetoid (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

/-- Exterior component geometry associated with a family of finite boxes. -/
structure ExteriorGeometry {E : Type u} (box : ℕ → FiniteBox.{u, v} E) where
  components : ∀ n, (box n).Exterior → Setoid (box n).Vertex
  infinite : ∀ n, (box n).Exterior → (box n).Vertex → Prop

/-- A law-level assignment has the two geometric properties stated below
Proposition 1.6 in the paper. -/
def IsGeometric {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box) (Φ : BoundaryAssignment box) : Prop :=
  (∀ n η, MergesOpenComponents (geo.components n η) (Φ.partition n η)) ∧
  (∀ n η, SeparatesFiniteComponents (geo.components n η) (Φ.partition n η)
    (geo.infinite n η))

/-- The free assignment: wire exactly each exterior open component. -/
def freeAssignment {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box)
    (hmeas : ∀ n, Measurable (geo.components n)) : BoundaryAssignment box where
  partition n := geo.components n
  measurable_partition := hmeas

/-- The relation which wires each component and also wires every pair of
infinite components. The invariance hypothesis is used only for transitivity. -/
def wiredAtInfinity {V : Type*} (C : Setoid V) (IsInfinite : V → Prop)
    (hI : ∀ {x y}, C.r x y → IsInfinite x → IsInfinite y) : Setoid V where
  r x y := C.r x y ∨ (IsInfinite x ∧ IsInfinite y)
  iseqv := by
    refine ⟨fun x => Or.inl (C.refl' x), ?_, ?_⟩
    · intro x y hxy
      rcases hxy with hxy | ⟨hx, hy⟩
      · exact Or.inl (C.symm' hxy)
      · exact Or.inr ⟨hy, hx⟩
    · intro x y z hxy hyz
      rcases hxy with hxy | ⟨hx, hy⟩
      · rcases hyz with hyz | ⟨hy', hz⟩
        · exact Or.inl (C.trans' hxy hyz)
        · exact Or.inr ⟨hI (x := y) (y := x) (C.symm' hxy) hy', hz⟩
      · rcases hyz with hyz | ⟨hy', hz⟩
        · exact Or.inr ⟨(by assumption), hI (x := y) (y := z) hyz hy⟩
        · exact Or.inr ⟨hx, hz⟩

/-- The wired assignment at infinity. -/
def wiredAssignment {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box)
    (hinv : ∀ n η {x y}, (geo.components n η).r x y →
      geo.infinite n η x → geo.infinite n η y)
    (hmeas : ∀ n, Measurable fun η =>
      wiredAtInfinity (geo.components n η) (geo.infinite n η) (hinv n η)) :
    BoundaryAssignment box where
  partition n η := wiredAtInfinity (geo.components n η) (geo.infinite n η) (hinv n η)
  measurable_partition := hmeas

lemma freeAssignment_isGeometric {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box) (hmeas : ∀ n, Measurable (geo.components n)) :
    IsGeometric geo (freeAssignment geo hmeas) := by
  constructor
  · intro n η x y hxy
    exact hxy
  · intro n η x y hxy _ h
    exact hxy h

lemma wiredAssignment_isGeometric {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box)
    (hinv : ∀ n η {x y}, (geo.components n η).r x y →
      geo.infinite n η x → geo.infinite n η y)
    (hmeas : ∀ n, Measurable fun η =>
      wiredAtInfinity (geo.components n η) (geo.infinite n η) (hinv n η)) :
    IsGeometric geo (wiredAssignment geo hinv hmeas) := by
  constructor
  · intro n η x y hxy
    exact Or.inl hxy
  · intro n η x y hxy hfin h
    rcases h with h | ⟨hx, hy⟩
    · exact hxy h
    · exact hfin.elim (fun hxi => hxi hx) (fun hyi => hyi hy)

/-- Under exterior at-most-one-cluster, every geometrically valid assignment
has the same partition as the free exterior-component assignment. -/
theorem partition_eq_free_of_atMostOne {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box) (Φ : BoundaryAssignment box)
    (hΦ : IsGeometric geo Φ) {n : ℕ} {η : (box n).Exterior}
    (hunique : AtMostOneInfiniteCluster (geo.components n η) (geo.infinite n η)) :
    Φ.partition n η = geo.components n η := by
  exact eq_openComponents_of_finite_separation _ _ _ (hΦ.1 n η) (hΦ.2 n η) hunique

/-- Any two geometrically valid assignments agree on every exterior
configuration with at most one infinite component. -/
theorem partition_eq_of_atMostOne {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box) (Φ Ψ : BoundaryAssignment box)
    (hΦ : IsGeometric geo Φ) (hΨ : IsGeometric geo Ψ)
    {n : ℕ} {η : (box n).Exterior}
    (hunique : AtMostOneInfiniteCluster (geo.components n η) (geo.infinite n η)) :
    Φ.partition n η = Ψ.partition n η := by
  exact convention_eq_of_atMostOneInfiniteCluster _ _ _ _ (hΦ.1 n η) (hΦ.2 n η)
    (hΨ.1 n η) (hΨ.2 n η) hunique

/-- The almost-everywhere exterior uniqueness input used for DLR transport.
This is intentionally formulated on every exterior marginal of the given law. -/
def AEAtMostOne {E : Type u} {box : ℕ → FiniteBox.{u, v} E}
    (geo : ExteriorGeometry box) (μ : ProbabilityMeasure (Configuration E)) : Prop :=
  ∀ n, ∀ᵐ η ∂((box n).exteriorMeasure μ : Measure (box n).Exterior),
    AtMostOneInfiniteCluster (geo.components n η) (geo.infinite n η)

/-- Actual DLR classes are preserved when the source law has almost surely at
most one infinite exterior component for every box. -/
theorem mem_dlrMeasures_of_atMostOne {E : Type u} (exh : BoxExhaustion.{u, v} E)
    (geo : ExteriorGeometry exh.box) (Φ Ψ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hΦ : IsGeometric geo Φ) (hΨ : IsGeometric geo Ψ)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hunique : AEAtMostOne geo μ) :
    μ ∈ DLRMeasures exh Ψ hq hp := by
  have hpart : ∀ n, ∀ᵐ η ∂((exh.box n).exteriorMeasure μ : Measure (exh.box n).Exterior),
      Φ.partition n η = Ψ.partition n η := by
    intro n
    filter_upwards [hunique n] with η hη
    exact partition_eq_of_atMostOne geo Φ Ψ hΦ hΨ hη
  exact (mem_dlrMeasures_iff_of_ae_partition_eq exh Φ Ψ hq hp hpart).mp hμ

/-- Gibbs-to-Gibbs part of Proposition 1.8(2): a coherent Gibbs law with
almost surely at most one infinite exterior component belongs to every other
coherent convention respecting the same geometry. -/
theorem mem_gibbsMeasures_of_atMostOne {E : Type u} (exh : BoxExhaustion.{u, v} E)
    (geo : ExteriorGeometry exh.box) {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ Ψ : BoundaryConvention exh hq hp)
    (hΦ : IsGeometric geo Φ.toBoundaryAssignment)
    (hΨ : IsGeometric geo Ψ.toBoundaryAssignment)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : μ ∈ GibbsMeasures exh Φ) (hunique : AEAtMostOne geo μ) :
    μ ∈ GibbsMeasures exh Ψ := by
  exact mem_dlrMeasures_of_atMostOne exh geo Φ.toBoundaryAssignment Ψ.toBoundaryAssignment
    hq hp hΦ hΨ hμ hunique


/-- Actual finite FK singleton masses are strictly positive at interior edge
parameters. -/
lemma fkMeasure_singleton_pos {E : Type*} (B : FiniteBox E) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (α : B.Exterior → B.BoundaryPartition) (η : B.Exterior) (ξ : B.Interior) :
    0 < B.graph.fkMeasure hq hp₁.le (α η) {ξ} := by
  rw [FK.Finite.LabelledMultigraph.fkMeasure_apply_singleton,
    FK.Finite.LabelledMultigraph.fkPMF_apply]
  exact ENNReal.coe_pos.mpr (div_pos
    (B.graph.fkWeight_pos hq hp₀ hp₁ (α η) ξ)
    (B.graph.partitionFunction_pos hq hp₁.le (α η)))

/-- A comp-product with full-support finite interior fibres transports a.e.
goodness of glued configurations to, for almost every exterior, goodness of
every interior configuration. -/
theorem ae_forall_interior_of_ae_glue {E : Type*} (B : FiniteBox E)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E))
    (hμ : B.IsDLR hq hp α hα μ)
    (hpos : ∀ η ξ, 0 < B.graph.fkMeasure hq hp (α η) {ξ})
    {P : Configuration E → Prop} (hP : MeasurableSet {ω | P ω})
    (hgood : ∀ᵐ ω ∂(μ : Measure (Configuration E)), P ω) :
    ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior),
      ∀ ξ, P (B.glue (η, ξ)) := by
  have hP' : MeasurableSet {z : B.Exterior × B.Interior | P (B.glue z)} :=
    hP.preimage B.splitEquiv.symm.measurable
  have hsplit : ∀ᵐ z ∂(Measure.map B.splitEquiv (μ : Measure (Configuration E))),
      P (B.glue z) := by
    apply (MeasureTheory.mem_ae_map_iff B.splitEquiv.measurable.aemeasurable hP').2
    filter_upwards [hgood] with ω hω
    change P (B.glue (B.splitEquiv ω))
    simpa only [FiniteBox.splitEquiv_apply, B.glue_split] using hω
  rw [hμ] at hsplit
  have hae := Measure.ae_ae_of_ae_compProd hsplit
  filter_upwards [hae] with η hη
  change ∀ᵐ ξ ∂(B.graph.fkMeasure hq hp (α η)), P (B.glue (η, ξ)) at hη
  intro ξ
  by_contra hξ
  have hbad : B.graph.fkMeasure hq hp (α η) {ζ | ¬ P (B.glue (η, ζ))} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    simpa only [Set.mem_ofPred_eq, not_not] using hη
  have hsingle : B.graph.fkMeasure hq hp (α η) {ξ} = 0 :=
    measure_mono_null (Set.singleton_subset_iff.mpr hξ) hbad
  exact (ne_of_gt (hpos η ξ)) hsingle

/-! ## Measurability of finite boundary partitions -/

/-- A setoid-valued function on a finite vertex type is measurable as soon as
all its pairwise relation events are measurable. -/
lemma measurable_setoid_of_measurable_rel {X V : Type*} [MeasurableSpace X]
    [Finite V] (C : X → Setoid V)
    (hC : ∀ x y, MeasurableSet {a | (C a).r x y}) : Measurable C := by
  apply measurable_to_countable'
  intro α
  have heq : C ⁻¹' {α} = ⋂ x, ⋂ y, {a | (C a).r x y ↔ α.r x y} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h x y
      rw [h]
    · intro h
      apply Setoid.ext
      intro x y
      exact h x y
  rw [heq]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => by
    by_cases hα : α.r x y
    · have heq' : {a | (C a).r x y ↔ α.r x y} = {a | (C a).r x y} := by
        ext a
        simp [hα]
      rw [heq']
      exact hC x y
    · have heq' : {a | (C a).r x y ↔ α.r x y} = {a | (C a).r x y}ᶜ := by
        ext a
        simp [hα]
      rw [heq']
      exact (hC x y).compl

/-- Open-path components on a boundary type mapped into a global graph. -/
def openPathSetoid {V W : Type*} (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (A : Set (Sym2 V)) (b : W → V) : Setoid W where
  r x y := OpenConnected G ω A (b x) (b y)
  iseqv := ⟨fun x => OpenConnected.refl ω A (b x),
    fun h => openConnected_symm h, fun hxy hyz => hxy.trans hyz⟩

lemma measurable_openPathSetoid {X V W : Type*} [MeasurableSpace X]
    (G : SimpleGraph V) [Countable V] [Finite W]
    (ω : X → G.edgeSet → Bool) (hω : Measurable ω)
    (A : Set (Sym2 V)) (b : W → V) :
    Measurable fun a => openPathSetoid G (ω a) A b := by
  apply measurable_setoid_of_measurable_rel
  intro x y
  exact (measurableSet_openConnected (G := G) A (b x) (b y)).preimage hω

lemma measurableSet_openPathInfinite {X V : Type*} [MeasurableSpace X]
    (G : SimpleGraph V) [Countable V] (ω : X → G.edgeSet → Bool)
    (hω : Measurable ω) (A : Set (Sym2 V)) (x : V) :
    MeasurableSet {a | ExteriorInfiniteCluster G (ω a) A x} := by
  have hm : Measurable (fun a => {y | OpenConnected G (ω a) A x y}) :=
    measurable_set_iff.mpr fun y => by
      rw [← measurableSet_setOfPred]
      exact (measurableSet_openConnected (G := G) A x y).preimage hω
  exact MeasurableSet.setOfPred_infinite.preimage hm

lemma measurable_wiredAtInfinity {X V : Type*} [MeasurableSpace X] [Finite V]
    (C : X → Setoid V) (Inf : X → V → Prop)
    (hI : ∀ a {x y}, (C a).r x y → Inf a x → Inf a y)
    (hC : ∀ x y, MeasurableSet {a | (C a).r x y})
    (hIm : ∀ x, MeasurableSet {a | Inf a x}) :
    Measurable fun a => wiredAtInfinity (C a) (Inf a) (hI a) := by
  apply measurable_setoid_of_measurable_rel
  intro x y
  have hm := (hC x y).union ((hIm x).inter (hIm y))
  have heq : {a | (wiredAtInfinity (C a) (Inf a) (hI a)).r x y} =
      {a | (C a).r x y} ∪ ({a | Inf a x} ∩ {a | Inf a y}) := by
    rfl
  rw [heq]
  exact hm

/-- Close every edge of a finite box while retaining its exterior. -/
def closeInside {E : Type*} (B : FiniteBox E) (η : B.Exterior) : Configuration E :=
  B.glue (η, fun _ => false)

lemma measurable_closeInside {E : Type*} (B : FiniteBox E) : Measurable (closeInside B) := by
  exact B.splitEquiv.symm.measurable.comp (measurable_id.prodMk measurable_const)


/-- At most one infinite open cluster in an actual global simple graph. -/
def GlobalAtMostOne {V : Type*} (G : SimpleGraph V) (ω : G.edgeSet → Bool) : Prop :=
  ∀ x y, ExteriorInfiniteCluster G ω Set.univ x →
    ExteriorInfiniteCluster G ω Set.univ y → OpenConnected G ω Set.univ x y

lemma measurableSet_globalAtMostOne {V : Type*} (G : SimpleGraph V) [Countable V] :
    MeasurableSet {ω | GlobalAtMostOne G ω} := by
  rw [measurableSet_setOfPred]
  refine Measurable.forall fun x => Measurable.forall fun y => ?_
  have hx : Measurable (fun ω : G.edgeSet → Bool =>
      ExteriorInfiniteCluster G ω Set.univ x) :=
    measurableSet_setOfPred.mp
      (measurableSet_openPathInfinite G id measurable_id Set.univ x)
  have hy : Measurable (fun ω : G.edgeSet → Bool =>
      ExteriorInfiniteCluster G ω Set.univ y) :=
    measurableSet_setOfPred.mp
      (measurableSet_openPathInfinite G id measurable_id Set.univ y)
  have hc : Measurable (fun ω : G.edgeSet → Bool => OpenConnected G ω Set.univ x y) :=
    measurableSet_setOfPred.mp (measurableSet_openConnected (G := G) Set.univ x y)
  exact hx.imp (hy.imp hc)

/-- Compatibility data embedding every finite labelled box in an actual global
simple graph. The endpoint identity retains the box's labelled edge subtype. -/
structure SimpleGraphBoxData {V : Type*} (G : SimpleGraph V)
    (box : ℕ → FiniteBox G.edgeSet) where
  vertex : ∀ n, (box n).Vertex → V
  endpoint : ∀ n (e : (box n).edges),
    s(vertex n ((box n).source e), vertex n ((box n).target e)) = e.1.1

namespace SimpleGraphBoxData

variable {V : Type*} {G : SimpleGraph V} {box : ℕ → FiniteBox G.edgeSet}

/-- The exterior geometry obtained by closing all interior coordinates. No
interior edge can occur in a nonempty open path. -/
def geometry (data : SimpleGraphBoxData G box) : ExteriorGeometry box where
  components n η := openPathSetoid G (closeInside (box n) η) Set.univ (data.vertex n)
  infinite n η x := ExteriorInfiniteCluster G (closeInside (box n) η) Set.univ (data.vertex n x)

lemma measurable_closeInside' (n : ℕ) :
    Measurable (fun η : (box n).Exterior => closeInside (box n) η) :=
  measurable_closeInside (box n)

lemma measurable_components (data : SimpleGraphBoxData G box) [Countable V] (n : ℕ) :
    Measurable (data.geometry.components n) := by
  exact measurable_openPathSetoid G _ (measurable_closeInside' n) Set.univ (data.vertex n)

lemma measurableSet_infinite (data : SimpleGraphBoxData G box) [Countable V]
    (n : ℕ) (x : (box n).Vertex) :
    MeasurableSet {η | data.geometry.infinite n η x} := by
  exact measurableSet_openPathInfinite G _ (measurable_closeInside' n) Set.univ
    (data.vertex n x)

/-- Infinitude is invariant along an exterior open path. -/
lemma infinite_invariant (data : SimpleGraphBoxData G box) (n : ℕ)
    (η : (box n).Exterior) {x y : (box n).Vertex}
    (hxy : (data.geometry.components n η).r x y) :
    data.geometry.infinite n η x → data.geometry.infinite n η y := by
  intro hx
  have hset : {z | OpenConnected G (closeInside (box n) η) Set.univ
      (data.vertex n x) z} = {z | OpenConnected G (closeInside (box n) η) Set.univ
      (data.vertex n y) z} := by
    ext z
    constructor
    · intro hxz
      exact (openConnected_symm hxy).trans hxz
    · intro hyz
      exact hxy.trans hyz
  change {z | OpenConnected G (closeInside (box n) η) Set.univ
    (data.vertex n y) z}.Infinite
  rw [← hset]
  exact hx

/-- The canonical measurable free assignment of an actual graph geometry. -/
def free (data : SimpleGraphBoxData G box) [Countable V] : BoundaryAssignment box :=
  freeAssignment data.geometry data.measurable_components

/-- The canonical measurable wired-at-infinity assignment of an actual graph
geometry. -/
def wired (data : SimpleGraphBoxData G box) [Countable V] : BoundaryAssignment box := by
  apply wiredAssignment data.geometry (fun n η => data.infinite_invariant n η)
  intro n
  apply measurable_wiredAtInfinity
  · intro x y
    exact (measurableSet_openConnected (G := G) Set.univ
      (data.vertex n x) (data.vertex n y)).preimage (measurable_closeInside' n)
  · intro x
    exact data.measurableSet_infinite n x

lemma free_isGeometric (data : SimpleGraphBoxData G box) [Countable V] :
    IsGeometric data.geometry data.free :=
  freeAssignment_isGeometric data.geometry data.measurable_components

lemma wired_isGeometric (data : SimpleGraphBoxData G box) [Countable V] :
    IsGeometric data.geometry data.wired := by
  unfold wired
  apply wiredAssignment_isGeometric

/-- The full-support comp-product argument identifies the exterior uniqueness
hypothesis from genuine global almost-sure uniqueness at interior parameters. -/
theorem aeAtMostOne_geometry_of_global {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment exh.box) (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp₁.le)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    AEAtMostOne data.geometry μ := by
  intro n
  have hae := ae_forall_interior_of_ae_glue (exh.box n) hq hp₁.le
    (Φ.partition n) (Φ.measurable_partition n) μ (hμ n)
    (fun η ξ => fkMeasure_singleton_pos (exh.box n) hq hp₀ hp₁ (Φ.partition n) η ξ)
    (measurableSet_globalAtMostOne G) hglobal
  filter_upwards [hae] with η hη
  intro x y hx hy
  exact hη (fun _ => false) (data.vertex n x) (data.vertex n y) hx hy

/-- DLR transport driven by the actual global at-most-one-cluster event. No
separate exterior-uniqueness or full-support hypothesis remains at interior
parameters. -/
theorem mem_dlrMeasures_of_global_atMostOne {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ Ψ : BoundaryAssignment exh.box)
    (hΦ : IsGeometric data.geometry Φ) (hΨ : IsGeometric data.geometry Ψ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp₁.le)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh Ψ hq hp₁.le := by
  refine mem_dlrMeasures_of_atMostOne exh data.geometry Φ Ψ hq hp₁.le hΦ hΨ hμ ?_
  exact aeAtMostOne_geometry_of_global exh data hq hp₀ hp₁ Φ μ hμ hglobal

/-- Every geometrically valid DLR law with global a.s. at-most-one-cluster is
a DLR law for the canonical free assignment. -/
theorem mem_dlrMeasures_free_of_global_atMostOne {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment exh.box) (hΦ : IsGeometric data.geometry Φ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp₁.le)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh data.free hq hp₁.le := by
  exact mem_dlrMeasures_of_global_atMostOne exh data hq hp₀ hp₁ Φ data.free
    hΦ data.free_isGeometric μ hμ hglobal

/-- Every geometrically valid DLR law with global a.s. at-most-one-cluster is
a DLR law for the canonical wired-at-infinity assignment. -/
theorem mem_dlrMeasures_wired_of_global_atMostOne {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ : BoundaryAssignment exh.box) (hΦ : IsGeometric data.geometry Φ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp₁.le)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures exh data.wired hq hp₁.le := by
  exact mem_dlrMeasures_of_global_atMostOne exh data hq hp₀ hp₁ Φ data.wired
    hΦ data.wired_isGeometric μ hμ hglobal

/-- Gibbs form of Proposition 1.8(2) for an actual global simple graph and
interior `p`: global a.s. at-most-one-cluster transports a coherent Gibbs law
to every convention with the same exterior geometry. -/
theorem mem_gibbsMeasures_of_global_atMostOne {V : Type*} {G : SimpleGraph V}
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    [Countable V] {q p : NNReal} {hq : 0 < q} (hp₀ : 0 < p) (hp₁ : p < 1)
    (Φ Ψ : BoundaryConvention exh hq hp₁.le)
    (hΦ : IsGeometric data.geometry Φ.toBoundaryAssignment)
    (hΨ : IsGeometric data.geometry Ψ.toBoundaryAssignment)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ GibbsMeasures exh Φ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ GibbsMeasures exh Ψ := by
  refine mem_gibbsMeasures_of_atMostOne exh data.geometry Φ Ψ hΦ hΨ hμ ?_
  exact aeAtMostOne_geometry_of_global exh data hq hp₀ hp₁ Φ.toBoundaryAssignment μ hμ hglobal

end SimpleGraphBoxData

end
end FK.InfiniteVolume.ConventionTransport
