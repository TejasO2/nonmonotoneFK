import FK.GeneralMovingClopenRate
import FK.DominatedOuterAssembly
import FK.NonlocalGeometry
import FK.NoncoherentFiniteEnergy
import FK.ClusterCover

/-!
Geometry for weak FK limits with a unique infinite open cluster.

The main new finite-dependence fact is that an open arm out of a finite vertex
set is clopen on a locally finite graph.  We also prove the rooted form of the
finite-edge cover theorem needed to transport at-most-one-cluster uniqueness
through a finite box.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR.GlobalClosure

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.InfiniteVolume.ClusterEscape
open FK.InfiniteVolume.NonlocalInterior
open FK.NestedMixture

noncomputable section

universe u

variable {V : Type u} [Countable V] {G : SimpleGraph V}

omit [Countable V] in
/-- Open connection is an open condition: one finite open walk is a witness. -/
lemma isOpen_openConnected (x y : V) :
    IsOpen {ω : G.edgeSet → Bool | OpenConnected G ω Set.univ x y} := by
  rw [isOpen_iff_mem_nhds]
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  have hU : (walkSupport p).pi (fun e => {ω e}) ∈ 𝓝 ω :=
    set_pi_mem_nhds (finite_walkSupport p) fun _ _ => by simp
  filter_upwards [hU] with ζ hζ
  exact openConnected_of_agree_walkSupport p hp fun e he => (hζ e he).symm

omit [Countable V] in
/-- On a locally finite graph, an arm out of a finite vertex set is clopen.
The complement is open because, at a configuration without such an arm, the
whole cluster is contained in the finite set and is stable on a finite-
coordinate neighbourhood. -/
theorem isClopen_clusterMeetsOutside [G.LocallyFinite] (K : Finset V) (x : V) :
    IsClopen {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x K} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro ω hω
    have hno : ¬ ClusterMeetsOutside G ω x K := by simpa using hω
    have hsub : {z : V | OpenConnected G ω Set.univ x z} ⊆ (K : Set V) := by
      intro z hz
      by_contra hzK
      exact hno ⟨z, hzK, hz⟩
    have hfin : {z : V | OpenConnected G ω Set.univ x z}.Finite :=
      K.finite_toSet.subset hsub
    filter_upwards [eventually_finite_component_eq ω x hfin] with ζ hζ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rintro ⟨z, hzK, hxz⟩
    have hz : z ∈ {w : V | OpenConnected G ω Set.univ x w} := by
      rw [← hζ]
      exact hxz
    exact hno ⟨z, hzK, hz⟩
  · rw [isOpen_iff_mem_nhds]
    rintro ω ⟨z, hzK, p, hp⟩
    have hU : (walkSupport p).pi (fun e => {ω e}) ∈ 𝓝 ω :=
      set_pi_mem_nhds (finite_walkSupport p) fun _ _ => by simp
    filter_upwards [hU] with ζ hζ
    exact ⟨z, hzK, openConnected_of_agree_walkSupport p hp fun e he => (hζ e he).symm⟩

omit [Countable V] in
/-- Changing one coordinate is continuous in the product topology. -/
lemma continuous_closeGlobalEdge (e : G.edgeSet) :
    Continuous (closeGlobalEdge e) := by
  refine continuous_pi fun f => ?_
  by_cases hf : f = e
  · subst f
    simpa [closeGlobalEdge] using
      (continuous_const : Continuous fun _ : G.edgeSet → Bool => false)
  · simpa [closeGlobalEdge, hf] using
      (continuous_apply f : Continuous fun ω : G.edgeSet → Bool => ω f)

lemma measurable_closeGlobalEdge' (e : G.edgeSet) :
    Measurable (closeGlobalEdge e) := (continuous_closeGlobalEdge e).measurable

omit [Countable V] in
/-- A rooted finite-edge cover: after deleting finitely many edges, some
infinite surviving cluster can be chosen in the original cluster of the root. -/
theorem exists_infinite_cluster_avoid_connected {ω : G.edgeSet → Bool}
    {x : V} {A : Set (Sym2 V)} (hA : A.Finite)
    (h : (FK.ClusterCover.clusterAvoid G ω ∅ x).Infinite) :
    ∃ z : V, OpenConnected G ω Set.univ x z ∧
      (FK.ClusterCover.clusterAvoid G ω A z).Infinite := by
  obtain ⟨L, hLfin, hL⟩ := FK.ClusterCover.exists_finite_cover
    (G := G) (ω := ω) x hA
  let C : Set V := FK.ClusterCover.clusterAvoid G ω ∅ x
  let L' : Set V := {z ∈ L | z ∈ C}
  have hL'fin : L'.Finite := hLfin.subset fun z hz => hz.1
  have hsub : C ⊆ ⋃ z ∈ L', FK.ClusterCover.clusterAvoid G ω A z := by
    intro y hy
    obtain ⟨z, hzL, hzy⟩ := hL y hy
    have hzC : z ∈ C := by
      have hzy' : OpenConnected G ω Set.univ z y :=
        OpenConnected.mono_edges hzy (Set.subset_univ _)
      have hy' : OpenConnected G ω Set.univ x y := by
        simpa [C, FK.ClusterCover.clusterAvoid] using hy
      simpa [C, FK.ClusterCover.clusterAvoid] using hy'.trans (openConnected_symm hzy')
    exact Set.mem_iUnion₂.mpr ⟨z, ⟨hzL, hzC⟩, hzy⟩
  have hinf : (⋃ z ∈ L', FK.ClusterCover.clusterAvoid G ω A z).Infinite :=
    h.mono hsub
  by_contra hall
  push Not at hall
  exact hinf (Set.Finite.biUnion hL'fin fun z hz => hall z (by
    simpa [C, FK.ClusterCover.clusterAvoid] using hz.2))

omit [Countable V] in
/-- At-most-one infinite cluster is preserved when finitely many coordinates
are opened.  Each new infinite cluster contains an infinite cluster of the
smaller configuration rooted in the original new cluster. -/
theorem globalAtMostOne_of_finite_change_le {A : Set (Sym2 V)} (hA : A.Finite)
    {ξ ω : G.edgeSet → Bool} (hle : ξ ≤ ω)
    (hagree : ∀ e : G.edgeSet, (e : Sym2 V) ∉ A → ξ e = ω e)
    (hξ : GlobalAtMostOne G ξ) : GlobalAtMostOne G ω := by
  intro x y hx hy
  change {z : V | OpenConnected G ω Set.univ x z}.Infinite at hx
  change {z : V | OpenConnected G ω Set.univ y z}.Infinite at hy
  have hx0 : (FK.ClusterCover.clusterAvoid G ω ∅ x).Infinite := by
    simpa only [FK.ClusterCover.clusterAvoid_empty_eq] using hx
  have hy0 : (FK.ClusterCover.clusterAvoid G ω ∅ y).Infinite := by
    simpa only [FK.ClusterCover.clusterAvoid_empty_eq] using hy
  obtain ⟨zx, hxzx, hzx⟩ := exists_infinite_cluster_avoid_connected hA hx0
  obtain ⟨zy, hyzy, hzy⟩ := exists_infinite_cluster_avoid_connected hA hy0
  have htransport : ∀ z : V, FK.ClusterCover.clusterAvoid G ω A z =
      FK.ClusterCover.clusterAvoid G ξ A z := by
    intro z
    ext w
    change OpenConnected G ω (Set.univ \ A) z w ↔
      OpenConnected G ξ (Set.univ \ A) z w
    constructor
    · intro h
      exact OpenConnected.congr h fun e he => (hagree e he.2).symm
    · intro h
      exact OpenConnected.congr h fun e he => hagree e he.2
  rw [htransport] at hzx hzy
  have hzxξ : {w : V | OpenConnected G ξ Set.univ zx w}.Infinite := by
    rw [← FK.ClusterCover.clusterAvoid_empty_eq]
    exact hzx.mono (FK.ClusterCover.clusterAvoid_antitone (Set.empty_subset A) zx)
  have hzyξ : {w : V | OpenConnected G ξ Set.univ zy w}.Infinite := by
    rw [← FK.ClusterCover.clusterAvoid_empty_eq]
    exact hzy.mono (FK.ClusterCover.clusterAvoid_antitone (Set.empty_subset A) zy)
  have hzz : OpenConnected G ω Set.univ zx zy :=
    OpenConnected.mono_config (hξ zx zy hzxξ hzyξ) hle
  exact (hxzx.trans hzz).trans (openConnected_symm hyzy)


omit [Countable V] in
/-- Closing the interior of a box and then deleting just one of its edges has
at most one infinite cluster whenever the fully closed exterior configuration
has that property. -/
lemma globalAtMostOne_closeGlobalEdge_of_closeInside
    (B : FiniteBox G.edgeSet) (e : B.edges) (η : B.Exterior) (ξ : B.Interior)
    (hclosed : GlobalAtMostOne G (closeInside B η)) :
    GlobalAtMostOne G (closeGlobalEdge (e.1 : G.edgeSet) (B.glue (η, ξ))) := by
  let A : Set (Sym2 V) := Subtype.val '' (B.edges : Set G.edgeSet)
  have hA : A.Finite := B.edges.finite_toSet.image Subtype.val
  have hfe : ∀ f : G.edgeSet, f ∉ B.edges → f ≠ (e.1 : G.edgeSet) := by
    intro f hf hfe
    apply hf
    rw [hfe]
    exact e.2
  refine globalAtMostOne_of_finite_change_le (A := A) (ξ := closeInside B η)
    (ω := closeGlobalEdge (e.1 : G.edgeSet) (B.glue (η, ξ))) hA ?_ ?_ hclosed
  · intro f
    by_cases hf : f ∈ B.edges
    · simp [closeInside, FiniteBox.glue, hf]
    · simp [closeInside, FiniteBox.glue, hf, closeGlobalEdge, hfe f hf]
  · intro f hfA
    have hf : f ∉ B.edges := by
      intro h
      exact hfA ⟨f, h, rfl⟩
    simp [closeInside, FiniteBox.glue, hf, closeGlobalEdge, hfe f hf]

/-- Noncoherent finite energy gives almost-sure at-most-one-cluster uniqueness
after deleting any prescribed edge of any finite box.  No DLR hypothesis on the
weak limit is used. -/
theorem ae_globalAtMostOne_closeGlobalEdge_of_isFKLimit
    (exh : BoxExhaustion G.edgeSet) (B : FiniteBox G.edgeSet)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit exh hq hp₁.le a μ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω)
    (e : B.edges) :
    ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      GlobalAtMostOne G (closeGlobalEdge (e.1 : G.edgeSet) ω) := by
  have hgood := NoncoherentFiniteEnergy.ae_globalAtMostOne_closeInside_of_isFKLimit
    exh B hq hp₀ hp₁ a hμ hglobal
  let P : B.Exterior → Prop := fun η => ∀ ξ : B.Interior,
    GlobalAtMostOne G (closeGlobalEdge (e.1 : G.edgeSet) (B.glue (η, ξ)))
  have hPgood : ∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior), P η := by
    filter_upwards [hgood] with η hη
    intro ξ
    exact globalAtMostOne_closeGlobalEdge_of_closeInside B e η ξ hη
  have hPmeas : MeasurableSet {η | P η} := by
    rw [measurableSet_setOfPred]
    apply Measurable.forall
    intro ξ
    have hm := measurableSet_setOfPred.mp
      ((measurableSet_globalAtMostOne G).preimage
        ((measurable_closeGlobalEdge' (e.1 : G.edgeSet)).comp
          (B.splitEquiv.symm.measurable.comp (measurable_id.prodMk
            (measurable_const : Measurable fun _ : B.Exterior => ξ)))))
    simpa only [Function.comp_apply, FiniteBox.splitEquiv_symm_apply, id_eq,
      Set.mem_ofPred_eq] using hm
  let f : Configuration G.edgeSet → B.Exterior := fun ω => (B.splitEquiv ω).1
  have hf : Measurable f := measurable_fst.comp B.splitEquiv.measurable
  change ∀ᵐ η ∂Measure.map f (μ : Measure (Configuration G.edgeSet)), P η at hPgood
  have hm := (ae_map_iff hf.aemeasurable hPmeas).mp hPgood
  filter_upwards [hm] with ω hω
  have h := hω (B.splitEquiv ω).2
  simpa only [P, f, FiniteBox.splitEquiv_apply, B.glue_split] using h


omit [Countable V] in
/-- Transport an almost-everywhere property from a box exterior marginal to the
original configuration law. -/
lemma ae_exterior_map (B : FiniteBox G.edgeSet)
    (μ : ProbabilityMeasure (Configuration G.edgeSet))
    {P : B.Exterior → Prop} (hP : MeasurableSet {η | P η}) :
    (∀ᵐ η ∂(B.exteriorMeasure μ : Measure B.Exterior), P η) ↔
      ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), P ((B.splitEquiv ω).1) := by
  let f : Configuration G.edgeSet → B.Exterior := fun ω => (B.splitEquiv ω).1
  have hf : Measurable f := measurable_fst.comp B.splitEquiv.measurable
  change (∀ᵐ η ∂Measure.map f (μ : Measure (Configuration G.edgeSet)), P η) ↔ _
  exact ae_map_iff hf.aemeasurable hP

local instance boundaryPartitionMeasurableSpaceGlobal (W : Type*) :
    MeasurableSpace (Setoid W) := ⊤

local instance finiteSetoidGlobal (W : Type*) [Finite W] : Finite (Setoid W) := by
  apply Finite.of_injective (fun α : Setoid W => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

local instance singletonSetoidGlobal (W : Type*) : MeasurableSingletonClass (Setoid W) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

local instance measurableEqSetoidGlobal (W : Type*) [Finite W] : MeasurableEq (Setoid W) :=
  ⟨Set.Countable.measurableSet (Set.to_countable _)⟩

/-- Every geometric target convention agrees with the canonical free
convention on almost every exterior of a noncoherent FK weak limit. -/
theorem ae_partition_eq_free_of_isFKLimit
    (exh : BoxExhaustion G.edgeSet) (data : SimpleGraphBoxData G exh.box)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (exh.box n).BoundaryPartition) (Ψ : BoundaryAssignment exh.box)
    (hΨ : IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit exh hq hp₁.le a μ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω)
    (b : ℕ) :
    ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      Ψ.partition b (((exh.box b).splitEquiv ω).1) =
        data.free.partition b (((exh.box b).splitEquiv ω).1) := by
  have hunique := NoncoherentFiniteEnergy.aeAtMostOne_geometry_of_isFKLimit
    exh data hq hp₀ hp₁ a hμ hglobal b
  have hgood : ∀ᵐ η ∂((exh.box b).exteriorMeasure μ : Measure (exh.box b).Exterior),
      Ψ.partition b η = data.free.partition b η := by
    filter_upwards [hunique] with η hη
    exact partition_eq_free_of_atMostOne data.geometry Ψ hΨ hη
  have hmeas : MeasurableSet {η : (exh.box b).Exterior |
      Ψ.partition b η = data.free.partition b η} :=
    measurableSet_setOfPred.mpr ((Ψ.measurable_partition b).eq
      (data.free.measurable_partition b))
  exact (ae_exterior_map (exh.box b) μ hmeas).mp hgood

/-- Closing one edge is idempotent. -/
lemma closeGlobalEdge_idem (e : G.edgeSet) (ω : G.edgeSet → Bool) :
    closeGlobalEdge e (closeGlobalEdge e ω) = closeGlobalEdge e ω := by
  funext f
  by_cases hf : f = e
  · subst f
    simp
  · simp [closeGlobalEdge, hf]

/-- Open connection using only edges internal to a finite vertex set, without
any distinguished deleted edge. -/
def innerConnectionInside (G : SimpleGraph V) (K : Finset V) (x y : V) : Set (G.edgeSet → Bool) :=
  {ω | OpenConnected G ω (innerEdges K) x y}

omit [Countable V] in
lemma isClopen_innerConnectionInside [G.LocallyFinite] (K : Finset V)
    (S : Finset G.edgeSet)
    (hS : ∀ f : G.edgeSet, f.1 ∈ innerEdges K → f ∈ S) (x y : V) :
    IsClopen (innerConnectionInside G K x y) := by
  apply FKLimit.DependsOnCoordinates.isClopen (S := S)
  intro ω η hωη
  have hcfg : ∀ f : G.edgeSet, f.1 ∈ innerEdges K → ω f = η f :=
    fun f hf => hωη f (hS f hf)
  constructor
  · intro h
    exact OpenConnected.congr h hcfg
  · intro h
    exact OpenConnected.congr h (fun f hf => (hcfg f hf).symm)

omit [Countable V] in
lemma innerConnectionInside_mono {K : ℕ → Finset V} (hK : Monotone K) (x y : V) :
    Monotone (fun m => innerConnectionInside G (K m) x y) := by
  intro m n hmn ω hω
  apply OpenConnected.mono_edges hω
  intro f hf
  obtain ⟨u, hu, v, hv, rfl⟩ := hf
  exact ⟨u, hK hmn hu, v, hK hmn hv, rfl⟩

lemma exists_innerConnectionInside_iff {K : ℕ → Finset V} (hK : Monotone K)
    (hKcov : ∀ v : V, ∃ m, v ∈ K m) (x y : V) (ω : G.edgeSet → Bool) :
    (∃ m, ω ∈ innerConnectionInside G (K m) x y) ↔
      OpenConnected G ω Set.univ x y := by
  constructor
  · rintro ⟨m, hm⟩
    exact OpenConnected.mono_edges hm (Set.subset_univ _)
  · intro h
    obtain ⟨p, hp⟩ := h
    obtain ⟨m, hm⟩ := exists_finset_subset hK hKcov p.support.toFinset
    refine ⟨m, openConnected_innerEdges_of_walk p hp (K m) ?_⟩
    intro w hw
    exact hm (by simpa using hw)

/-- The off-edge escape event is the ordinary escaping-pair event pulled back
through deletion of the conditioned edge. -/
def offEdgeEscape (e : G.edgeSet) (K : ℕ → Finset V)
    (C : ℕ → Set (G.edgeSet → Bool)) (x y : V) (m : ℕ) :
    Set (G.edgeSet → Bool) := closeGlobalEdge e ⁻¹' escapeSet G K C x y m

omit [Countable V] in
lemma isClopen_escapeSet [G.LocallyFinite] (K : Finset V)
    (C : Set (G.edgeSet → Bool)) (hC : IsClopen C) (x y : V) :
    IsClopen {ω : G.edgeSet → Bool |
      ClusterMeetsOutside G ω x K ∧ ClusterMeetsOutside G ω y K ∧ ω ∉ C} := by
  have hcl := ((isClopen_clusterMeetsOutside K x).inter
    (isClopen_clusterMeetsOutside K y)).inter hC.compl
  convert hcl using 1
  ext ω
  simp
  tauto

omit [Countable V] in
lemma isClopen_offEdgeEscape [G.LocallyFinite] (e : G.edgeSet)
    (K : ℕ → Finset V) (C : ℕ → Set (G.edgeSet → Bool))
    (hC : ∀ m, IsClopen (C m)) (x y : V) (m : ℕ) :
    IsClopen (offEdgeEscape e K C x y m) := by
  exact (isClopen_escapeSet (K m) (C m) (hC m) x y).preimage
    (continuous_closeGlobalEdge e)

lemma offEdgeEscape_anti (e : G.edgeSet) {K : ℕ → Finset V}
    (hK : Monotone K) {C : ℕ → Set (G.edgeSet → Bool)}
    (hC : Monotone C) (x y : V) : Antitone (offEdgeEscape e K C x y) := by
  intro m n hmn ω hω
  exact escapeSet_anti hK hC hmn hω

/-- The off-edge escaping-pair intersection is null as soon as the law after
edge deletion has at most one infinite cluster. -/
theorem measure_iInter_offEdgeEscape_eq_zero [G.LocallyFinite]
    (e : G.edgeSet) (μ : Measure (G.edgeSet → Bool))
    {K : ℕ → Finset V} (hK : Monotone K)
    (hKcov : ∀ v : V, ∃ m, v ∈ K m)
    {C : ℕ → Set (G.edgeSet → Bool)}
    (hCcl : ∀ m, IsClopen (C m)) {x y : V}
    (hUnion : ∀ ω : G.edgeSet → Bool,
      (∃ m, ω ∈ C m) ↔ OpenConnected G ω Set.univ x y)
    (hOff : ∀ᵐ ω ∂μ, GlobalAtMostOne G (closeGlobalEdge e ω)) :
    μ (⋂ m, offEdgeEscape e K C x y m) = 0 := by
  let T : (G.edgeSet → Bool) → (G.edgeSet → Bool) := closeGlobalEdge e
  have hT : Measurable T := measurable_closeGlobalEdge' e
  have hmap : ∀ᵐ ω ∂Measure.map T μ, GlobalAtMostOne G ω :=
    (ae_map_iff hT.aemeasurable (measurableSet_globalAtMostOne G)).mpr hOff
  have hzero := ClusterEscape.measure_escape_iInter_eq_zero G (Measure.map T μ)
    hK hKcov hUnion hmap
  have hmeas : MeasurableSet (⋂ m, escapeSet G K C x y m) := by
    apply MeasurableSet.iInter
    intro m
    exact (isClopen_escapeSet (K m) (C m) (hCcl m) x y).isOpen.measurableSet
  rw [Measure.map_apply hT hmeas] at hzero
  simpa only [offEdgeEscape, T, Set.preimage_iInter] using hzero

section OffEdgeContainment

variable {B C : FiniteBox G.edgeSet} (N : NestedBox B C)
variable (data : SimpleGraphBoxData G (fun _ : ℕ => C))

/-- Both off-edge clusters leave the finite region when a stage connection is
not explained by a path in that region. -/
lemma clusterPair_offEdge_of_outerStage_diff
    (hinj : Function.Injective (data.vertex 0)) (a : C.BoundaryPartition)
    (e : B.edges) (K : Finset V)
    (hKx : data.vertex 0 (N.vert (B.source e)) ∈ K)
    (hKy : data.vertex 0 (N.vert (B.target e)) ∈ K)
    (hγ : ∀ u v : C.Vertex, u ≠ v → a.r u v →
      data.vertex 0 u ∉ K ∧ data.vertex 0 v ∉ K)
    (ω : G.edgeSet → Bool) (hstage : ω ∈ outerStageConnectionEvent N a e)
    (hnot : ω ∉ offEdgeConnectionInside (e.1 : G.edgeSet) K
      (data.vertex 0 (N.vert (B.source e)))
      (data.vertex 0 (N.vert (B.target e)))) :
    ClusterMeetsOutside G (closeGlobalEdge (e.1 : G.edgeSet) ω)
        (data.vertex 0 (N.vert (B.source e))) K ∧
      ClusterMeetsOutside G (closeGlobalEdge (e.1 : G.edgeSet) ω)
        (data.vertex 0 (N.vert (B.target e))) K := by
  let x := data.vertex 0 (N.vert (B.source e))
  let y := data.vertex 0 (N.vert (B.target e))
  let e0 : G.edgeSet := e.1
  let η0 : G.edgeSet → Bool := closeGlobalEdge e0 ω
  have hγ' : ∀ u v : V, u ≠ v → (globalBoundary data hinj a).r u v →
      u ∉ K ∧ v ∉ K := by
    intro u v huv hrel
    rcases hrel with ⟨c, d, huc, hvd, hcd⟩ | heq
    · subst u
      subst v
      have hne : c ≠ d := by
        intro h
        subst d
        exact huv rfl
      exact hγ c d hne hcd
    · exact (huv heq).elim
  have hconn : (wiredGraph G (globalBoundary data hinj a)
      (closeOutside C η0)).Reachable x y :=
    (outerStageConnectionEvent_iff_globalWired N data hinj a e ω).mp hstage
  have hnotin : ¬ OpenConnected G (closeOutside C η0) (innerEdges K) x y := by
    intro hc
    apply hnot
    exact OpenConnected.mono_config hc (closeOutside_le η0)
  have hpair := escape_pair_of_wiredConn_ne hγ' hKx hKy hconn hnotin
  constructor
  · obtain ⟨z, hzK, hxz⟩ := hpair.1
    exact ⟨z, hzK, OpenConnected.mono_config hxz (closeOutside_le η0)⟩
  · obtain ⟨z, hzK, hyz⟩ := hpair.2
    exact ⟨z, hzK, OpenConnected.mono_config hyz (closeOutside_le η0)⟩

end OffEdgeContainment

end

end FK.NestedFinDLR.GlobalClosure
