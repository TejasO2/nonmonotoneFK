import FK.GlobalOuterGeometry
import FK.MetricStageGeometry
import FK.CoherentAllBoxesAdapters

/-! Arbitrary noncoherent nested weak FK limits under global uniqueness. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR.GlobalClosure

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ClusterEscape
open FK.NestedMixture
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.CoherentAllBoxes
open FK.InfiniteVolume.CoherentAllBoxes.AllBoxSimpleGraphBoxData

noncomputable section

universe u

theorem isDLR_of_globalAtMostOne_growingFamily_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (F : GrowingFamily.{u, u} G.edgeSet) (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (F.box n).BoundaryPartition)
    (Ψ : BoundaryAssignment F.box) (hΨ : IsGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit F.exh hq hp₁.le a μ)
    (hcompat : ∀ {k n : ℕ} (hkn : k ≤ n) (x : (F.box k).Vertex),
      data.vertex n ((F.nest k n hkn).vert x) = data.vertex k x)
    (b : ℕ) (K : (F.box b).edges → ℕ → Finset V)
    (S : (F.box b).edges → ℕ → Finset G.edgeSet)
    (hKmono : ∀ e, Monotone (K e))
    (hKcov : ∀ e v, ∃ m, v ∈ K e m)
    (hend : ∀ e m, data.vertex b ((F.box b).source e) ∈ K e m ∧
      data.vertex b ((F.box b).target e) ∈ K e m)
    (hKS : ∀ e m (f : G.edgeSet), f.1 ∈ innerEdges (K e m) → f ∈ S e m)
    (hfar : ∀ e m, ∀ᶠ n in atTop, ∀ u v : (F.box n).Vertex, u ≠ v → (a n).r u v →
      data.vertex n u ∉ K e m ∧ data.vertex n v ∉ K e m)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    (F.box b).IsDLR hq hp₁.le (Ψ.partition b) (Ψ.measurable_partition b) μ := by
  let N : ∀ n : ℕ, NestedBox (F.box b) (F.box (b + n)) :=
    fun n => F.nest b (b + n) (by omega)
  let μs : ℕ → ProbabilityMeasure (Configuration G.edgeSet) :=
    fun n => (F.box (b + n)).finiteVolumeLaw hq hp₁.le (a (b + n))
  let C : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e n => outerStageConnectionEvent (N n) (a (b + n)) e
  let lower : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e m => offEdgeConnectionInside (e.1 : G.edgeSet) (K e m)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  let inner : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e m => innerConnectionInside G (K e m)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  let Cinf : (e : (F.box b).edges) → Set (Configuration G.edgeSet) :=
    fun e => MovingClopenRate.FiniteBox.specificationConnectionEvent (F.box b)
      (data.free.partition b) e
  let esc : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e m => offEdgeEscape (e.1 : G.edgeSet) (K e) (inner e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e)) m
  have hshift : Tendsto (fun n : ℕ => b + n) atTop atTop := by
    simpa only [Nat.add_comm] using (tendsto_add_atTop_nat b)
  have hμtail : Tendsto μs atTop (𝓝 μ) := by
    have hμ0 : Tendsto (fun n => (F.box n).finiteVolumeLaw hq hp₁.le (a n))
        atTop (𝓝 μ) := hμ
    simpa only [μs, Function.comp_def] using hμ0.comp hshift
  have hα0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hβ1 : FK.prime (q : ℝ) (p : ℝ) ≤ 1 :=
    FK.prime_le_one (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁.le)
  have hβ0 : 0 ≤ FK.prime (q : ℝ) (p : ℝ) :=
    FK.prime_nonneg (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁.le)
  have hα1 : (p : ℝ) ≤ 1 := by exact_mod_cast hp₁.le
  have hCcl : ∀ e n, IsClopen (C e n) := by
    intro e n
    exact isClopen_outerStageConnectionEvent (N n) (a (b + n)) e
  have hlowerCl : ∀ e m, IsClopen (lower e m) := by
    intro e m
    exact isClopen_offEdgeConnectionInside (e.1 : G.edgeSet) (K e m)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
      (S e m) (hKS e m)
  have hlowerMono : ∀ e, Monotone (lower e) := by
    intro e
    exact offEdgeConnectionInside_mono (e.1 : G.edgeSet) (hKmono e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  have hUnion : ∀ e ω, (∃ m, ω ∈ lower e m) ↔ ω ∈ Cinf e := by
    intro e ω
    exact (exists_offEdgeConnectionInside_iff (e.1 : G.edgeSet) (hKmono e) (hKcov e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e)) ω).trans
      (free_specificationConnectionEvent_iff_openConnected
        (constantBoxData data b) (hinj b) e ω).symm
  have hsub : ∀ e m, ∀ᶠ n in atTop, lower e m ⊆ C e n := by
    intro e m
    have hS : ∀ᶠ n in atTop, S e m ⊆ (F.box (b + n)).edges := by
      simpa only [GrowingFamily.exh] using hshift.eventually (F.exh.eventually_subset (S e m))
    filter_upwards [hS] with n hn ω hω
    refine outerStage_mem_of_offEdgeConnectionInside (N n)
      (constantBoxData data (b + n)) (hinj (b + n)) (a (b + n)) e (K e m) (S e m)
      (hKS e m) hn ω ?_
    simpa only [constantBoxData_vertex, N, hcompat] using hω
  have hsdiff : ∀ e m, ∀ᶠ n in atTop, C e n \ lower e m ⊆ esc e m := by
    intro e m
    have hf : ∀ᶠ n in atTop, ∀ u v : (F.box (b + n)).Vertex, u ≠ v →
        (a (b + n)).r u v → data.vertex (b + n) u ∉ K e m ∧
          data.vertex (b + n) v ∉ K e m :=
      hshift.eventually (hfar e m)
    filter_upwards [hf] with n hn ω hω
    have hx : (constantBoxData data (b + n)).vertex 0
        ((N n).vert ((F.box b).source e)) ∈ K e m := by
      simpa only [constantBoxData_vertex, N, hcompat] using (hend e m).1
    have hy : (constantBoxData data (b + n)).vertex 0
        ((N n).vert ((F.box b).target e)) ∈ K e m := by
      simpa only [constantBoxData_vertex, N, hcompat] using (hend e m).2
    have hnot : ω ∉ offEdgeConnectionInside (e.1 : G.edgeSet) (K e m)
        ((constantBoxData data (b + n)).vertex 0 ((N n).vert ((F.box b).source e)))
        ((constantBoxData data (b + n)).vertex 0 ((N n).vert ((F.box b).target e))) := by
      simpa only [lower, constantBoxData_vertex, N, hcompat] using hω.2
    have hres := clusterPair_offEdge_of_outerStage_diff (N n)
      (constantBoxData data (b + n)) (hinj (b + n)) (a (b + n)) e (K e m)
      hx hy hn ω hω.1 hnot
    change closeGlobalEdge (e.1 : G.edgeSet) ω ∈ escapeSet G (K e) (inner e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e)) m
    refine ⟨?_, ?_, ?_⟩
    · simpa only [constantBoxData_vertex, N, hcompat] using hres.1
    · simpa only [constantBoxData_vertex, N, hcompat] using hres.2
    · exact hω.2
  have hInnerCl : ∀ e m, IsClopen (inner e m) := by
    intro e m
    exact isClopen_innerConnectionInside (K e m) (S e m) (hKS e m)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  have hInnerMono : ∀ e, Monotone (inner e) := by
    intro e
    exact innerConnectionInside_mono (hKmono e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  have hescCl : ∀ e m, IsClopen (esc e m) := by
    intro e m
    exact isClopen_offEdgeEscape (e.1 : G.edgeSet) (K e) (inner e)
      (hInnerCl e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e)) m
  have hescAnti : ∀ e, Antitone (esc e) := by
    intro e
    exact offEdgeEscape_anti (e.1 : G.edgeSet) (hKmono e) (hInnerMono e)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  have hescNull : ∀ e, (μ : Measure (Configuration G.edgeSet))
      (⋂ m, esc e m) = 0 := by
    intro e
    have hOff := ae_globalAtMostOne_closeGlobalEdge_of_isFKLimit
      F.exh (F.box b) hq hp₀ hp₁ a hμ hglobal e
    exact measure_iInter_offEdgeEscape_eq_zero (e.1 : G.edgeSet)
      (μ : Measure (Configuration G.edgeSet)) (hKmono e) (hKcov e)
      (hInnerCl e)
      (exists_innerConnectionInside_iff (hKmono e) (hKcov e)
        (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e)))
      hOff
  have hfin : ∀ (e : (F.box b).edges) (n : ℕ)
      (g : (F.box b).Exterior × Glauber.OffConfig Bool (F.box b).edges e → ℝ≥0∞),
      Measurable g →
      ∫⁻ ω, (bif (F.box b).splitBit e ω then g ((F.box b).splitOff e ω) else 0)
        ∂(μs n : Measure (Configuration G.edgeSet)) =
      ∫⁻ ω, ENNReal.ofReal (OneEdgeNoEscape.twoValuedRate (p : ℝ)
        (FK.prime (q : ℝ) (p : ℝ)) (C e n) ω) * g ((F.box b).splitOff e ω)
        ∂(μs n : Measure (Configuration G.edgeSet)) := by
    intro e n g hg
    have hbn : b ≤ b + n := by omega
    have hpoint := onePoint_twoValuedRate_growingFamily F hq hp₀ hp₁ a hbn e g hg
    have hCspec : C e n = MovingClopenRate.FiniteBox.specificationConnectionEvent
        (F.box b) ((inducedAssignments F a (b + n)).partition b) e := by
      ext ω
      change ω ∈ outerStageConnectionEvent (N n) (a (b + n)) e ↔ _
      rw [outerStageConnectionEvent_eq_specification]
      simp only [inducedAssignments, hbn, dite_true, N]
      rfl
    rw [← hCspec] at hpoint
    simpa only [μs] using hpoint
  have hrate : ∀ e, ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      OneEdgeNoEscape.twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) (Cinf e) ω =
        Glauber.FKBridge.openRate (F.box b).graph (q := q) (p := p)
          (Ψ.partition b (((F.box b).splitOff e ω).1)) e
          (((F.box b).splitOff e ω).2) := by
    intro e
    have hpart := ae_partition_eq_free_of_isFKLimit F.exh data hq hp₀ hp₁ a Ψ hΨ
      hμ hglobal b
    filter_upwards [hpart] with ω hω
    calc
      OneEdgeNoEscape.twoValuedRate (p : ℝ) (FK.prime (q : ℝ) (p : ℝ)) (Cinf e) ω =
          Glauber.FKBridge.openRate (F.box b).graph (q := q) (p := p)
            (data.free.partition b (((F.box b).splitOff e ω).1)) e
            (((F.box b).splitOff e ω).2) :=
        (congrFun (OneEdgeNoEscape.openRate_eq_twoValuedRate (F.box b) e
          (data.free.partition b)) ω).symm
      _ = Glauber.FKBridge.openRate (F.box b).graph (q := q) (p := p)
            (Ψ.partition b (((F.box b).splitOff e ω).1)) e
            (((F.box b).splitOff e ω).2) := by
        have hω' := hω
        change Ψ.partition b (((F.box b).splitOff e ω).1) =
          data.free.partition b (((F.box b).splitOff e ω).1) at hω'
        rw [hω']
  exact GeneralMovingClopenRate.isDLR_of_clopen_escape_moving
    (F.box b) μ hμtail (Ψ.partition b) (Ψ.measurable_partition b)
    hα0 hβ0 hα1 hβ1 hCcl hlowerCl hlowerMono hUnion hsub hsdiff
    hescCl hescAnti hescNull hfin hrate hq hp₀ hp₁


/-- Exterior-supported nonreflexive boundary pairs eventually avoid any fixed
finite vertex set along a genuine edge exhaustion. -/
lemma eventually_far_of_externallySupportedOn_growingFamily
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (F : GrowingFamily.{u, u} G.edgeSet) (data : SimpleGraphBoxData G F.box)
    (a : ∀ n, (F.box n).BoundaryPartition)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData data n) (a n))
    (K : Finset V) :
    ∀ᶠ n in atTop, ∀ u v : (F.box n).Vertex, u ≠ v → (a n).r u v →
      data.vertex n u ∉ K ∧ data.vertex n v ∉ K := by
  let S : Finset G.edgeSet :=
    (NonlocalInterior.finite_clusterSupport (G := G) K.finite_toSet).toFinset
  filter_upwards [F.exh.eventually_subset S] with n hn
  intro u v hne hrel
  obtain ⟨⟨eu, heu, huI⟩, ⟨ev, hev, hvI⟩⟩ := ha n u v hne hrel
  constructor
  · intro hu
    apply heu
    apply hn
    exact (NonlocalInterior.finite_clusterSupport
      (G := G) K.finite_toSet).mem_toFinset.mpr ⟨data.vertex n u, hu, huI⟩
  · intro hv
    apply hev
    apply hn
    exact (NonlocalInterior.finite_clusterSupport
      (G := G) K.finite_toSet).mem_toFinset.mpr ⟨data.vertex n v, hv, hvI⟩

/-- Radius placing two prescribed vertices in every lower metric ball. -/
noncomputable def lowerRadius {V : Type u} {G : SimpleGraph V}
    (_hG : G.Connected) (o x y : V) : ℕ :=
  max (G.dist o x) (G.dist o y) + 1

/-- Canonical lower vertex exhaustion for an unordered pair of endpoints. -/
noncomputable def lowerK {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o x y : V) (m : ℕ) : Finset V :=
  innerBall hG o (lowerRadius hG o x y + m)

/-- Finite set of graph edges incident to the canonical lower vertex set. -/
noncomputable def lowerS {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o x y : V) (m : ℕ) : Finset G.edgeSet :=
  (NonlocalInterior.finite_clusterSupport
    (G := G) (lowerK hG o x y m).finite_toSet).toFinset

lemma lowerK_mono {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o x y : V) : Monotone (lowerK hG o x y) := by
  intro m n hmn z hz
  apply (mem_innerBall hG).2
  have h := (mem_innerBall hG).1 hz
  omega

lemma lowerK_cov {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o x y z : V) : ∃ m, z ∈ lowerK hG o x y m := by
  refine ⟨G.dist o z + 1, (mem_innerBall hG).2 ?_⟩
  omega

lemma lowerK_endpoints {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o x y : V) (m : ℕ) :
    x ∈ lowerK hG o x y m ∧ y ∈ lowerK hG o x y m := by
  constructor <;> apply (mem_innerBall hG).2
  · have h : G.dist o x < lowerRadius hG o x y :=
      (le_max_left _ _).trans_lt (Nat.lt_succ_self _)
    omega
  · have h : G.dist o y < lowerRadius hG o x y :=
      (le_max_right _ _).trans_lt (Nat.lt_succ_self _)
    omega

lemma lowerS_support {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o x y : V) (m : ℕ)
    (f : G.edgeSet) (hf : f.1 ∈ innerEdges (lowerK hG o x y m)) :
    f ∈ lowerS hG o x y m := by
  obtain ⟨u, hu, v, hv, heq⟩ := hf
  exact (NonlocalInterior.finite_clusterSupport
    (G := G) (lowerK hG o x y m).finite_toSet).mem_toFinset.mpr ⟨u, hu, by
    rw [heq]
    exact Sym2.mem_mk_left u v⟩

/-- Whole-exhaustion DLR closure for a genuine nested growing family.  The
lower metric exhaustions, their finite edge supports, and the far-boundary
fact are all constructed internally. -/
theorem mem_dlrMeasures_of_globalAtMostOne_growingFamily_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V)
    (F : GrowingFamily.{u, u} G.edgeSet) (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (F.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit F.exh hq hp₁.le a μ)
    (hcompat : ∀ {k n : ℕ} (hkn : k ≤ n) (x : (F.box k).Vertex),
      data.vertex n ((F.nest k n hkn).vert x) = data.vertex k x)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData data n) (a n))
    (Ψ : BoundaryAssignment F.box) (hΨ : IsGeometric data.geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures F.exh Ψ hq hp₁.le := by
  intro b
  let x : (F.box b).edges → V := fun e => data.vertex b ((F.box b).source e)
  let y : (F.box b).edges → V := fun e => data.vertex b ((F.box b).target e)
  exact isDLR_of_globalAtMostOne_growingFamily_outerStage
    (F := F) (data := data) (hinj := hinj)
    (K := fun e => lowerK hG o (x e) (y e))
    (S := fun e => lowerS hG o (x e) (y e))
    hq hp₀ hp₁ a Ψ hΨ hμ hcompat b
    (fun e => lowerK_mono hG o (x e) (y e))
    (fun e z => lowerK_cov hG o (x e) (y e) z)
    (fun e m => lowerK_endpoints hG o (x e) (y e) m)
    (fun e m f hf => lowerS_support hG o (x e) (y e) m f hf)
    (fun e m => eventually_far_of_externallySupportedOn_growingFamily
      F data a ha (lowerK hG o (x e) (y e) m))
    hglobal


/-- All-finite-box target form of the nested weak-limit theorem at interior
edge parameters.  The target is the source coherent specification, not a bare
family of partitions. -/
theorem mem_allBoxDLRMeasures_of_globalAtMostOne_growingFamily_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V)
    (F : GrowingFamily.{u, u} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, u} G)
    (hinj : ∀ n, Function.Injective ((restrictionData F.exh data).vertex n))
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (F.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit F.exh hq hp₁.le a μ)
    (hcompat : ∀ {k n : ℕ} (hkn : k ≤ n) (x : (F.box k).Vertex),
      (restrictionData F.exh data).vertex n ((F.nest k n hkn).vert x) =
        (restrictionData F.exh data).vertex k x)
    (ha : ∀ n, ExternallySupportedOn
      (constantBoxData (restrictionData F.exh data) n) (a n))
    (Ψ : AllBoxConvention.{u, u} G.edgeSet hq hp₁.le)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction F.exh Ψ μ).2
  exact mem_dlrMeasures_of_globalAtMostOne_growingFamily_outerStage
    hG o F (restrictionData F.exh data) hinj hq hp₀ hp₁ a hμ hcompat ha
    (restriction F.exh Ψ).toBoundaryAssignment
    (isGeometric_restriction F.exh data.geometry Ψ hΨ) hglobal

/-- At zero rate every arbitrary-boundary FK weak limit belongs to every
coherent all-finite-box convention.  No source coherence or graph hypothesis is
needed. -/
theorem mem_allBoxDLRMeasures_zero_of_isFKLimit
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, u} E)
    {q : NNReal} (hq : 0 < q)
    (Ψ : AllBoxConvention.{u, u} E hq (p := 0) bot_le)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh hq (p := 0) bot_le a μ) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact ConventionTransport.mem_gibbsMeasures_zero_of_mem_limitOrGibbs
    exh (restriction exh Ψ) (Or.inl ⟨a, hμ⟩)

/-- At unit rate every arbitrary-boundary FK weak limit belongs to every
coherent all-finite-box convention, again with no source coherence input. -/
theorem mem_allBoxDLRMeasures_one_of_isFKLimit
    {E : Type u} [Countable E] (exh : BoxExhaustion.{u, u} E)
    {q : NNReal} (hq : 0 < q)
    (Ψ : AllBoxConvention.{u, u} E hq (p := 1) le_rfl)
    (a : ∀ n, (exh.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration E)}
    (hμ : IsFKLimit exh hq (p := 1) le_rfl a μ) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  apply (mem_allBoxDLRMeasures_iff_mem_gibbsMeasures_restriction exh Ψ μ).2
  exact ConventionTransport.mem_gibbsMeasures_one_of_mem_limitOrGibbs
    exh (restriction exh Ψ) (Or.inl ⟨a, hμ⟩)


/-- All-parameter form of the source weak-limit branch, with a coherent
all-finite-box target. -/
theorem mem_allBoxDLRMeasures_of_globalAtMostOne_growingFamily_outerStage_of_le_one
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V)
    (F : GrowingFamily.{u, u} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, u} G)
    (hinj : ∀ n, Function.Injective ((restrictionData F.exh data).vertex n))
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (a : ∀ n, (F.box n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit F.exh hq hp a μ)
    (hcompat : ∀ {k n : ℕ} (hkn : k ≤ n) (x : (F.box k).Vertex),
      (restrictionData F.exh data).vertex n ((F.nest k n hkn).vert x) =
        (restrictionData F.exh data).vertex k x)
    (ha : ∀ n, ExternallySupportedOn
      (constantBoxData (restrictionData F.exh data) n) (a n))
    (Ψ : AllBoxConvention.{u, u} G.edgeSet hq hp)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  by_cases hp₀ : 0 < p
  · by_cases hp₁ : p < 1
    · exact mem_allBoxDLRMeasures_of_globalAtMostOne_growingFamily_outerStage
        hG o F data hinj hq hp₀ hp₁ a hμ hcompat ha Ψ hΨ hglobal
    · have hp1 : p = 1 := le_antisymm hp (le_of_not_gt hp₁)
      subst p
      exact mem_allBoxDLRMeasures_one_of_isFKLimit F.exh hq Ψ a hμ
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp₀) zero_le
    subst p
    exact mem_allBoxDLRMeasures_zero_of_isFKLimit F.exh hq Ψ a hμ

/-- Proposition 1.8(2) for the repository's genuine nested-growing-box source
model and coherent all-finite-box conventions.  The disjunction is the two
source branches of `FK(p,q)`: an already-Gibbs law, or an actual arbitrary-
boundary finite-volume weak limit.  Exterior support records the source
outer-boundary class; it is not a fixed-source specification. -/
theorem proposition_1_8_2_growingFamily
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V)
    (F : GrowingFamily.{u, u} G.edgeSet)
    (data : AllBoxSimpleGraphBoxData.{u, u} G)
    (hinj : ∀ n, Function.Injective ((restrictionData F.exh data).vertex n))
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (hcompat : ∀ {k n : ℕ} (hkn : k ≤ n) (x : (F.box k).Vertex),
      (restrictionData F.exh data).vertex n ((F.nest k n hkn).vert x) =
        (restrictionData F.exh data).vertex k x)
    (Φ Ψ : AllBoxConvention.{u, u} G.edgeSet hq hp)
    (hΦ : IsAllBoxGeometric data.geometry Φ)
    (hΨ : IsAllBoxGeometric data.geometry Ψ)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (ha : ∀ a : ∀ n, (F.box n).BoundaryPartition,
      IsFKLimit F.exh hq hp a μ →
      ∀ n, ExternallySupportedOn (constantBoxData (restrictionData F.exh data) n) (a n))
    (hsource : μ ∈ AllBoxDLRMeasures Φ ∨
      ∃ a : ∀ n, (F.box n).BoundaryPartition, IsFKLimit F.exh hq hp a μ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ AllBoxDLRMeasures Ψ := by
  rcases hsource with hμ | ⟨a, hμ⟩
  · exact mem_allBoxDLRMeasures_of_globalAtMostOne_of_le_one
      F.exh data hq hp Φ Ψ hΦ hΨ μ hμ hglobal
  · exact mem_allBoxDLRMeasures_of_globalAtMostOne_growingFamily_outerStage_of_le_one
      hG o F data hinj hq hp a hμ hcompat (ha a hμ) Ψ hΨ hglobal


/-- Metric-exhaustion form: arbitrary externally supported boundaries, every
`q > 0`, interior `p`, and every geometric target convention.  Unlike the
older prime-dominated theorem, no stochastic majorant or subcritical
hypothesis is needed. -/
theorem mem_dlrMeasures_of_globalAtMostOne_metric_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]
    (hG : G.Connected) (o : V) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (metricBox hG o n).BoundaryPartition)
    {μ : ProbabilityMeasure (Configuration G.edgeSet)}
    (hμ : IsFKLimit (metricBoxExhaustion hG o) hq hp₁.le a μ)
    (ha : ∀ n, ExternallySupportedOn (constantBoxData (metricBoxData hG o) n) (a n))
    (Ψ : BoundaryAssignment (metricBoxExhaustion hG o).box)
    (hΨ : IsGeometric (metricBoxData hG o).geometry Ψ)
    (hglobal : ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)), GlobalAtMostOne G ω) :
    μ ∈ DLRMeasures (metricBoxExhaustion hG o) Ψ hq hp₁.le := by
  intro b
  have hμ' : IsFKLimit (metricGrowingFamily hG o).exh hq hp₁.le a μ := hμ
  exact isDLR_of_globalAtMostOne_growingFamily_outerStage
    (F := metricGrowingFamily hG o) (data := metricBoxData hG o)
    (hinj := metricBoxData_vertex_injective hG o)
    (K := fun e => metricLowerK hG o e) (S := fun e => metricLowerS hG o e)
    hq hp₀ hp₁ a Ψ hΨ hμ'
    (fun hkn x => metricGrowingFamily_compat hG o hkn x) b
    (fun e => metricLowerK_mono hG o e) (fun e => metricLowerK_cov hG o e)
    (fun e => metricLowerK_endpoints hG o e)
    (fun e m f hf => metricLowerS_support hG o e m f hf)
    (fun e m => eventually_far_of_externallySupportedOn_metric hG o a ha e m)
    hglobal


end

end FK.NestedFinDLR.GlobalClosure
