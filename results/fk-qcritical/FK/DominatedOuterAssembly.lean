import FK.StageContainment

/-! End-to-end free DLR closure for dominated outer-boundary stage families. -/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
open CurvatureVariance.Infra.Percolation

namespace FK.NestedFinDLR

attribute [local instance] Classical.decEq Classical.propDecidable

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ClusterEscape
open FK.NestedMixture

universe u

/-- At `q < 1`, a nonpercolating stochastic majorant turns the outer-stage
finite-path/escape geometry into the exact free DLR identity on every fixed
box of a growing family.  The far-boundary hypothesis is the source boundary
condition: no nonreflexive outer-boundary relation may touch the fixed finite
region.  Nested vertex maps must also agree with the global box embeddings. -/
theorem isDLR_free_of_dominated_growingFamily_outerStage
    {V : Type u} [Countable V] {G : SimpleGraph V}
    (F : GrowingFamily.{u, u} G.edgeSet) (data : SimpleGraphBoxData G F.box)
    (hinj : ∀ n, Function.Injective (data.vertex n))
    {q p : NNReal} (hq : 0 < q) (hq1 : q < 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (a : ∀ n, (F.box n).BoundaryPartition)
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
    (ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hdom : ∀ n, FKLimit.StochasticallyDominates ν
      ((F.box n).finiteVolumeLaw hq hp₁.le (a n)))
    (hnoPerc : ∀ x : V, (ν : Measure (Configuration G.edgeSet))
      {ω | {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    (F.box b).IsDLR hq hp₁.le (data.free.partition b)
      (data.free.measurable_partition b) μ := by
  let N : ∀ n : ℕ, NestedBox (F.box b) (F.box (b + n)) :=
    fun n => F.nest b (b + n) (by omega)
  let μs : ℕ → ProbabilityMeasure (Configuration G.edgeSet) :=
    fun n => (F.box (b + n)).finiteVolumeLaw hq hp₁.le (a (b + n))
  let C : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e n => outerStageConnectionEvent (N n) (a (b + n)) e
  let lower : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e m => offEdgeConnectionInside (e.1 : G.edgeSet) (K e m)
      (data.vertex b ((F.box b).source e)) (data.vertex b ((F.box b).target e))
  let Cinf : (e : (F.box b).edges) → Set (Configuration G.edgeSet) :=
    fun e => MovingClopenRate.FiniteBox.specificationConnectionEvent (F.box b)
      (data.free.partition b) e
  let esc : (e : (F.box b).edges) → ℕ → Set (Configuration G.edgeSet) :=
    fun e m => {ω | ClusterMeetsOutside G ω (data.vertex b ((F.box b).source e)) (K e m)}
  have hshift : Tendsto (fun n : ℕ => b + n) atTop atTop := by
    simpa only [Nat.add_comm] using (tendsto_add_atTop_nat b)
  have hμtail : Tendsto μs atTop (𝓝 μ) := by
    have hμ0 : Tendsto (fun n => (F.box n).finiteVolumeLaw hq hp₁.le (a n))
        atTop (𝓝 μ) := hμ
    simpa only [μs, Function.comp_def] using hμ0.comp hshift
  have hα0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hβ1 : FK.prime (q : ℝ) (p : ℝ) ≤ 1 :=
    FK.prime_le_one (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁.le)
  have hαβ : (p : ℝ) < FK.prime (q : ℝ) (p : ℝ) := by
    rw [OneEdgeNoEscape.lt_prime_iff (by exact_mod_cast hq)
      (by exact_mod_cast hp₀) (by exact_mod_cast hp₁)]
    exact_mod_cast hq1
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
    have hres := clusterMeetsOutside_of_outerStage_diff (N n)
      (constantBoxData data (b + n)) (hinj (b + n)) (a (b + n)) e (K e m)
      hx hy hn ω hω.1 hnot
    change ClusterMeetsOutside G ω (data.vertex b ((F.box b).source e)) (K e m)
    simpa only [constantBoxData_vertex, N, hcompat] using hres
  have hescMeas : ∀ e m, MeasurableSet (esc e m) := by
    intro e m
    exact measurableSet_clusterMeetsOutside G (K e m) (data.vertex b ((F.box b).source e))
  have hescUp : ∀ e m, IsUpperSet (esc e m) := by
    intro e m
    exact isUpperSet_clusterMeetsOutside G (K e m) (data.vertex b ((F.box b).source e))
  have hν : ∀ e, Tendsto (fun m => ((ν : Measure (Configuration G.edgeSet))
      (esc e m)).toReal) atTop (𝓝 0) := by
    intro e
    exact tendsto_measure_clusterMeetsOutside G (ν : Measure (Configuration G.edgeSet))
      (hKmono e) (hKcov e) (data.vertex b ((F.box b).source e))
      (hnoPerc (data.vertex b ((F.box b).source e)))
  have hdomtail : ∀ n, FKLimit.StochasticallyDominates ν (μs n) := by
    intro n
    exact hdom (b + n)
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
          (data.free.partition b (((F.box b).splitOff e ω).1)) e
          (((F.box b).splitOff e ω).2) := by
    intro e
    filter_upwards with ω
    exact (congrFun (OneEdgeNoEscape.openRate_eq_twoValuedRate (F.box b) e
      (data.free.partition b)) ω).symm
  exact MovingClopenRate.isDLR_of_dominated_escape_eventual_moving
    (F.box b) μ hμtail (data.free.partition b) (data.free.measurable_partition b)
    hα0 hαβ hβ1 hCcl hlowerCl hlowerMono hUnion hsub hsdiff hescMeas hescUp
    ν hdomtail hν hfin hrate hq hp₀ hp₁

end FK.NestedFinDLR
