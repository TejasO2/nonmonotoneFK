import FK.PcPos
import FK.ClusterTail
import FK.AGDifferentialShift

/-!
# Root independence of the zero set of the Bernoulli percolation probability

Worker m6 (swarm smwuwykef), direction d8.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Topology

namespace FK.PercolationRoot

open CurvatureVariance.Infra.Percolation

variable {V : Type*} {G : SimpleGraph V}

/-! ## Forcing a set of edges open -/

/-- The configuration obtained from `ω` by forcing every edge of `A` open. -/
noncomputable def forceOpen (A : Set G.edgeSet) (ω : G.edgeSet → Bool) : G.edgeSet → Bool := by
  classical
  exact fun e => if e ∈ A then true else ω e

theorem forceOpen_of_mem {A : Set G.edgeSet} {e : G.edgeSet} (he : e ∈ A)
    (ω : G.edgeSet → Bool) : forceOpen A ω e = true := by
  classical simp [forceOpen, he]

theorem forceOpen_of_notMem {A : Set G.edgeSet} {e : G.edgeSet} (he : e ∉ A)
    (ω : G.edgeSet → Bool) : forceOpen A ω e = ω e := by
  classical simp [forceOpen, he]

theorem le_forceOpen (A : Set G.edgeSet) (ω : G.edgeSet → Bool) : ω ≤ forceOpen A ω := by
  intro e
  classical
  by_cases h : e ∈ A
  · rw [forceOpen_of_mem h]; exact Bool.le_true _
  · rw [forceOpen_of_notMem h]

theorem measurable_forceOpen (A : Set G.edgeSet) : Measurable (forceOpen A) := by
  classical
  refine measurable_pi_iff.mpr (fun e => ?_)
  by_cases h : e ∈ A
  · have : (fun ω : G.edgeSet → Bool => forceOpen A ω e) = fun _ => true := by
      funext ω; exact forceOpen_of_mem h ω
    rw [this]; exact measurable_const
  · have : (fun ω : G.edgeSet → Bool => forceOpen A ω e) = fun ω => ω e := by
      funext ω; exact forceOpen_of_notMem h ω
    rw [this]; exact measurable_pi_apply e

theorem dependsOn_preimage_forceOpen (A : Set G.edgeSet) (E : Set (G.edgeSet → Bool)) :
    DependsOn (· ∈ forceOpen A ⁻¹' E) Aᶜ := by
  intro ω ω' hagree
  have h : forceOpen A ω = forceOpen A ω' := by
    funext e
    by_cases he : e ∈ A
    · rw [forceOpen_of_mem he, forceOpen_of_mem he]
    · rw [forceOpen_of_notMem he, forceOpen_of_notMem he]
      exact hagree e he
  simp only [Set.mem_preimage, h]

/-- The edges of a walk, as a finite set of edges. -/
noncomputable def walkEdges {o x : V} (π : G.Walk o x) : Finset G.edgeSet := by
  classical
  exact (π.darts.map (fun d => (⟨d.edge, d.edge_mem⟩ : G.edgeSet))).toFinset

theorem walkEdges_mem {o x : V} (π : G.Walk o x) (d : G.Dart)
    (hd : d ∈ π.darts) : (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ walkEdges π := by
  classical
  simp only [walkEdges, List.mem_toFinset, List.mem_map]
  exact ⟨d, hd, rfl⟩

/-- A walk all of whose edges lie in `A` is open in the forced configuration. -/
theorem isOpenIn_forceOpen {o x : V} (π : G.Walk o x) {A : Set G.edgeSet}
    (hA : ∀ d ∈ π.darts, (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ A)
    (ω : G.edgeSet → Bool) :
    IsOpenIn (forceOpen A ω) Set.univ π := by
  intro d hd
  exact ⟨trivial, forceOpen_of_mem (hA d hd) ω⟩

/-- Forcing open a set containing the edges of the walk `o → x` carries the open
cluster of `x` into the open cluster of `o`. -/
theorem cluster_subset_forceOpen {o x : V} (π : G.Walk o x) {A : Set G.edgeSet}
    (hA : ∀ d ∈ π.darts, (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ A)
    (ω : G.edgeSet → Bool) :
    {y | OpenConnected G ω Set.univ x y} ⊆
      {y | OpenConnected G (forceOpen A ω) Set.univ o y} := by
  intro y hy
  have hπ : OpenConnected G (forceOpen A ω) Set.univ o x := ⟨π, isOpenIn_forceOpen π hA ω⟩
  exact hπ.trans (OpenConnected.mono_config hy (le_forceOpen A ω))

namespace Cluster

/-- **Finite-energy comparison along a fixed walk.**  For the Bernoulli product
law, the probability that the cluster of `x` is infinite is at most
`p ^ -(edges of the walk)` times the probability that the cluster of `o` is
infinite.  The proof forces the walk's edges open and uses independence of
disjoint coordinate sets. -/
theorem measure_infiniteCluster_mul_le {o x : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (π : G.Walk o x) (p : I) :
    (percolation G p) {ω | {y | OpenConnected G ω Set.univ x y}.Infinite} *
      (ENNReal.ofReal (p : ℝ)) ^ (walkEdges π).card ≤
    (percolation G p) {ω | {y | OpenConnected G ω Set.univ o y}.Infinite} := by
  classical
  set A : Set G.edgeSet := ↑(walkEdges π) with hAdef
  set B : Set (G.edgeSet → Bool) := {ω | ∀ e ∈ walkEdges π, ω e = true} with hBdef
  set Cx : Set (G.edgeSet → Bool) := {ω | {y | OpenConnected G ω Set.univ x y}.Infinite}
    with hCxdef
  set Co : Set (G.edgeSet → Bool) := {ω | {y | OpenConnected G ω Set.univ o y}.Infinite}
    with hCodef
  have hAmem : ∀ d ∈ π.darts, (⟨d.edge, d.edge_mem⟩ : G.edgeSet) ∈ A := by
    intro d hd
    rw [hAdef]
    exact walkEdges_mem π d hd
  -- measurability
  have hBmeas : MeasurableSet B := by
    rw [hBdef]; exact measurableSet_forall_coord (walkEdges π)
  have hComeas : MeasurableSet Co := by
    rw [hCodef]; exact measurableSet_infiniteOpenCluster hG o
  have hFmeas : MeasurableSet (forceOpen A ⁻¹' Co) := (measurable_forceOpen A) hComeas
  -- the walk-open event depends on `A`, the forced preimage on `Aᶜ`
  have hBdep : DependsOn (· ∈ B) A := by
    rw [hBdef, hAdef]
    intro ω ω' hagree
    exact propext ⟨fun h e he => by rw [← hagree e he]; exact h e he,
      fun h e he => by rw [hagree e he]; exact h e he⟩
  have hFdep : DependsOn (· ∈ forceOpen A ⁻¹' Co) Aᶜ := dependsOn_preimage_forceOpen A Co
  have hind := measure_inter_eq_mul_of_dependsOn (ι := G.edgeSet) hFmeas hBmeas hFdep hBdep
    (Set.disjoint_left.mpr (fun a ha ha' => ha ha')) p
  -- on the walk-open event forcing is the identity
  have hset : forceOpen A ⁻¹' Co ∩ B = Co ∩ B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hfix : forceOpen A ω = ω := by
        funext e
        by_cases he : e ∈ A
        · rw [forceOpen_of_mem he]; exact (h2 e he).symm
        · rw [forceOpen_of_notMem he]
      rwa [hfix] at h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hfix : forceOpen A ω = ω := by
        funext e
        by_cases he : e ∈ A
        · rw [forceOpen_of_mem he]; exact (h2 e he).symm
        · rw [forceOpen_of_notMem he]
      rwa [hfix]
  -- monotonicity in the event
  have hmono : (percolation G p) Cx ≤ (percolation G p) (forceOpen A ⁻¹' Co) := by
    refine measure_mono ?_
    intro ω hω
    exact Set.Infinite.mono (cluster_subset_forceOpen π hAmem ω) hω
  have hBval : (percolation G p) B = ENNReal.ofReal (p : ℝ) ^ (walkEdges π).card := by
    rw [hBdef]
    exact bernoulliProduct_cylinder (G.edgeSet) p (walkEdges π)
  calc (percolation G p) Cx * (ENNReal.ofReal (p : ℝ)) ^ (walkEdges π).card
      = (percolation G p) Cx * (percolation G p) B := by rw [hBval]
    _ ≤ (percolation G p) (forceOpen A ⁻¹' Co) * (percolation G p) B := by
        exact mul_le_mul' hmono le_rfl
    _ = (percolation G p) (forceOpen A ⁻¹' Co ∩ B) := hind.symm
    _ = (percolation G p) (Co ∩ B) := by rw [hset]
    _ ≤ (percolation G p) Co := measure_mono (Set.inter_subset_left)

end Cluster

/-! ## Root independence -/

/-- **Quantitative finite-energy bound in `θ` language.**  For any walk
`o → x`, the percolation probability at `x` is at most `p ^ -|π|` times that
at `o`. -/
theorem percolationProb_mul_le {o x : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (π : G.Walk o x) (p : I) :
    percolationProb G x p * (ENNReal.ofReal (p : ℝ)) ^ (walkEdges π).card ≤
      percolationProb G o p := by
  rw [percolationProb_eq, percolationProb_eq]
  exact Cluster.measure_infiniteCluster_mul_le hG π p

/-- **Root independence of `θ = 0`.**  If the open cluster of `o` is almost
surely finite under the Bernoulli product law at a strictly positive parameter,
then the same holds at every vertex `x`. -/
theorem percolationProb_eq_zero_of_root {o x : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) {p : I} (hp0 : 0 < (p : ℝ))
    (ho : percolationProb G o p = 0) : percolationProb G x p = 0 := by
  classical
  obtain ⟨π⟩ := hG o x
  have hineq := Cluster.measure_infiniteCluster_mul_le hG π p
  have hzo : (percolation G p) {ω | {y | OpenConnected G ω Set.univ o y}.Infinite} = 0 := by
    rw [← percolationProb_eq]
    exact ho
  rw [hzo] at hineq
  have hcne : (ENNReal.ofReal (p : ℝ)) ^ (walkEdges π).card ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [ENNReal.ofReal_ne_zero_iff]
    exact hp0
  have hmul : (percolation G p) {ω | {y | OpenConnected G ω Set.univ x y}.Infinite} *
      (ENNReal.ofReal (p : ℝ)) ^ (walkEdges π).card = 0 :=
    le_antisymm hineq (by positivity)
  have hzero : (percolation G p) {ω | {y | OpenConnected G ω Set.univ x y}.Infinite} = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h hcne
  rw [percolationProb_eq]
  exact hzero

/-- **The zero set of `θ` is root independent** at strictly positive parameters. -/
theorem percolationProb_eq_zero_iff_root_pos {o x : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) {p : I} (hp0 : 0 < (p : ℝ)) :
    percolationProb G o p = 0 ↔ percolationProb G x p = 0 :=
  ⟨fun h => percolationProb_eq_zero_of_root hG hp0 h,
    fun h => percolationProb_eq_zero_of_root (G := G) (o := x) (x := o) hG hp0 h⟩

/-- Below the critical probability at a single root, every root has vanishing
percolation probability. -/
theorem forall_percolationProb_eq_zero_of_lt_criticalProb {o : V} [Countable V]
    [G.LocallyFinite] (hG : G.Connected) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hb : b < criticalProb G o) (x : V) :
    percolationProb G x ⟨b, ⟨le_of_lt hb0, hb1⟩⟩ = 0 := by
  have hb' : ((⟨b, ⟨le_of_lt hb0, hb1⟩⟩ : I) : ℝ) < criticalProb G o := hb
  exact percolationProb_eq_zero_of_root hG hb0
    (percolationProb_eq_zero_of_lt_criticalProb hG hb')

/-! ## The degenerate parameter `p = 0` -/

/-- At `p = 0` the product law is almost surely the all-closed configuration. -/
theorem ae_all_closed_percolation_zero [Countable V] (G : SimpleGraph V) :
    ∀ᵐ ω ∂(percolation G (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I)), ∀ e : G.edgeSet, ω e = false := by
  rw [ae_all_iff]
  intro e
  rw [ae_iff]
  have hmeas : MeasurableSet {ω : G.edgeSet → Bool | ω e = false} := by
    have h : {ω : G.edgeSet → Bool | ω e = false} = (fun ω => ω e) ⁻¹' {false} := rfl
    rw [h]
    exact (measurable_pi_apply (X := fun _ : G.edgeSet => Bool) e)
      (measurableSet_singleton false)
  have hone : (percolation G (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I)) {ω | ω e = false} = 1 := by
    have h := bernoulliProduct_coord_false (ι := G.edgeSet)
      (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) e
    simpa using h
  have hcompl : (percolation G (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I)) {ω | ω e = false}ᶜ = 0 := by
    rw [measure_compl hmeas (by simp), hone]
    simp
  have hset : {ω : G.edgeSet → Bool | ¬ω e = false} = {ω | ω e = false}ᶜ := rfl
  rw [hset]
  exact hcompl

/-- A configuration with no open edge has a singleton open cluster. -/
theorem cluster_subset_singleton_of_all_closed {x : V} {ω : G.edgeSet → Bool}
    (hω : ∀ e : G.edgeSet, ω e = false) :
    {y | OpenConnected G ω Set.univ x y} ⊆ {x} := by
  intro y hy
  obtain ⟨p, hp⟩ := hy
  by_contra hne
  have hlen : p.length ≠ 0 := by
    intro h
    have hnil : p.Nil := SimpleGraph.Walk.length_eq_zero_iff.mp h
    exact hne (SimpleGraph.Walk.Nil.eq hnil).symm
  have hdarts : p.darts ≠ [] := by
    intro h
    refine hlen ?_
    rw [← SimpleGraph.Walk.length_darts, h]
    rfl
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil p.darts hdarts
  have hopen := (hp d hd).2
  rw [hω ⟨d.edge, d.edge_mem⟩] at hopen
  exact Bool.noConfusion hopen

/-- The percolation probability vanishes at the degenerate parameter `0`. -/
theorem percolationProb_zero [Countable V] (G : SimpleGraph V) (x : V) :
    percolationProb G x (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) = 0 := by
  rw [percolationProb_eq]
  have hnull : (percolation G (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I))
      {ω : G.edgeSet → Bool | ∃ e : G.edgeSet, ω e = true} = 0 := by
    have hpos := ae_all_closed_percolation_zero (G := G)
    rw [ae_iff] at hpos
    have hset : {ω : G.edgeSet → Bool | ¬∀ e : G.edgeSet, ω e = false} =
        {ω | ∃ e : G.edgeSet, ω e = true} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        rw [not_forall] at h
        obtain ⟨e, he⟩ := h
        exact ⟨e, by cases hv : ω e <;> simp_all⟩
      · rintro ⟨e, he⟩ h
        rw [h e] at he
        exact Bool.noConfusion he
    rw [← hset]
    exact hpos
  refine measure_mono_null ?_ hnull
  intro ω hω
  by_contra hcon
  have hfalse : ∀ e : G.edgeSet, ω e = false := by
    intro e
    cases h : ω e
    · rfl
    · exact absurd ⟨e, h⟩ hcon
  refine hω (Set.Finite.subset (Set.finite_singleton x) ?_)
  intro y hy
  exact cluster_subset_singleton_of_all_closed hfalse hy

/-- **Root independence of `θ = 0` at every parameter.** -/
theorem percolationProb_eq_zero_iff_root {o x : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (p : I) :
    percolationProb G o p = 0 ↔ percolationProb G x p = 0 := by
  rcases eq_or_lt_of_le (p.2.1) with h | h
  · have hp : p = (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) := Subtype.ext h.symm
    rw [hp, percolationProb_zero G o, percolationProb_zero G x]
  · exact percolationProb_eq_zero_iff_root_pos hG h

/-- **The critical probability does not depend on the root.** -/
theorem criticalProb_eq_of_connected {o x : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) : criticalProb G o = criticalProb G x := by
  unfold criticalProb
  congr 1
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (percolationProb_eq_zero_iff_root hG p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (percolationProb_eq_zero_iff_root hG p).mpr hp, rfl⟩

/-- `Percolating G` is exactly the event that some cluster is infinite, as used
by the zero--one law of `FK.ClusterTail`. -/
theorem percolating_eq_hasInfiniteCluster (G : SimpleGraph V) :
    FK.EssentialWindow.Percolating G = {ω : G.edgeSet → Bool |
      FK.ClusterCover.HasInfiniteCluster G ω} := by
  ext ω
  simp only [FK.EssentialWindow.Percolating, FK.ClusterCover.HasInfiniteCluster,
    FK.ClusterCover.clusterAvoid_empty_eq, Set.mem_ofPred_eq]

/-- **The existence event has full mass exactly when some root percolates with
positive probability.**  The forward implication uses root independence and
almost-sure nonpercolation; the reverse uses the zero--one law. -/
theorem percolating_measure_eq_one_iff_percolationProb_pos {o : V} [Countable V]
    [G.LocallyFinite] (hG : G.Connected) (p : I) :
    (percolation G p) (FK.EssentialWindow.Percolating G) = 1 ↔
      percolationProb G o p ≠ 0 := by
  constructor
  · intro hone
    by_contra hzero
    have hnonzero : ∀ x : V, percolationProb G x p = 0 := fun x =>
      (percolationProb_eq_zero_iff_root (o := o) (x := x) hG p).mp hzero
    have hae : ∀ᵐ ω ∂(percolation G p), ω ∈ FK.NonPercolating G :=
      FK.InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero
        p hnonzero
    have hzero' := (FK.EssentialWindow.ae_nonPercolating_iff_measure_percolating_eq_zero G
      (percolation G p)).mp hae
    rw [hzero'] at hone
    exact zero_ne_one hone
  · intro hpos
    have htheta : 0 < percolationProb G o p := pos_iff_ne_zero.mpr hpos
    have hle : percolationProb G o p ≤
        (percolation G p) (FK.EssentialWindow.Percolating G) := by
      rw [percolationProb_eq]
      refine measure_mono ?_
      intro ω hω
      exact ⟨o, hω⟩
    have hpos' : 0 < (percolation G p) (FK.EssentialWindow.Percolating G) :=
      lt_of_lt_of_le htheta hle
    rcases FK.ClusterTail.percolation_hasInfiniteCluster_zero_one G p with h | h
    · rw [← percolating_eq_hasInfiniteCluster] at h
      rw [h] at hpos'
      exact absurd hpos' (lt_irrefl 0)
    · rw [← percolating_eq_hasInfiniteCluster] at h
      exact h


/-! ## The zero-decrement profile is the constant Bernoulli base -/

/-- The decrement weight at zero decrement is the constant base. -/
theorem decrementWeight_zero {E : Type*} (S : Set E) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    FK.AGDifferentialShift.decrementWeight S b 0 = fun _ => (⟨b, ⟨hb0, hb1⟩⟩ : I) := by
  funext e
  apply Subtype.ext
  simp only [FK.AGDifferentialShift.decrementWeight]
  split_ifs with he
  · rw [sub_zero, min_eq_right hb1, max_eq_right hb0]
  · rw [min_eq_right hb1, max_eq_right hb0]

/-- The zero-decrement profile mass is the mass of the constant-parameter
Bernoulli product law. -/
theorem mass_zero_eq_percolation (G : SimpleGraph V) (A : Set (G.edgeSet → Bool))
    (S : Set G.edgeSet) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    FK.AGDifferentialShift.mass A S b 0 =
      ((percolation G ⟨b, ⟨hb0, hb1⟩⟩) A).toReal := by
  rw [FK.AGDifferentialShift.mass, decrementWeight_zero S hb0 hb1]
  rfl

/-- The zero-decrement profile mass is nondecreasing in the base parameter. -/
theorem mass_zero_mono_base {E : Type*} [Countable E] {A : Set (E → Bool)}
    (hA : IsUpperSet A) (hmeas : MeasurableSet A) (S : Set E) {b c : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hbc : b ≤ c) :
    FK.AGDifferentialShift.mass A S b 0 ≤ FK.AGDifferentialShift.mass A S c 0 := by
  have hle : FK.AGDifferentialShift.decrementWeight S b 0 ≤
      FK.AGDifferentialShift.decrementWeight S c 0 := by
    rw [decrementWeight_zero S hb0 hb1, decrementWeight_zero S hc0 hc1]
    intro e
    show ((⟨b, ⟨hb0, hb1⟩⟩ : I) : ℝ) ≤ ((⟨c, ⟨hc0, hc1⟩⟩ : I) : ℝ)
    exact hbc
  have hdom := FK.EssentialWindow.stochasticallyDominates_bernoulliProduct_of_le hle
  have h := FK.EssentialWindow.measure_le_of_stochasticallyDominates hdom hmeas hA
  rw [FK.AGDifferentialShift.mass, FK.AGDifferentialShift.mass]
  exact ENNReal.toReal_mono (by simp) h

/-! ## The subcritical reference baseline -/

/-- **The percolation event is null below the critical probability at one
root**, at a parameter `0 ≤ b < criticalProb G o`.  Root independence supplies
all roots; the degenerate base `b = 0` uses the all-closed law. -/
theorem percolation_percolating_eq_zero {o : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < criticalProb G o) :
    (percolation G ⟨b, ⟨hb0, le_trans (le_of_lt hb) (criticalProb_mem_Icc G o).2⟩⟩)
      (FK.EssentialWindow.Percolating G) = 0 := by
  have hb1 : b ≤ 1 := le_trans (le_of_lt hb) (criticalProb_mem_Icc G o).2
  have hzero : ∀ x : V, percolationProb G x ⟨b, ⟨hb0, hb1⟩⟩ = 0 := by
    intro x
    rcases lt_or_eq_of_le hb0 with hpos | heq
    · exact percolationProb_eq_zero_of_root hG hpos
        (percolationProb_eq_zero_of_lt_criticalProb hG hb)
    · have hp : (⟨b, ⟨hb0, hb1⟩⟩ : I) = (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) :=
        Subtype.ext heq.symm
      rw [hp]
      exact percolationProb_zero G x
  refine (FK.EssentialWindow.ae_nonPercolating_iff_measure_percolating_eq_zero G
    (percolation G ⟨b, ⟨hb0, hb1⟩⟩)).mp ?_
  exact FK.InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero
    ⟨b, ⟨hb0, hb1⟩⟩ hzero

/-- **The subcritical reference baseline.**  For every base `0 ≤ b` below the
critical probability at one root, the zero-decrement profile mass of the actual
percolation event vanishes.  This is the `hbase` binder of
`FK.AGDifferentialShift.exists_subcritical_decrement`, discharged. -/
theorem mass_percolating_eq_zero {o : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : b < criticalProb G o) (S : Set G.edgeSet) :
    FK.AGDifferentialShift.mass (FK.EssentialWindow.Percolating G) S b 0 = 0 := by
  have hb1 : b ≤ 1 := le_trans (le_of_lt hb) (criticalProb_mem_Icc G o).2
  rw [mass_zero_eq_percolation G (FK.EssentialWindow.Percolating G) S hb0 hb1,
    percolation_percolating_eq_zero hG hb0 hb]
  simp

/-- **Almost-sure nonpercolation below the critical probability at a single
root.**  This is the single-root form of
`FK.ae_nonPercolating_percolation_of_lt_criticalProb`, which quantified over
every root. -/
theorem ae_nonPercolating_percolation_of_lt_criticalProb_single {o : V} [Countable V]
    [G.LocallyFinite] (hG : G.Connected) {s : I}
    (hs : (s : ℝ) < criticalProb G o) :
    ∀ᵐ ω ∂(percolation G s), ω ∈ FK.NonPercolating G :=
  FK.InfiniteVolume.NestedAssembly.ae_nonPercolating_percolation_of_percolationProb_eq_zero s
    (fun x => (percolationProb_eq_zero_iff_root (o := o) (x := x) hG s).mp
      (percolationProb_eq_zero_of_lt_criticalProb hG hs))

/-- The increment profile at zero increment has the same mass as the decrement
profile at zero decrement, so the subcritical baseline also covers `incMass`. -/
theorem incMass_percolating_eq_zero {o : V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < criticalProb G o)
    (S : Set G.edgeSet) :
    FK.AGDifferentialShift.incMass (FK.EssentialWindow.Percolating G) S b 0 = 0 := by
  rw [FK.AGDifferentialShift.incMass_zero]
  exact mass_percolating_eq_zero hG hb0 hb S

/-- **The subcritical domination step of Theorem 1.10 with a single root.**
`FK.ae_nonPercolating_of_dominated_by_subcritical` required the critical
hypothesis at every root; root independence makes one root enough. -/
theorem ae_nonPercolating_of_dominated_by_subcritical_single {o : V} [Countable V]
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected) {s : I}
    (hs : (s : ℝ) < criticalProb G o)
    {μ : Measure (G.edgeSet → Bool)} [IsProbabilityMeasure μ]
    {γ : Measure ((G.edgeSet → Bool) × (G.edgeSet → Bool))}
    (hγfst : γ.map Prod.fst = μ)
    (hγsnd : γ.map Prod.snd = percolation G s)
    (horder : ∀ᵐ z ∂γ, z.1 ≤ z.2) :
    ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G :=
  FK.ae_nonPercolating_of_dominated_by_subcritical hG
    (fun x => by rw [← criticalProb_eq_of_connected (o := o) (x := x) hG]; exact hs)
    hγfst hγsnd horder

/-! ## Discharging the decrement baseline of the strict-shift reduction -/

/-- **The decrement strict-shift reduction with its reference baseline
discharged.**  This is `FK.AGDifferentialShift.exists_subcritical_decrement`
specialised to the actual percolation event `Percolating G` of a connected
locally finite graph, with `pc = criticalProb G o` and the zero-mass reference
hypothesis supplied by `mass_percolating_eq_zero`.  The genuinely
Aizenman--Grimmett inputs (the finite-volume Fréchet derivatives, the uniform
trade inequality and the convergence of the finite approximations) remain
hypotheses, as they must. -/
theorem exists_subcritical_decrement_percolating {V : Type*} [Countable V] {G : SimpleGraph V}
    [G.LocallyFinite] (hG : G.Connected) (o : V)
    (hpc0 : 0 < criticalProb G o) (hpc1 : criticalProb G o < 1)
    (An : ℕ → Set (G.edgeSet → Bool)) (S : Set G.edgeSet)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (L : ℕ → ℝ → ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (hderiv : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 →
      HasFDerivAt (FK.AGDifferentialShift.massPair (An n) S) (L n b ε) (b, ε))
    (htrade : ∀ (n : ℕ) (b ε : ℝ), 0 ≤ ε → ε ≤ b → b ≤ 1 → (L n b ε) (c, 1) ≤ 0)
    (hconv : ∀ (b ε : ℝ), Tendsto (fun n => FK.AGDifferentialShift.mass (An n) S b ε) atTop
      (𝓝 (FK.AGDifferentialShift.mass (FK.EssentialWindow.Percolating G) S b ε)))
    (ε : ℝ) (hε0 : 0 < ε) (hεpc : ε < criticalProb G o / 2)
    (hε1 : ε < (1 - criticalProb G o) / 2) :
    ∃ b, criticalProb G o < b ∧ b ≤ 1 ∧ ε ≤ b ∧
      FK.AGDifferentialShift.mass (FK.EssentialWindow.Percolating G) S b ε = 0 :=
  FK.AGDifferentialShift.exists_subcritical_decrement (FK.EssentialWindow.Percolating G) An S
    (criticalProb G o) c hpc0 hpc1 hc0 hc1 L hderiv htrade hconv
    (fun b hb0 hb => mass_percolating_eq_zero (G := G) (o := o) (b := b) hG hb0 hb S)
    ε hε0 hεpc hε1

end FK.PercolationRoot

/-! ## Axiom audit -/

#print axioms FK.PercolationRoot.measurable_forceOpen
#print axioms FK.PercolationRoot.Cluster.measure_infiniteCluster_mul_le
#print axioms FK.PercolationRoot.percolationProb_mul_le
#print axioms FK.PercolationRoot.percolationProb_eq_zero_of_root
#print axioms FK.PercolationRoot.percolationProb_eq_zero_iff_root_pos
#print axioms FK.PercolationRoot.percolationProb_zero
#print axioms FK.PercolationRoot.percolationProb_eq_zero_iff_root
#print axioms FK.PercolationRoot.criticalProb_eq_of_connected
#print axioms FK.PercolationRoot.percolating_eq_hasInfiniteCluster
#print axioms FK.PercolationRoot.percolating_measure_eq_one_iff_percolationProb_pos
#print axioms FK.PercolationRoot.mass_zero_eq_percolation
#print axioms FK.PercolationRoot.mass_zero_mono_base
#print axioms FK.PercolationRoot.ae_nonPercolating_percolation_of_lt_criticalProb_single
#print axioms FK.PercolationRoot.percolation_percolating_eq_zero
#print axioms FK.PercolationRoot.mass_percolating_eq_zero
#print axioms FK.PercolationRoot.incMass_percolating_eq_zero
#print axioms FK.PercolationRoot.ae_nonPercolating_of_dominated_by_subcritical_single
#print axioms FK.PercolationRoot.exists_subcritical_decrement_percolating
