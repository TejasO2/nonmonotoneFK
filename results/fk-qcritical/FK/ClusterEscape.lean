import FK.ClopenEscape
import FK.ConventionTransport

/-!
# The geometric escape events of a growing box exhaustion

`FK.ClopenEscape` reduces the weak-limit DLR theorem to the existence of a
**clopen escape family** with vanishing limit mass.  This file supplies the
percolation content of that family.

The mechanism is the one the source uses: if the stage boundary condition only
acts *far away*, then a stage connection which the fixed finite box does not
already explain forces both open clusters to reach arbitrarily far out; under
at-most-one-cluster this is impossible unless the endpoints were already
connected.  Consequently the escape events have empty intersection and carry no
mass in any law with at most one infinite cluster.

Contents:

* `exists_finset_subset`: an increasing cofinal family of finite vertex sets
  swallows every finite set.
* `infinite_iff_clusterMeetsOutside`: an open cluster is infinite exactly when
  it meets the complement of every member of the exhaustion.
* `escapeSet`, `escape_iInter_eq_empty`, `measure_escape_iInter_eq_zero`: the
  escape events (both clusters meet the outside of the fixed box, and the box's
  own finite connection event fails) have empty intersection, hence vanish
  under any law with at most one infinite cluster.
* `isClopen_of_finiteDependence`: an event determined by finitely many edge
  coordinates is clopen, the tool that turns a *finite* boundary-witness
  formulation of the escape events into clopen sets.
-/

open Filter Set Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionGeometry FK.InfiniteVolume.ConventionTransport

noncomputable section

namespace FK.InfiniteVolume

namespace ClusterEscape

variable {V : Type*} [Countable V]

/-! ## Part 1: finite sets and cofinal exhaustions -/

/-- An increasing cofinal family of finite vertex sets swallows every finite
set. -/
theorem exists_finset_subset {K : ℕ → Finset V} (hmono : Monotone K)
    (hcov : ∀ v : V, ∃ N, v ∈ K N) (F : Finset V) :
    ∃ N, F ⊆ K N := by
  classical
  induction F using Finset.induction with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | insert a s ha ih =>
      obtain ⟨N₁, h₁⟩ := hcov a
      obtain ⟨N₂, h₂⟩ := ih
      refine ⟨max N₁ N₂, ?_⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact hmono (le_max_left _ _) h₁
      · exact hmono (le_max_right _ _) (h₂ hb)

/-! ## Part 2: infinite clusters meet the outside of every box -/

/-- `x`'s open cluster meets the complement of the finite vertex set `K`. -/
def ClusterMeetsOutside (G : SimpleGraph V) (ω : G.edgeSet → Bool) (x : V)
    (K : Finset V) : Prop :=
  ∃ z : V, z ∉ K ∧ OpenConnected G ω Set.univ x z

theorem clusterMeetsOutside_mono {G : SimpleGraph V} {ω : G.edgeSet → Bool} {x : V}
    {K L : Finset V} (hKL : K ⊆ L) (h : ClusterMeetsOutside G ω x L) :
    ClusterMeetsOutside G ω x K := by
  obtain ⟨z, hz, hxz⟩ := h
  exact ⟨z, fun hzK => hz (hKL hzK), hxz⟩

/-- **An open cluster is infinite exactly when it meets the complement of every
member of an increasing cofinal family of finite vertex sets.** -/
theorem infinite_iff_clusterMeetsOutside (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    {K : ℕ → Finset V} (hmono : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N) (x : V) :
    {z : V | OpenConnected G ω Set.univ x z}.Infinite ↔
      ∀ N, ClusterMeetsOutside G ω x (K N) := by
  classical
  constructor
  · intro hinf N
    by_contra hcon
    have hsub : {z : V | OpenConnected G ω Set.univ x z} ⊆ ↑(K N) := by
      intro z hz
      by_contra hzK
      exact hcon ⟨z, hzK, hz⟩
    exact hinf ((K N).finite_toSet.subset hsub)
  · intro h
    intro hfin
    obtain ⟨F, hF⟩ : ∃ F : Finset V,
        ∀ z : V, OpenConnected G ω Set.univ x z → z ∈ F :=
      ⟨hfin.toFinset, fun z hz => by simpa using hz⟩
    obtain ⟨N, hN⟩ := exists_finset_subset hmono hcov F
    obtain ⟨z, hzK, hxz⟩ := h N
    exact hzK (hN (hF z hxz))

/-! ## Part 3: the escape events and their empty intersection -/

/-- The escape event at scale `m`: both open clusters meet the outside of the
fixed finite vertex set `K m`, while the finite event `C m` (the connection the
box itself explains) fails. -/
def escapeSet (G : SimpleGraph V) (K : ℕ → Finset V)
    (C : ℕ → Set (G.edgeSet → Bool)) (x y : V) (m : ℕ) : Set (G.edgeSet → Bool) :=
  {ω | ClusterMeetsOutside G ω x (K m) ∧ ClusterMeetsOutside G ω y (K m) ∧ ω ∉ C m}

theorem escapeSet_anti {G : SimpleGraph V} {K : ℕ → Finset V} (hmono : Monotone K)
    {C : ℕ → Set (G.edgeSet → Bool)} {x y : V} (hCmono : Monotone C) :
    Antitone (escapeSet G K C x y) := by
  intro m n hmn ω hω
  obtain ⟨hx, hy, hCm⟩ := hω
  refine ⟨clusterMeetsOutside_mono (L := K n) (fun u hu => hmono hmn hu) hx,
    clusterMeetsOutside_mono (L := K n) (fun u hu => hmono hmn hu) hy, ?_⟩
  exact fun hCn => hCm (hCmono hmn hCn)

/-- **The escape events have empty intersection under at-most-one-cluster.**

If the finite events `C m` exhaust the actual connection event of `x` and `y`,
and `ω` has at most one infinite open cluster, then `ω` cannot be in every
escape event: being in all of them makes both clusters infinite, hence (at most
one cluster) connected, hence in some `C m`, contradicting the failure of every
`C m`. -/
theorem escape_iInter_eq_empty (G : SimpleGraph V) {ω : G.edgeSet → Bool}
    {K : ℕ → Finset V} (hmono : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N)
    {C : ℕ → Set (G.edgeSet → Bool)} {x y : V}
    (hUnion : ∀ ω : G.edgeSet → Bool,
      (∃ m, ω ∈ C m) ↔ OpenConnected G ω Set.univ x y)
    (hglobal : GlobalAtMostOne G ω) :
    ω ∉ ⋂ m, escapeSet G K C x y m := by
  classical
  intro hω
  have hm : ∀ m, ClusterMeetsOutside G ω x (K m) ∧ ClusterMeetsOutside G ω y (K m)
      ∧ ω ∉ C m := fun m => Set.mem_iInter.mp hω m
  have hx : ∀ N, ClusterMeetsOutside G ω x (K N) := fun N => (hm N).1
  have hy : ∀ N, ClusterMeetsOutside G ω y (K N) := fun N => (hm N).2.1
  have hnoC : ∀ m, ω ∉ C m := fun m => (hm m).2.2
  have hxinf : {z : V | OpenConnected G ω Set.univ x z}.Infinite :=
    (infinite_iff_clusterMeetsOutside G ω hmono hcov x).mpr hx
  have hyinf : {z : V | OpenConnected G ω Set.univ y z}.Infinite :=
    (infinite_iff_clusterMeetsOutside G ω hmono hcov y).mpr hy
  have hconn : OpenConnected G ω Set.univ x y := hglobal x y hxinf hyinf
  obtain ⟨m, hm'⟩ := (hUnion ω).mpr hconn
  exact hnoC m hm'

/-- **The escape events are null under any law with at most one infinite
cluster.** -/
theorem measure_escape_iInter_eq_zero (G : SimpleGraph V) (μ : Measure (G.edgeSet → Bool))
    {K : ℕ → Finset V} (hmono : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N)
    {C : ℕ → Set (G.edgeSet → Bool)} {x y : V}
    (hUnion : ∀ ω : G.edgeSet → Bool,
      (∃ m, ω ∈ C m) ↔ OpenConnected G ω Set.univ x y)
    (hae : ∀ᵐ ω ∂μ, GlobalAtMostOne G ω) :
    μ (⋂ m, escapeSet G K C x y m) = 0 := by
  classical
  have hempty : (⋂ m, escapeSet G K C x y m) ⊆ {ω : G.edgeSet → Bool | ¬ GlobalAtMostOne G ω} :=
    fun ω hω hglob => escape_iInter_eq_empty G hmono hcov hUnion hglob hω
  have hmeas : MeasurableSet {ω : G.edgeSet → Bool | ¬ GlobalAtMostOne G ω} :=
    (measurableSet_globalAtMostOne G).compl
  refine measure_mono_null hempty ?_
  exact MeasureTheory.ae_iff.mp hae

/-! ## Part 4: wiring outside the box only creates connections that leave it -/

/-- The edges of the ambient graph whose two endpoints both lie in `K`. -/
def innerEdges (K : Finset V) : Set (Sym2 V) :=
  {e : Sym2 V | ∃ u ∈ K, ∃ v ∈ K, e = s(u, v)}

theorem mem_innerEdges_iff {K : Finset V} {u v : V} :
    s(u, v) ∈ innerEdges K ↔ u ∈ K ∧ v ∈ K := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  · rintro ⟨hu, hv⟩
    exact ⟨u, hu, v, hv, rfl⟩

/-- The graph of a configuration together with an extra wiring relation, the
combinatorial form of an FK boundary partition imposed from outside. -/
def wiredGraph (G : SimpleGraph V) (γ : Setoid V) (ω : G.edgeSet → Bool) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (γ.r u v ∨ ∃ e : G.edgeSet, ω e = true ∧ e.1 = s(u, v))
  symm := ⟨by
    rintro u v ⟨hne, hcase⟩
    refine ⟨hne.symm, ?_⟩
    rcases hcase with hr | ⟨e, he, heq⟩
    · exact Or.inl (γ.symm hr)
    · exact Or.inr ⟨e, he, by rw [heq, Sym2.eq_swap]⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- An open edge of the ambient graph, read in the wired graph. -/
theorem openConnected_wiredGraph_of_adj {G : SimpleGraph V} {γ : Setoid V}
    {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {u v : V}
    (hadj : G.Adj u v) (hA : s(u, v) ∈ A)
    (hopen : ω ⟨s(u, v), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ = true) :
    OpenConnected G ω A u v :=
  OpenConnected.of_adj hadj hA hopen

/-- **A wired walk that stays inside `K` carries no wiring step**, hence is an
open connection inside `K`.  This is where the hypothesis that the wiring only
relates vertices outside `K` is used. -/
theorem openConnected_of_walk_support_subset (G : SimpleGraph V) {γ : Setoid V}
    {ω : G.edgeSet → Bool} {K : Finset V}
    (hγ : ∀ u v, γ.r u v → u ∉ K ∧ v ∉ K) :
    ∀ {u v : V} (p : (wiredGraph G γ ω).Walk u v),
      (∀ w ∈ p.support, w ∈ K) → u ∈ K → OpenConnected G ω (innerEdges K) u v := by
  intro u v p
  induction p with
  | nil => intro _ _; exact OpenConnected.refl ω (innerEdges K) _
  | @cons a b c h p ih =>
      intro hsupp ha
      have hbK : b ∈ K := hsupp b (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem a p.start_mem_support)
      have hstep : OpenConnected G ω (innerEdges K) a b := by
        obtain ⟨hne, hcase⟩ := h
        rcases hcase with hr | ⟨e, he, heq⟩
        · exact absurd ha (hγ a b hr).1
        · have hadj : G.Adj a b := by
            rw [← SimpleGraph.mem_edgeSet, ← heq]
            exact e.2
          have hsub : (⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet) = e := by
            apply Subtype.ext
            exact heq.symm
          have hopen : ω ⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ = true := by
            rw [hsub]
            exact he
          exact OpenConnected.of_adj hadj (mem_innerEdges_iff.mpr ⟨ha, hbK⟩) hopen
      exact hstep.trans (ih (fun w hw => hsupp w (by
        rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem a hw)) hbK)

/-- **A wired walk leaving `K` produces an open connection from its start to a
vertex outside `K`.** -/
theorem exists_outside_of_walk (G : SimpleGraph V) {γ : Setoid V}
    {ω : G.edgeSet → Bool} {K : Finset V}
    (hγ : ∀ u v, γ.r u v → u ∉ K ∧ v ∉ K) :
    ∀ {u v : V} (p : (wiredGraph G γ ω).Walk u v), u ∈ K →
      (∃ w ∈ p.support, w ∉ K) → ∃ w : V, w ∉ K ∧ OpenConnected G ω Set.univ u w := by
  intro u v p
  induction p with
  | nil =>
      intro _ hex
      obtain ⟨w, hw, hwK⟩ := hex
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      subst hw
      exact absurd ‹_ ∈ K› hwK
  | @cons a b c h p ih =>
      intro ha hex
      rw [SimpleGraph.Walk.support_cons] at hex
      obtain ⟨w, hw, hwK⟩ := hex
      have hstep : OpenConnected G ω Set.univ a b := by
        obtain ⟨hne, hcase⟩ := h
        rcases hcase with hr | ⟨e, he, heq⟩
        · exact absurd ha (hγ a b hr).1
        · have hadj : G.Adj a b := by
            rw [← SimpleGraph.mem_edgeSet, ← heq]
            exact e.2
          have hsub : (⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ : G.edgeSet) = e := by
            apply Subtype.ext
            exact heq.symm
          have hopen : ω ⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩ = true := by
            rw [hsub]
            exact he
          exact OpenConnected.of_adj hadj (Set.mem_univ _) hopen
      rcases List.mem_cons.mp hw with rfl | hwp
      · exact absurd ha hwK
      · by_cases hbK : b ∈ K
        · obtain ⟨w, hwK, hbw⟩ := ih hbK ⟨w, hwp, hwK⟩
          exact ⟨w, hwK, hstep.trans hbw⟩
        · exact ⟨b, hbK, hstep⟩

/-- **Wiring supported outside `K` can only create connections that leave `K`.**

If two vertices of `K` are connected in the configuration plus a boundary
wiring relation which only touches vertices outside `K`, and they are not
connected inside `K` by open edges alone, then *both* open clusters meet the
complement of `K`.  This is the exact combinatorial content of the escape
hypothesis of `ClopenEscape.isDLR_of_clopen_escape`: a stage connection which
the fixed region does not explain forces both clusters to run off to infinity,
which at most one infinite cluster then forbids. -/
theorem escape_pair_of_wiredConn (G : SimpleGraph V) {γ : Setoid V}
    {ω : G.edgeSet → Bool} {K : Finset V}
    (hγ : ∀ u v, γ.r u v → u ∉ K ∧ v ∉ K) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (hconn : (wiredGraph G γ ω).Reachable x y)
    (hnotin : ¬ OpenConnected G ω (innerEdges K) x y) :
    ClusterMeetsOutside G ω x K ∧ ClusterMeetsOutside G ω y K := by
  obtain ⟨p⟩ := hconn
  have hex : ∃ w ∈ p.support, w ∉ K := by
    by_contra hcon
    refine hnotin (openConnected_of_walk_support_subset G hγ p (fun w hw => ?_) hx)
    by_contra hwK
    exact hcon ⟨w, hw, hwK⟩
  constructor
  · exact exists_outside_of_walk G hγ p hx hex
  · obtain ⟨w, hw, hwK⟩ := hex
    refine exists_outside_of_walk G hγ p.reverse hy ⟨w, ?_, hwK⟩
    rw [SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hw

/-! ## Part 5: escaping-cluster tails vanish under nonpercolation -/

/-- The escape events of `Part 3` are increasing in the configuration, so they
can be bounded by any stochastically dominating law. -/
theorem isUpperSet_clusterMeetsOutside (G : SimpleGraph V) (K : Finset V) (x : V) :
    IsUpperSet {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x K} := by
  intro ω η hωη hω
  obtain ⟨z, hz, hxz⟩ := hω
  exact ⟨z, hz, OpenConnected.mono_config hxz hωη⟩

theorem measurableSet_clusterMeetsOutside (G : SimpleGraph V) [Countable V]
    (K : Finset V) (x : V) :
    MeasurableSet {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x K} := by
  have h : {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x K}
      = ⋃ z : V, {ω : G.edgeSet → Bool | z ∉ K ∧ OpenConnected G ω Set.univ x z} := by
    ext ω
    simp only [ClusterMeetsOutside, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h]
  refine MeasurableSet.iUnion fun z => ?_
  by_cases hz : z ∈ K
  · simpa [hz] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set (G.edgeSet → Bool)))
  · simpa [hz] using measurableSet_openConnected (G := G) Set.univ x z

/-- **The intersection of the escaping-cluster events is the event that the
cluster is infinite.** -/
theorem iInter_clusterMeetsOutside_eq (G : SimpleGraph V) {K : ℕ → Finset V}
    (hmono : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N) (x : V) :
    (⋂ m, {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x (K m)})
      = {ω : G.edgeSet → Bool | {z : V | OpenConnected G ω Set.univ x z}.Infinite} := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  exact (infinite_iff_clusterMeetsOutside G ω hmono hcov x).symm

theorem antitone_clusterMeetsOutside (G : SimpleGraph V) {K : ℕ → Finset V}
    (hmono : Monotone K) (x : V) :
    Antitone fun m => {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x (K m)} := by
  intro m n hmn ω hω
  exact clusterMeetsOutside_mono (L := K n) (fun u hu => hmono hmn hu) hω

/-- **Nonpercolation at `x` kills the escaping-cluster mass at all scales.** -/
theorem measure_iInter_clusterMeetsOutside_eq_zero (G : SimpleGraph V)
    (ν : Measure (G.edgeSet → Bool)) {K : ℕ → Finset V}
    (hmono : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N) (x : V)
    (hnoPerc : ν {ω : G.edgeSet → Bool |
      {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    ν (⋂ m, {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x (K m)}) = 0 := by
  rw [iInter_clusterMeetsOutside_eq G hmono hcov x]
  exact hnoPerc

/-- **The escaping-cluster tails vanish for a nonpercolating law.**  This is the
`hν` input of `ClopenEscape.isDLR_of_dominated_escape_of_null_escape` in its
concrete geometric form: the escape events are the increasing events "the open
cluster of `x` meets the complement of the `m`-th finite box", whose masses
decrease to the percolation probability. -/
theorem tendsto_measure_clusterMeetsOutside (G : SimpleGraph V) [Countable V]
    (ν : Measure (G.edgeSet → Bool)) [IsFiniteMeasure ν] {K : ℕ → Finset V}
    (hmono : Monotone K) (hcov : ∀ v : V, ∃ N, v ∈ K N) (x : V)
    (hnoPerc : ν {ω : G.edgeSet → Bool |
      {z : V | OpenConnected G ω Set.univ x z}.Infinite} = 0) :
    Tendsto (fun m => (ν {ω : G.edgeSet → Bool | ClusterMeetsOutside G ω x (K m)}).toReal)
      atTop (𝓝 0) :=
  ClopenEscape.tendsto_measure_toReal_escape_of_measurable ν
    (fun m => measurableSet_clusterMeetsOutside G (K m) x)
    (antitone_clusterMeetsOutside G hmono x)
    (measure_iInter_clusterMeetsOutside_eq_zero G ν hmono hcov x hnoPerc)

end ClusterEscape

end FK.InfiniteVolume
