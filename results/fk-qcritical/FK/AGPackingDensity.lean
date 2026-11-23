import FK.InfinitePackedSleeves
import FK.BernoulliDuality
import FK.PhasesCoordinate
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Positive density of bounded-range device packings and exponential activation tails

Two independent but composable contributions.

## 1. Covering counts and positive density

`card_ball_le_mul_card_devices` is the elementary counting step behind the
phrase "the packed sleeves have positive density".  If the devices indexed by a
finite set `J` have distinguished pivots `p i` that `K`-cover an edge metric, and
each radius-`K` ball around a pivot has at most `D` edges, then the radius-`n`
ball has at most `D * |J|` edges:

  `|ball f n| ≤ D * |J|`.

No disjointness of the templates enters this inequality: it is a pure covering
count.  Injectivity of the pivot map is what turns it into a count of *distinct
devices*; on the actual uniform sleeve packing it is supplied by pairwise
disjointness of the whole templates (`pivot_injOn_of_uniform_packing`).

`linear_growth_le_mul_card_devices` adds the growth input: if every radius-`n`
ball has at least `n + 1` edges (the line graph of any infinite connected
locally finite graph has this, since an infinite ray contributes one new edge
per step), then at least `(n + 1)/D` devices are needed to `K`-cover it.  So
bounded-distance density plus a uniform radius-`K` ball bound is genuine
positive density, with the explicit constant `1/D`.  The companion
`card_le_card_ball` gives the matching upper bound: pairwise-disjoint devices
have pairwise-distinct pivots, so a ball of radius `n` contains at most
`|ball f n|` devices.  Density is therefore sandwiched between `1/D` and `1`.

## 2. Exact activation-cylinder probabilities and the exponential tail

For the actual independent activation law `bernoulliProduct r` the all-inactive
cylinder on a finite device set `J` has the exact probability
`∏_{i∈J} (1 - r i)`, and if every activation rate is at least `s` this is at
most `(1 - s)^{|J|}`.  Composing the two parts: if the device sets `J n` of the
radius-`n` balls satisfy the density inequality `n + 1 ≤ D * |J n|`, then for
every `ε > 0` some ball has all-inactive probability below `ε`.  This is the
fixed-radius tail statement that positive density buys; it is a statement about
the actual infinite product law, not about a finite-volume surrogate.

No critical parameter, no `hAG`, and no derivative/limit interchange is used or
claimed here.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace FK.AGPackingDensity

/-! ## 1. Covering counts -/

/-- An edge metric with explicit finite balls.  This is the data supplied by the
line graph of a locally finite graph: `dist` is the line-graph distance and
`ball f n` the finite set of edges at distance at most `n` from `f`. -/
structure EdgeMetric (E : Type*) where
  /-- Edge distance. -/
  dist : E → E → ℕ
  /-- Finite metric ball. -/
  ball : E → ℕ → Finset E
  /-- The ball is exactly the distance sublevel set. -/
  mem_ball : ∀ f n g, g ∈ ball f n ↔ dist f g ≤ n
  /-- Edge distance is symmetric. -/
  dist_comm : ∀ a b, dist a b = dist b a
  /-- Edge distance satisfies the triangle inequality. -/
  dist_triangle : ∀ a b c, dist a c ≤ dist a b + dist b c

/-- **Covering count.**  If the pivots of the devices indexed by `J` `K`-cover
the whole edge set, and every radius-`K` ball around a pivot has at most `D`
edges, then the radius-`n` ball at `f` has at most `D * |J|` edges. -/
theorem card_ball_le_mul_card_devices {E ι : Type*} (M : EdgeMetric E)
    (J : Finset ι) {p : ι → E} {K D : ℕ}
    (hcover : ∀ g, ∃ i ∈ J, M.dist (p i) g ≤ K)
    (hD : ∀ i, (M.ball (p i) K).card ≤ D)
    (f : E) (n : ℕ) :
    (M.ball f n).card ≤ D * J.card := by
  classical
  have hsub : M.ball f n ⊆ (J.image p).biUnion (fun g => M.ball g K) := by
    intro x hx
    obtain ⟨i, hiJ, hpx⟩ := hcover x
    exact Finset.mem_biUnion.mpr ⟨p i, Finset.mem_image.2 ⟨i, hiJ, rfl⟩,
      (M.mem_ball (p i) K x).2 hpx⟩
  have hstep : (M.ball f n).card ≤ ∑ g ∈ J.image p, (M.ball g K).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hbound : ∑ g ∈ J.image p, (M.ball g K).card ≤ ∑ _g ∈ J.image p, D := by
    refine Finset.sum_le_sum fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
    exact hD i
  calc (M.ball f n).card ≤ ∑ g ∈ J.image p, (M.ball g K).card := hstep
    _ ≤ ∑ _g ∈ J.image p, D := hbound
    _ = (J.image p).card * D := by simp [Finset.sum_const]
    _ ≤ J.card * D := Nat.mul_le_mul_right D Finset.card_image_le
    _ = D * J.card := Nat.mul_comm _ _

/-- **Positive density.**  Add the linear growth input `n + 1 ≤ |ball f n|`: any
finite device set whose pivots `K`-cover the edge set has cardinality at least
`(n + 1)/D`, in the precise sense that `n + 1 ≤ D * |J|`. -/
theorem linear_growth_le_mul_card_devices {E ι : Type*} (M : EdgeMetric E)
    (J : Finset ι) {p : ι → E} {K D : ℕ}
    (hcover : ∀ g, ∃ i ∈ J, M.dist (p i) g ≤ K)
    (hD : ∀ i, (M.ball (p i) K).card ≤ D)
    (f : E) (n : ℕ) (hlin : n + 1 ≤ (M.ball f n).card) :
    n + 1 ≤ D * J.card :=
  hlin.trans (card_ball_le_mul_card_devices M J hcover hD f n)

/-- **Density upper bound.**  Pairwise-disjoint devices have pairwise-distinct
pivots, so a set of devices whose pivots all lie in the radius-`n` ball is no
larger than the ball.  Combined with the covering count, the number of packed
devices in a ball is sandwiched between `(n + 1)/D` and `|ball f n|`. -/
theorem card_le_card_ball {E ι : Type*} (M : EdgeMetric E)
    (J : Finset ι) {p : ι → E} (hinj : Function.Injective p) (f : E) (n : ℕ)
    (hJ : ∀ i ∈ J, M.dist f (p i) ≤ n) :
    J.card ≤ (M.ball f n).card := by
  classical
  rw [← Finset.card_image_of_injective J hinj]
  refine Finset.card_le_card fun g hg => ?_
  obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.1 hg
  exact (M.mem_ball f n (p i)).2 (hJ i hiJ)

/-- **Device density for an infinite device family.**  This is the form that
applies to the actual sleeve packing `M : Set (H ≃g H)`, whose index type is
infinite.  If every edge is within line-graph distance `K` of some pivot, pivots
are injective (pairwise-disjoint templates), and radius-`K` balls have at most
`D` edges, then the *number of devices whose pivot lies in the radius
`n + K` ball* is at least `(n + 1)/D`, in the precise sense

  `n + 1 ≤ D * #{devices meeting the radius n + K ball}`.

Here the device count is a `Set.ncard`, so no finiteness or countability of the
device index is assumed; finiteness of the counted device set follows from
injectivity of the pivot map into the finite ball. -/
theorem density_ncard {E ι : Type*} (M : EdgeMetric E) {p : ι → E}
    (hinj : Function.Injective p) {K D : ℕ}
    (hcover : ∀ g, ∃ i, M.dist (p i) g ≤ K)
    (hD : ∀ i, (M.ball (p i) K).card ≤ D)
    (f : E) (n : ℕ) (hlin : n + 1 ≤ (M.ball f n).card) :
    n + 1 ≤ D * (Set.ncard {i : ι | M.dist f (p i) ≤ n + K}) := by
  classical
  set S : Set ι := {i : ι | M.dist f (p i) ≤ n + K} with hS
  have hSmem : ∀ i, i ∈ S ↔ M.dist f (p i) ≤ n + K := fun i => Iff.rfl
  have hfin : S.Finite := by
    have himg : p '' S ⊆ (M.ball f (n + K) : Set E) := by
      rintro g ⟨i, hi, rfl⟩
      exact (M.mem_ball f (n + K) (p i)).2 ((hSmem i).1 hi)
    exact Set.Finite.of_finite_image ((M.ball f (n + K)).finite_toSet.subset himg)
      (hinj.injOn)
  have hsub : M.ball f n ⊆ (hfin.toFinset.image p).biUnion (fun g => M.ball g K) := by
    intro x hx
    have hxf : M.dist f x ≤ n := (M.mem_ball f n x).1 hx
    obtain ⟨i, hi⟩ := hcover x
    have hiS : i ∈ S := by
      show M.dist f (p i) ≤ n + K
      calc M.dist f (p i) ≤ M.dist f x + M.dist x (p i) := M.dist_triangle ..
        _ = M.dist f x + M.dist (p i) x := by rw [M.dist_comm x (p i)]
        _ ≤ n + K := Nat.add_le_add hxf hi
    exact Finset.mem_biUnion.2 ⟨p i,
      Finset.mem_image.2 ⟨i, hfin.mem_toFinset.2 hiS, rfl⟩,
      (M.mem_ball (p i) K x).2 hi⟩
  have hstep : (M.ball f n).card ≤ ∑ g ∈ hfin.toFinset.image p, (M.ball g K).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hbound : ∑ g ∈ hfin.toFinset.image p, (M.ball g K).card ≤
      ∑ _g ∈ hfin.toFinset.image p, D := by
    refine Finset.sum_le_sum fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hg
    exact hD i
  have hcast : (hfin.toFinset.image p).card ≤ S.ncard := by
    rw [Finset.card_image_of_injective _ hinj, Set.ncard_eq_toFinset_card S hfin]
  calc n + 1 ≤ (M.ball f n).card := hlin
    _ ≤ ∑ g ∈ hfin.toFinset.image p, (M.ball g K).card := hstep
    _ ≤ ∑ _g ∈ hfin.toFinset.image p, D := hbound
    _ = (hfin.toFinset.image p).card * D := by simp [Finset.sum_const]
    _ ≤ S.ncard * D := Nat.mul_le_mul_right D hcast
    _ = D * S.ncard := Nat.mul_comm _ _

/-- **No finite device set can `K`-cover a ball with linear growth.**  If every
radius-`n` ball has at least `n + 1` edges and every radius-`K` ball around a
pivot has at most `D` edges with `D > 0`, then no finite device set `J` covers
the whole edge metric at scale `K`.  This is the qualitative form of the density
theorem: bounded-range coverage of a graph with linear edge growth needs
infinitely many devices. -/
theorem exists_far_edge {E ι : Type*} (M : EdgeMetric E) (J : Finset ι)
    {p : ι → E} {K D : ℕ} (hD : ∀ i, (M.ball (p i) K).card ≤ D)
    (f : E) (hlin : ∀ n : ℕ, n + 1 ≤ (M.ball f n).card) :
    ∃ g : E, ∀ i ∈ J, K < M.dist (p i) g := by
  by_contra h
  push Not at h
  have hcover : ∀ g, ∃ i ∈ J, M.dist (p i) g ≤ K := fun g => h g
  have hbound := linear_growth_le_mul_card_devices M J hcover hD f (D * J.card)
    (hlin (D * J.card))
  have : D * J.card + 1 ≤ D * J.card := hbound
  omega

/-- **Density forces unbounded device counts.**  If the device sets of the balls
satisfy `n + 1 ≤ D * |J n|` with `D > 0`, then for every `N` some ball meets at
least `N` devices.  (Take the ball of radius `D * N`.) -/
theorem exists_card_ge {ι : Type*} {J : ℕ → Finset ι} {D : ℕ} (hD : 0 < D)
    (hdens : ∀ n, n + 1 ≤ D * (J n).card) (N : ℕ) : ∃ n, N ≤ (J n).card := by
  refine ⟨D * N, ?_⟩
  have h := hdens (D * N)
  have hle : D * N ≤ D * (J (D * N)).card := by omega
  exact Nat.le_of_mul_le_mul_left hle hD

/-! ## 2. Exact activation-cylinder probabilities -/

/-- The cylinder in which every coordinate of `J` is inactive. -/
def allClosed {E : Type*} (J : Finset E) : Set (E → Bool) :=
  {ω | ∀ e ∈ J, ω e = false}

lemma allClosed_eq_pi {E : Type*} (J : Finset E) :
    allClosed J = Set.pi (J : Set E) (fun _ => ({false} : Set Bool)) := rfl

lemma measurableSet_allClosed {E : Type*} (J : Finset E) : MeasurableSet (allClosed J) := by
  rw [allClosed_eq_pi]
  exact MeasurableSet.pi J.finite_toSet.countable (fun _ _ => measurableSet_singleton false)

/-- **Exact all-inactive cylinder probability** for the actual infinite product
Bernoulli law. -/
theorem bernoulliProduct_allClosed {E : Type*} (r : E → unitInterval) (J : Finset E) :
    FK.Configuration.bernoulliProduct r (allClosed J) =
      ∏ e ∈ J, ENNReal.ofReal (1 - (r e : ℝ)) := by
  rw [allClosed_eq_pi,
    FK.Configuration.bernoulliProduct_pi r J (fun _ => ({false} : Set Bool))
      (fun _ _ => measurableSet_singleton false)]
  exact Finset.prod_congr rfl fun e _ =>
    CurvatureVariance.Infra.Percolation.bernoulliMeasure_false (r e)

/-- **Exponential activation tail.**  If every activation rate of the finite
device set `J` is at least `s`, the probability that no device of `J` fires is at
most `(1 - s)^{|J|}`. -/
theorem bernoulliProduct_allClosed_toReal_le {E : Type*} (r : E → unitInterval)
    (J : Finset E) (s : unitInterval) (hs : ∀ e ∈ J, s ≤ r e) :
    (FK.Configuration.bernoulliProduct r (allClosed J)).toReal ≤
      (1 - (s : ℝ)) ^ J.card := by
  rw [bernoulliProduct_allClosed, ENNReal.toReal_prod]
  have hterm : ∀ e ∈ J, (ENNReal.ofReal (1 - (r e : ℝ))).toReal = 1 - (r e : ℝ) := by
    intro e _
    rw [ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr (r e).2.2
  have hprod : ∏ e ∈ J, (ENNReal.ofReal (1 - (r e : ℝ))).toReal =
      ∏ e ∈ J, (1 - (r e : ℝ)) := Finset.prod_congr rfl hterm
  rw [hprod]
  have hle : ∏ e ∈ J, (1 - (r e : ℝ)) ≤ ∏ _e ∈ J, (1 - (s : ℝ)) := by
    refine Finset.prod_le_prod₀ (fun e _ => ?_) (fun e he => ?_)
    · exact sub_nonneg.mpr (r e).2.2
    · have h : (s : ℝ) ≤ (r e : ℝ) := hs e he
      linarith
  calc ∏ e ∈ J, (1 - (r e : ℝ)) ≤ ∏ _e ∈ J, (1 - (s : ℝ)) := hle
    _ = (1 - (s : ℝ)) ^ J.card := by simp

/-- **Fixed-radius tail vanishing.**  If the ball device counts are dense in the
sense `n + 1 ≤ D * |J n|` with `D > 0`, then for every positive activation rate
`s > 0` and every `ε > 0` some ball has all-inactive probability below `ε`.
The bound is the explicit `(1 - s)^{|J n|}`; no limit of the probability itself
is formed by exchanging anything. -/
theorem exists_allClosed_le {ι : Type*} {J : ℕ → Finset ι} {D : ℕ} (hD : 0 < D)
    (hdens : ∀ n, n + 1 ≤ D * (J n).card) {s : unitInterval}
    (hs : 0 < (s : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, (1 - (s : ℝ)) ^ (J n).card < ε := by
  have hbase_lt : 1 - (s : ℝ) < 1 := by
    have := s.2.1
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hbase_lt
  obtain ⟨n, hn⟩ := exists_card_ge (J := J) hD hdens N
  refine ⟨n, lt_of_le_of_lt ?_ hN⟩
  have hbase_nonneg : 0 ≤ 1 - (s : ℝ) := by
    have := s.2.2
    linarith
  exact pow_le_pow_of_le_one hbase_nonneg (le_of_lt hbase_lt) hn

/-! ## 3. Finite distance balls in connected locally finite graphs

This section records the standard finiteness fact behind the `EdgeMetric`
interface: in a connected locally finite graph every distance ball is finite.
It is stated for the vertex metric of a `SimpleGraph`.  Applied to the line
graph of `graph H` it is exactly the input needed to build `EdgeMetric` on the
edge set of a sleeve graph; the one further brick there is local finiteness of
the line graph, which is not proved here. -/

section Balls

open SimpleGraph

variable {V : Type*}

/-- **Distance balls of a connected locally finite graph are finite.**  The
induction step uses an exact prefix walk: if `dist v w = n + 1`, then the vertex
`p.getVert n` of a shortest walk is at distance at most `n` from `v` and is
adjacent to `w`. -/
theorem finite_dist_ball (G : SimpleGraph V) [G.LocallyFinite] (hG : G.Connected)
    (v : V) (n : ℕ) : {w : V | G.dist v w ≤ n}.Finite := by
  induction n with
  | zero =>
      have hsub : {w : V | G.dist v w ≤ 0} ⊆ {v} := by
        intro w hw
        have h0 : G.dist v w = 0 := Nat.le_zero.1 hw
        have h0' : G.dist w v = 0 := by rw [SimpleGraph.dist_comm]; exact h0
        exact Set.mem_singleton_iff.2 ((hG.dist_eq_zero_iff).1 h0')
      exact Set.Finite.subset (Set.finite_singleton v) hsub
  | succ n ih =>
      have hsub : {w : V | G.dist v w ≤ n + 1} ⊆
          {w | G.dist v w ≤ n} ∪ ⋃ u ∈ {w | G.dist v w ≤ n}, G.neighborSet u := by
        intro w hw
        have hw' : G.dist v w ≤ n + 1 := hw
        by_cases hle : G.dist v w ≤ n
        · exact Or.inl hle
        · have hlt : n < G.dist v w := Nat.lt_of_not_le hle
          have hpos : G.dist v w = n + 1 := by omega
          obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v w
          rw [hpos] at hp
          refine Or.inr (Set.mem_iUnion.2 ⟨p.getVert n, ?_⟩)
          refine Set.mem_iUnion.2 ⟨?_, ?_⟩
          · have hlen : (p.take n).length = n := by
              rw [Walk.take_length, hp, Nat.min_eq_left (by omega)]
            have := G.dist_le (p.take n)
            rwa [hlen] at this
          · have hi : n < p.length := by omega
            have hadj := p.adj_getVert_succ hi
            have hlast : p.getVert (n + 1) = w := by
              rw [← hp]
              exact p.getVert_length
            rwa [hlast] at hadj
      refine Set.Finite.subset ?_ hsub
      refine ih.union (Set.Finite.biUnion ih ?_)
      intro u _
      exact Set.toFinite _

/-- The edges through a fixed vertex form a finite set in a locally finite
graph. -/
lemma finite_edges_through (G : SimpleGraph V) [G.LocallyFinite] (x : V) :
    {f : G.edgeSet | x ∈ (f : Sym2 V)}.Finite := by
  classical
  haveI : Fintype (G.neighborSet x) := ‹G.LocallyFinite› x
  haveI : Fintype (G.incidenceSet x) := SimpleGraph.incidenceSetFintype G x
  have hpre : {f : G.edgeSet | x ∈ (f : Sym2 V)} =
      Subtype.val ⁻¹' G.incidenceSet x := by
    ext f
    simp [SimpleGraph.incidenceSet]
  rw [hpre]
  exact Set.Finite.preimage (fun a _ b _ h => Subtype.ext h) (Set.toFinite _)

/-- **The line graph of a locally finite graph is locally finite.**  The edges
adjacent to `e` all lie in the incidence sets of the two canonical endpoints of
`e`. -/
noncomputable def lineGraph_locallyFinite (G : SimpleGraph V) [G.LocallyFinite] :
    G.lineGraph.LocallyFinite := by
  classical
  intro e
  have hsub : G.lineGraph.neighborSet e ⊆
      ({f : G.edgeSet | (e.1).out.1 ∈ (f : Sym2 V)} ∪
        {f : G.edgeSet | (e.1).out.2 ∈ (f : Sym2 V)}) := by
    intro f hf
    simp only [SimpleGraph.mem_neighborSet] at hf
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hf
    obtain ⟨-, x, hx1, hx2⟩ := hf
    have hx : x = (e.1).out.1 ∨ x = (e.1).out.2 := by
      have h : x ∈ (e.1 : Sym2 V) := hx1
      rw [← Quot.out_eq (e.1), Sym2.mem_iff] at h
      exact h
    rcases hx with h | h
    · exact Or.inl (h ▸ hx2)
    · exact Or.inr (h ▸ hx2)
  have hfin : ({f : G.edgeSet | (e.1).out.1 ∈ (f : Sym2 V)} ∪
      {f : G.edgeSet | (e.1).out.2 ∈ (f : Sym2 V)}).Finite :=
    (finite_edges_through G _).union (finite_edges_through G _)
  exact Set.Finite.fintype (hfin.subset hsub)

section Metric

/-- **The line-graph edge metric** of a connected locally finite graph: distance
is line-graph distance and balls are the finite distance balls proved above. -/
noncomputable def lineMetric {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [G.LocallyFinite] (hG : G.Connected) [Nonempty G.edgeSet] : EdgeMetric G.edgeSet where
  dist := G.lineGraph.dist
  ball f n := by
    haveI : G.lineGraph.LocallyFinite := lineGraph_locallyFinite G
    exact (finite_dist_ball G.lineGraph (FK.QuasiTransitive.lineGraph_connected G hG) f n).toFinset
  mem_ball := by
    intro f n g
    haveI : G.lineGraph.LocallyFinite := lineGraph_locallyFinite G
    exact Set.Finite.mem_toFinset _
  dist_comm := fun a b => SimpleGraph.dist_comm (G := G.lineGraph)
  dist_triangle := fun a b c =>
    (FK.QuasiTransitive.lineGraph_connected G hG).dist_triangle

end Metric

end Balls

end FK.AGPackingDensity
