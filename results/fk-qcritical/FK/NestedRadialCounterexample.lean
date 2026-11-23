import FK.NestedMetricRegionSplit
import FK.AGInfiniteLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The radial whole-ball error does not vanish under nonpercolation

On the semi-infinite path graph, the radial error based at `innerBall 0 (R+1)`
contains the single open edge from `R` to `R+1`.  Bernoulli percolation with
parameter `p < 1` is almost surely nonpercolating, yet the error has mass at
least `p` at every such radius.  A fixed-finite-root arm theorem cannot be
inferred from this same-radius whole-ball event.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal Topology unitInterval Sym2 SimpleGraph

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample

open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.NestedAssembly

/-- The Hasse graph on `ℕ`: exactly the semi-infinite path. -/
def lineGraph : SimpleGraph ℕ := SimpleGraph.hasse ℕ

lemma lineGraph_adj (u v : ℕ) :
    lineGraph.Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  simp [lineGraph, SimpleGraph.hasse]

lemma lineGraph_connected : lineGraph.Connected :=
  ⟨SimpleGraph.preconnected_hasse_of_succOrder ℕ⟩

noncomputable instance lineGraph_locallyFinite : lineGraph.LocallyFinite := by
  intro v
  have hfin : (lineGraph.neighborSet v).Finite := by
    apply ((Set.finite_singleton (v - 1)).insert (v + 1)).subset
    intro w hw
    change lineGraph.Adj v w at hw
    rw [lineGraph_adj] at hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  exact hfin.fintype

/-- The edge from `n` to `n+1`. -/
def lineEdge (n : ℕ) : lineGraph.edgeSet :=
  ⟨s(n, n + 1), (lineGraph_adj n (n + 1)).2 (Or.inl rfl)⟩

lemma lineEdge_apply (n : ℕ) : (lineEdge n : Sym2 ℕ) = s(n, n + 1) := rfl

lemma lineEdge_injective : Function.Injective lineEdge := by
  intro m n h
  have h' := congrArg Subtype.val h
  rw [lineEdge_apply, lineEdge_apply, Sym2.eq_iff] at h'
  omega

/-- An explicit length-`n` walk from zero to `n`. -/
def zeroWalk : (n : ℕ) → lineGraph.Walk 0 n
  | 0 => .nil
  | n + 1 => (zeroWalk n).concat ((lineGraph_adj n (n + 1)).2 (Or.inl rfl))

@[simp] lemma zeroWalk_length (n : ℕ) : (zeroWalk n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeroWalk, ih]

lemma walk_length_ge_natDist {u v : ℕ} (p : lineGraph.Walk u v) :
    Nat.dist u v ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
      rw [lineGraph_adj] at h
      simp only [SimpleGraph.Walk.length_cons]
      unfold Nat.dist at *
      omega

lemma lineGraph_dist_zero (n : ℕ) : lineGraph.dist 0 n = n := by
  apply le_antisymm
  · simpa using SimpleGraph.dist_le (zeroWalk n)
  · obtain ⟨p, hp⟩ := lineGraph_connected.exists_walk_length_eq_dist 0 n
    rw [← hp]
    simpa only [Nat.dist_zero_left] using walk_length_ge_natDist p

/-- A closed path edge at `k`, at or to the right of the root, bounds the
root's open cluster by `k`. -/
lemma reachable_le_of_closed {ω : lineGraph.edgeSet → Bool} {o k x : ℕ}
    (hok : o ≤ k) (hline : ω (lineEdge k) = false)
    (hx : OpenConnected lineGraph ω Set.univ o x) : x ≤ k := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at hx
  induction hx with
  | refl => exact hok
  | @tail a b hx hab ih =>
      rw [openGraph, SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨⟨e, he, hee⟩, -⟩ := hab
      have hG : lineGraph.Adj a b := by
        have he' := e.property
        rw [hee] at he'
        exact he'
      have hω : ω ⟨s(a, b), hG⟩ = true := by
        have heq : e = ⟨s(a, b), hG⟩ := Subtype.ext hee
        rw [← heq]
        exact he
      rw [lineGraph_adj] at hG
      rcases hG with hab | hab
      · by_contra hbk
        have hak : a = k := by omega
        have hbeq : b = k + 1 := by omega
        have heq : (⟨s(a, b), hG⟩ : lineGraph.edgeSet) = lineEdge k := by
          apply Subtype.ext
          simp [lineEdge_apply, hak, hbeq]
        rw [heq, hline] at hω
        contradiction
      · omega

/-- All path edges from `o` onwards are open. -/
def TailAllOpen (o : ℕ) : Set (lineGraph.edgeSet → Bool) :=
  {ω | ∀ n, o ≤ n → ω (lineEdge n) = true}

lemma rootInfinite_subset_tailAllOpen (o : ℕ) :
    {ω | {x | OpenConnected lineGraph ω Set.univ o x}.Infinite} ⊆ TailAllOpen o := by
  intro ω hω n hon
  by_contra hn
  have hline : ω (lineEdge n) = false := by
    cases h : ω (lineEdge n) with
    | false => rfl
    | true => exact (hn h).elim
  apply hω
  exact (Set.finite_le_nat n).subset fun x hx => reachable_le_of_closed hon hline hx

lemma tailAllOpen_le_pow (p : unitInterval) (o N : ℕ) :
    percolation lineGraph p (TailAllOpen o) ≤ (ENNReal.ofReal (p : ℝ)) ^ N := by
  let S : Finset lineGraph.edgeSet := (Finset.range N).image (fun n => lineEdge (o + n))
  let C : Set (lineGraph.edgeSet → Bool) :=
    Set.pi (↑S : Set lineGraph.edgeSet) (fun _ => {true})
  have hsub : TailAllOpen o ⊆ C := by
    intro ω hω e he
    change ω e = true
    obtain ⟨n, hn⟩ := Finset.mem_image.1 he
    obtain ⟨hnN, rfl⟩ := hn
    exact hω (o + n) (Nat.le_add_right o n)
  calc
    percolation lineGraph p (TailAllOpen o) ≤ percolation lineGraph p C := measure_mono hsub
    _ = ∏ e ∈ S, bernoulliMeasure true false p {true} := by
      exact Measure.infinitePi_pi _ (fun e _ => measurableSet_singleton true)
    _ = ∏ e ∈ S, ENNReal.ofReal (p : ℝ) := by
      apply Finset.prod_congr rfl
      intro e _
      exact bernoulliMeasure_true _
    _ = ∏ _n ∈ Finset.range N, ENNReal.ofReal (p : ℝ) := by
      dsimp only [S]
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact Nat.add_left_cancel (lineEdge_injective hab)
    _ = (ENNReal.ofReal (p : ℝ)) ^ N := by simp

lemma tailAllOpen_null {p : unitInterval} (hp : p < 1) (o : ℕ) :
    percolation lineGraph p (TailAllOpen o) = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hp))
  exact Filter.Eventually.of_forall (tailAllOpen_le_pow p o)

lemma rootInfinite_null {p : unitInterval} (hp : p < 1) (o : ℕ) :
    percolation lineGraph p {ω | {x | OpenConnected lineGraph ω Set.univ o x}.Infinite} = 0 :=
  measure_mono_null (rootInfinite_subset_tailAllOpen o) (tailAllOpen_null hp o)

/-- The subcritical Bernoulli law on the path is almost surely nonpercolating. -/
theorem ae_nonPercolating_percolation_line {p : unitInterval} (hp : p < 1) :
    ∀ᵐ ω ∂(percolation lineGraph p), ω ∈ FK.NonPercolating lineGraph := by
  change ∀ᵐ ω ∂(percolation lineGraph p), ∀ o,
    {x | OpenConnected lineGraph ω Set.univ o x}.Finite
  rw [ae_all_iff]
  intro o
  have hz := rootInfinite_null hp o
  have h := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [h] with ω hω
  simpa only [Set.mem_ofPred_eq, Set.Infinite, not_not] using hω

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample

open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.NestedAssembly

/-- One open boundary edge forces the same-radius whole-ball far connection. -/
theorem lineEdge_open_subset_radialFarConnection (R : ℕ) :
    {ω | ω (lineEdge R) = true} ⊆
      farConnection lineGraph (innerBall lineGraph_connected 0 (R + 1)) 0 (R + 1) := by
  intro ω hω
  refine ⟨R, (mem_innerBall lineGraph_connected).2 ?_, R + 1, ?_, ?_⟩
  · rw [lineGraph_dist_zero]
    omega
  · change R + 1 ≤ lineGraph.dist 0 (R + 1)
    rw [lineGraph_dist_zero]
  · exact OpenConnected.of_adj (lineEdge R).property (Set.mem_univ _) hω

lemma radialFarConnection_real_lower (p : unitInterval) (R : ℕ) :
    (p : ℝ) ≤ (percolation lineGraph p).real
      (farConnection lineGraph (innerBall lineGraph_connected 0 (R + 1)) 0 (R + 1)) := by
  have hmono := measureReal_mono (lineEdge_open_subset_radialFarConnection R)
    (measure_ne_top (percolation lineGraph p) _)
  have hcoord : (percolation lineGraph p).real {ω | ω (lineEdge R) = true} = (p : ℝ) := by
    rw [measureReal_def, bernoulliProduct_coord_true,
      ENNReal.toReal_ofReal (unitInterval.nonneg p)]
  rwa [hcoord] at hmono

/-- In particular, the shifted radial error cannot converge to zero when `p > 0`.
No stochastic comparison or independence of the far-connection events is used. -/
theorem not_tendsto_shifted_radialFarConnection_real {p : unitInterval} (hp : 0 < p) :
    ¬ Tendsto (fun R : ℕ => (percolation lineGraph p).real
      (farConnection lineGraph (innerBall lineGraph_connected 0 (R + 1)) 0 (R + 1)))
      atTop (𝓝 0) := by
  intro ht
  have hsmall : ∀ᶠ R : ℕ in atTop, (percolation lineGraph p).real
      (farConnection lineGraph (innerBall lineGraph_connected 0 (R + 1)) 0 (R + 1)) <
        (p : ℝ) / 2 := by
    exact (tendsto_order.1 ht).2 _ (by exact half_pos (unitInterval.coe_pos.2 hp))
  obtain ⟨R, hR⟩ := hsmall.exists
  have hlower := radialFarConnection_real_lower p R
  have hpR : 0 < (p : ℝ) := unitInterval.coe_pos.2 hp
  linarith

/-- Unshifted formulation: all radii `1,2,...` have the same positive lower
bound, and hence the entire radial sequence does not tend to zero. -/
theorem not_tendsto_radialFarConnection_real {p : unitInterval} (hp : 0 < p) :
    ¬ Tendsto (fun R : ℕ => (percolation lineGraph p).real
      (farConnection lineGraph (innerBall lineGraph_connected 0 R) 0 R)) atTop (𝓝 0) := by
  intro ht
  apply not_tendsto_shifted_radialFarConnection_real hp
  simpa only [Function.comp_def] using ht.comp (tendsto_add_atTop_nat 1)

/-- **Exact obstruction.**  The hypotheses needed by the fixed-finite-root
vanishing theorem all hold on the path at every `0 < p < 1`, but the radial
whole-ball error constructed in `NestedMetricRegionSplit` does not vanish.
Thus nonpercolation alone does not justify passing from that error to a fixed-root
arm estimate. -/
theorem radial_nonvanishing_of_nonPercolating {p : unitInterval} (hp₀ : 0 < p) (hp₁ : p < 1) :
    (∀ᵐ ω ∂(percolation lineGraph p), ω ∈ FK.NonPercolating lineGraph) ∧
    ¬ Tendsto (fun R : ℕ => (percolation lineGraph p).real
      (farConnection lineGraph (innerBall lineGraph_connected 0 R) 0 R)) atTop (𝓝 0) :=
  ⟨ae_nonPercolating_percolation_line hp₁, not_tendsto_radialFarConnection_real hp₀⟩

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample.lineGraph_dist_zero
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample.ae_nonPercolating_percolation_line
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample.lineEdge_open_subset_radialFarConnection
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample.radialFarConnection_real_lower
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample.not_tendsto_radialFarConnection_real
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample.radial_nonvanishing_of_nonPercolating

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RootAttached

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry.OpenPathGeometry

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- **Root-attached split criterion.**  A failed maximal split has a path from
some left vertex to the far right.  If every left vertex is openly attached to
the fixed root set, that path extends to a fixed-root arm.  The right radius is
`n+L`, while the roots lie in the fixed ball of radius `L`; this is exactly the
additional property absent from the whole-ball radial split. -/
theorem mem_finiteRootArms_of_not_mem_maximalSplitStratum
    (hG : G.Connected) {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (ρ : Fin m ⊕ Fin k → Bool) (ω : G.edgeSet → Bool)
    (M : LabelledOpenPathMap
      (ambientOfSum (splitSource si so) (splitTarget ti xo)) G ρ ω)
    (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hfar : ∀ k, n + L ≤ G.dist o (M.vertex (Sum.inr k)))
    (hroot : ∀ u, ∃ a ∈ roots,
      OpenConnected G ω Set.univ a (M.vertex (Sum.inl u)))
    (hρ : ρ ∉ maximalSplitStratum si ti so xo) :
    ω ∈ finiteRootArms G roots n := by
  obtain ⟨u, k, hk⟩ := exists_left_right_reachable_of_not_mem_maximalSplitStratum
    si ti so xo ρ hρ
  obtain ⟨a, ha, hau⟩ := hroot u
  apply Set.mem_iUnion.mpr
  refine ⟨a, Set.mem_iUnion.mpr ⟨ha, ?_⟩⟩
  refine ⟨M.vertex (Sum.inr k), le_dist_of_le_dist hG (hA a ha) (hfar k), ?_⟩
  exact hau.trans (ConventionGeometry.openConnected_symm (M.openConnected_of_reachable hk))

/-- The corresponding exact exceptional-set inclusion for the canonical nested
split.  Unlike the radial `hleft`, `hroot` quantifies over configurations: every
left vertex must be openly connected to a root in that configuration.  With a
finite-support realization of `finiteRootArms`, this is suitable as the `hD`
input; no whole-ball root set is used. -/
theorem bad_maximalSplit_subset_closedLocalEvent_finiteRootArms
    (hG : G.Connected) {nS nD m k : ℕ} {U K : Type*} [Fintype U] [Fintype K]
    (BS BD : FiniteBox G.edgeSet) (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (d : (Fin m ⊕ Fin k) ≃ Fin nD)
    (f : U ⊕ K → V)
    (hend : ∀ a, s(f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).source a),
      f ((ambientOfSum (splitSource si so) (splitTarget ti xo)).target a)) =
        ((jD (d a)).1).1)
    (roots : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hfar : ∀ k, n + L ≤ G.dist o (f (Sum.inr k)))
    (hroot : ∀ z, ∀ u, ∃ a ∈ roots,
      OpenConnected G (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
        (f (Sum.inl u))) :
    (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) ⁻¹'
      ((fun ρ : (BD.indexedGraph jD).Configuration => ρ ∘ d) ⁻¹'
        maximalSplitStratum si ti so xo))ᶜ ⊆
      BS.reindex jS ⁻¹' closedLocalEvent BS (finiteRootArms G roots n) := by
  intro z hz
  change (restrictΔ (nestedEdgeEquiv BS BD jS jD hBD) z ∘ d) ∉
    maximalSplitStratum si ti so xo at hz
  change BS.glue (BS.closedExterior, BS.reindex jS z) ∈ finiteRootArms G roots n
  exact mem_finiteRootArms_of_not_mem_maximalSplitStratum hG si ti so xo _ _
    (nestedOpenPathMap BS BD jS jD hBD si ti so xo d z f hend)
    roots o L n hA hfar (hroot z) hz

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RootAttached

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RootAttached.mem_finiteRootArms_of_not_mem_maximalSplitStratum
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RootAttached.bad_maximalSplit_subset_closedLocalEvent_finiteRootArms
