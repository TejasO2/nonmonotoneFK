import FK.SourceEscape

/-!
# Literal nested-boundary errors for the classical uniqueness argument

This module replaces the easier complement-escape event by the paper's actual
`∂Λ ↔ ∂Δ` geometry: an open connection to a vertex of the inner region having a
neighbour outside it.  The probabilities tend to zero under nonpercolation for
every cofinal vertex exhaustion.  The proof uses finite closed neighbourhoods
of finite root clusters and a first-exit alternative on open walks.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology Classical

namespace FK.SourceUniqueness

open FK.InfiniteVolume
open FK.InfiniteVolume.NestedAssembly
open CurvatureVariance.Infra.Percolation

universe u

section Geometry

variable {V : Type u} {G : SimpleGraph V}

/-- A vertex of `R` with at least one neighbour outside `R`. -/
def IsRegionBoundary (G : SimpleGraph V) (R : Finset V) (w : V) : Prop :=
  w ∈ R ∧ ∃ x, x ∉ R ∧ G.Adj w x

/-- The literal source event: a root is openly connected to the boundary of
`R`. -/
def boundaryConnection (G : SimpleGraph V) (roots R : Finset V) : Set (G.edgeSet → Bool) :=
  connectsFinsetTo G roots {w | IsRegionBoundary G R w}

lemma measurableSet_boundaryConnection [Countable V] (roots R : Finset V) :
    MeasurableSet (boundaryConnection G roots R) := by
  exact measurableSet_connectsFinsetTo roots _

/-- An open walk from inside `R` either stays in `R`, or reaches the boundary
of `R`.  The exit case is the predecessor of the first outside step, expressed
inductively without choosing a first-exit function. -/
lemma inside_or_boundary_of_isOpenIn {ω : G.edgeSet → Bool} {R : Finset V}
    {a b : V} (ha : a ∈ R) (p : G.Walk a b) (hp : IsOpenIn ω Set.univ p) :
    (b ∈ R ∧ ∀ v ∈ p.support, v ∈ R) ∨
      ∃ w, IsRegionBoundary G R w ∧ OpenConnected G ω Set.univ a w := by
  induction p with
  | nil =>
      left
      refine ⟨ha, ?_⟩
      intro v hv
      rw [SimpleGraph.Walk.mem_support_nil_iff] at hv
      exact hv ▸ ha
  | @cons a b c hab q ih =>
      rw [isOpenIn_cons] at hp
      by_cases hb : b ∈ R
      · rcases ih hb hp.2 with h | h
        · left
          refine ⟨h.1, ?_⟩
          intro v hv
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ha
          · exact h.2 v hv
        · right
          obtain ⟨w, hw, hconn⟩ := h
          refine ⟨w, hw, ?_⟩
          exact (OpenConnected.of_adj hab (Set.mem_univ _) hp.1.2).trans hconn
      · right
        refine ⟨a, ⟨ha, b, hb, hab⟩, OpenConnected.refl ω Set.univ a⟩

lemma boundaryConnection_antitone {roots : Finset V} {R : ℕ → Finset V}
    (hR : Monotone R) (hroots : ∀ n, roots ⊆ R n) :
    Antitone (fun n => boundaryConnection G roots (R n)) := by
  intro m n hmn ω hω
  rcases hω with ⟨a, ha, w, hwR, haw⟩
  obtain ⟨p, hp⟩ := haw
  rcases inside_or_boundary_of_isOpenIn (hroots m ha) p hp with h | h
  · refine ⟨a, ha, w, ?_, p, hp⟩
    rcases hwR with ⟨_, x, hxn, hwx⟩
    exact ⟨h.1, x, fun hxm => hxn (hR hmn hxm), hwx⟩
  · obtain ⟨z, hz, haz⟩ := h
    exact ⟨a, ha, z, hz, haz⟩

/-- A tail of a vertex exhaustion is again a vertex exhaustion. -/
noncomputable def VertexExhaustion.tail (E : VertexExhaustion V) (k : ℕ) :
    VertexExhaustion V where
  region n := E.region (n + k)
  monotone := by
    intro m n hmn
    exact E.monotone (Nat.add_le_add_right hmn k)
  covers := by
    intro v
    obtain ⟨n, hvn, hnk⟩ := ((E.eventually_mem v).and (eventually_ge_atTop k)).exists
    refine ⟨n - k, ?_⟩
    rw [Nat.sub_add_cancel hnk]
    exact hvn

end Geometry

section Vanishing

variable {V : Type u} {G : SimpleGraph V}

/-- If every finite root cluster is finite, their closed neighbourhoods are
finite.  Once such a neighbourhood is contained in the region, no root can
connect to the region boundary. -/
theorem mem_iInter_boundaryConnection_imp_exists_infinite [G.LocallyFinite]
    (roots : Finset V) (E : VertexExhaustion V) {ω : G.edgeSet → Bool}
    (hω : ω ∈ ⋂ n, boundaryConnection G roots (E.region n)) :
    ∃ a ∈ roots, {w | OpenConnected G ω Set.univ a w}.Infinite := by
  classical
  by_contra hno
  push_neg at hno
  let K : Finset V := roots.biUnion fun a =>
    if ha : {w | OpenConnected G ω Set.univ a w}.Finite then ha.toFinset else ∅
  have hK : ∀ a ∈ roots, ∀ w, OpenConnected G ω Set.univ a w → w ∈ K := by
    intro a ha w haw
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    have hfin : {w | OpenConnected G ω Set.univ a w}.Finite := hno a ha
    simp only [hfin, dite_true]
    exact hfin.mem_toFinset.mpr haw
  let N : Finset V := K ∪ K.biUnion (fun w => G.neighborFinset w)
  obtain ⟨n, hn⟩ := E.exists_subset N
  have hmem := Set.mem_iInter.mp hω n
  rcases hmem with ⟨a, ha, w, hwR, haw⟩
  have hwK : w ∈ K := hK a ha w haw
  rcases hwR.2 with ⟨x, hxn, hwx⟩
  have hxN : x ∈ N := by
    apply Finset.mem_union_right K
    apply Finset.mem_biUnion.mpr
    exact ⟨w, hwK, (G.mem_neighborFinset w x).mpr hwx⟩
  exact hxn (hn hxN)

lemma measure_iInter_boundaryConnection_eq_zero [Countable V] [G.LocallyFinite]
    (μ : Measure (G.edgeSet → Bool)) (roots : Finset V) (E : VertexExhaustion V)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    μ (⋂ n, boundaryConnection G roots (E.region n)) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hμ] with ω hω hmem
  obtain ⟨a, ha, hinf⟩ :=
    mem_iInter_boundaryConnection_imp_exists_infinite (G := G) roots E hmem
  exact hinf (hω a)

/-- **The source nested-boundary probabilities tend to zero.**  After passing
to a tail containing the roots, the boundary events are decreasing; their
intersection is null by finite closed neighbourhoods. -/
theorem tendsto_measureReal_boundaryConnection [Countable V] [G.LocallyFinite]
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (roots : Finset V) (E : VertexExhaustion V)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    Tendsto (fun n => μ.real (boundaryConnection G roots (E.region n)))
      atTop (𝓝 0) := by
  classical
  let k := (E.exists_subset roots).choose
  let D := E.tail k
  have hroots : ∀ n, roots ⊆ D.region n := by
    have hstart : roots ⊆ D.region 0 := by
      simpa only [D, k, VertexExhaustion.tail, Nat.zero_add] using
        (E.exists_subset roots).choose_spec
    intro n
    exact hstart.trans (D.monotone (Nat.zero_le n))
  have hlim : Tendsto (fun n => μ (boundaryConnection G roots (D.region n))) atTop
      (𝓝 (μ (⋂ n, boundaryConnection G roots (D.region n)))) := by
    simpa only [Function.comp_def] using
      (tendsto_measure_iInter_atTop (μ := μ)
        (fun n => (measurableSet_boundaryConnection (G := G) roots (D.region n)).nullMeasurableSet)
        (boundaryConnection_antitone (G := G) D.monotone hroots) ⟨0, measure_ne_top _ _⟩)
  rw [measure_iInter_boundaryConnection_eq_zero μ roots D hμ] at hlim
  have hreal := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hlim
  have hshift : Tendsto (fun n => μ.real (boundaryConnection G roots (E.region (n + k))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero, D,
      VertexExhaustion.tail] using hreal
  exact (tendsto_add_atTop_iff_nat k).mp hshift

end Vanishing

section Limit

variable {V : Type u} {G : SimpleGraph V}

/-- Equality of two genuine FK weak limits from literal nested-boundary
estimates. -/
theorem eq_of_isFKLimit_of_nested_boundary_bounds [Countable V] [G.LocallyFinite]
    (D E : VertexExhaustion V) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (E.box n).BoundaryPartition)
    (β : ∀ n, (D.box n).BoundaryPartition)
    (μ ν ρ : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : IsFKLimit E.exhaustion hq hp α μ)
    (hν : IsFKLimit D.exhaustion hq hp β ν)
    (hρ : ∀ᵐ ω ∂(ρ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)),
      ∀ᶠ m in atTop, ∀ᶠ n in atTop,
        |(((E.box n).finiteVolumeLaw hq hp (α n)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S) -
          (((D.box m).finiteVolumeLaw hq hp (β m)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S)| ≤
        (ρ : Measure (Configuration G.edgeSet)).real
          (boundaryConnection G (roots I) (D.region m))) :
    μ = ν := by
  apply Subtype.ext
  apply FKModel.measure_ext_of_eq_on_boolCylinders
    (μ : Measure (G.edgeSet → Bool)) (ν : Measure (G.edgeSet → Bool))
  intro I S
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hbound I S)
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  apply FKModel.eq_of_tendsto_of_eventually_abs_sub_le
    ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto
      (fun n => (E.box n).finiteVolumeLaw hq hp (α n)) μ).mp hμ I S)
    ((tendsto_add_atTop_iff_nat M).2
      ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto
        (fun n => (D.box n).finiteVolumeLaw hq hp (β n)) ν).mp hν I S))
    ((tendsto_add_atTop_iff_nat M).2
      (tendsto_measureReal_boundaryConnection (ρ : Measure (G.edgeSet → Bool))
        (roots I) D hρ))
  intro m
  have hh := hM (M + m) (Nat.le_add_right M m)
  have heq : M + m = m + M := Nat.add_comm _ _
  rw [heq] at hh
  exact hh

end Limit

end FK.SourceUniqueness
