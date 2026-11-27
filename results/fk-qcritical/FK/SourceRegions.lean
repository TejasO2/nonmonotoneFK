import FK.RandomRegionKernel
import FK.ExteriorIdentification
import FK.ClosedFrontierExhaustion

/-!
# Finite region packaging and source conventions

This file supplies the graph-only part of Theorem 5.1 of
Beffara--Faipeur--Oke (arXiv:2512.16486v1) for a general source convention.
It uses the actual region boxes and exterior open components already built in
`FK.RegionFibreIdentity`.  No probabilistic uniqueness statement is made here.
-/

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology
open CurvatureVariance.Infra.Percolation

namespace FK.SourceRegions

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionGeometry
open FK.RandomClosedBoundary

universe u

/-! ## Total finite-set packaging -/

/-- Package a finite set as a `Finset`; use the empty set on the infinite
fallback.  The hypotheses needed to rule out the fallback are stated by all
subsequent membership lemmas, rather than being hidden in a coercion. -/
noncomputable def finiteOrEmpty {α : Type*} (S : Set α) : Finset α := by
  classical
  exact if h : S.Finite then h.toFinset else ∅

lemma coe_finiteOrEmpty_of_finite {α : Type*} {S : Set α} (hS : S.Finite) :
    (finiteOrEmpty S : Set α) = S := by
  classical
  simp only [finiteOrEmpty, dif_pos hS]
  exact hS.coe_toFinset

lemma mem_finiteOrEmpty_of_finite {α : Type*} {S : Set α} (hS : S.Finite) {a : α} :
    a ∈ finiteOrEmpty S ↔ a ∈ S := by
  change a ∈ (finiteOrEmpty S : Set α) ↔ a ∈ S
  rw [coe_finiteOrEmpty_of_finite hS]

lemma finiteOrEmpty_eq_of_coe {α : Type*} {S : Set α} {t : Finset α}
    (h : S = (t : Set α)) : finiteOrEmpty S = t := by
  classical
  have hfin : S.Finite := h ▸ t.finite_toSet
  simp only [finiteOrEmpty, dif_pos hfin]
  apply Finset.coe_injective
  rw [hfin.coe_toFinset, h]

/-- Exact equality characterization, including the infinite fallback. -/
lemma finiteOrEmpty_eq_iff {α : Type*} (S : Set α) (t : Finset α) :
    finiteOrEmpty S = t ↔ S = (t : Set α) ∨ (¬ S.Finite ∧ t = ∅) := by
  classical
  constructor
  · intro h
    by_cases hfin : S.Finite
    · left
      rw [← h, coe_finiteOrEmpty_of_finite hfin]
    · right
      refine ⟨hfin, ?_⟩
      simpa only [finiteOrEmpty, dif_neg hfin] using h.symm
  · rintro (h | ⟨hfin, rfl⟩)
    · exact finiteOrEmpty_eq_of_coe h
    · simp only [finiteOrEmpty, dif_neg hfin]

section MeasurableFiniteOrEmpty

variable {Ω α : Type*} [MeasurableSpace Ω] [Countable α]

/-- Equality of a set-valued map with a fixed finite set is measurable as soon
as membership of each coordinate is measurable. -/
lemma measurableSet_set_eq_finset (S : Ω → Set α)
    (hmem : ∀ a, MeasurableSet {ω | a ∈ S ω}) (t : Finset α) :
    MeasurableSet {ω | S ω = (t : Set α)} := by
  have heq : {ω | S ω = (t : Set α)} =
      ⋂ a, {ω | (a ∈ S ω ↔ a ∈ (t : Set α))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h a => by rw [h], fun h => Set.ext h⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro a
  by_cases ha : a ∈ (t : Set α)
  · have h : {ω | (a ∈ S ω ↔ a ∈ (t : Set α))} = {ω | a ∈ S ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, ha, iff_true]
    rw [h]
    exact hmem a
  · have h : {ω | (a ∈ S ω ↔ a ∈ (t : Set α))} = {ω | a ∈ S ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, ha, iff_false]
    rw [h]
    exact (hmem a).compl

/-- The event that a coordinatewise-measurable set-valued map is finite is
measurable, expressed by its countably many finite-set fibres. -/
lemma measurableSet_finite (S : Ω → Set α)
    (hmem : ∀ a, MeasurableSet {ω | a ∈ S ω}) :
    MeasurableSet {ω | (S ω).Finite} := by
  have heq : {ω | (S ω).Finite} = ⋃ t : Finset α, {ω | S ω = (t : Set α)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨h.toFinset, h.coe_toFinset.symm⟩
    · rintro ⟨t, ht⟩
      rw [ht]
      exact t.finite_toSet
  rw [heq]
  exact MeasurableSet.iUnion (measurableSet_set_eq_finset S hmem)

/-- **Measurable total finite-set packaging.**  In particular this applies to
vertex regions and to their edge regions on a countable graph. -/
theorem measurable_finiteOrEmpty (S : Ω → Set α)
    (hmem : ∀ a, MeasurableSet {ω | a ∈ S ω}) :
    Measurable (fun ω => finiteOrEmpty (S ω)) := by
  classical
  apply measurable_to_countable'
  intro t
  have heq : (fun ω => finiteOrEmpty (S ω)) ⁻¹' {t} =
      {ω | S ω = (t : Set α)} ∪
        ({ω | ¬ (S ω).Finite} ∩ if t = ∅ then Set.univ else (∅ : Set Ω)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [finiteOrEmpty_eq_iff]
    by_cases ht : t = ∅ <;> simp [ht]
  rw [heq]
  apply MeasurableSet.union (measurableSet_set_eq_finset S hmem t)
  apply MeasurableSet.inter (measurableSet_finite S hmem).compl
  by_cases ht : t = ∅ <;> simp [ht]

end MeasurableFiniteOrEmpty

/-! ## Finite vertex and edge regions -/

variable {V : Type u} [Countable V] {G : SimpleGraph V}

/-- Finite packaging of the union of the open clusters based at `Vn`. -/
noncomputable def reachUnionFinset (ω : G.edgeSet → Bool) (Vn : Finset V) : Finset V :=
  finiteOrEmpty (reachUnion ω Vn)

lemma coe_reachUnionFinset {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) :
    (reachUnionFinset ω Vn : Set V) = reachUnion ω Vn :=
  coe_finiteOrEmpty_of_finite (reachUnion_finite hfin)

lemma mem_reachUnionFinset {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) {u : V} :
    u ∈ reachUnionFinset ω Vn ↔ u ∈ reachUnion ω Vn :=
  mem_finiteOrEmpty_of_finite (reachUnion_finite hfin)

/-- Finite packaging of all graph edges inside the random vertex region. -/
noncomputable def regionEdgeFinset (ω : G.edgeSet → Bool) (Vn : Finset V) : Finset G.edgeSet :=
  finiteOrEmpty (regionSet ω Vn)

lemma coe_regionEdgeFinset {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) :
    (regionEdgeFinset ω Vn : Set G.edgeSet) = regionSet ω Vn :=
  coe_finiteOrEmpty_of_finite (regionSet_finite hfin)

lemma mem_regionEdgeFinset {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) {e : G.edgeSet} :
    e ∈ regionEdgeFinset ω Vn ↔ e ∈ regionSet ω Vn :=
  mem_finiteOrEmpty_of_finite (regionSet_finite hfin)

/-- The vertex-region packaging is genuinely measurable, not merely an
almost-everywhere assertion about a chosen finite set. -/
theorem measurable_reachUnionFinset (Vn : Finset V) :
    Measurable (fun ω : G.edgeSet → Bool => reachUnionFinset ω Vn) := by
  apply measurable_finiteOrEmpty
  intro u
  exact measurableSet_mem_reachUnion Vn u

/-- The corresponding edge-region map is measurable. -/
theorem measurable_regionEdgeFinset (Vn : Finset V) :
    Measurable (fun ω : G.edgeSet → Bool => regionEdgeFinset ω Vn) := by
  apply measurable_finiteOrEmpty
  intro e
  have heq : {ω : G.edgeSet → Bool | e ∈ regionSet ω Vn} =
      ⋂ v : V, {ω : G.edgeSet → Bool | v ∈ (e.1 : Sym2 V) → v ∈ reachUnion ω Vn} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h v hv => h v hv, fun h v hv => h v hv⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro v
  by_cases hv : v ∈ (e.1 : Sym2 V)
  · have h : {ω : G.edgeSet → Bool | v ∈ (e.1 : Sym2 V) → v ∈ reachUnion ω Vn} =
        {ω : G.edgeSet → Bool | v ∈ reachUnion ω Vn} := by
      ext ω
      simp only [Set.mem_setOf_eq, hv, true_implies]
    rw [h]
    exact measurableSet_mem_reachUnion Vn v
  · have h : {ω : G.edgeSet → Bool | v ∈ (e.1 : Sym2 V) → v ∈ reachUnion ω Vn} =
        Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, hv, false_implies, Set.mem_univ]
    rw [h]
    exact MeasurableSet.univ

end FK.SourceRegions


namespace FK.SourceRegions

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionGeometry
open FK.RandomClosedBoundary
open FK.RandomRegionKernel

universe u

local instance sourceBoundaryMeasurableSpace (X : Type*) : MeasurableSpace (Setoid X) := ⊤

local instance sourceFiniteSetoid (X : Type*) [Finite X] : Finite (Setoid X) := by
  classical
  apply Finite.of_injective (fun α : Setoid X => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The actual exterior open-component partition on a finite vertex region. -/
noncomputable def sourceComponents (s : Finset V) (η : (boxOf (G := G) s).Exterior) :
    (boxOf (G := G) s).BoundaryPartition :=
  exteriorPartition (G := G) (s : Set V) s.finite_toSet η

/-- Infinitude of an exterior component is measured in the whole exterior
subgraph, not just in its intersection with the finite boundary. -/
noncomputable def sourceInfinite (s : Finset V) (η : (boxOf (G := G) s).Exterior)
    (x : (boxOf (G := G) s).Vertex) : Prop :=
  ExteriorInfiniteCluster G
    (extendExterior (G := G) (s : Set V) s.finite_toSet η)
    (nonInteriorEdges (s : Set V)) x.1

/-- A source convention indexed by every finite vertex region of a locally
finite simple graph.  The compatibility field is the actual finite-FK tower
condition at every nested pair of regions. -/
structure SourceConvention (G : SimpleGraph V) [G.LocallyFinite]
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1) where
  partition : ∀ s : Finset V, (boxOf (G := G) s).Exterior →
    (boxOf (G := G) s).BoundaryPartition
  measurable_partition : ∀ s, Measurable (partition s)
  compatible : ∀ {s t : Finset V}, s ⊆ t → ∀ η : (boxOf (G := G) t).Exterior,
    (boxOf (G := G) s).IsDLR hq hp (partition s) (measurable_partition s)
      ((boxOf (G := G) t).conditionalLaw hq hp (partition t) η)

/-- The all-finite-region DLR class.  Unlike an exhaustion-indexed class this
requires the source specification at every finite region. -/
def SourceDLRMeasures {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : SourceConvention G hq hp) : Set (ProbabilityMeasure (Configuration G.edgeSet)) :=
  {μ | ∀ s : Finset V, (boxOf (G := G) s).IsDLR hq hp (Φ.partition s)
    (Φ.measurable_partition s) μ}

/-- The two hypotheses imposed on every convention in Section 1.3 of the
paper: merge exterior open paths and separate distinct components whenever at
least one is finite. -/
def IsSourceGeometry {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : SourceConvention (V := V) G hq hp) : Prop :=
  (∀ s η, MergesOpenComponents (sourceComponents (G := G) s η) (Φ.partition s η)) ∧
  (∀ s η, SeparatesFiniteComponents (sourceComponents (G := G) s η)
    (Φ.partition s η) (sourceInfinite (G := G) s η))

/-! ## Closed exterior paths at a closed frontier -/

/-- On non-interior edges the exterior extension of the exterior restriction
is the original configuration. -/
lemma isOpenIn_of_isOpenIn_extendExterior_restrict {R : Set V} (hR : R.Finite)
    (ω : G.edgeSet → Bool) {a b : V} (p : G.Walk a b)
    (hp : IsOpenIn
      (extendExterior (G := G) R hR (restrictExterior (G := G) R hR ω))
      (nonInteriorEdges R) p) : IsOpenIn ω (nonInteriorEdges R) p := by
  induction p with
  | nil => exact isOpenIn_nil
  | @cons a b c hab q ih =>
    rw [isOpenIn_cons] at hp ⊢
    refine ⟨⟨hp.1.1, ?_⟩, ih hp.2⟩
    have he : (⟨s(a, b), hab⟩ : G.edgeSet) ∉ (regionBoxOf (G := G) R hR).edges :=
      not_mem_regionBox_edges_of_crossing R hR hp.1.1
    have hopen : extendExterior (G := G) R hR
        (restrictExterior (G := G) R hR ω) ⟨s(a, b), hab⟩ = true := hp.1.2
    rw [extendExterior_apply_of_notMem R hR he] at hopen
    exact hopen

/-- Every open exterior walk based at a vertex of a closed region stays at
that vertex; in particular its exterior component is a singleton. -/
theorem eq_of_openConnected_extendExterior_restrict {R : Set V} (hR : R.Finite)
    {ω : G.edgeSet → Bool} (hclosed : ClosedBoundary G (openSubgraph G ω) R)
    {x z : V} (hx : x ∈ R)
    (h : OpenConnected G
      (extendExterior (G := G) R hR (restrictExterior (G := G) R hR ω))
      (nonInteriorEdges R) x z) : x = z := by
  obtain ⟨p, hp⟩ := h
  exact eq_of_isOpenIn_nonInterior hclosed hx
    (isOpenIn_of_isOpenIn_extendExterior_restrict hR ω p hp)

/-- Closed crossing edges make every exterior boundary component finite,
without any global nonpercolation assumption. -/
theorem not_sourceInfinite_restrict {s : Finset V} {ω : G.edgeSet → Bool}
    (hclosed : ClosedBoundary G (openSubgraph G ω) (s : Set V))
    (x : (boxOf (G := G) s).Vertex) :
    ¬ sourceInfinite (G := G) s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) x := by
  intro hinf
  have hsub : {z : V | OpenConnected G
      (extendExterior (G := G) (s : Set V) s.finite_toSet
        (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))
      (nonInteriorEdges (s : Set V)) x.1 z} ⊆ {x.1} := by
    intro z hz
    exact (eq_of_openConnected_extendExterior_restrict s.finite_toSet hclosed x.2 hz).symm
  exact hinf ((Set.finite_singleton x.1).subset hsub)

/-- **General source-convention boundary theorem.**  When every crossing edge
is closed, both source rules force the boundary partition to be free.  This is
not restricted to the free or wired convention and needs no nonpercolation
assumption on the ambient configuration. -/
theorem sourcePartition_restrict_eq_bot {q p : NNReal} {hq : 0 < q} {hp : p ≤ 1}
    (Φ : SourceConvention (V := V) G hq hp) (hΦ : IsSourceGeometry Φ)
    (s : Finset V) {ω : G.edgeSet → Bool}
    (hclosed : ClosedBoundary G (openSubgraph G ω) (s : Set V)) :
    Φ.partition s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) = ⊥ := by
  have hcomponents : sourceComponents (G := G) s
      (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) = ⊥ := by
    exact exteriorPartition_restrict_eq_bot (G := G) (s : Set V) s.finite_toSet hclosed
  have hmerge := hΦ.1 s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω)
  have hsep : SeparatesFiniteComponents
      (sourceComponents (G := G) s
        (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))
      (Φ.partition s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))
      (sourceInfinite (G := G) s
        (restrictExterior (G := G) (s : Set V) s.finite_toSet ω)) :=
    hΦ.2 s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω)
  rw [hcomponents] at hmerge hsep
  apply le_antisymm
  · intro x y hxy
    by_contra hne
    exact (hsep hne (Or.inl (not_sourceInfinite_restrict hclosed x))) hxy
  · exact hmerge

/-- The general source specification therefore gives the free finite-volume
interior FK law at a closed region. -/
theorem sourceInteriorFKMeasure_restrict_eq_free {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention (V := V) G hq hp) (hΦ : IsSourceGeometry Φ)
    (s : Finset V) {ω : G.edgeSet → Bool}
    (hclosed : ClosedBoundary G (openSubgraph G ω) (s : Set V)) :
    (boxOf (G := G) s).interiorFKMeasure hq hp (Φ.partition s)
        (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) =
      (boxOf (G := G) s).graph.fkMeasure hq hp (boxOf (G := G) s).graph.freeBoundary := by
  unfold FK.InfiniteVolume.FiniteBox.interiorFKMeasure
  rw [sourcePartition_restrict_eq_bot Φ hΦ s hclosed, freeBoundary_eq_bot]

/-- Global conditional-law form of the same general source-convention
identity, retaining the actual exterior configuration. -/
theorem sourceConditionalLaw_restrict_eq_free {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention (V := V) G hq hp) (hΦ : IsSourceGeometry Φ)
    (s : Finset V) {ω : G.edgeSet → Bool}
    (hclosed : ClosedBoundary G (openSubgraph G ω) (s : Set V)) :
    ((boxOf (G := G) s).conditionalLaw hq hp (Φ.partition s)
        (restrictExterior (G := G) (s : Set V) s.finite_toSet ω) :
        Measure (Configuration G.edgeSet)) =
      Measure.map
        (fun i : (boxOf (G := G) s).Interior => (boxOf (G := G) s).glue
          (restrictExterior (G := G) (s : Set V) s.finite_toSet ω, i))
        ((boxOf (G := G) s).graph.fkMeasure hq hp (boxOf (G := G) s).graph.freeBoundary) := by
  change Measure.map
      (fun i : (boxOf (G := G) s).Interior => (boxOf (G := G) s).glue
        (restrictExterior (G := G) (s : Set V) s.finite_toSet ω, i))
      ((boxOf (G := G) s).graph.fkMeasure hq hp
        (Φ.partition s (restrictExterior (G := G) (s : Set V) s.finite_toSet ω))) = _
  rw [sourcePartition_restrict_eq_bot Φ hΦ s hclosed, freeBoundary_eq_bot]

/-! ## Monotone and cofinal finite edge regions -/

variable {ω : G.edgeSet → Bool}

lemma regionEdgeFinset_mono {Vm Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite)
    (hmn : Vm ⊆ Vn) : regionEdgeFinset (G := G) ω Vm ⊆ regionEdgeFinset (G := G) ω Vn := by
  intro e he
  exact (mem_regionEdgeFinset hfin).2
    (regionSet_mono hmn ((mem_regionEdgeFinset hfin).1 he))

/-- At finite clusters the packaged edge regions have exactly the cofinality
needed by the reverse-martingale layer. -/
lemma exists_mem_regionEdgeFinset {Vn : ℕ → Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite)
    (hmono : Monotone Vn) (hcof : ∀ v : V, ∃ n, v ∈ (Vn n : Set V))
    (e : G.edgeSet) : ∃ n, e ∈ regionEdgeFinset (G := G) ω (Vn n) := by
  obtain ⟨n, hn⟩ := regionSet_cofinal (ω := ω) hmono hcof e
  exact ⟨n, (mem_regionEdgeFinset hfin).2 hn⟩

end FK.SourceRegions



namespace FK.SourceRegions

open FK.InfiniteVolume
open FK.InfiniteVolume.ConventionGeometry
open FK.RandomClosedBoundary
open FK.RandomRegionKernel

universe u

local instance sourceBoundaryMeasurableSpace' (X : Type*) : MeasurableSpace (Setoid X) := ⊤

local instance sourceFiniteSetoid' (X : Type*) [Finite X] : Finite (Setoid X) := by
  classical
  apply Finite.of_injective (fun α : Setoid X => α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The two existing descriptions of the open-cluster enlargement of a finite
base set coincide. -/
theorem reachUnion_eq_region (ω : G.edgeSet → Bool) (Vn : Finset V) :
    reachUnion ω Vn = region G ω (Vn : Set V) := by
  ext u
  rw [mem_reachUnion, mem_region_iff]

theorem closedBoundary_reachUnion (ω : G.edgeSet → Bool) (Vn : Finset V) :
    ClosedBoundary G (openSubgraph G ω) (reachUnion ω Vn) := by
  rw [reachUnion_eq_region]
  exact region_closedBoundary (G := G) (Vn : Set V)

/-- The closed-frontier property passes from the dominating configuration to
an ordered lower configuration. -/
theorem closedBoundary_reachUnion_of_le {ω η : G.edgeSet → Bool} (hω : ω ≤ η)
    (Vn : Finset V) : ClosedBoundary G (openSubgraph G ω) (reachUnion η Vn) := by
  rw [reachUnion_eq_region]
  exact region_closedBoundary_of_le (G := G) hω (Vn : Set V)

lemma reachUnionFinset_mono {ω : G.edgeSet → Bool} {Vm Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite)
    (hmn : Vm ⊆ Vn) : reachUnionFinset (G := G) ω Vm ⊆ reachUnionFinset (G := G) ω Vn := by
  intro v hv
  exact (mem_reachUnionFinset hfin).2
    (reachUnion_mono hmn ((mem_reachUnionFinset hfin).1 hv))

lemma exists_mem_reachUnionFinset {ω : G.edgeSet → Bool} {Vn : ℕ → Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite)
    (hcof : ∀ v : V, ∃ n, v ∈ (Vn n : Set V)) (v : V) :
    ∃ n, v ∈ reachUnionFinset (G := G) ω (Vn n) := by
  obtain ⟨n, hn⟩ := hcof v
  exact ⟨n, (mem_reachUnionFinset hfin).2 (self_mem_reachUnion hn)⟩

/-- **The exact finite edge/vertex box bridge.**  On finite clusters, the
edge-finset used by the reverse martingale is literally the edge set of the
region box used by DLR. -/
theorem regionEdgeFinset_eq_box_edges {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) :
    regionEdgeFinset (G := G) ω Vn =
      (boxOf (G := G) (reachUnionFinset (G := G) ω Vn)).edges := by
  classical
  ext e
  rw [mem_regionEdgeFinset hfin]
  rw [mem_regionBox_edges_iff]
  change e ∈ regionSet ω Vn ↔ e ∈ interiorEdgeSet G
    ((reachUnionFinset (G := G) ω Vn : Finset V) : Set V)
  rw [coe_reachUnionFinset hfin]
  rfl

/-- The law-independent free value of a global event supported in a region
box. -/
noncomputable def freeCylinderMass {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (s : Finset V) (C : Set (Configuration G.edgeSet)) : ℝ :=
  ((boxOf (G := G) s).graph.fkMeasure hq hp (boxOf (G := G) s).graph.freeBoundary).real
    ((boxOf (G := G) s).interiorRestriction '' C)

/-- **Fixed-region DLR conditional identity for every source convention.**
The null set comes from the ordinary DLR conditional-expectation theorem for
the single fixed box.  On the closed-frontier event, merge and finite-component
separation then give the law-independent free cylinder mass. -/
theorem ae_condExp_eq_freeCylinderMass_of_closedBoundary
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (Φ : SourceConvention (V := V) G hq hp) (hΦ : IsSourceGeometry Φ)
    (μ : ProbabilityMeasure (Configuration G.edgeSet)) (hμ : μ ∈ SourceDLRMeasures Φ)
    (s : Finset V) {C : Set (Configuration G.edgeSet)}
    (hdep : FKLimit.DependsOnCoordinates C (boxOf (G := G) s).edges) :
    ∀ᵐ ω ∂(μ : Measure (Configuration G.edgeSet)),
      ClosedBoundary G (openSubgraph G ω) (s : Set V) →
      (μ : Measure (Configuration G.edgeSet))[
          C.indicator (fun _ => (1 : ℝ)) | FKLimit.outsideSigma (boxOf (G := G) s).edges] ω =
        freeCylinderMass (G := G) hq hp s C := by
  classical
  have hmain := (boxOf (G := G) s).condExp_of_dependsOn_edges_of_isDLR
    hq hp (Φ.partition s) (Φ.measurable_partition s) μ (hμ s) hdep
  filter_upwards [hmain] with ω hω
  intro hclosed
  rw [hω]
  have hpart : Φ.partition s
      (FKLimit.exteriorRestriction (boxOf (G := G) s).edges ω) = ⊥ := by
    have hext : FKLimit.exteriorRestriction (boxOf (G := G) s).edges ω =
        restrictExterior (G := G) (s : Set V) s.finite_toSet ω := by
      funext e
      rfl
    rw [hext]
    exact sourcePartition_restrict_eq_bot Φ hΦ s hclosed
  calc
    ((boxOf (G := G) s).conditionalLaw hq hp (Φ.partition s)
        (FKLimit.exteriorRestriction (boxOf (G := G) s).edges ω) :
        Measure (Configuration G.edgeSet)).real C =
      ((boxOf (G := G) s).conditionalLaw hq hp (Φ.partition s)
        (FKLimit.exteriorRestriction (boxOf (G := G) s).edges ω) :
        Measure (Configuration G.edgeSet)).real
        ((boxOf (G := G) s).interiorRestriction ⁻¹'
          ((boxOf (G := G) s).interiorRestriction '' C)) := by
        rw [← (boxOf (G := G) s).eq_preimage_interiorRestriction_image hdep]
    _ = ((boxOf (G := G) s).graph.fkMeasure hq hp
        (Φ.partition s (FKLimit.exteriorRestriction (boxOf (G := G) s).edges ω))).real
        ((boxOf (G := G) s).interiorRestriction '' C) :=
      (boxOf (G := G) s).conditionalLaw_real_interior_preimage hq hp _ _
        MeasurableSet.of_discrete
    _ = freeCylinderMass (G := G) hq hp s C := by
      unfold freeCylinderMass
      rw [hpart, freeBoundary_eq_bot]

end FK.SourceRegions



namespace FK.SourceRegions

open FK.InfiniteVolume
open FK.RandomClosedBoundary
open FK.RandomRegionKernel

universe u

variable {V : Type u} [Countable V] {G : SimpleGraph V} [G.LocallyFinite]

/-- Nonpercolation of the upper configuration makes the frontier of every
packaged random region closed for an ordered lower configuration. -/
theorem closedBoundary_packaged_of_le {ω η : G.edgeSet → Bool}
    (hle : ω ≤ η) (hη : η ∈ NonPercolating G) (Vn : Finset V) :
    ClosedBoundary G (openSubgraph G ω) ((reachUnionFinset (G := G) η Vn : Set V)) := by
  rw [coe_reachUnionFinset hη]
  exact closedBoundary_reachUnion_of_le (G := G) hle Vn

/-- Every finite edge set is contained in one of the packaged random regions;
this is not merely pointwise existence for each edge separately. -/
theorem exists_subset_regionEdgeFinset {η : G.edgeSet → Bool}
    (hη : η ∈ NonPercolating G) {Vn : ℕ → Finset V}
    (hmono : Monotone Vn) (hcof : ∀ v : V, ∃ n, v ∈ (Vn n : Set V))
    (K : Finset G.edgeSet) : ∃ n, K ⊆ regionEdgeFinset (G := G) η (Vn n) := by
  classical
  have hTmono : Monotone (fun n => regionEdgeFinset (G := G) η (Vn n)) :=
    fun _ _ hmn => regionEdgeFinset_mono hη (hmono hmn)
  induction K using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert e K he ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := exists_mem_regionEdgeFinset (G := G) hη hmono hcof e
    refine ⟨max N M, ?_⟩
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact hTmono (le_max_right N M) hM
    · exact hTmono (le_max_left N M) (hN hf)

/-- Cofinality upgrades a fixed cylinder to every sufficiently late random
region, uniformly after one threshold depending on its finite support. -/
theorem eventually_dependsOnCoordinates_packaged {η : G.edgeSet → Bool}
    (hη : η ∈ NonPercolating G) {Vn : ℕ → Finset V}
    (hmono : Monotone Vn) (hcof : ∀ v : V, ∃ n, v ∈ (Vn n : Set V))
    {K : Finset G.edgeSet} {C : Set (Configuration G.edgeSet)}
    (hC : FKLimit.DependsOnCoordinates C K) :
    ∀ᶠ n in atTop, FKLimit.DependsOnCoordinates C (regionEdgeFinset (G := G) η (Vn n)) := by
  have hTmono : Monotone (fun n => regionEdgeFinset (G := G) η (Vn n)) :=
    fun _ _ hmn => regionEdgeFinset_mono hη (hmono hmn)
  obtain ⟨N, hN⟩ := exists_subset_regionEdgeFinset (G := G) hη hmono hcof K
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hC.mono (fun _ he => hTmono hn (hN he))

/-- One null set supplies all geometric inputs to the random-exhaustion layer:
closed lower frontiers, monotone cofinal edge regions, and equality with the
DLR boxes' edge sets. -/
theorem ae_packagedRegion_data {ρ : Measure (G.edgeSet → Bool)}
    (hρ : ∀ᵐ η ∂ρ, η ∈ NonPercolating G) (Vn : ℕ → Finset V)
    (hmono : Monotone Vn) (hcof : ∀ v : V, ∃ n, v ∈ (Vn n : Set V)) :
    ∀ᵐ η ∂ρ,
      (∀ n, ClosedBoundary G (openSubgraph G η)
        ((reachUnionFinset (G := G) η (Vn n) : Set V))) ∧
      Monotone (fun n => regionEdgeFinset (G := G) η (Vn n)) ∧
      (∀ K : Finset G.edgeSet, ∃ n, K ⊆ regionEdgeFinset (G := G) η (Vn n)) ∧
      (∀ n, regionEdgeFinset (G := G) η (Vn n) =
        (boxOf (G := G) (reachUnionFinset (G := G) η (Vn n))).edges) := by
  filter_upwards [hρ] with η hη
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [coe_reachUnionFinset hη]
    exact closedBoundary_reachUnion (G := G) η (Vn n)
  · exact fun _ _ hmn => regionEdgeFinset_mono hη (hmono hmn)
  · exact fun K => exists_subset_regionEdgeFinset (G := G) hη hmono hcof K
  · exact fun n => regionEdgeFinset_eq_box_edges hη

end FK.SourceRegions
