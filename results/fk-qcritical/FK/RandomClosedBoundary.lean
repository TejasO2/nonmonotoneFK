import FK.StrongUniqueness
import FK.ExplorationGeometry
import FK.InfiniteVolume
import FK.ClosedBoundaryEventually

/-!
# A measurable random closed-boundary exhaustion (Theorem 5.1 geometry)

`FK/StrongUniqueness.lean` proves that non-percolation of a configuration
`ω : G.edgeSet → Bool` is equivalent to the existence of a finite connected
closed-boundary exhaustion, and that this event is measurable and is inherited
by both dominated laws of an ordered triple coupling.  The exhaustion there is
obtained by `Classical.choice` from a `Nonempty` statement, so nothing is known
about the measurability of the map `ω ↦ S_n(ω)`.

This file replaces the chosen object by an *explicit* one:

* `region G ω T` is the union of the open clusters based at the vertex set `T`;
  it is `ClosedRegion (openGraph G (openSet ω)) T` of `FK/ClosedBoundary.lean`,
  and the paper's `S_n(ω)` is `region G ω (base n)` for any cofinal family of
  finite connected bases `base` (Theorem 5.1, arXiv:2512.16486).

Main results:

* `closedBoundaryExhaustionOfRegion`: the explicit regions form a
  `ClosedBoundaryExhaustion` whenever the open clusters are finite, so no
  choice of exhaustion is required;
* `measurableSet_mem_region`, `measurableSet_region_subset`,
  `measurableSet_region_eq`: on a countable vertex type the region map is a
  genuine random variable, i.e. every stratum `{ω | region G ω T = S}` is
  measurable;
* `ae_region_finite`: almost surely the explicit region sequence is finite,
  connected, closed-boundary, monotone and exhaustive, with one null set;
* `exists_region_contains`: every fixed finite vertex set (in particular the
  endpoint set of a fixed cylinder event) is contained in all sufficiently late
  regions — deterministically, hence off no extra null set;
* `exteriorOpenSetoid_eq_bot`: **the paper's boundary step**.  If every ambient
  edge leaving `S` is closed in `ω`, then the setoid of exterior-open
  connections between vertices of `S` is discrete, so the boundary condition
  induced by `ω` on `S` is the free one;
* `region_union_of_closed`, `disjoint_region_of_subset_compl`: the finite-stack
  identities — exploration starting inside a closed region cannot leave it and
  exploration starting outside cannot enter it, so explorations stack.

No statement here is a new axiom or a conditional wrapper: the closed-boundary
properties are deterministic, the only probabilistic input is the
non-percolation event, and the boundary/discreteness results are proved for the
actual configuration.
-/

open MeasureTheory Set
open scoped ENNReal

open CurvatureVariance.Infra.Percolation

namespace FK.RandomClosedBoundary

variable {V : Type*} {G : SimpleGraph V}

/-! ## The open subgraph and the explicit region -/

/-- The spanning subgraph of open edges of a configuration. -/
noncomputable def openSubgraph (G : SimpleGraph V) (ω : G.edgeSet → Bool) : SimpleGraph V :=
  openGraph G (openSet ω)

/-- The region explored from the base set `T`: the union of the open clusters
based at vertices of `T`.  This is the paper's `S(ω)`. -/
noncomputable def region (G : SimpleGraph V) (ω : G.edgeSet → Bool) (T : Set V) : Set V :=
  ClosedRegion (openSubgraph G ω) T

theorem region_def (ω : G.edgeSet → Bool) (T : Set V) :
    region G ω T = ClosedRegion (openSubgraph G ω) T := rfl

/-- Closed regions are monotone in the open graph. -/
theorem closedRegion_mono_le {H H' : SimpleGraph V} (hHH' : H ≤ H') (T : Set V) :
    ClosedRegion H T ⊆ ClosedRegion H' T := by
  intro x hx
  rw [FK.Finite.Exploration.mem_outerRegion_iff] at hx ⊢
  obtain ⟨v, hv, hxv⟩ := hx
  exact ⟨v, hv, hxv.mono hHH'⟩

/-- Membership in the region is open connection to a base vertex. -/
theorem mem_region_iff {ω : G.edgeSet → Bool} {T : Set V} {x : V} :
    x ∈ region G ω T ↔ ∃ b ∈ T, OpenConnected G ω Set.univ b x := by
  rw [region, FK.Finite.Exploration.mem_outerRegion_iff]
  constructor
  · rintro ⟨b, hb, hbx⟩
    exact ⟨b, hb, (reachable_openGraph_openSet_iff ω b x).mp hbx⟩
  · rintro ⟨b, hb, hbx⟩
    exact ⟨b, hb, (reachable_openGraph_openSet_iff ω b x).mpr hbx⟩

/-- Open connection is symmetric. -/
theorem openConnected_symm {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {u v : V}
    (h : OpenConnected G ω A u v) : OpenConnected G ω A v u := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, ?_⟩
  intro d hd
  rw [SimpleGraph.Walk.darts_reverse] at hd
  obtain ⟨d', hd', hd''⟩ := List.mem_reverse.mp hd |> List.mem_map.mp
  subst hd''
  simpa using hp d' hd'

/-- The open subgraph is monotone in the configuration. -/
theorem openSubgraph_mono {ω ω' : G.edgeSet → Bool} (hω : ω ≤ ω') :
    openSubgraph G ω ≤ openSubgraph G ω' := by
  intro x y hxy
  rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj] at hxy ⊢
  obtain ⟨⟨e, he, hee⟩, hne⟩ := hxy
  have hopen : ω' e = true := Bool.le_iff_imp.mp (hω e) he
  exact ⟨⟨e, hopen, hee⟩, hne⟩

/-- The region is monotone in the configuration. -/
theorem region_mono_config {ω ω' : G.edgeSet → Bool} (hω : ω ≤ ω') (T : Set V) :
    region G ω T ⊆ region G ω' T :=
  closedRegion_mono_le (openSubgraph_mono hω) T

/-- The region is monotone in the base set. -/
theorem region_mono_seed {T U : Set V} (h : T ⊆ U) :
    region G ω T ⊆ region G ω U := closedRegion_mono h

/-- The base is contained in its region. -/
theorem subset_region (T : Set V) : T ⊆ region G ω T := subset_closedRegion

/-- Every ambient edge leaving the region is closed. -/
theorem region_closedBoundary (T : Set V) :
    ClosedBoundary G (openSubgraph G ω) (region G ω T) :=
  closedRegion_closedBoundary

/-- The region is the smallest set containing `T` whose outgoing ambient edges
are closed. -/
theorem region_minimal {T S : Set V} (hTS : T ⊆ S)
    (hS : ClosedBoundary G (openSubgraph G ω) S) : region G ω T ⊆ S := by
  intro x hx
  rw [mem_region_iff] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  exact mem_region_of_openConnected hS (hTS hb) hbx

/-- A region based at a finite set is finite when all open clusters are. -/
theorem region_finite {T : Set V} (hT : T.Finite)
    (hfin : FiniteOpenClusters (openSubgraph G ω)) : (region G ω T).Finite :=
  closedRegion_finite hT hfin

/-- A region based at a connected finite set is connected in the ambient
graph. -/
theorem region_connected {T : Set V} (hT : (G.induce T).Connected) :
    (G.induce (region G ω T)).Connected :=
  closedRegion_connected (openGraph_le G ω) hT

/-! ## The explicit exhaustion constructor -/

/-- The explicit region sequence is a `ClosedBoundaryExhaustion`.  This is the
paper's `S_n(ω)`, without a choice of exhaustion. -/
noncomputable def closedBoundaryExhaustionOfRegion
    (hHG : FiniteOpenClusters (openSubgraph G ω)) (T : ℕ → Set V)
    (hTfin : ∀ n, (T n).Finite) (hTconn : ∀ n, (G.induce (T n)).Connected)
    (hTmono : Monotone T) (hTcov : ⋃ n, T n = Set.univ) :
    ClosedBoundaryExhaustion G (openSubgraph G ω) where
  region n := region G ω (T n)
  finite n := region_finite (hTfin n) hHG
  connected n := region_connected (hTconn n)
  closed n := region_closedBoundary (T n)
  monotone m n hmn := region_mono_seed (hTmono hmn)
  exhaustive := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, T n := by rw [hTcov]; exact Set.mem_univ x
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n, subset_region (T n) hxn⟩

@[simp] theorem closedBoundaryExhaustionOfRegion_region
    (hHG : FiniteOpenClusters (openSubgraph G ω)) (T : ℕ → Set V)
    (hTfin : ∀ n, (T n).Finite) (hTconn : ∀ n, (G.induce (T n)).Connected)
    (hTmono : Monotone T) (hTcov : ⋃ n, T n = Set.univ) (n : ℕ) :
    (closedBoundaryExhaustionOfRegion (G := G) (ω := ω) hHG T hTfin hTconn hTmono
      hTcov).region n = region G ω (T n) := rfl

/-! ## Eventual containment

`T` is cofinal, so every fixed finite vertex set is contained in all late
regions.  No finiteness of clusters is needed for this, only the base family. -/

theorem exists_base_mem {T : ℕ → Set V} (hTmono : Monotone T)
    (hTcov : ⋃ n, T n = Set.univ) (x : V) : ∃ N, ∀ n ≥ N, x ∈ T n := by
  have hx : x ∈ ⋃ n, T n := by rw [hTcov]; exact Set.mem_univ x
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
  exact ⟨N, fun n hn => hTmono hn hN⟩

/-- Every fixed finite vertex set is eventually contained in the regions. -/
theorem exists_region_contains (T : ℕ → Set V) (hTmono : Monotone T)
    (hTcov : ⋃ n, T n = Set.univ) {W : Set V} (hW : W.Finite) :
    ∃ N, ∀ n ≥ N, W ⊆ region G ω (T n) := by
  classical
  have h : ∀ x : V, ∃ N, x ∈ W → ∀ n ≥ N, x ∈ T n :=
    fun x => ⟨(exists_base_mem hTmono hTcov x).choose, fun _ n hn =>
      (exists_base_mem hTmono hTcov x).choose_spec n hn⟩
  choose N hN using h
  refine ⟨hW.toFinset.sup N, ?_⟩
  intro n hn x hx
  have hx' : x ∈ hW.toFinset := hW.mem_toFinset.mpr hx
  exact subset_region (T n) (hN x hx n
    (le_trans (Finset.le_sup (s := hW.toFinset) (f := N) hx') hn))

/-- Every vertex set of a `Sym2` is finite. -/
theorem sym2_finite (p : Sym2 V) : {x : V | x ∈ p}.Finite := by
  induction p using Sym2.ind with
  | h a b =>
    have hset : {x : V | x ∈ s(a, b)} = {a, b} := by
      ext x
      simp only [Set.mem_ofPred_eq, Sym2.mem_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
    rw [hset]
    exact Set.toFinite _

/-- In particular every edge of a fixed labelled edge set has both endpoints in
all sufficiently late regions: the interior edge set of the region eventually
contains any fixed finite edge set. -/
theorem exists_edges_inside (T : ℕ → Set V) (hTmono : Monotone T)
    (hTcov : ⋃ n, T n = Set.univ) {F : Set G.edgeSet} (hF : F.Finite) :
    ∃ N, ∀ n ≥ N, ∀ e ∈ F, ∀ x ∈ (e.1 : Sym2 V), x ∈ region G ω (T n) := by
  classical
  set W : Set V := {x | ∃ e ∈ F, x ∈ (e.1 : Sym2 V)} with hWdef
  have hW : W.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion hF (fun e _ => sym2_finite e.1)) ?_
    rintro x ⟨e, he, hx⟩
    exact Set.mem_iUnion₂.mpr ⟨e, he, hx⟩
  obtain ⟨N, hN⟩ := exists_region_contains (G := G) (ω := ω) T hTmono hTcov hW
  refine ⟨N, ?_⟩
  intro n hn e he x hx
  exact hN n hn ⟨e, he, hx⟩


/-! ## Measurability: the region map is a random variable

The only measurability input is the library lemma
`measurableSet_exists_openConnected`: on a countable vertex type, "there is an
open walk from `x` to some vertex of `T`" is measurable.  Everything else is
countable set algebra, so no measurability of a chosen exhaustion is assumed. -/

section Measurable

variable [Countable V]

/-- Membership in the region is a measurable event. -/
theorem measurableSet_mem_region (T : Set V) (x : V) :
    MeasurableSet {ω : G.edgeSet → Bool | x ∈ region G ω T} := by
  have h : {ω : G.edgeSet → Bool | x ∈ region G ω T} =
      {ω | ∃ b ∈ T, OpenConnected G ω Set.univ x b} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [mem_region_iff]
    constructor
    · rintro ⟨b, hb, hbx⟩
      exact ⟨b, hb, openConnected_symm hbx⟩
    · rintro ⟨b, hb, hxb⟩
      exact ⟨b, hb, openConnected_symm hxb⟩
  rw [h]
  exact measurableSet_exists_openConnected Set.univ x T

/-- Containment of the region in a fixed set is a measurable event. -/
theorem measurableSet_region_subset (T S : Set V) :
    MeasurableSet {ω : G.edgeSet → Bool | region G ω T ⊆ S} := by
  have h : {ω : G.edgeSet → Bool | region G ω T ⊆ S} =
      ⋂ x : ↥Sᶜ, {ω | (x : V) ∉ region G ω T} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.subset_def, Set.mem_iInter]
    constructor
    · intro h x hx
      exact x.2 (h (x : V) hx)
    · intro h x hx
      by_contra hxS
      exact h ⟨x, hxS⟩ hx
  rw [h]
  exact MeasurableSet.iInter fun x => (measurableSet_mem_region T (x : V)).compl

/-- Every stratum of the region map is measurable.  This is the statement that
`ω ↦ S(ω)` is a genuine random variable with countably supported law. -/
theorem measurableSet_region_eq (T S : Set V) :
    MeasurableSet {ω : G.edgeSet → Bool | region G ω T = S} := by
  have h : {ω : G.edgeSet → Bool | region G ω T = S} =
      {ω | region G ω T ⊆ S} ∩ ⋂ x : ↥S, {ω | (x : V) ∈ region G ω T} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro rfl
      exact ⟨fun _ h => h, fun x => x.2⟩
    · rintro ⟨hsub, hin⟩
      exact Set.Subset.antisymm hsub fun x hx => hin ⟨x, hx⟩
  rw [h]
  exact (measurableSet_region_subset T S).inter
    (MeasurableSet.iInter fun x => measurableSet_mem_region T (x : V))

/-- The region map itself is measurable: `ω ↦ region G ω T` is a random
variable with values in the measurable space of subsets of `V`. -/
theorem measurable_region (T : Set V) :
    Measurable fun ω : G.edgeSet → Bool => region G ω T := by
  rw [measurable_set_iff]
  intro x
  exact measurableSet_setOfPred.mp (measurableSet_mem_region T x)

end Measurable

/-! ## Almost-sure exhaustion properties -/

section AlmostSure

variable {μ : Measure (G.edgeSet → Bool)}

/-- Almost surely the explicit region sequence is a finite, connected,
closed-boundary, monotone, exhaustive family, with a single null set. -/
theorem ae_exhaustion [IsProbabilityMeasure μ]
    (T : ℕ → Set V) (hTfin : ∀ n, (T n).Finite)
    (hTconn : ∀ n, (G.induce (T n)).Connected)
    (hTmono : Monotone T) (hTcov : ⋃ n, T n = Set.univ)
    (hfin : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    ∀ᵐ ω ∂μ, (∀ n, (region G ω (T n)).Finite) ∧
      (∀ n, ClosedBoundary G (openSubgraph G ω) (region G ω (T n))) ∧
      (∀ n, (G.induce (region G ω (T n))).Connected) ∧
      (∀ {m n : ℕ}, m ≤ n → region G ω (T m) ⊆ region G ω (T n)) ∧
      (⋃ n, region G ω (T n) = Set.univ) := by
  filter_upwards [hfin] with ω hω
  have hfinc : FiniteOpenClusters (openSubgraph G ω) :=
    finiteOpenClusters_of_nonPercolating G ω hω
  refine ⟨fun n => region_finite (hTfin n) hfinc,
    fun n => region_closedBoundary (T n),
    fun n => region_connected (hTconn n),
    fun hmn => region_mono_seed (hTmono hmn), ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ n, T n := by rw [hTcov]; exact Set.mem_univ x
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n, subset_region (T n) hxn⟩

/-- For a fixed finite vertex set, containment holds eventually off *no* extra
null set: it is a deterministic consequence of cofinality of the bases.  The
countable family version keeps one null set for countably many test sets. -/
theorem ae_eventually_contains_family [IsProbabilityMeasure μ]
    (T : ℕ → Set V) (hTmono : Monotone T) (hTcov : ⋃ n, T n = Set.univ)
    (W : ℕ → Set V) (hW : ∀ k, (W k).Finite) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ N, ∀ n ≥ N, W k ⊆ region G ω (T n) := by
  have h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ N, ∀ n ≥ N, W k ⊆ region G ω (T n) :=
    fun k => Filter.Eventually.of_forall
      (fun ω => exists_region_contains (G := G) (ω := ω) T hTmono hTcov (hW k))
  rw [MeasureTheory.ae_all_iff]
  exact h

end AlmostSure

/-! ## Strata and the finite-stack identity -/

/-- The stratum of configurations whose region is exactly `S`. -/
def stratum (G : SimpleGraph V) (T S : Set V) : Set (G.edgeSet → Bool) :=
  {ω | region G ω T = S}

theorem stratum_pairwise_disjoint (G : SimpleGraph V) (T : Set V) :
    Pairwise (Function.onFun (fun A B : Set (G.edgeSet → Bool) => Disjoint A B)
      (stratum G T)) := by
  intro S S' hSS'
  rw [Function.onFun, Set.disjoint_left]
  intro ω hωS hωS'
  exact hSS' (hωS.symm.trans hωS')

/-- The configurations whose (finite) region is contained in `S` are exactly
the disjoint union of the strata over the finite subsets of `S`. -/
theorem region_subset_eq_iUnion_stratum (G : SimpleGraph V) (T : Set V) {S : Set V}
    (hS : S.Finite) :
    {ω : G.edgeSet → Bool | region G ω T ⊆ S ∧ (region G ω T).Finite} =
      ⋃ S' ∈ hS.toFinset.powerset, stratum G T (S' : Set V) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_powerset, stratum]
  constructor
  · rintro ⟨hsub, hfin⟩
    refine ⟨hfin.toFinset, ?_, (hfin.coe_toFinset).symm⟩
    intro x hx
    exact hS.mem_toFinset.mpr (hsub (hfin.mem_toFinset.mp hx))
  · rintro ⟨S', hS', hreg⟩
    constructor
    · intro x hx
      rw [hreg] at hx
      exact hS.mem_toFinset.mp (hS' (Finset.mem_coe.mpr hx))
    · rw [hreg]
      exact S'.finite_toSet


/-! ## Closed boundaries induce the free boundary condition

The paper's step "`ω|∂Λ = 0` makes the boundary partition of the box discrete"
is proved here in the form actually needed: the setoid of exterior-open
connections between vertices of the closed region is the equality setoid, so
the boundary condition induced by `ω` is the free one.  The statement is
configuration-level and uses the actual open walks. -/

/-- Edges that are not interior to `S`: some endpoint lies outside `S`. -/
def nonInteriorEdges (S : Set V) : Set (Sym2 V) := {p | ∃ x ∈ p, x ∉ S}

theorem mem_nonInteriorEdges_iff {S : Set V} {p : Sym2 V} :
    p ∈ nonInteriorEdges S ↔ ∃ x ∈ p, x ∉ S := Iff.rfl

theorem not_mem_nonInteriorEdges_of_forall {S : Set V} {p : Sym2 V}
    (h : ∀ x ∈ p, x ∈ S) : p ∉ nonInteriorEdges S := by
  intro hp
  obtain ⟨x, hx, hxS⟩ := mem_nonInteriorEdges_iff.mp hp
  exact hxS (h x hx)

/-- An open walk inside the non-interior edges starting in `S` stays in `S`:
leaving `S` would cross a closed edge. -/
theorem mem_of_isOpenIn_nonInterior {S : Set V}
    (hS : ClosedBoundary G (openSubgraph G ω) S) {a : V} (ha : a ∈ S)
    {b : V} {p : G.Walk a b} (hp : IsOpenIn ω (nonInteriorEdges S) p) : b ∈ S := by
  induction p with
  | nil => exact ha
  | @cons a b c hab q ih =>
    rw [isOpenIn_cons] at hp
    refine ih ?_ hp.2
    by_contra hb
    exact hS ha hb hab (by
      rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨⟨s(a, b), hab⟩, hp.1.2, rfl⟩, G.ne_of_adj hab⟩)

/-- An open walk inside the non-interior edges cannot join two distinct
vertices of the closed region: every step between two region vertices is an
interior edge, which is excluded. -/
theorem eq_of_isOpenIn_nonInterior {S : Set V}
    (hS : ClosedBoundary G (openSubgraph G ω) S) {a : V} (ha : a ∈ S)
    {b : V} {p : G.Walk a b} (hp : IsOpenIn ω (nonInteriorEdges S) p) : a = b := by
  induction p with
  | nil => rfl
  | @cons a b c hab q ih =>
    rw [isOpenIn_cons] at hp
    have hb : b ∈ S := by
      by_contra hb
      exact hS ha hb hab (by
        rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨⟨s(a, b), hab⟩, hp.1.2, rfl⟩, G.ne_of_adj hab⟩)
    have hall : ∀ x ∈ (s(a, b) : Sym2 V), x ∈ S := by
      intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    exact absurd hp.1.1 (not_mem_nonInteriorEdges_of_forall hall)

/-- **The paper's boundary step.**  If every ambient edge leaving `S` is closed
in `ω`, the setoid of exterior-open connections between vertices of `S` is
discrete, i.e. the boundary condition induced by `ω` on `S` is free. -/
theorem exteriorOpenSetoid_eq_bot {S : Set V}
    (hS : ClosedBoundary G (openSubgraph G ω) S) :
    FK.InfiniteVolume.ConventionGeometry.exteriorOpenSetoid (S := S) G ω
      (nonInteriorEdges S) = ⊥ := by
  apply Setoid.ext
  intro x y
  constructor
  · intro hxy
    rw [Setoid.bot_def]
    obtain ⟨p, hp⟩ := hxy
    exact Subtype.ext (eq_of_isOpenIn_nonInterior hS x.2 hp)
  · rintro rfl
    exact OpenConnected.refl ω (nonInteriorEdges S) (x : V)

/-- An open walk starting outside a closed-boundary set stays outside. -/
theorem notMem_of_isOpenIn_of_notMem {S : Set V}
    (hS : ClosedBoundary G (openSubgraph G ω) S) {a : V} (ha : a ∉ S)
    {b : V} {p : G.Walk a b} (hp : IsOpenIn ω Set.univ p) : b ∉ S := by
  induction p with
  | nil => exact ha
  | @cons a b c hab q ih =>
    rw [isOpenIn_cons] at hp
    refine ih ?_ hp.2
    by_contra hb
    exact hS hb ha hab.symm (by
      rw [openSubgraph, openGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨⟨s(a, b), hab⟩, hp.1.2, Sym2.eq_swap⟩, (G.ne_of_adj hab).symm⟩)

/-! ## Stacking identities for sequential exploration -/

/-- Exploration is additive over unions of bases. -/
theorem region_union (T U : Set V) :
    region G ω (T ∪ U) = region G ω T ∪ region G ω U := by
  ext x
  rw [Set.mem_union, mem_region_iff, mem_region_iff, mem_region_iff]
  constructor
  · rintro ⟨b, hb | hb, hbx⟩
    · exact Or.inl ⟨b, hb, hbx⟩
    · exact Or.inr ⟨b, hb, hbx⟩
  · rintro (⟨b, hb, hbx⟩ | ⟨b, hb, hbx⟩)
    · exact ⟨b, Or.inl hb, hbx⟩
    · exact ⟨b, Or.inr hb, hbx⟩

/-- A closed-boundary set is a union of open clusters, hence its own region. -/
theorem region_eq_self_of_closed {S : Set V}
    (hS : ClosedBoundary G (openSubgraph G ω) S) : region G ω S = S :=
  Set.Subset.antisymm (region_minimal (Set.Subset.refl S) hS) (subset_region S)

/-- Adding seeds inside an exhausted closed region does not enlarge it. -/
theorem region_union_of_closed {S U : Set V}
    (hS : ClosedBoundary G (openSubgraph G ω) S) :
    region G ω (S ∪ U) = S ∪ region G ω U := by
  rw [region_union, region_eq_self_of_closed hS]

/-- Exploration started outside a closed region never enters it: the second
exploration stage is disjoint from the exhausted first stage. -/
theorem disjoint_region_of_subset_compl {S U : Set V} (hU : U ⊆ Sᶜ)
    (hS : ClosedBoundary G (openSubgraph G ω) S) : Disjoint (region G ω U) S := by
  rw [Set.disjoint_left]
  intro x hx hxS
  rw [mem_region_iff] at hx
  obtain ⟨b, hb, hbx⟩ := hx
  obtain ⟨p, hp⟩ := hbx
  exact notMem_of_isOpenIn_of_notMem hS (fun hbS => hU hb hbS) hp hxS

/-! ## The exhaustion chosen from the dominating configuration -/

/-- Closedness passes from the dominating configuration to a dominated one. -/
theorem closedBoundary_of_le {ω ω' : G.edgeSet → Bool} (hω : ω ≤ ω')
    {S : Set V} (hS : ClosedBoundary G (openSubgraph G ω') S) :
    ClosedBoundary G (openSubgraph G ω) S :=
  ClosedBoundary.mono (openSubgraph_mono hω) hS

/-- The region explored from the dominating configuration has closed boundary
for every dominated configuration: this is `ωᵢ|∂S_n(ω₃) = 0` of Theorem 5.1. -/
theorem region_closedBoundary_of_le {ω ω' : G.edgeSet → Bool} (hω : ω ≤ ω')
    (T : Set V) : ClosedBoundary G (openSubgraph G ω) (region G ω' T) :=
  closedBoundary_of_le hω (region_closedBoundary (G := G) (ω := ω') T)

/-- Consequently the boundary condition induced on the upper region by a
dominated configuration is free. -/
theorem exteriorOpenSetoid_upperRegion_eq_bot {ω ω' : G.edgeSet → Bool}
    (hω : ω ≤ ω') (T : Set V) :
    FK.InfiniteVolume.ConventionGeometry.exteriorOpenSetoid
      (S := region G ω' T) G ω (nonInteriorEdges (region G ω' T)) = ⊥ :=
  exteriorOpenSetoid_eq_bot (region_closedBoundary_of_le hω T)

/-- Almost surely in an ordered triple coupling, the exhaustion built from the
dominating coordinate has closed boundary for *both* dominated coordinates, so
both conditional laws at that region are free.  One null set suffices: the
statement is deterministic given the order relation. -/
theorem ae_upper_region_closed_for_lower
    {Ω : Type*} [MeasurableSpace Ω]
    {ω₁ ω₂ ω₃ : Ω → G.edgeSet → Bool}
    {τ : Measure Ω} [IsProbabilityMeasure τ]
    (hord : ∀ᵐ z ∂τ, ω₁ z ≤ ω₃ z ∧ ω₂ z ≤ ω₃ z) (T : Set V) :
    ∀ᵐ z ∂τ, ClosedBoundary G (openSubgraph G (ω₁ z)) (region G (ω₃ z) T) ∧
      ClosedBoundary G (openSubgraph G (ω₂ z)) (region G (ω₃ z) T) := by
  filter_upwards [hord] with z hz
  exact ⟨region_closedBoundary_of_le hz.1 T, region_closedBoundary_of_le hz.2 T⟩


/-! ## The stratum decomposition of the random region

Almost surely the region is a finite set, so the law of the random region is
carried by the countably many finite subsets of `V`.  This is the fibre
decomposition over which the conditional reverse convergence along
`n ↦ region G ω (base n)` runs. -/

section StratumMeasure

variable [Countable V]

/-- The random region is almost surely a finite set, hence a `Finset`. -/
theorem ae_region_finset {μ : Measure (G.edgeSet → Bool)} (T : Set V)
    (hreg : ∀ᵐ ω ∂μ, (region G ω T).Finite) :
    ∀ᵐ ω ∂μ, ∃ s : Finset V, (s : Set V) = region G ω T := by
  filter_upwards [hreg] with ω hω
  exact ⟨hω.toFinset, hω.coe_toFinset⟩

/-- The random region decomposes any measurable event into the countably many
strata of finite regions. -/
theorem measure_eq_tsum_finset {μ : Measure (G.edgeSet → Bool)} (T : Set V)
    (hreg : ∀ᵐ ω ∂μ, (region G ω T).Finite)
    (A : Set (G.edgeSet → Bool)) (hA : MeasurableSet A) :
    μ A = ∑' s : Finset V, μ (A ∩ stratum G T (s : Set V)) := by
  classical
  have hcover : A =ᵐ[μ] ⋃ s : Finset V, A ∩ stratum G T (s : Set V) := by
    filter_upwards [hreg] with ω hω
    apply propext
    simp only [Set.mem_iUnion, Set.mem_inter_iff, stratum, Set.mem_ofPred_eq]
    constructor
    · intro hAω
      exact ⟨hω.toFinset, hAω, (hω.coe_toFinset).symm⟩
    · rintro ⟨s, hAω, -⟩
      exact hAω
  rw [MeasureTheory.measure_congr hcover]
  have hdisj : Pairwise (Function.onFun (fun X Y : Set (G.edgeSet → Bool) => Disjoint X Y)
      (fun s : Finset V => A ∩ stratum G T (s : Set V))) := by
    intro s t hst
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    exact hst (Finset.coe_injective (hω.2.symm.trans hω'.2))
  have hmeas : ∀ s : Finset V, MeasurableSet (A ∩ stratum G T (s : Set V)) :=
    fun s => hA.inter (measurableSet_region_eq T (s : Set V))
  exact MeasureTheory.measure_iUnion hdisj hmeas

end StratumMeasure

end FK.RandomClosedBoundary

/-! ## Axiom audit -/

#print axioms FK.RandomClosedBoundary.openConnected_symm
#print axioms FK.RandomClosedBoundary.mem_region_iff
#print axioms FK.RandomClosedBoundary.region_closedBoundary
#print axioms FK.RandomClosedBoundary.region_minimal
#print axioms FK.RandomClosedBoundary.region_finite
#print axioms FK.RandomClosedBoundary.region_connected
#print axioms FK.RandomClosedBoundary.closedBoundaryExhaustionOfRegion
#print axioms FK.RandomClosedBoundary.exists_region_contains
#print axioms FK.RandomClosedBoundary.exists_edges_inside
#print axioms FK.RandomClosedBoundary.measurableSet_mem_region
#print axioms FK.RandomClosedBoundary.measurableSet_region_subset
#print axioms FK.RandomClosedBoundary.measurableSet_region_eq
#print axioms FK.RandomClosedBoundary.measurable_region
#print axioms FK.RandomClosedBoundary.ae_exhaustion
#print axioms FK.RandomClosedBoundary.ae_eventually_contains_family
#print axioms FK.RandomClosedBoundary.region_subset_eq_iUnion_stratum
#print axioms FK.RandomClosedBoundary.eq_of_isOpenIn_nonInterior
#print axioms FK.RandomClosedBoundary.exteriorOpenSetoid_eq_bot
#print axioms FK.RandomClosedBoundary.region_union_of_closed
#print axioms FK.RandomClosedBoundary.disjoint_region_of_subset_compl
#print axioms FK.RandomClosedBoundary.region_closedBoundary_of_le
#print axioms FK.RandomClosedBoundary.exteriorOpenSetoid_upperRegion_eq_bot
#print axioms FK.RandomClosedBoundary.ae_upper_region_closed_for_lower
#print axioms FK.RandomClosedBoundary.ae_region_finset
#print axioms FK.RandomClosedBoundary.measure_eq_tsum_finset
