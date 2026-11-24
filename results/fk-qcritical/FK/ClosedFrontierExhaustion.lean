import FK.UniformUpcrossing
import CurvatureVariance.Infra.Percolation.Connections

/-!
# The source's closed-frontier exhaustion `Ω̃`

`arXiv:2512.16486v1`, proof of Theorem 5.1: *"Let `Ω̃` denote the set of
configurations such that we can find an increasing sequence `S_n = S_n(ω₃) ⊂ ℤ²`
of connected subgraphs of `G` such that `S_n ↑ G` and `ω₃|_{∂S_n} = 0`. By
subcriticality of `ℙ`, it follows that `ℙ(Ω̃) = 1`."*

This file supplies the geometric core of that statement on an arbitrary
`SimpleGraph V` (no planarity, no local finiteness, no `ℤ²` structure is used):
given a configuration `ω` with finite clusters and a monotone cofinal vertex
exhaustion `V_n`, the union `reachUnion ω V_n` of the clusters of `V_n` is

* monotone in `n` (`monotone_reachUnion`),
* cofinal: every edge whose endpoints are eventually in `V_n` lies in the
  corresponding region (`regionSet_cofinal`),
* of **closed frontier**: an open edge with one endpoint in `reachUnion ω V_n`
  has its other endpoint there too (`open_edge_endpoints_mem_reachUnion`), i.e.
  no open edge leaves the region, which is the source's `ω|_{∂S_n} = 0`,
* measurable in `ω` at each vertex (`measurableSet_mem_reachUnion`), using
  `CurvatureVariance.Infra.Percolation.measurableSet_openConnected`.

Connectivity is *not* claimed (and is not used by the argument): the union of
several disjoint clusters is a legitimate region as long as no open edge leaves
it. The region is finite when all clusters are finite. The additional
packaging as a `Finset`-valued measurable map is not carried out here.
-/

open Set
open CurvatureVariance.Infra.Percolation

namespace FK

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V] {G : SimpleGraph V}

/-- The union of the open clusters of the vertices of `Vn`: the vertex set
reached from `Vn` by open paths. -/
def reachUnion (ω : G.edgeSet → Bool) (Vn : Finset V) : Set V :=
  ⋃ v ∈ (Vn : Set V), {u : V | OpenConnected G ω Set.univ v u}

/-- Auxiliary: every unordered pair is of the form `s(a, b)`. -/
lemma sym2_exists_eq_mk (s : Sym2 V) : ∃ a b : V, s = s(a, b) := by
  induction s using Sym2.ind with
  | h a b => exact ⟨a, b, rfl⟩

/-- Auxiliary: an unordered pair containing two distinct vertices `v ≠ w` is
`s(v, w)`. -/
lemma sym2_eq_mk_of_mem {v w : V} {s : Sym2 V} (hv : v ∈ s) (hw : w ∈ s) (hne : v ≠ w) :
    s = s(v, w) := by
  obtain ⟨a, b, rfl⟩ := sym2_exists_eq_mk s
  rw [Sym2.mem_iff] at hv hw
  rcases hv with hva | hvb
  · rcases hw with hwa | hwb
    · exact absurd (hva.trans hwa.symm) hne
    · rw [hva, hwb]
  · rcases hw with hwa | hwb
    · rw [hvb, hwa, Sym2.eq_swap]
    · exact absurd (hvb.trans hwb.symm) hne

lemma mem_reachUnion {ω : G.edgeSet → Bool} {Vn : Finset V} {u : V} :
    u ∈ reachUnion ω Vn ↔ ∃ v ∈ (Vn : Set V), OpenConnected G ω Set.univ v u := by
  simp only [reachUnion, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, h⟩

lemma reachUnion_mono {ω : G.edgeSet → Bool} {Vm Vn : Finset V} (h : Vm ⊆ Vn) :
    reachUnion ω Vm ⊆ reachUnion ω Vn := by
  intro u hu
  obtain ⟨v, hv, hc⟩ := mem_reachUnion.1 hu
  exact mem_reachUnion.2 ⟨v, h hv, hc⟩

/-- Members of `Vn` lie in their own cluster, hence in the region. -/
lemma self_mem_reachUnion {ω : G.edgeSet → Bool} {Vn : Finset V} {v : V}
    (hv : v ∈ (Vn : Set V)) : v ∈ reachUnion ω Vn :=
  mem_reachUnion.2 ⟨v, hv, OpenConnected.refl ω Set.univ v⟩

/-- The region membership of a fixed vertex is a measurable event. -/
theorem measurableSet_mem_reachUnion (Vn : Finset V) (u : V) :
    MeasurableSet {ω : G.edgeSet → Bool | u ∈ reachUnion ω Vn} := by
  have h : {ω : G.edgeSet → Bool | u ∈ reachUnion ω Vn} =
      ⋃ v ∈ (Vn : Set V), {ω : G.edgeSet → Bool | OpenConnected G ω Set.univ v u} := by
    ext ω
    simp only [reachUnion, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [h]
  exact MeasurableSet.biUnion (Set.to_countable (Vn : Set V)) fun v _ ↦
    measurableSet_openConnected Set.univ v u

/-- The edge region: all edges of `G` both of whose endpoints lie in
`reachUnion ω Vn`. -/
def regionSet (ω : G.edgeSet → Bool) (Vn : Finset V) : Set G.edgeSet :=
  {e | ∀ v : V, v ∈ (e.1 : Sym2 V) → v ∈ reachUnion ω Vn}

/-- **The frontier is closed.**  An open edge of `G` with one endpoint in the
region has both endpoints in it: there is no open edge leaving the region.  This
is the source's condition `ω|_{∂S_n} = 0`. -/
theorem open_edge_endpoints_mem_reachUnion {ω : G.edgeSet → Bool} {Vn : Finset V}
    {e : G.edgeSet} {v w : V} (hv : v ∈ (e.1 : Sym2 V)) (hw : w ∈ (e.1 : Sym2 V))
    (hreg : v ∈ reachUnion ω Vn) (hopen : ω e = true) :
    w ∈ reachUnion ω Vn := by
  obtain ⟨x, hx, hxc⟩ := mem_reachUnion.1 hreg
  rcases eq_or_ne v w with hvw | hvw
  · exact hvw ▸ hreg
  have hadj : G.Adj v w :=
    SimpleGraph.adj_iff_exists_edge.2 ⟨hvw, ⟨(e.1 : Sym2 V), e.2, hv, hw⟩⟩
  have hEq : s(v, w) = (e.1 : Sym2 V) := (sym2_eq_mk_of_mem hv hw hvw).symm
  have hsub : (⟨s(v, w), hadj⟩ : G.edgeSet) = e := Subtype.ext hEq
  have hopen' : ω ⟨s(v, w), hadj⟩ = true := by rw [hsub]; exact hopen
  exact mem_reachUnion.2 ⟨x, hx,
    hxc.trans (OpenConnected.of_adj hadj (mem_univ _) hopen')⟩

/-- Monotonicity of the edge regions in the vertex exhaustion. -/
lemma regionSet_mono {ω : G.edgeSet → Bool} {Vm Vn : Finset V} (h : Vm ⊆ Vn) :
    regionSet ω Vm ⊆ regionSet ω Vn :=
  fun _ he v hv ↦ reachUnion_mono h (he v hv)

/-- Cofinality: an edge whose endpoints lie in `Vn` belongs to the region of
`Vn`. -/
lemma mem_regionSet_of_endpoints {ω : G.edgeSet → Bool} {Vn : Finset V} {e : G.edgeSet}
    (h : ∀ v : V, v ∈ (e.1 : Sym2 V) → v ∈ (Vn : Set V)) : e ∈ regionSet ω Vn :=
  fun v hv ↦ self_mem_reachUnion (h v hv)

/-- Every edge lies in the region of a late enough member of a monotone cofinal
vertex exhaustion. -/
lemma regionSet_cofinal {ω : G.edgeSet → Bool} {Vn : ℕ → Finset V} (hmono : Monotone Vn)
    (hcof : ∀ v : V, ∃ n, v ∈ (Vn n : Set V)) (e : G.edgeSet) :
    ∃ n, e ∈ regionSet ω (Vn n) := by
  classical
  obtain ⟨a, b, hab⟩ := sym2_exists_eq_mk (e.1 : Sym2 V)
  have ha : a ∈ (e.1 : Sym2 V) := by rw [hab]; exact Sym2.mem_mk_left a b
  have hb : b ∈ (e.1 : Sym2 V) := by rw [hab]; exact Sym2.mem_mk_right a b
  obtain ⟨m, hm⟩ := hcof a
  obtain ⟨n, hn⟩ := hcof b
  refine ⟨max m n, mem_regionSet_of_endpoints fun v hv ↦ ?_⟩
  rw [hab] at hv
  rcases Sym2.mem_iff.1 hv with hva | hvb
  · rw [hva]
    exact hmono (le_max_left m n) hm
  · rw [hvb]
    exact hmono (le_max_right m n) hn


/-- **Finiteness of the region.**  If every cluster is finite, then the union of
the clusters of the finite set `Vn` is finite, hence the region, which consists
of edges with both endpoints in that union, is a finite edge set.  (A
`SimpleGraph` has at most one edge per unordered pair, so the edges inside a
finite vertex set are finite.) -/
theorem reachUnion_finite {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) :
    (reachUnion ω Vn).Finite := by
  have h : reachUnion ω Vn = ⋃ v ∈ (Vn : Set V),
      {u : V | OpenConnected G ω Set.univ v u} := rfl
  rw [h]
  exact Set.Finite.biUnion Vn.finite_toSet fun v _ ↦ hfin v

theorem regionSet_finite {ω : G.edgeSet → Bool} {Vn : Finset V}
    (hfin : ∀ v : V, {u : V | OpenConnected G ω Set.univ v u}.Finite) :
    (regionSet ω Vn).Finite := by
  have hU : (reachUnion ω Vn).Finite := reachUnion_finite hfin
  have himg : ((fun p : V × V ↦ s(p.1, p.2)) ''
      (reachUnion ω Vn ×ˢ reachUnion ω Vn)).Finite :=
    (hU.prod hU).image _
  refine Set.Finite.of_injOn (f := (Subtype.val : G.edgeSet → Sym2 V)) ?_ ?_ himg
  · intro e he
    obtain ⟨a, b, hab⟩ := sym2_exists_eq_mk (e.1 : Sym2 V)
    have ha : a ∈ (e.1 : Sym2 V) := by rw [hab]; exact Sym2.mem_mk_left a b
    have hb : b ∈ (e.1 : Sym2 V) := by rw [hab]; exact Sym2.mem_mk_right a b
    have hmem : (a, b) ∈ (reachUnion ω Vn ×ˢ reachUnion ω Vn : Set (V × V)) :=
      Set.mem_prod.2 ⟨he a ha, he b hb⟩
    have hthis := Set.mem_image_of_mem (fun p : V × V ↦ s(p.1, p.2)) hmem
    simp only [Prod.fst, Prod.snd] at hthis
    rwa [← hab] at hthis
  · intro e₁ _ e₂ _ h
    exact Subtype.ext h


end FK


#print axioms FK.measurableSet_mem_reachUnion
#print axioms FK.open_edge_endpoints_mem_reachUnion
#print axioms FK.regionSet_cofinal
#print axioms FK.regionSet_finite
