import FK.SeparatorCircuits
import FK.StaircaseConnected

/-!
# Vertex-sealed open circuits: the crossing-control field is not obtainable

`FK.SeparatorCircuits` isolates the Jordan-type input of the planar
dual-nonpercolation argument as a `TwoSidedSeparation` together with a
`SeparatorOpenCircuit`: a label set `C` which *controls the crossings* of the
barrier `K`, i.e. every edge arc meeting `K` carries a label of `C`.

This module shows that this crossing-control field is strictly too strong to be
derived from dual nonpercolation, and that it is not needed:

* `SealedOpenCircuit` replaces `CrossingControlledBy` by the per-edge condition
  that an edge whose arc meets `K` either belongs to `C` or has an endpoint
  incident to `C`.  This is satisfied by a grid cycle whose edges are open in a
  configuration where a closed ray leaves one of its vertices.
* `globalAtMostOne_of_sealedCircuitExhaustion`: a cofinal family of sealed
  circuits still joins any two infinite open components.
* `staircase_no_separatorCircuitExhaustion`: in the staircase configuration of
  `FK.PlanarTarget` (no infinite dual-open cluster, `GlobalAtMostOne`), **no**
  crossing-controlled separator circuit exhaustion exists, for any centre.
  Hence the crossing-control field cannot be produced from dual
  nonpercolation on the square lattice at all.
* `hasSealedCircuitExhaustion_staircase`: the sealed interface, by contrast, is
  inhabited in that very configuration by the boundaries of the `ℓ^∞` boxes.
  So the strict interface fails exactly where the sealed one holds.

The remaining planar obligation is unchanged: dual nonpercolation must still
produce a cofinal enclosing *cycle* in the primal graph.  What is established
here is which of the hypotheses on such a cycle are sharp necessities.
-/

namespace FK.PlaneTopology.SealedSeparation

open Set Metric unitInterval
open scoped Topology
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology
open FK.PlaneTopology.GridFrontier
open FK.PlaneTopology.PlanarTarget
open FK.PlaneTopology.StaircaseConnected
open FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon (straightPath)

/-! ## Sealed circuits -/

variable {V X : Type*} [TopologicalSpace X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- A primal circuit carrier on a two-sided separator, sealed at vertices.

Compared with `SeparatorOpenCircuit` the field `crossing` is replaced by
`sealed`: an edge whose realised arc meets the barrier may also be accounted
for by one of its endpoints being incident to a circuit label.  A path crossing
the barrier at such a vertex still passes through a circuit vertex, hence
through the circuit's open component, so no strength is lost in the argument.
-/
structure SealedOpenCircuit (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool)
    (C : Set G.edgeSet) (S : TwoSidedSeparation X) : Prop where
  /-- The circuit labels are open. -/
  label_open : ∀ e ∈ C, ω e = true
  /-- The vertices incident to `C` are open-connected through `C` alone. -/
  openConnected : OpenLabelConnected G ω C
  /-- Sealing: an edge meeting the barrier is a circuit label or meets the
  circuit at an endpoint. -/
  sealed : ∀ {u v : V} (h : G.Adj u v),
    (∃ t : I, R.arc h t ∈ S.K) →
      ((⟨s(u, v), h⟩ : G.edgeSet) ∈ C ∨ VertexOnLabels C u ∨ VertexOnLabels C v)

namespace SealedOpenCircuit

variable {R : OpenPathRealization G vertex} {ω : G.edgeSet → Bool} {C : Set G.edgeSet}
  {S : TwoSidedSeparation X}

/-- Walk induction for a sealed circuit: an open walk either stays inside the
separator or reaches a vertex incident to a circuit label. -/
theorem mem_inside_or_exists_vertexOnLabels_of_walk (hcirc : SealedOpenCircuit R ω C S)
    {x y : V} (p : G.Walk x y) (hp : IsOpenIn ω Set.univ p) (hx : vertex x ∈ S.inside) :
    vertex y ∈ S.inside ∨
      ∃ u : V, VertexOnLabels C u ∧ OpenConnected G ω Set.univ x u := by
  induction p with
  | nil => exact Or.inl hx
  | @cons a b y hab p ih =>
      have hparts := isOpenIn_cons.mp hp
      by_cases hc : ∃ t : I, R.arc hab t ∈ S.K
      · rcases hcirc.sealed hab hc with hedge | hu | hv
        · exact Or.inr ⟨a, ⟨b, hab, hedge⟩, OpenConnected.refl ω Set.univ a⟩
        · exact Or.inr ⟨a, hu, OpenConnected.refl ω Set.univ a⟩
        · exact Or.inr ⟨b, hv, OpenConnected.of_adj hab (Set.mem_univ _) hparts.1.2⟩
      · have hjoined : JoinedIn S.Kᶜ (vertex a) (vertex b) := by
          refine ⟨R.arc hab, fun t => ?_⟩
          change R.arc hab t ∉ S.K
          intro ht
          exact hc ⟨t, ht⟩
        have hb : vertex b ∈ S.inside := by
          rcases S.cover hjoined.target_mem with h | h
          · exact h
          · exact absurd hjoined (S.separated hx h)
        rcases ih hparts.2 hb with hy | ⟨u, hu, hbu⟩
        · exact Or.inl hy
        · exact Or.inr ⟨u, hu,
            (OpenConnected.of_adj hab (Set.mem_univ _) hparts.1.2).trans hbu⟩

/-- An open walk from the inside of a sealed separator to a point outside it
reaches a vertex incident to a circuit label. -/
theorem exists_vertexOnLabels_of_openConnected_inside_outside
    (hcirc : SealedOpenCircuit R ω C S)
    {x y : V} (hxy : OpenConnected G ω Set.univ x y)
    (hx : vertex x ∈ S.inside) (hy : vertex y ∈ S.outside) (hyK : vertex y ∈ S.Kᶜ) :
    ∃ u : V, VertexOnLabels C u ∧ OpenConnected G ω Set.univ x u := by
  obtain ⟨p, hp⟩ := hxy
  rcases hcirc.mem_inside_or_exists_vertexOnLabels_of_walk p hp hx with hin | h
  · exact (S.separated hin hy (JoinedIn.refl hyK)).elim
  · exact h

end SealedOpenCircuit

section SealedAssembly

variable {V X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : SimpleGraph V} {vertex : V → X}
variable {ω : G.edgeSet → Bool} {C : Set G.edgeSet} {S : TwoSidedSeparation X}

/-- A crossing-controlled separator circuit is a sealed one. -/
theorem sealedOpenCircuit_of_separatorOpenCircuit
    (h : SeparatorOpenCircuit (G := G) (vertex := vertex) R ω C S) :
    SealedOpenCircuit R ω C S where
  label_open := h.label_open
  openConnected := h.openConnected
  sealed := fun {u v} hab hc => Or.inl (h.crossing hab hc)

/-- **Two infinite components inside a sealed separator are joined.**  Compared
with `openConnected_of_two_infinite_of_separatorOpenCircuit` this uses no
vertex-off hypothesis; instead finitely many vertices may lie on the barrier. -/
theorem openConnected_of_two_infinite_of_sealedOpenCircuit
    {R : OpenPathRealization G vertex} (hcirc : SealedOpenCircuit R ω C S)
    (hfinite : (vertex ⁻¹' S.inside).Finite) (hfiniteK : (vertex ⁻¹' S.K).Finite)
    {x y : V} (hx : vertex x ∈ S.inside) (hy : vertex y ∈ S.inside)
    (hxinf : ExteriorInfiniteCluster G ω Set.univ x)
    (hyinf : ExteriorInfiniteCluster G ω Set.univ y) :
    OpenConnected G ω Set.univ x y := by
  have hfiniteU : (vertex ⁻¹' (S.inside ∪ S.K)).Finite := by
    rw [Set.preimage_union]
    exact hfinite.union hfiniteK
  have hexit : ∀ {z : V}, ExteriorInfiniteCluster G ω Set.univ z →
      ∃ w : V, OpenConnected G ω Set.univ z w ∧ vertex w ∉ S.inside ∪ S.K := by
    intro z hz
    by_contra! h
    exact hz (hfiniteU.subset fun w hw => h w hw)
  obtain ⟨z, hxz, hz⟩ := hexit hxinf
  obtain ⟨w, hyw, hw⟩ := hexit hyinf
  have hzK : vertex z ∈ S.Kᶜ := by
    intro hmem
    exact hz (Or.inr hmem)
  have hwK : vertex w ∈ S.Kᶜ := by
    intro hmem
    exact hw (Or.inr hmem)
  have hzout : vertex z ∈ S.outside := by
    rcases S.cover hzK with h | h
    · exact absurd h (hz ∘ Or.inl)
    · exact h
  have hwout : vertex w ∈ S.outside := by
    rcases S.cover hwK with h | h
    · exact absurd h (hw ∘ Or.inl)
    · exact h
  obtain ⟨u, hu, hxu⟩ := hcirc.exists_vertexOnLabels_of_openConnected_inside_outside
    hxz hx hzout hzK
  obtain ⟨v, hv, hyv⟩ := hcirc.exists_vertexOnLabels_of_openConnected_inside_outside
    hyw hy hwout hwK
  have huv : OpenConnected G ω Set.univ u v :=
    (hcirc.openConnected hu hv).mono_edges (Set.subset_univ _)
  exact hxu.trans (huv.trans (openConnected_symm hyv))

end SealedAssembly

/-! ## A general obstruction: infinite closed paths

The refutation of the staircase configuration is an instance of a shape-free
statement: a walk all of whose edges are closed cannot leave the inside of any
crossing-controlled circuit.  Hence a configuration containing an infinite
closed path out of a neighbourhood of the centre admits no crossing-controlled
circuit exhaustion there, whatever the shapes of the barriers.
-/

section ClosedRayObstruction

variable {V X : Type*} [TopologicalSpace X] {G : SimpleGraph V} {vertex : V → X}

/-- **A closed walk cannot leave a crossing-controlled circuit.**  Every edge
arc of the walk avoids the barrier, so the whole walk stays on one side of it. -/
theorem mem_inside_of_closedWalk
    (R : OpenPathRealization G vertex) {ω : G.edgeSet → Bool}
    {C : Set G.edgeSet} {S : TwoSidedSeparation X}
    (hcross : R.CrossingControlledBy S.K C) (hCopen : ∀ e ∈ C, ω e = true)
    {x y : V} (p : G.Walk x y)
    (hclosed : ∀ d ∈ p.darts, ω ⟨d.edge, d.edge_mem⟩ = false)
    (hx : vertex x ∈ S.inside) : vertex y ∈ S.inside := by
  induction p with
  | nil => exact hx
  | @cons a b c hab rest ih =>
      have hd : ω (⟨s(a, b), hab⟩ : G.edgeSet) = false := by
        have h₁ := hclosed
        rw [SimpleGraph.Walk.darts_cons] at h₁
        have := h₁ _ (List.Mem.head _)
        simpa using this
      have hrest : ∀ d ∈ rest.darts, ω ⟨d.edge, d.edge_mem⟩ = false := by
        intro d hd'
        have h₁ := hclosed
        rw [SimpleGraph.Walk.darts_cons] at h₁
        exact h₁ _ (List.Mem.tail _ hd')
      have havoid : ∀ t : I, R.arc hab t ∉ S.K := by
        intro t ht
        have hmem : (⟨s(a, b), hab⟩ : G.edgeSet) ∈ C := hcross hab ⟨t, ht⟩
        have h1 := hCopen _ hmem
        rw [hd] at h1
        exact Bool.false_ne_true h1
      have hjoin : JoinedIn S.Kᶜ (vertex a) (vertex b) := ⟨R.arc hab, havoid⟩
      have hb : vertex b ∈ S.inside := by
        rcases S.cover hjoin.target_mem with h | h
        · exact h
        · exact absurd hjoin (S.separated hx h)
      exact ih hrest hb

end ClosedRayObstruction

section ClosedRayExhaustion

variable {V X : Type*} [NormedAddCommGroup X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- **No crossing-controlled exhaustion through an infinite closed path.**  If
the configuration contains a closed path from a point near `c` to vertices
`v n` for every `n`, and those vertices are distinct, then no cofinal family of
crossing-controlled separator circuits based at `c` exists. -/
theorem not_hasSeparatorCircuitExhaustion_of_closedRay
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X) (ρ : ℝ)
    (v : ℕ → V) (hinj : Function.Injective v) (hv0 : vertex (v 0) ∈ ball c ρ)
    (hclosed : ∀ n : ℕ, ∃ p : G.Walk (v 0) (v n),
      ∀ d ∈ p.darts, ω ⟨d.edge, d.edge_mem⟩ = false) :
    ¬ HasSeparatorCircuitExhaustion R ω c := by
  intro hex
  obtain ⟨C, S, hball, hfin, hcirc⟩ := hex ρ
  have hx : vertex (v 0) ∈ S.inside := hball hv0
  have hall : ∀ n : ℕ, vertex (v n) ∈ S.inside := by
    intro n
    obtain ⟨p, hp⟩ := hclosed n
    exact mem_inside_of_closedWalk R hcirc.crossing hcirc.label_open p hp hx
  have hinf : (vertex ⁻¹' S.inside).Infinite :=
    Set.infinite_of_injective_forall_mem hinj (fun n => hall n)
  exact hfin.not_infinite hinf

end ClosedRayExhaustion

/-! ## The staircase configuration admits no crossing-controlled exhaustion

The staircase configuration closes exactly the horizontal unit edges of the
positive `x`-axis.  Its dual-open edges form a matching, so there is no infinite
dual-open cluster (`PlanarTarget.staircase_dual_nonpercolation`), and the primal
open graph is connected (`StaircaseConnected.staircase_globalAtMostOne`).

Every closed edge of that ray has an arc which must avoid the barrier of any
crossing-controlled circuit: an arc meeting the barrier would force a closed
label into `C`.  So the whole ray, vertices included, lies in one path component
of the barrier complement.  Since the barrier cannot pass through vertices, the
inside of a cofinal circuit would then contain infinitely many lattice
vertices, contradicting its finiteness.  Hence no crossing-controlled separator
(exhaustion) exists, at any centre.
-/

section StaircaseRefutation

variable {ω : gridGraph.edgeSet → Bool}

/-- The `n`-th horizontal edge of the positive axis is closed. -/
theorem staircaseEdge_closed (n : ℕ) : staircaseConfig (staircaseEdge n) = false :=
  (staircaseConfig_closed_iff _).mpr ⟨n, rfl⟩

/-- **No crossing-controlled exhaustion exists in the staircase configuration.**
For every centre, `SeparatorCircuit` geometry with crossing control is
impossible although the dual has no infinite cluster. -/
theorem staircase_no_separatorCircuitExhaustion (c : ℝ × ℝ) :
    ¬ HasSeparatorCircuitExhaustion (G := gridGraph) (vertex := gridVertex)
        gridRealization staircaseConfig c := by
  intro h
  obtain ⟨C, S, hball, hfin, hcirc⟩ :=
    h (dist (gridVertex ((0 : ℤ), (0 : ℤ))) c + 1)
  have h0 : gridVertex ((0 : ℤ), (0 : ℤ)) ∈ S.inside :=
    hball (Metric.mem_ball.mpr (by linarith))
  -- one step of the closed ray stays inside
  have hstep : ∀ n : ℕ, gridVertex ((n : ℤ), (0 : ℤ)) ∈ S.inside →
      gridVertex (((n : ℤ) + 1), (0 : ℤ)) ∈ S.inside := by
    intro n hn
    have hadj : gridAdj ((n : ℤ), (0 : ℤ)) ((n : ℤ) + 1, (0 : ℤ)) :=
      gridAdj_fst_add (n : ℤ) 0
    have hclosed : staircaseConfig
        (⟨s(((n : ℤ), (0 : ℤ)), ((n : ℤ) + 1, (0 : ℤ))), hadj⟩ :
          gridGraph.edgeSet) = false := by
      have hst : (⟨s(((n : ℤ), (0 : ℤ)), ((n : ℤ) + 1, (0 : ℤ))), hadj⟩ :
          gridGraph.edgeSet) = staircaseEdge n := Subtype.ext rfl
      rw [hst]
      exact staircaseEdge_closed n
    have havoid : ∀ t : I, gridRealization.arc hadj t ∉ S.K := by
      intro t ht
      have hmem : (⟨s(((n : ℤ), (0 : ℤ)), ((n : ℤ) + 1, (0 : ℤ))), hadj⟩ :
          gridGraph.edgeSet) ∈ C := hcirc.crossing hadj ⟨t, ht⟩
      have hopen := hcirc.label_open _ hmem
      rw [hclosed] at hopen
      exact Bool.false_ne_true hopen
    have hjoin : JoinedIn S.Kᶜ (gridVertex ((n : ℤ), (0 : ℤ)))
        (gridVertex ((n : ℤ) + 1, (0 : ℤ))) := ⟨gridRealization.arc hadj, havoid⟩
    rcases S.cover hjoin.target_mem with hin | hout
    · exact hin
    · exact absurd hjoin (S.separated hn hout)
  have hall : ∀ n : ℕ, gridVertex ((n : ℤ), (0 : ℤ)) ∈ S.inside :=
    fun n => Nat.rec h0 (fun k ih => hstep k ih) n
  have hinj : Function.Injective (fun n : ℕ => (((n : ℤ)), (0 : ℤ)) : ℕ → GridV) := by
    intro m n h
    have h1 : (m : ℤ) = (n : ℤ) := congrArg Prod.fst h
    exact_mod_cast h1
  have hinf : (gridVertex ⁻¹' S.inside).Infinite :=
    Set.infinite_of_injective_forall_mem hinj (fun n => hall n)
  exact hfin.not_infinite hinf

/-- Lattice vertices in a Euclidean ball form a finite set. -/
theorem finite_gridVertex_preimage_ball (c : ℝ × ℝ) (r : ℝ) :
    (gridVertex ⁻¹' ball c r).Finite := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max |c.1| |c.2| + max r 0)
  have hK1 : |c.1| + r ≤ (K : ℝ) := by
    have h1 : |c.1| ≤ max |c.1| |c.2| := le_max_left _ _
    have h2 : r ≤ max r 0 := le_max_left _ _
    linarith
  have hK2 : |c.2| + r ≤ (K : ℝ) := by
    have h1 : |c.2| ≤ max |c.1| |c.2| := le_max_right _ _
    have h2 : r ≤ max r 0 := le_max_left _ _
    linarith
  refine (finite_natAbs_le K).prod (finite_natAbs_le K) |>.subset ?_
  intro p hp
  simp only [mem_preimage, Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hp
  have hb1 : |(((p.1 : ℤ) : ℝ))| < |c.1| + r := by
    have h1 : dist (((p.1 : ℤ) : ℝ)) c.1 < r := hp.1
    rw [Real.dist_eq] at h1
    have htri : |(((p.1 : ℤ) : ℝ))| ≤ |((((p.1 : ℤ) : ℝ)) - c.1)| + |c.1| := by
      have h := abs_add_le ((((p.1 : ℤ) : ℝ)) - c.1) c.1
      rwa [sub_add_cancel] at h
    linarith
  have hb2 : |(((p.2 : ℤ) : ℝ))| < |c.2| + r := by
    have h1 : dist (((p.2 : ℤ) : ℝ)) c.2 < r := hp.2
    rw [Real.dist_eq] at h1
    have htri : |(((p.2 : ℤ) : ℝ))| ≤ |((((p.2 : ℤ) : ℝ)) - c.2)| + |c.2| := by
      have h := abs_add_le ((((p.2 : ℤ) : ℝ)) - c.2) c.2
      rwa [sub_add_cancel] at h
    linarith
  have hp1 : p.1.natAbs ≤ K := by
    have h : ((p.1.natAbs : ℕ) : ℝ) < (K : ℝ) := by
      rw [← abs_int_cast]
      exact lt_of_lt_of_le hb1 hK1
    exact_mod_cast le_of_lt h
  have hp2 : p.2.natAbs ≤ K := by
    have h : ((p.2.natAbs : ℕ) : ℝ) < (K : ℝ) := by
      rw [← abs_int_cast]
      exact lt_of_lt_of_le hb2 hK2
    exact_mod_cast le_of_lt h
  exact ⟨hp1, hp2⟩

/-- The spherical `HasOpenCircuitExhaustion` of `FK.InfiniteOpenCircuitUniqueness`
is refuted by the same configuration. -/
theorem staircase_no_sphericalOpenCircuit (c : ℝ × ℝ) :
    ¬ HasOpenCircuitExhaustion (G := gridGraph) (vertex := gridVertex)
        gridRealization staircaseConfig c := by
  intro h
  exact staircase_no_separatorCircuitExhaustion c
    (hasSeparatorCircuitExhaustion_of_hasOpenCircuitExhaustion gridRealization
      staircaseConfig c (finite_gridVertex_preimage_ball c) h)

end StaircaseRefutation


/-! ## The `ℓ^∞` box circuits in the staircase configuration

The sealed interface is not vacuous: in the same staircase configuration the
boundaries of the `ℓ^∞` boxes are cofinal sealed circuits.  The closed ray
leaves vertices of those box boundaries, which is exactly what the
crossing-control field forbids and what the sealed field tolerates.
-/

section BoxCircuits

/-- The `ℓ^∞` norm of the plane. -/
def boxNorm (z : ℝ × ℝ) : ℝ := max |z.1| |z.2|

theorem continuous_boxNorm : Continuous boxNorm := by
  unfold boxNorm
  fun_prop

theorem boxNorm_gridVertex (p : GridV) : boxNorm (gridVertex p) = ((lvlInf p : ℕ) : ℝ) := by
  simp only [boxNorm, gridVertex, lvlInf, Nat.cast_max, abs_int_cast]

/-- The `ℓ^∞` box shell of integer radius `k`. -/
def boxBarrier (k : ℕ) : Set (ℝ × ℝ) := {z | boxNorm z = (k : ℝ)}

/-- The open box of integer radius `k`. -/
def boxInside (k : ℕ) : Set (ℝ × ℝ) := {z | boxNorm z < (k : ℝ)}

/-- The exterior of the closed box of integer radius `k`. -/
def boxOutside (k : ℕ) : Set (ℝ × ℝ) := {z | (k : ℝ) < boxNorm z}

/-- **The integer box shell separates the plane**, by the intermediate value
theorem for `ℓ^∞`.  In contrast to the half-integral diamonds of `GridFrontier`
the barrier contains lattice vertices; this is harmless for sealed circuits. -/
noncomputable def boxSep (k : ℕ) : TwoSidedSeparation (ℝ × ℝ) where
  K := boxBarrier k
  inside := boxInside k
  outside := boxOutside k
  cover := by
    intro z hz
    rcases lt_trichotomy (boxNorm z) ((k : ℝ)) with h | h | h
    · exact Or.inl h
    · exact absurd h hz
    · exact Or.inr h
  separated := by
    intro x y hx hy
    exact not_joinedIn_compl_levelSet_of_lt continuous_boxNorm hx hy

/-- The label set of the boundary cycle of the box of radius `k`: the lattice
edges whose two endpoints both have `ℓ^∞` level `k`. -/
def boxBorder (k : ℕ) : Set gridGraph.edgeSet :=
  {e | ∃ (p q : GridV) (h : gridAdj p q), e = ⟨s(p, q), h⟩ ∧ lvlInf p = k ∧ lvlInf q = k}

theorem mem_boxBorder_of_levels {k : ℕ} {p q : GridV} (h : gridAdj p q)
    (hp : lvlInf p = k) (hq : lvlInf q = k) :
    (⟨s(p, q), h⟩ : gridGraph.edgeSet) ∈ boxBorder k :=
  ⟨p, q, h, rfl, hp, hq⟩

/-- Every vertex on a box border label has level `k`. -/
theorem lvlInf_of_vertexOnLabels_boxBorder {k : ℕ} {u : GridV}
    (hu : VertexOnLabels (boxBorder k) u) : lvlInf u = k := by
  obtain ⟨v, hadj, he⟩ := hu
  obtain ⟨p, q, h, heq, hp, hq⟩ := he
  have hsym : s(u, v) = s(p, q) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]; exact hp
  · rw [h1]; exact hq

/-- Every level-`k` vertex is incident to a box border label (`k ≥ 1`). -/
theorem boxBorder_vertex_neighbour {k : ℕ} (hk : 1 ≤ k) {v : GridV} (hv : lvlInf v = k) :
    VertexOnLabels (boxBorder k) v := by
  obtain ⟨x, y⟩ := v
  have hv' : max x.natAbs y.natAbs = k := hv
  have hxle : x.natAbs ≤ k := by rw [← hv']; exact le_max_left _ _
  have hyle : y.natAbs ≤ k := by rw [← hv']; exact le_max_right _ _
  have hxb : -(k : ℤ) ≤ x ∧ x ≤ (k : ℤ) := (natAbs_le_iff x k).mp hxle
  have hyb : -(k : ℤ) ≤ y ∧ y ≤ (k : ℤ) := (natAbs_le_iff y k).mp hyle
  have key : ∀ (w : GridV) (hw : gridAdj (x, y) w), lvlInf w = k →
      VertexOnLabels (boxBorder k) (x, y) := by
    intro w hw hwl
    exact ⟨w, hw, mem_boxBorder_of_levels hw hv' hwl⟩
  have lvl_of : ∀ (a b : ℤ), a.natAbs = k → b.natAbs ≤ k → lvlInf (a, b) = k := by
    intro a b ha hb
    show max a.natAbs b.natAbs = k
    rw [ha]
    exact max_eq_left hb
  have lvl_of' : ∀ (a b : ℤ), b.natAbs = k → a.natAbs ≤ k → lvlInf (a, b) = k := by
    intro a b hb ha
    show max a.natAbs b.natAbs = k
    rw [hb]
    exact max_eq_right ha
  have hcases : x.natAbs = k ∨ y.natAbs = k := by
    rcases le_total x.natAbs y.natAbs with h | h
    · right; rw [← hv']; exact (max_eq_right h).symm
    · left; rw [← hv']; exact (max_eq_left h).symm
  rcases hcases with hxk | hyk
  · by_cases hy : y < (k : ℤ)
    · exact key (x, y + 1) (gridAdj_snd_add x y)
        (lvl_of x (y + 1) hxk ((natAbs_le_iff _ k).mpr ⟨by omega, by omega⟩))
    · exact key (x, y - 1) (gridAdj_snd_sub x y)
        (lvl_of x (y - 1) hxk ((natAbs_le_iff _ k).mpr ⟨by omega, by omega⟩))
  · by_cases hx : x < (k : ℤ)
    · exact key (x + 1, y) (gridAdj_fst_add x y)
        (lvl_of' (x + 1) y hyk ((natAbs_le_iff _ k).mpr ⟨by omega, by omega⟩))
    · exact key (x - 1, y) (gridAdj_fst_sub x y)
        (lvl_of' (x - 1) y hyk ((natAbs_le_iff _ k).mpr ⟨by omega, by omega⟩))

/-- A configuration which closes no staircase edge outside the axis is open on
a horizontal edge off the axis and on every vertical edge. -/
theorem staircaseConfig_eq_true_of_not_staircase {e : gridGraph.edgeSet}
    (h : ∀ n : ℕ, e ≠ staircaseEdge n) : staircaseConfig e = true := by
  by_contra hc
  have hf : staircaseConfig e = false := by simpa using hc
  obtain ⟨n, hn⟩ := (staircaseConfig_closed_iff e).mp hf
  exact h n hn

/-- Box border labels are open in the staircase configuration (`k ≥ 1`). -/
theorem boxBorder_open {k : ℕ} (hk : 1 ≤ k) {e : gridGraph.edgeSet}
    (he : e ∈ boxBorder k) : staircaseConfig e = true := by
  obtain ⟨p, q, h, rfl, hp, hq⟩ := he
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [lvlInf] at hp hq
  refine staircaseConfig_eq_true_of_not_staircase (fun n hn => ?_)
  have hval : s((a, b), (c, d)) = s(((n : ℤ), 0), ((n : ℤ) + 1, 0)) := by
    have hh := congrArg Subtype.val hn
    simpa [staircaseEdge] using hh
  rcases Sym2.eq_iff.mp hval with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have ha : a = ((n : ℤ)) := congrArg Prod.fst e1
    have hb : b = 0 := congrArg Prod.snd e1
    have hc : c = ((n : ℤ)) + 1 := congrArg Prod.fst e2
    have hd : d = 0 := congrArg Prod.snd e2
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega
  · have ha : a = ((n : ℤ)) + 1 := congrArg Prod.fst e1
    have hb : b = 0 := congrArg Prod.snd e1
    have hc : c = ((n : ℤ)) := congrArg Prod.fst e2
    have hd : d = 0 := congrArg Prod.snd e2
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

/-- The staircase configuration is open on every box border label, `k ≥ 1`. -/
theorem boxBorder_label_open {k : ℕ} (hk : 1 ≤ k) {e : gridGraph.edgeSet}
    (he : e ∈ boxBorder k) : staircaseConfig e = true := boxBorder_open hk he

end BoxCircuits


/-! ### The box border is open-connected

The border labels are the tangential unit edges of the `ℓ^∞` level set `k`; as a
graph they form the boundary cycle of the box `[-k,k]^2`.  We prove connectivity
by explicit horizontal and vertical runs to the corner `(k,k)`.
-/

section BoxBorderConnectivity

/-- Horizontal run along the row of level `j` with `|j| = k`, in any
configuration which is open on the box border. -/
theorem rowConn {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ boxBorder k, ω e = true) {j : ℤ} (hj : j.natAbs = k) :
    ∀ (d : ℕ) (a : ℤ), a.natAbs ≤ k → (a + (d : ℤ)).natAbs ≤ k →
      OpenConnected gridGraph ω (LabelCarrier (boxBorder k))
        (a, j) (a + (d : ℤ), j) := by
  intro d
  induction d with
  | zero =>
      intro a _ _
      simpa using OpenConnected.refl (G := gridGraph) ω
        (LabelCarrier (boxBorder k)) (a, j)
  | succ n ih =>
      intro a ha hd
      have hprev : (a + (n : ℤ)).natAbs ≤ k := by
        rw [natAbs_le_iff] at hd ⊢
        constructor <;> omega
      have hnext : (a + (n : ℤ) + 1).natAbs ≤ k := by
        rw [natAbs_le_iff] at hd ⊢
        constructor <;> omega
      have h1 : lvlInf (a + (n : ℤ), j) = k := by
        show max (a + (n : ℤ)).natAbs j.natAbs = k
        rw [hj]
        exact max_eq_right hprev
      have h2 : lvlInf (a + (n : ℤ) + 1, j) = k := by
        show max (a + (n : ℤ) + 1).natAbs j.natAbs = k
        rw [hj]
        exact max_eq_right hnext
      have hstep : OpenConnected gridGraph ω
          (LabelCarrier (boxBorder k)) (a + (n : ℤ), j) (a + (n : ℤ) + 1, j) := by
        have hadj : gridAdj (a + (n : ℤ), j) (a + (n : ℤ) + 1, j) :=
          gridAdj_fst_add (a + (n : ℤ)) j
        have hmem : (⟨s((a + (n : ℤ), j), (a + (n : ℤ) + 1, j)), hadj⟩ :
            gridGraph.edgeSet) ∈ boxBorder k := mem_boxBorder_of_levels hadj h1 h2
        exact OpenConnected.of_adj hadj ⟨_, hmem, rfl⟩ (hopen _ hmem)
      have hh := (ih a ha hprev).trans hstep
      simpa [Nat.cast_succ, add_assoc] using hh

/-- Vertical run along the column of level `i` with `|i| = k`, in any
configuration which is open on the box border. -/
theorem colConn {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ boxBorder k, ω e = true) {i : ℤ} (hi : i.natAbs = k) :
    ∀ (d : ℕ) (a : ℤ), a.natAbs ≤ k → (a + (d : ℤ)).natAbs ≤ k →
      OpenConnected gridGraph ω (LabelCarrier (boxBorder k))
        (i, a) (i, a + (d : ℤ)) := by
  intro d
  induction d with
  | zero =>
      intro a _ _
      simpa using OpenConnected.refl (G := gridGraph) ω
        (LabelCarrier (boxBorder k)) (i, a)
  | succ n ih =>
      intro a ha hd
      have hprev : (a + (n : ℤ)).natAbs ≤ k := by
        rw [natAbs_le_iff] at hd ⊢
        constructor <;> omega
      have hnext : (a + (n : ℤ) + 1).natAbs ≤ k := by
        rw [natAbs_le_iff] at hd ⊢
        constructor <;> omega
      have h1 : lvlInf (i, a + (n : ℤ)) = k := by
        show max i.natAbs (a + (n : ℤ)).natAbs = k
        rw [hi]
        exact max_eq_left hprev
      have h2 : lvlInf (i, a + (n : ℤ) + 1) = k := by
        show max i.natAbs (a + (n : ℤ) + 1).natAbs = k
        rw [hi]
        exact max_eq_left hnext
      have hstep : OpenConnected gridGraph ω
          (LabelCarrier (boxBorder k)) (i, a + (n : ℤ)) (i, a + (n : ℤ) + 1) := by
        have hadj : gridAdj (i, a + (n : ℤ)) (i, a + (n : ℤ) + 1) :=
          gridAdj_snd_add i (a + (n : ℤ))
        have hmem : (⟨s((i, a + (n : ℤ)), (i, a + (n : ℤ) + 1)), hadj⟩ :
            gridGraph.edgeSet) ∈ boxBorder k := mem_boxBorder_of_levels hadj h1 h2
        exact OpenConnected.of_adj hadj ⟨_, hmem, rfl⟩ (hopen _ hmem)
      have hh := (ih a ha hprev).trans hstep
      simpa [Nat.cast_succ, add_assoc] using hh

/-- A horizontal run between two vertices of level `k` on the same row. -/
theorem rowConn' {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ boxBorder k, ω e = true) {j a b : ℤ} (hj : j.natAbs = k)
    (ha : a.natAbs ≤ k) (hb : b.natAbs ≤ k) (hab : a ≤ b) :
    OpenConnected gridGraph ω (LabelCarrier (boxBorder k)) (a, j) (b, j) := by
  have key := rowConn hopen hj (b - a).toNat a ha (by
    rw [natAbs_le_iff] at hb ⊢
    constructor <;> omega)
  rwa [show a + (((b - a).toNat : ℕ) : ℤ) = b by
    have : (((b - a).toNat : ℕ) : ℤ) = b - a := by
      rw [Int.toNat_of_nonneg (by omega)]
    rw [this]; ring] at key

/-- A vertical run between two vertices of level `k` on the same column. -/
theorem colConn' {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ boxBorder k, ω e = true) {i a b : ℤ} (hi : i.natAbs = k)
    (ha : a.natAbs ≤ k) (hb : b.natAbs ≤ k) (hab : a ≤ b) :
    OpenConnected gridGraph ω (LabelCarrier (boxBorder k)) (i, a) (i, b) := by
  have key := colConn hopen hi (b - a).toNat a ha (by
    rw [natAbs_le_iff] at hb ⊢
    constructor <;> omega)
  rwa [show a + (((b - a).toNat : ℕ) : ℤ) = b by
    have : (((b - a).toNat : ℕ) : ℤ) = b - a := by
      rw [Int.toNat_of_nonneg (by omega)]
    rw [this]; ring] at key

/-- **The box border labels are open-connected**: they form the boundary cycle of
the box. -/
theorem boxBorder_openLabelConnected {k : ℕ} {ω : gridGraph.edgeSet → Bool}
    (hopen : ∀ e ∈ boxBorder k, ω e = true) :
    OpenLabelConnected gridGraph ω (boxBorder k) := by
  intro u v hu hv
  have hu' : lvlInf u = k := lvlInf_of_vertexOnLabels_boxBorder hu
  have hv' : lvlInf v = k := lvlInf_of_vertexOnLabels_boxBorder hv
  have key : ∀ w : GridV, lvlInf w = k →
      OpenConnected gridGraph ω (LabelCarrier (boxBorder k))
        w ((k : ℤ), (k : ℤ)) := by
    intro w hw
    obtain ⟨x, y⟩ := w
    have hxl : x.natAbs ≤ k := by
      have := hw; simp only [lvlInf] at this
      rw [← this]; exact le_max_left _ _
    have hyl : y.natAbs ≤ k := by
      have := hw; simp only [lvlInf] at this
      rw [← this]; exact le_max_right _ _
    have hxle : x ≤ (k : ℤ) := ((natAbs_le_iff x k).mp hxl).2
    have hyle : y ≤ (k : ℤ) := ((natAbs_le_iff y k).mp hyl).2
    have hk' : ((k : ℤ)).natAbs = k := Int.natAbs_natCast k
    have hk'' : ((k : ℤ)).natAbs ≤ k := le_of_eq hk'
    by_cases hyk : y.natAbs = k
    · exact (rowConn' hopen hyk hxl hk'' hxle).trans
        (colConn' hopen hk' hyl hk'' hyle)
    · have hxk : x.natAbs = k := by
        have h1 : max x.natAbs y.natAbs = k := hw
        rcases le_total x.natAbs y.natAbs with h | h
        · rw [max_eq_right h] at h1
          exact absurd h1 hyk
        · rw [max_eq_left h] at h1
          exact h1
      exact (colConn' hopen hxk hyl hk'' hyle).trans
        (rowConn' hopen hk' hxl hk'' hxle)
  exact (key u hu').trans (openConnected_symm (key v hv'))

end BoxBorderConnectivity


/-! ### Sealing the box border against the `ℓ^∞` shell

Two elementary bounds on the sup-norm along a unit lattice step are needed: on
such a segment the norm is at most the maximum of its endpoint values
(convexity), and it is at least `K` as soon as both endpoint values are at least
`K` (the segment is axis-parallel with integer endpoints).
-/

section BoxSealing

/-- The sup-norm of an embedded lattice vertex, in coordinates. -/
theorem boxNorm_gridVertex_eq (p : GridV) :
    boxNorm (gridVertex p) = max |(p.1 : ℝ)| |(p.2 : ℝ)| := by
  simp [boxNorm, gridVertex]

/-- The one-dimensional step bound: if two consecutive integers have absolute
value at least `K`, so does every convex combination of them. -/
theorem abs_affine_step_ge {a b : ℤ} (hb : b = a + 1 ∨ b = a - 1) (t : I) {K : ℝ}
    (ha : K ≤ |(a : ℝ)|) (hbb : K ≤ |(b : ℝ)|) :
    K ≤ |(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)| := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hrew : ∀ (c : ℤ), c = a + 1 → ((c : ℝ)) = (a : ℝ) + 1 := by
    intro c hc; rw [hc]; push_cast; ring
  have hrew' : ∀ (c : ℤ), c = a - 1 → ((c : ℝ)) = (a : ℝ) - 1 := by
    intro c hc; rw [hc]; push_cast; ring
  have hbre : ((b : ℝ)) = (a : ℝ) + 1 ∨ ((b : ℝ)) = (a : ℝ) - 1 := by
    rcases hb with h | h
    · exact Or.inl (hrew b h)
    · exact Or.inr (hrew' b h)
  rcases le_or_gt K 0 with hK | hK
  · have := abs_nonneg ((1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ))
    linarith
  · have hane : a ≠ 0 := by
      intro h; rw [h] at ha; simp only [Int.cast_zero, abs_zero] at ha; linarith
    have hbne : b ≠ 0 := by
      intro h; rw [h] at hbb; simp only [Int.cast_zero, abs_zero] at hbb; linarith
    rcases lt_or_gt_of_ne hane with han | hap
    · have hbn : b < 0 := by
        rcases hb with h | h <;> omega
      have hle : (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤ 0 := by
        have ha' : (a : ℝ) < 0 := by exact_mod_cast han
        have hb' : (b : ℝ) < 0 := by exact_mod_cast hbn
        nlinarith
      rw [abs_of_nonpos hle]
      have haa : K ≤ -(a : ℝ) := by
        have h : |(a : ℝ)| = -(a : ℝ) := abs_of_neg (by exact_mod_cast han)
        linarith
      have hbbb : K ≤ -(b : ℝ) := by
        have h : |(b : ℝ)| = -(b : ℝ) := abs_of_neg (by exact_mod_cast hbn)
        linarith
      nlinarith
    · have hbp : 0 < b := by
        rcases hb with h | h <;> omega
      have hle : 0 ≤ (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) := by
        have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hap
        have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbp
        nlinarith
      rw [abs_of_nonneg hle]
      have haa : K ≤ (a : ℝ) := by
        have h : |(a : ℝ)| = (a : ℝ) := abs_of_pos (by exact_mod_cast hap)
        linarith
      have hbbb : K ≤ (b : ℝ) := by
        have h : |(b : ℝ)| = (b : ℝ) := abs_of_pos (by exact_mod_cast hbp)
        linarith
      nlinarith

/-- On a unit lattice step the sup-norm is at most the maximal endpoint value. -/
theorem boxNorm_straightPath_le_max {p q : GridV} (h : gridAdj p q) (t : I) :
    boxNorm (straightPath (gridVertex p) (gridVertex q) t) ≤
      max (boxNorm (gridVertex p)) (boxNorm (gridVertex q)) := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hcoord : ∀ (a b : ℤ),
      |(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)| ≤ max |(a : ℝ)| |(b : ℝ)| := by
    intro a b
    set M : ℝ := max |(a : ℝ)| |(b : ℝ)| with hM
    have hMa : |(a : ℝ)| ≤ M := le_max_left _ _
    have hMb : |(b : ℝ)| ≤ M := le_max_right _ _
    have hMnn : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) hMa
    calc |(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)|
        ≤ |(1 - (t : ℝ)) * (a : ℝ)| + |(t : ℝ) * (b : ℝ)| := abs_add_le _ _
      _ = (1 - (t : ℝ)) * |(a : ℝ)| + (t : ℝ) * |(b : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
      _ ≤ M := by nlinarith
  have hz : straightPath (gridVertex p) (gridVertex q) t =
      ((1 - (t : ℝ)) * (p.1 : ℝ) + (t : ℝ) * (q.1 : ℝ),
       (1 - (t : ℝ)) * (p.2 : ℝ) + (t : ℝ) * (q.2 : ℝ)) := by
    rw [straightPath_apply]
    ext <;> simp only [gridVertex] <;> ring
  rw [hz, boxNorm, boxNorm_gridVertex_eq, boxNorm_gridVertex_eq]
  refine max_le ?_ ?_
  · refine le_trans (hcoord p.1 q.1) ?_
    exact max_le (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · refine le_trans (hcoord p.2 q.2) ?_
    exact max_le (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The sup-norm of an explicit plane point. -/
theorem boxNorm_mk (x y : ℝ) : boxNorm (x, y) = max |x| |y| := rfl

/-- On a unit lattice step the sup-norm is at least `K` as soon as both endpoint
values are at least `K`. -/
theorem le_boxNorm_straightPath_of_le {p q : GridV} (h : gridAdj p q) (t : I) {K : ℝ}
    (hp : K ≤ boxNorm (gridVertex p)) (hq : K ≤ boxNorm (gridVertex q)) :
    K ≤ boxNorm (straightPath (gridVertex p) (gridVertex q) t) := by
  have hz : straightPath (gridVertex p) (gridVertex q) t =
      ((1 - (t : ℝ)) * (p.1 : ℝ) + (t : ℝ) * (q.1 : ℝ),
       (1 - (t : ℝ)) * (p.2 : ℝ) + (t : ℝ) * (q.2 : ℝ)) := by
    rw [straightPath_apply]
    ext <;> simp only [gridVertex] <;> ring
  have hp' := hp
  have hq' := hq
  rw [boxNorm_gridVertex_eq] at hp' hq'
  have key : ∀ (a b b' : ℤ), (b' = b + 1 ∨ b' = b - 1) →
      K ≤ max |(a : ℝ)| |(b : ℝ)| → K ≤ max |(a : ℝ)| |(b' : ℝ)| →
      K ≤ max |(a : ℝ)| |(1 - (t : ℝ)) * (b : ℝ) + (t : ℝ) * (b' : ℝ)| := by
    intro a b b' hbb h1 h2
    by_cases haK : K ≤ |(a : ℝ)|
    · exact le_trans haK (le_max_left _ _)
    · rw [not_le] at haK
      have hbK : K ≤ |(b : ℝ)| := by
        by_contra hc
        rw [not_le] at hc
        linarith [max_lt haK hc]
      have hbK' : K ≤ |(b' : ℝ)| := by
        by_contra hc
        rw [not_le] at hc
        linarith [max_lt haK hc]
      exact le_trans (abs_affine_step_ge hbb t hbK hbK') (le_max_right _ _)
  rw [hz, boxNorm_mk]
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have hq1 : ((q.1 : ℝ)) = (p.1 : ℝ) := by rw [h1]
    have hz1 : (1 - (t : ℝ)) * (p.1 : ℝ) + (t : ℝ) * (q.1 : ℝ) = (p.1 : ℝ) := by
      rw [hq1]; ring
    rw [hz1]
    rw [hq1] at hq'
    exact key p.1 p.2 q.2 (Or.inr (by omega)) hp' hq'
  · have hq1 : ((q.1 : ℝ)) = (p.1 : ℝ) := by rw [h1]
    have hz1 : (1 - (t : ℝ)) * (p.1 : ℝ) + (t : ℝ) * (q.1 : ℝ) = (p.1 : ℝ) := by
      rw [hq1]; ring
    rw [hz1]
    rw [hq1] at hq'
    exact key p.1 p.2 q.2 (Or.inl (by omega)) hp' hq'
  · have hq2 : ((q.2 : ℝ)) = (p.2 : ℝ) := by rw [h1]
    have hz2 : (1 - (t : ℝ)) * (p.2 : ℝ) + (t : ℝ) * (q.2 : ℝ) = (p.2 : ℝ) := by
      rw [hq2]; ring
    rw [hz2, max_comm]
    rw [hq2, max_comm] at hq'
    refine key p.2 p.1 q.1 (Or.inr (by omega)) ?_ hq'
    rw [max_comm]; exact hp'
  · have hq2 : ((q.2 : ℝ)) = (p.2 : ℝ) := by rw [h1]
    have hz2 : (1 - (t : ℝ)) * (p.2 : ℝ) + (t : ℝ) * (q.2 : ℝ) = (p.2 : ℝ) := by
      rw [hq2]; ring
    rw [hz2, max_comm]
    rw [hq2, max_comm] at hq'
    refine key p.2 p.1 q.1 (Or.inl (by omega)) ?_ hq'
    rw [max_comm]; exact hp'

/-- Adjacent lattice vertices have `ℓ^∞` levels differing by at most one. -/
theorem lvlInf_adj_le {p q : GridV} (h : gridAdj p q) :
    lvlInf p ≤ lvlInf q + 1 ∧ lvlInf q ≤ lvlInf p + 1 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [lvlInf]
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> subst_vars <;> constructor <;> omega

/-- **Sealing.**  Every edge whose arc meets the box shell belongs to the box
border or has an endpoint incident to it. -/
theorem boxBorder_sealed {k : ℕ} (hk : 1 ≤ k) {u v : GridV} (h : gridAdj u v)
    (hcross : ∃ t : I, straightPath (gridVertex u) (gridVertex v) t ∈ boxBarrier k) :
    ((⟨s(u, v), h⟩ : gridGraph.edgeSet) ∈ boxBorder k ∨
      VertexOnLabels (boxBorder k) u ∨ VertexOnLabels (boxBorder k) v) := by
  obtain ⟨t, ht⟩ := hcross
  have hz : boxNorm (straightPath (gridVertex u) (gridVertex v) t) = (k : ℝ) := ht
  have hu := boxNorm_gridVertex u
  have hv := boxNorm_gridVertex v
  have hle := boxNorm_straightPath_le_max h t
  rw [hz, hu, hv] at hle
  have hle' : k ≤ max (lvlInf u) (lvlInf v) := by
    have h2 : (k : ℝ) ≤ ((max (lvlInf u) (lvlInf v) : ℕ) : ℝ) := by
      rw [Nat.cast_max]
      exact hle
    exact_mod_cast h2
  have hbnd : ∀ (z : GridV), k + 1 ≤ lvlInf z → (k : ℝ) + 1 ≤ boxNorm (gridVertex z) := by
    intro z hz'
    rw [boxNorm_gridVertex z]
    have hc : ((k + 1 : ℕ) : ℝ) ≤ ((lvlInf z : ℕ) : ℝ) := by exact_mod_cast hz'
    push_cast at hc ⊢
    linarith
  have hadj := lvlInf_adj_le h
  have hkey : lvlInf u = k ∨ lvlInf v = k := by
    rcases le_total (lvlInf u) (lvlInf v) with hc | hc
    · rw [max_eq_right hc] at hle'
      by_cases hbv : lvlInf v = k
      · exact Or.inr hbv
      · left
        by_contra hbu
        have h1 : k + 1 ≤ lvlInf v := by omega
        have h2 : k + 1 ≤ lvlInf u := by omega
        have hbad := le_boxNorm_straightPath_of_le h t (K := (k : ℝ) + 1)
          (hbnd u h2) (hbnd v h1)
        rw [hz] at hbad
        linarith
    · rw [max_eq_left hc] at hle'
      by_cases hbu : lvlInf u = k
      · exact Or.inl hbu
      · right
        by_contra hbv
        have h1 : k + 1 ≤ lvlInf u := by omega
        have h2 : k + 1 ≤ lvlInf v := by omega
        have hbad := le_boxNorm_straightPath_of_le h t (K := (k : ℝ) + 1)
          (hbnd u h1) (hbnd v h2)
        rw [hz] at hbad
        linarith
  rcases hkey with h1 | h1
  · exact Or.inr (Or.inl (boxBorder_vertex_neighbour hk h1))
  · exact Or.inr (Or.inr (boxBorder_vertex_neighbour hk h1))

end BoxSealing


/-! ## A cofinal family of sealed circuits

This is the sealed analogue of `HasSeparatorCircuitExhaustion`.  Besides
finiteness of the vertices inside the barrier we require finiteness of the
vertices *on* it, because sealed circuits may pass through vertices.
-/

section SealedExhaustion

variable {V X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G : SimpleGraph V} {vertex : V → X}

/-- Cofinal sealed circuits: for every radius there is a sealed circuit whose
inside contains the whole ball and whose barrier and inside carry only finitely
many vertices. -/
def HasSealedCircuitExhaustion (R : OpenPathRealization G vertex)
    (ω : G.edgeSet → Bool) (c : X) : Prop :=
  ∀ ρ : ℝ, ∃ (C : Set G.edgeSet) (S : TwoSidedSeparation X),
    ball c ρ ⊆ S.inside ∧ (vertex ⁻¹' S.inside).Finite ∧ (vertex ⁻¹' S.K).Finite ∧
      SealedOpenCircuit R ω C S

/-- **A cofinal sealed circuit exhaustion gives uniqueness.** -/
theorem globalAtMostOne_of_sealedCircuitExhaustion
    (R : OpenPathRealization G vertex) (ω : G.edgeSet → Bool) (c : X)
    (hexhaust : HasSealedCircuitExhaustion R ω c) : GlobalAtMostOne G ω := by
  intro x y hxinf hyinf
  obtain ⟨C, S, hball, hfin, hfinK, hcirc⟩ :=
    hexhaust (max (dist (vertex x) c) (dist (vertex y) c) + 1)
  exact openConnected_of_two_infinite_of_sealedOpenCircuit hcirc hfin hfinK
    (hball (by
      rw [Metric.mem_ball]
      linarith [le_max_left (dist (vertex x) c) (dist (vertex y) c)]))
    (hball (by
      rw [Metric.mem_ball]
      linarith [le_max_right (dist (vertex x) c) (dist (vertex y) c)]))
    hxinf hyinf

end SealedExhaustion

/-! ## The box circuit exhaustion in the staircase configuration -/

section BoxInstance

/-- Lattice vertices inside a box carry only finitely many labels. -/
theorem finite_preimage_boxInside (k : ℕ) : (gridVertex ⁻¹' boxInside k).Finite := by
  refine (finite_natAbs_le k).prod (finite_natAbs_le k) |>.subset ?_
  intro p hp
  have hp' : boxNorm (gridVertex p) < (k : ℝ) := hp
  rw [boxNorm_gridVertex] at hp'
  have h1 : p.1.natAbs ≤ lvlInf p := le_max_left _ _
  have h2 : p.2.natAbs ≤ lvlInf p := le_max_right _ _
  have hk : lvlInf p < k := by exact_mod_cast hp'
  exact ⟨Nat.le_trans h1 (Nat.le_of_lt hk), Nat.le_trans h2 (Nat.le_of_lt hk)⟩

/-- Lattice vertices on a box shell are finite. -/
theorem finite_preimage_boxBarrier (k : ℕ) : (gridVertex ⁻¹' boxBarrier k).Finite := by
  refine (finite_natAbs_le k).prod (finite_natAbs_le k) |>.subset ?_
  intro p hp
  have hp' : boxNorm (gridVertex p) = (k : ℝ) := hp
  rw [boxNorm_gridVertex] at hp'
  have h1 : p.1.natAbs ≤ lvlInf p := le_max_left _ _
  have h2 : p.2.natAbs ≤ lvlInf p := le_max_right _ _
  have hk : lvlInf p = k := by exact_mod_cast hp'
  exact ⟨Nat.le_trans h1 (Nat.le_of_eq hk), Nat.le_trans h2 (Nat.le_of_eq hk)⟩

/-- Opaque ball growth: every Euclidean ball is contained in an open box of
integer radius at least one. -/
theorem exists_ball_subset_boxInside (c : ℝ × ℝ) (ρ : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ ball c ρ ⊆ boxInside k := by
  obtain ⟨K, hK⟩ := exists_nat_gt (‖c‖ + max ρ 0)
  refine ⟨max K 1, le_max_right _ _, fun z hz => ?_⟩
  have hbox : boxNorm z = ‖z‖ := by
    rw [boxNorm, Prod.norm_def]
    rfl
  have hlt : dist z c < ρ := Metric.mem_ball.mp hz
  have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
    have := norm_add_le (z - c) c
    rwa [sub_add_cancel] at this
  have hnorm : ‖z - c‖ = dist z c := (dist_eq_norm z c).symm
  have hK' : ‖c‖ + ρ ≤ (K : ℝ) := by
    have h1 : ρ ≤ max ρ 0 := le_max_left _ _
    linarith
  have hK'' : ‖c‖ + ρ ≤ (max K 1 : ℕ) := by
    have hle : (K : ℝ) ≤ ((max K 1 : ℕ) : ℝ) := by
      exact_mod_cast le_max_left K 1
    linarith
  show boxNorm z < ((max K 1 : ℕ) : ℝ)
  rw [hbox]
  linarith

/-- **The sealed interface is inhabited in the obstruction configuration.**
Every Euclidean ball is enclosed by the boundary cycle of an `ℓ^∞` box, whose
labels are open in the staircase configuration and whose sealing only uses the
box vertices. -/
theorem hasSealedCircuitExhaustion_staircase (c : ℝ × ℝ) :
    HasSealedCircuitExhaustion (G := gridGraph) (vertex := gridVertex)
      gridRealization staircaseConfig c := by
  intro ρ
  obtain ⟨k, hk1, hball⟩ := exists_ball_subset_boxInside c ρ
  have hopen : ∀ e ∈ boxBorder k, staircaseConfig e = true := fun e he => boxBorder_open hk1 he
  refine ⟨boxBorder k, boxSep k, hball, finite_preimage_boxInside k,
    finite_preimage_boxBarrier k, ?_⟩
  exact ⟨hopen, boxBorder_openLabelConnected hopen, fun {u v} h hc => boxBorder_sealed hk1 h hc⟩

/-- The staircase configuration, whose dual has no infinite open cluster,
satisfies the sealed exhaustion and hence at most one infinite primal cluster.
This is an independent proof of `StaircaseConnected.staircase_globalAtMostOne`
through the sealed interface, i.e. through the interface that the spherical and
crossing-controlled forms cannot provide here. -/
theorem globalAtMostOne_staircase_of_sealed :
    GlobalAtMostOne gridGraph staircaseConfig :=
  globalAtMostOne_of_sealedCircuitExhaustion gridRealization staircaseConfig
    ((0 : ℤ), (0 : ℤ)) (hasSealedCircuitExhaustion_staircase ((0 : ℤ), (0 : ℤ)))

end BoxInstance


/-! ## Positive instances: configurations whose closed edges avoid large box borders

The box construction of the previous sections needs only one property of the
configuration: `boxBorder k` consists of open edges, for arbitrarily large `k`.
This section isolates that condition, proves that it yields the sealed
exhaustion, and verifies it for bounded closed-edge sets.
-/

section BorderOpenInstance

variable {ω : gridGraph.edgeSet → Bool}

/-- The open boxes are monotone in the radius. -/
theorem boxInside_mono {k k' : ℕ} (h : k ≤ k') : boxInside k ⊆ boxInside k' := by
  intro z hz
  have hz' : boxNorm z < (k : ℝ) := hz
  have : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast h
  exact lt_of_lt_of_le hz' this

/-- **A cofinal box-border condition gives the sealed exhaustion.**  If box
borders of arbitrarily large radius consist of open edges, the box boundary
cycles are cofinal sealed circuits. -/
theorem hasSealedCircuitExhaustion_of_boxBorder_open
    (hborder : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ 1 ≤ k ∧ ∀ e ∈ boxBorder k, ω e = true)
    (c : ℝ × ℝ) :
    HasSealedCircuitExhaustion (G := gridGraph) (vertex := gridVertex) gridRealization ω c := by
  intro ρ
  obtain ⟨k₀, hkρ, hball⟩ := exists_ball_subset_boxInside c ρ
  obtain ⟨k, hk, hk1, hopen⟩ := hborder k₀
  refine ⟨boxBorder k, boxSep k, (Subset.trans hball (boxInside_mono hk)),
    finite_preimage_boxInside k, finite_preimage_boxBarrier k, ?_⟩
  exact ⟨hopen, boxBorder_openLabelConnected hopen,
    fun {u v} h hc => boxBorder_sealed hk1 h hc⟩

/-- Consequently the cofinal box-border condition forces at most one infinite
primal-open cluster. -/
theorem globalAtMostOne_of_boxBorder_open
    (hborder : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ 1 ≤ k ∧ ∀ e ∈ boxBorder k, ω e = true) :
    GlobalAtMostOne gridGraph ω :=
  globalAtMostOne_of_sealedCircuitExhaustion gridRealization ω ((0 : ℤ), (0 : ℤ))
    (hasSealedCircuitExhaustion_of_boxBorder_open hborder _)

/-- Every closed edge inside the box of radius `K` is avoided by all larger box
borders. -/
theorem boxBorder_open_of_bounded_closed {K : ℕ}
    (hbound : ∀ e : gridGraph.edgeSet, ω e = false →
      ∀ p ∈ (e.1 : Sym2 GridV), p.1.natAbs ≤ K ∧ p.2.natAbs ≤ K)
    {k : ℕ} (hk : K < k) : ∀ e ∈ boxBorder k, ω e = true := by
  intro e he
  by_contra hc
  have hf : ω e = false := by simpa using hc
  obtain ⟨p, q, h, heq, hp, hq⟩ := he
  have hmem : p ∈ (e.1 : Sym2 GridV) := by
    rw [heq]
    exact Sym2.mem_mk_left _ _
  have hpk := hbound e hf p hmem
  have hlev : lvlInf p ≤ K := by
    simp only [lvlInf]
    omega
  omega

/-- **Bounded closed-edge sets give at most one infinite primal cluster.**  This
is a genuine infinite family of configurations (closed edges may be infinite,
but stay in a fixed box) satisfying the deterministic planar target. -/
theorem globalAtMostOne_of_bounded_closed {K : ℕ}
    (hbound : ∀ e : gridGraph.edgeSet, ω e = false →
      ∀ p ∈ (e.1 : Sym2 GridV), p.1.natAbs ≤ K ∧ p.2.natAbs ≤ K) :
    GlobalAtMostOne gridGraph ω := by
  refine globalAtMostOne_of_boxBorder_open (fun K' => ⟨max K' (K + 1), le_max_left _ _, ?_, ?_⟩)
  · omega
  · intro e he
    exact boxBorder_open_of_bounded_closed hbound (by omega) e he

end BorderOpenInstance

/-! ## The residual obligation, in the paper's own target shape

`InfiniteOpenCircuitUniqueness` and `SeparatorCircuits` package the uniqueness
step against `FK.Planar.DualNonpercolationForcesPrimalAtMostOne`.  These
wrappers record the exact remaining hypothesis in the sealed form, and the two
refutations show that the published crossing-controlled forms of that
hypothesis cannot be met.
-/

section Residual

variable {V X : Type*} {G : SimpleGraph V} {vertex : V → X}

/-- The sealed construction hypothesis in the exact shape of the recorded
planar target. -/
theorem dualNonpercolationForcesPrimalAtMostOne_of_sealedExhaustion
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Type*} {GD : SimpleGraph F} (edge : G.edgeSet ≃ GD.edgeSet)
    (R : OpenPathRealization G vertex) (c : X)
    (hconstruct : ∀ ω : G.edgeSet → Bool,
      FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω) →
        HasSealedCircuitExhaustion R ω c) :
    FK.Planar.DualNonpercolationForcesPrimalAtMostOne G GD edge := by
  intro ω hdual
  exact globalAtMostOne_of_sealedCircuitExhaustion R ω c (hconstruct ω hdual)

end Residual

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.SealedSeparation.SealedOpenCircuit
#print axioms FK.PlaneTopology.SealedSeparation.SealedOpenCircuit.mem_inside_or_exists_vertexOnLabels_of_walk
#print axioms FK.PlaneTopology.SealedSeparation.SealedOpenCircuit.exists_vertexOnLabels_of_openConnected_inside_outside
#print axioms FK.PlaneTopology.SealedSeparation.sealedOpenCircuit_of_separatorOpenCircuit
#print axioms FK.PlaneTopology.SealedSeparation.openConnected_of_two_infinite_of_sealedOpenCircuit
#print axioms FK.PlaneTopology.SealedSeparation.finite_gridVertex_preimage_ball
#print axioms FK.PlaneTopology.SealedSeparation.mem_inside_of_closedWalk
#print axioms FK.PlaneTopology.SealedSeparation.not_hasSeparatorCircuitExhaustion_of_closedRay
#print axioms FK.PlaneTopology.SealedSeparation.staircase_no_separatorCircuitExhaustion
#print axioms FK.PlaneTopology.SealedSeparation.staircase_no_sphericalOpenCircuit
#print axioms FK.PlaneTopology.SealedSeparation.HasSealedCircuitExhaustion
#print axioms FK.PlaneTopology.SealedSeparation.globalAtMostOne_of_sealedCircuitExhaustion
#print axioms FK.PlaneTopology.SealedSeparation.lvlInf_of_vertexOnLabels_boxBorder
#print axioms FK.PlaneTopology.SealedSeparation.boxBorder_vertex_neighbour
#print axioms FK.PlaneTopology.SealedSeparation.boxBorder_open
#print axioms FK.PlaneTopology.SealedSeparation.rowConn
#print axioms FK.PlaneTopology.SealedSeparation.colConn
#print axioms FK.PlaneTopology.SealedSeparation.boxBorder_openLabelConnected
#print axioms FK.PlaneTopology.SealedSeparation.abs_affine_step_ge
#print axioms FK.PlaneTopology.SealedSeparation.boxNorm_straightPath_le_max
#print axioms FK.PlaneTopology.SealedSeparation.le_boxNorm_straightPath_of_le
#print axioms FK.PlaneTopology.SealedSeparation.lvlInf_adj_le
#print axioms FK.PlaneTopology.SealedSeparation.boxBorder_sealed
#print axioms FK.PlaneTopology.SealedSeparation.finite_preimage_boxInside
#print axioms FK.PlaneTopology.SealedSeparation.finite_preimage_boxBarrier
#print axioms FK.PlaneTopology.SealedSeparation.exists_ball_subset_boxInside
#print axioms FK.PlaneTopology.SealedSeparation.hasSealedCircuitExhaustion_staircase
#print axioms FK.PlaneTopology.SealedSeparation.globalAtMostOne_staircase_of_sealed
#print axioms FK.PlaneTopology.SealedSeparation.boxInside_mono
#print axioms FK.PlaneTopology.SealedSeparation.hasSealedCircuitExhaustion_of_boxBorder_open
#print axioms FK.PlaneTopology.SealedSeparation.globalAtMostOne_of_boxBorder_open
#print axioms FK.PlaneTopology.SealedSeparation.boxBorder_open_of_bounded_closed
#print axioms FK.PlaneTopology.SealedSeparation.globalAtMostOne_of_bounded_closed
#print axioms FK.PlaneTopology.SealedSeparation.dualNonpercolationForcesPrimalAtMostOne_of_sealedExhaustion

/-! ## Statements of the principal results -/

#check @FK.PlaneTopology.SealedSeparation.SealedOpenCircuit
#check @FK.PlaneTopology.SealedSeparation.openConnected_of_two_infinite_of_sealedOpenCircuit
#check @FK.PlaneTopology.SealedSeparation.HasSealedCircuitExhaustion
#check @FK.PlaneTopology.SealedSeparation.globalAtMostOne_of_sealedCircuitExhaustion
#check @FK.PlaneTopology.SealedSeparation.staircase_no_separatorCircuitExhaustion
#check @FK.PlaneTopology.SealedSeparation.staircase_no_sphericalOpenCircuit
#check @FK.PlaneTopology.SealedSeparation.hasSealedCircuitExhaustion_staircase
#check @FK.PlaneTopology.SealedSeparation.globalAtMostOne_staircase_of_sealed
#check @FK.PlaneTopology.SealedSeparation.dualNonpercolationForcesPrimalAtMostOne_of_sealedExhaustion
#check @FK.PlaneTopology.SealedSeparation.globalAtMostOne_of_boxBorder_open

end FK.PlaneTopology.SealedSeparation
