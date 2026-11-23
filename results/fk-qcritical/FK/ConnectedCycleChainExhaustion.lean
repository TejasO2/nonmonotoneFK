import FK.JordanUnicyclicEnclosure
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# A connected chain of square-cycle windows

This module constructs one fixed connected locally finite simple graph.  Its
vertices are indexed by `ℕ` and by either a vertex of a four-cycle or one
pendant.  Consecutive four-cycles are joined at their north-east vertices.
The cycle and connector edges are open and every pendant is closed.

Each block is realized on the boundary of an origin-centred sup-norm square.
The only arcs which can cross the selected half-integral sphere are radial
connectors.  The prefix of the open chain through stage `n` contains all such
crossings and is open-connected.  Thus the fixed configuration has a genuine
cofinal spherical open-circuit exhaustion.  This is an explicit geometric
example, not a construction from dual nonpercolation or a general Jordan
theorem.
-/

namespace FK.PlaneTopology.ConnectedCycleChainExhaustion

open Set Metric unitInterval
open scoped Classical Topology
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.ConventionGeometry
open FK.PlaneTopology.UnicyclicEnclosure.PolygonDigon

abbrev Core := Fin 4
abbrev BlockVertex := Option Core
abbrev Vertex := ℕ × BlockVertex

/-- The four-cycle, with a pendant attached to vertex `1`. -/
def blockAdj : BlockVertex → BlockVertex → Prop
  | some u, some v => (SimpleGraph.cycleGraph 4).Adj u v
  | some u, none => u = 1
  | none, some v => v = 1
  | none, none => False

lemma blockAdj_symm {u v : BlockVertex} (h : blockAdj u v) : blockAdj v u := by
  cases u with
  | none => cases v with
    | none => exact h.elim
    | some b => exact h
  | some a => cases v with
    | none => exact h
    | some b => exact h.symm

/-- One open radial connector joins north-east vertices in consecutive blocks. -/
def graph : SimpleGraph Vertex where
  Adj x y :=
    (x.1 = y.1 ∧ blockAdj x.2 y.2) ∨
      (x.2 = some 1 ∧ y.2 = some 1 ∧ (x.1 + 1 = y.1 ∨ y.1 + 1 = x.1))
  symm := ⟨by
    intro x y hxy
    rcases hxy with h | h
    · exact Or.inl ⟨h.1.symm, blockAdj_symm h.2⟩
    · exact Or.inr ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · have hb := h.2
      cases hx : x.2 with
      | none =>
          rw [hx] at hb
          exact hb.elim
      | some a =>
          rw [hx] at hb
          exact hb.ne rfl
    · rcases h.2.2 with h' | h' <;> omega⟩

/-- Inclusion of the actual simple four-cycle in block `n`. -/
def blockHom (n : ℕ) : SimpleGraph.cycleGraph 4 →g graph where
  toFun u := (n, some u)
  map_rel' h := Or.inl ⟨rfl, h⟩

lemma blockHom_injective (n : ℕ) : Function.Injective (blockHom n) := by
  intro u v h
  exact Option.some.inj (Prod.mk.inj h).2

/-- The embedded image of the standard four-edge cycle. -/
def embeddedCycle (n : ℕ) : graph.Walk (n, some 0) (n, some 0) :=
  (SimpleGraph.cycleGraph.cycle 1).map (blockHom n)

theorem embeddedCycle_isCycle (n : ℕ) : (embeddedCycle n).IsCycle :=
  SimpleGraph.cycleGraph.isCycle_cycle.map (blockHom_injective n)

@[simp] theorem embeddedCycle_length (n : ℕ) : (embeddedCycle n).length = 4 := by
  exact (SimpleGraph.Walk.length_map (blockHom n)
    (SimpleGraph.cycleGraph.cycle 1)).trans SimpleGraph.cycleGraph.length_cycle

/-- The pendant in block `n`. -/
def pendantAdj (n : ℕ) : graph.Adj (n, some 1) (n, none) :=
  Or.inl ⟨rfl, rfl⟩

/-- The open radial connector after block `n`. -/
def connectorAdj (n : ℕ) : graph.Adj (n, some 1) (n + 1, some 1) :=
  Or.inr ⟨rfl, rfl, Or.inl rfl⟩

/-- Every vertex of one block reaches its north-east core vertex. -/
lemma reachable_block_one (n : ℕ) (u : BlockVertex) :
    graph.Reachable (n, u) (n, some 1) := by
  cases u with
  | none => exact (pendantAdj n).symm.reachable
  | some a =>
      exact (SimpleGraph.preconnected_cycleGraph a 1).map (blockHom n)

/-- The north-east vertices form a chain reaching every block from block zero. -/
lemma reachable_zero_one (n : ℕ) : graph.Reachable (0, some 1) (n, some 1) := by
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih => exact ih.trans (connectorAdj n).reachable

/-- The infinite graph is connected, including every pendant vertex. -/
theorem graph_connected : graph.Connected := by
  apply graph.connected_iff_exists_forall_reachable.2
  refine ⟨(0, some 1), ?_⟩
  rintro ⟨n, u⟩
  exact (reachable_zero_one n).trans (reachable_block_one n u).symm

/-- Connector edges change the block index by one and all other edges preserve it. -/
lemma index_le_succ_of_adj {x y : Vertex} (hxy : graph.Adj x y) :
    y.1 ≤ x.1 + 1 := by
  rcases hxy with h | h
  · exact Nat.le_of_eq h.1.symm |>.trans (Nat.le_add_right _ _)
  · rcases h.2.2 with h | h <;> omega

/-- Every vertex has only finitely many neighbours: their block indices are bounded. -/
noncomputable instance graphLocallyFinite : graph.LocallyFinite := by
  intro x
  apply (((Set.finite_le_nat (x.1 + 1)).prod
    (Set.finite_univ : (Set.univ : Set BlockVertex).Finite)).subset ?_).fintype
  intro y hy
  exact ⟨index_le_succ_of_adj hy, Set.mem_univ _⟩

/-- The pendant edge in block `n`. -/
def pendantEdge (n : ℕ) : graph.edgeSet :=
  ⟨s((n, some 1), (n, none)), pendantAdj n⟩

/-- The radial connector following block `n`. -/
def connectorEdge (n : ℕ) : graph.edgeSet :=
  ⟨s((n, some 1), (n + 1, some 1)), connectorAdj n⟩

/-- All non-pendant edges are open; every pendant is closed. -/
noncomputable def configuration : graph.edgeSet → Bool :=
  fun e => if ∃ n, e = pendantEdge n then false else true

lemma configuration_pendant (n : ℕ) : configuration (pendantEdge n) = false := by
  simp [configuration]

/-- Radial connectors are genuinely open in the fixed configuration. -/
lemma configuration_connector (n : ℕ) : configuration (connectorEdge n) = true := by
  rw [configuration, if_neg]
  rintro ⟨m, hm⟩
  have h := congrArg Subtype.val hm
  change s((n, some 1), (n + 1, some 1)) = s((m, some 1), (m, none)) at h
  rcases Sym2.eq_iff.mp h with h | h <;> simp at h

/-- The fixed configuration is not the all-open configuration. -/
theorem configuration_ne_allOpen : configuration ≠ (fun _ => true) := by
  intro h
  have h' := congrFun h (pendantEdge 0)
  rw [configuration_pendant] at h'
  exact Bool.false_ne_true h'

/-- Non-pendant edges whose incident core vertices lie in the first `N+1`
blocks.  This is a finite prefix of the fixed open chain. -/
def prefixLabels (N : ℕ) : Set graph.edgeSet :=
  {e | configuration e = true ∧
    ∀ x ∈ (e : Sym2 Vertex), x.1 ≤ N ∧ ∃ a : Core, x.2 = some a}

/-- Only finitely many labels belong to a prefix. -/
theorem finite_prefixLabels (N : ℕ) : (prefixLabels N).Finite := by
  let VN : Set Vertex := {x | x.1 ≤ N}
  have hVN : VN.Finite := by
    rw [show VN = {n : ℕ | n ≤ N} ×ˢ (Set.univ : Set BlockVertex) by
      ext x
      simp [VN]]
    exact (Set.finite_le_nat N).prod Set.finite_univ
  let f : graph.edgeSet → Vertex × Vertex := fun e => (e : Sym2 Vertex).out
  apply Set.Finite.of_finite_image (s := prefixLabels N) (f := f) ?_ ?_
  · apply (hVN.prod hVN).subset
    rintro z ⟨e, he, rfl⟩
    exact ⟨(he.2 _ (Sym2.out_fst_mem (e : Sym2 Vertex))).1,
      (he.2 _ (Sym2.out_snd_mem (e : Sym2 Vertex))).1⟩
  · intro e he g hg hfg
    apply Subtype.ext
    have heq : s((e : Sym2 Vertex).out.1, (e : Sym2 Vertex).out.2) =
        s((g : Sym2 Vertex).out.1, (g : Sym2 Vertex).out.2) :=
      congrArg (fun p : Vertex × Vertex => s(p.1, p.2)) hfg
    calc
      (e : Sym2 Vertex) = s((e : Sym2 Vertex).out.1, (e : Sym2 Vertex).out.2) :=
        (Quot.out_eq _).symm
      _ = s((g : Sym2 Vertex).out.1, (g : Sym2 Vertex).out.2) := heq
      _ = (g : Sym2 Vertex) := Quot.out_eq _

/-- An edge with two core endpoints cannot be a pendant edge. -/
lemma configuration_of_core_adj {x y : Vertex} {a b : Core}
    (hxy : graph.Adj x y) (hx : x.2 = some a) (hy : y.2 = some b) :
    configuration ⟨s(x, y), hxy⟩ = true := by
  rw [configuration, if_neg]
  rintro ⟨n, hn⟩
  have h := congrArg Subtype.val hn
  change s(x, y) = s((n, some 1), (n, none)) at h
  rcases Sym2.eq_iff.mp h with h | h
  · have hh := congrArg (fun z : Vertex => z.2) h.2
    rw [hy] at hh
    contradiction
  · have hh := congrArg (fun z : Vertex => z.2) h.1
    rw [hx] at hh
    contradiction

/-- Membership of a core edge in the underlying prefix carrier. -/
lemma mem_labelCarrier_prefix_of_adj (N : ℕ) {x y : Vertex} {a b : Core}
    (hxy : graph.Adj x y) (hxN : x.1 ≤ N) (hyN : y.1 ≤ N)
    (hx : x.2 = some a) (hy : y.2 = some b) :
    s(x, y) ∈ LabelCarrier (prefixLabels N) := by
  refine ⟨⟨s(x, y), hxy⟩, ⟨configuration_of_core_adj hxy hx hy, ?_⟩, rfl⟩
  intro z hz
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact ⟨hxN, a, hx⟩
  · exact ⟨hyN, b, hy⟩

/-- A four-cycle edge in a retained block belongs to the prefix carrier. -/
lemma mem_prefix_cycle (N n : ℕ) (hn : n ≤ N) {u v : Core}
    (huv : (SimpleGraph.cycleGraph 4).Adj u v) :
    s((n, some u), (n, some v)) ∈ LabelCarrier (prefixLabels N) := by
  exact mem_labelCarrier_prefix_of_adj N (Or.inl ⟨rfl, huv⟩) hn hn rfl rfl

/-- A connector whose two blocks are retained belongs to the prefix carrier. -/
lemma mem_prefix_connector (N n : ℕ) (hn : n + 1 ≤ N) :
    s((n, some 1), (n + 1, some 1)) ∈ LabelCarrier (prefixLabels N) := by
  exact mem_labelCarrier_prefix_of_adj N (connectorAdj n) (by omega) hn rfl rfl

/-- Open connection inside one retained square, using only square labels. -/
lemma openConnected_block_one_prefix (N n : ℕ) (hn : n ≤ N) (u : Core) :
    OpenConnected graph configuration (LabelCarrier (prefixLabels N))
      (n, some u) (n, some 1) := by
  obtain ⟨p⟩ := SimpleGraph.preconnected_cycleGraph u 1
  refine ⟨p.map (blockHom n), ?_⟩
  generalize (1 : Core) = v at p ⊢
  induction p with
  | nil => exact isOpenIn_nil
  | @cons a b c hab p ih =>
      rw [SimpleGraph.Walk.map_cons]
      apply isOpenIn_cons.mpr
      refine ⟨⟨?_, ?_⟩, ih⟩
      · exact mem_prefix_cycle N n hn hab
      · exact configuration_of_core_adj _ rfl rfl

/-- Open connection through the retained chain of radial connectors. -/
lemma openConnected_zero_one_prefix (N n : ℕ) (hn : n ≤ N) :
    OpenConnected graph configuration (LabelCarrier (prefixLabels N))
      (0, some 1) (n, some 1) := by
  induction n with
  | zero => exact OpenConnected.refl _ _ _
  | succ n ih =>
      exact (ih (by omega)).trans (OpenConnected.of_adj (connectorAdj n)
        (mem_prefix_connector N n hn) (configuration_of_core_adj _ rfl rfl))

/-- Any retained core vertex is joined to the block-zero connector vertex. -/
lemma openConnected_zero_core_prefix (N n : ℕ) (hn : n ≤ N) (u : Core) :
    OpenConnected graph configuration (LabelCarrier (prefixLabels N))
      (0, some 1) (n, some u) := by
  exact (openConnected_zero_one_prefix N n hn).trans
    (openConnected_symm (openConnected_block_one_prefix N n hn u))

/-- Every vertex incident to a prefix label has retained block index and is a
core vertex; pendant vertices are excluded by the definition itself. -/
lemma index_le_of_vertexOnLabels_prefix {N : ℕ} {u : Vertex}
    (hu : VertexOnLabels (prefixLabels N) u) : u.1 ≤ N := by
  obtain ⟨v, huv, he⟩ := hu
  exact (he.2 u (by simp)).1

lemma exists_core_of_vertexOnLabels_prefix {N : ℕ} {u : Vertex}
    (hu : VertexOnLabels (prefixLabels N) u) : ∃ a : Core, u.2 = some a := by
  obtain ⟨v, huv, he⟩ := hu
  exact (he.2 u (by simp)).2

/-- The prefix labels are open by definition. -/
lemma prefixLabels_open (N : ℕ) :
    ∀ e ∈ prefixLabels N, configuration e = true := by
  intro e he
  exact he.1

/-- The incident vertices of the finite prefix form one genuinely open
component using only the underlying prefix labels. -/
theorem openLabelConnected_prefix (N : ℕ) :
    OpenLabelConnected graph configuration (prefixLabels N) := by
  intro u v hu hv
  obtain ⟨a, ha⟩ := exists_core_of_vertexOnLabels_prefix hu
  obtain ⟨b, hb⟩ := exists_core_of_vertexOnLabels_prefix hv
  rcases u with ⟨n, u⟩
  rcases v with ⟨m, v⟩
  dsimp at ha hb
  subst u
  subst v
  exact (openConnected_symm (openConnected_zero_core_prefix N n
    (index_le_of_vertexOnLabels_prefix hu) a)).trans
      (openConnected_zero_core_prefix N m (index_le_of_vertexOnLabels_prefix hv) b)

/-- Outer square scale of block `n`. -/
def scale (n : ℕ) : ℝ := 4 * (n + 1)

lemma scale_pos (n : ℕ) : 0 < scale n := by
  unfold scale
  positivity

lemma scale_nonneg (n : ℕ) : 0 ≤ scale n := (scale_pos n).le

lemma scale_mono : Monotone scale := by
  intro m n h
  dsimp [scale]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right h 1) (by norm_num)

noncomputable def radius (n : ℕ) : ℝ := n + 1 / 2

lemma radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

lemma scale_ne_radius (m n : ℕ) : scale m ≠ radius n := by
  intro h
  have heq : ((2 * n : ℕ) : ℝ) = ((8 * m + 7 : ℕ) : ℝ) := by
    push_cast
    dsimp [scale, radius] at h
    nlinarith [h]
  have heqnat : 2 * n = 8 * m + 7 := by exact_mod_cast heq
  omega

/-- The four square corners. -/
def corePoint (a : ℝ) : Core → ℝ × ℝ :=
  ![(-a, a), (a, a), (a, -a), (-a, -a)]

/-- The pendant lies on the east side of the same square. -/
def blockPoint (a : ℝ) : BlockVertex → ℝ × ℝ
  | some u => corePoint a u
  | none => (a, 0)

/-- Fixed proper embedding of the chain of blocks. -/
def vertex (x : Vertex) : ℝ × ℝ := blockPoint (scale x.1) x.2

lemma dist_corePoint (a : ℝ) (ha : 0 ≤ a) (u : Core) :
    dist (corePoint a u) 0 = a := by
  fin_cases u <;>
    simp [corePoint, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      abs_of_nonneg ha, max_eq_left ha]

lemma dist_blockPoint (a : ℝ) (ha : 0 ≤ a) (u : BlockVertex) :
    dist (blockPoint a u) 0 = a := by
  cases u with
  | none =>
      simp [blockPoint, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        abs_of_nonneg ha, max_eq_left ha]
  | some v => exact dist_corePoint a ha v

lemma dist_vertex (x : Vertex) : dist (vertex x) 0 = scale x.1 := by
  exact dist_blockPoint _ (scale_nonneg x.1) x.2

/-- No embedded vertex lies on a selected sphere. -/
theorem vertex_off (n : ℕ) (x : Vertex) :
    vertex x ∈ (sphere (0 : ℝ × ℝ) (radius n))ᶜ := by
  simp only [Set.mem_compl_iff, Metric.mem_sphere]
  rw [dist_vertex]
  exact scale_ne_radius x.1 n

/-- The fixed embedding is proper on metric balls.  A vertex in radius `r`
has block index below `⌈r⌉₊`, and each block has only five vertices. -/
theorem finite_vertex_preimage_ball (r : ℝ) :
    (vertex ⁻¹' ball 0 r).Finite := by
  let N := ⌈r⌉₊
  have hindices : {n : ℕ | scale n < r} ⊆ Iio N := by
    intro n hn
    have hnreal : (n : ℝ) < r := by
      have hlt : (n : ℝ) < scale n := by
        dsimp [scale]
        have hnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      exact hlt.trans hn
    exact Nat.lt_ceil.mpr hnreal
  have hfin : ({n : ℕ | scale n < r} ×ˢ
      (Set.univ : Set BlockVertex)).Finite :=
    ((Set.finite_Iio N).subset hindices).prod Set.finite_univ
  apply hfin.subset
  rintro ⟨n, v⟩ hx
  refine ⟨?_, Set.mem_univ v⟩
  change dist (vertex (n, v)) 0 < r at hx
  rw [dist_vertex] at hx
  exact hx

/-- Fixed straight-segment realization. -/
noncomputable def realization : OpenPathRealization graph vertex where
  arc {x y} _ := straightPath (vertex x) (vertex y)

/-- A horizontal segment on a square side has constant sup-norm distance. -/
lemma dist_straightPath_const_snd (a x y : ℝ) (ha : 0 ≤ a)
    (hx : |x| ≤ a) (hy : |y| ≤ a) (t : I) :
    dist (straightPath ((x, a) : ℝ × ℝ) (y, a) t) 0 = a := by
  apply le_antisymm
  · apply dist_straightPath_le
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        abs_of_nonneg ha, max_eq_right hx]
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        abs_of_nonneg ha, max_eq_right hy]
  · have hlow := abs_snd_le_dist_straightPath a x y t
    simpa [abs_of_nonneg ha] using hlow

/-- A vertical segment on a square side has constant sup-norm distance. -/
lemma dist_straightPath_const_fst (a x y : ℝ) (ha : 0 ≤ a)
    (hx : |x| ≤ a) (hy : |y| ≤ a) (t : I) :
    dist (straightPath ((a, x) : ℝ × ℝ) (a, y) t) 0 = a := by
  apply le_antisymm
  · apply dist_straightPath_le
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        abs_of_nonneg ha, max_eq_left hx]
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
        abs_of_nonneg ha, max_eq_left hy]
  · have hlow := abs_fst_le_dist_straightPath a x y t
    simpa [abs_of_nonneg ha] using hlow

/-- A vertical straight segment with first coordinate of absolute value `a`
lies on the sphere of radius `a`. -/
lemma dist_straightPath_const_fst_abs (a b x y : ℝ) (ha : 0 ≤ a)
    (hb : |b| = a) (hx : |x| ≤ a) (hy : |y| ≤ a) (t : I) :
    dist (straightPath ((b, x) : ℝ × ℝ) (b, y) t) 0 = a := by
  apply le_antisymm
  · apply dist_straightPath_le
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, hb, max_eq_left hx]
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, hb, max_eq_left hy]
  · have hlow := abs_fst_le_dist_straightPath b x y t
    rwa [hb] at hlow

/-- A horizontal straight segment with second coordinate of absolute value `a`
lies on the sphere of radius `a`. -/
lemma dist_straightPath_const_snd_abs (a b x y : ℝ) (ha : 0 ≤ a)
    (hb : |b| = a) (hx : |x| ≤ a) (hy : |y| ≤ a) (t : I) :
    dist (straightPath ((x, b) : ℝ × ℝ) (y, b) t) 0 = a := by
  apply le_antisymm
  · apply dist_straightPath_le
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, hb, max_eq_right hx]
    · simp [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, hb, max_eq_right hy]
  · have hlow := abs_snd_le_dist_straightPath b x y t
    rwa [hb] at hlow

/-- Distance along a radial diagonal segment between `(a,a)` and `(b,b)`. -/
lemma dist_straightPath_diag (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (t : I) :
    dist (straightPath ((a, a) : ℝ × ℝ) (b, b) t) 0 =
      (1 - (t : ℝ)) * a + (t : ℝ) * b := by
  have ht : 0 ≤ (1 - (t : ℝ)) * a + (t : ℝ) * b :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) ha) (mul_nonneg t.2.1 hb)
  have hfst : ((straightPath ((a, a) : ℝ × ℝ) (b, b) t).1 : ℝ) =
      (1 - (t : ℝ)) * a + (t : ℝ) * b := by
    simp [straightPath, segmentArc_apply]
    ring
  have hsnd : ((straightPath ((a, a) : ℝ × ℝ) (b, b) t).2 : ℝ) =
      (1 - (t : ℝ)) * a + (t : ℝ) * b := by
    simp [straightPath, segmentArc_apply]
    ring
  rw [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    hfst, hsnd, max_self, abs_of_nonneg ht]

/-- Explicit oriented description of the ten block edges. -/
lemma blockAdj_cases {u v : BlockVertex} (h : blockAdj u v) :
    (u = some 0 ∧ v = some 1) ∨ (u = some 1 ∧ v = some 0) ∨
    (u = some 1 ∧ v = some 2) ∨ (u = some 2 ∧ v = some 1) ∨
    (u = some 2 ∧ v = some 3) ∨ (u = some 3 ∧ v = some 2) ∨
    (u = some 3 ∧ v = some 0) ∨ (u = some 0 ∧ v = some 3) ∨
    (u = some 1 ∧ v = none) ∨ (u = none ∧ v = some 1) := by
  cases u with
  | none =>
      cases v with
      | none => simp [blockAdj] at h
      | some b =>
          fin_cases b <;> simp [blockAdj] at h ⊢
  | some a =>
      cases v with
      | none =>
          fin_cases a <;> simp [blockAdj] at h ⊢
      | some b =>
          fin_cases a <;> fin_cases b <;>
            simp [blockAdj, SimpleGraph.cycleGraph_adj, Fin.ext_iff] at h ⊢ <;>
              norm_num at h ⊢
          all_goals
            revert h
            decide

/-- Every same-block edge, including a pendant edge, is realized on its own
square's sphere. -/
lemma dist_realization_blockArc {n : ℕ} {u v : BlockVertex}
    (h : blockAdj u v) (t : I) :
    dist (realization.arc (show graph.Adj (n, u) (n, v) from Or.inl ⟨rfl, h⟩) t) 0 =
      scale n := by
  have ha := scale_nonneg n
  rcases blockAdj_cases h with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩
  · change dist (straightPath ((-scale n, scale n) : ℝ × ℝ)
      (scale n, scale n) t) 0 = scale n
    exact dist_straightPath_const_snd_abs (scale n) (scale n) (-scale n) (scale n)
      ha (abs_of_nonneg ha) (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((scale n, scale n) : ℝ × ℝ)
      (-scale n, scale n) t) 0 = scale n
    exact dist_straightPath_const_snd_abs (scale n) (scale n) (scale n) (-scale n)
      ha (abs_of_nonneg ha) (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((scale n, scale n) : ℝ × ℝ)
      (scale n, -scale n) t) 0 = scale n
    exact dist_straightPath_const_fst_abs (scale n) (scale n) (scale n) (-scale n)
      ha (abs_of_nonneg ha) (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((scale n, -scale n) : ℝ × ℝ)
      (scale n, scale n) t) 0 = scale n
    exact dist_straightPath_const_fst_abs (scale n) (scale n) (-scale n) (scale n)
      ha (abs_of_nonneg ha) (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((scale n, -scale n) : ℝ × ℝ)
      (-scale n, -scale n) t) 0 = scale n
    exact dist_straightPath_const_snd_abs (scale n) (-scale n) (scale n) (-scale n)
      ha (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha])
        (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((-scale n, -scale n) : ℝ × ℝ)
      (scale n, -scale n) t) 0 = scale n
    exact dist_straightPath_const_snd_abs (scale n) (-scale n) (-scale n) (scale n)
      ha (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha])
        (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((-scale n, -scale n) : ℝ × ℝ)
      (-scale n, scale n) t) 0 = scale n
    exact dist_straightPath_const_fst_abs (scale n) (-scale n) (-scale n) (scale n)
      ha (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha])
        (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((-scale n, scale n) : ℝ × ℝ)
      (-scale n, -scale n) t) 0 = scale n
    exact dist_straightPath_const_fst_abs (scale n) (-scale n) (scale n) (-scale n)
      ha (by simp [abs_of_nonneg ha]) (by simp [abs_of_nonneg ha])
        (by simp [abs_of_nonneg ha]) t
  · change dist (straightPath ((scale n, scale n) : ℝ × ℝ)
      (scale n, 0) t) 0 = scale n
    exact dist_straightPath_const_fst_abs (scale n) (scale n) (scale n) 0
      ha (abs_of_nonneg ha) (by simp [abs_of_nonneg ha]) (by simpa using ha) t
  · change dist (straightPath ((scale n, 0) : ℝ × ℝ)
      (scale n, scale n) t) 0 = scale n
    exact dist_straightPath_const_fst_abs (scale n) (scale n) 0 (scale n)
      ha (abs_of_nonneg ha) (by simpa using ha) (by simp [abs_of_nonneg ha]) t

/-- Reversing a straight segment is parametrized by unit-interval symmetry. -/
lemma straightPath_swap (x y : ℝ × ℝ) (t : I) :
    straightPath x y t = straightPath y x (unitInterval.symm t) := by
  apply Prod.ext <;>
    simp [straightPath, segmentArc_apply, unitInterval.coe_symm_eq] <;> ring

/-- If the connector from block `m` to `m+1` meets the selected sphere, its
larger endpoint lies in the corresponding retained prefix. -/
lemma connectorEnd_le_of_forward_cross (N m : ℕ) (t : I)
    (hcross : dist (straightPath ((scale m, scale m) : ℝ × ℝ)
      (scale (m + 1), scale (m + 1)) t) 0 = radius N) : m + 1 ≤ N := by
  rw [dist_straightPath_diag _ _ (scale_nonneg m) (scale_nonneg (m + 1)) t] at hcross
  have hmono := scale_mono (Nat.le_succ m)
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have hlow : scale m ≤ radius N := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hmono)]
  have hmN : m < N := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    dsimp [scale, radius] at hlow
    have hreal : (m : ℝ) < (N : ℝ) := by nlinarith
    exact_mod_cast hreal
  omega

/-- A retained connector is itself a prefix label, not only a member of its
underlying carrier. -/
lemma connectorEdge_mem_prefixLabels (N n : ℕ) (hn : n + 1 ≤ N) :
    connectorEdge n ∈ prefixLabels N := by
  refine ⟨configuration_connector n, ?_⟩
  intro x hx
  change x ∈ s((n, some 1), (n + 1, some 1)) at hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact ⟨by omega, 1, rfl⟩
  · exact ⟨hn, 1, rfl⟩

/-- All arcs meeting the selected sphere are controlled by the finite prefix.
Same-block arcs cannot meet it; a crossing connector must lie in the prefix. -/
theorem crossing_prefix (N : ℕ) :
    realization.CrossingControlledBy (sphere (0 : ℝ × ℝ) (radius N))
      (prefixLabels N) := by
  intro x y hxy hcross
  obtain ⟨t, ht⟩ := hcross
  have hdist := Metric.mem_sphere.mp ht
  rcases x with ⟨m, u⟩
  rcases y with ⟨n, v⟩
  rcases hxy with hxy | hxy
  · have hmn : m = n := hxy.1
    subst n
    have heq : scale m = radius N :=
      (dist_realization_blockArc hxy.2 t).symm.trans hdist
    exact (scale_ne_radius m N heq).elim
  · obtain ⟨hu, hv, hmn⟩ := hxy
    dsimp at hu hv hmn
    subst u
    subst v
    rcases hmn with hmn | hmn
    · subst n
      have hend : m + 1 ≤ N := by
        apply connectorEnd_le_of_forward_cross N m t
        exact hdist
      exact connectorEdge_mem_prefixLabels N m hend
    · subst m
      have hpath := straightPath_swap
        ((scale (n + 1), scale (n + 1)) : ℝ × ℝ) (scale n, scale n) t
      have hforward : dist (straightPath ((scale n, scale n) : ℝ × ℝ)
          (scale (n + 1), scale (n + 1)) (unitInterval.symm t)) 0 = radius N := by
        rw [← hpath]
        exact hdist
      have hend : n + 1 ≤ N := connectorEnd_le_of_forward_cross N n _ hforward
      have heq : (⟨s((n + 1, some 1), (n, some 1)),
          Or.inr ⟨rfl, rfl, Or.inr rfl⟩⟩ : graph.edgeSet) = connectorEdge n := by
        apply Subtype.ext
        exact Sym2.eq_swap
      rw [heq]
      exact connectorEdge_mem_prefixLabels N n hend

/-- Each retained prefix is an actual spherical open circuit of the fixed
connected graph and its fixed non-all-open configuration. -/
theorem sphericalOpenCircuit_prefix (N : ℕ) :
    SphericalOpenCircuit realization configuration (prefixLabels N) 0 (radius N) where
  radius_pos := radius_pos N
  crossing := crossing_prefix N
  vertex_off := vertex_off N
  label_open := prefixLabels_open N
  openConnected := openLabelConnected_prefix N

/-- Half-integral radii are cofinal, yielding a genuine open-circuit
exhaustion of the one fixed realization and configuration. -/
theorem hasOpenCircuitExhaustion :
    HasOpenCircuitExhaustion realization configuration 0 := by
  intro ρ
  obtain ⟨n, hn⟩ := exists_nat_gt ρ
  refine ⟨prefixLabels n, radius n, ?_, sphericalOpenCircuit_prefix n⟩
  dsimp [radius]
  nlinarith

/-- The block-zero connector vertex has an infinite open component.  Thus the
subsequent uniqueness statement is not vacuous. -/
theorem exteriorInfiniteCluster_zero :
    ExteriorInfiniteCluster graph configuration Set.univ (0, some 1) := by
  let f : ℕ → Vertex := fun n => (n, some 0)
  have hf : Function.Injective f := by
    intro m n h
    exact congrArg Prod.fst h
  apply (Set.infinite_range_of_injective hf).mono
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact (openConnected_zero_core_prefix n n (Nat.le_refl n) 0).mono_edges
    (Set.subset_univ _)

/-- The fixed connected locally finite graph has at most one infinite open
component in its fixed two-valued configuration. -/
theorem globalAtMostOne :
    FK.InfiniteVolume.ConventionTransport.GlobalAtMostOne graph configuration := by
  exact globalAtMostOne_of_openCircuitExhaustion realization configuration 0
    finite_vertex_preimage_ball hasOpenCircuitExhaustion

end FK.PlaneTopology.ConnectedCycleChainExhaustion
