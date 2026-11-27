import FK.EncounterTreeBound
import FK.BurtonKeaneGeometry
import CurvatureVariance.Infra.Percolation.Balls
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Finite trees obtained from three separated arms

This file constructs the graph determined by the edges of three simple paths.
The paths are truncated at their first exit from an open metric ball.  Extra
ambient-graph chords are deliberately not included in the encounter tree.
-/

open scoped Classical BigOperators
open Finset
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The coe graph of the subgraph of a simple path is a tree. -/
theorem isTree_toSubgraph_coe {x z : V} (p : G.Walk x z) (hp : p.IsPath) :
    p.toSubgraph.coe.IsTree := by
  exact hp.pathGraphIsoToSubgraph.isTree_iff.mp
    (SimpleGraph.isTree_pathGraph_add_one p.length)

/-- The edge type of a subgraph and of its coe graph have the same cardinality. -/
theorem natCard_coe_edgeSet (H : G.Subgraph) :
    Nat.card H.coe.edgeSet = Nat.card H.edgeSet := by
  change H.coe.edgeSet.ncard = H.edgeSet.ncard
  calc
    H.coe.edgeSet.ncard = (Sym2.map ((↑) : H.verts → V) '' H.coe.edgeSet).ncard :=
      (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.coe_injective)).symm
    _ = H.edgeSet.ncard := congrArg Set.ncard H.image_coe_edgeSet_coe

/-- Glue two finite subgraph trees along exactly one vertex. -/
theorem isTree_sup_of_inter_eq_singleton {H K : G.Subgraph}
    (hH : H.coe.IsTree) (hK : K.coe.IsTree) (y : V)
    (hverts : H.verts ∩ K.verts = {y})
    (hHV : H.verts.Finite) (hKV : K.verts.Finite)
    (hHE : H.edgeSet.Finite) (hKE : K.edgeSet.Finite) :
    (H ⊔ K).coe.IsTree := by
  letI : Finite H.verts := hHV.to_subtype
  letI : Finite K.verts := hKV.to_subtype
  letI : Finite H.edgeSet := hHE.to_subtype
  letI : Finite K.edgeSet := hKE.to_subtype
  have hsupV : (H ⊔ K).verts.Finite := by
    rw [SimpleGraph.Subgraph.verts_sup]
    exact hHV.union hKV
  letI : Finite (H ⊔ K).verts := hsupV.to_subtype
  have hconn : (H ⊔ K).Connected := by
    apply SimpleGraph.Subgraph.connected_sup
      ⟨hH.connected.preconnected⟩ ⟨hK.connected.preconnected⟩
    rw [show (H ⊓ K).verts = H.verts ∩ K.verts from rfl, hverts]
    exact Set.singleton_nonempty y
  have hedgeDisj : Disjoint H.edgeSet K.edgeSet := by
    rw [Set.disjoint_left]
    intro e heH heK
    induction e using Sym2.ind with
    | _ u v =>
      have huH : H.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp heH
      have huK : K.Adj u v := SimpleGraph.Subgraph.mem_edgeSet.mp heK
      have hu : u ∈ H.verts ∩ K.verts := ⟨H.edge_vert huH, K.edge_vert huK⟩
      have hv : v ∈ H.verts ∩ K.verts :=
        ⟨H.edge_vert huH.symm, K.edge_vert huK.symm⟩
      rw [hverts] at hu hv
      have huy : u = y := by simpa using hu
      have hvy : v = y := by simpa using hv
      subst u
      subst v
      exact huH.ne rfl
  have hcardE : Nat.card (H ⊔ K).edgeSet =
      Nat.card H.edgeSet + Nat.card K.edgeSet := by
    rw [SimpleGraph.Subgraph.edgeSet_sup]
    exact Set.ncard_union_eq hedgeDisj hHE hKE
  have hcardV : Nat.card (H ⊔ K).verts + 1 =
      Nat.card H.verts + Nat.card K.verts := by
    rw [SimpleGraph.Subgraph.verts_sup]
    have hcard := Set.ncard_union_add_ncard_inter H.verts K.verts hHV hKV
    rw [hverts, Set.ncard_singleton] at hcard
    exact hcard
  have hcardH := (SimpleGraph.isTree_iff_connected_and_card.mp hH).2
  have hcardK := (SimpleGraph.isTree_iff_connected_and_card.mp hK).2
  rw [natCard_coe_edgeSet] at hcardH hcardK
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn.coe, ?_⟩
  rw [natCard_coe_edgeSet, hcardE]
  omega

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- The vertex set of a walk subgraph is finite. -/
theorem finite_verts_toSubgraph {x z : V} (p : G.Walk x z) :
    p.toSubgraph.verts.Finite := by
  rw [SimpleGraph.Walk.verts_toSubgraph]
  simpa using p.support.toFinset.finite_toSet

/-- The edge set of a walk subgraph is finite. -/
theorem finite_edges_toSubgraph {x z : V} (p : G.Walk x z) :
    p.toSubgraph.edgeSet.Finite := by
  rw [SimpleGraph.Walk.edgeSet_toSubgraph]
  change {e | e ∈ p.edges}.Finite
  rw [show {e | e ∈ p.edges} = (↑p.edges.toFinset : Set (Sym2 V)) from by
    ext e
    simp]
  exact p.edges.toFinset.finite_toSet

/-- Two paths starting at `y` and otherwise separated have subgraph vertex
intersection exactly `{y}`. -/
theorem inter_verts_toSubgraph {y a b : V} (p : G.Walk y a) (q : G.Walk y b)
    (hsep : ∀ z ∈ p.support, z ∈ q.support → z = y) :
    p.toSubgraph.verts ∩ q.toSubgraph.verts = {y} := by
  ext z
  simp only [SimpleGraph.Walk.mem_verts_toSubgraph, Set.mem_inter_iff,
    Set.mem_singleton_iff]
  exact ⟨fun ⟨hzp, hzq⟩ => hsep z hzp hzq, by
    intro hzy
    subst z
    exact ⟨p.start_mem_support, q.start_mem_support⟩⟩

/-- The subgraph determined by the edges of three paths. -/
def triplePathSubgraph {y a b c : V} (p : G.Walk y a) (q : G.Walk y b)
    (r : G.Walk y c) : G.Subgraph :=
  (p.toSubgraph ⊔ q.toSubgraph) ⊔ r.toSubgraph

/-- Three simple paths with common start and otherwise pairwise disjoint
supports determine a finite tree. -/
theorem isTree_triplePathSubgraph {y a b c : V} (p : G.Walk y a)
    (q : G.Walk y b) (r : G.Walk y c)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hpq : ∀ z ∈ p.support, z ∈ q.support → z = y)
    (hpr : ∀ z ∈ p.support, z ∈ r.support → z = y)
    (hqr : ∀ z ∈ q.support, z ∈ r.support → z = y) :
    (triplePathSubgraph p q r).coe.IsTree := by
  have hpqVert := inter_verts_toSubgraph p q hpq
  have hpqTree : (p.toSubgraph ⊔ q.toSubgraph).coe.IsTree :=
    isTree_sup_of_inter_eq_singleton (isTree_toSubgraph_coe p hp)
      (isTree_toSubgraph_coe q hq) y hpqVert
      (finite_verts_toSubgraph p) (finite_verts_toSubgraph q)
      (finite_edges_toSubgraph p) (finite_edges_toSubgraph q)
  apply isTree_sup_of_inter_eq_singleton hpqTree (isTree_toSubgraph_coe r hr) y
    _ _ _ _ _
  · ext z
    simp only [SimpleGraph.Subgraph.verts_sup,
      SimpleGraph.Walk.mem_verts_toSubgraph, Set.mem_inter_iff, Set.mem_union,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzp | hzq, hzr⟩
      · exact hpr z hzp hzr
      · exact hqr z hzq hzr
    · intro hzy
      subst z
      exact ⟨Or.inl p.start_mem_support, r.start_mem_support⟩
  · rw [SimpleGraph.Subgraph.verts_sup]
    exact (finite_verts_toSubgraph p).union (finite_verts_toSubgraph q)
  · exact finite_verts_toSubgraph r
  · rw [SimpleGraph.Subgraph.edgeSet_sup]
    exact (finite_edges_toSubgraph p).union (finite_edges_toSubgraph q)
  · exact finite_edges_toSubgraph r

/-- Finiteness of the vertex type of a three-path tree. -/
theorem finite_verts_triplePathSubgraph {y a b c : V} (p : G.Walk y a)
    (q : G.Walk y b) (r : G.Walk y c) :
    (triplePathSubgraph p q r).verts.Finite := by
  simp only [triplePathSubgraph, SimpleGraph.Subgraph.verts_sup]
  exact ((finite_verts_toSubgraph p).union (finite_verts_toSubgraph q)).union
    (finite_verts_toSubgraph r)

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Three pairwise distinct elements force finite cardinality at least three. -/
theorem three_le_card_of_distinct {α : Type*} [Fintype α] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Fintype.card α := by
  let f : Fin 3 → α := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa using Fintype.card_le_of_injective f hf

/-- The next vertex on a non-nil simple path differs from its start. -/
theorem snd_ne_start {y z : V} (p : G.Walk y z) (hp : p.IsPath) (hnp : ¬p.Nil) :
    p.snd ≠ y := by
  intro hs
  have hi : 1 ≤ p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hnp
  have hzero := (hp.getVert_eq_start_iff hi).mp hs
  omega

/-- The centre of three non-nil separated arms has degree at least three in
their edge union. -/
theorem three_le_degree_triplePathSubgraph {y a b c : V} (p : G.Walk y a)
    (q : G.Walk y b) (r : G.Walk y c)
    [Fintype (triplePathSubgraph p q r).verts]
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hnp : ¬p.Nil) (hnq : ¬q.Nil) (hnr : ¬r.Nil)
    (hpq : ∀ z ∈ p.support, z ∈ q.support → z = y)
    (hpr : ∀ z ∈ p.support, z ∈ r.support → z = y)
    (hqr : ∀ z ∈ q.support, z ∈ r.support → z = y) :
    3 ≤ (triplePathSubgraph p q r).degree y := by
  classical
  let U := triplePathSubgraph p q r
  have hpU : p.toSubgraph ≤ U := by
    exact le_sup_left.trans le_sup_left
  have hqU : q.toSubgraph ≤ U := by
    exact le_sup_right.trans le_sup_left
  have hrU : r.toSubgraph ≤ U := le_sup_right
  have hpMem : p.snd ∈ p.support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (p.toSubgraph_adj_snd hnp).snd_mem
  have hqMem : q.snd ∈ q.support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (q.toSubgraph_adj_snd hnq).snd_mem
  have hrMem : r.snd ∈ r.support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (r.toSubgraph_adj_snd hnr).snd_mem
  have hsndpq : p.snd ≠ q.snd := by
    intro heq
    apply snd_ne_start p hp hnp
    exact hpq p.snd hpMem (by rw [heq]; exact hqMem)
  have hsndpr : p.snd ≠ r.snd := by
    intro heq
    apply snd_ne_start p hp hnp
    exact hpr p.snd hpMem (by rw [heq]; exact hrMem)
  have hsndqr : q.snd ≠ r.snd := by
    intro heq
    apply snd_ne_start q hq hnq
    exact hqr q.snd hqMem (by rw [heq]; exact hrMem)
  let np : U.neighborSet y := ⟨p.snd, hpU.2 (p.toSubgraph_adj_snd hnp)⟩
  let nq : U.neighborSet y := ⟨q.snd, hqU.2 (q.toSubgraph_adj_snd hnq)⟩
  let nr : U.neighborSet y := ⟨r.snd, hrU.2 (r.toSubgraph_adj_snd hnr)⟩
  change 3 ≤ Fintype.card (U.neighborSet y)
  apply three_le_card_of_distinct np nq nr
  · intro heq
    exact hsndpq (congrArg Subtype.val heq)
  · intro heq
    exact hsndpr (congrArg Subtype.val heq)
  · intro heq
    exact hsndqr (congrArg Subtype.val heq)

/-- Every internal vertex of one branch has degree at least two in the
three-path edge union. -/
theorem two_le_degree_triplePathSubgraph_of_internal {y a b c z : V}
    (p : G.Walk y a) (q : G.Walk y b) (r : G.Walk y c)
    [Fintype (triplePathSubgraph p q r).verts]
    (hp : p.IsPath) {i : ℕ} (hi0 : i ≠ 0) (hil : i < p.length)
    (hzi : p.getVert i = z) :
    2 ≤ (triplePathSubgraph p q r).degree z := by
  classical
  letI : Fintype p.toSubgraph.verts := (finite_verts_toSubgraph p).fintype
  have hpU : p.toSubgraph ≤ triplePathSubgraph p q r := le_sup_left.trans le_sup_left
  have hpathDegree : p.toSubgraph.degree z = 2 := by
    subst z
    change Fintype.card (p.toSubgraph.neighborSet (p.getVert i)) = 2
    rw [Set.fintypeCard_eq_ncard]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil
  have hle := SimpleGraph.Subgraph.degree_le' p.toSubgraph
    (triplePathSubgraph p q r) hpU z
  rwa [hpathDegree] at hle

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A degree-one vertex on a path contained in a graph is either the path's
start or its end. -/
theorem eq_end_of_degree_eq_one_of_mem {y a z : V} {U : G.Subgraph}
    (p : G.Walk y a) [Fintype U.verts] (hpU : p.toSubgraph ≤ U)
    (hp : p.IsPath) (hz : z ∈ p.support) (hzy : z ≠ y)
    (hdeg : U.degree z = 1) : z = a := by
  classical
  letI : Fintype p.toSubgraph.verts := (finite_verts_toSubgraph p).fintype
  obtain ⟨i, hzi, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    rw [p.getVert_zero] at hzi
    exact hzy hzi.symm
  by_contra hza
  have hil : i < p.length := by
    apply lt_of_le_of_ne hi
    intro hieq
    apply hza
    rw [← hzi, hieq, p.getVert_length]
  have hpathDegree : p.toSubgraph.degree z = 2 := by
    rw [← hzi]
    change Fintype.card (p.toSubgraph.neighborSet (p.getVert i)) = 2
    rw [Set.fintypeCard_eq_ncard]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil
  have hle := SimpleGraph.Subgraph.degree_le' p.toSubgraph U hpU z
  rw [hpathDegree, hdeg] at hle
  omega

/-- Every degree-one vertex of the three-path edge union is one of its three
terminal vertices, provided all three branches are non-nil and otherwise
separated. -/
theorem eq_end_of_degree_eq_one_triplePathSubgraph {y a b c z : V}
    (p : G.Walk y a) (q : G.Walk y b) (r : G.Walk y c)
    [Fintype (triplePathSubgraph p q r).verts]
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hnp : ¬p.Nil) (hnq : ¬q.Nil) (hnr : ¬r.Nil)
    (hpq : ∀ z ∈ p.support, z ∈ q.support → z = y)
    (hpr : ∀ z ∈ p.support, z ∈ r.support → z = y)
    (hqr : ∀ z ∈ q.support, z ∈ r.support → z = y)
    (hz : z ∈ (triplePathSubgraph p q r).verts)
    (hdeg : (triplePathSubgraph p q r).degree z = 1) :
    z = a ∨ z = b ∨ z = c := by
  have hpU : p.toSubgraph ≤ triplePathSubgraph p q r := le_sup_left.trans le_sup_left
  have hqU : q.toSubgraph ≤ triplePathSubgraph p q r := le_sup_right.trans le_sup_left
  have hrU : r.toSubgraph ≤ triplePathSubgraph p q r := le_sup_right
  have hcentre : 3 ≤ (triplePathSubgraph p q r).degree y :=
    three_le_degree_triplePathSubgraph p q r hp hq hr hnp hnq hnr hpq hpr hqr
  have hzy : z ≠ y := by
    intro hzy
    subst z
    omega
  simp only [triplePathSubgraph, SimpleGraph.Subgraph.verts_sup,
    SimpleGraph.Walk.mem_verts_toSubgraph, Set.mem_union] at hz
  rcases hz with (hzp | hzq) | hzr
  · exact Or.inl (eq_end_of_degree_eq_one_of_mem p hpU hp hzp hzy hdeg)
  · exact Or.inr (Or.inl (eq_end_of_degree_eq_one_of_mem q hqU hq hzq hzy hdeg))
  · exact Or.inr (Or.inr (eq_end_of_degree_eq_one_of_mem r hrU hr hzr hzy hdeg))

/-- The centre has coe-degree at least three. -/
theorem three_le_coe_degree_triplePathSubgraph {y a b c : V}
    (p : G.Walk y a) (q : G.Walk y b) (r : G.Walk y c)
    [Fintype (triplePathSubgraph p q r).verts]
    (hy : y ∈ (triplePathSubgraph p q r).verts)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hnp : ¬p.Nil) (hnq : ¬q.Nil) (hnr : ¬r.Nil)
    (hpq : ∀ z ∈ p.support, z ∈ q.support → z = y)
    (hpr : ∀ z ∈ p.support, z ∈ r.support → z = y)
    (hqr : ∀ z ∈ q.support, z ∈ r.support → z = y) :
    3 ≤ (triplePathSubgraph p q r).coe.degree ⟨y, hy⟩ := by
  simpa using three_le_degree_triplePathSubgraph p q r hp hq hr hnp hnq hnr hpq hpr hqr

/-- Every coe-degree-one vertex is one of the three terminal vertices. -/
theorem coe_degree_eq_one_triplePathSubgraph {y a b c : V}
    (p : G.Walk y a) (q : G.Walk y b) (r : G.Walk y c)
    [Fintype (triplePathSubgraph p q r).verts]
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hnp : ¬p.Nil) (hnq : ¬q.Nil) (hnr : ¬r.Nil)
    (hpq : ∀ z ∈ p.support, z ∈ q.support → z = y)
    (hpr : ∀ z ∈ p.support, z ∈ r.support → z = y)
    (hqr : ∀ z ∈ q.support, z ∈ r.support → z = y)
    (v : (triplePathSubgraph p q r).verts)
    (hdeg : (triplePathSubgraph p q r).coe.degree v = 1) :
    (v : V) = a ∨ (v : V) = b ∨ (v : V) = c := by
  apply eq_end_of_degree_eq_one_triplePathSubgraph p q r hp hq hr hnp hnq hnr
    hpq hpr hqr v.property
  simpa using hdeg

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- First-exit prefix of a simple open path from the interior of the open
radius-`n` ball to distance at least `n`.  The endpoint is on the sphere and
all retained vertices are in the closed ball. -/
theorem exists_open_exit_prefix [DecidableEq V] (hG : G.Connected)
    {ω : G.edgeSet → Bool} (y : V) (n : ℕ) {a z : V} (p : G.Walk a z)
    (hp : p.IsPath) (hopen : IsOpenIn ω Set.univ p)
    (ha : G.dist y a < n) (hz : n ≤ G.dist y z) :
    ∃ w : V, ∃ q : G.Walk a w, q.IsPath ∧ IsOpenIn ω Set.univ q ∧
      (∀ v ∈ q.support, G.dist y v ≤ n) ∧ G.dist y w = n ∧
      q.support ⊆ p.support := by
  induction p with
  | nil => omega
  | @cons a b c hab p ih =>
    rw [isOpenIn_cons] at hopen
    by_cases hb : G.dist y b < n
    · obtain ⟨w, q, hqpath, hqopen, hqball, hw, hqsub⟩ :=
        ih hp.of_cons hopen.2 hb hz
      refine ⟨w, q.cons hab, ?_, ?_, ?_, hw, ?_⟩
      · apply (SimpleGraph.Walk.cons_isPath_iff hab q).mpr
        refine ⟨hqpath, ?_⟩
        intro haq
        have haNot : a ∉ p.support :=
          (SimpleGraph.Walk.cons_isPath_iff hab p).mp hp |>.2
        exact haNot (hqsub haq)
      · exact isOpenIn_cons.mpr ⟨hopen.1, hqopen⟩
      · intro v hv
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact Nat.le_of_lt ha
        · exact hqball v hv
      · intro v hv
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inl rfl
        · exact Or.inr (hqsub hv)
    · have hbGe : n ≤ G.dist y b := le_of_not_gt hb
      have hbEq : G.dist y b = n :=
        le_antisymm (dist_le_of_adj_of_dist_lt hG hab ha) hbGe
      let q : G.Walk a b := SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil
      refine ⟨b, q, ?_, ?_, ?_, hbEq, ?_⟩
      · exact (SimpleGraph.Walk.cons_isPath_iff hab SimpleGraph.Walk.nil).mpr
          ⟨SimpleGraph.Walk.IsPath.nil, by simpa using hab.ne⟩
      · exact isOpenIn_cons.mpr ⟨hopen.1, isOpenIn_nil⟩
      · intro v hv
        simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Nat.le_of_lt ha
        · exact hbEq.le
      · intro v hv
        simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hv
        rw [SimpleGraph.Walk.support_cons, List.mem_cons]
        rcases hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr p.start_mem_support

/-- An open exit prefix is non-nil when its start was inside the open ball. -/
theorem not_nil_exit_prefix {y a w : V} (q : G.Walk a w) (n : ℕ)
    (ha : G.dist y a < n) (hw : G.dist y w = n) : ¬q.Nil := by
  intro hnil
  have hae : a = w := hnil.eq
  subst w
  omega

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- An adjacency in the subgraph of an open walk is an open ambient edge. -/
theorem open_of_adj_toSubgraph {ω : G.edgeSet → Bool} {x z v w : V}
    (p : G.Walk x z) (hopen : IsOpenIn ω Set.univ p)
    (h : p.toSubgraph.Adj v w) :
    ω ⟨s(v, w), h.adj_sub⟩ = true := by
  have hedge : s(v, w) ∈ p.edges :=
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp h
  rcases (SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_edges h.adj_sub).mpr hedge with
    hsub | hsub
  · have hd : (⟨(v, w), h.adj_sub⟩ : G.Dart) ∈ p.darts :=
      (SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_darts p h.adj_sub).mp hsub
    exact (hopen _ hd).2
  · have hd : (⟨(w, v), h.adj_sub.symm⟩ : G.Dart) ∈ p.darts :=
      (SimpleGraph.Walk.isSubwalk_toWalk_iff_mem_darts p h.adj_sub.symm).mp hsub
    have ho := (hopen _ hd).2
    change ω ⟨s(w, v), h.adj_sub.symm⟩ = true at ho
    simpa only [Sym2.eq_swap] using ho

/-- A finite tree generated by three open arms truncated to a metric sphere.
The explicit finite-vertex field makes the degree data directly consumable by
`TreeBranchBound`. -/
structure FiniteThreeArmTree (G : SimpleGraph V) (ω : G.edgeSet → Bool)
    (y : V) (n : ℕ) where
  graph : G.Subgraph
  center : graph.verts
  center_value : (center : V) = y
  vertsFintype : Fintype graph.verts
  nontrivial : Nontrivial graph.verts
  isTree : graph.coe.IsTree
  center_degree :
    letI := vertsFintype
    3 ≤ graph.coe.degree center
  leaves_on_sphere :
    letI := vertsFintype
    ∀ v : graph.verts, graph.coe.degree v = 1 → G.dist y v = n
  support_closedBall : ∀ v : graph.verts, G.dist y v ≤ n
  open_adj : ∀ {v w : V} (h : graph.Adj v w),
    ω ⟨s(v, w), h.adj_sub⟩ = true

/-- Construct a finite encounter tree from the actual arm witnesses at one
positive scale. -/
theorem nonempty_finiteThreeArmTree_of_threeWayArms [DecidableEq V]
    (hG : G.Connected) {ω : G.edgeSet → Bool} {y : V} {n : ℕ}
    (hn : 0 < n) (harms : FK.BurtonKeane.ThreeWayArms G ω y n) :
    Nonempty (FiniteThreeArmTree G ω y n) := by
  classical
  rcases harms with ⟨a, b, c, p, q, r, hna, hnb, hnc, hp, hq, hr,
    hop, hoq, hor, hpq, hpr, hqr⟩
  have hy : G.dist y y < n := by simpa using hn
  obtain ⟨a', P, hP, hPo, hPb, ha', hPsub⟩ :=
    exists_open_exit_prefix hG y n p hp hop hy hna
  obtain ⟨b', Q, hQ, hQo, hQb, hb', hQsub⟩ :=
    exists_open_exit_prefix hG y n q hq hoq hy hnb
  obtain ⟨c', R, hR, hRo, hRb, hc', hRsub⟩ :=
    exists_open_exit_prefix hG y n r hr hor hy hnc
  have hPQ : ∀ z ∈ P.support, z ∈ Q.support → z = y :=
    fun z hzP hzQ => hpq z (hPsub hzP) (hQsub hzQ)
  have hPR : ∀ z ∈ P.support, z ∈ R.support → z = y :=
    fun z hzP hzR => hpr z (hPsub hzP) (hRsub hzR)
  have hQR : ∀ z ∈ Q.support, z ∈ R.support → z = y :=
    fun z hzQ hzR => hqr z (hQsub hzQ) (hRsub hzR)
  have hnP : ¬P.Nil := not_nil_exit_prefix P n hy ha'
  have hnQ : ¬Q.Nil := not_nil_exit_prefix Q n hy hb'
  have hnR : ¬R.Nil := not_nil_exit_prefix R n hy hc'
  let U := triplePathSubgraph P Q R
  letI : Fintype U.verts := (finite_verts_triplePathSubgraph P Q R).fintype
  have hyU : y ∈ U.verts := by
    change y ∈ ((P.toSubgraph ⊔ Q.toSubgraph) ⊔ R.toSubgraph).verts
    simp only [SimpleGraph.Subgraph.verts_sup, SimpleGraph.Walk.mem_verts_toSubgraph,
      Set.mem_union]
    exact Or.inl (Or.inl P.start_mem_support)
  have haU : a' ∈ U.verts := by
    change a' ∈ ((P.toSubgraph ⊔ Q.toSubgraph) ⊔ R.toSubgraph).verts
    simp only [SimpleGraph.Subgraph.verts_sup, SimpleGraph.Walk.mem_verts_toSubgraph,
      Set.mem_union]
    exact Or.inl (Or.inl P.end_mem_support)
  have hya : y ≠ a' := by
    intro h
    subst a'
    simp at ha'
    omega
  have hnt : Nontrivial U.verts := by
    exact ⟨⟨⟨y, hyU⟩, ⟨a', haU⟩, fun h => hya (congrArg Subtype.val h)⟩⟩
  have htree : U.coe.IsTree := isTree_triplePathSubgraph P Q R hP hQ hR hPQ hPR hQR
  have hdegree : 3 ≤ U.coe.degree ⟨y, hyU⟩ :=
    three_le_coe_degree_triplePathSubgraph P Q R hyU hP hQ hR hnP hnQ hnR hPQ hPR hQR
  have hleaves : ∀ v : U.verts, U.coe.degree v = 1 → G.dist y v = n := by
    intro v hv
    rcases coe_degree_eq_one_triplePathSubgraph P Q R hP hQ hR hnP hnQ hnR
      hPQ hPR hQR v hv with hva | hvb | hvc
    · rw [hva]
      exact ha'
    · rw [hvb]
      exact hb'
    · rw [hvc]
      exact hc'
  have hball : ∀ v : U.verts, G.dist y v ≤ n := by
    intro v
    have hv := v.property
    change (v : V) ∈ ((P.toSubgraph ⊔ Q.toSubgraph) ⊔ R.toSubgraph).verts at hv
    simp only [SimpleGraph.Subgraph.verts_sup, SimpleGraph.Walk.mem_verts_toSubgraph,
      Set.mem_union] at hv
    rcases hv with (hvP | hvQ) | hvR
    · exact hPb v hvP
    · exact hQb v hvQ
    · exact hRb v hvR
  have hopen : ∀ {v w : V} (h : U.Adj v w),
      ω ⟨s(v, w), h.adj_sub⟩ = true := by
    intro v w h
    change ((P.toSubgraph.Adj v w ∨ Q.toSubgraph.Adj v w) ∨ R.toSubgraph.Adj v w) at h
    rcases h with (hP' | hQ') | hR'
    · exact open_of_adj_toSubgraph P hPo hP'
    · exact open_of_adj_toSubgraph Q hQo hQ'
    · exact open_of_adj_toSubgraph R hRo hR'
  exact ⟨{
    graph := U
    center := ⟨y, hyU⟩
    center_value := rfl
    vertsFintype := inferInstance
    nontrivial := hnt
    isTree := htree
    center_degree := hdegree
    leaves_on_sphere := hleaves
    support_closedBall := hball
    open_adj := hopen
  }⟩

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Degree does not depend on the selected Fintype instance. -/
theorem degree_eq_of_fintype {W : Type*} (H : SimpleGraph W) (v : W)
    (i j : Fintype (H.neighborSet v)) :
    @SimpleGraph.degree W H v i = @SimpleGraph.degree W H v j := by
  have hij : i = j := Subsingleton.elim _ _
  cases hij
  rfl

namespace FiniteThreeArmTree

variable {ω : G.edgeSet → Bool} {y : V} {n : ℕ}

/-- The metric-boundary vertices of a finite three-arm tree. -/
noncomputable def boundary (t : FiniteThreeArmTree G ω y n) : Finset t.graph.verts := by
  classical
  letI := t.vertsFintype
  exact Finset.univ.filter fun v => G.dist y (v : V) = n

@[simp] theorem mem_boundary (t : FiniteThreeArmTree G ω y n) (v : t.graph.verts) :
    v ∈ t.boundary ↔ G.dist y (v : V) = n := by
  classical
  letI := t.vertsFintype
  simp [boundary]

/-- The public tree-branch bound instantiated by the constructed tree. -/
theorem card_branch_le_card_boundary (t : FiniteThreeArmTree G ω y n) :
    letI := t.vertsFintype
    (FK.BurtonKeane.TreeCounting.branchFinset t.graph.coe).card ≤ t.boundary.card := by
  classical
  letI := t.vertsFintype
  letI := t.nontrivial
  apply FK.BurtonKeane.TreeCounting.card_branch_le_card_boundary
    t.graph.coe t.isTree t.boundary
  intro v hv
  have heq := degree_eq_of_fintype t.graph.coe v
    (SimpleGraph.Subgraph.coeFiniteAt v) (Subtype.fintype _)
  exact (mem_boundary t v).mpr (t.leaves_on_sphere v (heq.trans hv))

/-- The certified centre is a branch vertex. -/
theorem center_mem_branchFinset (t : FiniteThreeArmTree G ω y n) :
    letI := t.vertsFintype
    t.center ∈ FK.BurtonKeane.TreeCounting.branchFinset t.graph.coe := by
  classical
  letI := t.vertsFintype
  rw [FK.BurtonKeane.TreeCounting.branchFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have heq := degree_eq_of_fintype t.graph.coe t.center
    (SimpleGraph.Subgraph.coeFiniteAt t.center) (Subtype.fintype _)
  exact heq ▸ t.center_degree

end FiniteThreeArmTree

/-- The finite sphere of graph radius `n`. -/
noncomputable def metricSphere [G.LocallyFinite] (hG : G.Connected) (y : V) (n : ℕ) :
    Finset V :=
  (innerBall hG y (n + 1)).filter fun v => G.dist y v = n

@[simp] theorem mem_metricSphere [G.LocallyFinite] (hG : G.Connected)
    (y : V) (n : ℕ) (v : V) : v ∈ metricSphere hG y n ↔ G.dist y v = n := by
  classical
  simp only [metricSphere, Finset.mem_filter, mem_innerBall]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega, h⟩

/-- The tree boundary embeds in the fixed ambient metric sphere. -/
theorem card_boundary_le_metricSphere [G.LocallyFinite] (hG : G.Connected)
    {ω : G.edgeSet → Bool} {y : V} {n : ℕ} (t : FiniteThreeArmTree G ω y n) :
    t.boundary.card ≤ (metricSphere hG y n).card := by
  classical
  letI := t.vertsFintype
  apply Finset.card_le_card_of_injOn (fun v : t.graph.verts => (v : V))
  · intro v hv
    exact (mem_metricSphere hG y n v).mpr ((FiniteThreeArmTree.mem_boundary t v).mp hv)
  · intro a _ha b _hb hab
    exact Subtype.ext hab

/-- Branch points of the finite encounter tree are bounded by the fixed metric
sphere, not merely by a configuration-dependent boundary. -/
theorem card_branch_le_metricSphere [G.LocallyFinite] (hG : G.Connected)
    {ω : G.edgeSet → Bool} {y : V} {n : ℕ} (t : FiniteThreeArmTree G ω y n) :
    letI := t.vertsFintype
    (FK.BurtonKeane.TreeCounting.branchFinset t.graph.coe).card ≤
      (metricSphere hG y n).card := by
  letI := t.vertsFintype
  exact (t.card_branch_le_card_boundary).trans (card_boundary_le_metricSphere hG t)

end FK.BurtonKeane.EncounterTree

namespace FK.BurtonKeane.EncounterTree

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Every retained edge is open and belongs to the finite-window edge region
`innerEdges G y (n + 1)`. -/
theorem mem_innerEdges_and_open_adj {ω : G.edgeSet → Bool} {y : V} {n : ℕ}
    (t : FiniteThreeArmTree G ω y n) {v w : V} (h : t.graph.Adj v w) :
    s(v, w) ∈ innerEdges G y (n + 1) ∧ ω ⟨s(v, w), h.adj_sub⟩ = true := by
  refine ⟨⟨v, by simp, ?_⟩, t.open_adj h⟩
  exact lt_of_le_of_lt (t.support_closedBall ⟨v, h.fst_mem⟩) (Nat.lt_succ_self n)

/-- Specialize the fixed-scale construction to a centre having arms at all
scales. -/
theorem nonempty_finiteThreeArmTree_of_allScales [DecidableEq V]
    (hG : G.Connected) {ω : G.edgeSet → Bool} {y : V} {n : ℕ}
    (hn : 0 < n) (harms : ∀ m : ℕ, FK.BurtonKeane.ThreeWayArms G ω y m) :
    Nonempty (FiniteThreeArmTree G ω y n) :=
  nonempty_finiteThreeArmTree_of_threeWayArms hG hn (harms n)

end FK.BurtonKeane.EncounterTree
