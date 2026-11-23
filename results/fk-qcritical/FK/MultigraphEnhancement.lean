import FK.Proposition31All
import FK.OpenPathEnhancement
import FK.FiniteComponentCounts

/-!
# Enhancement certificates on finite wired multigraphs

This file supplies the graph-theoretic existence step in Theorem 1.2 without
passing through a simple graph.  Loops and parallel labelled edges are kept,
and a boundary partition is arbitrary.  For a non-loop after wiring, closing every other edge is an explicit cutset.
For an edge with an alternate route in the all-open wired graph, a finite set
of labelled edges is extracted from the route; boundary-wiring steps are free.

The open-path certificate is stated for the `Fin 2` configurations used by
`OpenPath`, through a proved conversion to the Bool configurations of the
finite FK model.
-/

namespace FK.Finite.WiredEnhancement

open scoped unitInterval
open Set
open FK.Finite FK.Finite.Conditional FK.FiniteFiber
open FK.Finite.LabelledMultigraph
open FKEnhancement OpenPath

noncomputable section

local instance (priority := low) edgeDecidableEq (G : LabelledMultigraph) :
    DecidableEq G.Edge := Classical.decEq _

variable (G : LabelledMultigraph)

/-- All edges except `e`; loops and parallel labels are not identified. -/
def otherEdges (e : G.Edge) : Finset G.Edge := by
  classical
  exact Finset.univ.erase e

@[simp] lemma mem_otherEdges {G : LabelledMultigraph} {e a : G.Edge} :
    a ∈ otherEdges G e ↔ a ≠ e := by
  classical
  simp [otherEdges]

/-- Two vertices are different after the boundary partition is wired. -/
def TwoWiredVertices (ξ : G.BoundaryPartition) : Prop :=
  ∃ u v, ¬ ξ.r u v

/-- `TwoWiredVertices` is exactly nontriviality of the quotient by the
boundary setoid, so it is the paper's "at least two vertices after wiring". -/
theorem twoWiredVertices_iff_nontrivial_quotient (ξ : G.BoundaryPartition) :
    TwoWiredVertices G ξ ↔ Nontrivial (Quotient ξ) := by
  constructor
  · rintro ⟨u, v, huv⟩
    exact ⟨⟨Quotient.mk ξ u, Quotient.mk ξ v, fun h => huv (Quotient.exact h)⟩⟩
  · intro h
    letI := h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Quotient ξ)
    obtain ⟨u, rfl⟩ := Quotient.exists_rep x
    obtain ⟨v, rfl⟩ := Quotient.exists_rep y
    exact ⟨u, v, fun huv => hxy (Quotient.sound huv)⟩

/-- The all-open labelled graph, with boundary wiring, is connected. -/
def WiredConnected (ξ : G.BoundaryPartition) : Prop :=
  (G.connectionGraph ξ G.allOpen).Preconnected

/-- `e` has a connection between its endpoints which does not use `e`.
This includes loops, parallel edges, and ordinary cycles after wiring. -/
def HasAlternateRoute (ξ : G.BoundaryPartition) (e : G.Edge) : Prop :=
  (G.connectionGraph ξ (withEdge e false G.allOpen)).Reachable
    (G.source e) (G.target e)

/-- A wired multigraph forest in the labelled sense: no edge has an alternate
route.  Adding connectedness gives the tree condition used in Theorem 1.2. -/
def IsWiredForest (ξ : G.BoundaryPartition) : Prop :=
  ∀ e, ¬ HasAlternateRoute G ξ e

lemma related_of_reachable_allClosed (ξ : G.BoundaryPartition) {u v : G.Vertex}
    (h : (G.connectionGraph ξ G.allClosed).Reachable u v) : ξ.r u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ξ.refl _
  | tail hxy hyz ih =>
      apply ξ.trans ih
      rcases hyz.2 with hwire | ⟨e, he, hjoin⟩
      · exact hwire
      · simp [allClosed] at he

lemma exists_nonselfLoop_of_reachable_not_related (ξ : G.BoundaryPartition)
    {u v : G.Vertex} (h : (G.connectionGraph ξ G.allOpen).Reachable u v)
    (huv : ¬ ξ.r u v) : ∃ e, ¬ ξ.r (G.source e) (G.target e) := by
  by_contra hn
  push Not at hn
  have hrel : ∀ {v : G.Vertex}, (G.connectionGraph ξ G.allOpen).Reachable u v → ξ.r u v := by
    intro v h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact ξ.refl _
    | tail hxy hyz ih =>
        apply ξ.trans ih
        rcases hyz.2 with hwire | ⟨e, he, hjoin⟩
        · exact hwire
        · rcases hjoin with hjoin | hjoin
          · rw [← hjoin.1, ← hjoin.2]
            exact hn e
          · rw [← hjoin.1, ← hjoin.2]
            exact ξ.symm (hn e)
  exact huv (hrel h)

/-- Distinct vertices in one boundary block form an alternate route for any
edge between them; in particular this covers labelled self-loops. -/
theorem hasAlternateRoute_of_related_endpoints (ξ : G.BoundaryPartition)
    {e : G.Edge} (he : ξ.r (G.source e) (G.target e)) :
    HasAlternateRoute G ξ e := by
  unfold HasAlternateRoute
  by_cases hst : G.source e = G.target e
  · rw [hst]
  · exact (show (G.connectionGraph ξ (withEdge e false G.allOpen)).Adj
      (G.source e) (G.target e) from ⟨hst, Or.inl he⟩).reachable

theorem not_isWiredForest_of_related_endpoints (ξ : G.BoundaryPartition)
    {e : G.Edge} (he : ξ.r (G.source e) (G.target e)) :
    ¬ IsWiredForest G ξ := by
  intro hforest
  exact hforest e (hasAlternateRoute_of_related_endpoints G ξ he)

/-- A distinct parallel labelled edge is an alternate route. -/
theorem hasAlternateRoute_of_parallel (ξ : G.BoundaryPartition)
    {e f : G.Edge} (hfe : f ≠ e)
    (hjoin : G.Joins f (G.source e) (G.target e)) :
    HasAlternateRoute G ξ e := by
  unfold HasAlternateRoute
  by_cases hst : G.source e = G.target e
  · rw [hst]
  · apply SimpleGraph.Adj.reachable
    refine ⟨hst, Or.inr ⟨f, ?_, hjoin⟩⟩
    rw [withEdge_off hfe]
    rfl

theorem not_isWiredForest_of_parallel (ξ : G.BoundaryPartition)
    {e f : G.Edge} (hfe : f ≠ e)
    (hjoin : G.Joins f (G.source e) (G.target e)) :
    ¬ IsWiredForest G ξ := by
  intro hforest
  exact hforest e (hasAlternateRoute_of_parallel G ξ hfe hjoin)

/-- A route which avoids the simple adjacency between `e`'s endpoints also
avoids the particular labelled edge `e`; parallel labels remain available. -/
lemma connectionGraph_deleteEdges_le_without (ξ : G.BoundaryPartition) (e : G.Edge) :
    (G.connectionGraph ξ G.allOpen).deleteEdges
        {s(G.source e, G.target e)} ≤
      G.connectionGraph ξ (withEdge e false G.allOpen) := by
  intro u v huv
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at huv
  rcases huv with ⟨⟨hne, hbranch⟩, hpair⟩
  refine ⟨hne, ?_⟩
  rcases hbranch with hwire | ⟨a, ha, hjoin⟩
  · exact Or.inl hwire
  · by_cases hae : a = e
    · subst a
      exfalso
      apply hpair
      rcases hjoin with hjoin | hjoin
      · rw [← hjoin.1, ← hjoin.2]
      · rw [← hjoin.1, ← hjoin.2, Sym2.eq_swap]
    · refine Or.inr ⟨a, ?_, hjoin⟩
      rw [withEdge_off hae]
      rfl

theorem hasAlternateRoute_of_reachable_deleteEdges (ξ : G.BoundaryPartition)
    (e : G.Edge)
    (h : ((G.connectionGraph ξ G.allOpen).deleteEdges
      {s(G.source e, G.target e)}).Reachable (G.source e) (G.target e)) :
    HasAlternateRoute G ξ e :=
  h.mono (connectionGraph_deleteEdges_le_without G ξ e)

/-- An ordinary cycle in the wired simple connection graph, together with a
label for one of its adjacencies, supplies a labelled alternate route. -/
theorem hasAlternateRoute_of_cycle (ξ : G.BoundaryPartition) (e : G.Edge)
    {u : G.Vertex} {p : (G.connectionGraph ξ G.allOpen).Walk u u}
    (hc : p.IsCycle) (he : s(G.source e, G.target e) ∈ p.edges) :
    HasAlternateRoute G ξ e := by
  have h := SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mpr
    ⟨u, p, hc, he⟩
  exact hasAlternateRoute_of_reachable_deleteEdges G ξ e h.2

theorem not_isWiredForest_of_cycle (ξ : G.BoundaryPartition) (e : G.Edge)
    {u : G.Vertex} {p : (G.connectionGraph ξ G.allOpen).Walk u u}
    (hc : p.IsCycle) (he : s(G.source e, G.target e) ∈ p.edges) :
    ¬ IsWiredForest G ξ := by
  intro hforest
  exact hforest e (hasAlternateRoute_of_cycle G ξ e hc he)


theorem exists_nonselfLoop (ξ : G.BoundaryPartition)
    (hconn : WiredConnected G ξ) (htwo : TwoWiredVertices G ξ) :
    ∃ e, ¬ ξ.r (G.source e) (G.target e) := by
  obtain ⟨u, v, huv⟩ := htwo
  exact exists_nonselfLoop_of_reachable_not_related G ξ (hconn u v) huv

/-- The other-edge cutset belongs to Proposition 3.1's exact cutset family for
the singleton enhanced set `{e}`. -/
theorem otherEdges_mem_cutsetFamily (ξ : G.BoundaryPartition) (e : G.Edge)
    (he : ¬ ξ.r (G.source e) (G.target e)) :
    ((otherEdges G e : Finset G.Edge) : Set G.Edge) ∈
      CutsetFamily (fun a ω => endpointsConnectedWithout G ξ a ω) {e} e := by
  classical
  constructor
  · intro a ha
    have hae : a ≠ e := mem_otherEdges.mp (by exact_mod_cast ha)
    exact ⟨by simpa [hae], hae⟩
  · intro ω hclosed hconn
    apply he
    apply related_of_reachable_allClosed G ξ
    have hcfg : withEdge e false ω = G.allClosed := by
      funext a
      by_cases hae : a = e
      · subst a
        simp [allClosed]
      · have ha : a ∈ ((otherEdges G e : Finset G.Edge) : Set G.Edge) := by
          exact_mod_cast mem_otherEdges.mpr hae
        rw [withEdge_off hae, hclosed a ha]
        rfl
    rw [endpointsConnectedWithout, hcfg] at hconn
    exact hconn

/-- Strict positivity of the closed-cutset enhancement at a non-loop edge. -/
theorem cutsetEpsilon_pos_of_nonselfLoop (ξ : G.BoundaryPartition) (e : G.Edge)
    (he : ¬ ξ.r (G.source e) (G.target e)) (p p' : I)
    (hp : p ≠ p') (hmax : max p p' < 1) :
    0 < cutsetEpsilon (fun a ω => endpointsConnectedWithout G ξ a ω) {e} p p' e := by
  apply cutsetEpsilon_pos _ _ _ _ hp _ (otherEdges G e)
  · exact otherEdges_mem_cutsetFamily G ξ e he
  · intro a ha
    exact hmax

lemma cutsetEpsilon_mem_Icc (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    (p p' : I) (e : G.Edge) :
    cutsetEpsilon (fun a ω => endpointsConnectedWithout G ξ a ω)
      enhanced p p' e ∈ Icc (0 : ℝ) 1 := by
  let K := fun a ω => endpointsConnectedWithout G ξ a ω
  have hgap : |(p' : ℝ) - (p : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [p.2.1, p.2.2, p'.2.1, p'.2.2]
  constructor
  · exact mul_nonneg (abs_nonneg _) (cutsetWeight_nonneg K enhanced p p' e)
  · have hweight : 0 ≤ cutsetWeight K enhanced p p' e :=
      cutsetWeight_nonneg K enhanced p p' e
    have h := mul_le_mul hgap (cutsetWeight_le_one K enhanced p p' e) hweight zero_le_one
    simpa [cutsetEpsilon, closedCutsetEnhancement, K] using h

/-- Closed-cutset enhancement sizes extended by zero outside the enhanced set. -/
def extendedCutsetEpsilon (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    (p p' : I) (e : G.Edge) : ℝ := by
  classical
  exact if e ∈ enhanced then
    cutsetEpsilon (fun a ω => endpointsConnectedWithout G ξ a ω) enhanced p p' e else 0

lemma extendedCutsetEpsilon_mem_Icc (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    (p p' : I) (e : G.Edge) :
    extendedCutsetEpsilon G ξ enhanced p p' e ∈ Icc (0 : ℝ) 1 := by
  by_cases he : e ∈ enhanced
  · rw [extendedCutsetEpsilon, if_pos he]
    exact cutsetEpsilon_mem_Icc G ξ enhanced p p' e
  · simp [extendedCutsetEpsilon, he]

lemma lowerEnhancedRate_eq_add_extended (ξ : G.BoundaryPartition)
    (enhanced : Set G.Edge) {p p' : I} (_hp : p ≤ p') (e : G.Edge) :
    lowerEnhancedRate (fun a ω => endpointsConnectedWithout G ξ a ω) enhanced p p' e =
      (p : ℝ) + extendedCutsetEpsilon G ξ enhanced p p' e := by
  by_cases he : e ∈ enhanced <;>
    simp [lowerEnhancedRate, extendedCutsetEpsilon, he]

lemma upperEnhancedRate_eq_sub_extended (ξ : G.BoundaryPartition)
    (enhanced : Set G.Edge) {p p' : I} (_hp : p' ≤ p) (e : G.Edge) :
    upperEnhancedRate (fun a ω => endpointsConnectedWithout G ξ a ω) enhanced p p' e =
      (p : ℝ) - extendedCutsetEpsilon G ξ enhanced p p' e := by
  by_cases he : e ∈ enhanced <;>
    simp [upperEnhancedRate, extendedCutsetEpsilon, he]

/-- The non-identically-zero cutset enhancement required by Theorem 1.2. -/
theorem exists_pos_cutsetEpsilon (ξ : G.BoundaryPartition)
    (hconn : WiredConnected G ξ) (htwo : TwoWiredVertices G ξ)
    (p p' : I) (hp : p ≠ p') (hmax : max p p' < 1) :
    ∃ enhanced : Set G.Edge, enhanced.Nonempty ∧
      ∃ e ∈ enhanced,
        0 < cutsetEpsilon (fun a ω => endpointsConnectedWithout G ξ a ω)
          enhanced p p' e ∧
        ∃ χ : Finset G.Edge, (χ : Set G.Edge) ∈
          CutsetFamily (fun a ω => endpointsConnectedWithout G ξ a ω) enhanced e := by
  obtain ⟨e, he⟩ := exists_nonselfLoop G ξ hconn htwo
  exact ⟨{e}, Set.singleton_nonempty e, e, Set.mem_singleton e,
    cutsetEpsilon_pos_of_nonselfLoop G ξ e he p p' hp hmax,
    otherEdges G e, otherEdges_mem_cutsetFamily G ξ e he⟩

/-- Convert the `Fin 2` configurations of `OpenPath` to the Bool
configurations of `FK.FiniteModel`. -/
def configToBool {E : Type*} (ω : OpenPath.Config E) : E → Bool :=
  fun e => decide (ω e = 1)

@[simp] lemma configToBool_eq_true {E : Type*} (ω : OpenPath.Config E) (e : E) :
    configToBool ω e = true ↔ ω e = 1 := by
  simp [configToBool]

lemma configToBool_mono {E : Type*} {ω η : OpenPath.Config E} (h : ω ≤ η) :
    configToBool ω ≤ configToBool η := by
  intro e
  cases he : configToBool ω e with
  | false => exact bot_le
  | true =>
      have he' : ω e = 1 := (configToBool_eq_true ω e).mp he
      have hle := h e
      rw [he'] at hle
      have heta : η e = 1 := by
        apply Fin.ext
        simp only [Fin.le_iff_val_le_val, Fin.val_one] at hle ⊢
        omega
      have hb : configToBool η e = true := (configToBool_eq_true η e).mpr heta
      rw [hb]

/-- A reachable pair in the all-open graph with `e` deleted has a finite set
of labelled edges, all distinct from `e`, whose openness reconstructs a route.
Boundary-wiring steps are used freely. -/
lemma exists_routeCertificate_of_reachable (ξ : G.BoundaryPartition) (e : G.Edge)
    {u v : G.Vertex}
    (h : (G.connectionGraph ξ (withEdge e false G.allOpen)).Reachable u v) :
    ∃ γ : Finset G.Edge, e ∉ γ ∧
      ∀ ω : G.Configuration, (∀ a ∈ γ, ω a = true) →
        (G.connectionGraph ξ (withEdge e false ω)).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl =>
      exact ⟨∅, by simp, fun ω hω => SimpleGraph.Reachable.refl _⟩
  | @tail y z hxy hyz ih =>
      obtain ⟨γ, heγ, hγ⟩ := ih
      rcases hyz.2 with hwire | ⟨a, ha, hjoin⟩
      · refine ⟨γ, heγ, fun ω hω => (hγ ω hω).trans ?_⟩
        exact (show (G.connectionGraph ξ (withEdge e false ω)).Adj y z from
          ⟨hyz.1, Or.inl hwire⟩).reachable
      · have hae : a ≠ e := by
          intro hae
          subst a
          simp at ha
        refine ⟨insert a γ, by simp [Ne.symm hae, heγ], ?_⟩
        intro ω hω
        apply (hγ ω (fun b hb => hω b (Finset.mem_insert_of_mem hb))).trans
        apply SimpleGraph.Adj.reachable
        refine ⟨hyz.1, Or.inr ⟨a, ?_, hjoin⟩⟩
        rw [withEdge_off hae]
        exact hω a (Finset.mem_insert_self a γ)

/-- A singleton collection containing a finite route certificate `γ` at `e`. -/
def wiredPathCollection (e : G.Edge) (γ : Finset G.Edge) :
    G.Edge → Set (Finset G.Edge) := by
  classical
  exact fun a => if a = e then {γ} else ∅

lemma hasEnhancingPaths_wiredPath {e : G.Edge} {γ : Finset G.Edge} (heγ : e ∉ γ) :
    HasEnhancingPaths {e} (wiredPathCollection G e γ) := by
  classical
  constructor
  · intro a ha
    have hae : a = e := by simpa using ha
    subst a
    intro δ hδ
    have hδeq : δ = γ := by simpa [wiredPathCollection] using hδ
    subst δ
    exact ⟨heγ, by simp_all⟩
  · intro a ha
    have hae : a = e := by simpa using ha
    subst a
    simp [wiredPathCollection]

/-- A non-forest wired multigraph has a genuine finite open-route certificate,
not merely the weaker universal other-edge event. -/
theorem exists_wiredPath_enhancement (ξ : G.BoundaryPartition)
    (hnot : ¬ IsWiredForest G ξ) :
    ∃ enhanced : Finset G.Edge, enhanced.Nonempty ∧
      ∃ Γ : G.Edge → Set (Finset G.Edge), HasEnhancingPaths enhanced Γ ∧
      ∃ e ∈ enhanced,
        ∀ {ω : OpenPath.Config G.Edge}, SomePathOpen (Γ e) ω →
          endpointsConnectedWithout G ξ e (configToBool ω) := by
  classical
  rw [IsWiredForest] at hnot
  push Not at hnot
  obtain ⟨e, he⟩ := hnot
  obtain ⟨γ, heγ, hγ⟩ := exists_routeCertificate_of_reachable G ξ e he
  refine ⟨{e}, Finset.singleton_nonempty e, wiredPathCollection G e γ,
    hasEnhancingPaths_wiredPath G heγ, e, Finset.mem_singleton_self e, ?_⟩
  intro ω hω
  obtain ⟨δ, hδ, hδopen⟩ := hω
  have hδeq : δ = γ := by simpa [wiredPathCollection] using hδ
  subst δ
  apply hγ (configToBool ω)
  intro a ha
  exact (configToBool_eq_true ω a).mpr (hδopen a ha)

/-- Endpoint connection is monotone under the `Fin 2` coordinatewise order. -/
lemma endpointsConnectedWithout_configToBool_mono (ξ : G.BoundaryPartition)
    (e : G.Edge) {ω η : OpenPath.Config G.Edge} (h : ω ≤ η)
    (hconn : endpointsConnectedWithout G ξ e (configToBool ω)) :
    endpointsConnectedWithout G ξ e (configToBool η) := by
  unfold endpointsConnectedWithout at hconn ⊢
  apply SimpleGraph.Reachable.mono _ hconn
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hwire | ⟨a, ha, hjoin⟩
  · exact Or.inl hwire
  · refine Or.inr ⟨a, ?_, hjoin⟩
    by_cases hae : a = e
    · subst a
      simpa using ha
    · rw [withEdge_off hae] at ha ⊢
      exact configToBool_mono h a ha

/-- Exact FK parameter gap used in both stochastic directions. -/
lemma prime_sub_gap {q p : ℝ} (hd : p + q * (1 - p) ≠ 0) :
    FK.prime q p - p = p * (1 - p) * (1 - q) / (p + q * (1 - p)) := by
  unfold FK.prime
  field_simp [hd]
  ring

lemma lt_prime_of_q_lt_one {q p : ℝ} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) (hq1 : q < 1) : p < FK.prime q p := by
  have hd : 0 < p + q * (1 - p) := FK.denominator_pos hq hp0.le hp1.le
  have hn : 0 < p * (1 - p) * (1 - q) :=
    mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) (sub_pos.mpr hq1)
  have hdiv := div_pos hn hd
  rw [← prime_sub_gap hd.ne'] at hdiv
  linarith

lemma prime_lt_of_one_lt_q {q p : ℝ} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) (hq1 : 1 < q) : FK.prime q p < p := by
  have hd : 0 < p + q * (1 - p) := FK.denominator_pos hq hp0.le hp1.le
  have hn : p * (1 - p) * (1 - q) < 0 := by
    apply mul_neg_of_pos_of_neg (mul_pos hp0 (sub_pos.mpr hp1))
    linarith
  have hdiv := div_neg_of_neg_of_pos hn hd
  rw [← prime_sub_gap hd.ne'] at hdiv
  linarith

lemma prime_ne_self_of_q_ne_one {q p : ℝ} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) (hq1 : q ≠ 1) : FK.prime q p ≠ p := by
  intro heq
  have hd : p + q * (1 - p) ≠ 0 :=
    (FK.denominator_pos hq hp0.le hp1.le).ne'
  unfold FK.prime at heq
  rw [div_eq_iff hd] at heq
  have hfac : p * (1 - p) * (1 - q) = 0 := by
    calc
      p * (1 - p) * (1 - q) = p - p * (p + q * (1 - p)) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  have hpne : p ≠ 0 := hp0.ne'
  have h1p : 1 - p ≠ 0 := (sub_pos.mpr hp1).ne'
  have h1q : 1 - q = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact (hpne h).elim
      · exact (h1p h).elim
    · exact h
  apply hq1
  linarith

lemma prime_lt_one_interior {q p : ℝ} (hq : 0 < q) (hp0 : 0 < p)
    (hp1 : p < 1) : FK.prime q p < 1 := by
  have hd : p + q * (1 - p) ≠ 0 :=
    (FK.denominator_pos hq hp0.le hp1.le).ne'
  rw [FK.prime_eq_one_sub_dual hd]
  have hdpos := FK.dual_pos hq hp0.le hp1
  linarith

/-- Strict positivity of the upper-path bonus for `p < p'`. -/
theorem exists_upperEpsilon_pos_of_not_forest (ξ : G.BoundaryPartition)
    (hnot : ¬ IsWiredForest G ξ) {p p' : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hp0 : 0 < p) (hp1 : p < 1) (h : p < p') :
    ∃ enhanced : Finset G.Edge,
      ∃ Γ : G.Edge → Set (Finset G.Edge), HasEnhancingPaths enhanced Γ ∧
      ∃ e ∈ enhanced, 0 < upperEpsilon enhanced p p' hp Γ e ∧
        ∀ {ω : OpenPath.Config G.Edge}, SomePathOpen (Γ e) ω →
          endpointsConnectedWithout G ξ e (configToBool ω) := by
  obtain ⟨enhanced, henh, Γ, hΓ, e, he, hsem⟩ :=
    exists_wiredPath_enhancement G ξ hnot
  exact ⟨enhanced, Γ, hΓ, e, he, upperEpsilon_pos hΓ hp hp0 hp1 h he, hsem⟩

/-- Strict positivity of the lower-path bonus for `p' < p`. -/
theorem exists_lowerEpsilon_pos_of_not_forest (ξ : G.BoundaryPartition)
    (hnot : ¬ IsWiredForest G ξ) {p p' : ℝ}
    (hp' : p' ∈ Icc (0 : ℝ) 1) (hp'0 : 0 < p') (hp'1 : p' < 1) (h : p' < p) :
    ∃ enhanced : Finset G.Edge,
      ∃ Γ : G.Edge → Set (Finset G.Edge), HasEnhancingPaths enhanced Γ ∧
      ∃ e ∈ enhanced, 0 < lowerEpsilon enhanced p p' hp' Γ e ∧
        ∀ {ω : OpenPath.Config G.Edge}, SomePathOpen (Γ e) ω →
          endpointsConnectedWithout G ξ e (configToBool ω) := by
  obtain ⟨enhanced, henh, Γ, hΓ, e, he, hsem⟩ :=
    exists_wiredPath_enhancement G ξ hnot
  exact ⟨enhanced, Γ, hΓ, e, he, lowerEpsilon_pos hΓ hp' hp'0 hp'1 h he, hsem⟩

/-- In the `q < 1` direction, non-tree geometry gives a strictly positive
upper-path enhancement at the actual FK parameters. -/
theorem exists_upperEpsilon_pos_fk_of_q_lt_one (ξ : G.BoundaryPartition)
    (hnot : ¬ IsWiredForest G ξ) {q p : ℝ}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q < 1) :
    ∃ enhanced : Finset G.Edge,
      ∃ Γ : G.Edge → Set (Finset G.Edge), HasEnhancingPaths enhanced Γ ∧
      (∀ a, upperEpsilon enhanced p (FK.prime q p) ⟨hp0.le, hp1.le⟩ Γ a ∈
        Icc (0 : ℝ) 1) ∧
      ∃ e ∈ enhanced,
        0 < upperEpsilon enhanced p (FK.prime q p) ⟨hp0.le, hp1.le⟩ Γ e ∧
        ∀ {ω : OpenPath.Config G.Edge}, SomePathOpen (Γ e) ω →
          endpointsConnectedWithout G ξ e (configToBool ω) := by
  have hlt := lt_prime_of_q_lt_one hq hp0 hp1 hq1
  obtain ⟨enhanced, Γ, hΓ, e, he, hpos, hsem⟩ :=
    exists_upperEpsilon_pos_of_not_forest G ξ hnot ⟨hp0.le, hp1.le⟩ hp0 hp1 hlt
  exact ⟨enhanced, Γ, hΓ,
    upperEpsilon_mem_Icc enhanced ⟨hp0.le, hp1.le⟩
      (prime_lt_one_interior hq hp0 hp1).le hlt.le Γ,
    e, he, hpos, hsem⟩

/-- In the `q > 1` direction, non-tree geometry gives a strictly positive
lower-path enhancement at the actual FK parameters. -/
theorem exists_lowerEpsilon_pos_fk_of_one_lt_q (ξ : G.BoundaryPartition)
    (hnot : ¬ IsWiredForest G ξ) {q p : ℝ}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : 1 < q) :
    ∃ enhanced : Finset G.Edge,
      ∃ Γ : G.Edge → Set (Finset G.Edge), HasEnhancingPaths enhanced Γ ∧
      (∀ a, lowerEpsilon enhanced p (FK.prime q p)
        ⟨(FK.prime_pos hq hp0 hp1.le).le, (prime_lt_one_interior hq hp0 hp1).le⟩ Γ a ∈
          Icc (0 : ℝ) 1) ∧
      ∃ e ∈ enhanced,
        0 < lowerEpsilon enhanced p (FK.prime q p)
          ⟨(FK.prime_pos hq hp0 hp1.le).le, (prime_lt_one_interior hq hp0 hp1).le⟩ Γ e ∧
        ∀ {ω : OpenPath.Config G.Edge}, SomePathOpen (Γ e) ω →
          endpointsConnectedWithout G ξ e (configToBool ω) := by
  have hp'0 := FK.prime_pos hq hp0 hp1.le
  have hp'1 := prime_lt_one_interior hq hp0 hp1
  have hlt := prime_lt_of_one_lt_q hq hp0 hp1 hq1
  obtain ⟨enhanced, Γ, hΓ, e, he, hpos, hsem⟩ :=
    exists_lowerEpsilon_pos_of_not_forest G ξ hnot
      ⟨hp'0.le, hp'1.le⟩ hp'0 hp'1 hlt
  exact ⟨enhanced, Γ, hΓ,
    lowerEpsilon_mem_Icc enhanced hp1.le ⟨hp'0.le, hp'1.le⟩ hlt.le Γ,
    e, he, hpos, hsem⟩

/-- Package a real probability as a unit-interval parameter without changing
its value. -/
def unitParameter (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : I := ⟨x, hx0, hx1⟩

@[simp] lemma coe_unitParameter (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (unitParameter x hx0 hx1 : ℝ) = x := rfl

/-- A non-identically-zero closed-cutset enhancement for the actual FK prime
parameter, in both cases `q < 1` and `q > 1` (only `q ≠ 1` is needed). -/
theorem exists_pos_cutsetEpsilon_fk (ξ : G.BoundaryPartition)
    (hconn : WiredConnected G ξ) (htwo : TwoWiredVertices G ξ) {q p : ℝ}
    (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1) (hq1 : q ≠ 1) :
    ∃ enhanced : Set G.Edge, enhanced.Nonempty ∧
      (∀ e, extendedCutsetEpsilon G ξ enhanced
        (unitParameter p hp0.le hp1.le)
        (unitParameter (FK.prime q p) (FK.prime_pos hq hp0 hp1.le).le
          (prime_lt_one_interior hq hp0 hp1).le) e ∈ Icc (0 : ℝ) 1) ∧
      ∃ e ∈ enhanced,
        0 < extendedCutsetEpsilon G ξ enhanced
          (unitParameter p hp0.le hp1.le)
          (unitParameter (FK.prime q p) (FK.prime_pos hq hp0 hp1.le).le
            (prime_lt_one_interior hq hp0 hp1).le) e ∧
        ∃ χ : Finset G.Edge, (χ : Set G.Edge) ∈
          CutsetFamily (fun a ω => endpointsConnectedWithout G ξ a ω) enhanced e := by
  have hp'0 := FK.prime_pos hq hp0 hp1.le
  have hp'1 := prime_lt_one_interior hq hp0 hp1
  let pI := unitParameter p hp0.le hp1.le
  let p'I := unitParameter (FK.prime q p) hp'0.le hp'1.le
  have hne : pI ≠ p'I := by
    intro h
    have hval := congrArg (fun x : I => (x : ℝ)) h
    change p = FK.prime q p at hval
    exact prime_ne_self_of_q_ne_one hq hp0 hp1 hq1 hval.symm
  have hmax : max pI p'I < 1 := by
    exact max_lt hp1 hp'1
  obtain ⟨enhanced, henh, e, he, hpos, χ, hχ⟩ :=
    exists_pos_cutsetEpsilon G ξ hconn htwo pI p'I hne hmax
  refine ⟨enhanced, henh, fun a => extendedCutsetEpsilon_mem_Icc G ξ enhanced pI p'I a,
    e, he, ?_, χ, hχ⟩
  simpa only [extendedCutsetEpsilon, if_pos he] using hpos


end
end FK.Finite.WiredEnhancement
