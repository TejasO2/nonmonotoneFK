import FK.PlanarForestDuality
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Cycle matroids on finite labelled multigraphs

The independent edge sets are the open forests already used by the finite FK
model.  This is genuinely multigraphic: loops are dependent, a pair of parallel
edges is dependent, and every labelled edge contributes to `openCard`.

The later planar results use a *graphic dual* of this matroid as the
combinatorial certificate of a plane dual.  The desired component-form Euler
identity is proved from matroid duality, rather than assumed as an axiom.
-/

namespace FK.Finite.LabelledMultigraph

open scoped BigOperators Classical
open FK.Finite.Conditional
open FK.FiniteFiber
open FK.FinitePlane

variable (G : LabelledMultigraph)

/-- The Boolean configuration whose open edges are exactly a set of labels. -/
noncomputable def setConfig (A : Set G.Edge) : G.Configuration := fun e => decide (e ∈ A)

/-- The set of open labels of a Boolean configuration. -/
def openEdgeSet (ω : G.Configuration) : Set G.Edge := {e | ω e = true}

@[simp] lemma openEdgeSet_setConfig (A : Set G.Edge) :
    G.openEdgeSet (G.setConfig A) = A := by
  ext e
  simp [openEdgeSet, setConfig]

@[simp] lemma setConfig_openEdgeSet (ω : G.Configuration) :
    G.setConfig (G.openEdgeSet ω) = ω := by
  funext e
  cases he : ω e <;> simp [setConfig, openEdgeSet, he]

lemma setConfig_mono {A B : Set G.Edge} (hAB : A ⊆ B) :
    G.setConfig A ≤ G.setConfig B := by
  intro e
  by_cases heA : e ∈ A
  · by_cases heB : e ∈ B
    · simp [setConfig, heA, heB]
    · exact (heB (hAB heA)).elim
  · by_cases heB : e ∈ B <;> simp [setConfig, heA, heB]

@[simp] lemma setConfig_empty : G.setConfig ∅ = G.allClosed := by
  funext e
  simp [setConfig, allClosed]

@[simp] lemma setConfig_univ : G.setConfig Set.univ = G.allOpen := by
  funext e
  simp [setConfig, allOpen]

lemma setConfig_insert (e : G.Edge) (A : Set G.Edge) :
    G.setConfig (insert e A) = withEdge e true (G.setConfig A) := by
  funext a
  by_cases hae : a = e
  · subst a
    simp [setConfig]
  · simp [setConfig, hae, withEdge]

/-- Forests are hereditary under taking open subsets. -/
lemma IsOpenForest.mono {ω η : G.Configuration} (hωη : ω ≤ η)
    (hη : G.IsOpenForest G.freeBoundary η) : G.IsOpenForest G.freeBoundary ω := by
  intro e he hconn
  have heη : η e = true := by
    have h := hωη e
    rw [Bool.le_iff_imp] at h
    exact h he
  apply hη e heη
  unfold endpointsConnectedWithout at hconn ⊢
  apply hconn.mono
  apply G.connectionGraph_mono
  intro a
  by_cases hae : a = e
  · subst a
    simp
  · rw [withEdge_off hae, withEdge_off hae]
    exact hωη a

/-- Any Boolean configuration on a finite graph has cyclomatic number zero or
more, written without subtraction. -/
lemma card_vertices_le_componentCount_add_openCard (ω : G.Configuration) :
    Fintype.card G.Vertex ≤ G.componentCount G.freeBoundary ω + openCard ω := by
  classical
  induction hcard : openCard ω generalizing ω with
  | zero =>
      have hclosed := (G.openCard_eq_zero_iff ω).mp hcard
      subst ω
      simp [G.componentCount_free_allClosed, Nat.card_eq_fintype_card]
  | succ n ih =>
      have hnzero : openCard ω ≠ 0 := by omega
      have hne : ω ≠ G.allClosed := by
        intro hclosed
        exact hnzero ((G.openCard_eq_zero_iff ω).mpr hclosed)
      obtain ⟨e, he⟩ := G.exists_open_of_ne_allClosed hne
      let ω₀ := withEdge e false ω
      have hcard₀ : openCard ω₀ = n := by
        have h := G.openCard_withEdge_false_add_one he
        dsimp [ω₀]
        omega
      have hi := ih ω₀ hcard₀
      have hopen : openCard ω₀ + 1 = openCard ω := by
        exact G.openCard_withEdge_false_add_one he
      by_cases hconn : endpointsConnectedWithout G G.freeBoundary e ω
      · have hc := componentCount_open_eq_of_connected G G.freeBoundary e ω hconn
        rw [G.withEdge_true_eq_self he] at hc
        change G.componentCount G.freeBoundary ω =
          G.componentCount G.freeBoundary ω₀ at hc
        omega
      · have hc := componentCount_open_add_one_of_not_connected G G.freeBoundary e ω hconn
        rw [G.withEdge_true_eq_self he] at hc
        change G.componentCount G.freeBoundary ω + 1 =
          G.componentCount G.freeBoundary ω₀ at hc
        omega

/-- Equality in the preceding inequality is an exact labelled-forest
certificate.  The reverse implication is the new part: a dependent open edge
already creates a strict cyclomatic excess. -/
lemma isOpenForest_iff_componentCount_add_openCard (ω : G.Configuration) :
    G.IsOpenForest G.freeBoundary ω ↔
      G.componentCount G.freeBoundary ω + openCard ω = Fintype.card G.Vertex := by
  constructor
  · exact G.componentCount_add_openCard_of_free_isOpenForest ω
  · intro hcard e he hconn
    have hi := G.card_vertices_le_componentCount_add_openCard (withEdge e false ω)
    have hc := componentCount_open_eq_of_connected G G.freeBoundary e ω hconn
    rw [G.withEdge_true_eq_self he] at hc
    have ho := G.openCard_withEdge_false_add_one he
    omega

lemma openCard_eq_ncard_openEdgeSet (ω : G.Configuration) :
    openCard ω = (G.openEdgeSet ω).ncard := by
  classical
  unfold openCard openEdgeSet
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

lemma openCard_setConfig (A : Set G.Edge) :
    openCard (G.setConfig A) = A.ncard := by
  rw [G.openCard_eq_ncard_openEdgeSet, G.openEdgeSet_setConfig]

lemma isOpenForest_setConfig_iff (A : Set G.Edge) :
    G.IsOpenForest G.freeBoundary (G.setConfig A) ↔
      G.componentCount G.freeBoundary (G.setConfig A) + A.ncard =
        Fintype.card G.Vertex := by
  rw [G.isOpenForest_iff_componentCount_add_openCard, G.openCard_setConfig]

lemma withEdge_false_setConfig (e : G.Edge) (A : Set G.Edge) :
    withEdge e false (G.setConfig A) = G.setConfig (A \ {e}) := by
  funext a
  by_cases hae : a = e
  · subst a
    simp [setConfig]
  · simp [withEdge, setConfig, hae]

lemma withEdge_false_setConfig_of_not_mem {e : G.Edge} {A : Set G.Edge}
    (he : e ∉ A) : withEdge e false (G.setConfig A) = G.setConfig A := by
  rw [G.withEdge_false_setConfig]
  congr 1
  exact Set.sdiff_singleton_eq_self he

/-- If adding `e` to a labelled forest creates dependence, then the two ends of
`e` were already connected in the forest. -/
lemma reachable_of_not_isOpenForest_insert {A : Set G.Edge}
    (hA : G.IsOpenForest G.freeBoundary (G.setConfig A)) {e : G.Edge} (he : e ∉ A)
    (hdep : ¬ G.IsOpenForest G.freeBoundary (G.setConfig (insert e A))) :
    (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable
      (G.source e) (G.target e) := by
  by_contra hconn
  apply hdep
  rw [G.isOpenForest_setConfig_iff]
  have hconn' : ¬ endpointsConnectedWithout G G.freeBoundary e (G.setConfig A) := by
    unfold endpointsConnectedWithout
    rwa [G.withEdge_false_setConfig_of_not_mem he]
  have hc := componentCount_open_add_one_of_not_connected G G.freeBoundary e
    (G.setConfig A) hconn'
  rw [← G.setConfig_insert e A, G.withEdge_false_setConfig_of_not_mem he] at hc
  have hAcard := (G.isOpenForest_setConfig_iff A).mp hA
  rw [Set.ncard_insert_of_notMem he (Set.toFinite A)]
  omega

/-- Independence in the labelled cycle matroid. -/
def IsForestSet (A : Set G.Edge) : Prop :=
  G.IsOpenForest G.freeBoundary (G.setConfig A)

/-- The cycle matroid of an arbitrary finite labelled multigraph.  No simplicity,
loop-freeness, or planarity assumption is used. -/
noncomputable def cycleMatroid : Matroid G.Edge :=
  (IndepMatroid.ofFinite (E := Set.univ) (Set.toFinite (Set.univ : Set G.Edge))
    G.IsForestSet
    (by
      rw [IsForestSet, G.setConfig_empty]
      exact G.isOpenForest_allClosed G.freeBoundary)
    (by
      intro I J hJ hIJ
      exact IsOpenForest.mono (G := G) (G.setConfig_mono hIJ) hJ)
    (by
      intro I J hI hJ hcard
      by_contra hn
      have hno : ∀ e ∈ J \ I, ¬ G.IsForestSet (insert e I) := by
        intro e he hforest
        exact hn ⟨e, he.1, he.2, hforest⟩
      have hle : G.connectionGraph G.freeBoundary (G.setConfig I) ≤
          G.connectionGraph G.freeBoundary (G.setConfig (I ∪ J)) :=
        G.connectionGraph_mono (G.setConfig_mono Set.subset_union_left)
      have hreach : ∀ {u v : G.Vertex},
          (G.connectionGraph G.freeBoundary (G.setConfig (I ∪ J))).Adj u v →
          (G.connectionGraph G.freeBoundary (G.setConfig I)).Reachable u v := by
        intro u v huv
        rcases huv.2 with hfree | ⟨e, heX, hjoin⟩
        · exact (huv.1 hfree).elim
        · have heX' : e ∈ I ∪ J := by simpa [setConfig] using heX
          by_cases heI : e ∈ I
          · apply SimpleGraph.Adj.reachable
            exact ⟨huv.1, Or.inr ⟨e, by simp [setConfig, heI], hjoin⟩⟩
          · have heJ' : e ∈ J := heX'.resolve_left heI
            have hdep := hno e ⟨heJ', heI⟩
            have hr := G.reachable_of_not_isOpenForest_insert hI heI hdep
            rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hr
            · exact hr.symm
      have hiff : ∀ u v : G.Vertex,
          (G.connectionGraph G.freeBoundary (G.setConfig I)).Reachable u v ↔
          (G.connectionGraph G.freeBoundary (G.setConfig (I ∪ J))).Reachable u v :=
        fun u v => SimpleGraph.reachable_iff_of_le_of_adj_reachable hle
          (fun h => hreach h) u v
      have hcc : G.componentCount G.freeBoundary (G.setConfig I) =
          G.componentCount G.freeBoundary (G.setConfig (I ∪ J)) :=
        Nat.card_congr (SimpleGraph.connectedComponentEquivOfReachableIff hiff)
      have hccle : G.componentCount G.freeBoundary (G.setConfig (I ∪ J)) ≤
          G.componentCount G.freeBoundary (G.setConfig J) :=
        G.componentCount_anti (G.setConfig_mono Set.subset_union_right)
      have hIcard : G.componentCount G.freeBoundary (G.setConfig I) + I.ncard =
          Fintype.card G.Vertex := (G.isOpenForest_setConfig_iff I).mp hI
      have hJcard : G.componentCount G.freeBoundary (G.setConfig J) + J.ncard =
          Fintype.card G.Vertex := (G.isOpenForest_setConfig_iff J).mp hJ
      omega)
    (by intro I _; exact Set.subset_univ I)).matroid

@[simp] lemma cycleMatroid_ground : (G.cycleMatroid).E = Set.univ := rfl

@[simp] lemma cycleMatroid_indep (A : Set G.Edge) :
    (G.cycleMatroid).Indep A ↔ G.IsOpenForest G.freeBoundary (G.setConfig A) :=
  Iff.rfl

/-- Every edge of a set that lies outside one of its spanning forests has its
ends connected in that forest. -/
lemma reachable_of_mem_diff_of_isBasis {A B : Set G.Edge}
    (hB : (G.cycleMatroid).IsBasis B A) {e : G.Edge} (he : e ∈ A \ B) :
    (G.connectionGraph G.freeBoundary (G.setConfig B)).Reachable
      (G.source e) (G.target e) := by
  have hBI : G.IsOpenForest G.freeBoundary (G.setConfig B) :=
    (G.cycleMatroid_indep B).mp hB.indep
  have hdep : ¬ (G.cycleMatroid).Indep (insert e B) :=
    (hB.insert_dep he).not_indep
  exact G.reachable_of_not_isOpenForest_insert hBI he.2
    ((G.cycleMatroid_indep (insert e B)).not.mp hdep)

/-- A spanning-forest basis of an edge set has exactly the reachability
relation of the whole edge set. -/
lemma reachable_setConfig_iff_of_isBasis {A B : Set G.Edge}
    (hB : (G.cycleMatroid).IsBasis B A) (u v : G.Vertex) :
    (G.connectionGraph G.freeBoundary (G.setConfig B)).Reachable u v ↔
      (G.connectionGraph G.freeBoundary (G.setConfig A)).Reachable u v := by
  have hle : G.connectionGraph G.freeBoundary (G.setConfig B) ≤
      G.connectionGraph G.freeBoundary (G.setConfig A) :=
    G.connectionGraph_mono (G.setConfig_mono hB.subset)
  apply SimpleGraph.reachable_iff_of_le_of_adj_reachable hle
  intro x y hxy
  rcases hxy.2 with hfree | ⟨e, heA, hjoin⟩
  · exact (hxy.1 hfree).elim
  · have heA' : e ∈ A := by simpa [setConfig] using heA
    by_cases heB : e ∈ B
    · apply SimpleGraph.Adj.reachable
      exact ⟨hxy.1, Or.inr ⟨e, by simp [setConfig, heB], hjoin⟩⟩
    · have hr := G.reachable_of_mem_diff_of_isBasis hB ⟨heA', heB⟩
      rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hr
      · exact hr.symm

lemma componentCount_setConfig_of_isBasis {A B : Set G.Edge}
    (hB : (G.cycleMatroid).IsBasis B A) :
    G.componentCount G.freeBoundary (G.setConfig B) =
      G.componentCount G.freeBoundary (G.setConfig A) := by
  exact Nat.card_congr (SimpleGraph.connectedComponentEquivOfReachableIff
    (G.reachable_setConfig_iff_of_isBasis hB))

/-- The cycle-matroid rank is exactly the graph rank: rank plus the actual
number of connected components, isolated vertices included, is `|V|`. -/
lemma cycleMatroid_eRk_add_componentCount (ω : G.Configuration) :
    (G.cycleMatroid).eRk (G.openEdgeSet ω) +
        (G.componentCount G.freeBoundary ω : ℕ∞) = Fintype.card G.Vertex := by
  obtain ⟨B, hB⟩ := (G.cycleMatroid).exists_isBasis (G.openEdgeSet ω)
  have hcomp := G.componentCount_setConfig_of_isBasis hB
  rw [G.setConfig_openEdgeSet] at hcomp
  have hforest : G.IsOpenForest G.freeBoundary (G.setConfig B) :=
    (G.cycleMatroid_indep B).mp hB.indep
  have hcard := (G.isOpenForest_setConfig_iff B).mp hforest
  rw [hB.eRk_eq_encard, ← hcomp, ← (Set.toFinite B).cast_ncard_eq]
  exact_mod_cast (show B.ncard + G.componentCount G.freeBoundary (G.setConfig B) =
    Fintype.card G.Vertex by omega)

@[simp] lemma openEdgeSet_allOpen : G.openEdgeSet G.allOpen = Set.univ := by
  ext e
  simp [openEdgeSet, allOpen]

@[simp] lemma openEdgeSet_allClosed : G.openEdgeSet G.allClosed = ∅ := by
  ext e
  simp [openEdgeSet, allClosed]

lemma cycleMatroid_eRank_add_componentCount_allOpen :
    (G.cycleMatroid).eRank + (G.componentCount G.freeBoundary G.allOpen : ℕ∞) =
      Fintype.card G.Vertex := by
  rw [(G.cycleMatroid).eRank_def, G.cycleMatroid_ground, ← G.openEdgeSet_allOpen]
  exact G.cycleMatroid_eRk_add_componentCount G.allOpen

lemma openEdgeSet_dualConfig_refl (ω : G.Configuration) :
    G.openEdgeSet (FK.Configuration.dualConfig (Equiv.refl G.Edge) ω) =
      (G.openEdgeSet ω)ᶜ := by
  ext e
  cases he : ω e <;> simp [openEdgeSet, FK.Configuration.dualConfig, he]

end FK.Finite.LabelledMultigraph

namespace FK.Finite.PlaneMatroid

open scoped BigOperators Classical
open FK.Finite.LabelledMultigraph
open FK.FinitePlane

/-- A pair of finite labelled multigraphs on the same labelled edge type.  The
second vertex type is named `Face`: in an application to a plane embedding it
is the type of faces.  Loops and parallel labelled edges are permitted on both
sides. -/
structure LabelledDualPair where
  Vertex : Type*
  Face : Type*
  Edge : Type*
  [fintypeVertex : Fintype Vertex]
  [fintypeFace : Fintype Face]
  [fintypeEdge : Fintype Edge]
  source : Edge → Vertex
  target : Edge → Vertex
  dualSource : Edge → Face
  dualTarget : Edge → Face

attribute [instance] LabelledDualPair.fintypeVertex LabelledDualPair.fintypeFace
  LabelledDualPair.fintypeEdge

namespace LabelledDualPair

variable (P : LabelledDualPair)

/-- The primal labelled multigraph. -/
def primal : LabelledMultigraph where
  Vertex := P.Vertex
  Edge := P.Edge
  source := P.source
  target := P.target

/-- The graph on face vertices, with the same labelled edges. -/
def faceDual : LabelledMultigraph where
  Vertex := P.Face
  Edge := P.Edge
  source := P.dualSource
  target := P.dualTarget

/-- A combinatorial graphic-duality certificate.  The first field is Whitney's
matroid condition; the second is genuine connectivity of the all-open dual,
not merely preconnectedness of an empty graph.  No component-form Euler
identity appears among the hypotheses. -/
structure GraphicDualCertificate : Prop where
  dual_cycleMatroid : (P.primal.cycleMatroid)✶ = P.faceDual.cycleMatroid
  nonemptyFace : Nonempty P.Face
  allOpen_preconnected :
    (P.faceDual.connectionGraph P.faceDual.freeBoundary P.faceDual.allOpen).Preconnected

lemma dual_eRank_add_one (hP : P.GraphicDualCertificate) :
    (P.primal.cycleMatroid)✶.eRank + 1 = (Fintype.card P.Face : ℕ∞) := by
  rw [hP.dual_cycleMatroid]
  have h := P.faceDual.cycleMatroid_eRank_add_componentCount_allOpen
  have hk : P.faceDual.componentCount P.faceDual.freeBoundary P.faceDual.allOpen = 1 :=
    componentCount_eq_one_of_preconnected P.faceDual P.faceDual.freeBoundary
      P.faceDual.allOpen hP.nonemptyFace.some hP.allOpen_preconnected
  rw [hk] at h
  exact h

/-- **Component-form Euler identity from graphic matroid duality.**  This is
proved for every Boolean configuration, including every loop and parallel
label, using Mathlib's dual-rank identity and the actual connection graphs.
The theorem is not a claim that arbitrary labelled graphs are planar: an
embedding must supply `GraphicDualCertificate`. -/
theorem componentCount_dual_add_card_vertices (hP : P.GraphicDualCertificate)
    (ω : P.Edge → Bool) :
    P.faceDual.componentCount P.faceDual.freeBoundary
        (FK.Configuration.dualConfig (Equiv.refl P.Edge) ω) + Fintype.card P.Vertex =
      P.primal.componentCount P.primal.freeBoundary ω + 1 + openCard ω := by
  let M : Matroid P.Edge := P.primal.cycleMatroid
  let X : Set P.Edge := P.primal.openEdgeSet ω
  let η : P.Edge → Bool := FK.Configuration.dualConfig (Equiv.refl P.Edge) ω
  have hset : P.faceDual.openEdgeSet η = Xᶜ := by
    exact P.primal.openEdgeSet_dualConfig_refl ω
  have hrankP := P.primal.cycleMatroid_eRk_add_componentCount ω
  change M.eRk X + (P.primal.componentCount P.primal.freeBoundary ω : ℕ∞) =
    Fintype.card P.Vertex at hrankP
  have hrankD := P.faceDual.cycleMatroid_eRk_add_componentCount η
  rw [hset, ← hP.dual_cycleMatroid] at hrankD
  change M✶.eRk Xᶜ + (P.faceDual.componentCount P.faceDual.freeBoundary η : ℕ∞) =
    Fintype.card P.Face at hrankD
  have hlocal0 := M.eRk_dual_add_eRank Xᶜ (by
    change Xᶜ ⊆ Set.univ
    exact Set.subset_univ _)
  rw [show M.E = Set.univ by rfl, Set.sdiff_compl, Set.univ_inter,
    ← (Set.toFinite Xᶜ).cast_ncard_eq] at hlocal0
  have hlocal : M✶.eRk Xᶜ + M.eRank = M.eRk X + (Xᶜ.ncard : ℕ∞) := hlocal0
  have hglobal0 := M.eRank_add_eRank_dual
  rw [show M.E = Set.univ by rfl, Set.encard_univ, ENat.card_eq_coe_fintype_card] at hglobal0
  have hface : M✶.eRank + 1 = (Fintype.card P.Face : ℕ∞) := by
    exact P.dual_eRank_add_one hP
  have hopen : openCard ω = X.ncard := by
    exact P.primal.openCard_eq_ncard_openEdgeSet ω
  have hcard : openCard ω + Xᶜ.ncard = Fintype.card P.Edge := by
    rw [hopen]
    have hcard0 := Set.ncard_add_ncard_compl X (Set.toFinite X) (Set.toFinite Xᶜ)
    rw [Nat.card_eq_fintype_card] at hcard0
    change X.ncard + Xᶜ.ncard = Fintype.card P.Edge at hcard0
    exact hcard0
  let a : ℕ := (M.eRk X).toNat
  let d : ℕ := (M✶.eRk Xᶜ).toNat
  let r : ℕ := M.eRank.toNat
  let rD : ℕ := M✶.eRank.toNat
  have ha : (a : ℕ∞) = M.eRk X := by
    exact ENat.natCast_toNat (M.isRkFinite_set X).eRk_lt_top.ne
  have hd : (d : ℕ∞) = M✶.eRk Xᶜ := by
    exact ENat.natCast_toNat (M✶.isRkFinite_set Xᶜ).eRk_lt_top.ne
  have hr : (r : ℕ∞) = M.eRank := by
    exact ENat.natCast_toNat (M.eRank_ne_top_iff.mpr inferInstance)
  have hrD : (rD : ℕ∞) = M✶.eRank := by
    exact ENat.natCast_toNat (M✶.eRank_ne_top_iff.mpr inferInstance)
  rw [← ha] at hrankP hlocal
  rw [← hd] at hrankD hlocal
  rw [← hr] at hlocal hglobal0
  rw [← hrD] at hglobal0 hface
  have hrankP' : a + P.primal.componentCount P.primal.freeBoundary ω =
      Fintype.card P.Vertex := by exact_mod_cast hrankP
  have hrankD' : d + P.faceDual.componentCount P.faceDual.freeBoundary η =
      Fintype.card P.Face := by exact_mod_cast hrankD
  have hlocal' : d + r = a + Xᶜ.ncard := by exact_mod_cast hlocal
  have hglobal' : r + rD = Fintype.card P.Edge := by exact_mod_cast hglobal0
  have hface' : rD + 1 = Fintype.card P.Face := by exact_mod_cast hface
  change P.faceDual.componentCount P.faceDual.freeBoundary η + Fintype.card P.Vertex =
    P.primal.componentCount P.primal.freeBoundary ω + 1 + openCard ω
  omega

/-- The usual Euler relation for the all-open primal configuration.  In the
possibly disconnected case its right side contains the all-open component
count. -/
theorem euler_allOpen (hP : P.GraphicDualCertificate) :
    Fintype.card P.Face + Fintype.card P.Vertex =
      P.primal.componentCount P.primal.freeBoundary P.primal.allOpen + 1 +
        Fintype.card P.Edge := by
  let ω : P.Edge → Bool := fun _ => true
  have h := P.componentCount_dual_add_card_vertices hP ω
  have hk : P.faceDual.componentCount P.faceDual.freeBoundary
      (FK.Configuration.dualConfig (Equiv.refl P.Edge) ω) = Fintype.card P.Face := by
    change P.faceDual.componentCount P.faceDual.freeBoundary (fun _ : P.Edge => false) =
      Fintype.card P.Face
    change P.faceDual.componentCount P.faceDual.freeBoundary P.faceDual.allClosed =
      Fintype.card P.Face
    exact P.faceDual.componentCount_free_allClosed.trans Nat.card_eq_fintype_card
  have hω : ω = P.primal.allOpen := rfl
  have ho : openCard ω = Fintype.card P.Edge := by
    rw [hω]
    exact openCard_allOpen P.primal
  calc
    Fintype.card P.Face + Fintype.card P.Vertex =
        P.faceDual.componentCount P.faceDual.freeBoundary
          (FK.Configuration.dualConfig (Equiv.refl P.Edge) ω) + Fintype.card P.Vertex :=
      (congrArg (fun n : ℕ => n + Fintype.card P.Vertex) hk.symm)
    _ = P.primal.componentCount P.primal.freeBoundary ω + 1 + openCard ω := h
    _ = P.primal.componentCount P.primal.freeBoundary P.primal.allOpen + 1 +
        Fintype.card P.Edge := by rw [ho, hω]

/-- Standard `V - E + F = 2`, in subtraction-free form, when the primal
all-open graph is connected. -/
theorem euler_allOpen_of_preconnected (hP : P.GraphicDualCertificate)
    (hV : Nonempty P.Vertex)
    (hconn : (P.primal.connectionGraph P.primal.freeBoundary
      P.primal.allOpen).Preconnected) :
    Fintype.card P.Face + Fintype.card P.Vertex = Fintype.card P.Edge + 2 := by
  have hk : P.primal.componentCount P.primal.freeBoundary P.primal.allOpen = 1 :=
    componentCount_eq_one_of_preconnected P.primal P.primal.freeBoundary
      P.primal.allOpen hV.some hconn
  have h := P.euler_allOpen hP
  rw [hk] at h
  omega

/-- Actual finite FK duality with its ambient geometric Euler obligation
proved by the graphic-dual certificate. -/
theorem actual_fkPMF_graphicDual_duality (hP : P.GraphicDualCertificate)
    (q p : NNReal) (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF.map (FK.Configuration.dualEquiv (Equiv.refl P.Edge))
        (P.primal.fkPMF hq hp₁.le P.primal.freeBoundary) =
      P.faceDual.fkPMF hq (dualParameter_le_one hq hp₁.le)
        P.faceDual.freeBoundary := by
  apply actual_fkPMF_duality P.primal P.faceDual (Equiv.refl P.Edge) q p hq hp₀ hp₁
  intro ω
  exact P.componentCount_dual_add_card_vertices hP ω

end LabelledDualPair
end FK.Finite.PlaneMatroid
