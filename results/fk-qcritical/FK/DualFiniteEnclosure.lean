import FK.PrimalOpenBoundary
import FK.ClosedBoundaryEventually
import FK.NonlocalGeometry
import FK.StrongUniqueness

/-!
# Finite dual boxes with metrically cofinal closed boundaries

This module constructs the deterministic finite-box input to the planar
open-circuit argument.  It uses the existing connected finite-region and
open-cluster closure constructions, but replaces a countable vertex
enumeration by proper metric balls.  No Jordan-circuit assertion is made.
-/

namespace FK.PlaneTopology.DualExhaustion

open Set Metric
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK FK.Configuration
open FK.InfiniteVolume.NonlocalInterior

variable {V X : Type*}

/-- Enlarge a finite connected region so that it also contains a prescribed
finite set.  The proof uses only ambient preconnectedness. -/
lemma exists_finiteConnectedRegion_superset {G : SimpleGraph V}
    (hG : G.Preconnected) (R : FiniteConnectedRegion G)
    {A : Set V} (hA : A.Finite) :
    ∃ S : FiniteConnectedRegion G, R.carrier ∪ A ⊆ S.carrier := by
  classical
  obtain ⟨v, hv⟩ := R.connected.nonempty
  have hn : (R.finite.toFinset ∪ hA.toFinset).Nonempty :=
    ⟨v, Finset.mem_union_left _ (R.finite.mem_toFinset.mpr hv)⟩
  obtain ⟨t, ht, hconn⟩ := SimpleGraph.extend_finset_to_connected hG hn
  refine ⟨⟨t, t.finite_toSet, hconn⟩, ?_⟩
  intro x hx
  apply ht
  rcases hx with hxR | hxA
  · exact Finset.mem_union_left _ (R.finite.mem_toFinset.mpr hxR)
  · exact Finset.mem_union_right _ (hA.mem_toFinset.mpr hxA)

/-- A chosen finite connected enlargement. -/
noncomputable def enlargeFiniteConnectedRegion {G : SimpleGraph V}
    (hG : G.Preconnected) (R : FiniteConnectedRegion G)
    {A : Set V} (hA : A.Finite) : FiniteConnectedRegion G :=
  (exists_finiteConnectedRegion_superset hG R hA).choose

lemma subset_enlargeFiniteConnectedRegion {G : SimpleGraph V}
    (hG : G.Preconnected) (R : FiniteConnectedRegion G)
    {A : Set V} (hA : A.Finite) :
    R.carrier ∪ A ⊆ (enlargeFiniteConnectedRegion hG R hA).carrier :=
  (exists_finiteConnectedRegion_superset hG R hA).choose_spec

/-- Recursively constructed finite connected bases covering an arbitrary
countable family of finite sets.  Countability of the vertex type is not
needed: the family is supplied directly. -/
noncomputable def connectedBases {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite) :
    ℕ → FiniteConnectedRegion G
  | 0 => enlargeFiniteConnectedRegion hG (FiniteConnectedRegion.singleton v₀) (hB 0)
  | n + 1 => enlargeFiniteConnectedRegion hG (connectedBases hG v₀ B hB n) (hB (n + 1))

lemma subset_connectedBases_zero {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite) :
    B 0 ⊆ (connectedBases hG v₀ B hB 0).carrier := by
  intro x hx
  exact subset_enlargeFiniteConnectedRegion hG _ (hB 0) (Or.inr hx)

lemma subset_connectedBases_succ {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite) (n : ℕ) :
    B (n + 1) ⊆ (connectedBases hG v₀ B hB (n + 1)).carrier := by
  intro x hx
  exact subset_enlargeFiniteConnectedRegion hG _ (hB (n + 1)) (Or.inr hx)

lemma carrier_connectedBases_succ {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite) (n : ℕ) :
    (connectedBases hG v₀ B hB n).carrier ⊆
      (connectedBases hG v₀ B hB (n + 1)).carrier := by
  intro x hx
  exact subset_enlargeFiniteConnectedRegion hG _ (hB (n + 1)) (Or.inl hx)

lemma monotone_carrier_connectedBases {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite) :
    Monotone (fun n => (connectedBases hG v₀ B hB n).carrier) := by
  apply monotone_nat_of_le_succ
  exact carrier_connectedBases_succ hG v₀ B hB

lemma mem_connectedBases {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite) {x : V} {n : ℕ}
    (hx : x ∈ B n) : x ∈ (connectedBases hG v₀ B hB n).carrier := by
  cases n with
  | zero => exact subset_connectedBases_zero hG v₀ B hB hx
  | succ n => exact subset_connectedBases_succ hG v₀ B hB n hx

lemma iUnion_carrier_connectedBases {G : SimpleGraph V} (hG : G.Preconnected)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite)
    (hcover : ∀ x, ∃ n, x ∈ B n) :
    (⋃ n, (connectedBases hG v₀ B hB n).carrier) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := hcover x
  exact Set.mem_iUnion.mpr ⟨n, mem_connectedBases hG v₀ B hB hn⟩

/-- The finite connected closed-boundary exhaustion attached to a supplied
family of finite bases.  Its `n`-th region contains the `n`-th base. -/
noncomputable def closedBoundaryExhaustionOfBases {G H : SimpleGraph V}
    (hG : G.Preconnected) (hHG : H ≤ G) (hfin : FiniteOpenClusters H)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite)
    (hcover : ∀ x, ∃ n, x ∈ B n) : ClosedBoundaryExhaustion G H :=
  closedBoundaryExhaustion hHG hfin
    (fun n => (connectedBases hG v₀ B hB n).carrier)
    (fun n => (connectedBases hG v₀ B hB n).finite)
    (fun n => (connectedBases hG v₀ B hB n).connected)
    (monotone_carrier_connectedBases hG v₀ B hB)
    (iUnion_carrier_connectedBases hG v₀ B hB hcover)

lemma mem_region_closedBoundaryExhaustionOfBases {G H : SimpleGraph V}
    (hG : G.Preconnected) (hHG : H ≤ G) (hfin : FiniteOpenClusters H)
    (v₀ : V) (B : ℕ → Set V) (hB : ∀ n, (B n).Finite)
    (hcover : ∀ x, ∃ n, x ∈ B n) {x : V} {n : ℕ} (hx : x ∈ B n) :
    x ∈ (closedBoundaryExhaustionOfBases hG hHG hfin v₀ B hB hcover).region n := by
  exact subset_closedRegion (mem_connectedBases hG v₀ B hB hx)

/-- Proper metric balls supply finite connected bases without enumerating the
vertex type. -/
lemma exists_nat_mem_ball [PseudoMetricSpace X] (vertex : V → X) (c : X) (x : V) :
    ∃ n : ℕ, x ∈ vertex ⁻¹' ball c (n : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (dist (vertex x) c)
  exact ⟨n, Metric.mem_ball.mpr hn⟩

/-- **Metric finite-box construction.**  Finite open clusters and finite
preimages of metric balls give a monotone, exhaustive family of finite
connected regions with closed ambient boundary, cofinal with respect to the
balls of integer radius. -/
noncomputable def metricClosedBoundaryExhaustion [PseudoMetricSpace X]
    {G H : SimpleGraph V} [Nonempty V]
    (hG : G.Preconnected) (hHG : H ≤ G) (hfin : FiniteOpenClusters H)
    (vertex : V → X) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite) :
    ClosedBoundaryExhaustion G H :=
  closedBoundaryExhaustionOfBases hG hHG hfin (Classical.choice inferInstance)
    (fun n : ℕ => vertex ⁻¹' ball c (n : ℝ)) (fun n => hproper n)
    (exists_nat_mem_ball vertex c)

lemma ball_subset_metricClosedBoundaryExhaustion [PseudoMetricSpace X]
    {G H : SimpleGraph V} [Nonempty V]
    (hG : G.Preconnected) (hHG : H ≤ G) (hfin : FiniteOpenClusters H)
    (vertex : V → X) (c : X)
    (hproper : ∀ r : ℝ, (vertex ⁻¹' ball c r).Finite) (n : ℕ) :
    vertex ⁻¹' ball c (n : ℝ) ⊆
      (metricClosedBoundaryExhaustion hG hHG hfin vertex c hproper).region n := by
  intro x hx
  exact mem_region_closedBoundaryExhaustionOfBases hG hHG hfin _ _ _ _ hx


/-- The oriented edge cut of a vertex set, represented on the actual simple
edge subtype.  Parallel-label collapse is not involved. -/
def edgeCut {F : Type*} (G : SimpleGraph F) (S : Set F) : Set G.edgeSet :=
  {e | ∃ x ∈ S, ∃ y ∉ S, G.Adj x y ∧ e.1 = s(x, y)}

lemma edgeCut_subset_clusterSupport {F : Type*} {G : SimpleGraph F} {S : Set F} :
    edgeCut G S ⊆ clusterSupport S := by
  rintro e ⟨x, hx, y, _hy, _hxy, he⟩
  refine ⟨x, hx, ?_⟩
  rw [he]
  simp

lemma finite_edgeCut {F : Type*} {G : SimpleGraph F} [G.LocallyFinite]
    {S : Set F} (hS : S.Finite) : (edgeCut G S).Finite := by
  exact (finite_clusterSupport hS).subset edgeCut_subset_clusterSupport

/-- Every dual edge crossing a closed ambient boundary is closed in the
configuration whose open graph defines that boundary. -/
lemma dual_closed_of_mem_edgeCut {F : Type*} {G : SimpleGraph F}
    {ω : G.edgeSet → Bool} {S : Set F}
    (hS : ClosedBoundary G (openGraph G (openSet ω)) S)
    {e : G.edgeSet} (he : e ∈ edgeCut G S) : ω e = false := by
  apply Bool.eq_false_iff.mpr
  intro hopen
  obtain ⟨x, hx, y, hy, hxy, hexy⟩ := he
  apply hS hx hy hxy
  rw [openGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨e, hopen, hexy⟩, G.ne_of_adj hxy⟩

/-- Under the prescribed global edge equivalence, the primal label associated
with a dual closed-boundary edge is genuinely open. -/
lemma primal_open_of_mem_edgeCut {V F : Type*} {G : SimpleGraph V}
    {GD : SimpleGraph F} (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    {S : Set F}
    (hS : ClosedBoundary GD (openGraph GD (openSet (dualConfig edge ω))) S)
    {f : GD.edgeSet} (hf : f ∈ edgeCut GD S) : ω (edge.symm f) = true := by
  have hclosed := dual_closed_of_mem_edgeCut hS hf
  change (!(ω (edge.symm f))) = false at hclosed
  cases h : ω (edge.symm f) <;> simp [h] at hclosed ⊢

/-- An open cluster rooted in a cluster-closed region cannot leave it. -/
lemma openCluster_subset_closedRegion {F : Type*} {H : SimpleGraph F}
    {T : Set F} {x : F} (hx : x ∈ ClosedRegion H T) :
    OpenCluster H x ⊆ ClosedRegion H T := by
  simp only [ClosedRegion, Set.mem_iUnion] at hx ⊢
  obtain ⟨v, hvT, hvx⟩ := hx
  intro y hxy
  apply Set.mem_iUnion_of_mem v
  apply Set.mem_iUnion_of_mem hvT
  rw [mem_openCluster_iff] at hvx hxy ⊢
  exact hvx.trans hxy

lemma mem_closedRegion_of_openConnected {F : Type*} {G : SimpleGraph F}
    {ω : G.edgeSet → Bool} {T : Set F} {x y : F}
    (hx : x ∈ ClosedRegion (openGraph G (openSet ω)) T)
    (hxy : OpenConnected G ω Set.univ x y) :
    y ∈ ClosedRegion (openGraph G (openSet ω)) T := by
  apply openCluster_subset_closedRegion hx
  rw [mem_openCluster_iff, reachable_openGraph_openSet_iff]
  exact hxy

/-- The chosen metrically cofinal dual closed-boundary exhaustion associated
with a nonpercolating complementary configuration. -/
noncomputable def planarDualMetricExhaustion [PseudoMetricSpace X]
    {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F]
    (hGD : GD.Preconnected) (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite) :
    ClosedBoundaryExhaustion GD (openGraph GD (openSet (dualConfig edge ω))) :=
  metricClosedBoundaryExhaustion hGD (openGraph_le GD (dualConfig edge ω))
    (finiteOpenClusters_of_nonPercolating GD (dualConfig edge ω) hdual)
    dualVertex c hproper

lemma ball_subset_planarDualMetricExhaustion [PseudoMetricSpace X]
    {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F]
    (hGD : GD.Preconnected) (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite) (n : ℕ) :
    dualVertex ⁻¹' ball c (n : ℝ) ⊆
      (planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n := by
  exact ball_subset_metricClosedBoundaryExhaustion hGD
    (openGraph_le GD (dualConfig edge ω))
    (finiteOpenClusters_of_nonPercolating GD (dualConfig edge ω) hdual)
    dualVertex c hproper n

lemma finite_edgeCut_planarDualMetricExhaustion [PseudoMetricSpace X]
    {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F]
    [GD.LocallyFinite]
    (hGD : GD.Preconnected) (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite) (n : ℕ) :
    (edgeCut GD
      ((planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n)).Finite := by
  exact finite_edgeCut
    ((planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).finite n)

/-- Every edge of every box boundary in the constructed exhaustion is open in
 the original primal configuration after applying `edge.symm`. -/
lemma primal_open_edgeCut_planarDualMetricExhaustion [PseudoMetricSpace X]
    {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F]
    (hGD : GD.Preconnected) (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite)
    {n : ℕ} {f : GD.edgeSet}
    (hf : f ∈ edgeCut GD
      ((planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n)) :
    ω (edge.symm f) = true := by
  exact primal_open_of_mem_edgeCut edge ω
    ((planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).closed n) hf

/-- A dual-open component rooted in the integer-radius ball is contained in
 the corresponding finite connected box. -/
lemma dualComponent_subset_planarDualMetricExhaustion [PseudoMetricSpace X]
    {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F]
    (hGD : GD.Preconnected) (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite)
    {n : ℕ} {x : F} (hx : dualVertex x ∈ ball c (n : ℝ)) {y : F}
    (hxy : OpenConnected GD (dualConfig edge ω) Set.univ x y) :
    y ∈ (planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper).region n := by
  exact mem_closedRegion_of_openConnected
    (ball_subset_planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper n hx)
    hxy

/-- **Scoped finite-box theorem.**  Dual nonpercolation, preconnectedness,
local finiteness and ball-properness produce a monotone exhaustive sequence of
finite connected dual boxes.  The boxes cover all integer metric balls, have
finite edge cuts, trap the corresponding dual-open components, and all their
cut labels map to genuinely open primal edges.  The remaining planar task is
to select an enclosing primal Jordan circuit inside one of these cuts. -/
theorem exists_metric_dual_boxes_with_primalOpen_boundaries [PseudoMetricSpace X]
    {V F : Type*} {G : SimpleGraph V} {GD : SimpleGraph F} [Nonempty F]
    [GD.LocallyFinite]
    (hGD : GD.Preconnected) (edge : G.edgeSet ≃ GD.edgeSet) (ω : G.edgeSet → Bool)
    (hdual : FK.Planar.NoInfiniteOpenCluster GD (dualConfig edge ω))
    (dualVertex : F → X) (c : X)
    (hproper : ∀ r : ℝ, (dualVertex ⁻¹' ball c r).Finite) :
    ∃ E : ClosedBoundaryExhaustion GD (openGraph GD (openSet (dualConfig edge ω))),
      (∀ n : ℕ, dualVertex ⁻¹' ball c (n : ℝ) ⊆ E.region n) ∧
      (∀ n : ℕ, (edgeCut GD (E.region n)).Finite) ∧
      (∀ (n : ℕ) (f : GD.edgeSet), f ∈ edgeCut GD (E.region n) →
        ω (edge.symm f) = true) ∧
      (∀ (n : ℕ) (x y : F), dualVertex x ∈ ball c (n : ℝ) →
        OpenConnected GD (dualConfig edge ω) Set.univ x y → y ∈ E.region n) := by
  let E := planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · exact ball_subset_planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper
  · exact finite_edgeCut_planarDualMetricExhaustion hGD edge ω hdual dualVertex c hproper
  · intro n f hf
    exact primal_open_edgeCut_planarDualMetricExhaustion hGD edge ω hdual
      dualVertex c hproper hf
  · intro n x y hx hxy
    exact dualComponent_subset_planarDualMetricExhaustion hGD edge ω hdual
      dualVertex c hproper hx hxy

end FK.PlaneTopology.DualExhaustion

#print axioms FK.PlaneTopology.DualExhaustion.exists_finiteConnectedRegion_superset
#print axioms FK.PlaneTopology.DualExhaustion.connectedBases
#print axioms FK.PlaneTopology.DualExhaustion.closedBoundaryExhaustionOfBases
#print axioms FK.PlaneTopology.DualExhaustion.metricClosedBoundaryExhaustion
#print axioms FK.PlaneTopology.DualExhaustion.ball_subset_metricClosedBoundaryExhaustion
#print axioms FK.PlaneTopology.DualExhaustion.finite_edgeCut
#print axioms FK.PlaneTopology.DualExhaustion.primal_open_of_mem_edgeCut
#print axioms FK.PlaneTopology.DualExhaustion.mem_closedRegion_of_openConnected
#print axioms FK.PlaneTopology.DualExhaustion.planarDualMetricExhaustion
#print axioms FK.PlaneTopology.DualExhaustion.finite_edgeCut_planarDualMetricExhaustion
#print axioms FK.PlaneTopology.DualExhaustion.primal_open_edgeCut_planarDualMetricExhaustion
#print axioms FK.PlaneTopology.DualExhaustion.dualComponent_subset_planarDualMetricExhaustion
#print axioms FK.PlaneTopology.DualExhaustion.exists_metric_dual_boxes_with_primalOpen_boundaries
