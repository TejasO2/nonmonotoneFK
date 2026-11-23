import Mathlib

/-!
# Finite regions with closed boundary in a non-percolating configuration

This file isolates the deterministic graph step in Theorem 5.1 of
Beffara--Faipeur--Oke (arXiv:2512.16486).  `H` is the spanning subgraph of
open edges of an ambient graph `G`.  A finite connected set is enlarged by
all open clusters based at its vertices.  The enlarged set is still finite
and connected, and every ambient edge leaving it is closed.
-/

open Set
open scoped BigOperators

namespace FK

variable {V : Type*}

/-- The open cluster at `v`, viewed as the support of a connected component. -/
def OpenCluster (H : SimpleGraph V) (v : V) : Set V :=
  (H.connectedComponentMk v).supp

@[simp] theorem self_mem_openCluster (H : SimpleGraph V) (v : V) :
    v ∈ OpenCluster H v := by
  rfl

theorem mem_openCluster_iff {H : SimpleGraph V} {v w : V} :
    w ∈ OpenCluster H v ↔ H.Reachable v w := by
  change H.connectedComponentMk w = H.connectedComponentMk v ↔ H.Reachable v w
  rw [SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Every open cluster is finite (the pointwise form of subcriticality). -/
def FiniteOpenClusters (H : SimpleGraph V) : Prop :=
  ∀ v, (OpenCluster H v).Finite

/-- Finite open clusters are inherited by every spanning subgraph of open
edges.  Under a coupling `ω₁ ≤ ω₃`, this passes subcriticality from the
dominating configuration to the dominated one. -/
theorem FiniteOpenClusters.mono {H K : SimpleGraph V} (hHK : H ≤ K)
    (hfin : FiniteOpenClusters K) : FiniteOpenClusters H := by
  intro v
  apply (hfin v).subset
  intro w hw
  rw [mem_openCluster_iff] at hw ⊢
  exact hw.mono hHK

/-- Enlarge `T` by every open cluster based at a vertex of `T`. -/
def ClosedRegion (H : SimpleGraph V) (T : Set V) : Set V :=
  ⋃ v ∈ T, OpenCluster H v

theorem subset_closedRegion {H : SimpleGraph V} {T : Set V} :
    T ⊆ ClosedRegion H T := by
  intro v hv
  exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv (self_mem_openCluster H v))

theorem closedRegion_finite {H : SimpleGraph V} {T : Set V}
    (hT : T.Finite) (hH : FiniteOpenClusters H) :
    (ClosedRegion H T).Finite := by
  exact hT.biUnion fun v _ => hH v

theorem closedRegion_mono {H : SimpleGraph V} {T U : Set V} (hTU : T ⊆ U) :
    ClosedRegion H T ⊆ ClosedRegion H U := by
  intro x hx
  simp only [ClosedRegion, Set.mem_iUnion] at hx ⊢
  obtain ⟨v, hv, hxv⟩ := hx
  exact ⟨v, hTU hv, hxv⟩

/-- `S` has closed boundary when every ambient edge crossing out of `S`
is absent from the open-edge graph `H`. -/
def ClosedBoundary (G H : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∉ S → G.Adj x y → ¬ H.Adj x y

/-- Closedness of a fixed boundary passes from a larger open-edge graph to
a smaller one.  In Theorem 5.1 this applies simultaneously to both dominated
configurations `ω₁, ω₂ ≤ ω₃`. -/
theorem ClosedBoundary.mono {G H K : SimpleGraph V} {S : Set V}
    (hHK : H ≤ K) (hK : ClosedBoundary G K S) : ClosedBoundary G H S := by
  intro x y hx hy hG hxy
  exact hK hx hy hG (hHK hxy)

theorem closedRegion_closedBoundary {G H : SimpleGraph V} {T : Set V} :
    ClosedBoundary G H (ClosedRegion H T) := by
  intro x y hx hy _ hxy
  apply hy
  simp only [ClosedRegion, Set.mem_iUnion] at hx ⊢
  obtain ⟨v, hv, hxv⟩ := hx
  refine ⟨v, hv, ?_⟩
  exact (H.connectedComponentMk v).mem_supp_of_adj_mem_supp hxv hxy

/-- Transport a path in an open cluster to the ambient induced graph on any
set containing that cluster. -/
theorem reachable_induce_of_openCluster_subset {G H : SimpleGraph V}
    (hHG : H ≤ G) {S : Set V} {a x : V} (hax : H.Reachable a x)
    (haS : a ∈ S) (hxS : x ∈ S)
    (hsub : OpenCluster H a ⊆ S) :
    (G.induce S).Reachable ⟨a, haS⟩ ⟨x, hxS⟩ := by
  let C := H.connectedComponentMk a
  let f : C.toSimpleGraph →g G.induce S :=
    { toFun := fun z => ⟨z.1, hsub z.2⟩
      map_rel' := by
        intro u v huv
        exact hHG huv }
  have hC : C.toSimpleGraph.Reachable
      ⟨a, self_mem_openCluster H a⟩
      ⟨x, mem_openCluster_iff.mpr hax⟩ :=
    C.reachable_toSimpleGraph _ _
  exact hC.map f

/-- The cluster enlargement of a connected set is connected in the ambient
graph.  Open edges are used only inside each attached cluster; paths between
the base vertices lie in the original connected set `T`. -/
theorem closedRegion_connected {G H : SimpleGraph V} (hHG : H ≤ G)
    {T : Set V} (hT : (G.induce T).Connected) :
    (G.induce (ClosedRegion H T)).Connected := by
  have hTS : T ⊆ ClosedRegion H T := subset_closedRegion
  refine { preconnected := ?_, nonempty := ?_ }
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [ClosedRegion, Set.mem_iUnion] at hx hy
    obtain ⟨a, haT, hxa⟩ := hx
    obtain ⟨b, hbT, hyb⟩ := hy
    have hax : H.Reachable a x := mem_openCluster_iff.mp hxa
    have hby : H.Reachable b y := mem_openCluster_iff.mp hyb
    have haS : a ∈ ClosedRegion H T := hTS haT
    have hbS : b ∈ ClosedRegion H T := hTS hbT
    have hxS : x ∈ ClosedRegion H T :=
      Set.mem_iUnion_of_mem a (Set.mem_iUnion_of_mem haT hxa)
    have hyS : y ∈ ClosedRegion H T :=
      Set.mem_iUnion_of_mem b (Set.mem_iUnion_of_mem hbT hyb)
    have haxS : (G.induce (ClosedRegion H T)).Reachable ⟨a, haS⟩ ⟨x, hxS⟩ :=
      reachable_induce_of_openCluster_subset hHG hax haS hxS
        (fun z hz => Set.mem_iUnion_of_mem a (Set.mem_iUnion_of_mem haT hz))
    have hbyS : (G.induce (ClosedRegion H T)).Reachable ⟨b, hbS⟩ ⟨y, hyS⟩ :=
      reachable_induce_of_openCluster_subset hHG hby hbS hyS
        (fun z hz => Set.mem_iUnion_of_mem b (Set.mem_iUnion_of_mem hbT hz))
    have habT : (G.induce T).Reachable ⟨a, haT⟩ ⟨b, hbT⟩ :=
      hT.preconnected _ _
    have habS : (G.induce (ClosedRegion H T)).Reachable ⟨a, haS⟩ ⟨b, hbS⟩ :=
      habT.map (G.induceHomOfLE hTS).toHom
    exact haxS.symm.trans (habS.trans hbyS)
  · obtain ⟨a, ha⟩ := hT.nonempty
    exact ⟨⟨a, hTS ha⟩⟩

structure FiniteConnectedRegion (G : SimpleGraph V) where
  carrier : Set V
  finite : carrier.Finite
  connected : (G.induce carrier).Connected

namespace FiniteConnectedRegion

variable {G : SimpleGraph V}

def singleton (v : V) : FiniteConnectedRegion G where
  carrier := {v}
  finite := Set.finite_singleton v
  connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨SimpleGraph.Preconnected.of_subsingleton, ⟨⟨v, rfl⟩⟩⟩

theorem exists_extension (hG : G.Preconnected) (R : FiniteConnectedRegion G) (v : V) :
    ∃ S : FiniteConnectedRegion G, R.carrier ⊆ S.carrier ∧ v ∈ S.carrier := by
  classical
  obtain ⟨t', ht', hconn⟩ := SimpleGraph.extend_finset_to_connected hG
    (t := R.finite.toFinset ∪ {v}) (by simp)
  refine ⟨⟨t', t'.finite_toSet, hconn⟩, ?_, ?_⟩
  · intro x hx
    apply ht'
    simp only [Finset.mem_union, Finset.mem_singleton]
    exact Or.inl (R.finite.mem_toFinset.mpr hx)
  · apply ht'
    simp

noncomputable def extension (hG : G.Preconnected) (R : FiniteConnectedRegion G) (v : V) :
    FiniteConnectedRegion G :=
  (exists_extension hG R v).choose

theorem subset_extension (hG : G.Preconnected) (R : FiniteConnectedRegion G) (v : V) :
    R.carrier ⊆ (extension hG R v).carrier :=
  (exists_extension hG R v).choose_spec.1

theorem mem_extension (hG : G.Preconnected) (R : FiniteConnectedRegion G) (v : V) :
    v ∈ (extension hG R v).carrier :=
  (exists_extension hG R v).choose_spec.2

noncomputable def sequence (hG : G.Preconnected) (e : ℕ → V) (v₀ : V) :
    ℕ → FiniteConnectedRegion G
  | 0 => singleton v₀
  | n + 1 => extension hG (sequence hG e v₀ n) (e n)

end FiniteConnectedRegion

theorem exists_finiteConnectedExhaustion {G : SimpleGraph V} (hG : G.Preconnected)
    (e : ℕ → V) (he : Function.Surjective e) (v₀ : V) :
    ∃ T : ℕ → Set V, (∀ n, (T n).Finite) ∧
      (∀ n, (G.induce (T n)).Connected) ∧ Monotone T ∧
      (⋃ n, T n) = Set.univ := by
  let R := FiniteConnectedRegion.sequence hG e v₀
  refine ⟨fun n => (R n).carrier, fun n => (R n).finite,
    fun n => (R n).connected, ?_, ?_⟩
  · apply monotone_nat_of_le_succ
    intro n
    exact FiniteConnectedRegion.subset_extension hG
      (FiniteConnectedRegion.sequence hG e v₀ n) (e n)
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, rfl⟩ := he x
    apply Set.mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    exact FiniteConnectedRegion.mem_extension hG
      (FiniteConnectedRegion.sequence hG e v₀ n) (e n)

/-- A finite connected exhaustion by regions whose ambient boundaries are
closed in `H`. -/
structure ClosedBoundaryExhaustion (G H : SimpleGraph V) where
  region : ℕ → Set V
  finite : ∀ n, (region n).Finite
  connected : ∀ n, (G.induce (region n)).Connected
  closed : ∀ n, ClosedBoundary G H (region n)
  monotone : Monotone region
  exhaustive : ⋃ n, region n = Set.univ

/-- Construct the closed-boundary exhaustion used in Theorem 5.1 from any
finite connected exhaustion.  The latter is an explicit geometric input;
local finiteness is not needed for this deterministic enlargement. -/
def closedBoundaryExhaustion {G H : SimpleGraph V} (hHG : H ≤ G)
    (hfin : FiniteOpenClusters H) (T : ℕ → Set V)
    (hTfin : ∀ n, (T n).Finite)
    (hTconn : ∀ n, (G.induce (T n)).Connected)
    (hTmono : Monotone T) (hTuniv : ⋃ n, T n = Set.univ) :
    ClosedBoundaryExhaustion G H where
  region n := ClosedRegion H (T n)
  finite n := closedRegion_finite (hTfin n) hfin
  connected n := closedRegion_connected hHG (hTconn n)
  closed _ := closedRegion_closedBoundary
  monotone _ _ hnm := closedRegion_mono (hTmono hnm)
  exhaustive := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, T n := by rw [hTuniv]; exact Set.mem_univ x
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n, subset_closedRegion hxn⟩


/-- On a countable nonempty preconnected graph, every configuration with
finite open clusters admits a finite connected closed-boundary exhaustion.
This is the deterministic part of the almost-sure choice of `S_n (ω₃)` in
Theorem 5.1. -/
theorem nonempty_closedBoundaryExhaustion_of_countable
    {G H : SimpleGraph V} [Countable V] [Nonempty V]
    (hG : G.Preconnected) (hHG : H ≤ G) (hfin : FiniteOpenClusters H) :
    Nonempty (ClosedBoundaryExhaustion G H) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat V
  let v₀ : V := Classical.choice inferInstance
  obtain ⟨T, hTfin, hTconn, hTmono, hTuniv⟩ :=
    exists_finiteConnectedExhaustion hG e he v₀
  exact ⟨closedBoundaryExhaustion hHG hfin T hTfin hTconn hTmono hTuniv⟩

end FK
