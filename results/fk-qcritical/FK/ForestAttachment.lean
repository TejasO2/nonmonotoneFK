import FK.PolygonalSegment
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Attaching a straight segment without disconnecting the plane

The topological part of the argument is component-based.  A component of the
new complement with no limit point on the attached segment would be clopen in
the old complement.  Explicit detours below will show that every segment point
has a neighbourhood all of whose off-segment points join one common basepoint.
-/

namespace FK.PlaneTopology.Continuous.Forest

noncomputable section

open Set Metric Filter Topology
open scoped Classical Convex unitInterval

/-- A path in a set stays in the connected component of its starting point. -/
lemma mem_connectedComponentIn_of_joinedIn {X : Type*} [TopologicalSpace X]
    {F : Set X} {x y : X} (hxy : JoinedIn F x y) :
    y ∈ connectedComponentIn F x := by
  have hx : x ∈ F := hxy.source_mem
  have hy : y ∈ F := hxy.target_mem
  have hj : Joined (⟨x, hx⟩ : F) (⟨y, hy⟩ : F) :=
    (joinedIn_iff_joined hx hy).mp hxy
  have hc : (⟨y, hy⟩ : F) ∈ connectedComponent (⟨x, hx⟩ : F) :=
    pathComponent_subset_component _ hj
  rw [connectedComponentIn_eq_image hx]
  exact ⟨⟨y, hy⟩, hc, rfl⟩

/-- Connected components in a subspace are closed under limits which remain
in that subspace. -/
lemma closure_connectedComponentIn_inter_subset {X : Type*} [TopologicalSpace X]
    {F : Set X} {x : F} :
    closure (connectedComponentIn F x.1) ∩ F ⊆ connectedComponentIn F x.1 := by
  rintro y ⟨hycl, hyF⟩
  rw [connectedComponentIn_eq_image x.2] at hycl ⊢
  have hy : (⟨y, hyF⟩ : F) ∈ connectedComponent x := by
    have hclosed : IsClosed (connectedComponent x) := isClosed_connectedComponent
    exact (isClosed_induced_iff'.mp hclosed) (⟨y, hyF⟩ : F) hycl
  exact ⟨⟨y, hyF⟩, hy, rfl⟩

/-- A common local link across a closed obstacle prevents a preconnected open
set from acquiring another path component when the obstacle is removed. -/
theorem isPathConnected_diff_of_localLink
    {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    {U S : Set X} (hUopen : IsOpen U) (hSclosed : IsClosed S)
    (hUconn : IsPreconnected U) (hUS : (U ∩ S).Nonempty)
    {c : X} (hc : c ∈ U \ S)
    (hlink : ∀ z ∈ U ∩ S, ∃ N ∈ 𝓝 z, ∀ x ∈ N, x ∈ U \ S →
      JoinedIn (U \ S) x c) :
    IsPathConnected (U \ S) := by
  have hFopen : IsOpen (U \ S) := hUopen.sdiff hSclosed
  have hmain : ∀ x ∈ U \ S, c ∈ connectedComponentIn (U \ S) x := by
    intro x hx
    let C := connectedComponentIn (U \ S) x
    have hCsub : C ⊆ U \ S := connectedComponentIn_subset _ _
    have hCU : C ⊆ U := hCsub.trans sdiff_subset
    have hCopen : IsOpen C := hFopen.connectedComponentIn
    have hboundary : (U ∩ S ∩ closure C).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      have hclosure : U ∩ closure C ⊆ C := by
        rintro y ⟨hyU, hyC⟩
        by_cases hyS : y ∈ S
        · exact (Set.eq_empty_iff_forall_notMem.mp hempty y ⟨⟨hyU, hyS⟩, hyC⟩).elim
        · exact closure_connectedComponentIn_inter_subset
            (x := (⟨x, hx⟩ : {z // z ∈ U \ S})) ⟨hyC, hyU, hyS⟩
      let CU : Set U := Subtype.val ⁻¹' C
      have himage : Subtype.val '' CU = C := by
        change Subtype.val '' (Subtype.val ⁻¹' C : Set U) = C
        rw [Subtype.image_preimage_coe]
        exact inter_eq_right.mpr hCU
      have hclopen : IsClopen CU := by
        constructor
        · rw [isClosed_induced_iff']
          intro y hy
          apply hclosure
          refine ⟨y.2, ?_⟩
          rwa [himage] at hy
        · exact hCopen.preimage continuous_subtype_val
      letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUconn
      have hall : CU = Set.univ := hclopen.eq_univ ⟨⟨x, hCU (mem_connectedComponentIn hx)⟩,
        mem_connectedComponentIn hx⟩
      obtain ⟨z, hzU, hzS⟩ := hUS
      have hzC : z ∈ C := by
        have hzCU : (⟨z, hzU⟩ : U) ∈ CU := by rw [hall]; exact mem_univ _
        exact hzCU
      exact (hCsub hzC).2 hzS
    obtain ⟨z, ⟨hzU, hzS⟩, hzC⟩ := hboundary
    obtain ⟨N, hN, hNlink⟩ := hlink z ⟨hzU, hzS⟩
    obtain ⟨w, hwN, hwC⟩ := (mem_closure_iff_nhds.mp hzC) N hN
    rw [connectedComponentIn_eq hwC]
    exact mem_connectedComponentIn_of_joinedIn (hNlink w hwN (hCsub hwC))
  let D := connectedComponentIn (U \ S) c
  have hDF : D = U \ S := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro x hx
    have hcx : c ∈ connectedComponentIn (U \ S) x := hmain x hx
    have heq := connectedComponentIn_eq hcx
    rw [← heq]
    exact mem_connectedComponentIn hx
  rw [← hDF]
  have hDopen : IsOpen D := hFopen.connectedComponentIn
  apply hDopen.isConnected_iff_isPathConnected.mp
  exact ⟨connectedComponentIn_nonempty_iff.mpr hc,
    isPreconnected_connectedComponentIn⟩

end
end FK.PlaneTopology.Continuous.Forest
