import FK.NestedMetricRegionSplit

/-!
# A general fixed-root obstruction for the whole-ball radial split

Let `G` be a connected locally finite graph, `o` a vertex, and split the metric
box of radius `r ≥ R` at the open ball of radius `R`.  This module shows that
the bad-only attachment required by the nested arm estimate cannot hold with a
root set of bounded radius, *provided* the box has an external edge with an
endpoint in the ball and the ball contains a vertex that is not an endpoint of
that edge and lies beyond the root radius.

The single-edge configuration "only `e₀` open" is bad (an open exterior edge
touches the ball) and isolates every other vertex, so bad-only attachment
forces every such vertex to be a root.  The path instantiation is in
`FixedRootObstruction`.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal Topology unitInterval Sym2 SimpleGraph

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.General

open CurvatureVariance.Infra.Percolation
open FK.Finite FK.Finite.LabelledMultigraph
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Exploration.MaximalStrata
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.InfiniteVolume
open FK.InfiniteVolume.NestedAssembly FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The two endpoints of a metric-box edge are exactly that edge. -/
lemma metricBox_source_target_pair [G.LocallyFinite] (hG : G.Connected) (o : V) (r : ℕ)
    (e : (metricBox hG o r).edges) :
    s(((metricBox hG o r).source e).1, ((metricBox hG o r).target e).1) = e.1.1 := by
  show s(e.1.1.out.1, e.1.1.out.2) = e.1.1
  rw [Sym2.mk, e.1.1.out_eq]

/-! ## The single-edge configuration -/

/-- The configuration of a box in which only the edge `e₀` is open. -/
noncomputable def singleEdge (BS : FiniteBox G.edgeSet) {nS : ℕ}
    (jS : Fin nS ≃ BS.edges) (e₀ : BS.edges) : (BS.indexedGraph jS).Configuration :=
  fun i => decide (jS i = e₀)

lemma reindex_apply {E : Type*} (B : FiniteBox E) {n : ℕ} (j : Fin n ≃ B.edges)
    (w : (B.indexedGraph j).Configuration) (x : B.edges) :
    B.reindex j w x = w (j.symm x) := rfl

lemma glue_singleEdge (BS : FiniteBox G.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (e₀ : BS.edges) (e : G.edgeSet) :
    BS.glue (BS.closedExterior, BS.reindex jS (singleEdge BS jS e₀)) e =
      decide (e = e₀.1) := by
  rw [FiniteBox.glue]
  split_ifs with he
  · show BS.reindex jS (singleEdge BS jS e₀) ⟨e, he⟩ = decide (e = e₀.1)
    rw [reindex_apply]
    simp only [singleEdge]
    rw [Equiv.apply_symm_apply]
    simp [Subtype.ext_iff]
  · have hne : e ≠ e₀.1 := by
      intro h
      apply he
      rw [h]; exact e₀.2
    simp [FiniteBox.closedExterior, hne]

/-- In the single-edge configuration every open walk stays at one vertex or uses
the unique open edge. -/
lemma openConnected_singleEdge [G.LocallyFinite] (BS : FiniteBox G.edgeSet) {nS : ℕ}
    (jS : Fin nS ≃ BS.edges) (e₀ : BS.edges) {a b : V}
    (h : OpenConnected G
      (BS.glue (BS.closedExterior, BS.reindex jS (singleEdge BS jS e₀))) Set.univ a b) :
    a = b ∨ s(a, b) = e₀.1.1 := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | @tail x y hxy hyz ih =>
      rw [CurvatureVariance.Infra.Percolation.openGraph, SimpleGraph.fromEdgeSet_adj] at hyz
      obtain ⟨⟨e, he, hee⟩, -⟩ := hyz
      change BS.glue (BS.closedExterior,
        BS.reindex jS (singleEdge BS jS e₀)) e = true at he
      have hglue := glue_singleEdge BS jS e₀ e
      rw [hglue] at he
      have hve : e = e₀.1 := of_decide_eq_true he
      have hpair : s(x, y) = e₀.1.1 := by rw [← hee, hve]
      rcases ih with hxy_eq | hxy_eq
      · subst hxy_eq
        exact Or.inr hpair
      · have hsame : s(a, x) = s(x, y) := by rw [hxy_eq, hpair]
        rw [Sym2.eq_iff] at hsame
        rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h1.trans h2)
        · exact Or.inl h1

/-! ## Badness of the single-edge configuration -/

/-- The inclusion of the smaller edge index into the nested edge equivalence. -/
lemma nestedEdgeEquiv_inl_apply {E : Type*} (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges) (hBD : BD.edges ⊆ BS.edges)
    (i : Fin nD) :
    nestedEdgeEquiv BS BD jS jD hBD (Sum.inl i) =
      jS.symm ⟨(jD i).1, hBD (jD i).2⟩ := by
  have h : nestedEdgeEquiv BS BD jS jD hBD (Sum.inl i) =
      jS.symm ((Equiv.Set.sumDiffSubset
        (show (BD.edges : Set E) ⊆ (BS.edges : Set E) from hBD)) (Sum.inl (jD i))) := rfl
  rw [h, Equiv.Set.sumDiffSubset_apply_inl]

/-- If the open edge `e₀` is not internal to the split region, the single-edge
configuration is outside the maximal split stratum. -/
theorem singleEdge_not_mem_stratum [G.LocallyFinite] (hG : G.Connected) (o : V)
    (R r : ℕ) (BS : FiniteBox G.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (hBD : (metricBox hG o r).edges ⊆ BS.edges)
    (e₀ : (metricBox hG o r).edges)
    (hnotint : ¬ IsInternal (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)
      ((edgeIndex (metricBox hG o r)).symm e₀))
    (hleftend : inBall hG o R r
        (boxSource hG o r ((edgeIndex (metricBox hG o r)).symm e₀)) ∨
      inBall hG o R r
        (boxTarget hG o r ((edgeIndex (metricBox hG o r)).symm e₀))) :
    (restrictΔ (nestedEdgeEquiv BS (metricBox hG o r) jS (edgeIndex _) hBD)
        (singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩)) ∉ stratum hG o R r := by
  classical
  intro h
  -- the canonical index of `e₀` in the smaller box
  have hi0 : edgeIndex (metricBox hG o r) ((edgeIndex (metricBox hG o r)).symm e₀) =
      e₀ := Equiv.apply_symm_apply _ _
  set i0 : Fin (Fintype.card (metricBox hG o r).edges) :=
    (edgeIndex (metricBox hG o r)).symm e₀ with hi0def
  have hnotint' : ¬ IsInternal (boxSource hG o r) (boxTarget hG o r)
      (inBall hG o R r) i0 := hnotint
  -- the exterior label of `e₀`
  let a₀ : Fin (Fintype.card (ExternalEdge (boxSource hG o r)
      (boxTarget hG o r) (inBall hG o R r))) :=
    (externalIndex _ _ _).symm ⟨i0, hnotint'⟩
  have ha₀ : externalIndex (boxSource hG o r) (boxTarget hG o r)
      (inBall hG o R r) a₀ = ⟨i0, hnotint'⟩ := Equiv.apply_symm_apply _ _
  have hsep : Separated (si hG o R r) (ti hG o R r) (so hG o R r) (xo hG o R r)
      (exteriorConfig (restrictΔ (nestedEdgeEquiv BS (metricBox hG o r) jS
        (edgeIndex (metricBox hG o r)) hBD)
        (singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩) ∘ d hG o R r)) :=
    (mem_maximalSplitStratum_iff _ _ _ _ _
      (Radial.exteriorHasRight (G := G) hG o R r)).mp h
  have hd : d hG o R r (Sum.inr a₀) = i0 := by
    simp only [d, edgeEquiv_inr]
    exact congrArg Subtype.val ha₀
  have hcoord : exteriorConfig (restrictΔ (nestedEdgeEquiv BS (metricBox hG o r) jS
        (edgeIndex (metricBox hG o r)) hBD)
        (singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩) ∘ d hG o R r) a₀ = true := by
    change (restrictΔ (nestedEdgeEquiv BS (metricBox hG o r) jS
      (edgeIndex (metricBox hG o r)) hBD)
      (singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩)) (d hG o R r (Sum.inr a₀)) = true
    rw [hd]
    change singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩
      (nestedEdgeEquiv BS (metricBox hG o r) jS
        (edgeIndex (metricBox hG o r)) hBD (Sum.inl i0)) = true
    rw [nestedEdgeEquiv_inl_apply, hi0]
    simp [singleEdge]
  have hdisj : so hG o R r a₀ ∈
        Set.range (Sum.inl : LeftVertex (inBall hG o R r) →
          LeftVertex (inBall hG o R r) ⊕ RightVertex (inBall hG o R r)) ∨
      xo hG o R r a₀ ∈
        Set.range (Sum.inl : LeftVertex (inBall hG o R r) →
          LeftVertex (inBall hG o R r) ⊕ RightVertex (inBall hG o R r)) := by
    have hsrc : boxSource hG o r (externalIndex (boxSource hG o r)
        (boxTarget hG o r) (inBall hG o R r) a₀) = boxSource hG o r i0 := by rw [ha₀]
    have htgt : boxTarget hG o r (externalIndex (boxSource hG o r)
        (boxTarget hG o r) (inBall hG o R r) a₀) = boxTarget hG o r i0 := by rw [ha₀]
    have hso : so hG o R r a₀ = (vertexEquiv (inBall hG o R r)).symm
        (boxSource hG o r i0) := by
      simp only [so, externalSource, hsrc]
    have hxo : xo hG o R r a₀ = (vertexEquiv (inBall hG o R r)).symm
        (boxTarget hG o r i0) := by
      simp only [xo, externalTarget, htgt]
    have hleftend' : inBall hG o R r (boxSource hG o r i0) ∨
        inBall hG o R r (boxTarget hG o r i0) := hleftend
    rcases hleftend' with hL | hLt
    · left
      rw [hso, vertexEquiv, Equiv.sumCompl_symm_apply_of_pos hL]
      exact ⟨_, rfl⟩
    · right
      rw [hxo, vertexEquiv, Equiv.sumCompl_symm_apply_of_pos hLt]
      exact ⟨_, rfl⟩
  exact absurd hdisj (by
    intro hd'
    exact hd'.elim (fun hx => (hsep a₀ hcoord).1 hx) (fun hx => (hsep a₀ hcoord).2 hx))

/-! ## The general obstruction -/

/-- **General fixed-root obstruction.**  Suppose the whole-ball radial split of
`metricBox o r` at radius `R` satisfies bad-only attachment for the root set
`roots` of radius `L`.  Let `e₀` be a box edge with an endpoint in the split
region and not both endpoints in it, and let `u` be a split vertex that is
neither endpoint of `e₀` and lies at distance strictly larger than `L`.  Then
the attachment hypothesis is contradictory: the single-edge configuration of
`e₀` is bad and isolates `u`. -/
theorem not_badRootAttachment_of_leftEdge [G.LocallyFinite] (hG : G.Connected) (o : V)
    (R r : ℕ) (BS : FiniteBox G.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (hBD : (metricBox hG o r).edges ⊆ BS.edges)
    (roots : Finset V) (L : ℕ) (hA : ∀ a ∈ roots, G.dist o a ≤ L)
    (hroot : ∀ z : (BS.indexedGraph jS).Configuration,
      (restrictΔ (nestedEdgeEquiv BS (metricBox hG o r) jS (edgeIndex _) hBD) z) ∉
        stratum hG o R r →
      ∀ u : LeftVertex (inBall hG o R r),
        ∃ a ∈ roots,
          OpenConnected G
            (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
            (f hG o R r (Sum.inl u)))
    (e₀ : (metricBox hG o r).edges)
    (hnotint : ¬ IsInternal (boxSource hG o r) (boxTarget hG o r) (inBall hG o R r)
      ((edgeIndex (metricBox hG o r)).symm e₀))
    (hleftend : inBall hG o R r
        (boxSource hG o r ((edgeIndex (metricBox hG o r)).symm e₀)) ∨
      inBall hG o R r
        (boxTarget hG o r ((edgeIndex (metricBox hG o r)).symm e₀)))
    (u : LeftVertex (inBall hG o R r))
    (hu1 : f hG o R r (Sum.inl u) ≠ ((metricBox hG o r).source e₀).1)
    (hu2 : f hG o R r (Sum.inl u) ≠ ((metricBox hG o r).target e₀).1)
    (hfar : L < G.dist o (f hG o R r (Sum.inl u))) :
    False := by
  classical
  have hbad := singleEdge_not_mem_stratum hG o R r BS jS hBD e₀ hnotint hleftend
  obtain ⟨a, ha, hconn⟩ := hroot (singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩) hbad u
  have hcases := openConnected_singleEdge BS jS ⟨e₀.1, hBD e₀.2⟩ hconn
  rcases hcases with h | h
  · rw [h] at ha
    have := hA _ ha
    omega
  · have hpair := metricBox_source_target_pair hG o r e₀
    have h' : s(a, f hG o R r (Sum.inl u)) =
        s(((metricBox hG o r).source e₀).1, ((metricBox hG o r).target e₀).1) := by
      rw [hpair]; exact h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hu2 h2
    · exact hu1 h2

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.General.glue_singleEdge
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.General.openConnected_singleEdge
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.General.singleEdge_not_mem_stratum
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.General.not_badRootAttachment_of_leftEdge

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.General
