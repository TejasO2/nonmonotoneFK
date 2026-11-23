import FK.NestedRadialCounterexample

/-!
# Fixed-root bad-only attachment forces a growing root radius

On the semi-infinite path, the radial (whole-ball) split at radius `R` of
`metricBox o r` cannot be attached to a fixed finite root set on bad
configurations unless the root set reaches distance `R - 1` from the centre:
the boundary vertex `R-1` of the split is isolated by the configuration whose
only open edge is `s(R-1,R)`.  Hence the required root radius grows with the
split radius, so no fixed root set can serve the whole-ball radial split of the
paper's nested metric estimate, and the split itself (a random/explored region)
must change.

The corrected radius is exact: with the whole open ball of radius `R` as root
set the bad-only attachment holds for every configuration
(`radial_rootBall_attachment`).
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal Topology unitInterval Sym2 SimpleGraph

namespace FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction

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
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.RadialCounterexample

universe u

/-! ## The path edge `R - 1 -- R` -/

/-- The edge from `R-1` to `R` of the semi-infinite path. -/
noncomputable def pathEdge (R : ℕ) (hR : 1 ≤ R) : lineGraph.edgeSet :=
  ⟨s(R - 1, R), (lineGraph_adj (R - 1) R).2 (by omega)⟩

@[simp] lemma pathEdge_val (R : ℕ) (hR : 1 ≤ R) :
    ((pathEdge R hR : lineGraph.edgeSet) : Sym2 ℕ) = s(R - 1, R) := rfl

/-- The path edge lies in the metric box of radius `r` whenever `R ≤ r`. -/
lemma pathEdge_mem_metricBox {R r : ℕ} (hR : 1 ≤ R) (hrR : R ≤ r) :
    pathEdge R hR ∈ (metricBox lineGraph_connected 0 r).edges := by
  rw [metricBox_edges, mem_metricEdges]
  refine ⟨R - 1, ?_, ?_⟩
  · rw [pathEdge_val]; exact Sym2.mem_mk_left _ _
  · rw [lineGraph_dist_zero]; omega

/-! ## The single-edge configuration -/

/-- The configuration of a box in which only the edge `s (R-1) R` is open. -/
noncomputable def singleEdgeConfig (BS : FiniteBox lineGraph.edgeSet) {nS : ℕ}
    (jS : Fin nS ≃ BS.edges) (R : ℕ) (hR : 1 ≤ R)
    (_hmem : pathEdge R hR ∈ BS.edges) :
    (BS.indexedGraph jS).Configuration :=
  fun i => decide ((jS i).1.1 = s(R - 1, R))

lemma reindex_apply {E : Type*} (B : FiniteBox E) {n : ℕ} (j : Fin n ≃ B.edges)
    (w : (B.indexedGraph j).Configuration) (x : B.edges) :
    B.reindex j w x = w (j.symm x) := rfl

lemma glue_singleEdgeConfig (BS : FiniteBox lineGraph.edgeSet) {nS : ℕ}
    (jS : Fin nS ≃ BS.edges) (R : ℕ) (hR : 1 ≤ R) (hmem : pathEdge R hR ∈ BS.edges)
    (e : lineGraph.edgeSet) :
    BS.glue (BS.closedExterior, BS.reindex jS (singleEdgeConfig BS jS R hR hmem)) e =
      decide (e.1 = s(R - 1, R)) := by
  rw [FiniteBox.glue]
  split_ifs with he
  · show BS.reindex jS (singleEdgeConfig BS jS R hR hmem) ⟨e, he⟩ =
      decide (e.1 = s(R - 1, R))
    rw [reindex_apply]
    simp [singleEdgeConfig]
  · have hne : e.1 ≠ s(R - 1, R) := by
      intro h
      apply he
      have hpe : e = pathEdge R hR := Subtype.ext (by rw [h, pathEdge_val])
      rw [hpe]; exact hmem
    simp [FiniteBox.closedExterior, hne]

/-- Every open step of the single-edge configuration uses the edge `s (R-1) R`. -/
lemma openConnected_singleEdgeConfig (BS : FiniteBox lineGraph.edgeSet) {nS : ℕ}
    (jS : Fin nS ≃ BS.edges) (R : ℕ) (hR : 1 ≤ R) (hmem : pathEdge R hR ∈ BS.edges)
    {a b : ℕ}
    (h : OpenConnected lineGraph
      (BS.glue (BS.closedExterior,
        BS.reindex jS (singleEdgeConfig BS jS R hR hmem))) Set.univ a b) :
    a = b ∨ s(a, b) = s(R - 1, R) := by
  rw [← reachable_openGraph_openSet_iff, SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl rfl
  | @tail x y hxy hyz ih =>
      rw [CurvatureVariance.Infra.Percolation.openGraph, SimpleGraph.fromEdgeSet_adj] at hyz
      obtain ⟨⟨e, he, hee⟩, -⟩ := hyz
      change BS.glue (BS.closedExterior,
        BS.reindex jS (singleEdgeConfig BS jS R hR hmem)) e = true at he
      have hglue := glue_singleEdgeConfig BS jS R hR hmem e
      rw [hglue] at he
      have hve : e.1 = s(R - 1, R) := of_decide_eq_true he
      have hpair : s(x, y) = s(R - 1, R) := by rw [← hee, hve]
      rcases ih with hxy_eq | hxy_eq
      · subst hxy_eq
        exact Or.inr hpair
      · have hsame : s(a, x) = s(x, y) := by rw [hxy_eq, hpair]
        have hay : a = y := by
          rw [Sym2.eq_iff] at hsame
          rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · omega
          · exact h1
        exact Or.inl hay


/-! ## The two endpoints of a metric-box edge -/

section General

variable {V : Type u} {G : SimpleGraph V}

/-- The two endpoints of a metric-box edge are exactly that edge. -/
lemma metricBox_source_target_pair [G.LocallyFinite] (hG : G.Connected) (o : V) (r : ℕ)
    (e : (metricBox hG o r).edges) :
    s(((metricBox hG o r).source e).1, ((metricBox hG o r).target e).1) = e.1.1 := by
  show s(e.1.1.out.1, e.1.1.out.2) = e.1.1
  rw [Sym2.mk, e.1.1.out_eq]

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

end General

/-! ## Badness of the single-edge configuration -/

lemma singleEdgeConfig_not_mem_stratum
    (R r : ℕ) (hR : 2 ≤ R) (hrR : R ≤ r) (hR1 : 1 ≤ R)
    (BS : FiniteBox lineGraph.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (hBD : (metricBox lineGraph_connected 0 r).edges ⊆ BS.edges) :
    (restrictΔ (nestedEdgeEquiv BS (metricBox lineGraph_connected 0 r) jS
        (edgeIndex (metricBox lineGraph_connected 0 r)) hBD)
        (singleEdgeConfig BS jS R hR1
          (hBD (pathEdge_mem_metricBox hR1 hrR)))) ∉
      stratum lineGraph_connected 0 R r := by
  classical
  intro h
  have hmemD : pathEdge R hR1 ∈ (metricBox lineGraph_connected 0 r).edges :=
    pathEdge_mem_metricBox hR1 hrR
  -- the canonical index of the path edge inside the smaller box
  let i0 : Fin (Fintype.card (metricBox lineGraph_connected 0 r).edges) :=
    (edgeIndex _).symm ⟨pathEdge R hR1, hmemD⟩
  have hi0 : edgeIndex (metricBox lineGraph_connected 0 r) i0 =
      ⟨pathEdge R hR1, hmemD⟩ := Equiv.apply_symm_apply _ _
  -- the edge is external: one endpoint is the far vertex `R`
  have hnotint : ¬ IsInternal (boxSource lineGraph_connected 0 r)
      (boxTarget lineGraph_connected 0 r) (inBall lineGraph_connected 0 R r) i0 := by
    intro hint
    have hpair := metricBox_source_target_pair lineGraph_connected 0 r
      ⟨pathEdge R hR1, hmemD⟩
    -- identify source and target of the canonical index
    have hsrc : boxSource lineGraph_connected 0 r i0 =
        (metricBox lineGraph_connected 0 r).source ⟨pathEdge R hR1, hmemD⟩ := by
      simp only [boxSource, hi0]
    have htgt : boxTarget lineGraph_connected 0 r i0 =
        (metricBox lineGraph_connected 0 r).target ⟨pathEdge R hR1, hmemD⟩ := by
      simp only [boxTarget, hi0]
    rw [IsInternal] at hint
    rw [hsrc, htgt] at hint
    rw [inBall] at hint
    have hpair' : s(((metricBox lineGraph_connected 0 r).source
          ⟨pathEdge R hR1, hmemD⟩).1,
        ((metricBox lineGraph_connected 0 r).target ⟨pathEdge R hR1, hmemD⟩).1) =
        s(R - 1, R) := by
      rw [hpair, pathEdge_val]
    rw [Sym2.eq_iff] at hpair'
    simp only [inBall] at hint
    rw [lineGraph_dist_zero, lineGraph_dist_zero] at hint
    rcases hpair' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  -- the exterior label of the path edge
  let a₀ : Fin (Fintype.card (ExternalEdge (boxSource lineGraph_connected 0 r)
      (boxTarget lineGraph_connected 0 r) (inBall lineGraph_connected 0 R r))) :=
    (externalIndex _ _ _).symm ⟨i0, hnotint⟩
  have ha₀ : externalIndex (boxSource lineGraph_connected 0 r)
      (boxTarget lineGraph_connected 0 r) (inBall lineGraph_connected 0 R r) a₀ =
        ⟨i0, hnotint⟩ := Equiv.apply_symm_apply _ _
  -- separation says no open exterior edge touches the interior vertex region
  have hsep : Separated (si lineGraph_connected 0 R r) (ti lineGraph_connected 0 R r)
      (so lineGraph_connected 0 R r) (xo lineGraph_connected 0 R r)
      (exteriorConfig (restrictΔ (nestedEdgeEquiv BS
        (metricBox lineGraph_connected 0 r) jS
        (edgeIndex (metricBox lineGraph_connected 0 r)) hBD)
        (singleEdgeConfig BS jS R hR1 (hBD (pathEdge_mem_metricBox hR1 hrR))) ∘
        d lineGraph_connected 0 R r)) := by
    exact (mem_maximalSplitStratum_iff _ _ _ _ _
      (Radial.exteriorHasRight (G := lineGraph) lineGraph_connected 0 R r)).mp h
  -- the exterior coordinate of the path edge is open
  have hd : d lineGraph_connected 0 R r (Sum.inr a₀) = i0 := by
    simp only [d, edgeEquiv_inr]
    exact congrArg Subtype.val ha₀
  have hcoord : exteriorConfig (restrictΔ (nestedEdgeEquiv BS
        (metricBox lineGraph_connected 0 r) jS
        (edgeIndex (metricBox lineGraph_connected 0 r)) hBD)
        (singleEdgeConfig BS jS R hR1 (hBD (pathEdge_mem_metricBox hR1 hrR))) ∘
        d lineGraph_connected 0 R r) a₀ = true := by
    change (restrictΔ (nestedEdgeEquiv BS (metricBox lineGraph_connected 0 r) jS
        (edgeIndex (metricBox lineGraph_connected 0 r)) hBD)
        (singleEdgeConfig BS jS R hR1 (hBD (pathEdge_mem_metricBox hR1 hrR))))
        (d lineGraph_connected 0 R r (Sum.inr a₀)) = true
    rw [hd]
    change singleEdgeConfig BS jS R hR1 (hBD (pathEdge_mem_metricBox hR1 hrR))
      (nestedEdgeEquiv BS (metricBox lineGraph_connected 0 r) jS
        (edgeIndex (metricBox lineGraph_connected 0 r)) hBD (Sum.inl i0)) = true
    rw [nestedEdgeEquiv_inl_apply, hi0]
    simp [singleEdgeConfig]
  -- one endpoint of the open path edge is an interior (left) vertex
  have hdisj : so lineGraph_connected 0 R r a₀ ∈
        Set.range (Sum.inl : LeftVertex (inBall lineGraph_connected 0 R r) →
          LeftVertex (inBall lineGraph_connected 0 R r) ⊕
            RightVertex (inBall lineGraph_connected 0 R r)) ∨
      xo lineGraph_connected 0 R r a₀ ∈
        Set.range (Sum.inl : LeftVertex (inBall lineGraph_connected 0 R r) →
          LeftVertex (inBall lineGraph_connected 0 R r) ⊕
            RightVertex (inBall lineGraph_connected 0 R r)) := by
    have hsrc : boxSource lineGraph_connected 0 r
        (externalIndex (boxSource lineGraph_connected 0 r)
          (boxTarget lineGraph_connected 0 r) (inBall lineGraph_connected 0 R r) a₀) =
        boxSource lineGraph_connected 0 r i0 := by
      rw [ha₀]
    have htgt : boxTarget lineGraph_connected 0 r
        (externalIndex (boxSource lineGraph_connected 0 r)
          (boxTarget lineGraph_connected 0 r) (inBall lineGraph_connected 0 R r) a₀) =
        boxTarget lineGraph_connected 0 r i0 := by
      rw [ha₀]
    have hso : so lineGraph_connected 0 R r a₀ =
        (vertexEquiv (inBall lineGraph_connected 0 R r)).symm
          (boxSource lineGraph_connected 0 r i0) := by
      simp only [so, externalSource, hsrc]
    have hxo : xo lineGraph_connected 0 R r a₀ =
        (vertexEquiv (inBall lineGraph_connected 0 R r)).symm
          (boxTarget lineGraph_connected 0 r i0) := by
      simp only [xo, externalTarget, htgt]
    by_cases hL : inBall lineGraph_connected 0 R r (boxSource lineGraph_connected 0 r i0)
    · left
      rw [hso, vertexEquiv, Equiv.sumCompl_symm_apply_of_pos hL]
      exact ⟨_, rfl⟩
    · right
      have hLt : inBall lineGraph_connected 0 R r (boxTarget lineGraph_connected 0 r i0) := by
        have hpair := metricBox_source_target_pair lineGraph_connected 0 r
          ⟨pathEdge R hR1, hmemD⟩
        have hsrc' : boxSource lineGraph_connected 0 r i0 =
            (metricBox lineGraph_connected 0 r).source ⟨pathEdge R hR1, hmemD⟩ := by
          simp only [boxSource, hi0]
        have htgt' : boxTarget lineGraph_connected 0 r i0 =
            (metricBox lineGraph_connected 0 r).target ⟨pathEdge R hR1, hmemD⟩ := by
          simp only [boxTarget, hi0]
        have hpair' : s(((metricBox lineGraph_connected 0 r).source
              ⟨pathEdge R hR1, hmemD⟩).1,
            ((metricBox lineGraph_connected 0 r).target
              ⟨pathEdge R hR1, hmemD⟩).1) = s(R - 1, R) := by
          rw [hpair, pathEdge_val]
        simp only [inBall] at hL
        rw [hsrc'] at hL
        simp only [inBall]
        rw [htgt']
        rw [Sym2.eq_iff] at hpair'
        rw [lineGraph_dist_zero] at hL ⊢
        rcases hpair' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      rw [hxo, vertexEquiv, Equiv.sumCompl_symm_apply_of_pos hLt]
      exact ⟨_, rfl⟩
  exact absurd hdisj (by
    intro hd'
    exact hd'.elim (fun hx => (hsep a₀ hcoord).1 hx) (fun hx => (hsep a₀ hcoord).2 hx))

/-! ## The obstruction -/

/-- **Fixed-root obstruction on the path.**  Let `R ≤ r`, `R ≥ 2`.  Suppose the
whole-ball radial split of `metricBox o r` at radius `R` satisfies the bad-only
attachment required by the nested arm estimate for some ambient box `BS`, some
edge index `jS`, and some root set `roots`.  Then the boundary vertex `R - 1` of
the split is itself openly attached only to `R - 1` or `R`, so some root lies at
distance at least `R - 1` from the centre: the root radius `L` satisfies
`R ≤ L + 1`.  In particular the root set must grow with the split radius. -/
theorem lineGraph_radial_badRootAttachment_forces
    (R r : ℕ) (hR : 2 ≤ R) (hrR : R ≤ r)
    (BS : FiniteBox lineGraph.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (hBD : (metricBox lineGraph_connected 0 r).edges ⊆ BS.edges)
    (roots : Finset ℕ) (L : ℕ)
    (hA : ∀ a ∈ roots, lineGraph.dist 0 a ≤ L)
    (hroot : ∀ z : (BS.indexedGraph jS).Configuration,
      (restrictΔ (nestedEdgeEquiv BS (metricBox lineGraph_connected 0 r) jS
          (edgeIndex _) hBD) z) ∉ stratum lineGraph_connected 0 R r →
      ∀ u : LeftVertex (inBall lineGraph_connected 0 R r),
        ∃ a ∈ roots,
          OpenConnected lineGraph
            (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
            (f lineGraph_connected 0 R r (Sum.inl u))) :
    R ≤ L + 1 := by
  classical
  have hR1 : 1 ≤ R := by omega
  have hmem : pathEdge R hR1 ∈ BS.edges := hBD (pathEdge_mem_metricBox hR1 hrR)
  have hbad := singleEdgeConfig_not_mem_stratum R r hR hrR hR1 BS jS hBD
  let u : LeftVertex (inBall lineGraph_connected 0 R r) :=
    ⟨⟨R - 1, by rw [mem_innerBall, lineGraph_dist_zero]; omega⟩, by
      simp only [inBall]; rw [lineGraph_dist_zero]; omega⟩
  obtain ⟨a, ha, hconn⟩ := hroot (singleEdgeConfig BS jS R hR1 hmem) hbad u
  have hf : f lineGraph_connected 0 R r (Sum.inl u) = R - 1 := rfl
  rw [hf] at hconn
  have hcases : a = R - 1 ∨ a = R := by
    rcases openConnected_singleEdgeConfig BS jS R hR1 hmem hconn with h | h
    · exact Or.inl h
    · right
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · omega
      · exact h1
  have hdist := hA a ha
  rw [lineGraph_dist_zero] at hdist
  rcases hcases with h | h <;> omega

/-- **The corrected root radius.**  With the whole open ball of radius `R` as
the root set, bad-only attachment is immediate: every left vertex of the radial
split is itself a root.  Together with
`lineGraph_radial_badRootAttachment_forces` this pins the minimal fixed-root
radius of the whole-ball radial split at the split radius itself. -/
theorem radial_rootBall_attachment
    (R r : ℕ) (BS : FiniteBox lineGraph.edgeSet) {nS : ℕ} (jS : Fin nS ≃ BS.edges)
    (z : (BS.indexedGraph jS).Configuration) :
    ∀ u : LeftVertex (inBall lineGraph_connected 0 R r),
      ∃ a ∈ innerBall lineGraph_connected 0 R,
        OpenConnected lineGraph
          (BS.glue (BS.closedExterior, BS.reindex jS z)) Set.univ a
          (f lineGraph_connected 0 R r (Sum.inl u)) := by
  intro u
  exact ⟨_, Radial.hleft lineGraph_connected 0 R r u, OpenConnected.refl _ _ _⟩

/-- **No fixed root radius serves every scale.**  For every finite root set
`roots` with root radius `L`, there is a split radius `R` at which the bad-only
attachment of the whole-ball radial split fails for the box of radius `R`. -/
theorem exists_scale_not_badRootAttachment (roots : Finset ℕ) (L : ℕ)
    (hA : ∀ a ∈ roots, lineGraph.dist 0 a ≤ L) :
    ∃ R : ℕ, 2 ≤ R ∧
      ¬ (∀ z : ((metricBox lineGraph_connected 0 R).indexedGraph
            (edgeIndex _)).Configuration,
          (restrictΔ (nestedEdgeEquiv (metricBox lineGraph_connected 0 R)
              (metricBox lineGraph_connected 0 R) (edgeIndex _) (edgeIndex _)
              (by simp)) z) ∉ stratum lineGraph_connected 0 R R →
          ∀ u : LeftVertex (inBall lineGraph_connected 0 R R),
            ∃ a ∈ roots,
              OpenConnected lineGraph
                ((metricBox lineGraph_connected 0 R).glue
                  ((metricBox lineGraph_connected 0 R).closedExterior,
                   (metricBox lineGraph_connected 0 R).reindex (edgeIndex _) z))
                Set.univ a (f lineGraph_connected 0 R R (Sum.inl u))) := by
  refine ⟨L + 2, by omega, ?_⟩
  intro h
  have hforce := lineGraph_radial_badRootAttachment_forces (L + 2) (L + 2)
    (by omega) le_rfl (metricBox lineGraph_connected 0 (L + 2)) (edgeIndex _)
    (by simp) roots L hA h
  omega

/-- **The exact hypothesis shape of the nested arm-vanishing theorem cannot hold
on the path at a fixed root radius.**  This is
`lineGraph_radial_badRootAttachment_forces` written directly in the
`metricNestedEquiv`/`maximalSplitStratum` form used by
`NestedBadRootArmVanishing.metricBox_cylinder_abs_sub_tendsto_zero_of_good_of_bad`:
the smaller metric box has radius `R`, the larger one radius `N`, and the
attachment is required only off the maximal split stratum. -/
theorem lineGraph_metricNested_hroot_forces
    (R N : ℕ) (hR : 2 ≤ R) (hRN : R ≤ N)
    (roots : Finset ℕ) (L : ℕ) (hA : ∀ a ∈ roots, lineGraph.dist 0 a ≤ L)
    (hroot : ∀ z : ((metricBox lineGraph_connected 0 N).indexedGraph
          (edgeIndex _)).Configuration,
      (restrictΔ (metricNestedEquiv lineGraph_connected 0 hRN) z ∘
          d lineGraph_connected 0 R R) ∉
        maximalSplitStratum (si lineGraph_connected 0 R R)
          (ti lineGraph_connected 0 R R) (so lineGraph_connected 0 R R)
          (xo lineGraph_connected 0 R R) →
      ∀ u : LeftVertex (inBall lineGraph_connected 0 R R),
        ∃ a ∈ roots,
          OpenConnected lineGraph
            ((metricBox lineGraph_connected 0 N).glue
              ((metricBox lineGraph_connected 0 N).closedExterior,
               (metricBox lineGraph_connected 0 N).reindex (edgeIndex _) z))
            Set.univ a (f lineGraph_connected 0 R R (Sum.inl u))) :
    R ≤ L + 1 :=
  lineGraph_radial_badRootAttachment_forces R R hR le_rfl
    (metricBox lineGraph_connected 0 N) (edgeIndex _)
    (nested_metricBox_edges lineGraph_connected 0 hRN) roots L hA hroot

end FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.glue_singleEdgeConfig
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.openConnected_singleEdgeConfig
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.singleEdgeConfig_not_mem_stratum
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.lineGraph_radial_badRootAttachment_forces
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.radial_rootBall_attachment
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.exists_scale_not_badRootAttachment
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.FixedRootObstruction.lineGraph_metricNested_hroot_forces
