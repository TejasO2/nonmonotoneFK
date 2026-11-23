import FK.NestedMetricRightExtension

/-!
# Exact compatibility and obstructions for right-extended metric boxes

The right-disjoint extension has the canonical nested edge labels after
reindexing. Its vertex type, however, is not the vertex type of an ordinary
larger metric box: it contains a copy of every small-box vertex in addition to
the fresh right graph's vertices. For the canonical `outsideGraph`, the latter
already contains every large-box vertex.

The demonstrated `largeSourceLaw` also has no cross-summand boundary relation.
Consequently it cannot be the pullback of any target setoid along a vertex map
which identifies a left and a right copy. Such identifications are precisely
what geometric gluing requires. These results do not assert or refute the
finite-volume arm estimate; they delimit the model to which it applies.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical BigOperators SimpleGraph Sym2

namespace FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility

open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedCoupledGood
open FK.Exploration.NestedFiniteCoupling
open FK.Finite.MarkovFactorization
open FK.InfiniteVolume.NestedFiniteAssembly
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit
open CurvatureVariance.Infra.Percolation
open FK.InfiniteVolume.NestedMetricGeometry.RegionSplit.Radial

universe u v w x

variable {E : Type u} {U : Type v} {K : Type w} {W : Type x}
variable [Fintype U] [Fintype K] {m k : ℕ}

/-- The finite large-box index obtained by composing the accepted right-block
enumeration with the canonical nested edge equivalence. -/
noncomputable def ordinaryNestedRightIndex (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) :
    Fin (nD + Fintype.card (outsideGraph BS BD).Edge) ≃ Fin nS :=
  (rightExtendedIndex (outsideGraph BS BD)).trans
    (nestedEdgeEquiv BS BD jS jD hBD)

/-- Inverting the right-block enumeration exposes exactly the canonical
nested edge equivalence. -/
lemma ordinaryNestedRightIndex_symm (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges)
    (a : Fin nD ⊕ (outsideGraph BS BD).Edge) :
    ordinaryNestedRightIndex BS BD jS jD hBD
      ((rightExtendedIndex (outsideGraph BS BD)).symm a) =
      nestedEdgeEquiv BS BD jS jD hBD a := by
  exact congrArg (nestedEdgeEquiv BS BD jS jD hBD)
    ((rightExtendedIndex (outsideGraph BS BD)).apply_symm_apply a)

/-- On a small edge, the right-extended enumeration has exactly its original
small-box global label. -/
lemma ordinaryNestedRightIndex_inl (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (a : Fin nD) :
    ((jS (ordinaryNestedRightIndex BS BD jS jD hBD
      ((rightExtendedIndex (outsideGraph BS BD)).symm (Sum.inl a))) : BS.edges) : E) =
      (jD a : BD.edges).1 := by
  rw [ordinaryNestedRightIndex_symm]
  change ((jS (jS.symm ((Equiv.Set.sumDiffSubset
    (show (BD.edges : Set E) ⊆ (BS.edges : Set E) from hBD))
    (Sum.inl (jD a)))) : BS.edges) : E) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- On an added edge, the same index returns the original global label in the
ordinary outside graph. -/
lemma ordinaryNestedRightIndex_inr (BS BD : FiniteBox E) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (hBD : BD.edges ⊆ BS.edges) (a : (outsideGraph BS BD).Edge) :
    ((jS (ordinaryNestedRightIndex BS BD jS jD hBD
      ((rightExtendedIndex (outsideGraph BS BD)).symm (Sum.inr a))) : BS.edges) : E) = a.1 := by
  rw [ordinaryNestedRightIndex_symm]
  change ((jS (jS.symm ((Equiv.Set.sumDiffSubset
    (show (BD.edges : Set E) ⊆ (BS.edges : Set E) from hBD))
    (Sum.inr a))) : BS.edges) : E) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The `largeSourceLaw` has literally no relation from the small summand to
an independently added right vertex. -/
lemma largeSourceLaw_inl_inr {D O : Finset E}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (θ : Setoid U) (ζ : Setoid K) (χ : GO.BoundaryPartition)
    (u : U ⊕ K) (v : GO.Vertex) :
    (largeSourceLaw si ti so xo GO hDO jD jO θ ζ χ).r
      (Sum.inl u) (Sum.inr v) = False := rfl

/-- The reverse cross relation is also literally false. -/
lemma largeSourceLaw_inr_inl {D O : Finset E}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (θ : Setoid U) (ζ : Setoid K) (χ : GO.BoundaryPartition)
    (u : U ⊕ K) (v : GO.Vertex) :
    (largeSourceLaw si ti so xo GO hDO jD jO θ ζ χ).r
      (Sum.inr v) (Sum.inl u) = False := rfl

/-- **Exact source-law obstruction.** If a proposed vertex map identifies a
left and a right copy, no target setoid pulls back to `largeSourceLaw` along
that map. This follows from reflexivity of the target setoid and does not
depend on edge labels or FK parameters. -/
theorem no_largeSourceLaw_comap_of_identified_left_right {D O : Finset E}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) (hDO : Disjoint (D : Set E) (O : Set E))
    (jD : Fin (k + m) ≃ D) (jO : GO.Edge ≃ O)
    (θ : Setoid U) (ζ : Setoid K) (χ : GO.BoundaryPartition)
    (g : (largeGraph si ti so xo GO).Vertex → W) (α : Setoid W)
    (u : U ⊕ K) (v : GO.Vertex)
    (hg : g (Sum.inl u) = g (Sum.inr v)) :
    ¬ (∀ a b, (largeSourceLaw si ti so xo GO hDO jD jO θ ζ χ).r a b ↔
      α.r (g a) (g b)) := by
  intro h
  have ha : α.r (g (Sum.inl u)) (g (Sum.inr v)) := by
    rw [hg]
  have hc := (h (Sum.inl u) (Sum.inr v)).2 ha
  exact hc

section Metric

universe uV

variable {V : Type uV} {Gph : SimpleGraph V}

/-- The split small metric vertices and the original small metric-box vertices
have the same finite cardinality. -/
lemma card_radial_split_vertices [Gph.LocallyFinite] (hG : Gph.Connected)
    (o : V) (R r : ℕ) :
    Fintype.card (LeftVertex (inBall hG o R r) ⊕ RightVertex (inBall hG o R r)) =
      Fintype.card (metricBox hG o r).Vertex := by
  exact Fintype.card_congr (vertexEquiv (inBall hG o R r))

/-- Every metric-box vertex type is inhabited by its centre. -/
lemma card_metricBox_vertices_pos [Gph.LocallyFinite] (hG : Gph.Connected)
    (o : V) (r : ℕ) : 0 < Fintype.card (metricBox hG o r).Vertex := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨o, (mem_innerBall hG).2 ?_⟩⟩
  simp

/-- **Ordinary metric nesting is not a right-disjoint vertex transport.** For
`GO = outsideGraph BS BD`, the right-extended vertex type has cardinality
`card BD.Vertex + card BS.Vertex`, whereas the ordinary larger box has only
`card BS.Vertex` vertices. Since the small metric box is inhabited, no vertex
equivalence exists between the two models. -/
theorem no_metric_rightExtended_vertexEquiv [Gph.LocallyFinite]
    (hG : Gph.Connected) (o : V) (R r n : ℕ) :
    ¬ Nonempty (((LeftVertex (inBall hG o R r) ⊕
        RightVertex (inBall hG o R r)) ⊕ (metricBox hG o n).Vertex) ≃
      (metricBox hG o n).Vertex) := by
  rintro ⟨e⟩
  have hc := Fintype.card_congr e
  have hs := card_radial_split_vertices hG o R r
  simp only [Fintype.card_sum] at hc hs
  have hp := card_metricBox_vertices_pos hG o r
  omega

end Metric

end FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility

#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.ordinaryNestedRightIndex_inl
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.ordinaryNestedRightIndex_inr
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.largeSourceLaw_inl_inr
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.no_largeSourceLaw_comap_of_identified_left_right
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.card_radial_split_vertices
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.card_metricBox_vertices_pos
#print axioms FK.InfiniteVolume.NestedMetricGeometry.RightExtension.Compatibility.no_metric_rightExtended_vertexEquiv
