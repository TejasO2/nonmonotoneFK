import FK.NestedAdaptiveMarginals
import FK.MarkovFactorization
import FK.NestedFiniteCoupling

/-!
# Induced small regions in a nested adaptive window
-/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.RegionSeal

structure NestedSumGeometry (V : Type*) [Fintype V]
    (D O : LabelledMultigraph) where
  source : D.Edge ⊕ O.Edge → V
  target : D.Edge ⊕ O.Edge → V
  vertex : D.Vertex → V
  vertex_injective : Function.Injective vertex
  source_inl : ∀ d, source (Sum.inl d) = vertex (D.source d)
  target_inl : ∀ d, target (Sum.inl d) = vertex (D.target d)
  core : Set D.Vertex
  not_core_of_source_inr : ∀ o d, vertex d = source (Sum.inr o) → d ∉ core
  not_core_of_target_inr : ∀ o d, vertex d = target (Sum.inr o) → d ∉ core

namespace NestedSumGeometry

variable {V : Type*} [Fintype V] {D O : LabelledMultigraph}
  (X : NestedSumGeometry V D O)

def graph : LabelledMultigraph where
  Vertex := V
  Edge := D.Edge ⊕ O.Edge
  source := X.source
  target := X.target

def smallInterior (U : Set V) : Set D.Vertex := X.vertex ⁻¹' U

/-- Inclusion of small region vertices in the large region. -/
def smallVertex (U : Set V) [DecidablePred (· ∈ U)] :
    ↥(smallInterior X U) → U :=
  fun d => ⟨X.vertex d.1, d.2⟩

lemma smallVertex_injective (U : Set V) [DecidablePred (· ∈ U)] :
    Function.Injective (smallVertex X U) := by
  intro x y h
  apply Subtype.ext
  apply X.vertex_injective
  exact congrArg Subtype.val h

def smallVertices (U : Set V) [DecidablePred (· ∈ U)] : Set U :=
  Set.range (smallVertex X U)

lemma isInternal_inl_iff (U : Set V) (d : D.Edge) :
    IsInternal X.graph U (Sum.inl d) ↔ IsInternal D (smallInterior X U) d := by
  change (X.source (Sum.inl d) ∈ U ∧ X.target (Sum.inl d) ∈ U) ↔ _
  rw [X.source_inl, X.target_inl]
  rfl

def smallEdge (U : Set V) [DecidablePred (· ∈ U)] :
    RegionSeal.Internal D (smallInterior X U) → RegionSeal.Internal X.graph U :=
  fun d => ⟨Sum.inl d.1, (X.isInternal_inl_iff U d.1).2 d.2⟩

lemma smallEdge_injective (U : Set V) [DecidablePred (· ∈ U)] :
    Function.Injective (smallEdge X U) := by
  intro x y h
  apply Subtype.ext
  exact Sum.inl.inj (congrArg Subtype.val h)

/-- No open edge of the large free region leaves the embedded small interior. -/
lemma mem_smallVertices_of_adj (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    (ω : RegionSeal.Internal X.graph U → Bool)
    {x y : U}
    (hxy : (regionGraph X.graph U).connectionGraph
      (regionGraph X.graph U).freeBoundary ω |>.Adj x y) :
    (x ∈ smallVertices X U ↔ y ∈ smallVertices X U) := by
  suffices key : ∀ a b : U,
      (regionGraph X.graph U).connectionGraph
        (regionGraph X.graph U).freeBoundary ω |>.Adj a b →
      a ∈ smallVertices X U → b ∈ smallVertices X U by
    exact ⟨key x y hxy, key y x hxy.symm⟩
  intro a b hab ha
  obtain ⟨d, rfl⟩ := ha
  obtain ⟨hne, hwire | ⟨e, he, hjoin⟩⟩ := hab
  · exact (hne hwire).elim
  have hjoin0 := (RegionSeal.regionGraph_joins X.graph U e
    (smallVertex X U d) b).mp hjoin
  change X.graph.Joins e.1 (X.vertex d.1) b.1 at hjoin0
  cases hd : e.1 with
  | inl d' =>
    have hi : IsInternal X.graph U (Sum.inl d') := by rw [← hd]; exact e.2
    rw [hd] at hjoin0
    have hiD : IsInternal D (smallInterior X U) d' :=
      (X.isInternal_inl_iff U d').1 hi
    rcases hjoin0 with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨⟨D.target d', hiD.2⟩, by
        apply Subtype.ext
        simpa only [graph, smallVertex, X.target_inl] using ht⟩
    · exact ⟨⟨D.source d', hiD.1⟩, by
        apply Subtype.ext
        simpa only [graph, smallVertex, X.source_inl] using hs⟩
  | inr o =>
    exfalso
    have hdcore : d.1 ∈ X.core := hcore d.1 d.2
    rw [hd] at hjoin0
    rcases hjoin0 with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact X.not_core_of_source_inr o d.1 (by simpa only [graph] using hs.symm) hdcore
    · exact X.not_core_of_target_inr o d.1 (by simpa only [graph] using ht.symm) hdcore

/-- The small free connection graph is the induced large free connection
graph on the embedded small vertices. -/
noncomputable def smallGraphIso (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    (ω : RegionSeal.Internal X.graph U → Bool) :
    (regionGraph D (smallInterior X U)).connectionGraph
      (regionGraph D (smallInterior X U)).freeBoundary
        (fun d => ω (smallEdge X U d)) ≃g
    (((regionGraph X.graph U).connectionGraph
      (regionGraph X.graph U).freeBoundary ω).induce (smallVertices X U)) where
  toEquiv := Equiv.ofInjective (smallVertex X U) (smallVertex_injective X U)
  map_rel_iff' := by
    intro x y
    constructor
    · intro hxy
      change (regionGraph X.graph U).connectionGraph
        (regionGraph X.graph U).freeBoundary ω |>.Adj
          (smallVertex X U x) (smallVertex X U y) at hxy
      obtain ⟨hne, hwire | ⟨e, he, hjoin⟩⟩ := hxy
      · exact (hne hwire).elim
      have hjoin0 := (RegionSeal.regionGraph_joins X.graph U e
        (smallVertex X U x) (smallVertex X U y)).mp hjoin
      change X.graph.Joins e.1 (X.vertex x.1) (X.vertex y.1) at hjoin0
      cases hd : e.1 with
      | inl d =>
        have hi : IsInternal X.graph U (Sum.inl d) := by rw [← hd]; exact e.2
        rw [hd] at hjoin0
        have hiD : IsInternal D (smallInterior X U) d :=
          (X.isInternal_inl_iff U d).1 hi
        have hedge : smallEdge X U ⟨d, hiD⟩ = e := Subtype.ext hd.symm
        have he' : (fun d => ω (smallEdge X U d)) ⟨d, hiD⟩ = true := by
          change ω (smallEdge X U ⟨d, hiD⟩) = true
          rw [hedge]
          exact he
        refine ⟨?_, Or.inr ⟨⟨d, hiD⟩, he', ?_⟩⟩
        · intro h
          exact hne (congrArg (smallVertex X U) h)
        · apply (RegionSeal.regionGraph_joins D (smallInterior X U)
            ⟨d, hiD⟩ x y).mpr
          rcases hjoin0 with ⟨hs, ht⟩ | ⟨hs, ht⟩
          · exact Or.inl ⟨X.vertex_injective (by
              simpa only [graph, X.source_inl] using hs), X.vertex_injective (by
              simpa only [graph, X.target_inl] using ht)⟩
          · exact Or.inr ⟨X.vertex_injective (by
              simpa only [graph, X.source_inl] using hs), X.vertex_injective (by
              simpa only [graph, X.target_inl] using ht)⟩
      | inr o =>
        exfalso
        have hxcore : x.1 ∈ X.core := hcore x.1 x.2
        rw [hd] at hjoin0
        rcases hjoin0 with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact X.not_core_of_source_inr o x.1 (by simpa only [graph] using hs.symm) hxcore
        · exact X.not_core_of_target_inr o x.1 (by simpa only [graph] using ht.symm) hxcore
    · intro hxy
      obtain ⟨hne, hwire | ⟨d, he, hjoin⟩⟩ := hxy
      · exact (hne hwire).elim
      change (regionGraph X.graph U).connectionGraph
        (regionGraph X.graph U).freeBoundary ω |>.Adj
          (smallVertex X U x) (smallVertex X U y)
      refine ⟨?_, Or.inr ⟨smallEdge X U d, he, ?_⟩⟩
      · intro h
        apply hne
        apply smallVertex_injective X U
        exact h
      · apply (RegionSeal.regionGraph_joins X.graph U (smallEdge X U d)
          (smallVertex X U x) (smallVertex X U y)).mpr
        have hjoin0 := (RegionSeal.regionGraph_joins D (smallInterior X U) d x y).mp hjoin
        change X.graph.Joins (Sum.inl d.1) (X.vertex x.1) (X.vertex y.1)
        unfold LabelledMultigraph.Joins
        rcases hjoin0 with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · exact Or.inl ⟨(X.source_inl _).trans (congrArg X.vertex hs),
          (X.target_inl _).trans (congrArg X.vertex ht)⟩
        · exact Or.inr ⟨(X.source_inl _).trans (congrArg X.vertex hs),
          (X.target_inl _).trans (congrArg X.vertex ht)⟩


/-- Residual internal edge labels. -/
abbrev ResidualEdge (U : Set V) [DecidablePred (· ∈ U)] :=
  {e : RegionSeal.Internal X.graph U // e ∉ Set.range (smallEdge X U)}

def smallReadout (U : Set V) [DecidablePred (· ∈ U)]
    (ω : RegionSeal.Internal X.graph U → Bool) :
    RegionSeal.Internal D (smallInterior X U) → Bool :=
  fun d => ω (smallEdge X U d)

def residualReadout (U : Set V) [DecidablePred (· ∈ U)]
    (ω : RegionSeal.Internal X.graph U → Bool) : ResidualEdge X U → Bool :=
  fun e => ω e.1

/-- The residual graph uses precisely the residual bits. -/
def residualGraph (U : Set V) [DecidablePred (· ∈ U)]
    (ρ : ResidualEdge X U → Bool) : SimpleGraph ↥(smallVertices X U)ᶜ where
  Adj x y := x ≠ y ∧ ∃ e : ResidualEdge X U,
    ρ e = true ∧ X.graph.Joins e.1.1 x.1.1 y.1.1
  symm := ⟨by
    rintro x y ⟨hne, e, he, hj⟩
    exact ⟨hne.symm, e, he, hj.symm⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

lemma source_smallEdge_mem (U : Set V) [DecidablePred (· ∈ U)]
    (d : RegionSeal.Internal D (smallInterior X U)) :
    (regionGraph X.graph U).source (smallEdge X U d) ∈ smallVertices X U := by
  refine ⟨⟨D.source d.1, d.2.1⟩, ?_⟩
  apply Subtype.ext
  exact (X.source_inl d.1).symm

lemma target_smallEdge_mem (U : Set V) [DecidablePred (· ∈ U)]
    (d : RegionSeal.Internal D (smallInterior X U)) :
    (regionGraph X.graph U).target (smallEdge X U d) ∈ smallVertices X U := by
  refine ⟨⟨D.target d.1, d.2.2⟩, ?_⟩
  apply Subtype.ext
  exact (X.target_inl d.1).symm

lemma residualGraph_eq_induce (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    (ω : RegionSeal.Internal X.graph U → Bool) :
    residualGraph X U (residualReadout X U ω) =
      (((regionGraph X.graph U).connectionGraph
        (regionGraph X.graph U).freeBoundary ω).induce (smallVertices X U)ᶜ) := by
  ext x y
  constructor
  · rintro ⟨hne, e, he, hj⟩
    refine ⟨?_, Or.inr ⟨e.1, he, ?_⟩⟩
    · intro h
      exact hne (Subtype.ext h)
    · exact (RegionSeal.regionGraph_joins X.graph U e.1 x.1 y.1).mpr hj
  · intro hxy
    change (regionGraph X.graph U).connectionGraph
      (regionGraph X.graph U).freeBoundary ω |>.Adj x.1 y.1 at hxy
    obtain ⟨hne, hwire | ⟨e, he, hj⟩⟩ := hxy
    · exact (hne hwire).elim
    have hj0 := (RegionSeal.regionGraph_joins X.graph U e x.1 y.1).mp hj
    have her : e ∉ Set.range (smallEdge X U) := by
      intro hr
      obtain ⟨d, rfl⟩ := hr
      rcases hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact x.2 (by rw [← hs]; exact X.source_smallEdge_mem U d)
      · exact x.2 (by rw [← ht]; exact X.target_smallEdge_mem U d)
    exact ⟨fun h => hne (congrArg Subtype.val h), ⟨⟨e, her⟩, he, hj0⟩⟩

lemma componentCount_split (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    (ω : RegionSeal.Internal X.graph U → Bool) :
    (regionGraph X.graph U).componentCount
      (regionGraph X.graph U).freeBoundary ω =
    (regionGraph D (smallInterior X U)).componentCount
      (regionGraph D (smallInterior X U)).freeBoundary (smallReadout X U ω) +
    Nat.card (residualGraph X U (residualReadout X U ω)).ConnectedComponent := by
  let H := (regionGraph X.graph U).connectionGraph
    (regionGraph X.graph U).freeBoundary ω
  have hcross : ∀ x y : U, H.Adj x y →
      (x ∈ smallVertices X U ↔ y ∈ smallVertices X U) := by
    intro x y hxy
    exact X.mem_smallVertices_of_adj U hcore ω hxy
  have hsplit := RegionSeal.SimpleGraph.natCard_connectedComponent_induce_split
    (H := H) (U := smallVertices X U) hcross
  have hiso : Nat.card (H.induce (smallVertices X U)).ConnectedComponent =
      Nat.card ((regionGraph D (smallInterior X U)).connectionGraph
        (regionGraph D (smallInterior X U)).freeBoundary
          (smallReadout X U ω)).ConnectedComponent :=
    (Nat.card_congr (X.smallGraphIso U hcore ω).connectedComponentEquiv).symm
  have hrest : Nat.card (H.induce (smallVertices X U)ᶜ).ConnectedComponent =
      Nat.card (residualGraph X U (residualReadout X U ω)).ConnectedComponent :=
    congrArg (fun K : SimpleGraph ↥(smallVertices X U)ᶜ =>
      Nat.card K.ConnectedComponent) (X.residualGraph_eq_induce U hcore ω).symm
  change Nat.card H.ConnectedComponent = _
  rw [hsplit]
  convert congrArg₂ (fun a b : ℕ => a + b) hiso hrest using 1 <;> rfl


noncomputable def residualWeight (U : Set V) [DecidablePred (· ∈ U)]
    (q p : NNReal) (ρ : ResidualEdge X U → Bool) : NNReal :=
  (∏ e, if ρ e then p else 1 - p) *
    q ^ Nat.card (residualGraph X U ρ).ConnectedComponent

noncomputable def residualPartition (U : Set V) [DecidablePred (· ∈ U)]
    (q p : NNReal) : NNReal := ∑ ρ, residualWeight X U q p ρ

noncomputable def edgeDecomposition (U : Set V) [DecidablePred (· ∈ U)] :
    RegionSeal.Internal D (smallInterior X U) ⊕ ResidualEdge X U ≃
      RegionSeal.Internal X.graph U :=
  (Equiv.sumCongr (Equiv.ofInjective (smallEdge X U) (smallEdge_injective X U))
    (Equiv.refl _)).trans (Equiv.sumCompl (fun e => e ∈ Set.range (smallEdge X U)))

@[simp] lemma edgeDecomposition_inl (U : Set V) [DecidablePred (· ∈ U)]
    (d : RegionSeal.Internal D (smallInterior X U)) :
    edgeDecomposition X U (Sum.inl d) = smallEdge X U d := by
  show (Equiv.sumCompl (fun e => e ∈ Set.range (smallEdge X U)))
    (Sum.inl ((Equiv.ofInjective (smallEdge X U) (smallEdge_injective X U)) d)) = _
  rw [Equiv.sumCompl_apply_inl, Equiv.ofInjective_apply]

@[simp] lemma edgeDecomposition_inr (U : Set V) [DecidablePred (· ∈ U)]
    (e : ResidualEdge X U) : edgeDecomposition X U (Sum.inr e) = e.1 := by
  show (Equiv.sumCompl (fun e => e ∈ Set.range (smallEdge X U))) (Sum.inr e) = _
  rw [Equiv.sumCompl_apply_inr]

noncomputable def configDecomposition (U : Set V) [DecidablePred (· ∈ U)] :
    (RegionSeal.Internal X.graph U → Bool) ≃
      (RegionSeal.Internal D (smallInterior X U) → Bool) ×
        (ResidualEdge X U → Bool) :=
  (Equiv.arrowCongr (edgeDecomposition X U).symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ Bool)

@[simp] lemma configDecomposition_fst (U : Set V) [DecidablePred (· ∈ U)]
    (ω : RegionSeal.Internal X.graph U → Bool) :
    (configDecomposition X U ω).1 = smallReadout X U ω := by
  funext d
  change ω (edgeDecomposition X U (Sum.inl d)) = _
  rw [edgeDecomposition_inl]
  rfl

@[simp] lemma configDecomposition_snd (U : Set V) [DecidablePred (· ∈ U)]
    (ω : RegionSeal.Internal X.graph U → Bool) :
    (configDecomposition X U ω).2 = residualReadout X U ω := by
  funext e
  change ω (edgeDecomposition X U (Sum.inr e)) = _
  rw [edgeDecomposition_inr]
  rfl

lemma edgeWeight_split (U : Set V) [DecidablePred (· ∈ U)]
    (p : NNReal) (ω : RegionSeal.Internal X.graph U → Bool) :
    (regionGraph X.graph U).edgeWeight p ω =
      (regionGraph D (smallInterior X U)).edgeWeight p (smallReadout X U ω) *
        ∏ e : ResidualEdge X U, if residualReadout X U ω e then p else 1 - p := by
  change (∏ e, if ω e then p else 1 - p) =
    (∏ d, if ω (smallEdge X U d) then p else 1 - p) *
      ∏ e : ResidualEdge X U, if ω e.1 then p else 1 - p
  have h := (edgeDecomposition X U).prod_comp (fun e => if ω e then p else 1 - p)
  rw [← h, Fintype.prod_sum_type]
  simp only [edgeDecomposition_inl, edgeDecomposition_inr]

lemma fkWeight_split (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    (q p : NNReal) (ω : RegionSeal.Internal X.graph U → Bool) :
    (regionGraph X.graph U).fkWeight q p (regionGraph X.graph U).freeBoundary ω =
      (regionGraph D (smallInterior X U)).fkWeight q p
        (regionGraph D (smallInterior X U)).freeBoundary (smallReadout X U ω) *
      residualWeight X U q p (residualReadout X U ω) := by
  unfold LabelledMultigraph.fkWeight residualWeight
  rw [X.edgeWeight_split U p ω, X.componentCount_split U hcore ω, pow_add]
  ac_rfl

lemma residualWeight_pos (U : Set V) [DecidablePred (· ∈ U)]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ : ResidualEdge X U → Bool) : 0 < residualWeight X U q p ρ := by
  unfold residualWeight
  apply mul_pos
  · apply Finset.prod_pos
    intro e he
    split_ifs
    · exact hp₀
    · exact tsub_pos_of_lt hp₁
  · exact pow_pos hq _

lemma residualPartition_pos (U : Set V) [DecidablePred (· ∈ U)]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < residualPartition X U q p := by
  apply lt_of_lt_of_le (X.residualWeight_pos U hq hp₀ hp₁ (fun _ => false))
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)

lemma partitionFunction_split (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core) (q p : NNReal) :
    (regionGraph X.graph U).partitionFunction q p (regionGraph X.graph U).freeBoundary =
      (regionGraph D (smallInterior X U)).partitionFunction q p
        (regionGraph D (smallInterior X U)).freeBoundary * residualPartition X U q p := by
  letI : Fintype (RegionSeal.Internal X.graph U → Bool) :=
    (regionGraph X.graph U).instFintypeConfiguration
  letI : Fintype (RegionSeal.Internal D (smallInterior X U) → Bool) :=
    (regionGraph D (smallInterior X U)).instFintypeConfiguration
  unfold LabelledMultigraph.partitionFunction residualPartition
  calc
    (∑ ω, (regionGraph X.graph U).fkWeight q p
      (regionGraph X.graph U).freeBoundary ω) =
      ∑ z : (RegionSeal.Internal D (smallInterior X U) → Bool) ×
        (ResidualEdge X U → Bool),
        (regionGraph D (smallInterior X U)).fkWeight q p
          (regionGraph D (smallInterior X U)).freeBoundary z.1 *
          residualWeight X U q p z.2 := by
      apply Fintype.sum_equiv (configDecomposition X U)
      intro ω
      have h := X.fkWeight_split U hcore q p ω
      rw [configDecomposition_fst, configDecomposition_snd]
      exact h
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum _ _).symm


noncomputable def residualPMF (U : Set V) [DecidablePred (· ∈ U)]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    PMF (ResidualEdge X U → Bool) :=
  LabelledMultigraph.normalizedPMFOfSumPos (residualWeight X U q p) (by
    simpa only [residualPartition] using X.residualPartition_pos U hq hp₀ hp₁)

@[simp] lemma residualPMF_apply (U : Set V) [DecidablePred (· ∈ U)]
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ : ResidualEdge X U → Bool) :
    residualPMF X U hq hp₀ hp₁ ρ =
      (residualWeight X U q p ρ / residualPartition X U q p : NNReal) := by
  change (residualWeight X U q p ρ : ℝ≥0∞) *
    (∑' η, (residualWeight X U q p η : ℝ≥0∞))⁻¹ = _
  rw [tsum_fintype, ENNReal.coe_div (X.residualPartition_pos U hq hp₀ hp₁).ne']
  simp [residualPartition, div_eq_mul_inv]

lemma map_configDecomposition_fkPMF (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ((regionGraph X.graph U).fkPMF hq hp₁.le
      (regionGraph X.graph U).freeBoundary).map (configDecomposition X U) =
    FK.Finite.MarkovFactorization.independentProd
      ((regionGraph D (smallInterior X U)).fkPMF hq hp₁.le
        (regionGraph D (smallInterior X U)).freeBoundary)
      (residualPMF X U hq hp₀ hp₁) := by
  letI : Fintype (RegionSeal.Internal X.graph U → Bool) :=
    (regionGraph X.graph U).instFintypeConfiguration
  letI : Fintype (RegionSeal.Internal D (smallInterior X U) → Bool) :=
    (regionGraph D (smallInterior X U)).instFintypeConfiguration
  apply PMF.ext
  rintro ⟨η, ρ⟩
  calc
    _ = ((regionGraph X.graph U).fkPMF hq hp₁.le
      (regionGraph X.graph U).freeBoundary) ((configDecomposition X U).symm (η, ρ)) :=
      FK.Exploration.NestedFiniteCoupling.map_equiv_apply (configDecomposition X U) _ _
    _ = (regionGraph D (smallInterior X U)).fkPMF hq hp₁.le
        (regionGraph D (smallInterior X U)).freeBoundary η * residualPMF X U hq hp₀ hp₁ ρ := by
      rw [(regionGraph X.graph U).fkPMF_apply hq hp₁.le
        (regionGraph X.graph U).freeBoundary ((configDecomposition X U).symm (η, ρ)),
        (regionGraph D (smallInterior X U)).fkPMF_apply hq hp₁.le
        (regionGraph D (smallInterior X U)).freeBoundary η,
        X.residualPMF_apply U hq hp₀ hp₁ ρ]
      have hw := X.fkWeight_split U hcore q p ((configDecomposition X U).symm (η, ρ))
      have hs : smallReadout X U ((configDecomposition X U).symm (η, ρ)) = η := by
        rw [← configDecomposition_fst, Equiv.apply_symm_apply]
      have hr : residualReadout X U ((configDecomposition X U).symm (η, ρ)) = ρ := by
        rw [← configDecomposition_snd, Equiv.apply_symm_apply]
      rw [hs, hr] at hw
      rw [hw, X.partitionFunction_split U hcore q p]
      exact_mod_cast (div_mul_div_comm
        ((regionGraph D (smallInterior X U)).fkWeight q p
          (regionGraph D (smallInterior X U)).freeBoundary η)
        ((regionGraph D (smallInterior X U)).partitionFunction q p
          (regionGraph D (smallInterior X U)).freeBoundary)
        (residualWeight X U q p ρ) (residualPartition X U q p)).symm
    _ = _ := (FK.Finite.MarkovFactorization.independentProd_apply _ _ (η, ρ)).symm

lemma independentProd_map_fst {A B : Type*} [Fintype A] [Fintype B]
    (P : PMF A) (Q : PMF B) :
    (FK.Finite.MarkovFactorization.independentProd P Q).map Prod.fst = P := by
  apply PMF.ext
  intro a
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [FK.Finite.MarkovFactorization.independentProd_apply]
  calc
    (∑ x, ∑ y, if a = x then P x * Q y else 0) =
        ∑ x, if a = x then P x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : a = x
      · simp only [h, if_pos]
        rw [← Finset.mul_sum]
        have hQ := Q.tsum_coe
        rw [tsum_fintype] at hQ
        rw [hQ, mul_one]
      · simp [h]
    _ = P a := by simp

/-- **Exact induced free-region marginal.**  No fresh-vertex extension is
required.  The small coordinates of the large stopped free law are the free
FK law of the ordinary small induced region. -/
theorem map_smallReadout_fkPMF (U : Set V) [DecidablePred (· ∈ U)]
    (hcore : ∀ d : D.Vertex, X.vertex d ∈ U → d ∈ X.core)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ((regionGraph X.graph U).fkPMF hq hp₁.le
      (regionGraph X.graph U).freeBoundary).map (smallReadout X U) =
    (regionGraph D (smallInterior X U)).fkPMF hq hp₁.le
      (regionGraph D (smallInterior X U)).freeBoundary := by
  letI : Fintype (RegionSeal.Internal X.graph U → Bool) :=
    (regionGraph X.graph U).instFintypeConfiguration
  letI : Fintype (RegionSeal.Internal D (smallInterior X U) → Bool) :=
    (regionGraph D (smallInterior X U)).instFintypeConfiguration
  have hmap := X.map_configDecomposition_fkPMF U hcore hq hp₀ hp₁
  have hfun : smallReadout X U = Prod.fst ∘ configDecomposition X U := by
    funext ω
    exact (configDecomposition_fst X U ω).symm
  rw [hfun]
  calc
    _ = (((regionGraph X.graph U).fkPMF hq hp₁.le
      (regionGraph X.graph U).freeBoundary).map (configDecomposition X U)).map Prod.fst :=
      (PMF.map_comp (configDecomposition X U) _ Prod.fst).symm
    _ = _ := by rw [hmap]; exact independentProd_map_fst _ _

end NestedSumGeometry
end FK.Adaptive


namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set MeasureTheory
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling FK.RegionSeal FK.FinitePlane
open FK.NestedFinDLR

noncomputable section

local instance {E : Type*} [Fintype E] [DecidableEq E] : MeasurableSpace (Assignment E) := ⊤

namespace NestedSumGeometry

variable {V : Type*} [Fintype V] {D O : LabelledMultigraph}
  (X : NestedSumGeometry V D O)

/-- Open external edges of a stopped upper history have both endpoints in the
outer exploration region. -/
theorem endpoints_mem_outer_of_open_external {L : LabelledMultigraph}
    (B : Set L.Vertex) {k : Assignment L.Edge} {e : L.Edge}
    (he : ¬ IsInternal L (interior B k) e) (ho : decodeOption k e = true) :
    L.source e ∈ outer B k ∧ L.target e ∈ outer B k := by
  have hR : L.source e ∈ outer B k ∨ L.target e ∈ outer B k := by
    by_contra hn
    push_neg at hn
    exact he ⟨hn.1, hn.2⟩
  have closeTargetOfSource (hsR : L.source e ∈ outer B k) :
      L.target e ∈ outer B k := by
    by_cases heq : L.source e = L.target e
    · rwa [← heq]
    · change L.source e ∈ ClosedRegion (L.openGraph L.freeBoundary (decodeOption k)) B at hsR
      change L.target e ∈ ClosedRegion (L.openGraph L.freeBoundary (decodeOption k)) B
      rw [FK.Finite.Exploration.mem_outerRegion_iff] at hsR ⊢
      obtain ⟨v, hv, hvs⟩ := hsR
      refine ⟨v, hv, hvs.trans ?_⟩
      apply SimpleGraph.Adj.reachable
      exact ⟨heq, Or.inr ⟨e, ho, Or.inl ⟨rfl, rfl⟩⟩⟩
  have closeSourceOfTarget (htR : L.target e ∈ outer B k) :
      L.source e ∈ outer B k := by
    by_cases heq : L.target e = L.source e
    · rwa [← heq]
    · change L.target e ∈ ClosedRegion (L.openGraph L.freeBoundary (decodeOption k)) B at htR
      change L.source e ∈ ClosedRegion (L.openGraph L.freeBoundary (decodeOption k)) B
      rw [FK.Finite.Exploration.mem_outerRegion_iff] at htR ⊢
      obtain ⟨v, hv, hvt⟩ := htR
      refine ⟨v, hv, hvt.trans ?_⟩
      apply SimpleGraph.Adj.reachable
      exact ⟨heq, Or.inr ⟨e, ho, Or.inr ⟨rfl, rfl⟩⟩⟩
  rcases hR with hs | ht
  · exact ⟨hs, closeTargetOfSource hs⟩
  · exact ⟨closeSourceOfTarget ht, ht⟩

/-- Read small internal coordinates from a full large configuration. -/
def readSmall (U : Set V) [DecidablePred (· ∈ U)] (ω : X.graph.Configuration) :
    RegionSeal.Internal D (smallInterior X U) → Bool :=
  fun d => ω (Sum.inl d.1)

lemma readSmall_eq_map_restrictI (U : Set V) [DecidablePred (· ∈ U)] :
    readSmall X U = smallReadout X U ∘ restrictI X.graph U := by
  funext ω d
  rfl

/-- Read small internal coordinates from the independently extended joined
configuration. -/
def readSmallJoin (U : Set V) [DecidablePred (· ∈ U)]
    (ω : D.Edge ⊕ O.Edge → Bool) :
    RegionSeal.Internal D (smallInterior X U) → Bool :=
  restrictI D (smallInterior X U) (ω ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge))

/-- Specialized nested process on the graph supplied by the induced-region
geometry. -/
noncomputable def windowStep (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :=
  nestedTripleStep (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
    τ ξO ξ hq hp₀ hp₁

noncomputable def windowTriple (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :=
  nestedAdaptiveTriple (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
    τ ξO ξ hq hp₀ hp₁ B e₀

noncomputable def windowStopLaw (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :=
  letI : DecidableEq X.graph.Edge := Classical.decEq _
  @runTripleUntil X.graph.Edge (Classical.decEq _) (windowStep X τ ξO ξ hq hp₀ hp₁)
    (frontierNext (G := X.graph) B e₀) (frontierExhausted (G := X.graph) B)
    blank blank blank (Fintype.card (D.Edge ⊕ O.Edge))

noncomputable def windowResume (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    (z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)) :=
  letI : DecidableEq X.graph.Edge := Classical.decEq _
  @runTriple X.graph.Edge (Classical.decEq _) (windowStep X τ ξO ξ hq hp₀ hp₁)
    (frontierNext (G := X.graph) B e₀) z.1 z.2.1 z.2.2 (unrevealed z.2.2).card

lemma window_invariants (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support) :
    unrevealed z.1 = unrevealed z.2.2 ∧ unrevealed z.2.1 = unrevealed z.2.2 ∧
      decodeOption z.1 ≤ decodeOption z.2.2 ∧ decodeOption z.2.1 ≤ decodeOption z.2.2 ∧
      NoInteriorReveal (G := X.graph) B z.2.2 ∧ frontierExhausted (G := X.graph) B z.2.2 := by
  letI : DecidableEq X.graph.Edge := Classical.decEq _
  change z ∈ (@runTripleUntil X.graph.Edge (Classical.decEq _) (windowStep X τ ξO ξ hq hp₀ hp₁)
    (frontierNext (G := X.graph) B e₀) (frontierExhausted (G := X.graph) B)
    blank blank blank (Fintype.card X.graph.Edge)).support at hz
  exact runTripleUntil_frontier_invariants (G := X.graph) B e₀
    (windowStep X τ ξO ξ hq hp₀ hp₁)
    (fun h₁ h₂ k e hh₁ hh₂ hke w hw => nestedTripleStep_ordered
      (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
      τ ξO ξ hq hp₀ hp₁ h₁ h₂ k hh₁ hh₂ hke hw) hz

lemma window_small_hint (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support)
    (i : RegionSeal.Internal D (smallInterior X (interior (G := X.graph) B z.2.2))) :
    z.2.1 (Sum.inl i.1) = none := by
  have hi := X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz
  have hk := hi.2.2.2.2.1 (Sum.inl i.1)
    ((X.isInternal_inl_iff (interior (G := X.graph) B z.2.2) i.1).2 i.2)
  apply mem_unrevealed.1
  rw [hi.2.1]
  exact mem_unrevealed.2 hk

lemma window_small_hext (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support)
    (o : RegionSeal.External D (smallInterior X (interior (G := X.graph) B z.2.2))) :
    z.2.1 (Sum.inl o.1) ≠ none := by
  have hi := X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz
  apply external_assigned_of_frontierExhausted (G := X.graph) B hi.2.1 hi.2.2.2.2.2
  intro hiD
  exact o.2 ((X.isInternal_inl_iff (interior (G := X.graph) B z.2.2) o.1).1 hiD)

lemma window_small_hseal (τ : D.BoundaryPartition) (ξO : O.BoundaryPartition)
    (ξ : X.graph.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support)
    (o : RegionSeal.External D (smallInterior X (interior (G := X.graph) B z.2.2)))
    (ho : decodeOption z.2.1 (Sum.inl o.1) = true) :
    D.source o.1 ∉ smallInterior X (interior (G := X.graph) B z.2.2) ∧
      D.target o.1 ∉ smallInterior X (interior (G := X.graph) B z.2.2) := by
  have hi := X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz
  have hko : decodeOption z.2.2 (Sum.inl o.1) = true := by
    have hle := hi.2.2.2.1 (Sum.inl o.1)
    rw [ho] at hle
    exact Bool.eq_true_of_true_le hle
  have hext : ¬ IsInternal X.graph (interior (G := X.graph) B z.2.2) (Sum.inl o.1) := by
    intro hiD
    exact o.2 ((X.isInternal_inl_iff (interior (G := X.graph) B z.2.2) o.1).1 hiD)
  have hboth := endpoints_mem_outer_of_open_external (L := X.graph) B hext hko
  constructor
  · intro hs
    apply hs
    simpa only [graph, X.source_inl] using hboth.1
  · intro ht
    apply ht
    simpa only [graph, X.target_inl] using hboth.2


/-- At every supported maximal-frontier stop, the two lower coordinates have
exactly the same free law on their common small internal coordinates. -/
theorem window_small_free_interiors (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    (hcore : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → d ∈ X.core)
    (hwireξ : ∀ k : Assignment X.graph.Edge, ∀ v : X.graph.Vertex,
      v ∈ interior (G := X.graph) B k → ∀ w : X.graph.Vertex, ξ.r v w → v = w)
    (hwireτ : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → ∀ w : D.Vertex, τ.r d w → d = w)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support) :
    (cond (X.graph.fkPMF hq hp₁.le ξ)
      (fun ω => fkPMF_ne_zero X.graph hq hp₀ hp₁ ξ ω) z.1).map
        (readSmall X (interior (G := X.graph) B z.2.2)) =
      (regionGraph D (smallInterior X (interior (G := X.graph) B z.2.2))).fkPMF
        hq hp₁.le (regionGraph D
          (smallInterior X (interior (G := X.graph) B z.2.2))).freeBoundary ∧
    (cond (productJoinLaw (D.fkPMF hq hp₁.le τ)
      (O.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
      (productJoinLaw_ne_zero
        (fun ω => fkPMF_ne_zero D hq hp₀ hp₁ τ ω)
        (bernoulliProductPMF_ne_zero O ξO (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁))) z.2.1).map
        (readSmallJoin X (interior (G := X.graph) B z.2.2)) =
      (regionGraph D (smallInterior X (interior (G := X.graph) B z.2.2))).fkPMF
        hq hp₁.le (regionGraph D
          (smallInterior X (interior (G := X.graph) B z.2.2))).freeBoundary := by
  let U : Set V := interior (G := X.graph) B z.2.2
  let UD : Set D.Vertex := smallInterior X U
  have hU : U = interior (G := X.graph) B z.2.2 := rfl
  have hDU : UD = smallInterior X U := rfl
  have hi := X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz
  have hbig : (cond (X.graph.fkPMF hq hp₁.le ξ)
      (fun ω => fkPMF_ne_zero X.graph hq hp₀ hp₁ ξ ω) z.1).map
      (restrictI X.graph U) = (regionGraph X.graph U).fkPMF hq hp₁.le
        (regionGraph X.graph U).freeBoundary := by
    exact cond_map_restrictI_eq_free_region (G := X.graph) B ξ hq hp₀ hp₁
      hi.1 hi.2.2.1 hi.2.2.2.2.2 hi.2.2.2.2.1 (hwireξ z.2.2)
  constructor
  · change (cond (X.graph.fkPMF hq hp₁.le ξ)
      (fun ω => fkPMF_ne_zero X.graph hq hp₀ hp₁ ξ ω) z.1).map
      (readSmall X U) = (regionGraph D UD).fkPMF hq hp₁.le
        (regionGraph D UD).freeBoundary
    have hcomp : (cond (X.graph.fkPMF hq hp₁.le ξ)
        (fun ω => fkPMF_ne_zero X.graph hq hp₀ hp₁ ξ ω) z.1).map
        (readSmall X U) = ((regionGraph X.graph U).fkPMF hq hp₁.le
          (regionGraph X.graph U).freeBoundary).map (smallReadout X U) := by
      rw [readSmall_eq_map_restrictI, ← PMF.map_comp, hbig]
    have hsmall := X.map_smallReadout_fkPMF U (hcore z.2.2) hq hp₀ hp₁
    exact hcomp.trans hsmall
  · have hs := cond_productJoinLaw_map_small_region (G := D) (H := O)
      τ ξO hq hp₀ hp₁ z.2.1 UD
      (X.window_small_hint τ ξO ξ hq hp₀ hp₁ B e₀ hz)
      (X.window_small_hext τ ξO ξ hq hp₀ hp₁ B e₀ hz)
      (hwireτ z.2.2)
      (X.window_small_hseal τ ξO ξ hq hp₀ hp₁ B e₀ hz)
    exact hs


/-- Exact good intersection on all maximal closed-frontier strata.  The event
may depend on the stopped upper cutset; outside coordinates play no role. -/
theorem window_good_intersection (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    (hcore : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → d ∈ X.core)
    (hwireξ : ∀ k : Assignment X.graph.Edge, ∀ v : X.graph.Vertex,
      v ∈ interior (G := X.graph) B k → ∀ w : X.graph.Vertex, ξ.r v w → v = w)
    (hwireτ : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → ∀ w : D.Vertex, τ.r d w → d = w)
    (A : ∀ k : Assignment X.graph.Edge,
      Set (RegionSeal.Internal D (smallInterior X (interior (G := X.graph) B k)) → Bool)) :
    let stopLaw := windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀
    let resume := windowResume X τ ξO ξ hq hp₀ hp₁ B e₀
    let joint := stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))
    joint.toMeasure {x | readSmall X (interior (G := X.graph) B x.1.2.2)
      (decodeOption x.2.1) ∈ A x.1.2.2} =
    joint.toMeasure {x | readSmallJoin X (interior (G := X.graph) B x.1.2.2)
      (decodeOption x.2.2.1) ∈ A x.1.2.2} := by
  intro stopLaw resume joint
  let L : Set ((Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)) :=
    {x | readSmall X (interior (G := X.graph) B x.1.2.2)
      (decodeOption x.2.1) ∈ A x.1.2.2}
  let R : Set ((Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)) :=
    {x | readSmallJoin X (interior (G := X.graph) B x.1.2.2)
      (decodeOption x.2.2.1) ∈ A x.1.2.2}
  change joint.toMeasure L = joint.toMeasure R
  rw [PMF.toMeasure_bind_apply _ _ L MeasurableSet.of_discrete,
    PMF.toMeasure_bind_apply _ _ R MeasurableSet.of_discrete]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ stopLaw.support
  · have hi := X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz
    have hfree := X.window_small_free_interiors τ ξO ξ hq hp₀ hp₁ B e₀
      hcore hwireξ hwireτ hz
    have hm (s : Side) :
        (resume z).map (fun w => decodeOption (pick s w.1 w.2.1 w.2.2)) =
          cond (nestedSideLaw (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
            τ ξ hq hp₀ hp₁ s)
          (nestedSideLaw_pos (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
            τ ξO ξ hq hp₀ hp₁ s) (pick s z.1 z.2.1 z.2.2) := by
      dsimp only [resume, windowResume]
      exact @runTriple_map_side (D.Edge ⊕ O.Edge) _ (Classical.decEq _)
        (nestedSideLaw (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
          τ ξ hq hp₀ hp₁)
        (nestedSideLaw_pos (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
          τ ξO ξ hq hp₀ hp₁)
        (windowStep X τ ξO ξ hq hp₀ hp₁)
        (frontierNext (G := X.graph) B e₀)
        (fun s h₁ h₂ k a ha => nestedTripleStep_map_side
          (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
          τ ξO ξ hq hp₀ hp₁ s h₁ h₂ k ha)
        (fun k hk => frontierNext_unrevealed (G := X.graph) B e₀ (k := k) hk)
        s z.1 z.2.1 z.2.2 hi.1 hi.2.1 _ rfl
    have hmL := hm Side.left
    change (resume z).map (fun w => decodeOption w.1) = _ at hmL
    have hgraph : nestedBig (G := X.graph) (D := D) (O := O)
        (eV := Equiv.refl V) (Equiv.refl (D.Edge ⊕ O.Edge)) = X.graph := rfl
    have hmL' : (resume z).map (fun w => decodeOption w.1) =
        cond (X.graph.fkPMF hq hp₁.le ξ)
          (fun ω => fkPMF_ne_zero X.graph hq hp₀ hp₁ ξ ω) z.1 := by
      simp only [nestedSideLaw, pick] at hmL
      with_unfolding_all exact hmL
    have hpushL : (resume z).map (fun w =>
        readSmall X (interior (G := X.graph) B z.2.2) (decodeOption w.1)) =
        (regionGraph D (smallInterior X (interior (G := X.graph) B z.2.2))).fkPMF
          hq hp₁.le (regionGraph D
            (smallInterior X (interior (G := X.graph) B z.2.2))).freeBoundary := by
      exact (PMF.map_comp (fun w : Assignment X.graph.Edge × Assignment X.graph.Edge ×
        Assignment X.graph.Edge => decodeOption w.1) (resume z)
        (readSmall X (interior (G := X.graph) B z.2.2))).symm.trans
          ((congrArg (PMF.map (readSmall X (interior (G := X.graph) B z.2.2))) hmL').trans
            hfree.1)
    have hmR := hm Side.right
    change (resume z).map (fun w => decodeOption w.2.1) = _ at hmR
    have hmR' : (resume z).map (fun w => decodeOption w.2.1) =
        cond (productJoinLaw (D.fkPMF hq hp₁.le τ)
          (O.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le))
          (productJoinLaw_ne_zero
            (fun ω => fkPMF_ne_zero D hq hp₀ hp₁ τ ω)
            (bernoulliProductPMF_ne_zero O ξO (upperRateNN_pos hp₀)
              (upperRateNN_lt_one hq hp₀ hp₁))) z.2.1 := by
      simp only [nestedSideLaw, pick] at hmR
      with_unfolding_all exact hmR
    have hpushR : (resume z).map (fun w =>
        readSmallJoin X (interior (G := X.graph) B z.2.2) (decodeOption w.2.1)) =
        (regionGraph D (smallInterior X (interior (G := X.graph) B z.2.2))).fkPMF
          hq hp₁.le (regionGraph D
            (smallInterior X (interior (G := X.graph) B z.2.2))).freeBoundary := by
      exact (PMF.map_comp (fun w : Assignment X.graph.Edge × Assignment X.graph.Edge ×
        Assignment X.graph.Edge => decodeOption w.2.1) (resume z)
        (readSmallJoin X (interior (G := X.graph) B z.2.2))).symm.trans
          ((congrArg (PMF.map (readSmallJoin X (interior (G := X.graph) B z.2.2))) hmR').trans
            hfree.2)
    have hmeasL : (resume z).toMeasure {w |
        readSmall X (interior (G := X.graph) B z.2.2) (decodeOption w.1) ∈ A z.2.2} =
        ((resume z).map (fun w => readSmall X (interior (G := X.graph) B z.2.2)
          (decodeOption w.1))).toMeasure (A z.2.2) := by
      symm
      exact PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete
    have hmeasR : (resume z).toMeasure {w |
        readSmallJoin X (interior (G := X.graph) B z.2.2) (decodeOption w.2.1) ∈ A z.2.2} =
        ((resume z).map (fun w => readSmallJoin X (interior (G := X.graph) B z.2.2)
          (decodeOption w.2.1))).toMeasure (A z.2.2) := by
      symm
      exact PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete
    have hjointL : ((resume z).map (fun w => (z, w))).toMeasure L =
        (resume z).toMeasure {w | readSmall X (interior (G := X.graph) B z.2.2)
          (decodeOption w.1) ∈ A z.2.2} := by
      rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete]
      rfl
    have hjointR : ((resume z).map (fun w => (z, w))).toMeasure R =
        (resume z).toMeasure {w | readSmallJoin X (interior (G := X.graph) B z.2.2)
          (decodeOption w.2.1) ∈ A z.2.2} := by
      rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete]
      rfl
    rw [hjointL, hjointR, hmeasL, hmeasR, hpushL, hpushR]
  · have hz0 : stopLaw z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
    simp [hz0]


lemma fiber_decode_le {L : LabelledMultigraph} {k : Assignment L.Edge}
    {ω : L.Configuration} (hω : ω ∈ Fiber k) : decodeOption k ≤ ω := by
  intro e
  cases hk : k e with
  | none => simp [decodeOption, hk]
  | some b =>
      have hb := hω e b hk
      simp [decodeOption, hk, hb]

/-- The genuinely maximal cutset does not change when hidden interior bits are
resumed. -/
theorem outer_eq_of_fiber_frontierExhausted {L : LabelledMultigraph}
    (B : Set L.Vertex) {k : Assignment L.Edge} {ω : L.Configuration}
    (hs : frontierExhausted B k) (hω : ω ∈ Fiber k) :
    outer B k = L.outerRegion L.freeBoundary B ω := by
  have hle : decodeOption k ≤ ω := fiber_decode_le hω
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ ClosedRegion (L.openGraph L.freeBoundary (decodeOption k)) B at hx
    change x ∈ ClosedRegion (L.openGraph L.freeBoundary ω) B
    rw [FK.Finite.Exploration.mem_outerRegion_iff] at hx ⊢
    obtain ⟨b, hb, hbx⟩ := hx
    exact ⟨b, hb, hbx.mono (L.connectionGraph_mono hle)⟩
  · apply FK.Finite.Exploration.outerRegion_subset_of_closedBoundary
      (L.openGraph_le_ambientGraph L.freeBoundary ω) subset_closedRegion
    intro x y hx hy _hAmbient hxy
    apply hy
    obtain ⟨hne, hwire | ⟨e, he, hjoin⟩⟩ := hxy
    · exact (hne hwire).elim
    have hext : ¬ IsInternal L (interior B k) e := by
      intro hi
      rcases hjoin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hi.1 hx
      · exact hi.2 hx
    have hke := external_assigned_of_frontierExhausted B (h := k) (k := k) rfl hs hext
    have hko : decodeOption k e = true := by
      cases hk : k e with
      | none => exact (hke hk).elim
      | some b =>
          have hb := hω e b hk
          rw [hb] at he
          subst b
          simp [decodeOption, hk]
    rw [FK.Finite.Exploration.mem_outerRegion_iff] at hx ⊢
    obtain ⟨r, hr, hrx⟩ := hx
    refine ⟨r, hr, hrx.trans (SimpleGraph.Adj.reachable ?_)⟩
    exact ⟨hne, Or.inr ⟨e, hko, hjoin⟩⟩

lemma mem_fiber_of_mem_support_cond {L : LabelledMultigraph}
    (μ : PMF L.Configuration) (hμ : ∀ ω, μ ω ≠ 0)
    (h : Assignment L.Edge) {ω : L.Configuration}
    (hω : ω ∈ (cond μ hμ h).support) : ω ∈ Fiber h := by
  by_contra hn
  have hzero : cond μ hμ h ω = 0 := by
    simp [cond_apply, hn]
  exact (PMF.mem_support_iff _ _).1 hω hzero

/-- The middle coordinate copies every outside bit from the common upper
configuration and leaves small bits untouched. -/
def copyMiddle (z : X.graph.Configuration × X.graph.Configuration ×
    X.graph.Configuration) : X.graph.Configuration :=
  fun a => match a with
    | Sum.inl d => z.2.1 (Sum.inl d)
    | Sum.inr o => z.2.2 (Sum.inr o)

def copyPoint (z : X.graph.Configuration × X.graph.Configuration ×
    X.graph.Configuration) : X.graph.Configuration × X.graph.Configuration ×
    X.graph.Configuration :=
  (z.1, copyMiddle X z, z.2.2)

/-- Actual adaptive FK/FK/Bernoulli triple with outside-coordinate copying.
Only the exact small FK restriction is asserted for the middle coordinate;
its full outside law is the one induced by the synchronized coupling. -/
noncomputable def windowCopyTriple (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    PMF.RelativeTripleCoupling
      (X.graph.fkPMF hq hp₁.le ξ)
      ((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyMiddle X))
      (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
      (fun a c => a ≤ c) (fun b c => b ≤ c) where
  dist := (windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyPoint X)
  map_fst := by
    let T := windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀
    refine (PMF.map_comp (copyPoint X) T.dist Prod.fst).trans ?_
    rw [show Prod.fst ∘ copyPoint X = (fun z : X.graph.Configuration ×
      X.graph.Configuration × X.graph.Configuration => z.1) from rfl]
    with_unfolding_all exact T.map_fst
  map_snd := by
    let T := windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀
    exact PMF.map_comp (copyPoint X) T.dist (fun z => z.2.1)
  map_thd := by
    let T := windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀
    refine (PMF.map_comp (copyPoint X) T.dist (fun z => z.2.2)).trans ?_
    rw [show (fun z => z.2.2) ∘ copyPoint X = (fun z : X.graph.Configuration ×
      X.graph.Configuration × X.graph.Configuration => z.2.2) from rfl]
    with_unfolding_all exact T.map_thd
  rel_fst := by
    intro z hz
    change z ∈ ((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyPoint X)).support at hz
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff (copyPoint X) _ z).1 hz
    with_unfolding_all exact (windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).rel_fst w hw
  rel_snd := by
    intro z hz
    change z ∈ ((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyPoint X)).support at hz
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff (copyPoint X) _ z).1 hz
    have h := (windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).rel_snd w hw
    intro a
    cases a with
    | inl d => exact h (Sum.inl d)
    | inr o => exact le_rfl

lemma windowCopyTriple_map_fst (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    (windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (fun z => z.1) =
      X.graph.fkPMF hq hp₁.le ξ :=
  (windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀).map_fst

lemma windowCopyTriple_map_snd_restrict_left (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    (windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
      (fun z => z.2.1 ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge)) = D.fkPMF hq hp₁.le τ := by
  change ((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyPoint X)).map
    (fun z => z.2.1 ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge)) = _
  let T := windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀
  refine (PMF.map_comp (copyPoint X) T.dist (fun z => z.2.1 ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge))).trans ?_
  with_unfolding_all convert
    (nestedAdaptiveTriple_map_snd_restrict_left
      (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
      τ ξO ξ hq hp₀ hp₁ B e₀) using 1 <;> rfl

lemma windowCopyTriple_outside (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) {o : O.Edge} :
    ∀ᵐ z ∂(windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.toMeasure,
      z.2.1 (Sum.inr o) = z.2.2 (Sum.inr o) := by
  apply PMF.ae_of_forall_mem_support
  intro z hz
  change z ∈ ((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyPoint X)).support at hz
  obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff (copyPoint X) _ z).1 hz
  rfl


lemma runTriple_decidableEq_irrel {E : Type*} [Fintype E]
    (i₁ i₂ : DecidableEq E)
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E) (h₁ h₂ k : Assignment E) (n : ℕ) :
    @runTriple E i₁ step next h₁ h₂ k n = @runTriple E i₂ step next h₁ h₂ k n := by
  have h : i₁ = i₂ := Subsingleton.elim _ _
  cases h
  rfl

/-- Ordinary readout of a resumed triple of partial configurations. -/
def decodePoint (z : Assignment X.graph.Edge × Assignment X.graph.Edge ×
    Assignment X.graph.Edge) : X.graph.Configuration × X.graph.Configuration ×
    X.graph.Configuration :=
  (decodeOption z.1, decodeOption z.2.1, decodeOption z.2.2)

/-- Joint stopped/resumed readout of a nested triple. -/
def decodeResumePoint (x : (Assignment X.graph.Edge × Assignment X.graph.Edge ×
    Assignment X.graph.Edge) × (Assignment X.graph.Edge × Assignment X.graph.Edge ×
    Assignment X.graph.Edge)) : X.graph.Configuration × X.graph.Configuration ×
    X.graph.Configuration := decodePoint X x.2

/-- The full synchronized triple factors through the common maximal stop and
its resumed hidden bits. -/
theorem windowTriple_eq_joint_map (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) :
    let stopLaw := windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀
    let resume := windowResume X τ ξO ξ hq hp₀ hp₁ B e₀
    let joint := stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))
    (windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist = joint.map (decodeResumePoint X) := by
  intro stopLaw resume joint
  let T := windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀
  let step := windowStep X τ ξO ξ hq hp₀ hp₁
  let next := frontierNext (G := X.graph) B e₀
  have hdec : @runTriple X.graph.Edge (fun a b => instDecidableEqSum a b)
      step next blank blank blank (Fintype.card X.graph.Edge) =
    @runTriple X.graph.Edge (Classical.decEq _)
      step next blank blank blank (Fintype.card X.graph.Edge) :=
    runTriple_decidableEq_irrel _ _ _ _ _ _ _ _
  have hr : @runTriple X.graph.Edge (Classical.decEq _)
      step next blank blank blank (Fintype.card X.graph.Edge) =
      stopLaw.bind resume := by
    exact @runTriple_eq_runTripleUntil_bind X.graph.Edge _ (Classical.decEq _)
      step next (frontierExhausted (G := X.graph) B)
      (fun k hk => frontierNext_unrevealed (G := X.graph) B e₀ (k := k) hk)
      blank blank blank (by simp) (by simp) _
      (by with_unfolding_all simp [unrevealed, blank])
  change T.dist = joint.map (decodeResumePoint X)
  refine (congrArg (PMF.map (decodePoint X)) hdec).trans ?_
  refine (congrArg (PMF.map (decodePoint X)) hr).trans ?_
  refine (PMF.map_bind stopLaw resume (decodePoint X)).trans ?_
  simp only [joint, decodeResumePoint, PMF.map_bind]
  congr 1
  funext z
  rw [PMF.map_comp]
  rfl


lemma windowResume_upper_cond (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support) :
    (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
      (fun w => decodeOption w.2.2) =
      cond (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
        (bernoulliProductPMF_ne_zero X.graph ξ (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁)) z.2.2 := by
  have hi := X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz
  have hm := @runTriple_map_side (D.Edge ⊕ O.Edge) _ (Classical.decEq _)
    (nestedSideLaw (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
      τ ξ hq hp₀ hp₁)
    (nestedSideLaw_pos (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
      τ ξO ξ hq hp₀ hp₁)
    (windowStep X τ ξO ξ hq hp₀ hp₁)
    (frontierNext (G := X.graph) B e₀)
    (fun s h₁ h₂ k a ha => nestedTripleStep_map_side
      (G := X.graph) (eV := Equiv.refl V) (Equiv.refl _)
      τ ξO ξ hq hp₀ hp₁ s h₁ h₂ k ha)
    (fun k hk => frontierNext_unrevealed (G := X.graph) B e₀ (k := k) hk)
    Side.upper z.1 z.2.1 z.2.2 hi.1 hi.2.1 (unrevealed z.2.2).card rfl
  change (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
    (fun w => decodeOption w.2.2) = _
  with_unfolding_all exact hm

lemma windowResume_upper_fiber (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {z : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hz : z ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support)
    {w : Assignment (D.Edge ⊕ O.Edge) × Assignment (D.Edge ⊕ O.Edge) ×
      Assignment (D.Edge ⊕ O.Edge)}
    (hw : w ∈ (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).support) :
    decodeOption w.2.2 ∈ Fiber z.2.2 := by
  have hwp : decodeOption w.2.2 ∈ ((windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
      (fun u => decodeOption u.2.2)).support :=
    (PMF.mem_support_map_iff (fun u => decodeOption u.2.2)
      (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z) (decodeOption w.2.2)).2
      ⟨w, hw, rfl⟩
  have hc := X.windowResume_upper_cond τ ξO ξ hq hp₀ hp₁ B e₀ hz
  have hwp' : decodeOption w.2.2 ∈
      (cond (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
        (bernoulliProductPMF_ne_zero X.graph ξ (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁)) z.2.2).support := by
    rw [← hc]
    exact hwp
  exact mem_fiber_of_mem_support_cond _ _ _ hwp'

lemma windowJoint_upper_fiber (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {x : (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)}
    (hx : x ∈ ((windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).bind
      (fun z => (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
        (fun w => (z, w)))).support) :
    decodeOption x.2.2.2 ∈ Fiber x.1.2.2 := by
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨z, hz, hx⟩ := hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact X.windowResume_upper_fiber τ ξO ξ hq hp₀ hp₁ B e₀ hz hw

/-- Cylinder observations on a fixed base of small edges. -/
def baseCylinder (J : Finset D.Edge) (S : Set (J → Bool))
    (ω : D.Edge → Bool) : Prop := (fun j : J => ω j.1) ∈ S

/-- The full upper configuration encloses every base edge in the maximal
unexplored small region. -/
def enclosedBase (J : Finset D.Edge) (B : Set V) (ω : X.graph.Configuration) : Prop :=
  ∀ j : J, IsInternal D (smallInterior X
    (X.graph.interior X.graph.freeBoundary B ω)) j.1

lemma enclosedBase_stopped_iff {J : Finset D.Edge} (B : Set V)
    {k : Assignment X.graph.Edge} {ω : X.graph.Configuration}
    (hs : frontierExhausted B k) (hω : ω ∈ Fiber k) :
    enclosedBase X J B ω ↔
      ∀ j : J, IsInternal D (smallInterior X (interior (G := X.graph) B k)) j.1 := by
  have hset : X.graph.interior X.graph.freeBoundary B ω = interior (G := X.graph) B k := by
    change (X.graph.outerRegion X.graph.freeBoundary B ω)ᶜ =
      (outer (G := X.graph) B k)ᶜ
    exact congrArg (fun s : Set V => sᶜ) (outer_eq_of_fiber_frontierExhausted B hs hω).symm
  unfold enclosedBase
  rw [hset]

/-- The stopped cutset observation used for a base cylinder. -/
def stoppedObservation (J : Finset D.Edge) (S : Set (J → Bool)) (B : Set V)
    (k : Assignment X.graph.Edge) :
    Set (RegionSeal.Internal D (smallInterior X (interior (G := X.graph) B k)) → Bool) :=
  if h : ∀ j : J, IsInternal D (smallInterior X (interior (G := X.graph) B k)) j.1 then
    {η | (fun j : J => η ⟨j.1, h j⟩) ∈ S} else ∅


lemma windowJoint_stop_support (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    {x : (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)}
    (hx : x ∈ ((windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).bind
      (fun z => (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
        (fun w => (z, w)))).support) :
    x.1 ∈ (windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).support := by
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨z, hz, hx⟩ := hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact hz

lemma copy_left_event_iff_stopped (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) (J : Finset D.Edge) (S : Set (J → Bool))
    {x : (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)}
    (hx : x ∈ ((windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).bind
      (fun z => (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
        (fun w => (z, w)))).support) :
    (baseCylinder J S ((copyPoint X (decodeResumePoint X x)).1 ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge)) ∧
      enclosedBase X J B ((copyPoint X (decodeResumePoint X x)).2.2)) ↔
    readSmall X (interior (G := X.graph) B x.1.2.2) (decodeOption x.2.1) ∈
      stoppedObservation X J S B x.1.2.2 := by
  have hz := X.windowJoint_stop_support τ ξO ξ hq hp₀ hp₁ B e₀ hx
  have hω := X.windowJoint_upper_fiber τ ξO ξ hq hp₀ hp₁ B e₀ hx
  have hs := (X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz).2.2.2.2.2
  have hc := enclosedBase_stopped_iff (X := X) (J := J) B hs hω
  change (baseCylinder J S (fun d : D.Edge => (show D.Edge ⊕ O.Edge → Bool from decodeOption x.2.1) (Sum.inl d)) ∧
      enclosedBase X J B (decodeOption x.2.2.2)) ↔ _
  rw [hc]
  by_cases h : ∀ j : J, IsInternal D
      (smallInterior X (interior (G := X.graph) B x.1.2.2)) j.1
  · unfold stoppedObservation
    rw [dif_pos h]
    constructor
    · rintro ⟨hbase, _⟩
      with_unfolding_all exact hbase
    · intro hobs
      refine ⟨?_, ?_⟩
      · with_unfolding_all exact hobs
      · intro a
        exact h a
  · unfold stoppedObservation
    rw [dif_neg h]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hg⟩
    exact h (fun j => hg j)

lemma copy_right_event_iff_stopped (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge) (J : Finset D.Edge) (S : Set (J → Bool))
    {x : (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)}
    (hx : x ∈ ((windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀).bind
      (fun z => (windowResume X τ ξO ξ hq hp₀ hp₁ B e₀ z).map
        (fun w => (z, w)))).support) :
    (baseCylinder J S ((copyPoint X (decodeResumePoint X x)).2.1 ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge)) ∧
      enclosedBase X J B ((copyPoint X (decodeResumePoint X x)).2.2)) ↔
    readSmallJoin X (interior (G := X.graph) B x.1.2.2) (decodeOption x.2.2.1) ∈
      stoppedObservation X J S B x.1.2.2 := by
  have hz := X.windowJoint_stop_support τ ξO ξ hq hp₀ hp₁ B e₀ hx
  have hω := X.windowJoint_upper_fiber τ ξO ξ hq hp₀ hp₁ B e₀ hx
  have hs := (X.window_invariants τ ξO ξ hq hp₀ hp₁ B e₀ hz).2.2.2.2.2
  have hc := enclosedBase_stopped_iff (X := X) (J := J) B hs hω
  change (baseCylinder J S (fun d : D.Edge => (show D.Edge ⊕ O.Edge → Bool from decodeOption x.2.2.1) (Sum.inl d)) ∧
      enclosedBase X J B (decodeOption x.2.2.2)) ↔ _
  rw [hc]
  by_cases h : ∀ j : J, IsInternal D
      (smallInterior X (interior (G := X.graph) B x.1.2.2)) j.1
  · unfold stoppedObservation
    rw [dif_pos h]
    constructor
    · rintro ⟨hbase, _⟩
      with_unfolding_all exact hbase
    · intro hobs
      refine ⟨?_, ?_⟩
      · with_unfolding_all exact hobs
      · intro a
        exact h a
  · unfold stoppedObservation
    rw [dif_neg h]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hg⟩
    exact h (fun j => hg j)

/-- **Common-upper good identity on the genuine maximal nested cutset.** -/
theorem windowCopyTriple_good_cylinder (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    (hcore : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → d ∈ X.core)
    (hwireξ : ∀ k : Assignment X.graph.Edge, ∀ v : X.graph.Vertex,
      v ∈ interior (G := X.graph) B k → ∀ w : X.graph.Vertex, ξ.r v w → v = w)
    (hwireτ : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → ∀ w : D.Vertex, τ.r d w → d = w)
    (J : Finset D.Edge) (S : Set (J → Bool)) :
    let T := windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀
    T.dist.toMeasure {z | baseCylinder J S (fun d : D.Edge => z.1 (Sum.inl d)) ∧ enclosedBase X J B z.2.2} =
    T.dist.toMeasure {z | baseCylinder J S (fun d : D.Edge => z.2.1 (Sum.inl d)) ∧ enclosedBase X J B z.2.2} := by
  intro T
  let stopLaw := windowStopLaw X τ ξO ξ hq hp₀ hp₁ B e₀
  let resume := windowResume X τ ξO ξ hq hp₀ hp₁ B e₀
  let joint := stopLaw.bind (fun z => (resume z).map (fun w => (z, w)))
  let EL : Set (X.graph.Configuration × X.graph.Configuration × X.graph.Configuration) :=
    {z | baseCylinder J S (fun d : D.Edge => z.1 (Sum.inl d)) ∧ enclosedBase X J B z.2.2}
  let ER : Set (X.graph.Configuration × X.graph.Configuration × X.graph.Configuration) :=
    {z | baseCylinder J S (fun d : D.Edge => z.2.1 (Sum.inl d)) ∧ enclosedBase X J B z.2.2}
  let OL : Set ((Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)) :=
    {x | readSmall X (interior (G := X.graph) B x.1.2.2) (decodeOption x.2.1) ∈
      stoppedObservation X J S B x.1.2.2}
  let OR : Set ((Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge) ×
      (Assignment X.graph.Edge × Assignment X.graph.Edge × Assignment X.graph.Edge)) :=
    {x | readSmallJoin X (interior (G := X.graph) B x.1.2.2)
      (decodeOption x.2.2.1) ∈ stoppedObservation X J S B x.1.2.2}
  have hdist : T.dist = joint.map (copyPoint X ∘ decodeResumePoint X) := by
    change (windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map (copyPoint X) = _
    rw [X.windowTriple_eq_joint_map τ ξO ξ hq hp₀ hp₁ B e₀]
    rw [PMF.map_comp]
  change T.dist.toMeasure EL = T.dist.toMeasure ER
  rw [hdist]
  rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete,
    PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete]
  have hleft : ((copyPoint X ∘ decodeResumePoint X) ⁻¹' EL) =ᵐ[joint.toMeasure] OL := by
    apply Filter.eventuallyEq_set.2
    apply PMF.ae_of_forall_mem_support
    intro x hx
    exact X.copy_left_event_iff_stopped τ ξO ξ hq hp₀ hp₁ B e₀ J S hx
  have hright : ((copyPoint X ∘ decodeResumePoint X) ⁻¹' ER) =ᵐ[joint.toMeasure] OR := by
    apply Filter.eventuallyEq_set.2
    apply PMF.ae_of_forall_mem_support
    intro x hx
    exact X.copy_right_event_iff_stopped τ ξO ξ hq hp₀ hp₁ B e₀ J S hx
  calc
    _ = joint.toMeasure OL := MeasureTheory.measure_congr hleft
    _ = joint.toMeasure OR := X.window_good_intersection τ ξO ξ hq hp₀ hp₁ B e₀
      hcore hwireξ hwireτ (stoppedObservation X J S B)
    _ = _ := (MeasureTheory.measure_congr hright).symm


/-- Finite equation (9) for an ordinary nested compatible window. -/
theorem windowCopyTriple_abs_sub_le (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    (hcore : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → d ∈ X.core)
    (hwireξ : ∀ k : Assignment X.graph.Edge, ∀ v : X.graph.Vertex,
      v ∈ interior (G := X.graph) B k → ∀ w : X.graph.Vertex, ξ.r v w → v = w)
    (hwireτ : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → ∀ w : D.Vertex, τ.r d w → d = w)
    (J : Finset D.Edge) (S : Set (J → Bool)) :
    abs ((X.graph.fkPMF hq hp₁.le ξ).toMeasure.real
        {ω | baseCylinder J S (fun d : D.Edge => ω (Sum.inl d))} -
      (D.fkPMF hq hp₁.le τ).toMeasure.real (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (enclosedBase X J B)ᶜ := by
  let T := windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀
  let A : Set X.graph.Configuration :=
    {ω | baseCylinder J S (fun d : D.Edge => ω (Sum.inl d))}
  let C : Set X.graph.Configuration := enclosedBase X J B
  let AD : Set D.Configuration := baseCylinder J S
  have hgood : T.dist.toMeasure
      ((fun z => z.1) ⁻¹' A ∩ (fun z => z.2.2) ⁻¹' C) =
    T.dist.toMeasure ((fun z => z.2.1) ⁻¹' A ∩ (fun z => z.2.2) ⁻¹' C) := by
    exact X.windowCopyTriple_good_cylinder τ ξO ξ hq hp₀ hp₁ B e₀
      hcore hwireξ hwireτ J S
  have hbase := T.equation_nine_abs_bound (A := A) (B := A) (C := C)
    MeasurableSet.of_discrete MeasurableSet.of_discrete MeasurableSet.of_discrete hgood
  let f : X.graph.Configuration → D.Configuration :=
    fun ω => ω ∘ (Sum.inl : D.Edge → D.Edge ⊕ O.Edge)
  have hpre : f ⁻¹' AD = A := by
    ext ω
    rfl
  have hρf : (((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
      (copyMiddle X)).map f) = D.fkPMF hq hp₁.le τ := by
    calc
      _ = ((windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
        (fun z => z.2.1)).map f := by
          rw [(windowCopyTriple X τ ξO ξ hq hp₀ hp₁ B e₀).map_snd]
      _ = _ := by
        rw [PMF.map_comp]
        exact X.windowCopyTriple_map_snd_restrict_left τ ξO ξ hq hp₀ hp₁ B e₀
  have hsecond : ((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
      (copyMiddle X)).toMeasure.real A = (D.fkPMF hq hp₁.le τ).toMeasure.real AD := by
    apply congrArg ENNReal.toReal
    calc
      _ = (((windowTriple X τ ξO ξ hq hp₀ hp₁ B e₀).dist.map
        (copyMiddle X)).map f).toMeasure AD := by
        rw [PMF.toMeasure_map_apply _ _ _ (by fun_prop) MeasurableSet.of_discrete, hpre]
      _ = _ := by rw [hρf]
  rw [hsecond] at hbase
  change |(X.graph.fkPMF hq hp₁.le ξ).toMeasure.real A -
      (D.fkPMF hq hp₁.le τ).toMeasure.real AD| ≤ _ at hbase
  change |(X.graph.fkPMF hq hp₁.le ξ).toMeasure.real A -
      (D.fkPMF hq hp₁.le τ).toMeasure.real AD| ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real Cᶜ
  convert hbase using 1 <;> simp only [AD]


/-- An upper-open arm from a base edge to the exploration roots. -/
def upperArm (J : Finset D.Edge) (B : Set V) (ω : X.graph.Configuration) : Prop :=
  ∃ j : J, ∃ b ∈ B,
    (X.graph.openGraph X.graph.freeBoundary ω).Reachable (X.vertex (D.source j.1)) b ∨
    (X.graph.openGraph X.graph.freeBoundary ω).Reachable (X.vertex (D.target j.1)) b

lemma compl_enclosedBase_subset_upperArm (J : Finset D.Edge) (B : Set V) :
    ({ω | ¬ enclosedBase X J B ω} : Set X.graph.Configuration) ⊆
      {ω | upperArm X J B ω} := by
  intro ω hω
  change ¬ enclosedBase X J B ω at hω
  unfold enclosedBase at hω
  push Not at hω
  obtain ⟨j, hj⟩ := hω
  have hor : X.vertex (D.source j.1) ∈ X.graph.outerRegion X.graph.freeBoundary B ω ∨
      X.vertex (D.target j.1) ∈ X.graph.outerRegion X.graph.freeBoundary B ω := by
    by_contra hn
    push Not at hn
    exact hj ⟨hn.1, hn.2⟩
  rcases hor with hs | ht
  · obtain ⟨b, hb, hpath⟩ := FK.Finite.Exploration.mem_outerRegion_iff.mp hs
    exact ⟨j, b, hb, Or.inl hpath.symm⟩
  · obtain ⟨b, hb, hpath⟩ := FK.Finite.Exploration.mem_outerRegion_iff.mp ht
    exact ⟨j, b, hb, Or.inr hpath.symm⟩

/-- Equation (9) with the error stated directly as an upper-Bernoulli arm. -/
theorem windowCopyTriple_abs_sub_le_arm (τ : D.BoundaryPartition)
    (ξO : O.BoundaryPartition) (ξ : X.graph.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (B : Set V) (e₀ : D.Edge ⊕ O.Edge)
    (hcore : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → d ∈ X.core)
    (hwireξ : ∀ k : Assignment X.graph.Edge, ∀ v : X.graph.Vertex,
      v ∈ interior (G := X.graph) B k → ∀ w : X.graph.Vertex, ξ.r v w → v = w)
    (hwireτ : ∀ k : Assignment X.graph.Edge, ∀ d : D.Vertex,
      X.vertex d ∈ interior (G := X.graph) B k → ∀ w : D.Vertex, τ.r d w → d = w)
    (J : Finset D.Edge) (S : Set (J → Bool)) :
    abs ((X.graph.fkPMF hq hp₁.le ξ).toMeasure.real
        {ω | baseCylinder J S (fun d : D.Edge => ω (Sum.inl d))} -
      (D.fkPMF hq hp₁.le τ).toMeasure.real (baseCylinder J S)) ≤
    (X.graph.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le).toMeasure.real
      (upperArm X J B) := by
  refine (X.windowCopyTriple_abs_sub_le τ ξO ξ hq hp₀ hp₁ B e₀
    hcore hwireξ hwireτ J S).trans ?_
  exact MeasureTheory.measureReal_mono (compl_enclosedBase_subset_upperArm (X := X) J B)

end NestedSumGeometry
end
end FK.Adaptive
