/-
This file closes the common-upper good-intersection obligation on an explicit
right-disjoint compatible-cross class.  It is not a construction of the metric
exploration-region certificate and is not a whole-paper uniqueness theorem.
-/

import FK.NestedFiniteCoupling
import FK.NestedArbitraryInterior
import FK.TransportBoundary
import FK.RightWiredGood

/-!
# Coupled good intersections on maximal nested strata

This module transports exact exterior-fiber interior laws through finite
ordered pairs and the nested common-upper coupling. The main graph class is
an explicitly right-disjoint extension of a separated split graph. The left
boundary setoid is arbitrary; no good-intersection equality is assumed.
-/

open scoped ENNReal BigOperators Classical

namespace FK.Exploration.NestedCoupledGood

open scoped ENNReal BigOperators Classical

/-- General pair-fiber version of the second-marginal weighted-sum identity,
valid on the infinite history types used by sequential exploration. -/
lemma tsum_pair_weight_eq_of_map_snd_general
    {α β : Type*} (P Q : PMF (α × β)) (ν : PMF β)
    (hP : P.map Prod.snd = ν) (hQ : Q.map Prod.snd = ν)
    (F : β → ℝ≥0∞) :
    (∑' z : α × β, P z * F z.2) = ∑' z : α × β, Q z * F z.2 := by
  have fiber (R : PMF (α × β)) (hR : R.map Prod.snd = ν) (y : β) :
      (∑' x : α, R (x, y)) = ν y := by
    have h := congrArg (fun r : PMF β => r y) hR
    rw [PMF.map_apply] at h
    rw [ENNReal.tsum_prod'] at h
    have hterm (x : α) :
        (∑' y' : β, if y = (x, y').2 then R (x, y') else 0) = R (x, y) := by
      classical
      calc
        _ = ∑' y' : β, if y' = y then R (x, y') else 0 := by
          apply tsum_congr
          intro y'
          by_cases hy' : y' = y
          · subst y'; simp
          · have hy : y ≠ y' := Ne.symm hy'
            simp [hy', hy]
        _ = _ := by simp
    simp_rw [hterm] at h
    exact h
  have oneSide (R : PMF (α × β)) (hR : R.map Prod.snd = ν) :
      (∑' z : α × β, R z * F z.2) = ∑' y : β, ν y * F y := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    apply tsum_congr
    intro y
    change (∑' x : α, R (x, y) * F y) = ν y * F y
    rw [ENNReal.tsum_mul_right, fiber R hR y]
  exact (oneSide P hP).trans (oneSide Q hQ).symm

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.tsum_pair_weight_eq_of_map_snd_general


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.TwoSidedInterior
open FK.Exploration.NestedFiniteCoupling
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Finite.MarkovFactorization

/-- The normalizing mass of a product PMF on an event depending only on its
left coordinate is the normalizing mass of that event in the left law. -/
lemma tsum_indicator_independentProd_preimage_fst
    {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (E : Set α) :
    (∑' z, (Prod.fst ⁻¹' E).indicator (independentProd P Q) z) =
      ∑' a, E.indicator P a := by
  rw [tsum_fintype, tsum_fintype, Fintype.sum_prod_type]
  have hfactor (a : α) :
      (∑ b : β, (Prod.fst ⁻¹' E).indicator (independentProd P Q) (a, b)) =
        E.indicator P a := by
    by_cases ha : a ∈ E
    · have hQ : (∑ b, Q b) = 1 := by
        simpa only [tsum_fintype] using Q.tsum_coe
      simp [Set.indicator_apply, ha, independentProd_apply, ← Finset.mul_sum, hQ]
    · simp [Set.indicator_apply, ha]
  exact Finset.sum_congr rfl fun a _ => hfactor a

/-- Filtering an independent product on a left-coordinate event and then
projecting left is exactly filtering the left marginal. -/
theorem map_fst_filter_independentProd_preimage_fst
    {α β : Type*} [Fintype α] [Fintype β]
    (P : PMF α) (Q : PMF β) (E : Set α)
    (hP : ∃ a ∈ E, a ∈ P.support)
    (hPQ : ∃ z ∈ Prod.fst ⁻¹' E, z ∈ (independentProd P Q).support) :
    ((independentProd P Q).filter (Prod.fst ⁻¹' E) hPQ).map Prod.fst =
      P.filter E hP := by
  apply PMF.ext
  intro a
  rw [PMF.map_apply, tsum_fintype]
  have ha : (∑ z : α × β, if a = z.1 then
      (independentProd P Q).filter (Prod.fst ⁻¹' E) hPQ z else 0) =
      ∑ b : β, (independentProd P Q).filter (Prod.fst ⁻¹' E) hPQ (a, b) := by
    simp only [Fintype.sum_prod_type, Prod.fst]
    rw [Finset.sum_eq_single a]
    · simp
    · intro a' _ ha'
      simp [Ne.symm ha']
    · intro ha'
      simp at ha'
  rw [ha]
  simp only [PMF.filter_apply]
  rw [tsum_indicator_independentProd_preimage_fst P Q E]
  have hfactor :
      (∑ b : β, (Prod.fst ⁻¹' E).indicator (independentProd P Q) (a, b)) =
        E.indicator P a := by
    by_cases haE : a ∈ E
    · have hQ : (∑ b, Q b) = 1 := by
        simpa only [tsum_fintype] using Q.tsum_coe
      simp [Set.indicator_apply, haE, independentProd_apply, ← Finset.mul_sum, hQ]
    · simp [Set.indicator_apply, haE]
  rw [← Finset.sum_mul, hfactor]
/-- On a separated exterior, the lower sequential continuation of a
`twoSidedBoundary` law has the actual region FK law with the same arbitrary
left setoid. -/
theorem extendLower_exteriorHistory_eq_region_twoSided
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (ρ : Fin m ⊕ Fin k → Bool)
    (hsep : Separated si ti so xo (exteriorConfig ρ)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζ)
    let μ := T.fkPMF hq hp₁.le ξ
    (extendLower (canonicalNext μ (fkPMF_ne_zero T hq hp₀ hp₁ ξ))
      (exteriorHistory ρ) m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
  let T := transportedAmbient si ti so xo
  let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
    (twoSidedBoundary si ti so xo θ ζ)
  let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ
  let e : (Fin (k + m) → Bool) ≃ (Fin m ⊕ Fin k → Bool) :=
    toAmbientConfig si ti so xo
  have hμ := fkPMF_ne_zero T hq hp₀ hp₁ ξ
  have hlen : (exteriorHistory ρ).length + m = k + m := by
    simp [exteriorHistory]
  dsimp only
  rw [extendLower_canonicalNext μ hμ (exteriorHistory ρ) m hlen]
  let P := prefixCylinder (n := k + m) (exteriorHistory ρ)
  have hP : P = e ⁻¹' exteriorFiber (exteriorConfig ρ) := by
    ext y
    exact exteriorHistory_prefix_iff si ti so xo ρ y
  have htransport : μ.map e =
      G.fkPMF hq hp₁.le (twoSidedBoundary si ti so xo θ ζ) := by
    exact G.map_transport_fkPMF (Equiv.refl (U ⊕ K)) exteriorFirst
      (twoSidedBoundary si ti so xo θ ζ) hq hp₀ hp₁
  have hBactual : ∃ a ∈ exteriorFiber (exteriorConfig ρ),
      a ∈ (G.fkPMF hq hp₁.le (twoSidedBoundary si ti so xo θ ζ)).support := by
    rw [← normalizedPMF_eq_actual_fkPMF G (twoSidedBoundary si ti so xo θ ζ)
      hq hp₀ hp₁]
    exact FinitePlane.exteriorFiber_support _
      (fun σ => G.fkWeight_pos hq hp₀ hp₁ _ σ) (exteriorConfig ρ)
  have hB : ∃ a ∈ exteriorFiber (exteriorConfig ρ), a ∈ (μ.map e).support := by
    rw [htransport]
    exact hBactual
  have hfilter : (μ.filter P
      (prefixCylinder_support_of_positive μ hμ (exteriorHistory ρ) (by omega))).map e =
      (G.fkPMF hq hp₁.le (twoSidedBoundary si ti so xo θ ζ)).filter
        (exteriorFiber (exteriorConfig ρ)) hBactual := by
    simp only [hP]
    have hA : ∃ a ∈ e ⁻¹' exteriorFiber (exteriorConfig ρ), a ∈ μ.support := by
      rw [← hP]
      exact prefixCylinder_support_of_positive μ hμ (exteriorHistory ρ) (by omega)
    have h0 := map_filter_equiv e μ (exteriorFiber (exteriorConfig ρ)) hA hB
    simp only [htransport] at h0
    with_unfolding_all exact h0
  rw [PMF.map_comp]
  have hc : (fun y => interiorConfig ((toAmbientConfig si ti so xo)
      (toConfig (k + m) y))) ∘ List.ofFn =
      (interiorConfig (I := Fin m) (O := Fin k)) ∘ e := by
    funext ω
    change interiorConfig (e (toConfig (k + m) (List.ofFn ω))) = interiorConfig (e ω)
    rw [toConfig_ofFn]
  rw [hc, ← PMF.map_comp]
  with_unfolding_all rw [hfilter]
  rw [← filter_fkPMF_eq_map_glue_region_twoSided si ti so xo hq hp₀ hp₁
    θ ζ (exteriorConfig ρ) hsep]
  refine (PMF.map_comp _ _ _).trans ?_
  have hid : (interiorConfig (I := Fin m) (O := Fin k)) ∘
      (fun (ω : Fin m → Bool) => glue (I := Fin m) (O := Fin k) ω
        (exteriorConfig ρ)) = id := by
    funext ω
    rfl
  rw [hid]
  with_unfolding_all exact PMF.map_id _

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.map_fst_filter_independentProd_preimage_fst
#print axioms FK.Exploration.NestedCoupledGood.extendLower_exteriorHistory_eq_region_twoSided


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.TripleSequential
open FK.Exploration.FKCoupling FK.Exploration.StoppedInterior
open FK.Exploration.MaximalStrata FK.Exploration.TwoSidedInterior
open FK.Exploration.NestedFiniteCoupling
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open FK.Finite.MarkovFactorization
open scoped ENNReal BigOperators Classical

/-- The preceding two-sided continuation applies below every upper
configuration in the canonical maximal stratum. -/
theorem extendLower_exteriorHistory_eq_region_twoSided_of_le_outerRegion
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (ρ π : Fin m ⊕ Fin k → Bool)
    (hπρ : π ≤ ρ) (hright : ExteriorHasRight so xo)
    (hρ : ρ ∈ maximalSplitStratum si ti so xo) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζ)
    let μ := T.fkPMF hq hp₁.le ξ
    (extendLower (canonicalNext μ (fkPMF_ne_zero T hq hp₀ hp₁ ξ))
      (exteriorHistory π) m).map (fun y =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y))) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  apply extendLower_exteriorHistory_eq_region_twoSided si ti so xo hq hp₀ hp₁ θ ζ π
  exact separated_of_le_of_outerRegion si ti so xo ρ π hπρ hright hρ

/-- The block enumeration used to adjoin a right-disjoint graph to the
exterior-first small graph. -/
noncomputable def rightExtendedIndex {n : ℕ} (GO : LabelledMultigraph) :
    Fin (n + Fintype.card GO.Edge) ≃ Fin n ⊕ GO.Edge :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin n)) (Fintype.equivFin GO.Edge).symm)

/-- The finite-indexed graph obtained by adjoining `GO` on a fresh right
vertex summand. -/
noncomputable def rightExtendedGraph {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (GO : LabelledMultigraph) : LabelledMultigraph :=
  (disjointSum (finIndexedGraph V n s t) GO).transport (Equiv.refl _)
    (rightExtendedIndex GO)

/-- Split a configuration on the right-extended indexed graph into its small
and new-right coordinates. -/
noncomputable def splitRightExtendedConfig {V : Type*} [Fintype V] {n : ℕ}
    (s t : Fin n → V) (GO : LabelledMultigraph) :
    (rightExtendedGraph s t GO).Configuration ≃
      (Fin n → Bool) × GO.Configuration :=
  ((disjointSum (finIndexedGraph V n s t) GO).transportConfig (Equiv.refl _)
    (rightExtendedIndex GO)).trans (splitConfig (finIndexedGraph V n s t) GO)

/-- Restricting to the first coordinate-compressed block is the same as
restricting to the small indexed graph. -/
lemma splitRightExtendedConfig_fst_apply_castAdd
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph) (ω : (rightExtendedGraph s t GO).Configuration)
    (i : Fin n) :
    (splitRightExtendedConfig s t GO ω).1 i = ω (Fin.castAdd _ i) := by
  rfl

/-- A prefix cylinder on the extended graph is exactly the same prefix
cylinder on its small graph. -/
theorem prefixCylinder_rightExtended
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph) (x : List Bool) (hx : x.length ≤ n) :
    prefixCylinder (n := n + Fintype.card GO.Edge) x =
      (splitRightExtendedConfig s t GO) ⁻¹'
        (Prod.fst ⁻¹' prefixCylinder (n := n) x) := by
  classical
  ext ω
  change (x <+: List.ofFn ω ↔
    x <+: List.ofFn (splitRightExtendedConfig s t GO ω).1)
  constructor
  · intro h
    rw [List.prefix_iff_getElem] at h ⊢
    obtain ⟨hlen, hget⟩ := h
    refine ⟨by simpa using hx, ?_⟩
    intro i hi
    have hiT : i < n := lt_of_lt_of_le hi hx
    have hiN : i < n + Fintype.card GO.Edge := by omega
    have hv := hget i hi
    simp only [List.getElem_ofFn] at hv ⊢
    have hsplit := splitRightExtendedConfig_fst_apply_castAdd s t GO ω
      (⟨i, hiT⟩ : Fin n)
    calc
      x[i] = ω ⟨i, hiN⟩ := hv
      _ = ω (Fin.castAdd _ (⟨i, hiT⟩ : Fin n)) :=
        congrArg ω (Fin.ext rfl).symm
      _ = (splitRightExtendedConfig s t GO ω).1 ⟨i, hiT⟩ := hsplit.symm
  · intro h
    rw [List.prefix_iff_getElem] at h ⊢
    obtain ⟨hlen, hget⟩ := h
    have hxN : x.length ≤ n + Fintype.card GO.Edge := by omega
    refine ⟨by simpa using hxN, ?_⟩
    intro i hi
    have hiT : i < n := lt_of_lt_of_le hi hx
    have hiN : i < n + Fintype.card GO.Edge := by omega
    have hv := hget i hi
    simp only [List.getElem_ofFn] at hv ⊢
    have hsplit := splitRightExtendedConfig_fst_apply_castAdd s t GO ω
      (⟨i, hiT⟩ : Fin n)
    calc
      x[i] = (splitRightExtendedConfig s t GO ω).1 ⟨i, hiT⟩ := hv
      _ = ω (Fin.castAdd _ (⟨i, hiT⟩ : Fin n)) := hsplit
      _ = ω ⟨i, hiN⟩ := congrArg ω (Fin.ext rfl)

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.extendLower_exteriorHistory_eq_region_twoSided_of_le_outerRegion
#print axioms FK.Exploration.NestedCoupledGood.prefixCylinder_rightExtended


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior
open FK.Exploration.NestedFiniteCoupling
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Finite.MarkovFactorization
open scoped ENNReal BigOperators Classical

/-- The extended FK law splits exactly into the small FK law and the new
right FK law. -/
theorem map_splitRightExtendedConfig_fkPMF
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    (χ : GO.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1) :
    let G := disjointSum (finIndexedGraph V n s t) GO
    let j : Fin (n + Fintype.card GO.Edge) ≃ G.Edge := rightExtendedIndex GO
    let ζ : (rightExtendedGraph s t GO).BoundaryPartition :=
      G.transportBoundaryOf (Equiv.refl _) (eE := j) (sumBoundary ξ χ)
    PMF.map (splitRightExtendedConfig s t GO)
      ((rightExtendedGraph s t GO).fkPMF hq hp₁.le ζ) =
      independentProd ((finIndexedGraph V n s t).fkPMF hq hp₁.le ξ)
        (GO.fkPMF hq hp₁.le χ) := by
  intro G j ζ
  let μ := (rightExtendedGraph s t GO).fkPMF hq hp₁.le ζ
  change PMF.map (splitRightExtendedConfig s t GO) μ = _
  have hsplit : PMF.map (splitRightExtendedConfig s t GO) μ =
      PMF.map (splitConfig (finIndexedGraph V n s t) GO)
        (PMF.map (G.transportConfig (Equiv.refl _) j) μ) := by
    have he : (splitRightExtendedConfig s t GO :
        (rightExtendedGraph s t GO).Configuration → _) =
        (splitConfig (finIndexedGraph V n s t) GO) ∘
          (G.transportConfig (Equiv.refl _) j) := rfl
    rw [he]
    exact (PMF.map_comp (p := μ) (f := G.transportConfig (Equiv.refl _) j)
      (splitConfig (finIndexedGraph V n s t) GO)).symm
  have hmap : PMF.map (G.transportConfig (Equiv.refl _) j) μ =
      G.fkPMF hq hp₁.le (sumBoundary ξ χ) := by
    exact G.map_transport_fkPMF (Equiv.refl _) j (sumBoundary ξ χ) hq hp₀ hp₁
  rw [hsplit, hmap]
  exact map_splitConfig_fkPMF_disjointSum _ _ hq hp₁.le ξ χ

/-- After a small prefix, the continuation of the right-extended FK law has
exactly the filtered small FK law in its small coordinates. -/
theorem extendLower_rightExtended_map_fst
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph) (ξ : (finIndexedGraph V n s t).BoundaryPartition)
    (χ : GO.BoundaryPartition) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (x : List Bool) (hx : x.length ≤ n) :
    let T := finIndexedGraph V n s t
    let G := disjointSum T GO
    let j : Fin (n + Fintype.card GO.Edge) ≃ G.Edge := rightExtendedIndex GO
    let ζ : (rightExtendedGraph s t GO).BoundaryPartition :=
      G.transportBoundaryOf (Equiv.refl _) (eE := j) (sumBoundary ξ χ)
    let μS := T.fkPMF hq hp₁.le ξ
    let μO := GO.fkPMF hq hp₁.le χ
    let μ := (rightExtendedGraph s t GO).fkPMF hq hp₁.le ζ
    (extendLower (canonicalNext μ
      (fkPMF_ne_zero (rightExtendedGraph s t GO) hq hp₀ hp₁ ζ)) x
        (n - x.length + Fintype.card GO.Edge)).map (fun y =>
          (splitRightExtendedConfig s t GO
            (toConfig (n + Fintype.card GO.Edge) y)).1) =
      μS.filter (prefixCylinder x)
        (prefixCylinder_support_of_positive μS
          (fkPMF_ne_zero T hq hp₀ hp₁ ξ) x hx) := by
  intro T G j ζ μS μO μ
  let e := splitRightExtendedConfig s t GO
  let P : Set (Fin n → Bool) := prefixCylinder x
  let E : Set ((Fin n → Bool) × GO.Configuration) := Prod.fst ⁻¹' P
  have hμS : ∀ ω, μS ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ
  have hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero (rightExtendedGraph s t GO) hq hp₀ hp₁ ζ
  have hlen : x.length + (n - x.length + Fintype.card GO.Edge) =
      n + Fintype.card GO.Edge := by omega
  rw [extendLower_canonicalNext μ hμ x _ hlen]
  rw [PMF.map_comp]
  change PMF.map ((fun y => (e (toConfig (n + Fintype.card GO.Edge) y)).1) ∘
    List.ofFn) (μ.filter (prefixCylinder x) _) = _
  have hc : (fun y => (e (toConfig (n + Fintype.card GO.Edge) y)).1) ∘
      List.ofFn = (fun z => (e z).1) := by
    funext ω
    change (e (toConfig (n + Fintype.card GO.Edge) (List.ofFn ω))).1 = _
    rw [toConfig_ofFn]
  rw [hc]
  have hcomp : PMF.map (fun z => (e z).1)
      (μ.filter (prefixCylinder x)
        (prefixCylinder_support_of_positive μ hμ x (by omega))) =
    PMF.map Prod.fst ((μ.filter (prefixCylinder x)
      (prefixCylinder_support_of_positive μ hμ x (by omega))).map e) := by
    simpa only [Function.comp_def] using
      (PMF.map_comp (p := μ.filter (prefixCylinder x)
        (prefixCylinder_support_of_positive μ hμ x (by omega))) (f := e) Prod.fst).symm
  have hA : ∃ a ∈ prefixCylinder x, a ∈ μ.support :=
    prefixCylinder_support_of_positive μ hμ x (by omega)
  have hP : prefixCylinder (n := n + Fintype.card GO.Edge) x = e ⁻¹' E := by
    exact prefixCylinder_rightExtended s t GO x hx
  have hprod : μ.map e = independentProd μS μO := by
    exact map_splitRightExtendedConfig_fkPMF s t GO ξ χ hq hp₀ hp₁
  have hAe : ∃ a ∈ e ⁻¹' E, a ∈ μ.support := by
    rw [← hP]
    exact hA
  have hB : ∃ z ∈ E, z ∈ (μ.map e).support := by
    obtain ⟨a, ha, haμ⟩ := hAe
    refine ⟨e a, ha, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨a, haμ, rfl⟩
  have hBprod : ∃ z ∈ E, z ∈ (independentProd μS μO).support := by
    rw [← hprod]
    exact hB
  have hfilter : (μ.filter (prefixCylinder x)
      (prefixCylinder_support_of_positive μ hμ x (by omega))).map e =
      (independentProd μS μO).filter E hBprod := by
    have hf : (μ.filter (e ⁻¹' E) hAe).map e =
        (independentProd μS μO).filter E hBprod :=
      (map_filter_equiv e μ E hAe hB).trans
        (FK.Exploration.WiredRightInterior.pmf_filter_congr hprod E hB hBprod)
    simpa only [← hP] using hf
  exact hcomp.trans ((congrArg (PMF.map Prod.fst) hfilter).trans
    (map_fst_filter_independentProd_preimage_fst μS μO P
      (prefixCylinder_support_of_positive μS hμS x hx) hBprod))

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.map_splitRightExtendedConfig_fkPMF
#print axioms FK.Exploration.NestedCoupledGood.extendLower_rightExtended_map_fst


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior FK.Exploration.RightWiredGood
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open scoped ENNReal BigOperators Classical

/-- The filtered small configuration law itself has the exact region interior
law; no list-history decoding remains in the conclusion. -/
theorem filter_exteriorHistory_interior_twoSided_of_le
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (ρ π : Fin m ⊕ Fin k → Bool)
    (hπρ : π ≤ ρ) (hright : ExteriorHasRight so xo)
    (hρ : ρ ∈ maximalSplitStratum si ti so xo) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζ)
    let μ := T.fkPMF hq hp₁.le ξ
    (μ.filter (prefixCylinder (exteriorHistory π))
      (prefixCylinder_support_of_positive μ
        (fkPMF_ne_zero T hq hp₀ hp₁ ξ) (exteriorHistory π)
        (by simp [exteriorHistory]))).map (fun ω =>
          interiorConfig (toAmbientConfig si ti so xo ω)) =
      (regionGraph si ti).fkPMF hq hp₁.le θ := by
  intro G T ξ μ
  have hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ
  have h := extendLower_exteriorHistory_eq_region_twoSided_of_le_outerRegion
    si ti so xo hq hp₀ hp₁ θ ζ ρ π hπρ hright hρ
  dsimp only at h
  rw [extendLower_canonicalNext μ hμ (exteriorHistory π) m
    (by simp [exteriorHistory] : (exteriorHistory π).length + m = k + m)] at h
  rw [PMF.map_comp] at h
  have hc : (fun y => interiorConfig (toAmbientConfig si ti so xo
      (toConfig (k + m) y))) ∘ List.ofFn =
      (fun ω => interiorConfig (toAmbientConfig si ti so xo ω)) := by
    funext ω
    change interiorConfig (toAmbientConfig si ti so xo
      (toConfig (k + m) (List.ofFn ω))) = _
    rw [toConfig_ofFn]
  rw [hc] at h
  exact h

/-- Two finite pair laws with the same second marginal assign the same mass
to every weight depending only on that second coordinate. -/
lemma tsum_pair_weight_eq_of_map_snd
    {α β : Type*} [Fintype α] [Fintype β]
    (P Q : PMF (α × β)) (ν : PMF β)
    (hP : P.map Prod.snd = ν) (hQ : Q.map Prod.snd = ν)
    (F : β → ℝ≥0∞) :
    (∑' z : α × β, P z * F z.2) = ∑' z : α × β, Q z * F z.2 := by
  have fiber (R : PMF (α × β)) (hR : R.map Prod.snd = ν) (y : β) :
      (∑ x : α, R (x, y)) = ν y := by
    have h := congrArg (fun r : PMF β => r y) hR
    simpa [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      Finset.sum_ite_eq'] using h
  have oneSide (R : PMF (α × β)) (hR : R.map Prod.snd = ν) :
      (∑' z : α × β, R z * F z.2) = ∑' y : β, ν y * F y := by
    rw [tsum_fintype, Fintype.sum_prod_type, tsum_fintype]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    change (∑ x : α, R (x, y) * F y) = ν y * F y
    rw [← Finset.sum_mul, fiber R hR y]
  exact (oneSide P hP).trans (oneSide Q hQ).symm

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.filter_exteriorHistory_interior_twoSided_of_le
#print axioms FK.Exploration.NestedCoupledGood.tsum_pair_weight_eq_of_map_snd


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.FKCoupling
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.MarkovFactorization
open scoped Classical

theorem rightExtendedGraph_eq_finIndexed {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph) :
    rightExtendedGraph s t GO =
      finIndexedGraph (V ⊕ GO.Vertex) (n + Fintype.card GO.Edge)
        (rightExtendedGraph s t GO).source (rightExtendedGraph s t GO).target := by
  rfl

end FK.Exploration.NestedCoupledGood


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open scoped ENNReal BigOperators Classical

/-- One supported small lower/upper continuation has the actual region FK
law with arbitrary shared left setoid. -/
theorem pair_interior_continuation_twoSided
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (ρ : Fin m ⊕ Fin k → Bool)
    (hright : ExteriorHasRight so xo)
    (hρ : ρ ∈ maximalSplitStratum si ti so xo) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζ)
    let μ : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξ
    let hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξ
    let r := upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξ hq hp₀ hp₁ x
    let step := orderedUpperStep μ hμ r (upperRateNN_le_one hq hp₁.le) hbound
    ∀ {x y : List Bool}, (x, y) ∈ (extendPair step [] [] k).support →
      y = exteriorHistory ρ →
      (extendPair step x y m).map (fun z =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z.1))) =
        (regionGraph si ti).fkPMF hq hp₁.le θ := by
  intro G T ξ μ hμ r hbound step x y hxy hy
  have hfst : ∀ x y, (step x y).map Prod.fst = canonicalNext μ hμ x := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (upperRateNN_le_one hq hp₁.le) (hbound x)).map_fst
  have hordstep : ∀ x y z, z ∈ (step x y).support → z.1 ≤ z.2 := by
    intro x y w hw
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (upperRateNN_le_one hq hp₁.le) (hbound x)).ordered w hw
  have hlen := extendPair_length_support step [] [] k hxy
  have hord := extendPair_ordered step hordstep List.Forall₂.nil k hxy
  have hex : exteriorHistory (m := m) (ambientOfHistory x) = x :=
    exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.1)
  have hconf : toConfig k x ≤ exteriorConfig ρ := by
    have hc := toConfig_le_of_forall₂ (n := k) hord
    rw [hy] at hc
    simpa only [exteriorHistory, toConfig_ofFn, exteriorConfig, Function.comp_def] using hc
  have hmono : ambientOfHistory x ≤ ρ := by
    intro a
    cases a with
    | inl a => exact Bool.false_le _
    | inr a => exact hconf a
  calc
    (extendPair step x y m).map (fun z =>
        interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z.1))) =
        ((extendPair step x y m).map Prod.fst).map (fun z =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z))) := by
      rw [PMF.map_comp]
      rfl
    _ = (extendLower (canonicalNext μ hμ) x m).map (fun z =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z))) := by
      rw [extendPair_map_fst step (canonicalNext μ hμ) hfst]
    _ = (extendLower (canonicalNext μ hμ)
          (exteriorHistory (m := m) (ambientOfHistory x)) m).map (fun z =>
          interiorConfig (toAmbientConfig si ti so xo (toConfig (k + m) z))) := by
      rw [hex]
    _ = _ := by
      apply extendLower_exteriorHistory_eq_region_twoSided_of_le_outerRegion
        si ti so xo hq hp₀ hp₁ θ ζ ρ (ambientOfHistory x) hmono hright hρ

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.pair_interior_continuation_twoSided


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior FK.Exploration.NestedFiniteCoupling
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.Finite.MarkovFactorization FK.FinitePlane FK.FinitePlane.FreeInterior
open scoped ENNReal BigOperators Classical

/-- On an upper maximal exterior, the large right-extended lower
continuation has the same small region interior law as the smaller graph. -/
theorem pair_interior_continuation_rightExtended_twoSided
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζ : Setoid K) (χ : GO.BoundaryPartition)
    (ρ : Fin m ⊕ Fin k → Bool) (hright : ExteriorHasRight so xo)
    (hρ : ρ ∈ maximalSplitStratum si ti so xo) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let sT : Fin (k + m) → U ⊕ K := T.source
    let tT : Fin (k + m) → U ⊕ K := T.target
    let ξ : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζ)
    let L := rightExtendedGraph (V := U ⊕ K) sT tT GO
    let D := disjointSum (finIndexedGraph (U ⊕ K) (k + m) sT tT) GO
    let j : Fin (k + m + Fintype.card GO.Edge) ≃ D.Edge := rightExtendedIndex GO
    let ξL : L.BoundaryPartition := D.transportBoundaryOf (Equiv.refl _)
      (eE := j) (sumBoundary ξ χ)
    let μ : PMF (Fin (k + m + Fintype.card GO.Edge) → Bool) :=
      L.fkPMF hq hp₁.le ξL
    let hμ : ∀ ω, μ ω ≠ 0 := fkPMF_ne_zero L hq hp₀ hp₁ ξL
    let r := upperRateNN q p
    let hbound : ∀ x, (canonicalNext μ hμ x true).toReal ≤ (r : ℝ) :=
      fun x => fk_upper_nextBound _ _ ξL hq hp₀ hp₁ x
    let step := orderedUpperStep μ hμ r (upperRateNN_le_one hq hp₁.le) hbound
    ∀ {x y : List Bool}, (x, y) ∈ (extendPair step [] [] k).support →
      y = exteriorHistory ρ →
      (extendPair step x y (m + Fintype.card GO.Edge)).map (fun z =>
        interiorConfig (toAmbientConfig si ti so xo
          ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
            (toConfig (k + m + Fintype.card GO.Edge) z.1)).1))) =
        (regionGraph si ti).fkPMF hq hp₁.le θ := by
  intro G T sT tT ξ L D j ξL μ hμ r hbound step x y hxy hy
  have hfst : ∀ x y, (step x y).map Prod.fst = canonicalNext μ hμ x := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (upperRateNN_le_one hq hp₁.le) (hbound x)).map_fst
  have hordstep : ∀ x y z, z ∈ (step x y).support → z.1 ≤ z.2 := by
    intro x y w hw
    exact (boolOrderedCouplingOfLe (canonicalNext μ hμ x) r
      (upperRateNN_le_one hq hp₁.le) (hbound x)).ordered w hw
  have hlen := extendPair_length_support step [] [] k hxy
  have hord := extendPair_ordered step hordstep List.Forall₂.nil k hxy
  have hex : exteriorHistory (m := m) (ambientOfHistory x) = x :=
    exteriorHistory_ambientOfHistory (m := m) (by simpa using hlen.1)
  have hconf : toConfig k x ≤ exteriorConfig ρ := by
    have hc := toConfig_le_of_forall₂ (n := k) hord
    rw [hy] at hc
    simpa only [exteriorHistory, toConfig_ofFn, exteriorConfig, Function.comp_def] using hc
  have hmono : ambientOfHistory x ≤ ρ := by
    intro a
    cases a with
    | inl a => exact Bool.false_le _
    | inr a => exact hconf a
  have hx : x.length ≤ k + m := by have := hlen.1; simp at this ⊢; omega
  have hcont := extendLower_rightExtended_map_fst (V := U ⊕ K) sT tT GO ξ χ
    hq hp₀ hp₁ x hx
  have hremainder : k + m - x.length + Fintype.card GO.Edge =
      m + Fintype.card GO.Edge := by have := hlen.1; simp at this; omega
  dsimp only at hcont
  rw [hremainder] at hcont
  have hinterior := filter_exteriorHistory_interior_twoSided_of_le
    si ti so xo hq hp₀ hp₁ θ ζ ρ (ambientOfHistory x) hmono hright hρ
  dsimp only at hinterior
  simp only [hex] at hinterior
  let intS : (Fin (k + m) → Bool) → (Fin m → Bool) := fun ω =>
    interiorConfig (toAmbientConfig si ti so xo ω)
  calc
    (extendPair step x y (m + Fintype.card GO.Edge)).map (fun z =>
        interiorConfig (toAmbientConfig si ti so xo
          ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
            (toConfig (k + m + Fintype.card GO.Edge) z.1)).1))) =
        ((extendPair step x y (m + Fintype.card GO.Edge)).map Prod.fst).map
          (fun y => intS ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
            (toConfig (k + m + Fintype.card GO.Edge) y)).1)) := by
      rw [PMF.map_comp]
      rfl
    _ = (extendLower (canonicalNext μ hμ) x (m + Fintype.card GO.Edge)).map
          (fun y => intS ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
            (toConfig (k + m + Fintype.card GO.Edge) y)).1)) := by
      rw [extendPair_map_fst step (canonicalNext μ hμ) hfst]
    _ = ((extendLower (canonicalNext μ hμ) x (m + Fintype.card GO.Edge)).map
          (fun y => (splitRightExtendedConfig (V := U ⊕ K) sT tT GO
            (toConfig (k + m + Fintype.card GO.Edge) y)).1)).map intS := by
      rw [PMF.map_comp]
      rfl
    _ = ((T.fkPMF hq hp₁.le ξ).filter (prefixCylinder x)
          (prefixCylinder_support_of_positive (T.fkPMF hq hp₁.le ξ)
            (fkPMF_ne_zero T hq hp₀ hp₁ ξ) x hx)).map intS := by
      exact congrArg (fun P : PMF (Fin (k + m) → Bool) => P.map intS) hcont
    _ = _ := by
      with_unfolding_all exact hinterior

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.pair_interior_continuation_rightExtended_twoSided


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.RightWiredGood
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.FinitePlane FK.FinitePlane.FreeInterior
open scoped ENNReal BigOperators Classical

/-- Reading an exterior bit through the small block of the extended graph is
just reading the corresponding initial history bit. -/
lemma toAmbient_rightExtended_exterior_apply
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (sT tT : Fin (k + m) → U ⊕ K) (GO : LabelledMultigraph)
    (y : List Bool) (i : Fin k) :
    toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO
        (toConfig (k + m + Fintype.card GO.Edge) y)).1) (Sum.inr i) =
      y.getD i false := by
  rw [toAmbientConfig_inr]
  change ((splitRightExtendedConfig sT tT GO
    (toConfig (k + m + Fintype.card GO.Edge) y)).1) (Fin.castAdd m i) = _
  have h := splitRightExtendedConfig_fst_apply_castAdd sT tT GO
    (show (rightExtendedGraph sT tT GO).Configuration from
      toConfig (k + m + Fintype.card GO.Edge) y) (Fin.castAdd m i)
  exact h

/-- The small maximal event read through a right extension depends only on
its exposed exterior history. -/
theorem mem_maximal_rightExtended_iff_ambientOfHistory
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (sT tT : Fin (k + m) → U ⊕ K) (GO : LabelledMultigraph)
    (hright : ExteriorHasRight so xo) (y : List Bool) :
    toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO
        (toConfig (k + m + Fintype.card GO.Edge) y)).1) ∈
        maximalSplitStratum si ti so xo ↔
      ambientOfHistory (m := m) y ∈ maximalSplitStratum si ti so xo := by
  have hext : exteriorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO
        (toConfig (k + m + Fintype.card GO.Edge) y)).1)) =
      exteriorConfig (ambientOfHistory (m := m) y) := by
    funext i
    change toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO
        (toConfig (k + m + Fintype.card GO.Edge) y)).1) (Sum.inr i) = _
    rw [toAmbient_rightExtended_exterior_apply]
    rfl
  constructor
  · intro h
    exact mem_maximalSplitStratum_of_exterior_eq si ti so xo h hright hext.symm
  · intro h
    exact mem_maximalSplitStratum_of_exterior_eq si ti so xo h hright hext

/-- Map-measure evaluation in the direction used for the sequential decoders. -/
lemma toMeasure_map_pmf {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (P : PMF α) (E : Set β)
    (hf : Measurable f) (hE : MeasurableSet E) :
    (P.map f).toMeasure E = P.toMeasure (f ⁻¹' E) :=
  PMF.toMeasure_map_apply (p := P) (f := f) (s := E) hf hE

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.mem_maximal_rightExtended_iff_ambientOfHistory
#print axioms FK.Exploration.NestedCoupledGood.toMeasure_map_pmf


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential

/-- Sequential pair continuations retain both exposed histories. -/
theorem extendPair_prefix_support
    (step : List Bool → List Bool → PMF (Bool × Bool))
    (x y : List Bool) (n : ℕ) {z : List Bool × List Bool}
    (hz : z ∈ (extendPair step x y n).support) : x <+: z.1 ∧ y <+: z.2 := by
  induction n generalizing x y z with
  | zero =>
      have h : z = (x, y) := (PMF.mem_support_pure_iff _ _).mp hz
      subst z
      exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | succ n ih =>
      rw [extendPair, PMF.mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      obtain ⟨h₁, h₂⟩ := ih (x ++ [w.1]) (y ++ [w.2]) hz
      exact ⟨(List.prefix_append _ _).trans h₁,
        (List.prefix_append _ _).trans h₂⟩

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.extendPair_prefix_support


namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior FK.Exploration.RightWiredGood
open FK.Exploration.NestedFiniteCoupling
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.Finite.MarkovFactorization FK.FinitePlane FK.FinitePlane.FreeInterior
open scoped ENNReal BigOperators Classical

local instance : MeasurableSpace (List Bool × List Bool) := ⊤

/-- The good-intersection masses of the small and right-extended ordered
pairs agree. The two right setoids are independent. The comparison is by exterior-prefix summation. -/
theorem good_intersection_rightExtended_twoSided
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo) (A : Set (Fin m → Bool)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let sT : Fin (k + m) → U ⊕ K := T.source
    let tT : Fin (k + m) → U ⊕ K := T.target
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξR : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζL)
    let L := rightExtendedGraph (V := U ⊕ K) sT tT GO
    let D := disjointSum (finIndexedGraph (U ⊕ K) (k + m) sT tT) GO
    let j : Fin (k + m + Fintype.card GO.Edge) ≃ D.Edge := rightExtendedIndex GO
    let ξL : L.BoundaryPartition := D.transportBoundaryOf (Equiv.refl _)
      (eE := j) (sumBoundary ξR χ)
    let μS : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξS
    let hμS : ∀ ω, μS ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξS
    let hboundS : ∀ x, (canonicalNext μS hμS x true).toReal ≤
        (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ ξS hq hp₀ hp₁ x
    let stepS := orderedUpperStep μS hμS (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) hboundS
    let μL : PMF (Fin (k + m + Fintype.card GO.Edge) → Bool) :=
      L.fkPMF hq hp₁.le ξL
    let hμL : ∀ ω, μL ω ≠ 0 := fkPMF_ne_zero L hq hp₀ hp₁ ξL
    let hboundL : ∀ x, (canonicalNext μL hμL x true).toReal ≤
        (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ ξL hq hp₀ hp₁ x
    let stepL := orderedUpperStep μL hμL (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) hboundL
    let EL : Set (List Bool × List Bool) :=
      {w | interiorConfig (toAmbientConfig si ti so xo
        ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
          (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A} ∩
      {w | toAmbientConfig si ti so xo
        ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
          (toConfig (k + m + Fintype.card GO.Edge) w.2)).1) ∈
          maximalSplitStratum si ti so xo}
    let ES : Set (List Bool × List Bool) :=
      {w | interiorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.1)) ∈ A} ∩
      {w | toAmbientConfig si ti so xo (toConfig (k + m) w.2) ∈
        maximalSplitStratum si ti so xo}
    (extendPair stepL [] [] (k + m + Fintype.card GO.Edge)).toMeasure EL =
      (extendPair stepS [] [] (k + m)).toMeasure ES := by
  intro G T sT tT ξS ξR L D j ξL μS hμS hboundS stepS μL hμL hboundL stepL EL ES
  let pfxS := extendPair stepS [] [] k
  let pfxL := extendPair stepL [] [] k
  let remS : List Bool × List Bool → PMF (List Bool × List Bool) := fun z =>
    extendPair stepS z.1 z.2 m
  let remL : List Bool × List Bool → PMF (List Bool × List Bool) := fun z =>
    extendPair stepL z.1 z.2 (m + Fintype.card GO.Edge)
  let free : PMF (Fin m → Bool) := (regionGraph si ti).fkPMF hq hp₁.le θ
  let F : List Bool → ℝ≥0∞ := fun y =>
    if ambientOfHistory (m := m) y ∈ maximalSplitStratum si ti so xo then
      free.toMeasure A else 0
  have hdecompS : extendPair stepS [] [] (k + m) = pfxS.bind remS := by
    exact extendPair_add stepS [] [] k m
  have hdecompL : extendPair stepL [] [] (k + m + Fintype.card GO.Edge) =
      pfxL.bind remL := by
    simpa only [pfxL, remL, Nat.add_assoc] using
      extendPair_add stepL [] [] k (m + Fintype.card GO.Edge)
  rw [hdecompL, hdecompS,
    PMF.toMeasure_bind_apply _ _ EL MeasurableSet.of_discrete,
    PMF.toMeasure_bind_apply _ _ ES MeasurableSet.of_discrete]
  have hS (z : List Bool × List Bool) :
      pfxS z * (remS z).toMeasure ES = pfxS z * F z.2 := by
    by_cases hz : z ∈ pfxS.support
    · have hlen := extendPair_length_support stepS [] [] k hz
      let ρ : Fin m ⊕ Fin k → Bool := ambientOfHistory (m := m) (k := k) z.2
      have hy : z.2 = exteriorHistory ρ := by
        exact (exteriorHistory_ambientOfHistory (m := m)
          (by simpa using hlen.2)).symm
      have hpre {w : List Bool × List Bool} (hw : w ∈ (remS z).support) :
          z.1 <+: w.1 ∧ z.2 <+: w.2 :=
        extendPair_prefix_support stepS z.1 z.2 m hw
      by_cases hM : ambientOfHistory (m := m) z.2 ∈ maximalSplitStratum si ti so xo
      · have hcont : (remS z).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1))) = free := by
          have h := pair_interior_continuation_twoSided si ti so xo hq hp₀ hp₁
            θ ζS ρ hright hM (x := z.1) (y := z.2)
          exact h hz hy
        have hstable : ∀ w ∈ (remS z).support,
            (w ∈ ES ↔ interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1)) ∈ A) := by
          intro w hw
          have hpref := hpre hw |>.2
          have heq := ambientOfHistory_eq_of_prefix (m := m)
            (by simpa using hlen.2) hpref
          have hg : toAmbientConfig si ti so xo (toConfig (k + m) w.2) ∈
              maximalSplitStratum si ti so xo := by
            apply (toAmbient_toConfig_mem_maximal_iff si ti so xo hright w.2).2
            rw [← heq]
            exact hM
          exact ⟨fun h => h.1, fun h => ⟨h, hg⟩⟩
        calc
          pfxS z * (remS z).toMeasure ES = pfxS z * (remS z).toMeasure
              {w | interiorConfig (toAmbientConfig si ti so xo
                (toConfig (k + m) w.1)) ∈ A} := by
            rw [pmf_toMeasure_eq_of_support (remS z) ES _ hstable]
            rfl
          _ = pfxS z * ((remS z).map (fun w =>
              interiorConfig (toAmbientConfig si ti so xo
                (toConfig (k + m) w.1)))).toMeasure A := by
            rw [toMeasure_map_pmf _ _ _ measurable_from_top MeasurableSet.of_discrete]
            rfl
          _ = pfxS z * free.toMeasure A := by rw [hcont]
          _ = pfxS z * F z.2 := by simp [F, hM]
      · have hzero : (remS z).toMeasure ES = 0 := by
          calc
            (remS z).toMeasure ES = (remS z).toMeasure ∅ := by
              apply pmf_toMeasure_eq_of_support
              intro w hw
              have hpref := hpre hw |>.2
              have heq := ambientOfHistory_eq_of_prefix (m := m)
                (by simpa using hlen.2) hpref
              constructor
              · intro h
                have hg := h.2
                have hg' := (toAmbient_toConfig_mem_maximal_iff si ti so xo
                  hright w.2).1 hg
                rw [← heq] at hg'
                exact (hM hg').elim
              · intro h; exact h.elim
            _ = 0 := by simp
        simp [hzero, F, hM]
    · have hz0 : pfxS z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
      simp [hz0]
  have hL (z : List Bool × List Bool) :
      pfxL z * (remL z).toMeasure EL = pfxL z * F z.2 := by
    by_cases hz : z ∈ pfxL.support
    · have hlen := extendPair_length_support stepL [] [] k hz
      let ρ : Fin m ⊕ Fin k → Bool := ambientOfHistory (m := m) (k := k) z.2
      have hy : z.2 = exteriorHistory ρ := by
        exact (exteriorHistory_ambientOfHistory (m := m)
          (by simpa using hlen.2)).symm
      have hpre {w : List Bool × List Bool} (hw : w ∈ (remL z).support) :
          z.1 <+: w.1 ∧ z.2 <+: w.2 :=
        extendPair_prefix_support stepL z.1 z.2 (m + Fintype.card GO.Edge) hw
      by_cases hM : ambientOfHistory (m := m) z.2 ∈ maximalSplitStratum si ti so xo
      · have hcont : (remL z).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.1)).1))) = free := by
          have h := pair_interior_continuation_rightExtended_twoSided si ti so xo
            GO hq hp₀ hp₁ θ ζL χ ρ hright hM (x := z.1) (y := z.2)
          exact h hz hy
        have hstable : ∀ w ∈ (remL z).support,
            (w ∈ EL ↔ interiorConfig (toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A) := by
          intro w hw
          have hpref := hpre hw |>.2
          have heq := ambientOfHistory_eq_of_prefix (m := m)
            (by simpa using hlen.2) hpref
          have hg : toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.2)).1) ∈
                maximalSplitStratum si ti so xo := by
            apply (mem_maximal_rightExtended_iff_ambientOfHistory si ti so xo
              sT tT GO hright w.2).2
            rw [← heq]
            exact hM
          exact ⟨fun h => h.1, fun h => ⟨h, hg⟩⟩
        calc
          pfxL z * (remL z).toMeasure EL = pfxL z * (remL z).toMeasure
              {w | interiorConfig (toAmbientConfig si ti so xo
                ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                  (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A} := by
            rw [pmf_toMeasure_eq_of_support (remL z) EL _ hstable]
            rfl
          _ = pfxL z * ((remL z).map (fun w =>
              interiorConfig (toAmbientConfig si ti so xo
                ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                  (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)))).toMeasure A := by
            rw [toMeasure_map_pmf _ _ _ measurable_from_top MeasurableSet.of_discrete]
            rfl
          _ = pfxL z * free.toMeasure A := by rw [hcont]
          _ = pfxL z * F z.2 := by simp [F, hM]
      · have hzero : (remL z).toMeasure EL = 0 := by
          calc
            (remL z).toMeasure EL = (remL z).toMeasure ∅ := by
              apply pmf_toMeasure_eq_of_support
              intro w hw
              have hpref := hpre hw |>.2
              have heq := ambientOfHistory_eq_of_prefix (m := m)
                (by simpa using hlen.2) hpref
              constructor
              · intro h
                have hg := h.2
                have hg' := (mem_maximal_rightExtended_iff_ambientOfHistory
                  si ti so xo sT tT GO hright w.2).1 hg
                rw [← heq] at hg'
                exact (hM hg').elim
              · intro h; exact h.elim
            _ = 0 := by simp
        simp [hzero, F, hM]
    · have hz0 : pfxL z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
      simp [hz0]
  let ν := extendLower (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le)) [] k
  have hsndS : ∀ x y, (stepS x y).map Prod.snd =
      FKModel.bernoulliPMF (upperRateNN q p) (upperRateNN_le_one hq hp₁.le) := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μS hμS x) (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) (hboundS x)).map_snd
  have hsndL : ∀ x y, (stepL x y).map Prod.snd =
      FKModel.bernoulliPMF (upperRateNN q p) (upperRateNN_le_one hq hp₁.le) := by
    intro x y
    exact (boolOrderedCouplingOfLe (canonicalNext μL hμL x) (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) (hboundL x)).map_snd
  have hpS : pfxS.map Prod.snd = ν := by
    exact extendPair_map_snd stepS
      (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)) hsndS [] [] k
  have hpL : pfxL.map Prod.snd = ν := by
    exact extendPair_map_snd stepL
      (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)) hsndL [] [] k
  calc
    (∑' z, pfxL z * (remL z).toMeasure EL) = ∑' z, pfxL z * F z.2 :=
      tsum_congr hL
    _ = ∑' z, pfxS z * F z.2 := tsum_pair_weight_eq_of_map_snd_general pfxL pfxS ν hpL hpS F
    _ = ∑' z, pfxS z * (remS z).toMeasure ES := (tsum_congr hS).symm

end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.good_intersection_rightExtended_twoSided


open scoped ENNReal BigOperators Classical

namespace FK.Exploration.NestedCoupledGood

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior FK.Exploration.RightWiredGood
open FK.Exploration.NestedFiniteCoupling
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.Finite.MarkovFactorization FK.FinitePlane FK.FinitePlane.FreeInterior

lemma orderedCoupling_dist_of_eq_mp {α : Type*} [LE α] {μ ν ν' : PMF α}
    (h : ν = ν') (c : PMF.OrderedCoupling μ ν') :
    (by rw [h]; exact c : PMF.OrderedCoupling μ ν).dist = c.dist := by
  cases h
  rfl

lemma splitRightExtendedConfig_configEquiv_apply
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph)
    (z : (finIndexedGraph V n s t).Configuration × GO.Configuration) :
    splitRightExtendedConfig s t GO
      (configEquiv (rightExtendedIndex (n := n) GO).symm z) = z := by
  apply Prod.ext
  · change restrictΔ (GS := rightExtendedGraph s t GO)
      (GD := finIndexedGraph V n s t) (rightExtendedIndex (n := n) GO).symm
        (configEquiv (rightExtendedIndex (n := n) GO).symm z) = z.1
    exact restrictΔ_configEquiv _ _
  · change restrictO (GS := rightExtendedGraph s t GO)
      (GD := finIndexedGraph V n s t) (rightExtendedIndex (n := n) GO).symm
        (configEquiv (rightExtendedIndex (n := n) GO).symm z) = z.2
    exact restrictO_configEquiv _ _

lemma restrictΔ_rightExtended_eq_fst
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph)
    (ω : (rightExtendedGraph s t GO).Configuration) :
    restrictΔ (GS := rightExtendedGraph s t GO)
      (GD := finIndexedGraph V n s t) (rightExtendedIndex (n := n) GO).symm ω =
      (splitRightExtendedConfig s t GO ω).1 := by
  rfl

lemma restrictO_rightExtended_eq_snd
    {V : Type*} [Fintype V] {n : ℕ} (s t : Fin n → V)
    (GO : LabelledMultigraph)
    (ω : (rightExtendedGraph s t GO).Configuration) :
    restrictO (GS := rightExtendedGraph s t GO)
      (GD := finIndexedGraph V n s t) (rightExtendedIndex (n := n) GO).symm ω =
      (splitRightExtendedConfig s t GO ω).2 := by
  rfl

local instance : MeasurableSpace (List Bool × List Bool) := ⊤

/-- The good-intersection identity for actual graph-configuration pairs on a
right-disjoint extension. The two right boundary setoids are independent. -/
theorem good_intersection_rightExtended_pairs_twoSided
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo) (A : Set (Fin m → Bool)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let sT : Fin (k + m) → U ⊕ K := T.source
    let tT : Fin (k + m) → U ⊕ K := T.target
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξR : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζL)
    let L := rightExtendedGraph (V := U ⊕ K) sT tT GO
    let D := disjointSum (finIndexedGraph (U ⊕ K) (k + m) sT tT) GO
    let j : Fin (k + m + Fintype.card GO.Edge) ≃ D.Edge := rightExtendedIndex GO
    let ξL : L.BoundaryPartition := D.transportBoundaryOf (Equiv.refl _)
      (eE := j) (sumBoundary ξR χ)
    let e : T.Edge ⊕ GO.Edge ≃ L.Edge := (rightExtendedIndex GO).symm
    let B : Set L.Configuration := {ω | interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO ω).1)) ∈ A}
    let AD : Set T.Configuration := {ω |
      interiorConfig (toAmbientConfig si ti so xo ω) ∈ A}
    let C : Set T.Configuration := {ω |
      toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
    (fkUpperPair L.source L.target ξL hq hp₀ hp₁).toMeasure
      (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) =
    (fkUpperPair sT tT ξS hq hp₀ hp₁).toMeasure
      (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
  intro G T sT tT ξS ξR L D j ξL e B AD C
  let N := k + m + Fintype.card GO.Edge
  let decodeL : List Bool × List Bool → L.Configuration × L.Configuration :=
    fun w => (toConfig N w.1, toConfig N w.2)
  let decodeS : List Bool × List Bool → T.Configuration × T.Configuration :=
    fun w => (toConfig (k + m) w.1, toConfig (k + m) w.2)
  let EL : Set (List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO (toConfig N w.1)).1)) ∈ A} ∩
    {w | toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO (toConfig N w.2)).1) ∈
        maximalSplitStratum si ti so xo}
  let ES : Set (List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo
      (toConfig (k + m) w.1)) ∈ A} ∩
    {w | toAmbientConfig si ti so xo (toConfig (k + m) w.2) ∈
      maximalSplitStratum si ti so xo}
  let μS : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξS
  let hμS : ∀ ω, μS ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξS
  let hboundS : ∀ x, (canonicalNext μS hμS x true).toReal ≤
      (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ ξS hq hp₀ hp₁ x
  let μL : PMF (Fin N → Bool) := L.fkPMF hq hp₁.le ξL
  let hμL : ∀ ω, μL ω ≠ 0 := fkPMF_ne_zero L hq hp₀ hp₁ ξL
  let hboundL : ∀ x, (canonicalNext μL hμL x true).toReal ≤
      (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ ξL hq hp₀ hp₁ x
  let histS := upperHistoryPair μS hμS (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) hboundS (k + m)
  let histL := upperHistoryPair μL hμL (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) hboundL N
  have h := good_intersection_rightExtended_twoSided si ti so xo GO hq hp₀ hp₁
    θ ζS ζL χ hright A
  have hL : decodeL ⁻¹' (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) = EL := by
    ext w
    change (interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO (toConfig N w.1)).1)) ∈ A ∧
      toAmbientConfig si ti so xo (restrictΔ e (toConfig N w.2)) ∈
        maximalSplitStratum si ti so xo) ↔ _
    have heq : toAmbientConfig si ti so xo (restrictΔ e (toConfig N w.2)) =
        toAmbientConfig si ti so xo
          ((splitRightExtendedConfig sT tT GO (toConfig N w.2)).1) := by
      dsimp only [e]
      exact congrArg (toAmbientConfig si ti so xo)
        (restrictΔ_rightExtended_eq_fst sT tT GO (toConfig N w.2))
    rw [heq]
    rfl
  have hS : decodeS ⁻¹' (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) = ES := by
    rfl
  have hmapL : histL.map decodeL = fkUpperPair L.source L.target ξL hq hp₀ hp₁ := by
    rfl
  have hmapS : histS.map decodeS = fkUpperPair sT tT ξS hq hp₀ hp₁ := by
    rfl
  calc
    (fkUpperPair L.source L.target ξL hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) =
        histL.toMeasure (decodeL ⁻¹'
          (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C))) := by
      rw [← hmapL]
      exact toMeasure_map_pmf decodeL histL _ measurable_from_top MeasurableSet.of_discrete
    _ = histL.toMeasure EL := by rw [hL]
    _ = histS.toMeasure ES := by
      with_unfolding_all exact h
    _ = histS.toMeasure (decodeS ⁻¹' (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C)) := by rw [hS]
    _ = (fkUpperPair sT tT ξS hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C) := by
      rw [← hmapS]
      exact (toMeasure_map_pmf decodeS histS _ measurable_from_top MeasurableSet.of_discrete).symm


/-- **Common-upper good intersection for the actual nested ordered triple** on
an explicitly right-disjoint two-sided split. No equality of good events is
assumed: it is transported from the two exact pair laws and their common
interior continuation. -/
theorem fkNestedOrderedTriple_good_rightExtended_twoSided
    {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo) (A : Set (Fin m → Bool)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let sT : Fin (k + m) → U ⊕ K := T.source
    let tT : Fin (k + m) → U ⊕ K := T.target
    let ξS : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζS)
    let ξR : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζL)
    let L := rightExtendedGraph (V := U ⊕ K) sT tT GO
    let D := disjointSum (finIndexedGraph (U ⊕ K) (k + m) sT tT) GO
    let j : Fin (k + m + Fintype.card GO.Edge) ≃ D.Edge := rightExtendedIndex GO
    let ξL : L.BoundaryPartition := D.transportBoundaryOf (Equiv.refl _)
      (eE := j) (sumBoundary ξR χ)
    let e : T.Edge ⊕ GO.Edge ≃ L.Edge := (rightExtendedIndex GO).symm
    let B : Set L.Configuration := {ω | interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO ω).1)) ∈ A}
    let AD : Set T.Configuration := {ω |
      interiorConfig (toAmbientConfig si ti so xo ω) ∈ A}
    let C : Set T.Configuration := {ω |
      toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
    let t := fkNestedOrderedTriple L.source L.target sT tT GO e ξL ξS hq hp₀ hp₁
    t.dist.toMeasure
      ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
    t.dist.toMeasure
      ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) := by
  intro G T sT tT ξS ξR L D j ξL e B AD C t
  let ρO := GO.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)
  let hsplit : splitLaw e (T.bernoulliProductPMF
      (upperRateNN_le_one hq hp₁.le)) ρO =
      L.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le) :=
    splitLaw_bernoulliProductPMF e (upperRateNN_le_one hq hp₁.le)
  let cS : PMF.OrderedCoupling (L.fkPMF hq hp₁.le ξL)
      (splitLaw e (T.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)) ρO) := by
    rw [hsplit]
    exact fkUpperOrderedCoupling L.source L.target ξL hq hp₀ hp₁
  let cΔ := fkUpperOrderedCoupling sT tT ξS hq hp₀ hp₁
  let cO := extendOrderedCoupling e cΔ ρO
  let eventL : Set (L.Configuration × L.Configuration) :=
    Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)
  let eventD : Set (T.Configuration × T.Configuration) :=
    Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C
  let smallPair : L.Configuration × L.Configuration →
      T.Configuration × T.Configuration :=
    fun z => (restrictΔ e z.1, restrictΔ e z.2)
  have hB : B = restrictΔ e ⁻¹' AD := by
    ext ω
    change interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO ω).1)) ∈ A ↔
        interiorConfig (toAmbientConfig si ti so xo (restrictΔ e ω)) ∈ A
    have he : restrictΔ e ω = (splitRightExtendedConfig sT tT GO ω).1 := by
      exact restrictΔ_rightExtended_eq_fst sT tT GO ω
    rw [he]
  have hrestrict : smallPair ⁻¹' eventD = eventL := by
    ext z
    change (z.1 ∈ restrictΔ e ⁻¹' AD ∧ z.2 ∈ restrictΔ e ⁻¹' C) ↔
      (z.1 ∈ B ∧ z.2 ∈ restrictΔ e ⁻¹' C)
    rw [← hB]
  have hcSdist : cS.dist = fkUpperPair L.source L.target ξL hq hp₀ hp₁ := by
    exact orderedCoupling_dist_of_eq_mp hsplit
      (fkUpperOrderedCoupling L.source L.target ξL hq hp₀ hp₁)
  have hpairs : cS.dist.toMeasure eventL = cΔ.dist.toMeasure eventD := by
    rw [hcSdist]
    exact good_intersection_rightExtended_pairs_twoSided si ti so xo GO hq hp₀ hp₁
      θ ζS ζL χ hright A
  have hfstthd : t.dist.map (fun z => (z.1, z.2.2)) = cS.dist := by
    with_unfolding_all exact PMF.Coupling.map_glueDist_fst_thd cS.toCoupling cO.toCoupling
  have hsndthd : t.dist.map (fun z => (z.2.1, z.2.2)) = cO.dist := by
    with_unfolding_all exact PMF.Coupling.map_glueDist_snd_thd cS.toCoupling cO.toCoupling
  have hsmall : cO.dist.map smallPair = cΔ.dist := by
    exact extendPairDist_map_restrictΔ_pair e cΔ ρO
  calc
    t.dist.toMeasure
        ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
        (t.dist.map (fun z => (z.1, z.2.2))).toMeasure eventL := by
      change t.dist.toMeasure ((fun z => (z.1, z.2.2)) ⁻¹' eventL) = _
      exact (toMeasure_map_pmf (fun z : L.Configuration × L.Configuration × L.Configuration =>
        (z.1, z.2.2)) t.dist eventL (measurable_of_finite _) MeasurableSet.of_discrete).symm
    _ = cS.dist.toMeasure eventL := by rw [hfstthd]; rfl
    _ = cΔ.dist.toMeasure eventD := hpairs
    _ = (cO.dist.map smallPair).toMeasure eventD := by rw [hsmall]; rfl
    _ = cO.dist.toMeasure (smallPair ⁻¹' eventD) := by
      exact toMeasure_map_pmf _ _ _ (measurable_of_finite _) MeasurableSet.of_discrete
    _ = cO.dist.toMeasure eventL := by rw [hrestrict]
    _ = (t.dist.map (fun z => (z.2.1, z.2.2))).toMeasure eventL := by rw [hsndthd]; rfl
    _ = t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) := by
      change (t.dist.map (fun z => (z.2.1, z.2.2))).toMeasure eventL =
        t.dist.toMeasure ((fun z => (z.2.1, z.2.2)) ⁻¹' eventL)
      exact toMeasure_map_pmf (fun z : L.Configuration × L.Configuration × L.Configuration =>
        (z.2.1, z.2.2)) t.dist eventL (measurable_of_finite _) MeasurableSet.of_discrete


end FK.Exploration.NestedCoupledGood

#print axioms FK.Exploration.NestedCoupledGood.splitRightExtendedConfig_configEquiv_apply
#print axioms FK.Exploration.NestedCoupledGood.restrictΔ_rightExtended_eq_fst
#print axioms FK.Exploration.NestedCoupledGood.restrictO_rightExtended_eq_snd
#print axioms FK.Exploration.NestedCoupledGood.good_intersection_rightExtended_pairs_twoSided
#print axioms FK.Exploration.NestedCoupledGood.fkNestedOrderedTriple_good_rightExtended_twoSided
#print axioms FK.Exploration.NestedCoupledGood.orderedCoupling_dist_of_eq_mp
#print axioms FK.Exploration.NestedCoupledGood.tsum_indicator_independentProd_preimage_fst
#print axioms FK.Exploration.NestedCoupledGood.rightExtendedIndex
#print axioms FK.Exploration.NestedCoupledGood.rightExtendedGraph
#print axioms FK.Exploration.NestedCoupledGood.splitRightExtendedConfig
#print axioms FK.Exploration.NestedCoupledGood.splitRightExtendedConfig_fst_apply_castAdd
#print axioms FK.Exploration.NestedCoupledGood.rightExtendedGraph_eq_finIndexed
#print axioms FK.Exploration.NestedCoupledGood.toAmbient_rightExtended_exterior_apply
