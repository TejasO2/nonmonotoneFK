/-
# Good intersections on exterior-refined strata

The accepted `fkNestedOrderedTriple_good_rightExtended_twoSided` proves the
common-upper good-intersection identity on the *maximal* split stratum of the
upper configuration.  The source (Lemma 2.1, item (3)) conditions instead on
the maximal closed cutset `M` of the upper configuration, i.e. on a stratum
that refines the no-connection event and is read off the exterior part of the
upper configuration only.

This file proves the corresponding refinement: the identity holds with the
third-coordinate event restricted to any set `E` of separated exterior
configurations, not only the whole set of them.  The maximal-stratum theorem is
the special case `E = {e | Separated si ti so xo e}`.
-/

import FK.NestedCommonUpperGood

open scoped ENNReal BigOperators Classical

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace FK.Exploration.RefinedStrata

open FK.Exploration.Sequential FK.Exploration.FKCoupling
open FK.Exploration.StoppedInterior FK.Exploration.MaximalStrata
open FK.Exploration.TwoSidedInterior FK.Exploration.RightWiredGood
open FK.Exploration.NestedFiniteCoupling FK.Exploration.NestedCoupledGood
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Exploration
open FK.Finite.MarkovFactorization FK.FinitePlane FK.FinitePlane.FreeInterior

local instance : MeasurableSpace (List Bool × List Bool) := ⊤

variable {U K : Type*} [Fintype U] [Fintype K] {m k : ℕ}

/-- Exterior configurations whose open labels avoid the region.  This is
exactly the set on which the maximal split stratum is detected
(`mem_maximalSplitStratum_iff`). -/
def SepExt (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K) :
    Set (Fin k → Bool) :=
  {e | Separated si ti so xo e}

/-- No element of the right summand is a left vertex. -/
lemma sum_inr_notMem_range_inl (k : K) :
    (Sum.inr k : U ⊕ K) ∉ Set.range (Sum.inl : U → U ⊕ K) := by
  rintro ⟨u, hu⟩
  cases hu

/-- **Non-vacuity of the refined class.**  When every exterior label has its
right endpoint in the exterior summand, every exterior configuration is
separated, so `SepExt` is everything and *arbitrary* subsets of the exterior
configurations are admissible external strata.  The refinement is therefore not
a restriction to a degenerate family. -/
theorem sepExt_eq_univ_of_right
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (hso : ∀ o, so o ∈ Set.range (Sum.inr : K → U ⊕ K))
    (hxo : ∀ o, xo o ∈ Set.range (Sum.inr : K → U ⊕ K)) :
    SepExt si ti so xo = Set.univ := by
  ext e
  constructor
  · intro _; trivial
  · intro _ o _
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨k, hk⟩ := hso o
      exact sum_inr_notMem_range_inl k ⟨u, hu.trans hk.symm⟩
    · rintro ⟨u, hu⟩
      obtain ⟨k, hk⟩ := hxo o
      exact sum_inr_notMem_range_inl k ⟨u, hu.trans hk.symm⟩

/-- An ambient configuration whose exterior part is separated belongs to the
maximal split stratum. -/
theorem mem_maximalSplitStratum_of_exterior_mem
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (hright : ExteriorHasRight so xo) {E : Set (Fin k → Bool)}
    (hE : E ⊆ SepExt si ti so xo) {ρ : Fin m ⊕ Fin k → Bool}
    (h : exteriorConfig ρ ∈ E) :
    ρ ∈ maximalSplitStratum si ti so xo := by
  rw [mem_maximalSplitStratum_iff _ _ _ _ _ hright]
  exact hE h

/-- The exterior part of the decoded ambient configuration of a short history is
the next-bit configuration of that history. -/
lemma exteriorConfig_toAmbientConfig_toConfig
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (y : List Bool) :
    exteriorConfig (toAmbientConfig si ti so xo (toConfig (k + m) y)) =
      toConfig k y := by
  funext i
  change toAmbientConfig si ti so xo (toConfig (k + m) y) (Sum.inr i) = _
  rw [toAmbientConfig_inr]
  rfl

/-- The exterior part of `ambientOfHistory` is the next-bit configuration. -/
lemma exteriorConfig_ambientOfHistory {m k : ℕ} (y : List Bool) :
    exteriorConfig (ambientOfHistory (m := m) (k := k) y) = toConfig k y := rfl

/-- **Good intersection on an exterior-refined stratum.**  The upper
configuration is restricted to the event that its exterior part avoids the
region layout, i.e. to a cutset stratum; the identity is the maximal-stratum
identity for the special case `E = SepExt`. -/
theorem good_intersection_exteriorStratum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo)
    (E : Set (Fin k → Bool)) (hE : E ⊆ SepExt si ti so xo)
    (A : Set (Fin m → Bool)) :
    let G := ambientOfSum (splitSource si so) (splitTarget ti xo)
    let T := transportedAmbient si ti so xo
    let sT : Fin (k + m) → U ⊕ K := T.source
    let tT : Fin (k + m) → U ⊕ K := T.target
    let ξR : T.BoundaryPartition := G.transportBoundaryOf (Equiv.refl (U ⊕ K))
      (twoSidedBoundary si ti so xo θ ζL)
    let L := rightExtendedGraph (V := U ⊕ K) sT tT GO
    let D := disjointSum (finIndexedGraph (U ⊕ K) (k + m) sT tT) GO
    let j : Fin (k + m + Fintype.card GO.Edge) ≃ D.Edge := rightExtendedIndex GO
    let μS : PMF (Fin (k + m) → Bool) :=
      T.fkPMF hq hp₁.le (G.transportBoundaryOf (Equiv.refl (U ⊕ K))
        (twoSidedBoundary si ti so xo θ ζS))
    let hμS : ∀ ω, μS ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ _
    let hboundS : ∀ x, (canonicalNext μS hμS x true).toReal ≤
        (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ _ hq hp₀ hp₁ x
    let stepS := orderedUpperStep μS hμS (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) hboundS
    let μL : PMF (Fin (k + m + Fintype.card GO.Edge) → Bool) :=
      L.fkPMF hq hp₁.le (D.transportBoundaryOf (Equiv.refl _)
        (eE := j) (sumBoundary ξR χ))
    let hμL : ∀ ω, μL ω ≠ 0 := fkPMF_ne_zero L hq hp₀ hp₁ _
    let hboundL : ∀ x, (canonicalNext μL hμL x true).toReal ≤
        (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ _ hq hp₀ hp₁ x
    let stepL := orderedUpperStep μL hμL (upperRateNN q p)
      (upperRateNN_le_one hq hp₁.le) hboundL
    let EL : Set (List Bool × List Bool) :=
      {w | interiorConfig (toAmbientConfig si ti so xo
        ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
          (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A} ∩
      {w | exteriorConfig (toAmbientConfig si ti so xo
        ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
          (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) ∈ E}
    let ES : Set (List Bool × List Bool) :=
      {w | interiorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.1)) ∈ A} ∩
      {w | exteriorConfig (toAmbientConfig si ti so xo
        (toConfig (k + m) w.2)) ∈ E}
    (extendPair stepL [] [] (k + m + Fintype.card GO.Edge)).toMeasure EL =
      (extendPair stepS [] [] (k + m)).toMeasure ES := by
  intro G T sT tT ξR L D j μS hμS hboundS stepS μL hμL hboundL stepL EL ES
  let pfxS := extendPair stepS [] [] k
  let pfxL := extendPair stepL [] [] k
  let remS : List Bool × List Bool → PMF (List Bool × List Bool) := fun z =>
    extendPair stepS z.1 z.2 m
  let remL : List Bool × List Bool → PMF (List Bool × List Bool) := fun z =>
    extendPair stepL z.1 z.2 (m + Fintype.card GO.Edge)
  let free : PMF (Fin m → Bool) := (regionGraph si ti).fkPMF hq hp₁.le θ
  let F : List Bool → ℝ≥0∞ := fun y =>
    if exteriorConfig (ambientOfHistory (m := m) (k := k) y) ∈ E then
      free.toMeasure A else 0
  have hdecompS : extendPair stepS [] [] (k + m) = pfxS.bind remS :=
    extendPair_add stepS [] [] k m
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
      have hpre {w : List Bool × List Bool} (hw : w ∈ (remS z).support) :
          z.1 <+: w.1 ∧ z.2 <+: w.2 :=
        extendPair_prefix_support stepS z.1 z.2 m hw
      by_cases hEc : exteriorConfig (ambientOfHistory (m := m) (k := k) z.2) ∈ E
      · have hM : ambientOfHistory (m := m) (k := k) z.2 ∈
            maximalSplitStratum si ti so xo :=
          mem_maximalSplitStratum_of_exterior_mem si ti so xo hright hE hEc
        let ρ : Fin m ⊕ Fin k → Bool := ambientOfHistory (m := m) (k := k) z.2
        have hy : z.2 = exteriorHistory (m := m) ρ := by
          exact (exteriorHistory_ambientOfHistory (m := m)
            (by simpa using hlen.2)).symm
        have hcont : (remS z).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1))) = free :=
          pair_interior_continuation_twoSided si ti so xo hq hp₀ hp₁
            θ ζS ρ hright hM hz hy
        have hstable : ∀ w ∈ (remS z).support,
            (w ∈ ES ↔ interiorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.1)) ∈ A) := by
          intro w hw
          have hpref := hpre hw |>.2
          have heq : toConfig k w.2 = toConfig k z.2 :=
            (toConfig_eq_of_prefix (x := z.2) (y := w.2)
              (by simpa using hlen.2) hpref).symm
          have hEeq : exteriorConfig (toAmbientConfig si ti so xo
              (toConfig (k + m) w.2)) ∈ E ↔
              exteriorConfig (ambientOfHistory (m := m) (k := k) z.2) ∈ E := by
            rw [exteriorConfig_toAmbientConfig_toConfig, heq,
              ← exteriorConfig_ambientOfHistory (m := m) (k := k) (y := z.2)]
          constructor
          · intro h; exact h.1
          · intro h; exact ⟨h, hEeq.2 hEc⟩
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
          _ = pfxS z * F z.2 := by simp [F, hEc]
      · have hzero : (remS z).toMeasure ES = 0 := by
          calc
            (remS z).toMeasure ES = (remS z).toMeasure ∅ := by
              apply pmf_toMeasure_eq_of_support
              intro w hw
              have hpref := hpre hw |>.2
              have heq : toConfig k w.2 = toConfig k z.2 :=
                (toConfig_eq_of_prefix (x := z.2) (y := w.2)
                  (by simpa using hlen.2) hpref).symm
              have hEeq : exteriorConfig (toAmbientConfig si ti so xo
                  (toConfig (k + m) w.2)) ∈ E ↔
                  exteriorConfig (ambientOfHistory (m := m) (k := k) z.2) ∈ E := by
                rw [exteriorConfig_toAmbientConfig_toConfig, heq,
                  ← exteriorConfig_ambientOfHistory (m := m) (k := k) (y := z.2)]
              constructor
              · intro h
                exact (hEc (hEeq.1 h.2)).elim
              · intro h; exact h.elim
            _ = 0 := by simp
        simp [hzero, F, hEc]
    · have hz0 : pfxS z = 0 := (PMF.apply_eq_zero_iff _ _).2 hz
      simp [hz0]
  have hL (z : List Bool × List Bool) :
      pfxL z * (remL z).toMeasure EL = pfxL z * F z.2 := by
    by_cases hz : z ∈ pfxL.support
    · have hlen := extendPair_length_support stepL [] [] k hz
      have hpre {w : List Bool × List Bool} (hw : w ∈ (remL z).support) :
          z.1 <+: w.1 ∧ z.2 <+: w.2 :=
        extendPair_prefix_support stepL z.1 z.2 (m + Fintype.card GO.Edge) hw
      by_cases hEc : exteriorConfig (ambientOfHistory (m := m) (k := k) z.2) ∈ E
      · have hM : ambientOfHistory (m := m) (k := k) z.2 ∈
            maximalSplitStratum si ti so xo :=
          mem_maximalSplitStratum_of_exterior_mem si ti so xo hright hE hEc
        let ρ : Fin m ⊕ Fin k → Bool := ambientOfHistory (m := m) (k := k) z.2
        have hy : z.2 = exteriorHistory (m := m) ρ := by
          exact (exteriorHistory_ambientOfHistory (m := m)
            (by simpa using hlen.2)).symm
        have hcont : (remL z).map (fun w =>
            interiorConfig (toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.1)).1))) = free :=
          pair_interior_continuation_rightExtended_twoSided si ti so xo
            GO hq hp₀ hp₁ θ ζL χ ρ hright hM hz hy
        have hstable : ∀ w ∈ (remL z).support,
            (w ∈ EL ↔ interiorConfig (toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A) := by
          intro w hw
          have hpref := hpre hw |>.2
          have heq : toConfig k w.2 = toConfig k z.2 :=
            (toConfig_eq_of_prefix (x := z.2) (y := w.2)
              (by simpa using hlen.2) hpref).symm
          have h1 : exteriorConfig (toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) =
              toConfig k w.2 := by
            funext i
            change toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.2)).1) (Sum.inr i) = _
            rw [toAmbient_rightExtended_exterior_apply]
            rfl
          have hEeq : exteriorConfig (toAmbientConfig si ti so xo
              ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) ∈ E ↔
              exteriorConfig (ambientOfHistory (m := m) (k := k) z.2) ∈ E := by
            rw [h1, heq,
              ← exteriorConfig_ambientOfHistory (m := m) (k := k) (y := z.2)]
          constructor
          · intro h; exact h.1
          · intro h; exact ⟨h, hEeq.2 hEc⟩
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
          _ = pfxL z * F z.2 := by simp [F, hEc]
      · have hzero : (remL z).toMeasure EL = 0 := by
          calc
            (remL z).toMeasure EL = (remL z).toMeasure ∅ := by
              apply pmf_toMeasure_eq_of_support
              intro w hw
              have hpref := hpre hw |>.2
              have heq : toConfig k w.2 = toConfig k z.2 :=
                (toConfig_eq_of_prefix (x := z.2) (y := w.2)
                  (by simpa using hlen.2) hpref).symm
              have h1 : exteriorConfig (toAmbientConfig si ti so xo
                  ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                    (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) =
                  toConfig k w.2 := by
                funext i
                change toAmbientConfig si ti so xo
                  ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                    (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)
                    (Sum.inr i) = _
                rw [toAmbient_rightExtended_exterior_apply]
                rfl
              have hEeq : exteriorConfig (toAmbientConfig si ti so xo
                  ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
                    (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) ∈ E ↔
                  exteriorConfig (ambientOfHistory (m := m) (k := k) z.2) ∈ E := by
                rw [h1, heq,
                  ← exteriorConfig_ambientOfHistory (m := m) (k := k) (y := z.2)]
              constructor
              · intro h
                exact (hEc (hEeq.1 h.2)).elim
              · intro h; exact h.elim
            _ = 0 := by simp
        simp [hzero, F, hEc]
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
  have hpS : pfxS.map Prod.snd = ν :=
    extendPair_map_snd stepS
      (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)) hsndS [] [] k
  have hpL : pfxL.map Prod.snd = ν :=
    extendPair_map_snd stepL
      (fun _ => FKModel.bernoulliPMF (upperRateNN q p)
        (upperRateNN_le_one hq hp₁.le)) hsndL [] [] k
  calc
    (∑' z, pfxL z * (remL z).toMeasure EL) = ∑' z, pfxL z * F z.2 :=
      tsum_congr hL
    _ = ∑' z, pfxS z * F z.2 := tsum_pair_weight_eq_of_map_snd_general pfxL pfxS ν hpL hpS F
    _ = ∑' z, pfxS z * (remS z).toMeasure ES := (tsum_congr hS).symm

/-- **Good intersection on an exterior-refined stratum, at the level of the
actual FK/upper pair laws.** -/
theorem good_intersection_rightExtended_pairs_exteriorStratum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo)
    (E : Set (Fin k → Bool)) (hE : E ⊆ SepExt si ti so xo)
    (A : Set (Fin m → Bool)) :
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
    let CE : Set T.Configuration := {ω |
      exteriorConfig (toAmbientConfig si ti so xo ω) ∈ E}
    (fkUpperPair L.source L.target ξL hq hp₀ hp₁).toMeasure
      (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' CE)) =
    (fkUpperPair sT tT ξS hq hp₀ hp₁).toMeasure
      (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' CE) := by
  intro G T sT tT ξS ξR L D j ξL e B AD CE
  let N := k + m + Fintype.card GO.Edge
  let decodeL : List Bool × List Bool → L.Configuration × L.Configuration :=
    fun w => (toConfig N w.1, toConfig N w.2)
  let decodeS : List Bool × List Bool → T.Configuration × T.Configuration :=
    fun w => (toConfig (k + m) w.1, toConfig (k + m) w.2)
  let EL : Set (List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
        (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A} ∩
    {w | exteriorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
        (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) ∈ E}
  let ES : Set (List Bool × List Bool) :=
    {w | interiorConfig (toAmbientConfig si ti so xo
      (toConfig (k + m) w.1)) ∈ A} ∩
    {w | exteriorConfig (toAmbientConfig si ti so xo
      (toConfig (k + m) w.2)) ∈ E}
  let μS : PMF (Fin (k + m) → Bool) := T.fkPMF hq hp₁.le ξS
  let hμS : ∀ ω, μS ω ≠ 0 := fkPMF_ne_zero T hq hp₀ hp₁ ξS
  let hboundS : ∀ x, (canonicalNext μS hμS x true).toReal ≤
      (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ ξS hq hp₀ hp₁ x
  let stepS := orderedUpperStep μS hμS (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) hboundS
  let μL : PMF (Fin N → Bool) := L.fkPMF hq hp₁.le ξL
  let hμL : ∀ ω, μL ω ≠ 0 := fkPMF_ne_zero L hq hp₀ hp₁ ξL
  let hboundL : ∀ x, (canonicalNext μL hμL x true).toReal ≤
      (upperRateNN q p : ℝ) := fun x => fk_upper_nextBound _ _ ξL hq hp₀ hp₁ x
  let stepL := orderedUpperStep μL hμL (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) hboundL
  let histS := upperHistoryPair μS hμS (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) hboundS (k + m)
  let histL := upperHistoryPair μL hμL (upperRateNN q p)
    (upperRateNN_le_one hq hp₁.le) hboundL N
  have h := good_intersection_exteriorStratum si ti so xo GO hq hp₀ hp₁
    θ ζS ζL χ hright E hE A
  have hL : decodeL ⁻¹' (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' CE)) = EL := by
    ext w
    have heq : toAmbientConfig si ti so xo (restrictΔ e (toConfig N w.2)) =
        toAmbientConfig si ti so xo
          ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO (toConfig N w.2)).1) := by
      dsimp only [e]
      exact congrArg (toAmbientConfig si ti so xo)
        (restrictΔ_rightExtended_eq_fst sT tT GO (toConfig N w.2))
    show (interiorConfig (toAmbientConfig si ti so xo
        ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
          (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A ∧
        exteriorConfig (toAmbientConfig si ti so xo
          (restrictΔ e (toConfig (k + m + Fintype.card GO.Edge) w.2))) ∈ E) ↔
      (interiorConfig (toAmbientConfig si ti so xo
        ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
          (toConfig (k + m + Fintype.card GO.Edge) w.1)).1)) ∈ A ∧
        exteriorConfig (toAmbientConfig si ti so xo
          ((splitRightExtendedConfig (V := U ⊕ K) sT tT GO
            (toConfig (k + m + Fintype.card GO.Edge) w.2)).1)) ∈ E)
    rw [heq]
  have hS : decodeS ⁻¹' (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' CE) = ES := by
    rfl
  have hmapL : histL.map decodeL = fkUpperPair L.source L.target ξL hq hp₀ hp₁ := by
    rfl
  have hmapS : histS.map decodeS = fkUpperPair sT tT ξS hq hp₀ hp₁ := by
    rfl
  calc
    (fkUpperPair L.source L.target ξL hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' CE)) =
        histL.toMeasure (decodeL ⁻¹'
          (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' CE))) := by
      rw [← hmapL]
      exact toMeasure_map_pmf decodeL histL _ measurable_from_top MeasurableSet.of_discrete
    _ = histL.toMeasure EL := by rw [hL]
    _ = histS.toMeasure ES := by
      with_unfolding_all exact h
    _ = histS.toMeasure (decodeS ⁻¹' (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' CE)) := by rw [hS]
    _ = (fkUpperPair sT tT ξS hq hp₀ hp₁).toMeasure
        (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' CE) := by
      rw [← hmapS]
      exact (toMeasure_map_pmf decodeS histS _ measurable_from_top MeasurableSet.of_discrete).symm

/-- **Common-upper good intersection for the actual nested ordered triple on an
exterior-refined stratum.**  The maximal-stratum identity
`FK.Exploration.NestedCoupledGood.fkNestedOrderedTriple_good_rightExtended_twoSided`
is the case `E = SepExt`. -/
theorem fkNestedOrderedTriple_good_rightExtended_exteriorStratum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo)
    (E : Set (Fin k → Bool)) (hE : E ⊆ SepExt si ti so xo)
    (A : Set (Fin m → Bool)) :
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
    let CE : Set T.Configuration := {ω |
      exteriorConfig (toAmbientConfig si ti so xo ω) ∈ E}
    let t := fkNestedOrderedTriple L.source L.target sT tT GO e ξL ξS hq hp₀ hp₁
    t.dist.toMeasure
      ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' CE)) =
    t.dist.toMeasure
      ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' CE)) := by
  intro G T sT tT ξS ξR L D j ξL e B AD CE t
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
    Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' CE)
  let eventD : Set (T.Configuration × T.Configuration) :=
    Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' CE
  let smallPair : L.Configuration × L.Configuration →
      T.Configuration × T.Configuration :=
    fun z => (restrictΔ e z.1, restrictΔ e z.2)
  have hB : B = restrictΔ e ⁻¹' AD := by
    ext ω
    change interiorConfig (toAmbientConfig si ti so xo
      ((splitRightExtendedConfig sT tT GO ω).1)) ∈ A ↔
        interiorConfig (toAmbientConfig si ti so xo (restrictΔ e ω)) ∈ A
    have he : restrictΔ e ω = (splitRightExtendedConfig sT tT GO ω).1 :=
      restrictΔ_rightExtended_eq_fst sT tT GO ω
    rw [he]
  have hrestrict : smallPair ⁻¹' eventD = eventL := by
    ext z
    change (z.1 ∈ restrictΔ e ⁻¹' AD ∧ z.2 ∈ restrictΔ e ⁻¹' CE) ↔
      (z.1 ∈ B ∧ z.2 ∈ restrictΔ e ⁻¹' CE)
    rw [← hB]
  have hcSdist : cS.dist = fkUpperPair L.source L.target ξL hq hp₀ hp₁ :=
    orderedCoupling_dist_of_eq_mp hsplit
      (fkUpperOrderedCoupling L.source L.target ξL hq hp₀ hp₁)
  have hpairs : cS.dist.toMeasure eventL = cΔ.dist.toMeasure eventD := by
    rw [hcSdist]
    exact good_intersection_rightExtended_pairs_exteriorStratum si ti so xo GO
      hq hp₀ hp₁ θ ζS ζL χ hright E hE A
  have hfstthd : t.dist.map (fun z => (z.1, z.2.2)) = cS.dist := by
    with_unfolding_all exact PMF.Coupling.map_glueDist_fst_thd cS.toCoupling cO.toCoupling
  have hsndthd : t.dist.map (fun z => (z.2.1, z.2.2)) = cO.dist := by
    with_unfolding_all exact PMF.Coupling.map_glueDist_snd_thd cS.toCoupling cO.toCoupling
  have hsmall : cO.dist.map smallPair = cΔ.dist :=
    extendPairDist_map_restrictΔ_pair e cΔ ρO
  calc
    t.dist.toMeasure
        ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' CE)) =
        (t.dist.map (fun z => (z.1, z.2.2))).toMeasure eventL := by
      change t.dist.toMeasure ((fun z => (z.1, z.2.2)) ⁻¹' eventL) = _
      exact (toMeasure_map_pmf (fun z : L.Configuration × L.Configuration × L.Configuration =>
        (z.1, z.2.2)) t.dist eventL (measurable_of_finite _) MeasurableSet.of_discrete).symm
    _ = cS.dist.toMeasure eventL := by rw [hfstthd]; rfl
    _ = cΔ.dist.toMeasure eventD := hpairs
    _ = (cO.dist.map smallPair).toMeasure eventD := by rw [hsmall]; rfl
    _ = cO.dist.toMeasure (smallPair ⁻¹' eventD) :=
      toMeasure_map_pmf _ _ _ (measurable_of_finite _) MeasurableSet.of_discrete
    _ = cO.dist.toMeasure eventL := by rw [hrestrict]
    _ = (t.dist.map (fun z => (z.2.1, z.2.2))).toMeasure eventL := by rw [hsndthd]; rfl
    _ = t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' CE)) := by
      change (t.dist.map (fun z => (z.2.1, z.2.2))).toMeasure eventL =
        t.dist.toMeasure ((fun z => (z.2.1, z.2.2)) ⁻¹' eventL)
      exact toMeasure_map_pmf (fun z : L.Configuration × L.Configuration × L.Configuration =>
        (z.2.1, z.2.2)) t.dist eventL (measurable_of_finite _) MeasurableSet.of_discrete

/-- **Equation (9) on an exterior-refined stratum.**  The refined good-intersection
identity is exactly the input shape of
`fkNestedOrderedTriple_abs_sub_le_of_good`, so the conditional arm estimate
holds with the refined exceptional event. -/
theorem fkNestedOrderedTriple_abs_sub_le_of_exteriorStratum
    (si : Fin m → U) (ti : Fin m → U) (so xo : Fin k → U ⊕ K)
    (GO : LabelledMultigraph) {q p : NNReal}
    (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (θ : Setoid U) (ζS ζL : Setoid K) (χ : GO.BoundaryPartition)
    (hright : ExteriorHasRight so xo)
    (E : Set (Fin k → Bool)) (hE : E ⊆ SepExt si ti so xo)
    (A : Set (Fin m → Bool)) :
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
    let CE : Set T.Configuration := {ω |
      exteriorConfig (toAmbientConfig si ti so xo ω) ∈ E}
    |(L.fkPMF hq hp₁.le ξL).toMeasure.real B -
        (T.fkPMF hq hp₁.le ξS).toMeasure.real AD| ≤
      (L.bernoulliProductPMF (upperRateNN_le_one hq hp₁.le)).toMeasure.real
        (restrictΔ e ⁻¹' CE)ᶜ := by
  intro G T sT tT ξS ξR L D j ξL e B AD CE
  refine fkNestedOrderedTriple_abs_sub_le_of_good L.source L.target sT tT GO e
    ξL ξS hq hp₀ hp₁ B AD CE rfl ?_
  exact fkNestedOrderedTriple_good_rightExtended_exteriorStratum si ti so xo GO
    hq hp₀ hp₁ θ ζS ζL χ hright E hE A

/-- **The accepted maximal-stratum identity is the special case** `E = SepExt`
of the refined identity: `CE` is literally the preimage of the maximal split
stratum under `toAmbientConfig`. -/
theorem fkNestedOrderedTriple_good_rightExtended_maximalStratum
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
    let C : Set T.Configuration := {ω |
      toAmbientConfig si ti so xo ω ∈ maximalSplitStratum si ti so xo}
    let t := fkNestedOrderedTriple L.source L.target sT tT GO e ξL ξS hq hp₀ hp₁
    t.dist.toMeasure
      ((fun z => z.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
    t.dist.toMeasure
      ((fun z => z.2.1) ⁻¹' B ∩ (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) := by
  intro G T sT tT ξS ξR L D j ξL e B C t
  have hCE : ({ω : T.Configuration |
      exteriorConfig (toAmbientConfig si ti so xo ω) ∈ SepExt si ti so xo}) = C := by
    ext ρ
    show Separated si ti so xo (exteriorConfig (toAmbientConfig si ti so xo ρ)) ↔
      toAmbientConfig si ti so xo ρ ∈ maximalSplitStratum si ti so xo
    exact (mem_maximalSplitStratum_iff si ti so xo
      (toAmbientConfig si ti so xo ρ) hright).symm
  rw [← hCE]
  exact fkNestedOrderedTriple_good_rightExtended_exteriorStratum si ti so xo GO
    hq hp₀ hp₁ θ ζS ζL χ hright (SepExt si ti so xo) (subset_refl _) A

end FK.Exploration.RefinedStrata

/-! ## Axiom audit -/

#print axioms FK.Exploration.RefinedStrata.good_intersection_exteriorStratum
#print axioms FK.Exploration.RefinedStrata.good_intersection_rightExtended_pairs_exteriorStratum
#print axioms FK.Exploration.RefinedStrata.fkNestedOrderedTriple_good_rightExtended_exteriorStratum
#print axioms FK.Exploration.RefinedStrata.fkNestedOrderedTriple_abs_sub_le_of_exteriorStratum
#print axioms FK.Exploration.RefinedStrata.mem_maximalSplitStratum_of_exterior_mem
#print axioms FK.Exploration.RefinedStrata.exteriorConfig_toAmbientConfig_toConfig
#print axioms FK.Exploration.RefinedStrata.exteriorConfig_ambientOfHistory
#print axioms FK.Exploration.RefinedStrata.sum_inr_notMem_range_inl
#print axioms FK.Exploration.RefinedStrata.sepExt_eq_univ_of_right
#print axioms FK.Exploration.RefinedStrata.fkNestedOrderedTriple_good_rightExtended_maximalStratum
