import FK.NestedRegionExploration

open scoped ENNReal NNReal BigOperators Classical
open MeasureTheory
open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.FKCoupling FK.Exploration.NestedFiniteCoupling
open FK.Exploration.NestedCoupledGood

namespace FK.NestedRegionExploration

/-- Glue a first/upper pair identity and a second/upper pair through their
common upper configuration.  This contains no FK or graph-geometry hypothesis. -/
theorem nestedOrderedTriple_good_of_pair_identity
    {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μS : PMF GS.Configuration} {μΔ ρΔ : PMF GD.Configuration}
    {ρO : PMF GO.Configuration}
    (cS : PMF.OrderedCoupling μS (splitLaw e ρΔ ρO))
    (cΔ : PMF.OrderedCoupling μΔ ρΔ)
    (B : Set GS.Configuration) (AD C : Set GD.Configuration)
    (hBA : B = restrictΔ e ⁻¹' AD)
    (hpairs : cS.dist.toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) =
      cΔ.dist.toMeasure (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C)) :
    let t := nestedOrderedTriple e cS cΔ
    t.dist.toMeasure
      ((fun z => z.1) ⁻¹' B ∩
        (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
    t.dist.toMeasure
      ((fun z => z.2.1) ⁻¹' B ∩
        (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) := by
  intro t
  let cO := extendOrderedCoupling e cΔ ρO
  let eventL : Set (GS.Configuration × GS.Configuration) :=
    Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)
  let eventD : Set (GD.Configuration × GD.Configuration) :=
    Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C
  let smallPair : GS.Configuration × GS.Configuration →
      GD.Configuration × GD.Configuration :=
    fun z => (restrictΔ e z.1, restrictΔ e z.2)
  have hrestrict : smallPair ⁻¹' eventD = eventL := by
    ext z
    change (z.1 ∈ restrictΔ e ⁻¹' AD ∧ z.2 ∈ restrictΔ e ⁻¹' C) ↔
      (z.1 ∈ B ∧ z.2 ∈ restrictΔ e ⁻¹' C)
    rw [← hBA]
  have hfstthd : t.dist.map (fun z => (z.1, z.2.2)) = cS.dist := by
    exact PMF.Coupling.map_glueDist_fst_thd cS.toCoupling cO.toCoupling
  have hsndthd : t.dist.map (fun z => (z.2.1, z.2.2)) = cO.dist := by
    exact PMF.Coupling.map_glueDist_snd_thd cS.toCoupling cO.toCoupling
  have hsmall : cO.dist.map smallPair = cΔ.dist := by
    exact extendPairDist_map_restrictΔ_pair e cΔ ρO
  calc
    t.dist.toMeasure
        ((fun z => z.1) ⁻¹' B ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
        (t.dist.map (fun z => (z.1, z.2.2))).toMeasure eventL := by
      change t.dist.toMeasure ((fun z => (z.1, z.2.2)) ⁻¹' eventL) = _
      exact (toMeasure_map_pmf (fun z : GS.Configuration × GS.Configuration ×
        GS.Configuration => (z.1, z.2.2)) t.dist eventL
        (measurable_of_finite _) MeasurableSet.of_discrete).symm
    _ = cS.dist.toMeasure eventL := by rw [hfstthd]
    _ = cΔ.dist.toMeasure eventD := hpairs
    _ = (cO.dist.map smallPair).toMeasure eventD := by rw [hsmall]
    _ = cO.dist.toMeasure (smallPair ⁻¹' eventD) := by
      exact toMeasure_map_pmf _ _ _ (measurable_of_finite _)
        MeasurableSet.of_discrete
    _ = cO.dist.toMeasure eventL := by rw [hrestrict]
    _ = (t.dist.map (fun z => (z.2.1, z.2.2))).toMeasure eventL := by
      rw [hsndthd]
    _ = t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' B ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) := by
      change (t.dist.map (fun z => (z.2.1, z.2.2))).toMeasure eventL =
        t.dist.toMeasure ((fun z => (z.2.1, z.2.2)) ⁻¹' eventL)
      exact toMeasure_map_pmf (fun z : GS.Configuration × GS.Configuration ×
        GS.Configuration => (z.2.1, z.2.2)) t.dist eventL
        (measurable_of_finite _) MeasurableSet.of_discrete

/-- Equation (9) for the explicitly glued nested triple.  The only coupling
input is the pair-level good-intersection identity; the smaller second
marginal is recovered by restricting along `restrictΔ`. -/
theorem nestedOrderedTriple_abs_sub_le_of_pair_identity
    {GS GD GO : LabelledMultigraph}
    (e : GD.Edge ⊕ GO.Edge ≃ GS.Edge)
    {μS : PMF GS.Configuration} {μΔ ρΔ : PMF GD.Configuration}
    {ρO : PMF GO.Configuration}
    (cS : PMF.OrderedCoupling μS (splitLaw e ρΔ ρO))
    (cΔ : PMF.OrderedCoupling μΔ ρΔ)
    (B : Set GS.Configuration) (AD C : Set GD.Configuration)
    (hBA : B = restrictΔ e ⁻¹' AD)
    (hpairs : cS.dist.toMeasure
        (Prod.fst ⁻¹' B ∩ Prod.snd ⁻¹' (restrictΔ e ⁻¹' C)) =
      cΔ.dist.toMeasure (Prod.fst ⁻¹' AD ∩ Prod.snd ⁻¹' C)) :
    |μS.toMeasure.real B - μΔ.toMeasure.real AD| ≤
      (splitLaw e ρΔ ρO).toMeasure.real (restrictΔ e ⁻¹' C)ᶜ := by
  let t := nestedOrderedTriple e cS cΔ
  have hgood := nestedOrderedTriple_good_of_pair_identity e cS cΔ B AD C hBA hpairs
  have hbase := t.equation_nine_abs_bound (A := B) (B := B)
    (C := restrictΔ e ⁻¹' C) MeasurableSet.of_discrete MeasurableSet.of_discrete
    MeasurableSet.of_discrete hgood
  have hsecond : (splitLaw e μΔ ρO).toMeasure.real B = μΔ.toMeasure.real AD := by
    rw [hBA]
    apply congrArg ENNReal.toReal
    calc
      _ = (Measure.map (restrictΔ e) (splitLaw e μΔ ρO).toMeasure) AD := by
        rw [Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
      _ = _ := by
        have hmap := congrArg PMF.toMeasure (map_restrictΔ_splitLaw e μΔ ρO)
        rw [← PMF.toMeasure_map _ _ (by fun_prop)] at hmap
        rw [hmap]
  rw [hsecond] at hbase
  exact hbase

end FK.NestedRegionExploration
