import FK.NestedFiniteAssembly
import FK.NestedBoundaryUniqueness

/-!
# Reverse assembly for genuinely nested finite-box estimates

The finite nested coupling compares two different boxes.  This file supplies
that missing scale bookkeeping for the reverse conditional laws, and then
constructs the auxiliary coupling on the product of the two global laws.
The finite estimate and the geometric/stratum inputs needed to prove it remain
explicit hypotheses.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace FK.InfiniteVolume

universe u v

/-- A common auxiliary representation of two global laws and a vanishing
bound between an *outer* and an *inner* exterior conditional law.  Unlike
`HasVanishingExteriorCouplingError`, the two boxes need not have the same
index.  The index maps are data; the uniqueness theorems additionally require
both to tend to infinity. -/
def HasVanishingNestedExteriorCouplingError {E : Type u}
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    (outer inner : ℕ → ℕ) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E)) : Prop :=
  ∃ (Θ : Type u) (_ : MeasurableSpace Θ) (ρ : Measure Θ)
    (_ : IsProbabilityMeasure ρ) (X Y : Θ → Configuration E) (err : Finset E → ℕ → Θ → ℝ),
    Measurable X ∧ Measurable Y ∧
    Measure.map X ρ = (μ : Measure (Configuration E)) ∧
    Measure.map Y ρ = (ν : Measure (Configuration E)) ∧
    (∀ I, ∀ᵐ z ∂ρ, Tendsto (fun n ↦ err I n z) atTop (𝓝 0)) ∧
    ∀ (I : Finset E) (S : Set (I → Bool)), ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      |(((exh.box (outer n)).conditionalLaw hq hp (Φ.partition (outer n))
          (FKLimit.exteriorRestriction (exh.box (outer n)).edges (X z)) :
          Measure (Configuration E)).real (MeasureTheory.cylinder I S)) -
        (((exh.box (inner n)).conditionalLaw hq hp (Φ.partition (inner n))
          (FKLimit.exteriorRestriction (exh.box (inner n)).edges (Y z)) :
          Measure (Configuration E)).real (MeasureTheory.cylinder I S))| ≤ err I n z

/-- Extremal DLR uniqueness from an outer/inner nested conditional estimate.
The actual reverse-martingale convergence is composed with each index map. -/
theorem eq_of_extremal_dlr_of_hasVanishingNestedExteriorCouplingError
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    (outer inner : ℕ → ℕ) (houter : Tendsto outer atTop atTop)
    (hinner : Tendsto inner atTop atTop)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hextμ : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (μ : Measure (Configuration E)))
    (hextν : FK.IsExtremalIn
      ((fun η : ProbabilityMeasure (Configuration E) ↦
        (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
      (ν : Measure (Configuration E)))
    (hcouple : HasVanishingNestedExteriorCouplingError
      exh Φ outer inner hq hp μ ν) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply FKModel.measure_ext_of_eq_on_boolCylinders
  intro I S
  rw [← ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (μ : Measure (Configuration E)) _)
    (measure_ne_top (ν : Measure (Configuration E)) _)]
  rcases hcouple with ⟨Θ, mΘ, ρ, hρ, X, Y, err,
    hX, hY, hXμ, hYν, herr, hbound⟩
  let _ : MeasurableSpace Θ := mΘ
  let _ : IsProbabilityMeasure ρ := hρ
  let A : Set (Configuration E) := MeasureTheory.cylinder I S
  let F : ℕ → Configuration E → ℝ := fun n ω ↦
    ((exh.box n).conditionalLaw hq hp (Φ.partition n)
      (FKLimit.exteriorRestriction (exh.box n).edges ω) :
      Measure (Configuration E)).real A
  have hμlim₀ : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ F n ω) atTop (𝓝 ((μ : Measure (Configuration E)).real A)) :=
    tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
      exh Φ hq hp μ hμ hextμ (dependsOnCoordinates_cylinder I S)
  have hνlim₀ : ∀ᵐ ω ∂(ν : Measure (Configuration E)),
      Tendsto (fun n ↦ F n ω) atTop (𝓝 ((ν : Measure (Configuration E)).real A)) :=
    tendsto_ae_exteriorConditionalLaw_of_dependsOn_of_extremal_dlr
      exh Φ hq hp ν hν hextν (dependsOnCoordinates_cylinder I S)
  have hμlim : ∀ᵐ ω ∂(μ : Measure (Configuration E)),
      Tendsto (fun n ↦ F (outer n) ω) atTop
        (𝓝 ((μ : Measure (Configuration E)).real A)) := by
    filter_upwards [hμlim₀] with ω hω
    exact hω.comp houter
  have hνlim : ∀ᵐ ω ∂(ν : Measure (Configuration E)),
      Tendsto (fun n ↦ F (inner n) ω) atTop
        (𝓝 ((ν : Measure (Configuration E)).real A)) := by
    filter_upwards [hνlim₀] with ω hω
    exact hω.comp hinner
  have hμρ : ∀ᵐ z ∂ρ, Tendsto (fun n ↦ F (outer n) (X z)) atTop
      (𝓝 ((μ : Measure (Configuration E)).real A)) := by
    exact (Measure.tendsto_ae_map (μ := ρ) hX.aemeasurable).eventually (by
      rwa [hXμ])
  have hνρ : ∀ᵐ z ∂ρ, Tendsto (fun n ↦ F (inner n) (Y z)) atTop
      (𝓝 ((ν : Measure (Configuration E)).real A)) := by
    exact (Measure.tendsto_ae_map (μ := ρ) hY.aemeasurable).eventually (by
      rwa [hYν])
  have hbound' : ∀ᵐ z ∂ρ, ∀ᶠ n in atTop,
      |F (outer n) (X z) - F (inner n) (Y z)| ≤ err I n z := by
    simpa only [F, A] using hbound I S
  have heq : ∀ᵐ z ∂ρ, (μ : Measure (Configuration E)).real A =
      (ν : Measure (Configuration E)).real A := by
    filter_upwards [hμρ, hνρ, herr I, hbound'] with z hμz hνz herrz hboundz
    have hdiff : Tendsto (fun n ↦ F (outer n) (X z) - F (inner n) (Y z)) atTop
        (𝓝 ((μ : Measure (Configuration E)).real A -
          (ν : Measure (Configuration E)).real A)) := hμz.sub hνz
    have hzero : Tendsto (fun n ↦ F (outer n) (X z) - F (inner n) (Y z)) atTop
        (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (by simpa using herrz.neg) herrz
      · filter_upwards [hboundz] with n hn
        exact (abs_le.mp hn).1
      · filter_upwards [hboundz] with n hn
        exact (abs_le.mp hn).2
    exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)
  simpa only [A, Measure.real] using heq.exists.choose_spec

/-- Full DLR uniqueness from pairwise nested errors.  The outer and inner
index maps may be chosen for each pair of extremal laws. -/
theorem eq_dlr_of_pairwise_hasVanishingNestedExteriorCouplingError
    {E : Type u} [Countable E]
    (exh : BoxExhaustion.{u, v} E) (Φ : BoundaryAssignment exh.box)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration E))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (hpair : ∀ κ ξ : ProbabilityMeasure (Configuration E),
      FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (κ : Measure (Configuration E)) →
      FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (ξ : Measure (Configuration E)) →
      ∃ outer inner : ℕ → ℕ, Tendsto outer atTop atTop ∧ Tendsto inner atTop atTop ∧
        HasVanishingNestedExteriorCouplingError exh Φ outer inner hq hp κ ξ) : μ = ν := by
  have hgood := (ae_mem_dlrMeasures_tailConditionalLaw exh Φ hq hp μ hμ).and
    (ae_isExtremalIn_dlr_tailConditionalLaw exh Φ hq hp μ hμ)
  obtain ⟨ω, hκ, hextκ⟩ := hgood.exists
  let κ : ProbabilityMeasure (Configuration E) := tailConditionalLaw μ ω
  change κ ∈ DLRMeasures exh Φ hq hp at hκ
  change FK.IsExtremalIn
    ((fun η : ProbabilityMeasure (Configuration E) ↦
      (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
    (κ : Measure (Configuration E)) at hextκ
  have heq (ξ : ProbabilityMeasure (Configuration E))
      (hξ : ξ ∈ DLRMeasures exh Φ hq hp)
      (hextξ : FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration E) ↦
          (η : Measure (Configuration E))) '' DLRMeasures exh Φ hq hp)
        (ξ : Measure (Configuration E))) : ξ = κ := by
    rcases hpair ξ κ hextξ hextκ with ⟨outer, inner, houter, hinner, hcouple⟩
    exact eq_of_extremal_dlr_of_hasVanishingNestedExteriorCouplingError
      exh Φ outer inner houter hinner hq hp ξ κ hξ hκ hextξ hextκ hcouple
  have hμκ : μ = κ := by
    apply eq_dlr_of_extremal_unique exh Φ hq hp μ κ hμ
    intro ξ hextξ
    exact heq ξ (mem_dlrMeasures_of_extremal_dlr exh Φ hq hp ξ hextξ) hextξ
  have hνκ : ν = κ := by
    apply eq_dlr_of_extremal_unique exh Φ hq hp ν κ hν
    intro ξ hextξ
    exact heq ξ (mem_dlrMeasures_of_extremal_dlr exh Φ hq hp ξ hextξ) hextξ
  exact hμκ.trans hνκ.symm


open CurvatureVariance.Infra.Percolation

/-- Build the nested conditional interface on the actual product of the two
configuration laws.  The premise is precisely a finite-volume arm estimate:
the finite-box conversion to exterior conditional laws is proved here using
eventual cylinder support.  Nonpercolation of the upper law makes every
cylinder's error tend to zero; no vanishing conditional bound is assumed. -/
theorem hasVanishingNestedExteriorCouplingError_of_finiteVolume_farConnection
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (exh : BoxExhaustion G.edgeSet)
    (Φ : BoundaryAssignment exh.box) (outer inner : ℕ → ℕ)
    (houter : Tendsto outer atTop atTop) (hinner : Tendsto inner atTop atTop)
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet)) (p' : unitInterval)
    (hnonperc : ∀ᵐ ω ∂(percolation G p'), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V) (center : Finset G.edgeSet → V)
    (width : Finset G.edgeSet → ℕ)
    (hwidth : ∀ I, ∀ a ∈ roots I, G.dist (center I) a ≤ width I)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)),
      ∀ᵐ z ∂((μ : Measure (Configuration G.edgeSet)).prod
        (ν : Measure (Configuration G.edgeSet))), ∀ᶠ n in atTop,
        |(((exh.box (outer n)).finiteVolumeLaw hq hp
            (Φ.partition (outer n)
              (FKLimit.exteriorRestriction (exh.box (outer n)).edges z.1)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S)) -
          (((exh.box (inner n)).finiteVolumeLaw hq hp
            (Φ.partition (inner n)
              (FKLimit.exteriorRestriction (exh.box (inner n)).edges z.2)) :
            Measure (Configuration G.edgeSet)).real (cylinder I S))| ≤
          (percolation G p').real
            (NestedAssembly.farConnection G (roots I) (center I) (n + width I))) :
    HasVanishingNestedExteriorCouplingError exh Φ outer inner hq hp μ ν := by
  let ρ : Measure (Configuration G.edgeSet × Configuration G.edgeSet) :=
    (μ : Measure (Configuration G.edgeSet)).prod (ν : Measure (Configuration G.edgeSet))
  refine ⟨Configuration G.edgeSet × Configuration G.edgeSet, inferInstance,
    ρ, inferInstance, Prod.fst, Prod.snd,
    fun I n _ ↦ (percolation G p').real
      (NestedAssembly.farConnection G (roots I) (center I) (n + width I)),
    measurable_fst, measurable_snd, ?_, ?_, ?_, ?_⟩
  · simp [ρ]
  · simp [ρ]
  · intro I
    exact Eventually.of_forall fun _ ↦
      NestedAssembly.tendsto_measureReal_farConnection_add_of_ae_nonPercolating
        hG (percolation G p') (roots I) (center I) (width I) (hwidth I) hnonperc
  · intro I S
    change ∀ᵐ z ∂ρ, _
    filter_upwards [hbound I S] with z hz
    filter_upwards [hz, houter.eventually (exh.eventually_subset I),
      hinner.eventually (exh.eventually_subset I)] with n hn hout hin
    rw [← (exh.box (outer n)).finiteVolumeLaw_real_eq_conditionalLaw_real_of_dependsOn
      hq hp (Φ.partition (outer n))
      (FKLimit.exteriorRestriction (exh.box (outer n)).edges z.1)
      (dependsOnCoordinates_cylinder I S) hout,
      ← (exh.box (inner n)).finiteVolumeLaw_real_eq_conditionalLaw_real_of_dependsOn
      hq hp (Φ.partition (inner n))
      (FKLimit.exteriorRestriction (exh.box (inner n)).edges z.2)
      (dependsOnCoordinates_cylinder I S) hin]
    exact hn


open FK.Finite FK.Finite.LabelledMultigraph
open FK.Exploration.NestedFiniteCoupling
open FK.Exploration.FKCoupling

/-- Single-scale nested conditional-cylinder estimate with arbitrary exterior
configurations on both boxes.  This is the actual finite nested coupling
estimate, transported from closed-exterior representatives to the FK exterior
kernels.  In particular `hgood`, `hD`, and the exact global realization `hU`
are premises, not consequences asserted by this theorem. -/
theorem conditionalLaw_cylinder_abs_sub_le_farConnection_of_good
    {V : Type u} {G : SimpleGraph V} (BS BD : FiniteBox G.edgeSet) {nS nD : ℕ}
    (jS : Fin nS ≃ BS.edges) (jD : Fin nD ≃ BD.edges)
    (GO : LabelledMultigraph)
    (e : (BD.indexedGraph jD).Edge ⊕ GO.Edge ≃ (BS.indexedGraph jS).Edge)
    (αS : BS.Exterior → BS.BoundaryPartition)
    (αD : BD.Exterior → BD.BoundaryPartition) (ηS : BS.Exterior) (ηD : BD.Exterior)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (J : Finset G.edgeSet) (S : Set (J → Bool))
    (hJS : J ⊆ BS.edges) (hJD : J ⊆ BD.edges)
    (he : ∀ i : J,
      e (Sum.inl (jD.symm ⟨i.1, hJD i.2⟩)) = jS.symm ⟨i.1, hJS i.2⟩)
    (C : Set (BD.indexedGraph jD).Configuration) (D : Set BS.Interior)
    (roots : Finset V) (center : V) (r : ℕ)
    (hU : BS.interiorRestriction ⁻¹' D = NestedAssembly.farConnection G roots center r)
    (hgood :
      let t := fkNestedOrderedTriple
        (fun i => BS.source (jS i)) (fun i => BS.target (jS i))
        (fun i => BD.source (jD i)) (fun i => BD.target (jD i))
        GO e (BS.indexedBoundary jS (αS ηS)) (BD.indexedBoundary jD (αD ηD)) hq hp₀ hp₁
      t.dist.toMeasure
        ((fun z => z.1) ⁻¹' (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)) =
      t.dist.toMeasure
        ((fun z => z.2.1) ⁻¹' (BS.reindex jS ⁻¹' BS.boxCylinder J S hJS) ∩
          (fun z => z.2.2) ⁻¹' (restrictΔ e ⁻¹' C)))
    (hD : (restrictΔ e ⁻¹' C)ᶜ ⊆ BS.reindex jS ⁻¹' D) :
    |(BS.conditionalLaw hq hp₁.le αS ηS : Measure (Configuration G.edgeSet)).real
          (cylinder J S) -
        (BD.conditionalLaw hq hp₁.le αD ηD : Measure (Configuration G.edgeSet)).real
          (cylinder J S)| ≤
      (percolation G (NestedFiniteAssembly.unitOfNN
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le))).real
        (NestedAssembly.farConnection G roots center r) := by
  have h := NestedFiniteAssembly.finiteBox_cylinder_abs_sub_le_farConnection_of_good
    BS BD jS jD GO e (αS ηS) (αD ηD) hq hp₀ hp₁ J S hJS hJD he C D
    roots center r hU hgood hD
  rw [← BS.finiteVolumeLaw_real_eq_conditionalLaw_real_of_dependsOn
    hq hp₁.le αS ηS (dependsOnCoordinates_cylinder J S) hJS,
    ← BD.finiteVolumeLaw_real_eq_conditionalLaw_real_of_dependsOn
    hq hp₁.le αD ηD (dependsOnCoordinates_cylinder J S) hJD]
  exact h


/-- End-to-end DLR uniqueness from the actual nested finite-volume arm
estimate.  Each extremal pair may use its own outer/inner subsequences.  The
premise is on closed-exterior finite-volume laws, exactly the output of
`NestedFiniteAssembly`; the product construction above turns it into the
conditional reverse-martingale interface. -/
theorem eq_dlr_of_pairwise_finiteVolume_farConnection
    {V : Type u} {G : SimpleGraph V} [Countable V] [G.LocallyFinite]
    (hG : G.Connected) (exh : BoxExhaustion G.edgeSet)
    (Φ : BoundaryAssignment exh.box) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (μ ν : ProbabilityMeasure (Configuration G.edgeSet))
    (hμ : μ ∈ DLRMeasures exh Φ hq hp) (hν : ν ∈ DLRMeasures exh Φ hq hp)
    (p' : unitInterval)
    (hnonperc : ∀ᵐ ω ∂(percolation G p'), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V) (center : Finset G.edgeSet → V)
    (width : Finset G.edgeSet → ℕ)
    (hwidth : ∀ I, ∀ a ∈ roots I, G.dist (center I) a ≤ width I)
    (hpair : ∀ κ ξ : ProbabilityMeasure (Configuration G.edgeSet),
      FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration G.edgeSet) ↦
          (η : Measure (Configuration G.edgeSet))) '' DLRMeasures exh Φ hq hp)
        (κ : Measure (Configuration G.edgeSet)) →
      FK.IsExtremalIn
        ((fun η : ProbabilityMeasure (Configuration G.edgeSet) ↦
          (η : Measure (Configuration G.edgeSet))) '' DLRMeasures exh Φ hq hp)
        (ξ : Measure (Configuration G.edgeSet)) →
      ∃ outer inner : ℕ → ℕ, Tendsto outer atTop atTop ∧ Tendsto inner atTop atTop ∧
        ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)),
          ∀ᵐ z ∂((κ : Measure (Configuration G.edgeSet)).prod
            (ξ : Measure (Configuration G.edgeSet))), ∀ᶠ n in atTop,
            |(((exh.box (outer n)).finiteVolumeLaw hq hp
                (Φ.partition (outer n)
                  (FKLimit.exteriorRestriction (exh.box (outer n)).edges z.1)) :
                Measure (Configuration G.edgeSet)).real (cylinder I S)) -
              (((exh.box (inner n)).finiteVolumeLaw hq hp
                (Φ.partition (inner n)
                  (FKLimit.exteriorRestriction (exh.box (inner n)).edges z.2)) :
                Measure (Configuration G.edgeSet)).real (cylinder I S))| ≤
              (percolation G p').real
                (NestedAssembly.farConnection G (roots I) (center I) (n + width I))) :
    μ = ν := by
  apply eq_dlr_of_pairwise_hasVanishingNestedExteriorCouplingError
    exh Φ hq hp μ ν hμ hν
  intro κ ξ hextκ hextξ
  rcases hpair κ ξ hextκ hextξ with ⟨outer, inner, houter, hinner, hbound⟩
  exact ⟨outer, inner, houter, hinner,
    hasVanishingNestedExteriorCouplingError_of_finiteVolume_farConnection
      hG exh Φ outer inner houter hinner hq hp κ ξ p' hnonperc
      roots center width hwidth hbound⟩

end FK.InfiniteVolume
