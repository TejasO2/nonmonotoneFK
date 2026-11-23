import FK.ClassicalCoupling
import FK.ReverseMartingale
import FK.AGInfiniteLimit
import FK.StrongUniqueness

/-!
# Nested arm estimates and uniqueness of FK weak limits

This file assembles the limiting part of the classical subcritical uniqueness
argument.  It does not prove the finite coupling Lemma 2.1: the nested
absolute-difference estimate is an explicit hypothesis.  The new step is that
its error may be the probability of a finite union of genuine one-arm events
under a nonpercolating upper law.  Those errors tend to zero, and hence two
FK weak limits agree on all finite-base cylinders.

The Bernoulli corollary uses the actual `percolationProb = 0` hypothesis at
every root, rather than silently inferring subcriticality from a numerical
comparison of critical parameters.
-/

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology

namespace FK.InfiniteVolume.NestedAssembly

open CurvatureVariance.Infra.Percolation

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-- The event that the open cluster based at `o` is infinite. -/
def infiniteOpenCluster (G : SimpleGraph V) (o : V) : Set (G.edgeSet → Bool) :=
  {ω | {x | OpenConnected G ω Set.univ o x}.Infinite}

/-- The simultaneous one-arm event for a finite set of possible starting
vertices.  This is the geometric error controlled by equation (9). -/
def finiteRootArms (G : SimpleGraph V) (A : Finset V) (n : ℕ) :
    Set (G.edgeSet → Bool) :=
  ⋃ a ∈ A, armEvent G a n

lemma measurableSet_finiteRootArms [Countable V] (A : Finset V) (n : ℕ) :
    MeasurableSet (finiteRootArms G A n) := by
  exact A.measurableSet_biUnion (fun a _ha ↦ measurableSet_armEvent a n)

/-- Almost-sure nonpercolation nullifies the infinite-cluster event at each
fixed root.  No uncountable intersection of null sets is involved. -/
lemma infiniteOpenCluster_measure_eq_zero_of_ae_nonPercolating
    (μ : Measure (G.edgeSet → Bool)) (o : V)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    μ (infiniteOpenCluster G o) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hμ] with ω hω
  intro hinf
  exact hinf (hω o)

/-- Under an almost-surely nonpercolating law, the real probability of a fixed
one-arm event tends to zero by continuity from above. -/
theorem tendsto_measureReal_armEvent_of_ae_nonPercolating
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ] (o : V)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    Tendsto (fun n ↦ μ.real (armEvent G o n)) atTop (𝓝 0) := by
  have hlim := AGGadget.tendsto_measure_armEvent hG o μ
  change Tendsto (fun n ↦ μ (armEvent G o n)) atTop
    (𝓝 (μ (infiniteOpenCluster G o))) at hlim
  rw [infiniteOpenCluster_measure_eq_zero_of_ae_nonPercolating μ o hμ] at hlim
  have hreal := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hlim
  simpa only [Function.comp_def, measureReal_def, ENNReal.toReal_zero] using hreal

/-- The real probability of arms from any fixed finite set of roots tends to
zero.  Countable subadditivity is needed only across a genuine `Finset`. -/
theorem tendsto_measureReal_finiteRootArms_of_ae_nonPercolating
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (A : Finset V) (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    Tendsto (fun n ↦ μ.real (finiteRootArms G A n)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n ↦ ∑ a ∈ A, μ.real (armEvent G a n)) atTop
      (𝓝 (∑ _a ∈ A, (0 : ℝ))) := by
    exact tendsto_finsetSum A fun a _ha ↦
      tendsto_measureReal_armEvent_of_ae_nonPercolating hG μ a hμ
  simp only [Finset.sum_const_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun _n ↦ measureReal_nonneg
  · exact Eventually.of_forall fun _n ↦ measureReal_biUnion_finset_le A _

/-- Open connection from a finite set of vertices to a prescribed target set. -/
def connectsFinsetTo (G : SimpleGraph V) (A : Finset V) (W : Set V) :
    Set (G.edgeSet → Bool) :=
  {ω | ∃ a ∈ A, ∃ w ∈ W, OpenConnected G ω Set.univ a w}

/-- Connection from `A` to vertices at graph distance at least `r` from `o`. -/
def farConnection (G : SimpleGraph V) (A : Finset V) (o : V) (r : ℕ) :
    Set (G.edgeSet → Bool) :=
  connectsFinsetTo G A {w | r ≤ G.dist o w}

/-- A path from a bounded finite set to the outside of the `n + L` ball has
an `n`-arm from at least one of its starting vertices. -/
theorem farConnection_add_subset_finiteRootArms
    (hG : G.Connected) (A : Finset V) (o : V) (L n : ℕ)
    (hA : ∀ a ∈ A, G.dist o a ≤ L) :
    farConnection G A o (n + L) ⊆ finiteRootArms G A n := by
  rintro ω ⟨a, ha, w, hw, haw⟩
  apply Set.mem_iUnion.mpr
  refine ⟨a, Set.mem_iUnion.mpr ⟨ha, ?_⟩⟩
  exact ⟨w, le_dist_of_le_dist hG (hA a ha) hw, haw⟩

lemma measurableSet_connectsFinsetTo [Countable V] (A : Finset V) (W : Set V) :
    MeasurableSet (connectsFinsetTo G A W) := by
  rw [show connectsFinsetTo G A W =
      ⋃ a ∈ A, {ω | ∃ w ∈ W, OpenConnected G ω Set.univ a w} by
    ext ω
    simp [connectsFinsetTo]]
  exact A.measurableSet_biUnion fun a _ha ↦
    measurableSet_exists_openConnected (W := W) Set.univ a

lemma measurableSet_farConnection [Countable V] (A : Finset V) (o : V) (r : ℕ) :
    MeasurableSet (farConnection G A o r) := by
  exact measurableSet_connectsFinsetTo A _

/-- Increasing the radius makes the far-connection event smaller. -/
lemma farConnection_add_antitone (A : Finset V) (o : V) (L : ℕ) :
    Antitone (fun n ↦ farConnection G A o (n + L)) := by
  intro m n hmn ω hω
  rcases hω with ⟨a, ha, w, hw, haw⟩
  exact ⟨a, ha, w, (Nat.add_le_add_right hmn L).trans hw, haw⟩

/-- Consequently, probabilities of escaping increasingly distant metric
spheres from a fixed bounded finite set tend to zero under nonpercolation. -/
theorem tendsto_measureReal_farConnection_add_of_ae_nonPercolating
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μ : Measure (G.edgeSet → Bool)) [IsProbabilityMeasure μ]
    (A : Finset V) (o : V) (L : ℕ)
    (hA : ∀ a ∈ A, G.dist o a ≤ L)
    (hμ : ∀ᵐ ω ∂μ, ω ∈ FK.NonPercolating G) :
    Tendsto (fun n ↦ μ.real (farConnection G A o (n + L))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_measureReal_finiteRootArms_of_ae_nonPercolating hG μ A hμ)
  · exact Eventually.of_forall fun _n ↦ measureReal_nonneg
  · exact Eventually.of_forall fun n ↦ measureReal_mono
      (farConnection_add_subset_finiteRootArms hG A o L n hA) (measure_ne_top _ _)

/-- Zero percolation probability at every root gives almost-sure
nonpercolation for the actual Bernoulli product law. -/
theorem ae_nonPercolating_percolation_of_percolationProb_eq_zero
    [Countable V] (p : unitInterval)
    (hzero : ∀ o, percolationProb G o p = 0) :
    ∀ᵐ ω ∂(percolation G p), ω ∈ FK.NonPercolating G := by
  change ∀ᵐ ω ∂(percolation G p), ∀ o,
    {x | OpenConnected G ω Set.univ o x}.Finite
  rw [ae_all_iff]
  intro o
  have hz : percolation G p (infiniteOpenCluster G o) = 0 := by
    change percolation G p {ω | {x | OpenConnected G ω Set.univ o x}.Infinite} = 0
    rw [← percolationProb_eq]
    exact hzero o
  have h := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [h] with ω hω
  simpa only [infiniteOpenCluster, Set.mem_ofPred_eq, Set.Infinite, not_not] using hω

/-- Abstract nested-limits assembly.  The sequences are arbitrary weakly
convergent probability laws on the same global configuration space.  The only
coupling input is the displayed eventual bound, with an error controlled by a
finite union of arms of the nonpercolating upper law `ρ`. -/
theorem probabilityMeasure_eq_of_nested_finiteRootArm_bounds
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (μs νs : ℕ → ProbabilityMeasure (G.edgeSet → Bool))
    (μ ν ρ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (hρ : ∀ᵐ ω ∂(ρ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)) (m : ℕ),
      ∀ᶠ n in atTop,
        |(μs n : Measure (G.edgeSet → Bool)).real (cylinder I S) -
          (νs m : Measure (G.edgeSet → Bool)).real (cylinder I S)| ≤
        (ρ : Measure (G.edgeSet → Bool)).real (finiteRootArms G (roots I) m)) :
    μ = ν := by
  apply Subtype.ext
  apply FKModel.measure_ext_of_eq_on_boolCylinders
    (μ : Measure (G.edgeSet → Bool)) (ν : Measure (G.edgeSet → Bool))
  intro I S
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  apply FKModel.eq_of_tendsto_of_eventually_abs_sub_le
    ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto μs μ).mp hμ I S)
    ((tendsto_probabilityMeasure_iff_cylinder_real_tendsto νs ν).mp hν I S)
    (tendsto_measureReal_finiteRootArms_of_ae_nonPercolating hG
      (ρ : Measure (G.edgeSet → Bool)) (roots I) hρ)
  exact hbound I S

/-- **Nested FK weak-limit assembly.**  Two genuine finite-volume FK weak
limits, possibly along different exhaustions and boundary sequences, coincide
whenever the equation-(9) error for each cylinder is eventually bounded by the
finite-root arm probability of a nonpercolating upper law.

This is not a replacement for Lemma 2.1: `hbound` is precisely the finite
nested-box coupling estimate still to be constructed. -/
theorem eq_of_isFKLimit_of_nested_finiteRootArm_bounds
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (exhS exhD : BoxExhaustion G.edgeSet) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exhS.box n).BoundaryPartition)
    (β : ∀ n, (exhD.box n).BoundaryPartition)
    (μ ν ρ : ProbabilityMeasure (G.edgeSet → Bool))
    (hμ : IsFKLimit exhS hq hp α μ) (hν : IsFKLimit exhD hq hp β ν)
    (hρ : ∀ᵐ ω ∂(ρ : Measure (G.edgeSet → Bool)), ω ∈ FK.NonPercolating G)
    (roots : Finset G.edgeSet → Finset V)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)) (m : ℕ),
      ∀ᶠ n in atTop,
        |(((exhS.box n).finiteVolumeLaw hq hp (α n)) :
            Measure (G.edgeSet → Bool)).real (cylinder I S) -
          (((exhD.box m).finiteVolumeLaw hq hp (β m)) :
            Measure (G.edgeSet → Bool)).real (cylinder I S)| ≤
        (ρ : Measure (G.edgeSet → Bool)).real (finiteRootArms G (roots I) m)) :
    μ = ν := by
  exact probabilityMeasure_eq_of_nested_finiteRootArm_bounds hG
    (fun n ↦ (exhS.box n).finiteVolumeLaw hq hp (α n))
    (fun m ↦ (exhD.box m).finiteVolumeLaw hq hp (β m)) μ ν ρ hμ hν hρ roots hbound

/-- Bernoulli-specialized nested FK weak-limit assembly.  The upper error law
is the genuine independent bond-percolation measure at `p'`; `hzero` is the
actual zero-percolation hypothesis at every root.  The error event is an open
connection from a bounded finite vertex set to the sphere at distance
`m + width I`, so the one-arm containment is proved rather than assumed. -/
theorem eq_of_isFKLimit_of_nested_bernoulliArm_bounds
    [Countable V] [G.LocallyFinite] (hG : G.Connected)
    (exhS exhD : BoxExhaustion G.edgeSet) {q p : NNReal}
    (hq : 0 < q) (hp : p ≤ 1)
    (α : ∀ n, (exhS.box n).BoundaryPartition)
    (β : ∀ n, (exhD.box n).BoundaryPartition)
    (μ ν : ProbabilityMeasure (G.edgeSet → Bool)) (p' : unitInterval)
    (hμ : IsFKLimit exhS hq hp α μ) (hν : IsFKLimit exhD hq hp β ν)
    (hzero : ∀ o, percolationProb G o p' = 0)
    (roots : Finset G.edgeSet → Finset V)
    (center : Finset G.edgeSet → V) (width : Finset G.edgeSet → ℕ)
    (hwidth : ∀ I, ∀ a ∈ roots I, G.dist (center I) a ≤ width I)
    (hbound : ∀ (I : Finset G.edgeSet) (S : Set (I → Bool)) (m : ℕ),
      ∀ᶠ n in atTop,
        |(((exhS.box n).finiteVolumeLaw hq hp (α n)) :
            Measure (G.edgeSet → Bool)).real (cylinder I S) -
          (((exhD.box m).finiteVolumeLaw hq hp (β m)) :
            Measure (G.edgeSet → Bool)).real (cylinder I S)| ≤
        (percolation G p').real
          (farConnection G (roots I) (center I) (m + width I))) :
    μ = ν := by
  let ρ : ProbabilityMeasure (G.edgeSet → Bool) := ⟨percolation G p', inferInstance⟩
  refine eq_of_isFKLimit_of_nested_finiteRootArm_bounds hG exhS exhD hq hp α β μ ν ρ
    hμ hν ?_ roots ?_
  · change ∀ᵐ ω ∂(percolation G p'), ω ∈ FK.NonPercolating G
    exact ae_nonPercolating_percolation_of_percolationProb_eq_zero p' hzero
  · intro I S m
    filter_upwards [hbound I S m] with n hn
    exact hn.trans (measureReal_mono
      (farConnection_add_subset_finiteRootArms hG (roots I) (center I) (width I) m
        (hwidth I)) (measure_ne_top _ _))

end FK.InfiniteVolume.NestedAssembly
