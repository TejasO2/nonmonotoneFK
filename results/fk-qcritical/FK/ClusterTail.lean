/-
# Zero--one law for percolation events depending on finitely many edges

This file proves that the event that a configuration possesses an infinite open
cluster has probability `0` or `1` under an i.i.d. Bernoulli edge law, and that
it is measurable for the tail sigma-algebra on edge configurations.

The measure-theoretic input is Kolmogorov's argument in the following form: if a
measurable event `A` is independent of every event depending on finitely many
coordinates (a cylinder), then `A` is independent of the full product
sigma-algebra and hence of itself, so `μ A = (μ A)^2`.
-/
import FK.ClusterCover

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval

namespace FK.ClusterTail

open CurvatureVariance.Infra.Percolation
open FK.ClusterCover

/-! ### Measurability -/

variable {V : Type*}

lemma measurable_openCluster (G : SimpleGraph V) [Countable V] (x : V) :
    Measurable fun ω : G.edgeSet → Bool => {y | OpenConnected G ω Set.univ x y} :=
  measurable_set_iff.mpr fun y => by
    rw [← measurableSet_setOfPred]
    exact measurableSet_openConnected Set.univ x y

theorem measurableSet_hasInfiniteCluster (G : SimpleGraph V) [Countable V] :
    MeasurableSet {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} := by
  have hset : {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} =
      ⋃ x : V, {ω | {y | OpenConnected G ω Set.univ x y}.Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, HasInfiniteCluster, clusterAvoid_empty_eq]
  rw [hset]
  exact MeasurableSet.iUnion fun x =>
    MeasurableSet.setOfPred_infinite.preimage (measurable_openCluster G x)

/-- The existence of an infinite open cluster is an increasing event. -/
theorem isUpperSet_hasInfiniteCluster (G : SimpleGraph V) :
    IsUpperSet {ω : G.edgeSet → Bool | HasInfiniteCluster G ω} := by
  rintro ω ω' hle ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [clusterAvoid_empty_eq] at hx ⊢
  exact hx.mono fun y hy => hy.mono_config hle

/-- The existence of an infinite open cluster depends only on the edges outside
any finite set of edges. -/
theorem dependsOn_hasInfiniteCluster (G : SimpleGraph V) (S : Set G.edgeSet)
    (hS : S.Finite) :
    DependsOn (· ∈ {ω : G.edgeSet → Bool | HasInfiniteCluster G ω}) Sᶜ := by
  intro ω ω' hagree
  exact propext (hasInfiniteCluster_congr (G := G) (A := Subtype.val '' S)
    (Set.Finite.image Subtype.val hS)
    (fun e he => hagree e (by
      intro hmem
      exact he (Set.mem_image_of_mem _ hmem))))

/-! ### Kolmogorov's zero--one argument -/

/-- **Zero--one law from cylinder independence.**  A measurable event that
depends only on the coordinates outside every finite set, and is independent of
every cylinder event, has probability zero or one. -/
theorem measure_eq_zero_or_one_of_cylinder_indep {ι : Type*} {μ : Measure (ι → Bool)}
    [IsProbabilityMeasure μ] {A : Set (ι → Bool)} (hA : MeasurableSet A)
    (hdep : ∀ S : Finset ι, DependsOn (· ∈ A) ((S : Set ι))ᶜ)
    (hind : ∀ (S : Finset ι) (B : Set (ι → Bool)), MeasurableSet B →
      DependsOn (· ∈ B) (S : Set ι) → μ (A ∩ B) = μ A * μ B) :
    μ A = 0 ∨ μ A = 1 := by
  classical
  set P : Set (Set (ι → Bool)) :=
    {B | MeasurableSet B ∧ ∃ S : Finset ι, DependsOn (· ∈ B) (S : Set ι)} with hP
  have hPpi : IsPiSystem P := by
    intro B hB C hC _
    rw [hP] at hB hC ⊢
    obtain ⟨hB, S, hBS⟩ := hB
    obtain ⟨hC, T, hCT⟩ := hC
    refine ⟨hB.inter hC, S ∪ T, ?_⟩
    intro u v huv
    have h1 : (u ∈ B) = (v ∈ B) := hBS (fun x hx => huv x (Finset.mem_union_left T hx))
    have h2 : (u ∈ C) = (v ∈ C) := hCT (fun x hx => huv x (Finset.mem_union_right S hx))
    simp only [Set.mem_inter_iff, h1, h2]
  have hsingleton : IsPiSystem ({A} : Set (Set (ι → Bool))) := by
    intro B hB C hC _
    rw [Set.mem_singleton_iff] at hB hC
    rw [hB, hC, Set.inter_self]
    exact Set.mem_singleton A
  have hindSets : IndepSets ({A} : Set (Set (ι → Bool))) P μ := by
    intro t1 t2 ht1 ht2
    rw [Set.mem_singleton_iff] at ht1
    subst ht1
    rw [hP] at ht2
    obtain ⟨ht2meas, S, ht2S⟩ := ht2
    simpa using hind S t2 ht2meas ht2S
  have hgen : MeasurableSpace.generateFrom P = MeasurableSpace.pi := by
    refine le_antisymm ?_ ?_
    · exact MeasurableSpace.generateFrom_le (fun B hB => by rw [hP] at hB; exact hB.1)
    have hprojections : ({B : Set (ι → Bool) |
        ∃ (i : ι) (s : Set Bool), MeasurableSet s ∧ (fun ω : ι → Bool => ω i) ⁻¹' s = B} :
          Set (Set (ι → Bool))) ⊆ P := by
      rintro B ⟨i, s, hs, rfl⟩
      rw [hP]
      refine ⟨hs.preimage (measurable_pi_apply i), {i}, fun u v huv => ?_⟩
      have h1 : u i = v i := huv i (Finset.mem_singleton_self i)
      simp only [Set.mem_preimage, h1]
    calc MeasurableSpace.pi
        = MeasurableSpace.generateFrom {B : Set (ι → Bool) |
            ∃ (i : ι) (s : Set Bool), MeasurableSet s ∧
              (fun ω : ι → Bool => ω i) ⁻¹' s = B} :=
          MeasurableSpace.pi_eq_generateFrom_projections
      _ ≤ MeasurableSpace.generateFrom P := MeasurableSpace.generateFrom_mono hprojections
  have hindep : Indep (MeasurableSpace.generateFrom ({A} : Set (Set (ι → Bool))))
      (MeasurableSpace.generateFrom P) μ :=
    IndepSets.indep' (fun B hB => by rw [Set.mem_singleton_iff] at hB; subst hB; exact hA)
      (fun B hB => hB.1) hsingleton hPpi hindSets
  have hAI : MeasurableSet[MeasurableSpace.generateFrom ({A} : Set (Set (ι → Bool)))] A :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton A)
  have hAgen : MeasurableSet[MeasurableSpace.generateFrom P] A := by
    rw [hgen]
    exact hA
  have hself : μ A = μ A * μ A := by
    have h := hindep A A hAI hAgen
    simpa using h
  have hfin : μ A ≠ ⊤ := measure_ne_top μ A
  have hle1 : (μ A).toReal ≤ 1 := by
    have hle : μ A ≤ μ Set.univ := measure_mono (Set.subset_univ A)
    have h' := ENNReal.toReal_mono (by simp) hle
    simpa using h'
  have hreal : (μ A).toReal = (μ A).toReal * (μ A).toReal := by
    rw [← ENNReal.toReal_mul, ← hself]
  have hfac : (μ A).toReal * (1 - (μ A).toReal) = 0 := by
    rw [mul_sub, mul_one, ← hreal, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h1
  · left
    rcases (ENNReal.toReal_eq_zero_iff (μ A)).mp h0 with h | h
    · exact h
    · exact absurd h hfin
  · right
    have : (μ A).toReal = 1 := by linarith
    exact (ENNReal.toReal_eq_one_iff (μ A)).mp this

/-- Bernoulli edge laws: an event that depends only on the coordinates outside
every finite set has probability zero or one. -/
theorem bernoulliProduct_eq_zero_or_one {ι : Type*} (p : I) {A : Set (ι → Bool)}
    (hA : MeasurableSet A)
    (hdep : ∀ S : Finset ι, DependsOn (· ∈ A) ((S : Set ι))ᶜ) :
    bernoulliProduct ι p A = 0 ∨ bernoulliProduct ι p A = 1 := by
  refine measure_eq_zero_or_one_of_cylinder_indep hA hdep ?_
  intro S B hB hBS
  exact measure_inter_eq_mul_of_dependsOn hA hB (hdep S) hBS
    (Set.disjoint_left.mpr fun a ha ha' => ha ha') p

/-- **Percolation zero--one law.**  Under i.i.d. Bernoulli bond percolation, the
probability that an infinite open cluster exists is zero or one. -/
theorem percolation_hasInfiniteCluster_zero_one (G : SimpleGraph V) [Countable V] (p : I) :
    percolation G p {ω | HasInfiniteCluster G ω} = 0 ∨
      percolation G p {ω | HasInfiniteCluster G ω} = 1 :=
  bernoulliProduct_eq_zero_or_one p (measurableSet_hasInfiniteCluster G)
    (fun S => dependsOn_hasInfiniteCluster G (S : Set G.edgeSet) S.finite_toSet)

/-- If a.s. no infinite open cluster exists, the cluster of every root is a.s.
finite, so the percolation probability vanishes. -/
theorem percolationProb_eq_zero_of_noInfiniteCluster {G : SimpleGraph V} {o : V} {p : I}
    (h : percolation G p {ω | HasInfiniteCluster G ω} = 0) :
    percolationProb G o p = 0 := by
  rw [percolationProb_eq]
  refine measure_mono_null ?_ h
  intro ω hω
  exact ⟨o, by rwa [clusterAvoid_empty_eq]⟩

end FK.ClusterTail
