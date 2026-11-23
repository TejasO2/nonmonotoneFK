import FK.UpperCutsetComparison
import FK.InfiniteVolume

/-!
# Bernoulli product factorization over a finite box

An infinite product of Bernoulli measures splits into independent exterior and
interior products across a `FiniteBox`.  This module is the measure-theoretic
bridge from uniform interior comparisons to actual DLR laws.  The exterior law
is matched explicitly; no comparison between different exterior configurations
is hidden in the statement.
-/

namespace FK.InfiniteVolume

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal unitInterval Classical

noncomputable section

local instance boundaryPartitionMeasurableSpace' (V : Type*) : MeasurableSpace (Setoid V) := ⊤
local instance finiteSetoid' (V : Type*) [Finite V] : Finite (Setoid V) := by
  classical
  apply Finite.of_injective (fun α : Setoid V ↦ α.r)
  intro α β h
  exact Setoid.eq_iff_rel_eq.mpr h

namespace FiniteBox

variable {E : Type*} (B : FiniteBox E)

/-- The infinite Bernoulli product factors exactly across the exterior/interior
split of a finite box. -/
theorem map_splitEquiv_bernoulliProduct (r : E → unitInterval) :
    Measure.map B.splitEquiv (FKLimit.bernoulliProduct r : Measure (Configuration E)) =
      (Measure.infinitePi (fun e : {e : E // e ∉ B.edges} =>
        bernoulliMeasure true false (r e.1))).prod
        (Measure.pi (fun e : B.edges => bernoulliMeasure true false (r e.1))) := by
  let μ : E → Measure Bool := fun e => bernoulliMeasure true false (r e)
  have hi : ProbabilityTheory.iIndepFun (fun i (ω : Configuration E) => ω i)
      (Measure.infinitePi μ) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (X := fun (_ : E) (x : Bool) => x) (by fun_prop)
  have hind : ProbabilityTheory.IndepFun
      (fun (ω : Configuration E) (e : {e : E // e ∉ B.edges}) => ω e.1)
      (fun (ω : Configuration E) (e : B.edges) => ω e.1)
      (Measure.infinitePi μ) :=
    hi.indepFun_set ({e : E | e ∉ B.edges}) (B.edges : Set E)
      (by simp [Set.disjoint_left]) (fun e => measurable_pi_apply e)
  have hj := hind.map_prod_eq_prod_map_map
    (Measurable.of_eval (fun e => measurable_pi_apply e.1)).aemeasurable
    (Measurable.of_eval (fun e => measurable_pi_apply e.1)).aemeasurable
  have hout : (Measure.infinitePi μ).map
      (fun (ω : Configuration E) (e : {e : E // e ∉ B.edges}) => ω e.1) =
      Measure.infinitePi (fun e : {e : E // e ∉ B.edges} => μ e.1) := by
    change Measure.map (Set.domRestrict {e : E | e ∉ B.edges}) (Measure.infinitePi μ) =
      Measure.infinitePi (fun e : {e : E // e ∉ B.edges} => μ e.1)
    exact Measure.infinitePi_map_restrict' μ
  have hin : (Measure.infinitePi μ).map B.edges.restrict =
      Measure.pi (fun e : B.edges => μ e.1) := by
    rw [Measure.infinitePi_map_restrict]
  have hin' : (Measure.infinitePi μ).map
      (fun (ω : Configuration E) (e : B.edges) => ω e.1) =
      Measure.pi (fun e : B.edges => μ e.1) := hin
  rw [hout, hin'] at hj
  change Measure.map
    (fun (ω : Configuration E) =>
      ((fun e : {e : E // e ∉ B.edges} => ω e.1), (fun e : B.edges => ω e.1)))
      (Measure.infinitePi μ) = _
  simpa only [μ] using hj

/-- The factored form of the infinite Bernoulli product through `B.glue`. -/
lemma bernoulliProduct_eq_map_glue_prod (r : E → unitInterval) :
    (FKLimit.bernoulliProduct r : Measure (Configuration E)) =
      Measure.map B.glue
        ((Measure.infinitePi (fun e : {e : E // e ∉ B.edges} =>
          bernoulliMeasure true false (r e.1))).prod
          (Measure.pi (fun e : B.edges => bernoulliMeasure true false (r e.1)))) := by
  exact B.splitEquiv.map_apply_eq_iff_map_symm_apply_eq.mp
    (B.map_splitEquiv_bernoulliProduct r)

lemma isUpperSet_glue_fiber {A : Set (Configuration E)} (hA : IsUpperSet A)
    (η : B.Exterior) : IsUpperSet ((fun ω : B.Interior => B.glue (η, ω)) ⁻¹' A) := by
  intro ω ξ hωξ hω
  apply hA _ hω
  intro e
  by_cases he : e ∈ B.edges
  · simpa only [glue, he, ↓reduceDIte] using hωξ ⟨e, he⟩
  · simp [glue, he]

/-- A uniform lower comparison of the finite interior Bernoulli product with
every conditional finite FK law transports to an actual DLR law with the same
exterior product law. -/
theorem stochasticallyDominates_of_isDLR_local_lower
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    (r : E → unitInterval)
    (hexterior : (B.exteriorMeasure μ : Measure B.Exterior) =
      Measure.infinitePi (fun e : {e : E // e ∉ B.edges} =>
        bernoulliMeasure true false (r e.1)))
    (hlocal : ∀ η, FKEnhancement.StochasticallyDominates
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1))
      (B.graph.fkMeasure hq hp (α η))) :
    FKLimit.StochasticallyDominates μ (FKLimit.bernoulliProduct r) := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  intro A hA hAupper
  change ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A).toNNReal ≤
    ((μ : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [B.bernoulliProduct_eq_map_glue_prod,
    Measure.map_apply hg hA, Measure.prod_apply (hg hA)]
  rw [B.measure_eq_map_glue_compProd hq hp α hα μ hμ, hexterior,
    Measure.map_apply hg hA, Measure.compProd_apply (hg hA)]
  exact lintegral_mono (fun η => hlocal η _
    (B.measurable_glue_const_left η hA) (B.isUpperSet_glue_fiber hAupper η))


/-- The corresponding upper comparison for an actual DLR law with the same
exterior product law. -/
theorem stochasticallyDominates_of_isDLR_local_upper
    {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)
    (α : B.Exterior → B.BoundaryPartition) (hα : Measurable α)
    (μ : ProbabilityMeasure (Configuration E)) (hμ : B.IsDLR hq hp α hα μ)
    (r : E → unitInterval)
    (hexterior : (B.exteriorMeasure μ : Measure B.Exterior) =
      Measure.infinitePi (fun e : {e : E // e ∉ B.edges} =>
        bernoulliMeasure true false (r e.1)))
    (hlocal : ∀ η, FKEnhancement.StochasticallyDominates
      (B.graph.fkMeasure hq hp (α η))
      (FKEnhancement.bernoulliProduct (fun e : B.edges => r e.1))) :
    FKLimit.StochasticallyDominates (FKLimit.bernoulliProduct r) μ := by
  have hg : Measurable B.glue := B.splitEquiv.symm.measurable
  intro A hA hAupper
  change ((μ : Measure (Configuration E)) A).toNNReal ≤
    ((FKLimit.bernoulliProduct r : Measure (Configuration E)) A).toNNReal
  apply (ENNReal.toNNReal_le_toNNReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
  rw [B.bernoulliProduct_eq_map_glue_prod,
    Measure.map_apply hg hA, Measure.prod_apply (hg hA)]
  rw [B.measure_eq_map_glue_compProd hq hp α hα μ hμ, hexterior,
    Measure.map_apply hg hA, Measure.compProd_apply (hg hA)]
  exact lintegral_mono (fun η => hlocal η _
    (B.measurable_glue_const_left η hA) (B.isUpperSet_glue_fiber hAupper η))

end FiniteBox

end

end FK.InfiniteVolume
