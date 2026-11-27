import FK.CactusGraph
import FK.AGTree.TwoRateCritical
import FK.BernoulliDuality

/-!
# Exact product law for the triangle cactus
-/

namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation
open scoped ENNReal NNReal unitInterval Sym2

/-- The Boolean direct-or-bypass map on one triangle. -/
def blockOpen (ω : Fin 3 → Bool) : Bool := ω 0 || (ω 1 && ω 2)

/-- The effective connection probability of one triangle. -/
noncomputable def effectiveRate (r : Fin 3 → unitInterval) : unitInterval :=
  ⟨(r 0 : ℝ) + (r 1 : ℝ) * (r 2 : ℝ) -
      (r 0 : ℝ) * ((r 1 : ℝ) * (r 2 : ℝ)), by
    have hr0 := unitInterval.nonneg (r 0)
    have hr1 := unitInterval.nonneg (r 1)
    have hr2 := unitInterval.nonneg (r 2)
    have hs0 := unitInterval.le_one (r 0)
    have hs1 := unitInterval.le_one (r 1)
    have hs2 := unitInterval.le_one (r 2)
    have hp0 : 0 ≤ (r 1 : ℝ) * (r 2 : ℝ) := mul_nonneg hr1 hr2
    have hp1 : (r 1 : ℝ) * (r 2 : ℝ) ≤ 1 := by nlinarith
    constructor
    · have h := mul_nonneg hr0 (sub_nonneg.mpr hp1)
      nlinarith
    · have h := mul_nonneg (sub_nonneg.mpr hs0) (sub_nonneg.mpr hp1)
      nlinarith⟩

@[simp] lemma coe_effectiveRate (r : Fin 3 → unitInterval) :
    (effectiveRate r : ℝ) = (r 0 : ℝ) + (r 1 : ℝ) * (r 2 : ℝ) -
      (r 0 : ℝ) * ((r 1 : ℝ) * (r 2 : ℝ)) := rfl

/-- The exact one-block image law, computed on all eight Boolean inputs. -/
theorem infinitePi_map_blockOpen (r : Fin 3 → unitInterval) :
    (Measure.infinitePi (fun k : Fin 3 => bernoulliMeasure true false (r k))).map
      blockOpen = bernoulliMeasure true false (effectiveRate r) := by
  let z : Fin 3 → Bool := ![false, false, false]
  let o : Fin 3 → Bool := ![false, false, true]
  let t : Fin 3 → Bool := ![false, true, false]
  have hpre : blockOpen ⁻¹' {false} = (↑({z, o, t} : Finset (Fin 3 → Bool)) : Set _) := by
    ext b
    have hb : b = ![b 0, b 1, b 2] := by
      funext k
      fin_cases k <;> rfl
    rw [hb]
    cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
      simp [blockOpen, z, o, t]
  have hfalse :
      (Measure.infinitePi (fun k : Fin 3 => bernoulliMeasure true false (r k)))
          (blockOpen ⁻¹' {false}) =
        bernoulliMeasure true false (effectiveRate r) {false} := by
    rw [hpre, ← sum_measure_singleton]
    simp [Measure.infinitePi_singleton_of_fintype, Fin.prod_univ_three,
      bernoulliMeasure_false, z, o, t]
    apply (ENNReal.toReal_eq_toReal_iff'
      (by
        simp only [← ENNReal.coe_mul, ← ENNReal.coe_add]
        exact ENNReal.coe_ne_top)
      (by exact ENNReal.coe_ne_top)).mp
    simp only [← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_toReal]
    norm_cast
    apply Subtype.ext
    simp [effectiveRate]
    ring
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)]
  cases b with
  | false => exact hfalse
  | true =>
      have hpretrue : blockOpen ⁻¹' {true} = (blockOpen ⁻¹' {false})ᶜ := by
        ext b
        cases hb : blockOpen b <;> simp [hb]
      rw [hpretrue, measure_compl (measurableSet_singleton false |>.preimage (by fun_prop))
        (measure_ne_top _ _), hfalse]
      simp only [measure_univ, bernoulliMeasure_true, bernoulliMeasure_false]
      apply ENNReal.sub_eq_of_eq_add (by simp)
      rw [← ENNReal.ofReal_add (unitInterval.nonneg _)
        (sub_nonneg.mpr (unitInterval.le_one _))]
      simp

end Ultra.TriangleCactus


namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation
open scoped ENNReal NNReal unitInterval Sym2

/-- The inhomogeneous rate attached to each actual bond. -/
noncomputable def profile (r : Fin 3 → unitInterval) (e : graph.edgeSet) : unitInterval :=
  r (bondEquiv.symm e).2

/-- Independent Bernoulli bonds on the expanded graph itself. -/
noncomputable def actualLaw (r : Fin 3 → unitInterval) : Measure (graph.edgeSet → Bool) :=
  Measure.infinitePi (fun e : graph.edgeSet => bernoulliMeasure true false (profile r e))

instance (r : Fin 3 → unitInterval) : IsProbabilityMeasure (actualLaw r) := by
  unfold actualLaw
  infer_instance

/-- The same product on the labelled coordinate space. -/
noncomputable def labelLaw (r : Fin 3 → unitInterval) :
    Measure (G.edgeSet × Fin 3 → Bool) :=
  Measure.infinitePi (fun x : G.edgeSet × Fin 3 => bernoulliMeasure true false (r x.2))

instance (r : Fin 3 → unitInterval) : IsProbabilityMeasure (labelLaw r) := by
  unfold labelLaw
  infer_instance

/-- Junction-tree edge `e` is effective-open exactly when its direct bond or
both of its two spoke bonds are open. -/
noncomputable def effective (ω : graph.edgeSet → Bool) (e : G.edgeSet) : Bool :=
  ω (baseEdge e) || (ω (leftSpoke e) && ω (rightSpoke e))

/-- The same map before transporting to the actual bond subtype. -/
def labelEffective (ω : G.edgeSet × Fin 3 → Bool) (e : G.edgeSet) : Bool :=
  ω (e, 0) || (ω (e, 1) && ω (e, 2))

lemma measurable_effective : Measurable effective := by
  apply measurable_pi_iff.2
  intro e
  fun_prop [effective]

lemma bondEquiv_symm_baseEdge (e : G.edgeSet) : bondEquiv.symm (baseEdge e) = (e, 0) := by
  apply bondEquiv.injective
  simp [bond]

lemma bondEquiv_symm_leftSpoke (e : G.edgeSet) : bondEquiv.symm (leftSpoke e) = (e, 1) := by
  apply bondEquiv.injective
  simp [bond]

lemma bondEquiv_symm_rightSpoke (e : G.edgeSet) : bondEquiv.symm (rightSpoke e) = (e, 2) := by
  apply bondEquiv.injective
  simp [bond]

@[simp] lemma profile_baseEdge (r : Fin 3 → unitInterval) (e : G.edgeSet) :
    profile r (baseEdge e) = r 0 := by
  rw [profile, bondEquiv_symm_baseEdge]

@[simp] lemma profile_leftSpoke (r : Fin 3 → unitInterval) (e : G.edgeSet) :
    profile r (leftSpoke e) = r 1 := by
  rw [profile, bondEquiv_symm_leftSpoke]

@[simp] lemma profile_rightSpoke (r : Fin 3 → unitInterval) (e : G.edgeSet) :
    profile r (rightSpoke e) = r 2 := by
  rw [profile, bondEquiv_symm_rightSpoke]

/-- Reindexing the labelled product gives exactly the original-bond product. -/
theorem map_reindex_labelLaw (r : Fin 3 → unitInterval) :
    Measure.map (MeasurableEquiv.piCongrLeft (fun _ : graph.edgeSet => Bool) bondEquiv)
      (labelLaw r) = actualLaw r := by
  exact FK.Configuration.map_reindex_bernoulliProduct bondEquiv (fun x => r x.2)

lemma effective_comp_reindex :
    effective ∘ (MeasurableEquiv.piCongrLeft (fun _ : graph.edgeSet => Bool) bondEquiv) =
      labelEffective := by
  funext ω e
  have h0 : (MeasurableEquiv.piCongrLeft (fun _ : graph.edgeSet => Bool) bondEquiv) ω
      (baseEdge e) = ω (e, 0) := by
    have hb : bondEquiv (e, 0) = baseEdge e := rfl
    rw [← hb]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : graph.edgeSet => Bool) bondEquiv ω (e, 0)
  have h1 : (MeasurableEquiv.piCongrLeft (fun _ : graph.edgeSet => Bool) bondEquiv) ω
      (leftSpoke e) = ω (e, 1) := by
    have hb : bondEquiv (e, 1) = leftSpoke e := rfl
    rw [← hb]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : graph.edgeSet => Bool) bondEquiv ω (e, 1)
  have h2 : (MeasurableEquiv.piCongrLeft (fun _ : graph.edgeSet => Bool) bondEquiv) ω
      (rightSpoke e) = ω (e, 2) := by
    have hb : bondEquiv (e, 2) = rightSpoke e := rfl
    rw [← hb]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : graph.edgeSet => Bool) bondEquiv ω (e, 2)
  change effective ((MeasurableEquiv.piCongrLeft (fun _ : graph.edgeSet => Bool) bondEquiv) ω) e =
    labelEffective ω e
  unfold effective labelEffective
  rw [h0, h1, h2]

/-- The exact pushforward on labelled coordinates, using independence of the
three edges in each triangle and disjointness of distinct triangles. -/
theorem map_labelEffective (r : Fin 3 → unitInterval) :
    Measure.map labelEffective (labelLaw r) = Ultra.law (fun _ => effectiveRate r) := by
  let C := MeasurableEquiv.curry G.edgeSet (Fin 3) Bool
  have hdecomp : labelEffective =
      (fun (f : G.edgeSet → Fin 3 → Bool) e => blockOpen (f e)) ∘ C := rfl
  rw [hdecomp, labelLaw, ← Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map (fun (f : G.edgeSet → Fin 3 → Bool) e => blockOpen (f e))
    (Measure.map C (Measure.infinitePi
      (fun x : G.edgeSet × Fin 3 => bernoulliMeasure true false (r x.2)))) = _
  dsimp only [C]
  rw [Measure.infinitePi_map_curry (fun _ : G.edgeSet =>
    fun k : Fin 3 => bernoulliMeasure true false (r k))]
  change Measure.map (fun (f : G.edgeSet → Fin 3 → Bool) e => blockOpen (f e))
    (Measure.infinitePi (fun _ : G.edgeSet => Measure.infinitePi
      (fun k : Fin 3 => bernoulliMeasure true false (r k)))) = _
  rw [Measure.infinitePi_map_pi _ (fun _ => by fun_prop)]
  simp_rw [infinitePi_map_blockOpen r]

/-- **Exact effective product law.**  Junction connections are independent
Bernoulli variables with rate `r₀ + r₁r₂ - r₀r₁r₂`, under the actual product law
on the original cactus bonds. -/
theorem map_effective (r : Fin 3 → unitInterval) :
    Measure.map effective (actualLaw r) = Ultra.law (fun _ => effectiveRate r) := by
  rw [← map_reindex_labelLaw r, Measure.map_map measurable_effective
    (MeasurableEquiv.measurable _), effective_comp_reindex]
  exact map_labelEffective r

end Ultra.TriangleCactus
