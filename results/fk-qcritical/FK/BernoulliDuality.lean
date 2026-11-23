import FK.ConfigurationDuality

/-!
# Planar duality of inhomogeneous Bernoulli percolation

`bernoulliProduct p` is the product probability measure under which edge `e`
is open with probability `p e`.  The main theorem identifies its pushforward
under planar open/closed duality, for arbitrary edge types (finite or infinite).
-/

namespace FK.Configuration

open MeasureTheory ProbabilityTheory unitInterval Set

/-- Inhomogeneous Bernoulli bond percolation on an arbitrary edge type. -/
noncomputable def bernoulliProduct {E : Type*} (p : E → I) : Measure (E → Bool) :=
  Measure.infinitePi (fun e => Ber(true, false, p e))

instance isProbabilityMeasure_bernoulliProduct {E : Type*} (p : E → I) :
    IsProbabilityMeasure (bernoulliProduct p) := by
  unfold bernoulliProduct
  infer_instance

/-- Finite-dimensional cylinders have the required product probabilities. -/
lemma bernoulliProduct_pi {E : Type*} (p : E → I) (s : Finset E)
    (t : E → Set Bool) (ht : ∀ e ∈ s, MeasurableSet (t e)) :
    bernoulliProduct p (Set.pi s t) = ∏ e ∈ s, Ber(true, false, p e) (t e) := by
  exact Measure.infinitePi_pi _ ht

@[simp] lemma map_bernoulliMeasure_not (p : I) :
    Measure.map Bool.not (Ber(true, false, p)) = Ber(true, false, σ p) := by
  rw [map_bernoulliMeasure]
  simp only [Bool.not_true, Bool.not_false]
  simp [bernoulliMeasure_def, add_comm]

/-- Simultaneous open/closed complementation turns parameter `p` into `1-p`. -/
lemma map_not_bernoulliProduct {E : Type*} (p : E → I) :
    Measure.map (fun (ω : E → Bool) e => !(ω e)) (bernoulliProduct p) =
      bernoulliProduct (fun e => σ (p e)) := by
  unfold bernoulliProduct
  rw [Measure.infinitePi_map_pi _ (fun _ => by fun_prop)]
  congr 1
  funext e
  exact map_bernoulliMeasure_not (p e)

/-- Reindexing the edges of a product measure along an edge equivalence. -/
lemma map_reindex_bernoulliProduct {E E' : Type*} (e : E ≃ E') (p : E → I) :
    Measure.map (MeasurableEquiv.piCongrLeft (fun _ : E' => Bool) e)
      (bernoulliProduct p) = bernoulliProduct (fun f => p (e.symm f)) := by
  let μ : E' → Measure Bool := fun f => Ber(true, false, p (e.symm f))
  have h := Measure.infinitePi_map_piCongrLeft μ e
  simpa only [bernoulliProduct, μ, Equiv.symm_apply_apply] using h

/-- Section 5.2's Bernoulli duality, including inhomogeneous edge weights. -/
theorem map_dual_bernoulliProduct {E E' : Type*} (e : E ≃ E') (p : E → I) :
    Measure.map (dualMeasurableEquiv e) (bernoulliProduct p) =
      bernoulliProduct (fun f => σ (p (e.symm f))) := by
  let N : (E → Bool) → (E → Bool) := fun ω x => !(ω x)
  let R := MeasurableEquiv.piCongrLeft (fun _ : E' => Bool) e
  have hN : Measurable N := by
    apply measurable_pi_lambda
    intro x
    change Measurable (fun ω : E → Bool => !(ω x))
    fun_prop
  have hdecomp : (dualMeasurableEquiv e : (E → Bool) → (E' → Bool)) = R ∘ N := by
    funext ω f
    simp [R, N, dualMeasurableEquiv, dualEquiv, dualConfig, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply]
  rw [hdecomp, ← Measure.map_map R.measurable hN]
  change Measure.map R (Measure.map N (bernoulliProduct p)) = _
  rw [show Measure.map N (bernoulliProduct p) =
    bernoulliProduct (fun x => σ (p x)) from map_not_bernoulliProduct p]
  exact map_reindex_bernoulliProduct e (fun x => σ (p x))

/-- The dual form of an inhomogeneous lower stochastic bound.  This is the
measure-theoretic content of the displayed dual domination in the proof of
Theorem 1.11. -/
theorem dual_stochDom_bernoulliProduct {E E' : Type*} (e : E ≃ E') (p : E → I)
    (φ : Measure (E → Bool)) [IsProbabilityMeasure φ]
    (h : StochDom (bernoulliProduct p) φ) :
    StochDom (Measure.map (dualMeasurableEquiv e) φ)
      (bernoulliProduct (fun f => σ (p (e.symm f)))) := by
  have hdual := stochDom_dual e (bernoulliProduct p) φ h
  rwa [map_dual_bernoulliProduct] at hdual

end FK.Configuration
