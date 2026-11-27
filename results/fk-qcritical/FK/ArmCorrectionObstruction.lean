import FK.NormalizedFilter
import FK.FinitePlanarDuality
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# A finite obstruction to a root-to-boundary correction identity

The graphs in this file witness that conditioning on no open path from the
endpoints of a cylinder to the wired boundary does not make the conditional
cylinder law independent of the boundary partition.  This is a finite
counterexample to that proposed shortcut, not to Theorem 5.1.
-/

open scoped BigOperators ENNReal
open MeasureTheory
open FK.Finite

namespace FK.ArmCorrectionObstruction

/-- Five edges `0-1`, `0-2`, `1-2`, `2-3`, `2-4`. -/
abbrev G : LabelledMultigraph where
  Vertex := Fin 5
  Edge := Fin 5
  source := ![0, 0, 1, 2, 2]
  target := ![1, 2, 2, 3, 4]

/-- The free boundary, together with the wired pair `3 ~ 4`. -/
@[instance_reducible] def wire34 : G.BoundaryPartition where
  r u v := u = v ∨ (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩ <;> decide

instance decidableFree : DecidableRel G.freeBoundary.r := by
  intro u v
  change Decidable (u = v)
  infer_instance

instance decidableWire34 : DecidableRel wire34.r := by
  intro u v
  change Decidable (u = v ∨ (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3))
  infer_instance

instance decidableJoins (e : G.Edge) : DecidableRel (G.Joins e) := by
  intro u v
  unfold LabelledMultigraph.Joins
  infer_instance

instance decidableConnection (ξ : G.BoundaryPartition) [DecidableRel ξ.r]
    (ω : G.Configuration) : DecidableRel (G.connectionGraph ξ ω).Adj := by
  intro u v
  change Decidable (u ≠ v ∧ (ξ.r u v ∨ ∃ e, ω e = true ∧ G.Joins e u v))
  infer_instance

instance connectedComponentFintype (ξ : G.BoundaryPartition) [DecidableRel ξ.r]
    (ω : G.Configuration) : Fintype (G.connectionGraph ξ ω).ConnectedComponent :=
  SimpleGraph.instFintypeConnectedComponent _

/-- Use the computable finite-product enumeration, not the noncomputable
configuration instance supplied for general graphs. -/
local instance computableConfig : Fintype G.Configuration := Pi.instFintype

/-- No open path from either endpoint of edge `0` to either wired leaf. -/
def good (ω : G.Configuration) : Prop :=
  ∀ a ∈ ({0, 1} : Finset (Fin 5)), ∀ b ∈ ({3, 4} : Finset (Fin 5)),
    ¬ (G.connectionGraph G.freeBoundary ω).Reachable a b

instance decidableGood : DecidablePred good := by
  intro ω
  unfold good
  infer_instance

/-- Number of open labels. -/
def openCount (ω : G.Configuration) : ℕ := FK.FinitePlane.openCard ω

/-- The actual FK weight at `q = 2`, `p = 4/5`, multiplied by `5^5`.
It is computable and integral. -/
def scaledWeight (ξ : G.BoundaryPartition) [DecidableRel ξ.r]
    (ω : G.Configuration) : ℕ :=
  4 ^ openCount ω * 2 ^ Fintype.card (G.connectionGraph ξ ω).ConnectedComponent

/-- Restricted scaled FK mass. -/
def goodMass (ξ : G.BoundaryPartition) [DecidableRel ξ.r] : ℕ :=
  ∑ ω : G.Configuration, if good ω then scaledWeight ξ ω else 0

/-- The same mass with the cylinder edge closed. -/
def goodClosedMass (ξ : G.BoundaryPartition) [DecidableRel ξ.r] : ℕ :=
  ∑ ω : G.Configuration, if good ω ∧ ω 0 = false then scaledWeight ξ ω else 0

lemma goodMass_free : goodMass G.freeBoundary = 1888 := by decide

lemma goodClosedMass_free : goodClosedMass G.freeBoundary = 544 := by decide

lemma goodMass_wire34 : goodMass wire34 = 1136 := by decide

lemma goodClosedMass_wire34 : goodClosedMass wire34 = 336 := by decide

lemma edgeWeight_scaled (ω : G.Configuration) :
    (5 : ℝ) ^ 5 * (G.edgeWeight (4 / 5) ω : ℝ) = 4 ^ openCount ω := by
  have hp : (4 / 5 : NNReal) ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 5)]
    norm_num
  change (5 : ℝ) ^ 5 *
    ((FK.FinitePlane.edgeWeight (4 / 5) (1 - 4 / 5) ω : NNReal) : ℝ) = _
  rw [FK.FinitePlane.edgeWeight_eq_pow]
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_sub hp, Fintype.card_fin]
  norm_num only [show ((4 : NNReal) : ℝ) = 4 by rfl,
    show ((5 : NNReal) : ℝ) = 5 by rfl, show ((1 : NNReal) : ℝ) = 1 by rfl]
  change (3125 : ℝ) * ((4 / 5 : ℝ) ^ openCount ω *
    (1 / 5 : ℝ) ^ (5 - openCount ω)) = 4 ^ openCount ω
  have hk : openCount ω ≤ 5 := FK.FinitePlane.openCard_le_card ω
  have hsum : openCount ω + (5 - openCount ω) = 5 := by omega
  calc
    (3125 : ℝ) * ((4 / 5) ^ openCount ω *
        (1 / 5) ^ (5 - openCount ω)) =
        (5 ^ openCount ω * 5 ^ (5 - openCount ω)) *
          ((4 / 5) ^ openCount ω * (1 / 5) ^ (5 - openCount ω)) := by
            rw [← pow_add, hsum]
            norm_num
    _ = 4 ^ openCount ω := by
      rw [div_pow, div_pow]
      field_simp
      ring

/-- The scaled computable weight agrees with the actual FK weight. -/
lemma scaledWeight_eq (ξ : G.BoundaryPartition) [DecidableRel ξ.r]
    (ω : G.Configuration) :
    (5 : ℝ) ^ 5 * (G.fkWeight 2 (4 / 5) ξ ω : ℝ) = scaledWeight ξ ω := by
  rw [LabelledMultigraph.fkWeight]
  simp only [scaledWeight, NNReal.coe_mul, NNReal.coe_pow,
    LabelledMultigraph.componentCount, Nat.card_eq_fintype_card]
  push_cast
  rw [← mul_assoc, edgeWeight_scaled]

lemma conditional_scaled_weight_free :
    (goodClosedMass G.freeBoundary : ℝ) / goodMass G.freeBoundary = 17 / 59 := by
  rw [goodMass_free, goodClosedMass_free]
  norm_num

lemma conditional_scaled_weight_wire34 :
    (goodClosedMass wire34 : ℝ) / goodMass wire34 = 21 / 71 := by
  rw [goodMass_wire34, goodClosedMass_wire34]
  norm_num

/-- The actual, unnormalised FK mass on `good`. -/
noncomputable def actualGoodMass (ξ : G.BoundaryPartition) : ℝ :=
  ∑ ω : G.Configuration, if good ω then
    (G.fkWeight 2 (4 / 5) ξ ω : ℝ) else 0

/-- The actual, unnormalised FK mass on `good` with edge zero closed. -/
noncomputable def actualGoodClosedMass (ξ : G.BoundaryPartition) : ℝ :=
  ∑ ω : G.Configuration, if good ω ∧ ω 0 = false then
    (G.fkWeight 2 (4 / 5) ξ ω : ℝ) else 0

lemma actualGoodMass_scaled (ξ : G.BoundaryPartition) [DecidableRel ξ.r] :
    (5 : ℝ) ^ 5 * actualGoodMass ξ = goodMass ξ := by
  unfold actualGoodMass goodMass
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : good ω
  · simp only [h]
    exact scaledWeight_eq ξ ω
  · simp [h]

lemma actualGoodClosedMass_scaled (ξ : G.BoundaryPartition) [DecidableRel ξ.r] :
    (5 : ℝ) ^ 5 * actualGoodClosedMass ξ = goodClosedMass ξ := by
  unfold actualGoodClosedMass goodClosedMass
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : good ω ∧ ω 0 = false
  · simp only [h]
    exact scaledWeight_eq ξ ω
  · simp [h]

lemma actual_conditional_weight (ξ : G.BoundaryPartition) [DecidableRel ξ.r] :
    actualGoodClosedMass ξ / actualGoodMass ξ =
      (goodClosedMass ξ : ℝ) / goodMass ξ := by
  have hs : (5 : ℝ) ^ 5 ≠ 0 := by norm_num
  calc
    actualGoodClosedMass ξ / actualGoodMass ξ =
        ((5 : ℝ) ^ 5 * actualGoodClosedMass ξ) /
          ((5 : ℝ) ^ 5 * actualGoodMass ξ) := by
            rw [mul_div_mul_left _ _ hs]
    _ = (goodClosedMass ξ : ℝ) / goodMass ξ := by
      rw [actualGoodMass_scaled, actualGoodClosedMass_scaled]

/-- The two restricted conditional weights differ, so the proposed
boundary-independence identity on `good` is false. -/
theorem conditional_scaled_weights_ne :
    (goodClosedMass G.freeBoundary : ℝ) / goodMass G.freeBoundary ≠
      (goodClosedMass wire34 : ℝ) / goodMass wire34 := by
  rw [conditional_scaled_weight_free, conditional_scaled_weight_wire34]
  norm_num

lemma actual_conditional_weight_free :
    actualGoodClosedMass G.freeBoundary / actualGoodMass G.freeBoundary = 17 / 59 := by
  rw [actual_conditional_weight, conditional_scaled_weight_free]

lemma actual_conditional_weight_wire34 :
    actualGoodClosedMass wire34 / actualGoodMass wire34 = 21 / 71 := by
  rw [actual_conditional_weight, conditional_scaled_weight_wire34]

theorem actual_conditional_weights_ne :
    actualGoodClosedMass G.freeBoundary / actualGoodMass G.freeBoundary ≠
      actualGoodClosedMass wire34 / actualGoodMass wire34 := by
  rw [actual_conditional_weight_free, actual_conditional_weight_wire34]
  norm_num

lemma q_pos : 0 < (2 : NNReal) := by norm_num

lemma p_le : (4 / 5 : NNReal) ≤ 1 := by
  rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 5)]
  norm_num

lemma p_pos : 0 < (4 / 5 : NNReal) := by positivity

lemma p_lt : (4 / 5 : NNReal) < 1 := by
  rw [div_lt_iff₀ (by norm_num : (0 : NNReal) < 5)]
  norm_num

lemma good_support (ξ : G.BoundaryPartition) :
    ∃ ω ∈ {ω | good ω}, ω ∈ (G.fkPMF q_pos p_le ξ).support := by
  refine ⟨G.allClosed, by decide, (PMF.mem_support_iff _ _).2 ?_⟩
  rw [G.fkPMF_apply]
  exact_mod_cast (div_pos (G.fkWeight_pos q_pos p_pos p_lt ξ G.allClosed)
    (G.partitionFunction_pos q_pos p_le ξ)).ne'

lemma filtered_closed_eq_actual (ξ : G.BoundaryPartition) :
    ((G.fkPMF q_pos p_le ξ).filter {ω | good ω} (good_support ξ)).toMeasure.real
        {ω | ω 0 = false} =
      actualGoodClosedMass ξ / actualGoodMass ξ := by
  unfold LabelledMultigraph.fkPMF
  rw [@FK.Finite.FilteredWeight.normalizedPMFOfSumPos_filter_toMeasure_real
    G.Configuration (LabelledMultigraph.instFintypeConfiguration G) _ _ _
    (G.fkWeight 2 (4 / 5) ξ) (G.partitionFunction_pos q_pos p_le ξ)
    {ω | good ω} {ω | ω 0 = false} _ _ (good_support ξ)]
  simp only [actualGoodClosedMass, actualGoodMass, Set.mem_inter_iff,
    Set.mem_ofPred_eq, and_comm]
  rw [show (@Finset.univ G.Configuration
      (LabelledMultigraph.instFintypeConfiguration G)) =
      (@Finset.univ G.Configuration Pi.instFintype) from
      congrArg (fun i : Fintype G.Configuration ↦ @Finset.univ G.Configuration i)
        (Subsingleton.elim _ _)]

lemma filtered_closed_free :
    ((G.fkPMF q_pos p_le G.freeBoundary).filter {ω | good ω}
      (good_support G.freeBoundary)).toMeasure.real {ω | ω 0 = false} = 17 / 59 := by
  rw [filtered_closed_eq_actual, actual_conditional_weight_free]

lemma filtered_closed_wire34 :
    ((G.fkPMF q_pos p_le wire34).filter {ω | good ω}
      (good_support wire34)).toMeasure.real {ω | ω 0 = false} = 21 / 71 := by
  rw [filtered_closed_eq_actual, actual_conditional_weight_wire34]

/-- The actual no-root-to-boundary conditional cylinder masses differ.
This rules out the proposed root-to-boundary correction identity; it is not a
counterexample to Theorem 5.1 or to closed-frontier conditioning. -/
theorem filtered_closed_ne :
    ((G.fkPMF q_pos p_le G.freeBoundary).filter {ω | good ω}
      (good_support G.freeBoundary)).toMeasure.real {ω | ω 0 = false} ≠
    ((G.fkPMF q_pos p_le wire34).filter {ω | good ω}
      (good_support wire34)).toMeasure.real {ω | ω 0 = false} := by
  rw [filtered_closed_free, filtered_closed_wire34]
  norm_num

end FK.ArmCorrectionObstruction
