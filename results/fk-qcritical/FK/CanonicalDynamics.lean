import FK.LowerPathCoupling
import FK.UpperCutsetComparison
import FK.UpperPathStationarity

open FK.Finite FK.Finite.Conditional Glauber
open OpenPath

/-!
# Canonical auxiliary choices for the enhanced Glauber dynamics

A uniform positive clock law and duplicate-free enumeration of the auxiliary
edges exist on every nonempty finite edge type.  These wrapper theorems remove
those algorithmic inputs from applications of the comparison results.
-/

namespace FKEnhancement.CanonicalDynamics

noncomputable section

open scoped Classical

variable {E : Type*} [Fintype E]

/-- Uniform edge clocks, positive at every edge of a nonempty finite type. -/
noncomputable def uniformClock (E : Type*) [Fintype E] [Nonempty E] : OpenPath.FinProb E where
  mass _ := (Fintype.card E : ℝ)⁻¹
  mass_nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_mass := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma uniformClock_mass_pos [Nonempty E] (e : E) : 0 < (uniformClock E).mass e :=
  inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

/-- A duplicate-free enumeration of every coordinate outside `enhanced`. -/
def auxiliaryList (enhanced : Finset E) : List E := enhancedᶜ.toList

lemma auxiliaryList_spec (enhanced : Finset E) :
    Glauber.IsAuxiliaryEnumeration enhanced (auxiliaryList enhanced) := by
  constructor
  · exact Finset.nodup_toList _
  · intro e
    simp [auxiliaryList]

/-- A schedule containing every edge. -/
def completeSchedule (E : Type*) [Fintype E] : List E := Finset.univ.toList

lemma mem_completeSchedule (e : E) : e ∈ (completeSchedule E) := by
  simp [completeSchedule]

end

end FKEnhancement.CanonicalDynamics

namespace FKEnhancement

open scoped Classical unitInterval

variable {E : Type*} [Fintype E] [Nonempty E]

/-- Canonical-clock form of the lower closed-cutset comparison. -/
theorem graphConnectionEvent_lower_comparison_canonical
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1) (hq1 : q < 1)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) (hne : Nonempty G.Edge) :
    StochasticallyDominates
      (lowerEnhancedLaw (graphConnectionEvent G ξ) enhanced
        (actualLower_le_prime hq hr0 hr1 hq1))
      (G.fkMeasure hq hr1.le ξ) := by
  letI := hne
  exact graphConnectionEvent_lower_comparison G hq hr0 hr1 hq1 ξ enhanced
    (CanonicalDynamics.uniformClock G.Edge)
    (fun e => CanonicalDynamics.uniformClock_mass_pos e)
    (CanonicalDynamics.auxiliaryList enhanced.toFinset)
    (CanonicalDynamics.auxiliaryList_spec enhanced.toFinset)
    (CanonicalDynamics.completeSchedule G.Edge)
    (fun e => CanonicalDynamics.mem_completeSchedule e)

/-- Canonical-clock form of the upper closed-cutset comparison. -/
theorem graphConnectionEvent_upper_comparison_canonical
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1) (hq1 : 1 < q)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge) (hne : Nonempty G.Edge) :
    StochasticallyDominates (G.fkMeasure hq hr1.le ξ)
      (upperEnhancedLaw (graphConnectionEvent G ξ) enhanced
        (actualPrime_le_lower hq hr0 hr1 hq1)) := by
  letI := hne
  exact graphConnectionEvent_upper_comparison G hq hr0 hr1 hq1 ξ enhanced
    (CanonicalDynamics.uniformClock G.Edge)
    (fun e => CanonicalDynamics.uniformClock_mass_pos e)
    (CanonicalDynamics.auxiliaryList enhanced.toFinset)
    (CanonicalDynamics.auxiliaryList_spec enhanced.toFinset)
    (CanonicalDynamics.completeSchedule G.Edge)
    (fun e => CanonicalDynamics.mem_completeSchedule e)

end FKEnhancement



namespace OpenPath.LowerPathCoupling

open scoped Classical BigOperators

/-- Canonical-clock form of the actual lower open-path comparison. -/
theorem lower_path_comparison_of_one_lt_q_canonical
    (G : LabelledMultigraph) {q p : NNReal} (hq1 : 1 < q)
    (hp0 : 0 < p) (hp1 : p < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge)) (hΓ : HasEnhancingPaths enhanced Γ)
    (hpath : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → endpointsConnectedWithout G ξ e (configToBool ω))
    (hne : Nonempty G.Edge) :
    FKEnhancement.StochasticallyDominates
      ((lowerProductPMF enhanced (by exact_mod_cast hp1.le)
        (FK.prime_mem_Icc (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
          (by exact_mod_cast hp0.le) (by exact_mod_cast hp1.le))
        (FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
          (by exact_mod_cast (lt_trans zero_lt_one hq1 : 0 < q))
          (by exact_mod_cast hp0) (by exact_mod_cast hp1)
          (by exact_mod_cast hq1)).le Γ).map configToBool).toMeasure
        (G.fkPMF (lt_trans zero_lt_one hq1) hp1.le ξ).toMeasure := by
  letI := hne
  exact lower_path_comparison_of_one_lt_q G hq1 hp0 hp1 ξ enhanced Γ hΓ hpath
    (FKEnhancement.CanonicalDynamics.uniformClock G.Edge)
    (fun e => FKEnhancement.CanonicalDynamics.uniformClock_mass_pos e)
    (FKEnhancement.CanonicalDynamics.auxiliaryList enhanced)
    (FKEnhancement.CanonicalDynamics.auxiliaryList_spec enhanced)
    (FKEnhancement.CanonicalDynamics.completeSchedule G.Edge)
    (fun e => FKEnhancement.CanonicalDynamics.mem_completeSchedule e)

end OpenPath.LowerPathCoupling

namespace FKEnhancement.CanonicalDynamics

open scoped Classical

/-- Canonical-clock form of the actual upper open-path comparison for `q < 1`. -/
theorem graphConnectionEvent_upper_path_comparison_canonical
    (G : LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1) (hq1 : q < 1)
    (ξ : G.BoundaryPartition) (enhanced : Finset G.Edge)
    (Γ : G.Edge → Set (Finset G.Edge))
    (hΓ : ∀ e ∈ enhanced, AuxiliaryPaths enhanced e (Γ e))
    (hΓK : ∀ e ∈ enhanced, ∀ {ω : Config G.Edge},
      SomePathOpen (Γ e) ω → graphConnectionEvent G ξ e (configToBool ω))
    (hne : Nonempty G.Edge) :
    StochasticallyDominates (G.fkPMF hq hr1.le ξ).toMeasure
      ((upperProductPMF enhanced
        ⟨r.coe_nonneg, by exact_mod_cast hr1.le⟩
        (FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity)
          (by exact_mod_cast hr1.le)).2
        (FK.Finite.WiredEnhancement.lt_prime_of_q_lt_one
          (by exact_mod_cast hq) (by exact_mod_cast hr0)
          (by exact_mod_cast hr1) (by exact_mod_cast hq1)).le Γ).map
            configToBool).toMeasure := by
  letI := hne
  exact graphConnectionEvent_upper_path_comparison G hq hr0 hr1 hq1 ξ enhanced Γ hΓ hΓK
    (uniformClock G.Edge) (fun e => uniformClock_mass_pos e)
    (auxiliaryList enhanced) (auxiliaryList_spec enhanced)
    (completeSchedule G.Edge) (fun e => mem_completeSchedule e)

end FKEnhancement.CanonicalDynamics
