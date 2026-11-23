import FK.Glauber
import FK.FiniteConditional

/-!
# The actual finite FK Glauber dynamics

This file instantiates the generic block chain with the normalized FK PMF from
`FK.FiniteModel` and equation (2) from direction B's `FiniteConditional`.
-/

noncomputable section

local instance (priority := low) fkGlauberPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

open scoped BigOperators ENNReal
open FK.FiniteFiber FK.Finite.Conditional

namespace Glauber.FKBridge

open FK.Finite

/-- A finite Bernoulli law on Boolean edge states. -/
def boolLaw (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : OpenPath.FinProb Bool where
  mass b := if b then r else 1 - r
  mass_nonneg b := by
    rcases hr with ⟨hr0, hr1⟩
    cases b <;> simp <;> linarith
  sum_mass := by
    rw [Fintype.sum_bool]
    simp

@[simp] lemma boolLaw_true (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (boolLaw r hr).mass true = r := by simp [boolLaw]

@[simp] lemma boolLaw_false (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (boolLaw r hr).mass false = 1 - r := by simp [boolLaw]

variable (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

/-- Recombine an off-edge restriction with the closed bit. -/
def offConfiguration (_ξ : G.BoundaryPartition) (e : G.Edge) (off : OffConfig Bool G.Edge e) :
    G.Configuration :=
  (configSplit Bool e).symm (off, false)

/-- The two FK threshold probabilities from equation (2). -/
def openRate (ξ : G.BoundaryPartition) (e : G.Edge) (off : OffConfig Bool G.Edge e) : ℝ :=
  if endpointsConnectedWithout G ξ e (offConfiguration G ξ e off) then (p : ℝ)
  else FK.prime (q : ℝ) (p : ℝ)

include hq hp in
lemma openRate_mem_Icc (ξ : G.BoundaryPartition) (e : G.Edge)
    (off : OffConfig Bool G.Edge e) : openRate G (q := q) (p := p) ξ e off ∈ Set.Icc (0 : ℝ) 1 := by
  unfold openRate
  split_ifs
  · exact ⟨p.coe_nonneg, by exact_mod_cast hp⟩
  · exact FK.prime_mem_Icc (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp)

/-- The exact FK conditional law of every off-edge restriction. -/
noncomputable def edgeConditionals (hq : 0 < q) (hp : p ≤ 1)
    (ξ : G.BoundaryPartition) : EdgeConditionals Bool G.Edge :=
  fun e off => boolLaw (openRate G (q := q) (p := p) ξ e off)
    (openRate_mem_Icc G hq hp ξ e off)

lemma recombine_eq_withEdge (ξ : G.BoundaryPartition) (e : G.Edge)
    (off : OffConfig Bool G.Edge e) (b : Bool) :
    (configSplit Bool e).symm (off, b) = withEdge e b (offConfiguration G ξ e off) := by
  have h := configSplit_symm_update (B := Bool) e (offConfiguration G ξ e off) b
  simpa [offConfiguration, withEdge] using h

lemma fkFinProb_mass (ξ : G.BoundaryPartition) (ω : G.Configuration) :
    (ofPMF (G.fkPMF hq hp ξ)).mass ω =
      (G.fkWeight q p ξ ω : ℝ) / (G.partitionFunction q p ξ : ℝ) := by
  rw [ofPMF_mass, LabelledMultigraph.fkPMF_apply]
  simp

lemma outside_fk_eq (ξ : G.BoundaryPartition) (e : G.Edge)
    (off : OffConfig Bool G.Edge e) :
    outsideMassConj (configSplit Bool e) (ofPMF (G.fkPMF hq hp ξ)) off =
      (ofPMF (G.fkPMF hq hp ξ)).mass ((configSplit Bool e).symm (off, true)) +
      (ofPMF (G.fkPMF hq hp ξ)).mass ((configSplit Bool e).symm (off, false)) := by
  rw [outsideMassConj, Fintype.sum_bool]

lemma exists_support_of_outside_ne_zero (ξ : G.BoundaryPartition) (e : G.Edge)
    (off : OffConfig Bool G.Edge e)
    (ho : outsideMassConj (configSplit Bool e) (ofPMF (G.fkPMF hq hp ξ)) off ≠ 0) :
    ∃ ω ∈ offFiber e (offConfiguration G ξ e off), ω ∈ (G.fkPMF hq hp ξ).support := by
  classical
  by_contra hn
  apply ho
  rw [outsideMassConj, Fintype.sum_bool]
  have ht : G.fkPMF hq hp ξ ((configSplit Bool e).symm (off, true)) = 0 := by
    by_contra hne
    apply hn
    refine ⟨(configSplit Bool e).symm (off, true), ?_, hne⟩
    rw [recombine_eq_withEdge]
    exact withEdge_mem_offFiber e true _
  have hc : G.fkPMF hq hp ξ ((configSplit Bool e).symm (off, false)) = 0 := by
    by_contra hne
    apply hn
    refine ⟨(configSplit Bool e).symm (off, false), ?_, hne⟩
    rw [recombine_eq_withEdge]
    exact withEdge_mem_offFiber e false _
  simp [ht, hc]

end Glauber.FKBridge


namespace Glauber.FKBridge

open FK.Finite

variable (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q) (hp : p ≤ 1)

lemma edgeConditionals_true_eq_ratio (ξ : G.BoundaryPartition) (e : G.Edge)
    (off : OffConfig Bool G.Edge e)
    (h : ∃ ω ∈ offFiber e (offConfiguration G ξ e off), ω ∈ (G.fkPMF hq hp ξ).support) :
    (edgeConditionals G hq hp ξ e off).mass true =
      (G.fkWeight q p ξ (withEdge e true (offConfiguration G ξ e off)) : ℝ) /
        ((G.fkWeight q p ξ (withEdge e true (offConfiguration G ξ e off)) : ℝ) +
          (G.fkWeight q p ξ (withEdge e false (offConfiguration G ξ e off)) : ℝ)) := by
  unfold edgeConditionals
  by_cases hconn : endpointsConnectedWithout G ξ e (offConfiguration G ξ e off)
  · simp only [boolLaw_true, openRate, hconn, ↓reduceIte]
    exact (fk_conditional_open_of_connected G hq hp ξ e _ hconn h).symm.trans
      (fk_conditional_weight_ratio G hq hp ξ e _ h)
  · simp only [boolLaw_true, openRate, hconn, ↓reduceIte]
    exact (fk_conditional_open_of_not_connected G hq hp ξ e _ hconn h).symm.trans
      (fk_conditional_weight_ratio G hq hp ξ e _ h)

/-- The exact FK singleton conditional law in the zero-safe product form used
by the heat-bath invariance theorem. -/
theorem fk_hasEdgeConditional (ξ : G.BoundaryPartition) (e : G.Edge) :
    HasEdgeConditional (ofPMF (G.fkPMF hq hp ξ)) (edgeConditionals G hq hp ξ) e := by
  intro off b
  change (ofPMF (G.fkPMF hq hp ξ)).mass ((configSplit Bool e).symm (off, b)) =
    outsideMassConj (configSplit Bool e) (ofPMF (G.fkPMF hq hp ξ)) off *
      (edgeConditionals G hq hp ξ e off).mass b
  by_cases ho : outsideMassConj (configSplit Bool e) (ofPMF (G.fkPMF hq hp ξ)) off = 0
  · rw [outside_fk_eq] at ho
    have hz : ∀ b : Bool,
        (ofPMF (G.fkPMF hq hp ξ)).mass ((configSplit Bool e).symm (off, b)) = 0 := by
      intro b
      have ht := (ofPMF (G.fkPMF hq hp ξ)).mass_nonneg ((configSplit Bool e).symm (off, true))
      have hc := (ofPMF (G.fkPMF hq hp ξ)).mass_nonneg ((configSplit Bool e).symm (off, false))
      cases b <;> nlinarith
    rw [hz b, outside_fk_eq, ho, zero_mul]
  · have hsupp := exists_support_of_outside_ne_zero G hq hp ξ e off ho
    have hrate := edgeConditionals_true_eq_ratio G hq hp ξ e off hsupp
    have hz : (G.partitionFunction q p ξ : ℝ) ≠ 0 := by
      exact_mod_cast (G.partitionFunction_pos hq hp ξ).ne'
    have hsNN := fkWeight_pair_ne_zero_of_support G hq hp ξ e
      (offConfiguration G ξ e off) hsupp
    have hs : (G.fkWeight q p ξ (withEdge e true (offConfiguration G ξ e off)) : ℝ) +
        (G.fkWeight q p ξ (withEdge e false (offConfiguration G ξ e off)) : ℝ) ≠ 0 := by
      exact_mod_cast hsNN
    have hrate' : openRate G (q := q) (p := p) ξ e off =
        (G.fkWeight q p ξ (withEdge e true (offConfiguration G ξ e off)) : ℝ) /
          ((G.fkWeight q p ξ (withEdge e true (offConfiguration G ξ e off)) : ℝ) +
            (G.fkWeight q p ξ (withEdge e false (offConfiguration G ξ e off)) : ℝ)) := by
      simpa only [edgeConditionals, boolLaw_true] using hrate
    cases b
    · rw [outside_fk_eq]
      simp only [recombine_eq_withEdge, fkFinProb_mass, edgeConditionals, boolLaw_false]
      rw [hrate']
      field_simp [hz, hs]
      ring
    · rw [outside_fk_eq]
      simp only [recombine_eq_withEdge, fkFinProb_mass, edgeConditionals, boolLaw_true]
      rw [hrate']
      field_simp [hz, hs]

/-- The actual FK law is invariant for every modified block Glauber jump. -/
theorem fk_modifiedJump_invariant (ρ : OpenPath.FinProb G.Edge) (ξ : G.BoundaryPartition)
    (enhanced : Finset G.Edge) (auxiliary : List G.Edge) :
    Invariant (ofPMF (G.fkPMF hq hp ξ))
      (modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary) := by
  apply modifiedJump_invariant _ _ _ _ enhanced auxiliary
  intro e
  exact fk_hasEdgeConditional G hq hp ξ e

end Glauber.FKBridge


namespace Glauber.FKBridge

open FK.Finite

variable (G : LabelledMultigraph) {q p : NNReal} (hq : 0 < q)

include hq in
lemma openRate_pos (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : OffConfig Bool G.Edge e) :
    0 < openRate G (q := q) (p := p) ξ e off := by
  unfold openRate
  split_ifs
  · exact_mod_cast hp₀
  · exact FK.prime_pos (by exact_mod_cast hq) (by exact_mod_cast hp₀)
      (by exact_mod_cast hp₁.le)

include hq in
lemma openRate_lt_one (hp₀ : 0 < p) (hp₁ : p < 1) (ξ : G.BoundaryPartition)
    (e : G.Edge) (off : OffConfig Bool G.Edge e) :
    openRate G (q := q) (p := p) ξ e off < 1 := by
  unfold openRate
  split_ifs
  · exact_mod_cast hp₁
  · have hd : 0 < FK.dual (q : ℝ) (p : ℝ) :=
      FK.dual_pos (by exact_mod_cast hq) (by exact_mod_cast hp₀.le) (by exact_mod_cast hp₁)
    have heq := FK.prime_eq_one_sub_dual (q := (q : ℝ)) (p := (p : ℝ))
      (FK.denominator_ne_zero (by exact_mod_cast hq) (by positivity) (by exact_mod_cast hp₁.le))
    rw [heq]
    linarith

lemma edgeConditionals_pos (hp : p ≤ 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ξ : G.BoundaryPartition) (e : G.Edge) (off : OffConfig Bool G.Edge e) (b : Bool) :
    0 < (edgeConditionals G hq hp ξ e off).mass b := by
  unfold edgeConditionals
  cases b
  · rw [boolLaw_false]
    exact sub_pos.mpr (openRate_lt_one G hq hp₀ hp₁ ξ e off)
  · rw [boolLaw_true]
    exact openRate_pos G hq hp₀ hp₁ ξ e off

/-- Interior FK dynamics has positive probability of reaching every
configuration at the length of any complete clock schedule. -/
theorem fk_modifiedJump_iterate_pos (hp : p ≤ 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (ρ : OpenPath.FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e) (ξ : G.BoundaryPartition)
    (enhanced : Finset G.Edge) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) (ω η : G.Configuration) :
    0 < ((FinProb.dirac ω).bind
      (iterate (modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary)
        schedule.length)).mass η := by
  apply modifiedJump_iterate_pos _ _ _ _ enhanced auxiliary schedule hschedule ω η
  · intro e off b
    exact edgeConditionals_pos G hq hp hp₀ hp₁ ξ e off b
  · exact hρ

/-- **Interior FK convergence theorem for the modified Section 3 chain.**  The
initial law is arbitrary and the limit is the actual normalized FK PMF. -/
theorem fk_modifiedJump_tendsto (hp : p ≤ 1) (hp₀ : 0 < p) (hp₁ : p < 1)
    (μ : OpenPath.FinProb G.Configuration) (ρ : OpenPath.FinProb G.Edge)
    (hρ : ∀ e, 0 < ρ.mass e) (ξ : G.BoundaryPartition)
    (enhanced : Finset G.Edge) (auxiliary : List G.Edge)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    OpenPath.FinProb.LawTendsto Filter.atTop
      (fun n => μ.bind (iterate
        (modifiedJump ρ (edgeConditionals G hq hp ξ) enhanced auxiliary) n))
      (ofPMF (G.fkPMF hq hp ξ)) := by
  obtain ⟨e₀, he₀⟩ := FinProb.exists_mass_pos ρ
  let _ : Nonempty G.Edge := ⟨e₀⟩
  apply modifiedJump_tendsto μ (ofPMF (G.fkPMF hq hp ξ)) ρ
    (edgeConditionals G hq hp ξ) _ _ hρ enhanced auxiliary schedule hschedule
  · intro e
    exact fk_hasEdgeConditional G hq hp ξ e
  · intro e off b
    exact edgeConditionals_pos G hq hp hp₀ hp₁ ξ e off b

end Glauber.FKBridge
