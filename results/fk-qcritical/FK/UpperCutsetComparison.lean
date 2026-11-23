import FK.UpperCutsetChain
import FK.LowerCutsetComparison

/-!
# Unconditional upper closed-cutset comparison

The outer pair starts in its stationary ordinary/enhanced law and the FK
coordinate starts at its ordinary marginal.  The enhanced upper marginal is
therefore constant, while the existing FK convergence theorem applies to the
ordinary initial product.  No convergence theorem for the singular ordered
pair chain is needed.
-/

namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- Ordered outer pair together with the intermediate FK configuration. -/
abbrev UpperJointState (E : Type*) := LowerJointState E

/-- Both pair/FK inequalities on a joint state. -/
abbrev UpperJointOrdered (s : UpperJointState E) : Prop := LowerJointOrdered s

/-- Full update at one edge, using the upper pair conditional rules. -/
def upperJointEdgeUpdate (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (e : E) (s : UpperJointState E) :
    OpenPath.FinProb (UpperJointState E) := by
  classical
  exact (if e ∈ enhanced then
    enhancedCutsetUpdateLawTotal K enhanced e p p' (pairLower s.1) s.2 (pairUpper s.1)
  else ordinaryCutsetUpdateLaw K e p p' (pairLower s.1) s.2 (pairUpper s.1)).map
    tripleJoint

/-- One coupled modified-block update on upper joint states. -/
def upperJointBlockUpdate (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (auxiliary : List E) (e : E) :
    UpperJointState E → OpenPath.FinProb (UpperJointState E) :=
  Glauber.sweep ((Glauber.blockCoordinates enhanced.toFinset auxiliary e).map
    (upperJointEdgeUpdate K enhanced hp))

/-- Shared-clock coupled upper modified jump. -/
def upperJointJump (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E) :
    UpperJointState E → OpenPath.FinProb (UpperJointState E) :=
  Glauber.mixture ρ (upperJointBlockUpdate K enhanced hp auxiliary)

/-- Initialize the upper outer pair in its stationary law and put FK at its
ordinary first marginal. -/
def upperJointInitial (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) : OpenPath.FinProb (UpperJointState E) :=
  (upperCutsetPairLaw K enhanced hp).map (fun w => (w, pairLower w))

/-- Finite-time upper coupled laws. -/
def upperJointLaw (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E) :
    ℕ → OpenPath.FinProb (UpperJointState E) :=
  GlauberCoupling.iterateLaw (upperJointInitial K enhanced hp)
    (upperJointJump K enhanced hp ρ auxiliary)

/-- The outer marginal is the exact upper enhanced pair heat bath. -/
theorem upperJointEdgeUpdate_map_fst (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (e : E) (s : UpperJointState E) :
    (upperJointEdgeUpdate K enhanced hp e s).map Prod.fst =
      Glauber.edgeUpdate (upperCutsetPairConditionals K enhanced hp) e s.1 := by
  classical
  unfold upperJointEdgeUpdate
  rw [Glauber.edgeUpdate_eq_map]
  split_ifs with he
  · rw [GlauberCoupling.map_map]
    change (enhancedCutsetUpdateLawTotal K enhanced e p p'
      (pairLower s.1) s.2 (pairUpper s.1)).map triplePair = _
    rw [enhancedCutsetUpdateLawTotal_map_triplePair]
    simp only [upperCutsetPairConditionals, if_pos he]
    rw [pairUpperOff_eq_update, cutsetOuterPairLaw_update]
    rfl
  · rw [GlauberCoupling.map_map]
    change (ordinaryCutsetUpdateLaw K e p p'
      (pairLower s.1) s.2 (pairUpper s.1)).map triplePair = _
    rw [ordinaryCutsetUpdateLaw_map_triplePair]
    simp only [upperCutsetPairConditionals, if_neg he]
    have hp'p : (p' : ℝ) ≤ (p : ℝ) := hp
    have hb : boolPair (min (p : ℝ) (p' : ℝ)) (max (p : ℝ) (p' : ℝ))
        (le_min p.2.1 p'.2.1) min_le_max (max_le p.2.2 p'.2.2) =
        boolPair p' p p'.2.1 hp p.2.2 := by
      apply OpenPath.FinProb.ext
      rintro ⟨i, j⟩
      cases i <;> cases j <;> simp [boolPair, min_eq_right hp'p, max_eq_left hp'p]
    rw [hb, configPair_lowerUpper]
    simp [upperCutsetFactor, upperEnhancedRate, he]

/-- The middle marginal is the exact FK heat bath. -/
theorem upperJointEdgeUpdate_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (e : E) (s : UpperJointState E) :
    (upperJointEdgeUpdate K enhanced hp e s).map Prod.snd =
      Glauber.edgeUpdate (abstractFKConditionals K p p') e s.2 := by
  classical
  unfold upperJointEdgeUpdate
  rw [Glauber.edgeUpdate_eq_map]
  have hc : abstractFKConditionals K p p' e (fun f : {f : E // f ≠ e} => s.2 f.1) =
      boolLaw (FKEnhancement.fkRate K e (p : ℝ) (p' : ℝ) s.2)
        (fkRate_mem_Icc K e p p' s.2) := by
    simpa only [Glauber.configSplit_apply_fst] using
      abstractFKConditionals_apply K hK p p' e s.2
  rw [hc]
  split_ifs with he
  · rw [GlauberCoupling.map_map]
    exact enhancedCutsetUpdateLawTotal_map_snd K enhanced e p p'
      (pairLower s.1) s.2 (pairUpper s.1)
  · rw [GlauberCoupling.map_map]
    exact ordinaryCutsetUpdateLaw_map_snd K e p p'
      (pairLower s.1) s.2 (pairUpper s.1)

/-- The sequential upper joint block projects to the pair block. -/
theorem upperJointBlockUpdate_map_fst (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (auxiliary : List E)
    (e : E) (s : UpperJointState E) :
    (upperJointBlockUpdate K enhanced hp auxiliary e s).map Prod.fst =
      Glauber.blockUpdate (upperCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary e s.1 := by
  unfold upperJointBlockUpdate Glauber.blockUpdate
  exact Glauber.map_sweep_kernel Prod.fst _ _ (upperJointEdgeUpdate_map_fst K enhanced hp)
    _ s

/-- The sequential upper joint block projects to the FK block. -/
theorem upperJointBlockUpdate_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (auxiliary : List E)
    (e : E) (s : UpperJointState E) :
    (upperJointBlockUpdate K enhanced hp auxiliary e s).map Prod.snd =
      Glauber.blockUpdate (abstractFKConditionals K p p')
        enhanced.toFinset auxiliary e s.2 := by
  unfold upperJointBlockUpdate Glauber.blockUpdate
  exact Glauber.map_sweep_kernel Prod.snd _ _
    (upperJointEdgeUpdate_map_snd K hK enhanced hp) _ s

/-- Outer marginal of an upper joint jump. -/
theorem upperJointJump_map_fst (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E)
    (auxiliary : List E) (s : UpperJointState E) :
    (upperJointJump K enhanced hp ρ auxiliary s).map Prod.fst =
      Glauber.modifiedJump ρ (upperCutsetPairConditionals K enhanced hp)
        enhanced.toFinset auxiliary s.1 := by
  unfold upperJointJump Glauber.modifiedJump
  exact Glauber.map_mixture Prod.fst ρ _ _
    (upperJointBlockUpdate_map_fst K enhanced hp auxiliary) s

/-- FK marginal of an upper joint jump. -/
theorem upperJointJump_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E)
    (auxiliary : List E) (s : UpperJointState E) :
    (upperJointJump K enhanced hp ρ auxiliary s).map Prod.snd =
      Glauber.modifiedJump ρ (abstractFKConditionals K p p')
        enhanced.toFinset auxiliary s.2 := by
  unfold upperJointJump Glauber.modifiedJump
  exact Glauber.map_mixture Prod.snd ρ _ _
    (upperJointBlockUpdate_map_snd K hK enhanced hp auxiliary) s

/-- The ordered upper pair marginal is stationary at every finite time. -/
theorem upperJointLaw_map_fst (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) (n : ℕ) :
    (upperJointLaw K enhanced hp ρ auxiliary n).map Prod.fst =
      upperCutsetPairLaw K enhanced hp := by
  have hm := Glauber.map_iterateLaw Prod.fst
    (upperJointJump K enhanced hp ρ auxiliary)
    (Glauber.modifiedJump ρ (upperCutsetPairConditionals K enhanced hp)
      enhanced.toFinset auxiliary)
    (upperJointJump_map_fst K enhanced hp ρ auxiliary)
    (upperJointInitial K enhanced hp) n
  have hinit : (upperJointInitial K enhanced hp).map Prod.fst =
      upperCutsetPairLaw K enhanced hp := by
    unfold upperJointInitial
    rw [GlauberCoupling.map_map]
    exact OpenPath.FinProb.map_id _
  rw [hinit] at hm
  change (upperJointLaw K enhanced hp ρ auxiliary n).map Prod.fst = _ at hm
  rw [hm, GlauberCoupling.iterateLaw_eq_bind_iterate]
  exact Glauber.iterate_invariant
    (upperCutsetPairLaw_modifiedJump_invariant K enhanced hp ρ auxiliary haux) n

/-- The upper product marginal is the target enhanced product at every time. -/
theorem upperJointLaw_map_upper (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary) (n : ℕ) :
    (upperJointLaw K enhanced hp ρ auxiliary n).map (fun s => pairUpper s.1) =
      upperEnhancedFinProb K enhanced hp := by
  rw [show (fun s : UpperJointState E => pairUpper s.1) = pairUpper ∘ Prod.fst from rfl,
    ← GlauberCoupling.map_map, upperJointLaw_map_fst K enhanced hp ρ auxiliary haux]
  exact upperCutsetPairLaw_map_snd K enhanced hp

/-- Exact FK marginal at every finite time, starting at the ordinary first
marginal of the stationary upper pair. -/
theorem upperJointLaw_map_snd (K : E → Configuration E → Prop)
    (hK : ∀ e (x : Configuration E) b, K e (Function.update x e b) ↔ K e x)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E)
    (auxiliary : List E) (n : ℕ) :
    (upperJointLaw K enhanced hp ρ auxiliary n).map Prod.snd =
      ((upperCutsetPairLaw K enhanced hp).map pairLower).bind
        (Glauber.iterate (Glauber.modifiedJump ρ (abstractFKConditionals K p p')
          enhanced.toFinset auxiliary) n) := by
  have hm := Glauber.map_iterateLaw Prod.snd
    (upperJointJump K enhanced hp ρ auxiliary)
    (Glauber.modifiedJump ρ (abstractFKConditionals K p p')
      enhanced.toFinset auxiliary)
    (upperJointJump_map_snd K hK enhanced hp ρ auxiliary)
    (upperJointInitial K enhanced hp) n
  have hinit : (upperJointInitial K enhanced hp).map Prod.snd =
      (upperCutsetPairLaw K enhanced hp).map pairLower := by
    unfold upperJointInitial
    rw [GlauberCoupling.map_map]
    rfl
  rw [hinit] at hm
  change (upperJointLaw K enhanced hp ρ auxiliary n).map Prod.snd =
    GlauberCoupling.iterateLaw ((upperCutsetPairLaw K enhanced hp).map pairLower)
      (Glauber.modifiedJump ρ (abstractFKConditionals K p p')
        enhanced.toFinset auxiliary) n at hm
  rw [GlauberCoupling.iterateLaw_eq_bind_iterate] at hm
  exact hm

end

end FKEnhancement


namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology
open FK.Finite.Comparison

noncomputable section

variable {E : Type*} [Fintype E]

/-- Order is preserved by one upper enhanced/ordinary joint edge update. -/
theorem upperJointEdgeUpdate_ordered (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) (e : E)
    {s : UpperJointState E} (hs : UpperJointOrdered s)
    {u : UpperJointState E} (hu : (upperJointEdgeUpdate K enhanced hp e s).mass u ≠ 0) :
    UpperJointOrdered u := by
  classical
  obtain ⟨t, ht, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
  change t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2
  split_ifs at ht with he
  · exact enhancedCutsetUpdateLawTotal_ordered K enhanced e p p' hs.1 hs.2 ht
  · exact ordinaryCutsetUpdateLaw_ordered K e p p' hs.1 hs.2 ht

/-- Order propagation through one upper sequential block. -/
theorem upperJointSweep_ordered (K : E → Configuration E → Prop)
    (enhanced : Set E) {p p' : I} (hp : p' ≤ p) :
    ∀ (l : List E) {s : UpperJointState E}, UpperJointOrdered s →
      ∀ {u : UpperJointState E},
        (Glauber.sweep (l.map (upperJointEdgeUpdate K enhanced hp)) s).mass u ≠ 0 →
        UpperJointOrdered u := by
  intro l
  induction l with
  | nil =>
      intro s hs u hu
      have hus : u = s := by
        by_contra hne
        simpa [Glauber.sweep, Glauber.FinProb.dirac, hne] using hu
      simpa [hus] using hs
  | cons e l ih =>
      intro s hs u hu
      simp only [List.map_cons, Glauber.sweep] at hu
      unfold Glauber.seq at hu
      obtain ⟨v, hv, hvu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact ih (upperJointEdgeUpdate_ordered K enhanced hp e hs hv) hvu

/-- Order propagation through an upper joint clock jump. -/
theorem upperJointJump_ordered (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E)
    {s : UpperJointState E} (hs : UpperJointOrdered s)
    {u : UpperJointState E} (hu : (upperJointJump K enhanced hp ρ auxiliary s).mass u ≠ 0) :
    UpperJointOrdered u := by
  unfold upperJointJump Glauber.mixture at hu
  obtain ⟨e, _, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
  exact upperJointSweep_ordered K enhanced hp _ hs hu

/-- Every supported finite-time upper joint state is ordered in both slots. -/
theorem upperJointLaw_ordered (K : E → Configuration E → Prop) (enhanced : Set E)
    {p p' : I} (hp : p' ≤ p) (ρ : OpenPath.FinProb E) (auxiliary : List E) :
    ∀ n u, (upperJointLaw K enhanced hp ρ auxiliary n).mass u ≠ 0 →
      UpperJointOrdered u := by
  intro n
  induction n with
  | zero =>
      intro u hu
      change (upperJointInitial K enhanced hp).mass u ≠ 0 at hu
      obtain ⟨w, hw, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero hu
      exact ⟨le_rfl, upperCutsetPairLaw_ordered K enhanced hw⟩
  | succ n ih =>
      intro u hu
      change ((upperJointLaw K enhanced hp ρ auxiliary n).bind
        (upperJointJump K enhanced hp ρ auxiliary)).mass u ≠ 0 at hu
      obtain ⟨s, hs, hu⟩ := GlauberCoupling.exists_of_mass_bind_ne_zero hu
      exact upperJointJump_ordered K enhanced hp ρ auxiliary (ih s hs) hu

end

end FKEnhancement

namespace FKEnhancement

open Set Filter
open scoped Classical BigOperators unitInterval Topology

/-- The `q > 1` orientation is exactly `p' < p` in the interior. -/
theorem actualPrime_le_lower {q r : NNReal} (hq : 0 < q) (hr0 : 0 < r)
    (hr1 : r < 1) (hq1 : 1 < q) :
    actualPrimeParameter hq hr1.le ≤ actualLowerParameter r hr1.le := by
  exact_mod_cast (FK.Finite.WiredEnhancement.prime_lt_of_one_lt_q
    (by exact_mod_cast hq) (by exact_mod_cast hr0) (by exact_mod_cast hr1)
    (by exact_mod_cast hq1)).le

/-- **Unconditional upper closed-cutset comparison for the actual finite FK
model.**  No finite-time coupling, stationarity equation, or enhanced-chain
convergence is assumed. -/
theorem graphConnectionEvent_upper_comparison
    (G : FK.Finite.LabelledMultigraph) {q r : NNReal}
    (hq : 0 < q) (hr0 : 0 < r) (hr1 : r < 1) (hq1 : 1 < q)
    (ξ : G.BoundaryPartition) (enhanced : Set G.Edge)
    (ρ : OpenPath.FinProb G.Edge) (hρ : ∀ e, 0 < ρ.mass e)
    (auxiliary : List G.Edge)
    (haux : Glauber.IsAuxiliaryEnumeration enhanced.toFinset auxiliary)
    (schedule : List G.Edge) (hschedule : ∀ e, e ∈ schedule) :
    StochasticallyDominates (G.fkMeasure hq hr1.le ξ)
      (upperEnhancedLaw (graphConnectionEvent G ξ) enhanced
        (actualPrime_le_lower hq hr0 hr1 hq1)) := by
  let p := actualLowerParameter r hr1.le
  let p' := actualPrimeParameter hq hr1.le
  let hp : p' ≤ p := actualPrime_le_lower hq hr0 hr1 hq1
  let K := graphConnectionEvent G ξ
  let μ₀ := (upperCutsetPairLaw K enhanced hp).map pairLower
  let fkN : ℕ → OpenPath.FinProb G.Configuration := fun n => μ₀.bind
    (Glauber.iterate (Glauber.modifiedJump ρ
      (Glauber.FKBridge.edgeConditionals G hq hr1.le ξ)
      enhanced.toFinset auxiliary) n)
  let joint : ℕ → OpenPath.FinProb (G.Configuration × G.Configuration) := fun n =>
    (upperJointLaw K enhanced hp ρ auxiliary n).map (fun s => (s.2, pairUpper s.1))
  have hK : ∀ e (x : Configuration G.Edge) b,
      K e (Function.update x e b) ↔ K e x := graphConnectionEvent_update G ξ
  have hcond : abstractFKConditionals K p p' =
      Glauber.FKBridge.edgeConditionals G hq hr1.le ξ := by
    exact abstractFKConditionals_graphConnectionEvent G hq hr1.le ξ
  have hfst : ∀ n, (joint n).map Prod.fst = fkN n := by
    intro n
    change ((upperJointLaw K enhanced hp ρ auxiliary n).map
      (fun s => (s.2, pairUpper s.1))).map Prod.fst = _
    rw [GlauberCoupling.map_map]
    change (upperJointLaw K enhanced hp ρ auxiliary n).map Prod.snd = _
    simpa only [hcond] using upperJointLaw_map_snd K hK enhanced hp ρ auxiliary n
  have hsnd : ∀ n, (joint n).map Prod.snd = upperEnhancedFinProb K enhanced hp := by
    intro n
    change ((upperJointLaw K enhanced hp ρ auxiliary n).map
      (fun s => (s.2, pairUpper s.1))).map Prod.snd = _
    rw [GlauberCoupling.map_map]
    exact upperJointLaw_map_upper K enhanced hp ρ auxiliary haux n
  have horder : ∀ n a, (joint n).mass a ≠ 0 → a.1 ≤ a.2 := by
    intro n a ha
    obtain ⟨s, hs, rfl⟩ := GlauberCoupling.exists_of_mass_map_ne_zero ha
    exact (upperJointLaw_ordered K enhanced hp ρ auxiliary n s hs).2
  have hupperLim : OpenPath.FinProb.LawTendsto atTop
      (fun _ : ℕ => upperEnhancedFinProb K enhanced hp) (upperEnhancedFinProb K enhanced hp) := by
    intro a
    exact tendsto_const_nhds
  exact graphConnectionEvent_upper_comparison_of_tendsto_upper_and_modifiedFK
    G hq hr1.le hr0 hr1 ξ enhanced hp μ₀ ρ hρ auxiliary schedule hschedule
    (fun _ : ℕ => upperEnhancedFinProb K enhanced hp) joint hsnd hfst horder hupperLim

end FKEnhancement
