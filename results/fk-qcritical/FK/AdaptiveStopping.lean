import FK.AdaptiveFK

/-!
# Stopping adaptive FK exploration and resuming with exact conditionals
-/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Total FK step, with the legal-state bound as an explicit argument.  This
version avoids attaching any conditional claim to an already revealed edge. -/
noncomputable def fkStepOfBound (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (h k : Assignment G.Edge) (e : G.Edge)
    (hb : (bit (G.fkPMF hq hp1.le ξ)
      (fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω) h e true).toReal ≤
        (upperRateNN q p : ℝ)) : PMF (Bool × Bool) :=
  (boolOrderedCouplingOfLe
    (bit (G.fkPMF hq hp1.le ξ)
      (fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω) h e)
    (upperRateNN q p) (upperRateNN_le_one hq hp1.le) hb).dist

lemma bernoulliProductPMF_ne_zero (G : LabelledMultigraph)
    (ξ : G.BoundaryPartition) {r : NNReal} (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ ω, G.bernoulliProductPMF hr1.le ω ≠ 0 := by
  intro ω
  rw [← G.fkPMF_q_one hr1.le ξ]
  exact fkPMF_ne_zero G zero_lt_one hr0 hr1 ξ ω

/-- The actual FK/Bernoulli adaptive step.  The second and third branches are
outside the legal support of the process and merely make the kernel total. -/
noncomputable def fkStep (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (h k : Assignment G.Edge) (e : G.Edge) : PMF (Bool × Bool) :=
  if hhe : h e = none then
    (boolOrderedCouplingOfLe
      (bit (G.fkPMF hq hp1.le ξ)
        (fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω) h e)
      (upperRateNN q p) (upperRateNN_le_one hq hp1.le)
      (fk_bit_true_toReal_le G ξ hq hp0 hp1 hhe)).dist
  else if hke : k e = none then
    (bit (G.bernoulliProductPMF (upperRateNN_lt_one hq hp0 hp1).le)
      (bernoulliProductPMF_ne_zero G ξ (upperRateNN_pos hp0)
        (upperRateNN_lt_one hq hp0 hp1)) k e).map (fun b => (false, b))
  else PMF.pure (false, false)

lemma fkStep_map_fst (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (h k : Assignment G.Edge) {e : G.Edge} (he : h e = none) :
    (fkStep G ξ hq hp0 hp1 h k e).map Prod.fst =
      bit (G.fkPMF hq hp1.le ξ)
        (fun ω => fkPMF_ne_zero G hq hp0 hp1 ξ ω) h e := by
  rw [fkStep, dif_pos he]
  exact (boolOrderedCouplingOfLe _ _ _ _).map_fst

lemma fkStep_map_snd (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (h k : Assignment G.Edge) {e : G.Edge} (he : k e = none) :
    (fkStep G ξ hq hp0 hp1 h k e).map Prod.snd =
      bit (G.bernoulliProductPMF (upperRateNN_lt_one hq hp0 hp1).le)
        (bernoulliProductPMF_ne_zero G ξ (upperRateNN_pos hp0)
          (upperRateNN_lt_one hq hp0 hp1)) k e := by
  by_cases hh : h e = none
  · rw [fkStep, dif_pos hh]
    exact (boolOrderedCouplingOfLe _ _ _ _).map_snd.trans
      (bit_bernoulliProductPMF G ξ (upperRateNN_pos hp0)
        (upperRateNN_lt_one hq hp0 hp1) he).symm
  · rw [fkStep, dif_neg hh, dif_pos he, PMF.map_comp]
    have hid : (Prod.snd ∘ fun b : Bool => (false, b)) = id := rfl
    rw [hid, PMF.map_id]

lemma fkStep_ordered (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (h k : Assignment G.Edge) {e : G.Edge} (hh : h e = none) (hk : k e = none)
    {z : Bool × Bool} (hz : z ∈ (fkStep G ξ hq hp0 hp1 h k e).support) : z.1 ≤ z.2 := by
  rw [fkStep, dif_pos hh] at hz
  exact (boolOrderedCouplingOfLe _ _ _ _).ordered z hz

/-- Any legal upper-history edge strategy gives an exact ordered coupling of
an arbitrary-boundary finite FK law and its upper Bernoulli product. -/
noncomputable def fkAdaptiveCoupling (G : LabelledMultigraph) (ξ : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp0 : 0 < p) (hp1 : p < 1)
    (next : Assignment G.Edge → G.Edge)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none) :
    AdaptiveCoupling (G.fkPMF hq hp1.le ξ)
      (G.bernoulliProductPMF (upperRateNN_lt_one hq hp0 hp1).le) := by
  exact adaptiveCoupling (fkStep G ξ hq hp0 hp1) next
    (fun h k e he => fkStep_map_fst G ξ hq hp0 hp1 h k he)
    (fun h k e he => fkStep_map_snd G ξ hq hp0 hp1 h k he)
    (fun h k e hh hk z hz => fkStep_ordered G ξ hq hp0 hp1 h k hh hk hz)
    (fun k hk => hnext k hk)

/-- Truncate an adaptive process when the stopping predicate first holds. -/
noncomputable def runUntil
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E) (stop : Assignment E → Prop)
    (h k : Assignment E) : ℕ → PMF (Assignment E × Assignment E)
  | 0 => PMF.pure (h, k)
  | n + 1 =>
      if stop k then PMF.pure (h, k) else
        let e := next k
        (step h k e).bind (fun z =>
          runUntil step next stop (reveal h e z.1) (reveal k e z.2) n)

/-- The full adaptive law is the stopped law followed by the ordinary resumed
law with exactly the number of unrevealed coordinates as fuel. -/
theorem run_eq_runUntil_bind
    (step : Assignment E → Assignment E → E → PMF (Bool × Bool))
    (next : Assignment E → E) (stop : Assignment E → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h k : Assignment E) (hhk : unrevealed h = unrevealed k)
    (n : ℕ) (hn : (unrevealed h).card = n) :
    run step next h k n =
      (runUntil step next stop h k n).bind (fun z =>
        run step next z.1 z.2 (unrevealed z.2).card) := by
  induction n generalizing h k with
  | zero =>
      have he : unrevealed h = ∅ := Finset.card_eq_zero.1 hn
      have hk : unrevealed k = ∅ := by rw [← hhk, he]
      simp [run, runUntil, hk]
  | succ n ih =>
      have hcard : (unrevealed h).card = n + 1 := hn
      have hkne : (unrevealed k).Nonempty := by
        rw [← hhk, Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
      have hkcard : (unrevealed k).card = n + 1 := by rw [← hhk, hcard]
      let e := next k
      have hke : k e = none := hnext k hkne
      have hhe : h e = none := by
        apply mem_unrevealed.1
        rw [hhk]
        exact mem_unrevealed.2 hke
      have hnew (a b : Bool) : unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
        have hc := congrArg (fun s : Finset E => s.erase e) hhk
        simpa [unrevealed_reveal hhe, unrevealed_reveal hke] using hc
      have hnum (a b : Bool) : (unrevealed (reveal h e a)).card = n := by
        have hc := card_unrevealed_reveal hhe a
        omega
      have hknum (a b : Bool) : (unrevealed (reveal k e b)).card = n := by
        have hc := card_unrevealed_reveal hke b
        omega
      by_cases hs : stop k
      · simp [runUntil, hs, hkcard]
      · rw [run, runUntil, if_neg hs, PMF.bind_bind]
        congr 1
        funext z
        have hrec := ih (reveal h e z.1) (reveal k e z.2) (hnew z.1 z.2) (hnum z.1 z.2)
        rw [← hrec]

end FK.Adaptive
