import FK.AdaptiveFrontier

/-!
# Two lower FK coordinates driven by one shared adaptive upper history
-/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling
open FK.RegionSeal FK.FinitePlane

/-- The three coordinates of a nested coupling. -/
inductive Side where
  | left | right | upper
  deriving DecidableEq

instance : Fintype Side where
  elems := {.left, .right, .upper}
  complete := by intro x; cases x <;> simp

/-- Select one partial configuration from a triple. -/
def pick {E : Type*} : Side → Assignment E → Assignment E → Assignment E → Assignment E
  | .left, h, _, _ => h
  | .right, _, h, _ => h
  | .upper, _, _, h => h

/-- Select one newly sampled bit from a triple. -/
def project : Side → Bool × Bool × Bool → Bool
  | .left, z => z.1
  | .right, z => z.2.1
  | .upper, z => z.2.2

/-- Adaptive exploration with two lower histories and one shared upper history. -/
noncomputable def runTriple {E : Type*} [DecidableEq E]
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E) (h₁ h₂ k : Assignment E) : ℕ →
      PMF (Assignment E × Assignment E × Assignment E)
  | 0 => PMF.pure (h₁, h₂, k)
  | n + 1 =>
      let e := next k
      (step h₁ h₂ k e).bind (fun z =>
        runTriple step next (reveal h₁ e z.1) (reveal h₂ e z.2.1) (reveal k e z.2.2) n)

lemma runTriple_map_side {E : Type*} [Fintype E] [DecidableEq E]
    {μ : Side → PMF (E → Bool)} {hμ : ∀ s ω, μ s ω ≠ 0}
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E)
    (hs : ∀ s h₁ h₂ k e, pick s h₁ h₂ k e = none →
      (step h₁ h₂ k e).map (project s) = bit (μ s) (hμ s) (pick s h₁ h₂ k) e)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (s : Side) (h₁ h₂ k : Assignment E)
    (hh₁ : unrevealed h₁ = unrevealed k) (hh₂ : unrevealed h₂ = unrevealed k)
    (n : ℕ) (hn : (unrevealed k).card = n) :
    (runTriple step next h₁ h₂ k n).map
      (fun z => decodeOption (pick s z.1 z.2.1 z.2.2)) = cond (μ s) (hμ s) (pick s h₁ h₂ k) := by
  induction n generalizing h₁ h₂ k with
  | zero =>
      have hk : unrevealed k = ∅ := Finset.card_eq_zero.1 hn
      have he : unrevealed (pick s h₁ h₂ k) = ∅ := by
        cases s <;> simpa [pick, hh₁, hh₂] using hk
      rw [runTriple, cond_eq_pure_of_unrevealed_eq_empty (μ s) (hμ s) he]
      exact PMF.pure_map (fun z : Assignment E × Assignment E × Assignment E =>
        decodeOption (pick s z.1 z.2.1 z.2.2)) (h₁, h₂, k)
  | succ n ih =>
      have hcard : (unrevealed k).card = n + 1 := hn
      have hkne : (unrevealed k).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
      let e := next k
      have hke : k e = none := hnext k hkne
      have hh₁e : h₁ e = none := by
        apply mem_unrevealed.1
        rw [hh₁]
        exact mem_unrevealed.2 hke
      have hh₂e : h₂ e = none := by
        apply mem_unrevealed.1
        rw [hh₂]
        exact mem_unrevealed.2 hke
      have hse : pick s h₁ h₂ k e = none := by
        cases s with
        | left => exact hh₁e
        | right => exact hh₂e
        | upper => exact hke
      have hnew₁ (z : Bool × Bool × Bool) :
          unrevealed (reveal h₁ e z.1) = unrevealed (reveal k e z.2.2) := by
        have hc := congrArg (fun t : Finset E => t.erase e) hh₁
        simpa [unrevealed_reveal hh₁e, unrevealed_reveal hke] using hc
      have hnew₂ (z : Bool × Bool × Bool) :
          unrevealed (reveal h₂ e z.2.1) = unrevealed (reveal k e z.2.2) := by
        have hc := congrArg (fun t : Finset E => t.erase e) hh₂
        simpa [unrevealed_reveal hh₂e, unrevealed_reveal hke] using hc
      have hnum (b : Bool) : (unrevealed (reveal k e b)).card = n := by
        have hc := card_unrevealed_reveal hke b
        omega
      rw [runTriple, PMF.map_bind]
      calc
        _ = (step h₁ h₂ k e).bind (fun z =>
            cond (μ s) (hμ s) (pick s (reveal h₁ e z.1) (reveal h₂ e z.2.1) (reveal k e z.2.2))) := by
          congr 1
          funext z
          cases s <;> simp only [pick] <;>
            exact ih _ _ _ (hnew₁ z) (hnew₂ z) (hnum z.2.2)
        _ = ((step h₁ h₂ k e).map (project s)).bind (fun b =>
            cond (μ s) (hμ s) (reveal (pick s h₁ h₂ k) e b)) := by
          rw [PMF.bind_map]
          congr 1
          funext z
          cases s <;> rfl
        _ = (bit (μ s) (hμ s) (pick s h₁ h₂ k) e).bind (fun b =>
            cond (μ s) (hμ s) (reveal (pick s h₁ h₂ k) e b)) := by rw [hs s h₁ h₂ k e hse]
        _ = cond (μ s) (hμ s) (pick s h₁ h₂ k) := bind_bit_cond hse (μ s) (hμ s)

lemma runTriple_ordered {E : Type*} [Fintype E] [DecidableEq E]
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E)
    (hstep : ∀ h₁ h₂ k e, h₁ e = none → h₂ e = none → k e = none →
      ∀ z, z ∈ (step h₁ h₂ k e).support → z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h₁ h₂ k : Assignment E)
    (hh₁ : unrevealed h₁ = unrevealed k) (hh₂ : unrevealed h₂ = unrevealed k)
    (hle₁ : decodeOption h₁ ≤ decodeOption k) (hle₂ : decodeOption h₂ ≤ decodeOption k)
    (n : ℕ) (hn : (unrevealed k).card = n)
    {z : Assignment E × Assignment E × Assignment E}
    (hz : z ∈ (runTriple step next h₁ h₂ k n).support) :
    decodeOption z.1 ≤ decodeOption z.2.2 ∧ decodeOption z.2.1 ≤ decodeOption z.2.2 := by
  induction n generalizing h₁ h₂ k z with
  | zero =>
      have heq : z = (h₁, h₂, k) := (PMF.mem_support_pure_iff _ _).1 hz
      subst z
      exact ⟨hle₁, hle₂⟩
  | succ n ih =>
      have hcard : (unrevealed k).card = n + 1 := hn
      have hkne : (unrevealed k).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he] at hcard
        simp at hcard
      let e := next k
      have hke : k e = none := hnext k hkne
      have hh₁e : h₁ e = none := by
        apply mem_unrevealed.1
        rw [hh₁]
        exact mem_unrevealed.2 hke
      have hh₂e : h₂ e = none := by
        apply mem_unrevealed.1
        rw [hh₂]
        exact mem_unrevealed.2 hke
      have hnew₁ (z : Bool × Bool × Bool) :
          unrevealed (reveal h₁ e z.1) = unrevealed (reveal k e z.2.2) := by
        have hc := congrArg (fun t : Finset E => t.erase e) hh₁
        simpa [unrevealed_reveal hh₁e, unrevealed_reveal hke] using hc
      have hnew₂ (z : Bool × Bool × Bool) :
          unrevealed (reveal h₂ e z.2.1) = unrevealed (reveal k e z.2.2) := by
        have hc := congrArg (fun t : Finset E => t.erase e) hh₂
        simpa [unrevealed_reveal hh₂e, unrevealed_reveal hke] using hc
      have hnum (b : Bool) : (unrevealed (reveal k e b)).card = n := by
        have hc := card_unrevealed_reveal hke b
        omega
      rw [runTriple, PMF.mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      exact ih _ _ _ (hnew₁ w) (hnew₂ w)
        (decodeOption_reveal_le hle₁ (hstep h₁ h₂ k e hh₁e hh₂e hke w hw).1)
        (decodeOption_reveal_le hle₂ (hstep h₁ h₂ k e hh₁e hh₂e hke w hw).2)
        (hnum w.2.2) hz

/-- Independent triple with prescribed marginals. -/
noncomputable def productTriple {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : PMF A) (ρ : PMF B) (ν : PMF C) : PMF.TripleCoupling μ ρ ν where
  dist := ((PMF.Coupling.product (PMF.Coupling.product μ ρ).dist ν).dist.map
    (fun z => (z.1.1, z.1.2, z.2)))
  map_fst := by
    rw [PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun z : (A × B) × C => (z.1.1, z.1.2, z.2)) =
        Prod.fst ∘ Prod.fst := rfl
    rw [hcomp, ← PMF.map_comp, (PMF.Coupling.product (PMF.Coupling.product μ ρ).dist ν).map_fst,
      (PMF.Coupling.product μ ρ).map_fst]
  map_snd := by
    rw [PMF.map_comp]
    have hcomp : ((fun z : A × B × C => z.2.1) ∘ fun z : (A × B) × C =>
        (z.1.1, z.1.2, z.2)) = Prod.snd ∘ Prod.fst := rfl
    rw [hcomp, ← PMF.map_comp, (PMF.Coupling.product (PMF.Coupling.product μ ρ).dist ν).map_fst,
      (PMF.Coupling.product μ ρ).map_snd]
  map_thd := by
    rw [PMF.map_comp]
    have hcomp : ((fun z : A × B × C => z.2.2) ∘ fun z : (A × B) × C =>
        (z.1.1, z.1.2, z.2)) = Prod.snd := rfl
    rw [hcomp, (PMF.Coupling.product (PMF.Coupling.product μ ρ).dist ν).map_snd]

/-- One synchronized step for two finite FK laws with arbitrary boundary
setoids on their common edge-labelled graph. -/
noncomputable def fkTripleStep
    (G : LabelledMultigraph) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (h₁ h₂ k : Assignment G.Edge) (e : G.Edge) : PMF (Bool × Bool × Bool) :=
  if hh : h₁ e = none ∧ h₂ e = none ∧ k e = none then
    (PMF.OrderedCoupling.glue
      (boolOrderedCouplingOfLe
        (bit (G.fkPMF hq hp₁.le α)
          (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω) h₁ e)
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
        (fk_bit_true_toReal_le G α hq hp₀ hp₁ hh.1))
      (boolOrderedCouplingOfLe
        (bit (G.fkPMF hq hp₁.le β)
          (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ β ω) h₂ e)
        (upperRateNN q p) (upperRateNN_le_one hq hp₁.le)
        (fk_bit_true_toReal_le G β hq hp₀ hp₁ hh.2.1))).dist
  else
    (productTriple
      (bit (G.fkPMF hq hp₁.le α)
        (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω) h₁ e)
      (bit (G.fkPMF hq hp₁.le β)
        (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ β ω) h₂ e)
      (bit (G.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
        (bernoulliProductPMF_ne_zero G α (upperRateNN_pos hp₀)
          (upperRateNN_lt_one hq hp₀ hp₁)) k e)).dist

lemma fkTripleStep_map_side
    (G : LabelledMultigraph) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (s : Side) (h₁ h₂ k : Assignment G.Edge) {e : G.Edge}
    (he : pick s h₁ h₂ k e = none) :
    (fkTripleStep G α β hq hp₀ hp₁ h₁ h₂ k e).map (project s) =
      bit (match s with
        | .left => G.fkPMF hq hp₁.le α
        | .right => G.fkPMF hq hp₁.le β
        | .upper => G.bernoulliProductPMF (upperRateNN_lt_one hq hp₀ hp₁).le)
        (match s with
        | .left => fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω
        | .right => fun ω => fkPMF_ne_zero G hq hp₀ hp₁ β ω
        | .upper => bernoulliProductPMF_ne_zero G α (upperRateNN_pos hp₀)
            (upperRateNN_lt_one hq hp₀ hp₁)) (pick s h₁ h₂ k) e := by
  by_cases hh : h₁ e = none ∧ h₂ e = none ∧ k e = none
  · cases s with
    | left =>
        rw [fkTripleStep, dif_pos hh]
        exact (PMF.OrderedCoupling.glue _ _).map_fst
    | right =>
        rw [fkTripleStep, dif_pos hh]
        exact (PMF.OrderedCoupling.glue _ _).map_snd
    | upper =>
        rw [fkTripleStep, dif_pos hh]
        exact (PMF.OrderedCoupling.glue _ _).map_thd.trans
          (bit_bernoulliProductPMF G α (upperRateNN_pos hp₀)
            (upperRateNN_lt_one hq hp₀ hp₁) hh.2.2).symm
  · cases s with
    | left =>
        rw [fkTripleStep, dif_neg hh]
        exact (productTriple _ _ _).map_fst
    | right =>
        rw [fkTripleStep, dif_neg hh]
        exact (productTriple _ _ _).map_snd
    | upper =>
        rw [fkTripleStep, dif_neg hh]
        exact (productTriple _ _ _).map_thd

lemma fkTripleStep_ordered
    (G : LabelledMultigraph) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (h₁ h₂ k : Assignment G.Edge) {e : G.Edge}
    (hh₁ : h₁ e = none) (hh₂ : h₂ e = none) (hhk : k e = none)
    {z : Bool × Bool × Bool} (hz : z ∈ (fkTripleStep G α β hq hp₀ hp₁ h₁ h₂ k e).support) :
    z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2 := by
  have hh : h₁ e = none ∧ h₂ e = none ∧ k e = none := ⟨hh₁, hh₂, hhk⟩
  rw [fkTripleStep, dif_pos hh] at hz
  exact ⟨(PMF.OrderedCoupling.glue _ _).rel_fst z hz,
    (PMF.OrderedCoupling.glue _ _).rel_snd z hz⟩

end FK.Adaptive
