import FK.AdaptiveTriple

/-! # Stopping the synchronized two-boundary adaptive exploration -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling
open FK.RegionSeal FK.FinitePlane

/-- Truncate a synchronized triple process when the upper history stops. -/
noncomputable def runTripleUntil {E : Type*} [DecidableEq E]
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E) (stop : Assignment E → Prop)
    (h₁ h₂ k : Assignment E) : ℕ → PMF (Assignment E × Assignment E × Assignment E)
  | 0 => PMF.pure (h₁, h₂, k)
  | n + 1 =>
      if stop k then PMF.pure (h₁, h₂, k) else
        let e := next k
        (step h₁ h₂ k e).bind (fun z =>
          runTripleUntil step next stop (reveal h₁ e z.1) (reveal h₂ e z.2.1)
            (reveal k e z.2.2) n)

/-- Preserve any synchronized support invariant at the stopped state. -/
theorem runTripleUntil_invariant {E : Type*} [Fintype E] [DecidableEq E]
    {P : Assignment E → Assignment E → Assignment E → Prop}
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E) (stop : Assignment E → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (hPstep : ∀ h₁ h₂ k e z, h₁ e = none → h₂ e = none → k e = none →
      ¬ stop k → e = next k → z ∈ (step h₁ h₂ k e).support → P h₁ h₂ k →
      P (reveal h₁ e z.1) (reveal h₂ e z.2.1) (reveal k e z.2.2))
    (h₁ h₂ k : Assignment E)
    (hh₁ : unrevealed h₁ = unrevealed k) (hh₂ : unrevealed h₂ = unrevealed k)
    (n : ℕ) (hn : (unrevealed k).card = n) (hP : P h₁ h₂ k)
    {z : Assignment E × Assignment E × Assignment E}
    (hz : z ∈ (runTripleUntil step next stop h₁ h₂ k n).support) : P z.1 z.2.1 z.2.2 := by
  induction n generalizing h₁ h₂ k z with
  | zero =>
      have heq : z = (h₁, h₂, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runTripleUntil] using hz)
      subst z
      exact hP
  | succ n ih =>
      by_cases hs : stop k
      · have heq : z = (h₁, h₂, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runTripleUntil, hs] using hz)
        subst z
        exact hP
      · have hcard : (unrevealed k).card = n + 1 := hn
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
        rw [runTripleUntil, if_neg hs, PMF.mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        exact ih _ _ _ (hnew₁ w) (hnew₂ w) (hnum w.2.2)
          (hPstep h₁ h₂ k e w hh₁e hh₂e hke hs rfl hw hP) hz

lemma runTripleUntil_stopped {E : Type*} [Fintype E] [DecidableEq E]
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E) (stop : Assignment E → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (hfull : ∀ k, unrevealed k = ∅ → stop k)
    (h₁ h₂ k : Assignment E)
    (hh₁ : unrevealed h₁ = unrevealed k) (hh₂ : unrevealed h₂ = unrevealed k)
    (n : ℕ) (hn : (unrevealed k).card = n)
    {z : Assignment E × Assignment E × Assignment E}
    (hz : z ∈ (runTripleUntil step next stop h₁ h₂ k n).support) : stop z.2.2 := by
  induction n generalizing h₁ h₂ k z with
  | zero =>
      have he : unrevealed k = ∅ := Finset.card_eq_zero.1 hn
      have heq : z = (h₁, h₂, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runTripleUntil] using hz)
      subst z
      exact hfull k he
  | succ n ih =>
      by_cases hs : stop k
      · have heq : z = (h₁, h₂, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runTripleUntil, hs] using hz)
        subst z
        exact hs
      · have hcard : (unrevealed k).card = n + 1 := hn
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
        rw [runTripleUntil, if_neg hs, PMF.mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        exact ih _ _ _ (hnew₁ w) (hnew₂ w) (hnum w.2.2) hz

/-- The resumed full synchronized process factors through the stopped process. -/
theorem runTriple_eq_runTripleUntil_bind {E : Type*} [Fintype E] [DecidableEq E]
    (step : Assignment E → Assignment E → Assignment E → E → PMF (Bool × Bool × Bool))
    (next : Assignment E → E) (stop : Assignment E → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h₁ h₂ k : Assignment E)
    (hh₁ : unrevealed h₁ = unrevealed k) (hh₂ : unrevealed h₂ = unrevealed k)
    (n : ℕ) (hn : (unrevealed k).card = n) :
    runTriple step next h₁ h₂ k n =
      (runTripleUntil step next stop h₁ h₂ k n).bind (fun z =>
        runTriple step next z.1 z.2.1 z.2.2 (unrevealed z.2.2).card) := by
  induction n generalizing h₁ h₂ k with
  | zero =>
      have he : unrevealed k = ∅ := Finset.card_eq_zero.1 hn
      simp [runTriple, runTripleUntil, he]
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
      by_cases hs : stop k
      · simp [runTripleUntil, hs, hcard]
      · rw [runTriple, runTripleUntil, if_neg hs, PMF.bind_bind]
        congr 1
        funext z
        have hrec := ih _ _ _ (hnew₁ z) (hnew₂ z) (hnum z.2.2)
        rw [← hrec]

/-- Combined geometric invariants of the stopped synchronized outer-frontier
exploration. -/
theorem runTripleUntil_frontier_invariants {G : LabelledMultigraph}
    (B : Set G.Vertex) (e₀ : G.Edge)
    (step : Assignment G.Edge → Assignment G.Edge → Assignment G.Edge → G.Edge →
      PMF (Bool × Bool × Bool))
    (hstep : ∀ h₁ h₂ k e, h₁ e = none → h₂ e = none → k e = none →
      ∀ z, z ∈ (step h₁ h₂ k e).support → z.1 ≤ z.2.2 ∧ z.2.1 ≤ z.2.2)
    {z : Assignment G.Edge × Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runTripleUntil step (frontierNext B e₀) (frontierExhausted B)
      blank blank blank (Fintype.card G.Edge)).support) :
    unrevealed z.1 = unrevealed z.2.2 ∧ unrevealed z.2.1 = unrevealed z.2.2 ∧
      decodeOption z.1 ≤ decodeOption z.2.2 ∧ decodeOption z.2.1 ≤ decodeOption z.2.2 ∧
      NoInteriorReveal B z.2.2 ∧ frontierExhausted B z.2.2 := by
  let P : Assignment G.Edge → Assignment G.Edge → Assignment G.Edge → Prop :=
    fun h₁ h₂ k => unrevealed h₁ = unrevealed k ∧ unrevealed h₂ = unrevealed k ∧
      decodeOption h₁ ≤ decodeOption k ∧ decodeOption h₂ ≤ decodeOption k ∧
      NoInteriorReveal B k
  have hP : P (blank : Assignment G.Edge) blank blank := by
    refine ⟨by simp, by simp, by simp [decodeOption, blank], by simp [decodeOption, blank],
      noInteriorReveal_blank B⟩
  have hn : (unrevealed (blank : Assignment G.Edge)).card = Fintype.card G.Edge := by simp
  have hinv := runTripleUntil_invariant (P := P) step (frontierNext B e₀)
    (frontierExhausted B) (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
    (fun h₁ h₂ k e w hh₁ hh₂ hke hs heq hw hP => by
      subst e
      have hc : unrevealed (reveal h₁ (frontierNext B e₀ k) w.1) =
          unrevealed (reveal k (frontierNext B e₀ k) w.2.2) :=
        unrevealed_reveal_pair_eq hP.1 _ _ _
      have hc' : unrevealed (reveal h₂ (frontierNext B e₀ k) w.2.1) =
          unrevealed (reveal k (frontierNext B e₀ k) w.2.2) :=
        unrevealed_reveal_pair_eq hP.2.1 _ _ _
      have hord := hstep h₁ h₂ k _ hh₁ hh₂ hke w hw
      exact ⟨hc, hc', decodeOption_reveal_le hP.2.2.1 hord.1,
        decodeOption_reveal_le hP.2.2.2.1 hord.2,
        NoInteriorReveal_reveal B hke w.2.2 hP.2.2.2.2
          (frontierNext_candidate B e₀ hs).2⟩)
    (blank : Assignment G.Edge) blank blank (by simp) (by simp) _ hn hP hz
  have hstop := runTripleUntil_stopped step (frontierNext B e₀)
    (frontierExhausted B) (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
    (fun _ hk => frontierExhausted_of_unrevealed_empty B hk)
    (blank : Assignment G.Edge) blank blank (by simp) (by simp) _ hn hz
  exact ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2, hstop⟩

/-- At a stopped outer-frontier state, both FK coordinates have exactly the
same free law on the common unrevealed interior. -/
theorem runTripleUntil_free_interiors {G : LabelledMultigraph}
    (B : Set G.Vertex) (e₀ : G.Edge) (α β : G.BoundaryPartition)
    {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hwireα : ∀ k : Assignment G.Edge, ∀ v ∈ interior B k, ∀ w : G.Vertex, α.r v w → v = w)
    (hwireβ : ∀ k : Assignment G.Edge, ∀ v ∈ interior B k, ∀ w : G.Vertex, β.r v w → v = w)
    {z : Assignment G.Edge × Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runTripleUntil (fkTripleStep G α β hq hp₀ hp₁)
      (frontierNext B e₀) (frontierExhausted B) blank blank blank
      (Fintype.card G.Edge)).support) :
    (cond (G.fkPMF hq hp₁.le α)
      (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω) z.1).map
        (restrictI G (interior B z.2.2)) =
      (regionGraph G (interior B z.2.2)).fkPMF hq hp₁.le
        (regionGraph G (interior B z.2.2)).freeBoundary ∧
    (cond (G.fkPMF hq hp₁.le β)
      (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ β ω) z.2.1).map
        (restrictI G (interior B z.2.2)) =
      (regionGraph G (interior B z.2.2)).fkPMF hq hp₁.le
        (regionGraph G (interior B z.2.2)).freeBoundary := by
  have hi := runTripleUntil_frontier_invariants B e₀
    (fkTripleStep G α β hq hp₀ hp₁)
    (fun h₁ h₂ k e hh₁ hh₂ hke w hw => fkTripleStep_ordered G α β hq hp₀ hp₁
      h₁ h₂ k hh₁ hh₂ hke hw) hz
  exact ⟨cond_map_restrictI_eq_free_region B α hq hp₀ hp₁ hi.1 hi.2.2.1
      hi.2.2.2.2.2 hi.2.2.2.2.1 (hwireα z.2.2),
    cond_map_restrictI_eq_free_region B β hq hp₀ hp₁ hi.2.1 hi.2.2.2.1
      hi.2.2.2.2.2 hi.2.2.2.2.1 (hwireβ z.2.2)⟩

end FK.Adaptive
