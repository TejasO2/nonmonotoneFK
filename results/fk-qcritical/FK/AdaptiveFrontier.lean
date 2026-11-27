import FK.AdaptiveRegion

/-! # Outer-frontier adaptive strategy and its stopped-state invariants -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling
open FK.RegionSeal FK.FinitePlane

variable {G : LabelledMultigraph} (B : Set G.Vertex)

/-- Choose a frontier edge if one exists, otherwise any unrevealed edge.  The
last argument is only used at the already complete state, where no further step
is taken. -/
noncomputable def frontierNext (e₀ : G.Edge) (k : Assignment G.Edge) : G.Edge :=
  if h : ∃ e, frontierCandidate B k e then Classical.choose h else
    if h' : ∃ e, e ∈ unrevealed k then Classical.choose h' else e₀

lemma frontierNext_unrevealed (e₀ : G.Edge) {k : Assignment G.Edge}
    (hk : (unrevealed k).Nonempty) : k (frontierNext B e₀ k) = none := by
  classical
  by_cases h : ∃ e, frontierCandidate B k e
  · rw [frontierNext, dif_pos h]
    exact mem_unrevealed.1 (Classical.choose_spec h).1
  · rw [frontierNext, dif_neg h]
    by_cases h' : ∃ e, e ∈ unrevealed k
    · rw [dif_pos h']
      exact mem_unrevealed.1 (Classical.choose_spec h')
    · exfalso
      obtain ⟨e, he⟩ := hk
      exact h' ⟨e, he⟩

lemma frontierNext_candidate (e₀ : G.Edge) {k : Assignment G.Edge}
    (hs : ¬ frontierExhausted B k) :
    frontierCandidate B k (frontierNext B e₀ k) := by
  classical
  have h : ∃ e, frontierCandidate B k e := by
    by_contra hn
    apply hs
    intro e he
    exact hn ⟨e, he⟩
  rw [frontierNext, dif_pos h]
  exact Classical.choose_spec h

/-- Generic support invariants of a stopped adaptive process. -/
theorem runUntil_invariant
    {P : Assignment G.Edge → Assignment G.Edge → Prop}
    (step : Assignment G.Edge → Assignment G.Edge → G.Edge → PMF (Bool × Bool))
    (next : Assignment G.Edge → G.Edge) (stop : Assignment G.Edge → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (hPstep : ∀ h k e z, h e = none → k e = none → ¬ stop k → e = next k →
      z ∈ (step h k e).support → P h k →
      P (reveal h e z.1) (reveal k e z.2))
    (h k : Assignment G.Edge) (hhk : unrevealed h = unrevealed k)
    (n : ℕ) (hn : (unrevealed h).card = n) (hP : P h k)
    {z : Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runUntil step next stop h k n).support) : P z.1 z.2 := by
  induction n generalizing h k z with
  | zero =>
      have heq : z = (h, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runUntil] using hz)
      subst z
      exact hP
  | succ n ih =>
      by_cases hs : stop k
      · have heq : z = (h, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runUntil, hs] using hz)
        subst z
        exact hP
      · have hcard : (unrevealed h).card = n + 1 := hn
        have hkne : (unrevealed k).Nonempty := by
          rw [← hhk, Finset.nonempty_iff_ne_empty]
          intro he
          rw [he] at hcard
          simp at hcard
        let e := next k
        have hke : k e = none := hnext k hkne
        have hhe : h e = none := by
          apply mem_unrevealed.1
          rw [hhk]
          exact mem_unrevealed.2 hke
        have hnew (a b : Bool) : unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
          have hc := congrArg (fun s : Finset G.Edge => s.erase e) hhk
          simpa [unrevealed_reveal hhe, unrevealed_reveal hke] using hc
        have hnum (a b : Bool) : (unrevealed (reveal h e a)).card = n := by
          have hc := card_unrevealed_reveal hhe a
          omega
        rw [runUntil, if_neg hs, PMF.mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        exact ih _ _ (hnew w.1 w.2) (hnum w.1 w.2)
          (hPstep h k e w hhe hke hs rfl hw hP) hz

lemma runUntil_unrevealed_eq
    (step : Assignment G.Edge → Assignment G.Edge → G.Edge → PMF (Bool × Bool))
    (next : Assignment G.Edge → G.Edge) (stop : Assignment G.Edge → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (h k : Assignment G.Edge) (hhk : unrevealed h = unrevealed k)
    (n : ℕ) (hn : (unrevealed h).card = n)
    {z : Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runUntil step next stop h k n).support) :
    unrevealed z.1 = unrevealed z.2 := by
  exact runUntil_invariant (P := fun h k => unrevealed h = unrevealed k)
    step next stop hnext
    (fun h k e w _ _ _ _ _ hP => unrevealed_reveal_pair_eq hP e w.1 w.2)
    h k hhk n hn hhk hz

lemma runUntil_ordered
    (step : Assignment G.Edge → Assignment G.Edge → G.Edge → PMF (Bool × Bool))
    (next : Assignment G.Edge → G.Edge) (stop : Assignment G.Edge → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (hstep : ∀ h k e, h e = none → k e = none →
      ∀ z, z ∈ (step h k e).support → z.1 ≤ z.2)
    (h k : Assignment G.Edge) (hhk : unrevealed h = unrevealed k)
    (hle : decodeOption h ≤ decodeOption k)
    (n : ℕ) (hn : (unrevealed h).card = n)
    {z : Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runUntil step next stop h k n).support) :
    decodeOption z.1 ≤ decodeOption z.2 := by
  exact runUntil_invariant (P := fun h k => decodeOption h ≤ decodeOption k)
    step next stop hnext
    (fun h k e w hhe hke _ _ hw hP => decodeOption_reveal_le hP (hstep h k e hhe hke w hw))
    h k hhk n hn hle hz

lemma runUntil_noInteriorReveal
    (e₀ : G.Edge)
    (step : Assignment G.Edge → Assignment G.Edge → G.Edge → PMF (Bool × Bool))
    (h k : Assignment G.Edge) (hhk : unrevealed h = unrevealed k)
    (hnk : NoInteriorReveal B k)
    (n : ℕ) (hn : (unrevealed h).card = n)
    {z : Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runUntil step (frontierNext B e₀) (frontierExhausted B) h k n).support) :
    NoInteriorReveal B z.2 := by
  exact runUntil_invariant (P := fun _ k => NoInteriorReveal B k)
    step (frontierNext B e₀) (frontierExhausted B) (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
    (fun h k e w hhe hke hs heq _ hP => by
      subst e
      exact NoInteriorReveal_reveal B hke w.2 hP (frontierNext_candidate B e₀ hs).2)
    h k hhk n hn hnk hz

lemma runUntil_stopped
    (step : Assignment G.Edge → Assignment G.Edge → G.Edge → PMF (Bool × Bool))
    (next : Assignment G.Edge → G.Edge) (stop : Assignment G.Edge → Prop)
    (hnext : ∀ k, (unrevealed k).Nonempty → k (next k) = none)
    (hfull : ∀ k, unrevealed k = ∅ → stop k)
    (h k : Assignment G.Edge) (hhk : unrevealed h = unrevealed k)
    (n : ℕ) (hn : (unrevealed h).card = n)
    {z : Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runUntil step next stop h k n).support) : stop z.2 := by
  induction n generalizing h k z with
  | zero =>
      have he : unrevealed h = ∅ := Finset.card_eq_zero.1 hn
      have heq : z = (h, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runUntil] using hz)
      subst z
      exact hfull k (by rw [← hhk, he])
  | succ n ih =>
      by_cases hs : stop k
      · have heq : z = (h, k) := (PMF.mem_support_pure_iff _ _).1 (by simpa [runUntil, hs] using hz)
        subst z
        exact hs
      · have hcard : (unrevealed h).card = n + 1 := hn
        have hkne : (unrevealed k).Nonempty := by
          rw [← hhk, Finset.nonempty_iff_ne_empty]
          intro he
          rw [he] at hcard
          simp at hcard
        let e := next k
        have hke : k e = none := hnext k hkne
        have hhe : h e = none := by
          apply mem_unrevealed.1
          rw [hhk]
          exact mem_unrevealed.2 hke
        have hnew (a b : Bool) : unrevealed (reveal h e a) = unrevealed (reveal k e b) := by
          have hc := congrArg (fun s : Finset G.Edge => s.erase e) hhk
          simpa [unrevealed_reveal hhe, unrevealed_reveal hke] using hc
        have hnum (a b : Bool) : (unrevealed (reveal h e a)).card = n := by
          have hc := card_unrevealed_reveal hhe a
          omega
        rw [runUntil, if_neg hs, PMF.mem_support_bind_iff] at hz
        obtain ⟨w, hw, hz⟩ := hz
        exact ih _ _ (hnew w.1 w.2) (hnum w.1 w.2) hz

lemma frontierExhausted_of_unrevealed_empty {k : Assignment G.Edge}
    (hk : unrevealed k = ∅) : frontierExhausted B k := by
  intro e he
  have he' : e ∈ unrevealed k := he.1
  rw [hk] at he'
  exact Finset.notMem_empty e he'

lemma noInteriorReveal_blank : NoInteriorReveal B (blank : Assignment G.Edge) := by
  intro e _
  rfl

/-- All geometric and probabilistic invariants at a stopped outer-frontier
exploration begun with no revealed coordinates. -/
theorem runUntil_frontier_invariants (e₀ : G.Edge)
    (step : Assignment G.Edge → Assignment G.Edge → G.Edge → PMF (Bool × Bool))
    (hstep : ∀ h k e, h e = none → k e = none →
      ∀ z, z ∈ (step h k e).support → z.1 ≤ z.2)
    {z : Assignment G.Edge × Assignment G.Edge}
    (hz : z ∈ (runUntil step (frontierNext B e₀) (frontierExhausted B)
      blank blank (Fintype.card G.Edge)).support) :
    unrevealed z.1 = unrevealed z.2 ∧ decodeOption z.1 ≤ decodeOption z.2 ∧
      NoInteriorReveal B z.2 ∧ frontierExhausted B z.2 := by
  have hn : (unrevealed (blank : Assignment G.Edge)).card = Fintype.card G.Edge := by simp
  refine ⟨runUntil_unrevealed_eq step _ _ (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
      blank blank (by simp) _ hn hz,
    runUntil_ordered step _ _ (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk) hstep
      blank blank (by simp) (by simp [decodeOption, blank]) _ hn hz,
    runUntil_noInteriorReveal B e₀ step blank blank (by simp)
      (noInteriorReveal_blank B) _ hn hz,
    runUntil_stopped step _ _ (fun k hk => frontierNext_unrevealed B e₀ (k := k) hk)
      (fun _ hk => frontierExhausted_of_unrevealed_empty B hk)
      blank blank (by simp) _ hn hz⟩

end FK.Adaptive
