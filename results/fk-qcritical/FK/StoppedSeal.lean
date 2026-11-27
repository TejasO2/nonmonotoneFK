import FK.AdaptiveTripleStopping

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.RegionSeal FK.FinitePlane

/-- Any external edge open in the stopped lower history has both endpoints in
the revealed outer region; consequently no open external edge touches the
unrevealed interior. -/
theorem stopped_sealed_exterior {G : LabelledMultigraph} (B : Set G.Vertex)
    {h k : Assignment G.Edge} (hhk : unrevealed h = unrevealed k)
    (hle : decodeOption h ≤ decodeOption k) (hs : frontierExhausted B k) :
    ∀ o : RegionSeal.External G (interior B k), decodeOption h o.1 = true →
      G.source o.1 ∉ interior B k ∧ G.target o.1 ∉ interior B k := by
  intro o ho
  have hko : decodeOption k o.1 = true := by
    have hlo : decodeOption h o.1 = true := ho
    have hl := hle o.1
    rw [hlo] at hl
    exact Bool.eq_true_of_true_le hl
  have hR : G.source o.1 ∈ outer B k ∨ G.target o.1 ∈ outer B k := by
    by_contra hn'
    push_neg at hn'
    exact o.2 ⟨hn'.1, hn'.2⟩
  have closeTargetOfSource (hsR : G.source o.1 ∈ outer B k) :
      G.target o.1 ∈ outer B k := by
    by_cases heq : G.source o.1 = G.target o.1
    · rwa [← heq]
    · change G.source o.1 ∈ ClosedRegion (G.openGraph G.freeBoundary (decodeOption k)) B at hsR
      change G.target o.1 ∈ ClosedRegion (G.openGraph G.freeBoundary (decodeOption k)) B
      rw [FK.Finite.Exploration.mem_outerRegion_iff] at hsR ⊢
      obtain ⟨v, hv, hvs⟩ := hsR
      refine ⟨v, hv, hvs.trans ?_⟩
      apply SimpleGraph.Adj.reachable
      exact ⟨heq, Or.inr ⟨o.1, hko, Or.inl ⟨rfl, rfl⟩⟩⟩
  have closeSourceOfTarget (htR : G.target o.1 ∈ outer B k) :
      G.source o.1 ∈ outer B k := by
    by_cases heq : G.target o.1 = G.source o.1
    · rwa [← heq]
    · change G.target o.1 ∈ ClosedRegion (G.openGraph G.freeBoundary (decodeOption k)) B at htR
      change G.source o.1 ∈ ClosedRegion (G.openGraph G.freeBoundary (decodeOption k)) B
      rw [FK.Finite.Exploration.mem_outerRegion_iff] at htR ⊢
      obtain ⟨v, hv, hvt⟩ := htR
      refine ⟨v, hv, hvt.trans ?_⟩
      apply SimpleGraph.Adj.reachable
      exact ⟨heq, Or.inr ⟨o.1, hko, Or.inr ⟨rfl, rfl⟩⟩⟩
  rcases hR with hsR | htR
  · exact ⟨by simpa [interior] using hsR, by simpa [interior] using closeTargetOfSource hsR⟩
  · exact ⟨by simpa [interior] using closeSourceOfTarget htR, by simpa [interior] using htR⟩

end FK.Adaptive
