import FK.RegionFiberTransport

/-! # The sealed free interior at an adaptively explored outer region -/

namespace FK.Adaptive

open scoped ENNReal NNReal BigOperators Classical
open Set
open FK.Exploration.Sequential
open FK.Finite FK.Finite.LabelledMultigraph FK.Finite.Comparison
open FK.Exploration.FKCoupling
open FK.RegionSeal FK.FinitePlane

variable {G : LabelledMultigraph} (B : Set G.Vertex)

/-- The outer region generated only by revealed open edges. -/
def outer (k : Assignment G.Edge) : Set G.Vertex :=
  G.outerRegion G.freeBoundary B (decodeOption k)

/-- Its complementary, wholly unrevealed interior. -/
def interior (k : Assignment G.Edge) : Set G.Vertex := (outer B k)ᶜ

/-- An unrevealed edge incident with the current outer exploration region. -/
def frontierCandidate (k : Assignment G.Edge) (e : G.Edge) : Prop :=
  e ∈ unrevealed k ∧ (G.source e ∈ outer B k ∨ G.target e ∈ outer B k)

/-- No unrevealed edge is incident with the current outer region. -/
def frontierExhausted (k : Assignment G.Edge) : Prop :=
  ∀ e, ¬ frontierCandidate B k e

/-- No edge internal to the current complementary region has been revealed. -/
def NoInteriorReveal (k : Assignment G.Edge) : Prop :=
  ∀ e, IsInternal G (interior B k) e → k e = none

lemma decodeOption_le_reveal {k : Assignment G.Edge} {e : G.Edge}
    (he : k e = none) (b : Bool) : decodeOption k ≤ decodeOption (reveal k e b) := by
  intro a
  by_cases hae : a = e
  · subst a
    simp [decodeOption, reveal, he]
  · simp [decodeOption, reveal, Function.update_of_ne hae]

lemma outer_mono_reveal {k : Assignment G.Edge} {e : G.Edge}
    (he : k e = none) (b : Bool) : outer B k ⊆ outer B (reveal k e b) := by
  intro x hx
  change x ∈ ClosedRegion (G.openGraph G.freeBoundary (decodeOption k)) B at hx
  change x ∈ ClosedRegion (G.openGraph G.freeBoundary (decodeOption (reveal k e b))) B
  rw [FK.Finite.Exploration.mem_outerRegion_iff] at hx ⊢
  obtain ⟨v, hv, hvx⟩ := hx
  refine ⟨v, hv, hvx.mono ?_⟩
  exact G.connectionGraph_mono (decodeOption_le_reveal he b)

lemma NoInteriorReveal_reveal {k : Assignment G.Edge} {e : G.Edge}
    (he : k e = none) (b : Bool) (hn : NoInteriorReveal B k)
    (hf : G.source e ∈ outer B k ∨ G.target e ∈ outer B k) :
    NoInteriorReveal B (reveal k e b) := by
  intro a ha
  have haold : IsInternal G (interior B k) a := by
    refine ⟨?_, ?_⟩
    · intro hs
      exact ha.1 (outer_mono_reveal B he b hs)
    · intro ht
      exact ha.2 (outer_mono_reveal B he b ht)
  by_cases hae : a = e
  · subst a
    exfalso
    rcases hf with hs | ht
    · exact ha.1 (outer_mono_reveal B he b hs)
    · exact ha.2 (outer_mono_reveal B he b ht)
  · rw [reveal, Function.update_of_ne hae]
    exact hn a haold

lemma external_assigned_of_frontierExhausted {h k : Assignment G.Edge}
    (hhk : unrevealed h = unrevealed k) (hs : frontierExhausted B k)
    {e : G.Edge} (he : ¬ IsInternal G (interior B k) e) : h e ≠ none := by
  intro hh
  have hk : k e = none := by
    apply mem_unrevealed.1
    rw [← hhk]
    exact mem_unrevealed.2 hh
  apply hs e
  refine ⟨mem_unrevealed.2 hk, ?_⟩
  have he' : G.source e ∈ outer B k ∨ G.target e ∈ outer B k := by
    by_contra hn
    push_neg at hn
    exact he ⟨hn.1, hn.2⟩
  exact he'

/-- The full exterior configuration recorded by a stopped lower history. -/
noncomputable def stoppedExterior (h : Assignment G.Edge) :
    RegionSeal.External G (interior B k) → Bool :=
  fun o => decodeOption h o.1

lemma fiber_eq_stoppedExterior {h k : Assignment G.Edge}
    (hhk : unrevealed h = unrevealed k) (hs : frontierExhausted B k)
    (hn : NoInteriorReveal B k) :
    Fiber h = extFiber G (interior B k) (stoppedExterior B (k := k) h) := by
  ext ω
  constructor
  · intro hω
    funext o
    have hout : h o.1 ≠ none := by
      apply external_assigned_of_frontierExhausted B hhk hs o.2
    cases hh : h o.1 with
    | none => exact (hout hh).elim
    | some b =>
        have hb := hω o.1 b hh
        change ω o.1 = decodeOption h o.1
        rw [hb]
        simp [decodeOption, hh]
  · intro hω e b hb
    by_cases hi : IsInternal G (interior B k) e
    · have hk : k e = none := hn e hi
      have hh : h e = none := by
        apply mem_unrevealed.1
        rw [hhk]
        exact mem_unrevealed.2 hk
      rw [hh] at hb
      contradiction
    · have heq : restrictO G (interior B k) ω = stoppedExterior B (k := k) h := hω
      have heval := congrFun heq ⟨e, hi⟩
      change ω e = b
      change ω e = decodeOption h e at heval
      rw [heval]
      simp [decodeOption, hb]

/-- Every stopped compatible pair of histories determines the same sealed
exterior fibre, and hence the free FK law on its unrevealed interior. -/
theorem cond_map_restrictI_eq_free_region
    (α : G.BoundaryPartition) {q p : NNReal} (hq : 0 < q) (hp₀ : 0 < p) (hp₁ : p < 1)
    {h k : Assignment G.Edge} (hhk : unrevealed h = unrevealed k)
    (hle : decodeOption h ≤ decodeOption k)
    (hs : frontierExhausted B k) (hn : NoInteriorReveal B k)
    (hwire : ∀ v : G.Vertex, v ∈ interior B k → ∀ w : G.Vertex, α.r v w → v = w) :
    (cond (G.fkPMF hq hp₁.le α)
      (fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω) h).map
        (restrictI G (interior B k)) =
      (regionGraph G (interior B k)).fkPMF hq hp₁.le
        (regionGraph G (interior B k)).freeBoundary := by
  classical
  let U : Set G.Vertex := interior B k
  let ζ : RegionSeal.External G U → Bool := fun o => decodeOption h o.1
  have hfib : Fiber h = extFiber G U ζ := fiber_eq_stoppedExterior B hhk hs hn
  have hseal : ∀ o : RegionSeal.External G U, ζ o = true →
      G.source o.1 ∉ U ∧ G.target o.1 ∉ U := by
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
    · exact ⟨by simpa [U, interior] using hsR,
        by simpa [U, interior] using closeTargetOfSource hsR⟩
    · exact ⟨by simpa [U, interior] using closeSourceOfTarget htR,
        by simpa [U, interior] using htR⟩
  let μ := G.fkPMF hq hp₁.le α
  let hμ : ∀ ω, μ ω ≠ 0 := fun ω => fkPMF_ne_zero G hq hp₀ hp₁ α ω
  have hsupp : ∃ ω ∈ extFiber G U ζ, ω ∈ μ.support := by
    refine ⟨glueExt G U (fun _ => false) ζ, glueExt_mem_extFiber G U _ ζ, ?_⟩
    exact (PMF.mem_support_iff _ _).2 (hμ _)
  have hcond : cond μ hμ h = μ.filter (extFiber G U ζ) hsupp := by
    exact filter_congr_set μ hfib (fiber_support_of_positive μ hμ h) hsupp
  rw [hcond, map_restrictI_filter_fkPMF U α ζ hq hp₀ hp₁]
  exact fiberPMF_eq_region G U α ζ hwire hseal hq hp₀ hp₁

end FK.Adaptive
