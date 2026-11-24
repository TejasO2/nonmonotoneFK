/-
# Obstruction: no percolation does not give closed box boundaries

Source: Beffara--Faipeur--Oke, arXiv:2512.16486v1, proof of Theorem 5.1.

The paper uses the fact that a subcritical (null-percolation) law `ρ` admits,
almost surely, a *cofinal increasing family of connected finite regions* `Sₙ(ω)`
with closed edge boundary `ω|∂Sₙ = 0`; the regions are chosen as a function of
the configuration.

This file proves that the corresponding statement for a *fixed* box exhaustion
is false, even on the integer line: the configuration whose open edges are the
matching `{(2k, 2k+1)}` has no infinite open cluster, but **every** interval
`[-n,n]` has an open boundary edge.  Consequently the closed-boundary input of
`FK.InfiniteVolume.forall_eq_of_dominated_frequently_boundaryClosed` cannot be
derived from nonpercolation of `ρ` alone: adaptive regions (and hence the
specification at those regions) are genuinely needed.
-/
import FK.InfiniteVolume
import FK.CoFinalFreeUniqueness

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FK.InfiniteVolume

namespace ClosedBoundaryObstruction

/-- The integer line. -/
def lineGraph : SimpleGraph ℤ where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨by
    intro a b h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h <;> omega⟩

lemma lineGraph_adj {a b : ℤ} : lineGraph.Adj a b ↔ b = a + 1 ∨ a = b + 1 := Iff.rfl

/-- The matching configuration: exactly the edges `{2k, 2k+1}` are open. -/
noncomputable def matchingOpen : lineGraph.edgeSet → Bool :=
  fun e => by
    classical
    exact if ∃ k : ℤ, (e.1 : Sym2 ℤ) = s(2 * k, 2 * k + 1) then true else false

lemma matchingOpen_eq_true_iff (e : lineGraph.edgeSet) :
    matchingOpen e = true ↔ ∃ k : ℤ, (e.1 : Sym2 ℤ) = s(2 * k, 2 * k + 1) := by
  classical
  unfold matchingOpen
  by_cases h : ∃ k : ℤ, (e.1 : Sym2 ℤ) = s(2 * k, 2 * k + 1)
  · simp [h]
  · simp [h]

/-- The matching edge `{2k, 2k+1}` as an edge of the line. -/
def matchingEdge (k : ℤ) : lineGraph.edgeSet :=
  ⟨s(2 * k, 2 * k + 1), (SimpleGraph.mem_edgeSet lineGraph).mpr (Or.inl (by omega))⟩

lemma matchingOpen_matchingEdge (k : ℤ) : matchingOpen (matchingEdge k) = true :=
  matchingOpen_eq_true_iff _ |>.mpr ⟨k, rfl⟩

/-- Each vertex belongs to at most one open matching edge. -/
lemma eq_of_mem_matching {k m : ℤ} (h : (2 * k : ℤ) ∈ (s(2 * m, 2 * m + 1) : Sym2 ℤ)) :
    k = m := by
  rw [Sym2.mem_iff] at h
  rcases h with h | h <;> omega

/-- Two consecutive open edges return to the starting vertex: the open matching
has no paths of length two. -/
lemma eq_of_two_step {x z y : ℤ} (h1 : lineGraph.Adj x z) (h2 : lineGraph.Adj z y)
    (ho1 : matchingOpen (⟨s(x, z), (SimpleGraph.mem_edgeSet lineGraph).mpr h1⟩ : lineGraph.edgeSet) = true)
    (ho2 : matchingOpen (⟨s(z, y), (SimpleGraph.mem_edgeSet lineGraph).mpr h2⟩ : lineGraph.edgeSet) = true) :
    y = x := by
  classical
  obtain ⟨k, hk⟩ := matchingOpen_eq_true_iff _ |>.mp ho1
  obtain ⟨m, hm⟩ := matchingOpen_eq_true_iff _ |>.mp ho2
  have hz1 : z ∈ (s(2 * k, 2 * k + 1) : Sym2 ℤ) := hk ▸ Sym2.mem_mk_right x z
  have hz2 : z ∈ (s(2 * m, 2 * m + 1) : Sym2 ℤ) := hm ▸ Sym2.mem_mk_left z y
  rw [Sym2.mem_iff] at hz1 hz2
  have hkm : k = m := by omega
  subst hkm
  have hx : x ∈ (s(2 * k, 2 * k + 1) : Sym2 ℤ) := hk ▸ Sym2.mem_mk_left x z
  have hy : y ∈ (s(2 * k, 2 * k + 1) : Sym2 ℤ) := hm ▸ Sym2.mem_mk_right z y
  rw [Sym2.mem_iff] at hx hy
  have hxz : x ≠ z := by
    intro h
    rw [h] at h1
    rcases h1 with h1 | h1 <;> omega
  have hyz : y ≠ z := by
    intro h
    rw [h] at h2
    rcases h2 with h2 | h2 <;> omega
  omega

/-- Any open walk of the matching configuration ends at the start, or at a
neighbour of the start joined to it by an open edge. -/
lemma walk_end_strong : ∀ {x y : ℤ} (p : lineGraph.Walk x y),
    CurvatureVariance.Infra.Percolation.IsOpenIn matchingOpen Set.univ p →
    y = x ∨ ∃ (h : lineGraph.Adj x y),
      matchingOpen (⟨s(x, y), (SimpleGraph.mem_edgeSet lineGraph).mpr h⟩ : lineGraph.edgeSet) = true := by
  intro x y p
  induction p with
  | nil => intro _; exact Or.inl rfl
  | cons h rest ih =>
    intro hp
    rw [CurvatureVariance.Infra.Percolation.isOpenIn_cons] at hp
    obtain ⟨⟨-, hopen⟩, hopenrest⟩ := hp
    rcases ih hopenrest with hy | ⟨h', ho'⟩
    · subst hy
      exact Or.inr ⟨h, hopen⟩
    · exact Or.inl (eq_of_two_step h h' hopen ho')

/-- Any open walk of the matching configuration ends at the start or at a
neighbour of the start. -/
lemma walk_end {x y : ℤ} (p : lineGraph.Walk x y)
    (hp : CurvatureVariance.Infra.Percolation.IsOpenIn matchingOpen Set.univ p) :
    y = x ∨ lineGraph.Adj x y := by
  rcases walk_end_strong p hp with h | ⟨h', -⟩
  · exact Or.inl h
  · exact Or.inr h'

/-- The matching configuration has no infinite open cluster. -/
theorem no_infinite_cluster (x : ℤ) :
    ¬ ConventionGeometry.ExteriorInfiniteCluster lineGraph matchingOpen Set.univ x := by
  intro hinf
  have hsub : {y : ℤ | CurvatureVariance.Infra.Percolation.OpenConnected lineGraph
      matchingOpen Set.univ x y} ⊆ ({x - 1, x, x + 1} : Set ℤ) := by
    intro y hy
    obtain ⟨p, hp⟩ := hy
    rcases walk_end p hp with h | h
    · simp [h]
    · rcases h with h | h
      · simp [h]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
  exact hinf (Set.Finite.subset (Set.toFinite _) hsub)

/-! ## Every interval has an open boundary edge -/

/-- The right boundary edge of the interval `[-n,n]`. -/
def intervalRightEdge (n : ℕ) : lineGraph.edgeSet :=
  ⟨s((n : ℤ), (n : ℤ) + 1),
    (SimpleGraph.mem_edgeSet lineGraph).mpr (Or.inl (by omega))⟩

/-- The left boundary edge of the interval `[-n,n]`. -/
def intervalLeftEdge (n : ℕ) : lineGraph.edgeSet :=
  ⟨s(-(n : ℤ) - 1, -(n : ℤ)),
    (SimpleGraph.mem_edgeSet lineGraph).mpr (Or.inl (by omega))⟩

/-- Every interval `[-n,n]` has an open boundary edge. -/
theorem interval_boundary_open (n : ℕ) :
    matchingOpen (intervalRightEdge n) = true ∨
      matchingOpen (intervalLeftEdge n) = true := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [matchingOpen_eq_true_iff]
    refine ⟨(k : ℤ), ?_⟩
    show s((n : ℤ), (n : ℤ) + 1) = s(2 * (k : ℤ), 2 * (k : ℤ) + 1)
    rw [show (n : ℤ) = 2 * (k : ℤ) by omega]
  · right
    rw [matchingOpen_eq_true_iff]
    refine ⟨-((k : ℤ) + 1), ?_⟩
    show s(-(n : ℤ) - 1, -(n : ℤ)) = s(2 * (-((k : ℤ) + 1)), 2 * (-((k : ℤ) + 1)) + 1)
    rw [show (n : ℤ) = 2 * (k : ℤ) + 1 by omega]
    ring_nf


/-- **The matching configuration has no closed interval boundary, ever.**  With
the boundary of `[-n,n]` taken to be its two crossing edges, the hypothesis
`FrequentlyBoundaryClosed` of the uniqueness theorem fails identically — while
the configuration has no infinite open cluster. -/
theorem not_frequentlyBoundaryClosed_matchingOpen :
    ¬ FrequentlyBoundaryClosed
      (fun n : ℕ => ({intervalLeftEdge n, intervalRightEdge n} : Set lineGraph.edgeSet))
      matchingOpen := by
  intro hfreq
  obtain ⟨n, -, hn⟩ := frequentlyBoundaryClosed_iff.mp hfreq 0
  rcases interval_boundary_open n with hopen | hopen
  · have := hn _ (Set.mem_insert_iff.mpr (Or.inr rfl))
    rw [hopen] at this
    exact Bool.noConfusion this
  · have := hn _ (Set.mem_insert_iff.mpr (Or.inl rfl))
    rw [hopen] at this
    exact Bool.noConfusion this

/-- **Obstruction.**  The matching configuration on the integer line has no
infinite open cluster, yet every interval `[-n,n]` has an open boundary edge.
So nonpercolation of a law does not by itself produce closed box boundaries for
a fixed box exhaustion. -/
theorem no_percolation_without_closed_interval_boundary :
    (∀ x : ℤ, ¬ ConventionGeometry.ExteriorInfiniteCluster lineGraph matchingOpen Set.univ x) ∧
      (∀ n : ℕ, matchingOpen (intervalRightEdge n) = true ∨
        matchingOpen (intervalLeftEdge n) = true) :=
  ⟨no_infinite_cluster, interval_boundary_open⟩

end ClosedBoundaryObstruction

end FK.InfiniteVolume

/-! ## Axiom audit -/

#print axioms FK.InfiniteVolume.ClosedBoundaryObstruction.eq_of_two_step
#print axioms FK.InfiniteVolume.ClosedBoundaryObstruction.walk_end
#print axioms FK.InfiniteVolume.ClosedBoundaryObstruction.no_infinite_cluster
#print axioms FK.InfiniteVolume.ClosedBoundaryObstruction.interval_boundary_open
#print axioms FK.InfiniteVolume.ClosedBoundaryObstruction.not_frequentlyBoundaryClosed_matchingOpen
#print axioms FK.InfiniteVolume.ClosedBoundaryObstruction.no_percolation_without_closed_interval_boundary
