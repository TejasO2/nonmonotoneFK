/-
# Finite edge modifications preserve the existence of an infinite open cluster

Combinatorial input for the tail zero--one law of percolation events: whether a
configuration possesses an infinite open cluster is unchanged by modifying
finitely many edges.

Main point: a finite cover lemma.  For a finite set `A` of edges and a vertex
`x`, the full open cluster of `x` is covered by finitely many clusters computed
while avoiding `A`.  Hence if the full cluster of `x` is infinite, some
`A`-avoiding cluster is infinite, and since `A`-avoiding connections are
unaffected by changing the configuration on `A`, an infinite open cluster
survives every finite modification.
-/
import CurvatureVariance.Infra.Percolation.Critical

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FK.ClusterCover

open CurvatureVariance.Infra.Percolation

variable {V : Type*}

/-- The cluster of `x` computed from open walks that avoid the edge set `A`. -/
def clusterAvoid (G : SimpleGraph V) (ω : G.edgeSet → Bool) (A : Set (Sym2 V))
    (x : V) : Set V :=
  {y | OpenConnected G ω (Set.univ \ A) x y}

/-- A configuration has an infinite open cluster. -/
def HasInfiniteCluster (G : SimpleGraph V) (ω : G.edgeSet → Bool) : Prop :=
  ∃ x, (clusterAvoid G ω ∅ x).Infinite

lemma clusterAvoid_antitone {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A A' : Set (Sym2 V)} (h : A ⊆ A') (x : V) :
    clusterAvoid G ω A' x ⊆ clusterAvoid G ω A x := by
  intro y hy
  refine OpenConnected.mono_edges hy ?_
  intro e he
  exact ⟨he.1, fun hA => he.2 (h hA)⟩

lemma clusterAvoid_empty_eq {G : SimpleGraph V} {ω : G.edgeSet → Bool} (x : V) :
    clusterAvoid G ω ∅ x = {y | OpenConnected G ω Set.univ x y} := by
  simp [clusterAvoid]

/-- Every `e : Sym2 V` is a pair. -/
lemma exists_eq_s (e : Sym2 V) : ∃ a b : V, e = s(a, b) := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, rfl⟩

/-- **Single-edge cover.**  Avoiding a larger edge set splits the cluster into
the piece through `x` together with the pieces through the two endpoints of the
newly avoided edge. -/
lemma clusterAvoid_cover_insert {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {A : Set (Sym2 V)} {e : Sym2 V} (he : e ∉ A) {a b : V} (hab : e = s(a, b))
    (x : V) :
    clusterAvoid G ω A x ⊆ clusterAvoid G ω (insert e A) x ∪
      (clusterAvoid G ω (insert e A) a ∪ clusterAvoid G ω (insert e A) b) := by
  classical
  set A' : Set (Sym2 V) := Set.univ \ (insert e A) with hA'
  set B : Set (Sym2 V) := Set.univ \ A with hB
  set C : V → Set V := fun z => clusterAvoid G ω (insert e A) z with hC
  have hBA : B = A' ∪ {e} := by
    rw [hA', hB]
    ext g
    constructor
    · intro hg
      by_cases hge : g = e
      · exact Or.inr hge
      · refine Or.inl ⟨trivial, ?_⟩
        intro hcon
        rcases hcon with he' | hA
        · exact hge he'
        · exact hg.2 hA
    · intro hA
      rcases hA with ⟨-, hA'⟩ | hge
      · exact ⟨trivial, fun hcon => hA' (Or.inr hcon)⟩
      · exact ⟨trivial, fun hcon => he (hge ▸ hcon)⟩
  intro y hy
  have key : ∀ {u v : V} (q : G.Walk u v), IsOpenIn ω B q → v ∈ C u ∪ (C a ∪ C b) := by
    intro u v q
    induction q with
    | nil => intro _; exact Or.inl (OpenConnected.refl _ _ _)
    | @cons u w v hadj q ih =>
      intro hq
      obtain ⟨hhead, htail⟩ := isOpenIn_cons.mp hq
      have ih' := ih htail
      by_cases hmem : s(u, w) ∈ A'
      · have hsub : C w ⊆ C u := fun z hz =>
          (OpenConnected.of_adj hadj hmem hhead.2).trans hz
        rcases ih' with h | h
        · exact Or.inl (hsub h)
        · exact Or.inr h
      · have hBmem : s(u, w) ∈ B := hhead.1
        rw [hBA] at hBmem
        have hse : s(u, w) = e := by
          rcases hBmem with h' | h'
          · exact absurd h' hmem
          · exact h'
        have hse2 : s(u, w) = s(a, b) := by rw [hab] at hse; exact hse
        have hw : w = a ∨ w = b := by
          rcases (Sym2.eq_iff).mp hse2 with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact Or.inr h2
          · exact Or.inl h2
        rcases hw with hwa | hwb
        · subst hwa
          rcases ih' with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr h
        · subst hwb
          rcases ih' with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr h
  obtain ⟨p, hp⟩ := hy
  exact key p hp

/-- **Finite cover.**  For a finite edge set `A`, the full open cluster of `x` is
covered by the `A`-avoiding clusters of finitely many vertices. -/
theorem exists_finite_cover {G : SimpleGraph V} {ω : G.edgeSet → Bool} (x : V) :
    ∀ {A : Set (Sym2 V)}, A.Finite →
      ∃ L : Set V, L.Finite ∧
        ∀ y, y ∈ clusterAvoid G ω ∅ x → ∃ z ∈ L, y ∈ clusterAvoid G ω A z := by
  intro A hA
  refine Set.Finite.induction_on
    (motive := fun A _ => ∃ L : Set V, L.Finite ∧
      ∀ y, y ∈ clusterAvoid G ω ∅ x → ∃ z ∈ L, y ∈ clusterAvoid G ω A z) A hA ?_ ?_
  · refine ⟨{x}, Set.finite_singleton x, ?_⟩
    intro y hy
    exact ⟨x, rfl, hy⟩
  · rintro a A ha hAf ⟨L, hLfin, hL⟩
    obtain ⟨p, q, hpq⟩ := exists_eq_s a
    refine ⟨insert p (insert q L), (hLfin.insert q).insert p, ?_⟩
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hL y hy
    have hcov := clusterAvoid_cover_insert (G := G) (ω := ω) ha hpq z hzy
    rcases hcov with h | h | h
    · exact ⟨z, Or.inr (Or.inr hz), h⟩
    · exact ⟨p, Or.inl rfl, h⟩
    · exact ⟨q, Or.inr (Or.inl rfl), h⟩

/-- **Existence of infinite clusters survives avoiding finitely many edges.** -/
theorem exists_infinite_cluster_avoid {G : SimpleGraph V} {ω : G.edgeSet → Bool}
    {x : V} {A : Set (Sym2 V)} (hA : A.Finite)
    (h : (clusterAvoid G ω ∅ x).Infinite) :
    ∃ z, (clusterAvoid G ω A z).Infinite := by
  obtain ⟨L, hLfin, hL⟩ := exists_finite_cover (G := G) (ω := ω) x hA
  have hsub : clusterAvoid G ω ∅ x ⊆ ⋃ z ∈ L, clusterAvoid G ω A z := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hL y hy
    exact Set.mem_iUnion₂.mpr ⟨z, hz, hzy⟩
  have h' : (⋃ z ∈ L, clusterAvoid G ω A z).Infinite := h.mono hsub
  by_contra hall
  push Not at hall
  exact h' (Set.Finite.biUnion hLfin fun z _ => hall z)

/-- **Finite-modification invariance** of the existence of an infinite cluster. -/
theorem hasInfiniteCluster_congr {G : SimpleGraph V} {ω ω' : G.edgeSet → Bool}
    {A : Set (Sym2 V)} (hA : A.Finite)
    (h : ∀ e : G.edgeSet, (e : Sym2 V) ∉ A → ω e = ω' e) :
    HasInfiniteCluster G ω ↔ HasInfiniteCluster G ω' := by
  have step : ∀ {ω ω' : G.edgeSet → Bool}, (∀ e : G.edgeSet, (e : Sym2 V) ∉ A → ω e = ω' e) →
      HasInfiniteCluster G ω → HasInfiniteCluster G ω' := by
    rintro ω ω' hagree ⟨x, hx⟩
    obtain ⟨z, hz⟩ := exists_infinite_cluster_avoid hA hx
    refine ⟨z, ?_⟩
    rw [clusterAvoid_empty_eq]
    refine hz.mono ?_
    intro y hy
    exact OpenConnected.mono_edges (OpenConnected.congr hy fun e he => hagree e he.2)
      (fun g _ => trivial)
  exact ⟨step h, step (fun e he => (h e he).symm)⟩

end FK.ClusterCover
