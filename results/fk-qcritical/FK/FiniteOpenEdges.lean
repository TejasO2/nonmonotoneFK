import FK.PlaneClusterTarget

/-!
# Finite open edge sets have finite open components

A purely graph-theoretic step used by the planar instance: if only finitely many
edges of a configuration are open, then every open component is finite.  The
component of a vertex is contained in that vertex together with the endpoints of
the finitely many open edges.

## Main results

* `FK.PlaneTopology.FiniteOpenEdges.noInfiniteOpenCluster_of_finite_openEdges`
-/

namespace FK.PlaneTopology.FiniteOpenEdges

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration

variable {V : Type*}

/-- The two canonical endpoints of a `Sym2`-edge.  This is the unordered-pair
counterpart of `Quot.out`. -/
lemma sym2_out_mem {a b : V} {e : Sym2 V} (h : e = s(a, b)) :
    e.out.1 = a ∨ e.out.2 = a := by
  have hout : s(e.out.1, e.out.2) = s(a, b) := (Quot.out_eq e).trans h
  rcases Sym2.eq_iff.mp hout with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact Or.inl h1
  · exact Or.inr h2

/-- Both vertices of a `Sym2` belong to the canonical representative. -/
lemma sym2_out_mem_right {a b : V} {e : Sym2 V} (h : e = s(a, b)) :
    e.out.1 = b ∨ e.out.2 = b := by
  have hout : s(e.out.1, e.out.2) = s(a, b) := (Quot.out_eq e).trans h
  rcases Sym2.eq_iff.mp hout with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact Or.inr h2
  · exact Or.inl h1

/-- **A finite open edge set has finite open components.** -/
theorem noInfiniteOpenCluster_of_finite_openEdges {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} (hfin : ({e : G.edgeSet | ω e = true}).Finite) (x : V) :
    {y : V | OpenConnected G ω Set.univ x y}.Finite := by
  classical
  set S : Set G.edgeSet := {e | ω e = true} with hS
  have hverts : (⋃ e ∈ S, ({e.1.out.1, e.1.out.2} : Set V)).Finite :=
    hfin.biUnion fun e _ => (Set.finite_singleton e.1.out.2).insert e.1.out.1
  refine (hverts.insert x).subset ?_
  rintro y ⟨p, hp⟩
  have key : ∀ {u v : V}, (q : G.Walk u v) → IsOpenIn ω Set.univ q →
      v = u ∨ v ∈ (⋃ e ∈ S, ({e.1.out.1, e.1.out.2} : Set V)) := by
    intro u v q
    induction q with
    | nil => intro _; exact Or.inl rfl
    | @cons a b c hab r ih =>
        intro hq
        obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hq
        rcases ih hrest with hc | hc
        · rw [hc]
          right
          have hmem : b ∈ ({((⟨s(a, b), hab⟩ : G.edgeSet)).1.out.1,
              ((⟨s(a, b), hab⟩ : G.edgeSet)).1.out.2} : Set V) := by
            have := sym2_out_mem_right (e := s(a, b)) rfl
            rcases this with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨hopen, hmem⟩⟩
        · exact Or.inr hc
  rcases key p hp with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The vertex set is a union of finitely many `Sym2` endpoint pairs, so a
configuration with finitely many open edges has finite open clusters. -/
theorem finiteOpenClusters_of_finite_openEdges {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} (hfin : ({e : G.edgeSet | ω e = true}).Finite) :
    ∀ x : V, {y : V | OpenConnected G ω Set.univ x y}.Finite :=
  noInfiniteOpenCluster_of_finite_openEdges hfin

end FK.PlaneTopology.FiniteOpenEdges

/-! ## Axiom audit -/

#print axioms FK.PlaneTopology.FiniteOpenEdges.noInfiniteOpenCluster_of_finite_openEdges
