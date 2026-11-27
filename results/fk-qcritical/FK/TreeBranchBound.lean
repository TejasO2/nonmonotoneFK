import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring

/-!
# Branch points in finite trees

A nontrivial finite tree has at most `L - 2` vertices of degree at least
three, where `L` is its number of leaves.  The proof is the exact degree-sum
identity, not an asymptotic or probabilistic argument.

In a Burton--Keane application a pruned encounter tree can be chosen with all
its leaves on the boundary of a finite window.  The corollary below then
bounds its branch points by the boundary size.  Constructing and pruning that
tree from open three-arm configurations is intentionally outside this file.
-/

open scoped BigOperators Classical
open Finset

namespace FK.BurtonKeane.TreeCounting

universe u
variable {V : Type u} (G : SimpleGraph V)

/-- Degree-one vertices of a finite graph. -/
noncomputable def leafFinset [Fintype V] [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

/-- Vertices of degree at least three in a finite graph. -/
noncomputable def branchFinset [Fintype V] [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 3 ≤ G.degree v

/-- **The branch-point/leaf identity.**  Every finite nontrivial tree has two
more leaves than the lower bound obtained by counting one excess branch per
branch point. -/
theorem card_branch_add_two_le_card_leaf [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [Nontrivial V] (hG : G.IsTree) :
    (branchFinset G).card + 2 ≤ (leafFinset G).card := by
  classical
  have hedge := hG.card_edgeFinset
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hnat : (∑ v : V, G.degree v) + 2 = 2 * Fintype.card V := by
    calc
      (∑ v : V, G.degree v) + 2 = 2 * #G.edgeFinset + 2 :=
        congrArg (fun n => n + 2) hsum
      _ = 2 * Fintype.card V := by omega
  have hint : (∑ v : V, (G.degree v : ℤ)) + 2 = 2 * (Fintype.card V : ℤ) := by
    exact_mod_cast hnat
  have hpoint (v : V) :
      0 ≤ (G.degree v : ℤ) - 2 + (if G.degree v = 1 then 1 else 0) -
        (if 3 ≤ G.degree v then 1 else 0) := by
    have hpos := hG.preconnected.degree_pos_of_nontrivial v
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun v _hv => hpoint v)
  have hrewrite :
      (∑ v : V, ((G.degree v : ℤ) - 2 + (if G.degree v = 1 then 1 else 0) -
        (if 3 ≤ G.degree v then 1 else 0))) =
      (∑ v : V, (G.degree v : ℤ)) - 2 * (Fintype.card V : ℤ) +
        ((leafFinset G).card : ℤ) - ((branchFinset G).card : ℤ) := by
    simp only [leafFinset, branchFinset, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hrewrite] at hs
  simp only [Finset.sum_const_zero] at hs
  have hdegree : (∑ v : V, (G.degree v : ℤ)) = 2 * (Fintype.card V : ℤ) - 2 := by
    omega
  rw [hdegree] at hs
  have hz : ((branchFinset G).card : ℤ) + 2 ≤ ((leafFinset G).card : ℤ) := by
    omega
  exact_mod_cast hz

/-- If every leaf occurs in a prescribed boundary set, then the number of
branch points is bounded by that set's cardinality. -/
theorem card_branch_le_card_boundary [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [Nontrivial V] (hG : G.IsTree)
    (B : Finset V) (hleaves : ∀ v, G.degree v = 1 → v ∈ B) :
    (branchFinset G).card ≤ B.card := by
  have hsub : leafFinset G ⊆ B := by
    intro v hv
    exact hleaves v (Finset.mem_filter.mp hv).2
  have hcard := Finset.card_le_card hsub
  have hmain := card_branch_add_two_le_card_leaf G hG
  omega

/-- A set of certified branch points is bounded by any boundary set containing
all the leaves. -/
theorem card_le_card_boundary_of_subset_branch [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [Nontrivial V] (hG : G.IsTree)
    (B X : Finset V) (hleaves : ∀ v, G.degree v = 1 → v ∈ B)
    (hX : X ⊆ branchFinset G) :
    X.card ≤ B.card := by
  exact (Finset.card_le_card hX).trans (card_branch_le_card_boundary G hG B hleaves)

end FK.BurtonKeane.TreeCounting
