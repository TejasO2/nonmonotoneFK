import FK.EncounterTreeBound

/-!
# Configurationwise marked-count bounds for finite encounter forests

The existing tree bound requires one connected tree.  This file proves the
corresponding bound for an arbitrary finite forest with no isolated vertices.
The no-isolated-vertices hypothesis is explicit: it is what lets the degree-one
vertices alone pay for all branch points.  No forest construction, invariance,
or Burton--Keane conclusion is asserted.
-/

open scoped BigOperators Classical
open Finset

namespace FK.BurtonKeane.TreeCounting

universe u v

variable {V : Type u} (G : SimpleGraph V)

/-- A finite nonempty forest has at most one fewer edge than vertex.  Extend it
to a spanning tree of the complete graph and compare edge sets. -/
lemma card_edgeFinset_add_one_le_card_of_isAcyclic [Fintype V] [Nonempty V]
    [Fintype G.edgeSet] (hG : G.IsAcyclic) :
    G.edgeFinset.card + 1 ≤ Fintype.card V := by
  classical
  let K : SimpleGraph V := ⊤
  have hK : K.Connected := by
    rw [show K = (⊤ : SimpleGraph V) from rfl]
    exact SimpleGraph.connected_top
  obtain ⟨T, hGT, _hTK, hT⟩ :=
    hK.exists_isTree_le_of_le_of_isAcyclic (show G ≤ K from le_top) hG
  have hc : G.edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_mono (by simpa using hGT)
  have hcard := hT.card_edgeFinset
  omega

/-- The forest form of the tree branch/leaf inequality.  Isolated vertices are
excluded; connected components may otherwise be arbitrary, including components
that are just one edge or a path. -/
theorem card_branch_add_two_le_card_leaf_of_isAcyclic_of_degree_pos
    [Fintype V] [Nonempty V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (hpos : ∀ v, 0 < G.degree v) :
    (branchFinset G).card + 2 ≤ (leafFinset G).card := by
  classical
  have hedge := card_edgeFinset_add_one_le_card_of_isAcyclic G hG
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hnat : (∑ v : V, G.degree v) + 2 ≤ 2 * Fintype.card V := by omega
  have hint : (∑ v : V, (G.degree v : ℤ)) + 2 ≤ 2 * (Fintype.card V : ℤ) := by
    exact_mod_cast hnat
  have hpoint (v : V) :
      0 ≤ (G.degree v : ℤ) - 2 + (if G.degree v = 1 then 1 else 0) -
        (if 3 ≤ G.degree v then 1 else 0) := by
    have hv := hpos v
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
  omega

/-- Branch points of a finite encounter forest are bounded by any boundary set
containing all its leaves. -/
theorem card_branch_le_card_boundary_of_isAcyclic_of_degree_pos
    [Fintype V] [Nonempty V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (hpos : ∀ v, 0 < G.degree v)
    (B : Finset V) (hleaves : ∀ v, G.degree v = 1 → v ∈ B) :
    (branchFinset G).card ≤ B.card := by
  have hsub : leafFinset G ⊆ B := by
    intro v hv
    exact hleaves v (Finset.mem_filter.mp hv).2
  have hcard := Finset.card_le_card hsub
  have hmain := card_branch_add_two_le_card_leaf_of_isAcyclic_of_degree_pos G hG hpos
  omega

/-- A configurationwise, genuinely multi-centre marked-count bound.  The
supplied graph may be a disconnected forest and all marked vertices of `F` are
charged simultaneously.  Constructing that forest from encounter geometry is a
separate, retained hypothesis. -/
theorem markedCount_le_of_encounterForest [Fintype V] [Nonempty V] [DecidableEq V]
    {Ω : Type v} (A : V → Set Ω) (T : Ω → SimpleGraph V)
    [∀ ω, DecidableRel (T ω).Adj]
    (hT : ∀ ω, (T ω).IsAcyclic) (hpos : ∀ ω v, 0 < (T ω).degree v)
    (F B : Finset V)
    (hleaves : ∀ ω v, (T ω).degree v = 1 → v ∈ B)
    (hmarked : ∀ ω v, v ∈ F → ω ∈ A v → 3 ≤ (T ω).degree v) (ω : Ω) :
    Folner.markedCount A F ω ≤ B.card := by
  unfold Folner.markedCount
  have hsub : F.filter (fun v => ω ∈ A v) ⊆ branchFinset (T ω) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [branchFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, hmarked ω v hv.1 hv.2⟩
  have hb := card_branch_le_card_boundary_of_isAcyclic_of_degree_pos
    (T ω) (hT ω) (hpos ω) B (hleaves ω)
  exact (Finset.card_le_card hsub).trans hb

end FK.BurtonKeane.TreeCounting

#print axioms FK.BurtonKeane.TreeCounting.card_edgeFinset_add_one_le_card_of_isAcyclic
#print axioms FK.BurtonKeane.TreeCounting.card_branch_add_two_le_card_leaf_of_isAcyclic_of_degree_pos
#print axioms FK.BurtonKeane.TreeCounting.card_branch_le_card_boundary_of_isAcyclic_of_degree_pos
#print axioms FK.BurtonKeane.TreeCounting.markedCount_le_of_encounterForest
