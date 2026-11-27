import FK.FolnerFirstMoment
import FK.TreeBranchBound

/-!
# From an encounter tree to a finite-window marked-count bound

This is the deterministic interface between the first-moment and tree-counting
components.  For each configuration, the caller must supply a finite tree on
the window's vertex type, prove that its leaves lie in the specified boundary,
and prove that every marked centre has degree at least three.  The theorem
then gives exactly the configurationwise bound used by `FolnerFirstMoment`.
No spanning-tree or pruning construction is asserted here.
-/

open scoped Classical
open FK.BurtonKeane.Folner

namespace FK.BurtonKeane.TreeCounting

universe u v
variable {Ω : Type u} {V : Type v}

/-- If every configuration admits an encounter tree whose leaves are on `B`
and in which every `F`-marked vertex has degree at least three, then there are
at most `B.card` marked vertices of `F`. -/
theorem markedCount_le_of_encounterTree [Fintype V] [DecidableEq V] [Nontrivial V]
    (A : V → Set Ω) (T : Ω → SimpleGraph V) [∀ ω, DecidableRel (T ω).Adj]
    (hT : ∀ ω, (T ω).IsTree) (F B : Finset V)
    (hleaves : ∀ ω v, (T ω).degree v = 1 → v ∈ B)
    (hmarked : ∀ ω v, v ∈ F → ω ∈ A v → 3 ≤ (T ω).degree v) (ω : Ω) :
    markedCount A F ω ≤ B.card := by
  unfold markedCount
  apply card_le_card_boundary_of_subset_branch (T ω) (hT ω) B
    (F.filter fun v => ω ∈ A v) (hleaves ω)
  intro v hv
  rw [Finset.mem_filter] at hv
  rw [branchFinset, Finset.mem_filter]
  exact ⟨Finset.mem_univ v, hmarked ω v hv.1 hv.2⟩

end FK.BurtonKeane.TreeCounting
