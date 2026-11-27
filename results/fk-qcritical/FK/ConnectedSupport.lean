import FK.AssemblyBranch

open scoped Classical

namespace FK.BurtonKeane

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A finite connected vertex set containing three prescribed vertices. -/
theorem exists_connected_support (hG : G.Connected) (a b c : V) :
    ∃ U : Set V, U.Finite ∧ a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ (G.induce U).Connected := by
  let pab := Classical.choice (hG.preconnected a b)
  let pac := Classical.choice (hG.preconnected a c)
  let U : Set V := {x | x ∈ pab.support ∨ x ∈ pac.support}
  have hU : U.Finite := pab.support.finite_toSet.union pac.support.finite_toSet
  have ha : a ∈ U := Or.inl pab.start_mem_support
  have hb : b ∈ U := Or.inl pab.end_mem_support
  have hc : c ∈ U := Or.inr pac.end_mem_support
  have reachable_a {x : V} (hx : x ∈ U) :
      (G.induce U).Reachable ⟨a, ha⟩ ⟨x, by exact hx⟩ := by
    rcases hx with hx | hx
    · let q := pab.takeUntil x hx
      exact ⟨q.induce U (fun z hz => Or.inl (pab.support_takeUntil_subset_support hx hz))⟩
    · let q := pac.takeUntil x hx
      exact ⟨q.induce U (fun z hz => Or.inr (pac.support_takeUntil_subset_support hx hz))⟩
  letI : Nonempty U := ⟨⟨a, ha⟩⟩
  refine ⟨U, hU, ha, hb, hc, SimpleGraph.Connected.mk ?_⟩
  intro x y
  obtain ⟨px⟩ := reachable_a x.2
  obtain ⟨py⟩ := reachable_a y.2
  exact px.reverse.append py |>.reachable
