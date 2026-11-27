import FK.TreeJunction

/-!
# Central junctions in a graph with three leaves

A connected central graph with three singly attached leaves has a junction at
a central vertex.  This packages the finite graph used by the Burton--Keane
encounter-box construction.  The source inclusion is retained so edges can
subsequently be transported to open configurations.
-/

open scoped Classical

namespace FK.BurtonKeane

universe u

variable {B : Type u} (H : SimpleGraph B) (v : Fin 3 → B)

/-- A central graph with one external leaf attached at `v i` for each `i`. -/
def withLeaves : SimpleGraph (B ⊕ Fin 3) where
  Adj
    | .inl a, .inl b => H.Adj a b
    | .inl a, .inr i => a = v i
    | .inr i, .inl a => a = v i
    | .inr _, .inr _ => False
  symm := ⟨by
    rintro (a | i) (b | j) h
    · exact H.symm.symm _ _ h
    · exact h
    · exact h
    · exact h.elim⟩
  loopless := ⟨by
    rintro (a | i) h
    · exact H.loopless.irrefl a h
    · exact h.elim⟩

/-- Inclusion of the central graph in the three-leaf graph. -/
def centralHom : H →g withLeaves H v where
  toFun := Sum.inl
  map_rel' := fun h => h

lemma preconnected_withLeaves (hH : H.Connected) :
    (withLeaves H v).Preconnected := by
  letI : Nonempty B := hH.nonempty
  have hmap {a b : B} (p : H.Walk a b) :
      (withLeaves H v).Walk (.inl a) (.inl b) := p.map (centralHom H v)
  have rightLeft (i : Fin 3) (b : B) :
      (withLeaves H v).Reachable (.inr i) (.inl b) := by
    obtain ⟨p⟩ := hH.preconnected (v i) b
    let e : (withLeaves H v).Adj (.inr i) (.inl (v i)) := rfl
    exact (SimpleGraph.Walk.cons e (hmap p)).reachable
  intro x y
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          obtain ⟨p⟩ := hH.preconnected a b
          exact (hmap p).reachable
      | inr j => exact (rightLeft j a).symm
  | inr i =>
      cases y with
      | inl b => exact rightLeft i b
      | inr j =>
          let e : (withLeaves H v).Adj (.inl (v j)) (.inr j) := rfl
          obtain ⟨w⟩ := rightLeft i (v j)
          exact (w.append e.toWalk).reachable

lemma connected_withLeaves (hH : H.Connected) :
    (withLeaves H v).Connected := by
  letI : Nonempty B := hH.nonempty
  letI : Nonempty (B ⊕ Fin 3) := ⟨.inl Classical.ofNonempty⟩
  exact SimpleGraph.Connected.mk (preconnected_withLeaves H v hH)

/-- Two walks from the same degree-one vertex to two other vertices cannot
have only that vertex in common. -/
lemma false_of_junction_eq_leaf {W : Type*} {T : SimpleGraph W}
    {y l b c d : W} {pb : T.Walk y b} {pc : T.Walk y c}
    (hyl : y = l) (hb : b ≠ l) (hc : c ≠ l)
    (hsep : ∀ z ∈ pb.support, z ∈ pc.support → z = y)
    (hleaf : ∀ z, T.Adj l z → z = d) : False := by
  subst y
  cases pb with
  | nil => exact hb rfl
  | @cons _ w _ hp p =>
      cases pc with
      | nil => exact hc rfl
      | @cons _ w' _ hq q =>
          have hw : w = d := hleaf w hp
          have hw' : w' = d := hleaf w' hq
          subst w
          subst w'
          have hdp : d ∈ (SimpleGraph.Walk.cons hp p).support := by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr p.start_mem_support
          have hdq : d ∈ (SimpleGraph.Walk.cons hq q).support := by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr q.start_mem_support
          exact hp.ne (hsep d hdp hdq).symm

/-- Any spanning tree of `withLeaves` has only the prescribed central
neighbour at an external leaf. -/
lemma leaf_adj_unique {T : SimpleGraph (B ⊕ Fin 3)}
    (hle : T ≤ withLeaves H v) (i : Fin 3) (z : B ⊕ Fin 3)
    (hz : T.Adj (.inr i) z) : z = .inl (v i) := by
  have hf := hle hz
  cases z with
  | inl a => exact congrArg Sum.inl hf
  | inr j => exact hf.elim

/-- **Central three-way junction.**  Besides pairwise separation, each branch
avoids the other two external leaves. -/
theorem exists_central_three_way_junction (hH : H.Connected) :
    ∃ T : SimpleGraph (B ⊕ Fin 3), ∃ _hle : T ≤ withLeaves H v,
      ∃ _hT : T.IsTree,
      ∃ y : B, ∃ pa : T.Walk (.inl y) (.inr 0), ∃ pb : T.Walk (.inl y) (.inr 1),
        ∃ pc : T.Walk (.inl y) (.inr 2),
          pa.IsPath ∧ pb.IsPath ∧ pc.IsPath ∧
          (∀ z ∈ pa.support, z ∈ pb.support → z = .inl y) ∧
          (∀ z ∈ pa.support, z ∈ pc.support → z = .inl y) ∧
          (∀ z ∈ pb.support, z ∈ pc.support → z = .inl y) ∧
          (.inr 1 ∉ pa.support) ∧ (.inr 2 ∉ pa.support) ∧
          (.inr 0 ∉ pb.support) ∧ (.inr 2 ∉ pb.support) ∧
          (.inr 0 ∉ pc.support) ∧ (.inr 1 ∉ pc.support) := by
  obtain ⟨T, hle, hT⟩ := (connected_withLeaves H v hH).exists_isTree_le
  obtain ⟨y, pa, pb, pc, hpa, hpb, hpc, hab, hac, hbc⟩ :=
    hT.exists_three_way_junction (.inr 0) (.inr 1) (.inr 2)
  have hleaf (i : Fin 3) := leaf_adj_unique H v hle i
  have hnot0 : y ≠ .inr 0 := by
    intro hy
    subst y
    exact false_of_junction_eq_leaf (pb := pb) (pc := pc) rfl
      (by simp) (by simp) hbc (hleaf 0)
  have hnot1 : y ≠ .inr 1 := by
    intro hy
    subst y
    exact false_of_junction_eq_leaf (pb := pa) (pc := pc) rfl
      (by simp) (by simp) hac (hleaf 1)
  have hnot2 : y ≠ .inr 2 := by
    intro hy
    subst y
    exact false_of_junction_eq_leaf (pb := pa) (pc := pb) rfl
      (by simp) (by simp) hab (hleaf 2)
  have hnot : ∀ i : Fin 3, y ≠ .inr i := by
    intro i
    fin_cases i
    · exact hnot0
    · exact hnot1
    · exact hnot2
  cases y with
  | inr i => exact (hnot i rfl).elim
  | inl y =>
      refine ⟨T, hle, hT, y, pa, pb, pc, hpa, hpb, hpc, hab, hac, hbc, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have he := hab (.inr 1) h pb.end_mem_support
        exact (hnot 1 he.symm).elim
      · intro h
        have he := hac (.inr 2) h pc.end_mem_support
        exact (hnot 2 he.symm).elim
      · intro h
        have he := hab (.inr 0) pa.end_mem_support h
        exact (hnot 0 he.symm).elim
      · intro h
        have he := hbc (.inr 2) h pc.end_mem_support
        exact (hnot 2 he.symm).elim
      · intro h
        have he := hac (.inr 0) pa.end_mem_support h
        exact (hnot 0 he.symm).elim
      · intro h
        have he := hbc (.inr 1) pb.end_mem_support h
        exact (hnot 1 he.symm).elim
