import FK.LeafJunction
import FK.BurtonKeaneGeometry

/-!
# Removing and mapping leaves of central junction paths

The final leaf of a junction branch is stripped by reversing twice.  The
remaining central path is transported with `Walk.ofSupport`; its support is
exactly the mapped original support, so openness and disjointness can be
checked in the receiving graph.
-/

open scoped Classical
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane

universe u v

variable {B : Type u} (H : SimpleGraph B) (attach : Fin 3 → B)

/-- Strip the final external vertex of a path to a leaf. -/
theorem exists_stripLeaf {T : SimpleGraph (B ⊕ Fin 3)}
    (hle : T ≤ withLeaves H attach) {y : B} {i : Fin 3}
    (p : T.Walk (.inl y) (.inr i)) (hp : p.IsPath)
    (hother : ∀ j : Fin 3, j ≠ i → .inr j ∉ p.support) :
    ∃ q : T.Walk (.inl y) (.inl (attach i)),
      q.IsPath ∧ q.support ⊆ p.support ∧ (∀ j : Fin 3, .inr j ∉ q.support) := by
  have hrev : p.reverse.IsPath := p.isPath_reverse_iff.mpr hp
  cases hr : p.reverse with
  | @cons _ w _ hadj r =>
      have hw : w = .inl (attach i) := leaf_adj_unique H attach hle i w hadj
      subst w
      have hcons : (SimpleGraph.Walk.cons hadj r).IsPath := hr ▸ hrev
      have hrpath : r.IsPath := hcons.of_cons
      have hown : (.inr i) ∉ r.support :=
        (SimpleGraph.Walk.cons_isPath_iff hadj r).mp hcons |>.2
      let q := r.reverse
      have hqsub : q.support ⊆ p.support := by
        have hformula : p.support = r.support.reverse ++ [Sum.inr i] := by
          calc
            p.support = p.support.reverse.reverse := by simp
            _ = p.reverse.support.reverse := by rw [SimpleGraph.Walk.support_reverse]
            _ = (Sum.inr i :: r.support).reverse := by rw [hr, SimpleGraph.Walk.support_cons]
            _ = r.support.reverse ++ [Sum.inr i] := by simp
        intro z hz
        rw [hformula, List.mem_append]
        apply Or.inl
        simpa [q, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
      refine ⟨q, hrpath.reverse, hqsub, ?_⟩
      intro j
      by_cases hji : j = i
      · subst j
        simpa [q, SimpleGraph.Walk.support_reverse, List.mem_reverse] using hown
      · intro hz
        exact hother j hji (hqsub hz)

/-- Transport a central path with `Walk.ofSupport`.  Only the central image of
`F` needs to preserve adjacency and injectivity. -/
noncomputable def mappedCentralWalk {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hle : T ≤ withLeaves H attach) {a b : B}
    (q : T.Walk (.inl a) (.inl b)) (hno : ∀ i : Fin 3, .inr i ∉ q.support) :
    G.Walk (F (.inl a)) (F (.inl b)) := by
  let l := q.support.map F
  have hne : l ≠ [] := by simp [l]
  have hchain : l.IsChain G.Adj := by
    apply (List.isChain_map F).2
    apply q.isChain_adj_support.imp_of_mem_imp
    intro x y hx hy hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact hFadj x y (hle hxy)
        | inr j => exact (hno j hy).elim
    | inr i => exact (hno i hx).elim
  have hw := SimpleGraph.Walk.ofSupport l hne hchain
  exact hw.copy (by simp only [l, List.head_map, SimpleGraph.Walk.head_support])
    (by simp only [l, List.getLast_map, SimpleGraph.Walk.getLast_support])

lemma support_mappedCentralWalk {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hle : T ≤ withLeaves H attach) {a b : B}
    (q : T.Walk (.inl a) (.inl b)) (hno : ∀ i : Fin 3, .inr i ∉ q.support) :
    (mappedCentralWalk H attach F hFadj hle q hno).support = q.support.map F := by
  unfold mappedCentralWalk
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]

lemma isPath_mappedCentralWalk {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hFinj : Function.Injective (F ∘ Sum.inl))
    (hle : T ≤ withLeaves H attach) {a b : B}
    (q : T.Walk (.inl a) (.inl b)) (hq : q.IsPath)
    (hno : ∀ i : Fin 3, .inr i ∉ q.support) :
    (mappedCentralWalk H attach F hFadj hle q hno).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [support_mappedCentralWalk H attach F hFadj hle q hno]
  apply hq.support_nodup.map_on
  intro x hx y hy hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (hFinj hxy)
      | inr j => exact (hno j hy).elim
  | inr i => exact (hno i hx).elim



/-- Openness is unchanged by endpoint copies. -/
lemma isOpenIn_copy {V : Type u} {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {u v u' v' : V}
    {p : G.Walk u v} (hu : u = u') (hv : v = v')
    (hp : IsOpenIn ω A p) : IsOpenIn ω A (p.copy hu hv) := by
  cases hu
  cases hv
  exact hp

/-- Map the support of a central walk, keeping the original adjacency
available for every open-edge proof. -/
theorem isOpenIn_map_ofSupport {V : Type v} {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} [DecidableEq V]
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hFopen : ∀ a b (hab : H.Adj a b),
      ω ⟨s(F (.inl a), F (.inl b)), hFadj a b hab⟩ = true)
    (hle : T ≤ withLeaves H attach)
    (l : List (B ⊕ Fin 3)) (hne : l.map F ≠ [])
    (hchainF : (l.map F).IsChain G.Adj)
    (hchain : l.IsChain T.Adj) (hno : ∀ i : Fin 3, .inr i ∉ l) :
    IsOpenIn ω Set.univ (SimpleGraph.Walk.ofSupport (l.map F) hne hchainF) := by
  induction l using List.twoStepInduction with
  | nil => exact (hne (by simp)).elim
  | singleton x => exact isOpenIn_nil
  | cons_cons x y r ih ih' =>
      simp only [List.map_cons] at *
      change IsOpenIn ω Set.univ (SimpleGraph.Walk.cons hchainF.rel
        (SimpleGraph.Walk.ofSupport ((y :: r).map F)
          (by simp) hchainF.of_cons))
      apply isOpenIn_cons.mpr
      refine ⟨⟨Set.mem_univ _, ?_⟩, ?_⟩
      · have hadj := hchain.rel
        cases x with
        | inl x =>
            cases y with
            | inl y => exact hFopen x y (hle hadj)
            | inr j => exact (hno j (by simp)).elim
        | inr i => exact (hno i (by simp)).elim
      · exact ih' y (by simp) hchainF.of_cons hchain.of_cons (by
          intro i hi
          exact hno i (by simp [hi]))

/-- The mapped central path is open when each central edge is open in the
receiving configuration. -/
theorem isOpenIn_mappedCentralWalk {V : Type v} {G : SimpleGraph V}
    {ω : G.edgeSet → Bool} [DecidableEq V]
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hFopen : ∀ a b (hab : H.Adj a b),
      ω ⟨s(F (.inl a), F (.inl b)), hFadj a b hab⟩ = true)
    (hle : T ≤ withLeaves H attach) {a b : B}
    (q : T.Walk (.inl a) (.inl b)) (hno : ∀ i : Fin 3, .inr i ∉ q.support) :
    IsOpenIn ω Set.univ (mappedCentralWalk H attach F hFadj hle q hno) := by
  unfold mappedCentralWalk
  apply isOpenIn_copy
  let l := q.support.map F
  have hne : l ≠ [] := by simp [l]
  have hchainF : l.IsChain G.Adj := by
    apply (List.isChain_map F).2
    apply q.isChain_adj_support.imp_of_mem_imp
    intro x y hx hy hxy
    cases x with
    | inl x =>
        cases y with
        | inl y => exact hFadj x y (hle hxy)
        | inr j => exact (hno j hy).elim
    | inr i => exact (hno i hx).elim
  apply isOpenIn_map_ofSupport H attach F hFadj hFopen hle q.support hne hchainF
    q.isChain_adj_support hno



/-- Separation of two central junction paths descends to their mapped walks. -/
lemma mappedCentral_meet {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hFinj : Function.Injective (F ∘ Sum.inl))
    (hle : T ≤ withLeaves H attach) {y a b : B}
    (qa : T.Walk (.inl y) (.inl a)) (qb : T.Walk (.inl y) (.inl b))
    (haNo : ∀ i : Fin 3, .inr i ∉ qa.support)
    (hbNo : ∀ i : Fin 3, .inr i ∉ qb.support)
    (hsep : ∀ z ∈ qa.support, z ∈ qb.support → z = .inl y) :
    ∀ z ∈ (mappedCentralWalk H attach F hFadj hle qa haNo).support,
      z ∈ (mappedCentralWalk H attach F hFadj hle qb hbNo).support →
      z = F (.inl y) := by
  intro z hza hzb
  rw [support_mappedCentralWalk H attach F hFadj hle qa haNo] at hza
  rw [support_mappedCentralWalk H attach F hFadj hle qb hbNo] at hzb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hza
  obtain ⟨w, hw, hwz⟩ := List.mem_map.mp hzb
  cases x with
  | inl x =>
      cases w with
      | inl w =>
          apply congrArg F
          have hxw : w = x := hFinj hwz
          exact hsep (.inl x) hx (by simpa [hxw] using hw)
      | inr j => exact (hbNo j hw).elim
  | inr i => exact (haNo i hx).elim

/-- An external set containing no central image vertex is disjoint from a
mapped central walk. -/
lemma mappedCentral_disjoint_of_forall_inl {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hle : T ≤ withLeaves H attach) {a b : B}
    (q : T.Walk (.inl a) (.inl b)) (hno : ∀ i : Fin 3, .inr i ∉ q.support)
    (R : Set V) (hR : ∀ x : B, F (.inl x) ∉ R) :
    ∀ z ∈ (mappedCentralWalk H attach F hFadj hle q hno).support, z ∈ R → False := by
  intro z hz hRz
  rw [support_mappedCentralWalk H attach F hFadj hle q hno] at hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  cases x with
  | inl x => exact hR x hRz
  | inr i => exact hno i hx



/-- Disjointness with one designated central attachment allowed only outside
that branch. -/
lemma mappedCentral_disjoint_except {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hle : T ≤ withLeaves H attach) {a b : B}
    (q : T.Walk (.inl a) (.inl b)) (hno : ∀ i : Fin 3, .inr i ∉ q.support)
    (bad : B) (hbad : .inl bad ∉ q.support)
    (R : Set V) (hR : ∀ x : B, x ≠ bad → F (.inl x) ∉ R) :
    ∀ z ∈ (mappedCentralWalk H attach F hFadj hle q hno).support, z ∈ R → False := by
  intro z hz hRz
  rw [support_mappedCentralWalk H attach F hFadj hle q hno] at hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  cases x with
  | inl x =>
      by_cases hxb : x = bad
      · subst bad
        exact hbad hx
      · exact hR x hxb hRz
  | inr i => exact hno i hx



/-- Other-parent contacts either return the common centre or are excluded. -/
lemma mappedCentral_disjoint_except_center {V : Type v} {G : SimpleGraph V}
    {T : SimpleGraph (B ⊕ Fin 3)} (F : B ⊕ Fin 3 → V)
    (hFadj : ∀ a b : B, H.Adj a b → G.Adj (F (.inl a)) (F (.inl b)))
    (hle : T ≤ withLeaves H attach) {y b : B}
    (q : T.Walk (.inl y) (.inl b)) (hno : ∀ i : Fin 3, .inr i ∉ q.support)
    (bad : B) (hbad : .inl bad ∈ q.support → bad = y)
    (R : Set V) (hR : ∀ x : B, x ≠ bad → F (.inl x) ∉ R) :
    ∀ z ∈ (mappedCentralWalk H attach F hFadj hle q hno).support, z ∈ R →
      z = F (.inl y) := by
  intro z hz hRz
  rw [support_mappedCentralWalk H attach F hFadj hle q hno] at hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  cases x with
  | inl x =>
      by_cases hxb : x = bad
      · subst bad
        exact congrArg (fun a => F (.inl a)) (hbad hx)
      · exact (hR x hxb hRz).elim
  | inr i => exact (hno i hx).elim
