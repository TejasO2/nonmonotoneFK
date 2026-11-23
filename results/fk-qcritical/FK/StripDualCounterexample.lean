import FK.PlaneClusterTarget

/-!
# A genuine plane strip whose dual is not locally finite

`FK/PlaneClusterTarget.lean` records the deterministic target
`DualNonpercolationForcesPrimalAtMostOne G GD edge`: for **any** pair of simple
graphs with an edge bijection, absence of an infinite dual-open cluster must
force at most one infinite primal-open cluster.  That predicate carries no
geometric hypotheses at all.

This module proves the predicate **false**, with a witness whose `GD` is the
actual planar dual of a genuine straight-line drawing:

* `stripGraph` is the infinite three-row strip on `ℤ × Fin 3`: horizontal edges
  inside each row, vertical rungs between consecutive rows.  It is connected,
  locally finite, and is drawn with straight segments on the lattice.
* `dualGraph` is its planar dual: one vertex per bounded unit square `(i,0)`,
  `(i,1)` plus the outer face `none`, and one dual edge per primal edge,
  pairing the two faces adjacent to that edge.
* Closing the three horizontal edges crossing the column boundary between
  `x = 0` and `x = 1` disconnects the strip into two infinite pieces, while the
  three corresponding dual edges span only the three dual vertices
  `none, (0,0), (0,1)`; every other dual-open component is a single vertex.

Hence no infinite dual-open cluster exists and yet the primal has two infinite
open clusters.  The obstruction is exactly the hypothesis the source paper adds
in Theorem 1.11 and which the repository's bare predicate omits: the outer face
of the strip has infinitely many boundary edges, so `dualGraph` is **not
locally finite** (its vertex `none` has infinitely many neighbours).  With a
locally finite dual a finite cut cannot be assembled this way, which is the
residual geometric content of the planar cluster-count step.

## Main results

* `FK.PlaneTopology.StripDual.not_dualNonpercolationForcesPrimalAtMostOne`
* `FK.PlaneTopology.StripDual.dualGraph_neighbourSet_none_infinite`
-/

namespace FK.PlaneTopology.StripDual

open Set
open scoped Classical
open CurvatureVariance.Infra.Percolation
open FK.Configuration
open FK.InfiniteVolume.ConventionTransport
open FK.InfiniteVolume.ConventionGeometry

/-- Vertices of the three-row strip: column index and row index. -/
abbrev PVertex := ℤ × Fin 3

/-- Vertices of the dual: `some (i, k)` is the bounded unit square in columns
`i, i+1` and rows `k, k+1`; `none` is the outer face. -/
abbrev FVertex := Option (ℤ × Fin 2)

/-- Edge index: three horizontal families (one per row) and two vertical
families (one per pair of adjacent rows). -/
inductive EIdx
  | h0 (i : ℤ)
  | h1 (i : ℤ)
  | h2 (i : ℤ)
  | v0 (i : ℤ)
  | v1 (i : ℤ)
  deriving DecidableEq

namespace EIdx

/-- Primal source of an indexed edge. -/
def pSrc : EIdx → PVertex
  | h0 i => (i, 0)
  | h1 i => (i, 1)
  | h2 i => (i, 2)
  | v0 i => (i, 0)
  | v1 i => (i, 1)

/-- Primal target of an indexed edge. -/
def pTgt : EIdx → PVertex
  | h0 i => (i + 1, 0)
  | h1 i => (i + 1, 1)
  | h2 i => (i + 1, 2)
  | v0 i => (i, 1)
  | v1 i => (i, 2)

/-- First dual endpoint of the indexed edge: the face on one side. -/
def dSrc : EIdx → FVertex
  | h0 i => none
  | h1 i => some (i, 0)
  | h2 i => some (i, 1)
  | v0 i => some (i - 1, 0)
  | v1 i => some (i - 1, 1)

/-- Second dual endpoint of the indexed edge: the face on the other side. -/
def dTgt : EIdx → FVertex
  | h0 i => some (i, 0)
  | h1 i => some (i, 1)
  | h2 i => none
  | v0 i => some (i, 0)
  | v1 i => some (i, 1)

lemma pSrc_ne_pTgt (a : EIdx) : pSrc a ≠ pTgt a := by
  cases a <;> simp [pSrc, pTgt]

lemma dSrc_ne_dTgt (a : EIdx) : dSrc a ≠ dTgt a := by
  cases a <;> simp [dSrc, dTgt]

end EIdx

/-- The infinite three-row strip, with adjacency presented through the edge
index. -/
def stripGraph : SimpleGraph PVertex where
  Adj x y := ∃ a : EIdx,
    (x = a.pSrc ∧ y = a.pTgt) ∨ (x = a.pTgt ∧ y = a.pSrc)
  symm := ⟨by
    intro x y h
    obtain ⟨a, h | h⟩ := h
    · exact ⟨a, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨a, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, h | h⟩ := h
    · exact EIdx.pSrc_ne_pTgt a (h.1.symm.trans h.2)
    · exact EIdx.pSrc_ne_pTgt a (h.2.symm.trans h.1)⟩

/-- The planar dual of the strip: one vertex per face. -/
def dualGraph : SimpleGraph FVertex where
  Adj f g := ∃ a : EIdx,
    (f = a.dSrc ∧ g = a.dTgt) ∨ (f = a.dTgt ∧ g = a.dSrc)
  symm := ⟨by
    intro x y h
    obtain ⟨a, h | h⟩ := h
    · exact ⟨a, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨a, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, h | h⟩ := h
    · exact EIdx.dSrc_ne_dTgt a (h.1.symm.trans h.2)
    · exact EIdx.dSrc_ne_dTgt a (h.2.symm.trans h.1)⟩

namespace EIdx

lemma stripGraph_adj (a : EIdx) : stripGraph.Adj a.pSrc a.pTgt :=
  ⟨a, Or.inl ⟨rfl, rfl⟩⟩

lemma dualGraph_adj (a : EIdx) : dualGraph.Adj a.dSrc a.dTgt :=
  ⟨a, Or.inl ⟨rfl, rfl⟩⟩

/-- The primal edge represented by an index. -/
def pEdge (a : EIdx) : stripGraph.edgeSet := ⟨s(a.pSrc, a.pTgt), a.stripGraph_adj⟩

/-- The dual edge represented by an index. -/
def dEdge (a : EIdx) : dualGraph.edgeSet := ⟨s(a.dSrc, a.dTgt), a.dualGraph_adj⟩

/-- Recovering the index from a primal edge. -/
lemma pEdge_injective : Function.Injective pEdge := by
  intro a b h
  have h' : s(a.pSrc, a.pTgt) = s(b.pSrc, b.pTgt) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at h'
  rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · cases a <;> cases b <;>
      simp [pSrc, pTgt, Prod.mk.injEq] at h1 h2 ⊢ <;>
      omega
  · cases a <;> cases b <;>
      simp [pSrc, pTgt, Prod.mk.injEq] at h1 h2 <;>
      omega

/-- Recovering the index from a dual edge. -/
lemma dEdge_injective : Function.Injective dEdge := by
  intro a b h
  have h' : s(a.dSrc, a.dTgt) = s(b.dSrc, b.dTgt) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at h'
  rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · cases a <;> cases b <;>
      simp [dSrc, dTgt, Prod.mk.injEq] at h1 h2 ⊢ <;>
      omega
  · cases a <;> cases b <;>
      simp [dSrc, dTgt, Prod.mk.injEq] at h1 h2 <;>
      omega

/-- Every primal edge is indexed. -/
lemma pEdge_surjective : Function.Surjective pEdge := by
  intro e
  have hmem : s((e : Sym2 PVertex).out.1, (e : Sym2 PVertex).out.2) ∈
      stripGraph.edgeSet := by
    rw [Sym2.mk, Quot.out_eq]
    exact e.2
  rw [SimpleGraph.mem_edgeSet] at hmem
  obtain ⟨a, h | h⟩ := hmem
  · refine ⟨a, Subtype.ext ?_⟩
    have hp : (EIdx.pSrc a, EIdx.pTgt a) =
        ((e : Sym2 PVertex).out.1, (e : Sym2 PVertex).out.2) := by
      rw [Prod.mk.injEq]
      exact ⟨h.1.symm, h.2.symm⟩
    have heq : (e : Sym2 PVertex) =
        s((e : Sym2 PVertex).out.1, (e : Sym2 PVertex).out.2) := (Quot.out_eq _).symm
    rw [heq]
    exact congrArg (Quot.mk (Sym2.Rel PVertex)) hp
  · refine ⟨a, Subtype.ext ?_⟩
    have hp : (EIdx.pSrc a, EIdx.pTgt a) =
        ((e : Sym2 PVertex).out.2, (e : Sym2 PVertex).out.1) := by
      rw [Prod.mk.injEq]
      exact ⟨h.2.symm, h.1.symm⟩
    have heq : (e : Sym2 PVertex) =
        s((e : Sym2 PVertex).out.1, (e : Sym2 PVertex).out.2) := (Quot.out_eq _).symm
    rw [heq]
    calc s(EIdx.pSrc a, EIdx.pTgt a)
        = s((e : Sym2 PVertex).out.2, (e : Sym2 PVertex).out.1) :=
          congrArg (Quot.mk (Sym2.Rel PVertex)) hp
      _ = s((e : Sym2 PVertex).out.1, (e : Sym2 PVertex).out.2) := Sym2.eq_swap

/-- Every dual edge is indexed. -/
lemma dEdge_surjective : Function.Surjective dEdge := by
  intro e
  have hmem : s((e : Sym2 FVertex).out.1, (e : Sym2 FVertex).out.2) ∈
      dualGraph.edgeSet := by
    rw [Sym2.mk, Quot.out_eq]
    exact e.2
  rw [SimpleGraph.mem_edgeSet] at hmem
  obtain ⟨a, h | h⟩ := hmem
  · refine ⟨a, Subtype.ext ?_⟩
    have hp : (EIdx.dSrc a, EIdx.dTgt a) =
        ((e : Sym2 FVertex).out.1, (e : Sym2 FVertex).out.2) := by
      rw [Prod.mk.injEq]
      exact ⟨h.1.symm, h.2.symm⟩
    have heq : (e : Sym2 FVertex) =
        s((e : Sym2 FVertex).out.1, (e : Sym2 FVertex).out.2) := (Quot.out_eq _).symm
    rw [heq]
    exact congrArg (Quot.mk (Sym2.Rel FVertex)) hp
  · refine ⟨a, Subtype.ext ?_⟩
    have hp : (EIdx.dSrc a, EIdx.dTgt a) =
        ((e : Sym2 FVertex).out.2, (e : Sym2 FVertex).out.1) := by
      rw [Prod.mk.injEq]
      exact ⟨h.2.symm, h.1.symm⟩
    have heq : (e : Sym2 FVertex) =
        s((e : Sym2 FVertex).out.1, (e : Sym2 FVertex).out.2) := (Quot.out_eq _).symm
    rw [heq]
    calc s(EIdx.dSrc a, EIdx.dTgt a)
        = s((e : Sym2 FVertex).out.2, (e : Sym2 FVertex).out.1) :=
          congrArg (Quot.mk (Sym2.Rel FVertex)) hp
      _ = s((e : Sym2 FVertex).out.1, (e : Sym2 FVertex).out.2) := Sym2.eq_swap

end EIdx

/-- The actual global edge bijection between the strip and its planar dual:
both edge sets are indexed by the same five edge families. -/
noncomputable def edgeEquiv : stripGraph.edgeSet ≃ dualGraph.edgeSet where
  toFun e := EIdx.dEdge (Classical.choose (EIdx.pEdge_surjective e))
  invFun f := EIdx.pEdge (Classical.choose (EIdx.dEdge_surjective f))
  left_inv e := by
    have h1 : EIdx.pEdge (Classical.choose (EIdx.pEdge_surjective e)) = e :=
      Classical.choose_spec (EIdx.pEdge_surjective e)
    have h2 : Classical.choose
        (EIdx.dEdge_surjective (EIdx.dEdge (Classical.choose (EIdx.pEdge_surjective e)))) =
        Classical.choose (EIdx.pEdge_surjective e) :=
      EIdx.dEdge_injective (Classical.choose_spec
        (EIdx.dEdge_surjective (EIdx.dEdge (Classical.choose (EIdx.pEdge_surjective e)))))
    show EIdx.pEdge (Classical.choose
      (EIdx.dEdge_surjective (EIdx.dEdge (Classical.choose (EIdx.pEdge_surjective e))))) = e
    rw [h2, h1]
  right_inv f := by
    have h1 : EIdx.dEdge (Classical.choose (EIdx.dEdge_surjective f)) = f :=
      Classical.choose_spec (EIdx.dEdge_surjective f)
    have h2 : Classical.choose
        (EIdx.pEdge_surjective (EIdx.pEdge (Classical.choose (EIdx.dEdge_surjective f)))) =
        Classical.choose (EIdx.dEdge_surjective f) :=
      EIdx.pEdge_injective (Classical.choose_spec
        (EIdx.pEdge_surjective (EIdx.pEdge (Classical.choose (EIdx.dEdge_surjective f)))))
    show EIdx.dEdge (Classical.choose
      (EIdx.pEdge_surjective (EIdx.pEdge (Classical.choose (EIdx.dEdge_surjective f))))) = f
    rw [h2, h1]

@[simp] lemma edgeEquiv_pEdge (a : EIdx) : edgeEquiv (EIdx.pEdge a) = EIdx.dEdge a := by
  have h : Classical.choose (EIdx.pEdge_surjective (EIdx.pEdge a)) = a :=
    EIdx.pEdge_injective (Classical.choose_spec (EIdx.pEdge_surjective (EIdx.pEdge a)))
  show EIdx.dEdge (Classical.choose (EIdx.pEdge_surjective (EIdx.pEdge a))) = EIdx.dEdge a
  rw [h]

/-! ## The separating configuration and the two infinite clusters -/

/-- The three horizontal edges crossing the column boundary between `0` and
`1`.  Closing exactly these severs the strip into a left and a right half. -/
def cutIdx : Set EIdx := {a | a = EIdx.h0 0 ∨ a = EIdx.h1 0 ∨ a = EIdx.h2 0}

/-- The three dual vertices spanned by the dual-open edges above. -/
def smallFaceSet : Set FVertex :=
  {none, some ((0 : ℤ), (0 : Fin 2)), some ((0 : ℤ), (1 : Fin 2))}

lemma smallFaceSet_finite : smallFaceSet.Finite := by
  simp [smallFaceSet]

/-- The closed primal edges: the separating horizontals. -/
def closedSet : Set stripGraph.edgeSet := EIdx.pEdge '' cutIdx

/-- The configuration used for the counterexample: exactly the three
separating horizontal edges are closed. -/
noncomputable def ω : stripGraph.edgeSet → Bool := by
  classical
  exact fun e => if e ∈ closedSet then false else true

lemma omega_pEdge (a : EIdx) : ω (EIdx.pEdge a) = if a ∈ cutIdx then false else true := by
  have h : (EIdx.pEdge a ∈ closedSet) ↔ a ∈ cutIdx := by
    constructor
    · rintro ⟨b, hb, hba⟩
      rwa [← EIdx.pEdge_injective hba]
    · intro ha
      exact ⟨a, ha, rfl⟩
  simp only [ω, h]

lemma omega_pEdge_eq_true_iff (a : EIdx) : ω (EIdx.pEdge a) = true ↔ a ∉ cutIdx := by
  rw [omega_pEdge]
  by_cases ha : a ∈ cutIdx <;> simp [ha]

/-- **Dual openness.**  A dual edge is open exactly when its index is one of
the three separating horizontals. -/
lemma dualConfig_dEdge (a : EIdx) :
    dualConfig edgeEquiv ω (EIdx.dEdge a) = if a ∈ cutIdx then true else false := by
  have h : edgeEquiv.symm (EIdx.dEdge a) = EIdx.pEdge a := by
    rw [← edgeEquiv_pEdge a, Equiv.symm_apply_apply]
  rw [dualConfig, h, omega_pEdge]
  by_cases ha : a ∈ cutIdx <;> simp [ha]

/-- Both endpoints of a separating dual edge lie in the three-element face
set. -/
lemma dEnds_mem_smallFaceSet {a : EIdx} (ha : a ∈ cutIdx) :
    EIdx.dSrc a ∈ smallFaceSet ∧ EIdx.dTgt a ∈ smallFaceSet := by
  rcases ha with rfl | rfl | rfl <;>
    simp [EIdx.dSrc, EIdx.dTgt, smallFaceSet]

/-- A dual-open edge has both endpoints in `smallFaceSet`. -/
lemma dualOpen_ends {f : dualGraph.edgeSet} (hf : dualConfig edgeEquiv ω f = true)
    {x y : FVertex} (hxy : (f : Sym2 FVertex) = s(x, y)) :
    x ∈ smallFaceSet ∧ y ∈ smallFaceSet := by
  obtain ⟨a, rfl⟩ := EIdx.dEdge_surjective f
  rw [dualConfig_dEdge] at hf
  have ha : a ∈ cutIdx := by
    by_contra h
    rw [if_neg h] at hf
    exact Bool.false_ne_true hf
  have hends := dEnds_mem_smallFaceSet ha
  have hEq : s(EIdx.dSrc a, EIdx.dTgt a) = s(x, y) := hxy
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hEq
  · rw [← h1, ← h2]; exact hends
  · rw [← h1, ← h2]; exact ⟨hends.2, hends.1⟩

/-- **Every dual-open component is finite.**  A walk that stays on dual-open
edges can only visit the three faces above, plus its own starting vertex. -/
theorem noInfiniteOpenCluster_dual :
    FK.Planar.NoInfiniteOpenCluster dualGraph (dualConfig edgeEquiv ω) := by
  intro x
  have key : ∀ {u v : FVertex},
      OpenConnected dualGraph (dualConfig edgeEquiv ω) Set.univ u v →
      v ∈ smallFaceSet ∨ v = u := by
    intro u v huv
    obtain ⟨p, hp⟩ := huv
    induction p with
    | nil => exact Or.inr rfl
    | @cons a b c hab ptail ih =>
        obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
        have hb : b ∈ smallFaceSet := (dualOpen_ends hopen rfl).2
        rcases ih hrest with hc | hc
        · exact Or.inl hc
        · exact Or.inl (hc ▸ hb)
  refine (smallFaceSet_finite.union (Set.finite_singleton x)).subset ?_
  rintro y hy
  rcases key hy with hy' | rfl
  · exact Or.inl hy'
  · exact Or.inr rfl

/-! ## The primal configuration has two infinite open clusters -/

/-- The side of the separating boundary: `0` on columns `≤ 0`, `1` above. -/
def side : PVertex → ℤ := fun x => if x.1 ≤ 0 then 0 else 1

/-- Along an open edge the side is constant: the only edges joining the two
sides are the three closed horizontals. -/
lemma side_eq_of_open {x y : PVertex} (h : stripGraph.Adj x y)
    (hopen : ω ⟨s(x, y), h⟩ = true) : side x = side y := by
  obtain ⟨a, ha⟩ := EIdx.pEdge_surjective (⟨s(x, y), h⟩ : stripGraph.edgeSet)
  have hopen' : ω (EIdx.pEdge a) = true := by rw [ha]; exact hopen
  rw [omega_pEdge_eq_true_iff] at hopen'
  have hEq : s(EIdx.pSrc a, EIdx.pTgt a) = s(x, y) := congrArg Subtype.val ha
  have hp : side (EIdx.pSrc a) = side (EIdx.pTgt a) := by
    cases a with
    | h0 i =>
        have hi : i ≠ 0 := by
          intro h0
          exact hopen' (by rw [h0]; exact Or.inl rfl)
        have hs : side ((i, (0 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        have ht : side ((i + 1, (0 : Fin 3)) : PVertex) =
            (if i + 1 ≤ 0 then (0 : ℤ) else 1) := rfl
        rw [EIdx.pSrc, EIdx.pTgt, hs, ht]
        split_ifs <;> omega
    | h1 i =>
        have hi : i ≠ 0 := by
          intro h0
          exact hopen' (by rw [h0]; exact Or.inr (Or.inl rfl))
        have hs : side ((i, (1 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        have ht : side ((i + 1, (1 : Fin 3)) : PVertex) =
            (if i + 1 ≤ 0 then (0 : ℤ) else 1) := rfl
        rw [EIdx.pSrc, EIdx.pTgt, hs, ht]
        split_ifs <;> omega
    | h2 i =>
        have hi : i ≠ 0 := by
          intro h0
          exact hopen' (by rw [h0]; exact Or.inr (Or.inr rfl))
        have hs : side ((i, (2 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        have ht : side ((i + 1, (2 : Fin 3)) : PVertex) =
            (if i + 1 ≤ 0 then (0 : ℤ) else 1) := rfl
        rw [EIdx.pSrc, EIdx.pTgt, hs, ht]
        split_ifs <;> omega
    | v0 i =>
        have hs : side ((i, (0 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        have ht : side ((i, (1 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        rw [EIdx.pSrc, EIdx.pTgt, hs, ht]
    | v1 i =>
        have hs : side ((i, (1 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        have ht : side ((i, (2 : Fin 3)) : PVertex) = (if i ≤ 0 then (0 : ℤ) else 1) := rfl
        rw [EIdx.pSrc, EIdx.pTgt, hs, ht]
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hEq
  · rw [← h1, ← h2]; exact hp
  · rw [← h1, ← h2]; exact hp.symm

lemma side_eq_of_openConnected {u v : PVertex}
    (h : OpenConnected stripGraph ω Set.univ u v) : side u = side v := by
  obtain ⟨p, hp⟩ := h
  induction p with
  | nil => rfl
  | @cons a b c hab ptail ih =>
      obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
      exact (side_eq_of_open hab hopen).trans (ih hrest)

/-- Hence the two sides are not openly connected. -/
theorem not_openConnected_zero_one :
    ¬ OpenConnected stripGraph ω Set.univ ((0 : ℤ), (0 : Fin 3)) ((1 : ℤ), (0 : Fin 3)) := by
  intro h
  have hside := side_eq_of_openConnected h
  simp [side] at hside

/-- One horizontal step inside row `0`, using an open indexed edge. -/
lemma openConnected_h0_step (i : ℤ) (hi : i ≠ 0) :
    OpenConnected stripGraph ω Set.univ ((i, (0 : Fin 3)) : PVertex)
      ((i + 1, (0 : Fin 3)) : PVertex) := by
  have hopen : ω (EIdx.pEdge (EIdx.h0 i)) = true := by
    rw [omega_pEdge_eq_true_iff]
    intro hmem
    rcases hmem with h | h | h
    · exact hi (by simpa using h)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  exact OpenConnected.of_adj (G := stripGraph) (ω := ω)
    (EIdx.stripGraph_adj (EIdx.h0 i)) (Set.mem_univ _) hopen

/-- Horizontal open connectivity along row `0`, to the left of the origin. -/
lemma openConnected_left (n : ℕ) :
    OpenConnected stripGraph ω Set.univ (((-(n : ℤ)), (0 : Fin 3)) : PVertex)
      ((0 : ℤ), (0 : Fin 3)) := by
  induction n with
  | zero => exact OpenConnected.refl _ _ _
  | succ n ih =>
      have hcast : ((-((n + 1 : ℕ) : ℤ), (0 : Fin 3)) : PVertex) =
          ((-(n : ℤ) - 1, (0 : Fin 3)) : PVertex) := by
        congr 1
        push_cast
        ring
      rw [hcast]
      have hstep := openConnected_h0_step (-(n : ℤ) - 1) (by omega)
      have hgoal : ((-(n : ℤ) - 1 + 1, (0 : Fin 3)) : PVertex) =
          ((-(n : ℤ), (0 : Fin 3)) : PVertex) := by
        congr 1
        ring
      rw [hgoal] at hstep
      exact hstep.trans ih

/-- Horizontal open connectivity along row `0`, to the right of the origin. -/
lemma openConnected_right (n : ℕ) :
    OpenConnected stripGraph ω Set.univ ((((n : ℤ) + 1), (0 : Fin 3)) : PVertex)
      ((1 : ℤ), (0 : Fin 3)) := by
  induction n with
  | zero => exact OpenConnected.refl _ _ _
  | succ n ih =>
      have hcast : (((((n + 1 : ℕ) : ℤ) + 1), (0 : Fin 3)) : PVertex) =
          ((((n : ℤ) + 1) + 1, (0 : Fin 3)) : PVertex) := by
        push_cast
        ring
      rw [hcast]
      have hstep := openConnected_h0_step ((n : ℤ) + 1) (by omega)
      exact (openConnected_symm hstep).trans ih

lemma infiniteCluster_zero :
    ExteriorInfiniteCluster stripGraph ω Set.univ ((0 : ℤ), (0 : Fin 3)) := by
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => ((-(n : ℤ), (0 : Fin 3)) : PVertex)))
  · rintro y ⟨n, rfl⟩
    exact openConnected_symm (openConnected_left n)
  · apply Set.infinite_range_of_injective
    intro m n h
    simp at h
    omega

lemma infiniteCluster_one :
    ExteriorInfiniteCluster stripGraph ω Set.univ ((1 : ℤ), (0 : Fin 3)) := by
  apply Set.Infinite.mono (s := Set.range (fun n : ℕ => (((n : ℤ) + 1, (0 : Fin 3)) : PVertex)))
  · rintro y ⟨n, rfl⟩
    exact openConnected_symm (openConnected_right n)
  · apply Set.infinite_range_of_injective
    intro m n h
    simp at h
    omega

theorem not_globalAtMostOne : ¬ GlobalAtMostOne stripGraph ω := by
  intro h
  exact not_openConnected_zero_one
    (h ((0 : ℤ), (0 : Fin 3)) ((1 : ℤ), (0 : Fin 3)) infiniteCluster_zero
      infiniteCluster_one)

/-- **The bare plane-cluster target is false.**  The strip and its genuine
planar dual admit a configuration with no infinite dual-open cluster and two
infinite primal-open clusters. -/
theorem not_dualNonpercolationForcesPrimalAtMostOne :
    ¬ FK.Planar.DualNonpercolationForcesPrimalAtMostOne stripGraph dualGraph edgeEquiv := by
  intro h
  exact not_globalAtMostOne (h ω noInfiniteOpenCluster_dual)

/-- The outer face of the strip has infinitely many neighbours in the dual:
this is exactly the local-finiteness hypothesis the source adds in
Theorem 1.11 and which the bare predicate omits. -/
theorem dualGraph_neighbourSet_none_infinite :
    Set.Infinite {f : FVertex | dualGraph.Adj none f} := by
  apply Set.Infinite.mono (s := Set.range (fun i : ℤ => some (i, (0 : Fin 2))))
  · rintro f ⟨i, rfl⟩
    exact ⟨EIdx.h0 i, Or.inl ⟨rfl, rfl⟩⟩
  · apply Set.infinite_range_of_injective
    intro i j hij
    simp at hij
    exact hij

/-! ## The strip lies in the source's graph class

The counterexample is not an artefact of a disconnected or badly infinite graph:
`stripGraph` is connected and locally finite, exactly the standing hypotheses on
`G` in the source.  Only the *dual* local finiteness fails. -/

lemma reachable_vertical (i : ℤ) (k : Fin 3) :
    stripGraph.Reachable ((i, k) : PVertex) ((i, (0 : Fin 3)) : PVertex) := by
  fin_cases k
  · exact SimpleGraph.Reachable.refl _
  · exact (EIdx.stripGraph_adj (EIdx.v0 i)).reachable.symm
  · exact ((EIdx.stripGraph_adj (EIdx.v1 i)).reachable.symm).trans
      (EIdx.stripGraph_adj (EIdx.v0 i)).reachable.symm

lemma reachable_horizontal (m : ℤ) :
    ∀ d : ℕ, stripGraph.Reachable ((m, (0 : Fin 3)) : PVertex)
      (((m + d), (0 : Fin 3)) : PVertex) := by
  intro d
  induction d with
  | zero => simpa using SimpleGraph.Reachable.refl (G := stripGraph) ((m, (0 : Fin 3)) : PVertex)
  | succ d ih =>
      have hstep : stripGraph.Reachable (((m + d), (0 : Fin 3)) : PVertex)
          (((m + d) + 1, (0 : Fin 3)) : PVertex) :=
        (EIdx.stripGraph_adj (EIdx.h0 (m + d))).reachable
      have hgoal : (((m + (d + 1 : ℕ)), (0 : Fin 3)) : PVertex) =
          (((m + d) + 1, (0 : Fin 3)) : PVertex) := by
        congr 1
        push_cast
        ring
      rw [hgoal]
      exact ih.trans hstep

/-- The strip is connected. -/
theorem stripGraph_connected : stripGraph.Connected := by
  apply stripGraph.connected_iff_exists_forall_reachable.2
  refine ⟨((0 : ℤ), (0 : Fin 3)), ?_⟩
  rintro ⟨i, k⟩
  have hv := reachable_vertical i k
  rcases lt_or_ge i 0 with hi | hi
  · have hd : i + ((-i).toNat : ℤ) = 0 := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hh := reachable_horizontal i (-i).toNat
    rw [hd] at hh
    exact (hv.trans hh).symm
  · have hd : (0 : ℤ) + (i.toNat : ℤ) = i := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    have hh := reachable_horizontal 0 i.toNat
    rw [hd] at hh
    exact (hv.trans hh.symm).symm

/-- Every vertex of the strip has at most five neighbours: at most one step in
each horizontal direction and at most three rung endpoints. -/
theorem stripGraph_neighbourSet_finite (v : PVertex) :
    {w : PVertex | stripGraph.Adj v w}.Finite := by
  have hsub : {w : PVertex | stripGraph.Adj v w} ⊆
      ({((v.1 - 1, v.2) : PVertex), ((v.1 + 1, v.2) : PVertex),
        ((v.1, (0 : Fin 3)) : PVertex), ((v.1, (1 : Fin 3)) : PVertex),
        ((v.1, (2 : Fin 3)) : PVertex)} : Set PVertex) := by
    rintro w ⟨a, h | h⟩
    · cases a with
      | h0 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | h1 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | h2 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | v0 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | v1 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
    · cases a with
      | h0 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | h1 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | h2 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | v0 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
      | v1 j => rw [h.1, h.2]; simp [EIdx.pSrc, EIdx.pTgt]
  exact (Set.toFinite _).subset hsub

/-! ## The predicate also fails with a locally finite self-pairing

Adding local finiteness to the dual does not repair the bare predicate either:
the strip is locally finite and connected, so the identity edge bijection
`stripGraph.edgeSet ≃ stripGraph.edgeSet` is an allowed "duality".  Under it
dual openness is *primal closedness*, and the three closed edges span only
finitely many vertices. -/

/-- The six vertices touched by the three separating edges. -/
def smallVertexSet : Set PVertex :=
  {((0 : ℤ), (0 : Fin 3)), ((1 : ℤ), (0 : Fin 3)), ((0 : ℤ), (1 : Fin 3)),
   ((1 : ℤ), (1 : Fin 3)), ((0 : ℤ), (2 : Fin 3)), ((1 : ℤ), (2 : Fin 3))}

lemma smallVertexSet_finite : smallVertexSet.Finite := by
  simp [smallVertexSet]

lemma closedSet_finite : closedSet.Finite := by
  have hcut : cutIdx.Finite := by
    rw [show cutIdx = ({EIdx.h0 0, EIdx.h1 0, EIdx.h2 0} : Set EIdx) by
      ext a; simp [cutIdx]]
    exact (Set.toFinite _)
  exact hcut.image EIdx.pEdge

lemma omega_eq_false_iff {e : stripGraph.edgeSet} : ω e = false ↔ e ∈ closedSet := by
  simp only [ω]
  by_cases he : e ∈ closedSet <;> simp [he]

/-- Every vertex incident to a closed edge lies in the six-element set above. -/
lemma mem_smallVertexSet_of_closed {a : EIdx} (ha : a ∈ cutIdx) :
    EIdx.pSrc a ∈ smallVertexSet ∧ EIdx.pTgt a ∈ smallVertexSet := by
  rcases ha with rfl | rfl | rfl <;>
    simp [EIdx.pSrc, EIdx.pTgt, smallVertexSet]

/-- **Dual nonpercolation for the self-pairing.**  With the identity edge
bijection on the locally finite connected strip, dual openness is primal
closedness, and a walk on closed edges stays inside the six vertices above. -/
theorem noInfiniteOpenCluster_self :
    FK.Planar.NoInfiniteOpenCluster stripGraph
      (dualConfig (Equiv.refl stripGraph.edgeSet) ω) := by
  intro x
  have key : ∀ {u v : PVertex},
      OpenConnected stripGraph (dualConfig (Equiv.refl stripGraph.edgeSet) ω) Set.univ u v →
      v ∈ smallVertexSet ∨ v = u := by
    intro u v huv
    obtain ⟨p, hp⟩ := huv
    induction p with
    | nil => exact Or.inr rfl
    | @cons a b c hab ptail ih =>
        obtain ⟨⟨-, hopen⟩, hrest⟩ := isOpenIn_cons.mp hp
        have hclosed : ω (⟨s(a, b), hab⟩ : stripGraph.edgeSet) = false := by
          simpa [dualConfig] using hopen
        obtain ⟨a', ha', he'⟩ :=
          (omega_eq_false_iff.mp hclosed : (⟨s(a, b), hab⟩ : stripGraph.edgeSet) ∈ closedSet)
        have hcarrier : s(a, b) = s(EIdx.pSrc a', EIdx.pTgt a') :=
          (congrArg Subtype.val he').symm
        have hends := mem_smallVertexSet_of_closed ha'
        have hb : b ∈ smallVertexSet := by
          obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hcarrier
          · rw [h2]; exact hends.2
          · rw [h2]; exact hends.1
        rcases ih hrest with hc | hc
        · exact Or.inl hc
        · exact Or.inl (hc ▸ hb)
  refine (smallVertexSet_finite.union (Set.finite_singleton x)).subset ?_
  rintro y hy
  rcases key hy with hy' | rfl
  · exact Or.inl hy'
  · exact Or.inr rfl

/-- **No combinatorial repair.**  The locally finite connected strip paired
with itself by the identity edge bijection already violates the bare target. -/
theorem not_dualNonpercolationForcesPrimalAtMostOne_self :
    ¬ FK.Planar.DualNonpercolationForcesPrimalAtMostOne stripGraph stripGraph
      (Equiv.refl stripGraph.edgeSet) := by
  intro h
  exact not_globalAtMostOne (h ω noInfiniteOpenCluster_self)

end FK.PlaneTopology.StripDual

#print axioms FK.PlaneTopology.StripDual.EIdx.pEdge_surjective
#print axioms FK.PlaneTopology.StripDual.EIdx.dEdge_surjective
#print axioms FK.PlaneTopology.StripDual.noInfiniteOpenCluster_dual
#print axioms FK.PlaneTopology.StripDual.infiniteCluster_zero
#print axioms FK.PlaneTopology.StripDual.infiniteCluster_one
#print axioms FK.PlaneTopology.StripDual.not_globalAtMostOne
#print axioms FK.PlaneTopology.StripDual.not_dualNonpercolationForcesPrimalAtMostOne
#print axioms FK.PlaneTopology.StripDual.dualGraph_neighbourSet_none_infinite
#print axioms FK.PlaneTopology.StripDual.stripGraph_connected
#print axioms FK.PlaneTopology.StripDual.stripGraph_neighbourSet_finite
#print axioms FK.PlaneTopology.StripDual.noInfiniteOpenCluster_self
#print axioms FK.PlaneTopology.StripDual.not_dualNonpercolationForcesPrimalAtMostOne_self
