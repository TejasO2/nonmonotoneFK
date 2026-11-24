import FK.AGTree.Main

/-!
# Open percolation on the two-class tree

The existing branching development (`FK/AGTree/`) works with the *forward* cluster
`Cluster ω u` (the open child chains of `u` reach every depth).  This file shows that this
is a genuine percolation notion on the graph `G`:

* `OAdj`/`OReach` are the edge-open subgraph and its connectivity relation,
* `oReach_iff_exists_downOpen`: two vertices are open-connected iff they have a common
  open ancestor, which is the tree shape of an open path;
* `cluster_infinite`: a forward cluster is an infinite open cluster;
* `exists_cluster_ancestor`: every infinite open cluster contains an ancestor with an
  infinite forward cluster, so forward clusters exhaust infinite clusters;
* `cluster_iff_infinite_root`: at the root the two notions coincide.

No measure theory is used here; this is the geometric interface for
`TreeBaseNonpercolation`.
-/

namespace Ultra
open V MeasureTheory ProbabilityTheory

/-! ### The open subgraph -/

/-- The edge of `G` carried by an adjacency. -/
def eOf {v w : V} (h : G.Adj v w) : G.edgeSet := ⟨s(v, w), (SimpleGraph.mem_edgeSet G).2 h⟩

lemma eOf_symm {v w : V} (h : G.Adj v w) : eOf h.symm = eOf h := Subtype.ext Sym2.eq_swap

lemma eOf_adj_snoc {v : V} {a : A} (h : v.Valid a) :
    eOf (adj_snoc h) = childE (⟨(v, a), h⟩ : Echild) := Subtype.ext rfl

lemma eOf_eq_childE_left {a c : V} (hG : G.Adj a c) {b : A} (hv : a.Valid b)
    (hcw : c = a.snoc b hv) : eOf hG = childE (⟨(a, b), hv⟩ : Echild) :=
  Subtype.ext (by
    show s(a, c) = s(a, a.snoc b hv)
    rw [hcw])

lemma eOf_eq_childE_right {a c : V} (hG : G.Adj a c) {b : A} (hv : c.Valid b)
    (hav : a = c.snoc b hv) : eOf hG = childE (⟨(c, b), hv⟩ : Echild) :=
  Subtype.ext (by
    show s(a, c) = s(c, c.snoc b hv)
    rw [hav, Sym2.eq_swap])

/-- The two shapes of an adjacency, oriented by the parent relation. -/
lemma adj_iff' {v w : V} :
    G.Adj v w ↔ (∃ (a : A) (h : v.Valid a), w = v.snoc a h) ∨
      (∃ (a : A) (h : w.Valid a), v = w.snoc a h) := by
  rw [adj_iff]
  constructor
  · rintro (h | ⟨hne, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨v.w.getLast hne, ?_, ?_⟩
      · exact valid_of_append (by rw [V.parent_w, List.dropLast_append_getLast hne]; exact v.red)
      · apply V.ext
        rw [V.snoc_w, V.parent_w, List.dropLast_append_getLast]
  · rintro (h | ⟨b, hv, rfl⟩)
    · exact Or.inl h
    · have hne : (w.snoc b hv).w ≠ [] := by simp
      refine Or.inr ⟨hne, ?_⟩
      apply V.ext
      rw [V.parent_w, V.snoc_w, List.dropLast_concat]

/-- `v` and `w` are adjacent in the subgraph of open edges. -/
def OAdj (ω : G.edgeSet → Bool) (v w : V) : Prop := ∃ h : G.Adj v w, ω (eOf h) = true

instance oAdjInstSymm (ω : G.edgeSet → Bool) : Std.Symm (OAdj ω) :=
  ⟨fun v w h => by
    obtain ⟨hh, ho⟩ := h
    exact ⟨hh.symm, by rw [eOf_symm]; exact ho⟩⟩

/-- Open connectivity. -/
abbrev OReach (ω : G.edgeSet → Bool) (u v : V) : Prop := Relation.ReflTransGen (OAdj ω) u v

lemma oReach_refl (ω : G.edgeSet → Bool) (u : V) : OReach ω u u :=
  Relation.ReflTransGen.refl

lemma oReach_trans {ω : G.edgeSet → Bool} {u v z : V} (h1 : OReach ω u v) (h2 : OReach ω v z) :
    OReach ω u z := Relation.ReflTransGen.trans h1 h2

lemma oReach_symm {ω : G.edgeSet → Bool} {u v : V} (h : OReach ω u v) : OReach ω v u :=
  Std.Symm.symm _ _ h

lemma oReach_single {ω : G.edgeSet → Bool} {u v : V} (h : OAdj ω u v) : OReach ω u v :=
  Relation.ReflTransGen.single h

/-- The open cluster of `u`: the set of vertices reachable from `u` through open edges. -/
def clusterSet (ω : G.edgeSet → Bool) (u : V) : Set V := {v | OReach ω u v}

/-- `u` lies in an infinite open cluster. -/
def InfiniteClusterAt (ω : G.edgeSet → Bool) (u : V) : Prop := (clusterSet ω u).Infinite

/-- `u` lies in no infinite open cluster. -/
def FiniteClusterAt (ω : G.edgeSet → Bool) (u : V) : Prop := (clusterSet ω u).Finite

/-! ### Open descents -/

/-- The descent from `m` along the list `l` is open and ends at `u`. -/
def DownOpen (ω : G.edgeSet → Bool) (m u : V) : Prop :=
  ∃ l : List A, u.w = m.w ++ l ∧ ChainOpen ω m l

lemma downOpen_refl (ω : G.edgeSet → Bool) (u : V) : DownOpen ω u u :=
  ⟨[], (List.append_nil _).symm, trivial⟩

lemma Pref_of_downOpen {ω : G.edgeSet → Bool} {m u : V} (h : DownOpen ω m u) :
    Pref m.w u.w := by
  obtain ⟨l, hl, _⟩ := h
  exact ⟨l, hl⟩

lemma length_le_of_downOpen {ω : G.edgeSet → Bool} {m u : V} (h : DownOpen ω m u) :
    m.w.length ≤ u.w.length := by
  obtain ⟨l, hl, _⟩ := h
  rw [hl, List.length_append]
  exact Nat.le_add_right _ _

lemma eq_of_downOpen_of_le {ω : G.edgeSet → Bool} {m u : V} (h : DownOpen ω m u)
    (hle : u.w.length ≤ m.w.length) : m = u := by
  obtain ⟨l, hl, _⟩ := h
  have hlen : l.length = 0 := by
    have h2 := congrArg List.length hl
    rw [List.length_append] at h2
    omega
  have hl0 : l = [] := List.eq_nil_of_length_eq_zero hlen
  rw [hl0, List.append_nil] at hl
  exact V.ext hl.symm

lemma chainOpen_reduced {ω : G.edgeSet → Bool} :
    ∀ (l : List A) (u : V), ChainOpen ω u l → Reduced (u.w ++ l) := by
  intro l
  induction l with
  | nil => intro u _; simpa using u.red
  | cons a rest ih =>
    intro u hc
    obtain ⟨hv, _, hrest⟩ := hc
    have h2 : Reduced ((u.snoc a hv).w ++ rest) := ih (u.snoc a hv) hrest
    rw [V.snoc_w, List.append_assoc] at h2
    simpa using h2

lemma chainOpen_oReach {ω : G.edgeSet → Bool} :
    ∀ (l : List A) (m u : V), u.w = m.w ++ l → ChainOpen ω m l → OReach ω m u := by
  intro l
  induction l with
  | nil =>
    intro m u hu _
    have hmu : m = u := V.ext (by rw [hu, List.append_nil])
    rw [hmu]
  | cons a rest ih =>
    intro m u hu hc
    obtain ⟨hv, hω, hrest⟩ := hc
    have hadj : OAdj ω m (m.snoc a hv) := ⟨adj_snoc hv, by rw [eOf_adj_snoc]; exact hω⟩
    have hrest' : OReach ω (m.snoc a hv) u := by
      refine ih (m.snoc a hv) u ?_ hrest
      rw [hu, V.snoc_w]
      simp
    exact oReach_trans (oReach_single hadj) hrest'

lemma downOpen_oReach {ω : G.edgeSet → Bool} {m u : V} (h : DownOpen ω m u) : OReach ω m u := by
  obtain ⟨l, hl, hc⟩ := h
  exact chainOpen_oReach l m u hl hc

lemma chainOpen_Pref {ω : G.edgeSet → Bool} {m : V} {l' l : List A} (h : Pref l' l)
    (hc : ChainOpen ω m l) : ChainOpen ω m l' := by
  obtain ⟨t, ht⟩ := h
  have h2 : ChainOpen ω m (l.take l'.length) := chainOpen_take l hc l'.length
  rwa [ht, List.take_left] at h2

/-- Prepending one open letter to a descent. -/
lemma chainOpen_cons {ω : G.edgeSet → Bool} {a c : V} {b : A} (hval : a.Valid b)
    (hopen : ω (childE (⟨(a, b), hval⟩ : Echild)) = true) {l : List A}
    (hca : c = a.snoc b hval) (hc : ChainOpen ω c l) : ChainOpen ω a (b :: l) := by
  subst hca
  exact ⟨hval, hopen, hc⟩

/-- Appending one open letter to a descent. -/
lemma chainOpen_snoc {ω : G.edgeSet → Bool} :
    ∀ (l : List A) (m : V) (c : V) (b : A) (hv : c.Valid b), ChainOpen ω m l →
      c.w = m.w ++ l → ω (childE (⟨(c, b), hv⟩ : Echild)) = true → ChainOpen ω m (l ++ [b]) := by
  intro l
  induction l with
  | nil =>
    intro m c b hv _ hw he
    have hmc : m = c := V.ext (by rw [hw, List.append_nil])
    subst hmc
    exact ⟨hv, he, trivial⟩
  | cons a rest ih =>
    intro m c b hv hc hw he
    obtain ⟨hv', hω, hrest⟩ := hc
    refine ⟨hv', hω, ?_⟩
    exact ih (m.snoc a hv') c b hv hrest (by rw [hw, V.snoc_w, List.append_assoc]; simp) he

/-! ### The common-open-ancestor characterisation -/

/-- If `c` is a child of `a` (by the open edge `(a,b)`), a common open ancestor of `c` and
`x` can be replaced by a common open ancestor of `a` and `x`. -/
lemma exists_downOpen_of_child {ω : G.edgeSet → Bool} {a c x : V} {b : A} (hval : a.Valid b)
    (hopen : ω (childE (⟨(a, b), hval⟩ : Echild)) = true) (hca : c = a.snoc b hval)
    (h : ∃ m, DownOpen ω m c ∧ DownOpen ω m x) : ∃ m, DownOpen ω m a ∧ DownOpen ω m x := by
  classical
  obtain ⟨m, hmc, hmx⟩ := h
  obtain ⟨l, hl, hcl⟩ := hmc
  have hcw : c.w = a.w ++ [b] := by rw [hca, V.snoc_w]
  have heq : m.w ++ l = a.w ++ [b] := by rw [← hl, hcw]
  by_cases hle : m.w.length ≤ a.w.length
  · have htake : m.w = a.w.take m.w.length := by
      calc m.w = (m.w ++ l).take m.w.length := (List.take_left (l₁ := m.w) (l₂ := l)).symm
        _ = (a.w ++ [b]).take m.w.length := by rw [heq]
        _ = (a.w.take m.w.length) ++ ([b]).take (m.w.length - a.w.length) := List.take_append
        _ = a.w.take m.w.length := by
              rw [Nat.sub_eq_zero_of_le hle, List.take_zero, List.append_nil]
    set d : List A := a.w.drop m.w.length with hd
    have hsplit : a.w = m.w ++ d := by
      rw [hd]
      calc a.w = a.w.take m.w.length ++ a.w.drop m.w.length := (List.take_append_drop _ _).symm
        _ = m.w ++ a.w.drop m.w.length := by rw [← htake]
    have hdrop : l = d ++ [b] := by
      have h2 : m.w ++ l = m.w ++ (d ++ [b]) := by
        rw [heq, hsplit, List.append_assoc]
      exact List.append_cancel_left h2
    refine ⟨m, ⟨d, hsplit, ?_⟩, hmx⟩
    exact chainOpen_Pref ⟨[b], hdrop⟩ hcl
  · have hlen : m.w.length ≤ c.w.length := by
      rw [hl, List.length_append]
      exact Nat.le_add_right _ _
    have h1 : m.w.length = c.w.length := by
      have hg : c.w.length = a.w.length + 1 := by rw [hcw]; simp
      omega
    have hmcw : m.w = c.w := by
      have h2 : m.w = (m.w ++ l).take m.w.length := (List.take_left (l₁ := m.w) (l₂ := l)).symm
      rw [heq] at h2
      rw [h1] at h2
      rw [← hcw] at h2
      rw [h2, List.take_of_length_le (le_refl _)]
    have hmc_eq : m = c := V.ext hmcw
    have hl0 : l = [] := by
      rw [hmcw] at hl
      have hlen : l.length = 0 := by
        have h3 := congrArg List.length hl
        rw [List.length_append] at h3
        omega
      exact List.eq_nil_of_length_eq_zero hlen
    obtain ⟨l₂, hx2, hcl₂⟩ := hmx
    subst hmc_eq
    subst hl0
    refine ⟨a, downOpen_refl ω a, b :: l₂, ?_, ?_⟩
    · rw [hx2, hca, V.snoc_w, List.append_assoc]
      simp
    · exact chainOpen_cons hval hopen hca hcl₂

/-- If `a` is a child of `c`, a common open ancestor of `c` and `x` can be pushed down to
`a`. -/
lemma exists_downOpen_of_parent {ω : G.edgeSet → Bool} {a c x : V} {b : A}
    (hval : c.Valid b) (hopen : ω (childE (⟨(c, b), hval⟩ : Echild)) = true)
    (hca : a = c.snoc b hval) (h : ∃ m, DownOpen ω m c ∧ DownOpen ω m x) :
    ∃ m, DownOpen ω m a ∧ DownOpen ω m x := by
  obtain ⟨m, hmc, hmx⟩ := h
  obtain ⟨l, hl, hcl⟩ := hmc
  refine ⟨m, ⟨l ++ [b], ?_, chainOpen_snoc l m c b hval hcl hl hopen⟩, hmx⟩
  rw [hca, V.snoc_w, hl, List.append_assoc]

/-- **Shape of an open path in the tree.**  Two vertices are open-connected iff they have a
common vertex from which both are reached by open descents. -/
theorem oReach_iff_exists_downOpen (ω : G.edgeSet → Bool) (u x : V) :
    OReach ω u x ↔ ∃ m : V, DownOpen ω m u ∧ DownOpen ω m x := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨x, downOpen_refl ω x, downOpen_refl ω x⟩
    | @head a c hadj hrest ih =>
      obtain ⟨hG, hω⟩ := hadj
      rcases (adj_iff' (v := a) (w := c)).1 hG with ⟨b, hv, hcw⟩ | ⟨b, hv, hav⟩
      · refine exists_downOpen_of_child hv ?_ hcw ih
        rw [eOf_eq_childE_left hG hv hcw] at hω
        exact hω
      · refine exists_downOpen_of_parent hv ?_ hav ih
        rw [eOf_eq_childE_right hG hv hav] at hω
        exact hω
  · rintro ⟨m, h1, h2⟩
    exact oReach_trans (oReach_symm (downOpen_oReach h1)) (downOpen_oReach h2)

/-! ### Forward clusters and infinite open clusters -/

lemma Fwd.mono {ω : G.edgeSet → Bool} {u : V} {n m : ℕ} (hle : n ≤ m) (hf : Fwd ω u m) :
    Fwd ω u n := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  clear hle
  induction d with
  | zero => simpa using hf
  | succ d ih => exact ih (fwd_anti hf)

lemma downOpen_fwd {ω : G.edgeSet → Bool} {m u : V} (h : DownOpen ω m u) :
    Fwd ω m (u.w.length - m.w.length) := by
  obtain ⟨l, hl, hc⟩ := h
  refine ⟨l, ?_, hc⟩
  rw [hl, List.length_append]
  omega

/-- An open descent reaches an actual vertex, so a forward cluster consists of open-connected
vertices. -/
lemma fwd_vertex {ω : G.edgeSet → Bool} {u : V} {n : ℕ} (h : Fwd ω u n) :
    ∃ x : V, OReach ω u x ∧ x.w.length = u.w.length + n := by
  obtain ⟨l, hlen, hc⟩ := h
  refine ⟨⟨u.w ++ l, chainOpen_reduced l u hc⟩, chainOpen_oReach l u ⟨u.w ++ l, chainOpen_reduced l u hc⟩ rfl hc, ?_⟩
  simp [hlen]

/-- A forward cluster is an infinite open cluster. -/
theorem cluster_infinite {ω : G.edgeSet → Bool} {u : V} (h : Cluster ω u) :
    InfiniteClusterAt ω u := by
  classical
  choose v hv using fun n : ℕ => fwd_vertex (h n)
  have hinj : Function.Injective v := by
    intro n m hnm
    have h1 := (hv n).2
    have h2 := (hv m).2
    rw [hnm] at h1
    omega
  have hinf : (Set.range v).Infinite := Set.infinite_range_of_injective hinj
  exact hinf.mono (fun x hx => by obtain ⟨n, rfl⟩ := hx; exact (hv n).1)

/-- Lists of length below `N` over a finite alphabet form a finite set. -/
lemma finite_lists_lt (N : ℕ) : {l : List A | l.length < N}.Finite := by
  have hlen : ∀ k : ℕ, {l : List A | l.length = k}.Finite := by
    intro k
    induction k with
    | zero =>
      have hset : {l : List A | l.length = 0} = {[]} := by
        ext l
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun h => List.eq_nil_of_length_eq_zero h, fun h => by rw [h]; rfl⟩
      rw [hset]
      exact Set.finite_singleton []
    | succ k ih =>
      have hsub : {l : List A | l.length = k + 1} ⊆
          ⋃ a : A, (fun m : List A => a :: m) '' {l : List A | l.length = k} := by
        intro l hl
        cases l with
        | nil => simp at hl
        | cons a rest =>
          refine Set.mem_iUnion.2 ⟨a, ?_⟩
          refine Set.mem_image_of_mem _ ?_
          simp only [Set.mem_setOf_eq, List.length_cons] at hl ⊢
          omega
      exact Set.Finite.subset (Set.finite_iUnion (fun a => ih.image _)) hsub
  have hset : {l : List A | l.length < N} =
      ⋃ k ∈ Finset.range N, {l : List A | l.length = k} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact ⟨fun h => ⟨l.length, h, rfl⟩, fun ⟨k, hk, h⟩ => h ▸ hk⟩
  rw [hset]
  exact Set.Finite.biUnion (Finset.range N).finite_toSet (fun k _ => hlen k)

/-- Vertices at a bounded depth form a finite set. -/
lemma finite_levels (N : ℕ) : {v : V | v.w.length < N}.Finite := by
  refine Set.Finite.of_injOn (f := fun v : V => v.w) (t := {l : List A | l.length < N})
    (fun v hv => hv) (fun v _ w _ h => V.ext h) (finite_lists_lt N)

/-- **Every infinite open cluster contains an ancestor with an infinite forward cluster.** -/
theorem exists_cluster_ancestor {ω : G.edgeSet → Bool} {u : V}
    (h : InfiniteClusterAt ω u) : ∃ t : V, Pref t.w u.w ∧ Cluster ω t := by
  classical
  have hex : ∃ k : ℕ, ∃ v : V, v ∈ clusterSet ω u ∧ v.w.length = k :=
    ⟨u.w.length, u, oReach_refl ω u, rfl⟩
  obtain ⟨t, htC, htk⟩ : ∃ t : V, t ∈ clusterSet ω u ∧ t.w.length = Nat.find hex :=
    Nat.find_spec hex
  have hmin : ∀ v : V, v ∈ clusterSet ω u → Nat.find hex ≤ v.w.length := by
    intro v hv
    by_contra hlt
    push_neg at hlt
    exact Nat.find_min hex hlt ⟨v, hv, rfl⟩
  have key : ∀ x : V, x ∈ clusterSet ω u → DownOpen ω t x := by
    intro x hx
    obtain ⟨m, hmt, hmx⟩ :=
      (oReach_iff_exists_downOpen ω t x).1 (oReach_trans (oReach_symm htC) hx)
    have hmC : m ∈ clusterSet ω u := oReach_trans htC (oReach_symm (downOpen_oReach hmt))
    have hle : t.w.length ≤ m.w.length := by rw [htk]; exact hmin m hmC
    have hmeq : m = t := eq_of_downOpen_of_le (ω := ω) (m := m) (u := t) hmt hle
    rwa [hmeq] at hmx
  have hunb : ∀ n : ℕ, ∃ x : V, x ∈ clusterSet ω u ∧ Nat.find hex + n ≤ x.w.length := by
    intro n
    by_contra hcon
    push_neg at hcon
    refine h (Set.Finite.subset (finite_levels (Nat.find hex + n + 1)) ?_)
    intro x hx
    have := hcon x hx
    simp only [Set.mem_setOf_eq]
    omega
  refine ⟨t, Pref_of_downOpen (key u (oReach_refl ω u)), fun n => ?_⟩
  obtain ⟨x, hxC, hxk⟩ := hunb n
  have hfwd : Fwd ω t (x.w.length - t.w.length) := downOpen_fwd (key x hxC)
  refine Fwd.mono ?_ hfwd
  rw [htk]
  omega

/-- Infinite open clusters are exactly the infinite forward clusters. -/
theorem infinite_iff_exists_cluster (ω : G.edgeSet → Bool) :
    (∃ u : V, InfiniteClusterAt ω u) ↔ (∃ m : V, Cluster ω m) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨t, _, ht⟩ := exists_cluster_ancestor hu
    exact ⟨t, ht⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, cluster_infinite hm⟩

/-- At the root, forward percolation and infinite open percolation coincide. -/
theorem cluster_iff_infinite_root (ω : G.edgeSet → Bool) :
    Cluster ω V.root ↔ InfiniteClusterAt ω V.root := by
  constructor
  · exact cluster_infinite
  · intro h
    obtain ⟨t, hpref, ht⟩ := exists_cluster_ancestor h
    have hw : t.w = [] := by
      obtain ⟨s, hs⟩ := hpref
      exact (List.append_eq_nil_iff.1 hs.symm).1
    have htroot : t = V.root := by
      apply V.ext
      rw [V.root, hw]
    rwa [htroot] at ht

end Ultra
