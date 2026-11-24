/-
First-moment (branching) bound for Bernoulli bond percolation:
on a graph of bounded degree `d`, `θ(p) = 0` whenever `d * p < 1`.
Hence `p_c (G) ≥ 1/d > 0`, the non-degeneracy assertion of Remark 1.5 of
arXiv:2512.16486v1 ("this is the case for all graphs of bounded degree (this
can easily be seen by comparison with a Galton–Watson process)").
-/
import FK.SubcriticalPercolation

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

namespace CurvatureVariance.Infra.Percolation

variable {ι : Type*} {V : Type*}

/-! ### Finite cylinder probabilities -/

theorem measurableSet_forall_coord (s : Finset ι) :
    MeasurableSet {ω : ι → Bool | ∀ i ∈ s, ω i = true} := by
  have h : {ω : ι → Bool | ∀ i ∈ s, ω i = true} = ⋂ i ∈ s, {ω : ι → Bool | ω i = true} := by
    ext ω; simp
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
    (measurable_pi_apply (X := fun _ : ι => Bool) i) (measurableSet_singleton true)

variable (ι) in
/-- The probability that every coordinate in a finite set is `true`. -/
theorem bernoulliProduct_cylinder (p : I) (F : Finset ι) :
    bernoulliProduct ι p {ω : ι → Bool | ∀ i ∈ F, ω i = true} =
      (ENNReal.ofReal (p : ℝ)) ^ F.card := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have h : {ω : ι → Bool | ∀ i ∈ (∅ : Finset ι), ω i = true} = Set.univ := by
      ext ω; simp
    rw [h, measure_univ, Finset.card_empty, pow_zero]
  | insert a s ha ih =>
    have hset : {ω : ι → Bool | ∀ i ∈ insert a s, ω i = true} =
        {ω : ι → Bool | ω a = true} ∩ {ω : ι → Bool | ∀ i ∈ s, ω i = true} := by
      ext ω; simp
    have hBD : DependsOn (fun x : ι → Bool => ∀ i ∈ s, x i = true) (s : Set ι) := by
      intro x y hxy
      apply propext
      exact ⟨fun h i hi => by rw [← hxy i hi]; exact h i hi,
        fun h i hi => by rw [hxy i hi]; exact h i hi⟩
    have hmain := measure_inter_eq_mul_of_dependsOn (p := p)
      ((measurable_pi_apply (X := fun _ : ι => Bool) a) (measurableSet_singleton true))
      (measurableSet_forall_coord s) (dependsOn_coord a true) hBD (by
        simp only [Set.disjoint_left, Set.mem_singleton_iff]
        rintro i rfl hi
        exact ha hi)
    simp only [Set.preimage, Set.mem_singleton_iff] at hmain
    rw [hset, hmain, bernoulliProduct_coord_true p a, ih, Finset.card_insert_of_notMem ha,
      pow_succ']

/-! ### Counting walks by their vertex lists -/

section WalkLists

variable {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite]

open Classical in
/-- The finite set of vertex lists of length `n + 1` starting at `o` whose consecutive
vertices are adjacent: the `n`-step walks out of `o`, recorded by vertex sequence. -/
noncomputable def walkLists (G : SimpleGraph V) [G.LocallyFinite] (o : V) : ℕ → Finset (List V)
  | 0 => {[o]}
  | n + 1 =>
      (walkLists G o n).biUnion fun l =>
        ((G.neighborSet (l.getLastD o)).toFinite.toFinset.filter fun y => y ∉ l).image fun y =>
          l ++ [y]

variable {o x : V} {l : List V} {n : ℕ}

theorem mem_walkLists_zero_iff : l ∈ walkLists G o 0 ↔ l = [o] := by
  simp [walkLists]

theorem mem_walkLists_succ_iff {m : ℕ} :
    l ∈ walkLists G o (m + 1) ↔
      ∃ l' ∈ walkLists G o m, ∃ y ∈ G.neighborSet (l'.getLastD o), y ∉ l' ∧ l = l' ++ [y] := by
  classical
  simp only [walkLists, Finset.mem_biUnion, Finset.mem_image, Set.Finite.mem_toFinset,
    Finset.mem_filter]
  constructor
  · rintro ⟨l', hl', y, ⟨hy, hyl⟩, rfl⟩
    exact ⟨l', hl', y, hy, hyl, rfl⟩
  · rintro ⟨l', hl', y, hy, hyl, rfl⟩
    exact ⟨l', hl', y, ⟨hy, hyl⟩, rfl⟩

end WalkLists

section Counting

variable {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite] {o : V} {d : ℕ}

theorem ncard_neighborSet_le (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) (v : V) :
    ((G.neighborSet v).toFinite.toFinset).card ≤ d := by
  simpa [Set.ncard_eq_toFinset_card] using hdeg v

theorem card_walkLists_le (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) :
    ∀ n : ℕ, (walkLists G o n).card ≤ d ^ n
  | 0 => by simp [walkLists]
  | n + 1 => by
    classical
    have hstep : (walkLists G o (n + 1)).card ≤
        ∑ l ∈ walkLists G o n,
          (((G.neighborSet (l.getLastD o)).toFinite.toFinset.filter fun y => y ∉ l).image
            fun y => l ++ [y]).card := by
      rw [show walkLists G o (n + 1) = (walkLists G o n).biUnion (fun l =>
          ((G.neighborSet (l.getLastD o)).toFinite.toFinset.filter fun y => y ∉ l).image
            fun y => l ++ [y]) from rfl]
      exact Finset.card_biUnion_le
    have hsum : ∑ l ∈ walkLists G o n,
          (((G.neighborSet (l.getLastD o)).toFinite.toFinset.filter fun y => y ∉ l).image
            fun y => l ++ [y]).card ≤ (walkLists G o n).card * d := by
      have hterm : ∀ l ∈ walkLists G o n,
          (((G.neighborSet (l.getLastD o)).toFinite.toFinset.filter fun y => y ∉ l).image
            fun y => l ++ [y]).card ≤ d := by
        intro l _
        refine le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _) ?_)
        exact ncard_neighborSet_le hdeg _
      calc ∑ l ∈ walkLists G o n,
            (((G.neighborSet (l.getLastD o)).toFinite.toFinset.filter fun y => y ∉ l).image
              fun y => l ++ [y]).card
          ≤ ∑ _l ∈ walkLists G o n, d := Finset.sum_le_sum hterm
        _ = (walkLists G o n).card * d := by simp
    calc (walkLists G o (n + 1)).card ≤ (walkLists G o n).card * d := le_trans hstep hsum
      _ ≤ d ^ n * d := Nat.mul_le_mul_right d (card_walkLists_le hdeg n)
      _ = d ^ (n + 1) := (Nat.pow_succ d n).symm

/-- A vertex list of length `n + 1` that starts at `o` and has adjacent consecutive
vertices is one of the recorded `n`-step walks out of `o`. -/
theorem mem_walkLists_of_head_chain (o : V) :
    ∀ (n : ℕ) {l : List V}, l.head? = some o → l.IsChain G.Adj → l.Nodup →
      l.length = n + 1 → l ∈ walkLists G o n := by
  intro n
  induction n with
  | zero =>
    intro l hhead hchain hnd hlen
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    simp [mem_walkLists_zero_iff]
  | succ n ih =>
    intro l hhead hchain hnd hlen
    have hne : l ≠ [] := by rintro rfl; simp at hlen
    have hsplit : l = l.dropLast ++ [l.getLast hne] := (List.dropLast_append_getLast hne).symm
    have hne' : l.dropLast ≠ [] := by
      rw [Ne, List.dropLast_eq_nil_iff]; omega
    rw [hsplit] at hhead hchain hlen hnd ⊢
    obtain ⟨hchain', -, hlast⟩ := List.isChain_append.1 hchain
    obtain ⟨hnd', -, hdisj⟩ := List.nodup_append.1 hnd
    have hyl : l.getLast hne ∉ l.dropLast := by
      intro hmem
      exact hdisj _ hmem _ (by simp) rfl
    have hlen' : l.dropLast.length = n + 1 := by
      simp only [List.length_append, List.length_singleton] at hlen; omega
    have hhead' : l.dropLast.head? = some o := by
      rcases hl : l.dropLast.head? with _ | a
      · exfalso
        have hnil : l.dropLast = [] := by
          cases h : l.dropLast with
          | nil => rfl
          | cons b t => rw [h] at hl; exact absurd hl (by simp)
        exact hne' hnil
      · rw [List.head?_append, hl] at hhead
        simpa using hhead
    have hmem : l.dropLast ∈ walkLists G o n := ih hhead' hchain' hnd' hlen'
    have hadj : G.Adj (l.dropLast.getLastD o) (l.getLast hne) := by
      have hgl : l.dropLast.getLast? = some (l.dropLast.getLast hne') :=
        List.getLast?_eq_some_getLast hne'
      have hd : l.dropLast.getLastD o = l.dropLast.getLast hne' := by
        rw [List.getLastD_eq_getLast?, hgl]; rfl
      rw [hd]
      exact hlast _ hgl _ (by simp)
    rw [mem_walkLists_succ_iff]
    exact ⟨l.dropLast, hmem, l.getLast hne, hadj, hyl, rfl⟩

end Counting

/-! ### Edge coordinates of a vertex list and the cylinder event -/

section Coordinates

variable {G : SimpleGraph V} [DecidableEq V]

open Classical in
/-- The set of edges traversed by consecutive vertices of a vertex list. -/
noncomputable def coordOf (G : SimpleGraph V) (l : List V) : Finset G.edgeSet :=
  ((l.zip l.tail).filterMap fun z =>
    if h : G.Adj z.1 z.2 then some (⟨s(z.1, z.2), G.mem_edgeSet.mpr h⟩ : G.edgeSet) else none).toFinset

/-- The event that every edge traversed by a vertex list is open. -/
def cylEvent (G : SimpleGraph V) (l : List V) : Set (G.edgeSet → Bool) :=
  {ω | ∀ e ∈ coordOf G l, ω e = true}

theorem measure_cylEvent (G : SimpleGraph V) (p : I) (l : List V) :
    percolation G p (cylEvent G l) =
      (ENNReal.ofReal (p : ℝ)) ^ (coordOf G l).card :=
  bernoulliProduct_cylinder (ι := G.edgeSet) p (coordOf G l)

theorem mem_coordOf {l : List V} {e : G.edgeSet} :
    e ∈ coordOf G l ↔ ∃ z ∈ l.zip l.tail, ∃ h : G.Adj z.1 z.2, e = ⟨s(z.1, z.2), G.mem_edgeSet.mpr h⟩ := by
  classical
  rw [coordOf, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨z, hz, hf⟩
    split at hf
    · exact ⟨z, hz, ‹G.Adj z.1 z.2›, (Option.some.inj hf).symm⟩
    · exact absurd hf (by simp)
  · rintro ⟨z, hz, hadj, rfl⟩
    exact ⟨z, hz, by simp only [dif_pos hadj]⟩

/-- A consecutive pair of a list splits the list at that pair. -/
theorem exists_append_of_mem_zip {l : List V} {z : V × V} (hz : z ∈ l.zip l.tail) :
    ∃ l₁ l₂ : List V, l = l₁ ++ z.1 :: z.2 :: l₂ := by
  induction l with
  | nil => simp at hz
  | cons a rest ih =>
    cases rest with
    | nil => simp at hz
    | cons b rest =>
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨[], rest, rfl⟩
      · obtain ⟨l₁, l₂, hl⟩ := ih hz
        exact ⟨a :: l₁, l₂, by rw [hl, List.cons_append]⟩

theorem IsChain.zip_adj {l : List V} (h : l.IsChain G.Adj) :
    ∀ z ∈ l.zip l.tail, G.Adj z.1 z.2 := by
  intro z hz
  obtain ⟨l₁, l₂, hl⟩ := exists_append_of_mem_zip hz
  exact List.isChain_iff_forall_rel_of_append_cons_cons.mp h hl

theorem mem_of_mem_zip_left {l : List V} {z : V × V} (hz : z ∈ l.zip l.tail) : z.1 ∈ l := by
  obtain ⟨l₁, l₂, hl⟩ := exists_append_of_mem_zip hz
  rw [hl]
  exact List.mem_append_right _ (List.mem_cons_self)

theorem mem_of_mem_zip_right {l : List V} {z : V × V} (hz : z ∈ l.zip l.tail) : z.2 ∈ l := by
  obtain ⟨l₁, l₂, hl⟩ := exists_append_of_mem_zip hz
  rw [hl]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem coordOf_cons_cons {a b : V} {rest : List V} (hab : G.Adj a b) :
    coordOf G (a :: b :: rest) =
      insert (⟨s(a, b), G.mem_edgeSet.mpr hab⟩ : G.edgeSet) (coordOf G (b :: rest)) := by
  classical
  ext e
  rw [mem_coordOf, Finset.mem_insert, mem_coordOf]
  constructor
  · rintro ⟨z, hz, hadj, rfl⟩
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · left
      exact Subtype.ext rfl
    · exact Or.inr ⟨z, hz, hadj, rfl⟩
  · rintro (h | ⟨z, hz, hadj, rfl⟩)
    · subst h
      exact ⟨(a, b), by simp, hab, rfl⟩
    · exact ⟨z, by simp only [List.tail_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hz,
        hadj, rfl⟩

theorem notMem_coordOf_of_nodup {a b : V} {rest : List V}
    (hnd : (a :: b :: rest).Nodup) (hab : G.Adj a b) :
    (⟨s(a, b), G.mem_edgeSet.mpr hab⟩ : G.edgeSet) ∉ coordOf G (b :: rest) := by
  rw [mem_coordOf]
  rintro ⟨z, hz, hzadj, he⟩
  have ha : a ∉ b :: rest := (List.nodup_cons.mp hnd).1
  have hev : (s(a, b) : Sym2 V) = s(z.1, z.2) := congrArg Subtype.val he
  have h1 : a ∈ (s(z.1, z.2) : Sym2 V) := by
    rw [← hev]
    exact Sym2.mem_mk_left a b
  refine ha ?_
  rw [Sym2.mem_iff] at h1
  rcases h1 with h | h
  · rw [h]; exact mem_of_mem_zip_left hz
  · rw [h]; exact mem_of_mem_zip_right hz

theorem coordOf_card : ∀ {l : List V}, l.Nodup → l.IsChain G.Adj →
    (coordOf G l).card = l.length - 1
  | [], _, _ => by simp [coordOf]
  | [_], _, _ => by simp [coordOf]
  | a :: b :: rest, hnd, hch => by
    obtain ⟨hab, hch'⟩ := List.isChain_cons_cons.mp hch
    have hnd' : (b :: rest).Nodup := List.Nodup.of_cons hnd
    rw [coordOf_cons_cons hab, Finset.card_insert_of_notMem (notMem_coordOf_of_nodup hnd hab),
      coordOf_card hnd' hch']
    simp

end Coordinates

section WalkCylinder

variable {G : SimpleGraph V} [DecidableEq V]

theorem IsOpenIn.take {ω : G.edgeSet → Bool} {A : Set (Sym2 V)} {a b : V} {p : G.Walk a b}
    (hw : IsOpenIn ω A p) (n : ℕ) : IsOpenIn ω A (p.take n) := by
  intro d hd
  rw [SimpleGraph.Walk.darts_take] at hd
  exact hw d (List.mem_of_mem_take hd)

/-- Every edge traversed by the support of an open walk is open: the cylinder event of the
support of an open walk holds. -/
theorem isOpenIn_cylEvent_support {a b : V} :
    ∀ (w : G.Walk a b) {ω : G.edgeSet → Bool}, IsOpenIn ω Set.univ w → ω ∈ cylEvent G w.support
  | .nil, ω, _ => by
    intro e he
    rw [SimpleGraph.Walk.support_nil] at he
    have hempty : coordOf G ([a] : List V) = ∅ := by
      rw [coordOf]
      simp
    rw [hempty] at he
    simp at he
  | @SimpleGraph.Walk.cons V G u v x h p, ω, hw => by
    have hdarts : ∀ d ∈ (SimpleGraph.Walk.cons h p).darts,
        d.edge ∈ Set.univ ∧ ω ⟨d.edge, d.edge_mem⟩ = true := hw
    rw [SimpleGraph.Walk.darts_cons] at hdarts
    set d0 : G.Dart := { fst := u, snd := v, adj := h } with hd0
    have hfirst : ω (⟨s(u, v), G.mem_edgeSet.mpr h⟩ : G.edgeSet) = true :=
      (hdarts d0 (List.mem_cons_self)).2
    have hpne : p.support ≠ [] := by simp
    have hsp : p.support = v :: p.support.tail := by
      conv_lhs => rw [← List.cons_head_tail hpne, SimpleGraph.Walk.head_support]
    have hzip : (u :: p.support).zip p.support =
        (u, v) :: (p.support.zip p.support.tail) := by
      rw [hsp, List.zip_cons_cons, List.tail_cons]
    intro e he
    rw [mem_coordOf] at he
    obtain ⟨z, hz, hzadj, rfl⟩ := he
    rw [SimpleGraph.Walk.support_cons, List.tail_cons, hzip, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rw [show (⟨s(u, v), G.mem_edgeSet.mpr hzadj⟩ : G.edgeSet) =
          ⟨s(u, v), G.mem_edgeSet.mpr h⟩ from Subtype.ext rfl]
      exact hfirst
    · have hrec : ∀ e ∈ coordOf G p.support, ω e = true :=
        isOpenIn_cylEvent_support p (fun d hd => hdarts d (List.mem_cons_of_mem _ hd))
      exact hrec _ (mem_coordOf.mpr ⟨z, hz, hzadj, rfl⟩)

end WalkCylinder

section WalkListsProps

variable {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite] {o : V}

theorem walkLists_length : ∀ {n : ℕ} {l : List V}, l ∈ walkLists G o n → l.length = n + 1
  | 0, l, hl => by
    rw [mem_walkLists_zero_iff] at hl
    rw [hl]; simp
  | n + 1, l, hl => by
    rw [mem_walkLists_succ_iff] at hl
    obtain ⟨l', hl', y, -, -, rfl⟩ := hl
    rw [List.length_append, walkLists_length hl']
    simp

theorem walkLists_nodup : ∀ {n : ℕ} {l : List V}, l ∈ walkLists G o n → l.Nodup
  | 0, l, hl => by
    rw [mem_walkLists_zero_iff] at hl
    rw [hl]; simp
  | n + 1, l, hl => by
    rw [mem_walkLists_succ_iff] at hl
    obtain ⟨l', hl', y, -, hyl, rfl⟩ := hl
    rw [List.nodup_append]
    exact ⟨walkLists_nodup hl', by simp, fun a ha b hb => by
      rw [List.mem_singleton] at hb
      subst hb
      exact fun heq => hyl (heq ▸ ha)⟩

theorem walkLists_chain : ∀ {n : ℕ} {l : List V}, l ∈ walkLists G o n → l.IsChain G.Adj
  | 0, l, hl => by
    rw [mem_walkLists_zero_iff] at hl
    rw [hl]
    exact List.isChain_singleton o
  | n + 1, l, hl => by
    rw [mem_walkLists_succ_iff] at hl
    obtain ⟨l', hl', y, hy, hyl, rfl⟩ := hl
    have hchain' := walkLists_chain hl'
    have hlen' := walkLists_length hl'
    have hne : l' ≠ [] := by rintro rfl; simp at hlen'
    refine List.IsChain.append hchain' (List.isChain_singleton y) ?_
    intro a ha b hb
    rw [List.head?_cons, Option.mem_some_iff] at hb
    subst hb
    rw [List.getLast?_eq_some_getLast hne, Option.mem_some_iff] at ha
    subst ha
    have hd : l'.getLast hne = l'.getLastD o := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]; rfl
    rw [hd]
    exact hy

end WalkListsProps

section MainBounds

variable {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite] {o : V} {d : ℕ}

theorem armEvent_subset_walkLists (n : ℕ) :
    armEvent G o n ⊆ ⋃ l ∈ walkLists G o n, cylEvent G l := by
  intro ω hω
  obtain ⟨x, hdist, hconn⟩ := hω
  obtain ⟨q, hq⟩ := hconn
  have hbyp : IsOpenIn ω Set.univ q.bypass := fun e he =>
    hq e (SimpleGraph.Walk.darts_bypass_subset_darts (p := q) he)
  have hlen : n ≤ q.bypass.length := le_trans hdist (SimpleGraph.dist_le q.bypass)
  have hw : IsOpenIn ω Set.univ (q.bypass.take n) := hbyp.take n
  have hpath : (q.bypass.take n).IsPath := q.bypass_isPath.take n
  have hlenw : (q.bypass.take n).length = n := by
    rw [SimpleGraph.Walk.take_length]; omega
  have hsupne : (q.bypass.take n).support ≠ [] := by
    intro h
    have h1 : (q.bypass.take n).support.length = (q.bypass.take n).length + 1 :=
      SimpleGraph.Walk.length_support _
    rw [h] at h1
    simp only [List.length_nil] at h1
    omega
  have hhead : (q.bypass.take n).support.head? = some o := by
    cases h : (q.bypass.take n).support with
    | nil => exact absurd h hsupne
    | cons a t =>
        have h1 : ((q.bypass.take n).support).head hsupne = o := SimpleGraph.Walk.head_support _
        simp only [h] at h1
        simpa using h1
  have hnd : (q.bypass.take n).support.Nodup := (SimpleGraph.Walk.isPath_def _).1 hpath
  have hlen2 : (q.bypass.take n).support.length = n + 1 := by
    rw [SimpleGraph.Walk.length_support, hlenw]
  exact Set.mem_biUnion
    (mem_walkLists_of_head_chain o n hhead (SimpleGraph.Walk.isChain_adj_support _) hnd hlen2)
    (isOpenIn_cylEvent_support _ hw)

theorem measure_armEvent_le (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) (p : I) (n : ℕ) :
    percolation G p (armEvent G o n) ≤ (ENNReal.ofReal (p : ℝ) * d) ^ n := by
  refine le_trans (measure_mono (armEvent_subset_walkLists n)) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hne : ∀ l ∈ walkLists G o n, l ≠ [] := by
    intro l hl hnil
    have := walkLists_length hl
    rw [hnil] at this
    simp at this
  have hterm : ∀ l ∈ walkLists G o n,
      percolation G p (cylEvent G l) = (ENNReal.ofReal (p : ℝ)) ^ n := by
    intro l hl
    rw [measure_cylEvent, coordOf_card (walkLists_nodup hl) (walkLists_chain hl),
      walkLists_length hl]
    simp
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (walkLists G o n).card * (ENNReal.ofReal (p : ℝ)) ^ n
      ≤ d ^ n * (ENNReal.ofReal (p : ℝ)) ^ n := by
        gcongr
        exact_mod_cast card_walkLists_le hdeg n
    _ = ((d : ENNReal) * ENNReal.ofReal (p : ℝ)) ^ n := by
        rw [mul_pow]
    _ = (ENNReal.ofReal (p : ℝ) * d) ^ n := by rw [mul_comm]

end MainBounds

section Main

variable {G : SimpleGraph V} [Countable V] [G.LocallyFinite] {o : V} {d : ℕ}

/-- A finite measure whose mass is dominated by every positive real is zero. -/
theorem measure_eq_zero_of_forall_ofReal {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (h : ∀ γ : ℝ, 0 < γ → μ s ≤ ENNReal.ofReal γ) : μ s = 0 := by
  refine le_antisymm ?_ (by simp)
  by_contra hne
  have hne0 : μ s ≠ 0 := by
    intro h
    rw [h] at hne
    simp at hne
  have htop : μ s ≠ ⊤ := by
    intro htop
    have h1 := h 1 one_pos
    rw [htop] at h1
    simp at h1
  have hpos : 0 < (μ s).toReal := ENNReal.toReal_pos hne0 htop
  have hle : (μ s).toReal ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hb := h ε hε
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (le_of_lt hε)] at h2
    linarith
  linarith

/-- **First-moment (branching) bound.** On a graph whose vertex neighbourhoods have at most `d`
vertices, Bernoulli bond percolation with `p * d < 1` has zero percolation probability at every
vertex. This is the Galton–Watson comparison invoked in Remark 1.5 of arXiv:2512.16486v1. -/
theorem percolationProb_eq_zero_of_mul_card_lt_one (hG : G.Connected)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) {p : I} (hp : (p : ℝ) * d < 1) :
    percolationProb G o p = 0 := by
  classical
  rw [percolationProb_eq, setOf_infinite_eq_iInter_armEvent hG o]
  refine measure_eq_zero_of_forall_ofReal (fun γ hγ => ?_)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hγ hp
  refine le_trans (measure_mono (Set.iInter_subset _ n))
    (le_trans (measure_armEvent_le hdeg p n) ?_)
  have hcast : (ENNReal.ofReal (p : ℝ) * (d : ENNReal)) ^ n =
      ENNReal.ofReal (((p : ℝ) * d) ^ n) := by
    have h1 : ENNReal.ofReal (p : ℝ) * (d : ENNReal) = ENNReal.ofReal ((p : ℝ) * d) := by
      rw [← ENNReal.ofReal_natCast d, ENNReal.ofReal_mul p.2.1]
    rw [h1, ← ENNReal.ofReal_pow (mul_nonneg p.2.1 (Nat.cast_nonneg d))]
  rw [hcast]
  exact ENNReal.ofReal_le_ofReal (le_of_lt hn)

/-- **`p_c (G) > 0` for graphs of bounded degree**: the non-degeneracy assertion of Remark 1.5 of
arXiv:2512.16486v1, so that the subcritical window `max (p, p') < p_c` of Theorems 1.9 and 1.10 is
nonempty. -/
theorem criticalProb_pos (hG : G.Connected) (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d)
    (hd : 0 < d) : 0 < criticalProb G o := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hrew : (1 : ℝ) / (2 * (d : ℝ)) > 0 := by positivity
  set r : ℝ := min 1 (1 / (2 * (d : ℝ))) with hr
  have hr0 : 0 ≤ r := le_min zero_le_one (le_of_lt hrew)
  have hr1 : r ≤ 1 := min_le_left _ _
  let p : I := ⟨r, hr0, hr1⟩
  have hpval : (p : ℝ) = r := rfl
  have hpmul : (p : ℝ) * (d : ℝ) < 1 := by
    rw [hpval]
    have h2 : r ≤ 1 / (2 * (d : ℝ)) := min_le_right _ _
    have h3 : r * (d : ℝ) ≤ (1 / (2 * (d : ℝ))) * (d : ℝ) :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hdpos)
    have h4 : (1 / (2 * (d : ℝ))) * (d : ℝ) = 1 / 2 := by
      field_simp
    linarith
  have hzero : percolationProb G o p = 0 :=
    percolationProb_eq_zero_of_mul_card_lt_one hG hdeg hpmul
  have hle : (p : ℝ) ≤ criticalProb G o :=
    le_sSup_image_val (s := {q : I | percolationProb G o q = 0}) (p := p) hzero
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    rw [hpval]
    exact lt_min one_pos hrew
  linarith

/-- **An explicit positive subcritical Bernoulli parameter on any locally finite graph of
bounded degree**: combined with the repository's `percolationProb_eq_zero_of_lt_criticalProb`,
`p_c (G) > 0` gives a genuine parameter `s > 0` with `θ (s) = 0`. This is the non-degeneracy of
the subcritical window used in Theorems 1.9 and 1.10 of arXiv:2512.16486v1. -/
theorem exists_pos_percolationProb_eq_zero (hG : G.Connected)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) (hd : 0 < d) :
    ∃ s : I, 0 < (s : ℝ) ∧ percolationProb G o s = 0 := by
  classical
  have hpos : 0 < criticalProb G o := criticalProb_pos hG hdeg hd
  have hr0 : (0 : ℝ) ≤ min 1 (criticalProb G o / 2) :=
    le_min zero_le_one (by linarith)
  have hr1 : min 1 (criticalProb G o / 2) ≤ 1 := min_le_left _ _
  refine ⟨⟨min 1 (criticalProb G o / 2), hr0, hr1⟩, ?_, ?_⟩
  · have : (0 : ℝ) < min 1 (criticalProb G o / 2) := lt_min one_pos (by linarith)
    exact this
  · refine percolationProb_eq_zero_of_lt_criticalProb hG ?_
    have h2 : min 1 (criticalProb G o / 2) ≤ criticalProb G o / 2 := min_le_right _ _
    linarith

/-- **`1/d ≤ p_c (G)`**: the explicit sharpening of `criticalProb_pos` obtained from the
first-moment bound. Combined with the paper's comparison rate `p' = p/(p + q(1-p))` of
`FK.prime`, it locates an explicit small-`p` window where the comparison Bernoulli law is
subcritical. -/
theorem inv_card_le_criticalProb (hG : G.Connected)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) (hd : 0 < d) :
    (1 : ℝ) / (d : ℝ) ≤ criticalProb G o := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have ha1 : 1 / (d : ℝ) - ε ≤ 1 := by
    have h1 : 1 / (d : ℝ) ≤ 1 := by
      rw [div_le_one hdpos]
      exact_mod_cast hd
    linarith
  have hr0 : (0 : ℝ) ≤ max 0 (1 / (d : ℝ) - ε) := le_max_left _ _
  have hr1 : max 0 (1 / (d : ℝ) - ε) ≤ 1 := max_le zero_le_one ha1
  let s : I := ⟨max 0 (1 / (d : ℝ) - ε), hr0, hr1⟩
  have hsv : (s : ℝ) = max 0 (1 / (d : ℝ) - ε) := rfl
  have hmul : (s : ℝ) * (d : ℝ) < 1 := by
    rw [hsv]
    by_cases h : 1 / (d : ℝ) - ε ≤ 0
    · rw [max_eq_left h, zero_mul]
      exact zero_lt_one
    · rw [max_eq_right (not_le.mp h).le]
      have hexp : (1 / (d : ℝ) - ε) * (d : ℝ) = 1 - ε * (d : ℝ) := by
        field_simp
      rw [hexp]
      have : 0 < ε * (d : ℝ) := mul_pos hε hdpos
      linarith
  have hzero : percolationProb G o s = 0 :=
    percolationProb_eq_zero_of_mul_card_lt_one hG hdeg hmul
  have hle : (s : ℝ) ≤ criticalProb G o :=
    le_sSup_image_val (s := {q : I | percolationProb G o q = 0}) (p := s) hzero
  have hge : 1 / (d : ℝ) - ε ≤ (s : ℝ) := by
    rw [hsv]; exact le_max_right _ _
  linarith

/-- **The small-`p` subcritical comparison window.** For every `q > 0` there is an explicit
`p₀ > 0` such that for every `0 < p < p₀` the paper's comparison rate
`p' = FK.prime q p = p/(p + q (1-p))` is strictly below `p_c (G)`. This is the quantitative form
of the sentence in §1.3 of arXiv:2512.16486v1 that the comparison percolation is subcritical for
every `p` small enough; it uses only the degree bound, not graph invariance. -/
theorem exists_prime_lt_criticalProb (hG : G.Connected)
    (hdeg : ∀ v : V, (G.neighborSet v).ncard ≤ d) (hd : 0 < d) {q : ℝ} (hq : 0 < q) :
    ∃ p₀ : I, 0 < (p₀ : ℝ) ∧ ∀ p : I, 0 < (p : ℝ) → (p : ℝ) < (p₀ : ℝ) →
      FK.prime q (p : ℝ) < criticalProb G o := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hc : (1 : ℝ) / (d : ℝ) ≤ criticalProb G o := inv_card_le_criticalProb hG hdeg hd
  have hrpos : (0 : ℝ) < min (1 / 2) (q / (4 * (d : ℝ))) :=
    lt_min (by norm_num) (by positivity)
  have hr1 : min (1 / 2) (q / (4 * (d : ℝ))) ≤ 1 :=
    le_trans (min_le_left _ _) (by norm_num)
  refine ⟨⟨min (1 / 2) (q / (4 * (d : ℝ))), le_of_lt hrpos, hr1⟩, hrpos, ?_⟩
  intro p hp0 hpr
  have hp1 : (p : ℝ) ≤ 1 := le_trans (le_of_lt hpr) hr1
  have hhalf : (p : ℝ) < 1 / 2 := lt_of_lt_of_le hpr (min_le_left _ _)
  have hsmall : (p : ℝ) < q / (4 * (d : ℝ)) := lt_of_lt_of_le hpr (min_le_right _ _)
  rw [FK.prime]
  have hqpos : (0 : ℝ) < q / 2 := by linarith
  have hlow : q / 2 ≤ q * (1 - (p : ℝ)) := by nlinarith
  have hstep : (p : ℝ) / ((p : ℝ) + q * (1 - (p : ℝ))) ≤ (p : ℝ) / (q / 2) := by
    have hpos : 0 < (p : ℝ) + q * (1 - (p : ℝ)) := FK.denominator_pos hq p.2.1 p.2.2
    exact div_le_div_of_nonneg_left p.2.1 hqpos (by linarith)
  have hval : (p : ℝ) / (q / 2) = 2 * (p : ℝ) / q := by
    field_simp
  have hfinal : 2 * (p : ℝ) / q < 1 / (2 * (d : ℝ)) := by
    rw [div_lt_div_iff₀ hq (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
    have h4 : (p : ℝ) * (4 * (d : ℝ)) < q := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (d : ℝ))] at hsmall
      linarith
    nlinarith
  have hmono : 1 / (2 * (d : ℝ)) ≤ 1 / (d : ℝ) := by
    have h1 : 1 / (2 * (d : ℝ)) = (1 / 2) * (1 / (d : ℝ)) := by
      field_simp
    rw [h1]
    have h2 : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
    linarith
  calc (p : ℝ) / ((p : ℝ) + q * (1 - (p : ℝ))) ≤ (p : ℝ) / (q / 2) := hstep
    _ = 2 * (p : ℝ) / q := hval
    _ < 1 / (2 * (d : ℝ)) := hfinal
    _ ≤ 1 / (d : ℝ) := hmono
    _ ≤ criticalProb G o := hc

end Main
