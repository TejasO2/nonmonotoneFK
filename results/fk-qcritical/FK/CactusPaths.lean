import FK.CactusMeasure

/-!
# Open paths on the triangle cactus

The projection `effective` identifies open connection of two junctions in the
original cactus with open connection in the five-regular junction tree.  The
proof in both directions uses the original cactus walks themselves.
-/

namespace Ultra.TriangleCactus

open Ultra V MeasureTheory ProbabilityTheory Filter
open CurvatureVariance.Infra.Percolation FK.AGImplant
open scoped ENNReal NNReal unitInterval Sym2

lemma baseEdge_eq_actual {u v : V} (h : G.Adj u v) :
    baseEdge (eOf h) = (⟨s(Sum.inl u, Sum.inl v), h⟩ : graph.edgeSet) := by
  apply Subtype.ext
  exact baseEdge_val (eOf h)

lemma actual_open_direct {ω : graph.edgeSet → Bool} {u v : V} (h : G.Adj u v)
    (ho : ω (baseEdge (eOf h)) = true) : OpenConnected graph ω Set.univ (Sum.inl u) (Sum.inl v) := by
  have hg : graph.Adj (Sum.inl u) (Sum.inl v) := h
  apply OpenConnected.of_adj hg (Set.mem_univ _)
  rwa [← baseEdge_eq_actual h]

lemma actual_open_bypass (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    (hl : ω (leftSpoke e) = true) (hr : ω (rightSpoke e) = true) :
    OpenConnected graph ω Set.univ
      (Sum.inl (e : Sym2 V).out.1) (Sum.inl (e : Sym2 V).out.2) := by
  exact (OpenConnected.of_adj (Sym2.out_fst_mem (e : Sym2 V))
    (Set.mem_univ _) hl).trans
    (OpenConnected.of_adj (Sym2.out_snd_mem (e : Sym2 V)) (Set.mem_univ _) hr)

lemma openConnected_congr_junction {ω : graph.edgeSet → Bool} {a b u v : V}
    (ha : a = u) (hb : b = v)
    (h : OpenConnected graph ω Set.univ (Sum.inl a) (Sum.inl b)) :
    OpenConnected graph ω Set.univ (Sum.inl u) (Sum.inl v) := by
  cases ha
  cases hb
  exact h

/-- One effective-open tree edge lifts to an actual cactus connection, using
its direct bond or its original two-edge bypass. -/
lemma actual_of_effective_adj {ω : graph.edgeSet → Bool} {u v : V} (h : OAdj (effective ω) u v) :
    OpenConnected graph ω Set.univ (Sum.inl u) (Sum.inl v) := by
  rcases h with ⟨h, he⟩
  by_cases hd : ω (baseEdge (eOf h)) = true
  · exact actual_open_direct h hd
  · have hp : ω (leftSpoke (eOf h)) = true ∧ ω (rightSpoke (eOf h)) = true := by
      cases hl : ω (leftSpoke (eOf h)) <;> cases hr : ω (rightSpoke (eOf h)) <;>
        simp_all [effective]
    have heq : s((eOf h : Sym2 V).out.1, (eOf h : Sym2 V).out.2) = s(u, v) :=
      Quot.out_eq (eOf h : Sym2 V)
    rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact openConnected_congr_junction hu hv
        (actual_open_bypass ω (eOf h) hp.1 hp.2)
    · exact openConnected_congr_junction hv hu
        (openConnected_reverse (actual_open_bypass ω (eOf h) hp.1 hp.2))

lemma actual_of_effective_reach {ω : graph.edgeSet → Bool} {u v : V}
    (h : OReach (effective ω) u v) : OpenConnected graph ω Set.univ (Sum.inl u) (Sum.inl v) := by
  induction h with
  | refl => exact OpenConnected.refl _ _ _
  | @tail b c hab hbc ih => exact OpenConnected.trans ih (actual_of_effective_adj hbc)

/-- A direct cactus bond gives an effective-open tree adjacency. -/
lemma effective_adj_of_direct {ω : graph.edgeSet → Bool} {u v : V} (h : G.Adj u v)
    (ho : ω (⟨s(Sum.inl u, Sum.inl v), h⟩ : graph.edgeSet) = true) :
    OAdj (effective ω) u v := by
  refine ⟨h, ?_⟩
  have hb := baseEdge_eq_actual h
  simp only [effective, hb, ho, Bool.true_or]

lemma effective_open_of_spokes (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    (hl : ω (leftSpoke e) = true) (hr : ω (rightSpoke e) = true) :
    effective ω e = true := by
  simp [effective, hl, hr]

lemma effective_adj_endpoints (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    (hl : ω (leftSpoke e) = true) (hr : ω (rightSpoke e) = true) :
    OReach (effective ω) (e : Sym2 V).out.1 (e : Sym2 V).out.2 := by
  have h : G.Adj (e : Sym2 V).out.1 (e : Sym2 V).out.2 := by
    have he : s((e : Sym2 V).out.1, (e : Sym2 V).out.2) = (e : Sym2 V) := Quot.out_eq _
    rw [← SimpleGraph.mem_edgeSet, he]
    exact e.property
  refine oReach_single ⟨h, ?_⟩
  rw [show eOf h = e from Subtype.ext (Quot.out_eq (e : Sym2 V))]
  exact effective_open_of_spokes ω e hl hr

lemma leftSpoke_open_at_out1 (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    {h : graph.Adj (Sum.inl (e : Sym2 V).out.1) (Sum.inr e)}
    (ho : ω (⟨s(Sum.inl (e : Sym2 V).out.1, Sum.inr e), h⟩ : graph.edgeSet) = true) :
    ω (leftSpoke e) = true := ho

lemma rightSpoke_open_at_out2 (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    {h : graph.Adj (Sum.inl (e : Sym2 V).out.2) (Sum.inr e)}
    (ho : ω (⟨s(Sum.inl (e : Sym2 V).out.2, Sum.inr e), h⟩ : graph.edgeSet) = true) :
    ω (rightSpoke e) = true := by
  rw [show (⟨s(Sum.inl (e : Sym2 V).out.2, Sum.inr e), h⟩ : graph.edgeSet) =
    rightSpoke e from Subtype.ext Sym2.eq_swap] at ho
  exact ho

lemma leftSpoke_open_at_out1_rev (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    {h : graph.Adj (Sum.inr e) (Sum.inl (e : Sym2 V).out.1)}
    (ho : ω (⟨s(Sum.inr e, Sum.inl (e : Sym2 V).out.1), h⟩ : graph.edgeSet) = true) :
    ω (leftSpoke e) = true := by
  rw [show (⟨s(Sum.inr e, Sum.inl (e : Sym2 V).out.1), h⟩ : graph.edgeSet) =
    leftSpoke e from Subtype.ext Sym2.eq_swap] at ho
  exact ho

lemma rightSpoke_open_at_out2_rev (ω : graph.edgeSet → Bool) (e : G.edgeSet)
    {h : graph.Adj (Sum.inr e) (Sum.inl (e : Sym2 V).out.2)}
    (ho : ω (⟨s(Sum.inr e, Sum.inl (e : Sym2 V).out.2), h⟩ : graph.edgeSet) = true) :
    ω (rightSpoke e) = true := ho

/-- Compress an open cactus walk between junctions to an effective open walk
in the junction tree.  Every midpoint takes two steps, and those two steps
open exactly the two-spoke bypass needed for the same effective edge. -/
theorem effective_reach_of_actual {ω : graph.edgeSet → Bool} {u v : V}
    (p : graph.Walk (Sum.inl u) (Sum.inl v)) (hp : IsOpenIn ω Set.univ p) :
    OReach (effective ω) u v := by
  induction hn : p.length using Nat.strong_induction_on generalizing u with
  | h n ih =>
      cases p with
    | nil => exact oReach_refl (effective ω) _
    | @cons _ b _ h q =>
        cases b with
        | inl w =>
            have hh := (isOpenIn_cons.mp hp).1.2
            exact (oReach_single (effective_adj_of_direct h hh)).trans
              (ih q.length (by simp only [SimpleGraph.Walk.length_cons] at hn; omega) q
              (isOpenIn_cons.mp hp).2 rfl)
        | inr e =>
            cases q with
            | @cons _ b' _ h' q' =>
                cases b' with
                | inl w =>
                    by_cases huw : u = w
                    · subst w
                      exact ih q'.length (by simp only [SimpleGraph.Walk.length_cons] at hn; omega) q'
                        (isOpenIn_cons.mp (isOpenIn_cons.mp hp).2).2 rfl
                    · have hu : u ∈ (e : Sym2 V) := h
                      have hw : w ∈ (e : Sym2 V) := h'
                      have heq : (e : Sym2 V) = s((e : Sym2 V).out.1, (e : Sym2 V).out.2) :=
                        (Quot.out_eq (e : Sym2 V)).symm
                      rw [heq, Sym2.mem_iff] at hu hw
                      have ho1 := (isOpenIn_cons.mp hp).1.2
                      have ho2 := (isOpenIn_cons.mp (isOpenIn_cons.mp hp).2).1.2
                      have hrest : OReach (effective ω) w v :=
                        ih q'.length (by simp only [SimpleGraph.Walk.length_cons] at hn; omega) q'
                        (isOpenIn_cons.mp (isOpenIn_cons.mp hp).2).2 rfl
                      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
                      · exact (huw rfl).elim
                      · have hl := leftSpoke_open_at_out1 ω e ho1
                        have hr := rightSpoke_open_at_out2_rev ω e ho2
                        exact (effective_adj_endpoints ω e hl hr).trans hrest
                      · have hl := leftSpoke_open_at_out1_rev ω e ho2
                        have hr := rightSpoke_open_at_out2 ω e ho1
                        exact (oReach_symm (effective_adj_endpoints ω e hl hr)).trans hrest
                      · exact (huw rfl).elim
                | inr f => exact h'.elim

/-- An actual midpoint connection carries an effective connection to one of its
incident junctions. -/
lemma endpoint_effective_reach_of_midpoint {ω : graph.edgeSet → Bool} {u : V} {e : G.edgeSet}
    (h : OpenConnected graph ω Set.univ (Sum.inl u) (Sum.inr e)) :
    ∃ w : V, OReach (effective ω) u w ∧ w ∈ (e : Sym2 V) := by
  obtain ⟨q, hq⟩ := openConnected_reverse h
  cases q with
  | @cons _ b _ hfirst q =>
      cases b with
      | inl w =>
          have hw : OReach (effective ω) w u :=
            effective_reach_of_actual q (isOpenIn_cons.mp hq).2
          exact ⟨w, oReach_symm hw, hfirst⟩
      | inr f => exact hfirst.elim

lemma effective_perc_of_actual_junction {ω : graph.edgeSet → Bool} {u : V}
    (hu : {y : Vertex | OpenConnected graph ω Set.univ (Sum.inl u) y}.Infinite) :
    Perc (effective ω) := by
  let J : Set V := {v : V | OReach (effective ω) u v}
  have hJ : J.Infinite := by
    by_contra! hJf
    let F : Set Vertex := Sum.inl '' J ∪
      ⋃ w : {w : V // w ∈ J}, Sum.inr '' {e : G.edgeSet | (w : V) ∈ (e : Sym2 V)}
    have hmid (w : V) : {e : G.edgeSet | w ∈ (e : Sym2 V)}.Finite := by
      letI : Finite {e : G.edgeSet // w ∈ (e : Sym2 V)} :=
        FK.AGImplant.Sleeve.finite_edges_containing G w
      exact @Set.toFinite _ _ (FK.AGImplant.Sleeve.finite_edges_containing G w)
    have hF : F.Finite := by
      letI := hJf.fintype
      exact (hJf.image _).union (Set.finite_iUnion fun w => (hmid w.1).image _)
    have hsub : {y : Vertex | OpenConnected graph ω Set.univ (Sum.inl u) y} ⊆ F := by
      intro z hz
      cases z with
      | inl v =>
          obtain ⟨p, hp⟩ := hz
          exact Or.inl ⟨v, effective_reach_of_actual p hp, rfl⟩
      | inr e =>
          obtain ⟨w, hw, hwe⟩ := endpoint_effective_reach_of_midpoint hz
          exact Or.inr (Set.mem_iUnion.2 ⟨⟨w, hw⟩, ⟨e, hwe, rfl⟩⟩)
    exact hu (hF.subset hsub)
  exact ⟨u, hJ⟩

/-- There is an infinite open cluster in the actual cactus. -/
def ActualPerc (ω : graph.edgeSet → Bool) : Prop :=
  ∃ x : Vertex, {y : Vertex | OpenConnected graph ω Set.univ x y}.Infinite

/-- Effective percolation and actual percolation are the same event. -/
theorem actualPerc_iff_effective (ω : graph.edgeSet → Bool) :
    ActualPerc ω ↔ Perc (effective ω) := by
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | inl u => exact effective_perc_of_actual_junction hx
    | inr e =>
        obtain ⟨y, hy, hyx⟩ : ∃ y, OpenConnected graph ω Set.univ (Sum.inr e) y ∧ y ≠ Sum.inr e := by
          by_contra h
          push_neg at h
          exact hx ((Set.finite_singleton (Sum.inr e)).subset (fun y hy => h y hy))
        obtain ⟨p, hp⟩ := hy
        cases p with
        | nil => exact (hyx rfl).elim
        | @cons _ b _ h q =>
            cases b with
            | inl w =>
                have hxw : OpenConnected graph ω Set.univ (Sum.inr e) (Sum.inl w) :=
                  OpenConnected.of_adj h (Set.mem_univ _) (isOpenIn_cons.mp hp).1.2
                exact effective_perc_of_actual_junction
                  (hx.mono (fun z hz => (openConnected_reverse hxw).trans hz))
            | inr f => exact h.elim
  · rintro ⟨u, hu⟩
    refine ⟨Sum.inl u, ?_⟩
    have himg : Sum.inl '' clusterSet (effective ω) u ⊆
        {y : Vertex | OpenConnected graph ω Set.univ (Sum.inl u) y} := by
      rintro _ ⟨v, hv, rfl⟩
      exact actual_of_effective_reach hv
    exact (hu.image Sum.inl_injective.injOn).mono himg

end Ultra.TriangleCactus
