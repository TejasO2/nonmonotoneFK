import FK.ExternalClusters

open scoped Classical
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane

open FK.ClusterCover

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- Edges with at least one endpoint in `U`. -/
def incidence (G : SimpleGraph V) (U : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ x ∈ U, x ∈ e}

/-- A pair with neither endpoint in `U` avoids `incidence G U`. -/
lemma not_mem_incidence {U : Set V} {a b : V} (ha : a ∉ U) (hb : b ∉ U) :
    s(a, b) ∉ incidence G U := by
  rintro ⟨_, x, hxU, hxe⟩
  change x ∈ s(a, b) at hxe
  rcases (by simpa using hxe : x = a ∨ x = b) with rfl | rfl
  · exact ha hxU
  · exact hb hxU

/-- Openness and incidence avoidance from a start and all later vertices
outside the central set. -/
lemma isOpenIn_avoidIncidence_of_tail {U : Set V} {a b : V}
    (p : G.Walk a b) (hp : IsOpenIn ω Set.univ p) (ha : a ∉ U)
    (htail : ∀ x ∈ p.support.tail, x ∉ U) :
    IsOpenIn ω (Set.univ \ incidence G U) p := by
  intro d hd
  refine ⟨?_, (hp d hd).2⟩
  have outside {x : V} (hx : x ∈ p.support) : x ∉ U := by
    by_cases hxa : x = a
    · exact hxa ▸ ha
    · rw [← p.cons_tail_support] at hx
      exact htail x (List.mem_of_ne_of_mem hxa hx)
  exact ⟨Set.mem_univ _, not_mem_incidence
    (outside (p.dart_fst_mem_support_of_mem_darts hd))
    (outside (p.dart_snd_mem_support_of_mem_darts hd))⟩

/-- An incident-avoiding walk from a central root stays central. -/
lemma clusterAvoid_incidence_subset {U : Set V} {r : V} (hr : r ∈ U) :
    clusterAvoid G ω (incidence G U) r ⊆ U := by
  intro x hx
  obtain ⟨p, hp⟩ := hx
  cases p with
  | nil => exact hr
  | @cons _ b _ hadj q =>
      have hinc : s(r, b) ∈ incidence G U := by
        refine ⟨hadj, r, hr, by simp⟩
      have hbad := (isOpenIn_cons.mp hp).1.1.2
      exact (hbad hinc).elim

lemma not_mem_of_infinite_clusterAvoid_incidence {U : Set V} (hU : U.Finite)
    {z : V} (hinf : (clusterAvoid G ω (incidence G U) z).Infinite) : z ∉ U := by
  intro hzU
  have hzinf : clusterAvoid G ω (incidence G U) z ⊆ U := clusterAvoid_incidence_subset hzU
  exact hinf (hU.subset hzinf)

/-- Strip at the last central vertex of an open path from a central root to an
outside endpoint. -/
theorem exists_lastIncidenceSuffix {U : Set V} {r z : V}
    (p : G.Walk r z) (hp : IsOpenIn ω Set.univ p) (hr : r ∈ U) (hz : z ∉ U) :
    ∃ a : V, a ∈ U ∧ ∃ q : G.Walk a z,
      IsOpenIn ω Set.univ q ∧ (∀ x ∈ q.support.tail, x ∉ U) := by
  let P : ℕ → Prop := fun i => p.getVert i ∈ U
  have hP0 : P 0 := by
    change p.getVert 0 ∈ U
    rw [show p.getVert 0 = r from p.getVert_zero]
    exact hr
  let k := Nat.findGreatest P p.length
  have hk : k ≤ p.length := Nat.findGreatest_le p.length
  have hkP : P k := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hP0
  let a := p.getVert k
  let q := p.drop k
  have ha : a ∈ U := hkP
  have hnon : ¬ q.Nil := by
    intro hnil
    have heq : a = z := SimpleGraph.Walk.Nil.eq hnil
    exact hz (heq ▸ ha)
  have hq : IsOpenIn ω Set.univ q := by
    intro d hd
    rw [SimpleGraph.Walk.darts_drop] at hd
    exact hp d (List.mem_of_mem_drop hd)
  have htail : ∀ x ∈ q.support.tail, x ∉ U := by
    intro x hx
    rw [← SimpleGraph.Walk.support_tail_of_not_nil q hnon] at hx
    obtain ⟨j, hj, hjlen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    rw [SimpleGraph.Walk.getVert_tail, SimpleGraph.Walk.drop_getVert] at hj
    have hqLen : 0 < q.length := (SimpleGraph.Walk.not_nil_iff_lt_length).mp hnon
    have hql : q.length = p.length - k := SimpleGraph.Walk.drop_length p k
    simp only [SimpleGraph.Walk.length_tail] at hjlen
    rw [hql] at hjlen hqLen
    have hlen : k + (j + 1) ≤ p.length := by omega
    have hgt : k < k + (j + 1) := by omega
    have hnot : ¬ P (k + (j + 1)) := Nat.findGreatest_is_greatest hgt hlen
    intro hxU
    apply hnot
    simpa [P, hj] using hxU
  exact ⟨a, ha, q, hq, htail⟩



/-- Transport an avoided-edge cluster across an avoiding connection. -/
lemma clusterAvoid_subset_of_openConnected {A : Set (Sym2 V)} {u v : V}
    (h : OpenConnected G ω (Set.univ \ A) u v) :
    clusterAvoid G ω A v ⊆ clusterAvoid G ω A u := by
  intro x hx
  exact h.trans hx

/-- No vertex on an avoiding walk from outside `U` can be central. -/
lemma not_mem_of_mem_support_of_avoidIncidence {U : Set V} {a : V} (ha : a ∉ U)
    {b : V} (p : G.Walk a b) (hp : IsOpenIn ω (Set.univ \ incidence G U) p) :
    ∀ x ∈ p.support, x ∉ U := by
  intro x hx hxU
  let r₀ := p.takeUntil x hx
  let q := r₀.reverse
  have hr₀ : IsOpenIn ω (Set.univ \ incidence G U) r₀ := isOpenIn_takeUntil p hp hx
  have hq : IsOpenIn ω (Set.univ \ incidence G U) q := isOpenIn_reverse r₀ hr₀
  have hax : a ≠ x := by
    intro h
    subst x
    exact ha hxU
  have hrnon : ¬ r₀.Nil := by
    intro hn
    have hxa : a = x := SimpleGraph.Walk.Nil.eq hn
    exact hax hxa
  have hqnon : ¬ q.Nil := by
    rw [SimpleGraph.Walk.nil_reverse]
    exact hrnon
  have hlen : 0 < q.darts.length := by
    rw [SimpleGraph.Walk.length_darts, SimpleGraph.Walk.length_reverse]
    exact (SimpleGraph.Walk.not_nil_iff_lt_length).mp hrnon
  have hd : q.darts[0] ∈ q.darts := List.getElem_mem hlen
  have hstart : q.getVert 0 ∈ U := by simpa using hxU
  have hinc : s(q.getVert 0, q.getVert (0 + 1)) ∈ incidence G U := by
    exact ⟨q.adj_getVert_succ ((SimpleGraph.Walk.not_nil_iff_lt_length).mp hqnon),
      q.getVert 0, hstart, by simp⟩
  have ho := hq q.darts[0] hd
  rw [q.darts_getElem_eq_getVert 0 hlen] at ho
  exact ho.1.2 hinc
