import FK.LeafArms
import FK.PcPos

open scoped Classical
open CurvatureVariance.Infra.Percolation

namespace FK.BurtonKeane

open FK.ClusterCover
open Set

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- Prefixes of avoiding walks are avoiding walks. -/
lemma isOpenIn_takeUntil {A : Set (Sym2 V)} {u v z : V} (p : G.Walk u v)
    (hp : IsOpenIn ω A p) (hz : z ∈ p.support) :
    IsOpenIn ω A (p.takeUntil z hz) := by
  intro d hd
  exact hp d (p.darts_takeUntil_subset_darts hz hd)

/-- Reversing a walk preserves avoidance and openness. -/
lemma isOpenIn_reverse {A : Set (Sym2 V)} {u v : V} (p : G.Walk u v)
    (hp : IsOpenIn ω A p) : IsOpenIn ω A p.reverse := by
  intro d hd
  have hd' : d.symm ∈ p.darts := (SimpleGraph.Walk.mem_darts_reverse).mp hd
  simpa using hp d.symm hd'

/-- Every vertex on an avoiding walk belongs to its root's avoided-edge
cluster. -/
lemma mem_clusterAvoid_of_mem_support {A : Set (Sym2 V)} {r z : V}
    (p : G.Walk r z) (hp : IsOpenIn ω (Set.univ \ A) p) {x : V}
    (hx : x ∈ p.support) : x ∈ clusterAvoid G ω A r := by
  exact ⟨p.takeUntil x hx, isOpenIn_takeUntil p hp hx⟩

/-- Two different avoided-edge clusters have disjoint walk supports. -/
lemma disjoint_support_of_not_openConnected {A : Set (Sym2 V)} {r s a b : V}
    (p : G.Walk r a) (q : G.Walk s b)
    (hp : IsOpenIn ω (Set.univ \ A) p) (hq : IsOpenIn ω (Set.univ \ A) q)
    (hfree : ¬ OpenConnected G ω (Set.univ \ A) r s) :
    ∀ x ∈ p.support, x ∈ q.support → False := by
  intro x hxp hxq
  let px := p.takeUntil x hxp
  let qx := q.takeUntil x hxq
  have hpx : IsOpenIn ω (Set.univ \ A) px := isOpenIn_takeUntil p hp hxp
  have hqx : IsOpenIn ω (Set.univ \ A) qx := isOpenIn_takeUntil q hq hxq
  apply hfree
  exact ⟨px.append qx.reverse, isOpenIn_append.mpr ⟨hpx, isOpenIn_reverse qx hqx⟩⟩

/-- An infinite avoided-edge cluster contains an open arm of every finite
metric radius. -/
lemma exists_far_mem_of_infinite [G.LocallyFinite] (hG : G.Connected)
    {A : Set (Sym2 V)} {r : V} (hinf : (clusterAvoid G ω A r).Infinite)
    (y : V) (n : ℕ) :
    ∃ z, n ≤ G.dist y z ∧ OpenConnected G ω (Set.univ \ A) r z := by
  let B : Set V := {z | G.dist y z ≤ n}
  have hfin : B.Finite := finite_setOf_dist_le hG y n
  have hdiff : (clusterAvoid G ω A r \ B).Infinite := hinf.sdiff hfin
  obtain ⟨z, hzC, hzB⟩ := hdiff.nonempty
  have hn : n < G.dist y z := by simpa [B] using hzB
  exact ⟨z, hn.le, hzC⟩
