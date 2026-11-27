import FK.InternalGeometry

open scoped Classical
open CurvatureVariance.Infra.Percolation
open Set

namespace FK.BurtonKeane
open FK.ClusterCover

universe u
variable {V : Type u} {G : SimpleGraph V} {ω : G.edgeSet → Bool}

/-- An external avoided component, its stem, and one central parent. -/
structure AssemblyBranch (G : SimpleGraph V) (ω : G.edgeSet → Bool) (U : Set V) where
  root : V
  parent : V
  parent_mem : parent ∈ U
  stem : V
  stem_not_mem : stem ∉ U
  stemInf : (clusterAvoid G ω (incidence G U) stem).Infinite
  conn : OpenConnected G ω (Set.univ \ incidence G U) stem root
  adj : G.Adj parent stem
  adj_open : ω ⟨s(parent, stem), adj⟩ = true
  original : V
  original_mem : original ∈ U
  link : G.Walk original root
  link_open : IsOpenIn ω Set.univ link

namespace AssemblyBranch

variable {U : Set V}

/-- A branch with one attaching edge followed by an arbitrary far arm. -/
abbrev walk (B : AssemblyBranch G ω U) {w : V} (arm : G.Walk B.stem w) : G.Walk B.parent w :=
  SimpleGraph.Walk.cons B.adj arm

lemma mem_avoiding_of_mem_support_tail {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w} (harm : IsOpenIn ω (Set.univ \ incidence G U) arm)
    {x : V} (hx : x ∈ (walk B arm).support.tail) :
    x ∈ clusterAvoid G ω (incidence G U) B.stem := by
  simpa only [walk] using (mem_clusterAvoid_of_mem_support arm harm hx)

lemma walk_parent_or_not_mem {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w} (harm : IsOpenIn ω (Set.univ \ incidence G U) arm)
    {x : V} (hx : x ∈ (walk B arm).support) :
    x = B.parent ∨ x ∉ U := by
  simp only [walk, SimpleGraph.Walk.support_cons, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  · exact Or.inr (not_mem_of_mem_support_of_avoidIncidence B.stem_not_mem arm harm x hx)

lemma walk_central_eq_parent {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w} (harm : IsOpenIn ω (Set.univ \ incidence G U) arm)
    {x : V} (hx : x ∈ (walk B arm).support) (hxU : x ∈ U) :
    x = B.parent := by
  rcases walk_parent_or_not_mem harm hx with rfl | hxnot
  · rfl
  · exact (hxnot hxU).elim

lemma walk_open {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w}
    (hcons : IsOpenIn ω Set.univ (walk B arm)) :
    IsOpenIn (openInternal U ω) Set.univ (walk B arm) :=
  hcons.mono_config (le_openInternal ω)

lemma arm_open_avoiding {B : AssemblyBranch G ω U} {w : V}
    {arm : G.Walk B.stem w} (harm : IsOpenIn ω (Set.univ \ incidence G U) arm) :
    IsOpenIn (openInternal U ω) (Set.univ \ incidence G U) arm :=
  isOpenIn_openInternal_of_avoidIncidence arm harm

/-- Construct an assembly branch from an original component and finite central
set, retaining the prescribed original root.  The next vertex, rather than the
final parent, carries the same infinite incident-avoiding component. -/
theorem exists_at_original [G.LocallyFinite] (hG : G.Connected)
    {U : Set V} (hU : U.Finite) {r : V} (hr : r ∈ U)
    (hinf : {z | OpenConnected G ω Set.univ r z}.Infinite) :
    ∃ B : AssemblyBranch G ω U, B.original = r := by
  obtain ⟨z, hzU, hzinf, pfull, hpfull⟩ := exists_external_root hU hinf
  obtain ⟨a, haU, b, hbU, hbinf, hab, hb_conn, hfar⟩ :=
    exists_incidence_attachment hG pfull hpfull hr hzU hzinf r
  obtain ⟨_, _, _, _, hcons0, _⟩ := hfar 0
  have hadjopen : ω ⟨s(a, b), hab⟩ = true := (isOpenIn_cons.mp hcons0).1.2
  exact ⟨⟨z, a, haU, b, hbU, hbinf, hb_conn, hab, hadjopen,
    r, hr, pfull, hpfull⟩, rfl⟩

/-- Construct an assembly branch from an original component and finite central
set. -/
theorem exists_of_original [G.LocallyFinite] (hG : G.Connected)
    {U : Set V} (hU : U.Finite) {r : V} (hr : r ∈ U)
    (hinf : {z | OpenConnected G ω Set.univ r z}.Infinite) :
    Nonempty (AssemblyBranch G ω U) := by
  obtain ⟨B, _⟩ := exists_at_original hG hU hr hinf
  exact ⟨B⟩




/-- Separating an original component from another selected root separates the
corresponding stems after both transports. -/
lemma avoiding_nonConnected {B B' : AssemblyBranch G ω U}
    (h : ¬ OpenConnected G ω Set.univ B.original B'.root) :
    ¬ OpenConnected G ω (Set.univ \ incidence G U) B.root B'.root := by
  exact external_nonConnected_of_nonConnected B.link B.link_open h

lemma avoiding_nonConnected_stems {B B' : AssemblyBranch G ω U}
    (h : ¬ OpenConnected G ω (Set.univ \ incidence G U) B.root B'.root) :
    ¬ OpenConnected G ω (Set.univ \ incidence G U) B.stem B'.stem := by
  intro hbb
  obtain ⟨q, hq⟩ := hbb
  obtain ⟨qb, hqb⟩ := B.conn
  obtain ⟨qb', hqb'⟩ := B'.conn
  have hback : OpenConnected G ω (Set.univ \ incidence G U) B.root B.stem :=
    ⟨qb.reverse, isOpenIn_reverse qb hqb⟩
  apply h
  exact ⟨qb.reverse.append (q.append qb'),
    isOpenIn_append.mpr ⟨isOpenIn_reverse qb hqb, isOpenIn_append.mpr ⟨hq, hqb'⟩⟩⟩


end AssemblyBranch
